// (c) Meta Platforms, Inc. and affiliates. Confidential and proprietary.

// Mapping of grammar defined here (or variant thereof):
// https://github.com/tree-sitter/tree-sitter-python/blob/master/grammar.js

use std::collections::HashMap;

use ast::Alias;
use ast::Arg;
use ast::Arguments;
use ast::Boolop;
use ast::Cmpop;
use ast::Comprehension;
use ast::ConstantDesc;
use ast::Excepthandler;
use ast::ExcepthandlerDesc;
use ast::Expr;
use ast::ExprContext;
use ast::ExprDesc;
use ast::Keyword as AstKeyword;
use ast::Mod_;
use ast::Num;
use ast::Operator;
use ast::Stmt;
use ast::StmtDesc;
use ast::Unaryop;
use ast::Withitem;
use itertools::join;
use sitter::get_node_type;
use sitter::AugAssignOperator;
use sitter::BinaryOperator;
use sitter::ComparisonOperator;
use sitter::Keyword;
use sitter::NodeType;
use sitter::Production;
use sitter::ProductionKind;
use tree_sitter::Node;
use tree_sitter::Parser as SitterParser;

use crate::ast;
use crate::sitter;

#[derive(Debug, thiserror::Error)]
pub enum ParserError {
    #[error("failed to set tree_sitter language: {0}")]
    Language(#[from] tree_sitter::LanguageError),
    #[error("parser timed out or was cancelled")]
    DidNotComplete,
    #[error("expected a node, but it was missing")]
    MissingChild,
    #[error("expected comparison to have lhs node, but it was missing")]
    MissingLhs,
    #[error("expected comparison to have rhs node, but it was missing")]
    MissingRhs,
    #[error("expected BinaryOperator node, but got unexpected node kind: {0}")]
    MissingOperator(String),
}

///
/// Parser is responsible for driving parsing of a python code String into an internal CST representation
/// before lowering to an AST. The AST is expected to match 1:1 with CPython. The AST is held within an
/// `ASTAndMetaData` instance (and potentitally additional metadata)
///
#[derive(Debug)]
pub struct Parser {
    code: String,
    ast_and_metadata: ASTAndMetaData,
    // contingent on if we are on lhs or rhs of assignment or del expression
    current_expr_ctx: Vec<Option<ExprContext>>,
    inc_expr_col_offset: isize,
}

///
/// `ASTAndMetaData` presently just holds the lowered AST
///
#[derive(Debug)]
pub struct ASTAndMetaData {
    // AST root for what was parsed correctly
    pub ast: Option<Mod_>,
}

impl ASTAndMetaData {
    fn new() -> Self {
        ASTAndMetaData { ast: None }
    }
}

impl Stmt {
    fn new(desc: StmtDesc, node_start: &Node, node_end: &Node) -> Stmt {
        let start_position = node_start.start_position();
        let end_position = node_end.end_position();

        Stmt {
            desc,
            lineno: start_position.row as isize + 1,
            col_offset: start_position.column as isize,
            end_lineno: Some(end_position.row as isize + 1),
            end_col_offset: Some(end_position.column as isize),
        }
    }
}

impl AstKeyword {
    fn new(arg: Option<String>, value: Expr, node: &Node) -> AstKeyword {
        let start_position = node.start_position();
        let end_position = node.end_position();

        AstKeyword {
            arg,
            value,
            lineno: start_position.row as isize + 1,
            col_offset: start_position.column as isize,
            end_lineno: Some(end_position.row as isize + 1),
            end_col_offset: Some(end_position.column as isize),
        }
    }
}

impl Expr {
    fn new(
        desc: ExprDesc,
        lineno: isize,
        col_offset: isize,
        end_lineno: isize,
        end_col_offset: isize,
    ) -> Expr {
        Expr {
            desc: Box::new(desc),
            lineno,
            col_offset,
            end_lineno: Some(end_lineno),
            end_col_offset: Some(end_col_offset),
        }
    }
}

impl Alias {
    fn new(name: String, asname: Option<String>, node: &Node) -> Alias {
        let start_position = node.start_position();
        let end_position = node.end_position();

        Alias {
            name,
            asname,
            lineno: start_position.row as isize + 1,
            col_offset: start_position.column as isize,
            end_lineno: Some(end_position.row as isize + 1),
            end_col_offset: Some(end_position.column as isize),
        }
    }
}

impl Excepthandler {
    fn new(desc: ExcepthandlerDesc, node: &Node) -> Excepthandler {
        let start_position = node.start_position();
        let end_position = node.end_position();

        Excepthandler {
            desc,
            lineno: start_position.row as isize + 1,
            col_offset: start_position.column as isize,
            end_lineno: Some(end_position.row as isize + 1),
            end_col_offset: Some(end_position.column as isize),
        }
    }
}

impl Arg {
    fn new_simple(arg: String, start_node: &Node, end_node: &Node) -> Arg {
        let start_position = start_node.start_position();
        let end_position = end_node.end_position();

        Arg {
            arg,
            annotation: None,
            type_comment: None,
            lineno: start_position.row as isize + 1,
            col_offset: start_position.column as isize,
            end_lineno: Some(end_position.row as isize + 1),
            end_col_offset: Some(end_position.column as isize),
        }
    }

    fn new_with_type(arg: String, annotation: Expr, start_node: &Node, end_node: &Node) -> Arg {
        let start_position = start_node.start_position();
        let end_position = end_node.end_position();

        Arg {
            arg,
            annotation: Some(annotation),
            type_comment: None,
            lineno: start_position.row as isize + 1,
            col_offset: start_position.column as isize,
            end_lineno: Some(end_position.row as isize + 1),
            end_col_offset: Some(end_position.column as isize),
        }
    }
}

impl Parser {
    pub fn new(code: String) -> Self {
        Parser {
            code,
            ast_and_metadata: ASTAndMetaData::new(),
            current_expr_ctx: Vec::new(),
            inc_expr_col_offset: 0,
        }
    }

    pub fn get_ast_and_metadata(&self) -> &ASTAndMetaData {
        &self.ast_and_metadata
    }

    fn new_expr(&mut self, desc: ExprDesc, node: &Node) -> Expr {
        let start_position = node.start_position();
        let end_position = node.end_position();

        Expr::new(
            desc,
            start_position.row as isize + 1,
            start_position.column as isize + self.inc_expr_col_offset,
            end_position.row as isize + 1,
            end_position.column as isize + self.inc_expr_col_offset,
        )
    }

    ///
    /// Public entry point to parse code.
    /// Code is defined at construction time (`new`) but it could also be passed
    /// to this function. We could also pass a delta
    ///
    pub fn parse(&mut self, internal_ast: bool) -> Result<(), ParserError> {
        let mut cst_to_ast = SitterParser::new();
        cst_to_ast.set_language(tree_sitter_python::language())?;
        let tree = match cst_to_ast.parse(&self.code, None) {
            Some(t) => t,
            None => return Err(ParserError::DidNotComplete),
        };
        let root = tree.root_node();

        if internal_ast {
            println!(">>> SITTER DERIVED AST :\n");
            print_internal_ast(&root, "");
        }

        self.parse_module(&root)
    }

    //
    //
    // Functions that consumes the tree-sitter productions
    //
    //

    // Process a module.
    // module: $ => repeat($._statement),
    fn parse_module(&mut self, root: &Node) -> Result<(), ParserError> {
        // root must be a module
        if root.kind() != "module" {
            self.ast_and_metadata.ast = Some(Mod_::Module {
                body: vec![],
                type_ignores: vec![],
            });
            return Ok(());
        }
        let mut body = vec![];
        self.block(root, &mut body)?;
        self.ast_and_metadata.ast = Some(Mod_::Module {
            body,
            type_ignores: vec![],
        });
        Ok(())
    }

    // Process a generic block updating `statements`.
    // Generally sequences of `repeat($._statement)`
    fn block(&mut self, block: &Node, statements: &mut Vec<Stmt>) -> Result<(), ParserError> {
        for child in block.named_children(&mut block.walk()) {
            let node_type = get_node_type(&child);
            match &node_type {
                NodeType::Production(production) => match &production.production_kind {
                    ProductionKind::COMMENT => (),
                    _ => statements.push(self.statement(production)?),
                },
                _ => (),
            }
        }
        Ok(())
    }

    // Process a StmtDesc
    //
    // _statement: $ => choice(
    //     $._simple_statements,
    //     $._compound_statement
    // ),
    // _simple_statements: $ => seq(
    //     sep1($._simple_statement, SEMICOLON),
    //     optional(SEMICOLON),
    //     $._newline
    //   ),
    // _simple_statement: $ => choice(
    //     $.future_import_statement,
    //     $.import_statement,
    //     $.import_from_statement,
    //     $.print_statement,
    //     $.assert_statement,
    //     $.expression_statement, // this recurses down
    //     $.return_statement,
    //     $.delete_statement,
    //     $.raise_statement,
    //     $.pass_statement,
    //     $.break_statement,
    //     $.continue_statement,
    //     $.global_statement,
    //     $.nonlocal_statement,
    //     $.exec_statement
    //   ),
    // _compound_statement: $ => choice(
    //     $.if_statement,
    //     $.for_statement,
    //     $.while_statement,
    //     $.try_statement,
    //     $.with_statement,
    //     $.function_definition,
    //     $.class_definition,
    //     $.decorated_definition,
    //     $.match_statement,
    //   ),
    fn statement(&mut self, rule: &Production) -> Result<Stmt, ParserError> {
        use ProductionKind::*;

        match &rule.production_kind {
            DECORATED_DEFINITION => self.decorated_definition(rule.node),
            rest => {
                let statement_desc = match rest {
                    // _simple_statement
                    ASSERT_STATEMENT => self.assert_statement(rule.node)?,
                    IMPORT_STATEMENT => self.import_statement(rule.node)?,
                    IMPORT_FROM_STATEMENT => self.import_from_statement(rule.node)?,
                    FUTURE_IMPORT_STATEMENT => self.future_import_statement(rule.node)?,
                    EXPRESSION_STATEMENT => self.expression_statement(rule.node)?,
                    DELETE_STATEMENT => self.delete_statement(rule.node)?,
                    RETURN_STATEMENT => self.return_statement(rule.node)?,
                    RAISE_STATEMENT => self.raise_statement(rule.node)?,
                    PASS_STATEMENT => StmtDesc::Pass,
                    BREAK_STATEMENT => StmtDesc::Break,
                    CONTINUE_STATEMENT => StmtDesc::Continue,
                    GLOBAL_STATEMENT => self.global_statement(rule.node)?,
                    NONLOCAL_STATEMENT => self.nonlocal_statement(rule.node)?,
                    // EXEC_STATEMENT,  // legacy, not sure if we will do these two...
                    // PRINT_STATEMENT, // legacy, not sure if we will do these two...
                    // _compound_statement
                    IF_STATEMENT => self.if_statement(rule.node)?,
                    FOR_STATEMENT => self.for_statement(rule.node)?,
                    WHILE_STATEMENT => self.while_statement(rule.node)?,
                    TRY_STATEMENT => self.try_statement(rule.node)?,
                    WITH_STATEMENT => self.with_statement(rule.node)?,
                    FUNCTION_DEFINITION => self.function_definition(rule.node, vec![])?,
                    CLASS_DEFINITION => self.class_definition(rule.node, vec![])?,

                    // MATCH_STATEMENT,

                    // uncomment above when writing the production and delete from here
                    // the order above is that in the tree sitter grammar so easier to
                    // check for now
                    PRINT_STATEMENT | EXEC_STATEMENT | MATCH_STATEMENT => {
                        panic!("unexpected statement node: {:?}", rule.node)
                    }
                    _ => panic!("unexpected statement node: {:?}", rule.node),
                };

                Ok(Stmt::new(statement_desc, rule.node, rule.node))
            }
        }
    }

    fn decorated_definition(&mut self, node: &Node) -> Result<Stmt, ParserError> {
        // resolves to a class definition or funcdef
        let mut decorator_list: Vec<Expr> = vec![];

        for child in node.named_children(&mut node.walk()) {
            let node_type = get_node_type(&child);
            match &node_type {
                NodeType::Production(production) => match &production.production_kind {
                    ProductionKind::FUNCTION_DEFINITION => {
                        let func_def = self.function_definition(&child, decorator_list)?;
                        return Ok(Stmt::new(func_def, &child, &child));
                    }
                    ProductionKind::CLASS_DEFINITION => {
                        let class_def = self.class_definition(&child, decorator_list)?;
                        return Ok(Stmt::new(class_def, &child, &child));
                    }
                    ProductionKind::DECORATOR => {
                        // decorator
                        let dec_expr_node = child.child(1).expect("dectorator missing elaboration");
                        let dec_expr_node_type = get_node_type(&dec_expr_node);
                        let dec_expr = self.expression(&dec_expr_node_type)?;
                        decorator_list.push(dec_expr);
                    }
                    _ => (),
                },
                _ => (),
            }
        }

        Err(ParserError::MissingChild)
    }

    /*     global_statement: $ => seq(
      'global',
      commaSep1($.identifier)
    ), */
    fn global_statement(&mut self, node: &Node) -> Result<StmtDesc, ParserError> {
        let mut identifiers = vec![];
        self.parse_identifiers(node, &mut identifiers)?;
        Ok(StmtDesc::Global(identifiers))
    }

    /*     nonlocal_statement: $ => seq(
      'nonlocal',
      commaSep1($.identifier)
    ), */
    fn nonlocal_statement(&mut self, node: &Node) -> Result<StmtDesc, ParserError> {
        let mut identifiers = vec![];
        self.parse_identifiers(node, &mut identifiers)?;

        Ok(StmtDesc::Nonlocal(identifiers))
    }

    fn parse_identifiers(
        &mut self,
        node: &Node,
        identifiers: &mut Vec<String>,
    ) -> Result<(), ParserError> {
        for child in node.named_children(&mut node.walk()) {
            let identifier = self.get_text(&child);
            identifiers.push(identifier);
        }
        Ok(())
    }

    // Process Function Definition
    //
    // function_definition: $ => seq(
    //     optional('async'),
    //     'def',
    //     field('name', $.identifier),
    //     field('parameters', $.parameters),
    //     optional(
    //       seq(
    //         '->',
    //         field('return_type', $.type)
    //       )
    //     ),
    //     ':',
    //     field('body', $._suite)
    // ),
    fn function_definition(
        &mut self,
        func_def: &Node,
        decorator_list: Vec<Expr>,
    ) -> Result<StmtDesc, ParserError> {
        let name_node = func_def
            .child_by_field_name("name")
            .expect("missing function name");
        let name = self.get_text(&name_node);
        let parameters_node = func_def
            .child_by_field_name("parameters")
            .expect("missing function parameters");
        let parameters = self.get_parameters(&parameters_node)?;
        let body_node = func_def
            .child_by_field_name("body")
            .expect("missing function body");
        let mut body = vec![];
        self.block(&body_node, &mut body)?;

        let return_annotation_node = func_def.child_by_field_name("return_type");
        let return_annotation_expr = match &return_annotation_node {
            Some(ret_annotation) => {
                let annotation_node = ret_annotation.child(0).expect("type node missing type");
                let annotation_node_type = get_node_type(&annotation_node);
                Some(self.expression(&annotation_node_type)?)
            }
            _ => None,
        };

        if self.get_text(&func_def.child(0).expect("def or async node expected")) == "async" {
            Ok(StmtDesc::AsyncFunctionDef {
                name,
                args: parameters,
                body,
                decorator_list, // decorators are added by wrapping code
                returns: return_annotation_expr,
                type_comment: None,
            })
        } else {
            Ok(StmtDesc::FunctionDef {
                name,
                args: parameters,
                body,
                decorator_list, // decorators are added by wrapping code
                returns: return_annotation_expr,
                type_comment: None,
            })
        }
    }

    // Load the function parameters
    //
    // parameters: $ => seq(
    //     '(',
    //     optional($._parameters),
    //     ')'
    // ),
    // _parameters: $ => seq(
    //     commaSep1($.parameter),
    //     optional(',')
    // ),
    // parameter: $ => choice(
    //     $.identifier,
    //     $.typed_parameter,
    //     $.default_parameter,
    //     $.typed_default_parameter,
    //     $.list_splat_pattern,
    //     $.tuple_pattern,
    //     $.keyword_separator,
    //     $.positional_separator,
    //     $.dictionary_splat_pattern
    // ),
    fn get_parameters(&mut self, parameters: &Node) -> Result<Arguments, ParserError> {
        let mut posonlyargs: Vec<Arg> = vec![];
        let mut args: Vec<Arg> = vec![];
        let mut vararg: Option<Arg> = None;
        let mut kwonlyargs: Vec<Arg> = vec![]; // arguments go in here after a vararg or / token
        let mut kw_defaults: Vec<Option<Expr>> = vec![]; //defaults go here after a vararg  or * token
        let mut kwarg: Option<Arg> = None;
        let mut defaults: Vec<Expr> = vec![];

        let mut require_kw_args = false;

        for parameter in parameters.named_children(&mut parameters.walk()) {
            let parameter_annotation = get_node_type(&parameter);
            match &parameter_annotation {
                NodeType::Production(param) => match &param.production_kind {
                    ProductionKind::IDENTIFIER => {
                        self.get_parameters_identifier(
                            param.node,
                            &require_kw_args,
                            &mut kwonlyargs,
                            &mut kw_defaults,
                            &mut args,
                        );
                    }
                    ProductionKind::TYPED_PARAMETER => {
                        self.get_parameters_typed_parameter(
                            param.node,
                            &parameter,
                            &mut require_kw_args,
                            &mut kwonlyargs,
                            &mut kw_defaults,
                            &mut args,
                            &mut vararg,
                            &mut kwarg,
                        )?;
                    }
                    ProductionKind::DEFAULT_PARAMETER => {
                        self.get_parameters_default_parameter(
                            param.node,
                            &require_kw_args,
                            &mut kwonlyargs,
                            &mut kw_defaults,
                            &mut args,
                            &mut defaults,
                        )?;
                    }
                    ProductionKind::TYPED_DEFAULT_PARAMETER => {
                        self.get_parameters_typed_default_parameter(
                            param.node,
                            &require_kw_args,
                            &mut kwonlyargs,
                            &mut kw_defaults,
                            &mut args,
                            &mut defaults,
                        )?;
                    }
                    ProductionKind::LIST_SPLAT_PATTERN => {
                        let ident_node =
                            &param.node.child(1).expect("identifier of starred missing");
                        let identifier = self.get_text(ident_node);

                        vararg = Some(Arg::new_simple(identifier, ident_node, &parameter));
                        require_kw_args = true;
                    }
                    ProductionKind::TUPLE_PATTERN => panic!("get_parameters: TUPLE_PATTERN"),
                    ProductionKind::KEYWORD_SEPARATOR => {
                        // all arguments defined past this point are now keyword args
                        require_kw_args = true;
                    }
                    ProductionKind::POSITIONAL_SEPARATOR => {
                        // everything declared as an arugment now becomes a posonlyargs
                        while !args.is_empty() {
                            posonlyargs.push(args.remove(0));
                        }
                    }
                    ProductionKind::DICTIONARY_SPLAT_PATTERN => {
                        let ident_node = &param
                            .node
                            .child(1)
                            .expect("identifier of dictionary argument");
                        let identifier = self.get_text(ident_node);

                        kwarg = Some(Arg::new_simple(identifier, ident_node, &parameter));
                    }
                    _ => panic!("unexpected parameter production"),
                },
                _ => (),
            }
        }

        Ok(Arguments {
            posonlyargs,
            args,
            vararg,
            kwonlyargs,
            kw_defaults,
            kwarg,
            defaults,
        })
    }

    // identifier: $ => /[_\p{XID_Start}][_\p{XID_Continue}]*/,
    fn get_parameters_identifier(
        &mut self,
        node: &Node,
        require_kw_args: &bool,
        kwonlyargs: &mut Vec<Arg>,
        kw_defaults: &mut Vec<Option<Expr>>,
        args: &mut Vec<Arg>,
    ) {
        let identifier = self.get_text(node);

        let arg = Arg::new_simple(identifier, node, node);

        match require_kw_args {
            true => {
                kwonlyargs.push(arg);
                kw_defaults.push(None);
            }
            _ => args.push(arg),
        };
    }

    // typed_parameter: $ => prec(PREC.typed_parameter, seq(
    //  choice(
    //    $.identifier,
    //    $.list_splat_pattern,
    //    $.dictionary_splat_pattern
    //  ),
    //  ':',
    //  field('type', $.type)
    // )),
    fn get_parameters_typed_parameter(
        &mut self,
        node: &Node,
        parameter: &Node,
        require_kw_args: &mut bool,
        kwonlyargs: &mut Vec<Arg>,
        kw_defaults: &mut Vec<Option<Expr>>,
        args: &mut Vec<Arg>,
        vararg: &mut Option<Arg>,
        kwarg: &mut Option<Arg>,
    ) -> Result<(), ParserError> {
        let typed_parameter_node = node
            .child_by_field_name("type")
            .expect("default param missing type");
        let annotation_node = typed_parameter_node
            .child(0)
            .expect("type node missing type");

        let annotation_node_type = get_node_type(&annotation_node);
        let annotation_expr = self.expression(&annotation_node_type)?;

        let ident_node = &node.child(0).expect("typed param id, *id or **id missing");
        let ident_node_type = get_node_type(ident_node);
        match ident_node_type {
            NodeType::Production(param) => match &param.production_kind {
                ProductionKind::IDENTIFIER => {
                    let identifier = self.get_text(param.node);
                    let arg = Arg::new_with_type(identifier, annotation_expr, parameter, parameter);
                    match require_kw_args {
                        true => {
                            kwonlyargs.push(arg);
                            kw_defaults.push(None);
                        }
                        _ => args.push(arg),
                    };
                }
                ProductionKind::LIST_SPLAT_PATTERN => {
                    let ident_node = &param.node.child(1).expect("identifier of starred missing");
                    let identifier = self.get_text(ident_node);

                    *vararg = Some(Arg::new_with_type(
                        identifier,
                        annotation_expr,
                        ident_node,
                        parameter,
                    ));
                    // all arguments defined past this point are now keyword args
                    *require_kw_args = true;
                }
                ProductionKind::DICTIONARY_SPLAT_PATTERN => {
                    let ident_node = &param
                        .node
                        .child(1)
                        .expect("identifier of dictionary argument");
                    let identifier = self.get_text(ident_node);

                    *kwarg = Some(Arg::new_with_type(
                        identifier,
                        annotation_expr,
                        ident_node,
                        parameter,
                    ));
                }
                _ => panic!("unexpected typed parameter production"),
            },
            _ => (),
        }
        Ok(())
    }

    // default_parameter: $ => seq(
    //  field('name', $.identifier),
    //  '=',
    //  field('value', $.expression)
    // ),
    fn get_parameters_default_parameter(
        &mut self,
        node: &Node,
        require_kw_args: &bool,
        kwonlyargs: &mut Vec<Arg>,
        kw_defaults: &mut Vec<Option<Expr>>,
        args: &mut Vec<Arg>,
        defaults: &mut Vec<Expr>,
    ) -> Result<(), ParserError> {
        let name_node = &node
            .child_by_field_name("name")
            .expect("default param missing name");

        let identifier = self.get_text(name_node);
        let arg = Arg::new_simple(identifier, name_node, name_node);

        let default_value_node = &node
            .child_by_field_name("value")
            .expect("default param missing value");
        let default_value_type = &get_node_type(default_value_node);
        let default_value = self.expression(default_value_type)?;

        match require_kw_args {
            true => {
                kwonlyargs.push(arg);
                kw_defaults.push(Some(default_value));
            }
            _ => {
                args.push(arg);
                defaults.push(default_value);
            }
        };

        Ok(())
    }

    // typed_default_parameter: $ => prec(PREC.typed_parameter, seq(
    //  field('name', $.identifier),
    //  ':',
    //  field('type', $.type),
    //  '=',
    //  field('value', $.expression)
    // )),
    fn get_parameters_typed_default_parameter(
        &mut self,
        node: &Node,
        require_kw_args: &bool,
        kwonlyargs: &mut Vec<Arg>,
        kw_defaults: &mut Vec<Option<Expr>>,
        args: &mut Vec<Arg>,
        defaults: &mut Vec<Expr>,
    ) -> Result<(), ParserError> {
        let name_node = &node
            .child_by_field_name("name")
            .expect("typed default param missing name");

        let typed_default_parameter_node = &node
            .child_by_field_name("type")
            .expect("typed default param missing name");
        let annotation_node = typed_default_parameter_node
            .child(0)
            .expect("type node missing type");

        let default_value_node = &node
            .child_by_field_name("value")
            .expect("typed default param missing name");

        let annotation_node_type = get_node_type(&annotation_node);
        let annotation_expr = self.expression(&annotation_node_type)?;

        let identifier = self.get_text(name_node);

        let arg = Arg::new_with_type(
            identifier,
            annotation_expr,
            name_node,
            typed_default_parameter_node,
        );

        let default_value_type = &get_node_type(default_value_node);
        let default_value = self.expression(default_value_type)?;

        match require_kw_args {
            true => {
                kwonlyargs.push(arg);
                kw_defaults.push(Some(default_value));
            }
            _ => {
                args.push(arg);
                defaults.push(default_value);
            }
        };

        Ok(())
    }

    // Process a Class Definition
    //
    // class_definition: $ => seq(
    //     'class',
    //     field('name', $.identifier),
    //     field('superclasses', optional($.argument_list)),
    //     ':',
    //     field('body', $._suite)
    // ),
    fn class_definition(
        &mut self,
        class_def: &Node,
        decorator_list: Vec<Expr>,
    ) -> Result<StmtDesc, ParserError> {
        let name_node = class_def
            .child_by_field_name("name")
            .expect("missing class name");
        let name = self.get_text(&name_node);
        let body_node = class_def
            .child_by_field_name("body")
            .expect("missing class body");
        let mut body = vec![];
        self.block(&body_node, &mut body)?;

        let mut bases: Vec<Expr> = vec![];
        let mut keywords: Vec<AstKeyword> = vec![];

        match class_def.child_by_field_name("superclasses") {
            Some(superclasses_node) => {
                self.argument_list(&superclasses_node, &mut bases, &mut keywords)?;
            }
            _ => (),
        }

        Ok(StmtDesc::ClassDef {
            name,
            bases,
            keywords,
            body,
            decorator_list,
        })
    }

    // assert_statement: $ => seq(
    //  'assert',
    //  commaSep1($.expression)
    // ),
    fn assert_statement(&mut self, node: &Node) -> Result<StmtDesc, ParserError> {
        let test_node = node.child(1).unwrap();
        let test_node_type = get_node_type(&test_node);
        let test = self.expression(&test_node_type)?;

        let mut msg = None;
        if node.child_count() == 4 {
            let msg_node = node.child(3).unwrap();
            let msg_node_type = get_node_type(&msg_node);
            msg = Some(self.expression(&msg_node_type)?);
        }

        Ok(StmtDesc::Assert { test, msg })
    }

    fn dotted_name_to_string(&mut self, node: &Node) -> Result<String, ParserError> {
        Ok(join(
            node.named_children(&mut node.walk())
                .map(|x| self.get_text(&x)),
            ".",
        ))
    }

    fn get_aliases(&mut self, node: &Node, aliases: &mut Vec<Alias>) -> Result<(), ParserError> {
        for alias_child in node.named_children(&mut node.walk()) {
            match alias_child.child_by_field_name("alias") {
                Some(alias_name) => {
                    aliases.push(Alias::new(
                        self.dotted_name_to_string(
                            &alias_child
                                .child_by_field_name("name")
                                .expect("missing aliased_import name"),
                        )?,
                        Some(self.get_text(&alias_name)),
                        &alias_child,
                    ));
                }
                _ => {
                    // straight dotted name: a.b.c etc
                    aliases.push(Alias::new(
                        self.dotted_name_to_string(&alias_child)?,
                        None,
                        &alias_child,
                    ));
                }
            }
        }
        Ok(())
    }

    //import_statement: $ => seq(
    // 'import',
    // $._import_list
    // ),
    //aliased_import: $ => seq(
    //  field('name', $.dotted_name),
    //  'as',
    //  field('alias', $.identifier)
    //),
    fn import_statement(&mut self, node: &Node) -> Result<StmtDesc, ParserError> {
        let mut aliases: Vec<Alias> = vec![];
        self.get_aliases(node, &mut aliases)?;
        Ok(StmtDesc::Import(aliases))
    }

    // import_from_statement: $ => seq(
    //    'from',
    //    field('module_name', choice(
    //      $.relative_import,
    //      $.dotted_name
    //    )),
    //    'import',
    //    choice(
    //      $.wildcard_import,
    //      $._import_list,
    //      seq('(', $._import_list, ')')
    //    )
    //  ),
    fn import_from_statement(&mut self, node: &Node) -> Result<StmtDesc, ParserError> {
        let mut names: Vec<Alias> = vec![];
        let mut level: isize = 0;

        let module_name_node = node
            .child_by_field_name("module_name")
            .expect("import_from_statement missing module_name");
        let module__ = match module_name_node.kind() {
            "relative_import" => {
                // Relative imports are interesting. From the docs: "level is
                // an integer holding the level of the relative import (0
                // means absolute import)." It can be thought of like
                // directoris in a filesystem where by the number of dots
                // preceding a dotted name indicates how many levels upwards
                // one must look for the import dependency
                let dots_and_name = self.get_text(&module_name_node);

                for c in dots_and_name.chars() {
                    if c == '.' {
                        level += 1;
                    } else {
                        break; // only dots at start
                    }
                }

                let remainder: String = dots_and_name.trim_start_matches('.').to_string();
                if remainder.is_empty() {
                    None
                } else {
                    Some(remainder)
                }
            }
            _ => Some(self.dotted_name_to_string(&module_name_node)?),
        };

        let aliases_or_wildcard = &node
            .child(3)
            .expect("list of imports for import_from_statement");
        match aliases_or_wildcard.kind() {
            "wildcard_import" => {
                names.push(Alias::new(String::from("*"), None, aliases_or_wildcard))
            }
            _ => {
                for alias in node.named_children(&mut node.walk()) {
                    if alias == module_name_node {
                        continue; // skip the `from xyz`, `xzy` node as processed already
                    }
                    match alias.child_by_field_name("alias") {
                        Some(alias_name) => {
                            names.push(Alias::new(
                                self.dotted_name_to_string(
                                    &alias
                                        .child_by_field_name("name")
                                        .expect("missing aliased_import name"),
                                )?,
                                Some(self.get_text(&alias_name)),
                                &alias,
                            ));
                        }
                        _ => {
                            // straight dotted name: a.b.c etc
                            names.push(Alias::new(
                                self.dotted_name_to_string(&alias)?,
                                None,
                                &alias,
                            ));
                        }
                    }
                }
            }
        }

        Ok(StmtDesc::ImportFrom {
            module__,
            names,
            level: Some(level), // optional but always included
        })
    }

    fn future_import_statement(&mut self, node: &Node) -> Result<StmtDesc, ParserError> {
        let mut names: Vec<Alias> = vec![];
        self.get_aliases(node, &mut names)?;

        Ok(StmtDesc::ImportFrom {
            module__: Some("__future__".to_string()),
            names,
            level: Some(0), // optional but always included
        })
    }

    // Process Return StmtDesc
    //
    // return_statement: $ => seq(
    //     'return',
    //     optional($._expressions)
    // ),
    fn return_statement(&mut self, node: &Node) -> Result<StmtDesc, ParserError> {
        let mut expr = None;
        for child in node.children(&mut node.walk()) {
            let node_type = get_node_type(&child);
            match &node_type {
                NodeType::Production(_) => {
                    expr = Some(self.expression(&node_type)?);
                }
                _ => (), // skip other nodes, error recovery may play a role here
            }
        }

        Ok(StmtDesc::Return(expr))
    }

    /* raise_statement: $ => seq(
      'raise',
      optional($._expressions),
      optional(seq('from', field('cause', $.expression)))
    ), */
    fn raise_statement(&mut self, node: &Node) -> Result<StmtDesc, ParserError> {
        let mut exc = None;
        let mut cause = None;
        match node.child_by_field_name("cause") {
            Some(from_node) => {
                let expr_node = node.child(1).unwrap();
                let expr_node_type = get_node_type(&expr_node);
                exc = Some(self.expression(&expr_node_type)?);

                let from_node_type = get_node_type(&from_node);
                cause = Some(self.expression(&from_node_type)?);
            }
            _ => match node.child(1) {
                Some(expr_node) => {
                    let expr_node_type = get_node_type(&expr_node);
                    exc = Some(self.expression(&expr_node_type)?);
                }
                _ => (),
            },
        }

        Ok(StmtDesc::Raise { exc, cause })
    }

    // Process an ExprDesc StmtDesc.
    // expression_statement: $ => choice(
    //     $.expression,
    //     seq(commaSep1($.expression), optional(',')),
    //     $.assignment,
    //     $.augmented_assignment,
    //     $.yield
    // ),
    fn expression_statement(&mut self, node: &Node) -> Result<StmtDesc, ParserError> {
        // TODO: do sequences of expression come here?
        let child_expr = node.named_child(0).ok_or(ParserError::MissingChild)?;
        let expr_ = get_node_type(&child_expr);
        let expr_statement = match expr_ {
            NodeType::Production(ref rule) => {
                match &rule.production_kind {
                    ProductionKind::ASSIGNMENT => {
                        let (mut targets, type_annot, value, type_comment, simple) =
                            self.assignment(rule.node)?;

                        if let Some(annotation) = type_annot {
                            StmtDesc::AnnAssign {
                                target: targets.pop().unwrap(),
                                annotation,
                                value,
                                simple,
                            }
                        } else {
                            StmtDesc::Assign {
                                targets,
                                value: value.unwrap(),
                                type_comment,
                            }
                        }
                    }
                    ProductionKind::AUGMENTED_ASSIGNMENT => self.aug_assign(rule.node)?,
                    ProductionKind::YIELD => {
                        let yeild_desc = self.yield_statement(rule.node)?;
                        StmtDesc::Expr(self.new_expr(yeild_desc, node))
                    }
                    // TODO: do sequences of expression come here?
                    _ => StmtDesc::Expr(self.expression(&expr_)?),
                }
            }
            _ => panic!("should be unreachable"),
        };
        Ok(expr_statement)
    }

    // Delete(expr* targets)
    fn delete_statement(&mut self, node: &Node) -> Result<StmtDesc, ParserError> {
        let mut expressions: Vec<Expr> = vec![];

        self.set_expression_context(ExprContext::Del);

        for child in node.children(&mut node.walk()) {
            let node_type = get_node_type(&child);
            match node_type {
                NodeType::Production(ref rule) => match &rule.production_kind {
                    ProductionKind::EXPRESSION_LIST => {
                        self.primary_expression_sequence(&child, &mut expressions)?;
                    }
                    _ => expressions.push(self.expression(&node_type)?),
                },
                _ => (), //del keyword
            }
        }

        self.pop_expression_context();

        Ok(StmtDesc::Delete(expressions))
    }

    // for_statement: $ => seq(
    //  optional('async'),
    //  'for',
    //  field('left', $._left_hand_side),
    //  'in',
    //  field('right', $._expressions),
    //  ':',
    //  field('body', $._suite),
    //  field('alternative', optional($.else_clause))
    //),
    fn for_statement(&mut self, for_node: &Node) -> Result<StmtDesc, ParserError> {
        self.set_expression_context(ExprContext::Store);
        let target_node = for_node
            .child_by_field_name("left")
            .expect("missing left in for statement");
        let target_type = get_node_type(&target_node);
        let target = self.expression(&target_type)?;
        self.pop_expression_context();

        let iter_node = for_node
            .child_by_field_name("right")
            .expect("missing right in for statement");
        let iter_type = get_node_type(&iter_node);
        let iter = self.expression(&iter_type)?;

        let body_node = for_node
            .child_by_field_name("body")
            .expect("missing body in for statement");
        let mut body_block = vec![];
        self.block(&body_node, &mut body_block)?;

        let mut orelse_block = vec![];

        let orelse_node = for_node.child_by_field_name("alternative");
        match &orelse_node {
            Some(orelse_cont) => match &orelse_cont.child_by_field_name("body") {
                Some(body_cont) => self.block(body_cont, &mut orelse_block)?,
                _ => (),
            },
            _ => (),
        }
        if for_node.child(0).unwrap().kind().eq("async") {
            Ok(StmtDesc::AsyncFor {
                target,
                iter,
                body: body_block,
                orelse: orelse_block,
                type_comment: None,
            })
        } else {
            Ok(StmtDesc::For {
                target,
                iter,
                body: body_block,
                orelse: orelse_block,
                type_comment: None,
            })
        }
    }

    // with_statement: $ => seq(
    //    optional('async'),
    //    'with',
    //    $.with_clause,
    //    ':',
    //    field('body', $._suite)
    //  ),
    //
    //  with_clause: $ => choice(
    //    commaSep1($.with_item),
    //    seq('(', commaSep1($.with_item), ')')
    //  ),
    //
    //  with_item: $ => prec.dynamic(-1, seq(
    //    field('value', $.expression),
    //  )),
    fn with_statement(&mut self, with_node: &Node) -> Result<StmtDesc, ParserError> {
        let is_async: bool = with_node.child(0).unwrap().kind().eq("async");
        let body_node = with_node
            .child_by_field_name("body")
            .expect("missing body in with statement");
        let mut body = vec![];
        self.block(&body_node, &mut body)?;

        let mut items: Vec<Withitem> = vec![];

        let with_clause_node_idx = if is_async { 2 } else { 1 };
        let with_clause_node = with_node.child(with_clause_node_idx).unwrap();

        for with_item_node in with_clause_node.named_children(&mut with_node.walk()) {
            let mut optional_vars: Option<Expr> = None;

            let expr_node = with_item_node
                .child(0)
                .expect("with_item to wrap an expression or as_pattern");

            let expr_type = &get_node_type(&expr_node);

            use ProductionKind::*;

            let context_expr: Expr = match expr_type {
                NodeType::Production(rule) => match &rule.production_kind {
                    AS_PATTERN => {
                        let node = rule.node;
                        let lhs_expression = node.child(0).expect("expression for with_item");
                        let target_expression = node
                            .child(2)
                            .expect("target for with_item")
                            .child(0)
                            .expect("pattern target");

                        let target_expression_type = &get_node_type(&target_expression);
                        self.set_expression_context(ExprContext::Store);
                        optional_vars = Some(self.expression(target_expression_type)?);
                        self.pop_expression_context();

                        let lhs_expression_type = &get_node_type(&lhs_expression);
                        self.expression(lhs_expression_type)?
                    }
                    _ => self.expression(expr_type)?,
                },
                _ => panic!("unexpected statement handling: {:?}", expr_type), // TODO: needs better handle
            };

            items.push(Withitem {
                context_expr,
                optional_vars,
            });
        }

        if is_async {
            Ok(StmtDesc::AsyncWith {
                items,
                body,
                type_comment: None,
            })
        } else {
            Ok(StmtDesc::With {
                items,
                body,
                type_comment: None,
            })
        }
    }

    //    try_statement: $ => seq(
    //    'try',
    //    ':',
    //    field('body', $._suite),
    //    choice(
    //      seq(
    //        repeat1($.except_clause),
    //        optional($.else_clause),
    //        optional($.finally_clause)
    //      ),
    //      seq(
    //        repeat1($.except_group_clause),
    //        optional($.else_clause),
    //        optional($.finally_clause)
    //      ),
    //      $.finally_clause
    //    )
    //  ),
    //
    //  except_clause: $ => seq(
    //    'except',
    //    optional(seq(
    //      $.expression,
    //      optional(seq(
    //        choice('as', ','),
    //        $.expression
    //      ))
    //    )),
    //    ':',
    //    $._suite
    //  ),
    //
    // except_group_clause - comes in 3.11 ( so we need to care about this for the 3.12 upgrade )
    //
    // except_group_clause: $ => seq(
    //    'except*',
    //    seq(
    //      $.expression,
    //      optional(seq(
    //        'as',
    //        $.expression
    //      ))
    //    ),
    //    ':',
    //    $._suite
    //  ),
    //
    // finally_clause: $ => seq(
    //    'finally',
    //    ':',
    //    $._suite
    //  ),
    fn try_statement(&mut self, try_node: &Node) -> Result<StmtDesc, ParserError> {
        let mut body: Vec<Stmt> = vec![];
        let mut handlers: Vec<Excepthandler> = vec![];
        let mut orelse: Vec<Stmt> = vec![];
        let mut finalbody: Vec<Stmt> = vec![];

        let body_node = try_node
            .child_by_field_name("body")
            .expect("missing body in for statement");
        self.block(&body_node, &mut body)?;

        for child_node in try_node.named_children(&mut try_node.walk()) {
            match child_node.kind() {
                "except_clause" => {
                    let mut type__: Option<Expr> = None;
                    let mut name: Option<String> = None;
                    let mut body: Vec<Stmt> = vec![];
                    self.block(
                        &child_node
                            .child(child_node.child_count() - 1)
                            .expect("exception handler body"),
                        &mut body,
                    )?;

                    if child_node.child_count() > 3 {
                        // not just `except: ...`
                        let expr_node = &child_node.child(1).expect("expression or as_pattern");
                        let expr_type = &get_node_type(expr_node);
                        type__ = match expr_type {
                            NodeType::Production(rule) => match &rule.production_kind {
                                ProductionKind::AS_PATTERN => {
                                    let node = rule.node;
                                    let lhs_expression =
                                        node.child(0).expect("expression for exception handler");
                                    let target_expression = node
                                        .child(2)
                                        .expect("target for exception handler")
                                        .child(0)
                                        .expect("pattern target");

                                    name = Some(self.get_text(&target_expression));

                                    let lhs_expression_type = &get_node_type(&lhs_expression);
                                    Some(self.expression(lhs_expression_type)?)
                                }
                                _ => Some(self.expression(expr_type)?),
                            },
                            _ => panic!("unexpected statement handling: {:?}", expr_type),
                        };
                    }

                    handlers.push(Excepthandler::new(
                        ExcepthandlerDesc::ExceptHandler { type__, name, body },
                        &child_node,
                    ));
                }
                "except_group_clause" => panic!("except* not supported until Python 3.11"),
                "else_clause" => {
                    self.block(&child_node.child(2).expect("else body"), &mut orelse)?;
                }
                "finally_clause" => {
                    self.block(&child_node.child(2).expect("finally body"), &mut finalbody)?;
                }
                _ => (),
            }
        }

        Ok(StmtDesc::Try {
            body,
            handlers,
            orelse,
            finalbody,
        })
    }

    // while_statement: $ => seq(
    //    'while',
    //    field('condition', $.expression),
    //    ':',
    //    field('body', $._suite),
    //    optional(field('alternative', $.else_clause))
    //  ),
    fn while_statement(&mut self, for_node: &Node) -> Result<StmtDesc, ParserError> {
        let test_node = for_node
            .child_by_field_name("condition")
            .expect("missing condition in while statement");
        let test_type = get_node_type(&test_node);
        let test = self.expression(&test_type)?;

        let body_node = for_node
            .child_by_field_name("body")
            .expect("missing body in for statement");
        let mut body = vec![];
        self.block(&body_node, &mut body)?;

        let mut orelse = vec![];

        let orelse_node = for_node.child_by_field_name("alternative");
        match &orelse_node {
            Some(orelse_cont) => match &orelse_cont.child_by_field_name("body") {
                Some(body_cont) => self.block(body_cont, &mut orelse)?,
                _ => (),
            },
            _ => (),
        }

        Ok(StmtDesc::While { test, body, orelse })
    }

    // Process If StmtDesc
    //
    // if_statement: $ => seq(
    //     'if',
    //     field('condition', $.expression),
    //     ':',
    //     field('consequence', $._suite),
    //     repeat(field('alternative', $.elif_clause)),
    //     optional(field('alternative', $.else_clause))
    // ),
    fn if_statement(&mut self, if_node: &Node) -> Result<StmtDesc, ParserError> {
        let condition_node = if_node
            .child_by_field_name("condition")
            .expect("missing condition in if statement");
        let condition_type = get_node_type(&condition_node);
        let condition = self.expression(&condition_type)?;
        let block_node = if_node
            .child_by_field_name("consequence")
            .expect("missing consequence in if statement");
        let mut block = vec![];
        self.block(&block_node, &mut block)?;

        let mut elif_elses = vec![];

        for elif_or_else in if_node.children_by_field_name("alternative", &mut if_node.walk()) {
            elif_elses.push(elif_or_else);
        }

        let mut last_orelse = vec![];

        for elif_or_else in elif_elses.iter().rev() {
            match elif_or_else.child_by_field_name("body") {
                Some(else_body) => {
                    last_orelse = vec![];
                    self.block(&else_body, &mut last_orelse)?;
                }
                _ => {
                    //elif body
                    let elif_condition_node = elif_or_else
                        .child_by_field_name("condition")
                        .expect("missing condition in if statement");
                    let elif_condition_type = get_node_type(&elif_condition_node);
                    let elif_condition = self.expression(&elif_condition_type)?;

                    let elif_block_node = elif_or_else
                        .child_by_field_name("consequence")
                        .expect("missing consequence in if statement");
                    let mut elif_block = vec![];
                    self.block(&elif_block_node, &mut elif_block)?;

                    let elif_statement = Stmt::new(
                        StmtDesc::If {
                            test: elif_condition,
                            body: elif_block,
                            orelse: last_orelse,
                        },
                        elif_or_else,
                        if_node,
                    );

                    last_orelse = vec![];
                    last_orelse.push(elif_statement);
                }
            }
        }

        Ok(StmtDesc::If {
            test: condition,
            body: block,
            orelse: last_orelse,
        })
    }

    /*     seems overly complex...
      yield: $ => prec.right(seq(
      'yield',
      choice(
        seq(
          'from',
          $.expression
        ),
        optional($._expressions)
      )
    )), */
    fn yield_statement(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        //let yield_res = match node.childer

        let yield_statement = match node.child_count() {
            2 => {
                let rhs_expr = node.child(1).expect("expected yield rhs");
                let rhs_expr_type = get_node_type(&rhs_expr);
                let expr = self.expression(&rhs_expr_type)?;

                ExprDesc::Yield(Some(expr))
            }
            3 => {
                let rhs_expr = node.child(2).expect("expected yield from rhs");
                let rhs_expr_type = get_node_type(&rhs_expr);
                let expr = self.expression(&rhs_expr_type)?;

                ExprDesc::YieldFrom(expr)
            }
            _ => ExprDesc::Yield(None),
        };

        Ok(yield_statement)
    }

    /* augmented_assignment: $ => seq(
      field('left', $._left_hand_side),
      field('operator', choice(
        '+=', '-=', '*=', '/=', '@=', '//=', '%=', '**=',
        '>>=', '<<=', '&=', '^=', '|='
      )),
      field('right', $._right_hand_side)
    ), */
    fn aug_assign(&mut self, node: &Node) -> Result<StmtDesc, ParserError> {
        let target_node = node
            .child_by_field_name("left")
            .expect("missing left in aug_assign");
        let operator_node = node
            .child_by_field_name("operator")
            .expect("missing operator in aug_assign");
        let value_node = node
            .child_by_field_name("right")
            .expect("missing right in aug_assign");

        let target = self.assign_left_hand_side(&target_node)?;

        let operator_type = get_node_type(&operator_node);
        let operator = match &operator_type {
            &NodeType::AugAssignOperator(op) => Operator::from(op),
            _ => panic!("missing AugAssignOperator operator"),
        };

        let mut targets = vec![];
        let value = self.assign_right_hand_side(&value_node, &mut targets)?;

        Ok(StmtDesc::AugAssign {
            target,
            op: operator,
            value,
        })
    }

    // assignment: $ => seq(
    //     field('left', $._left_hand_side),
    //     choice(
    //       seq('=', field('right', $._right_hand_side)),
    //       seq(':', field('type', $.type)),
    //       seq(':', field('type', $.type), '=', field('right', $._right_hand_side))
    //     )
    // ),
    fn assignment(
        &mut self,
        node: &Node,
    ) -> Result<(Vec<Expr>, Option<Expr>, Option<Expr>, Option<String>, isize), ParserError> {
        let mut targets = vec![];

        let lhs = node
            .child_by_field_name("left")
            .expect("missing left hand side");

        // simple is a 'boolean integer' (what?) set to True for a Name node in target
        // that do not appear in between parenthesis and are hence pure names and not expressions.
        let simple: isize = if lhs.kind() == "identifier" { 1 } else { 0 };

        let lhs_expr = self.assign_left_hand_side(&lhs)?;

        targets.push(lhs_expr);

        // deal with types...
        let ty = None;

        let type_annot = if let Some(type_node) = node.child_by_field_name("type") {
            let type_expr_node = type_node.child(0).expect("expression of type node");
            let type_node_type = &get_node_type(&type_expr_node);
            Some(self.expression(type_node_type)?)
        } else {
            None
        };

        // get right hand side, if any
        let rhs = if let Some(rhs_node) = node.child_by_field_name("right") {
            Some(self.assign_right_hand_side(&rhs_node, &mut targets)?)
        } else {
            None
        };

        Ok((targets, type_annot, rhs, ty, simple))
    }

    // _right_hand_side: $ => choice(
    //     $.expression,
    //     $.expression_list,
    //     $.assignment,
    //     $.augmented_assignment,
    //     $.yield
    // ),
    fn assign_right_hand_side(
        &mut self,
        rhs_node: &Node,
        targets: &mut Vec<Expr>,
    ) -> Result<Expr, ParserError> {
        let expr_type = &get_node_type(rhs_node);
        let rhs = match expr_type {
            NodeType::Production(rule) => match &rule.production_kind {
                ProductionKind::ASSIGNMENT => {
                    let (mut targetsx, _type_annot, rhsx, _ty, _simple) =
                        self.assignment(rule.node)?;
                    targets.append(&mut targetsx);
                    rhsx.unwrap()
                    // deal with types...
                }
                ProductionKind::YIELD => {
                    let yield_desc = self.yield_statement(rule.node)?;
                    self.new_expr(yield_desc, rhs_node)
                }
                ProductionKind::EXPRESSION_LIST => {
                    let tuple_desc = self.tuple(rule.node)?;
                    self.new_expr(tuple_desc, rhs_node)
                }
                ProductionKind::AUGMENTED_ASSIGNMENT => {
                    panic!(
                        "assign_right_hand_side - AUGMENTED_ASSIGNMENT {:?}",
                        rule.node
                    )
                }
                //TODO: what about yeild, augmented assignment
                _ => self.expression(expr_type)?,
            },
            _ => self.expression(expr_type)?,
        };
        Ok(rhs)
    }

    // _left_hand_side: $ => choice(
    //     $.pattern,
    //     $.pattern_list,
    // ),
    // pattern_list: $ => seq(
    //     $.pattern,
    //     choice(
    //       ',',
    //       seq(
    //         repeat1(seq(
    //           ',',
    //           $.pattern
    //         )),
    //         optional(',')
    //       )
    //     )
    // ),
    fn assign_left_hand_side(&mut self, lhs: &Node) -> Result<Expr, ParserError> {
        self.set_expression_context(ExprContext::Store);
        let lhs_type = &get_node_type(lhs);
        // left hand side, assignment target
        let lhs_expr = match lhs_type {
            NodeType::Production(rule) => match &rule.production_kind {
                // we can treat pattern_list as a tuple
                ProductionKind::PATTERN_LIST => {
                    let tuple_desc = self.tuple(rule.node)?;
                    self.new_expr(tuple_desc, rule.node)
                }
                _ => self.pattern(lhs_type)?,
            },
            _ => panic!("unexpected assignment lhs {:?}", lhs),
        };
        self.pop_expression_context();
        Ok(lhs_expr)
    }

    // pattern: $ => choice(
    //     $.identifier,
    //     alias('match', $.identifier), // ambiguity with match statement: only ":" at end of line decides if "match" keyword
    //     $.keyword_identifier,
    //     $.subscript,
    //     $.attribute,
    //     $.list_splat_pattern,
    //     $.tuple_pattern,
    //     $.list_pattern
    // ),
    fn pattern(&mut self, node_type: &NodeType) -> Result<Expr, ParserError> {
        let expr: Expr = match &node_type {
            NodeType::Production(rule) => match &rule.production_kind {
                ProductionKind::IDENTIFIER => {
                    let name_desc = self.name(self.get_text(rule.node));
                    self.new_expr(name_desc, rule.node)
                }
                ProductionKind::KEYWORD_IDENTIFIER => {
                    panic!("pattern - KEYWORD_IDENTIFIER {:?}", rule.node)
                }
                ProductionKind::LIST_PATTERN => {
                    let list_pat_desc = self.list_pattern(rule.node)?;
                    self.new_expr(list_pat_desc, rule.node)
                }
                ProductionKind::TUPLE_PATTERN => {
                    if rule.node.child_count() == 3 {
                        // if single item in tuple, unwrap this and teat as individual item
                        let expr_node = &rule.node.child(1).unwrap();
                        let expr_type = &get_node_type(expr_node);
                        self.expression(expr_type)?
                    } else {
                        let tuple_desc = self.tuple(rule.node)?;
                        self.new_expr(tuple_desc, rule.node)
                    }
                }
                ProductionKind::LIST_SPLAT_PATTERN => self.list_splat_pattern(node_type)?,
                _ => self.expression(node_type)?,
            },
            _ => panic!("unexpected assignment lhs {:?}", node_type),
        };

        Ok(expr)
    }

    /*list_splat_pattern: $ => seq(
        '*',
        choice($.identifier, $.keyword_identifier, $.subscript, $.attribute)
      ),
    */
    fn list_splat_pattern(&mut self, node_type: &NodeType) -> Result<Expr, ParserError> {
        let expr: Expr = match &node_type {
            NodeType::Production(rule) => match &rule.production_kind {
                ProductionKind::IDENTIFIER => {
                    let text_desc = self.name(self.get_text(rule.node));
                    self.new_expr(text_desc, rule.node)
                }
                ProductionKind::KEYWORD_IDENTIFIER => {
                    panic!("pattern - KEYWORD_IDENTIFIER {:?}", rule.node)
                }
                ProductionKind::ATTRIBUTE => {
                    let attribute_desc = self.attribute(rule.node)?;
                    self.new_expr(attribute_desc, rule.node)
                }
                _ => self.expression(node_type)?,
            },
            _ => panic!("unexpected assignment lhs {:?}", node_type),
        };

        Ok(expr)
    }

    fn list_pattern(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        self.list(node)
    }

    // Process an ExprDesc.
    // expression: $ => choice(
    //     $.comparison_operator,
    //     $.not_operator,
    //     $.boolean_operator,
    //     $.await,
    //     $.lambda,
    //     $.primary_expression,
    //     $.conditional_expression,
    //     $.named_expression,
    //     $.as_pattern
    //   ),
    fn expression(&mut self, node: &NodeType) -> Result<Expr, ParserError> {
        use ProductionKind::*;

        let expr = match node {
            NodeType::Production(rule) => match &rule.production_kind {
                COMPARISON_OPERATOR => {
                    let comparison_op_desc = self.comparison_operator(rule.node)?;
                    self.new_expr(comparison_op_desc, rule.node)
                }
                NOT_OPERATOR => {
                    let not_op_desc = self.not_operator(rule.node)?;
                    self.new_expr(not_op_desc, rule.node)
                }
                BOOLEAN_OPERATOR => {
                    let bool_op_desc = self.bool_op(rule.node)?;
                    self.new_expr(bool_op_desc, rule.node)
                }
                AWAIT => {
                    let await_desc = self.await_expr(rule.node)?;
                    self.new_expr(await_desc, rule.node)
                }
                LAMBDA => {
                    let lambda_desc = self.lambda(rule.node)?;
                    self.new_expr(lambda_desc, rule.node)
                }
                CONDITIONAL_EXPRESSION => {
                    let if_desc = self.if_exp(rule.node)?;
                    self.new_expr(if_desc, rule.node)
                }
                NAMED_EXPRESSION => {
                    let named_desc = self.named_expression(rule.node)?;
                    self.new_expr(named_desc, rule.node)
                }
                AS_PATTERN => panic!(
                    "AS_PATTERN not expected to be handled at expression level {:?}",
                    rule.node
                ),
                _ => self.primary_expression(node, rule.node)?,
            },
            _ => panic!("unexpected statement handling: {:?}", node), // TODO: needs better handle
        };
        Ok(expr)
    }

    // Process a Primary ExprDesc
    // primary_expression: $ => choice(
    //     $.binary_operator,
    //     $.identifier,
    //     alias("match", $.identifier),
    //     $.keyword_identifier,
    //     $.string,
    //     $.concatenated_string,
    //     $.integer,
    //     $.float,
    //     $.true,
    //     $.false,
    //     $.none,
    //     $.unary_operator,
    //     $.attribute,
    //     $.subscript,
    //     $.call,
    //     $.list,
    //     $.list_comprehension,
    //     $.dictionary,
    //     $.dictionary_comprehension,
    //     $.set,
    //     $.set_comprehension,
    //     $.tuple,
    //     $.parenthesized_expression,
    //     $.generator_expression,
    //     $.ellipsis
    // ),
    fn primary_expression(
        &mut self,
        node_type: &NodeType,
        node: &Node,
    ) -> Result<Expr, ParserError> {
        use ProductionKind::*;

        let exprdesc: ExprDesc = match node_type {
            NodeType::Production(rule) => match &rule.production_kind {
                BINARY_OPERATOR => self.binary_op(rule.node)?,
                // TODO: soft keywords like `match` and that story with python and tree-sitter
                IDENTIFIER => self.name(self.get_text(rule.node)),
                KEYWORD_IDENTIFIER => self.name(self.get_text(rule.node)),
                STRING => self.raw_string(rule.node, rule.node)?,
                CONCATENATED_STRING => self.concatenated_string(rule.node)?,
                INTEGER => self.integer(self.get_text(rule.node)),
                FLOAT => self.float(self.get_text(rule.node)),
                TRUE => self.constant(ConstantDesc::Bool(true)),
                FALSE => self.constant(ConstantDesc::Bool(false)),
                NONE => self.none(),
                ELLIPSIS => self.constant(ConstantDesc::Ellipsis),
                PARENTHESIZED_EXPRESSION => {
                    let child = rule.node.named_child(0).ok_or(ParserError::MissingChild)?;
                    let child_type = get_node_type(&child);
                    return self.expression(&child_type);
                }
                ATTRIBUTE => self.attribute(rule.node)?,
                CALL => self.call(rule.node)?,
                LIST => self.list(rule.node)?,
                TUPLE => self.tuple(rule.node)?,
                SET => self.set(rule.node)?,
                DICTIONARY => self.dict(rule.node)?,
                UNARY_OPERATOR => self.unary_op(rule.node)?,
                LIST_COMPREHENSION => self.list_comp(rule.node)?,
                SET_COMPREHENSION => self.set_comp(rule.node)?,
                GENERATOR_EXPRESSION => self.generator_expr(rule.node)?,
                DICTIONARY_COMPREHENSION => self.dict_comp(rule.node)?,
                LIST_SPLAT_PATTERN => self.starred(rule.node)?,
                SUBSCRIPT => self.subscript(rule.node)?,
                _ => panic!("unexpected token: {:?}", node),
            },
            _ => panic!("unexpected statement handling: {:?}", node),
        };
        Ok(self.new_expr(exprdesc, node))
    }

    /* named_expression: $ => seq(
        field('name', $._named_expresssion_lhs),
        ':=',
        field('value', $.expression)
      ),
    */
    fn named_expression(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let target_node = &node
            .child_by_field_name("name")
            .expect("named_expression missing name field");
        let target_type = get_node_type(target_node);

        self.set_expression_context(ExprContext::Store);
        let target = self.expression(&target_type)?;
        self.pop_expression_context();

        let value_node = &node
            .child_by_field_name("value")
            .expect("named_expression missing value field");
        let value_type = get_node_type(value_node);
        let value = self.expression(&value_type)?;

        Ok(ExprDesc::NamedExpr { target, value })
    }

    // list_comprehension: $ => seq(
    //   '[',
    //   field('body', $.expression),
    //   $._comprehension_clauses,
    //   ']'
    // ),
    //     set_comprehension: $ => seq(
    //   '{',
    //   field('body', $.expression),
    //   $._comprehension_clauses,
    //   '}'
    // ),

    // generator_expression: $ => seq(
    //   '(',
    //   field('body', $.expression),
    //   $._comprehension_clauses,
    //   ')'
    // ),
    fn list_comp(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let mut generators = vec![];
        let elt = self.comprehension_core(node, &mut generators)?;

        Ok(ExprDesc::ListComp { elt, generators })
    }

    fn set_comp(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let mut generators = vec![];
        let elt = self.comprehension_core(node, &mut generators)?;
        Ok(ExprDesc::SetComp { elt, generators })
    }

    fn generator_expr(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let mut generators = vec![];
        let elt = self.comprehension_core(node, &mut generators)?;
        Ok(ExprDesc::GeneratorExp { elt, generators })
    }

    fn dict_comp(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let mut generators = vec![];
        let (key, value) = self.dict_pair(node, &mut generators)?;

        Ok(ExprDesc::DictComp {
            key,
            value,
            generators,
        })
    }

    fn dict_pair(
        &mut self,
        node: &Node,
        generators: &mut Vec<Comprehension>,
    ) -> Result<(Expr, Expr), ParserError> {
        //let elt =
        let pair_node = node
            .child_by_field_name("body")
            .expect("missing pair in dict_comp");

        let key_node = pair_node
            .child_by_field_name("key")
            .expect("missing key in pair node of dict");
        let key_node_type = get_node_type(&key_node);
        let key = self.expression(&key_node_type)?;

        let value_node = pair_node
            .child_by_field_name("value")
            .expect("missing value in pair node of dict");
        let value_node_type = get_node_type(&value_node);
        let value = self.expression(&value_node_type)?;

        self.comprehension_core_gennerator(node, generators)?;
        Ok((key, value))
    }

    fn comprehension_core(
        &mut self,
        node: &Node,
        generators: &mut Vec<Comprehension>,
    ) -> Result<Expr, ParserError> {
        let body_node = node
            .child_by_field_name("body")
            .expect("missing body in comprehension");
        let body_node_type = get_node_type(&body_node);
        let elt = self.expression(&body_node_type)?;

        self.comprehension_core_gennerator(node, generators)?;
        Ok(elt)
    }

    fn comprehension_core_gennerator(
        &mut self,
        node: &Node,
        generators: &mut Vec<Comprehension>,
    ) -> Result<(), ParserError> {
        for child_node in node.named_children(&mut node.walk()) {
            //_comprehension_clauses
            let child_type = &get_node_type(&child_node);
            match child_type {
                // for_in_clause
                NodeType::Production(prod) => match prod.production_kind {
                    ProductionKind::COMPREHENSION => {
                        let comp = self.comprehension_clause(&child_node)?;
                        generators.push(comp);
                    }
                    ProductionKind::IF_CLAUSE => {
                        let expr = self.if_clause(&child_node)?;
                        generators.last_mut().unwrap().ifs.push(expr);
                    }
                    _ => (),
                },
                _ => (), // skip other nodes
            }
        }
        Ok(())
    }

    // _comprehension_clauses: $ => seq(
    //  $.for_in_clause,
    //  repeat(choice(
    //    $.for_in_clause,
    //    $.if_clause
    //  ))
    // for_in_clause: $ => prec.left(seq(
    //    optional('async'),
    //    'for',
    //   field('left', $._left_hand_side),
    //    'in',
    //    field('right', commaSep1($._expression_within_for_in_clause)),
    //    optional(',')
    //  )),
    //    if_clause: $ => seq(
    //    'if',
    //    $.expression
    //  ),
    //),
    fn comprehension_clause(&mut self, node: &Node) -> Result<Comprehension, ParserError> {
        let left_node = &node
            .child_by_field_name("left")
            .expect("comprehension_clause missing left field");
        let left_type = get_node_type(left_node);

        let right_node = &node
            .child_by_field_name("right")
            .expect("comprehension_clause missing right field");
        let right_type = get_node_type(right_node);

        self.set_expression_context(ExprContext::Store);
        let target = self.expression(&left_type)?;
        self.pop_expression_context();

        self.set_expression_context(ExprContext::Load);
        let iter = self.expression(&right_type)?;
        self.pop_expression_context();

        let ifs = vec![];

        Ok(Comprehension {
            target,
            iter,
            ifs,
            is_async: node.child(0).unwrap().kind().eq("async"),
        })
    }

    fn if_clause(&mut self, node: &Node) -> Result<Expr, ParserError> {
        let expr_node = &node.child(1).expect("if_clause missing expression");
        let expr_type = get_node_type(expr_node);

        self.expression(&expr_type)
    }

    //
    // Process Binary Operators
    //
    // binary_operator: $ => {
    //     const table = [
    //       [prec.left, '+', PREC.plus],
    //       [prec.left, '-', PREC.plus],
    //       [prec.left, '*', PREC.times],
    //       [prec.left, '@', PREC.times],
    //       [prec.left, '/', PREC.times],
    //       [prec.left, '%', PREC.times],
    //       [prec.left, '//', PREC.times],
    //       [prec.right, '**', PREC.power],
    //       [prec.left, '|', PREC.bitwise_or],
    //       [prec.left, '&', PREC.bitwise_and],
    //       [prec.left, '^', PREC.xor],
    //       [prec.left, '<<', PREC.shift],
    //       [prec.left, '>>', PREC.shift],
    //     ];
    //     return choice(...table.map(([fn, operator, precedence]) => fn(precedence, seq(
    //       field('left', $.primary_expression),
    //       field('operator', operator),
    //       field('right', $.primary_expression)
    //     ))));
    // },
    fn binary_op(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let lhs_node = node
            .child_by_field_name("left")
            .expect("missing lhs in binary op");
        let lhs_type = get_node_type(&lhs_node);
        let left = self.expression(&lhs_type)?;
        let operator_node = node
            .child_by_field_name("operator")
            .expect("missing operator in binary op");
        let operator = match get_node_type(&operator_node) {
            NodeType::BinaryOperator(op) => Operator::try_from(op)
                .expect("expected NodeType::BinaryOperator to have valid binary operator"),
            _ => return Err(ParserError::MissingOperator(operator_node.kind().into())),
        };
        let rhs_node = node
            .child_by_field_name("right")
            .expect("missing rhs in binary op");
        let rhs_type = get_node_type(&rhs_node);
        let right = self.expression(&rhs_type)?;

        Ok(ExprDesc::BinOp {
            left,
            op: operator,
            right,
        })
    }

    // Process Attribute
    //
    // attribute: $ => prec(PREC.call, seq(
    //     field('object', $.primary_expression),
    //     '.',
    //     field('attribute', $.identifier)
    // )),
    fn attribute(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let lhs = node
            .child_by_field_name("object")
            .expect("missing left hand side (attribute.object)");
        let lhs_type = get_node_type(&lhs);
        self.set_expression_context(ExprContext::Load);
        let value = self.primary_expression(&lhs_type, &lhs)?;
        self.pop_expression_context();
        let rhs = node
            .child_by_field_name("attribute")
            .expect("missing right hand side (attribute.attribute)");
        let attr = self.get_text(&rhs);

        Ok(ExprDesc::Attribute {
            value,
            attr,
            ctx: self.get_expression_context(),
        })
    }

    fn set_expression_context(&mut self, ctx: ExprContext) {
        self.current_expr_ctx.push(Some(ctx));
    }

    fn pop_expression_context(&mut self) {
        self.current_expr_ctx.pop();
    }

    fn get_expression_context(&mut self) -> ExprContext {
        match self.current_expr_ctx.last() {
            Some(None) => ExprContext::Load,
            Some(not_none) => match not_none {
                Some(ExprContext::Store) => ExprContext::Store,
                Some(ExprContext::Del) => ExprContext::Del,
                _ => ExprContext::Load,
            },
            _ => ExprContext::Load,
        }
    }

    fn primary_expression_sequence(
        &mut self,
        node: &Node,
        exp_list: &mut Vec<Expr>,
    ) -> Result<(), ParserError> {
        for child in node.named_children(&mut node.walk()) {
            let child_type = get_node_type(&child);
            let arg = self.expression(&child_type)?;
            exp_list.push(arg);
        }
        Ok(())
    }

    //Process List expression
    fn list(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let mut expressions = vec![];
        self.primary_expression_sequence(node, &mut expressions)?;

        Ok(ExprDesc::List {
            elts: expressions,
            ctx: self.get_expression_context(),
        })
    }

    //Process Tuple expression
    fn tuple(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let mut expressions = vec![];
        self.primary_expression_sequence(node, &mut expressions)?;

        if expressions.len() == 1 && node.child(node.child_count() - 2).unwrap().kind() != "," {
            // if only one and there is no comma
            return Ok(*expressions.pop().unwrap().desc);
        }

        Ok(ExprDesc::Tuple {
            elts: expressions,
            ctx: self.get_expression_context(),
        })
    }

    //Process Set expression
    fn set(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let mut expressions = vec![];
        self.primary_expression_sequence(node, &mut expressions)?;

        Ok(ExprDesc::Set(expressions))
    }

    //Process Set expression
    fn if_exp(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let body_node = node.child(0).expect("if_exp missing body");
        let body_node_type = get_node_type(&body_node);
        let body = self.expression(&body_node_type)?;

        let test_node = node.child(2).expect("if_exp missing test");
        let test_node_type = get_node_type(&test_node);
        let test = self.expression(&test_node_type)?;

        let orelse_node = node.child(4).expect("if_exp missing orelse");
        let orelse_node_type = get_node_type(&orelse_node);
        let orelse = self.expression(&orelse_node_type)?;

        Ok(ExprDesc::IfExp { test, body, orelse })
    }

    //Process Dict expression
    fn dict(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let mut keys = vec![];
        let mut values = vec![];

        for pair in node.named_children(&mut node.walk()) {
            let pair_type = get_node_type(&pair);
            match &pair_type {
                NodeType::Production(param) => match &param.production_kind {
                    ProductionKind::PAIR => {
                        {
                            let key = pair.child(0).ok_or(ParserError::MissingChild)?;

                            let key_type = get_node_type(&key);
                            let keyx = self.expression(&key_type)?;
                            keys.push(keyx);
                        }

                        {
                            let value = pair.child(2).ok_or(ParserError::MissingChild)?;

                            let value_type = get_node_type(&value);
                            let valuex = self.expression(&value_type)?;
                            values.push(valuex);
                        }
                    }
                    _ => panic!("unexpected dict production {:?}", param),
                },
                _ => (),
            }
        }

        Ok(ExprDesc::Dict { keys, values })
    }

    // Process Call
    //
    // call: $ => prec(PREC.call, seq(
    //     field('function', $.primary_expression),
    //     field('arguments', choice(
    //       $.generator_expression,
    //       $.argument_list
    //     ))
    // )),
    fn call(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let function = node
            .child_by_field_name("function")
            .expect("missing function in call");
        let function_type = get_node_type(&function);
        let func = self.expression(&function_type)?;
        let args_node = node
            .child_by_field_name("arguments")
            .expect("missing arguments in call");
        let mut args = vec![];
        let mut keywords = vec![];
        self.argument_list(&args_node, &mut args, &mut keywords)?;

        Ok(ExprDesc::Call {
            func,
            args,
            keywords,
        })
    }

    // Process Argument List
    //
    // argument_list: $ => seq(
    //     '(',
    //     optional(commaSep1(
    //       choice(
    //         $.expression,
    //         $.list_splat,
    //         $.dictionary_splat,
    //         alias($.parenthesized_list_splat, $.parenthesized_expression),
    //         $.keyword_argument
    //       )
    //     )),
    //     optional(','),
    //     ')'
    // ),
    fn argument_list(
        &mut self,
        node: &Node,
        arg_list: &mut Vec<Expr>,
        keyword_list: &mut Vec<AstKeyword>,
    ) -> Result<(), ParserError> {
        use ProductionKind::*;

        for child in node.named_children(&mut node.walk()) {
            let child_type = get_node_type(&child);

            match &child_type {
                NodeType::Production(rule) => match &rule.production_kind {
                    //TODO: alias($.parenthesized_list_splat, $.parenthesized_expression), - what does this resolve to?
                    LIST_SPLAT => {
                        let starred = self.starred(&child)?;
                        arg_list.push(self.new_expr(starred, &child));
                    }
                    KEYWORD_ARGUMENT => {
                        let keywordarg = self.keyword_argument(&child)?;
                        keyword_list.push(keywordarg);
                    }
                    DICTIONARY_SPLAT => {
                        let keywordarg = self.dictionary_splat(&child)?;
                        keyword_list.push(keywordarg);
                    }
                    _ => {
                        let expr = self.expression(&child_type)?;
                        arg_list.push(expr);
                    }
                },
                _ => panic!("unexpected argument handling: {:?}", child),
            };
        }
        Ok(())
    }

    // list_splat: $ => seq(
    //  '*',
    //  $.expression,
    // ),
    fn starred(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let identifier = node.child(1).expect("missing identifier in starred");

        let ident_type = get_node_type(&identifier);
        let value = self.expression(&ident_type)?;

        Ok(ExprDesc::Starred {
            value,
            ctx: self.get_expression_context(),
        })
    }
    //    subscript: $ => prec(PREC.call, seq(
    //    field('value', $.primary_expression),
    //    '[',
    //    commaSep1(field('subscript', choice($.expression, $.slice))),
    //    optional(','),
    //    ']'
    //  )),
    //
    //  slice: $ => seq(
    //    optional($.expression),
    //    ':',
    //    optional($.expression),
    //    optional(seq(':', optional($.expression)))
    //  ),
    fn subscript(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let value_node = node
            .child_by_field_name("value")
            .expect("value field in subscript");
        let value_type = get_node_type(&value_node);

        // subscripts are always loaded, even if they are on the lhs of an assignment operation
        self.set_expression_context(ExprContext::Load);
        let value = self.expression(&value_type)?;
        self.pop_expression_context();

        // if many slices, then wrapped inside a Tuple, otherwise slice on its own if only one
        let mut slices: Vec<Expr> = vec![];

        for subscript_node in node.children_by_field_name("subscript", &mut node.walk()) {
            let mut slice_elements: Vec<Option<Expr>> = vec![];

            let mut last_expr: Option<Expr> = None;

            if subscript_node.kind() == "slice" {
                for slice_child in subscript_node.children(&mut subscript_node.walk()) {
                    // if : or something else
                    let token = self.get_text(&slice_child);
                    if token == ":" {
                        slice_elements.push(last_expr);
                        last_expr = None;
                    } else {
                        let slice_child_type = get_node_type(&slice_child);
                        last_expr = Some(self.expression(&slice_child_type)?);
                    }
                }
                slice_elements.push(last_expr);

                slices.push(self.new_expr(
                    ExprDesc::Slice {
                        lower: slice_elements.remove(0),
                        upper: {
                            if slice_elements.is_empty() {
                                None
                            } else {
                                slice_elements.remove(0)
                            }
                        },
                        step: {
                            if slice_elements.is_empty() {
                                None
                            } else {
                                slice_elements.remove(0)
                            }
                        },
                    },
                    &subscript_node,
                ));
            } else {
                // single expression
                let subscript_node_type = get_node_type(&subscript_node);
                slices.push(self.expression(&subscript_node_type)?);
            }
        }

        let slice = match slices.len() {
            1 => slices.pop().expect("should be at least one slice"),
            _ => {
                let start_position = node.child(1).expect("'[' node in subscript").end_position();

                let end_position = node
                    .child(node.child_count() - 2)
                    .expect("']' node in subscript")
                    .end_position();

                Expr::new(
                    ExprDesc::Tuple {
                        elts: slices,
                        ctx: self.get_expression_context(),
                    },
                    start_position.row as isize + 1,
                    start_position.column as isize + self.inc_expr_col_offset,
                    end_position.row as isize + 1,
                    end_position.column as isize + self.inc_expr_col_offset,
                )
            }
        };

        Ok(ExprDesc::Subscript {
            value,
            slice,
            ctx: self.get_expression_context(),
        })
    }

    // dictionary_splat: $ => seq(
    //  '**',
    //  $.expression
    // ),
    fn dictionary_splat(&mut self, node: &Node) -> Result<AstKeyword, ParserError> {
        let identifier = node
            .child(1)
            .expect("missing identifier in dictionary_splat");

        let identifier_type = get_node_type(&identifier);
        let value = self.expression(&identifier_type)?;

        //Ok(Box::new(DictionaryFuncArg::new(
        Ok(AstKeyword::new(None, value, node))
    }

    // keyword_argument: $ => seq(
    //  field('name', choice($.identifier, $.keyword_identifier, alias("match", $.identifier))),
    //  '=',
    //  field('value', $.expression)
    // ),
    fn keyword_argument(&mut self, node: &Node) -> Result<AstKeyword, ParserError> {
        let lhs = node
            .child_by_field_name("name")
            .expect("missing lhs in keyword_argument");
        let arg = self.get_text(&lhs);

        let rhs = node
            .child_by_field_name("value")
            .expect("missing rhs in keyword_argument");

        let rhs_type = get_node_type(&rhs);
        let value = self.expression(&rhs_type)?;

        //Ok(Box::new(DictionaryFuncArg::new(
        Ok(AstKeyword::new(Some(arg), value, node))
    }

    // Process a Comparison Operator
    // comparison_operator: $ => prec.left(PREC.compare, seq(
    //     $.primary_expression,
    //     repeat1(seq(
    //       field('operators',
    //         choice(
    //           '<',
    //           '<=',
    //           '==',
    //           '!=',
    //           '>=',
    //           '>',
    //           '<>',
    //           'in',
    //           seq('not', 'in'),
    //           'is',
    //           seq('is', 'not')
    //         )),
    //       $.primary_expression
    //     ))
    // )),
    fn comparison_operator(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        // we have to do some hoo haa re skipping nodes and reading ahead to accommodate the
        // fact that `is not` and `not in` are represented as two separate sets of nodes in the cst

        let mut left = None;
        let mut ops = vec![];
        let mut comparators = vec![];

        // we need to examine more than one item so in a vector is needed
        let mut all_items = vec![];

        for child in node.children(&mut node.walk()) {
            all_items.push(child);
        }
        let mut next_itr = all_items.iter();
        next_itr.next();
        let mut skip_next = false;
        for child in all_items.iter() {
            let next_child_type = next_itr.next().map(get_node_type);
            if skip_next {
                skip_next = false;
                continue;
            }
            let child_type = &get_node_type(child);
            match child_type {
                NodeType::Production(_) => match left {
                    // comparitor
                    None => left = Some(self.primary_expression(child_type, child)?),
                    Some(_) => comparators.push(self.primary_expression(child_type, child)?),
                },
                _ => {
                    // must be an operator
                    if let Some(cmp_operator) = get_comp_op(child_type, next_child_type) {
                        if cmp_operator == Cmpop::NotIn {
                            skip_next = true;
                        }

                        ops.push(cmp_operator);
                    }
                }
            }
        }

        Ok(ExprDesc::Compare {
            left: left.ok_or(ParserError::MissingLhs)?,
            ops,
            comparators,
        })
    }

    // not_operator: $ => prec(PREC.not, seq(
    //     'not',
    //     field('argument', $.expression)
    // )),
    fn not_operator(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let arg = node
            .child_by_field_name("argument")
            .expect("missing argument in not operator");
        let arg_type = get_node_type(&arg);
        let operand = self.expression(&arg_type)?;

        Ok(ExprDesc::UnaryOp {
            op: Unaryop::Not,
            operand,
        })
    }
    //await: $ => prec(PREC.unary, seq(
    //   'await',
    //  $.expression
    //)),
    fn await_expr(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let arg = node.child(1).expect("missing argument in await");
        let arg_type = get_node_type(&arg);
        let arg = self.expression(&arg_type)?;

        Ok(ExprDesc::Await(arg))
    }

    // lambda: $ => prec(PREC.lambda, seq(
    //   'lambda',
    //   field('parameters', optional($.lambda_parameters)),
    //   ':',
    //   field('body', $.expression)
    // )),
    fn lambda(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let params_node = node
            .child_by_field_name("parameters")
            .expect("missing parameters in lambda");
        let args = self.get_parameters(&params_node)?;

        let body_node = node
            .child_by_field_name("body")
            .expect("missing body in lambda");
        let body_type = get_node_type(&body_node);
        let body = self.expression(&body_type)?;

        Ok(ExprDesc::Lambda { args, body })
    }

    // boolean_operator: $ => choice(
    //    prec.left(PREC.and, seq(
    //      field('left', $.expression),
    //      field('operator', 'and'),
    //      field('right', $.expression)
    //    )),
    //    prec.left(PREC.or, seq(
    //      field('left', $.expression),
    //      field('operator', 'or'),
    //      field('right', $.expression)
    //    ))
    //  ),
    fn bool_op(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let op_node = node
            .child_by_field_name("operator")
            .expect("missing operator in unary operator");
        let op_type = get_node_type(&op_node);
        let operator = match op_type {
            NodeType::Keyword(Keyword::AND) => Boolop::And,
            NodeType::Keyword(Keyword::OR) => Boolop::Or,
            _ => panic!("unexpected boolean operator node {:?}", op_type),
        };

        let mut values: Vec<Expr> = vec![];

        values.push(
            self.expression(&get_node_type(
                &node
                    .child_by_field_name("left")
                    .expect("missing left in boolean_operator"),
            ))?,
        );

        values.push(
            self.expression(&get_node_type(
                &node
                    .child_by_field_name("right")
                    .expect("missing right in boolean_operator"),
            ))?,
        );

        Ok(ExprDesc::BoolOp {
            op: operator,
            values,
        })
    }

    // unary_operator: $ => prec(PREC.unary, seq(
    //  field('operator', choice('+', '-', '~')),
    //  field('argument', $.primary_expression)
    // )),
    fn unary_op(&mut self, node: &Node) -> Result<ExprDesc, ParserError> {
        let operator_node = node
            .child_by_field_name("operator")
            .expect("missing operator in unary operator");
        let operator_type = get_node_type(&operator_node);
        let operator = match operator_type {
            NodeType::BinaryOperator(BinaryOperator::MINUS) => Unaryop::USub,
            NodeType::BinaryOperator(BinaryOperator::PLUS) => Unaryop::UAdd,
            NodeType::BinaryOperator(BinaryOperator::TILDE) => Unaryop::Invert,
            _ => panic!("unexpected unary operator node {:?}", operator_type),
        };

        let arg = node
            .child_by_field_name("argument")
            .expect("missing argument in not operator");
        let arg_type = get_node_type(&arg);
        let operand = self.primary_expression(&arg_type, &arg)?;

        Ok(ExprDesc::UnaryOp {
            op: operator,
            operand,
        })
    }

    //
    //
    // AST node constructors
    //
    //

    fn none(&mut self) -> ExprDesc {
        ExprDesc::Constant {
            value: None,
            kind: None,
        }
    }

    fn constant(&mut self, const_value: ConstantDesc) -> ExprDesc {
        ExprDesc::Constant {
            value: Some(const_value),
            kind: None,
        }
    }

    /// replace all {{ with { and }} with }
    fn tidy_double_braces(&mut self, from_string: String) -> String {
        from_string.replace("{{", "{").replace("}}", "}")
    }

    // string: $ => seq(
    //  alias($._string_start, '"'),
    //  repeat(choice($.interpolation, $._escape_interpolation, $.escape_sequence, $._not_escape_sequence, $._string_content)),
    //  alias($._string_end, '"')
    // ),

    // interpolation: $ => seq(
    //  '{',
    //  $.expression,
    //  optional('='),
    //  optional($.type_conversion),
    //  optional($.format_specifier),
    //  '}'
    // ),
    // origin_node will be different from format_node where the format string exists within
    // a concatenated string
    fn format_string(
        &mut self,
        format_node: &Node,
        origin_node: &Node,
    ) -> Result<ExprDesc, ParserError> {
        let mut expressions: Vec<Expr> = vec![];
        let mut node_text = format_node
            .utf8_text(self.code.as_bytes())
            .expect("Invalid node text")
            .to_string();

        let apostrophe_or_quote = node_text[1..2].to_string();
        let mut multiline_offsets = HashMap::new();
        let base_row = format_node.start_position().row;
        let base_col = format_node.start_position().column;

        let mut prev_idx = 2;

        let is_multiline = if node_text.starts_with("f\"\"\"") || node_text.starts_with("f\'\'\'") {
            // multiline f strings are interesting and require some giggling around so
            // that we can consistantly extract substring strings from the string.
            // Essnetially we must:
            // Offset 2 extra chars off start of String (""" is 2 more chars wider than ")
            // we also need to remove newlines and do some offset calculations
            // keep track of column offsets on a per line basis
            let mut cur_row = base_row;
            multiline_offsets.insert(cur_row, 0);
            // move chars across one at a time and update offsets as approperiate
            let mut new_node_text = String::from("");
            for ch in node_text.chars() {
                if ch == '\n' {
                    new_node_text.push('\\');
                    new_node_text.push('n');
                    cur_row += 1;
                    multiline_offsets.insert(cur_row, new_node_text.len());
                } else {
                    new_node_text.push(ch);
                }
            }
            node_text = new_node_text;
            prev_idx += 2;

            true
        } else {
            false
        };

        let mut has_interpolation_nodes = false;

        for interpolation_node in format_node.named_children(&mut format_node.walk()) {
            //walk all interpolated nodes and
            // push each one to expressions as FormattedValue's
            // push any intervening string chunks to expressions as strings
            if interpolation_node.kind() == "interpolation" {
                has_interpolation_nodes = true;
                let mut start_col = interpolation_node.start_position().column - base_col;
                let mut end_col = interpolation_node.end_position().column - base_col;

                if is_multiline {
                    // if multiline, we need line column offset adjustment
                    // might be a CPython bug
                    let start_row = interpolation_node.start_position().row;
                    start_col += multiline_offsets.get(&start_row).unwrap();
                    end_col += multiline_offsets
                        .get(&interpolation_node.end_position().row)
                        .unwrap();
                }

                if start_col > prev_idx {
                    // indicates that there is a string at one of the following two locations
                    // start of the f-string before the first {} (formatted value)
                    // in between two {}'s
                    // strings after the last {} are handled after iterating through
                    //the interpolation nodes
                    let tidy_braces =
                        self.tidy_double_braces(node_text[prev_idx..start_col].to_string());
                    let string_desc = self.process_string(format!(
                        "{}{}{}",
                        apostrophe_or_quote, tidy_braces, apostrophe_or_quote
                    ));
                    expressions.push(self.new_expr(string_desc, origin_node));
                }

                // add next FormattedValue corresponding to {} region
                let interpolation_expression = interpolation_node
                    .child(1)
                    .expect("expression node of interpolation node");
                let interpolation_type = get_node_type(&interpolation_expression);

                let value =
                    if is_multiline && interpolation_expression.start_position().row > base_row {
                        // potential CPython bug here, column offsets for interpolation nodes for
                        // nodes on the nth (where n>0) line are off by one, so we must correct them
                        let prev_offset = self.inc_expr_col_offset;
                        self.inc_expr_col_offset = 1;
                        let expr_node = self.expression(&interpolation_type)?;
                        self.inc_expr_col_offset = prev_offset;
                        expr_node
                    } else {
                        self.expression(&interpolation_type)?
                    };

                let mut format_spec: Option<Expr> = None;
                let mut conversion: Option<isize> = Some(-1);

                // format_specifier and/or type_conversion may be specified for interpolation_node
                self.extract_interpolation_node_optionals(
                    &interpolation_node,
                    origin_node,
                    &mut format_spec,
                    &mut conversion,
                );

                expressions.push(self.new_expr(
                    ExprDesc::FormattedValue {
                        value,
                        conversion,
                        format_spec,
                    },
                    origin_node,
                ));

                prev_idx = end_col;
            }
        }

        let mut adjusted_node_text_len = node_text.chars().count() - 1;
        if is_multiline {
            // the characters used to demarcate the end of the string are
            // two characters wider, so we take 2 away: """ vs "
            adjusted_node_text_len -= 2;
        }

        if adjusted_node_text_len > prev_idx {
            let expr = if has_interpolation_nodes {
                // add remainder of string as node at end of format string
                let tidy_braces = self
                    .tidy_double_braces(node_text[prev_idx..adjusted_node_text_len].to_string());
                let string_desc = self.process_string(format!(
                    "{}{}{}",
                    apostrophe_or_quote, tidy_braces, apostrophe_or_quote
                ));
                self.new_expr(string_desc, origin_node)
            } else {
                // no interpolation nodes, just treat as normal string and cut of f from start
                let tidy_braces = self.tidy_double_braces(node_text[1..].to_string());
                let string_desc = self.process_string(tidy_braces);
                self.new_expr(string_desc, origin_node)
            };

            expressions.push(expr);
        }

        Ok(ExprDesc::JoinedStr(expressions))
    }

    /// Interpolation nodes can contain:
    /// a conversion is an integer:
    /// * -1: no formatting
    /// * 115: !s string formatting
    /// * 114: !r repr formatting
    /// * 97: !a ascii formatting
    /// format_spec is a JoinedStr node representing the formatting of the value.
    ///  Both conversion and format_spec can be set at the same time.
    fn extract_interpolation_node_optionals(
        &mut self,
        interpolation_node: &Node,
        origin_node: &Node,
        format_spec: &mut Option<Expr>,
        conversion: &mut Option<isize>,
    ) {
        let interpolation_node_count = interpolation_node.child_count();
        if interpolation_node_count > 3 {
            for node_id in 2..(interpolation_node_count - 1) {
                let interpolation_component_node = &interpolation_node
                    .child(node_id)
                    .expect("interpolation_node child");
                match interpolation_component_node.kind() {
                    "format_specifier" => {
                        let mut format_spec_expressions = vec![];
                        let interpolation_node_str =
                            self.get_text(interpolation_component_node)[1..].to_string();
                        let string_desc = self.string(format!("'{}'", interpolation_node_str,));
                        format_spec_expressions.push(self.new_expr(string_desc, origin_node));
                        *format_spec =
                            Some(self.new_expr(
                                ExprDesc::JoinedStr(format_spec_expressions),
                                origin_node,
                            ));
                    }
                    "type_conversion" => {
                        // the following magic numbers are defined in the Python
                        // language spec:
                        // https://docs.python.org/3.10/library/ast.html#ast.FormattedValue
                        *conversion =
                            Some(match self.get_text(interpolation_component_node).as_str() {
                                "!s" => 115,
                                "!r" => 114,
                                "!a" => 97,
                                _ => -1,
                            });
                    }
                    _ => (),
                }
            }
        }
    }

    /// create one large string from a number contained in a Vec<Expr>
    /// if any ' 's are within the strings then all are wrapped in double
    /// quotes
    fn sew_strings_together(&mut self, strings: Vec<Expr>) -> ExprDesc {
        let mut one_big_string = String::from("");
        let mut needs_doublequote = false;
        for child_string in strings {
            if let ExprDesc::Constant {
                value: Some(ConstantDesc::Str(astring)),
                kind: _,
            } = &*child_string.desc
            {
                let segment = &astring[1..astring.len() - 1].to_string();
                if segment.contains('\'') {
                    needs_doublequote = true;
                }
                one_big_string.push_str(segment);
            }
        }

        let quote_style = if needs_doublequote { "\"" } else { "'" };
        one_big_string = format!("{}{}{}", quote_style, one_big_string, quote_style);
        self.process_string(one_big_string)
    }

    fn extract_concatinated_strings(
        &mut self,
        conc_str_node: &Node,
        strings: &mut Vec<Expr>,
    ) -> Result<bool, ParserError> {
        let mut contains_f_string = false;
        for child_string_node in conc_str_node.named_children(&mut conc_str_node.walk()) {
            let child_string_expr = self.raw_string(&child_string_node, conc_str_node)?;
            if let ExprDesc::JoinedStr(_) = child_string_expr {
                contains_f_string = true;
            }
            strings.push(self.new_expr(child_string_expr, &child_string_node));
        }
        Ok(contains_f_string)
    }

    // concatenated_string: $ => seq(
    //    $.string,
    //    repeat1($.string)
    //  ),
    /// Concatinated strings are just regular strings which are made up of a number
    /// of other strings apread across multiple consecutive lines and
    /// delimited by a \ followed by a newline.
    /// most of the time, if all nodes are regular strings then we need
    /// just return a concatinated string.
    /// BUT if any nodes are an f string then return one big concatinated f string
    /// must be returned. This is achieved by creating a new f string and adding all
    /// f string and regular string components into one large expression list
    /// when joining f strings it is expected that string nodes are to be
    /// merged together to form one large string at the boundry point
    /// f-string([a:FormattedValue, b:FormattedValue, c:str]) + f-string([d:str, e:FormattedValue, f:FormattedValue])
    /// => f-string([a:FormattedValue, b:FormattedValue, concat(c+d):str, e:FormattedValue, f:FormattedValue])
    fn concatenated_string(&mut self, conc_str_node: &Node) -> Result<ExprDesc, ParserError> {
        let mut strings: Vec<Expr> = vec![];
        let contains_f_string = self.extract_concatinated_strings(conc_str_node, &mut strings)?;
        if contains_f_string {
            let mut expressions: Vec<Expr> = vec![];

            for mut child_string in strings {
                if let ExprDesc::JoinedStr(mut child_expressions) = *child_string.desc {
                    if !expressions.is_empty() && !child_expressions.is_empty() {
                        let last_item: &Expr = expressions.last().unwrap();
                        if let ExprDesc::Constant {
                            value: Some(ConstantDesc::Str(_)),
                            kind: _,
                        } = &*last_item.desc
                        {
                            let to_add_first_item = child_expressions.first().unwrap();
                            if let ExprDesc::Constant {
                                value: Some(ConstantDesc::Str(_)),
                                kind: _,
                            } = &*to_add_first_item.desc
                            {
                                // last item and first are strings, so we need to sew these together
                                let mut to_sew = vec![];
                                to_sew.push(expressions.pop().unwrap());
                                to_sew.push(child_expressions.remove(0));
                                let sewn_desc = self.sew_strings_together(to_sew);
                                expressions.push(self.new_expr(sewn_desc, conc_str_node));
                                // and the rest of the items can be extended into the expressions list
                            }
                        }
                    }

                    expressions.extend(child_expressions);
                } else if let ExprDesc::Constant {
                    value: Some(ConstantDesc::Str(_)),
                    kind: _,
                } = &*child_string.desc
                {
                    // sew previous lines together if both string constants
                    if !expressions.is_empty() {
                        let last_item = expressions.last().unwrap();
                        if let ExprDesc::Constant {
                            value: Some(ConstantDesc::Str(_)),
                            kind: _,
                        } = &*last_item.desc
                        {
                            // last item was a string, so lets sew them together
                            let mut to_sew = vec![];
                            to_sew.push(expressions.pop().unwrap());
                            to_sew.push(child_string);
                            let sewn_desc = self.sew_strings_together(to_sew);
                            child_string = self.new_expr(sewn_desc, conc_str_node)
                        }
                    }

                    expressions.push(child_string);
                }
            }

            Ok(ExprDesc::JoinedStr(expressions))
        } else {
            Ok(self.sew_strings_together(strings))
        }
    }

    fn raw_string(
        &mut self,
        raw_string_node: &Node,
        origin_node: &Node,
    ) -> Result<ExprDesc, ParserError> {
        let string_contents = self.get_text(raw_string_node);

        if string_contents.starts_with("f\"") || string_contents.starts_with("f\'") {
            self.format_string(raw_string_node, origin_node)
        } else {
            Ok(self.process_string(string_contents))
        }
    }

    /// process_string performs the following:
    /// First we convert multiline strings to single line strings (denoted via single quote marks)
    /// and insert newlines with escapes for newlines
    /// Then, we remove all quote mark escape characters \' -> ', \" -> "
    /// Then, strings created via double quotes ("") are converted to single quote (''), unless they
    /// contain a single quote (')
    fn process_string(&mut self, string_contents: String) -> ExprDesc {
        let mut string_contents = string_contents;
        if string_contents.starts_with("\"\"\"") || string_contents.starts_with("\'\'\'") {
            string_contents = string_contents[2..string_contents.len() - 2]
                .to_string()
                .replace('\n', "\\n")
        }

        string_contents = {
            string_contents = string_contents.replace("\\\'", "\'");
            string_contents = string_contents.replace("\\\"", "\"");

            if string_contents.starts_with('\"') && !string_contents.contains('\'') {
                // convert string to being wrapped in '' unless there are inner ' s
                string_contents = string_contents[1..string_contents.len() - 1].to_string();
                format!("'{}'", string_contents)
            } else {
                string_contents
            }
        };

        self.string(string_contents)
    }

    fn string(&mut self, const_value: String) -> ExprDesc {
        ExprDesc::Constant {
            value: Some(ConstantDesc::Str(const_value)),
            kind: None,
        }
    }

    fn integer(&mut self, const_value: String) -> ExprDesc {
        ExprDesc::Constant {
            value: Some(ConstantDesc::Num(Num::Int(
                const_value.parse::<isize>().unwrap(),
            ))),
            kind: None,
        }
    }

    fn float(&mut self, const_value: String) -> ExprDesc {
        ExprDesc::Constant {
            value: Some(ConstantDesc::Num(Num::Float(
                const_value.parse::<f64>().unwrap(),
            ))),
            kind: None,
        }
    }

    fn name(&mut self, identifier: String) -> ExprDesc {
        ExprDesc::Name {
            id: identifier,
            ctx: self.get_expression_context(),
        }
    }

    //
    //
    // utilities
    //
    //

    // Get a copy of the source code behind this node.
    // For identifiers that is the identifer name.
    fn get_text(&self, node: &Node) -> String {
        get_node_text(&self.code, node)
    }
}

pub fn get_node_text(code: &String, node: &Node) -> String {
    node.utf8_text(code.as_bytes())
        .expect("Invalid Identifier") // deal with errors
        .to_string()
}

fn get_comp_op(operator: &NodeType, operator_next: Option<NodeType>) -> Option<Cmpop> {
    // We need to look one token ahead to deal with `not in` and `is not` cases
    match operator {
        NodeType::ComparisonOperator(cmp_operator) => Some(match cmp_operator {
            ComparisonOperator::LESS_THAN => Cmpop::Lt,
            ComparisonOperator::LESS_THAN_EQUAL => Cmpop::LtE,
            ComparisonOperator::EQUAL => Cmpop::Eq,
            ComparisonOperator::NOT_EQUAL => Cmpop::NotEq,
            ComparisonOperator::GREATER_THAN_EQUAL => Cmpop::GtE,
            ComparisonOperator::GREATER_THAN => Cmpop::Gt,
            ComparisonOperator::IN | ComparisonOperator::NOT | ComparisonOperator::IS => {
                panic!("unexpected comparison operator node {:?}", cmp_operator)
            }
        }),
        // deal with `not in` and `is not`
        NodeType::Keyword(Keyword::IN) => Some(Cmpop::In),
        NodeType::Keyword(Keyword::IS) => match operator_next {
            Some(NodeType::Keyword(Keyword::NOT)) => Some(Cmpop::IsNot),
            _ => Some(Cmpop::Is),
        },
        NodeType::Keyword(Keyword::NOT) => match operator_next {
            Some(NodeType::Keyword(Keyword::IN)) => Some(Cmpop::NotIn),
            _ => None,
        },
        _ => None,
    }
}

impl TryFrom<BinaryOperator> for Operator {
    type Error = FromBinaryOperatorError;
    fn try_from(operator: BinaryOperator) -> Result<Operator, Self::Error> {
        match operator {
            BinaryOperator::AT => Ok(Self::MatMult),
            BinaryOperator::BITWISE_AND => Ok(Self::BitAnd),
            BinaryOperator::BITWISE_OR => Ok(Self::BitOr),
            BinaryOperator::BITWISE_XOR => Ok(Self::BitXor),
            BinaryOperator::LEFT_SHIFT => Ok(Self::LShift),
            BinaryOperator::RIGHT_SHIFT => Ok(Self::RShift),
            BinaryOperator::PLUS => Ok(Self::Add),
            BinaryOperator::MINUS => Ok(Self::Sub),
            BinaryOperator::STAR => Ok(Self::Mult),
            BinaryOperator::PERCENT => Ok(Self::Mod),
            BinaryOperator::SLASH => Ok(Self::Div),
            BinaryOperator::DOUBLE_SLASH => Ok(Self::FloorDiv),
            BinaryOperator::DOUBLE_STAR => Ok(Self::Pow),
            _ => Err(FromBinaryOperatorError(operator)),
        }
    }
}

#[derive(Copy, Clone, Debug, thiserror::Error)]
#[error("invalid binary operator: {0:?}")]
pub struct FromBinaryOperatorError(BinaryOperator);

impl From<AugAssignOperator> for Operator {
    fn from(operator: AugAssignOperator) -> Operator {
        match operator {
            AugAssignOperator::AT_EQUAL => Self::MatMult,
            AugAssignOperator::BITWISE_AND_EQUAL => Self::BitAnd,
            AugAssignOperator::BITWISE_OR_EQUAL => Self::BitOr,
            AugAssignOperator::BITWISE_XOR_EQUAL => Self::BitXor,
            AugAssignOperator::LEFT_SHIFT_EQUAL => Self::LShift,
            AugAssignOperator::RIGHT_SHIFT_EQUAL => Self::RShift,
            AugAssignOperator::PLUS_EQUAL => Self::Add,
            AugAssignOperator::MINUS_EQUAL => Self::Sub,
            AugAssignOperator::STAR_EQUAL => Self::Mult,
            AugAssignOperator::PERCENT_EQUAL => Self::Mod,
            AugAssignOperator::SLASH_EQUAL => Self::Div,
            AugAssignOperator::DOUBLE_SLASH_EQUAL => Self::FloorDiv,
            AugAssignOperator::DOUBLE_STAR_EQUAL => Self::Pow,
        }
    }
}

// Prints the sitter nodes transformed in their internal representation.
// It only prints proper AST nodes as opposed to the tree sitter CST nodes
// (no syntax nodes)
fn print_internal_ast(node: &Node, indent: &str) {
    let node_type = get_node_type(node);
    match node_type {
        NodeType::Production(rule) => println!("{}{}", indent, rule.node.kind()),
        _ => (),
    }
    for child in node.children(&mut node.walk()) {
        let new_indent = format!("  {}", indent);
        print_internal_ast(&child, new_indent.as_str());
    }
}
