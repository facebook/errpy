// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree

// Mapping of grammar defined here (or variant thereof):
// https://github.com/tree-sitter/tree-sitter-python/blob/master/grammar.js

use std::collections::HashMap;
use std::collections::HashSet;
use std::num::ParseIntError;

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
use errors::ParserError;
use errors::RecoverableError;
use itertools::join;
use phf::phf_map;
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
use crate::errors;
use crate::sitter;

type ErrorableResult<T> = std::result::Result<T, ()>;

static SPECIAL_CHARS: [char; 21] = [
    '0', '1', '2', '3', '4', '5', '6', '7', 'a', 'b', 'f', 'n', 'r', 't', 'u', 'v', 'x', 'N', 'U',
    '\'', '\"',
];
static HEXA_CHAR_CONVERSION: phf::Map<char, &'static str> = phf_map! {
    '0' => "x00",
    '1' => "x01",
    '2' => "x02",
    '3' => "x03",
    '4' => "x04",
    '5' => "x05",
    '6' => "x06",
    '7' => "x07",
    'a' => "x07",
    'b' => "x08",
    'f' => "x0c",
    'v' => "x0b"
};

#[derive(Debug)]
pub struct RecoverableErrorWithLocation {
    pub parser_error: RecoverableError,
    pub location: RecoverableErrorLocation,
    pub stack: Vec<String>,
}

#[derive(Debug)]
pub struct RecoverableErrorLocation {
    pub lineno: isize,
    pub col_offset: isize,
    pub end_lineno: isize,
    pub end_col_offset: isize,
}

///
/// Parser is responsible for driving parsing of a python code String into an internal CST representation
/// before lowering to an AST. The AST is expected to match 1:1 with CPython. The AST is held within an
/// `ASTAndMetaData` instance (and potentitally additional metadata)
///
#[derive(Debug)]
pub struct Parser {
    code: String,
    pub ast_and_metadata: ASTAndMetaData,
    // contingent on if we are on lhs or rhs of assignment or del expression
    current_expr_ctx: Vec<Option<ExprContext>>,
    increment_expression_column_offset: isize,
    integer_overflow_error: ParseIntError,
    python_keywords: HashSet<String>,
}

///
/// `ASTAndMetaData` presently just holds the lowered AST
///
#[derive(Debug)]
pub struct ASTAndMetaData {
    // AST root for what was parsed correctly
    pub ast: Option<Mod_>,
    pub recoverable_errors: Vec<RecoverableErrorWithLocation>,
}

impl ASTAndMetaData {
    fn new() -> Self {
        ASTAndMetaData {
            ast: None,
            recoverable_errors: vec![],
        }
    }
}

impl Stmt {
    fn new(desc: StmtDesc, node_start: &Node, node_end: &Node) -> Stmt {
        let start_position = node_start.start_position();
        // Comment node is not to be considered for the end_lineno and end_col_offset
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

fn assemble_node_stack(node: &Node) -> Vec<String> {
    let mut result: Vec<String> = Vec::new();
    let mut current: Option<Node> = Some(*node);
    while let Some(n) = current {
        result.push(format!("{:?}", n));
        current = n.parent();
    }
    result
}

impl Parser {
    pub fn new(code: String) -> Self {
        Parser {
            code,
            ast_and_metadata: ASTAndMetaData::new(),
            current_expr_ctx: Vec::new(),
            increment_expression_column_offset: 0,
            integer_overflow_error: "184467440737095516150".parse::<isize>().err().unwrap(),
            // keywords obtained through running: buck2 run errpy/facebook/scripts:list_python_keywords -- errpy/facebook/scripts/peg_grammar_specs/3.10
            python_keywords: vec![
                "and", "as", "assert", "async", "await", "break", "class", "continue", "def",
                "del", "elif", "else", "except", "finally", "for", "from", "global", "if",
                "import", "in", "is", "lambda", "nonlocal", "not", "or", "pass", "raise", "return",
                "try", "while", "with", "yield",
            ]
            .into_iter()
            .map(String::from)
            .collect(),
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
            start_position.column as isize + self.increment_expression_column_offset,
            end_position.row as isize + 1,
            end_position.column as isize + self.increment_expression_column_offset,
        )
    }

    fn record_recoverable_error(&mut self, parser_error: RecoverableError, node: &Node) {
        if node.kind() == "ERROR" {
            // Error nodes should only be recorded as SyntaxError's
            // TODO: remove this code when we have filtered out ERROR nodes
            // from the CST to be walked [once they have already been marked]
            // as SyntaxError's
            if let RecoverableError::SyntaxError(_) = parser_error {
            } else {
                return;
            }
        }

        let start_position = node.start_position();
        let end_position = node.end_position();

        let location = RecoverableErrorLocation {
            lineno: start_position.row as isize + 1,
            col_offset: start_position.column as isize
                + self.increment_expression_column_offset
                + 1,
            end_lineno: end_position.row as isize + 1,
            end_col_offset: end_position.column as isize
                + self.increment_expression_column_offset
                + 1,
        };

        let stack = assemble_node_stack(node);

        self.ast_and_metadata
            .recoverable_errors
            .push(RecoverableErrorWithLocation {
                parser_error,
                location,
                stack,
            });
    }

    ///
    /// Public entry point to parse code.
    /// Code is defined at construction time (`new`) but it could also be passed
    /// to this function. We could also pass a delta
    ///
    pub fn parse(&mut self) -> Result<(), ParserError> {
        let mut cst_to_ast = SitterParser::new();
        cst_to_ast.set_language(tree_sitter_python::language())?;
        let tree = match cst_to_ast.parse(&self.code, None) {
            Some(t) => t,
            None => return Err(ParserError::DidNotComplete),
        };

        let root = &tree.root_node();

        self.find_error_nodes(root);
        self.parse_module(root);
        Ok(())
    }

    ///
    /// Mark all error nodes from the Tree-sitter CST as SyntaxErrors
    ///
    fn find_error_nodes(&mut self, node: &Node) {
        if node.kind() == "ERROR" {
            self.record_recoverable_error(
                RecoverableError::SyntaxError("invalid syntax".to_string()),
                node,
            );
            // don't process child nodes of ERROR nodes - otherwise this can
            // lead to a cascade of ERROR nodes being reported
            return;
        }
        for child in node.children(&mut node.walk()) {
            self.find_error_nodes(&child);
        }
    }

    // Process a module.
    // module: $ => repeat($._statement),
    fn parse_module(&mut self, root: &Node) {
        // root must be a module
        if root.kind() != "module" {
            self.ast_and_metadata.ast = Some(Mod_::Module {
                body: vec![],
                type_ignores: vec![],
            });
            return;
        }
        let mut body = vec![];
        self.block(root, &mut body);
        self.ast_and_metadata.ast = Some(Mod_::Module {
            body,
            type_ignores: vec![],
        });
    }

    //
    //
    // Functions that consumes the tree-sitter productions
    //
    //

    // Process a generic block updating `statements`.
    // Generally sequences of `repeat($._statement)`
    fn block(&mut self, block: &Node, statements: &mut Vec<Stmt>) {
        for child in block.named_children(&mut block.walk()) {
            let node_type = get_node_type(&child);
            match &node_type {
                NodeType::Production(production) => match &production.production_kind {
                    ProductionKind::COMMENT => (),
                    _ => match self.statement(production) {
                        Ok(statement) => statements.push(statement),
                        // ok to skip statements which have errors within them
                        Err(_) => (),
                    },
                },
                _ => (),
            }
        }
    }

    // Process a StmtDesc
    //
    // _statement: $ => choice(
    //   $._simple_statements,
    //   $._compound_statement
    // ),
    // _simple_statements: $ => seq(
    //   sep1($._simple_statement, SEMICOLON),
    //   optional(SEMICOLON),
    //   $._newline
    // ),
    // _simple_statement: $ => choice(
    //   $.future_import_statement,
    //   $.import_statement,
    //   $.import_from_statement,
    //   $.print_statement,
    //   $.assert_statement,
    //   $.expression_statement, // this recurses down
    //   $.return_statement,
    //   $.delete_statement,
    //   $.raise_statement,
    //   $.pass_statement,
    //   $.break_statement,
    //   $.continue_statement,
    //   $.global_statement,
    //   $.nonlocal_statement,
    //   $.exec_statement
    // ),
    // _compound_statement: $ => choice(
    //   $.if_statement,
    //   $.for_statement,
    //   $.while_statement,
    //   $.try_statement,
    //   $.with_statement,
    //   $.function_definition,
    //   $.class_definition,
    //   $.decorated_definition,
    //   $.match_statement,
    // ),
    fn statement(&mut self, rule: &Production) -> ErrorableResult<Stmt> {
        use ProductionKind::*;

        match &rule.production_kind {
            DECORATED_DEFINITION => self.decorated_definition(rule.node),
            rest => {
                let statement_desc = match rest {
                    // _simple_statement
                    FUTURE_IMPORT_STATEMENT => self.future_import_statement(rule.node)?,
                    IMPORT_STATEMENT => self.import_statement(rule.node)?,
                    IMPORT_FROM_STATEMENT => self.import_from_statement(rule.node)?,
                    ASSERT_STATEMENT => self.assert_statement(rule.node)?,
                    EXPRESSION_STATEMENT => self.expression_statement(rule.node)?,
                    RETURN_STATEMENT => self.return_statement(rule.node)?,
                    DELETE_STATEMENT => self.delete_statement(rule.node)?,
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
                        return Err(self.record_recoverable_error(
                            RecoverableError::UnimplementedStatement(format!("{:?}", rule.node)),
                            rule.node,
                        ));
                    }
                    _ => panic!("unexpected statement node: {:?}", rule.node),
                };

                Ok(Stmt::new(statement_desc, rule.node, rule.node))
            }
        }
    }

    // decorated_definition: $ => seq(
    //   repeat1($.decorator),
    //   field('definition', choice(
    //     $.class_definition,
    //     $.function_definition
    //   ))
    // ),
    fn decorated_definition(&mut self, node: &Node) -> ErrorableResult<Stmt> {
        use ProductionKind::*;

        // resolves to a class definition or funcdef
        let mut decorator_list: Vec<Expr> = vec![];

        for child in node.named_children(&mut node.walk()) {
            let node_type = get_node_type(&child);
            match &node_type {
                NodeType::Production(production) => match &production.production_kind {
                    FUNCTION_DEFINITION => {
                        let func_def = self.function_definition(&child, decorator_list)?;
                        return Ok(Stmt::new(func_def, &child, &child));
                    }
                    CLASS_DEFINITION => {
                        let class_def = self.class_definition(&child, decorator_list)?;
                        return Ok(Stmt::new(class_def, &child, &child));
                    }
                    DECORATOR => {
                        // decorator
                        let dec_expr_node = child.child(1).expect("dectorator missing elaboration");
                        let dec_expr = self.expression(&dec_expr_node)?;
                        decorator_list.push(dec_expr);
                    }
                    _ => (),
                },
                _ => (),
            }
        }

        Err(self.record_recoverable_error(RecoverableError::MissingChild, node))
    }

    // global_statement: $ => seq(
    //   'global',
    //   commaSep1($.identifier)
    // ),
    fn global_statement(&mut self, node: &Node) -> ErrorableResult<StmtDesc> {
        let mut identifiers = vec![];
        self.parse_identifiers(node, &mut identifiers)?;
        Ok(StmtDesc::Global(identifiers))
    }

    // nonlocal_statement: $ => seq(
    //   'nonlocal',
    //   commaSep1($.identifier)
    // ),
    fn nonlocal_statement(&mut self, node: &Node) -> ErrorableResult<StmtDesc> {
        let mut identifiers = vec![];
        self.parse_identifiers(node, &mut identifiers)?;

        Ok(StmtDesc::Nonlocal(identifiers))
    }

    fn parse_identifiers(
        &mut self,
        node: &Node,
        identifiers: &mut Vec<String>,
    ) -> ErrorableResult<()> {
        for child in node.named_children(&mut node.walk()) {
            let identifier = self.get_valid_identifier(&child);
            identifiers.push(identifier);
        }
        Ok(())
    }

    // Process Function Definition
    //
    // function_definition: $ => seq(
    //   optional('async'),
    //   'def',
    //   field('name', $.identifier),
    //   field('parameters', $.parameters),
    //   optional(
    //     seq(
    //       '->',
    //       field('return_type', $.type)
    //     )
    //   ),
    //   ':',
    //   field('body', $._suite)
    // ),
    fn function_definition(
        &mut self,
        func_def: &Node,
        decorator_list: Vec<Expr>,
    ) -> ErrorableResult<StmtDesc> {
        let name_node = func_def
            .child_by_field_name("name")
            .expect("missing function name");
        let name = self.get_valid_identifier(&name_node);
        let parameters_node = func_def
            .child_by_field_name("parameters")
            .expect("missing function parameters");
        let parameters = self.get_parameters(&parameters_node)?;
        let body_node = func_def
            .child_by_field_name("body")
            .expect("missing function body");
        let mut body = vec![];
        self.block(&body_node, &mut body);

        let return_annotation_node = func_def.child_by_field_name("return_type");
        let return_annotation_expr = match &return_annotation_node {
            Some(ret_annotation) => {
                let annotation_node = ret_annotation.child(0).expect("type node missing type");
                Some(self.expression(&annotation_node)?)
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
    //   '(',
    //   optional($._parameters),
    //   ')'
    // ),
    // _parameters: $ => seq(
    //   commaSep1($.parameter),
    //   optional(',')
    // ),
    // parameter: $ => choice(
    //   $.identifier,
    //   $.typed_parameter,
    //   $.default_parameter,
    //   $.typed_default_parameter,
    //   $.list_splat_pattern,
    //   $.tuple_pattern,
    //   $.keyword_separator,
    //   $.positional_separator,
    //   $.dictionary_splat_pattern
    // ),
    fn get_parameters(&mut self, parameters: &Node) -> ErrorableResult<Arguments> {
        use ProductionKind::*;

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
                    IDENTIFIER => {
                        self.get_parameters_identifier(
                            param.node,
                            &require_kw_args,
                            &mut kwonlyargs,
                            &mut kw_defaults,
                            &mut args,
                        );
                    }
                    TYPED_PARAMETER => {
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
                    DEFAULT_PARAMETER => {
                        self.get_parameters_default_parameter(
                            param.node,
                            &require_kw_args,
                            &mut kwonlyargs,
                            &mut kw_defaults,
                            &mut args,
                            &mut defaults,
                        )?;
                    }
                    TYPED_DEFAULT_PARAMETER => {
                        self.get_parameters_typed_default_parameter(
                            param.node,
                            &require_kw_args,
                            &mut kwonlyargs,
                            &mut kw_defaults,
                            &mut args,
                            &mut defaults,
                        )?;
                    }
                    LIST_SPLAT_PATTERN => {
                        let ident_node =
                            &param.node.child(1).expect("identifier of starred missing");
                        let identifier = self.get_valid_identifier(ident_node);

                        vararg = Some(Arg::new_simple(identifier, ident_node, &parameter));
                        require_kw_args = true;
                    }
                    TUPLE_PATTERN => panic!("unimplemented token in get_parameters: TUPLE_PATTERN"),
                    KEYWORD_SEPARATOR => {
                        // all arguments defined past this point are now keyword args
                        require_kw_args = true;
                    }
                    POSITIONAL_SEPARATOR => {
                        // everything declared as an arugment now becomes a posonlyargs
                        while !args.is_empty() {
                            posonlyargs.push(args.remove(0));
                        }
                    }
                    DICTIONARY_SPLAT_PATTERN => {
                        let ident_node = &param
                            .node
                            .child(1)
                            .expect("identifier of dictionary argument");
                        let identifier = self.get_valid_identifier(ident_node);

                        kwarg = Some(Arg::new_simple(identifier, ident_node, &parameter));
                    }
                    _ => {
                        return Err(self.record_recoverable_error(
                            RecoverableError::UnexpectedExpression(format!(
                                "unexpected function parameter: {:?}",
                                param
                            )),
                            &parameter,
                        ));
                    }
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
        let identifier = self.get_valid_identifier(node);

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
    //   choice(
    //     $.identifier,
    //     $.list_splat_pattern,
    //     $.dictionary_splat_pattern
    //   ),
    //   ':',
    //   field('type', $.type)
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
    ) -> ErrorableResult<()> {
        use ProductionKind::*;

        let typed_parameter_node = node
            .child_by_field_name("type")
            .expect("default param missing type");
        let annotation_node = typed_parameter_node
            .child(0)
            .expect("type node missing type");

        let annotation_expr = self.expression(&annotation_node)?;

        let ident_node = &node.child(0).expect("typed param id, *id or **id missing");
        let ident_node_type = get_node_type(ident_node);
        match ident_node_type {
            NodeType::Production(param) => match &param.production_kind {
                IDENTIFIER => {
                    let identifier = self.get_valid_identifier(param.node);
                    let arg = Arg::new_with_type(identifier, annotation_expr, parameter, parameter);
                    match require_kw_args {
                        true => {
                            kwonlyargs.push(arg);
                            kw_defaults.push(None);
                        }
                        _ => args.push(arg),
                    };
                }
                LIST_SPLAT_PATTERN => {
                    let ident_node = &param.node.child(1).expect("identifier of starred missing");
                    let identifier = self.get_valid_identifier(ident_node);

                    *vararg = Some(Arg::new_with_type(
                        identifier,
                        annotation_expr,
                        ident_node,
                        parameter,
                    ));
                    // all arguments defined past this point are now keyword args
                    *require_kw_args = true;
                }
                DICTIONARY_SPLAT_PATTERN => {
                    let ident_node = &param
                        .node
                        .child(1)
                        .expect("identifier of dictionary argument");
                    let identifier = self.get_valid_identifier(ident_node);

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
    //   field('name', $.identifier),
    //   '=',
    //   field('value', $.expression)
    // ),
    fn get_parameters_default_parameter(
        &mut self,
        node: &Node,
        require_kw_args: &bool,
        kwonlyargs: &mut Vec<Arg>,
        kw_defaults: &mut Vec<Option<Expr>>,
        args: &mut Vec<Arg>,
        defaults: &mut Vec<Expr>,
    ) -> ErrorableResult<()> {
        let name_node = &node
            .child_by_field_name("name")
            .expect("default param missing name");

        let identifier = self.get_valid_identifier(name_node);
        let arg = Arg::new_simple(identifier, name_node, name_node);

        let default_value_node = &node
            .child_by_field_name("value")
            .expect("default param missing value");
        let default_value = self.expression(default_value_node)?;

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
    //   field('name', $.identifier),
    //   ':',
    //   field('type', $.type),
    //   '=',
    //   field('value', $.expression)
    // )),
    fn get_parameters_typed_default_parameter(
        &mut self,
        node: &Node,
        require_kw_args: &bool,
        kwonlyargs: &mut Vec<Arg>,
        kw_defaults: &mut Vec<Option<Expr>>,
        args: &mut Vec<Arg>,
        defaults: &mut Vec<Expr>,
    ) -> ErrorableResult<()> {
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

        let annotation_expr = self.expression(&annotation_node)?;

        let identifier = self.get_valid_identifier(name_node);

        let arg = Arg::new_with_type(
            identifier,
            annotation_expr,
            name_node,
            typed_default_parameter_node,
        );

        let default_value = self.expression(default_value_node)?;

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
    //   'class',
    //   field('name', $.identifier),
    //   field('superclasses', optional($.argument_list)),
    //   ':',
    //   field('body', $._suite)
    // ),
    fn class_definition(
        &mut self,
        class_def: &Node,
        decorator_list: Vec<Expr>,
    ) -> ErrorableResult<StmtDesc> {
        let name_node = class_def
            .child_by_field_name("name")
            .expect("missing class name");
        let name = self.get_valid_identifier(&name_node);
        let body_node = class_def
            .child_by_field_name("body")
            .expect("missing class body");
        let mut body = vec![];
        self.block(&body_node, &mut body);

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
    //   'assert',
    //   commaSep1($.expression)
    // ),
    fn assert_statement(&mut self, node: &Node) -> ErrorableResult<StmtDesc> {
        let test_node = node.child(1).unwrap();
        let test = self.expression(&test_node)?;

        let mut msg = None;
        if node.child_count() == 4 {
            let msg_node = node.child(3).unwrap();
            msg = Some(self.expression(&msg_node)?);
        }

        Ok(StmtDesc::Assert { test, msg })
    }

    fn dotted_name_to_string(&mut self, node: &Node) -> ErrorableResult<String> {
        Ok(join(
            node.named_children(&mut node.walk())
                .map(|x| self.get_valid_identifier(&x)),
            ".",
        ))
    }

    fn get_aliases(&mut self, node: &Node, aliases: &mut Vec<Alias>) -> ErrorableResult<()> {
        for alias_child in node.named_children(&mut node.walk()) {
            match alias_child.child_by_field_name("alias") {
                Some(alias_name) => {
                    aliases.push(Alias::new(
                        self.dotted_name_to_string(
                            &alias_child
                                .child_by_field_name("name")
                                .expect("missing aliased_import name"),
                        )?,
                        Some(self.get_valid_identifier(&alias_name)),
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

    // import_statement: $ => seq(
    //   'import',
    //   $._import_list
    // ),
    // aliased_import: $ => seq(
    //   field('name', $.dotted_name),
    //   'as',
    //   field('alias', $.identifier)
    // ),
    fn import_statement(&mut self, node: &Node) -> ErrorableResult<StmtDesc> {
        let mut aliases: Vec<Alias> = vec![];
        self.get_aliases(node, &mut aliases)?;
        Ok(StmtDesc::Import(aliases))
    }

    // import_from_statement: $ => seq(
    //   'from',
    //   field('module_name', choice(
    //     $.relative_import,
    //     $.dotted_name
    //   )),
    //   'import',
    //   choice(
    //     $.wildcard_import,
    //     $._import_list,
    //     seq('(', $._import_list, ')')
    //   )
    // ),
    //
    // relative_import: $ => seq(
    //  $.import_prefix,
    //  optional($.dotted_name)
    //),
    fn import_from_statement(&mut self, node: &Node) -> ErrorableResult<StmtDesc> {
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
                // directories in a filesystem where by the number of dots
                // preceding a dotted name indicates how many levels upwards
                // one must look for the import dependency

                let import_prefix = module_name_node.child(0).expect("import_prefix");
                level = import_prefix.child_count() as isize;

                if module_name_node.child_count() == 2 {
                    let dotted_name = module_name_node.child(1).expect("dotted_name");
                    Some(self.dotted_name_to_string(&dotted_name)?)
                } else {
                    None
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
                                Some(self.get_valid_identifier(&alias_name)),
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

    // future_import_statement: $ => seq(
    //   'from',
    //   '__future__',
    //   'import',
    //   choice(
    //     $._import_list,
    //     seq('(', $._import_list, ')'),
    //   )
    // ),
    fn future_import_statement(&mut self, node: &Node) -> ErrorableResult<StmtDesc> {
        let mut names: Vec<Alias> = vec![];
        self.get_aliases(node, &mut names)?;

        Ok(StmtDesc::ImportFrom {
            module__: Some("__future__".to_string()),
            names,
            level: Some(0), // optional but always included
        })
    }

    // expressions: $ => choice(
    //  $.expression,
    //  $.expression_list
    // ),
    fn expressions(&mut self, node: &Node) -> ErrorableResult<Expr> {
        match node.kind() {
            "expression_list" => {
                let mut expressions: Vec<Expr> = vec![];
                self.expression_list(node, &mut expressions);

                let tuple_desc = ExprDesc::Tuple {
                    elts: expressions,
                    ctx: self.get_expression_context(),
                };

                Ok(self.new_expr(tuple_desc, node))
            }
            _ => self.expression(node),
        }
    }

    fn expression_list(&mut self, node: &Node, expressions: &mut Vec<Expr>) {
        for child in node.named_children(&mut node.walk()) {
            // it is ok to leave out a subexpression if there is a problem with it
            match self.expression(&child) {
                Ok(arg) => expressions.push(arg),
                _ => (),
            };
        }
    }

    // Process Return StmtDesc
    //
    // return_statement: $ => seq(
    //   'return',
    //   optional($._expressions)
    // ),
    fn return_statement(&mut self, node: &Node) -> ErrorableResult<StmtDesc> {
        let mut expr = None;
        if node.child_count() == 2 {
            expr = Some(self.expressions(&node.child(1).unwrap())?);
        }

        Ok(StmtDesc::Return(expr))
    }

    // raise_statement: $ => seq(
    //   'raise',
    //   optional($._expressions),
    //   optional(seq('from', field('cause', $.expression)))
    // ),
    fn raise_statement(&mut self, node: &Node) -> ErrorableResult<StmtDesc> {
        let mut exc = None;
        let mut cause = None;
        match node.child_by_field_name("cause") {
            Some(from_node) => {
                let expr_node = node.child(1).unwrap();
                exc = Some(self.expression(&expr_node)?);

                cause = Some(self.expression(&from_node)?);
            }
            _ => match node.child(1) {
                Some(expr_node) => {
                    exc = Some(self.expression(&expr_node)?);
                }
                _ => (),
            },
        }

        Ok(StmtDesc::Raise { exc, cause })
    }

    // Process an ExprDesc StmtDesc.
    // expression_statement: $ => choice(
    //   $.expression,
    //   seq(commaSep1($.expression), optional(',')),
    //   $.assignment,
    //   $.augmented_assignment,
    //   $.yield
    // ),
    fn expression_statement(&mut self, node: &Node) -> ErrorableResult<StmtDesc> {
        use ProductionKind::*;

        let expression_statement = if 1 == node.child_count() {
            let child_expression = node.child(0).ok_or_else(|| {
                self.record_recoverable_error(RecoverableError::MissingChild, node)
            })?;
            let child_expression_type = get_node_type(&child_expression);
            match child_expression_type {
                NodeType::Production(ref rule) => {
                    match &rule.production_kind {
                        ASSIGNMENT => {
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
                        AUGMENTED_ASSIGNMENT => self.aug_assign(rule.node)?,
                        YIELD => {
                            let yeild_desc = self.yield_statement(rule.node)?;
                            StmtDesc::Expr(self.new_expr(yeild_desc, node))
                        }
                        _ => {
                            let expression = self.expression(&child_expression)?;

                            // If the expression statement has a trailing comma we
                            // should treat it as a tuple of size one, otherwise
                            // it is a plain expression.
                            let ends_in_comma =
                                node.child(node.child_count() - 1).unwrap().kind() == ",";
                            if ends_in_comma {
                                let mut expressions = vec![];
                                expressions.push(expression);
                                let tuple_desc = ExprDesc::Tuple {
                                    elts: expressions,
                                    ctx: self.get_expression_context(),
                                };

                                StmtDesc::Expr(self.new_expr(tuple_desc, node))
                            } else {
                                StmtDesc::Expr(expression)
                            }
                        }
                    }
                }
                _ => panic!("should be unreachable for expression"),
            }
        } else {
            // sequence of expressions: seq(commaSep1($.expression), optional(',')),
            let tuple_desc = self.tuple(node)?;
            StmtDesc::Expr(self.new_expr(tuple_desc, node))
        };

        Ok(expression_statement)
    }

    // Delete(expr* targets)
    // delete_statement: $ => seq(
    //   'del',
    //   $._expressions
    // ),
    fn delete_statement(&mut self, node: &Node) -> ErrorableResult<StmtDesc> {
        let mut expressions: Vec<Expr> = vec![];

        self.set_expression_context(ExprContext::Del);

        let expressions_node = node.child(1).unwrap();

        match expressions_node.kind() {
            "expression_list" => self.expression_list(&expressions_node, &mut expressions),
            _ => {
                let expression = self.expression(&expressions_node)?;
                expressions.push(expression);
            }
        };

        self.pop_expression_context();

        Ok(StmtDesc::Delete(expressions))
    }

    // for_statement: $ => seq(
    //   optional('async'),
    //   'for',
    //   field('left', $._left_hand_side),
    //   'in',
    //   field('right', $._expressions),
    //   ':',
    //   field('body', $._suite),
    //   field('alternative', optional($.else_clause))
    // ),
    fn for_statement(&mut self, for_node: &Node) -> ErrorableResult<StmtDesc> {
        self.set_expression_context(ExprContext::Store);
        let target_node = for_node
            .child_by_field_name("left")
            .expect("missing left in for statement");
        let target = self.assign_left_hand_side(&target_node)?;
        self.pop_expression_context();

        let iter_node = for_node
            .child_by_field_name("right")
            .expect("missing right in for statement");
        let iter = self.expressions(&iter_node)?;

        let body_node = for_node
            .child_by_field_name("body")
            .expect("missing body in for statement");
        let mut body_block = vec![];
        self.block(&body_node, &mut body_block);

        let mut orelse_block = vec![];

        let orelse_node = for_node.child_by_field_name("alternative");
        match &orelse_node {
            Some(orelse_cont) => match &orelse_cont.child_by_field_name("body") {
                Some(body_cont) => self.block(body_cont, &mut orelse_block),
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

    fn process_withitem_as_pattern_or_expression(
        &mut self,
        items: &mut Vec<Withitem>,
        pattern_or_expression: &Node,
    ) -> ErrorableResult<()> {
        let mut optional_vars: Option<Expr> = None;
        let pattern_or_expression_type = &get_node_type(pattern_or_expression);

        match pattern_or_expression_type {
            NodeType::Production(rule) => match &rule.production_kind {
                ProductionKind::AS_PATTERN => {
                    let node = rule.node;
                    let lhs_expression = pattern_or_expression
                        .child(0)
                        .expect("expression for with_item");
                    let target_expression = node
                        .child(2)
                        .expect("target for with_item")
                        .child(0)
                        .expect("pattern target");

                    self.set_expression_context(ExprContext::Store);
                    optional_vars = Some(self.expression(&target_expression)?);
                    self.pop_expression_context();

                    let context_expr: Expr = self.expression(&lhs_expression)?;

                    items.push(Withitem {
                        context_expr,
                        optional_vars,
                    });
                }
                _ => {
                    if pattern_or_expression.child_count() >= 5 {
                        let sub_expression = pattern_or_expression
                            .child(4)
                            .expect("target for with_item");
                        if sub_expression.kind() == "as_pattern" {
                            let target_expression = sub_expression
                                .child(2)
                                .expect("target for with_item as")
                                .child(0)
                                .expect("pattern target");
                            self.set_expression_context(ExprContext::Store);
                            optional_vars = Some(self.expression(&target_expression)?);
                            self.pop_expression_context();
                        }
                    }
                    let context_expr: Expr = self.expression(pattern_or_expression)?;
                    items.push(Withitem {
                        context_expr,
                        optional_vars,
                    });
                }
            },

            _ => (),
        }

        Ok(())
    }

    // with_statement: $ => seq(
    //   optional('async'),
    //   'with',
    //   $.with_clause,
    //   ':',
    //   field('body', $._suite)
    // ),
    //
    // with_clause: $ => choice(
    //   seq(commaSep1($.with_item), optional(',')),
    //   seq('(', commaSep1($.with_item), optional(','), ')')
    // ),
    //
    // with_item: $ => prec.dynamic(1, seq(
    //   field('value', $.expression),
    // )),
    fn with_statement(&mut self, with_node: &Node) -> ErrorableResult<StmtDesc> {
        let is_async: bool = with_node.child(0).unwrap().kind().eq("async");
        let body_node = with_node
            .child_by_field_name("body")
            .expect("missing body in with statement");
        let mut body = vec![];
        self.block(&body_node, &mut body);

        let mut items: Vec<Withitem> = vec![];

        let with_clause_node_idx = if is_async { 2 } else { 1 };
        let with_clause_node = with_node.child(with_clause_node_idx).unwrap();

        for with_item_node in with_clause_node.named_children(&mut with_node.walk()) {
            let expression_node = &with_item_node
                .child(0)
                .expect("with_item to wrap an expression or as_pattern");

            let expression_node_type = &get_node_type(expression_node);

            match expression_node_type {
                NodeType::Production(rule) => match &rule.production_kind {
                    ProductionKind::TUPLE => {
                        for tuple_child_node in
                            expression_node.named_children(&mut with_node.walk())
                        {
                            match self.process_withitem_as_pattern_or_expression(
                                &mut items,
                                &tuple_child_node,
                            ) {
                                Ok(_) => (),
                                Err(error) => return Err(error),
                            }
                        }
                    }
                    _ => {
                        self.process_withitem_as_pattern_or_expression(
                            &mut items,
                            expression_node,
                        )?;
                    }
                },
                _ => {
                    self.record_recoverable_error(
                        RecoverableError::UnexpectedExpression(format!("{:?}", expression_node)),
                        expression_node,
                    );
                }
            };
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

    // try_statement: $ => seq(
    //   'try',
    //   ':',
    //   field('body', $._suite),
    //   choice(
    //     seq(
    //       repeat1($.except_clause),
    //       optional($.else_clause),
    //       optional($.finally_clause)
    //     ),
    //     seq(
    //       repeat1($.except_group_clause),
    //       optional($.else_clause),
    //       optional($.finally_clause)
    //     ),
    //     $.finally_clause
    //   )
    // ),
    //
    // except_clause: $ => seq(
    //   'except',
    //   optional(seq(
    //     $.expression,
    //     optional(seq(
    //       choice('as', ','),
    //       $.expression
    //     ))
    //   )),
    //   ':',
    //   $._suite
    // ),
    //
    // except_group_clause - comes in 3.11 ( so we need to care about this for the 3.12 upgrade )
    //
    // except_group_clause: $ => seq(
    //   'except*',
    //   seq(
    //     $.expression,
    //     optional(seq(
    //       'as',
    //       $.expression
    //     ))
    //   ),
    //   ':',
    //   $._suite
    // ),
    //
    // finally_clause: $ => seq(
    //   'finally',
    //   ':',
    //   $._suite
    // ),
    fn try_statement(&mut self, try_node: &Node) -> ErrorableResult<StmtDesc> {
        let mut body: Vec<Stmt> = vec![];
        let mut handlers: Vec<Excepthandler> = vec![];
        let mut orelse: Vec<Stmt> = vec![];
        let mut finalbody: Vec<Stmt> = vec![];

        let body_node = try_node
            .child_by_field_name("body")
            .expect("missing body in for statement");
        self.block(&body_node, &mut body);

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
                    );

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

                                    name = Some(self.get_valid_identifier(&target_expression));

                                    Some(self.expression(&lhs_expression)?)
                                }
                                _ => Some(self.expression(expr_node)?),
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
                    self.block(&child_node.child(2).expect("else body"), &mut orelse);
                }
                "finally_clause" => {
                    self.block(&child_node.child(2).expect("finally body"), &mut finalbody);
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
    //   'while',
    //   field('condition', $.expression),
    //   ':',
    //   field('body', $._suite),
    //   optional(field('alternative', $.else_clause))
    // ),
    fn while_statement(&mut self, for_node: &Node) -> ErrorableResult<StmtDesc> {
        let test_node = for_node
            .child_by_field_name("condition")
            .expect("missing condition in while statement");
        let test = self.expression(&test_node)?;

        let body_node = for_node
            .child_by_field_name("body")
            .expect("missing body in for statement");
        let mut body = vec![];
        self.block(&body_node, &mut body);

        let mut orelse = vec![];

        let orelse_node = for_node.child_by_field_name("alternative");
        match &orelse_node {
            Some(orelse_cont) => match &orelse_cont.child_by_field_name("body") {
                Some(body_cont) => self.block(body_cont, &mut orelse),
                _ => (),
            },
            _ => (),
        }

        Ok(StmtDesc::While { test, body, orelse })
    }

    // Process If StmtDesc
    //
    // if_statement: $ => seq(
    //   'if',
    //   field('condition', $.expression),
    //   ':',
    //   field('consequence', $._suite),
    //   repeat(field('alternative', $.elif_clause)),
    //   optional(field('alternative', $.else_clause))
    // ),
    fn if_statement(&mut self, if_node: &Node) -> ErrorableResult<StmtDesc> {
        let condition_node = if_node
            .child_by_field_name("condition")
            .expect("missing condition in if statement");
        let condition = self.expression(&condition_node)?;
        let block_node = if_node
            .child_by_field_name("consequence")
            .expect("missing consequence in if statement");
        let mut block = vec![];
        self.block(&block_node, &mut block);

        let mut elif_elses = vec![];

        for elif_or_else in if_node.children_by_field_name("alternative", &mut if_node.walk()) {
            elif_elses.push(elif_or_else);
        }

        let mut last_orelse = vec![];

        for elif_or_else in elif_elses.iter().rev() {
            match elif_or_else.child_by_field_name("body") {
                Some(else_body) => {
                    last_orelse = vec![];
                    self.block(&else_body, &mut last_orelse);
                }
                _ => {
                    //elif body
                    let elif_condition_node = elif_or_else
                        .child_by_field_name("condition")
                        .expect("missing condition in if statement");
                    let elif_condition = self.expression(&elif_condition_node)?;

                    let elif_block_node = elif_or_else
                        .child_by_field_name("consequence")
                        .expect("missing consequence in if statement");
                    let mut elif_block = vec![];
                    self.block(&elif_block_node, &mut elif_block);

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

    // seems overly complex...
    // yield: $ => prec.right(seq(
    //   'yield',
    //   choice(
    //     seq(
    //       'from',
    //       $.expression
    //     ),
    //     optional($._expressions)
    //   )
    // )),
    fn yield_statement(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let yield_statement = match node.child_count() {
            2 => {
                let rhs_expr = node.child(1).expect("expected yield rhs");
                let expr = self.expressions(&rhs_expr)?;

                ExprDesc::Yield(Some(expr))
            }
            3 => {
                let rhs_expr = node.child(2).expect("expected yield from rhs");
                let expr = self.expression(&rhs_expr)?;

                ExprDesc::YieldFrom(expr)
            }
            _ => ExprDesc::Yield(None),
        };

        Ok(yield_statement)
    }

    // augmented_assignment: $ => seq(
    //   field('left', $._left_hand_side),
    //   field('operator', choice(
    //     '+=', '-=', '*=', '/=', '@=', '//=', '%=', '**=',
    //     '>>=', '<<=', '&=', '^=', '|='
    //   )),
    //   field('right', $._right_hand_side)
    // ),
    fn aug_assign(&mut self, node: &Node) -> ErrorableResult<StmtDesc> {
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
    //   field('left', $._left_hand_side),
    //   choice(
    //     seq('=', field('right', $._right_hand_side)),
    //     seq(':', field('type', $.type)),
    //     seq(':', field('type', $.type), '=', field('right', $._right_hand_side))
    //   )
    // ),
    fn assignment(
        &mut self,
        node: &Node,
    ) -> Result<(Vec<Expr>, Option<Expr>, Option<Expr>, Option<String>, isize), ()> {
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
            Some(self.expression(&type_expr_node)?)
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
    //   $.expression,
    //   $.expression_list,
    //   $.assignment,
    //   $.augmented_assignment,
    //   $.yield
    // ),
    fn assign_right_hand_side(
        &mut self,
        rhs_node: &Node,
        targets: &mut Vec<Expr>,
    ) -> ErrorableResult<Expr> {
        use ProductionKind::*;

        let expr_type = &get_node_type(rhs_node);
        let rhs = match expr_type {
            NodeType::Production(rule) => match &rule.production_kind {
                EXPRESSION_LIST => {
                    let tuple_desc = self.tuple(rule.node)?;
                    self.new_expr(tuple_desc, rhs_node)
                }
                ASSIGNMENT => {
                    let (mut targetsx, _type_annot, rhsx, _ty, _simple) =
                        self.assignment(rule.node)?;
                    targets.append(&mut targetsx);
                    rhsx.unwrap()
                    // deal with types...
                }
                AUGMENTED_ASSIGNMENT => {
                    panic!(
                        "not yet implemented assign_right_hand_side - AUGMENTED_ASSIGNMENT {:?}",
                        rule.node
                    )
                }
                YIELD => {
                    let yield_desc = self.yield_statement(rule.node)?;
                    self.new_expr(yield_desc, rhs_node)
                }
                //TODO: what about yeild, augmented assignment
                _ => self.expression(rhs_node)?,
            },
            _ => self.expression(rhs_node)?,
        };
        Ok(rhs)
    }

    //
    // pattern_list: $ => seq(
    //   $.pattern,
    //   choice(
    //     ',',
    //     seq(
    //       repeat1(seq(
    //         ',',
    //         $.pattern
    //       )),
    //       optional(',')
    //     )
    //   )
    // ),
    //
    fn pattern_list(&mut self, pattern_list_node: &Node) -> Expr {
        // pattern lists are processed like tuples of patterns
        let mut patterns = vec![];

        for pattern_node in pattern_list_node.named_children(&mut pattern_list_node.walk()) {
            match self.pattern(&pattern_node) {
                Ok(expression) => patterns.push(expression),
                _ => (),
            }
        }

        let tuple_desc = ExprDesc::Tuple {
            elts: patterns,
            ctx: self.get_expression_context(),
        };

        self.new_expr(tuple_desc, pattern_list_node)
    }

    //
    // _left_hand_side: $ => choice(
    //   $.pattern,
    //   $.pattern_list,
    // ),
    //
    fn assign_left_hand_side(&mut self, lhs: &Node) -> ErrorableResult<Expr> {
        self.set_expression_context(ExprContext::Store);
        let lhs_type = &get_node_type(lhs);
        // left hand side, assignment target
        let lhs_expr = match lhs_type {
            NodeType::Production(rule) => match &rule.production_kind {
                // we can treat pattern_list as a tuple
                ProductionKind::PATTERN_LIST => self.pattern_list(lhs),
                _ => self.pattern(lhs)?,
            },
            _ => {
                return Err(self.record_recoverable_error(
                    RecoverableError::UnexpectedExpression(format!(
                        "unexpected assignment left hand side: {:?}",
                        lhs
                    )),
                    lhs,
                ));
            }
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
    fn pattern(&mut self, node: &Node) -> ErrorableResult<Expr> {
        use ProductionKind::*;

        let node_type = &get_node_type(node);
        let expr: Expr = match &node_type {
            NodeType::Production(rule) => match &rule.production_kind {
                IDENTIFIER => {
                    let name_desc = self.name(rule.node);
                    self.new_expr(name_desc, rule.node)
                }
                KEYWORD_IDENTIFIER => {
                    panic!(
                        "not yet implemented pattern - KEYWORD_IDENTIFIER {:?}",
                        rule.node
                    )
                }
                SUBSCRIPT => {
                    let subscript = self.subscript(node)?;
                    self.new_expr(subscript, rule.node)
                }
                ATTRIBUTE => {
                    let attribute = self.attribute(node)?;
                    self.new_expr(attribute, rule.node)
                }
                LIST_SPLAT_PATTERN => self.list_splat_pattern(node)?,
                TUPLE_PATTERN => self.tuple_pattern(rule.node)?,
                LIST_PATTERN => self.list_pattern(rule.node)?,
                _ => {
                    return Err(self.record_recoverable_error(
                        RecoverableError::UnexpectedExpression(format!(
                            "unexpected token in pattern: {:?}",
                            node
                        )),
                        node,
                    ));
                }
            },
            _ => {
                return Err(self.record_recoverable_error(
                    RecoverableError::UnexpectedExpression(format!(
                        "unexpected token in pattern: {:?}",
                        node
                    )),
                    node,
                ));
            }
        };

        Ok(expr)
    }

    fn comma_separated_patterns(&mut self, node: &Node, sub_patterns: &mut Vec<Expr>) {
        for child in node.named_children(&mut node.walk()) {
            // it is ok to leave out a sub-pattern if there is a problem with it
            match self.pattern(&child) {
                Ok(arg) => sub_patterns.push(arg),
                _ => (),
            };
        }
    }

    // tuple_pattern: $ => seq(
    //   '(',
    //   optional($._patterns),
    //   ')'
    // ),
    fn tuple_pattern(&mut self, node: &Node) -> ErrorableResult<Expr> {
        if node.child_count() == 3 {
            // if single item in tuple, unwrap this and teat as individual item
            // e.g.
            // `(a) = g` would be treated simply as a=g (normal assignment)
            // but, `(a,) = g` would be treated as `(a,) = g` (tuple assignment)
            let expr_node = &node.child(1).unwrap();
            self.pattern(expr_node)
        } else {
            let mut sub_patterns = vec![];
            self.comma_separated_patterns(node, &mut sub_patterns);

            let tuple_pattern = ExprDesc::Tuple {
                elts: sub_patterns,
                ctx: self.get_expression_context(),
            };

            Ok(self.new_expr(tuple_pattern, node))
        }
    }

    // list_pattern: $ => seq(
    //   '[',
    //   optional($._patterns),
    //   ']'
    // ),
    fn list_pattern(&mut self, node: &Node) -> ErrorableResult<Expr> {
        let mut sub_patterns = vec![];
        self.comma_separated_patterns(node, &mut sub_patterns);

        let list_pattern = ExprDesc::List {
            elts: sub_patterns,
            ctx: self.get_expression_context(),
        };

        Ok(self.new_expr(list_pattern, node))
    }

    // list_splat_pattern: $ => seq(
    //   '*',
    //   choice($.identifier, $.keyword_identifier, $.subscript, $.attribute)
    // ),
    fn list_splat_pattern(&mut self, node: &Node) -> ErrorableResult<Expr> {
        use ProductionKind::*;

        // first node is *, second is the choice of ...
        let actual_pattern_node = &node.child(1).unwrap();

        let node_type = &get_node_type(actual_pattern_node);
        let value: Expr = match &node_type {
            NodeType::Production(rule) => match &rule.production_kind {
                IDENTIFIER => {
                    let text_desc = self.name(rule.node);
                    self.new_expr(text_desc, rule.node)
                }
                KEYWORD_IDENTIFIER => {
                    panic!(
                        "KEYWORD_IDENTIFIER not yet implemented for list_splat_pattern {:?}",
                        rule.node
                    )
                }
                SUBSCRIPT => {
                    let subscript = self.subscript(rule.node)?;
                    self.new_expr(subscript, rule.node)
                }
                ATTRIBUTE => {
                    let attribute_desc = self.attribute(rule.node)?;
                    self.new_expr(attribute_desc, rule.node)
                }
                _ => {
                    return Err(self.record_recoverable_error(
                        RecoverableError::UnexpectedExpression(format!(
                            "unexpected token in list_splat_pattern: {:?}",
                            actual_pattern_node
                        )),
                        actual_pattern_node,
                    ));
                }
            },
            _ => {
                return Err(self.record_recoverable_error(
                    RecoverableError::UnexpectedExpression(format!(
                        "unexpected token in list_splat_pattern: {:?}",
                        actual_pattern_node
                    )),
                    actual_pattern_node,
                ));
            }
        };

        let starred = ExprDesc::Starred {
            value,
            ctx: self.get_expression_context(),
        };

        Ok(self.new_expr(starred, node))
    }

    // Process an ExprDesc.
    // expression: $ => choice(
    //   $.comparison_operator,
    //   $.not_operator,
    //   $.boolean_operator,
    //   $.await,
    //   $.lambda,
    //   $.primary_expression,
    //   $.conditional_expression,
    //   $.named_expression,
    // ),
    fn expression(&mut self, node: &Node) -> ErrorableResult<Expr> {
        use ProductionKind::*;

        let node_type = &get_node_type(node);

        let expr = match node_type {
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
                    let node = rule.node;
                    let sub_node = node.child(4).expect("if_exp missing orelse");
                    let start_position = node.start_position();
                    let mut end_position = node.end_position();

                    if sub_node.kind() == "as_pattern" {
                        end_position = node
                            .child(4)
                            .expect("if_exp missing orelse")
                            .child(0)
                            .expect("orelse missing child")
                            .end_position();
                    }
                    Expr::new(
                        if_desc,
                        start_position.row as isize + 1,
                        start_position.column as isize + self.increment_expression_column_offset,
                        end_position.row as isize + 1,
                        end_position.column as isize + self.increment_expression_column_offset,
                    )
                }
                NAMED_EXPRESSION => {
                    let named_desc = self.named_expression(rule.node)?;
                    self.new_expr(named_desc, rule.node)
                }
                AS_PATTERN => {
                    let body_node = node.child(0).expect("as_pattern missing body");
                    let node_type = &get_node_type(&body_node);
                    self.primary_expression(node_type, &body_node)?
                }
                _ => self.primary_expression(node_type, rule.node)?,
            },
            _ => {
                return Err(self.record_recoverable_error(
                    RecoverableError::UnexpectedExpression(format!("{:?}", node_type)),
                    node,
                ));
            }
        };
        Ok(expr)
    }

    // Process a Primary ExprDesc
    // primary_expression: $ => choice(
    //   $.binary_operator,
    //   $.identifier,
    //   alias("match", $.identifier),
    //   $.keyword_identifier,
    //   $.string,
    //   $.concatenated_string,
    //   $.integer,
    //   $.float,
    //   $.true,
    //   $.false,
    //   $.none,
    //   $.unary_operator,
    //   $.attribute,
    //   $.subscript,
    //   $.call,
    //   $.list,
    //   $.list_comprehension,
    //   $.dictionary,
    //   $.dictionary_comprehension,
    //   $.set,
    //   $.set_comprehension,
    //   $.tuple,
    //   $.parenthesized_expression,
    //   $.generator_expression,
    //   $.ellipsis
    // ),
    fn primary_expression(&mut self, node_type: &NodeType, node: &Node) -> ErrorableResult<Expr> {
        use ProductionKind::*;

        let exprdesc: ExprDesc = match node_type {
            NodeType::Production(rule) => match &rule.production_kind {
                BINARY_OPERATOR => self.binary_op(rule.node)?,
                // TODO: soft keywords like `match` and that story with python and tree-sitter
                IDENTIFIER => self.name(rule.node),
                KEYWORD_IDENTIFIER => self.name(node),
                STRING => self.raw_string(rule.node, rule.node)?,
                CONCATENATED_STRING => self.concatenated_string(rule.node)?,
                INTEGER => self.integer(rule.node)?,
                FLOAT => self.float(rule.node)?,
                TRUE => self.constant(ConstantDesc::Bool(true)),
                FALSE => self.constant(ConstantDesc::Bool(false)),
                NONE => self.none(),
                UNARY_OPERATOR => self.unary_op(rule.node)?,
                ATTRIBUTE => self.attribute(rule.node)?,
                SUBSCRIPT => self.subscript(rule.node)?,
                CALL => self.call(rule.node)?,
                LIST => self.list(rule.node)?,
                LIST_COMPREHENSION => self.list_comp(rule.node)?,
                LIST_SPLAT_PATTERN => self.starred(rule.node)?, // FIXME: why splat isn't in the comments?
                DICTIONARY => self.dictionary(rule.node)?,
                DICTIONARY_COMPREHENSION => self.dictionary_comprehension(rule.node)?,
                SET => self.set(rule.node)?,
                SET_COMPREHENSION => self.set_comp(rule.node)?,
                TUPLE => self.tuple(rule.node)?,
                PARENTHESIZED_EXPRESSION => return self.parenthesized_expression(rule.node),
                GENERATOR_EXPRESSION => self.generator_expression(rule.node)?,
                ELLIPSIS => self.constant(ConstantDesc::Ellipsis),
                _ => {
                    return Err(self.record_recoverable_error(
                        RecoverableError::UnexpectedExpression(format!(
                            "unexpected token: {:?}",
                            node
                        )),
                        node,
                    ));
                }
            },
            _ => {
                return Err(self.record_recoverable_error(
                    RecoverableError::UnexpectedExpression(format!("{:?}", node)),
                    node,
                ));
            }
        };
        Ok(self.new_expr(exprdesc, node))
    }

    // parenthesized_expression: $ => prec(PREC.parenthesized_expression, seq(
    //  '(',
    //   choice($.expression, $.yield),
    //   ')'
    // )),
    fn parenthesized_expression(&mut self, node: &Node) -> ErrorableResult<Expr> {
        let middle_node = &node
            .child(1)
            .expect("middle node of parenthesized_expression");
        if middle_node.kind() == "yield" {
            let yield_desc = self.yield_statement(middle_node)?;
            Ok(self.new_expr(yield_desc, middle_node))
        } else {
            self.expression(middle_node)
        }
    }

    // named_expression: $ => seq(
    //   field('name', $._named_expresssion_lhs),
    //   ':=',
    //   field('value', $.expression)
    // ),
    fn named_expression(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let target_node = &node
            .child_by_field_name("name")
            .expect("named_expression missing name field");

        self.set_expression_context(ExprContext::Store);
        let target = self.expression(target_node)?;
        self.pop_expression_context();

        let value_node = &node
            .child_by_field_name("value")
            .expect("named_expression missing value field");
        let value = self.expression(value_node)?;

        Ok(ExprDesc::NamedExpr { target, value })
    }

    // list_comprehension: $ => seq(
    //   '[',
    //   field('body', $.expression),
    //   $._comprehension_clauses,
    //   ']'
    // ),
    fn list_comp(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let mut generators = vec![];
        let elt = self.comprehension_core(node, &mut generators)?;

        Ok(ExprDesc::ListComp { elt, generators })
    }

    // set_comprehension: $ => seq(
    //   '{',
    //   field('body', $.expression),
    //   $._comprehension_clauses,
    //   '}'
    // ),
    fn set_comp(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let mut generators = vec![];
        let elt = self.comprehension_core(node, &mut generators)?;
        Ok(ExprDesc::SetComp { elt, generators })
    }

    // generator_expression: $ => seq(
    //   '(',
    //   field('body', $.expression),
    //   $._comprehension_clauses,
    //   ')'
    // ),
    fn generator_expression(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let mut generators = vec![];
        let elt = self.comprehension_core(node, &mut generators)?;
        Ok(ExprDesc::GeneratorExp { elt, generators })
    }

    // dictionary_comprehension: $ => seq(
    //   '{',
    //   field('body', $.pair),
    //   $._comprehension_clauses,
    //   '}'
    // ),
    fn dictionary_comprehension(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let mut generators = vec![];
        let (key, value) = self.dictionary_pair(node, &mut generators)?;

        Ok(ExprDesc::DictComp {
            key,
            value,
            generators,
        })
    }

    fn dictionary_pair(
        &mut self,
        node: &Node,
        generators: &mut Vec<Comprehension>,
    ) -> ErrorableResult<(Expr, Expr)> {
        //let elt =
        let pair_node = node
            .child_by_field_name("body")
            .expect("missing pair in dictionary_comprehension");

        let key_node = pair_node
            .child_by_field_name("key")
            .expect("missing key in pair node of dictionary");
        let key = self.expression(&key_node)?;

        let value_node = pair_node
            .child_by_field_name("value")
            .expect("missing value in pair node of dictionary");
        let value = self.expression(&value_node)?;

        self.comprehension_clauses(node, generators)?;
        Ok((key, value))
    }

    fn comprehension_core(
        &mut self,
        node: &Node,
        generators: &mut Vec<Comprehension>,
    ) -> ErrorableResult<Expr> {
        let body_node = node
            .child_by_field_name("body")
            .expect("missing body in comprehension");
        let elt = self.expression(&body_node)?;

        self.comprehension_clauses(node, generators)?;
        Ok(elt)
    }

    // _comprehension_clauses: $ => seq(
    //  $.for_in_clause,
    //  repeat(choice(
    //    $.for_in_clause,
    //    $.if_clause
    //  ))
    // ),
    fn comprehension_clauses(
        &mut self,
        node: &Node,
        generators: &mut Vec<Comprehension>,
    ) -> ErrorableResult<()> {
        use ProductionKind::*;

        for child_node in node.named_children(&mut node.walk()) {
            //_comprehension_clauses
            let child_type = &get_node_type(&child_node);
            match child_type {
                // for_in_clause
                NodeType::Production(prod) => match prod.production_kind {
                    FOR_IN_CLAUSE => {
                        let comp = self.comprehension_clause(&child_node)?;
                        generators.push(comp);
                    }
                    IF_CLAUSE => {
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
    //   $.for_in_clause,
    //   repeat(choice(
    //     $.for_in_clause,
    //     $.if_clause
    //   ))
    // ),
    //
    // _expression_within_for_in_clause: $ => choice(
    //     $.expression,
    //     alias($.lambda_within_for_in_clause, $.lambda)
    //   ),
    //
    // for_in_clause: $ => prec.left(seq(
    //   optional('async'),
    //   'for',
    //   field('left', $._left_hand_side),
    //   'in',
    //   field('right', commaSep1($._expression_within_for_in_clause)),
    //   optional(',')
    // )),
    fn comprehension_clause(&mut self, node: &Node) -> ErrorableResult<Comprehension> {
        let left_node = &node
            .child_by_field_name("left")
            .expect("comprehension_clause missing left field");

        let right_node = &node
            .child_by_field_name("right")
            .expect("comprehension_clause missing right field");

        self.set_expression_context(ExprContext::Store);
        let target = self.assign_left_hand_side(left_node)?;
        self.pop_expression_context();

        self.set_expression_context(ExprContext::Load);
        let iter = self.expression(right_node)?; // TODO this should call _expression_within_for_in_clause, which takes lambda too
        self.pop_expression_context();

        let ifs = vec![];

        Ok(Comprehension {
            target,
            iter,
            ifs,
            is_async: node.child(0).unwrap().kind().eq("async"),
        })
    }

    // if_clause: $ => seq(
    //   'if',
    //   $.expression
    // ),
    fn if_clause(&mut self, node: &Node) -> ErrorableResult<Expr> {
        let expr_node = &node.child(1).expect("if_clause missing expression");

        self.expression(expr_node)
    }

    //
    // Process Binary Operators
    //
    // binary_operator: $ => {
    //   const table = [
    //     [prec.left, '+', PREC.plus],
    //     [prec.left, '-', PREC.plus],
    //     [prec.left, '*', PREC.times],
    //     [prec.left, '@', PREC.times],
    //     [prec.left, '/', PREC.times],
    //     [prec.left, '%', PREC.times],
    //     [prec.left, '//', PREC.times],
    //     [prec.right, '**', PREC.power],
    //     [prec.left, '|', PREC.bitwise_or],
    //     [prec.left, '&', PREC.bitwise_and],
    //     [prec.left, '^', PREC.xor],
    //     [prec.left, '<<', PREC.shift],
    //     [prec.left, '>>', PREC.shift],
    //   ];

    //   return choice(...table.map(([fn, operator, precedence]) => fn(precedence, seq(
    //     field('left', $.primary_expression),
    //     field('operator', operator),
    //     field('right', $.primary_expression)
    //   ))));
    // },
    fn binary_op(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let lhs_node = node
            .child_by_field_name("left")
            .expect("missing lhs in binary op");
        let left = self.expression(&lhs_node)?;
        let operator_node = node
            .child_by_field_name("operator")
            .expect("missing operator in binary op");
        let operator = match get_node_type(&operator_node) {
            NodeType::BinaryOperator(op) => Operator::try_from(op)
                .expect("expected NodeType::BinaryOperator to have valid binary operator"),
            _ => {
                return Err(self.record_recoverable_error(
                    RecoverableError::MissingOperator(operator_node.kind().into()),
                    node,
                ));
            }
        };
        let rhs_node = node
            .child_by_field_name("right")
            .expect("missing rhs in binary op");
        let right = self.expression(&rhs_node)?;

        Ok(ExprDesc::BinOp {
            left,
            op: operator,
            right,
        })
    }

    // Process Attribute
    //
    // attribute: $ => prec(PREC.call, seq(
    //   field('object', $.primary_expression),
    //   '.',
    //   field('attribute', $.identifier)
    // )),
    fn attribute(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
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
        let attr = self.get_valid_identifier(&rhs);

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

    // _collection_elements: $ => seq(
    //  commaSep1(choice(
    //   $.yield, $.list_splat, $.parenthesized_list_splat, s.expression
    //  )),
    //  optional(',')
    // ),
    fn collection_elements(&mut self, node: &Node, exp_list: &mut Vec<Expr>) {
        for child in node.named_children(&mut node.walk()) {
            // it is ok to leave out a subexpression if there is a problem with it
            match child.kind() {
                "yield" => {
                    // I don't think we should support yield here
                    self.record_recoverable_error(
                        RecoverableError::UnimplementedStatement(format!("{:?}", &child)),
                        &child,
                    );
                }
                "list_splat" => {
                    match self.starred(&child) {
                        Ok(starred) => exp_list.push(self.new_expr(starred, &child)),
                        _ => (),
                    };
                }
                "parenthesized_list_splat" => {
                    // TODO: add support for parenthesized_list_splat
                    self.record_recoverable_error(
                        RecoverableError::UnimplementedStatement(format!("{:?}", &child)),
                        &child,
                    );
                }
                _ => {
                    match self.expression(&child) {
                        Ok(arg) => exp_list.push(arg),
                        _ => (),
                    };
                }
            };
        }
    }

    // Process List expression
    // list: $ => seq(
    //   '[',
    //   optional($._collection_elements),
    //   ']'
    // ),
    fn list(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let mut expressions = vec![];
        self.collection_elements(node, &mut expressions);

        Ok(ExprDesc::List {
            elts: expressions,
            ctx: self.get_expression_context(),
        })
    }

    // Process Tuple expression
    // tuple: $ => seq(
    //   '(',
    //   optional($._collection_elements),
    //   ')'
    // ),
    fn tuple(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let mut expressions = vec![];
        self.collection_elements(node, &mut expressions);

        Ok(ExprDesc::Tuple {
            elts: expressions,
            ctx: self.get_expression_context(),
        })
    }

    // Process Set expression
    // set: $ => seq(
    //   '{',
    //   $._collection_elements,
    //   '}'
    // ),
    fn set(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let mut expressions = vec![];
        self.collection_elements(node, &mut expressions);

        Ok(ExprDesc::Set(expressions))
    }

    //Process Set expression
    fn if_exp(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let body_node = node.child(0).expect("if_exp missing body");
        let body = self.expression(&body_node)?;

        let test_node = node.child(2).expect("if_exp missing test");
        let test = self.expression(&test_node)?;

        let orelse_node = node.child(4).expect("if_exp missing orelse");
        let orelse = self.expression(&orelse_node)?;

        Ok(ExprDesc::IfExp { test, body, orelse })
    }

    // dictionary: $ => seq(
    //   '{',
    //   optional(commaSep1(choice($.pair, $.dictionary_splat))),
    //   optional(','),
    //   '}'
    // ),
    //
    // dictionary_splat: $ => seq(
    //   '**',
    //   $.expression
    // ),
    fn dictionary(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        use ProductionKind::*;

        let mut keys = vec![];
        let mut values = vec![];

        for pair_or_dictionary_splat in node.named_children(&mut node.walk()) {
            let pair_or_dictionary_splat_type = get_node_type(&pair_or_dictionary_splat);
            match &pair_or_dictionary_splat_type {
                NodeType::Production(param) => match &param.production_kind {
                    PAIR => {
                        let key_node = pair_or_dictionary_splat.child(0).ok_or_else(|| {
                            self.record_recoverable_error(
                                RecoverableError::MissingChild,
                                &pair_or_dictionary_splat,
                            )
                        })?;

                        let key = self.expression(&key_node)?;
                        keys.push(Some(key));

                        let value_node = pair_or_dictionary_splat.child(2).ok_or_else(|| {
                            self.record_recoverable_error(
                                RecoverableError::MissingChild,
                                &pair_or_dictionary_splat,
                            )
                        })?;

                        let value = self.expression(&value_node)?;
                        values.push(value);
                    }
                    DICTIONARY_SPLAT => {
                        let value_node = pair_or_dictionary_splat.child(1).ok_or_else(|| {
                            self.record_recoverable_error(
                                RecoverableError::MissingChild,
                                &pair_or_dictionary_splat,
                            )
                        })?;

                        keys.push(None);
                        let value = self.expression(&value_node)?;
                        values.push(value);
                    }
                    _ => {
                        self.record_recoverable_error(
                            RecoverableError::UnexpectedExpression(format!(
                                "unexpected dictionary production: {:?}",
                                param
                            )),
                            node,
                        );
                    }
                },
                _ => {
                    self.record_recoverable_error(
                        RecoverableError::UnexpectedExpression(format!(
                            "unexpected dictionary production: {:?}",
                            node
                        )),
                        node,
                    );
                }
            }
        }

        Ok(ExprDesc::Dict { keys, values })
    }

    // Process Call
    //
    // call: $ => prec(PREC.call, seq(
    //   field('function', $.primary_expression),
    //   field('arguments', choice(
    //     $.generator_expression,
    //     $.argument_list
    //   ))
    // )),
    fn call(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let function = node
            .child_by_field_name("function")
            .expect("missing function in call");
        let func = self.expression(&function)?;

        let argument_or_generator = node
            .child_by_field_name("arguments")
            .expect("missing arguments (or generator) in call");

        let mut args = vec![];
        let mut keywords = vec![];

        match argument_or_generator.kind() {
            "generator_expression" => {
                let generator_expression = self.generator_expression(&argument_or_generator)?;
                args.push(self.new_expr(generator_expression, &argument_or_generator));
            }
            _ => {
                self.argument_list(&argument_or_generator, &mut args, &mut keywords)?;
            }
        }

        Ok(ExprDesc::Call {
            func,
            args,
            keywords,
        })
    }

    // Process Argument List
    //
    // argument_list: $ => seq(
    //   '(',
    //   optional(commaSep1(
    //     choice(
    //       $.expression,
    //       $.list_splat,
    //       $.dictionary_splat,
    //       alias($.parenthesized_list_splat, $.parenthesized_expression),
    //       $.keyword_argument
    //     )
    //   )),
    //   optional(','),
    //   ')'
    // ),
    fn argument_list(
        &mut self,
        node: &Node,
        arg_list: &mut Vec<Expr>,
        keyword_list: &mut Vec<AstKeyword>,
    ) -> ErrorableResult<()> {
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
                    DICTIONARY_SPLAT => {
                        let keywordarg = self.dictionary_splat(&child)?;
                        keyword_list.push(keywordarg);
                    }
                    KEYWORD_ARGUMENT => {
                        let keywordarg = self.keyword_argument(&child)?;
                        keyword_list.push(keywordarg);
                    }
                    _ => {
                        let expr = self.expression(&child)?;
                        arg_list.push(expr);
                    }
                },
                _ => {
                    self.record_recoverable_error(
                        RecoverableError::UnexpectedExpression(format!(
                            "unexpected argument handling: {:?}",
                            child_type
                        )),
                        &child,
                    );
                }
            };
        }
        Ok(())
    }

    // list_splat: $ => seq(
    //   '*',
    //   $.expression,
    // ),
    fn starred(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let identifier = node.child(1).expect("missing identifier in starred");

        let value = self.expression(&identifier)?;

        Ok(ExprDesc::Starred {
            value,
            ctx: self.get_expression_context(),
        })
    }

    // subscript: $ => prec(PREC.call, seq(
    //   field('value', $.primary_expression),
    //   '[',
    //   commaSep1(field('subscript', choice($.expression, $.slice))),
    //   optional(','),
    //   ']'
    // )),
    //
    // slice: $ => seq(
    //   optional($.expression),
    //   ':',
    //   optional($.expression),
    //   optional(seq(':', optional($.expression)))
    // ),
    fn subscript(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let value_node = node
            .child_by_field_name("value")
            .expect("value field in subscript");

        // subscripts and their slies are always loaded, even if they are on the lhs of an assignment operation
        self.set_expression_context(ExprContext::Load);
        let value = self.expression(&value_node)?;

        // if many slices, then wrapped inside a Tuple, otherwise slice on its own if only one
        let mut slices: Vec<Expr> = vec![];

        for subscript_node in node.children_by_field_name("subscript", &mut node.walk()) {
            let mut slice_elements: Vec<Option<Expr>> = vec![];

            let mut last_expr: Option<Expr> = None;

            if subscript_node.kind() == "slice" {
                for slice_child in subscript_node.children(&mut subscript_node.walk()) {
                    // if : or something else
                    let token = self.get_valid_identifier(&slice_child);
                    if token == ":" {
                        slice_elements.push(last_expr);
                        last_expr = None;
                    } else {
                        last_expr = Some(self.expression(&slice_child)?);
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
                slices.push(self.expression(&subscript_node)?);
            }
        }

        let ends_in_comma = node.child(node.child_count() - 2).unwrap().kind() == ",";

        let slice = if !ends_in_comma && slices.len() == 1 {
            slices.pop().expect("should be at least one slice")
        } else {
            // if ends in comma or if there are more than one slice
            let start_position = node
                .child(2)
                .expect("first element of tuple")
                .start_position();

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
                start_position.column as isize + self.increment_expression_column_offset,
                end_position.row as isize + 1,
                end_position.column as isize + self.increment_expression_column_offset,
            )
        };

        self.pop_expression_context();

        Ok(ExprDesc::Subscript {
            value,
            slice,
            ctx: self.get_expression_context(),
        })
    }

    // dictionary_splat: $ => seq(
    //   '**',
    //   $.expression
    // ),
    fn dictionary_splat(&mut self, node: &Node) -> ErrorableResult<AstKeyword> {
        let identifier = node
            .child(1)
            .expect("missing identifier in dictionary_splat");

        let value = self.expression(&identifier)?;

        //Ok(Box::new(DictionaryFuncArg::new(
        Ok(AstKeyword::new(None, value, node))
    }

    // keyword_argument: $ => seq(
    //   field('name', choice($.identifier, $.keyword_identifier, alias("match", $.identifier))),
    //   '=',
    //   field('value', $.expression)
    // ),
    fn keyword_argument(&mut self, node: &Node) -> ErrorableResult<AstKeyword> {
        let lhs = node
            .child_by_field_name("name")
            .expect("missing lhs in keyword_argument");
        // TODO: keywords (await and async) are permitted in this location but
        // we use get_valid_identifier anyway as it would be strange for anyone
        // to be giving a variable name (await and async) in real code.
        // If this turns out to be a problem then we can add a modifed version
        // of get_valid_identifier that permits await and async to be used as
        // identifiers
        let arg = self.get_valid_identifier(&lhs);

        let rhs = node
            .child_by_field_name("value")
            .expect("missing rhs in keyword_argument");

        let value = self.expression(&rhs)?;

        //Ok(Box::new(DictionaryFuncArg::new(
        Ok(AstKeyword::new(Some(arg), value, node))
    }

    // Process a Comparison Operator
    // comparison_operator: $ => prec.left(PREC.compare, seq(
    //   $.primary_expression,
    //   repeat1(seq(
    //     field('operators',
    //       choice(
    //         '<',
    //         '<=',
    //         '==',
    //         '!=',
    //         '>=',
    //         '>',
    //         '<>',
    //         'in',
    //         seq('not', 'in'),
    //         'is',
    //         seq('is', 'not')
    //       )),
    //     $.primary_expression
    //   ))
    // )),
    fn comparison_operator(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
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
            left: left
                .ok_or_else(|| self.record_recoverable_error(RecoverableError::MissingLhs, node))?,
            ops,
            comparators,
        })
    }

    // not_operator: $ => prec(PREC.not, seq(
    //   'not',
    //   field('argument', $.expression)
    // )),
    fn not_operator(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let arg = node
            .child_by_field_name("argument")
            .expect("missing argument in not operator");
        let operand = self.expression(&arg)?;

        Ok(ExprDesc::UnaryOp {
            op: Unaryop::Not,
            operand,
        })
    }

    // await: $ => prec(PREC.unary, seq(
    //   'await',
    //   $.expression
    // )),
    fn await_expr(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let arg = node.child(1).expect("missing argument in await");
        let arg = self.expression(&arg)?;

        Ok(ExprDesc::Await(arg))
    }

    // lambda_within_for_in_clause: $ => seq(
    //     'lambda',
    //     field('parameters', optional($.lambda_parameters)),
    //     ':',
    //     field('body', $._expression_within_for_in_clause)
    //   ),
    //
    // lambda: $ => prec(PREC.lambda, seq(
    //   'lambda',
    //   field('parameters', optional($.lambda_parameters)),
    //   ':',
    //   field('body', $.expression)
    // )),
    fn lambda(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let args = match node.child_by_field_name("parameters") {
            Some(params_node) => self.get_parameters(&params_node)?,
            _ => Arguments {
                posonlyargs: vec![],
                args: vec![],
                vararg: None,
                kwonlyargs: vec![],
                kw_defaults: vec![],
                kwarg: None,
                defaults: vec![],
            },
        };

        let body_node = node
            .child_by_field_name("body")
            .expect("missing body in lambda");
        let body = self.expression(&body_node)?;

        Ok(ExprDesc::Lambda { args, body })
    }

    // boolean_operator: $ => choice(
    //   prec.left(PREC.and, seq(
    //     field('left', $.expression),
    //     field('operator', 'and'),
    //     field('right', $.expression)
    //   )),
    //   prec.left(PREC.or, seq(
    //     field('left', $.expression),
    //     field('operator', 'or'),
    //     field('right', $.expression)
    //   ))
    // ),
    fn bool_op(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
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

        for child_name in &["left", "right"] {
            let child_node = node
                .child_by_field_name(child_name)
                .expect("missing child node in boolean_operator");
            let child_node_expression = self.expression(&child_node)?;

            if let ExprDesc::BoolOp { op: child_op, .. } = &*child_node_expression.desc {
                if child_node.kind() != "parenthesized_expression" && child_op == &operator {
                    // Consecutive operations with the same operator, such as a
                    // or b or c, are collapsed into one node with several
                    // values. Unless child node is wrapped up within a param ()
                    // in which case it is not collapsed. e.g.
                    // a or b or c   <-    collapsed
                    // a or (b or c) < not collapsed

                    if let ExprDesc::BoolOp {
                        values: child_values,
                        ..
                    } = *child_node_expression.desc
                    {
                        values.extend(child_values);
                    }

                    continue;
                }
            }
            values.push(child_node_expression);
        }

        Ok(ExprDesc::BoolOp {
            op: operator,
            values,
        })
    }

    // unary_operator: $ => prec(PREC.unary, seq(
    //   field('operator', choice('+', '-', '~')),
    //   field('argument', $.primary_expression)
    // )),
    fn unary_op(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
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

    // none: $ => 'None',
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

    fn is_triple_quote_multiline(&mut self, string: &String) -> bool {
        // possible to have "\"" - double brackets inside double brackets as input
        string.starts_with("\"\"\"") && string.ends_with("\"\"\"") && string.len() >= 6
            || string.starts_with("\'\'\'") && string.ends_with("\'\'\'") && string.len() >= 6
            || string.starts_with("f\"\"\"") && string.ends_with("\"\"\"") && string.len() >= 7
            || string.starts_with("f\'\'\'") && string.ends_with("\'\'\'") && string.len() >= 7
    }

    // string: $ => seq(
    //   alias($._string_start, '"'),
    //   repeat(choice($.interpolation, $._escape_interpolation, $.escape_sequence, $._not_escape_sequence, $._string_content)),
    //   alias($._string_end, '"')
    // ),
    //
    // interpolation: $ => seq(
    //   '{',
    //   $.expression,
    //   optional('='),
    //   optional($.type_conversion),
    //   optional($.format_specifier),
    //   '}'
    // ),
    // origin_node will be different from format_node where the format string exists within
    // a concatenated string
    // 1. Check if this f string is multiline
    // 2. Calculate offsets for each row in multiline string
    // 3. Iterate by string collecting: string before {}, strings in {} and strings after
    // 4. All subparts pushed respectively to expressions
    fn format_string(
        &mut self,
        format_node: &Node,
        origin_node: &Node,
        mut node_text: String,
    ) -> ErrorableResult<ExprDesc> {
        let mut expressions: Vec<Expr> = vec![];

        let apostrophe_or_quote = node_text[1..2].to_string();
        let mut multiline_offsets = HashMap::new();
        let base_row = format_node.start_position().row;
        let base_col = format_node.start_position().column;

        let mut prev_idx = 2;

        let is_multiline = if node_text.contains('\n') || self.is_triple_quote_multiline(&node_text)
        {
            // multiline f strings are interesting and require some giggling around so
            // that we can consistantly extract substring strings from the string.
            // Essentially we must:
            // Offset 2 extra chars off start of String (""" is 2 more chars wider than ")
            // we also need to remove newlines and do some offset calculations
            // keep track of column offsets on a per line basis
            let mut cur_row = base_row;
            multiline_offsets.insert(cur_row, 0);
            // move chars across one at a time and update offsets as approperiate
            let mut new_node_text = String::from("");
            let mut prev_char_is_backslash = false;

            for ch in node_text.chars() {
                if ch == '\n' {
                    if !prev_char_is_backslash {
                        new_node_text.push('\\');
                        new_node_text.push('n');
                    } else {
                        new_node_text.pop();
                    }

                    cur_row += 1;
                    multiline_offsets.insert(cur_row, new_node_text.len());
                } else {
                    new_node_text.push(ch);
                }
                prev_char_is_backslash = ch == '\\';
            }
            node_text = new_node_text;
            if self.is_triple_quote_multiline(&node_text) {
                prev_idx += 2;
            }
            true
        } else {
            false
        };

        let mut has_interpolation_nodes = false;

        for interpolation_node in format_node.named_children(&mut format_node.walk()) {
            // walk all interpolated nodes and
            // push each one to expressions as FormattedValue's
            // push any intervening string chunks to expressions as strings
            if interpolation_node.kind() == "interpolation" {
                has_interpolation_nodes = true;

                let start_row = interpolation_node.start_position().row;
                let end_row = interpolation_node.end_position().row;
                let mut start_col = interpolation_node.start_position().column;
                let mut end_col = interpolation_node.end_position().column;
                if is_multiline && start_row > base_row {
                    // if multiline, we need line column offset adjustment
                    // might be a CPython bug
                    start_col += multiline_offsets.get(&start_row).unwrap();
                    end_col += multiline_offsets.get(&end_row).unwrap();
                } else if is_multiline && start_row == base_row && start_row != end_row {
                    // if multiline and interpoaltion brackets begin in first line and
                    // end in further lines, we need line column adjustment for ending row
                    start_col -= base_col;
                    end_col += multiline_offsets.get(&end_row).unwrap();
                } else {
                    // single line f-literal or first line of multiline f-literal
                    // => decrease by code before the f-literal
                    start_col -= base_col;
                    end_col -= base_col;
                }

                // add next FormattedValue corresponding to {} region
                let interpolation_expression = interpolation_node
                    .child(1)
                    .expect("expression node of interpolation node");

                let mut format_spec: Option<Expr> = None;
                let mut conversion: Option<isize> = Some(-1);
                let mut has_equals = false;

                // format_specifier and/or type_conversion may be specified for interpolation_node
                self.extract_interpolation_node_optionals(
                    &interpolation_node,
                    origin_node,
                    &mut format_spec,
                    &mut conversion,
                    &mut has_equals,
                );

                if start_col > prev_idx {
                    // indicates that there is a string at one of the following two locations
                    // start of the f-string before the first {} (formatted value)
                    // in between two {}'s
                    // strings after the last {} are handled after iterating through
                    //the interpolation nodes
                    let mut string_before_tidy_braces =
                        self.tidy_double_braces(node_text[prev_idx..start_col].to_string());

                    if has_equals {
                        string_before_tidy_braces = string_before_tidy_braces
                            + interpolation_expression
                                .utf8_text(self.code.as_bytes())
                                .expect("Could not fetch param name")
                            + "="
                    }
                    // in multiline string allowed to have " inside """ """
                    // so we have to "\"" or '\'' respectively to correctly preprocess substring
                    if is_multiline {
                        string_before_tidy_braces = string_before_tidy_braces.replace(
                            &apostrophe_or_quote,
                            &format!("{}{}", "\\", apostrophe_or_quote),
                        );
                    }
                    let string_desc = self.process_string(format!(
                        "{}{}{}",
                        apostrophe_or_quote, string_before_tidy_braces, apostrophe_or_quote
                    ));
                    expressions.push(self.new_expr(string_desc, origin_node));
                } else if has_equals {
                    // Create new const expression
                    let expr = interpolation_expression
                        .utf8_text(self.code.as_bytes())
                        .expect("Could not fetch param name")
                        .to_string()
                        + "=";

                    let expr = self.string(format!("'{}'", expr));
                    expressions.push(self.new_expr(expr, origin_node));
                }

                let value =
                    if is_multiline && interpolation_expression.start_position().row > base_row {
                        // potential CPython bug here, column offsets for interpolation nodes for
                        // nodes on the nth (where n>0) line are off by one, so we must correct them
                        // and add the base col (code before the literal, e.g. assignment statement)
                        let prev_offset = self.increment_expression_column_offset;
                        self.increment_expression_column_offset = 1 + (base_col as isize);
                        let expr_node = self.expression(&interpolation_expression)?;
                        self.increment_expression_column_offset = prev_offset;
                        expr_node
                    } else {
                        self.expression(&interpolation_expression)?
                    };

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
        // adjusted_node_text is only required in case if there is leftover string
        // dropping last " symbol
        let mut adjusted_node_text = node_text[..node_text.len() - 1].to_string();
        if self.is_triple_quote_multiline(&node_text) {
            // the characters used to demarcate the end of the string are
            // two characters wider, so we take 2 away: """ vs "
            adjusted_node_text = adjusted_node_text[..adjusted_node_text.len() - 2].to_string();
        }

        if adjusted_node_text.len() > prev_idx {
            let expr = if has_interpolation_nodes {
                // add remainder of string as node at end of format string
                let mut after_last_tidy_braces =
                    self.tidy_double_braces(adjusted_node_text[prev_idx..].to_string());
                // in multiline string allowed to have " inside """ """
                // so we have to "\"" or '\'' respectively to correctly preprocess substring
                if is_multiline {
                    after_last_tidy_braces = after_last_tidy_braces.replace(
                        &apostrophe_or_quote,
                        &format!("{}{}", "\\", apostrophe_or_quote),
                    );
                }
                let string_desc = self.process_string(format!(
                    "{}{}{}",
                    apostrophe_or_quote, after_last_tidy_braces, apostrophe_or_quote
                ));
                self.new_expr(string_desc, origin_node)
            } else {
                // no interpolation nodes, just treat as normal string and cut of f from start
                let normal_string = self.tidy_double_braces(node_text[1..].to_string());
                let string_desc = self.process_string(normal_string);
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
        has_equals: &mut bool,
    ) {
        let interpolation_node_count = interpolation_node.child_count();
        *has_equals = false;
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
                    "=" => *has_equals = true,
                    _ => (),
                }
            }

            // Only set conversion by = if neither explicit conversion nor explicit formatters are set.
            if *has_equals && format_spec.is_none() && conversion == &mut Some(-1isize) {
                *conversion = Some(114)
            }
        }
    }

    /// create one large string from a number contained in a Vec<Expr>
    /// if any ' 's are within the strings then all are wrapped in double
    /// quotes
    fn sew_strings_together(&mut self, strings: Vec<Expr>, conc_str_node: &Node) -> ExprDesc {
        let mut one_big_string = String::from("");
        let mut needs_doublequote = false;
        let mut prev_byte = false;
        let mut first = true;

        for child_string in strings {
            if let ExprDesc::Constant {
                value: Some(ConstantDesc::Str(astring)),
                kind: _,
            } = &*child_string.desc
            {
                let byte = astring.starts_with('b');
                if !first && byte != prev_byte {
                    self.record_recoverable_error(
                        RecoverableError::SyntaxError(
                            "cannot mix bytes and nonbytes literals".to_string(),
                        ),
                        conc_str_node,
                    );
                }
                first = false;
                prev_byte = byte;
                let start = if byte { 2 } else { 1 };
                let segment = &astring[start..astring.len() - 1].to_string();
                if segment.contains('\'') {
                    needs_doublequote = true;
                }
                one_big_string.push_str(segment);
            }
        }

        let prefix = if prev_byte { "b" } else { "" };
        let quote_style = if needs_doublequote { "\"" } else { "'" };
        one_big_string = format!("{}{}{}{}", prefix, quote_style, one_big_string, quote_style);
        self.process_string(one_big_string)
    }

    fn extract_concatinated_strings(
        &mut self,
        conc_str_node: &Node,
        strings: &mut Vec<Expr>,
    ) -> ErrorableResult<bool> {
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
    //   $.string,
    //   repeat1($.string)
    // ),
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
    fn concatenated_string(&mut self, conc_str_node: &Node) -> ErrorableResult<ExprDesc> {
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
                                let sewn_desc = self.sew_strings_together(to_sew, conc_str_node);
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
                            let sewn_desc = self.sew_strings_together(to_sew, conc_str_node);
                            child_string = self.new_expr(sewn_desc, conc_str_node)
                        }
                    }

                    expressions.push(child_string);
                }
            }

            Ok(ExprDesc::JoinedStr(expressions))
        } else {
            Ok(self.sew_strings_together(strings, conc_str_node))
        }
    }

    fn raw_string(
        &mut self,
        raw_string_node: &Node,
        origin_node: &Node,
    ) -> ErrorableResult<ExprDesc> {
        // collect escape sequences and parse into corresponding unicode characters
        let mut escape_sequences = vec![];
        for child in raw_string_node.children(&mut raw_string_node.walk()) {
            if child.kind() == "escape_sequence" {
                let escape_sequence = self.get_text(&child);
                if escape_sequence.to_uppercase().starts_with("\\U")
                    || escape_sequence.starts_with("\\x")
                {
                    let escape_code = u32::from_str_radix(&escape_sequence[2..], 16).unwrap();
                    let escape_sequence = if escape_code < 32 // unprintable ascii
                        || escape_code == 92  // backslash
                        || escape_code == 173  // soft hyphen
                        || (127..=160).contains(&escape_code)
                    {
                        // code corresponds to a non-printable character, or character
                        // with a special escape sequence. we need to manually create
                        // the new escape sequence
                        match escape_code {
                            9 => String::from("\\t"),
                            10 => String::from("\\n"),
                            13 => String::from("\\r"),
                            92 => String::from("\\\\"),
                            _ => format!("\\x{:02x}", escape_code),
                        }
                    } else {
                        let as_unicode = std::char::from_u32(escape_code);
                        // In cases where escape_code is not a valid u32, it
                        // seems that CPython formats the unicode character
                        // as escape_sequence.to_lowercase() so we do the same
                        match as_unicode {
                            Some(formatted) => format!("{}", formatted),
                            None => escape_sequence.to_lowercase(),
                        }
                    };
                    escape_sequences.push((
                        escape_sequence,
                        child.start_byte() - raw_string_node.start_byte(),
                        child.end_byte() - raw_string_node.start_byte(),
                    ));
                }
            }
        }
        let string_contents = self.escape_decode_text(raw_string_node, &escape_sequences);
        if string_contents.starts_with("f\"") || string_contents.starts_with("f\'") {
            self.format_string(raw_string_node, origin_node, string_contents)
        } else {
            Ok(self.process_string(string_contents))
        }
    }

    /// Retrieves actual text representation of the string, additionally converting any escape
    /// sequences (like \xc3, \xXX) found in the previous steps to actual unicode form
    /// (unless there are no escape sequences or the string is a byte string)
    fn escape_decode_text(
        &mut self,
        raw_string_node: &Node,
        escape_sequences: &Vec<(String, usize, usize)>,
    ) -> String {
        let original_contents = self.get_text(raw_string_node);
        let is_byte = original_contents.starts_with('b');
        if escape_sequences.is_empty() || is_byte {
            original_contents
        } else {
            // substitute the new characters
            let mut string_contents = String::new();
            let mut left = 0;
            for (escape_sequence, start_byte, end_byte) in escape_sequences.iter() {
                string_contents.push_str(&original_contents[left..*start_byte]);
                string_contents.push_str(escape_sequence);
                left = *end_byte;
            }
            string_contents.push_str(&original_contents[left..]);
            string_contents
        }
    }

    // - Add an extra '\' for non special characters which are escaped (e.g. \c => \\c)
    //   Equivalent to matching Regex::new(r#"(?<!^)(?<!\)\(\\)*([^0-7abfnrtuvxNU '"\])"#) and replacing by \\\\${1}${2}
    //   i.e. <not beginning of string nor '\'><odd number of '\'><non escapable Python char>
    // - Translate hexadecimal characters which are not escaped (e.g. \0 => \x00)
    fn process_escaped_chars(&mut self, string_contents: String) -> String {
        let mut new_node_text = String::from("");
        let mut prev_backslashes = 0;

        for ch in string_contents.chars() {
            if ch == '\\' {
                prev_backslashes += 1;
                new_node_text.push(ch);
            } else {
                // Non special chars
                if !SPECIAL_CHARS.contains(&ch) {
                    if prev_backslashes % 2 == 1 {
                        // For non special chars escaped (odd number of '\', add an additional '\' to result in an even number of '\' (not escaped)
                        new_node_text.push('\\');
                    }
                    new_node_text.push(ch);
                // Hexa chars which are not escaped are translated, e.g. '\0' => "\x00",
                } else if let Some(hex_str) = HEXA_CHAR_CONVERSION.get(&ch) {
                    if prev_backslashes % 2 == 1 {
                        for hex_ch in hex_str.chars() {
                            new_node_text.push(hex_ch);
                        }
                    } else {
                        new_node_text.push(ch);
                    }
                // Special chars left as is
                } else {
                    new_node_text.push(ch);
                }
                prev_backslashes = 0;
            }
        }
        new_node_text.to_string()
    }

    /// process_string performs the following:
    ///  1. We check if a string is prefixed with a 'b' or 'r', if so
    ///  this is stripped out and added back as a prefix to the output of the
    ///  following steps (except 'r' which is thrown away)...
    ///  2. We consider '\' at the end of a line, which is treated as a line
    ///  continuation (ignored), or as a literal '\' for raw strings (prefixed with 'r')
    ///  3. We convert multiline strings to single line strings (denoted
    ///  via single quote marks) and insert newlines with escapes for newlines
    ///  4. We remove all quote mark escape characters \' -> ', \" -> "
    ///  5. Strings created via double quotes ("") are converted to single
    ///  quote (''), unless they contain a single quote (') or if they contain both a
    ///  single quote (') and a double quote (", originally \" but \ is removed in step
    ///  4). Whereas strings created with single quotes ('') containing other single
    ///  quotes but no double quotes (") are converted to double quoted strings.
    ///  6. We add escape characters again if needed (' -> \' or " -> \"). In practice,
    ///  this is relevant only when the the string contains both single (') and double
    ///  (") quotes.
    fn process_string(&mut self, string_contents: String) -> ExprDesc {
        let mut string_contents = string_contents;
        let byte = string_contents.starts_with('b');
        let raw = string_contents.starts_with('r');
        let prefix = if byte { "b" } else { "" };

        if raw || byte {
            string_contents = string_contents[1..].to_string();
        }
        if raw {
            string_contents = string_contents.replace('\\', "\\\\");
        } else {
            // ignore line continuations
            string_contents = string_contents.replace("\\\n", "");

            // replace \' and \" except at the end
            if let Some(i) = string_contents.find("\\\'") {
                if i < string_contents.len() - 2 {
                    string_contents = string_contents.replace("\\\'", "\'");
                }
            }

            if let Some(i) = string_contents.find("\\\"") {
                if i < string_contents.len() - 2 {
                    string_contents = string_contents.replace("\\\"", "\"");
                }
            }
        }

        string_contents = self.process_escaped_chars(string_contents);

        string_contents = string_contents.replace('\n', "\\n").replace('\t', "\\t");
        // check is line multiline string and replace with single double quote
        if self.is_triple_quote_multiline(&string_contents) {
            string_contents = string_contents[2..string_contents.len() - 2].to_string();
        }

        string_contents = {
            // convert string to being wrapped in '' (or "") unless there are inner ' s (or " s)
            if string_contents.starts_with('\"')
                && (!string_contents.contains('\'')
                    || string_contents.contains('\'')
                        && string_contents[1..string_contents.len() - 1].contains('\"'))
                && string_contents.len() > 1
            {
                string_contents = string_contents[1..string_contents.len() - 1].to_string();
                format!("'{}'", string_contents)
            } else if string_contents.starts_with('\'')
                && !string_contents.contains('\"')
                && string_contents.len() > 1
            {
                // wrap only if there is a ' in the middle of the string
                // e.g. '\\''  -> "\\'"
                let index: Option<usize> = string_contents[1..].find('\'').map(|i| i + 1);
                match index {
                    Some(i) if i > 0 && i < string_contents.len() - 1 => {
                        string_contents = string_contents[1..string_contents.len() - 1].to_string();

                        format!("\"{}\"", string_contents)
                    }
                    _ => string_contents,
                }
            } else {
                string_contents
            }
        };

        string_contents = {
            if string_contents.starts_with('\"') && string_contents.len() > 1 {
                string_contents = string_contents[1..string_contents.len() - 1].to_string();
                string_contents = string_contents.replace('\"', "\\\"");
                if !raw {
                    // \' reverts back to \\' when located in a double quote string
                    string_contents = string_contents.replace("\\'", "\\\\'");
                }
                format!("\"{}\"", string_contents)
            } else if string_contents.len() > 1 {
                string_contents = string_contents[1..string_contents.len() - 1].to_string();
                string_contents = string_contents.replace('\'', "\\\'");
                if !raw {
                    // \" reverts back to \\" when located in a single quote string
                    string_contents = string_contents.replace("\\\"", "\\\\\"");
                }
                format!("'{}'", string_contents)
            } else {
                string_contents
            }
        };

        self.string(format!("{prefix}{string_contents}"))
    }

    // string: $ => seq(
    //   alias($._string_start, '"'),
    //   repeat(choice($.interpolation, $._escape_interpolation, $.escape_sequence, $._not_escape_sequence, $._string_content)),
    //   alias($._string_end, '"')
    // ),
    fn string(&mut self, const_value: String) -> ExprDesc {
        ExprDesc::Constant {
            value: Some(ConstantDesc::Str(const_value)),
            kind: None,
        }
    }

    fn parse_integer_from_str_radix(
        &mut self,
        const_value: &str,
        node: &Node,
        radix: u32,
        variant_name: &str,
    ) -> ErrorableResult<isize> {
        match isize::from_str_radix(&const_value[2..], radix) {
            Ok(value) => Ok(value),
            Err(error_msg) => {
                return Err(self.record_recoverable_error(
                    RecoverableError::UnexpectedExpression(format!(
                        "cannot parse integer (Not a binary {:?}): {:?} as {:?}",
                        variant_name, const_value, error_msg
                    )),
                    node,
                ));
            }
        }
    }

    // integer: $ => token(choice(
    //   seq(
    //     choice('0x', '0X'),
    //     repeat1(/_?[A-Fa-f0-9]+/),
    //   ),
    //   seq(
    //     choice('0o', '0O'),
    //     repeat1(/_?[0-7]+/),
    //   ),
    //   seq(
    //     choice('0b', '0B'),
    //     repeat1(/_?[0-1]+/),
    //   ),
    //   seq(
    //     repeat1(/[0-9]+_?/),
    //     choice(
    //       optional(/[Ll]/), // long numbers
    //       optional(/[jJ]/) // complex numbers
    //     )
    //   )
    // )),
    fn integer(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let const_value = self.get_text(node).replace('_', "");

        let integer_value = if const_value.starts_with("0b") || const_value.starts_with("0B") {
            // binary integer
            self.parse_integer_from_str_radix(&const_value, node, 2, "binary")?
        } else if const_value.starts_with("0x") || const_value.starts_with("0X") {
            // hexadecimal integer
            self.parse_integer_from_str_radix(&const_value, node, 16, "hexadecimal")?
        } else if const_value.starts_with("0o") || const_value.starts_with("0O") {
            // octal integer
            self.parse_integer_from_str_radix(&const_value, node, 8, "octal")?
        } else {
            if const_value.ends_with('j') || const_value.ends_with('J') {
                // imaginary part of complex numbers are always parsed like floats
                // even when they have an integer component as here
                return self.float(node);
            }

            match const_value.parse::<isize>() {
                Ok(value) => value,
                Err(ref e) if *e == self.integer_overflow_error => {
                    // TODO: use ParseIntError.kind() to detect integer overflow of
                    // parse of const_value when Meta is on rust 2022.
                    // In rust 2021 ParseIntError.kind is private
                    // For now, store an overflow Err from parsing a large integer
                    // Adapted from https://github.com/rust-lang/rust/issues/22639
                    // and https://github.com/uutils/coreutils/pull/2882/
                    return Ok(ExprDesc::Constant {
                        value: Some(ConstantDesc::Num(Num::BigInt(const_value))),
                        kind: None,
                    });
                }
                Err(error_msg) => {
                    return Err(self.record_recoverable_error(
                        RecoverableError::UnexpectedExpression(format!(
                            "cannot parse integer: {:?} as {:?}",
                            const_value, error_msg
                        )),
                        node,
                    ));
                }
            }
        };

        Ok(ExprDesc::Constant {
            value: Some(ConstantDesc::Num(Num::Int(integer_value))),
            kind: None,
        })
    }

    // float: $ => {
    //   const digits = repeat1(/[0-9]+_?/);
    //   const exponent = seq(/[eE][\+-]?/, digits)

    //   return token(seq(
    //     choice(
    //       seq(digits, '.', optional(digits), optional(exponent)),
    //       seq(optional(digits), '.', digits, optional(exponent)),
    //       seq(digits, exponent)
    //     ),
    //     optional(choice(/[Ll]/, /[jJ]/))
    //   ))
    // },
    fn float(&mut self, node: &Node) -> ErrorableResult<ExprDesc> {
        let mut const_value = self.get_text(node).replace('_', "");

        let is_complex = const_value.ends_with('j') || const_value.ends_with('J');
        if is_complex {
            const_value = const_value[0..const_value.len() - 1].to_string();
        }

        let float_value = match const_value.parse::<f64>() {
            Ok(value) => value,
            Err(error_msg) => {
                return Err(self.record_recoverable_error(
                    RecoverableError::UnexpectedExpression(format!(
                        "cannot parse float: {:?} as {:?}",
                        const_value, error_msg
                    )),
                    node,
                ));
            }
        };

        Ok(ExprDesc::Constant {
            value: Some(ConstantDesc::Num(if is_complex {
                Num::Complex(float_value)
            } else {
                Num::Float(float_value)
            })),
            kind: None,
        })
    }

    ///
    /// Will return an identifier as a String and will record a
    /// recoverable error if the identifier is invalid
    /// (e.g. keyword, empty space etc)
    ///
    fn get_valid_identifier(&mut self, node: &Node) -> String {
        let identifier: String = self.get_text(node);
        self.check_identifier_valid(&identifier, node);
        identifier
    }

    ///
    /// Will record a recoverable error if the identifier
    /// is invalid (e.g. keyword, empty sapce etc)
    ///
    fn check_identifier_valid(&mut self, identifier: &String, node: &Node) {
        if self.python_keywords.contains(identifier) {
            self.record_recoverable_error(
                RecoverableError::SyntaxError(format!(
                    "keyword: {:?} cannot be used as identifier",
                    identifier
                )),
                node,
            )
        } else if identifier.is_empty() {
            self.record_recoverable_error(
                RecoverableError::SyntaxError(
                    "empty string cannot be used as identifier".to_string(),
                ),
                node,
            )
        }
    }

    fn name(&mut self, node: &Node) -> ExprDesc {
        let identifier: String = self.get_valid_identifier(node);

        ExprDesc::Name {
            id: identifier,
            ctx: self.get_expression_context(),
        }
    }

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
