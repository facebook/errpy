// (c) Meta Platforms, Inc. and affiliates. Confidential and proprietary.

use std::cmp::min;

use ast::Alias;
use ast::Arg;
use ast::Arguments;
use ast::Boolop;
use ast::Cmpop;
use ast::Comprehension;
use ast::ConstantDesc;
use ast::ExcepthandlerDesc;
use ast::Expr;
use ast::ExprDesc;
use ast::Keyword;
use ast::Mod_;
use ast::Num;
use ast::Operator;
use ast::Stmt;
use ast::StmtDesc;
use ast::Unaryop;
use ast::Withitem;
use printers::ast_print::UNKOWN_NODE_MOD;
use printers::ast_print::UNKOWN_NODE_STMT;

use crate::ast;
use crate::cst_to_ast::ASTAndMetaData;
use crate::printers;

pub struct PrintHelper<'a> {
    pub pprint_output: &'a mut String,
    ident_amount: usize,
    ident_current: usize,
    ident_str: String,
    ignore_next_n_chars: usize,
}

impl PrintHelper<'_> {
    pub fn new(pprint_output: &'_ mut String, ident_amount: usize) -> PrintHelper {
        PrintHelper {
            pprint_output,
            ident_amount,
            ident_current: 0,
            ident_str: "".to_string(),
            ignore_next_n_chars: 0,
        }
    }

    fn ignore_next_n_chars(&mut self, ignore_next_n_chars: usize) {
        self.ignore_next_n_chars += ignore_next_n_chars;
    }

    fn push_str(&mut self, to_push: &str) {
        if self.ignore_next_n_chars > 0 {
            // cut up to ignore_next_n_chars chars from input, if not enough to remove in one go
            // cut remainder from next call to push_str
            let to_cut = min(to_push.len(), self.ignore_next_n_chars);
            self.pprint_output.push_str(&to_push[to_cut..]);
            self.ignore_next_n_chars -= to_cut;
        } else {
            self.pprint_output.push_str(to_push);
        }
    }

    fn ends_with(&mut self, something: &str) -> bool {
        self.pprint_output.ends_with(something)
    }

    fn push_ident(&mut self) {
        if self.ident_current > 0 {
            self.pprint_output.push_str(&self.ident_str);
        }
    }

    fn pop(&mut self) {
        self.pprint_output.pop();
    }

    fn inc_ident(&mut self) {
        self.ident_current += self.ident_amount;
        self.inc_calc();
    }

    fn dec_ident(&mut self) {
        self.ident_current -= self.ident_amount;
        self.inc_calc();
    }

    fn inc_calc(&mut self) {
        self.ident_str = " ".repeat(self.ident_current);
    }

    fn current_length(&mut self) -> usize {
        self.pprint_output.len()
    }

    fn insert_at(&mut self, at_point: usize, what: &str) {
        self.pprint_output.insert_str(at_point, what);
    }

    fn substring_contains(&mut self, at_point: usize, what: &str) -> bool {
        self.pprint_output[at_point..].contains(what)
    }
}

impl ASTAndMetaData {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        self.ast.as_ref().unwrap().pprint(pprint_output);
    }
}

impl Mod_ {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        match self {
            Mod_::Module {
                body,
                type_ignores: _,
            } => process_mod_class_fucdef_block(body, false, pprint_output),
            _ => pprint_output.push_str(UNKOWN_NODE_MOD), // ignore
        }
    }
}

fn process_mod_class_fucdef_block(
    body: &[Stmt],
    in_function_body: bool,
    pprint_output: &mut PrintHelper,
) {
    let mut prev_item: Option<&StmtDesc> = None;
    for targ_elm in body.iter() {
        match prev_item {
            Some(prev_item) => {
                // if two \n's followed by something thats not a class or funcdef, remove last \n
                match targ_elm.desc {
                    StmtDesc::FunctionDef { .. } | StmtDesc::ClassDef { .. } => {
                        if let StmtDesc::ClassDef { .. } = prev_item {
                            pprint_output.pop();
                        }
                    }
                    _ => {
                        if pprint_output.ends_with("\n\n") {
                            pprint_output.pop();
                        }
                    }
                }
            }
            _ => {
                // if the first line is a string, we turn it into a docstring
                if let StmtDesc::Expr(expr) = &targ_elm.desc {
                    if let ExprDesc::Constant {
                        value: Some(ConstantDesc::Str(astring)),
                        kind: _,
                    } = &*expr.desc
                    {
                        let mut res = astring.to_string().replace("\\n", "\n");
                        res = res[1..res.len() - 1].to_string();
                        pprint_output.push_ident();
                        pprint_output.push_str(&format!("\"\"\"{}\"\"\"", res).to_string());
                        pprint_output.push_str("\n");
                        continue;
                    }
                }
            }
        }
        if in_function_body {
            if let StmtDesc::FunctionDef { .. } = &targ_elm.desc {
                pprint_output.push_str("\n");
            }
        }

        targ_elm.pprint(pprint_output);
        pprint_output.push_str("\n");
        prev_item = Some(&targ_elm.desc);
    }
}

fn format_vec_str(names: &[String], pprint_output: &mut PrintHelper) {
    let mut at_least_one = false;
    for name in names.iter() {
        at_least_one = true;
        pprint_output.push_str(name);
        pprint_output.push_str(", ");
    }
    if at_least_one {
        pprint_output.pop();
        pprint_output.pop();
    }
}

fn format_vec_expr(exprs: &[Expr], pprint_output: &mut PrintHelper) {
    let mut at_least_one = false;
    for expr in exprs.iter() {
        at_least_one = true;
        (*expr.desc).pprint(pprint_output);
        pprint_output.push_str(", ");
    }
    if at_least_one {
        pprint_output.pop();
        pprint_output.pop();
    }
}

fn format_vec_alias(aliases: &[Alias], pprint_output: &mut PrintHelper) {
    let mut at_least_one = false;
    for alias in aliases.iter() {
        at_least_one = true;
        pprint_output.push_str(&alias.name);
        match &alias.asname {
            Some(asname_text) => {
                pprint_output.push_str(" as ");
                pprint_output.push_str(asname_text);
            }
            _ => (),
        }
        pprint_output.push_str(", ");
    }
    if at_least_one {
        pprint_output.pop();
        pprint_output.pop();
    }
}

fn format_vec_keywords(keywords: &[Keyword], pprint_output: &mut PrintHelper) {
    let mut at_least_one = false;
    for keyword in keywords.iter() {
        at_least_one = true;
        keyword.pprint(pprint_output);
        pprint_output.push_str(", ");
    }
    if at_least_one {
        pprint_output.pop();
        pprint_output.pop();
    }
}

fn format_block(body: &[Stmt], pprint_output: &mut PrintHelper) {
    pprint_output.inc_ident();
    for item in body.iter() {
        item.pprint(pprint_output);
        pprint_output.push_str("\n");
    }
    pprint_output.dec_ident();
}

impl Stmt {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        pprint_output.push_ident();
        match &self.desc {
            StmtDesc::Assign {
                targets,
                value,
                type_comment: _,
            } => {
                for targ_elm in targets.iter() {
                    (*targ_elm.desc).pprint(pprint_output);
                    pprint_output.push_str(" = ");
                }
                pprint_output.pop();
                pprint_output.pop();
                pprint_output.pop();

                pprint_output.push_str(" = ");
                handle_assign_rhs_yield(&value.desc, pprint_output);
            }
            StmtDesc::AnnAssign {
                target,
                annotation,
                value,
                simple,
            } => {
                let lhs = &*target.desc;
                if *simple == 0 {
                    // not simple and lhs is a Name, then wrap the name in ()'s
                    match lhs {
                        ExprDesc::Name { id, ctx: _ } => {
                            pprint_output.push_str("(");
                            pprint_output.push_str(id);
                            pprint_output.push_str(")");
                        }
                        _ => lhs.pprint(pprint_output),
                    }
                } else {
                    lhs.pprint(pprint_output);
                }

                pprint_output.push_str(": ");
                (*annotation.desc).pprint(pprint_output);

                if let Some(v) = value {
                    pprint_output.push_str(" = ");
                    (*v.desc).pprint(pprint_output);
                }
            }
            StmtDesc::AugAssign { target, op, value } => {
                (*target.desc).pprint(pprint_output);
                pprint_output.push_str(" ");
                op.pprint(pprint_output);
                pprint_output.push_str("= ");
                handle_assign_rhs_yield(&value.desc, pprint_output);
            }
            StmtDesc::Expr(expr) => (*expr.desc).pprint(pprint_output),
            StmtDesc::Delete(exprs) => {
                pprint_output.push_str("del ");
                format_vec_expr(exprs, pprint_output);
            }
            StmtDesc::Import(aliases) => {
                pprint_output.push_str("import ");
                format_vec_alias(aliases, pprint_output);
            }
            StmtDesc::ImportFrom {
                module__,
                names,
                level,
            } => {
                pprint_output.push_str("from ");

                match level {
                    Some(llevel) => {
                        let compl = *llevel as isize;
                        if compl > 0 {
                            let mut ll = 0;
                            while ll < compl {
                                pprint_output.push_str(".");
                                ll += 1;
                            }
                        }
                    }
                    _ => (),
                }

                match module__ {
                    Some(mm) => pprint_output.push_str(mm),
                    _ => (),
                }

                pprint_output.push_str(" import ");
                format_vec_alias(names, pprint_output);
            }
            StmtDesc::Pass => pprint_output.push_str("pass"),
            StmtDesc::Break => pprint_output.push_str("break"),
            StmtDesc::Continue => pprint_output.push_str("continue"),
            StmtDesc::Raise { exc, cause } => {
                pprint_output.push_str("raise");

                match &exc {
                    Some(ex) => {
                        pprint_output.push_str(" ");
                        (*ex.desc).pprint(pprint_output);
                        match &cause {
                            Some(ca) => {
                                pprint_output.push_str(" from ");
                                (*ca.desc).pprint(pprint_output);
                            }
                            _ => (),
                        }
                    }
                    _ => (),
                };
            }
            StmtDesc::Assert { test, msg } => {
                pprint_output.push_str("assert ");
                (*test.desc).pprint(pprint_output);

                match &msg {
                    Some(msg) => {
                        pprint_output.push_str(", ");
                        (*msg.desc).pprint(pprint_output);
                    }
                    _ => (),
                };
            }
            StmtDesc::Return(value) => {
                pprint_output.push_str("return");

                match &value {
                    Some(val) => {
                        pprint_output.push_str(" ");
                        (*val.desc).pprint(pprint_output);
                    }
                    _ => (),
                };
            }
            StmtDesc::Global(names) => {
                pprint_output.push_str("global ");
                format_vec_str(names, pprint_output);
            }
            StmtDesc::Nonlocal(names) => {
                pprint_output.push_str("nonlocal ");
                format_vec_str(names, pprint_output);
            }
            StmtDesc::If { test, body, orelse } => {
                format_if_stmt(test, body, orelse, pprint_output)
            }
            StmtDesc::For {
                target,
                iter,
                body,
                orelse,
                type_comment: _,
            } => format_for_stmt(target, iter, body, orelse, false, pprint_output),
            StmtDesc::AsyncFor {
                target,
                iter,
                body,
                orelse,
                type_comment: _,
            } => format_for_stmt(target, iter, body, orelse, true, pprint_output),
            StmtDesc::While { test, body, orelse } => {
                pprint_output.push_str("while ");
                (*test.desc).pprint(pprint_output);
                pprint_output.push_str(":\n");

                format_block(body, pprint_output);

                if !orelse.is_empty() {
                    pprint_output.push_str("else:\n");
                    format_block(orelse, pprint_output);
                }
            }
            StmtDesc::AsyncFunctionDef {
                name,
                args,
                body,
                decorator_list,
                returns,
                type_comment,
            } => format_funcdef(
                true,
                name,
                args,
                body,
                decorator_list,
                returns,
                type_comment,
                pprint_output,
            ),
            StmtDesc::FunctionDef {
                name,
                args,
                body,
                decorator_list,
                returns,
                type_comment,
            } => format_funcdef(
                false,
                name,
                args,
                body,
                decorator_list,
                returns,
                type_comment,
                pprint_output,
            ),
            StmtDesc::With {
                items,
                body,
                type_comment,
            } => format_with(false, items, body, type_comment, pprint_output),
            StmtDesc::AsyncWith {
                items,
                body,
                type_comment,
            } => format_with(true, items, body, type_comment, pprint_output),
            StmtDesc::Try {
                body,
                handlers,
                orelse,
                finalbody,
            } => {
                pprint_output.push_str("try:\n");
                format_block(body, pprint_output);

                for handle in handlers {
                    handle.desc.pprint(pprint_output);
                }

                if !orelse.is_empty() {
                    pprint_output.push_str("else:\n");
                    format_block(orelse, pprint_output);
                }

                if !finalbody.is_empty() {
                    pprint_output.push_str("finally:\n");
                    format_block(finalbody, pprint_output);
                }
            }
            StmtDesc::ClassDef {
                name,
                bases,
                keywords,
                body,
                decorator_list,
            } => format_class_def(name, bases, keywords, body, decorator_list, pprint_output),
            _ => pprint_output.push_str(UNKOWN_NODE_STMT), // ignore
        }
    }
}

fn format_class_def(
    name: &str,
    bases: &[Expr],
    keywords: &[Keyword],
    body: &[Stmt],
    decorator_list: &[Expr],
    pprint_output: &mut PrintHelper,
) {
    for item in decorator_list.iter() {
        pprint_output.push_str("@");
        (*item.desc).pprint(pprint_output);
        pprint_output.push_str("\n");
    }

    pprint_output.push_str(format!("class {}", name).as_str());

    if !bases.is_empty() || !keywords.is_empty() {
        //superclass_items
        pprint_output.push_str("(");
        format_vec_expr(bases, pprint_output);
        if !bases.is_empty() && !keywords.is_empty() {
            pprint_output.push_str(", ");
        }

        if !keywords.is_empty() {
            format_vec_keywords(keywords, pprint_output)
        }
        pprint_output.push_str(")");
    }

    pprint_output.push_str(":\n");

    if !body.is_empty() {
        pprint_output.inc_ident();
        match &body[0].desc {
            StmtDesc::FunctionDef { .. } | StmtDesc::ClassDef { .. } => {
                // extra newline if first item is a funcdef or classdef
                pprint_output.push_str("\n");
            }
            _ => (),
        }

        process_mod_class_fucdef_block(body, false, pprint_output);
        pprint_output.dec_ident();

        match &body.last().unwrap().desc {
            StmtDesc::FunctionDef { .. } => (),
            _ => {
                pprint_output.push_str("\n");
            }
        }
    }
}

pub fn format_with(
    is_async: bool,
    items: &[Withitem],
    body: &[Stmt],
    _type_comment: &Option<String>,
    pprint_output: &mut PrintHelper,
) {
    if is_async {
        pprint_output.push_str("async ");
    }
    pprint_output.push_str("with ");

    let mut at_least_one = false;
    for withitem in items.iter() {
        at_least_one = true;
        withitem.pprint(pprint_output);
        pprint_output.push_str(", ");
    }
    if at_least_one {
        pprint_output.pop();
        pprint_output.pop();
    }

    pprint_output.push_str(":\n");
    format_block(body, pprint_output);
}

pub fn format_funcdef(
    is_async: bool,
    name: &str,
    args: &Arguments,
    body: &[Stmt],
    decorator_list: &[Expr],
    returns: &Option<Expr>,
    _type_comment: &Option<String>,
    pprint_output: &mut PrintHelper,
) {
    for item in decorator_list.iter() {
        pprint_output.push_str("@");
        (*item.desc).pprint(pprint_output);
        pprint_output.push_str("\n");
    }
    if is_async {
        pprint_output.push_str("async def ");
    } else {
        pprint_output.push_str("def ");
    }
    pprint_output.push_str(name);
    // args are quite involved
    {
        let mut at_least_one_arg = false;
        pprint_output.push_str("(");

        {
            let mut positional_and_args = vec![];
            for it in args.posonlyargs.iter() {
                positional_and_args.push(it);
            }

            let mut pos_slash_index: i32 = positional_and_args.len() as i32;

            for it in args.args.iter() {
                positional_and_args.push(it);
            }

            // normal args - may have default values...
            let mut args_w_detaults = vec![]; // these come second
            for it in positional_and_args
                .iter()
                .rev()
                .zip(args.defaults.iter().rev())
            {
                args_w_detaults.push(it);
            }

            // printing
            // print those without defaults
            let mut w_default_cnt = positional_and_args.len() - args_w_detaults.len();
            if w_default_cnt > 0 {
                for arg_no_default in positional_and_args.iter() {
                    at_least_one_arg = true;
                    arg_no_default.pprint(pprint_output);
                    pprint_output.push_str(", ");
                    pos_slash_index -= 1;
                    if pos_slash_index == 0 {
                        pprint_output.push_str("/, ");
                    }
                    w_default_cnt -= 1;
                    if w_default_cnt == 0 {
                        break;
                    }
                }
            }
            // now for those with defaults:
            for it in args_w_detaults.iter().rev() {
                at_least_one_arg = true;
                let (arg, defaultx) = it;
                arg.pprint(pprint_output);
                pprint_output.push_str("=");
                (*defaultx.desc).pprint(pprint_output);
                pprint_output.push_str(", ");
                pos_slash_index -= 1;
                if pos_slash_index == 0 {
                    pprint_output.push_str("/, ");
                }
            }
        }

        //vararg
        match &args.vararg {
            Some(vararg) => {
                at_least_one_arg = true;
                pprint_output.push_str("*");
                vararg.pprint(pprint_output);
                pprint_output.push_str(", ");
            }
            _ => {
                if !args.kwonlyargs.is_empty() {
                    pprint_output.push_str("*, ");
                }
            }
        }

        //kwonlyargs
        for it in args.kwonlyargs.iter().zip(args.kw_defaults.iter()) {
            // normal args
            at_least_one_arg = true;
            let (kwonlyarg, kwonlyarg_default) = it;

            kwonlyarg.pprint(pprint_output);

            match kwonlyarg_default {
                Some(x) => {
                    pprint_output.push_str("=");
                    (*x.desc).pprint(pprint_output);
                }
                _ => (),
            }

            pprint_output.push_str(", ");
        }

        //...

        //kwarg
        match &args.kwarg {
            Some(kwarg) => {
                at_least_one_arg = true;
                pprint_output.push_str("**");
                kwarg.pprint(pprint_output);
                pprint_output.push_str(", ");
            }
            _ => (),
        }

        if at_least_one_arg {
            pprint_output.pop();
            pprint_output.pop();
        }

        pprint_output.push_str(")");
    }
    // args

    match &returns {
        Some(ret) => {
            pprint_output.push_str(" -> ");
            (*ret.desc).pprint(pprint_output);
        }
        _ => (),
    }

    pprint_output.push_str(":\n");
    pprint_output.inc_ident();
    process_mod_class_fucdef_block(body, true, pprint_output);
    pprint_output.dec_ident();
}

pub fn format_for_stmt(
    target: &Expr,
    iter: &Expr,
    body: &[Stmt],
    orelse: &[Stmt],
    is_async: bool,
    pprint_output: &mut PrintHelper,
) {
    if is_async {
        pprint_output.push_str("async ");
    }
    pprint_output.push_str("for ");
    (*target.desc).pprint(pprint_output);
    pprint_output.push_str(" in ");
    (*iter.desc).pprint(pprint_output);
    pprint_output.push_str(":\n");

    format_block(body, pprint_output);

    if !orelse.is_empty() {
        pprint_output.push_str("else:\n");

        format_block(orelse, pprint_output);
    }
}

pub fn format_if_stmt(
    test: &Expr,
    body: &[Stmt],
    orelse: &[Stmt],
    pprint_output: &mut PrintHelper,
) {
    pprint_output.push_str("if ");
    (*test.desc).pprint(pprint_output);
    pprint_output.push_str(":\n");

    format_block(body, pprint_output);

    let mut isfirst = true;
    for orelse in orelse.iter() {
        match &orelse.desc {
            StmtDesc::If { test, body, orelse } => {
                if isfirst {
                    pprint_output.push_ident();
                    pprint_output.push_str("el");
                }
                isfirst = false;
                format_if_stmt(test, body, orelse, pprint_output)
            }
            _ => {
                if isfirst {
                    pprint_output.push_ident();
                    pprint_output.push_str("else:\n");
                }
                isfirst = false;
                pprint_output.inc_ident();
                orelse.pprint(pprint_output);
                pprint_output.dec_ident();
            }
        }
        pprint_output.push_str("\n");
    }
    // remove last newline
    pprint_output.pop();
}

impl ExprDesc {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        match self {
            ExprDesc::Name { id, ctx: _ } => pprint_output.push_str(id),
            ExprDesc::Constant { value, kind: _ } => match value {
                Some(val) => val.pprint(pprint_output),
                _ => pprint_output.push_str("None"),
            },
            ExprDesc::List { elts, ctx: _ } => {
                pprint_output.push_str("[");
                format_vec_expr(elts, pprint_output);
                pprint_output.push_str("]");
            }
            ExprDesc::Tuple { elts, ctx: _ } => {
                pprint_output.push_str("(");

                let mut count = 0;
                for expr in elts.iter() {
                    count += 1;
                    (*expr.desc).pprint(pprint_output);
                    pprint_output.push_str(", ");
                }

                pprint_output.pop();
                if count > 1 {
                    // leave the last comma if ther is only one item in the tuple
                    pprint_output.pop();
                }

                pprint_output.push_str(")");
            }
            ExprDesc::Set(ss) => {
                pprint_output.push_str("{");
                format_vec_expr(ss, pprint_output);
                pprint_output.push_str("}");
            }
            ExprDesc::Await(arg) => {
                pprint_output.push_str("await ");
                (*arg.desc).pprint(pprint_output);
            }
            ExprDesc::Dict { keys, values } => {
                pprint_output.push_str("{");
                let mut atleastone = false;

                for (k, v) in keys.iter().zip(values.iter()) {
                    (*k.desc).pprint(pprint_output);
                    pprint_output.push_str(": ");
                    (*v.desc).pprint(pprint_output);
                    pprint_output.push_str(", ");
                    atleastone = true;
                }

                if atleastone {
                    pprint_output.pop();
                    pprint_output.pop();
                }

                pprint_output.push_str("}");
                //dd.pprint(pprint_output),
            }
            ExprDesc::Lambda { args, body } => {
                pprint_output.push_str("lambda ");

                let mut atleastone = false;
                for arg in args.args.iter() {
                    atleastone = true;
                    arg.pprint(pprint_output);
                    pprint_output.push_str(", ");
                }

                if atleastone {
                    pprint_output.pop();
                    pprint_output.pop();
                }

                pprint_output.push_str(": ");
                (*body.desc).pprint(pprint_output);
            }
            ExprDesc::UnaryOp { op, operand } => {
                op.pprint(pprint_output);
                (*operand.desc).pprint(pprint_output);
            }
            ExprDesc::Subscript {
                value,
                slice,
                ctx: _,
            } => {
                (*value.desc).pprint(pprint_output);
                pprint_output.push_str("[");

                match &(*slice.desc) {
                    ExprDesc::Tuple { elts, ctx: _ } => {
                        format_vec_expr(elts, pprint_output);
                    }
                    _ => (*slice.desc).pprint(pprint_output),
                }

                pprint_output.push_str("]");
            }
            ExprDesc::Slice { lower, upper, step } => {
                if lower.is_none() && upper.is_none() && step.is_none() {
                    pprint_output.push_str(":");
                } else {
                    match lower {
                        Some(thing) => {
                            (*thing.desc).pprint(pprint_output);
                            pprint_output.push_str(":");
                        }
                        _ => (),
                    }

                    match upper {
                        Some(thing) => {
                            match lower {
                                Some(_) => (),
                                _ => pprint_output.push_str(":"),
                            }
                            (*thing.desc).pprint(pprint_output);
                        }
                        _ => (),
                    }

                    match step {
                        Some(thing) => {
                            match lower {
                                Some(_) => (),
                                _ => pprint_output.push_str(":"),
                            }

                            pprint_output.push_str(":");

                            (*thing.desc).pprint(pprint_output);
                        }
                        _ => (),
                    }
                }
            }
            ExprDesc::BinOp { left, op, right } => {
                (left.desc).pprint(pprint_output);
                pprint_output.push_str(" ");
                op.pprint(pprint_output);
                pprint_output.push_str(" ");
                (right.desc).pprint(pprint_output);
            }
            ExprDesc::BoolOp { op, values } => {
                for value in values.iter() {
                    (*value.desc).pprint(pprint_output);
                    pprint_output.push_str(" ");
                    op.pprint(pprint_output);
                    pprint_output.push_str(" ");
                }

                //TODO: this pop method is not very pretty
                pprint_output.pop();
                pprint_output.pop();
                match op {
                    Boolop::And => {
                        pprint_output.pop();
                        pprint_output.pop();
                        pprint_output.pop();
                    }
                    Boolop::Or => {
                        pprint_output.pop();
                        pprint_output.pop();
                    }
                };
            }
            ExprDesc::Compare {
                left,
                ops,
                comparators,
            } => {
                (*left.desc).pprint(pprint_output);
                pprint_output.push_str(" ");

                for it in ops.iter().zip(comparators.iter()) {
                    let (op, comp) = it;
                    op.pprint(pprint_output);
                    pprint_output.push_str(" ");
                    (*comp.desc).pprint(pprint_output);
                    pprint_output.push_str(" ");
                }
                pprint_output.pop();
            }
            ExprDesc::Attribute {
                value,
                attr,
                ctx: _,
            } => {
                (*value.desc).pprint(pprint_output);
                pprint_output.push_str(".");
                pprint_output.push_str(attr);
            }
            ExprDesc::Call {
                func,
                args,
                keywords,
            } => {
                (*func.desc).pprint(pprint_output);
                pprint_output.push_str("(");

                let mut atleastone = false;
                for keyword_or_arg in args.iter() {
                    atleastone = true;
                    (*keyword_or_arg.desc).pprint(pprint_output);
                    pprint_output.push_str(", ");
                }
                for keyword_or_arg in keywords.iter() {
                    atleastone = true;
                    keyword_or_arg.pprint(pprint_output);
                    pprint_output.push_str(", ");
                }
                if atleastone {
                    pprint_output.pop();
                    pprint_output.pop();
                }

                pprint_output.push_str(")");
            }
            ExprDesc::Starred { value, ctx: _ } => {
                pprint_output.push_str("*");
                (*value.desc).pprint(pprint_output);
            }
            ExprDesc::IfExp { test, body, orelse } => {
                (*body.desc).pprint(pprint_output);
                pprint_output.push_str(" if ");
                (*test.desc).pprint(pprint_output);
                pprint_output.push_str(" else ");
                (*orelse.desc).pprint(pprint_output);
            }
            ExprDesc::ListComp { elt, generators } => {
                format_list_comp("[", "]", &elt.desc, generators, pprint_output);
            }
            ExprDesc::SetComp { elt, generators } => {
                format_list_comp("{", "}", &elt.desc, generators, pprint_output);
            }
            ExprDesc::GeneratorExp { elt, generators } => {
                format_list_comp("(", ")", &elt.desc, generators, pprint_output);
            }
            ExprDesc::DictComp {
                key,
                value,
                generators,
            } => {
                pprint_output.push_str("{");
                (*key.desc).pprint(pprint_output);
                pprint_output.push_str(": ");
                (*value.desc).pprint(pprint_output);
                pprint_output.push_str(" ");

                for comp in generators.iter() {
                    comp.pprint(pprint_output);
                    pprint_output.push_str(" ");
                }
                pprint_output.pop();

                pprint_output.push_str("}");
            }
            ExprDesc::NamedExpr { target, value } => {
                pprint_output.push_str("(");
                (*target.desc).pprint(pprint_output);
                pprint_output.push_str(" := ");
                (*value.desc).pprint(pprint_output);
                pprint_output.push_str(")");
            }
            ExprDesc::Yield(callx) => {
                pprint_output.push_str("yield");

                match &callx {
                    Some(val) => {
                        pprint_output.push_str(" ");
                        (*val.desc).pprint(pprint_output);
                    }
                    _ => (),
                }
            }
            ExprDesc::YieldFrom(val) => {
                pprint_output.push_str("yield from ");
                (*val.desc).pprint(pprint_output);
            }
            ExprDesc::JoinedStr(exprs) => {
                pprint_output.push_str("f");

                if exprs.len() == 1 {
                    // special logic to deal with case where f-string consists
                    // of a single string and no iterpolation nodes...
                    if let ExprDesc::Constant {
                        value: Some(ConstantDesc::Str(const_string)),
                        kind: _,
                    } = &*exprs[0].desc
                    {
                        let formatted_output = const_string.replace('{', "{{").replace('}', "}}");
                        pprint_output.push_str(&formatted_output);
                        return;
                    }
                }

                let f_string_output_start = pprint_output.current_length();
                for expr in exprs.iter() {
                    pprint_output.ignore_next_n_chars(1);

                    if let ExprDesc::Constant {
                        value: Some(ConstantDesc::Str(const_string)),
                        kind: _,
                    } = &*expr.desc
                    {
                        let formatted_output = const_string.replace('{', "{{").replace('}', "}}");
                        pprint_output.push_str(&formatted_output);
                    } else {
                        (*expr.desc).pprint(pprint_output);
                    }

                    pprint_output.pop();
                }

                let quote_type = if pprint_output.substring_contains(f_string_output_start, "'") {
                    "\""
                } else {
                    "'"
                };

                pprint_output.insert_at(f_string_output_start, quote_type);
                pprint_output.push_str(quote_type);
            }
            ExprDesc::FormattedValue {
                value,
                conversion,
                format_spec,
            } => {
                // The f-string's consists of a series of formattedValues and
                // string constant nodes. Strings are always wrapped in either
                // ' or " (depending on if they themselves contain a ') and we
                // always ignore the leading and trailing char (the ' or ")
                // via the `ignore_next_n_chars` and `pop` calls. For
                // consistency therefore, we have to add a leading and
                // trailing '
                pprint_output.push_str("'{");
                (*value.desc).pprint(pprint_output);

                if let Some(conversion) = conversion {
                    // the following magic numbers are defined in the Python
                    // language spec:
                    // https://docs.python.org/3.10/library/ast.html#ast.FormattedValue
                    pprint_output.push_str(match conversion {
                        115 => "!s",
                        114 => "!r",
                        97 => "!a",
                        _ => "",
                    });
                }

                if let Some(format_spec) = format_spec {
                    pprint_output.push_str(":");
                    pprint_output.ignore_next_n_chars(2);
                    (*format_spec.desc).pprint(pprint_output);
                    pprint_output.pop();
                }
                pprint_output.push_str("}'");
            }
        }
    }
}

fn format_list_comp(
    prefix: &str,
    postfix: &str,
    exprdesc: &ExprDesc,
    generators: &[Comprehension],
    pprint_output: &mut PrintHelper,
) {
    pprint_output.push_str(prefix);
    exprdesc.pprint(pprint_output);
    pprint_output.push_str(" ");

    for comp in generators.iter() {
        comp.pprint(pprint_output);
        pprint_output.push_str(" ");
    }
    pprint_output.pop();

    pprint_output.push_str(postfix);
}

impl Arg {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        pprint_output.push_str(&self.arg);
        match &self.annotation {
            Some(annot) => {
                pprint_output.push_str(": ");
                (*annot.desc).pprint(pprint_output);
            }
            _ => (),
        }
    }
}

fn handle_assign_rhs_yield(value: &ExprDesc, pprint_output: &mut PrintHelper) {
    // Bit of a hack but it seems that yeild when used on the rhs of an expression requires wrapping in params: ()
    match &value {
        ExprDesc::Yield(yldarg) => {
            pprint_output.push_str("(yield");
            match yldarg {
                Some(arg) => {
                    pprint_output.push_str(" ");
                    (*arg.desc).pprint(pprint_output)
                }
                _ => (),
            }
            pprint_output.push_str(")");
        }
        ExprDesc::YieldFrom(yfarg) => {
            pprint_output.push_str("(yield from ");
            (*yfarg.desc).pprint(pprint_output);
            pprint_output.push_str(")");
        }
        _ => {
            value.pprint(pprint_output);
        }
    };
}

impl Comprehension {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        pprint_output.push_str(if self.is_async { "async for " } else { "for " });
        self.target.desc.pprint(pprint_output);
        pprint_output.push_str(" in ");
        self.iter.desc.pprint(pprint_output);
        pprint_output.push_str(" ");
        for gaurd in self.ifs.iter() {
            pprint_output.push_str("if ");
            gaurd.desc.pprint(pprint_output);
            pprint_output.push_str(" ");
        }

        pprint_output.pop();
    }
}

impl Keyword {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        match &self.arg {
            Some(arg) => {
                pprint_output.push_str(arg);
                pprint_output.push_str("=");
                (*self.value.desc).pprint(pprint_output);
            }
            _ => {
                pprint_output.push_str("**");
                (*self.value.desc).pprint(pprint_output);
            }
        }
    }
}

impl Unaryop {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        let res = match self {
            Unaryop::Invert => "~",
            Unaryop::Not => "not ",
            Unaryop::UAdd => "+",
            Unaryop::USub => "-",
        };

        pprint_output.push_str(res)
    }
}

impl Operator {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        let res = match self {
            Operator::Add => "+",
            Operator::Sub => "-",
            Operator::Mult => "*",
            Operator::MatMult => "@",
            Operator::Div => "/",
            Operator::Mod => "%",
            Operator::Pow => "**",
            Operator::LShift => "<<",
            Operator::RShift => ">>",
            Operator::BitOr => "|",
            Operator::BitXor => "^",
            Operator::BitAnd => "&",
            Operator::FloorDiv => "//",
        };

        pprint_output.push_str(res)
    }
}

impl Cmpop {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        let res = match self {
            Cmpop::Eq => "==",
            Cmpop::NotEq => "!=",
            Cmpop::Lt => "<",
            Cmpop::LtE => "<=",
            Cmpop::Gt => ">",
            Cmpop::GtE => ">=",
            Cmpop::Is => "is",
            Cmpop::IsNot => "is not",
            Cmpop::In => "in",
            Cmpop::NotIn => "not in",
        };

        pprint_output.push_str(res)
    }
}

impl Boolop {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        let res = match self {
            Boolop::And => "and",
            Boolop::Or => "or",
        };

        pprint_output.push_str(res)
    }
}

impl ConstantDesc {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        match self {
            ConstantDesc::Num(Num::Int(vala)) => {
                pprint_output.push_str(&vala.to_string());
            }
            ConstantDesc::Num(Num::Float(vala)) => {
                pprint_output.push_str(&vala.to_string());
            }
            rest => {
                let res = match rest {
                    ConstantDesc::Str(vala) => vala,
                    ConstantDesc::Num(Num::BigInt(vala)) => vala,
                    ConstantDesc::Bool(true) => "True",
                    ConstantDesc::Bool(false) => "False",
                    ConstantDesc::Ellipsis => "...",
                    _ => "",
                };
                pprint_output.push_str(res)
            }
        };
    }
}

impl Withitem {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        self.context_expr.desc.pprint(pprint_output);

        if let Some(opt) = &self.optional_vars {
            pprint_output.push_str(" as ");
            opt.desc.pprint(pprint_output);
        }
    }
}

impl ExcepthandlerDesc {
    pub fn pprint(&self, pprint_output: &mut PrintHelper) {
        match self {
            ExcepthandlerDesc::ExceptHandler { type__, name, body } => {
                pprint_output.push_str("except");

                if let Some(tt) = type__ {
                    pprint_output.push_str(" ");
                    (*tt.desc).pprint(pprint_output);
                }

                if let Some(nname) = name {
                    pprint_output.push_str(" as ");
                    pprint_output.push_str(nname);
                }

                pprint_output.push_str(":\n");

                format_block(body, pprint_output);
            }
        }
    }
}
