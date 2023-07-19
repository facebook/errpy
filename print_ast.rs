// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree

#[macro_use]
extern crate rust_to_ocaml_attr;

use crate::printers::parse_module_print_ast_code;
use crate::printers::PrintingMode;

pub mod ast;
pub mod constants;
pub mod cst_to_ast;
pub mod errors;
pub mod node_wrapper;
pub mod parser_post_process;
pub mod parser_pre_process;
pub mod printers;
pub mod sitter;
pub mod string_helpers;

/// Python Parser which will output AST and optional pretty print of input code from derived AST
#[derive(clap::Parser)]
struct Args {
    /// Python code to generate AST for input string
    input_code: String,
}

fn main() {
    let args = <Args as clap::Parser>::parse();

    let input_code = args.input_code;
    let (ast, errors) = parse_module_print_ast_code(input_code, PrintingMode::ASTAndPrettyPrintAST);
    if errors.is_empty() {
        println!("{}", ast);
    } else {
        print!("{}\n{}", ast, errors);
    }
}
