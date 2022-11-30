// (c) Meta Platforms, Inc. and affiliates. Confidential and proprietary.

#[macro_use]
extern crate rust_to_ocaml_attr;

use crate::printers::parse_module_print_ast_code;

pub mod ast;
pub mod cst_to_ast;
pub mod printers;
pub mod sitter;

/// Python Parser which will output AST and optional pretty print of input code from derived AST
#[derive(clap::Parser)]
struct Args {
    /// Python code to generate AST for input string
    input_code: String,
}

fn main() {
    let args = <Args as clap::Parser>::parse();

    let input_code = args.input_code;
    println!("{}", parse_module_print_ast_code(input_code, true));
}
