// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree

#[macro_use]
extern crate rust_to_ocaml_attr;

use clap::Parser as ClapParser;

use crate::printers::CSTPrinter;

pub mod ast;
pub mod constants;
pub mod cst_to_ast;
pub mod errors;
pub mod parser_pre_process;
pub mod printers;
pub mod sitter;

/// Python Parser which will output Tree-sitter CST
#[derive(ClapParser)]
struct Args {
    /// Python code to generate CST for
    input_code: String,
}

fn main() {
    let args = <Args as clap::Parser>::parse();
    let input_code = args.input_code;
    CSTPrinter::new(input_code).print_cst();
}
