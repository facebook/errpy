// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree

#[macro_use]
extern crate rust_to_ocaml_attr;

use cst_to_ast::Parser as CSTToASTParser;
use parser_pre_process::remove_comments;

pub mod ast;
pub mod cst_to_ast;
pub mod errors;
pub mod sitter;

ocamlrep_ocamlpool::ocaml_ffi! {
    fn parse(_source_text: bstr::BString) -> Result<ast::Mod_, String> {
        let input_code_as_rust_string = format!("{}", _source_text);
        let input_without_comments = remove_comments(input_code_as_rust_string);

        let mut cst_to_ast = CSTToASTParser::new(input_without_comments);
        match cst_to_ast.parse() {
            Ok(_) => {
                let ast = cst_to_ast.ast_and_metadata.ast.unwrap();
                Ok(ast)
            }
            Err(e) => panic!("Failure parsing input\n{:?}\n", e),
        }
    }
}
