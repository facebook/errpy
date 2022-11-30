// (c) Meta Platforms, Inc. and affiliates. Confidential and proprietary.

pub mod ast_pretty_print;
pub mod ast_print;
use ast_pretty_print::PrintHelper;
use tree_sitter::Node;
use tree_sitter::Parser as TreeSitterParser;

use crate::cst_to_ast::get_node_text;
use crate::cst_to_ast::Parser as CSTToASTParser;

pub fn parse_module_print_ast_code(input_code: String, print_ast: bool) -> String {
    let mut cst_to_ast = CSTToASTParser::new(input_code);
    let to_print = match cst_to_ast.parse(false) {
        Ok(_) => format!("{}\n", cst_to_ast.get_ast_and_metadata()),
        Err(e) => format!("Failure parsing python module\n{:?}\n", e),
    };

    let pprint_output = &mut String::new();
    let printer = &mut PrintHelper::new(pprint_output, 4);

    cst_to_ast.get_ast_and_metadata().pprint(printer);

    if print_ast {
        to_print + pprint_output
    } else {
        pprint_output.to_string()
    }
}

pub struct CSTPrinter {
    code: String,
}

impl CSTPrinter {
    pub fn new(code: String) -> CSTPrinter {
        CSTPrinter { code }
    }

    // Prints the sitter nodes in their "derived `Debug` form"
    pub fn print_cst(&self) {
        let mut parser = TreeSitterParser::new();
        parser
            .set_language(tree_sitter_python::language())
            .expect("Fail to initialize TreeSitter");
        let tree = parser.parse(&self.code, None).expect("Fail to parse file");
        let root = tree.root_node();
        println!(">>> Tree-Sitter CST Nodes:\n");
        self.print_cst_node(&root, "");
    }

    fn print_cst_node(&self, node: &Node, indent: &str) {
        println!(
            "{}{:?} :: {}",
            indent,
            node,
            get_node_text(&self.code, node).replace('\n', "\\n")
        );
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            let new_indent = format!("  {}", indent);
            self.print_cst_node(&child, new_indent.as_str());
        }
    }
}
