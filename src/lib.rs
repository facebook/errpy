use pyo3::prelude::*;

#[macro_use]
extern crate rust_to_ocaml_attr;

use crate::printers::parse_module_print_ast_code;

pub mod ast;
pub mod cst_to_ast;
pub mod printers;
pub mod sitter;

#[pyfunction]
fn py_parse_module_print_ast_code(input_code: String) -> PyResult<String> {
    Ok(parse_module_print_ast_code(input_code, true))
}

#[pyfunction]
fn py_parse_module_print_ast_code_pretty_only(input_code: String) -> PyResult<String> {
    Ok(parse_module_print_ast_code(input_code, false))
}

/// A Python module implemented in Rust. The name of this function must match
/// the `lib.name` setting in the `Cargo.toml`, else Python will not be able to
/// import the module.
#[pymodule]
fn interop_python(_py: Python<'_>, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(py_parse_module_print_ast_code, m)?)?;
    m.add_function(wrap_pyfunction!(
        py_parse_module_print_ast_code_pretty_only,
        m
    )?)?;
    Ok(())
}
