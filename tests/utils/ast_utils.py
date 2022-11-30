# (c) Meta Platforms, Inc. and affiliates. Confidential and proprietary.

import ast

# pyre-ignore
from python.errpy import interop_python


def get_cpython_ast(source: str) -> str:
    try:
        ast_inst = ast.parse(source)
        return (
            ast.dump(ast_inst, include_attributes=True)
            + "\n"
            # pyre-ignore # unparse exists in 3.10 only...
            + ast.unparse(ast_inst)
        )
    except BaseException as e:
        return "Invalid CPython Syntax: " + str(e)


def run_errpy(source: str, just_pretty_print_ast: bool = False) -> tuple[str, bool]:
    """returns: (result, did_errpy_panic)"""
    try:
        if just_pretty_print_ast:
            return (
                interop_python.py_parse_module_print_ast_code_pretty_only(source),
                False,
            )
        return (interop_python.py_parse_module_print_ast_code(source), False)
    except BaseException as e:
        return ("ERRPY Failure: " + str(e), True)
