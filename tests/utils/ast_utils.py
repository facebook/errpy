# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree

import ast

from python.errpy.src import ffi_python


def get_cpython_ast(
    source: str, raise_exception: bool = False, pretty_print: bool = True
) -> str:
    try:
        ast_inst = ast.parse(source)
        ast_dump = ast.dump(ast_inst, include_attributes=True)
        if pretty_print:
            return (
                ast_dump
                + "\n"
                # pyre-ignore # unparse exists in 3.10 only...
                + ast.unparse(ast_inst)
            )
        else:
            return ast_dump
    except BaseException as e:
        if raise_exception:
            raise e
        return "Invalid CPython Syntax: " + str(e)


def run_errpy(
    source: str, just_pretty_print_ast: bool = False
) -> tuple[tuple[str, str], bool]:
    """returns: (result, did_errpy_panic)"""
    try:
        if just_pretty_print_ast:
            return (
                ffi_python.py_parse_module_print_ast_pretty_print_only(source),
                False,
            )
        return (ffi_python.py_parse_module_print_ast_and_pretty_print(source), False)
    except BaseException as e:
        return (("ERRPY Failure: " + str(e), ""), True)


def run_errpy_ast_only(
    source: str,
) -> tuple[tuple[str, str], bool]:
    """returns: (result, did_errpy_panic)"""
    try:
        return (
            ffi_python.py_parse_module_print_ast(source),
            False,
        )
    except BaseException as e:
        return (("ERRPY Failure: " + str(e), ""), True)
