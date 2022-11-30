#!/usr/bin/env fbpython
# (c) Meta Platforms, Inc. and affiliates. Confidential and proprietary.

import unittest

import python.errpy.tests.utils.ast_utils as ast_utils

from python.errpy.tests.utils.test_common import read_code


class TestSandbox(unittest.TestCase):
    """The sandbox area can be used in order to test ERRPY syntax and compare
    the output AST with that produced by CPython."""

    def check_ast_file(self, fname: str, verbose=False) -> None:
        code = read_code(fname)
        expected = ast_utils.get_cpython_ast(code).strip()
        got_ast, _ = ast_utils.run_errpy(code)
        got_ast = got_ast.strip()

        if got_ast != expected:
            print("\n\ntest fail\n")
            print("Result:\n" + got_ast)
            print("\nExpect:\n" + expected)

            self.assertEqual(got_ast, expected)

        if verbose:
            print("Result:\n" + got_ast)

    def test_sandbox(self) -> None:
        self.check_ast_file("sandbox.pytest", True)


if __name__ == "__main__":
    unittest.main()
