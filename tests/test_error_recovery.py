#!/usr/bin/env fbpython
# (c) Meta Platforms, Inc. and affiliates. Confidential and proprietary.

import unittest

from python.errpy.tests.utils.error_recovery_common import ErrorRecoveryCommon


class AllLargeInputTests(ErrorRecoveryCommon):
    """These tests focus on ERRPY error recovery across a large input
    with simulated input source errors"""

    def test_simple_er_char_by_char(self) -> None:
        self.check_error_recovery_char_by_char("simple.pytest")

    def test_simple_er_insert_whitespace(self) -> None:
        self.check_error_recovery_insert_whitespace("simple.pytest")

    def test_simple_er_nth_removed(self) -> None:
        self.check_error_recovery_nth_removed("simple.pytest")


class TestSpecificInputs(ErrorRecoveryCommon):
    def test_invalid_grammar(self) -> None:
        self.compare_recovered_ast_many("invalid_grammar.pytest")

    def test_milestone_tests(self) -> None:
        self.compare_recovered_ast_many("milestone_tests.pytest")


if __name__ == "__main__":
    unittest.main()
