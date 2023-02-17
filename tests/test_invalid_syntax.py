#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree

import unittest

from python.errpy.tests.utils.error_recovery_common import ErrorRecoveryCommon
from python.errpy.tests.utils.test_common import INVALID_SYNTAX_TESTS_DIR


class ExpectedFailureTests(ErrorRecoveryCommon):
    """These tests focus aspects of invalid syntax we wish to explicitly fail on"""

    def test_invalid_keywords(self) -> None:
        self.compare_recovered_ast_many(
            "invalid_identifiers.pytest", test_dir=INVALID_SYNTAX_TESTS_DIR
        )


if __name__ == "__main__":
    unittest.main()
