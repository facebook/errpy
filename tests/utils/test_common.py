# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree

import json
import os
import traceback
import unittest
from os.path import exists
from typing import List, Optional, Tuple

import python.errpy.tests.utils.ast_utils as ast_utils

EXPECTED_FAILS_POSTFIX = ".expect_fails"
RESOURCES_DIR = "python/errpy/tests/test_resources/"
UNIT_TESTS_DIR = "unit_tests/"
PRETTY_PRINTER_TESTS_DIR = "pretty_printer_tests/"
ERROR_RECOVERY_TESTS_DIR = "error_recovery/"
ERROR_RECOVERY_SPECIFIC_TESTS_DIR = "error_recovery_specific_tests/"
EXPECTED_RESULTS_POSTFIX = "_expected_results"
EXPECTED_RESULTS_POSTFIX_NEW = ".new"

TEST_CONFIG_FNAME = RESOURCES_DIR + "test_config.json"

TEST_ERRPY_RESULTS_NEWFILE_CONFIG_KEY = "TEST_ERRPY_RESULTS_NEWFILE"

WRITE_EXPECTED_RESULTS_NEWFILE = False


def load_test_config():
    global WRITE_EXPECTED_RESULTS_NEWFILE
    try:
        with open(TEST_CONFIG_FNAME) as fobj:
            config = fobj.read()
            params = json.loads(config)
            WRITE_EXPECTED_RESULTS_NEWFILE = params[
                TEST_ERRPY_RESULTS_NEWFILE_CONFIG_KEY
            ]

    except Exception:
        print("Cannot load_test_config due to: {}".format(traceback.format_exc()))


load_test_config()


def read_code(
    fname: str, flavour: str = UNIT_TESTS_DIR, return_if_not_exist: Optional[str] = None
) -> str:
    to_open = RESOURCES_DIR + flavour + fname

    if not exists(to_open) and return_if_not_exist is not None:
        return return_if_not_exist

    with open(to_open) as fobj:
        return fobj.read()


def write_file(fname: str, to_write: str, flavour: str = UNIT_TESTS_DIR) -> None:
    with open(RESOURCES_DIR + flavour + fname, "w") as fobj:
        fobj.write(to_write)


def make_results_dir(dirname: str, flavour: str = UNIT_TESTS_DIR) -> str:
    full_dir_path = RESOURCES_DIR + flavour + dirname + "/"
    os.makedirs(full_dir_path, exist_ok=True)
    return dirname + "/"


def format_side_by_side(left_input: str, right_input: str) -> str:
    """Print existing and replacement text side by side"""
    ret = ""

    width = max(len(x) for x in left_input.split("\n")) + 5

    leftx = "Input:\n" + "".join(["-"] * width) + "\n" + left_input
    rightx = "ERRPY Recovered AST:\n" + "".join(["-"] * width) + "\n" + right_input

    left = [x[0 : min(len(x), width)].ljust(width) for x in leftx.split("\n")]
    right = [x[0 : min(len(x), width)].ljust(width) for x in rightx.split("\n")]

    for i in range(len(left)):
        ret += left[i]
        ret += "| "
        if i < len(right):
            ret += right[i]
        ret += "\n"
    return ret


class ASTTestCommon(unittest.TestCase):
    def splitmany_test_cases(
        self, many_fname: str, flavour: str
    ) -> List[Tuple[str, str]]:
        all_tests_Split = read_code(many_fname, flavour).split("##")
        sanitized_test_cases = []
        for caze in all_tests_Split:
            caze = caze.strip()
            lines = caze.split("\n")
            code_title = lines[0].strip()
            test_body = "\n".join(lines[1:]).strip()
            sanitized_test_cases.append((code_title, test_body))
        return sanitized_test_cases

    def check_many_cases_in_file(
        self, many_fname: str, flavour: str = UNIT_TESTS_DIR
    ) -> list[tuple[str, str]]:
        """Test many code blocks delimiatated by ##'s in many_fname
        We expect all code blocks in test resource to be cases syntatically compliant with 3.10 syntax
        May OPTIONALLY provide '.expect_fails' postfixed file for tests which are expected to fail - which specifies
        a newline delimitated list of test cases expected to fail - normally expected to be empty but a
        handy tool during development process"""

        failed_cases_file = many_fname + EXPECTED_FAILS_POSTFIX
        failed_cases_file_contents = read_code(
            failed_cases_file, flavour, return_if_not_exist=""
        )

        expect_fails = []
        if failed_cases_file_contents:
            expect_fails = [
                x.strip() for x in failed_cases_file_contents.split("\n") if x
            ]

        expect_fails_set = set(expect_fails)
        fails = []
        unexpected_fails_postfix = []

        # split into individual tests
        sanitized_test_cases = self.splitmany_test_cases(many_fname, flavour)

        for (code_title, test_body) in sanitized_test_cases:
            expected_ast = ast_utils.get_cpython_ast(test_body).strip()
            (got_ast, errors), _ = ast_utils.run_errpy(test_body)

            if errors:
                got_ast += errors
            got_ast = got_ast.strip()
            if expected_ast != got_ast:
                fails.append(code_title)
                if code_title not in expect_fails_set:
                    unexpected_fails_postfix += [code_title]
                    print("test code: %s failed..." % code_title)
                    print("\n\ntest fail\n")
                    print("Result:\n" + got_ast)
                    print("\nExpect:\n" + expected_ast)
                    print("\n\n")

        if unexpected_fails_postfix:
            failed_instances = "Unexpected failures:\n%s\n" % "\n".join(
                sorted(unexpected_fails_postfix)
            )
            print(failed_instances)
            self.fail(
                "\n%s out of %s tests failed, with %s being unexpected in: %s%s- %s"
                % (
                    len(fails),
                    len(sanitized_test_cases) - 1,
                    len(unexpected_fails_postfix),
                    many_fname,
                    (
                        " (add these to `{}{}`) ".format(
                            many_fname, EXPECTED_FAILS_POSTFIX
                        )
                    ),
                    unexpected_fails_postfix,
                )
            )
        else:
            self.assertEqual(
                sorted(fails),
                sorted(expect_fails),
                "Failed cases don't match expectation defined in: " + failed_cases_file,
            )

        return sanitized_test_cases
