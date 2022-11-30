# (c) Meta Platforms, Inc. and affiliates. Confidential and proprietary.


import traceback
from difflib import unified_diff
from typing import Callable, Iterator, List, Optional

import python.errpy.tests.utils.ast_utils as ast_utils
from python.errpy.tests.utils.test_common import (
    ASTTestCommon,
    ERROR_RECOVERY_SPECIFIC_TESTS_DIR,
    ERROR_RECOVERY_TESTS_DIR,
    EXPECTED_RESULTS_POSTFIX,
    EXPECTED_RESULTS_POSTFIX_NEW,
    format_side_by_side,
    make_results_dir,
    read_code,
    TEST_CONFIG_FNAME,
    TEST_ERRPY_RESULTS_NEWFILE_CONFIG_KEY,
    WRITE_EXPECTED_RESULTS_NEWFILE,
    write_file,
)


class ErrorRecoveryCommon(ASTTestCommon):
    def compare_recovered_ast_many(self, many_fname: str) -> None:
        """Iterate through series of inputs delimited by ## and check pprint ast
        of each against expected recovered pprint ast"""
        test_dir = ERROR_RECOVERY_SPECIFIC_TESTS_DIR

        # split input into individual tests
        # create directory for holding test results if not one exists already
        # generate expected results in approperiate files
        # gather test failures together for overall testcase failure
        expected_results_fname = many_fname + EXPECTED_RESULTS_POSTFIX

        got_results = ""
        for (code_title, test_body) in self.splitmany_test_cases(many_fname, test_dir):
            if code_title.startswith("#"):
                continue  # skip copywrite notice

            pprint_ast, _ = ast_utils.run_errpy(test_body, True)
            got_results += f"##{code_title}\n{pprint_ast.strip()}\n\n"

        got_results = (
            "@" + "generated\n\n" + got_results
        )  # help diff review tool undestand this to be generated

        expected_results = None
        try:
            expected_results = read_code(expected_results_fname, flavour=test_dir)
        except Exception:
            write_file(expected_results_fname, got_results, flavour=test_dir)
            self.fail(
                "No '%s' file defined, so created a new one! Check this document and ensure results match expectation. Future runs will treat contents as correct test result"
                % (expected_results_fname)
            )

        # great now we can check the results against what's expected
        if expected_results != got_results:
            if WRITE_EXPECTED_RESULTS_NEWFILE:
                new_results_fname = (
                    expected_results_fname + EXPECTED_RESULTS_POSTFIX_NEW
                )
                print(
                    "test config variable: '{}' is set in '{}'. Writing results to new file: '{}' (for diffing etc)".format(
                        TEST_ERRPY_RESULTS_NEWFILE_CONFIG_KEY,
                        TEST_CONFIG_FNAME,
                        new_results_fname,
                    )
                )
                try:
                    write_file(new_results_fname, got_results, flavour=test_dir)
                    print(f"new file write of: {new_results_fname} complete")
                except Exception:
                    print(
                        "new file write failed due to: {}".format(
                            traceback.format_exc()
                        )
                    )

            print("Test for: %s failed:\n" % (many_fname))
            expected_results = expected_results or ""

            diff = unified_diff(
                pprint_ast.splitlines(keepends=True),
                expected_results.splitlines(keepends=True),
            )
            print("".join(diff), end="")

            print("\n\n")

            self.fail("Test for: %s failed" % (many_fname))

    def check_error_recovery_char_by_char(self, many_fname: str) -> None:
        def generator(
            test_body: str, skip_comments_and_whitespace: bool
        ) -> Iterator[tuple[int, str, bool, str, str, list[str], str]]:
            char_no = -1
            last_few_chars_input = []
            curr_body = ""
            in_comment = False
            for charr in test_body:
                # we progress char by char
                char_no += 1
                last_few_chars_input.append(charr)
                if len(last_few_chars_input) > 30:
                    last_few_chars_input.pop(0)

                if skip_comments_and_whitespace:
                    # probably don't want to skip for CST
                    curr_body += charr
                    if charr == " ":
                        continue

                    if in_comment:
                        if charr == "\n":
                            in_comment = False
                        else:
                            continue
                    if charr == "#":
                        in_comment = True
                        continue

                got_ast, errpy_panic = ast_utils.run_errpy(curr_body.strip(), True)
                got_ast = got_ast.strip()

                # show diff of input code and error recovered outcome

                diff = "".join(
                    unified_diff(
                        got_ast.splitlines(keepends=True),
                        curr_body.splitlines(keepends=True),
                    )
                )

                yield (
                    char_no,
                    charr,
                    errpy_panic,
                    curr_body,
                    got_ast,
                    last_few_chars_input,
                    diff,
                )

        self._check_error_recovery(many_fname, ".tailtest.", generator)

    def make_progressive_test_gennerator(
        self, is_white_space_test: bool
    ) -> Callable[
        [str, bool], Iterator[tuple[int, str, bool, str, str, list[str], str]]
    ]:
        def generator(
            test_body: str, skip_comments_and_whitespace: bool
        ) -> Iterator[tuple[int, str, bool, str, str, list[str], str]]:
            last_few_chars_input = []
            in_comment = False
            for (char_no, charr) in enumerate(test_body):
                # we progress char by char
                last_few_chars_input.append(charr)
                if len(last_few_chars_input) > 30:
                    last_few_chars_input.pop(0)

                if skip_comments_and_whitespace:
                    # probably don't want to skip for CST
                    if charr == " ":
                        continue

                    if in_comment:
                        if charr == "\n":
                            in_comment = False
                        else:
                            continue
                    if charr == "#":
                        in_comment = True
                        continue

                if is_white_space_test:
                    curr_body = test_body[:char_no] + " " + test_body[char_no:]
                else:
                    # remove nth test
                    curr_body = test_body[:char_no] + test_body[char_no + 1 :]

                region_of_interest = curr_body[max(char_no - 10, 0) : char_no + 10]

                got_ast, errpy_panic = ast_utils.run_errpy(curr_body.strip(), True)
                got_ast = got_ast.strip()

                # show diff of input code and error recovered outcome

                diff = "".join(
                    unified_diff(
                        got_ast.splitlines(keepends=True),
                        curr_body.splitlines(keepends=True),
                    )
                )

                yield (
                    char_no,
                    region_of_interest,
                    errpy_panic,
                    curr_body,
                    got_ast,
                    last_few_chars_input,
                    diff,
                )

        return generator

    def check_error_recovery_insert_whitespace(self, many_fname: str) -> None:
        self._check_error_recovery(
            many_fname,
            ".insert_whitespace.",
            self.make_progressive_test_gennerator(True),
        )

    def check_error_recovery_nth_removed(self, many_fname: str) -> None:
        self._check_error_recovery(
            many_fname, ".nth_removed.", self.make_progressive_test_gennerator(False)
        )

    def _check_error_recovery(
        self,
        many_fname: str,
        test_name: str,
        gennerator: Callable[
            [str, bool], Iterator[tuple[int, str, bool, str, str, list[str], str]]
        ],
        flavour: str = ERROR_RECOVERY_TESTS_DIR,
        skip_comments_and_whitespace: bool = True,
    ) -> None:
        """Runs a series of tests to investigate error recovery in the following scenarios for the given input:
        1. Progressively building up the input to the parser char by char and seeing how much of an AST can be built for any particular input. - check_error_recovery_char_by_char
        2. Inserting a whitespace ` ` character char by char on the overall input. - check_error_recovery_insert_whitespace
        3. Trying the input with nth character from the input stream removed. - check_error_recovery_nth_removed

        the scenarious of implemented as generators operating over the given input

        We must ensure that:
        1. ERRPY doesn't panic,
        2. ERRPY doesn't produce an empty AST
        3. and we must also ensure that the AST output is as desired in order to satisfy the requirements of the client's
        e.g. supporting dot completion, partial function argument narrowing, etc"""
        # basic 'sanity check' to ensue final state of input will produce a valid AST before continuing
        sanitized_test_cases = self.check_many_cases_in_file(
            many_fname, flavour=flavour
        )

        # split input into individual tests
        # create directory for holding test results if not one exists already
        # generate expected results in approperiate files
        # gather test failures together for overall testcase failure
        expected_results_dir = make_results_dir(
            many_fname + test_name + EXPECTED_RESULTS_POSTFIX, flavour
        )

        fail_cases = []

        for (code_title, test_body) in sanitized_test_cases:
            if code_title.startswith("#"):
                continue  # skip copywrite notice

            # we prevoiusly validated that the input code is syntatically valid.
            # now we ensure that the input code for the test is formatted as par the
            # implicit formatting scheme of our ast pretty printer - which outputs
            # Python code from the AST.
            # We do this by writing over the test_body with the output of ERRPPY
            test_body, _ = ast_utils.run_errpy(test_body, True)

            expected_results_fname = (
                expected_results_dir
                + code_title.replace(" ", "-")
                + EXPECTED_RESULTS_POSTFIX
            )

            expected_results = None
            try:
                expected_results = read_code(expected_results_fname, flavour=flavour)
            except Exception:
                pass

            results = ""  # help diff review tool undestand this to be generated
            errpy_panics = []  # we want to avoid these
            empty_asts = []  # this is usually a bad thing

            for iteration in gennerator(test_body, skip_comments_and_whitespace):
                (
                    char_no,
                    charr,
                    errpy_panic,
                    curr_body,
                    got_ast,
                    last_few_chars_input,
                    diff,
                ) = iteration
                if diff.strip() == "":
                    diff = "No difference - AST matches, fully recovered!"

                results += "{}. Input. char of interest: '{}':\n\n{}\n\nERRPY Recovered AST diff:\n{}\n\n===============================================================================\n".format(
                    char_no,
                    "\\n" if charr == "\n" else charr,
                    format_side_by_side(curr_body, got_ast),
                    diff,
                )
                if errpy_panic:
                    errpy_panics.append(
                        "{}.->{}<-".format(char_no, "".join(last_few_chars_input))
                    )

                if got_ast == "":
                    empty_asts.append(
                        "{}.->{}<-".format(char_no, "".join(last_few_chars_input))
                    )

            if empty_asts:
                results = "Errpy makes empty AST (weird) with input prior to and including:\n{}\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n{}".format(
                    "\n\n".join(empty_asts),
                    results,
                )

            if errpy_panics:
                results = "Errpy panics (really bad) with input prior to and including:\n{}\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n{}".format(
                    "\n\n".join(errpy_panics),
                    results,
                )

            results = (
                "@" + "generated\n\n" + results
            )  # help diff review tool undestand this to be generated

            self._compare_results(
                code_title,
                expected_results,
                results,
                expected_results_fname,
                flavour,
                fail_cases,
            )

        if fail_cases:
            self.fail("Following subtests failed: %s" % (fail_cases))

    def _compare_results(
        self,
        code_title: str,
        expected_results: Optional[str],
        results: str,
        expected_results_fname: str,
        flavour: str,
        fail_cases: List[str],
    ) -> None:
        if expected_results is None:
            write_file(expected_results_fname, results, flavour=flavour)
            print(
                "No '%s' file defined, so created a new one! Check this document and ensure results match expectation. Future runs will treat contents as correct test result"
                % (expected_results_fname)
            )
            fail_cases.append(code_title)
        else:
            # great now we can check the results against what's expected
            if expected_results != results:
                if WRITE_EXPECTED_RESULTS_NEWFILE:
                    new_results_fname = (
                        expected_results_fname + EXPECTED_RESULTS_POSTFIX_NEW
                    )
                    print(
                        "test config variable: '{}' is set in '{}'. Writing results to new file: '{}' (for diffing etc)".format(
                            TEST_ERRPY_RESULTS_NEWFILE_CONFIG_KEY,
                            TEST_CONFIG_FNAME,
                            new_results_fname,
                        )
                    )
                    try:
                        write_file(new_results_fname, results, flavour=flavour)
                        print("new file write complete")
                    except Exception:
                        print(
                            "new file write failed due to: {}".format(
                                traceback.format_exc()
                            )
                        )

                print("test code: %s failed..." % code_title)
                print("\n\ntest fail\n")

                diff = unified_diff(
                    results.splitlines(keepends=True),
                    expected_results.splitlines(keepends=True),
                )
                print("".join(diff), end="")

                print("\n\n")

                fail_cases.append(code_title)
