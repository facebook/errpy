// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree

///
/// This function will remove comment's from input_code.
/// Comments are replaced with newlines so as to preserve line
/// and column information
///
/// TODO: This code will need refactoring in the future if/when we wish to
///  * Handle `# pyre-fixme:`'s better by integrating them into the AST.
///  * Outut a CST code will need refactoring.
///
/// For now this function is only used on in the context of AST production
/// so it's fit for purpose.
///
pub fn remove_comments(input_code: String) -> String {
    let without_comments = &mut String::new();
    for line in input_code.split('\n') {
        without_comments.push_str(match line.split_once('#') {
            Some((text_before_comment, _comment)) => text_before_comment,
            _ => line,
        });
        without_comments.push('\n');
    }

    without_comments.to_string()
}
