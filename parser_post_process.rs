// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree

#[derive(Debug)]
pub struct ParserPostprocessor {}

impl ParserPostprocessor {
    pub fn new() -> Self {
        ParserPostprocessor {}
    }

    // Private functions will be added hear to abstract the post-processing logic
    // Only `new` and `postprocess` methods will be exposed

    pub fn postprocess(self, input_code: &str) -> String {
        input_code.to_string()
    }
}
