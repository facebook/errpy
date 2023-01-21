// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree

#[derive(Debug, thiserror::Error)]
pub enum ParserError {
    #[error("failed to set tree_sitter language: {0}")]
    Language(#[from] tree_sitter::LanguageError),
    #[error("parser timed out or was cancelled")]
    DidNotComplete,
}

#[derive(Debug, thiserror::Error)]
pub enum RecoverableError {
    #[error("encountered unexpected expression")]
    UnexpectedExpression(String),
    #[error("encountered unimplemented expression")]
    UnimplementedStatement(String),
    #[error("expected a node, but it was missing")]
    MissingChild, // TODO: add String parameter to state which child is missing
    #[error("expected comparison to have lhs node, but it was missing")]
    MissingLhs,
    #[error("expected BinaryOperator node, but got unexpected node kind: {0}")]
    MissingOperator(String),
}
