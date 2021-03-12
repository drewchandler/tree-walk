use std::error;
use std::fmt;

use crate::token::Token;

#[derive(Debug, Clone, PartialEq)]
pub struct RuntimeError {
    line: u64,
    message: String,
}

impl RuntimeError {
    pub fn new(line: u64, message: String) -> Self {
        Self { line, message }
    }

    pub fn from_token(token: &Token, message: String) -> Self {
        Self::new(token.line, message)
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} [line: {}]", self.message, self.line)
    }
}

impl error::Error for RuntimeError {}
