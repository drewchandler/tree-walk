use std::fmt;

use crate::expression::Value;
use crate::interpreter::Interpreter;
use crate::interpreter::InterpreterResult;

#[derive(Clone)]
pub enum Callable {
    BuiltIn {
        arity: usize,
        func: fn(interpreter: &mut Interpreter, Vec<Value>) -> InterpreterResult,
    },
}

impl Callable {
    pub fn arity(self: &Self) -> usize {
        match self {
            Self::BuiltIn { arity, .. } => *arity,
        }
    }

    pub fn call(
        self: &Self,
        interpreter: &mut Interpreter,
        arguments: Vec<Value>,
    ) -> InterpreterResult {
        match self {
            Self::BuiltIn { func, .. } => func(interpreter, arguments),
        }
    }

    pub fn to_string(&self) -> String {
        "<native fn>".to_owned()
    }
}

impl PartialEq for Callable {
    fn eq(&self, _: &Callable) -> bool {
        todo!()
    }
}

impl fmt::Debug for Callable {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        todo!()
    }
}
