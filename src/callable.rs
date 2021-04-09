use crate::environment::env_define;
use std::fmt;

use crate::environment::env_new;
use crate::expression::Value;
use crate::interpreter::{Interpreter, InterpreterResult};
use crate::statement::Statement;
use crate::token::Token;

#[derive(Clone)]
pub enum Callable {
    BuiltIn {
        arity: usize,
        func: fn(interpreter: &mut Interpreter, Vec<Value>) -> InterpreterResult,
    },
    UserDefined {
        name: String,
        params: Vec<Token>,
        body: Box<Statement>,
    },
}

impl Callable {
    pub fn arity(self: &Self) -> usize {
        match self {
            Self::BuiltIn { arity, .. } => *arity,
            Self::UserDefined { params, .. } => params.len(),
        }
    }

    pub fn call(
        self: &Self,
        interpreter: &mut Interpreter,
        arguments: Vec<Value>,
    ) -> InterpreterResult {
        match self {
            Self::BuiltIn { func, .. } => func(interpreter, arguments),
            Self::UserDefined { params, body, .. } => {
                let call_env = env_new(Some(&interpreter.environment));

                for (p, a) in params.iter().zip(arguments.iter()) {
                    env_define(&call_env, p, a.clone());
                }

                let mut block_interpreter =
                    Interpreter::new_with_environment(interpreter.output, call_env);

                block_interpreter.execute(body)
            }
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            Self::BuiltIn { .. } => "<native fn>".to_owned(),
            Self::UserDefined { name, .. } => format!("<fn {}>", name),
        }
    }
}

impl PartialEq for Callable {
    fn eq(&self, other: &Callable) -> bool {
        return self == other;
    }
}

impl fmt::Debug for Callable {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        todo!()
    }
}
