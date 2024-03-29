use std::fmt;

use crate::callable::Callable;
use crate::token::Token;

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    String(String),
    Number(f64),
    Bool(bool),
    Callable(Callable),
    Nil,
}

impl Value {
    pub fn is_truthy(&self) -> bool {
        match self {
            &Self::Nil => false,
            &Self::Bool(b) => b,
            _ => true,
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            &Self::Nil => "nil".to_owned(),
            &Self::Bool(b) => b.to_string(),
            &Self::Callable(ref c) => c.to_string(),
            &Self::Number(n) => n.to_string(),
            &Self::String(ref s) => s.clone(),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Assign {
        name: Token,
        value: Box<Expression>,
    },
    Binary {
        left: Box<Expression>,
        operator: Token,
        right: Box<Expression>,
    },
    Call {
        callee: Box<Expression>,
        paren: Token,
        arguments: Vec<Expression>,
    },
    Grouping(Box<Expression>),
    Literal(Value),
    Logical {
        left: Box<Expression>,
        operator: Token,
        right: Box<Expression>,
    },
    Unary {
        operator: Token,
        expression: Box<Expression>,
    },
    Variable(Token),
}
impl Expression {
    pub fn accept<T>(&self, visitor: &mut dyn ExpressionVisitor<T>) -> T {
        match *self {
            Self::Assign {
                ref name,
                ref value,
            } => visitor.visit_assign(name, value),
            Self::Binary {
                ref left,
                ref operator,
                ref right,
            } => visitor.visit_binary(left, operator, right),
            Self::Call {
                ref callee,
                ref paren,
                ref arguments,
            } => visitor.visit_call(callee, paren, arguments),
            Self::Grouping(ref e) => visitor.visit_grouping(e),
            Self::Literal(ref value) => visitor.visit_literal(value),
            Self::Logical {
                ref left,
                ref operator,
                ref right,
            } => visitor.visit_logical(left, operator, right),
            Self::Unary {
                ref operator,
                ref expression,
            } => visitor.visit_unary(operator, expression),
            Self::Variable(ref name) => visitor.visit_variable(name),
        }
    }
}

pub trait ExpressionVisitor<T> {
    fn visit_assign(&mut self, name: &Token, value: &Expression) -> T;
    fn visit_binary(&mut self, left: &Expression, operator: &Token, right: &Expression) -> T;
    fn visit_call(&mut self, callee: &Expression, paren: &Token, arguments: &Vec<Expression>) -> T;
    fn visit_grouping(&mut self, expression: &Expression) -> T;
    fn visit_literal(&mut self, value: &Value) -> T;
    fn visit_logical(&mut self, left: &Expression, operator: &Token, right: &Expression) -> T;
    fn visit_unary(&mut self, operator: &Token, expression: &Expression) -> T;
    fn visit_variable(&mut self, name: &Token) -> T;
}
