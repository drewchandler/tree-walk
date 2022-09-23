use std::fmt;

use crate::token::Token;
use crate::visitor::Visitor;

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    String(String),
    Number(f64),
    Bool(bool),
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
            &Self::Number(n) => n.to_string(),
            &Self::String(ref s) => format!("\"{}\"", s),
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
    Binary {
        left: Box<Expression>,
        operator: Token,
        right: Box<Expression>,
    },
    Grouping(Box<Expression>),
    Literal(Value),
    Unary {
        operator: Token,
        expression: Box<Expression>,
    },
}

impl Expression {
    pub fn accept<T>(&self, visitor: &mut dyn Visitor<T>) -> T {
        match *self {
            Expression::Binary {
                ref left,
                ref operator,
                ref right,
            } => visitor.visit_binary(left, operator, right),
            Expression::Grouping(ref e) => visitor.visit_grouping(e),
            Expression::Literal(ref value) => visitor.visit_literal(value),
            Expression::Unary {
                ref operator,
                ref expression,
            } => visitor.visit_unary(operator, expression),
        }
    }
}
