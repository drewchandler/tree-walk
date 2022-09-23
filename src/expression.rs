use crate::token::Token;
use crate::visitor::Visitor;

pub enum Expression {
    Binary {
        left: Box<Expression>,
        operator: Token,
        right: Box<Expression>,
    },
    Grouping(Box<Expression>),
    Literal(f64),
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
            Expression::Literal(value) => visitor.visit_literal(value),
            Expression::Unary {
                ref operator,
                ref expression,
            } => visitor.visit_unary(operator, expression),
        }
    }
}
