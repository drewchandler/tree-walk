use crate::expression::Expression;
use crate::token::Token;

pub trait Visitor<T> {
    fn visit_binary(&mut self, left: &Expression, operator: &Token, right: &Expression) -> T;
    fn visit_grouping(&mut self, expression: &Expression) -> T;
    fn visit_literal(&mut self, value: f64) -> T;
    fn visit_unary(&mut self, operator: &Token, expression: &Expression) -> T;
}
