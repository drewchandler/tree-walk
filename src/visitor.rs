use crate::expression::{Expression, Value};
use crate::token::Token;

pub trait Visitor<T> {
    fn visit_binary(&mut self, left: &Expression, operator: &Token, right: &Expression) -> T;
    fn visit_grouping(&mut self, expression: &Expression) -> T;
    fn visit_literal(&mut self, value: &Value) -> T;
    fn visit_unary(&mut self, operator: &Token, expression: &Expression) -> T;
}
