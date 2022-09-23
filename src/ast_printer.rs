use crate::expression::Expression;
use crate::token::Token;
use crate::visitor::Visitor;

pub struct AstPrinter;

impl AstPrinter {
    pub fn parenthesize(&mut self, name: String, expressions: &[&Expression]) -> String {
        let mut parts: Vec<String> = Vec::new();
        parts.push(name);

        for e in expressions {
            parts.push(e.accept(self));
        }

        format!("({})", parts.join(" "))
    }
}

impl Visitor<String> for AstPrinter {
    fn visit_binary(&mut self, left: &Expression, operator: &Token, right: &Expression) -> String {
        self.parenthesize(operator.to_string(), &[left, right])
    }

    fn visit_grouping(&mut self, expression: &Expression) -> String {
        self.parenthesize("group".to_owned(), &[expression])
    }

    fn visit_literal(&mut self, value: &Token) -> String {
        value.to_string()
    }

    fn visit_unary(&mut self, operator: &Token, expression: &Expression) -> String {
        self.parenthesize(operator.to_string(), &[expression])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::Expression;
    use crate::token::{Lexeme, Token};

    #[test]
    fn it_works() {
        let expression = Expression::Binary {
            left: Box::new(Expression::Unary {
                operator: Token::new(Lexeme::Minus, 0),
                expression: Box::new(Expression::Literal(Token::new(Lexeme::Number(123.0), 0))),
            }),
            operator: Token::new(Lexeme::Star, 0),
            right: Box::new(Expression::Grouping(Box::new(Expression::Literal(
                Token::new(Lexeme::Number(45.67), 0),
            )))),
        };

        assert_eq!(
            expression.accept(&mut AstPrinter),
            "(* (- 123) (group 45.67))"
        );
    }
}
