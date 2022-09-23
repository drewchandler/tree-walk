use std::error;
use std::fmt;

use crate::expression::{Expression, Value};
use crate::token::{Lexeme, Token};
use crate::visitor::Visitor;

#[derive(Debug, Clone, PartialEq)]
pub struct RuntimeError {
    line: u64,
    message: String,
}

impl RuntimeError {
    fn new(token: &Token, message: String) -> Self {
        Self {
            line: token.line,
            message,
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} [line: {}]", self.message, self.line)
    }
}

impl error::Error for RuntimeError {}

type InterpreterResult = Result<Value, RuntimeError>;

pub struct Interpreter;

impl Interpreter {
    fn evaluate(&mut self, expression: &Expression) -> InterpreterResult {
        expression.accept(self)
    }
}

impl Visitor<InterpreterResult> for Interpreter {
    fn visit_binary(
        &mut self,
        left: &Expression,
        operator: &Token,
        right: &Expression,
    ) -> InterpreterResult {
        let left_value = self.evaluate(left)?;
        let right_value = self.evaluate(right)?;

        match operator.lexeme {
            Lexeme::Minus => {
                let left_numeric = check_number_operand(operator, left_value)?;
                let right_numeric = check_number_operand(operator, right_value)?;

                Ok(Value::Number(left_numeric - right_numeric))
            }
            Lexeme::Slash => {
                let left_numeric = check_number_operand(operator, left_value)?;
                let right_numeric = check_number_operand(operator, right_value)?;

                Ok(Value::Number(left_numeric / right_numeric))
            }
            Lexeme::Star => {
                let left_numeric = check_number_operand(operator, left_value)?;
                let right_numeric = check_number_operand(operator, right_value)?;

                Ok(Value::Number(left_numeric * right_numeric))
            }
            Lexeme::Plus => match [left_value, right_value] {
                [Value::Number(left_numeric), Value::Number(right_numeric)] => {
                    Ok(Value::Number(left_numeric + right_numeric))
                }
                [Value::String(left_string), Value::String(ref right_string)] => {
                    Ok(Value::String(left_string + right_string))
                }
                _ => Err(RuntimeError::new(
                    operator,
                    "Operands must be two numbers or two strings.".to_owned(),
                )),
            },
            _ => Err(RuntimeError::new(
                operator,
                "Invalid binary operator.".to_owned(),
            )),
        }
    }

    fn visit_grouping(&mut self, expression: &Expression) -> InterpreterResult {
        self.evaluate(expression)
    }

    fn visit_literal(&mut self, value: &Value) -> InterpreterResult {
        Ok(value.clone())
    }

    fn visit_unary(&mut self, operator: &Token, expression: &Expression) -> InterpreterResult {
        let operand = self.evaluate(expression)?;

        match operator.lexeme {
            Lexeme::Minus => {
                let numeric_operand = check_number_operand(operator, operand)?;
                Ok(Value::Number(-numeric_operand))
            }
            Lexeme::Bang => Ok(Value::Bool(!operand.is_truthy())),
            _ => Err(RuntimeError::new(
                operator,
                "Invalid unary operator.".to_owned(),
            )),
        }
    }
}

fn check_number_operand(operator: &Token, operand: Value) -> Result<f64, RuntimeError> {
    match operand {
        Value::Number(n) => Ok(n),
        _ => Err(RuntimeError::new(
            operator,
            "Operand must be a number.".to_owned(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::{Expression, Value};
    use crate::token::{Lexeme, Token};

    #[test]
    fn it_handles_string_literal_expressions() {
        let expression = Expression::Literal(Value::String("string literal".to_owned()));

        assert_eq!(
            expression.accept(&mut Interpreter),
            Ok(Value::String("string literal".to_owned()))
        );
    }

    #[test]
    fn it_handles_number_literal_expressions() {
        let expression = Expression::Literal(Value::Number(12.0));

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Number(12.0)));
    }

    #[test]
    fn it_handles_true_boolean_literal_expressions() {
        let expression = Expression::Literal(Value::Bool(true));

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Bool(true)));
    }

    #[test]
    fn it_handles_false_boolean_literal_expressions() {
        let expression = Expression::Literal(Value::Bool(false));

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Bool(false)));
    }

    #[test]
    fn it_handles_nil_literal_expressions() {
        let expression = Expression::Literal(Value::Nil);

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Nil));
    }

    #[test]
    fn it_handles_unary_minus_expressions() {
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Minus, 0),
            expression: Box::new(Expression::Literal(Value::Number(12.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter),
            Ok(Value::Number(-12.0))
        );
    }

    #[test]
    fn it_handles_unary_minus_expressions_with_non_number_values() {
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Minus, 0),
            expression: Box::new(Expression::Literal(Value::Nil)),
        };

        assert_eq!(
            expression.accept(&mut Interpreter),
            Err(RuntimeError {
                line: 0,
                message: "Operand must be a number.".to_owned()
            })
        );
    }

    #[test]
    fn it_handles_unary_expressions_with_invalid_operators() {
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Star, 0),
            expression: Box::new(Expression::Literal(Value::Number(12.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter),
            Err(RuntimeError {
                line: 0,
                message: "Invalid unary operator.".to_owned()
            })
        );
    }

    #[test]
    fn it_handles_unary_bang_expressions_with_nil() {
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Bang, 0),
            expression: Box::new(Expression::Literal(Value::Nil)),
        };

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Bool(true)));
    }

    #[test]
    fn it_handles_unary_bang_expressions_with_false() {
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Bang, 0),
            expression: Box::new(Expression::Literal(Value::Bool(false))),
        };

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Bool(true)));
    }

    #[test]
    fn it_handles_unary_bang_expressions_with_true() {
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Bang, 0),
            expression: Box::new(Expression::Literal(Value::Bool(true))),
        };

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Bool(false)));
    }

    #[test]
    fn it_handles_unary_bang_expressions_with_numbers() {
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Bang, 0),
            expression: Box::new(Expression::Literal(Value::Number(12.0))),
        };

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Bool(false)));
    }

    #[test]
    fn it_handles_unary_bang_expressions_with_strings() {
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Bang, 0),
            expression: Box::new(Expression::Literal(Value::String("abc".to_owned()))),
        };

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Bool(false)));
    }

    #[test]
    fn it_handles_minus_binary_expressions() {
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::Number(2.0))),
            operator: Token::new(Lexeme::Minus, 0),
            right: Box::new(Expression::Literal(Value::Number(12.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter),
            Ok(Value::Number(-10.0))
        );
    }

    #[test]
    fn it_handles_plus_binary_expressions() {
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::Number(2.0))),
            operator: Token::new(Lexeme::Plus, 0),
            right: Box::new(Expression::Literal(Value::Number(12.0))),
        };

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Number(14.0)));
    }

    #[test]
    fn it_handles_plus_binary_expressions_with_strings() {
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::String("ab".to_owned()))),
            operator: Token::new(Lexeme::Plus, 0),
            right: Box::new(Expression::Literal(Value::String("cd".to_owned()))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter),
            Ok(Value::String("abcd".to_owned()))
        );
    }

    #[test]
    fn it_handles_plus_binary_expressions_with_bad_operands() {
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::Nil)),
            operator: Token::new(Lexeme::Plus, 0),
            right: Box::new(Expression::Literal(Value::String("cd".to_owned()))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter),
            Err(RuntimeError {
                line: 0,
                message: "Operands must be two numbers or two strings.".to_owned()
            })
        );
    }

    #[test]
    fn it_handles_star_binary_expressions() {
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::Number(2.0))),
            operator: Token::new(Lexeme::Star, 0),
            right: Box::new(Expression::Literal(Value::Number(12.0))),
        };

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Number(24.0)));
    }

    #[test]
    fn it_handles_slash_binary_expressions() {
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::Number(12.0))),
            operator: Token::new(Lexeme::Slash, 0),
            right: Box::new(Expression::Literal(Value::Number(2.0))),
        };

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Number(6.0)));
    }

    #[test]
    fn it_handles_arithmetic_binary_expressions_with_non_numeric_operands() {
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::Nil)),
            operator: Token::new(Lexeme::Slash, 0),
            right: Box::new(Expression::Literal(Value::Number(2.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter),
            Err(RuntimeError {
                line: 0,
                message: "Operand must be a number.".to_owned()
            })
        );
    }

    #[test]
    fn it_handles_grouping_expressions() {
        let expression = Expression::Grouping(Box::new(Expression::Literal(Value::Number(2.0))));

        assert_eq!(expression.accept(&mut Interpreter), Ok(Value::Number(2.0)));
    }
}
