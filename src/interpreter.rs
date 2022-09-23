use std::error;
use std::fmt;
use std::io;

use crate::callable::Callable;
use crate::environment::{env_assign, env_define, env_get, env_new, env_root, Environment};
use crate::errors::RuntimeError;
use crate::expression::{Expression, ExpressionVisitor, Value};
use crate::statement::{Statement, StatementVisitor};
use crate::token::{Lexeme, Token};

#[derive(Debug)]
pub enum ErrorOrReturn {
    Error(RuntimeError),
    Return(Value),
}

impl fmt::Display for ErrorOrReturn {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Error(ref e) => e.fmt(f),
            Self::Return(ref v) => write!(f, "{}", v.to_string()),
        }
    }
}

impl error::Error for ErrorOrReturn {}

impl From<RuntimeError> for ErrorOrReturn {
    fn from(error: RuntimeError) -> Self {
        Self::Error(error)
    }
}

pub type InterpreterResult = Result<Value, ErrorOrReturn>;

pub struct Interpreter<'a> {
    pub output: &'a mut dyn io::Write,
    pub environment: Environment,
}

impl<'a> Interpreter<'a> {
    pub fn new_with_environment(output: &'a mut dyn io::Write, environment: Environment) -> Self {
        Self {
            output,
            environment,
        }
    }

    pub fn new(output: &'a mut dyn io::Write) -> Self {
        Self::new_with_environment(output, env_root())
    }

    pub fn execute(&mut self, statement: &Statement) -> InterpreterResult {
        statement.accept(self)
    }

    fn evaluate(&mut self, expression: &Expression) -> InterpreterResult {
        expression.accept(self)
    }
}

impl<'a> ExpressionVisitor<InterpreterResult> for Interpreter<'a> {
    fn visit_assign(&mut self, name: &Token, value: &Expression) -> InterpreterResult {
        let expression_value = value.accept(self)?;

        env_assign(&self.environment, name, expression_value.clone())?;

        Ok(expression_value)
    }

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
                _ => Err(ErrorOrReturn::Error(RuntimeError::from_token(
                    operator,
                    "Operands must be two numbers or two strings.".to_owned(),
                ))),
            },
            Lexeme::Less => {
                let left_numeric = check_number_operand(operator, left_value)?;
                let right_numeric = check_number_operand(operator, right_value)?;

                Ok(Value::Bool(left_numeric < right_numeric))
            }
            Lexeme::LessEqual => {
                let left_numeric = check_number_operand(operator, left_value)?;
                let right_numeric = check_number_operand(operator, right_value)?;

                Ok(Value::Bool(left_numeric <= right_numeric))
            }
            Lexeme::Greater => {
                let left_numeric = check_number_operand(operator, left_value)?;
                let right_numeric = check_number_operand(operator, right_value)?;

                Ok(Value::Bool(left_numeric > right_numeric))
            }
            Lexeme::GreaterEqual => {
                let left_numeric = check_number_operand(operator, left_value)?;
                let right_numeric = check_number_operand(operator, right_value)?;

                Ok(Value::Bool(left_numeric >= right_numeric))
            }
            Lexeme::EqualEqual => Ok(Value::Bool(left_value == right_value)),
            Lexeme::BangEqual => Ok(Value::Bool(left_value != right_value)),
            ref l => Err(ErrorOrReturn::Error(RuntimeError::from_token(
                operator,
                format!("Invalid binary operator '{:?}'.", l),
            ))),
        }
    }

    fn visit_call(
        &mut self,
        callee: &Expression,
        paren: &Token,
        arguments: &Vec<Expression>,
    ) -> InterpreterResult {
        let callee_value = self.evaluate(callee)?;
        let argument_values = arguments
            .iter()
            .map(|a| self.evaluate(a))
            .collect::<Result<Vec<_>, _>>()?;

        match callee_value {
            Value::Callable(ref c) => {
                if c.arity() != argument_values.len() {
                    return Err(ErrorOrReturn::Error(RuntimeError::from_token(
                        paren,
                        format!(
                            "Expected {} arguments but got {}.",
                            c.arity(),
                            argument_values.len()
                        ),
                    )));
                }

                c.call(self, argument_values)
            }
            _ => Err(ErrorOrReturn::Error(RuntimeError::from_token(
                paren,
                "Can only call functions and classes".to_owned(),
            ))),
        }
    }

    fn visit_grouping(&mut self, expression: &Expression) -> InterpreterResult {
        self.evaluate(expression)
    }

    fn visit_literal(&mut self, value: &Value) -> InterpreterResult {
        Ok(value.clone())
    }

    fn visit_logical(
        &mut self,
        left: &Expression,
        operator: &Token,
        right: &Expression,
    ) -> InterpreterResult {
        let left_value = self.evaluate(left)?;

        match operator.lexeme {
            Lexeme::Or => {
                if left_value.is_truthy() {
                    Ok(left_value)
                } else {
                    self.evaluate(right).map(|r| Ok(r))?
                }
            }
            Lexeme::And => {
                if left_value.is_truthy() {
                    self.evaluate(right).map(|r| Ok(r))?
                } else {
                    Ok(left_value)
                }
            }
            _ => Err(ErrorOrReturn::Error(RuntimeError::from_token(
                operator,
                "Invalid logical operator.".to_owned(),
            ))),
        }
    }

    fn visit_unary(&mut self, operator: &Token, expression: &Expression) -> InterpreterResult {
        let operand = self.evaluate(expression)?;

        match operator.lexeme {
            Lexeme::Minus => {
                let numeric_operand = check_number_operand(operator, operand)?;
                Ok(Value::Number(-numeric_operand))
            }
            Lexeme::Bang => Ok(Value::Bool(!operand.is_truthy())),
            _ => Err(ErrorOrReturn::Error(RuntimeError::from_token(
                operator,
                "Invalid unary operator.".to_owned(),
            ))),
        }
    }

    fn visit_variable(&mut self, name: &Token) -> InterpreterResult {
        env_get(&self.environment, name).map_err(|e| ErrorOrReturn::Error(e))
    }
}

impl<'a> StatementVisitor<InterpreterResult> for Interpreter<'a> {
    fn visit_block(&mut self, statements: &Vec<Statement>) -> InterpreterResult {
        let mut block_interpreter =
            Interpreter::new_with_environment(self.output, env_new(Some(&self.environment)));

        for s in statements {
            s.accept(&mut block_interpreter)?;
        }

        Ok(Value::Nil)
    }

    fn visit_expression(&mut self, expression: &Expression) -> InterpreterResult {
        self.evaluate(expression)?;

        Ok(Value::Nil)
    }

    fn visit_function(
        &mut self,
        name: &Token,
        params: &Vec<Token>,
        body: &Box<Statement>,
    ) -> InterpreterResult {
        env_define(
            &self.environment,
            name,
            Value::Callable(Callable::UserDefined {
                name: name.identifier(),
                params: params.clone(),
                body: body.clone(),
                closure: env_new(Some(&self.environment)),
            }),
        );

        Ok(Value::Nil)
    }

    fn visit_if(
        &mut self,
        condition: &Expression,
        then_branch: &Statement,
        else_branch: Option<&Statement>,
    ) -> InterpreterResult {
        if self.evaluate(condition)?.is_truthy() {
            then_branch.accept(self)?;
        } else if let Some(e) = else_branch {
            e.accept(self)?;
        };

        Ok(Value::Nil)
    }

    fn visit_return(&mut self, expression: Option<&Expression>) -> InterpreterResult {
        let value = if let Some(e) = expression {
            self.evaluate(e)?
        } else {
            Value::Nil
        };

        Err(ErrorOrReturn::Return(value))
    }

    fn visit_print(&mut self, expression: &Expression) -> InterpreterResult {
        let value = self.evaluate(expression)?;

        write!(&mut self.output, "{}\n", value).unwrap();

        Ok(Value::Nil)
    }

    fn visit_var(&mut self, name: &Token, initializer: Option<&Expression>) -> InterpreterResult {
        let mut value = Value::Nil;

        if let Some(expression) = initializer {
            let expression_value = self.evaluate(&expression)?;
            value = expression_value;
        }

        env_define(&self.environment, name, value);

        Ok(Value::Nil)
    }

    fn visit_while(&mut self, condition: &Expression, body: &Statement) -> InterpreterResult {
        while self.evaluate(condition)?.is_truthy() {
            body.accept(self)?;
        }

        Ok(Value::Nil)
    }
}

fn check_number_operand(operator: &Token, operand: Value) -> Result<f64, RuntimeError> {
    match operand {
        Value::Number(n) => Ok(n),
        _ => Err(RuntimeError::from_token(
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
        let mut output = Vec::new();
        let expression = Expression::Literal(Value::String("string literal".to_owned()));

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::String("string literal".to_owned()))
        );
    }

    #[test]
    fn it_handles_number_literal_expressions() {
        let mut output = Vec::new();
        let expression = Expression::Literal(Value::Number(12.0));

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Number(12.0))
        );
    }

    #[test]
    fn it_handles_true_boolean_literal_expressions() {
        let mut output = Vec::new();
        let expression = Expression::Literal(Value::Bool(true));

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Bool(true))
        );
    }

    #[test]
    fn it_handles_false_boolean_literal_expressions() {
        let mut output = Vec::new();
        let expression = Expression::Literal(Value::Bool(false));

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Bool(false))
        );
    }

    #[test]
    fn it_handles_nil_literal_expressions() {
        let mut output = Vec::new();
        let expression = Expression::Literal(Value::Nil);

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Nil)
        );
    }

    #[test]
    fn it_handles_unary_minus_expressions() {
        let mut output = Vec::new();
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Minus, 0),
            expression: Box::new(Expression::Literal(Value::Number(12.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Number(-12.0))
        );
    }

    #[test]
    fn it_handles_unary_minus_expressions_with_non_number_values() {
        let mut output = Vec::new();
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Minus, 0),
            expression: Box::new(Expression::Literal(Value::Nil)),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Err(RuntimeError::new(0, "Operand must be a number.".to_owned()))
        );
    }

    #[test]
    fn it_handles_unary_expressions_with_invalid_operators() {
        let mut output = Vec::new();
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Star, 0),
            expression: Box::new(Expression::Literal(Value::Number(12.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Err(RuntimeError::new(0, "Invalid unary operator.".to_owned()))
        );
    }

    #[test]
    fn it_handles_unary_bang_expressions_with_nil() {
        let mut output = Vec::new();
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Bang, 0),
            expression: Box::new(Expression::Literal(Value::Nil)),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Bool(true))
        );
    }

    #[test]
    fn it_handles_unary_bang_expressions_with_false() {
        let mut output = Vec::new();
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Bang, 0),
            expression: Box::new(Expression::Literal(Value::Bool(false))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Bool(true))
        );
    }

    #[test]
    fn it_handles_unary_bang_expressions_with_true() {
        let mut output = Vec::new();
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Bang, 0),
            expression: Box::new(Expression::Literal(Value::Bool(true))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Bool(false))
        );
    }

    #[test]
    fn it_handles_unary_bang_expressions_with_numbers() {
        let mut output = Vec::new();
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Bang, 0),
            expression: Box::new(Expression::Literal(Value::Number(12.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Bool(false))
        );
    }

    #[test]
    fn it_handles_unary_bang_expressions_with_strings() {
        let mut output = Vec::new();
        let expression = Expression::Unary {
            operator: Token::new(Lexeme::Bang, 0),
            expression: Box::new(Expression::Literal(Value::String("abc".to_owned()))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Bool(false))
        );
    }

    #[test]
    fn it_handles_minus_binary_expressions() {
        let mut output = Vec::new();
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::Number(2.0))),
            operator: Token::new(Lexeme::Minus, 0),
            right: Box::new(Expression::Literal(Value::Number(12.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Number(-10.0))
        );
    }

    #[test]
    fn it_handles_plus_binary_expressions() {
        let mut output = Vec::new();
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::Number(2.0))),
            operator: Token::new(Lexeme::Plus, 0),
            right: Box::new(Expression::Literal(Value::Number(12.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Number(14.0))
        );
    }

    #[test]
    fn it_handles_plus_binary_expressions_with_strings() {
        let mut output = Vec::new();
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::String("ab".to_owned()))),
            operator: Token::new(Lexeme::Plus, 0),
            right: Box::new(Expression::Literal(Value::String("cd".to_owned()))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::String("abcd".to_owned()))
        );
    }

    #[test]
    fn it_handles_plus_binary_expressions_with_bad_operands() {
        let mut output = Vec::new();
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::Nil)),
            operator: Token::new(Lexeme::Plus, 0),
            right: Box::new(Expression::Literal(Value::String("cd".to_owned()))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Err(RuntimeError::new(
                0,
                "Operands must be two numbers or two strings.".to_owned()
            ))
        );
    }

    #[test]
    fn it_handles_star_binary_expressions() {
        let mut output = Vec::new();
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::Number(2.0))),
            operator: Token::new(Lexeme::Star, 0),
            right: Box::new(Expression::Literal(Value::Number(12.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Number(24.0))
        );
    }

    #[test]
    fn it_handles_slash_binary_expressions() {
        let mut output = Vec::new();
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::Number(12.0))),
            operator: Token::new(Lexeme::Slash, 0),
            right: Box::new(Expression::Literal(Value::Number(2.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Number(6.0))
        );
    }

    #[test]
    fn it_handles_arithmetic_binary_expressions_with_non_numeric_operands() {
        let mut output = Vec::new();
        let expression = Expression::Binary {
            left: Box::new(Expression::Literal(Value::Nil)),
            operator: Token::new(Lexeme::Slash, 0),
            right: Box::new(Expression::Literal(Value::Number(2.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Err(RuntimeError::new(0, "Operand must be a number.".to_owned()))
        );
    }

    #[test]
    fn it_handles_grouping_expressions() {
        let mut output = Vec::new();
        let expression = Expression::Grouping(Box::new(Expression::Literal(Value::Number(2.0))));

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Number(2.0))
        );
    }

    #[test]
    fn it_handles_variable_statements() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);
        let name = Token::new(Lexeme::Identifier("foo".to_owned()), 0);
        let statement = Statement::Var {
            name: name.clone(),
            initializer: None,
        };

        assert_eq!(statement.accept(&mut interpreter), Ok(Value::Nil));
        assert_eq!(env_get(&interpreter.environment, &name), Ok(Value::Nil));
    }

    #[test]
    fn it_handles_variable_statements_with_initializers() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);
        let name = Token::new(Lexeme::Identifier("foo".to_owned()), 0);
        let statement = Statement::Var {
            name: name.clone(),
            initializer: Some(Box::new(Expression::Literal(Value::Number(5.0)))),
        };

        assert_eq!(statement.accept(&mut interpreter), Ok(Value::Nil));
        assert_eq!(
            env_get(&interpreter.environment, &name),
            Ok(Value::Number(5.0))
        );
    }

    #[test]
    fn it_handles_assignment_expressions() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);
        let name = Token::new(Lexeme::Identifier("foo".to_owned()), 0);
        env_define(&interpreter.environment, &name, Value::Nil);

        let expression = Expression::Assign {
            name: name.clone(),
            value: Box::new(Expression::Literal(Value::Number(5.0))),
        };

        assert_eq!(expression.accept(&mut interpreter), Ok(Value::Number(5.0)));
        assert_eq!(
            env_get(&interpreter.environment, &name),
            Ok(Value::Number(5.0))
        );
    }

    #[test]
    fn it_handles_assign_expressions_with_undefined_variables() {
        let mut output = Vec::new();
        let expression = Expression::Assign {
            name: Token::new(Lexeme::Identifier("foo".to_owned()), 0),
            value: Box::new(Expression::Literal(Value::Number(5.0))),
        };

        assert_eq!(
            expression.accept(&mut Interpreter::new(&mut output)),
            Err(RuntimeError::new(0, "Undefined variable 'foo'.".to_owned()))
        );
    }

    #[test]
    fn it_handles_print_statements() {
        let mut output = Vec::new();
        let statement = Statement::Print(Box::new(Expression::Literal(Value::Number(5.0))));

        assert_eq!(
            statement.accept(&mut Interpreter::new(&mut output)),
            Ok(Value::Nil)
        );
        assert_eq!(output, b"5\n");
    }

    #[test]
    fn it_handles_blocks_that_references_the_outer_scope() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let var_statement = Statement::Var {
            name: Token::new(Lexeme::Identifier("foo".to_owned()), 0),
            initializer: Some(Box::new(Expression::Literal(Value::Number(5.0)))),
        };

        assert_eq!(var_statement.accept(&mut interpreter), Ok(Value::Nil));

        let block_statement = Statement::Block(vec![Statement::Print(Box::new(
            Expression::Variable(Token::new(Lexeme::Identifier("foo".to_owned()), 0)),
        ))]);

        assert_eq!(block_statement.accept(&mut interpreter), Ok(Value::Nil));

        assert_eq!(output, b"5\n");
    }

    #[test]
    fn it_handles_blocks_that_assign_to_vars_from_the_outer_scope() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let var_statement = Statement::Var {
            name: Token::new(Lexeme::Identifier("foo".to_owned()), 0),
            initializer: Some(Box::new(Expression::Literal(Value::Number(5.0)))),
        };

        assert_eq!(var_statement.accept(&mut interpreter), Ok(Value::Nil));

        let block_statement = Statement::Block(vec![
            Statement::Expression(Box::new(Expression::Assign {
                name: Token::new(Lexeme::Identifier("foo".to_owned()), 0),
                value: Box::new(Expression::Literal(Value::Number(10.0))),
            })),
            Statement::Print(Box::new(Expression::Variable(Token::new(
                Lexeme::Identifier("foo".to_owned()),
                0,
            )))),
        ]);

        assert_eq!(block_statement.accept(&mut interpreter), Ok(Value::Nil));

        let after_block_statement = Statement::Print(Box::new(Expression::Variable(Token::new(
            Lexeme::Identifier("foo".to_owned()),
            0,
        ))));

        assert_eq!(
            after_block_statement.accept(&mut interpreter),
            Ok(Value::Nil)
        );

        assert_eq!(output, b"10\n10\n");
    }

    #[test]
    fn it_handles_blocks_that_shadow_vars_from_the_outer_scope() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let var_statement = Statement::Var {
            name: Token::new(Lexeme::Identifier("foo".to_owned()), 0),
            initializer: Some(Box::new(Expression::Literal(Value::Number(5.0)))),
        };

        assert_eq!(var_statement.accept(&mut interpreter), Ok(Value::Nil));

        let block_statement = Statement::Block(vec![
            Statement::Var {
                name: Token::new(Lexeme::Identifier("foo".to_owned()), 0),
                initializer: Some(Box::new(Expression::Literal(Value::Number(10.0)))),
            },
            Statement::Print(Box::new(Expression::Variable(Token::new(
                Lexeme::Identifier("foo".to_owned()),
                0,
            )))),
        ]);

        assert_eq!(block_statement.accept(&mut interpreter), Ok(Value::Nil));

        let after_block_statement = Statement::Print(Box::new(Expression::Variable(Token::new(
            Lexeme::Identifier("foo".to_owned()),
            0,
        ))));

        assert_eq!(
            after_block_statement.accept(&mut interpreter),
            Ok(Value::Nil)
        );

        assert_eq!(output, b"10\n5\n");
    }

    #[test]
    fn it_handles_an_if_with_a_truthy_condition() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let if_statement = Statement::If {
            condition: Box::new(Expression::Literal(Value::Bool(true))),
            then_branch: Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("here".to_owned()),
            )))),
            else_branch: None,
        };

        assert_eq!(if_statement.accept(&mut interpreter), Ok(Value::Nil));
        assert_eq!(output, b"here\n");
    }

    #[test]
    fn it_handles_an_if_with_a_falsey_condition() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let if_statement = Statement::If {
            condition: Box::new(Expression::Literal(Value::Bool(false))),
            then_branch: Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("here".to_owned()),
            )))),
            else_branch: None,
        };

        assert_eq!(if_statement.accept(&mut interpreter), Ok(Value::Nil));
        assert_eq!(output, b"");
    }

    #[test]
    fn it_handles_an_if_plus_else_with_a_truthy_condition() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let if_statement = Statement::If {
            condition: Box::new(Expression::Literal(Value::Bool(true))),
            then_branch: Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("then".to_owned()),
            )))),
            else_branch: Some(Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("else".to_owned()),
            ))))),
        };

        assert_eq!(if_statement.accept(&mut interpreter), Ok(Value::Nil));
        assert_eq!(output, b"then\n");
    }

    #[test]
    fn it_handles_an_if_plus_else_with_a_falsey_condition() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let if_statement = Statement::If {
            condition: Box::new(Expression::Literal(Value::Bool(false))),
            then_branch: Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("then".to_owned()),
            )))),
            else_branch: Some(Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("else".to_owned()),
            ))))),
        };

        assert_eq!(if_statement.accept(&mut interpreter), Ok(Value::Nil));
        assert_eq!(output, b"else\n");
    }

    #[test]
    fn if_handles_or_with_truthy_left() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let if_statement = Statement::If {
            condition: Box::new(Expression::Logical {
                left: Box::new(Expression::Literal(Value::Bool(true))),
                operator: Token::new(Lexeme::Or, 1),
                right: Box::new(Expression::Literal(Value::Bool(false))),
            }),
            then_branch: Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("then".to_owned()),
            )))),
            else_branch: Some(Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("else".to_owned()),
            ))))),
        };

        assert_eq!(if_statement.accept(&mut interpreter), Ok(Value::Nil));
        assert_eq!(output, b"then\n");
    }

    #[test]
    fn if_handles_or_with_truthy_right() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let if_statement = Statement::If {
            condition: Box::new(Expression::Logical {
                left: Box::new(Expression::Literal(Value::Bool(false))),
                operator: Token::new(Lexeme::Or, 1),
                right: Box::new(Expression::Literal(Value::Bool(true))),
            }),
            then_branch: Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("then".to_owned()),
            )))),
            else_branch: Some(Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("else".to_owned()),
            ))))),
        };

        assert_eq!(if_statement.accept(&mut interpreter), Ok(Value::Nil));
        assert_eq!(output, b"then\n");
    }

    #[test]
    fn if_handles_or_with_everything_falsey() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let if_statement = Statement::If {
            condition: Box::new(Expression::Logical {
                left: Box::new(Expression::Literal(Value::Bool(false))),
                operator: Token::new(Lexeme::Or, 1),
                right: Box::new(Expression::Literal(Value::Bool(false))),
            }),
            then_branch: Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("then".to_owned()),
            )))),
            else_branch: Some(Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("else".to_owned()),
            ))))),
        };

        assert_eq!(if_statement.accept(&mut interpreter), Ok(Value::Nil));
        assert_eq!(output, b"else\n");
    }

    #[test]
    fn if_handles_and_with_truthy_left() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let if_statement = Statement::If {
            condition: Box::new(Expression::Logical {
                left: Box::new(Expression::Literal(Value::Bool(true))),
                operator: Token::new(Lexeme::And, 1),
                right: Box::new(Expression::Literal(Value::Bool(false))),
            }),
            then_branch: Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("then".to_owned()),
            )))),
            else_branch: Some(Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("else".to_owned()),
            ))))),
        };

        assert_eq!(if_statement.accept(&mut interpreter), Ok(Value::Nil));
        assert_eq!(output, b"else\n");
    }

    #[test]
    fn if_handles_and_with_truthy_right() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let if_statement = Statement::If {
            condition: Box::new(Expression::Logical {
                left: Box::new(Expression::Literal(Value::Bool(false))),
                operator: Token::new(Lexeme::And, 1),
                right: Box::new(Expression::Literal(Value::Bool(true))),
            }),
            then_branch: Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("then".to_owned()),
            )))),
            else_branch: Some(Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("else".to_owned()),
            ))))),
        };

        assert_eq!(if_statement.accept(&mut interpreter), Ok(Value::Nil));
        assert_eq!(output, b"else\n");
    }

    #[test]
    fn if_handles_and_with_everything_truthy() {
        let mut output = Vec::new();
        let mut interpreter = Interpreter::new(&mut output);

        let if_statement = Statement::If {
            condition: Box::new(Expression::Logical {
                left: Box::new(Expression::Literal(Value::Bool(true))),
                operator: Token::new(Lexeme::And, 1),
                right: Box::new(Expression::Literal(Value::Bool(true))),
            }),
            then_branch: Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("then".to_owned()),
            )))),
            else_branch: Some(Box::new(Statement::Print(Box::new(Expression::Literal(
                Value::String("else".to_owned()),
            ))))),
        };

        assert_eq!(if_statement.accept(&mut interpreter), Ok(Value::Nil));
        assert_eq!(output, b"then\n");
    }
}
