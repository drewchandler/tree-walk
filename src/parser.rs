use core::slice;
use std::error;
use std::fmt;
use std::iter;

use crate::expression::{Expression, Value};
use crate::token::{Lexeme, Token};

#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    UnexpectedToken { token: Token, message: String },
    UnexpectedEnd,
}

impl ParseError {
    fn unexpected_token(token: Token, message: String) -> Self {
        Self::UnexpectedToken { token, message }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnexpectedToken { token, message } => write!(
                f,
                "[line {}] at '{}' {}",
                token.line,
                token.to_string(),
                message
            ),
            Self::UnexpectedEnd => {
                write!(f, "Unexpected end of tokens")
            }
        }
    }
}

impl error::Error for ParseError {}

type ParseResult = Result<Expression, ParseError>;

pub struct Parser<'a> {
    tokens: iter::Peekable<slice::Iter<'a, Token>>,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a Vec<Token>) -> Self {
        Parser {
            tokens: tokens.iter().peekable(),
        }
    }

    fn expression(&mut self) -> ParseResult {
        self.equality()
    }

    fn equality(&mut self) -> ParseResult {
        let mut expr = self.comparision()?;

        while matches!(
            self.peek_lexeme(),
            Some(&Lexeme::BangEqual) | Some(&Lexeme::EqualEqual)
        ) {
            let operator = self.advance().unwrap();
            let right = self.comparision()?;

            expr = Expression::Binary {
                left: Box::new(expr),
                operator: operator,
                right: Box::new(right),
            };
        }

        Ok(expr)
    }

    fn comparision(&mut self) -> ParseResult {
        let mut expr = self.term()?;

        while matches!(
            self.peek_lexeme(),
            Some(&Lexeme::Greater)
                | Some(&Lexeme::GreaterEqual)
                | Some(&Lexeme::Less)
                | Some(&Lexeme::LessEqual)
        ) {
            let operator = self.advance().unwrap();
            let right = self.term()?;

            expr = Expression::Binary {
                left: Box::new(expr),
                operator: operator,
                right: Box::new(right),
            };
        }

        Ok(expr)
    }

    fn term(&mut self) -> ParseResult {
        let mut expr = self.factor()?;

        while matches!(
            self.peek_lexeme(),
            Some(&Lexeme::Minus) | Some(&Lexeme::Plus)
        ) {
            let operator = self.advance().unwrap();
            let right = self.factor()?;

            expr = Expression::Binary {
                left: Box::new(expr),
                operator: operator,
                right: Box::new(right),
            };
        }

        Ok(expr)
    }

    fn factor(&mut self) -> ParseResult {
        let mut expr = self.unary()?;

        while matches!(
            self.peek_lexeme(),
            Some(&Lexeme::Slash) | Some(&Lexeme::Star)
        ) {
            let operator = self.advance().unwrap();
            let right = self.unary()?;

            expr = Expression::Binary {
                left: Box::new(expr),
                operator: operator,
                right: Box::new(right),
            };
        }

        Ok(expr)
    }

    fn unary(&mut self) -> ParseResult {
        if matches!(
            self.peek_lexeme(),
            Some(&Lexeme::Bang) | Some(&Lexeme::Minus)
        ) {
            let operator = self.advance().unwrap();
            let right = self.unary()?;

            return Ok(Expression::Unary {
                operator: operator,
                expression: Box::new(right),
            });
        }

        self.primary()
    }

    fn primary(&mut self) -> ParseResult {
        match self.advance() {
            Some(Token {
                lexeme: Lexeme::False,
                ..
            }) => Ok(Expression::Literal(Value::Bool(false))),
            Some(Token {
                lexeme: Lexeme::True,
                ..
            }) => Ok(Expression::Literal(Value::Bool(true))),
            Some(Token {
                lexeme: Lexeme::Nil,
                ..
            }) => Ok(Expression::Literal(Value::Nil)),
            Some(Token {
                lexeme: Lexeme::Number(number),
                ..
            }) => Ok(Expression::Literal(Value::Number(number))),
            Some(Token {
                lexeme: Lexeme::String(string),
                ..
            }) => Ok(Expression::Literal(Value::String(string))),
            Some(Token {
                lexeme: Lexeme::LeftParen,
                ..
            }) => {
                let expr = self.expression()?;
                self.consume(
                    |l| l == &Lexeme::RightParen,
                    "Expected ')' after expression.".to_owned(),
                )?;
                Ok(Expression::Grouping(Box::new(expr)))
            }
            Some(token @ Token { .. }) => Err(ParseError::unexpected_token(
                token,
                "Expected expression.".to_owned(),
            )),
            _ => Err(ParseError::UnexpectedEnd),
        }
    }

    fn advance(&mut self) -> Option<Token> {
        self.tokens.next().map(|t| t.clone())
    }

    fn peek_lexeme(&mut self) -> Option<&Lexeme> {
        self.tokens.peek().map(|t| &t.lexeme)
    }

    fn consume<P>(&mut self, predicate: P, error_message: String) -> Result<(), ParseError>
    where
        P: Fn(&Lexeme) -> bool,
    {
        match self.tokens.peek() {
            Some(token) => {
                if predicate(&token.lexeme) {
                    self.advance();
                    Ok(())
                } else {
                    Err(ParseError::unexpected_token(
                        (*token).clone(),
                        error_message,
                    ))
                }
            }
            None => Err(ParseError::UnexpectedEnd),
        }
    }
}

impl<'a> Iterator for Parser<'a> {
    type Item = ParseResult;

    fn next(&mut self) -> Option<Self::Item> {
        match self.peek_lexeme() {
            Some(&Lexeme::Eof) => None,
            _ => Some(self.expression()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::{Expression, Value};
    use crate::token::{Lexeme, Token};

    #[test]
    fn it_handles_string_literal_expressions() {
        let tokens = vec![
            Token::new(Lexeme::String("string literal".to_owned()), 0),
            Token::new(Lexeme::Eof, 0),
        ];
        let mut parser = Parser::new(&tokens);

        assert_eq!(
            parser.next(),
            Some(Ok(Expression::Literal(Value::String(
                "string literal".to_owned()
            ))))
        );
        assert_eq!(parser.next(), None);
    }

    #[test]
    fn it_handles_number_literal_expressions() {
        let tokens = vec![
            Token::new(Lexeme::Number(12.0), 0),
            Token::new(Lexeme::Eof, 0),
        ];
        let mut parser = Parser::new(&tokens);

        assert_eq!(
            parser.next(),
            Some(Ok(Expression::Literal(Value::Number(12.0))))
        );
        assert_eq!(parser.next(), None);
    }

    #[test]
    fn it_handles_true_boolean_literal_expressions() {
        let tokens = vec![Token::new(Lexeme::True, 0), Token::new(Lexeme::Eof, 0)];
        let mut parser = Parser::new(&tokens);

        assert_eq!(
            parser.next(),
            Some(Ok(Expression::Literal(Value::Bool(true))))
        );
        assert_eq!(parser.next(), None);
    }

    #[test]
    fn it_handles_false_boolean_literal_expressions() {
        let tokens = vec![Token::new(Lexeme::False, 0), Token::new(Lexeme::Eof, 0)];
        let mut parser = Parser::new(&tokens);

        assert_eq!(
            parser.next(),
            Some(Ok(Expression::Literal(Value::Bool(false))))
        );
        assert_eq!(parser.next(), None);
    }

    #[test]
    fn it_handles_nil_literal_expressions() {
        let tokens = vec![Token::new(Lexeme::Nil, 0), Token::new(Lexeme::Eof, 0)];
        let mut parser = Parser::new(&tokens);

        assert_eq!(parser.next(), Some(Ok(Expression::Literal(Value::Nil))));
        assert_eq!(parser.next(), None);
    }

    #[test]
    fn it_handles_unary_expressions() {
        let tokens = vec![
            Token::new(Lexeme::Minus, 0),
            Token::new(Lexeme::Number(12.0), 0),
            Token::new(Lexeme::Eof, 0),
        ];
        let mut parser = Parser::new(&tokens);

        assert_eq!(
            parser.next(),
            Some(Ok(Expression::Unary {
                operator: Token::new(Lexeme::Minus, 0),
                expression: Box::new(Expression::Literal(Value::Number(12.0)))
            }))
        );
        assert_eq!(parser.next(), None);
    }

    #[test]
    fn it_handles_binary_expressions() {
        let tokens = vec![
            Token::new(Lexeme::Number(2.0), 0),
            Token::new(Lexeme::Minus, 0),
            Token::new(Lexeme::Number(12.0), 0),
            Token::new(Lexeme::Eof, 0),
        ];
        let mut parser = Parser::new(&tokens);

        assert_eq!(
            parser.next(),
            Some(Ok(Expression::Binary {
                left: Box::new(Expression::Literal(Value::Number(2.0))),
                operator: Token::new(Lexeme::Minus, 0),
                right: Box::new(Expression::Literal(Value::Number(12.0)))
            }))
        );
        assert_eq!(parser.next(), None);
    }

    #[test]
    fn it_handles_grouping_expressions() {
        let tokens = vec![
            Token::new(Lexeme::LeftParen, 0),
            Token::new(Lexeme::Number(2.0), 0),
            Token::new(Lexeme::RightParen, 0),
            Token::new(Lexeme::Eof, 0),
        ];
        let mut parser = Parser::new(&tokens);

        assert_eq!(
            parser.next(),
            Some(Ok(Expression::Grouping(Box::new(Expression::Literal(
                Value::Number(2.0)
            )))))
        );
        assert_eq!(parser.next(), None);
    }

    #[test]
    fn it_handles_unclosed_grouping_expressions() {
        let tokens = vec![
            Token::new(Lexeme::LeftParen, 0),
            Token::new(Lexeme::Number(2.0), 0),
            Token::new(Lexeme::Eof, 0),
        ];
        let mut parser = Parser::new(&tokens);

        assert_eq!(
            parser.next(),
            Some(Err(ParseError::UnexpectedToken {
                token: Token::new(Lexeme::Eof, 0),
                message: "Expected ')' after expression.".to_owned()
            }))
        );
        assert_eq!(parser.next(), None);
    }

    #[test]
    fn it_handles_incomplete_expressions() {
        let tokens = vec![Token::new(Lexeme::Minus, 0), Token::new(Lexeme::Eof, 0)];
        let mut parser = Parser::new(&tokens);

        assert_eq!(
            parser.next(),
            Some(Err(ParseError::UnexpectedToken {
                token: Token::new(Lexeme::Eof, 0),
                message: "Expected expression.".to_owned()
            }))
        );
    }

    #[test]
    fn it_handles_a_premature_end_of_tokens() {
        let tokens = vec![Token::new(Lexeme::Minus, 0)];
        let mut parser = Parser::new(&tokens);

        assert_eq!(parser.next(), Some(Err(ParseError::UnexpectedEnd)));
    }
}
