use crate::lexer::{LexemeKind, Scanner, Token};

#[derive(Debug, PartialEq)]
pub enum Expr {
    Binary(ExprBinary),
    Literal(ExprLiteral),
    Unary(ExprUnary),
    Grouping(ExprGrouping),
    Error,
}

#[derive(Debug, PartialEq)]
pub struct ExprBinary {
    left: Box<Expr>,
    operator: LexemeKind,
    right: Box<Expr>,
}

#[derive(Debug, PartialEq)]
pub struct ExprUnary {
    operator: LexemeKind,
    right: Box<Expr>,
}

#[derive(Debug, PartialEq)]
pub enum ExprLiteral {
    BOOLEAN(bool),
    STRING(String),
    NUMBER(f64),
}

#[derive(Debug, PartialEq)]
pub struct ExprGrouping {
    value: Box<Expr>,
}

pub struct Parser {
    tokens: Vec<Token>,
    cursor: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, cursor: 0 }
    }

    pub fn parse(&mut self) -> Option<Expr> {
        self.expression()
    }

    fn at_end(&self) -> bool {
        self.peek_kind() == Some(LexemeKind::EOF)
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.cursor)
    }

    fn peek_kind(&self) -> Option<LexemeKind> {
        self.peek()
            .and_then(|Token { lexeme, .. }| Some(lexeme.clone()))
    }

    fn expect(&mut self, kind: LexemeKind) {
        if self.at(kind) {
            self.cursor += 1;
        } else {
            todo!();
        }
    }

    fn at(&self, kind: LexemeKind) -> bool {
        if self.at_end() {
            return false;
        };
        self.peek_kind() == Some(kind)
    }

    fn error(&self) -> Option<Expr> {
        Some(Expr::Error)
    }

    fn is_equal(&self, kinds: Vec<LexemeKind>) -> bool {
        let res = kinds.iter().find(|&k| self.at(k.clone()));
        res.is_some()
    }

    fn expression(&mut self) -> Option<Expr> {
        self.equality()
    }

    fn equality(&mut self) -> Option<Expr> {
        let mut expr = self.comparison();

        while self.is_equal(vec![LexemeKind::BANG_EQUAL, LexemeKind::EQUAL_EQUAL]) {
            let operator = self.peek_kind().unwrap();
            self.cursor += 1;
            let right = self.comparison();
            expr = Some(Expr::Binary(ExprBinary {
                left: Box::new(expr.unwrap()),
                operator,
                right: Box::new(right.unwrap()),
            }))
        }

        expr
    }

    fn comparison(&mut self) -> Option<Expr> {
        let mut expr = self.term();

        while self.is_equal(vec![
            LexemeKind::GREATER,
            LexemeKind::GREATER_EQUAL,
            LexemeKind::LESS,
            LexemeKind::LESS_EQUAL,
        ]) {
            let operator = self.peek_kind().unwrap();
            self.cursor += 1;
            let right = self.term();
            expr = Some(Expr::Binary(ExprBinary {
                left: Box::new(expr.unwrap()),
                operator,
                right: Box::new(right.unwrap()),
            }))
        }

        expr
    }

    fn term(&mut self) -> Option<Expr> {
        let mut expr = self.factor();

        while self.is_equal(vec![LexemeKind::MINUS, LexemeKind::PLUS]) {
            let operator = self.peek_kind().unwrap();
            self.cursor += 1;
            let right = self.factor();
            expr = Some(Expr::Binary(ExprBinary {
                left: Box::new(expr.unwrap()),
                operator,
                right: Box::new(right.unwrap()),
            }))
        }

        expr
    }

    fn factor(&mut self) -> Option<Expr> {
        let mut expr = self.unary();

        while self.is_equal(vec![LexemeKind::SLASH, LexemeKind::STAR]) {
            let operator = self.peek_kind().unwrap();
            self.cursor += 1;
            let right = self.unary();
            expr = Some(Expr::Binary(ExprBinary {
                left: Box::new(expr.unwrap()),
                operator,
                right: Box::new(right.unwrap()),
            }))
        }

        expr
    }

    fn unary(&mut self) -> Option<Expr> {
        let mut res = None;
        while self.is_equal(vec![LexemeKind::BANG, LexemeKind::MINUS]) {
            let operator = self.peek_kind().unwrap();
            self.cursor += 1;
            let right = self.unary();
            res = Some(Expr::Unary(ExprUnary {
                operator,
                right: Box::new(right.unwrap()),
            }))
        }

        if res.is_some() {
            res
        } else {
            self.primary()
        }
    }

    fn primary(&mut self) -> Option<Expr> {
        let token = self.tokens.get(self.cursor).unwrap();
        match &token.lexeme {
            LexemeKind::FALSE => {
                self.cursor += 1;
                Some(Expr::Literal(ExprLiteral::BOOLEAN(false)))
            }
            LexemeKind::TRUE => {
                self.cursor += 1;
                Some(Expr::Literal(ExprLiteral::BOOLEAN(true)))
            }
            LexemeKind::STRING(st) => {
                self.cursor += 1;
                Some(Expr::Literal(ExprLiteral::STRING(st.to_string())))
            }
            LexemeKind::NUMBER(num) => {
                self.cursor += 1;
                Some(Expr::Literal(ExprLiteral::NUMBER(*num)))
            }
            LexemeKind::LEFT_PAREN => {
                self.cursor += 1;
                let expr = self.expression();

                self.expect(LexemeKind::RIGHT_PAREN);

                Some(Expr::Grouping(ExprGrouping {
                    value: Box::new(expr.unwrap()),
                }))
            }
            _ => self.error(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn it_works() {
        let tokens = Scanner::new("1+1".to_owned()).collect();
        let ast = Parser::new(tokens).parse().unwrap();
        assert_eq!(
            ast,
            Expr::Binary(ExprBinary {
                left: Box::new(Expr::Literal(ExprLiteral::NUMBER(1.0))),
                operator: LexemeKind::PLUS,
                right: Box::new(Expr::Literal(ExprLiteral::NUMBER(1.0))),
            })
        );
    }

    #[test]
    fn it_works_parenthesized_expression() {
        let tokens = Scanner::new("(1+1)".to_owned()).collect();
        let ast = Parser::new(tokens).parse().unwrap();
        assert_eq!(
            ast,
            Expr::Grouping(ExprGrouping {
                value: Box::new(Expr::Binary(ExprBinary {
                    left: Box::new(Expr::Literal(ExprLiteral::NUMBER(1.0))),
                    operator: LexemeKind::PLUS,
                    right: Box::new(Expr::Literal(ExprLiteral::NUMBER(1.0))),
                })),
            })
        );
    }

    #[test]
    fn it_errors() {
        let tokens = Scanner::new("+1+1".to_owned()).collect();
        let ast = Parser::new(tokens).parse().unwrap();
        assert_eq!(
            ast,
            Expr::Binary(ExprBinary {
                left: Box::new(Expr::Binary(ExprBinary {
                    left: Box::new(Expr::Error),
                    operator: LexemeKind::PLUS,
                    right: Box::new(Expr::Literal(ExprLiteral::NUMBER(1.0)))
                })),
                operator: LexemeKind::PLUS,
                right: Box::new(Expr::Literal(ExprLiteral::NUMBER(1.0))),
            })
        );
    }
}
