pub(crate) mod expression;
pub(crate) mod statement;

use crate::lexer::{LexemeKind, Token};
pub use expression::{Expr, Value};
pub use statement::Stmt;

#[derive(Debug)]
pub(crate) struct Parser {
    tokens: Vec<Token>,
    pub cursor: usize,
}

pub(crate) fn debug_tree(ast: &Stmt) -> String {
    let mut st = String::new();
    st.push_str("(");
    if let Stmt::Expr(Expr::Binary {
        left,
        operator,
        right,
    }) = ast
    {
        let op = operator.to_string();
        st.push_str(&op);
        st.push_str(" ");

        let l = &(*left).debug();
        st.push_str(l);
        st.push_str(" ");

        let r = &(*right).debug();
        st.push_str(r);
    } else {
        // println!("Not an expression");
    }

    st.push_str(")");
    st
}

impl Parser {
    pub(crate) fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, cursor: 0 }
    }

    // ultimately, we execute a list of statements
    pub(crate) fn parse(&mut self) -> Vec<Stmt> {
        let mut stmts = Vec::new();
        while !self.at_end() {
            let res = statement::parse(self);

            self.eat_whitespace();

            stmts.push(res.unwrap());
        }

        stmts
    }

    pub fn at_end(&self) -> bool {
        self.peek_kind() == Some(LexemeKind::EOF) || self.peek_kind() == None
    }

    fn last_token(&self) -> Option<&Token> {
        self.tokens.get(self.cursor - 1)
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.cursor)
    }

    fn peek_kind(&self) -> Option<LexemeKind> {
        self.peek()
            .and_then(|Token { lexeme, .. }| Some(lexeme.clone()))
    }

    fn expect(&mut self, kind: LexemeKind) -> Result<(), Option<Expr>> {
        if self.at(kind) {
            self.cursor += 1;
            return Ok(());
        } else if !self.at_end() {
            let token = self.peek().unwrap();
            return Err(self.error(token.line, &format!("Unexpected token: {}", token.lexeme)));
        }

        // no token
        Err(self.error(0, &format!("Unexpected token")))
    }

    fn at(&self, kind: LexemeKind) -> bool {
        if self.at_end() {
            return false;
        };
        self.peek_kind() == Some(kind)
    }

    fn eat_whitespace(&mut self) {
        while let Some(LexemeKind::Whitespace) = self.peek_kind() {
            self.cursor += 1;
        }
    }

    fn error(&self, line: usize, msg: &str) -> Option<Expr> {
        Some(Expr::Error { line, message: msg.to_string() })
    }

    fn is_equal(&self, kinds: Vec<LexemeKind>) -> bool {
        let res = kinds.iter().find(|&k| self.at(k.clone()));
        res.is_some()
    }

    fn expression(&mut self) -> Option<Expr> {
        // here we parse left to right. As we "eat" tokens, we traverse forward,
        self.assignment()
    }

    fn assignment(&mut self) -> Option<Expr> {
        let mut expr = self.or();

        self.eat_whitespace();

        while self.is_equal(vec![LexemeKind::Equal]) {
            self.cursor += 1; // EQUAL

            self.eat_whitespace();

            if let Some(Expr::Variable(st)) = expr {
                // this came from fn primary()
                // recursive call in case a = b = 1;
                let right = self.assignment();
                match right {
                    Some(r) => {
                        expr = Some(Expr::Assign {
                            name: st,
                            expr: Box::new(r),
                        });

                        let _ = self.expect(LexemeKind::Semicolon);
                    }
                    None => {
                        let last_token = self.last_token().unwrap();
                        expr = self.error(last_token.line, "Unfinished right hand assignment expression");
                    }
                }
            } else {
                let last_token = self.last_token().unwrap();
                expr = self.error(last_token.line, "Invalid left hand assignment expression");
            }
        }

        expr
    }

    fn or(&mut self) -> Option<Expr> {
        let mut expr = self.and();

        self.eat_whitespace();

        while self.is_equal(vec![LexemeKind::OR]) {
            let operator = self.peek_kind().unwrap();
            self.cursor += 1;
            let right = self.and();
            expr = Some(Expr::Logical {
                left: Box::new(expr.unwrap()),
                operator,
                right: Box::new(right.unwrap()),
            });
        }

        expr
    }

    fn and(&mut self) -> Option<Expr> {
        let mut expr = self.equality();

        self.eat_whitespace();

        while self.is_equal(vec![LexemeKind::AND]) {
            let operator = self.peek_kind().unwrap();
            self.cursor += 1;
            let right = self.equality();
            expr = Some(Expr::Logical {
                left: Box::new(expr.unwrap()),
                operator,
                right: Box::new(right.unwrap()),
            });
        }

        expr
    }

    fn equality(&mut self) -> Option<Expr> {
        let mut expr = self.comparison();

        self.eat_whitespace();

        while self.is_equal(vec![LexemeKind::BangEqual, LexemeKind::EqualEqual]) {
            let operator = self.peek_kind().unwrap();
            self.cursor += 1;
            let right = self.comparison();
            expr = Some(Expr::Binary {
                left: Box::new(expr.unwrap()),
                operator,
                right: Box::new(right.unwrap()),
            })
        }

        expr
    }

    fn comparison(&mut self) -> Option<Expr> {
        let mut expr = self.term();

        self.eat_whitespace();

        while self.is_equal(vec![
            LexemeKind::Greater,
            LexemeKind::GreaterEqual,
            LexemeKind::Less,
            LexemeKind::LessEqual,
        ]) {
            let operator = self.peek_kind().unwrap();

            self.cursor += 1;

            let right = self.term();
            expr = Some(Expr::Binary {
                left: Box::new(expr.unwrap()),
                operator,
                right: Box::new(right.unwrap()),
            })
        }

        expr
    }

    fn term(&mut self) -> Option<Expr> {
        let mut expr = self.factor();

        self.eat_whitespace();

        while self.is_equal(vec![LexemeKind::Minus, LexemeKind::Plus]) {
            let operator = self.peek_kind().unwrap();

            self.cursor += 1;

            let right = self.factor();
            expr = Some(Expr::Binary {
                left: Box::new(expr.unwrap()), // 1
                operator, // +
                right: Box::new(right.unwrap()), // 1
            })
        }

        expr
    }

    fn factor(&mut self) -> Option<Expr> {
        let mut expr = self.unary();

        self.eat_whitespace();

        while self.is_equal(vec![LexemeKind::Slash, LexemeKind::Star]) {
            let operator = self.peek_kind().unwrap();
            self.cursor += 1;
            let right = self.unary();
            expr = Some(Expr::Binary {
                left: Box::new(expr.unwrap()),
                operator,
                right: Box::new(right.unwrap()),
            })
        }

        expr
    }

    fn unary(&mut self) -> Option<Expr> {
        let mut res = None;

        self.eat_whitespace();

        while self.is_equal(vec![LexemeKind::Bang, LexemeKind::Minus, LexemeKind::Plus]) {
            let operator = self.peek_kind().unwrap();

            self.cursor += 1;

            let new = self.unary();
            match res {
                Some(Expr::Unary { operator, right }) => {
                    res = Some(Expr::Binary {
                        left: right,
                        operator: operator.clone(),
                        right: Box::new(new.unwrap()),
                    });
                },
                _ => {
                    res = Some(Expr::Unary {
                        operator,
                        right: Box::new(new.unwrap()),
                    });
                }
            }
        }

        if res.is_some() {
            res
        } else {
            let res = self.primary();
            let token = self.tokens.get(self.cursor);
            if let Some(Token { lexeme: LexemeKind::UNEXPECTED(l), line }) = token {
                self.cursor += 1;
                self.error(*line, &format!("Parsing error at {}", l))
            } else {
                res
            }
        }
    }

    fn primary(&mut self) -> Option<Expr> {
        // first check if we have something to look at
        if self.peek_kind() == None {
            return None;
        }

        let token = self.tokens.get(self.cursor).unwrap();
        match &token.lexeme {
            LexemeKind::FALSE => {
                self.cursor += 1;
                Some(Expr::Literal(Value::BOOLEAN(false)))
            }
            LexemeKind::TRUE => {
                self.cursor += 1;
                Some(Expr::Literal(Value::BOOLEAN(true)))
            }
            LexemeKind::STRING(st) => {
                self.cursor += 1;
                Some(Expr::Literal(Value::STRING(st.to_string())))
            }
            LexemeKind::NUMBER(num) => {
                self.cursor += 1;
                Some(Expr::Literal(Value::NUMBER(*num)))
            }
            LexemeKind::IDENTIFIER(st) => {
                self.cursor += 1;
                // this will be used by the fn assignment
                Some(Expr::Variable(st.to_string()))
            }
            LexemeKind::LeftParen => {
                self.cursor += 1;

                // empty print stmt - print()
                if self.peek_kind() == Some(LexemeKind::RightParen) {
                    return Some(Expr::Grouping(
                        Box::new(Expr::Literal(Value::STRING("".to_string()))),
                    ));
                }

                let expr = self.expression();

                match expr {
                    None => {
                        // fail gracefully if we haven't closed out the RightParen
                        let last_token = self.last_token().unwrap();
                        self.error(last_token.line, &format!("~~Parsing error at {}", last_token.lexeme))
                    }
                    ex => Some(Expr::Grouping(
                        Box::new(ex.unwrap())
                    )),
                }
            }
            m => {
                self.cursor += 1;
                self.error(token.line, &format!("Parsing error at {}", m))
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::lexer::Scanner;

    #[test]
    fn it_handles_binary() {
        let tokens = Scanner::new("1+1".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(Expr::Binary {
                left: Box::new(Expr::Literal(Value::NUMBER(1.0))),
                operator: LexemeKind::Plus,
                right: Box::new(Expr::Literal(Value::NUMBER(1.0))),
            })
        );

        let tokens = Scanner::new("1 == 1".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(Expr::Binary {
                left: Box::new(Expr::Literal(Value::NUMBER(1.0))),
                operator: LexemeKind::EqualEqual,
                right: Box::new(Expr::Literal(Value::NUMBER(1.0))),
            })
        );
    }

    #[test]
    fn it_handles_co() {
        let tokens = Scanner::new("1 >= 2".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(Expr::Binary {
                left: Box::new(Expr::Literal(Value::NUMBER(1.0))),
                operator: LexemeKind::GreaterEqual,
                right: Box::new(Expr::Literal(Value::NUMBER(2.0))),
            })
        );

        let tokens = Scanner::new("1 <= 2".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(Expr::Binary {
                left: Box::new(Expr::Literal(Value::NUMBER(1.0))),
                operator: LexemeKind::LessEqual,
                right: Box::new(Expr::Literal(Value::NUMBER(2.0))),
            })
        );
    }

    #[test]
    fn it_handles_unary() {
        let tokens = Scanner::new("-1".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(Expr::Unary {
                operator: LexemeKind::Minus,
                right: Box::new(Expr::Literal(Value::NUMBER(1.0))),
            })
        );

        let tokens = Scanner::new("+1".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(Expr::Unary {
                operator: LexemeKind::Plus,
                right: Box::new(Expr::Literal(Value::NUMBER(1.0))),
            })
        );
    }

    #[test]
    fn it_errors_keyword() {
        let tokens = Scanner::new("and".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(Expr::Error { line: 0, message: "Parsing error at AND".to_string() })
        );
    }

    #[test]
    fn not_expression() {
        let tokens = Scanner::new("a".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(Expr::Variable("a".to_string()))
        );
    }

    #[test]
    fn it_works_parenthesized_expression() {
        let tokens = Scanner::new("(1+1)".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(Expr::Grouping(
                Box::new(Expr::Binary {
                    left: Box::new(Expr::Literal(Value::NUMBER(1.0))),
                    operator: LexemeKind::Plus,
                    right: Box::new(Expr::Literal(Value::NUMBER(1.0))),
                }),
            ))
        );
    }

    #[test]
    fn it_works_plus_plus() {
        let tokens = Scanner::new("+1+1".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(Expr::Binary {
                left: Box::new(Expr::Literal(Value::NUMBER(1.0))),
                operator: LexemeKind::Plus,
                right: Box::new(Expr::Literal(Value::NUMBER(1.0))),
            })
        );
    }

    #[test]
    fn variables_semicolon() {
        let tokens = Scanner::new("var a;".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::VariableDef { ident: "a".to_string(), expr: None}
        );
    }

    #[test]
    fn variables_no_semicolon() {
        let tokens = Scanner::new("var a".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::VariableDef { ident: "a".to_string(), expr: None}
        );
    }

    #[test]
    fn assignment() {
        let tokens = Scanner::new("a = 2;".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(Expr::Assign { name: "a".to_string(), expr: Box::new(Expr::Literal(Value::NUMBER(2.0))) })
        );
    }

    #[test]
    fn multiple_assignment() {
        let tokens = Scanner::new("a = b = 2;".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(
                Expr::Assign {
                    name: "a".to_string(),
                    expr: Box::new(
                        Expr::Assign {
                            name: "b".to_string(),
                            expr: Box::new(Expr::Literal(Value::NUMBER(2.0)))
                        }
                    )
                }
            )
        );
    }

    #[test]
    fn logical_and() {
        let tokens = Scanner::new("a = 2 and 5;".to_owned()).collect();
        let ast = Parser::new(tokens).parse().into_iter().nth(0).unwrap();
        assert_eq!(
            ast,
            Stmt::Expr(Expr::Assign {
                name: "a".to_string(),
                expr: Box::new(Expr::Logical {
                    left: Box::new(Expr::Literal(Value::NUMBER(2.0))),
                    operator: LexemeKind::AND,
                    right: Box::new(Expr::Literal(Value::NUMBER(5.0))),
                })
            })
        );
    }
}
