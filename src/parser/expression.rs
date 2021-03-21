use std::fmt;
use crate::lexer::{LexemeKind, Token};
use crate::visitor::ExpressionVisitor;

#[derive(Debug, PartialEq)]
pub enum Expr {
    Assign {
        name: String,
        expr: Box<Expr>,
    },
    Binary {
        left: Box<Expr>,
        operator: LexemeKind,
        right: Box<Expr>,
    },
    Literal(Value),
    Logical {
        left: Box<Expr>,
        operator: LexemeKind,
        right: Box<Expr>,
    },
    Variable(String),
    Unary {
        operator: LexemeKind,
        right: Box<Expr>,
    },
    Grouping(Box<Expr>),
    Error {
        line: usize,
        message: String,
    }
}

// a single element tuple struct over a generic type will not work.
// arms in parser will return different types for T
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    BOOLEAN(bool),
    STRING(String),
    NUMBER(f64),
    Null,
}

impl Value {
    pub fn to_string(&self) -> String {
        match self {
            Self::BOOLEAN(b) => b.to_string(),
            Self::NUMBER(n) => n.to_string(),
            Self::STRING(ref s) => format!("\"{}\"", s),
            Self::Null => "nil".to_owned(),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl Expr {
    pub(crate) fn accept<T>(&self, visitor: &mut dyn ExpressionVisitor<T>) -> T {
        match self {
            Expr::Assign { name, expr } => {
                visitor.visit_assign(name, expr)
            }
            Expr::Binary { operator, left, right } => {
                visitor.visit_binary(left, operator, right)
            }
            Expr::Logical { operator, left, right } => {
                visitor.visit_logical(left, operator, right)
            }
            Expr::Unary { operator, right } => {
                visitor.visit_unary(operator, right)
            }
            Expr::Grouping(val) => {
                visitor.visit_grouping(val)
            }
            Expr::Literal(v) => {
                visitor.visit_literal(v)
            }
            Expr::Variable(v) => {
                visitor.visit_variable(v)
            }
            Expr::Error { line, message } => {
                visitor.visit_error(line, message)
            }
        }
    }

    pub(crate) fn debug(&self) -> String {
        match self {
            Expr::Assign { name, expr} => {
                let mut st = String::new();
                st.push_str("(");

                let op = name.to_string();
                st.push_str(&op);
                st.push_str(" ");

                let l = &expr.debug();
                st.push_str(l);
                st.push_str(" ");

                st
            },
            Expr::Binary { operator, left, right } => {
                let mut st = String::new();
                st.push_str("(");

                let op = operator.to_string();
                st.push_str(&op);
                st.push_str(" ");

                let l = &left.debug();
                st.push_str(l);
                st.push_str(" ");

                let r = &right.debug();
                st.push_str(r);

                st
            },
            Expr::Logical { operator, left, right } => {
                let mut st = String::new();
                st.push_str("(");

                let op = operator.to_string();
                st.push_str(&op);
                st.push_str(" ");

                let l = &left.debug();
                st.push_str(l);
                st.push_str(" ");

                let r = &right.debug();
                st.push_str(r);

                st
            },
            Expr::Literal(v) => {
                match v {
                    Value::BOOLEAN(true) => "true".to_string(),
                    Value::BOOLEAN(false) => "true".to_string(),
                    Value::STRING(st) => st.to_string(),
                    Value::NUMBER(n) => n.to_string(),
                    Value::Null => "".to_string(),
                }
            }
            Expr::Unary { operator, right } => {
                let mut st = String::new();
                st.push_str("( ");

                let op = operator.to_string();
                st.push_str(&op);
                st.push_str(" ");

                let r = &right.debug();
                st.push_str(r);
                st.push_str(" ");

                st
            },
            Expr::Grouping(value) => {
                value.debug()
            },
            Expr::Variable(st) => {
                st.to_string()
            },
            Expr::Error { message, .. } => message.to_string()
        }
    }
}

