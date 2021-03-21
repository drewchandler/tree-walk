mod environment;

use std::fmt;
use std::cell::RefCell;
use std::rc::Rc;
use crate::parser::{Expr, Stmt, Value};
use crate::lexer::LexemeKind;
use crate::parser;
use crate::visitor::{ExpressionVisitor, StatementVisitor};
pub use environment::Environment;

// Error strategy
// Lexer - captures all tokens. UNEXPECTED(String) enum variant for unknown
// Parser - add Expr::Error { line, message } if come across something that is unexpected. No build
// compile time error thrown.  Baked into return type
// Interpreter - RuntimeError when iterating over ast provided by Parser
#[derive(Debug, PartialEq)]
pub struct RuntimeError {
    line: usize,
    message: String,
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} [line: {}]", self.message, self.line)
    }
}

type InterpreterResult = Result<Value, RuntimeError>;

pub struct Interpreter {
    environment: Rc<RefCell<Environment>>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            environment: Rc::new(RefCell::new(Environment::new()))
        }
    }

    pub fn start(&mut self, stmts: Vec<Stmt>) -> InterpreterResult {
        let mut result = Ok(Value::Null);
        let mut iter_stmts = stmts.into_iter();

        while let Some(stmt) = iter_stmts.next() {
            println!("{:?}", parser::debug_tree(&stmt));

            // keep reassigning assuming the last one is an expression
            result = self.execute(&stmt);
        }

        result
    }

    pub fn execute(&mut self, stmt: &Stmt) -> InterpreterResult {
        stmt.accept(self)
    }

    pub fn evaluate(&mut self, expr: &Expr) -> InterpreterResult {
        expr.accept(self)
    }
}

impl ExpressionVisitor<InterpreterResult> for Interpreter {
    fn visit_assign(&mut self, name: &str, expr: &Expr) -> InterpreterResult {
        let val = self.evaluate(&expr)?;

        self.environment.borrow_mut().assign(name.to_string(), val.clone())?;

        Ok(val)
    }

    fn visit_binary(&mut self, l: &Expr, op: &LexemeKind, r: &Expr) -> InterpreterResult {
        let num = unwrap_number(self.evaluate(l))?;
        let num2 = unwrap_number(self.evaluate(r))?;

        match op {
            LexemeKind::Minus => Ok(Value::NUMBER(num - num2)),
            LexemeKind::Plus => Ok(Value::NUMBER(num + num2)),
            LexemeKind::Slash => Ok(Value::NUMBER(num / num2)),
            LexemeKind::Star => Ok(Value::NUMBER(num * num2)),
            _ => Err(RuntimeError {
                line: 0,
                message: "Invalid".to_string(),
            })
        }
    }

    fn visit_logical(&mut self, l: &Expr, op: &LexemeKind, r: &Expr) -> InterpreterResult {
        let left_result = self.evaluate(l);

        if op == &LexemeKind::OR {
            if is_truthy(&left_result) {
                return left_result;
            }
        } else {
            if !is_truthy(&left_result) {
                return left_result;
            }
        }

        self.evaluate(r)
    }

    fn visit_literal(&mut self, val: &Value) -> InterpreterResult {
        Ok(val.clone())
    }

    fn visit_unary(&mut self, op: &LexemeKind, r: &Expr) -> InterpreterResult {
        let num = unwrap_number(self.evaluate(r))?;

        match op {
            LexemeKind::Minus => Ok(Value::NUMBER(-num)),
            LexemeKind::Plus => Ok(Value::NUMBER(num)),
            _ => Err(RuntimeError {
                line: 0,
                message: "Can only prefix a number with + or -".to_string(),
            })
        }
    }

    fn visit_grouping(&mut self, expr: &Expr) -> InterpreterResult {
        let value = expr.accept(self)?;
        Ok(value)
    }

    fn visit_variable(&mut self, ident: &str) -> InterpreterResult {
        match self.environment.borrow().retrieve(ident) {
            Ok(val) => Ok(val.clone()),
            m => m
        }
    }

    fn visit_error(&mut self, line: &usize, message: &str) -> InterpreterResult {
        Err(RuntimeError {
            line: *line,
            message: message.to_string(),
        })
    }
}

fn unwrap_number(v: InterpreterResult) -> Result<f64, RuntimeError> {
    match v {
        Ok(Value::NUMBER(n)) => Ok(n),
        _ => Err(RuntimeError {
            line: 0,
            message: "Not a number".to_string(),
        })
    }
}

fn is_truthy(expr: &Result<Value, RuntimeError>) -> bool {
    match expr {
        Ok(Value::Null) => false,
        Ok(Value::BOOLEAN(false)) => false,
        _ => true,
    }
}

impl StatementVisitor<InterpreterResult> for Interpreter {
    fn visit_block(&mut self, stmts: &Vec<Stmt>) -> InterpreterResult {
        // make new inner environment
        // unable to have mutable copy as we descend down the tree :(
        let new_env = Environment::new_with_scope(&self.environment);

        let tmp = std::mem::replace(&mut self.environment, Rc::new(RefCell::new(new_env)));

        for stmt in stmts {
            self.execute(stmt)?;
        }

        self.environment = tmp;

        Ok(Value::Null)
    }

    fn visit_if(&mut self, condition: &Expr, then_branch: &Stmt, else_branch: &Option<Stmt>) -> InterpreterResult {
        match self.evaluate(condition) {
            Ok(Value::BOOLEAN(true)) => self.execute(then_branch),
            Ok(Value::BOOLEAN(false)) => {
                if let Some(e) = else_branch {
                    self.execute(e)
                } else {
                    Ok(Value::Null)
                }
            }
            _ => Ok(Value::Null)
        }
    }

    fn visit_while(&mut self, condition: &Expr, body: &Stmt) -> InterpreterResult {
        while is_truthy(&self.evaluate(condition)) {
            let _ = self.execute(body);
        }

        Ok(Value::Null)
    }

    fn visit_variable_def(&mut self, ident: &str, initializer: &Option<Expr>) -> InterpreterResult {
        if let Some(expr) = initializer {
            match self.evaluate(&expr) {
                Ok(val) => {
                    self.environment.borrow_mut().define(ident.to_string(), val);
                    Ok(Value::Null)
                }
                err => {
                    // var a = b;
                    err
                }
            }
        } else {
            // var a;
            Ok(Value::Null)
        }
    }

    fn visit_print(&mut self, expr: &Option<Expr>) -> InterpreterResult {
        match expr {
            Some(expr) => {
                let value = self.evaluate(expr)?;

                println!("{}", value);

                Ok(value)
            }
            _ => Ok(Value::Null)
        }
    }

    fn visit_expr(&mut self, expr: &Expr) -> InterpreterResult {
        self.evaluate(expr)
    }

    fn visit_error(&mut self, line: &usize, message: &str) -> InterpreterResult {
        Err(RuntimeError {
            line: *line,
            message: message.to_string(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Scanner;
    use crate::parser::Parser;

    #[test]
    fn it_works() {
        let tokens = Scanner::new("-1".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res.unwrap(), Value::NUMBER(-1.0));
    }

    #[test]
    fn it_adds() {
        let tokens = Scanner::new("-1+1".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res.unwrap(), Value::NUMBER(0.0));
    }

    #[test]
    fn it_unary_works() {
        let tokens = Scanner::new("+1".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res.unwrap(), Value::NUMBER(1.0));
    }

    #[test]
    fn it_errors() {
        let tokens = Scanner::new("()".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Err(RuntimeError { line: 0, message: "Parsing error at RightParen".to_string() }));
    }

    #[test]
    fn it_does_not_error_prefix_number() {
        let tokens = Scanner::new("*1".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::NUMBER(1.0)));
    }

    // #[test]
    // fn it_errors_invalid_operator() {
    //     let tokens = Scanner::new("1&1".to_owned()).collect();
    //     let stmts = Parser::new(tokens).parse();
    //     let mut interp = Interpreter::new();
    //     let res = interp.start(stmts);
    //     assert_eq!(res, Err(RuntimeError { line: 0, message: "Parsing error at &".to_string() }));
    // }

    #[test]
    fn it_works_stmts() {
        let tokens = Scanner::new("print(\"foo\")".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::STRING("foo".to_string())));

        let tokens = Scanner::new("print(2)".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::NUMBER(2.0)));

        let tokens = Scanner::new("print(2+1)".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::NUMBER(3.0)));

        let tokens = Scanner::new("print()".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::Null));
    }

    #[test]
    fn it_works_variables() {
        let tokens = Scanner::new("var a;".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::Null));
        assert_eq!(interp.environment.borrow().variables.len(), 0);
        assert_eq!(interp.environment.borrow().variables.get("a"), None);

        let tokens = Scanner::new("var a = \"foo\";".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::Null));
        assert_eq!(interp.environment.borrow().variables.len(), 1);
        assert_eq!(interp.environment.borrow().variables.get("a"), Some(&Value::STRING("foo".to_string())));
    }

    #[test]
    fn it_works_multiline() {
        let tokens = Scanner::new("var a = 4;
print(a);".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::NUMBER(4.0)));
        assert_eq!(interp.environment.borrow().variables.len(), 1);
        assert_eq!(interp.environment.borrow().variables.get("a"), Some(&Value::NUMBER(4.0)));
    }

    #[test]
    fn it_errors_variable() {
        let tokens = Scanner::new("var a = b;".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Err(RuntimeError { line: 0, message: "Variable \"b\" does not exist".to_string() }));
    }

    #[test]
    fn it_works_block_ss() {
        let tokens = Scanner::new("{
var a = 4;
print(a);
}".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::Null));
        assert_eq!(interp.environment.borrow().variables.len(), 0);
        assert_eq!(interp.environment.borrow().variables.get("a"), None);
        assert_eq!(interp.environment.borrow().enclosing, None);
    }

    #[test]
    fn it_works_shadow_block() {
        let tokens = Scanner::new("
var a = 4;
{
    var a = 4;
    print(a);
}
".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::Null));
        assert_eq!(interp.environment.borrow().variables.len(), 1);
        assert_eq!(interp.environment.borrow().variables.get("a"), Some(&Value::NUMBER(4.0)));
        // assert_eq!(interp.environment.borrow().enclosing, None);
    }

    #[test]
    fn it_works_replace_inner_block() {
        let tokens = Scanner::new("
var a = 4;
{
    a = 5;
    var b = 10.1;
    print(a);
}
".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::Null));
        assert_eq!(interp.environment.borrow().variables.len(), 1);
        assert_eq!(interp.environment.borrow().variables.get("a"), Some(&Value::NUMBER(5.0)));
        assert_eq!(interp.environment.borrow().enclosing, None);
    }

    #[test]
    fn it_block_errors() {
        let tokens = Scanner::new("
var a = 4;
{
    b = 5;
    print(b);
}
".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Err(RuntimeError { line: 0, message: "Variable \"b\" does not exist".to_string() }));
    }

    #[test]
    fn it_if_stmt_works() {
        let tokens = Scanner::new("
var a = 5;
if (true)
{
    var b = 10.1;
    print(a);
}
".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::Null));
        assert_eq!(interp.environment.borrow().variables.len(), 1);
        assert_eq!(interp.environment.borrow().variables.get("a"), Some(&Value::NUMBER(5.0)));
        assert_eq!(interp.environment.borrow().enclosing, None);
    }

    #[test]
    fn it_and_operator_works() {
        let tokens = Scanner::new("
var a = true and 5;
if (a)
{
    print(a);
}
".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::Null));
        assert_eq!(interp.environment.borrow().variables.len(), 1);
        assert_eq!(interp.environment.borrow().variables.get("a"), Some(&Value::NUMBER(5.0)));
        assert_eq!(interp.environment.borrow().enclosing, None);
    }

    #[test]
    fn it_or_operator_works() {
        let tokens = Scanner::new("
var a = \"hi\" or 5;
if (a)
{
    print(a);
}
".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::Null));
        assert_eq!(interp.environment.borrow().variables.len(), 1);
        assert_eq!(interp.environment.borrow().variables.get("a"), Some(&Value::STRING("hi".to_string())));
        assert_eq!(interp.environment.borrow().enclosing, None);
    }

    #[test]
    fn it_or_falsey_operator_works() {
        let tokens = Scanner::new("
var a = false or 5;
print(a);
".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::NUMBER(5.0)));
        assert_eq!(interp.environment.borrow().variables.len(), 1);
        assert_eq!(interp.environment.borrow().variables.get("a"), Some(&Value::NUMBER(5.0)));
        assert_eq!(interp.environment.borrow().enclosing, None);
    }

    #[test]
    fn it_and_falsey_operator_works() {
        let tokens = Scanner::new("
var a = false and false;
print(a);
".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::BOOLEAN(false)));
        assert_eq!(interp.environment.borrow().variables.len(), 1);
        assert_eq!(interp.environment.borrow().variables.get("a"), Some(&Value::BOOLEAN(false)));
        assert_eq!(interp.environment.borrow().enclosing, None);
    }

    #[test]
    fn it_while_works() {
        let tokens = Scanner::new("
var a = 1;
var b = true;
while (b) {
    b = false;
    a = 2;
}
".to_owned()).collect();
        let stmts = Parser::new(tokens).parse();
        let mut interp = Interpreter::new();
        let res = interp.start(stmts);
        assert_eq!(res, Ok(Value::Null));
        assert_eq!(interp.environment.borrow().variables.len(), 2);
        assert_eq!(interp.environment.borrow().variables.get("b"), Some(&Value::BOOLEAN(false)));
        assert_eq!(interp.environment.borrow().variables.get("a"), Some(&Value::NUMBER(2.0)));
        assert_eq!(interp.environment.borrow().enclosing, None);
    }
}
