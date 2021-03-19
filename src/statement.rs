use crate::expression::Expression;
use crate::token::Token;

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Block(Vec<Statement>),
    Expression(Box<Expression>),
    If {
        condition: Box<Expression>,
        then_branch: Box<Statement>,
        else_branch: Option<Box<Statement>>,
    },
    Print(Box<Expression>),
    Var {
        name: Token,
        initializer: Option<Box<Expression>>,
    },
    While {
        condition: Box<Expression>,
        body: Box<Statement>,
    },
}

impl Statement {
    pub fn accept<T>(&self, visitor: &mut dyn StatementVisitor<T>) -> T {
        match &self {
            &Self::Block(ss) => visitor.visit_block(ss),
            &Self::If {
                ref condition,
                ref then_branch,
                else_branch,
            } => visitor.visit_if(condition, then_branch, else_branch.as_deref()),
            &Self::Expression(ref e) => visitor.visit_expression(e),
            &Self::Print(ref e) => visitor.visit_print(e),
            &Self::Var {
                ref name,
                initializer,
            } => visitor.visit_var(name, initializer.as_deref()),
            &Self::While {
                ref condition,
                ref body,
            } => visitor.visit_while(condition, body),
        }
    }
}

pub trait StatementVisitor<T> {
    fn visit_block(&mut self, statements: &Vec<Statement>) -> T;
    fn visit_if(
        &mut self,
        condition: &Expression,
        then_branch: &Statement,
        else_branch: Option<&Statement>,
    ) -> T;
    fn visit_expression(&mut self, expression: &Expression) -> T;
    fn visit_print(&mut self, expression: &Expression) -> T;
    fn visit_var(&mut self, name: &Token, initializer: Option<&Expression>) -> T;
    fn visit_while(&mut self, condition: &Expression, body: &Statement) -> T;
}
