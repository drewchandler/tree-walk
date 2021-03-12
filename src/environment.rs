use std::cell;
use std::collections;
use std::rc;

use crate::errors::RuntimeError;
use crate::expression::Value;
use crate::token::Token;

pub type Environment = rc::Rc<cell::RefCell<EnvironmentData>>;

pub struct EnvironmentData {
    values: collections::HashMap<String, Value>,
    enclosing: Option<Environment>,
}

impl EnvironmentData {
    pub fn new(enclosing: Option<Environment>) -> Self {
        Self {
            values: collections::HashMap::new(),
            enclosing: enclosing,
        }
    }
}

pub fn env_new(enclosing: Option<&Environment>) -> Environment {
    rc::Rc::new(cell::RefCell::new(EnvironmentData::new(
        enclosing.map(|e| e.clone()),
    )))
}

pub fn env_define(env: &Environment, name: &Token, value: Value) {
    let mut e = env.borrow_mut();

    e.values.insert(name.identifier(), value);
}

pub fn env_assign(env: &Environment, name: &Token, value: Value) -> Result<(), RuntimeError> {
    let mut e = env.borrow_mut();
    let identifier = name.identifier();

    if !e.values.contains_key(&identifier) {
        if let Some(ref enclosing) = e.enclosing {
            return env_assign(enclosing, name, value);
        } else {
            return Err(RuntimeError::from_token(
                name,
                format!("Undefined variable '{}'.", identifier),
            ));
        }
    }

    e.values.insert(identifier, value);
    Ok(())
}

pub fn env_get(env: &Environment, name: &Token) -> Result<Value, RuntimeError> {
    let e = env.borrow();
    let identifier = name.identifier();

    if let Some(value) = e.values.get(&identifier) {
        Ok(value.clone())
    } else {
        if let Some(ref enclosing) = e.enclosing {
            env_get(enclosing, name)
        } else {
            Err(RuntimeError::from_token(
                name,
                format!("Undefined variable '{}'.", identifier),
            ))
        }
    }
}
