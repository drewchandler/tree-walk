use std::cell::RefCell;
use std::collections;
use std::rc::Rc;
use std::collections::HashMap;
use crate::parser::Value;
use super::RuntimeError;

#[derive(Clone, Debug, PartialEq)]
pub struct Environment {
    pub variables: collections::HashMap<String, Value>,
    pub enclosing: Option<Rc<RefCell<Environment>>>, // pattern especially useful when a function will cannot borrow a field as mutable. Once something already has a reference, you can't then borrow as mutable
    // place to mutate and read from enclosing.  But b/c cloned, the original Environment does not
    // inherit values after mutation
}

impl Environment {
    pub fn new() -> Self {
        Self {
            variables: HashMap::new(),
            enclosing: None,
        }
    }

    pub fn new_with_scope(env: &Rc<RefCell<Environment>>) -> Self {
        // create a new inner scope
        Self {
            variables: HashMap::new(), // empty b/c retrieve will look up enclosing chain for variables if need be
            enclosing: Some(env.clone()),
        }
    }

    pub fn define(&mut self, name: String, value: Value) {
        self.variables.insert(name, value);
    }

    pub fn assign(&mut self, name: String, value: Value) -> Result<(), RuntimeError> {
        if !self.variables.contains_key(&name) {
            // if inner most scope self.variables does not contain variable, check outer for variable
            if let Some(ref encl) = self.enclosing {
                // Rc<RefCell> - pointer with shared ownership with interior mutability
                // need a ref b/c enclosing value does not implement the Copy trait
                return encl.borrow_mut().assign(name.clone(), value.clone());
            } else {
                // if can never find, then error
                // for key in self.variables.keys() {
                //     eprintln!("{:?}", key);
                // }
                return Err(RuntimeError {
                    line: 0,
                    message: format!("Variable \"{}\" does not exist", name),
                });
            }
        }

        self.variables.insert(name, value);

        Ok(())
    }

    pub fn retrieve(&self, name: &str) -> Result<Value, RuntimeError> {
        let val = self.variables.get(name);
        if val.is_some() {
            Ok(val.unwrap().clone())
        } else {
            // check enclosing scope recursively. Variables are lexically scoped so we need to do this
            if let Some(ref enclosing) = self.enclosing {
                let enc = enclosing.borrow();
                let val = enc.retrieve(name);
                match val {
                    Ok(val) => Ok(val.clone()),
                    Err(RuntimeError { line, message }) => Err(RuntimeError { line, message })
                }
            } else {
                // if can never find, then error
                // for key in self.variables.keys() {
                //     eprintln!("{:?}", key);
                // }
                Err(RuntimeError {
                    line: 0,
                    message: format!("Variable \"{}\" does not exist", name),
                })
            }
        }
    }
}
