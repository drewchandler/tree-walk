mod ast_printer;
mod expression;
mod interpreter;
mod parser;
mod scanner;
mod token;
mod visitor;

use std::env;
use std::fmt;
use std::fs;
use std::io::{self, Write};
use std::path;
use std::process;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn main() -> Result<()> {
    let args: Vec<String> = env::args().skip(1).collect();

    match args.len() {
        0 => run_prompt(),
        1 => run_file(&args[0]),
        _ => {
            println!("Usage: tree-walk [script]");
            process::exit(64);
        }
    }
}

fn run_prompt() -> Result<()> {
    loop {
        print!("> ");
        io::stdout().flush()?;

        let mut line = String::new();
        io::stdin().read_line(&mut line)?;

        if line.len() == 0 {
            break;
        }

        match run(line) {
            Ok(v) => {
                println!("{}", v);
            }
            Err(e) => {
                eprintln!("{}", e);
            }
        }
    }

    Ok(())
}

fn run_file<P: AsRef<path::Path> + fmt::Display>(filename: P) -> Result<()> {
    let source = fs::read_to_string(filename)?;

    if let Err(e) = run(source) {
        eprintln!("{}", e);
        std::process::exit(70);
    }

    Ok(())
}

fn run(source: String) -> Result<expression::Value> {
    let scan_results =
        scanner::Scanner::new(&source).collect::<std::result::Result<Vec<_>, _>>()?;
    let parse_results =
        parser::Parser::new(&scan_results).collect::<std::result::Result<Vec<_>, _>>()?;

    let mut last_value = expression::Value::Nil;

    for expression in parse_results {
        last_value = expression.accept(&mut interpreter::Interpreter)?;
    }

    Ok(last_value)
}
