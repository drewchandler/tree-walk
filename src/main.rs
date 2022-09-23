mod ast_printer;
mod environment;
mod errors;
mod expression;
mod interpreter;
mod parser;
mod scanner;
mod statement;
mod token;

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
    let mut stdout = io::stdout();
    let mut interpreter = interpreter::Interpreter::new(&mut stdout);

    loop {
        print!("> ");
        io::stdout().flush()?;

        let mut line = String::new();
        io::stdin().read_line(&mut line)?;

        if line.len() == 0 {
            break;
        }

        if let Err(e) = run(&mut interpreter, line) {
            eprintln!("{}", e);
        }
    }

    Ok(())
}

fn run_file<P: AsRef<path::Path> + fmt::Display>(filename: P) -> Result<()> {
    let source = fs::read_to_string(filename)?;

    if let Err(e) = run(
        &mut interpreter::Interpreter::new(&mut io::stdout()),
        source,
    ) {
        eprintln!("{}", e);
        std::process::exit(70);
    }

    Ok(())
}

fn run(interpreter: &mut interpreter::Interpreter, source: String) -> Result<()> {
    let scan_results =
        scanner::Scanner::new(&source).collect::<std::result::Result<Vec<_>, _>>()?;
    let parse_results =
        parser::Parser::new(&scan_results).collect::<std::result::Result<Vec<_>, _>>()?;

    for statement in parse_results {
        interpreter.execute(&statement)?;
    }

    Ok(())
}
