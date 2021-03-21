mod lexer;
mod parser;
mod interpreter;
mod visitor;

use lexer::Scanner;
use parser::Parser;
use interpreter::Interpreter;

use std::env;
use std::fmt;
use std::fs;
use std::io::{self, Write};
use std::path;
use std::process;

type TWResult<T> = Result<T, Box<dyn std::error::Error>>;

fn main() -> TWResult<()> {
    let args: Vec<String> = env::args().skip(1).collect();

    match args.len() {
        0 => run_prompt(),
        1 => run_file(&args[0]),
        _ => {
            eprintln!("Usage: tree-walk [script]");
            process::exit(64);
        }
    }
}

fn run_prompt() -> TWResult<()> {
    loop {
        print!("> ");
        io::stdout().flush()?;

        let mut line = String::new();
        io::stdin().read_line(&mut line)?;

        if line.len() == 0 {
            break;
        }

        run(line)?;
    }

    Ok(())
}

fn run_file<P: AsRef<path::Path> + fmt::Display>(filename: P) -> TWResult<()> {
    run(fs::read_to_string(filename)?)
}

fn run(source: String) -> TWResult<()> {
    let tokens = Scanner::new(source).collect();

    let mut parser = Parser::new(tokens); // vec![token1, token2]
    let stmts = parser.parse();
    let mut interp = Interpreter::new();
    let res = interp.start(stmts);
    eprintln!("{:?}", res);

    Ok(())
}
