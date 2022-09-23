use std::error;
use std::fmt;
use std::str;

use peekmore::PeekMore;

use crate::token::{Lexeme, Token};

#[derive(Debug, Clone, PartialEq)]
pub enum ScanErrorType {
    UnexpectedCharacter(char),
    UnterminatedString,
}

impl fmt::Display for ScanErrorType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnexpectedCharacter(c) => write!(f, "Unexpected character {}", c),
            Self::UnterminatedString => write!(f, "Unterminated string"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ScanError {
    line: u64,
    error: ScanErrorType,
}

impl ScanError {
    fn new(error: ScanErrorType, line: u64) -> Self {
        Self { error, line }
    }
}

impl fmt::Display for ScanError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} on line {}", self.error, self.line)
    }
}

impl error::Error for ScanError {}

type ScanResult = Result<Token, ScanError>;

fn is_digit(c: char) -> bool {
    c >= '0' && c <= '9'
}

fn is_alpha(c: char) -> bool {
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'
}

fn is_alpha_numeric(c: char) -> bool {
    is_alpha(c) || is_digit(c)
}

pub struct Scanner<'a> {
    chars: peekmore::PeekMoreIterator<str::Chars<'a>>,
    line: u64,
    done: bool,
}

impl<'a> Scanner<'a> {
    pub fn new(source: &'a String) -> Self {
        Self {
            chars: source.chars().peekmore(),
            line: 0,
            done: false,
        }
    }

    fn build_token(&self, lexeme: Lexeme) -> ScanResult {
        Ok(Token::new(lexeme, self.line))
    }

    fn if_match(
        &mut self,
        cmp: char,
        match_lexeme: Lexeme,
        non_match_lexeme: Lexeme,
    ) -> ScanResult {
        let lexeme = if self.peek_eq(cmp) {
            self.chars.next();

            match_lexeme
        } else {
            non_match_lexeme
        };

        self.build_token(lexeme)
    }

    fn err(&self, error: ScanErrorType) -> ScanResult {
        Err(ScanError::new(error, self.line))
    }

    fn peek_eq(&mut self, cmp: char) -> bool {
        self.chars.peek() == Some(&cmp)
    }

    fn at_end(&mut self) -> bool {
        self.chars.peek() == None
    }

    fn string(&mut self) -> ScanResult {
        let mut chars: Vec<char> = Vec::new();

        let mut new_lines = 0;
        self.collect_while(
            &mut |c| match c {
                '"' => false,
                '\n' => {
                    new_lines += 1;
                    true
                }
                _ => true,
            },
            &mut chars,
        );

        self.line += new_lines;

        if self.at_end() {
            return self.err(ScanErrorType::UnterminatedString);
        }

        self.chars.next();

        self.build_token(Lexeme::String(chars.iter().collect()))
    }

    fn number(&mut self, first_digit: char) -> ScanResult {
        let mut chars: Vec<char> = Vec::new();
        chars.push(first_digit);

        self.collect_while(&mut is_digit, &mut chars);

        if self.peek_eq('.') {
            match self.chars.peek_nth(1) {
                Some(c) if is_digit(*c) => {
                    chars.push(self.chars.next().unwrap());
                    self.collect_while(&mut is_digit, &mut chars);
                }
                _ => {}
            }
        }

        let number_string: String = chars.iter().collect();
        self.build_token(Lexeme::Number(number_string.parse().unwrap()))
    }

    fn identifier(&mut self, first_char: char) -> ScanResult {
        let mut chars: Vec<char> = Vec::new();
        chars.push(first_char);
        self.collect_while(&mut is_alpha_numeric, &mut chars);
        let identifier: String = chars.iter().collect();

        let lexeme = match identifier.as_str() {
            "and" => Lexeme::And,
            "class" => Lexeme::Class,
            "else" => Lexeme::Else,
            "false" => Lexeme::False,
            "for" => Lexeme::For,
            "fun" => Lexeme::Fun,
            "if" => Lexeme::If,
            "nil" => Lexeme::Nil,
            "or" => Lexeme::Or,
            "print" => Lexeme::Print,
            "return" => Lexeme::Return,
            "super" => Lexeme::Super,
            "this" => Lexeme::This,
            "true" => Lexeme::True,
            "var" => Lexeme::Var,
            "while" => Lexeme::While,
            _ => Lexeme::Identifier(identifier),
        };

        self.build_token(lexeme)
    }

    fn collect_while<P>(&mut self, predicate: &mut P, buffer: &mut Vec<char>) -> ()
    where
        P: FnMut(char) -> bool,
    {
        loop {
            match self.chars.peek() {
                Some(c) if predicate(*c) => {
                    buffer.push(self.chars.next().unwrap());
                }
                _ => break,
            };
        }
    }
}

impl<'a> Iterator for Scanner<'a> {
    type Item = ScanResult;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let token = loop {
            match self.chars.next() {
                None => {
                    self.done = true;
                    break self.build_token(Lexeme::Eof);
                }
                Some('(') => break self.build_token(Lexeme::LeftParen),
                Some(')') => break self.build_token(Lexeme::RightParen),
                Some('{') => break self.build_token(Lexeme::LeftBrace),
                Some('}') => break self.build_token(Lexeme::RightBrace),
                Some(',') => break self.build_token(Lexeme::Comma),
                Some('.') => break self.build_token(Lexeme::Dot),
                Some('-') => break self.build_token(Lexeme::Minus),
                Some('+') => break self.build_token(Lexeme::Plus),
                Some(';') => break self.build_token(Lexeme::Semicolon),
                Some('*') => break self.build_token(Lexeme::Star),
                Some('!') => break self.if_match('=', Lexeme::BangEqual, Lexeme::Bang),
                Some('=') => break self.if_match('=', Lexeme::EqualEqual, Lexeme::Equal),
                Some('<') => break self.if_match('=', Lexeme::LessEqual, Lexeme::Less),
                Some('>') => break self.if_match('=', Lexeme::GreaterEqual, Lexeme::Greater),
                Some('/') => {
                    if self.peek_eq('/') {
                        self.chars
                            .by_ref()
                            .take_while(|c| *c != '\n')
                            .for_each(drop);

                        continue;
                    } else {
                        break self.build_token(Lexeme::Slash);
                    }
                }
                Some(' ') | Some('\r') | Some('\t') => continue,
                Some('\n') => {
                    self.line += 1;
                    continue;
                }
                Some('"') => break self.string(),
                Some(c) => {
                    if is_digit(c) {
                        break self.number(c);
                    } else if is_alpha(c) {
                        break self.identifier(c);
                    } else {
                        break self.err(ScanErrorType::UnexpectedCharacter(c));
                    }
                }
            }
        };

        Some(token)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_handles_comments() {
        let source = "{} // foo".to_owned();
        let mut sc = Scanner::new(&source);
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::LeftBrace, 0))));
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::RightBrace, 0))));
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Eof, 0))));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_comments_end() {
        let source = "{} //".to_owned();
        let mut sc = Scanner::new(&source);
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::LeftBrace, 0))));
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::RightBrace, 0))));
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Eof, 0))));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_strings() {
        let source = "\"bar\"".to_owned();
        let mut sc = Scanner::new(&source);
        assert_eq!(
            sc.next(),
            Some(Ok(Token::new(Lexeme::String("bar".to_string()), 0)))
        );
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Eof, 0))));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_combo_strings() {
        let source = "\"foo\" == \"bar\" ".to_owned();
        let mut sc = Scanner::new(&source);
        assert_eq!(
            sc.next(),
            Some(Ok(Token::new(Lexeme::String("foo".to_string()), 0)))
        );
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::EqualEqual, 0))));
        assert_eq!(
            sc.next(),
            Some(Ok(Token::new(Lexeme::String("bar".to_string()), 0)))
        );
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Eof, 0))));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_numbers() {
        let source = "1.2".to_owned();
        let mut sc = Scanner::new(&source);
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Number(1.2), 0))));
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Eof, 0))));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_addition() {
        let source = "1+2.0".to_owned();
        let mut sc = Scanner::new(&source);
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Number(1.0), 0))));
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Plus, 0))));
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Number(2.0), 0))));
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Eof, 0))));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_reserved_words() {
        let source = "and".to_owned();
        let mut sc = Scanner::new(&source);
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::And, 0))));
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Eof, 0))));
        assert_eq!(sc.next(), None);

        let source = "while".to_owned();
        let mut sc = Scanner::new(&source);
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::While, 0))));
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Eof, 0))));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_idents_partial_reserved() {
        let source = "andd".to_owned();
        let mut sc = Scanner::new(&source);
        assert_eq!(
            sc.next(),
            Some(Ok(Token::new(Lexeme::Identifier("andd".to_string()), 0)))
        );
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Eof, 0))));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_newlines() {
        let source = "
and while

andd
"
        .to_owned();
        let mut sc = Scanner::new(&source);
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::And, 1))));
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::While, 1))));
        assert_eq!(
            sc.next(),
            Some(Ok(Token::new(Lexeme::Identifier("andd".to_string()), 3)))
        );
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Eof, 4))));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_unexpected_character() {
        let source = "/·".to_owned();
        let mut sc = Scanner::new(&source);
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Slash, 0))));
        assert_eq!(
            sc.next(),
            Some(Err(ScanError::new(
                ScanErrorType::UnexpectedCharacter('·'),
                0
            )))
        );
        assert_eq!(sc.next(), Some(Ok(Token::new(Lexeme::Eof, 0))));
        assert_eq!(sc.next(), None);
    }
}
