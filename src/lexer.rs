extern crate regex;
use regex::Regex;
use std::fmt;

#[derive(Clone, Debug, PartialEq)]
pub enum LexemeKind {
    // Single-character tokens.
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,
    Whitespace,

    // One or two character tokens.
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // Literals.
    IDENTIFIER(String),
    STRING(String),
    NUMBER(f64),

    // Keywords.
    AND,
    CLASS,
    ELSE,
    FALSE,
    FUN,
    FOR,
    IF,
    NIL,
    OR,
    PRINT,
    RETURN,
    SUPER,
    THIS,
    TRUE,
    VAR,
    WHILE,

    UNEXPECTED(String),

    EOF,
}

impl LexemeKind {
    pub fn to_string(&self) -> String {
        match self {
            Self::LeftParen => "(".to_owned(),
            Self::RightParen => ")".to_owned(),
            Self::LeftBrace => "{".to_owned(),
            Self::RightBrace => "}".to_owned(),
            Self::Comma => ".".to_owned(),
            Self::Dot => ".".to_owned(),
            Self::Minus => "-".to_owned(),
            Self::Plus => "+".to_owned(),
            Self::Semicolon => ";".to_owned(),
            Self::Slash => "/".to_owned(),
            Self::Star => "*".to_owned(),
            Self::Bang => "!".to_owned(),
            Self::BangEqual => "!!".to_owned(),
            Self::Equal => "=".to_owned(),
            Self::EqualEqual => "==".to_owned(),
            Self::Greater => ">".to_owned(),
            Self::GreaterEqual => ">=".to_owned(),
            Self::Less => "<".to_owned(),
            Self::LessEqual => "<=".to_owned(),
            Self::Whitespace => " ".to_owned(),
            Self::IDENTIFIER(i) => i.to_owned(),
            Self::STRING(s) => format!("\"{}\"", s),
            Self::NUMBER(n) => n.to_string(),
            Self::AND => "and".to_owned(),
            Self::CLASS => "class".to_owned(),
            Self::ELSE => "else".to_owned(),
            Self::FALSE => "false".to_owned(),
            Self::FUN => "fun".to_owned(),
            Self::FOR => "for".to_owned(),
            Self::IF => "if".to_owned(),
            Self::NIL => "nil".to_owned(),
            Self::OR => "or".to_owned(),
            Self::PRINT => "print".to_owned(),
            Self::RETURN => "return".to_owned(),
            Self::SUPER => "super".to_owned(),
            Self::THIS => "this".to_owned(),
            Self::TRUE => "true".to_owned(),
            Self::VAR => "var".to_owned(),
            Self::WHILE => "while".to_owned(),
            Self::EOF => "<EOF>".to_owned(),
            Self::UNEXPECTED(st) => st.clone(),
        }
    }
}

impl fmt::Display for LexemeKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, PartialEq)]
pub struct Token {
    pub line: usize,
    pub lexeme: LexemeKind,
}

impl Token {
    pub fn new(lexeme: LexemeKind, line: usize) -> Self {
        Self { lexeme, line }
    }
}

pub struct Scanner {
    cursor: usize,
    chars: Vec<char>,
    line: usize,
}

// Lexer - group raw substrings into lexemes.  This is a higher representation than the raw source.
impl Scanner {
    pub fn new(source: String) -> Self {
        Self {
            // time and space higher with collect
            chars: source.chars().collect(),
            cursor: 0,
            line: 0,
        }
    }

    fn current_char(&self) -> Option<&char> {
        self.chars.get(self.cursor)
    }

    fn peek_next(&self) -> Option<&char> {
        self.chars.get(self.cursor + 1)
    }

    fn is_finished(&self) -> bool {
        self.cursor >= self.chars.len()
    }

    fn number_boundary(&mut self) -> f64 {
        let mut buffer = String::new();
        while self.current_char().is_some() {
            let c = self.current_char().unwrap();
            match *c {
                add if is_number(add) || add == '.' => {
                    buffer.push(add.to_owned());
                    self.cursor += 1;
                }
                _ => break,
            }
        }

        buffer.parse().unwrap()
    }

    fn word_boundary(&mut self) -> String {
        // first was ". next char is potentially the word
        self.cursor += 1;
        let mut buffer = String::new();
        while self.peek_next().is_some() {
            let c = self.current_char().unwrap();
            match *c {
                '"' => break,
                add => {
                    buffer.push(add.to_owned());
                    self.cursor += 1;
                }
            }
        }

        buffer
    }

    fn identifier_boundary(&mut self) -> LexemeKind {
        let mut buffer = String::new();
        while self.current_char().is_some() {
            let c = self.current_char().unwrap();
            match *c {
                add if is_number(add) || is_valid_ident(add) => {
                    buffer.push(add.to_owned());
                    self.cursor += 1;
                }
                _ => break,
            }
        }

        match buffer.as_str() {
            "and" => LexemeKind::AND,
            "class" => LexemeKind::CLASS,
            "else" => LexemeKind::ELSE,
            "false" => LexemeKind::FALSE,
            "for" => LexemeKind::FOR,
            "fun" => LexemeKind::FUN,
            "if" => LexemeKind::IF,
            "nil" => LexemeKind::NIL,
            "or" => LexemeKind::OR,
            "print" => LexemeKind::PRINT,
            "return" => LexemeKind::RETURN,
            "super" => LexemeKind::SUPER,
            "this" => LexemeKind::THIS,
            "true" => LexemeKind::TRUE,
            "var" => LexemeKind::VAR,
            "while" => LexemeKind::WHILE,
            _ => LexemeKind::IDENTIFIER(buffer),
        }
    }
}

impl Iterator for Scanner {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_finished() {
            return None;
        }

        let c = self.chars[self.cursor];

        if is_number(c) {
            let num = self.number_boundary();
            return Some(Token::new(LexemeKind::NUMBER(num), self.line));
        } else if is_valid_ident(c) {
            let lexeme = self.identifier_boundary();
            return Some(Token::new(lexeme, self.line));
        }

        let lexeme = match c {
            ')' => Some(Token::new(LexemeKind::RightParen, self.line)),
            '(' => Some(Token::new(LexemeKind::LeftParen, self.line)),
            '{' => Some(Token::new(LexemeKind::LeftBrace, self.line)),
            '}' => Some(Token::new(LexemeKind::RightBrace, self.line)),
            ',' => Some(Token::new(LexemeKind::Comma, self.line)),
            '.' => Some(Token::new(LexemeKind::Dot, self.line)),
            '-' => Some(Token::new(LexemeKind::Minus, self.line)),
            '+' => Some(Token::new(LexemeKind::Plus, self.line)),
            ';' => Some(Token::new(LexemeKind::Semicolon, self.line)),
            '*' => Some(Token::new(LexemeKind::Star, self.line)),
            '!' => {
                let next = self.peek_next();
                Some(Token::new(
                    if next == Some(&'=') {
                        self.cursor += 1;
                        LexemeKind::BangEqual
                    } else {
                        LexemeKind::Bang
                    },
                    self.line,
                ))
            }
            '=' => {
                let next = self.peek_next();
                Some(Token::new(
                    if next == Some(&'=') {
                        self.cursor += 1;
                        LexemeKind::EqualEqual
                    } else {
                        LexemeKind::Equal
                    },
                    self.line,
                ))
            }
            '<' => {
                let next = self.peek_next();
                Some(Token::new(
                    if next == Some(&'=') {
                        self.cursor += 1;
                        LexemeKind::LessEqual
                    } else {
                        LexemeKind::Less
                    },
                    self.line,
                ))
            }
            '>' => {
                let next = self.peek_next();
                Some(Token::new(
                    if next == Some(&'=') {
                        self.cursor += 1;
                        LexemeKind::GreaterEqual
                    } else {
                        LexemeKind::Greater
                    },
                    self.line,
                ))
            }
            '/' => {
                let next = self.peek_next();
                if next == Some(&'/') {
                    self.cursor += 1;
                    let mut done = false;
                    while !done {
                        if self.is_finished() {
                            done = true;
                        } else {
                            let next = self.peek_next();
                            if next != Some(&'\n') {
                                if self.is_finished() {
                                    done = true;
                                } else {
                                    self.cursor += 1;
                                }
                            } else {
                                done = true;
                            }
                        }
                    }

                    // We aren't capturing tokens because the point of this is to execute the
                    // program and not faithfully represent every character (lossless)
                    self.next()
                } else {
                    Some(Token::new(LexemeKind::Slash, self.line))
                }
            }
            c if c.is_whitespace() => {
                // eat whitepsace so it doesnt show up Token
                if c == '\n' {
                    self.line += 1;
                }
                Some(Token::new(LexemeKind::Whitespace, self.line))
            }
            '"' => {
                let word = self.word_boundary();
                Some(Token::new(LexemeKind::STRING(word), self.line))
            }
            _ => {
                if self.is_finished() {
                    Some(Token::new(LexemeKind::EOF, self.line))
                } else {
                    Some(Token::new(LexemeKind::UNEXPECTED(c.to_string()), self.line))
                }
            }
        };

        self.cursor += 1;
        lexeme
    }
}

fn is_number(c: char) -> bool {
    c >= '0' && c <= '9'
}

fn is_valid_ident(c: char) -> bool {
    let re = Regex::new(r"[a-zA-Z_]").unwrap();
    re.is_match(&c.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut sc = Scanner::new("(!=) ==".to_owned());
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::LeftParen, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::BangEqual, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::RightParen, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::EqualEqual, 0));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_works_collect() {
        let tokens: Vec<Token> = Scanner::new("(!=) ==".to_owned()).collect();
        assert_eq!(tokens.len(), 5);
    }

    #[test]
    fn it_handles_comments() {
        let mut sc = Scanner::new("{} // foo".to_owned());
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::LeftBrace, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::RightBrace, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 0));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_comments_end() {
        let mut sc = Scanner::new("{} //".to_owned());
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::LeftBrace, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::RightBrace, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 0));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_comparisons() {
        let mut sc = Scanner::new(">= <= != () ==".to_owned());
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::GreaterEqual, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::LessEqual, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::BangEqual, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::LeftParen, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::RightParen, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::EqualEqual, 0));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_strings() {
        let mut sc = Scanner::new("\"bar\" ".to_owned());
        assert_eq!(
            sc.next().unwrap(),
            Token::new(LexemeKind::STRING("bar".to_string()), 0)
        );
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 0));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_combo_strings() {
        let mut sc = Scanner::new("\"foo\" = \"bar\" ".to_owned());
        assert_eq!(
            sc.next().unwrap(),
            Token::new(LexemeKind::STRING("foo".to_string()), 0)
        );
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Equal, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 0));
        assert_eq!(
            sc.next().unwrap(),
            Token::new(LexemeKind::STRING("bar".to_string()), 0)
        );
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 0));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_numbers() {
        let mut sc = Scanner::new("1.2".to_owned());
        assert_eq!(
            sc.next().unwrap(),
            Token::new(LexemeKind::NUMBER("1.2".parse().unwrap()), 0)
        );
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_addition() {
        let mut sc = Scanner::new("1+2.0".to_owned());
        assert_eq!(
            sc.next().unwrap(),
            Token::new(LexemeKind::NUMBER("1.0".parse().unwrap()), 0)
        );
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Plus, 0));
        assert_eq!(
            sc.next().unwrap(),
            Token::new(LexemeKind::NUMBER("2.0".parse().unwrap()), 0)
        );
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_reserved_words() {
        let mut sc = Scanner::new("and".to_owned());
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::AND, 0));
        assert_eq!(sc.next(), None);

        let mut sc = Scanner::new("while".to_owned());
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::WHILE, 0));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_idents_partial_reserved() {
        let mut sc = Scanner::new("andd".to_owned());
        assert_eq!(
            sc.next().unwrap(),
            Token::new(LexemeKind::IDENTIFIER("andd".to_string()), 0)
        );
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_newlines() {
        let source = "
and while

andd
";
        let mut sc = Scanner::new(source.to_owned());
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 1));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::AND, 1));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 1));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::WHILE, 1));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 2));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 3));
        assert_eq!(
            sc.next().unwrap(),
            Token::new(LexemeKind::IDENTIFIER("andd".to_string()), 3)
        );
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 4));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_unexpected_character() {
        let source = "/·";
        let mut sc = Scanner::new(source.to_owned());
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Slash, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::UNEXPECTED("·".to_string()), 0));
        assert_eq!(sc.next(), None);
    }

    #[test]
    fn it_handles_keywords() {
        let source = "print(\"foo\")";
        let mut sc = Scanner::new(source.to_owned());
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::PRINT, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::LeftParen, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::STRING("foo".to_string()), 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::RightParen, 0));
        assert_eq!(sc.next(), None);

        let source = "print(1)";
        let mut sc = Scanner::new(source.to_owned());
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::PRINT, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::LeftParen, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::NUMBER(1.0), 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::RightParen, 0));
        assert_eq!(sc.next(), None);

        let source = "var foo";
        let mut sc = Scanner::new(source.to_owned());
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::VAR, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::Whitespace, 0));
        assert_eq!(sc.next().unwrap(), Token::new(LexemeKind::IDENTIFIER("foo".to_string()), 0));
        assert_eq!(sc.next(), None);
    }
}
