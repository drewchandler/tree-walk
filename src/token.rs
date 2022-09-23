#[derive(Debug, PartialEq, Clone)]
pub enum Lexeme {
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
    Identifier(String),
    String(String),
    Number(f64),

    // Keywords.
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,

    Eof,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub lexeme: Lexeme,
    pub line: u64,
}

impl Token {
    pub fn new(lexeme: Lexeme, line: u64) -> Self {
        Token { lexeme, line }
    }

    pub fn identifier(&self) -> String {
        match self.lexeme {
            Lexeme::Identifier(ref ident) => ident.clone(),
            _ => panic!("Variables should only have Identifier lexeme!"),
        }
    }

    pub fn to_string(&self) -> String {
        match &self.lexeme {
            Lexeme::LeftParen => "(".to_owned(),
            Lexeme::RightParen => ")".to_owned(),
            Lexeme::LeftBrace => "{".to_owned(),
            Lexeme::RightBrace => "}".to_owned(),
            Lexeme::Comma => ".".to_owned(),
            Lexeme::Dot => ".".to_owned(),
            Lexeme::Minus => "-".to_owned(),
            Lexeme::Plus => "+".to_owned(),
            Lexeme::Semicolon => ";".to_owned(),
            Lexeme::Slash => "/".to_owned(),
            Lexeme::Star => "*".to_owned(),
            Lexeme::Bang => "!".to_owned(),
            Lexeme::BangEqual => "!!".to_owned(),
            Lexeme::Equal => "=".to_owned(),
            Lexeme::EqualEqual => "==".to_owned(),
            Lexeme::Greater => ">".to_owned(),
            Lexeme::GreaterEqual => ">=".to_owned(),
            Lexeme::Less => "<".to_owned(),
            Lexeme::LessEqual => "<=".to_owned(),
            Lexeme::Identifier(i) => i.to_owned(),
            Lexeme::String(s) => format!("\"{}\"", s),
            Lexeme::Number(n) => n.to_string(),
            Lexeme::And => "and".to_owned(),
            Lexeme::Class => "class".to_owned(),
            Lexeme::Else => "else".to_owned(),
            Lexeme::False => "false".to_owned(),
            Lexeme::Fun => "fun".to_owned(),
            Lexeme::For => "for".to_owned(),
            Lexeme::If => "if".to_owned(),
            Lexeme::Nil => "nil".to_owned(),
            Lexeme::Or => "or".to_owned(),
            Lexeme::Print => "print".to_owned(),
            Lexeme::Return => "return".to_owned(),
            Lexeme::Super => "super".to_owned(),
            Lexeme::This => "this".to_owned(),
            Lexeme::True => "true".to_owned(),
            Lexeme::Var => "var".to_owned(),
            Lexeme::While => "while".to_owned(),
            Lexeme::Eof => "<EOF>".to_owned(),
        }
    }
}
