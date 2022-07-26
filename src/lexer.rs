use std::fmt::Write;
use std::str::Chars;

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    Illegal(String),

    Ident(String),
    String(String),
    Number(String),
    True,
    False,
    Eq,
    NotEq,
    Less,
    LessEq,
    Greater,
    GreaterEq,
    LParenthesis,
    RParenthesis,
    And,
    Or,
    In,
    Not,
    Is,
    Null,
}

pub struct Lexer<'a> {
    input: Chars<'a>,

    idx: usize,
    buf: [Option<char>; 1],
}

impl<'a> Lexer<'a> {
    pub fn new<T: AsRef<str> + ?Sized>(input: &'a T) -> Self {
        Lexer {
            input: input.as_ref().chars(),
            idx: 0,
            buf: [None; 1],
        }
    }

    // reads the next character
    fn read(&mut self) -> Option<char> {
        if self.idx > 0 {
            // we already have a character in the buffer so return it
            self.idx -= 1;
            let ch = self.buf[self.idx];
            self.buf[self.idx] = None;
            return ch;
        }

        // if buf is empty, we should read the next character and put it in buffer to be able unread it
        let ch = self.input.next();
        self.buf[0] = ch;
        ch
    }

    // unread the last character
    fn unread(&mut self) {
        self.idx = 1;
    }

    fn scan_ident(&mut self, ch: char) -> Token {
        let mut data: String = String::from(ch);
        // read possible ident
        while let Some(ch) = self.read() {
            if !ch.is_alphanumeric() && ch != '_' {
                // some vars might have '_' in them
                self.unread();
                break;
            } else {
                write!(data, "{}", ch).unwrap();
            }
        }
        match data.to_uppercase().as_str() {
            "AND" => Token::And,
            "OR" => Token::Or,
            "TRUE" => Token::True,
            "FALSE" => Token::False,
            "IN" => Token::In,
            "NOT" => Token::Not,
            "IS" => Token::Is,
            "NULL" => Token::Null,
            _ => Token::Ident(data),
        }
    }

    fn scan_number(&mut self, ch: char) -> Token {
        let mut data: String = String::from(ch);
        while let Some(ch) = self.read() {
            if !(ch.is_numeric() || self.is_sign(ch) || ch == '.') {
                self.unread();
                break;
            } else {
                write!(data, "{}", ch).unwrap();
            }
        }
        // simple validation if we can parse string
        if data.parse::<i32>().is_err() && data.parse::<f64>().is_err() {
            return Token::Illegal(data);
        }
        Token::Number(data)
    }

    fn scan_string(&mut self, quote: char) -> Token {
        let mut data: String = String::from("");

        let prev = quote;
        while let Some(ch) = self.read() {
            if ch == quote && prev != '\\' {
                return Token::String(data);
            }
            write!(data, "{}", ch).unwrap();
        }
        Token::Illegal(data)
    }

    fn is_sign(&self, ch: char) -> bool {
        ch == '+' || ch == '-'
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(ch) = self.read() {
            if ch.is_ascii_whitespace() {
                continue;
            }

            if ch.is_alphabetic() {
                return Some(self.scan_ident(ch));
            } else if self.is_sign(ch) || ch.is_ascii_digit() {
                return Some(self.scan_number(ch));
            } else if ch == '\'' || ch == '"' {
                return Some(self.scan_string(ch));
            }

            if ch == '(' {
                return Some(Token::LParenthesis);
            } else if ch == ')' {
                return Some(Token::RParenthesis);
            }

            if ch == '=' || ch == '!' || ch == '>' || ch == '<' {
                // read the next character and check if it's one of the two symbol operators
                let next = self.read();
                return if let Some(next) = next {
                    Some(match (ch, next) {
                        ('=', '=') => Token::Illegal(format!("{}{}", ch, next)),
                        ('=', _) => Token::Eq,
                        ('!', '=') => Token::NotEq,
                        ('<', '=') => Token::LessEq,
                        ('<', _) => {
                            self.unread();
                            Token::Less
                        }
                        ('>', '=') => Token::GreaterEq,
                        ('>', _) => {
                            self.unread();
                            Token::Greater
                        }
                        _ => Token::Illegal(format!("{}{}", ch, next)),
                    })
                } else {
                    Some(Token::Illegal(String::from(ch)))
                };
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn peek() {
        let mut lex = Lexer::new("a = 12").into_iter().peekable();
        assert_eq!(lex.peek(), Some(&Token::Ident(String::from("a"))));
        assert_eq!(lex.peek(), Some(&Token::Ident(String::from("a"))));
        assert_eq!(lex.peek(), Some(&Token::Ident(String::from("a"))));

        assert_eq!(lex.next(), Some(Token::Ident(String::from("a"))));
        assert_eq!(lex.next(), Some(Token::Eq));
        assert_eq!(lex.next(), Some(Token::Number(String::from("12"))));
    }

    #[test]
    fn read_unread() {
        let mut lex = Lexer::new("12");
        assert_eq!(lex.read(), Some('1'));
        lex.unread();
        assert_eq!(lex.read(), Some('1'));
        assert_eq!(lex.read(), Some('2'));
        assert_eq!(lex.read(), None);
    }

    #[test]
    fn unread_multiple_times() {
        let mut lex = Lexer::new("1234");
        assert_eq!(lex.read(), Some('1'));
        assert_eq!(lex.read(), Some('2'));
        assert_eq!(lex.read(), Some('3'));
        // We always unread only the last read character
        lex.unread();
        lex.unread();
        lex.unread();
        assert_eq!(lex.read(), Some('3'));
        assert_eq!(lex.read(), Some('4'));
        assert_eq!(lex.read(), None);
    }

    #[test]
    fn unread_empty_string() {
        let mut l = Lexer::new("");
        l.unread();
        // unread more times to make sure that we do not panic
        l.unread();
        l.unread();
        l.unread();
        assert_eq!(l.read(), None);
    }

    #[test]
    fn read_empty_string() {
        let mut l = Lexer::new("");
        assert_eq!(l.read(), None);
    }

    #[test]
    fn ident() {
        let mut lex = Lexer::new("some_var");
        let t = lex.next().unwrap();
        assert_eq!(t, Token::Ident("some_var".to_string()));
    }

    #[test]
    fn number() {
        let mut lex = Lexer::new("1.124");
        let t = lex.next().unwrap();
        assert_eq!(t, Token::Number("1.124".to_string()));

        let mut lex = Lexer::new("-34");
        let t = lex.next().unwrap();
        assert_eq!(t, Token::Number("-34".to_string()));

        let mut lex = Lexer::new("-34.123123.123123");
        let t = lex.next().unwrap();
        assert_eq!(t, Token::Illegal("-34.123123.123123".to_string()));
    }

    #[test]
    fn string() {
        let mut lex = Lexer::new("'hello world!'");
        let t = lex.next().unwrap();
        assert_eq!(t, Token::String("hello world!".to_string()));

        let mut lex = Lexer::new("'hello world!");
        let t = lex.next().unwrap();
        assert_eq!(t, Token::Illegal("hello world!".to_string()));
    }

    macro_rules! tokens_test {
        ($suite:ident, $($name:ident: $input:expr, $output:expr,)*) => {
            mod $suite {
                use super::*;
                $(
                    #[test]
                    fn $name() {
                        let tokens: Vec<Token> = Lexer::new($input).collect();
                        assert_eq!(
                            $output,
                            tokens
                        );
                    }
                )*
            }
        }
    }
    tokens_test!(tests,
        eq: "a = 1", vec![Token::Ident(String::from("a")), Token::Eq, Token::Number(String::from("1"))],
        not_eq: "a != 1", vec![Token::Ident(String::from("a")), Token::NotEq, Token::Number(String::from("1"))],
        gt: "a > 1", vec![Token::Ident(String::from("a")), Token::Greater, Token::Number(String::from("1"))],
        gt_eq: "a >= 1", vec![Token::Ident(String::from("a")), Token::GreaterEq, Token::Number(String::from("1"))],
        lt: "a < 1", vec![Token::Ident(String::from("a")), Token::Less, Token::Number(String::from("1"))],
        lt_eq: "a <= 1", vec![Token::Ident(String::from("a")), Token::LessEq, Token::Number(String::from("1"))],
        bool_true: "a = true", vec![Token::Ident(String::from("a")), Token::Eq, Token::True],
        bool_false: "b != false", vec![Token::Ident(String::from("b")), Token::NotEq, Token::False],
        or: "a <= 1 OR b = 'test'", vec![
            Token::Ident(String::from("a")),
            Token::LessEq,
            Token::Number(String::from("1")),
            Token::Or,
            Token::Ident(String::from("b")),
            Token::Eq,
            Token::String(String::from("test")),
        ],

        compare_string: "a = 'test'", vec![Token::Ident(String::from("a")), Token::Eq, Token::String(String::from("test"))],
        complex: "(a > -3.14 AND b = 'test') OR c != 525 ", vec![
            Token::LParenthesis,
            Token::Ident(String::from("a")),
            Token::Greater,
            Token::Number(String::from("-3.14")),
            Token::And,
            Token::Ident(String::from("b")),
            Token::Eq,
            Token::String(String::from("test")),
            Token::RParenthesis,
            Token::Or,
            Token::Ident(String::from("c")),
            Token::NotEq,
            Token::Number(String::from("525"))
        ],
        in_list: "a IN (1, 2, 3)", vec![
            Token::Ident(String::from("a")),
            Token::In,
            Token::LParenthesis,
            Token::Number(String::from("1")),
            Token::Number(String::from("2")),
            Token::Number(String::from("3")),
            Token::RParenthesis,
        ],
    );

    tokens_test!(validation_test,
        invalid_eq: "a === 1", vec![
            Token::Ident(String::from("a")),
            Token::Illegal(String::from("==")),
            Token::Eq,
            Token::Number(String::from("1"))
        ],
    );
}
