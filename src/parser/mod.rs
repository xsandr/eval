use crate::lexer::{Lexer, Token};

use std::collections::HashMap;
use std::iter::Peekable;

pub trait Eval {
    fn eval(&self, ctx: &Context) -> bool;
}

enum Cmp {
    Eq,
    NotEq,
    Lt,
    Lte,
    Gt,
    Gte,
}

impl TryFrom<Token> for Cmp {
    type Error = String;
    fn try_from(token: Token) -> Result<Self, Self::Error> {
        match token {
            Token::Eq => Ok(Cmp::Eq),
            Token::NotEq => Ok(Cmp::NotEq),
            Token::Less => Ok(Cmp::Lt),
            Token::LessEq => Ok(Cmp::Lte),
            Token::Greater => Ok(Cmp::Gt),
            Token::GreaterEq => Ok(Cmp::Gte),
            _ => {
                return Err(format!(
                    "cannot convert token {:?} into comparison operator",
                    token
                ))
            }
        }
    }
}

/// Value represents variable and their respective types
#[derive(Debug, PartialOrd, PartialEq)] // do I even need Eq/Ord traits here
pub enum Value {
    Str(String),
    Int(i64),
    Bool(bool),
    Float(f64),
}

impl TryFrom<Token> for Value {
    type Error = String;
    fn try_from(token: Token) -> Result<Self, Self::Error> {
        match token {
            Token::True => Ok(Value::Bool(true)),
            Token::False => Ok(Value::Bool(false)),
            Token::String(v) => Ok(Value::Str(v)),
            Token::Number(num) => {
                if let Ok(i) = num.parse::<i64>() {
                    Ok(Value::Int(i))
                } else if let Ok(f) = num.parse::<f64>() {
                    Ok(Value::Float(f))
                } else {
                    Err(format!("cannot parse {:?}", num))
                }
            }
            _ => Err(format!("unexpected token {:?}", token)),
        }
    }
}

/// Context stores variables and their values
pub type Context = HashMap<String, Value>;

pub struct Expression {
    or: Vec<AndConditionSet>,
}

impl Eval for Expression {
    fn eval(&self, ctx: &Context) -> bool {
        if self.or.is_empty() {
            return false;
        }

        for or in &self.or {
            if or.eval(ctx) {
                return true;
            }
        }
        false
    }
}

struct AndConditionSet {
    and: Vec<Condition>,
}

impl Eval for AndConditionSet {
    fn eval(&self, ctx: &Context) -> bool {
        for set in &self.and {
            if !set.eval(ctx) {
                return false;
            }
        }
        true
    }
}

enum Condition {
    SubExpr(Expression),
    Cond(Operator),
}

impl Eval for Condition {
    fn eval(&self, ctx: &Context) -> bool {
        match self {
            Condition::SubExpr(sub) => sub.eval(ctx),
            Condition::Cond(op) => op.eval(ctx),
        }
    }
}

enum Operator {
    ValueComparison(Comparison),
    IsNull(IsNull),
    In(InList),
}

impl Eval for Operator {
    fn eval(&self, ctx: &Context) -> bool {
        match self {
            Operator::ValueComparison(comp) => comp.eval(ctx),
            Operator::IsNull(is_null) => is_null.eval(ctx),
            Operator::In(lst) => lst.eval(ctx),
        }
    }
}

struct IsNull {
    not: bool,
    variable: String,
}

impl Eval for IsNull {
    fn eval(&self, ctx: &Context) -> bool {
        !ctx.contains_key(&self.variable) ^ self.not
    }
}

struct IsNullBuilder {
    not: bool,
    variable: Option<String>,
}

impl IsNullBuilder {
    fn new() -> Self {
        Self {
            not: false,
            variable: None,
        }
    }

    fn variable(&mut self, var: String) {
        self.variable = Some(var);
    }
    fn not(&mut self, not: bool) {
        self.not = not;
    }

    fn build(self) -> Result<IsNull, String> {
        Ok(IsNull {
            variable: self
                .variable
                .ok_or_else(|| String::from("variable is not set"))?,
            not: self.not,
        })
    }
}

struct Comparison {
    variable: String,
    value: Value,
    cmp: Cmp,
}

struct ComparisonBuilder {
    variable: Option<String>,
    value: Option<Value>,
    cmp: Option<Cmp>,
}

impl ComparisonBuilder {
    fn new() -> Self {
        Self {
            variable: None,
            value: None,
            cmp: None,
        }
    }

    fn variable(&mut self, var: String) {
        self.variable = Some(var);
    }
    fn value(&mut self, val: Value) {
        self.value = Some(val);
    }
    fn cmp(&mut self, c: Cmp) {
        self.cmp = Some(c);
    }

    fn build(self) -> Result<Comparison, String> {
        Ok(Comparison {
            variable: self
                .variable
                .ok_or_else(|| String::from("variable is not set"))?,
            value: self.value.ok_or_else(|| String::from("value is not set"))?,
            cmp: self.cmp.ok_or_else(|| String::from("cmp is not set"))?,
        })
    }
}

impl Eval for Comparison {
    fn eval(&self, ctx: &Context) -> bool {
        if let Some(val) = ctx.get(&self.variable) {
            return match self.cmp {
                Cmp::Eq => *val == self.value,
                Cmp::NotEq => *val != self.value,
                Cmp::Lt => *val < self.value,
                Cmp::Lte => *val <= self.value,
                Cmp::Gt => *val > self.value,
                Cmp::Gte => *val >= self.value,
            };
        }
        false
    }
}

struct InList {
    variable: String,
    not: bool,
    list: Vec<Value>,
}

impl Eval for InList {
    fn eval(&self, ctx: &Context) -> bool {
        if let Some(val) = ctx.get(&self.variable) {
            self.list.contains(val) ^ self.not
        } else {
            self.not
        }
    }
}

struct InListBuilder {
    variable: Option<String>,
    not: bool,
    list: Vec<Value>,
}

impl InListBuilder {
    fn new() -> Self {
        Self {
            variable: None,
            not: false,
            list: Vec::new(),
        }
    }

    fn variable(&mut self, var: String) {
        self.variable = Some(var);
    }
    fn not(&mut self, not: bool) {
        self.not = not;
    }
    fn value(&mut self, val: Value) -> Result<(), String> {
        if !self.list.is_empty() {
            let first = self.list.get(0).unwrap();
            // is there a better way to check if values have the same type?
            match (first, &val) {
                (Value::Int(_), Value::Int(_)) => (),
                (Value::Str(_), Value::Str(_)) => (),
                (Value::Float(_), Value::Float(_)) => (),
                (Value::Bool(_), Value::Bool(_)) => (),
                _ => {
                    return Err(format!(
                        "trying to use mixed type as a list value: {:?}",
                        val
                    ))
                }
            }
        }
        self.list.push(val);
        Ok(())
    }

    fn build(self) -> Result<InList, String> {
        Ok(InList {
            variable: self
                .variable
                .ok_or_else(|| String::from("variable is not set"))?,
            not: self.not,
            list: self.list,
        })
    }
}

pub struct Parser;

impl Parser {
    pub fn parse<T: AsRef<str> + ?Sized>(input: &T) -> Result<Expression, String> {
        let mut lexer = Lexer::new(input);
        let expr = Parser::parse_expression(&mut lexer)?;
        Ok(expr)
    }

    fn parse_expression(lexer: &mut Lexer) -> Result<Expression, String> {
        #[derive(PartialEq)]
        enum ParsingState {
            ExpectingCondition,
            ExpectingSeparator,
        }

        let mut set = AndConditionSet { and: Vec::new() };
        let mut exp = Expression { or: Vec::new() };
        let mut state = ParsingState::ExpectingCondition;

        while let Some(token) = lexer.next() {
            state = match state {
                ParsingState::ExpectingSeparator => {
                    match token {
                        Token::Or => {
                            exp.or.push(set);
                            set = AndConditionSet { and: Vec::new() };
                        }
                        Token::And => (), // intentionally do nothing
                        Token::RParenthesis => {
                            // exit from parsing subexpression
                            break;
                        }
                        _ => {
                            return Err(format!("unexpected token {:?}", token));
                        }
                    }
                    ParsingState::ExpectingCondition
                }
                ParsingState::ExpectingCondition => {
                    match token {
                        Token::Ident(_) => {
                            let cond = Parser::expect_condition(lexer, token)?;
                            set.and.push(cond);
                        }
                        Token::LParenthesis => {
                            let sub = Parser::parse_expression(lexer)?;
                            set.and.push(Condition::SubExpr(sub));
                        }
                        _ => return Err(format!("unexpected token {:?}", token)),
                    };
                    ParsingState::ExpectingSeparator
                }
            };
        }
        if state == ParsingState::ExpectingCondition {
            return Err(String::from("invalid string"));
        }
        if !set.and.is_empty() {
            exp.or.push(set);
        }
        Ok(exp)
    }

    fn expect_condition(lexer: &mut Lexer, token: Token) -> Result<Condition, String> {
        let mut lexer = lexer.into_iter().peekable();
        if let Some(next_token) = lexer.peek() {
            return match next_token {
                Token::In | Token::Not => {
                    let in_list = Self::parse_inlist(&mut lexer, token)?;
                    Ok(Condition::Cond(Operator::In(in_list)))
                }
                Token::Is => {
                    let is_null = Self::parse_isnull(&mut lexer, token)?;
                    Ok(Condition::Cond(Operator::IsNull(is_null)))
                }
                Token::Eq
                | Token::NotEq
                | Token::Greater
                | Token::GreaterEq
                | Token::Less
                | Token::LessEq => {
                    let comp = Self::parse_comparison(&mut lexer, token)?;
                    Ok(Condition::Cond(Operator::ValueComparison(comp)))
                }
                _ => Err(format!("unexpected token {:?}", next_token)),
            };
        }
        Err(String::from("unexpected EOF"))
    }

    fn parse_isnull(lexer: &mut Peekable<&mut Lexer>, token: Token) -> Result<IsNull, String> {
        let mut is_null = IsNullBuilder::new();
        if let Token::Ident(value) = token {
            is_null.variable(value);
        } else {
            return Err(format!("unexpected token: {:?}", token));
        }

        let token = lexer.next().ok_or_else(|| String::from("unexpected EOF"))?;
        if token != Token::Is {
            return Err(format!("expected IS got {:?}", token));
        }

        // Optional Not
        let mut token = lexer.next().ok_or_else(|| String::from("unexpected EOF"))?;
        if token == Token::Not {
            is_null.not(true);
            token = lexer.next().ok_or_else(|| String::from("unexpected EOF"))?;
        }

        if token != Token::Null {
            return Err(format!("unexpected token {:?}", token));
        }
        is_null.build()
    }

    fn parse_inlist(lexer: &mut Peekable<&mut Lexer>, token: Token) -> Result<InList, String> {
        enum State {
            Ident,
            In,
            LParen,
            ListValues,
        }

        let mut in_list = InListBuilder::new();
        let mut state = State::Ident;
        let mut token = token;
        loop {
            match state {
                State::Ident => {
                    if let Token::Ident(value) = token {
                        in_list.variable(value);
                    } else {
                        return Err(format!("unexpected token: {:?}", token));
                    }
                    state = State::In
                }
                State::In => {
                    // IN or NOT IN
                    if token == Token::Not {
                        in_list.not(true);
                        token = lexer.next().ok_or_else(|| String::from("unexpected EOF"))?;
                    }
                    if token != Token::In {
                        return Err(format!("unexpected token {:?}", token));
                    }
                    state = State::LParen
                }
                State::LParen => {
                    if token != Token::LParenthesis {
                        return Err(format!(
                            "expected {:?} got {:?}",
                            Token::LParenthesis,
                            token
                        ));
                    }
                    state = State::ListValues;
                }
                State::ListValues => {
                    if token == Token::RParenthesis {
                        break;
                    }
                    in_list.value(token.try_into()?)?;
                }
            }

            token = lexer.next().ok_or_else(|| String::from("unexpected EOF"))?;
        }
        in_list.build()
    }

    fn parse_comparison(
        lexer: &mut Peekable<&mut Lexer>,
        token: Token,
    ) -> Result<Comparison, String> {
        enum State {
            Ident,
            Operator,
            Value,
        }

        let mut cmp = ComparisonBuilder::new();
        let mut state = State::Ident;
        let mut token = token;
        loop {
            match state {
                State::Ident => {
                    if let Token::Ident(value) = token {
                        cmp.variable(value);
                    } else {
                        return Err(format!("unexpected token: {:?}", token));
                    }
                    state = State::Operator
                }
                State::Operator => {
                    cmp.cmp(token.try_into()?);
                    state = State::Value
                }
                State::Value => {
                    cmp.value(token.try_into()?);
                    break;
                }
            }

            token = lexer.next().ok_or_else(|| String::from("unexpected EOF"))?;
        }
        cmp.build()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_expression() {
        let expr = Parser::parse("a = 1");
        assert!(expr.is_ok())
    }

    #[test]
    fn simple_comparison() {
        let mut ctx = Context::new();
        ctx.insert(String::from("a"), Value::Int(1));

        let comparison = Comparison {
            value: Value::Int(1),
            variable: String::from("a"),
            cmp: Cmp::Eq,
        };

        assert!(comparison.eval(&ctx));
    }

    #[test]
    fn mismatched_type() {
        let comparison = Comparison {
            variable: String::from("a"),
            cmp: Cmp::Eq,
            value: Value::Int(1),
        };

        let mut ctx = Context::new();
        ctx.insert(String::from("a"), Value::Bool(true));

        assert!(!comparison.eval(&ctx));
    }

    #[test]
    fn parse_and_evaluate() {
        let expr = Parser::parse("a >= -15").unwrap();

        let mut ctx = Context::new();
        ctx.insert(String::from("a"), Value::Int(12));

        assert!(expr.eval(&ctx));
    }

    #[test]
    fn or_condition() {
        let expr = Parser::parse("a < 3 OR b = 'hello'").unwrap();

        let mut ctx = Context::new();
        ctx.insert(String::from("a"), Value::Int(4));
        ctx.insert(String::from("b"), Value::Str(String::from("hello")));

        assert!(expr.eval(&ctx));
    }

    #[test]
    fn bool() {
        let expr = Parser::parse("a = true").unwrap();

        let mut ctx = Context::new();
        ctx.insert(String::from("a"), Value::Bool(true));

        assert!(expr.eval(&ctx));
    }

    #[test]
    fn floats() {
        let expr = Parser::parse("a = 1.13").unwrap();

        let mut ctx = Context::new();
        ctx.insert(String::from("a"), Value::Float(1.13));

        assert!(expr.eval(&ctx));
    }

    #[test]
    fn in_list() {
        let expr = Parser::parse("a IN (1, 2, 3)").unwrap();

        let mut ctx = Context::new();
        ctx.insert(String::from("a"), Value::Int(1));

        assert!(expr.eval(&ctx));

        ctx.insert(String::from("a"), Value::Int(-1));
        assert!(!expr.eval(&ctx));
    }

    #[test]
    fn not_in_list() {
        let expr = Parser::parse("a NOT IN ('hello', 'world')").unwrap();

        let mut ctx = Context::new();
        ctx.insert(String::from("a"), Value::Str(String::from("one")));

        assert!(expr.eval(&ctx));

        ctx.insert(String::from("a"), Value::Str(String::from("hello")));
        assert!(!expr.eval(&ctx));
    }

    #[test]
    fn is_null() {
        let expr = Parser::parse("a IS NULL").unwrap();

        let mut ctx = Context::new();

        assert!(expr.eval(&ctx));

        ctx.insert(String::from("a"), Value::Str(String::from("hello")));
        assert!(!expr.eval(&ctx));
    }

    #[test]
    fn is_not_null() {
        let expr = Parser::parse("a IS NOT NULL").unwrap();

        let mut ctx = Context::new();

        assert!(!expr.eval(&ctx));

        ctx.insert(String::from("a"), Value::Str(String::from("hello")));
        assert!(expr.eval(&ctx));
    }

    #[test]
    fn subexpression() {
        let expr = Parser::parse("(a = 1 AND b = 2) OR c = 3").unwrap();

        let mut ctx = Context::new();
        ctx.insert(String::from("a"), Value::Int(1));
        ctx.insert(String::from("b"), Value::Int(2));
        ctx.insert(String::from("c"), Value::Int(4));

        assert!(expr.eval(&ctx));

        let mut ctx = Context::new();
        ctx.insert(String::from("a"), Value::Str(String::from("hello")));
        ctx.insert(String::from("b"), Value::Int(2));
        ctx.insert(String::from("c"), Value::Int(3));
        assert!(expr.eval(&ctx));

        let mut ctx = Context::new();
        ctx.insert(String::from("a"), Value::Str(String::from("hello")));
        ctx.insert(String::from("b"), Value::Int(2));
        ctx.insert(String::from("c"), Value::Int(0));
        assert!(!expr.eval(&ctx));
    }
}
