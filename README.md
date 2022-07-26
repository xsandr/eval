## Eval [![Rust](https://github.com/xsandr/eval/actions/workflows/rust.yaml/badge.svg)](https://github.com/xsandr/eval/actions/workflows/rust.yaml)

Eval is a library for boolean expression evaluation

```rust
    let expr = Parser::parse("(a IN ('one', 'two') AND b => 13) OR c IS NOT NULL").unwrap();

    let mut ctx = Context::new();
    ctx.insert(String::from("a"), Value::Str("one".to_string()));
    ctx.insert(String::from("b"), Value::Int(2));
    ctx.insert(String::from("c"), Value::Bool(true));

    assert!(expr.eval(&ctx));
```