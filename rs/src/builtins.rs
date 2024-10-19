use crate::interpreter::Context;
use crate::value::{AsyncCallable, Function, Value};
use anyhow::Result;
use std::convert::TryInto;

#[derive(Clone)]
struct Abs;

#[derive(Clone)]
struct Str;

#[derive(Clone)]
struct Len;

#[derive(Clone)]
struct Min;

#[derive(Clone)]
struct Max;

#[derive(Clone)]
struct Sqrt;

#[derive(Clone)]
struct Ceil;

#[derive(Clone)]
struct Floor;

#[derive(Clone)]
struct Lowercase;

#[derive(Clone)]
struct Uppercase;

#[derive(Clone)]
struct Number;

#[derive(Clone)]
struct Strip;

#[derive(Clone)]
struct Range;

#[derive(Clone)]
struct Rstrip;

#[derive(Clone)]
struct Lstrip;

#[derive(Clone)]
struct Join;

#[derive(Clone)]
struct Split;

pub fn builtins(context: &mut Context<'_>) {
    let functions = [
        ("abs", Box::new(Abs) as Box<dyn AsyncCallable>),
        ("str", Box::new(Str)),
        ("len", Box::new(Len)),
        ("min", Box::new(Min)),
        ("max", Box::new(Max)),
        ("sqrt", Box::new(Sqrt)),
        ("ceil", Box::new(Ceil)),
        ("floor", Box::new(Floor)),
        ("lowercase", Box::new(Lowercase)),
        ("uppercase", Box::new(Uppercase)),
        ("number", Box::new(Number)),
        ("strip", Box::new(Strip)),
        ("range", Box::new(Range)),
        ("rstrip", Box::new(Rstrip)),
        ("lstrip", Box::new(Lstrip)),
        ("join", Box::new(Join)),
        ("split", Box::new(Split)),
    ];
    for (name, f) in functions {
        context.insert(name.to_string(), Value::Function(Function::new(name, f)));
    }
}

// utility functions

fn array_arithmetic<F: Fn(f64, f64) -> f64>(args: &[Value], f: F) -> Result<Value> {
    let mut res = None;
    for arg in args {
        let arg = *arg
            .as_f64()
            .ok_or_else(|| interpreter_error!("invalid arguments to builtin: min"))?;
        if let Some(r) = res {
            res = Some(f(arg, r));
        } else {
            res = Some(arg);
        }
    }
    if let Some(r) = res {
        Ok(Value::Number(r))
    } else {
        Err(interpreter_error!("invalid arguments to builtin: min"))
    }
}

fn unary_arithmetic<F: Fn(f64) -> f64>(args: &[Value], op: F) -> Result<Value> {
    if args.len() != 1 {
        return Err(interpreter_error!("expected one argument"));
    }
    let v = &args[0];

    match v {
        Value::Number(n) => Ok(Value::Number(op(*n))),
        _ => Err(interpreter_error!("invalid arguments to builtin")),
    }
}

fn unary_string<F: Fn(&str) -> String>(args: &[Value], op: F) -> Result<Value> {
    if args.len() != 1 {
        return Err(interpreter_error!("expected one argument"));
    }
    let v = &args[0];

    match v {
        Value::String(s) => Ok(Value::String(op(s.as_ref()))),
        _ => Err(interpreter_error!("invalid arguments to builtin")),
    }
}

// builtin implementations

#[async_trait::async_trait]
impl AsyncCallable for Abs {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        unary_arithmetic(args, f64::abs)
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Str {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        if args.len() != 1 {
            return Err(interpreter_error!("str expects one argument"));
        }
        let v = &args[0];

        match v {
            Value::Null | Value::String(_) | Value::Number(_) | Value::Bool(_) => {
                v.stringify().map(|s| Value::String(s))
            }
            _ => Err(interpreter_error!("invalid arguments to builtin: str")),
        }
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Len {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        if args.len() != 1 {
            return Err(interpreter_error!("len expects one argument"));
        }
        let v = &args[0];

        match v {
            Value::String(s) => Ok(Value::Number(s.chars().count() as f64)),
            Value::Array(a) => Ok(Value::Number(a.len() as f64)),
            _ => Err(interpreter_error!("invalid arguments to builtin: len")),
        }
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Min {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        array_arithmetic(args, |a, b| if a < b { a } else { b })
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Max {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        array_arithmetic(args, |a, b| if a < b { b } else { a })
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Sqrt {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        unary_arithmetic(args, f64::sqrt)
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Ceil {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        unary_arithmetic(args, f64::ceil)
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Floor {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        unary_arithmetic(args, f64::floor)
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Lowercase {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        unary_string(args, str::to_lowercase)
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Uppercase {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        unary_string(args, str::to_uppercase)
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Number {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        if args.len() != 1 {
            return Err(interpreter_error!("number expects one argument"));
        }
        let v = &args[0];
        let num: f64 = match v {
            Value::String(s) => match s.parse() {
                Ok(num) => num,
                Err(_) => return Err(interpreter_error!("string can't be converted to number")),
            },
            _ => return Err(interpreter_error!("invalid arguments to builtin: number")),
        };
        Ok(Value::Number(num))
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Strip {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        unary_string(args, |s| str::trim(s).to_owned())
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Range {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        if args.len() < 2 || args.len() > 3 {
            return Err(interpreter_error!(
                "range requires two arguments and optionally supports a third"
            ));
        }
        let start = &args[0];
        let start: i64 = match start {
            Value::Number(n) if n.fract() == 0.0 => n.round() as i64,
            _ => return Err(interpreter_error!("invalid arguments to builtin: range")),
        };
        let stop = &args[1];
        let stop: i64 = match stop {
            Value::Number(n) if n.fract() == 0.0 => n.round() as i64,
            _ => return Err(interpreter_error!("invalid arguments to builtin: range")),
        };
        let step: i64 = match args.get(2) {
            // If step is not provided by the user, it defaults to 1.
            None => 1,
            Some(val) => match val {
                Value::Number(n) if n.fract() == 0.0 => n.round() as i64,
                _ => return Err(interpreter_error!("invalid arguments to builtin: range")),
            },
        };

        if step > 0 {
            let step: usize = step.try_into()?;
            let range = (start..stop)
                .step_by(step)
                .map(|i| Value::Number(i as f64))
                .collect();
            Ok(Value::Array(range))
        } else if step < 0 {
            let step: usize = (step * -1).try_into()?;
            let range = (stop + 1..=start)
                .rev()
                .step_by(step)
                .map(|i| Value::Number(i as f64))
                .collect();
            Ok(Value::Array(range))
        } else {
            return Err(interpreter_error!(
                "invalid argument `step` to builtin: range"
            ));
        }
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Rstrip {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        unary_string(args, |s| str::trim_end(s).to_owned())
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Lstrip {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        unary_string(args, |s| str::trim_start(s).to_owned())
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Join {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        if args.len() != 2 {
            return Err(interpreter_error!("join expects two arguments"));
        }
        let v = &args[0];
        let sep = &args[1];

        let sep = match sep.stringify() {
            Ok(s) => s,
            Err(_) => return Err(interpreter_error!("invalid separator for split")),
        };

        match v {
            Value::Array(v) => {
                let strings: Result<Vec<String>> =
                    v.into_iter().map(|val| val.stringify()).collect();
                match strings {
                    Ok(s) => Ok(Value::String(s.join(&sep))),
                    Err(_) => Err(interpreter_error!(
                        "BuiltinError: invalid arguments to builtin: join"
                    )),
                }
            }
            _ => Err(interpreter_error!(
                "BuiltinError: invalid arguments to builtin: join"
            )),
        }
    }
}

#[async_trait::async_trait]
impl AsyncCallable for Split {
    async fn call(&self, _: &Context<'_>, args: &[Value]) -> Result<Value> {
        if args.len() != 2 {
            return Err(interpreter_error!("split expects two arguments"));
        }
        let v = &args[0];
        let sep = &args[1];

        let sep = match sep.stringify() {
            Ok(s) => s,
            Err(_) => return Err(interpreter_error!("invalid separator for split")),
        };

        match v {
            Value::String(s) => {
                if s.is_empty() {
                    return Ok(Value::Array(vec![Value::String("".to_string())]));
                };
                let strings = s
                    .split(&sep)
                    .filter(|v| !v.is_empty())
                    .map(|v| Value::String(v.to_string()))
                    .collect();
                Ok(Value::Array(strings))
            }
            _ => Err(interpreter_error!(
                "BuiltinError: invalid arguments to builtin: split"
            )),
        }
    }
}
