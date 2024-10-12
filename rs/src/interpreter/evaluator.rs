#![allow(unused_variables)]
#![allow(dead_code)]
use std::future::IntoFuture;

use super::context::Context;
use super::node::Node;
use crate::value::{Object, Value};
use anyhow::Result;
use async_recursion::async_recursion;
use futures::future::try_join_all;

async fn map_async<'n, R: IntoFuture, F>(
    x: Option<&'n Node<'n>>,
    f: F,
) -> Option<<R as IntoFuture>::Output>
where
    F: Fn(&'n Node) -> R,
{
    if let Some(x) = x {
        Some(f(x).await)
    } else {
        None
    }
}

#[async_recursion]
pub(crate) async fn evaluate<'ctx, 'n>(node: &Node<'n>, context: &Context<'ctx>) -> Result<Value> {
    match *node {
        Node::Number(n) => Ok(Value::Number(n.parse()?)),
        Node::String(s) => Ok(Value::String(s.to_owned())),
        Node::Ident(i) => match context.get(i) {
            Some(v) => Ok(v.clone()),
            None => Err(interpreter_error!("unknown context value {}", i)),
        },
        Node::True => Ok(Value::Bool(true)),
        Node::False => Ok(Value::Bool(false)),
        Node::Null => Ok(Value::Null),
        Node::Array(ref items) => Ok(Value::Array(
            try_join_all(items.iter().map(|i| evaluate(i, context))).await?,
        )),
        Node::Object(ref items) => {
            let mut map = Object::new();
            for (k, v) in items.iter() {
                let v = evaluate(v, context).await?;
                map.insert((*k).to_owned(), v);
            }
            Ok(Value::Object(map))
        }
        Node::Un(ref op, ref v) => un(context, op, v.as_ref()).await,
        Node::Op(ref l, ref o, ref r) => op(context, l.as_ref(), o, r.as_ref()).await,
        Node::Index(ref v, ref i) => index(context, v.as_ref(), i.as_ref()).await,
        Node::Slice(ref v, ref a, ref b) => {
            slice(context, v.as_ref(), a.as_deref(), b.as_deref()).await
        }
        Node::Dot(ref v, ref p) => dot(context, v.as_ref(), p).await,
        Node::Func(ref f, ref args) => func(context, f.as_ref(), &args[..]).await,
    }
}

/// Convert numbers that can be represented as an i64 into an i64.  This is used
/// for indexing and slicing.
fn number_to_i64(v: &Value) -> Option<i64> {
    match v {
        Value::Number(n) => {
            let i = *n as i64;
            if i as f64 == *n {
                Some(i)
            } else {
                None
            }
        }
        _ => None,
    }
}

async fn un<'ctx, 'n>(context: &Context<'ctx>, op: &str, v: &Node<'n>) -> Result<Value> {
    let v = evaluate(v, context).await?;
    match (op, v) {
        ("-", Value::Number(ref n)) => Ok(Value::Number(-*n)),
        ("-", _) => Err(interpreter_error!("This operator expects a number")),

        ("+", v @ Value::Number(_)) => Ok(v),
        ("+", _) => Err(interpreter_error!("This operator expects a number")),

        ("!", v) => Ok(Value::Bool(!bool::from(v))),

        _ => unreachable!(),
    }
}

async fn op<'ctx, 'n>(
    context: &Context<'ctx>,
    l: &Node<'n>,
    o: &str,
    r: &Node<'n>,
) -> Result<Value> {
    let l = evaluate(l, context).await?;

    // perform the short-circuiting operations first
    if o == "||" && bool::from(&l) {
        return Ok(Value::Bool(true));
    } else if o == "&&" && !bool::from(&l) {
        return Ok(Value::Bool(false));
    }

    // now we can unconditionally evaluate the right operand
    let r = evaluate(r, context).await?;

    match (l, o, r) {
        (Value::Number(ref l), "**", Value::Number(ref r)) => Ok(Value::Number(l.powf(*r))),
        (_, "**", _) => Err(interpreter_error!("This operator expects numbers")),

        (Value::Number(ref l), "*", Value::Number(ref r)) => Ok(Value::Number(*l * *r)),
        (_, "*", _) => Err(interpreter_error!("This operator expects numbers")),

        (Value::Number(ref l), "/", Value::Number(ref r)) => {
            let q = *l / *r;
            if !q.is_infinite() {
                Ok(Value::Number(q))
            } else {
                Err(interpreter_error!("division by zero"))
            }
        }
        (_, "/", _) => Err(interpreter_error!("This operator expects numbers")),

        (Value::String(ref l), "+", Value::String(ref r)) => {
            Ok(Value::String(format!("{}{}", l, r)))
        }
        (Value::Number(ref l), "+", Value::Number(ref r)) => Ok(Value::Number(*l + *r)),
        (_, "+", _) => Err(interpreter_error!(
            "This operator expects numbers or strings"
        )),

        (Value::Number(ref l), "-", Value::Number(ref r)) => Ok(Value::Number(*l - *r)),
        (_, "-", _) => Err(interpreter_error!("This operator expects numbers")),

        (Value::String(ref a), "<", Value::String(ref b)) => Ok(Value::Bool(a < b)),
        (Value::Number(a), "<", Value::Number(b)) => Ok(Value::Bool(a < b)),
        (_, "<", _) => Err(interpreter_error!("Expected numbers or strings")),

        (Value::String(ref a), ">", Value::String(ref b)) => Ok(Value::Bool(a > b)),
        (Value::Number(a), ">", Value::Number(b)) => Ok(Value::Bool(a > b)),
        (_, ">", _) => Err(interpreter_error!("Expected numbers or strings")),

        (Value::String(ref a), "<=", Value::String(ref b)) => Ok(Value::Bool(a <= b)),
        (Value::Number(a), "<=", Value::Number(b)) => Ok(Value::Bool(a <= b)),
        (_, "<=", _) => Err(interpreter_error!("Expected numbers or strings")),

        (Value::String(ref a), ">=", Value::String(ref b)) => Ok(Value::Bool(a >= b)),
        (Value::Number(a), ">=", Value::Number(b)) => Ok(Value::Bool(a >= b)),
        (_, ">=", _) => Err(interpreter_error!("Expected numbers or strings")),

        (l, "==", r) => Ok(Value::Bool(l == r)),
        (l, "!=", r) => Ok(Value::Bool(l != r)),

        (Value::String(ref l), "in", Value::String(ref r)) => Ok(Value::Bool(r.find(l).is_some())),
        (ref l, "in", Value::Array(ref r)) => Ok(Value::Bool(r.iter().any(|x| l == x))),
        (Value::String(ref l), "in", Value::Object(ref r)) => Ok(Value::Bool(r.contains_key(l))),
        (_, "in", _) => Err(interpreter_error!("Expected proper args for in")),

        // We have already handled the left operand of the logical operators above, so these
        // consider only the right.
        (_, "&&", r) => Ok(Value::Bool(r.into())),
        (_, "||", r) => Ok(Value::Bool(r.into())),

        (_, _, _) => unreachable!(),
    }
}

async fn index<'ctx, 'n>(context: &Context<'ctx>, v: &Node<'n>, i: &Node<'n>) -> Result<Value> {
    match (evaluate(v, context).await?, evaluate(i, context).await?) {
        (Value::Array(ref a), ref n) => {
            let mut i = number_to_i64(n).ok_or(interpreter_error!(
                "should only use integers to access arrays or strings"
            ))?;
            if i < 0 {
                i = a.len() as i64 + i
            }
            if let Some(v) = a.get(i as usize) {
                Ok(v.clone())
            } else {
                Err(interpreter_error!("index out of bounds"))
            }
        }

        (Value::String(ref s), ref n) => {
            let mut i = number_to_i64(n).ok_or(interpreter_error!(
                "should only use integers to access arrays or strings"
            ))?;
            if i < 0 {
                i = s.chars().count() as i64 + i;
                if i < 0 {
                    i = 0;
                }
            }
            if let Some(c) = s.chars().nth(i as usize) {
                Ok(Value::String(c.into()))
            } else {
                Err(interpreter_error!(
                    "index out of bounds or not on utf8 boundary"
                ))
            }
        }

        (Value::Object(ref o), Value::String(ref s)) => {
            if let Some(v) = o.get(s) {
                Ok(v.clone())
            } else {
                Ok(Value::Null)
            }
        }
        (Value::Object(_), _) => Err(interpreter_error!("object keys must be strings")),
        _ => Err(interpreter_error!(
            "indexing operator expects an object, string, or array"
        )),
    }
}

async fn slice<'ctx, 'n>(
    context: &Context<'ctx>,
    v: &Node<'n>,
    a: Option<&Node<'n>>,
    b: Option<&Node<'n>>,
) -> Result<Value> {
    let mut v = evaluate(v, context).await?;
    let len = match v {
        Value::String(ref s) => s.chars().count(),
        Value::Array(ref v) => v.len(),
        _ => Err(interpreter_error!("can only slice strings and arrays"))?,
    };

    /// Handle wrapping and limiting in accordance with JSON-e rules
    fn wrap(mut x: i64, len: usize) -> usize {
        if x < 0 {
            x = x + len as i64;
        }
        if x < 0 {
            return 0;
        }
        if x > len as i64 {
            return len;
        }
        x as usize
    }

    let a = map_async(a, |x| evaluate(x, context))
        .await
        .transpose()?
        .map(|x| number_to_i64(&x).ok_or(interpreter_error!("slice indices must be integers")))
        .transpose()?
        .map(|x| wrap(x, len))
        .unwrap_or(0);
    let b = map_async(b, |x| evaluate(x, context))
        .await
        .transpose()?
        .map(|x| number_to_i64(&x).ok_or(interpreter_error!("slice indices must be integers")))
        .transpose()?
        .map(|x| wrap(x, len))
        .unwrap_or(len);

    let r = Ok(match v {
        Value::String(ref s) => {
            if a < b {
                // To index characters, we must scan the string from the start.
                let indices = s.char_indices().map(|(i, c)| i);
                let mut indices = indices.skip(a);
                let a_idx = indices.next().unwrap_or_else(|| s.len());
                let mut indices = indices.skip(b - a - 1);
                let b_idx = indices.next().unwrap_or_else(|| s.len());
                Value::String(
                    s.get(a_idx..b_idx)
                        .expect("invalid string slice indices")
                        .into(),
                )
            } else {
                Value::String(String::new())
            }
        }

        Value::Array(ref mut v) => {
            if a < b {
                Value::Array(v.drain(a..b).collect())
            } else {
                Value::Array(Vec::new())
            }
        }

        _ => unreachable!(),
    });
    r
}

async fn dot<'ctx, 'n>(context: &Context<'ctx>, v: &Node<'n>, p: &str) -> Result<Value> {
    match evaluate(v, context).await? {
        Value::Object(ref o) => {
            if let Some(v) = o.get(p) {
                Ok(v.clone())
            } else {
                Err(interpreter_error!("object has no property {}", p))
            }
        }
        _ => Err(interpreter_error!("dot operator expects an object")),
    }
}

async fn func<'ctx, 'n>(context: &Context<'ctx>, f: &Node<'n>, args: &[Node<'n>]) -> Result<Value> {
    let f = evaluate(f, context).await?;
    let args = try_join_all(args.iter().map(|x| evaluate(x, context))).await?;
    match f {
        Value::Function(ref f) => Ok(f.call(&context, &args).await?),
        _ => Err(interpreter_error!(
            "function invocation requires a function"
        )),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[tokio::test]
    async fn test_literals() {
        assert_eq!(
            evaluate(&Node::Null, &Context::new()).await.unwrap(),
            Value::Null
        );
        assert_eq!(
            evaluate(&Node::True, &Context::new()).await.unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            evaluate(&Node::False, &Context::new()).await.unwrap(),
            Value::Bool(false)
        );
    }

    #[tokio::test]
    async fn test_number() {
        assert_eq!(
            evaluate(&Node::Number("13"), &Context::new())
                .await
                .unwrap(),
            Value::Number(13.0),
        );
        assert_eq!(
            evaluate(&Node::Number("13.5"), &Context::new())
                .await
                .unwrap(),
            Value::Number(13.5),
        );
    }

    #[tokio::test]
    async fn test_string() {
        assert_eq!(
            evaluate(&Node::String("abc"), &Context::new())
                .await
                .unwrap(),
            Value::String("abc".into()),
        );
    }

    #[tokio::test]
    async fn test_ident() {
        let mut c = Context::new();
        c.insert("a", Value::Number(29.0));
        assert_eq!(
            evaluate(&Node::Ident("a"), &c).await.unwrap(),
            Value::Number(29.0)
        );
    }

    #[tokio::test]
    async fn test_ident_nosuch() {
        let c = Context::new();
        assert_interpreter_error!(
            evaluate(&Node::Ident("a"), &c).await,
            "unknown context value a"
        );
    }

    #[tokio::test]
    async fn test_unary_minus_i64() {
        let c = Context::new();
        assert_eq!(
            evaluate(&Node::Un("-", Box::new(Node::Number("-10"))), &c)
                .await
                .unwrap(),
            Value::Number(10.0),
        );
    }

    #[tokio::test]
    async fn test_unary_minus_u64() {
        let c = Context::new();
        assert_eq!(
            evaluate(
                // this number is larger that i64::MAX
                &Node::Un("-", Box::new(Node::Number("9223372036854775809"))),
                &c
            )
            .await
            .unwrap(),
            Value::Number("-9223372036854775809".parse().unwrap()),
        );
    }

    #[tokio::test]
    async fn test_unary_minus_f64() {
        let c = Context::new();
        assert_eq!(
            evaluate(
                // this number is larger that i64::MAX
                &Node::Un("-", Box::new(Node::Number("29.25"))),
                &c
            )
            .await
            .unwrap(),
            Value::Number(-29.25),
        );
    }

    #[tokio::test]
    async fn test_unary_minus_not_number() {
        let c = Context::new();
        assert_interpreter_error!(
            evaluate(
                // this number is larger that i64::MAX
                &Node::Un("-", Box::new(Node::String("abc"))),
                &c
            )
            .await,
            "This operator expects a number"
        );
    }

    #[tokio::test]
    async fn test_unary_plus() {
        let c = Context::new();
        assert_eq!(
            evaluate(&Node::Un("+", Box::new(Node::Number("29.25"))), &c)
                .await
                .unwrap(),
            Value::Number(29.25),
        );
    }

    #[tokio::test]
    async fn test_unary_plus_not_number() {
        let c = Context::new();
        assert_interpreter_error!(
            evaluate(&Node::Un("-", Box::new(Node::String("abc"))), &c).await,
            "This operator expects a number"
        );
    }

    #[tokio::test]
    async fn test_unary_bang() {
        let c = Context::new();
        assert_eq!(
            evaluate(&Node::Un("!", Box::new(Node::False)), &c)
                .await
                .unwrap(),
            Value::Bool(true),
        );
    }
}
