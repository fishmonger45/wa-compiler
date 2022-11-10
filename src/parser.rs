use std::cell::RefCell;
use std::ops::RangeFrom;
use std::rc::Rc;

use nom::branch::alt;
use nom::combinator::{map, map_res, opt, recognize, value};
use nom::error::{context, ParseError};
use nom::multi::{many0, many1};
use nom::sequence::{pair, preceded, tuple};
use nom::{
    bytes::complete::*, character::complete::*, sequence::delimited, AsChar, IResult,
    InputTakeAtPosition, Parser,
};
use nom::{InputIter, Slice};

use crate::ast::{EDesc, Export, Func, FuncType, Index, Instr, Module, ValueType};
use crate::ctx::Ctx;

pub fn pt<I, O, E: ParseError<I>, G>(inner: G) -> impl FnMut(I) -> IResult<I, O, E>
where
    G: Parser<I, O, E>,
    I: Slice<RangeFrom<usize>> + InputIter,
    <I as InputIter>::Item: AsChar,
{
    delimited(char('('), inner, char(')'))
}

pub fn bws<I, O, E: ParseError<I>, G>(inner: G) -> impl FnMut(I) -> IResult<I, O, E>
where
    G: Parser<I, O, E>,
    I: InputTakeAtPosition,
    <I as InputTakeAtPosition>::Item: AsChar + Clone,
{
    delimited(multispace0, inner, multispace0)
}

pub fn ws(input: &str) -> IResult<&str, &str> {
    context("ws", multispace0)(input)
}

pub fn func(input: &str) -> IResult<&str, &str> {
    context("func", bws(tag("func")))(input)
}

pub fn param(input: &str) -> IResult<&str, &str> {
    context("param", bws(tag("param")))(input)
}

pub fn result(input: &str) -> IResult<&str, &str> {
    context("result", bws(tag("result")))(input)
}

pub fn export(input: &str) -> IResult<&str, &str> {
    context("export", bws(tag("export")))(input)
}

pub fn module(input: &str) -> IResult<&str, &str> {
    context("module", bws(tag("module")))(input)
}

pub fn id(input: &str) -> IResult<&str, &str> {
    let additional_chars = "!#$%&′∗+−./:<=>?@∖^_`|~";
    let id_char = alt((alphanumeric1, is_a(additional_chars)));
    let id = recognize(pair(tag("$"), many1(id_char)));
    bws(id)(input)
}

pub fn u32(input: &str) -> IResult<&str, u32> {
    map_res(digit1, |d: &str| d.parse())(input)
}
pub fn literal(input: &str) -> IResult<&str, String> {
    map(
        bws(delimited(char('"'), is_not("\""), char('"'))),
        |s: &str| s.to_string(),
    )(input)
}

pub fn index(input: &str) -> IResult<&str, Index> {
    let idx = map(u32, |u| Index::Idx(u as usize));
    let id = map(id, |id| Index::Id(id.to_string()));
    alt((idx, id))(input)
}

pub fn value_type(input: &str) -> IResult<&str, ValueType> {
    let types = alt((
        value(ValueType::I32, tag("i32")),
        value(ValueType::I64, tag("i64")),
    ));
    bws(types)(input)
}

// Takes a given string and context and returns a FuncType.
pub fn func_type<'a>(input: &'a str, ctx: &mut Rc<RefCell<Ctx>>) -> IResult<&'a str, FuncType> {
    // Declare a helper enum, as we need to parse
    // either a Return value "R" or a parameter "P".
    // The parameter has an optional idenfifier, like "$lhs" or "$rhs"
    // in our example.
    #[derive(Clone)]
    enum PR {
        R(ValueType),                 // Return type
        P(ValueType, Option<String>), // Paremeter type
    }
    // Parse a parameter with an optional identifier
    let p = map(preceded(ws, pt(tuple((param, opt(id), value_type)))), |p| {
        PR::P(p.2, p.1.and_then(|id| Some(id.to_string())))
    });
    // Parse a result type
    let r = map(preceded(ws, pt(preceded(result, value_type))), PR::R);
    // Parse a type "t" that is either a parameter "p" or a result type "r".
    let t = alt((p, r));
    // Parse multiple types "t"
    let (input, many_t) = many0(t)(input)?;
    // Get all result types from the list
    // of parsed types.
    let results = many_t
        .iter()
        .filter_map(|t| match t {
            PR::R(r) => Some(*r),
            PR::P(_, _) => None,
        })
        .collect::<Vec<ValueType>>();
    // get all parameter types from the list
    // of parsed types.
    let params = many_t
        .iter()
        .filter_map(|t| match t {
            PR::R(_) => None,
            PR::P(p, id) => {
                ctx.borrow_mut().insert_local_id(id); // Insert the id into the context
                Some(*p)
            }
        })
        .collect::<Vec<ValueType>>();
    // Combine the list of parameters and result types to
    // the FuncType tuple and return the result.
    let ft = (params, results);
    Ok((input, ft))
}

pub fn type_use<'a>(input: &'a str, ctx: &mut Rc<RefCell<Ctx>>) -> IResult<&'a str, usize> {
    let mut ft = |i| func_type(i, ctx);
    let (input, ft) = ft(input)?;
    let index = ctx.borrow_mut().upsert_func_type(&ft);
    Ok((input, index))
}

fn local_get<'a>(input: &'a str, ctx: &Rc<RefCell<Ctx>>) -> IResult<&'a str, Instr> {
    let local_get = bws(tag("local.get"));
    let (input, i) = preceded(local_get, index)(input)?;
    let i = ctx.borrow().get_local_idx(&i);
    Ok((input, Instr::LocalGet(i)))
}

fn i32_add(input: &str) -> IResult<&str, Instr> {
    map(bws(tag("i32.add")), |_| Instr::I32Add)(input)
}

pub fn instrs<'a>(input: &'a str, ctx: &mut Rc<RefCell<Ctx>>) -> IResult<&'a str, Vec<Instr>> {
    let lg = |i| local_get(i, ctx);
    let instruction = alt((lg, i32_add));
    many1(bws(instruction))(input)
}

fn func_entire<'a>(input: &'a str, ctx: &mut Rc<RefCell<Ctx>>) -> IResult<&'a str, Func> {
    fn inner<'a>(input: &'a str, ctx: &mut Rc<RefCell<Ctx>>) -> IResult<&'a str, Func> {
        let (input, id) = preceded(func, id)(input)?;
        ctx.borrow_mut().insert_func_id(Some(id.to_string()));
        let (input, f_type) = type_use(input, ctx)?;
        let (input, instrs) = instrs(input, ctx)?;

        let f = Func {
            f_type: f_type as i32,
            locals: vec![],
            body: instrs,
        };

        Ok((input, f))
    }

    let in_pt = |i| inner(i, ctx);
    let (input, func) = pt(in_pt)(input)?;
    ctx.borrow_mut().insert_func(&func);

    Ok((input, func))
}

fn export_entire<'a>(input: &'a str, ctx: &mut Rc<RefCell<Ctx>>) -> IResult<&'a str, Export> {
    let index = pt(preceded(func, index));
    let mut exp = pt(preceded(export, tuple((literal, index))));
    let (input, (lit, idx)) = exp(input)?;
    let export = Export {
        name: lit.clone(),
        e_desc: EDesc::FuncExport(ctx.borrow().get_func_idx(&idx)),
    };

    ctx.borrow_mut().insert_export(&Some(lit), &export);
    Ok((input, export))
}

pub fn module_entire(input: &str) -> IResult<&str, Module> {
    let ctx = Rc::new(RefCell::new(Ctx::new()));
    let func_ctx = |i| func_entire(i, &mut ctx.clone());
    let export_ctx = |i| export_entire(i, &mut ctx.clone());
    let mod_field = bws(many0(bws(alt((
        map(func_ctx, |_| ()),
        map(export_ctx, |_| ()),
    )))));
    let _ = preceded(ws, pt(preceded(module, mod_field)))(input)?;
    let module = Module {
        types: ctx.borrow().types.list.clone(),
        funcs: ctx.borrow().funcs.list.clone(),
        exports: ctx.borrow().exports.list.clone(),
    };
    Ok(("", module))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_ws() {
        assert_eq!(ws("  foo"), Ok(("foo", "  ")));
        assert_eq!(ws("  \t\r\nfoo"), Ok(("foo", "  \t\r\n")));
        assert_eq!(ws("foo"), Ok(("foo", "")));
    }

    #[test]
    fn parse_func() {
        assert_eq!(func("func"), Ok(("", "func")));
        assert_eq!(func("  func  "), Ok(("", "func")));
        assert!(func("anything").is_err());
    }

    #[test]
    fn parse_param() {
        assert_eq!(param("param"), Ok(("", "param")));
        assert_eq!(param("  param  "), Ok(("", "param")));
        assert!(param("anything").is_err());
    }

    #[test]
    fn parse_result() {
        assert_eq!(result("result"), Ok(("", "result")));
        assert_eq!(result("  result  "), Ok(("", "result")));
        assert!(param("anything").is_err());
    }

    #[test]
    fn parse_export() {
        assert_eq!(export("export"), Ok(("", "export")));
        assert_eq!(export("  export  "), Ok(("", "export")));
        assert!(export("anything").is_err());
    }

    #[test]
    fn parse_module() {
        assert_eq!(module("module"), Ok(("", "module")));
        assert_eq!(module("  module  "), Ok(("", "module")));
        assert!(module("anything").is_err());
    }

    #[test]
    fn parse_id() {
        assert_eq!(id("$valid_id%#! foo "), Ok(("foo ", "$valid_id%#!")));
        assert_eq!(id("  $valid_id%#! foo "), Ok(("foo ", "$valid_id%#!")));
        assert!(id("valid_id%#! foo ").is_err());
    }

    #[test]
    fn parse_u32() {
        assert_eq!(u32("12"), Ok(("", 12)));
        assert!(u32("anything").is_err());
    }

    #[test]
    fn parse_literal() {
        assert_eq!(
            literal("\"valid#+123\""),
            Ok(("", "valid#+123".to_string()))
        );
        assert!(literal("invalid").is_err());
    }

    #[test]
    fn parse_index() {
        assert_eq!(index("32"), Ok(("", Index::Idx(32))));
        assert_eq!(
            index("$valid_id%#! foo "),
            Ok(("foo ", Index::Id("$valid_id%#!".to_string())))
        );
    }

    #[test]
    fn parse_value_type() {
        assert_eq!(value_type("i32"), Ok(("", ValueType::I32)));
        assert_eq!(value_type("i64"), Ok(("", ValueType::I64)));
        assert!(value_type("x32").is_err());
    }

    #[test]
    fn parse_func_type_1() {
        let mut ctx = Rc::new(RefCell::new(Ctx::new()));
        assert_eq!(
            func_type("(param $lhs i32)", &mut ctx),
            Ok(("", (vec![ValueType::I32], vec![])))
        )
    }

    #[test]
    fn parse_func_type_2() {
        let mut ctx = Rc::new(RefCell::new(Ctx::new()));
        assert_eq!(
            func_type("(param $lhs i32) (param $rhs i32)", &mut ctx),
            Ok(("", (vec![ValueType::I32, ValueType::I32], vec![])))
        )
    }

    #[test]
    fn parse_func_type_3() {
        let mut ctx = Rc::new(RefCell::new(Ctx::new()));
        assert_eq!(
            func_type("(xparam $lhs i32)", &mut ctx),
            Ok(("(xparam $lhs i32)", (vec![], vec![])))
        )
    }

    #[test]
    fn parse_func_type_4() {
        let mut ctx = Rc::new(RefCell::new(Ctx::new()));
        assert_eq!(
            func_type("param $lhs u32", &mut ctx),
            Ok(("param $lhs u32", (vec![], vec![])))
        )
    }

    #[test]
    fn parse_func_type_5() {
        let mut ctx = Rc::new(RefCell::new(Ctx::new()));
        assert_eq!(
            func_type("param $xlhs u32", &mut ctx),
            Ok(("param $xlhs u32", (vec![], vec![])))
        )
    }

    #[test]
    fn parse_func_type_6() {
        let mut ctx = Rc::new(RefCell::new(Ctx::new()));
        assert_eq!(
            func_type("(param $lhs i32)", &mut ctx),
            Ok(("", (vec![ValueType::I32], vec![])))
        );
    }
    #[test]
    fn parse_func_type_7() {
        let mut ctx = Rc::new(RefCell::new(Ctx::new()));
        assert_eq!(
            func_type("(param $lhs i32) (param $rhs i32) (result i64)", &mut ctx),
            Ok((
                "",
                (vec![ValueType::I32, ValueType::I32], vec![ValueType::I64])
            ))
        );
    }

    #[test]
    fn parse_func_type_8() {
        let mut ctx = Rc::new(RefCell::new(Ctx::new()));
        assert_eq!(
            func_type("(param i32) (param i32) (result i64)", &mut ctx),
            Ok((
                "",
                (vec![ValueType::I32, ValueType::I32], vec![ValueType::I64])
            ))
        );
    }

    #[test]
    fn parse_local_get() {
        let ctx = Rc::new(RefCell::new(Ctx {
            locals: vec![Some("$lhs".to_string())],
            ..Ctx::new()
        }));
        assert_eq!(local_get("local.get 1", &ctx), Ok(("", Instr::LocalGet(1))));
        assert_eq!(
            local_get("local.get $lhs", &ctx),
            Ok(("", Instr::LocalGet(0)))
        );
    }

    #[test]
    fn parse_i32_add() {
        assert_eq!(i32_add(" i32.add "), Ok(("", Instr::I32Add)));
        assert!(i32_add("local.get").is_err());
    }

    #[test]
    fn parse_instrs() {
        let mut ctx = Rc::new(RefCell::new(Ctx::new()));
        assert_eq!(
            instrs(
                "local.get 1\
                i32.add\
                local.get 2",
                &mut ctx
            ),
            Ok((
                "",
                vec![Instr::LocalGet(1), Instr::I32Add, Instr::LocalGet(2)]
            ))
        );
    }
}
