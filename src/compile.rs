use crate::ast::{EDesc, Export, Func, Instr, Module, Type, ValueType};

pub const MAGIC: &[u8] = &[0x00, 0x61, 0x73, 0x6d];
pub const VERSION: &[u8] = &[0x01, 0x00, 0x00, 0x00];

pub fn val_type(vt: &ValueType) -> u8 {
    match vt {
        ValueType::I32 => 0x7f,
        ValueType::I64 => 0x7e,
    }
}
pub mod section {
    pub const TYPE: u8 = 0x01;
    pub const CODE: u8 = 0x0a;
    pub const FUNC: u8 = 0x03;
    pub const EXPORT: u8 = 0x07;
}

pub mod var_instr {
    pub const LOCAL_GET: u8 = 0x20;
}

pub mod num_instr {
    pub const I32_ADD: u8 = 0x6a;
}

pub mod indices {
    pub const FUNC: u8 = 0x00;
}

pub mod control_flow {
    pub const FUNC: u8 = 0x60;
    pub const END: u8 = 0x0b;
}

// https://en.wikipedia.org/wiki/LEB128
pub fn u32_leb128(v: u32) -> Vec<u8> {
    fn encode(i: u32, r: &[u8]) -> Vec<u8> {
        let b = i & 0x7fu32;
        let ii = 1 >> 7;
        if ii == 0 {
            [r, &[b as u8]].concat()
        } else {
            let r = [r, &[(0x80u32 | b) as u8]].concat();
            encode(ii, &r)
        }
    }

    encode(v, &[]).to_vec()
}

fn type_section(ast: &Module) -> Vec<u8> {
    // Encode one type
    fn encode_type(t: &Type) -> Vec<u8> {
        vec![
            vec![control_flow::FUNC],
            vec![t.0.len() as u8],
            t.0.iter().map(val_type).collect::<Vec<u8>>(),
            vec![t.1.len() as u8],
            t.1.iter().map(val_type).collect::<Vec<u8>>(),
        ]
        .concat()
    }

    let body: Vec<u8> = ast.types.iter().flat_map(|t| encode_type(t)).collect();
    vec![
        vec![section::TYPE],
        u32_leb128((body.len() + 1) as u32),
        u32_leb128(ast.types.len() as u32),
        body,
    ]
    .concat()
}

fn func_section(ast: &Module) -> Vec<u8> {
    if ast.funcs.is_empty() {
        vec![]
    } else {
        let body = ast
            .funcs
            .iter()
            .map(|f| f.f_type as u8)
            .collect::<Vec<u8>>();

        vec![
            vec![section::FUNC],
            u32_leb128((body.len() + 1) as u32),
            u32_leb128((ast.funcs.len()) as u32),
            body,
        ]
        .concat()
    }
}

fn export_section(ast: &Module) -> Vec<u8> {
    fn encode(export: &Export) -> Vec<u8> {
        vec![
            u32_leb128(export.name.len() as u32),
            export.name.as_bytes().to_vec(),
            match export.e_desc {
                EDesc::FuncExport(_) => vec![indices::FUNC],
            },
            match export.e_desc {
                EDesc::FuncExport(idx) => vec![idx as u8],
            },
        ]
        .concat()
    }

    if ast.exports.is_empty() {
        vec![]
    } else {
        let body = ast.exports.iter().flat_map(encode).collect::<Vec<u8>>();

        vec![
            vec![section::EXPORT],
            u32_leb128((body.len() + 1) as u32),
            u32_leb128((ast.exports.len()) as u32),
            body,
        ]
        .concat()
    }
}

fn code_section(ast: &Module) -> Vec<u8> {
    fn func(func: &Func) -> Vec<u8> {
        fn instr(instr: &Instr) -> Vec<u8> {
            match instr {
                Instr::LocalGet(idx) => vec![var_instr::LOCAL_GET, (*idx as u8)],
                Instr::I32Add => vec![num_instr::I32_ADD],
            }
        }

        let body = vec![
            vec![func.locals.len() as u8],
            func.body.iter().flat_map(instr).collect(),
            vec![control_flow::END],
        ]
        .concat();

        vec![u32_leb128((body.len()) as u32), body].concat()
    }

    if ast.funcs.is_empty() {
        vec![]
    } else {
        let body = vec![
            vec![ast.funcs.len() as u8],
            ast.funcs.iter().flat_map(func).collect(),
        ]
        .concat();

        vec![vec![section::CODE], u32_leb128(body.len() as u32), body].concat()
    }
}

pub fn compile(ast: &Module) -> Vec<u8> {
    vec![
        MAGIC,
        VERSION,
        &type_section(&ast),
        &func_section(&ast),
        &export_section(&ast),
        &code_section(&ast),
    ]
    .concat()
}
