use std::{
    fs::{self, File},
    io::Write,
};

use parser::module_entire;

mod ast;
mod compile;
mod ctx;
mod parser;

fn main() {
    let wat = fs::read_to_string("add.wat").unwrap();
    let (_, ast) = module_entire(&wat).expect("Couldn't parse wat");
    println!("{:#?}", ast);
    let bytes = compile::compile(&ast);
    let mut fh = File::create("add.wasm").expect("Failed to create wasm");
    fh.write_all(&bytes).expect("Failed to write wasm");
}
