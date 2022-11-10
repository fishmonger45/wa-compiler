use std::fs;

use parser::module_entire;

mod ast;
mod ctx;
mod parser;

fn main() {
    let wat = fs::read_to_string("add.wat").unwrap();
    let (_, ast) = module_entire(&wat).expect("Ups, something went wrong!");
    println!("{:?}", ast);
}
