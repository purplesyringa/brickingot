#![cfg_attr(false, no_std)]

mod arrows;
mod ast;
mod cfg;
mod insn2stmt;
mod instructions;
mod matcher;
mod unstructured;

use crate::cfg::structurize_cfg;
use crate::matcher::rewrite_control_flow;
use crate::unstructured::{convert_code_to_stackless, StatementGenerationError};
use noak::{
    error::DecodeError,
    reader::{attributes::Code, cpool::ConstantPool, Class, Method},
    MStr,
};
use thiserror::Error;

#[derive(Debug, Error)]
enum ClassDecompileError {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error("In method `{name}`: {error}")]
    Method {
        name: String,
        error: MethodDecompileError,
    },
}

#[derive(Debug, Error)]
pub enum MethodDecompileError {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error("While generating initial statements: {0}")]
    StatementGeneration(#[from] StatementGenerationError),

    #[error("`Code` attribute missing")]
    NoCodeAttribute,
}

fn decompile_class_file(raw_bytes: &[u8]) -> Result<(), ClassDecompileError> {
    let class = Class::new(&raw_bytes)?;
    let pool = class.pool();

    // let bootstrap_methods: Vec<BootstrapMethod> = match class
    //     .attributes()
    //     .find_attribute::<BootstrapMethods>(pool)?
    // {
    //     Some(methods) => methods.methods().iter().collect::<Result<_, _>>()?,
    //     None => Vec::new(),
    // };

    // TODO: issue a diagnostic if ACC_SUPER is unset

    for method in class.methods() {
        let method = method?;
        decompile_method(pool, &method).map_err(|error| ClassDecompileError::Method {
            name: pool
                .retrieve(method.name())
                .unwrap_or(MStr::from_mutf8(b"??").unwrap())
                .display()
                .to_string(),
            error,
        })?;
    }

    Ok(())
}

fn decompile_method(
    pool: &ConstantPool<'_>,
    method: &Method<'_>,
) -> Result<(), MethodDecompileError> {
    let code: Code = method
        .attributes()
        .find_attribute(pool)?
        .ok_or_else(|| MethodDecompileError::NoCodeAttribute)?;

    println!("entered {}", pool.retrieve(method.name())?.display());
    let unstructured_program = convert_code_to_stackless(pool, &code)?;
    let mut stmt = structurize_cfg(unstructured_program);
    // rewrite_control_flow(&mut stmt);
    println!("{stmt}\n");

    // method attributes: +Code, Exceptions (§4.7.5), Synthetic (§4.7.8), Signature (§4.7.9), Deprecated (§4.7.15), RuntimeVisibleAnnotations (§4.7.16), RuntimeInvisibleAnnotations (§4.7.17), RuntimeVisibleParameterAnnotations (§4.7.18), RuntimeInvisibleParameterAnnotations (§4.7.19), and AnnotationDefault
    // code attributes: LocalVariableTable (§4.7.13), LocalVariableTypeTable (§4.7.14), and +StackMapTable

    Ok(())
}

fn main() {
    // let raw_bytes = std::fs::read("/home/purplesyringa/mc/public/server-1.21.5/avx.class")
    //     .expect("failed to read class file");
    // let raw_bytes = std::fs::read("/home/purplesyringa/mc/public/server-1.21.5/dao.class")
    //     .expect("failed to read class file");
    // let raw_bytes = std::fs::read("/home/purplesyringa/mc/public/vineflower-1.11.1-slim/org/jetbrains/java/decompiler/modules/decompiler/exps/InvocationExprent.class").expect("failed to read class file");

    let raw_bytes = std::fs::read("Test.class").expect("failed to read class file");

    if let Err(e) = decompile_class_file(&raw_bytes) {
        panic!("class decompilation failed: {e}");
    }
}
