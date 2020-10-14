use cc::Build;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    Build::new().file("src/lib.s").compile("asm");
    println!("cargo:rerun-if-changed=src/lib.s");
    Ok(())
}
