//! This file is focused on generating the root `Dino.lean` file.

use crate::{Fsm, Lean, Result};

use std::fs::File;
use std::io::Write;

pub fn content_processing(lean_files: &mut Vec<Lean>) -> Result<()> {
    let mut buf = String::new();
    for lean_file in lean_files {
        lean_file.strip_trailing_whitespaces(&mut buf)?;
    }
    Ok(())
}

/// Generate the aggregated `.lean` file for the project.
pub fn generate(
    fsm: &mut Fsm,
    target: &str,
    lean_files: &Vec<Lean>,
) -> Result<()> {
    let lean_files = lean_files
        .into_iter()
        .filter(|v| {
            let import = v.import();
            import.contains('.') && import.starts_with(target)
        })
        .collect::<Vec<_>>();

    let lake_root = fsm.absolute_lake_root();
    let target_file = lake_root.join(&target).with_extension("lean");

    // Handle the case when there are no children `.lean` files.
    if lean_files.is_empty() {
        println!("{target:?}, {lean_files:?}");
        let _ = std::fs::remove_file(&target_file);
        return Ok(());
    }

    let mut f = File::create(&target_file)?;
    for lean in lean_files.iter() {
        writeln!(f, "import {}", lean.import())?;
    }
    Ok(())
}
