use crate::error::*;
use crate::lean::Lean;

/// Take in a line with an index number, and checks if it starts with a "--".
fn no_comment(enumerated_line: &(usize, &str)) -> bool {
    !enumerated_line.1.trim_start().starts_with("--")
}

/// If the line contains any of the strings given as `starters`, then it MUST
/// start with that string.
pub fn line_starts_with<'a>(lean: &'a Lean, starters: &[&str]) -> Result<()> {
    for (line_idx, line) in lean.lines().enumerate().filter(no_comment) {
        for s in starters {
            if line.contains(s) && !line.starts_with(s) {
                return Err(Error::Content {
                    filepath: lean.path.to_path_buf(),
                    line_idx,
                    err: LineError::StartsWith(s.to_string()),
                });
            }
        }
    }
    Ok(())
}

/// If the line contains "theorem" or "lemma", then it must start with that,
/// unless it starts with "private" or "protected".
pub fn line_starts_with_theorem_lemma<'a>(lean: &'a Lean) -> Result<()> {
    const IDENTIFIERS: [&str; 2] = ["theorem", "lemma"];
    for (line_idx, mut line) in lean.lines().enumerate().filter(no_comment) {
        for ident in IDENTIFIERS {
            if line.contains(ident) {
                if let Some(v) = line.strip_prefix("private") {
                    line = v.trim_start();
                }
                if let Some(v) = line.strip_prefix("protected") {
                    line = v.trim_start();
                }
                if !line.starts_with(ident) {
                    return Err(Error::Content {
                        filepath: lean.path.to_path_buf(),
                        line_idx,
                        err: LineError::StartsWith(ident.to_string()),
                    });
                }
            }
        }
    }
    Ok(())
}

pub fn space_between_import_libraries<'a>(lean: &'a Lean) {
    let mut last_mathlib = None;

    for (idx, line) in lean
        .lines()
        .enumerate()
        .filter_map(|(i, v)| Some((i, v.strip_prefix("import")?)))
    {
        let line = line.trim_start();
        if line.starts_with("Mathlib") {
            last_mathlib = Some(idx);
            continue;
        }
        let Some(pidx) = last_mathlib else { continue };
        let bad = line.starts_with("Dino") && pidx + 1 == idx;
        assert!(
            !bad,
            "Leave a space between `Mathlib` imports and `Dino` imports."
        );
    }
}
