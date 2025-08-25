use std::path::{Path, PathBuf};
use std::{fs, io};

pub struct Fsm {
    cwd: Option<PathBuf>,
    absolute_lake_root: Option<PathBuf>,
}

impl Fsm {
    pub fn new() -> Self {
        Self { cwd: None, absolute_lake_root: None }
    }

    /// Get the current directory of the running program.
    pub fn cwd(&mut self) -> PathBuf {
        if let None = self.cwd {
            self.cwd = std::env::current_dir().ok();
        }
        self.cwd.as_ref().unwrap().to_path_buf()
    }

    /// Get the absolute path to the Lake project root.
    pub fn absolute_lake_root(&mut self) -> PathBuf {
        if let None = self.absolute_lake_root {
            self.absolute_lake_root =
                Some(first_parent_that_contains(&self.cwd(), "lakefile.toml"));
        }
        self.absolute_lake_root.as_ref().unwrap().to_path_buf()
    }
}

/// Gets the the absolute path that contains a particular file.
fn first_parent_that_contains(cwd: &Path, filename: &str) -> PathBuf {
    let mut buf = cwd.join(filename);
    for _ in 0..=9 {
        let Ok(m) = fs::metadata(&buf) else {
            buf.pop();
            buf.set_file_name(filename);
            continue;
        };
        if m.is_file() {
            buf.pop();
            return buf;
        }
    }
    panic!("{filename} not found in parent dirs.");
}

/// Convert a (relative) path to a Lean import string.
pub fn lean_import(path: &Path) -> String {
    let z = path.to_str().unwrap();
    let z = z.strip_suffix(".lean").unwrap_or(z);
    z.replace('/', ".")
}

/// Recursively walks through the contents of a directory. Ignores a
/// fixed set of directories.
pub fn walk(path: &Path, acc: &mut Vec<PathBuf>) -> io::Result<()> {
    for dir_ent in fs::read_dir(path)? {
        let dir_ent = dir_ent?;
        let ft = dir_ent.file_type()?;
        if ft.is_dir() {
            let filepath = dir_ent.path();
            match filepath.file_name().and_then(|v| v.to_str()) {
                Some(".git") | Some("target") | Some(".lake")
                | Some(".github") => (),
                _ => walk(&filepath, acc)?,
            }
        } else if ft.is_file() {
            acc.push(dir_ent.path());
        }
    }
    Ok(())
}
