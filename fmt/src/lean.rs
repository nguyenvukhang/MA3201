use crate::{Result, fs};

use core::fmt;
use std::io;
use std::io::Read;
use std::path::{Path, PathBuf};

#[derive(PartialEq, Eq)]
pub struct Lean {
    /// The absolute path to the directory containing the root `lakefile.toml`
    /// file.
    lake_root: PathBuf,

    /// The absolute path of the `.lean` file.
    pub path: PathBuf,

    /// The text content of the `.lean` file.
    pub text: Option<String>,
}

impl fmt::Debug for Lean {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Lean({})", self.path.display())
    }
}

impl Lean {
    /// Create a new `Lean` instance from a `Path`. Panics if the `Path` does
    /// not point to a file that has the ".lean" extension.
    pub fn new(
        lake_root: PathBuf,
        path: PathBuf,
        text: Option<String>,
    ) -> Self {
        assert_eq!(
            path.extension().unwrap_or_default(),
            "lean",
            "Filepath `{}` should end with \".lean\"",
            path.display()
        );
        Self { lake_root, path, text }
    }

    /// Fetch contents of the `*.lean` file from the filesystem.
    pub fn fetch_contents(&mut self) -> io::Result<()> {
        self.text = Some(String::new());
        let Some(mut text) = self.text.as_mut() else { unreachable!() };
        std::fs::File::open(&self.path)?.read_to_string(&mut text)?;
        Ok(())
    }

    pub fn text_checked(&self) -> &str {
        let Some(text) = self.text.as_ref() else {
            panic!("Lean file's text not read yet.")
        };
        text.as_str()
    }

    pub fn strip_trailing_whitespaces(
        &mut self,
        output_buf: &mut String,
    ) -> io::Result<()> {
        let text = self.text_checked();
        output_buf.clear();
        for line in text.lines() {
            output_buf.push_str(line.trim_end());
            output_buf.push('\n');
        }
        if output_buf.trim() == text.trim() {
            return Ok(());
        }
        self.text = Some(output_buf.to_string());
        std::fs::write(&self.path, &output_buf)
    }

    /// Get the corresponding `import` string of this file. Really, it's just
    /// converting all '/' to '.', and then stripping the ".lean" suffix.
    pub fn import(&self) -> String {
        fs::lean_import(self.path.strip_prefix(&self.lake_root).unwrap())
    }

    pub fn lines<'a>(&'a self) -> core::str::Lines<'a> {
        self.text_checked().lines()
    }

    pub fn theorem_finder(&self, text: &str) {
        let mut switch = false;
        let mut buf = vec![];
        for line in text.lines() {
            let line = match line.strip_prefix("theorem") {
                Some(line) => {
                    switch = true;
                    line.trim_start()
                }
                None => line,
            };
            if switch {
                match line.split_once(":=") {
                    Some((pre, _)) => {
                        buf.push(pre.trim());
                        switch = false;
                        println!("{}", buf.join(" "));
                        buf.clear()
                    }
                    None => buf.push(line.trim()),
                }
                continue;
            }
        }
    }
}

/// Loads all the `*.lean` files along with their contents in an owned buffer.
/// Returns them sorted by filename.
pub fn load_all(lake_root: &Path) -> Result<Vec<Lean>> {
    // Get all files.
    let mut files = vec![];
    fs::walk(lake_root, &mut files)?;

    // Keep only files that are `*.lean`.
    files.retain(|v| v.extension().map_or(false, |v| v == "lean"));
    files.sort();

    // Load the contents.
    files
        .into_iter()
        .map(|path| Ok(Lean::new(lake_root.to_path_buf(), path, None)))
        .collect()
}
