mod cli;
mod colors;
mod error;
mod fmt;
mod fs;
mod generate;
mod lean;

use error::*;
use fs::Fsm;
use generate::{content_processing, generate};
use lean::Lean;

use std::process::Command;
use std::time::Instant;

fn _main(mut fsm: Fsm) -> Result<()> {
    use cli::{Subcommand as S, *};

    match cli::parse().subcommand {
        S::Generate(Generate { targets }) => {
            let _t = Instant::now();
            let lake_root = fsm.absolute_lake_root();
            let mut lean_files = lean::load_all(&lake_root)?;

            for lf in &mut lean_files {
                lf.fetch_contents()?;
            }

            content_processing(&mut lean_files)?;
            for target in targets {
                generate(&mut fsm, target.as_str(), &lean_files)?;
            }
            println!("Generate time: \x1b[32m{:?}\x1b[m", _t.elapsed());
        }
        S::CheckFormat(CheckFormat {}) => {
            let lake_root = fsm.absolute_lake_root();
            for mut lean in lean::load_all(&lake_root)? {
                lean.fetch_contents()?;
                fmt::space_between_import_libraries(&lean);
                fmt::line_starts_with(
                    &lean,
                    &["import", "universe", "variable", "namespace"],
                )?;
                fmt::line_starts_with_theorem_lemma(&lean)?;
            }
        }
        S::Build(Build { include_cwd, filter }) => {
            let _t = Instant::now();
            let lake_root = fsm.absolute_lake_root();
            let mut lean_files = lean::load_all(&lake_root)?;

            let cwd = fsm.cwd();
            let cwd = cwd.as_os_str();
            if !include_cwd {
                lean_files
                    .retain(|v| v.path.parent().map_or(false, |v| v != cwd));
            }

            if let Some(filter) = filter {
                lean_files.retain(|v| {
                    v.path.to_str().map_or(false, |v| v.contains(&filter))
                });
            }

            let mut cmd = Command::new("lake");
            cmd.args(["build", "--log-level=warning"]);
            for lf in lean_files {
                cmd.arg(lf.path);
            }

            cmd.spawn()?.wait()?;
        }
    }
    Ok(())
}

fn main() {
    let fsm = Fsm::new();
    if let Err(err) = _main(fsm) {
        println!("{err}");
    }
}
