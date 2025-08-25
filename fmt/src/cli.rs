use argh::FromArgs;

#[derive(FromArgs, Debug)]
/// Generate the root `*.lean` file.
#[argh(subcommand, name = "generate")]
pub struct Generate {
    #[argh(positional)]
    /// the Lake targets to generate `.lean` files for.
    pub targets: Vec<String>,
}

#[derive(FromArgs, Debug)]
/// Check the formatting of `*.lean` files.
#[argh(subcommand, name = "check-fmt")]
pub struct CheckFormat {}

#[derive(FromArgs, Debug)]
/// Build all *.lean files below the current directory.
#[argh(subcommand, name = "build")]
pub struct Build {
    /// whether or not in include the *.lean files in the current directory.
    #[argh(switch)]
    pub include_cwd: bool,

    /// a simple matcher to filter *.lean files.
    #[argh(positional)]
    pub filter: Option<String>,
}

#[derive(FromArgs, Debug)]
#[argh(subcommand)]
pub enum Subcommand {
    Generate(Generate),
    CheckFormat(CheckFormat),
    Build(Build),
}

#[derive(FromArgs, Debug)]
/// Top-level CLI.
pub struct Cli {
    #[argh(subcommand)]
    pub subcommand: Subcommand,
}

pub fn parse() -> Cli {
    argh::from_env()
}
