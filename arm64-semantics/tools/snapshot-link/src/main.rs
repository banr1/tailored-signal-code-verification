// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! CLI entry point for `snapshot-link` (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` — builds the executable that `proc-snapshot` runs. Nothing
//!   it produces is trusted: the snapshot records whatever the loader actually mapped, and Lean
//!   proofs compare those bytes against the exported image.
//! - **Purpose:** `snapshot-link --config <translation.toml> --out-dir <dir>` extracts the
//!   objects of a `translation.toml` with `rust-obj2lean`, links them with `ld.lld` into a static
//!   non-PIE musl executable whose image part matches the exported `Arm64.Obj.LinkedImage`
//!   loaded at `--base`, checks that embedding (see [`verify`]), and writes `<name>` +
//!   `link.json`. `--config` (with its `--base`, `--expect-code`, `--expect-data`, paired by
//!   position) can be repeated: each `translation.toml` becomes its own image at its own base,
//!   an extern of one image that another image defines as a function branches to that
//!   definition, and every image is checked as for a single link. When `--main-rust <Cargo.toml>`
//!   names an ordinary safe Rust `std` binary crate (`0` or more `--config` images), `snapshot-link`
//!   compiles it under the pinned Rust `1.98.1` `-Zbuild-std=std,panic_abort` profile and links it
//!   with bundled `rust-lld` and musl `self-contained` inputs (`--check-std-toolchain` verifies
//!   those toolchain pins standalone). Passing `--strip-runtime-debug` (off by default so committed
//!   ELF fixtures do not change) stages stripped copies of `zig cc`'s C runtime inputs before
//!   linking so cold-cache `DW_AT_comp_dir` paths do not leak into `.symtab` or `link.json`.
//!   `--stock` instead links the unmodified objects with plain `ld.lld` defaults (see [`stock`];
//!   trimmed `[[sysroot_objects]]` are linked as real objects of their trims, see [`trimmed`])
//!   and writes a relocation-site census of the result (see [`census`]). Under `--stock`, a Rust
//!   `std` binary `--main-rust` is linked against rustc's pinned musl `self-contained` runtime,
//!   and `--stock-native-object` adds hashed native objects (see [`stock_std`]).
//!
//! # Key Types & Functions
//! - [`Cli`]: flags. [`link::run`]: the recipe. [`link::place_bases`]: image placement.
//!   [`link::resolve_externs`]: cross-image extern resolution. [`link::stage_runtime_inputs`]:
//!   runtime debug staging. [`std_profile::StdToolchain`]: pinned `std` toolchain checks.
//!   [`verify::check_images`], [`verify::check_std_elf`]: embedding and static-ELF checks.
//!
//! # When to Read This File
//! - Read this file for the CLI flags.

mod census;
mod link;
mod std_profile;
mod stock;
mod stock_hooks;
#[cfg(test)]
mod stock_hooks_tests;
mod stock_std;
mod stock_std_audit;
#[cfg(test)]
mod stock_std_audit_tests;
#[cfg(test)]
mod stock_std_tests;
#[cfg(test)]
mod tests;
mod trimmed;
#[cfg(test)]
mod trimmed_tests;
mod verify;

use clap::{Parser, ValueEnum};
use std::path::PathBuf;

/// What the extern-stub words of the image hold in the executable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum StubMode {
    /// `b <real function>`: the executable can call the externs (the stub words differ from the
    /// image's zero words; the semantics never fetches a hooked stub).
    Branch,
    /// Zero words, exactly as in the exported image (calls into externs fault), except any
    /// externs explicitly listed in `--branch-stubs`.
    Zero,
    /// Zero words by default, emitting `b <real function>` only for `--branch-stubs`.
    Mixed,
}

#[derive(Parser, Debug)]
#[command(
    name = "snapshot-link",
    about = "Link the objects of one or more translation.toml files into a static AArch64 \
             executable, each image at a pinned base",
    after_help = "Examples:\n  snapshot-link --config Implementation/my_lib/translation.toml --out-dir out --stubs zero\n  \
                  snapshot-link --config Implementation/my_rt/translation.toml --base 0x400000 \\\n    \
                  --config Implementation/my_lib/translation.toml --base 0x480000 --out-dir out"
)]
pub struct Cli {
    /// `translation.toml` whose objects are linked as one image. Repeat to link several
    /// pre-verified images into one executable; an extern of one image that another image
    /// defines branches to that definition. Optional when `--main-rust` is a `std` binary crate.
    #[arg(long)]
    pub config: Vec<PathBuf>,
    /// Repository root (default: current directory).
    #[arg(long, default_value = ".")]
    pub repo_root: PathBuf,
    /// Load address of the image of the `--config` at the same position (page aligned, at
    /// least one page above zero: the ELF and program headers are mapped in the page below the
    /// lowest image). Images without a `--base` are placed automatically: the first at
    /// `0x400000`, a later one at the first page boundary after every earlier image.
    #[arg(long, value_parser = parse_u64)]
    pub base: Vec<u64>,
    /// Contents of the extern-stub words.
    #[arg(long, value_enum, default_value_t = StubMode::Branch)]
    pub stubs: StubMode,
    /// Extern symbol names whose stubs emit `b <sym>` even when `--stubs zero` / `--stubs mixed`.
    #[arg(long, value_delimiter = ',')]
    pub branch_stubs: Vec<String>,
    /// Optional `translation.toml` whose `[[native_objects]]` are compiled via `rust-obj2lean`
    /// and linked after `main.o` and before runtime archives.
    #[arg(long)]
    pub native_objects: Option<PathBuf>,
    /// Extract `VerifiedLibraries/Musl` `.lo` members from the pinned Rust 1.98.1 bundled musl
    /// `self-contained/libc.a` (`SHA-256 = b03473b6...`) and link them before runtime archives.
    #[arg(long, conflicts_with = "native_objects")]
    pub musl_string: bool,
    /// Comma-separated subset of native object / `libc.a` member names to link (defaults to
    /// `memcpy,memset,memmove,memcmp,bcmp` with `--musl-string`, or all declared native objects
    /// with `--native-objects`).
    #[arg(long, value_delimiter = ',')]
    pub native_only: Vec<String>,
    /// Force the page-separated image data layout (read-only data, writable data/bss/extern data,
    /// and GOT on disjoint 4 KiB pages and separate `PT_LOAD` segments) even when an image's
    /// `translation.toml` omits `page_separate_data = true`.
    #[arg(long)]
    pub page_separate_data: bool,
    /// Output directory (gets the executable, `link.json`, and the intermediate files).
    #[arg(long, default_value = "", hide_default_value = true, value_parser = parse_out_dir)]
    pub out_dir: PathBuf,
    /// File name of the executable inside `--out-dir`.
    #[arg(long, default_value = "prog")]
    pub name: String,
    /// C source of `main` (default: `int main(void) { return 0; }`).
    #[arg(long, conflicts_with = "main_rust")]
    pub main_c: Option<PathBuf>,
    /// Cargo `Cargo.toml` building either a Rust `staticlib` driver or a safe Rust `std` binary
    /// crate (`aarch64-unknown-linux-musl`). Both forms also work with `--stock`.
    #[arg(long, conflicts_with = "main_c")]
    pub main_rust: Option<PathBuf>,
    /// Verify the pinned Rust 1.98.1 compiler, `rust-src`, bundled `rust-lld`, and musl
    /// `self-contained` SHA-256 digests, print confirmation, and exit 0.
    #[arg(long)]
    pub check_std_toolchain: bool,
    /// Also require the code of the image of the `--config` at the same position to equal this
    /// file (e.g. the exported `.code.bin`).
    #[arg(long)]
    pub expect_code: Vec<PathBuf>,
    /// Also require the unrelocated data of the image of the `--config` at the same position to
    /// equal this file (e.g. the exported `.data.bin`).
    #[arg(long)]
    pub expect_data: Vec<PathBuf>,
    /// Stage stripped copies of `zig cc`'s C runtime `.o`/`.a` inputs (`llvm-objcopy
    /// --strip-debug`, deterministic archives) before linking so cold-cache `DW_AT_comp_dir`
    /// strings do not leak into `.symtab` or `link.json`. Off by default so existing committed
    /// ELF fixtures do not change.
    #[arg(long)]
    pub strip_runtime_debug: bool,
    /// Stock link: pass the unmodified extracted objects of every `--config`, `main`, and the
    /// musl runtime to `ld.lld` with its default layout (no linker script, relaxation on, no
    /// pinned bases), then write `<name>`, `stock-link.json`, and the relocation-site census
    /// `census.json` (see [`census`]). Only `--config`, `--main-c`/`--main-rust` (staticlib),
    /// `--out-dir`, `--name`, `--stock-lld-arg`, and `--stock-keep-library` apply.
    #[arg(long)]
    pub stock: bool,
    /// Extra argument appended to the `--stock` `ld.lld` command line (repeatable), e.g.
    /// `--stock-lld-arg=--icf=all`. Files it names (`-T<f>`, `-T <f>`, `--script <f>`,
    /// `--opt=<f>`, `<f>`) are hashed into `stock-link.json`; `@<f>`, `-L`, `-l` are rejected.
    #[arg(long, requires = "stock", allow_hyphen_values = true)]
    pub stock_lld_arg: Vec<String>,
    /// With `--stock`: make every global function or object the library objects define a
    /// `--gc-sections` root (`--undefined=<sym>`), so the whole library survives (with its layout
    /// as a contiguous block) while the runtime is still garbage-collected.
    #[arg(long, requires = "stock")]
    pub stock_keep_library: bool,
    /// With `--stock`: a native relocatable AArch64 object (e.g. a `.S` shim assembled to `.o`)
    /// linked as is (repeatable). Each is copied to `work/native/<file name>` and recorded with
    /// its SHA-256 and `"kind": "nativeObject"` in `stock-link.json` `inputs[]`.
    #[arg(long, requires = "stock")]
    pub stock_native_object: Vec<PathBuf>,
    /// With `--stock` and a Rust `std` binary `--main-rust`: take rustc's musl `self-contained`
    /// runtime (`crt1.o`, `crti.o`, `crtbegin.o`, `libc.a`, `libunwind.a`, `crtend.o`,
    /// `crtn.o`) from this directory instead of the pinned sysroot's
    /// `lib/rustlib/aarch64-unknown-linux-musl/lib/self-contained/`. Every file must still have
    /// its pinned SHA-256.
    #[arg(long, requires = "stock")]
    pub stock_self_contained_dir: Option<PathBuf>,
}

fn parse_out_dir(s: &str) -> Result<PathBuf, std::convert::Infallible> {
    Ok(PathBuf::from(s))
}

fn parse_u64(s: &str) -> Result<u64, String> {
    match s.strip_prefix("0x") {
        Some(h) => u64::from_str_radix(h, 16),
        None => s.parse(),
    }
    .map_err(|e| e.to_string())
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    if cli.stock {
        return stock::run(&cli);
    }
    link::run(cli)
}
