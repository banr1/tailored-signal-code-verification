/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process

@[expose] public section

set_option autoImplicit false

/-!
# The `libsignal-cli` ELF, built from source

**Trusted: the statement.** `cliElfBytes` is the raw byte sequence of
`.GeneratedLean/cli-elf/libsignal-cli.elf`, read at elaboration time via `file_bytes%`
(`Arm64/Trusted/Process.lean`), which verifies the SHA-256 digest pinned below.

**Where the file comes from.** It is not committed (`.GeneratedLean/` is gitignored).
`scripts/cli-elf-stock --stdbin --build` builds it from source with stock LLVM `ld.lld`
(`-static -no-pie --no-relax --gc-sections`, linker script
`third_party/libsignal/libsignal-session/cli-elf/stock.ld`, load base `0x400000`), with the
`libsignal` revision, `rustc` `1.98.1` (and its `aarch64-unknown-linux-musl` `self-contained/` CRT
objects and `libc.a`), `zig` (for `rdl_shim.S`), `ld.lld` version prefix, `std-main` entry crate,
and `arm64-semantics` commit pinned in
`third_party/libsignal/libsignal-session/cli-elf/stock/inputs_stock_stdbin.lock`, from the same
Rust objects that `rust-obj2lean` reads: the compiled crate objects and trimmed `alloc`/`std`
sysroot members of `libsignal-session/translation.toml` (`cliLinkObjs`, extracted into
`libsignalSessionLib` = `libsignalSessionMultiLib`), and the `libsignal-cli-io` crate object of
`cli/io/translation.toml` (`SignalSessionIoPlacedObj`). In CI, the parallel `cli-elf-build` job
builds the ELF from source, checks its SHA-256 and link metadata against the lock and this module's
pin (`scripts/cli-elf-stock --stdbin --verify-pin --lean-mod
LibsignalBinary/Specifications/SignalSession/CliElf.lean`), checks structural invariants and
separate-path-depth deterministic reproducibility (`scripts/cli-elf-stock --stdbin --verify` and
`--check`), and runs the A-LINK linker-resolution check (`scripts/stock-pin/alink_check.py --lock
third_party/libsignal/libsignal-session/cli-elf/stock/m4_stock.lock`); the `lake build` job then
downloads the verified ELF artifact, re-checks `--verify-pin`, and builds and audits the lake
library `CliElfLib` (which owns this module and lists `.GeneratedLean/cli-elf/libsignal-cli.elf` as
an `input_file`; no default lake root imports this module). These jobs and steps run unconditionally
on every `push` to `main` (and `workflow_dispatch`) and on `pull_request`s touching the ELF's byte
or build inputs, trusted specifications, or the `CliElfLib`-only proof modules
(`scripts/clielf_ci_paths.txt`); a PR that modifies only shared upstream proof modules skips them,
so any breakage it introduces in the `CliElfLib`-only modules surfaces on the first `main` push that
contains it, and the binary-level verification claim refers to a `main` commit SHA whose
`cli-elf-build` and `lake build` jobs ran the CLI ELF steps green.

**What the pin means.** Anyone can rebuild the ELF from source and compare its SHA-256 with the pin.
The pin is the only place where a byte of the ELF is named. Every address the statement uses comes
from the ELF itself (`ElfImage.parse`, `loadState`) or from `libsignalSessionLib` and
`VerifiedLibraries.mallocngLib` under kernel-checked `MultiPlacement`s `mpl` and `mmpl`
(`CliBinaryPq.lean`, stock `ld.lld` link under `stock.ld` at base `0x400000`; name labels:
`CliLabelsFromObjects` (`CliLabels.lean`)).

## Main definitions

* `cliElfBytes`: the raw bytes of the pinned `libsignal-cli` ELF, the subject of every binary-level
  CLI statement (`CliBinaryPq.lean`, `CliBinaryExtProofDefs.lean`).
-/

namespace CryptoVerification.SignalSession

set_option maxRecDepth 4000000 in
/-- Raw bytes of the static ARM64 `libsignal-cli` ELF (`ET_EXEC`, musl), verified against its
pinned digest by `file_bytes%`. -/
noncomputable def cliElfBytes : List (BitVec 8) :=
  file_bytes% "../../../.GeneratedLean/cli-elf/libsignal-cli.elf"
    sha256 "2f20c836342437a882b5882c34eab604e4f23b2b388c2b2a0696eeda51cddc7e"

end CryptoVerification.SignalSession
