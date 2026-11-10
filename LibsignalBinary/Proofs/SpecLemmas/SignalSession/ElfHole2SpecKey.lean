/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import ProofLib.Placed.Fetch
public import ProofLib.Process.FastParse
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection

/-!
# Symbol-Table and Program-Header Keying Guards for `CliElfHole2Assumption`

**Checked by Lean.** Untrusted (`Role::Proof`, `CliElfLib`, `P-KEY` / GK row 926).

Provides closed, zero-hex `rfl_kernel` `SPEC-KEY` guards and universal `ElfImage.parse` /
`LinkedAt` corollaries keying every operational address literal, keep-range bound, appended
branch-stub word, and layout segment index read by `CliElfHole2Assumption`
(`LibsignalBinary/Proofs/SpecLemmas/SignalSession/ElfSlicesPqOomPlacedInst.lean:379`) to
independent by-name `.symtab` lookups (`Obj.lookupUnique`), `PT_LOAD` segment bounds, and raw
ELF64 program-header (`PHDR[2]`) fields over `cliElfBytes` / `cliElfImage`:

1. **Rows A1–A6 (`hole2_targets`, `f3RdlAddrs` / `f3RdlAzAddr`, & `f3StubAddrs` / `f3StubAzAddr`):**
   - **A1:** `(hole2_targets mpl).readFile` keyed to unique `.symtab` `STT_FUNC`
     `"_RNvCs8Lktt10E3TH_17signal_session_io9read_file"` (`hole2_targets_readFile_specKey_guard`,
     `hole2_targets_readFile_specKey`).
   - **A2:** `(hole2_targets mpl).readStdin` keyed to unique `.symtab` `STT_FUNC`
     `"_RNvCs8Lktt10E3TH_17signal_session_io10read_stdin"` (`hole2_targets_readStdin_specKey_guard`,
     `hole2_targets_readStdin_specKey`).
   - **A3:** `f3RdlAddrs.alloc` (`= (hole2_targets mpl).alloc`) keyed to unique `.symtab`
     `STT_FUNC` `"__rdl_alloc"` and `f3StubAddrs.alloc` keyed to
     `"_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"`
     (`f3RdlAddrs_alloc_specKey_guard`, `f3StubAddrs_alloc_rustc_specKey_guard`,
     `f3RdlAddrs_alloc_specKey`).
   - **A4:** `f3RdlAddrs.dealloc` (`= (hole2_targets mpl).dealloc`) keyed to unique `.symtab`
     `STT_FUNC` `"__rdl_dealloc"` and `f3StubAddrs.dealloc` keyed to
     `"_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"`
     (`f3RdlAddrs_dealloc_specKey_guard`, `f3StubAddrs_dealloc_rustc_specKey_guard`,
     `f3RdlAddrs_dealloc_specKey`).
   - **A5:** `f3RdlAddrs.realloc` (`= (hole2_targets mpl).realloc`) keyed to unique `.symtab`
     `STT_FUNC` `"__rdl_realloc"` and `f3StubAddrs.realloc` keyed to
     `"_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"`
     (`f3RdlAddrs_realloc_specKey_guard`, `f3StubAddrs_realloc_rustc_specKey_guard`,
     `f3RdlAddrs_realloc_specKey`).
   - **A6:** `f3RdlAzAddr` (`= (hole2_targets mpl).allocZeroed`) keyed to unique `.symtab`
     `STT_FUNC` `"__rdl_alloc_zeroed"` and `f3StubAzAddr` keyed to
     `"_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed"`
     (`f3RdlAzAddr_specKey_guard`, `f3StubAzAddr_rustc_specKey_guard`, `f3RdlAzAddr_specKey`).
2. **Rows A7–A12 (`hole2_keepSub` & `hole2_keep` executable keep-range bounds):**
   - **A7/A8/A11/A12:** `cliElfImage.segments[2]` (`Perm.rx`, start keyed to `read_stdin`, end
     `start + bytes.length`) guards both endpoints of `hole2_keepSub` and the second interval of
     `hole2_keep` (`hole2_keepSub_lo_specKey_guard`, `hole2_keepSub_hi_specKey_guard`,
     `hole2_keep_r2Lo_specKey_guard`, `hole2_keep_r2Hi_specKey_guard`, `hole2_keepSub_specKey`).
   - **A9:** first interval lower bound of `hole2_keep` keyed to unique `.symtab` `STT_FUNC`
     `"_RNvXs4_NtCs69KKACWg7bl_5alloc6stringNtB5_6StringNtNtCskxtBwYRO61I_4core5clone5Clone5clone"`
     (`= mpl.base 623` for every `LinkedAt` placement; `hole2_keep_r1Lo_specKey_guard`,
     `elfCloneSym_eq_base623_specKey`).
   - **A10:** first interval upper bound of `hole2_keep` keyed to unique `.symtab` `STT_FUNC`
     `"_RNvCs8Lktt10E3TH_17signal_session_io10write_file"` (`= mpl.base 623 + 132`), plus all-zero
     (`0#8`) verification of the trailing page-padding bytes `[p_vaddr + p_memsz, seg1End)` of
     `PHDR[2]` in `cliElfImage.segments[1]` (`hole2_keep_r1Hi_specKey_guard`,
     `elfSeg1_tailZero_specKey_guard`, `hole2_keep_specKey`).
3. **Rows A13–A14 (`hole2_str1Prog` exact block-623 equality & `f3StubAddrs.alloc` `Instr.b` thunk):**
   - Verifies `(hole2_str1Prog mpl).code = (libsignalSessionLib.blockProgram mpl 623).code` (`0`
     appended stub bytes on stock `--no-relax`), and decodes the 32-bit thunk word at
     `f3StubAddrs.alloc` in `cliElfImage.segments[2]` via `Arm64.decode` as `Instr.b` targeting
     `"__rdl_alloc"` (`= f3RdlAddrs.alloc`) (`hole2_str1Prog_appendedLen_guard`,
     `f3StubAddrs_alloc_seg2_isB_specKey_guard`, `hole2_str1Prog_stubs_specKey`).
4. **Table 2 (`f3StdLayout.rxSegIdx`):**
   - Keys `f3StdLayout.rxSegIdx` (`= 2`) as the unique segment in `cliElfImage.segments` starting
     at `read_stdin` (`Perm.rx`) (`f3StdLayout_rxSegIdx_specKey_guard`,
     `f3StdLayout_rxSegIdx_specKey`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfHole2SpecKey

open Arm64 Arm64.Obj Arm64.Obj.Interned Arm64.Process
open ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoVerification.SignalSession (cliElfBytes cliElfImage cliElf_parse libsignalSessionLib)
open LibsignalBinary.Heap.Fine
  (f3NoShimV2Addr f3RdlAddrs f3RdlAzAddr f3StdLayout f3StubAddrs f3StubAzAddr)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars (cliElfSymChars cliElf_symbols_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (f3LsBlockBases f3LsBlocksLen libsignalBlocks_len)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_libsignal_linkedAt_unique f3LsMpl)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_keep hole2_keepSub hole2_str1Prog hole2_targets)

/-! ## Interned `.symtab` Lookup Bridge -/

def zeroMpl : MultiPlacement where
  base := fun _ => 0#64
  ρ := fun _ => 0#64

def symReadFile : String := "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io9read_file"
def symReadFileChars : List Char := ['_', 'R', 'N', 'v', 'C', 's', '9', 'X', 'u', 'l', '1', 'K', 'j', 'r', '0', 'Q', 'F', '_', '1', '6', 'l', 'i', 'b', 's', 'i', 'g', 'n', 'a', 'l', '_', 'c', 'l', 'i', '_', 'i', 'o', '9', 'r', 'e', 'a', 'd', '_', 'f', 'i', 'l', 'e']
private theorem symReadFile_eq : symReadFile = String.ofList symReadFileChars := by rfl_kernel

def symReadStdin : String := "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io10read_stdin"
def symReadStdinChars : List Char := ['_', 'R', 'N', 'v', 'C', 's', '9', 'X', 'u', 'l', '1', 'K', 'j', 'r', '0', 'Q', 'F', '_', '1', '6', 'l', 'i', 'b', 's', 'i', 'g', 'n', 'a', 'l', '_', 'c', 'l', 'i', '_', 'i', 'o', '1', '0', 'r', 'e', 'a', 'd', '_', 's', 't', 'd', 'i', 'n']
private theorem symReadStdin_eq : symReadStdin = String.ofList symReadStdinChars := by rfl_kernel

def symWriteFile : String := "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io10write_file"
def symWriteFileChars : List Char := ['_', 'R', 'N', 'v', 'C', 's', '9', 'X', 'u', 'l', '1', 'K', 'j', 'r', '0', 'Q', 'F', '_', '1', '6', 'l', 'i', 'b', 's', 'i', 'g', 'n', 'a', 'l', '_', 'c', 'l', 'i', '_', 'i', 'o', '1', '0', 'w', 'r', 'i', 't', 'e', '_', 'f', 'i', 'l', 'e']
private theorem symWriteFile_eq : symWriteFile = String.ofList symWriteFileChars := by rfl_kernel

def symRdlAlloc : String := "__rdl_alloc"
def symRdlAllocChars : List Char := ['_', '_', 'r', 'd', 'l', '_', 'a', 'l', 'l', 'o', 'c']
private theorem symRdlAlloc_eq : symRdlAlloc = String.ofList symRdlAllocChars := by rfl_kernel

def symRustcAlloc : String := "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"
def symRustcAllocChars : List Char := ['_', 'R', 'N', 'v', 'C', 's', '1', 'n', 'j', 'K', 'G', '4', 'L', '9', 'a', 'B', '3', '_', '7', '_', '_', '_', 'r', 'u', 's', 't', 'c', '1', '2', '_', '_', '_', 'r', 'u', 's', 't', '_', 'a', 'l', 'l', 'o', 'c']
private theorem symRustcAlloc_eq : symRustcAlloc = String.ofList symRustcAllocChars := by rfl_kernel

def symRdlDealloc : String := "__rdl_dealloc"
def symRdlDeallocChars : List Char := ['_', '_', 'r', 'd', 'l', '_', 'd', 'e', 'a', 'l', 'l', 'o', 'c']
private theorem symRdlDealloc_eq : symRdlDealloc = String.ofList symRdlDeallocChars := by rfl_kernel

def symRustcDealloc : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
def symRustcDeallocChars : List Char := ['_', 'R', 'N', 'v', 'C', 's', '1', 'n', 'j', 'K', 'G', '4', 'L', '9', 'a', 'B', '3', '_', '7', '_', '_', '_', 'r', 'u', 's', 't', 'c', '1', '4', '_', '_', '_', 'r', 'u', 's', 't', '_', 'd', 'e', 'a', 'l', 'l', 'o', 'c']
private theorem symRustcDealloc_eq : symRustcDealloc = String.ofList symRustcDeallocChars := by rfl_kernel

def symRdlRealloc : String := "__rdl_realloc"
def symRdlReallocChars : List Char := ['_', '_', 'r', 'd', 'l', '_', 'r', 'e', 'a', 'l', 'l', 'o', 'c']
private theorem symRdlRealloc_eq : symRdlRealloc = String.ofList symRdlReallocChars := by rfl_kernel

def symRustcRealloc : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"
def symRustcReallocChars : List Char := ['_', 'R', 'N', 'v', 'C', 's', '1', 'n', 'j', 'K', 'G', '4', 'L', '9', 'a', 'B', '3', '_', '7', '_', '_', '_', 'r', 'u', 's', 't', 'c', '1', '4', '_', '_', '_', 'r', 'u', 's', 't', '_', 'r', 'e', 'a', 'l', 'l', 'o', 'c']
private theorem symRustcRealloc_eq : symRustcRealloc = String.ofList symRustcReallocChars := by rfl_kernel

def symRdlAllocZeroed : String := "__rdl_alloc_zeroed"
def symRdlAllocZeroedChars : List Char := ['_', '_', 'r', 'd', 'l', '_', 'a', 'l', 'l', 'o', 'c', '_', 'z', 'e', 'r', 'o', 'e', 'd']
private theorem symRdlAllocZeroed_eq : symRdlAllocZeroed = String.ofList symRdlAllocZeroedChars := by rfl_kernel

def symRustcAllocZeroed : String := "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed"
def symRustcAllocZeroedChars : List Char := ['_', 'R', 'N', 'v', 'C', 's', '1', 'n', 'j', 'K', 'G', '4', 'L', '9', 'a', 'B', '3', '_', '7', '_', '_', '_', 'r', 'u', 's', 't', 'c', '1', '9', '_', '_', '_', 'r', 'u', 's', 't', '_', 'a', 'l', 'l', 'o', 'c', '_', 'z', 'e', 'r', 'o', 'e', 'd']
private theorem symRustcAllocZeroed_eq : symRustcAllocZeroed = String.ofList symRustcAllocZeroedChars := by rfl_kernel

def symStringClone : String := "_RNvXs4_NtCs69KKACWg7bl_5alloc6stringNtB5_6StringNtNtCskxtBwYRO61I_4core5clone5Clone5clone"
def symStringCloneChars : List Char := ['_', 'R', 'N', 'v', 'X', 's', '4', '_', 'N', 't', 'C', 's', '6', '9', 'K', 'K', 'A', 'C', 'W', 'g', '7', 'b', 'l', '_', '5', 'a', 'l', 'l', 'o', 'c', '6', 's', 't', 'r', 'i', 'n', 'g', 'N', 't', 'B', '5', '_', '6', 'S', 't', 'r', 'i', 'n', 'g', 'N', 't', 'N', 't', 'C', 's', 'k', 'x', 't', 'B', 'w', 'Y', 'R', 'O', '6', '1', 'I', '_', '4', 'c', 'o', 'r', 'e', '5', 'c', 'l', 'o', 'n', 'e', '5', 'C', 'l', 'o', 'n', 'e', '5', 'c', 'l', 'o', 'n', 'e']
private theorem symStringClone_eq : symStringClone = String.ofList symStringCloneChars := by rfl_kernel

def symNoAllocShimV2 : String := "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"
def symNoAllocShimV2Chars : List Char := ['_', 'R', 'N', 'v', 'C', 's', '1', 'n', 'j', 'K', 'G', '4', 'L', '9', 'a', 'B', '3', '_', '7', '_', '_', '_', 'r', 'u', 's', 't', 'c', '3', '5', '_', '_', '_', 'r', 'u', 's', 't', '_', 'n', 'o', '_', 'a', 'l', 'l', 'o', 'c', '_', 's', 'h', 'i', 'm', '_', 'i', 's', '_', 'u', 'n', 's', 't', 'a', 'b', 'l', 'e', '_', 'v', '2']
private theorem symNoAllocShimV2_eq : symNoAllocShimV2 = String.ofList symNoAllocShimV2Chars := by rfl_kernel

noncomputable def lookupSymChars (cs : List Char) : Option (BitVec 64) :=
  buildEncSymTable cliElfSymChars fun enc => lookupUniqueEnc (encodeCharKey cs) enc

private theorem lookupUnique_cliElf_of_enc {name : String} {cs : List Char} {addr : BitVec 64}
    (hname : name = String.ofList cs)
    (henc : lookupSymChars cs = some addr)
    {img : ElfImage} (hparse : ElfImage.parse cliElfBytes = .ok img) :
    lookupUnique name img.symbols = some addr := by
  cases cliElf_parse.symm.trans hparse
  rw [lookupUnique_eq_lookupUniqueEnc cliElf_symbols_eq rfl hname]
  unfold lookupSymChars at henc
  rw [← buildEncSymTable_eq cliElfSymChars (fun enc => lookupUniqueEnc (encodeCharKey cs) enc)]
  exact henc

attribute [local irreducible] lookupSymChars

/-! ## Extern Ghost-Hook and Allocator Shim Entry Targets -/

/-- `(hole2_targets _).readFile` equals the unique `.symtab` entry for `signal_session_io::read_file`. -/
theorem hole2_targets_readFile_specKey_guard :
    lookupSymChars symReadFileChars = some (hole2_targets zeroMpl).readFile := by
  rfl_kernel

/-- `ElfImage.parse` corollary keying `(hole2_targets mpl).readFile` via `lookupUnique`. -/
theorem hole2_targets_readFile_specKey (mpl : MultiPlacement) {img : ElfImage}
    (hparse : ElfImage.parse cliElfBytes = .ok img) :
    lookupUnique symReadFile img.symbols = some (hole2_targets mpl).readFile :=
  lookupUnique_cliElf_of_enc symReadFile_eq hole2_targets_readFile_specKey_guard hparse

/-- `(hole2_targets _).readStdin` equals the unique `.symtab` entry for `signal_session_io::read_stdin`. -/
theorem hole2_targets_readStdin_specKey_guard :
    lookupSymChars symReadStdinChars = some (hole2_targets zeroMpl).readStdin := by
  rfl_kernel

/-- `ElfImage.parse` corollary keying `(hole2_targets mpl).readStdin` via `lookupUnique`. -/
theorem hole2_targets_readStdin_specKey (mpl : MultiPlacement) {img : ElfImage}
    (hparse : ElfImage.parse cliElfBytes = .ok img) :
    lookupUnique symReadStdin img.symbols = some (hole2_targets mpl).readStdin :=
  lookupUnique_cliElf_of_enc symReadStdin_eq hole2_targets_readStdin_specKey_guard hparse

theorem f3RdlAddrs_alloc_specKey_guard :
    lookupSymChars symRdlAllocChars = some f3RdlAddrs.alloc := by
  rfl_kernel

/-- **Row A3 (`___rust_alloc` thunk `rfl_kernel` guard):** `f3StubAddrs.alloc` equals the unique
`.symtab` entry `"_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"` in `cliElfImage`. -/
theorem f3StubAddrs_alloc_rustc_specKey_guard :
    lookupSymChars symRustcAllocChars = some f3StubAddrs.alloc := by
  rfl_kernel

/-- Keys `f3RdlAddrs.alloc` (`= (hole2_targets mpl).alloc`) to `"__rdl_alloc"` and `f3StubAddrs.alloc`
to `"_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"` in `.symtab`. -/
theorem f3RdlAddrs_alloc_specKey (mpl : MultiPlacement) {img : ElfImage}
    (hparse : ElfImage.parse cliElfBytes = .ok img) :
    lookupUnique symRdlAlloc img.symbols = some f3RdlAddrs.alloc ∧
    lookupUnique symRustcAlloc img.symbols = some f3StubAddrs.alloc ∧
    (hole2_targets mpl).alloc = f3RdlAddrs.alloc :=
  ⟨lookupUnique_cliElf_of_enc symRdlAlloc_eq f3RdlAddrs_alloc_specKey_guard hparse,
   lookupUnique_cliElf_of_enc symRustcAlloc_eq f3StubAddrs_alloc_rustc_specKey_guard hparse,
   rfl⟩

theorem f3RdlAddrs_dealloc_specKey_guard :
    lookupSymChars symRdlDeallocChars = some f3RdlAddrs.dealloc := by
  rfl_kernel

/-- **Row A4 (`___rust_dealloc` thunk `rfl_kernel` guard):** `f3StubAddrs.dealloc` equals the unique
`.symtab` entry `"_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"` in `cliElfImage`. -/
theorem f3StubAddrs_dealloc_rustc_specKey_guard :
    lookupSymChars symRustcDeallocChars = some f3StubAddrs.dealloc := by
  rfl_kernel

/-- Keys `f3RdlAddrs.dealloc` (`= (hole2_targets mpl).dealloc`) to `"__rdl_dealloc"` and
`f3StubAddrs.dealloc` to `"___rust_dealloc"` in `.symtab`. -/
theorem f3RdlAddrs_dealloc_specKey (mpl : MultiPlacement) {img : ElfImage}
    (hparse : ElfImage.parse cliElfBytes = .ok img) :
    lookupUnique symRdlDealloc img.symbols = some f3RdlAddrs.dealloc ∧
    lookupUnique symRustcDealloc img.symbols = some f3StubAddrs.dealloc ∧
    (hole2_targets mpl).dealloc = f3RdlAddrs.dealloc :=
  ⟨lookupUnique_cliElf_of_enc symRdlDealloc_eq f3RdlAddrs_dealloc_specKey_guard hparse,
   lookupUnique_cliElf_of_enc symRustcDealloc_eq f3StubAddrs_dealloc_rustc_specKey_guard hparse,
   rfl⟩

theorem f3RdlAddrs_realloc_specKey_guard :
    lookupSymChars symRdlReallocChars = some f3RdlAddrs.realloc := by
  rfl_kernel

/-- **Row A5 (`___rust_realloc` thunk `rfl_kernel` guard):** `f3StubAddrs.realloc` equals the unique
`.symtab` entry `"_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"` in `cliElfImage`. -/
theorem f3StubAddrs_realloc_rustc_specKey_guard :
    lookupSymChars symRustcReallocChars = some f3StubAddrs.realloc := by
  rfl_kernel

/-- Keys `f3RdlAddrs.realloc` (`= (hole2_targets mpl).realloc`) to `"__rdl_realloc"` and
`f3StubAddrs.realloc` to `"___rust_realloc"` in `.symtab`. -/
theorem f3RdlAddrs_realloc_specKey (mpl : MultiPlacement) {img : ElfImage}
    (hparse : ElfImage.parse cliElfBytes = .ok img) :
    lookupUnique symRdlRealloc img.symbols = some f3RdlAddrs.realloc ∧
    lookupUnique symRustcRealloc img.symbols = some f3StubAddrs.realloc ∧
    (hole2_targets mpl).realloc = f3RdlAddrs.realloc :=
  ⟨lookupUnique_cliElf_of_enc symRdlRealloc_eq f3RdlAddrs_realloc_specKey_guard hparse,
   lookupUnique_cliElf_of_enc symRustcRealloc_eq f3StubAddrs_realloc_rustc_specKey_guard hparse,
   rfl⟩

theorem f3RdlAzAddr_specKey_guard :
    lookupSymChars symRdlAllocZeroedChars = some f3RdlAzAddr := by
  rfl_kernel

/-- **Row A6 (`___rust_alloc_zeroed` thunk `rfl_kernel` guard):** `f3StubAzAddr` equals the unique
`.symtab` entry `"_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed"` in `cliElfImage`. -/
theorem f3StubAzAddr_rustc_specKey_guard :
    lookupSymChars symRustcAllocZeroedChars = some f3StubAzAddr := by
  rfl_kernel

/-- Keys `f3RdlAzAddr` (`= (hole2_targets mpl).allocZeroed`) to `"__rdl_alloc_zeroed"` and
`f3StubAzAddr` to `"___rust_alloc_zeroed"` in `.symtab`. -/
theorem f3RdlAzAddr_specKey (mpl : MultiPlacement) {img : ElfImage}
    (hparse : ElfImage.parse cliElfBytes = .ok img) :
    lookupUnique symRdlAllocZeroed img.symbols = some f3RdlAzAddr ∧
    lookupUnique symRustcAllocZeroed img.symbols = some f3StubAzAddr ∧
    (hole2_targets mpl).allocZeroed = f3RdlAzAddr :=
  ⟨lookupUnique_cliElf_of_enc symRdlAllocZeroed_eq f3RdlAzAddr_specKey_guard hparse,
   lookupUnique_cliElf_of_enc symRustcAllocZeroed_eq f3StubAzAddr_rustc_specKey_guard hparse,
   rfl⟩

/-! ## `hole2_keepSub` and `hole2_keep` Range Bounds -/

/-- Start virtual address (`BitVec 64`) of `img.segments[2]` (`0#64` if out of range). -/
def elfSeg2Start (img : ElfImage) : BitVec 64 :=
  match img.segments[2]? with
  | some r => r.start
  | none => 0#64

/-- Inclusive lower bound (`Nat`) of `img.segments[2]`. -/
def elfSeg2Lo (img : ElfImage) : Nat :=
  (elfSeg2Start img).toNat

/-- Exclusive upper bound (`Nat`) of `img.segments[2]` computed via `fastLen512`. -/
def elfSeg2Hi (img : ElfImage) : Nat :=
  match img.segments[2]? with
  | some r => r.start.toNat + fastLen512 4096 r.bytes
  | none => 0

noncomputable def elfCloneSymAddr : BitVec 64 :=
  (lookupSymChars symStringCloneChars).getD 0#64

/-- Unique `.symtab` `signal_session_io::write_file` entry (`0#64` if absent). -/
noncomputable def elfWriteFileSymAddr : BitVec 64 :=
  (lookupSymChars symWriteFileChars).getD 0#64

/-- Reads `PHDR[2]` `p_vaddr + p_memsz` from raw ELF64 `elfBytes` (`e_phoff + 2 * 56`) when
`e_phentsize = 56`, `2 < e_phnum`, `p_type = 1` (`PT_LOAD`), and `p_flags = 5` (`PF_R | PF_X`). -/
def elfPhdr2RxEndFast? (elfBytes : List (BitVec 8)) : Option Nat :=
  let hdr := fastTake 64 elfBytes
  let ePhoff := listReadU64LE hdr 32
  let ePhent := listReadU16LE hdr 54
  let ePhnum := listReadU16LE hdr 56
  if ePhent == 56 && 2 < ePhnum then
    let ph2 := fastTake 56 (fastDrop (ePhoff + 2 * 56) elfBytes)
    let pType := listReadU32LE ph2 0
    let pFlags := listReadU32LE ph2 4
    let pVaddr := listReadU64LE ph2 16
    let pMemsz := listReadU64LE ph2 40
    if pType == 1 && pFlags == 5 then
      some (pVaddr + pMemsz)
    else
      none
  else
    none

/-- `List.take`/`List.drop` specification counterpart of `elfPhdr2RxEndFast?`. -/
def elfPhdr2RxEnd? (elfBytes : List (BitVec 8)) : Option Nat :=
  let hdr := elfBytes.take 64
  let ePhoff := listReadU64LE hdr 32
  let ePhent := listReadU16LE hdr 54
  let ePhnum := listReadU16LE hdr 56
  if ePhent == 56 && 2 < ePhnum then
    let ph2 := (elfBytes.drop (ePhoff + 2 * 56)).take 56
    let pType := listReadU32LE ph2 0
    let pFlags := listReadU32LE ph2 4
    let pVaddr := listReadU64LE ph2 16
    let pMemsz := listReadU64LE ph2 40
    if pType == 1 && pFlags == 5 then
      some (pVaddr + pMemsz)
    else
      none
  else
    none

theorem elfPhdr2RxEndFast?_eq (elfBytes : List (BitVec 8)) :
    elfPhdr2RxEndFast? elfBytes = elfPhdr2RxEnd? elfBytes := by
  unfold elfPhdr2RxEndFast? elfPhdr2RxEnd?
  simp only [fastTake_eq_take, fastDrop_eq_drop]

/-- `cliElfImage.segments[2]` has executable `Perm.rx` permissions. -/
theorem elfSeg2Perm_specKey_guard :
    (cliElfImage.segments[2]?).map (·.perm) = some Perm.rx := by
  rfl_kernel

/-- `cliElfImage.segments[2].start` equals the unique `.symtab` `read_stdin` entry. -/
theorem elfSeg2ReadStdinSym_specKey_guard :
    lookupSymChars symReadStdinChars = (cliElfImage.segments[2]?).map (·.start) := by
  rfl_kernel

/-- `hole2_keepSub` transitions from `false` to `true` at `cliElfImage.segments[2].start` (`read_stdin`). -/
theorem hole2_keepSub_lo_specKey_guard :
    (hole2_keepSub (BitVec.ofNat 64 (elfSeg2Lo cliElfImage - 1)),
     hole2_keepSub (elfSeg2Start cliElfImage)) = (false, true) := by
  rfl_kernel

/-- `hole2_keepSub` transitions from `true` to `false` at the end of `cliElfImage.segments[2]`. -/
theorem hole2_keepSub_hi_specKey_guard :
    (hole2_keepSub (BitVec.ofNat 64 (elfSeg2Hi cliElfImage - 1)),
     hole2_keepSub (BitVec.ofNat 64 (elfSeg2Hi cliElfImage))) = (true, false) := by
  rfl_kernel

/-- `img.segments[2]` is a `Perm.rx` segment starting at `read_stdin`, matching the rising and falling
boundaries of `hole2_keepSub`. -/
theorem hole2_keepSub_specKey {img : ElfImage}
    (hparse : ElfImage.parse cliElfBytes = .ok img) :
    ∃ seg2,
      img.segments[2]? = some seg2 ∧
      seg2.perm = Perm.rx ∧
      lookupUnique symReadStdin img.symbols = some seg2.start ∧
      (hole2_keepSub (BitVec.ofNat 64 (seg2.start.toNat - 1)),
       hole2_keepSub seg2.start) = (false, true) ∧
      (hole2_keepSub (BitVec.ofNat 64 (seg2.start.toNat + seg2.bytes.length - 1)),
       hole2_keepSub (BitVec.ofNat 64 (seg2.start.toNat + seg2.bytes.length))) = (true, false) := by
  cases cliElf_parse.symm.trans hparse
  have hperm := elfSeg2Perm_specKey_guard
  have hrds := elfSeg2ReadStdinSym_specKey_guard
  have hlo := hole2_keepSub_lo_specKey_guard
  have hhi := hole2_keepSub_hi_specKey_guard
  unfold elfSeg2Lo elfSeg2Start at hlo
  unfold elfSeg2Hi at hhi
  cases hseg2 : cliElfImage.segments[2]? with
  | none => rw [hseg2] at hperm; nomatch hperm
  | some seg2 =>
    rw [hseg2] at hperm hrds hlo hhi
    dsimp only [Option.map] at hperm hrds
    dsimp only at hlo hhi
    injection hperm with hperm_eq
    rw [fastLen512_eq_length 4096 seg2.bytes] at hhi
    exact ⟨seg2, rfl, hperm_eq,
      lookupUnique_cliElf_of_enc symReadStdin_eq hrds cliElf_parse, hlo, hhi⟩

theorem elfCloneSym_base623_specKey_guard :
    lookupSymChars symStringCloneChars = some (f3LsBlockBases.getD 623 0#64) := by
  rfl_kernel

private theorem blk623_lt_f3LsBlocksLen : Nat.blt 623 f3LsBlocksLen = true := by
  rfl_kernel

private theorem blk623_lt_blocks : 623 < libsignalSessionLib.blocks.length := by
  have hlen : libsignalSessionLib.blocks.length = f3LsBlocksLen := Nat.beq_eq.mp libsignalBlocks_len
  have hlt : 623 < f3LsBlocksLen := Nat.blt_eq.mp blk623_lt_f3LsBlocksLen
  omega

/-- Keys `mpl.base 623` to `<String as Clone>::clone` in `.symtab` for any `LinkedAt` placement. -/
theorem elfCloneSym_eq_base623_specKey {mpl : MultiPlacement} {img : ElfImage}
    (hparse : ElfImage.parse cliElfBytes = .ok img)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    lookupUnique symStringClone img.symbols = some (mpl.base 623) := by
  have hbase : mpl.base 623 = f3LsMpl.base 623 :=
    (f3CliElf_libsignal_linkedAt_unique hLs).1 623 blk623_lt_blocks
  have hf3 : f3LsMpl.base 623 = f3LsBlockBases.getD 623 0#64 := rfl
  rw [hbase, hf3]
  exact lookupUnique_cliElf_of_enc symStringClone_eq elfCloneSym_base623_specKey_guard hparse

/-- First-interval lower bound of `hole2_keep` transitions at `<String as Clone>::clone`. -/
theorem hole2_keep_r1Lo_specKey_guard :
    (hole2_keep (BitVec.ofNat 64 (elfCloneSymAddr.toNat - 1)),
     hole2_keep elfCloneSymAddr) = (false, true) := by
  rfl_kernel

/-- `signal_session_io::write_file` is present as a unique `.symtab` `STT_FUNC` entry. -/
theorem elfWriteFileSym_isSome_specKey_guard :
    (lookupSymChars symWriteFileChars).isSome = true := by
  rfl_kernel

/-- First-interval upper bound of `hole2_keep` transitions at `elfWriteFileSymAddr` (`signal_session_io::write_file`, following block `623`). -/
theorem hole2_keep_r1Hi_specKey_guard :
    (hole2_keep (BitVec.ofNat 64 (elfWriteFileSymAddr.toNat - 1)),
     hole2_keep elfWriteFileSymAddr) = (true, false) := by
  rfl_kernel

theorem elfPhdr2RxEnd_isSome_specKey_guard :
    (elfPhdr2RxEndFast? cliElfBytes).isSome = true := by
  rfl_kernel

/-- `cliElfImage.segments[1]` (`Perm.rx`) contains `PHDR[2]` `p_vaddr + p_memsz`, with all trailing
page-padding bytes equal to `0#8`. -/
theorem elfSeg1_tailZero_specKey_guard :
    (match elfPhdr2RxEndFast? cliElfBytes, cliElfImage.segments[1]? with
     | some textEnd, some seg1 =>
       let seg1Len := fastLen512 4096 seg1.bytes
       seg1.perm == Perm.rx &&
       decide (seg1.start.toNat ≤ textEnd ∧ textEnd < seg1.start.toNat + seg1Len) &&
       (fastDrop (textEnd - seg1.start.toNat) seg1.bytes).all (· == 0#8)
     | _, _ => false) = true := by
  rfl_kernel

theorem hole2_keep_r2Lo_specKey_guard :
    (hole2_keep (BitVec.ofNat 64 (elfSeg2Lo cliElfImage - 1)),
     hole2_keep (elfSeg2Start cliElfImage)) = (false, true) := by
  rfl_kernel

theorem hole2_keep_r2Hi_specKey_guard :
    (hole2_keep (BitVec.ofNat 64 (elfSeg2Hi cliElfImage - 1)),
     hole2_keep (BitVec.ofNat 64 (elfSeg2Hi cliElfImage))) = (true, false) := by
  rfl_kernel

/-- Packages all four endpoint characterizations of `hole2_keep` (`<String as Clone>::clone` and
`write_file` in `.symtab`, plus `img.segments[2]`) and the zero-padding invariant on `img.segments[1]`. -/
theorem hole2_keep_specKey {img : ElfImage}
    (hparse : ElfImage.parse cliElfBytes = .ok img) :
    ∃ cloneAddr writeFileAddr textEnd seg1 seg2,
      lookupUnique symStringClone img.symbols = some cloneAddr ∧
      lookupUnique symWriteFile img.symbols = some writeFileAddr ∧
      elfPhdr2RxEnd? cliElfBytes = some textEnd ∧
      img.segments[1]? = some seg1 ∧
      seg1.perm = Perm.rx ∧
      seg1.start.toNat ≤ textEnd ∧
      textEnd < seg1.start.toNat + seg1.bytes.length ∧
      (∀ b ∈ seg1.bytes.drop (textEnd - seg1.start.toNat), b = 0#8) ∧
      img.segments[2]? = some seg2 ∧
      seg2.perm = Perm.rx ∧
      lookupUnique symReadStdin img.symbols = some seg2.start ∧
      (hole2_keep (BitVec.ofNat 64 (cloneAddr.toNat - 1)),
       hole2_keep cloneAddr) = (false, true) ∧
      (hole2_keep (BitVec.ofNat 64 (writeFileAddr.toNat - 1)),
       hole2_keep writeFileAddr) = (true, false) ∧
      (hole2_keep (BitVec.ofNat 64 (seg2.start.toNat - 1)),
       hole2_keep seg2.start) = (false, true) ∧
      (hole2_keep (BitVec.ofNat 64 (seg2.start.toNat + seg2.bytes.length - 1)),
       hole2_keep (BitVec.ofNat 64 (seg2.start.toNat + seg2.bytes.length))) = (true, false) := by
  cases cliElf_parse.symm.trans hparse
  have hclone_enc := elfCloneSym_base623_specKey_guard
  have hwf_some := elfWriteFileSym_isSome_specKey_guard
  have hr1Lo := hole2_keep_r1Lo_specKey_guard
  have hr1Hi := hole2_keep_r1Hi_specKey_guard
  have hpad := elfSeg1_tailZero_specKey_guard
  have hperm2 := elfSeg2Perm_specKey_guard
  have hrds2 := elfSeg2ReadStdinSym_specKey_guard
  have hr2Lo := hole2_keep_r2Lo_specKey_guard
  have hr2Hi := hole2_keep_r2Hi_specKey_guard
  unfold elfCloneSymAddr at hr1Lo
  rw [hclone_enc] at hr1Lo
  dsimp only [Option.getD] at hr1Lo
  unfold elfWriteFileSymAddr at hr1Hi
  unfold elfSeg2Lo elfSeg2Start at hr2Lo
  unfold elfSeg2Hi at hr2Hi
  cases hwf : lookupSymChars symWriteFileChars with
  | none => rw [hwf] at hwf_some; nomatch hwf_some
  | some writeFileAddr =>
    rw [hwf] at hr1Hi
    dsimp only [Option.getD] at hr1Hi
    cases hph2 : elfPhdr2RxEndFast? cliElfBytes with
    | none => rw [hph2] at hpad; nomatch hpad
    | some textEnd =>
      rw [hph2] at hpad
      cases hseg1 : cliElfImage.segments[1]? with
      | none => rw [hseg1] at hpad; nomatch hpad
      | some seg1 =>
        rw [hseg1] at hpad
        dsimp only at hpad
        rw [fastLen512_eq_length 4096 seg1.bytes,
            fastDrop_eq_drop (textEnd - seg1.start.toNat) seg1.bytes] at hpad
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hpad
        obtain ⟨⟨hseg1_perm, hseg1_lo, hseg1_hi⟩, hseg1_zeros⟩ := hpad
        cases hseg2 : cliElfImage.segments[2]? with
        | none => rw [hseg2] at hperm2; nomatch hperm2
        | some seg2 =>
          rw [hseg2] at hperm2 hrds2 hr2Lo hr2Hi
          dsimp only [Option.map] at hperm2 hrds2
          dsimp only at hr2Lo hr2Hi
          injection hperm2 with hperm2_eq
          rw [fastLen512_eq_length 4096 seg2.bytes] at hr2Hi
          have hph2_tcb : elfPhdr2RxEnd? cliElfBytes = some textEnd := by
            rw [← elfPhdr2RxEndFast?_eq]; exact hph2
          exact ⟨f3LsBlockBases.getD 623 0#64, writeFileAddr, textEnd, seg1, seg2,
            lookupUnique_cliElf_of_enc symStringClone_eq hclone_enc cliElf_parse,
            lookupUnique_cliElf_of_enc symWriteFile_eq hwf cliElf_parse,
            hph2_tcb, rfl, hseg1_perm, hseg1_lo, hseg1_hi, hseg1_zeros,
            rfl, hperm2_eq,
            lookupUnique_cliElf_of_enc symReadStdin_eq hrds2 cliElf_parse,
            hr1Lo, hr1Hi, hr2Lo, hr2Hi⟩

/-! ## `hole2_str1Prog` Exact Block-623 Equality and `f3StubAddrs.alloc` Thunk -/

noncomputable def str1Blk623Len : Nat :=
  fastLen512 4 (libsignalSessionLib.blockProgram zeroMpl 623).code

/-- Trailing bytes of `hole2_str1Prog` past block `623` (`[]` on stock `--no-relax`). -/
noncomputable def str1AppendedBytes : List (BitVec 8) :=
  fastDrop str1Blk623Len (hole2_str1Prog zeroMpl).code

private theorem blockProgram_623_len_eq (mpl : MultiPlacement) :
    (libsignalSessionLib.blockProgram mpl 623).code.length = str1Blk623Len := by
  unfold str1Blk623Len
  rw [fastLen512_eq_length 4 (libsignalSessionLib.blockProgram zeroMpl 623).code]
  change ((libsignalSessionLib.blockLib 623).text.patched
      (libsignalSessionLib.blockPlacement mpl 623)).length =
    ((libsignalSessionLib.blockLib 623).text.patched
      (libsignalSessionLib.blockPlacement zeroMpl 623)).length
  rw [CodeBlock.length_patched, CodeBlock.length_patched]

/-- `hole2_str1Prog` appends `0` stub bytes on stock `--no-relax`. -/
theorem hole2_str1Prog_appendedLen_guard :
    fastLen512 1 str1AppendedBytes = 0 := by
  rfl_kernel

/-- `f3NoShimV2Addr` equals unique `.symtab`
`"_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"`. -/
theorem f3NoShimV2Addr_specKey_guard :
    lookupSymChars symNoAllocShimV2Chars = some f3NoShimV2Addr := by
  rfl_kernel

/-- **Row A14 `segments[2]` thunk decode (`rfl_kernel` guard):** `f3StubAddrs.alloc` sits inside
`cliElfImage.segments[2]` (`Perm.rx`), and the 32-bit word there decodes via `Arm64.decode` as an
unconditional `Instr.b` targeting `f3RdlAddrs.alloc` (`= "__rdl_alloc"`). -/
theorem f3StubAddrs_alloc_seg2_isB_specKey_guard :
    (match cliElfImage.segments[2]? with
     | some seg2 =>
       let seg2Len := fastLen512 4096 seg2.bytes
       let off := f3StubAddrs.alloc.toNat - seg2.start.toNat
       let w := wordOfBytesLE (fastTake 4 (fastDrop off seg2.bytes)) 0
       seg2.perm == Perm.rx &&
       decide (seg2.start.toNat ≤ f3StubAddrs.alloc.toNat ∧ off + 4 ≤ seg2Len) &&
       (match Arm64.decode w with
        | some (.b boff) => f3StubAddrs.alloc + boff == f3RdlAddrs.alloc
        | _ => false)
     | none => false) = true := by
  rfl_kernel

/-- `(hole2_str1Prog mpl).code` matches `(libsignalSessionLib.blockProgram mpl 623).code` with zero
appended stub bytes, `f3NoShimV2Addr` matches `symNoAllocShimV2` in `.symtab`, and `f3StubAddrs.alloc`
in `img.segments[2]` decodes to an `Instr.b` targeting `f3RdlAddrs.alloc` (`"__rdl_alloc"`). -/
theorem hole2_str1Prog_stubs_specKey {mpl : MultiPlacement} {img : ElfImage}
    (hparse : ElfImage.parse cliElfBytes = .ok img)
    (_hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    let blkLen := (libsignalSessionLib.blockProgram mpl 623).code.length
    let tail := (hole2_str1Prog mpl).code.drop blkLen
    tail = [] ∧
    lookupUnique symNoAllocShimV2 img.symbols = some f3NoShimV2Addr ∧
    lookupUnique symRustcAlloc img.symbols = some f3StubAddrs.alloc ∧
    lookupUnique symRdlAlloc img.symbols = some f3RdlAddrs.alloc ∧
    (∃ seg2 off0,
      img.segments[2]? = some seg2 ∧
      seg2.perm = Perm.rx ∧
      seg2.start.toNat ≤ f3StubAddrs.alloc.toNat ∧
      (f3StubAddrs.alloc.toNat - seg2.start.toNat) + 4 ≤ seg2.bytes.length ∧
      Arm64.decode
        (wordOfBytesLE ((seg2.bytes.drop (f3StubAddrs.alloc.toNat - seg2.start.toNat)).take 4) 0) =
        some (.b off0) ∧
      f3StubAddrs.alloc + off0 = f3RdlAddrs.alloc) := by
  cases cliElf_parse.symm.trans hparse
  have htail : (hole2_str1Prog mpl).code.drop (libsignalSessionLib.blockProgram mpl 623).code.length = [] :=
    List.drop_length
  have hthunk := f3StubAddrs_alloc_seg2_isB_specKey_guard
  cases hs2 : cliElfImage.segments[2]? with
  | none => rw [hs2] at hthunk; nomatch hthunk
  | some seg2 =>
    rw [hs2] at hthunk
    dsimp only at hthunk
    rw [fastLen512_eq_length 4096 seg2.bytes,
        fastDrop_eq_drop (f3StubAddrs.alloc.toNat - seg2.start.toNat) seg2.bytes,
        fastTake_eq_take 4] at hthunk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hthunk
    obtain ⟨⟨hp, hlo, hhi⟩, hdec⟩ := hthunk
    split at hdec
    · rename_i boff hdec_eq
      rw [beq_iff_eq] at hdec
      exact ⟨htail,
        lookupUnique_cliElf_of_enc symNoAllocShimV2_eq f3NoShimV2Addr_specKey_guard cliElf_parse,
        lookupUnique_cliElf_of_enc symRustcAlloc_eq f3StubAddrs_alloc_rustc_specKey_guard cliElf_parse,
        lookupUnique_cliElf_of_enc symRdlAlloc_eq f3RdlAddrs_alloc_specKey_guard cliElf_parse,
        ⟨seg2, boff, rfl, hp, hlo, hhi, hdec_eq, hdec⟩⟩
    · cases hdec

/-! ## `f3StdLayout.rxSegIdx` Uniqueness (`segments[2]`, `read_stdin`) -/

theorem f3StdLayout_rxSegIdx_specKey_guard :
    (match cliElfImage.segments[f3StdLayout.rxSegIdx]? with
     | some rxSeg =>
       rxSeg.perm == Perm.rx &&
       lookupSymChars symReadStdinChars == some rxSeg.start &&
       ((List.range cliElfImage.segments.length).filter
         (fun idx => (cliElfImage.segments[idx]?).map (·.start) == some rxSeg.start)) ==
         [f3StdLayout.rxSegIdx]
     | none => false) = true := by
  rfl_kernel

/-- `img.segments[f3StdLayout.rxSegIdx]` is the unique segment starting at `.symtab` `read_stdin` and
carries `Perm.rx`. -/
theorem f3StdLayout_rxSegIdx_specKey {img : ElfImage}
    (hparse : ElfImage.parse cliElfBytes = .ok img) :
    ∃ rxSeg,
      img.segments[f3StdLayout.rxSegIdx]? = some rxSeg ∧
      rxSeg.perm = Perm.rx ∧
      lookupUnique symReadStdin img.symbols = some rxSeg.start ∧
      (List.range img.segments.length).filter
        (fun idx => (img.segments[idx]?).map (·.start) == some rxSeg.start) =
        [f3StdLayout.rxSegIdx] := by
  cases cliElf_parse.symm.trans hparse
  have hg := f3StdLayout_rxSegIdx_specKey_guard
  cases hrx : cliElfImage.segments[f3StdLayout.rxSegIdx]? with
  | none => rw [hrx] at hg; nomatch hg
  | some rxSeg =>
    rw [hrx] at hg
    dsimp only at hg
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    obtain ⟨⟨hperm, hsym⟩, huniq⟩ := hg
    exact ⟨rxSeg, rfl, hperm,
      lookupUnique_cliElf_of_enc symReadStdin_eq hsym cliElf_parse,
      huniq⟩

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfHole2SpecKey
