/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionObj
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
public import LibsignalBinary.Specifications.LibsignalPublicApi
public import ProofLib.FsTrace

@[expose] public section

set_option autoImplicit false

/-!
# CLI Process Semantics Under Contract-Satisfying Extern Tables

**Checked by Lean.** Generalizes fixed-image CLI execution (`cliRunAbortOnPanic elf W`) to an
arbitrary extern table `ext` (`cliRunAbortOnPanicUnderExterns elf ext`) satisfying separation-logic
contracts `CliExternsOk P A ext`.

Whereas the fixed hooks in `cliHookTable W` preserve caller-saved registers (DEV-E1) and treat
`__rust_dealloc` as a no-op (DEV-E6), `CliExternsOk` requires only `HookSat` against each row's
`Spec` (clobbering caller-saved registers, flags, and bounded stack frames `memHookStack` = 4 KiB
or `extHookStack` = 16 KiB, and consuming `live` tokens on deallocation via `RustAlloc`), while
preserving `tpidr_el0`, execute permissions, and file-system state outside the four I/O hooks.
The fixed hook table is the special case `ext := cliHookExterns W` (`cliRunSig_eq`).
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet

/-! ## Execution Under an Arbitrary Extern Table -/

/-- Extern lookup mapping CLI image panic symbols to `Rust.panicked` (`withCliPanics`) and all
other symbols via `ext`. -/
noncomputable def cliExternsWith (ext : String → Option (State → State)) :
    String → Option (State → State) :=
  withCliPanics ext

/-- `cliExternsWith ext` with every hook wrapped in `abortOnPanic` (`SIGABRT` on panic). -/
noncomputable def cliExternsSigWith (ext : String → Option (State → State)) :
    String → Option (State → State) :=
  fun name => (cliExternsWith ext name).map abortOnPanic

/-- Fixed-image CLI `Program` at `cliBase` using `cliExternsSigWith ext`. -/
noncomputable def cliProgAbortOnPanicUnderExterns (ext : String → Option (State → State)) : Program :=
  libsignalSessionImage.toProgram.rebase cliBase (cliExternsSigWith ext)

/-- Whole-process run predicate for `elf` on `i` under extern table `ext` starting at
`cliTokenPatch s0`. -/
def CliRunsToUnderExterns (elf : ElfImage) (ext : String → Option (State → State)) (i : Inputs)
    (o : Outcome) : Prop :=
  ∃ s0, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    _root_.Arm64.Process.ProcessRunsTo (cliProgAbortOnPanicUnderExterns ext) (cliTokenPatch s0) (OutcomeMatchesProcess o)

open Classical in
/-- Partial run function returning the outcome satisfying `CliRunsToUnderExterns elf ext i`, if any. -/
noncomputable def cliRunAbortOnPanicUnderExterns (elf : ElfImage) (ext : String → Option (State → State)) :
    CliRun := fun i =>
  if h : ∃ o, CliRunsToUnderExterns elf ext i o then some (Classical.choose h) else none

/-- Lookup in the fixed hook table `cliHookTable W` as an extern map. -/
noncomputable def cliHookExterns (W : CliHooks) : String → Option (State → State) :=
  fun name => (cliHookTable W).lookup name

/-! ### Specialization to `cliHookExterns W` -/

theorem cliExterns_eq (W : CliHooks) : cliExterns W = cliExternsWith (cliHookExterns W) := rfl

theorem cliExternsSig_eq (W : CliHooks) :
    cliExternsAbortOnPanic W = cliExternsSigWith (cliHookExterns W) := rfl

theorem cliProgSig_eq (W : CliHooks) : cliProgAbortOnPanic W = cliProgAbortOnPanicUnderExterns (cliHookExterns W) := rfl

theorem cliRunsTo_eq (elf : ElfImage) (W : CliHooks) :
    CliRunsTo elf W = CliRunsToUnderExterns elf (cliHookExterns W) := rfl

theorem cliRunSig_eq (elf : ElfImage) (W : CliHooks) :
    cliRunAbortOnPanic elf W = cliRunAbortOnPanicUnderExterns elf (cliHookExterns W) := rfl

/-! ## Separation-Logic Extern Contracts -/

namespace CliExt

/-- Stack scratch budget (4 KiB below `sp`) available to libc memory hooks. -/
abbrev memHookStack : Nat := 4096

/-- Adjoins `stackAt s.sp stk` to the pre- and postcondition of `spec`. -/
def withStack {α : Type} (spec : Spec α) (stk : Nat := extHookStack) : Spec α :=
  { spec with
    pre := fun x s => spec.pre x s ∗ stackAt s.sp stk
    post := fun x s0 sf => spec.post x s0 sf ∗ stackAt s0.sp stk }

/-- Read-only (`↦ᵣ`) or owned (`↦ₛ`) byte slice at `p`, selected by `ro`. -/
def bytesAt (ro : Bool) (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if ro then p ↦ᵣ bs else p ↦ₛ bs

/-! ### Allocator Shim and libc Memory Routines -/

/-- No-op contract for `__rust_no_alloc_shim_is_unstable_v2()`. -/
def shimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

/-- `memcpy(dst, src, n)` from owned memory with `memHookStack` stack budget and unchanged trace. -/
def memcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := (libcMemcpySpec memHookStack).pre
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp memHookStack

/-- `memcpy(dst, src, n)` from read-only memory with `memHookStack` stack budget. -/
def memcpyROSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withStack
    { pre := fun (dst, src, bs) s0 =>
        ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
          bs.length ≤ 2 ^ 64⌝ ∗ memRegion dst bs.length ∗ (src ↦ᵣ bs)
      post := fun (dst, src, bs) s0 sf =>
        ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) }
    memHookStack

/-- `memmove(base + dst, base + src, len)` within a single owned buffer, preserving the trace. -/
def memmoveSpec : Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) where
  pre := (libcMemmoveSpec memHookStack).pre
  post := fun (base, buf, dst, src, len) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧ sf.trace = s0.trace⌝ ∗
      (base ↦ₛ listMove buf dst src len) ∗ stackAt s0.sp memHookStack

/-- `memset(ptr, c, len)` with `memHookStack` stack budget, preserving the trace. -/
def memsetSpec : Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := (libcMemsetSpec memHookStack).pre
  post := fun (ptr, c, len) s0 sf =>
    ⌜sf.readReg64 .x0 = ptr ∧ sf.trace = s0.trace⌝ ∗
      (ptr ↦ₛ List.replicate len c) ∗ stackAt s0.sp memHookStack

/-- Arguments and ownership flags for a `bcmp(a, b, n)` call. -/
structure BcmpCall where
  a : BitVec 64
  aRo : Bool
  bsA : List (BitVec 8)
  b : BitVec 64
  bRo : Bool
  bsB : List (BitVec 8)

/-- C `bcmp` contract: sets the low 32 bits of `x0` to `0` iff the two `n`-byte slices are equal,
returning both slices with trace unchanged. -/
def bcmpSpec : Spec BcmpCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ s.readReg64 .x1 = x.b ∧
      (s.readReg64 .x2).toNat = x.bsA.length ∧ x.bsB.length = x.bsA.length⌝ ∗
      bytesAt x.aRo x.a x.bsA ∗ bytesAt x.bRo x.b x.bsB ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 32 = 0#32 ↔ x.bsA = x.bsB) ∧ sf.trace = s0.trace⌝ ∗
      bytesAt x.aRo x.a x.bsA ∗ bytesAt x.bRo x.b x.bsB ∗ stackAt s0.sp extHookStack

/-- Owned NUL-terminated byte string `s` at `p`. -/
def cStrAt (p : BitVec 64) (s : List (BitVec 8)) : SepProp := p ↦ₛ (s ++ [0#8])

/-- `strlen(p)` on an interior-NUL-free C string `s`: returns `x0 = s.length` with trace and file
system unchanged. -/
def strlenSpec : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (p, s) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ ∀ b ∈ s, b ≠ 0#8⌝ ∗ cStrAt p s ∗ stackAt s0.sp extHookStack
  post := fun (p, s) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 s.length ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      cStrAt p s ∗ stackAt s0.sp extHookStack

/-- `core::str::from_utf8` on ASCII bytes `bs`: writes `Ok(&bs)` (`tag = 0`, pointer, length) to
sret `x8` with trace and file system unchanged. -/
def fromUtf8Spec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (r, p, bs) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 (.gpr 8#5) = r ∧ ∀ b ∈ bs, b.toNat < 128⌝ ∗
      (p ↦ₛ bs) ∗ memRegion r 24 ∗ stackAt s0.sp extHookStack
  post := fun (r, p, bs) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗ (p ↦ₛ bs) ∗ (r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ p) ∗
      ((r + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ stackAt s0.sp extHookStack

/-- Arguments and ownership flag for a `memrchr(c, p, len)` call. -/
structure MemrchrCall where
  c : BitVec 8
  p : BitVec 64
  bs : List (BitVec 8)

/-- Last index of byte `c` in `bs`, if present. -/
def memrchrIdx (c : BitVec 8) (bs : List (BitVec 8)) : Option Nat :=
  ((List.range bs.length).filter fun i => bs[i]? == some c).getLast?

/-- `core::slice::memchr::memrchr(c, p, len) -> Option<usize>`: returns `(1, i)` at the last index
`i` of `c` or `x0 = 0` when absent, preserving trace and file system. -/
def memrchrSpec : Spec MemrchrCall where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = x.c ∧ s.readReg64 .x1 = x.p ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.bs.length ∧ x.bs.length < 2 ^ 64⌝ ∗
      (x.p ↦ₛ x.bs) ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs ∧ match memrchrIdx x.c x.bs with
      | some i => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 i
      | none => sf.readReg64 .x0 = 0#64⌝ ∗ (x.p ↦ₛ x.bs) ∗ stackAt s0.sp extHookStack

/-! ### File-System and Standard-I/O Contracts -/

/-- Converts raw path bytes one-to-one into an `FsState.files` key string. -/
def pathStr (p : List (BitVec 8)) : String := String.ofList (p.map fun b => Char.ofNat b.toNat)

/-- Valid CLI path bytes: `PathOk`, ASCII, components `≤ 255` bytes, and total length
`< cliPathMaxBytes` (`4096`). -/
def cliPathOk (path : List (BitVec 8)) : Prop :=
  PathOk (pathStr path) = true ∧
    ((∀ b ∈ path, b.toNat < 128) ∧
      ((pathComps (pathStr path)).all fun c => decide (c.length ≤ NAME_MAX)) = true) ∧
    path.length < cliPathMaxBytes

def blockingAncestorF (F : String → Option FsEntry) (p : String) : Option (Option FsEntry) :=
  ((ancestors p).find? fun q => match F q with | some .dir => false | _ => true).map F

/-- File-map read view at `p`: `none` on a regular-file proper ancestor, directory target, or size
above `fileCapBytes`; `some []` if missing; `some bs` otherwise. -/
def readViewF (F : String → Option FsEntry) (p : String) : Option (List (BitVec 8)) :=
  match blockingAncestorF F p with
  | some (some _) => none
  | some none => some []
  | none =>
    match F p with
    | some (.file bs) => if bs.length ≤ fileCapBytes then some bs else none
    | some .dir => none
    | none => some []

/-- Result of `read_file` on file map `F` and `path`. -/
def readFileResult (F : String → Option FsEntry) (path : List (BitVec 8)) :
    Except Unit (List (BitVec 8)) :=
  match readViewF F (pathStr path) with
  | none => .error ()
  | some bs => .ok bs

/-- File-map update of `write_file`: `none` if blocked by a regular-file ancestor or existing
directory at `path`, otherwise sets `path`'s canonical entry to `bs`. -/
def writeFileResult (F : String → Option FsEntry) (path bs : List (BitVec 8)) :
    Option (String → Option FsEntry) :=
  match blockingAncestorF F (pathStr path), F (pathStr path) with
  | some _, _ => none
  | none, some .dir => none
  | none, _ => some fun q =>
      if (normalizePath q).isEmpty then some .dir
      else if normalizePath q = normalizePath (pathStr path) then some (.file bs) else F q

/-- Remaining `stdin` bytes when fd 0 is a readable `.stdio` descriptor. -/
def stdinBytes (fs : FsState) : Option (List (BitVec 8)) :=
  match fs.fds 0#64 with
  | some e =>
    if e.kind == .stdio && e.accMode.canRead then
      some (fs.stdin.drop e.offset)
    else none
  | none => none

/-- Memory layout of `Result<Vec<u8>, IoError>` at `r` (24 bytes): owned `Vec<u8>` on `.ok`, tag
`-1` on `.error`. -/
def ioVecAt (A : RustAlloc) (r : BitVec 64) : Except Unit (List (BitVec 8)) → SepProp
  | .ok bs => vecU8 A r bs
  | .error _ => (r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (r + 8#64) 16

/-- Call parameters for `read_file`. -/
structure ReadFileCall where
  pathA : BitVec 64
  ro : Bool
  path : List (BitVec 8)
  ret : BitVec 64

/-- `read_file(path)` (sret `x8`): writes `readFileResult s0.fs.files path`, preserving files;
panics after logging `allocFailedEvent` on allocation failure. -/
def readFileSpec (A : RustAlloc) (img : Obj.Image) : Spec ReadFileCall :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
          s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ cliPathOk x.path⌝ ∗
          bytesAt x.ro x.pathA x.path ∗ memRegion x.ret 24 ∗ stackAt s.sp extHookStack ∗ A.pool
      post := fun x s0 sf =>
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜sf.fs.files = s0.fs.files ∧ r = readFileResult s0.fs.files x.path ∧ sf.trace = s0.trace⌝ ∗
            ioVecAt A x.ret r) ∗
          bytesAt x.ro x.pathA x.path ∗ stackAt s0.sp extHookStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Call parameters for `read_stdin`. -/
structure ReadStdinCall where
  ret : BitVec 64
  bs : List (BitVec 8)

/-- `read_stdin()` (sret `x8`): writes `readStdinResult` on `stdinBytes s0.fs`, preserving files;
panics after logging `allocFailedEvent` on allocation failure. -/
def readStdinSpec (A : RustAlloc) (img : Obj.Image) : Spec ReadStdinCall :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x8 = x.ret ∧ stdinBytes s.fs = some x.bs⌝ ∗
          memRegion x.ret 24 ∗ stackAt s.sp extHookStack ∗ A.pool
      post := fun x s0 sf =>
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜sf.fs.files = s0.fs.files ∧ r = readStdinResult x.bs ∧ sf.trace = s0.trace⌝ ∗ ioVecAt A x.ret r) ∗
          stackAt s0.sp extHookStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Call parameters for `write_file`. -/
structure WriteFileCall where
  pathA : BitVec 64
  path : List (BitVec 8)
  buf : BitVec 64
  bs : List (BitVec 8)

/-- `write_file(path, bytes)` (`x0 = 0` on `Ok`, `1` on `Err`): updates files by `writeFileResult`,
preserving stdout and extending the trace monotonically. -/
def writeFileSpec (img : Obj.Image) : Spec WriteFileCall :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
          s.readReg64 .x2 = x.buf ∧ (s.readReg64 .x3).toNat = x.bs.length ∧
          x.path.length < 2 ^ 32 ∧ cliPathOk x.path⌝ ∗
          (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s.sp extHookStack
      post := fun x s0 sf =>
        ⌜(match writeFileResult s0.fs.files x.path x.bs with
          | some F' => sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = F'
          | none => sf.readReg64 .x0 = 1#64 ∧ sf.fs.files = s0.fs.files) ∧
          s0.trace <+: sf.trace ∧
          ProcessOutcome.traceStreamBytes .stdout sf.trace =
            ProcessOutcome.traceStreamBytes .stdout s0.trace⌝ ∗
          (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp extHookStack }
    img

/-- Call parameters for `write_stdout`. -/
structure WriteStdoutCall where
  buf : BitVec 64
  bs : List (BitVec 8)

/-- `write_stdout(bytes)` (`x0 = 0`): appends `bytes` to stdout and leaves files unchanged. -/
def writeStdoutSpec (img : Obj.Image) : Spec WriteStdoutCall :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.buf ∧ (s.readReg64 .x1).toNat = x.bs.length⌝ ∗
          (x.buf ↦ₛ x.bs) ∗ stackAt s.sp extHookStack
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = s0.fs.files ∧ s0.trace <+: sf.trace ∧
          ProcessOutcome.traceStreamBytes .stdout sf.trace =
            ProcessOutcome.traceStreamBytes .stdout s0.trace ++ x.bs⌝ ∗
          (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp extHookStack }
    img

/-! ### Time, Constant-Time Barrier, and Session Crypto (`C : Crypto`) -/

/-- `SystemTime::duration_since(&UNIX_EPOCH, UNIX_EPOCH)` (sret `x8`): returns `Ok` with 0 seconds,
leaving tag and nanosecond words unconstrained. -/
def durationSinceEpochSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun (p, ret) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret ∧
      s.readReg64 .x1 = 0#64 ∧ (s.readReg64 .x2).setWidth 32 = 0#32⌝ ∗
      (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₃₂ 0#32) ∗ memRegion (p + 12#64) 4 ∗
      memRegion ret 24 ∗ stackAt s.sp extHookStack
  post := fun (p, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion p 16 ∗
      ((∃∗ w2 : BitVec 64, ∃∗ w0 : BitVec 64,
        (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗ ((ret + 16#64) ↦₆₄ w2))) ∗
      stackAt s0.sp extHookStack

/-- `subtle::black_box::<u8>(v)`: zero-extends the low byte of `v` into `w0` with trace unchanged. -/
def blackBoxSpec : Spec (BitVec 64) :=
  withStack
    { pre := fun v s => ⌜s.readReg64 .x0 = v⌝
      post := fun v s0 sf =>
        ⌜(sf.readReg64 .x0).setWidth 32 = (v.setWidth 8).zeroExtend 32 ∧ sf.trace = s0.trace⌝ }

/-- `sha2::sha256::compress256(state, blocks, n)`: folds `n` 64-byte blocks into `state` via `C.F`. -/
def compress256Spec (C : Crypto) :
    Spec (BitVec 64 × HMAC.ShaState × BitVec 64 × List (BitVec 8) × Nat) :=
  withStack
    { pre := fun (stA, st, blkA, bs, n) s =>
        ⌜s.readReg64 .x0 = stA ∧ s.readReg64 .x1 = blkA ∧ (s.readReg64 .x2).toNat = n ∧
          bs.length = 64 * n⌝ ∗
          (stA ↦ₛ LibsignalHmac.shaStateBytes st) ∗ (blkA ↦ₛ bs)
      post := fun (stA, st, blkA, bs, _) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          (stA ↦ₛ LibsignalHmac.shaStateBytes ((HMAC.chunks64 bs).foldl C.F st)) ∗ (blkA ↦ₛ bs) }

/-- `StaticSecret::diffie_hellman(&self, &their_public)` (sret `x8`, 32 bytes): writes `C.X sec pub`. -/
def dhSpec (C : Crypto) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List.Vector (BitVec 8) 32 ×
      BitVec 64) :=
  withStack
    { pre := fun (secA, sec, pubA, pub, ret) s =>
        ⌜s.readReg64 .x0 = secA ∧ s.readReg64 .x1 = pubA ∧ s.readReg64 .x8 = ret⌝ ∗
          (secA ↦ₛ sec.toList) ∗ (pubA ↦ₛ pub.toList) ∗ memRegion ret 32
      post := fun (secA, sec, pubA, pub, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          (secA ↦ₛ sec.toList) ∗ (pubA ↦ₛ pub.toList) ∗ (ret ↦ₛ (C.X sec pub).toList) }

/-- `<PublicKey as From<&StaticSecret>>::from(&secret)` (sret `x8`, 32 bytes): writes `C.pubKey sec`. -/
def pubFromSecretSpec (C : Crypto) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64) :=
  withStack
    { pre := fun (secA, sec, ret) s =>
        ⌜s.readReg64 .x0 = secA ∧ s.readReg64 .x8 = ret⌝ ∗
          (secA ↦ₛ sec.toList) ∗ memRegion ret 32
      post := fun (secA, sec, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ (secA ↦ₛ sec.toList) ∗ (ret ↦ₛ (C.pubKey sec).toList) }

/-- `Drop::drop` on `StaticSecret` / `SharedSecret`: zeroes the 32-byte buffer at `x0`. -/
def zeroizeSpec : Spec (BitVec 64) :=
  withStack
    { pre := fun a s => ⌜s.readReg64 .x0 = a⌝ ∗ memRegion a 32
      post := fun a s0 sf => ⌜sf.trace = s0.trace⌝ ∗ (a ↦ₛ List.replicate 32 0#8) }

/-! ### PQXDH Primitives (`Q : E2E.PqxdhPrims`) and Contract Bundle -/

/-- Post-call ownership of an `n`-byte input at `p`: preserved (`↦ₛ v`) if borrowed, or an
arbitrary `memRegion` if passed by value (`byVal`). -/
def inputAfter {n : Nat} (byVal : Bool) (p : BitVec 64) (v : List.Vector (BitVec 8) n) : SepProp :=
  if byVal then memRegion p n else p ↦ₛ v.toList

/-- Generic pure leaf contract reading `m` input bytes at `x0` and writing `n` output bytes to sret
`x8`. -/
def pureByteFunctionSpec {m n : Nat} (f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n)
    (byVal : Bool) : Spec (BitVec 64 × List.Vector (BitVec 8) m × BitVec 64) :=
  withStack
    { pre := fun (inA, v, ret) s =>
        ⌜s.readReg64 .x0 = inA ∧ s.readReg64 .x8 = ret⌝ ∗ (inA ↦ₛ v.toList) ∗ memRegion ret n
      post := fun (inA, v, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ inputAfter byVal inA v ∗ (ret ↦ₛ (f v).toList) }

/-- `sha2::sha512::compress512(state, blocks, n)`: folds `n` 128-byte blocks into the 8 LE words at
`x0` via `Q.F512`. -/
def compress512Spec (Q : E2E.PqxdhPrims) :
    Spec (BitVec 64 × E2E.Sha512State × BitVec 64 × List (BitVec 8) × Nat) :=
  withStack
    { pre := fun (stA, st, blkA, bs, n) s =>
        ⌜s.readReg64 .x0 = stA ∧ s.readReg64 .x1 = blkA ∧ (s.readReg64 .x2).toNat = n ∧
          bs.length = 128 * n⌝ ∗ (stA ↦ₛ E2E.sha512StateBytesLE st) ∗ (blkA ↦ₛ bs)
      post := fun (stA, st, blkA, bs, _) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          (stA ↦ₛ E2E.sha512StateBytesLE ((E2E.chunks128 bs).foldl Q.F512 st)) ∗ (blkA ↦ₛ bs) }

/-- Memory layout of `Option<EdwardsPoint>` at `r` (168 bytes): `u64` tag (`1` for `some`, `0` for
`none`) followed by 160 point bytes. -/
def optionEdwardsPointAt (r : BitVec 64) : Option (List.Vector (BitVec 8) 160) → SepProp
  | some p => (r ↦₆₄ 1#64) ∗ ((r + 8#64) ↦ₛ p.toList)
  | none => (r ↦₆₄ 0#64) ∗ memRegion (r + 8#64) 160

/-- `MontgomeryPoint::to_edwards(&u, sign)` (sret `x8`): writes `Q.montToEd u (sign &&& 1#8)`,
extracting bit 0 of `w1`. -/
def toEdwardsSpec (Q : E2E.PqxdhPrims) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 8 × BitVec 64) :=
  withStack
    { pre := fun (uA, u, sign, ret) s =>
        ⌜s.readReg64 .x0 = uA ∧ (s.readReg64 .x1).setWidth 8 = sign ∧ s.readReg64 .x8 = ret⌝ ∗
          (uA ↦ₛ u.toList) ∗ memRegion ret 168
      post := fun (uA, u, sign, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ (uA ↦ₛ u.toList) ∗
          optionEdwardsPointAt ret (Q.montToEd u (sign &&& 1#8)) }

/-- `EdwardsPoint::is_torsion_free(&p) -> bool`: sets the low 32 bits of `x0` to `1` or `0`
according to `Q.isTorsionFree p`. -/
def torsionFreeSpec (Q : E2E.PqxdhPrims) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 160) :=
  withStack
    { pre := fun (pA, p) s => ⌜s.readReg64 .x0 = pA⌝ ∗ (pA ↦ₛ p.toList)
      post := fun (pA, p) s0 sf =>
        ⌜sf.trace = s0.trace ∧
          (sf.readReg64 .x0).setWidth 32 = (if Q.isTorsionFree p then 1#32 else 0#32)⌝ ∗
          (pA ↦ₛ p.toList) }

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint(&a, &A, &b)` (sret `x8`): writes
`Q.dsmb a A b`. -/
def dsmbSpec (Q : E2E.PqxdhPrims) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List.Vector (BitVec 8) 160 ×
      BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64) :=
  withStack
    { pre := fun (aA, a, pA, p, bA, b, ret) s =>
        ⌜s.readReg64 .x0 = aA ∧ s.readReg64 .x1 = pA ∧ s.readReg64 .x2 = bA ∧
          s.readReg64 .x8 = ret⌝ ∗
          (aA ↦ₛ a.toList) ∗ (pA ↦ₛ p.toList) ∗ (bA ↦ₛ b.toList) ∗ memRegion ret 160
      post := fun (aA, a, pA, p, bA, b, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ (aA ↦ₛ a.toList) ∗ (pA ↦ₛ p.toList) ∗ (bA ↦ₛ b.toList) ∗
          (ret ↦ₛ (Q.dsmb a p b).toList) }

/-- `kyber::encapsulate(&pk, randomness)` (sret `x8`): writes ciphertext at `+0` and shared secret
at `+0x620` from `Q.encaps pk rnd`, consuming by-value `randomness`. -/
def kemEncapsSpec (Q : E2E.PqxdhPrims) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 1568 × BitVec 64 × List.Vector (BitVec 8) 32 ×
      BitVec 64) :=
  withStack
    { pre := fun (pkA, pk, rA, rnd, ret) s =>
        ⌜s.readReg64 .x0 = pkA ∧ s.readReg64 .x1 = rA ∧ s.readReg64 .x8 = ret⌝ ∗
          (pkA ↦ₛ pk.toList) ∗ (rA ↦ₛ rnd.toList) ∗ memRegion ret 1600
      post := fun (pkA, pk, rA, rnd, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ (pkA ↦ₛ pk.toList) ∗ memRegion rA 32 ∗
          (ret ↦ₛ (Q.encaps pk rnd).1.toList) ∗ ((ret + 0x620#64) ↦ₛ (Q.encaps pk rnd).2.toList) }

/-- `kyber::decapsulate(&sk, &ct)` (sret `x8`): writes `Q.decaps sk ct`. -/
def kemDecapsSpec (Q : E2E.PqxdhPrims) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 3168 × BitVec 64 × List.Vector (BitVec 8) 1568 ×
      BitVec 64) :=
  withStack
    { pre := fun (skA, sk, ctA, ct, ret) s =>
        ⌜s.readReg64 .x0 = skA ∧ s.readReg64 .x1 = ctA ∧ s.readReg64 .x8 = ret⌝ ∗
          (skA ↦ₛ sk.toList) ∗ (ctA ↦ₛ ct.toList) ∗ memRegion ret 32
      post := fun (skA, sk, ctA, ct, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ (skA ↦ₛ sk.toList) ∗ (ctA ↦ₛ ct.toList) ∗
          (ret ↦ₛ (Q.decaps sk ct).toList) }

/-- Extern stub names of the four file-system/stdio I/O routines. -/
def ioNames : List String := [readFileName, writeFileName, readStdinName, writeStdoutName]

end CliExt

open CliExt in
/-- Separation-logic contract bundle for an extern table `ext` at primitives `P` and allocator `A`:
`HookSat` on every hooked CLI extern together with preservation of `tpidr_el0`, execute
permissions, monotone file-change tracing (`HookFsTraced`), file-system frame outside `ioNames`,
and empty initial allocator pool (`A.poolEmp`). -/
structure CliExternsOk (P : E2E.PEParams) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop where
  tpidr : ∀ n f, ext n = some f → ∀ s, (f s).tpidrEl0 = s.tpidrEl0
  noExec : ∀ n f, ext n = some f → ∀ s a, ((f s).mem.perm a).x → (s.mem.perm a).x
  fsTraced : ∀ n f, ext n = some f → HookFsTraced (fun e => e.isFsChange = true) f
  fsKept : ∀ n f, ext n = some f → n ∉ ioNames → ∀ s, (f s).fs = s.fs
  poolEmp : emp ⊢ A.pool
  -- The allocator.
  shim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" shimSpec
  alloc : AllocHooks A ext
  allocZeroed : HookSat ext allocZeroedName (rustAllocZeroedSpec A)
  -- libc.
  memset : HookSat ext "memset" memsetSpec
  memmove : HookSat ext "memmove" memmoveSpec
  memcpy : HookSat ext "memcpy" memcpySpec
  memcpyRO : HookSat ext "memcpy" memcpyROSpec
  bcmp : HookSat ext "bcmp" bcmpSpec
  strlen : HookSat ext "strlen" strlenSpec
  -- The I/O crate.
  readFile : ∀ img, HookSat ext readFileName (readFileSpec A img)
  writeFile : ∀ img, HookSat ext writeFileName (writeFileSpec img)
  readStdin : ∀ img, HookSat ext readStdinName (readStdinSpec A img)
  writeStdout : ∀ img, HookSat ext writeStdoutName (writeStdoutSpec img)
  -- `core` / `std`.
  memrchr : HookSat ext "core::slice::memchr::memrchr" memrchrSpec
  fromUtf8 : HookSat ext "core::str::converts::from_utf8" fromUtf8Spec
  fmtWrite : HookSat ext fmtWriteName (fmtWriteSpec A)
  formatInner : HookSat ext formatInnerName (formatInnerSpec A)
  durationSince : HookSat ext LibsignalPublicApi.durationSinceHookName durationSinceEpochSpec
  timeAdd : HookSat ext LibsignalPublicApi.timeAddHookName LibsignalPublicApi.timeAddSpec
  blackBox : HookSat ext "subtle::black_box::<u8>" blackBoxSpec
  -- The session primitives `P.C`.
  compress256 : HookSat ext "sha2::sha256::compress256" (compress256Spec P.C)
  aesEnc : HookSat ext aesEncName (aesEncSpec P.C.E A)
  aesDec : HookSat ext aesDecName (aesDecSpec P.C.D A)
  pubFromSecret : HookSat ext pubFromSecretName (pubFromSecretSpec P.C)
  dh : HookSat ext dhName (dhSpec P.C)
  staticDrop : HookSat ext staticDropName zeroizeSpec
  sharedDrop : HookSat ext sharedDropName zeroizeSpec
  -- The PQXDH primitives `P.Q`.
  compress512 : HookSat ext E2E.compress512Name (compress512Spec P.Q)
  toEdwards : HookSat ext E2E.toEdwardsName (toEdwardsSpec P.Q)
  compress : HookSat ext E2E.compressName (pureByteFunctionSpec P.Q.compress false)
  edNeg : HookSat ext E2E.edNegName (pureByteFunctionSpec P.Q.edNeg true)
  torsionFree : HookSat ext E2E.torsionFreeName (torsionFreeSpec P.Q)
  dsmb : HookSat ext E2E.dsmbName (dsmbSpec P.Q)
  scalarMod : HookSat ext E2E.scalarModName (pureByteFunctionSpec P.Q.scalarMod true)
  scalarWide : HookSat ext E2E.scalarWideName (pureByteFunctionSpec P.Q.scalarWide false)
  kemEncaps : HookSat ext E2E.kemEncapsName (kemEncapsSpec P.Q)
  kemDecaps : HookSat ext E2E.kemDecapsName (kemDecapsSpec P.Q)
  -- SPQR V1's ML-KEM-768 and helpers (`P.Q.K`, HMAC over `P.C.F`).
  spqr : LibsignalSpqrV1.SpqrHooks P.C A P.Q.K ext

end CryptoVerification.SignalSession
