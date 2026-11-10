/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Hyps
public import LibsignalBinary.Specifications.SignalSession.CliRun
public import LibsignalBinary.Proofs.SpecLemmas.SymtabGhost
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ProcessProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.RunProofDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Model
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliSymtabGhost
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run

/-!
# CLI `main` Specification and Process Composition

Specification of `extern "C" fn main(argc, argv) -> c_int` (`mainSpec`, `mainSpecTight`) and its
composition (`outcome_of_main`, `outcome_of_main_or_oom`) with musl's `_start`/`exit_group` harness
(`MuslHarness`).

Because the `#![no_main]` binary returns `0` (accept), `1` (reject), or `2` (usage or I/O error) to
musl, `exit_group` terminates with `.Exited (signExtend 64 w0)`. Since the ELF loader installs a flat
symbol table rather than the per-object `img.symtab` expected by `Spec.inImage`, `outcome_of_main`
executes `main`'s contract with `img.symtab` swapped in and transports the execution back via
`SymtabGhost`.
-/

@[expose] public section

set_option warningAsError false

/-! ## `main` -/

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ### Inputs -/

/-- Process inputs for one CLI invocation on `i`, with `argv[0] = "signal-session"` followed by `i.argv`. -/
def cliInputs (i : Inputs) : ProcessInputs :=
  processInputs ("libsignal-cli" :: i.argv) i.stdin i.files i.dirs

/-- Input precondition for musl startup: printable ASCII arguments fitting the initial stack (`ArgvFitsInitialStack`). -/
def CliInputsOk (i : Inputs) : Prop := (∀ a ∈ i.argv, PrintableAsciiArg a) ∧ ArgvFitsInitialStack i.argv

/-- Loader admissibility predicate: every directory and file path satisfies `LoadablePath`, and every initial regular file has size at most `MAX_LFS_FILESIZE` (`2 ^ 63 - 1`). -/
def InputsLoadable (i : Inputs) : Prop :=
  (∀ d ∈ i.dirs, LoadablePath d) ∧
  (∀ f ∈ i.files, LoadablePath f.1 ∧ f.2.length ≤ MAX_LFS_FILESIZE)

/-- Static ELF well-formedness and `brk` bound below the base of the 8 MiB stack (`DEV-CLI7`). -/
def ElfStaticOk (elf : ElfImage) : Prop :=
  elf.WellFormed = true ∧ elf.brkStart.toNat ≤ defaultStackTop.toNat - 8388608

/-! ### `main`'s result -/

/-- Outcome of `main` on a single call: panic (`abort`), or return code `code` after committing `writes` in order and writing `out` to stdout. -/
inductive MainResult where
  | abort
  | ret (code : Nat) (writes : List (String × List (BitVec 8))) (out : List (BitVec 8))

/-- Result of `run`: `none` on panic, `some none` on reject, or `some (some (writes, out))` on accept. -/
abbrev RunAnswer := Option (Option (List (String × List (BitVec 8)) × List (BitVec 8)))

/-- Maps `run`'s `RunAnswer` to `MainResult` (`abort` on `none`, exit `1` on reject, exit `0` committing `writes` and printing `out` on accept). -/
def MainResult.ofAnswer : RunAnswer → MainResult
  | none => .abort
  | some none => .ret 1 [] []
  | some (some (w, out)) => .ret 0 w out

/-- `"coins"` is not a directory in the initial file system and any regular file there has size at most `fileCapBytes`, so `read_file("coins")` returns `Ok`. -/
def CoinsReadable (i : Inputs) : Prop :=
  (initFsState (cliInputs i)).files "coins" ≠ some .dir ∧
    ∀ bs, (initFsState (cliInputs i)).files "coins" = some (.file bs) → bs.length ≤ fileCapBytes

/-- `p` is a valid non-directory path whose proper ancestors are all directories in the initial file system, so `write_file(p, _)` returns `Ok`. -/
def WriteOk (i : Inputs) (p : String) : Prop :=
  PathOk p = true ∧ (initFsState (cliInputs i)).files p ≠ some .dir ∧
    (∀ q ∈ ancestors p, (initFsState (cliInputs i)).files q = some .dir) ∧
    ∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast,
      (initFsState (cliInputs i)).entries pref = some .dir

/-- Every committed write in `r` satisfies `WriteOk i`. -/
def CommitOk (i : Inputs) : MainResult → Prop
  | .ret _ w _ => ∀ pw ∈ w, WriteOk i pw.1
  | .abort => True

/-- Expected `MainResult` for input `i`: `usage` (exit `2` with no I/O when `i.argv` fails CLI grammar parsing) or `call` (`run` yields `r` with `CoinsReadable` and `CommitOk`). -/
inductive MainCase (Run : Inputs → RunAnswer → Prop) : Inputs → MainResult → Prop
  | usage {i : Inputs} : (∀ a ∈ i.argv, PrintableAsciiArg a) → ArgvShapeOk i.argv = false →
      MainCase Run i (.ret 2 [] [])
  | call {i : Inputs} {r : RunAnswer} : Run i r → CoinsReadable i →
      CommitOk i (MainResult.ofAnswer r) → MainCase Run i (MainResult.ofAnswer r)

theorem MainCase.commitOk {Run : Inputs → RunAnswer → Prop} {i : Inputs} {r : MainResult}
    (h : MainCase Run i r) : CommitOk i r := by
  cases h with
  | usage _ _ => intro _ hp; cases hp
  | call _ _ hc => exact hc

theorem MainResult.ofAnswer_code_le {a : RunAnswer} {code : Nat}
    {w : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (h : MainResult.ofAnswer a = .ret code w out) : code ≤ 2 := by
  match a, h with
  | none, h => cases h
  | some none, h => cases h; decide
  | some (some _), h => cases h; decide

/-- Every `MainCase` return code is at most `2`. -/
theorem MainCase.code_le {Run : Inputs → RunAnswer → Prop} {i : Inputs} {r : MainResult}
    (hc : MainCase Run i r) {code : Nat} {w : List (String × List (BitVec 8))}
    {out : List (BitVec 8)} (hr : r = .ret code w out) : code ≤ 2 := by
  cases hc with
  | usage _ _ => cases hr; decide
  | call _ _ _ => exact MainResult.ofAnswer_code_le hr

/-- Expected `MainResult` with bounded `read_stdin` (`StdinOverCap`, exit `2`) and early send-plaintext length check (`SendOverCap`, exit `1`). -/
inductive MainCaseB2 (Run : Inputs → RunAnswer → Prop)
    (SendOverCap StdinOverCap : Inputs → Prop) : Inputs → MainResult → Prop
  | usage {i : Inputs} : (∀ a ∈ i.argv, PrintableAsciiArg a) → ArgvShapeOk i.argv = false →
      MainCaseB2 Run SendOverCap StdinOverCap i (.ret 2 [] [])
  | stdinOverCap {i : Inputs} : StdinOverCap i →
      MainCaseB2 Run SendOverCap StdinOverCap i (.ret 2 [] [])
  | sendOverCap {i : Inputs} : SendOverCap i → ¬ StdinOverCap i → CoinsReadable i →
      MainCaseB2 Run SendOverCap StdinOverCap i (.ret 1 [] [])
  | call {i : Inputs} {r : RunAnswer} : Run i r → ¬ SendOverCap i → ¬ StdinOverCap i →
      CoinsReadable i → CommitOk i (MainResult.ofAnswer r) →
      MainCaseB2 Run SendOverCap StdinOverCap i (MainResult.ofAnswer r)

theorem MainCaseB2.commitOk {Run : Inputs → RunAnswer → Prop}
    {SendOverCap StdinOverCap : Inputs → Prop}
    {i : Inputs} {r : MainResult} (h : MainCaseB2 Run SendOverCap StdinOverCap i r) :
    CommitOk i r := by
  cases h with
  | usage _ _ => intro _ hp; cases hp
  | stdinOverCap _ => intro _ hp; cases hp
  | sendOverCap _ _ _ => intro _ hp; cases hp
  | call _ _ _ _ hc => exact hc

/-- Every `MainCaseB2` return code is at most `2`. -/
theorem MainCaseB2.code_le {Run : Inputs → RunAnswer → Prop}
    {SendOverCap StdinOverCap : Inputs → Prop}
    {i : Inputs} {r : MainResult} (hc : MainCaseB2 Run SendOverCap StdinOverCap i r)
    {code : Nat} {w : List (String × List (BitVec 8))}
    {out : List (BitVec 8)} (hr : r = .ret code w out) : code ≤ 2 := by
  cases hc with
  | usage _ _ => cases hr; decide
  | stdinOverCap _ => cases hr; decide
  | sendOverCap _ _ _ => cases hr; decide
  | call _ _ _ _ _ => exact MainResult.ofAnswer_code_le hr

/-- Send-plaintext cap violation: `argv` parses as `send <peer>` and `1_000_000 < i.stdin.length`. -/
def IsSendOverCap (i : Inputs) : Prop :=
  (∃ peer, MainHops.parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer)) ∧
    1_000_000 < i.stdin.length

/-- Standard-input cap violation: `argv` parses as `send` or `recv` and `stdinCapBytes < i.stdin.length`. -/
def IsStdinOverCap (i : Inputs) : Prop :=
  (∃ c, MainHops.parseArgs uuidTryParse (i.argv.map bytesOfString) = some c ∧ 1 < c.tag) ∧
    stdinCapBytes < i.stdin.length

/-! ### `mainSpec` -/

/-- NUL-terminated byte string `s` at `p`. -/
def cStrAt (p : BitVec 64) (s : List (BitVec 8)) : SepProp := p ↦ₛ (s ++ [0#8])

/-- NULL-terminated C `argv` pointer array at `a`, each entry pointing to its NUL-terminated string. -/
def argvAt : BitVec 64 → List (List (BitVec 8)) → SepProp
  | a, [] => a ↦₆₄ 0#64
  | a, s :: ss => ∃∗ p, (a ↦₆₄ p) ∗ cStrAt p s ∗ argvAt (a + 8#64) ss

/-- Entry separation-logic frame for `main`: `argv` at `x1`, `stk` stack bytes below `sp`, the allocator pool, and writable statics `Statics`. -/
def mainFrame (A : RustAlloc) (stk : Nat) (Statics : SepProp) (i : Inputs) (s : State) :
    SepProp :=
  argvAt (s.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
    stackAt s.sp stk ∗ A.pool ∗ Statics

/-- Image-base offset of `signal_session::coins::NEXT.0` (`.img.data`, 8 bytes). -/
abbrev coinsNextOff : BitVec 64 := 0x9a050#64

/-- Image-base offset of `signal_session::coins::LEFT.0` (`.img.bss`, 8 bytes). -/
abbrev coinsLeftOff : BitVec 64 := 0x9a058#64

/-- Writable statics `coins::NEXT` and `coins::LEFT`, initialized by `coins::install` before first read. -/
def coinsStatics (img : Obj.Image) : SepProp :=
  (∃∗ v : BitVec 64, (img.base + coinsNextOff) ↦₆₄ v) ∗
    (∃∗ v : BitVec 64, (img.base + coinsLeftOff) ↦₆₄ v)

/-- Writable statics touched during a CLI run, disjoint from `img.FrozenLoaded`: `coinsStatics img`, SPQR's `TokenInit img` (`STORAGE.0 = false`), and `log::MAX_LOG_LEVEL_FILTER = 0` at `img.base + 0x9a160`. -/
def cliStatics (img : Obj.Image) : SepProp :=
  coinsStatics img ∗ CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
    CryptoVerification.LibsignalTripleRatchet.logOff img

/-- Register and state invariants at `main` entry: `w0 = argc`, initial file system, and empty trace. -/
def MainEntryFacts (i : Inputs) (s : State) : Prop :=
  (s.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
    s.fs = initFsState (cliInputs i) ∧ s.trace = []

/-- Postcondition of a normal return from `main`: `w0 = code`, committed writes applied in order, and stdout `out`. -/
def MainPost (r : MainResult) (s0 sf : State) : Prop :=
  ∃ code w out, r = .ret code w out ∧
    (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code ∧
    sf.fs.files = (writeAll s0.fs w).files ∧
    ProcessOutcome.traceStreamBytes .stdout sf.trace = out
where
  /-- Applies each `(path, bytes)` write in `ws` to `fs` in order. -/
  writeAll (fs : FsState) (ws : List (String × List (BitVec 8))) : FsState :=
    ws.foldl (fun fs w => fs.setFile w.1 (some (.file w.2))) fs

structure MainGhost where
  i : Inputs
  r : MainResult

/-- Subroutine contract for `main`: given `MainCase Run i r`, `CliInputsOk i`, `MainEntryFacts`, and `mainFrame`, normal return establishes `MainPost` (modulo `allocFailedIn`) while returning the stack frame, and `onPanic`/`onExit`/`onOom` allow allocation failure. -/
def mainSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → RunAnswer → Prop) : Spec MainGhost :=
  Spec.inImage
    { pre := fun g s => ⌜MainCaseB2 Run IsSendOverCap IsStdinOverCap g.i g.r ∧
        CliInputsOk g.i ∧ MainEntryFacts g.i s ∧
        stk ≤ s.sp.toNat⌝ ∗
        mainFrame A stk Statics g.i s
      post := fun g s0 sf => ⌜MainPost g.r s0 sf ∨ allocFailedIn s0 sf⌝ ∗
        stackAt s0.sp stk ∗ anyHeap
      onPanic := fun g s0 sf => ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
      onExit := fun _ _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap
      onOom := fun _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap }
    img

abbrev mainName : String := "main"

theorem main_fnOff : libsignalSessionCode.fnOff mainName = num% (ls_off% "main") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "main")

/-! ### Musl Startup and Exit -/

/-- Contract for musl's `_start` startup to `mainPc` and `exit_group` shutdown from `main`'s return, preserving the file system and trace and converting `w0` to `.Exited (signExtend 64 w0)`. -/
def MuslHarness (elf : ElfImage) (P : Program) (mainPc : BitVec 64) (Fr : SepProp)
    (Ok : Inputs → Prop) (MainPre : Inputs → State → SepProp) : Prop :=
  ElfStaticOk elf → ∀ i, Ok i → ∃ s0 sm,
    elf.loadState (cliInputs i) = .ok s0 ∧ Steps P s0 sm ∧
    sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
    sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
    (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
    (sm.mem ⊨ MainPre i sm ∗ Fr) ∧
    ∀ sr, Steps P sm sr → Returned sm sr → (sr.mem ⊨ stackAt sm.sp 48 ∗ Fr ∗ anyHeap) →
      ∃ sx, Steps P sr sx ∧
        sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
        sx.fs = sr.fs ∧ sx.trace = sr.trace

/-- Entry memory provided by `MuslHarness`: `img.FrozenLoaded` and `mainFrame` (without pinning `symtab`, which `outcome_of_main` swaps via `SymtabGhost`). -/
def mainEntryPre (img : Obj.Image) (A : RustAlloc) (stk : Nat) (Statics : SepProp)
    (i : Inputs) (s : State) : SepProp :=
  ⌜img.FrozenLoaded s ∧ stk ≤ s.sp.toNat⌝ ∗ mainFrame A stk Statics i s

/-- Every PC in `[lo, hi)` has `P.externAt? pc = none`. -/
def MuslHookFree (P : Program) (lo hi : BitVec 64) : Prop :=
  ∀ pc, lo ≤ pc → pc < hi → (P.externAt? pc).isNone = true

/-! ### Process Composition -/

/-- Some execution of `P` from the loaded state on `i` records an allocation failure. -/
def RunAllocFails (elf : ElfImage) (P : Program) (i : Inputs) : Prop :=
  ∃ s0 s, elf.loadState (cliInputs i) = .ok s0 ∧ Steps P s0 s ∧ allocFailedEvent ∈ s.trace

/-- Relates a `MainResult` to the process-level `ProcessResult` (`abort` maps to `.aborted`; `ret code writes out` maps to exit `code`, stdout `out`, and `filesOf (files ++ writes)`). -/
def MainResult.Observed (files : List (String × List (BitVec 8))) :
    MainResult → ProcessResult → Prop
  | .abort, .aborted => True
  | .ret code w out, .exited c o fs =>
      c = BitVec.ofNat 64 code ∧ o = out ∧ fsView fs = filesOf (files ++ w)
  | _, _ => False

theorem loadState_fs_trace {elf : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h : elf.loadState inputs = .ok s0) : s0.fs = initFsState inputs ∧ s0.trace = [] := by
  dsimp only [ElfImage.loadState, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          exact ⟨rfl, rfl⟩

theorem mem_stdioPaths (q : String) :
    q ∈ stdioPaths ↔ q = "<stdin>" ∨ q = "<stdout>" ∨ q = "<stderr>" := by
  simp [stdioPaths]

theorem fsView_congr {fs fs' : FsState} (h : fs.files = fs'.files) :
    fsView fs = fsView fs' := by
  funext q
  simp only [fsView, h]

private theorem writeAll_entries_congr {a b : FsState}
    (ws : List (String × List (BitVec 8))) {k : FsPath} (h : a.entries k = b.entries k) :
    (MainPost.writeAll a ws).entries k = (MainPost.writeAll b ws).entries k := by
  induction ws generalizing a b with
  | nil => exact h
  | cons w ws ih =>
    apply ih
    simp only [FsState.setFile, FsState.setEntry]
    split
    · rfl
    · exact h

private theorem writeOk_disjoint_prefix {i : Inputs} {p p' : String}
    (hp : WriteOk i p) (hp' : WriteOk i p')
    {pref : FsPath} (hpref : pref ∈ (FsPath.nonEmptyPrefixes (normalizePath p')).dropLast) :
    pref ≠ normalizePath p := by
  intro heq
  have he : (initFsState (cliInputs i)).entries (normalizePath p) = some .dir :=
    heq ▸ hp'.2.2.2 pref hpref
  have hf : (initFsState (cliInputs i)).files p = some .dir := by
    rw [files_eq_entries]
    split
    · rfl
    · exact he
  exact hp.2.1 hf

private theorem sameFiles_setEntry_dir_right {a b : FsState} (h : SameFiles a b)
    {pref : FsPath} (hdir : a.entries pref = some .dir) :
    SameFiles a (b.setEntry pref (some .dir)) := by
  intro k
  simp only [FsState.setEntry]
  split
  · rename_i hk
    rw [beq_iff_eq.mp hk, hdir]
  · exact h k

private theorem sameFiles_foldl_dir_right {a b : FsState} (h : SameFiles a b)
    {l : List FsPath} (hl : ∀ pref ∈ l, a.entries pref = some .dir) :
    SameFiles a (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) b) := by
  induction l generalizing b with
  | nil => exact h
  | cons pref ls ih =>
    exact ih (sameFiles_setEntry_dir_right h (hl pref (.head _)))
      (fun p hp => hl p (.tail _ hp))

private theorem sameFiles_writeAll_filesFold {a b : FsState}
    (ws : List (String × List (BitVec 8))) (h : SameFiles a b)
    (hdir : ∀ w ∈ ws, ∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath w.1)).dropLast,
      a.entries pref = some .dir)
    (hne : ∀ w ∈ ws, ∀ w' ∈ ws,
      ∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath w'.1)).dropLast,
      pref ≠ normalizePath w.1) :
    SameFiles (MainPost.writeAll a ws) (filesFold ws b) := by
  induction ws generalizing a b with
  | nil => exact h
  | cons w ws ih =>
    obtain ⟨p, bs⟩ := w
    apply ih
    · exact (sameFiles_foldl_dir_right h (hdir (p, bs) (.head _))).setEntry
        (normalizePath p) (some (.file bs))
    · intro w' hw' pref hpref
      have hne' : pref ≠ normalizePath p := hne (p, bs) (.head _) w' (.tail _ hw') pref hpref
      simp only [FsState.setFile, FsState.setEntry]
      split
      · rename_i heq
        exact absurd (beq_iff_eq.mp heq) hne'
      · exact hdir w' (.tail _ hw') pref hpref
    · intro w1 hw1 w2 hw2 pref hpref
      exact hne w1 (.tail _ hw1) w2 (.tail _ hw2) pref hpref

private theorem filesFold_append (xs ys : List (String × List (BitVec 8))) (a : FsState) :
    filesFold (xs ++ ys) a = filesFold ys (filesFold xs a) := by
  unfold filesFold
  rw [List.foldl_append]

/-- `fsView` after applying valid writes `ws` to `initFsState (cliInputs i)` equals `filesOf (i.files ++ ws)`. -/
theorem fsView_writeAll_initFsState (i : Inputs) (ws : List (String × List (BitVec 8)))
    (hw : ∀ pw ∈ ws, WriteOk i pw.1) :
    fsView (MainPost.writeAll (initFsState (cliInputs i)) ws) = filesOf (i.files ++ ws) := by
  funext q
  unfold filesOf fsView
  split
  · rfl
  · rename_i hq
    show fileOfEntry ((MainPost.writeAll (initFsState (cliInputs i)) ws).files q) =
      fileOfEntry ((initFsState { files := i.files ++ ws }).files q)
    simp only [FsState.files, FsState.getEntry]
    split
    · rfl
    · rw [writeAll_entries_congr ws (initFsState_entries (cliInputs i) (normalizePath q) hq),
        initFsState_entries { files := i.files ++ ws } (normalizePath q) hq,
        filesFold_append]
      exact sameFiles_writeAll_filesFold ws
        (SameFiles.filesFold_same
          (NoFiles.sameFiles (NoFiles.dirsFold_none i.dirs) (NoFiles.dirsFold_none [])) i.files)
        (fun w hw_mem pref hpref => (hw w hw_mem).2.2.2 pref hpref)
        (fun w hw1 w' hw2 _ hpref => writeOk_disjoint_prefix (hw w hw1) (hw w' hw2) hpref)
        (normalizePath q)

theorem signExtend_ofNat_small {code : Nat} (h : code ≤ 2) :
    (BitVec.ofNat 32 code).signExtend 64 = BitVec.ofNat 64 code := by
  rcases (by omega : code = 0 ∨ code = 1 ∨ code = 2) with rfl | rfl | rfl <;> decide

theorem exit_frame {m : Memory} {sp : BitVec 64} {stk : Nat} {Fr : SepProp}
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64) (h : m ⊨ (stackAt sp stk ∗ anyHeap) ∗ Fr) :
    m ⊨ stackAt sp 48 ∗ Fr ∗ anyHeap := by
  have hsplit := stackAt_split_bottom sp 48 (stk - 48) (by omega)
  rw [show 48 + (stk - 48) = stk by omega] at hsplit
  rw [hsplit] at h
  refine Satisfies.mono ?_ h
  have e : ((memRegion (sp - BitVec.ofNat 64 stk) (stk - 48) ∗ stackAt sp 48) ∗ anyHeap) ∗ Fr =
      stackAt sp 48 ∗ Fr ∗ (memRegion (sp - BitVec.ofNat 64 stk) (stk - 48) ∗ anyHeap) := by
    ac_rfl
  rw [e]
  exact sepConj_mono_right (sepConj_mono_right (entails_anyHeap _))

/-- Composes `MuslHarness`, `SymtabGhost`, and `mainSpec` to establish `MainResult.Observed` (or `RunAllocFails`) for `outcomeOf elf P (cliInputs i)`. -/
theorem outcome_of_main {elf : ElfImage} {img : Obj.Image} {ext : String → Option (State → State)}
    {A : RustAlloc} {stk : Nat} {Statics Fr : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hE : ElfStaticOk elf)
    (hH : MuslHarness elf (cliProg img ext) (entryOf img mainName) Fr
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPre img A stk Statics))
    (hG : SymtabGhost (cliProg img ext))
    (hmain : subroutine_ok (cliProg img ext) (entryOf img mainName)
      (mainSpec A img stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    (∃ res, outcomeOf elf (cliProg img ext) (cliInputs i) = some res ∧
      MainResult.Observed i.files r res) ∨
    RunAllocFails elf (cliProg img ext) i := by
  obtain ⟨s0, sm, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ := hH hE i ⟨hi, hl⟩
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [mainEntryPre, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hFL, hsp⟩, hmem⟩ := hmem
  -- `main`'s entry state with the image's symbol table.
  let sm' : State := { sm with symtab := img.symtab }
  have hpre : sm'.mem ⊨ (mainSpec A img stk Statics Run).pre ⟨i, r⟩ sm' ∗ Fr := by
    simp only [mainSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    have hentry : MainEntryFacts i sm' := by
      unfold MainEntryFacts; exact ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩
    exact ⟨⟨hFL.of_mem_eq rfl, rfl⟩, ⟨hc, hi, hentry, hsp⟩, hmem⟩
  have hcode : (cliProg img ext).CodeLoaded sm'.mem := hFL.codeLoaded_ofImage _ _
  obtain ⟨sf', hsteps1', hout, _⟩ := hmain.no_fault_before_outcome ⟨i, r⟩ Fr sm' hpc hrun hpre hal hcode
  -- Back to the loader's symbol table.
  let sf : State := { sf' with symtab := sm.symtab }
  have hsteps1 : Steps (cliProg img ext) sm sf := by
    have h := hG sm.symtab hsteps1'
    exact h
  have hsteps01 := hsteps0.trans hsteps1
  have hAF : allocFailedIn sm' sf' → RunAllocFails elf (cliProg img ext) i :=
    fun h => ⟨s0, sf, hload, hsteps01, List.mem_of_mem_drop h⟩
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨c, hex, hpost⟩ | ⟨hoom, hpost⟩
  ·
    simp only [mainSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hφ, hpost⟩ := hpost
    rcases hφ with ⟨code, w, out, rfl, hw0, hfiles, hout⟩ | hA
    · rw [← sepConj_assoc] at hpost
      have hret' : Returned sm sf := hret
      obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
        hexit sf hsteps1 hret' (exit_frame hstk hstk' hpost)
      have hle := hc.code_le rfl
      have hw0' : (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code := hw0
      have hfiles' : sf.fs.files = (MainPost.writeAll sm'.fs w).files := hfiles
      have hout' : ProcessOutcome.traceStreamBytes .stdout sf.trace = out := hout
      refine Or.inl ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
      dsimp only [MainResult.Observed]
      refine ⟨?_, ?_, ?_⟩
      · rw [hw0', signExtend_ofNat_small hle]
      · rw [htrx, hout']
      · rw [hfsx, fsView_congr hfiles']
        change fsView (MainPost.writeAll sm.fs w) = _
        rw [hfs, hfs0]
        exact fsView_writeAll_initFsState i w hc.commitOk
    · exact Or.inr (hAF hA)
  ·
    simp only [mainSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hpan' : sf.status = .Panicked := hpan
    rcases hpost.1 with rfl | hA
    · exact Or.inl ⟨_, outcomeOf_eq_aborted hload hsteps01 hpan', trivial⟩
    · exact Or.inr (hAF hA)
  ·
    simp only [mainSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inr (hAF hpost.1)
  ·
    simp only [mainSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inr (hAF hpost.1)

/-- Specialization of `outcome_of_main` to `cliExterns W`, discharging `SymtabGhost` via `symtabGhost_ofImage_cliExterns`. -/
theorem outcome_of_main_cliExterns {elf : ElfImage} {img : Obj.Image} {W : CliHooks}
    {A : RustAlloc} {stk : Nat} {Statics Fr : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hE : ElfStaticOk elf)
    (hH : MuslHarness elf (cliProg img (cliExterns W)) (entryOf img mainName) Fr
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPre img A stk Statics))
    (hmain : subroutine_ok (cliProg img (cliExterns W)) (entryOf img mainName)
      (mainSpec A img stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    (∃ res, outcomeOf elf (cliProg img (cliExterns W)) (cliInputs i) = some res ∧
      MainResult.Observed i.files r res) ∨
    RunAllocFails elf (cliProg img (cliExterns W)) i :=
  outcome_of_main hE hH (symtabGhost_ofImage_cliExterns img W) hmain hstk hstk' hi hl hc
/-- Tightened `main` contract under panic-on-OOM hooks: allocation failure routes exclusively to `onPanic`, normal return establishes `MainPost`, and `onExit`/`onOom` are `False`. -/
def mainSpecTight (A : RustAlloc) (img : Obj.Image) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → RunAnswer → Prop) : Spec MainGhost :=
  Spec.inImage
    { pre := fun g s => ⌜MainCaseB2 Run IsSendOverCap IsStdinOverCap g.i g.r ∧
        CliInputsOk g.i ∧ MainEntryFacts g.i s ∧
        stk ≤ s.sp.toNat⌝ ∗
        mainFrame A stk Statics g.i s
      post := fun g s0 sf => ⌜MainPost g.r s0 sf⌝ ∗
        stackAt s0.sp stk ∗ anyHeap
      onPanic := fun g s0 sf => ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
      onExit := fun _ _ _ _ => ⌜False⌝
      onOom := fun _ _ _ => ⌜False⌝ }
    img

theorem subroutine_ok_mainSpec_of_tight {P : Program} {e : BitVec 64}
    {A : RustAlloc} {img : Obj.Image} {stk : Nat} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (h : subroutine_ok P e (mainSpecTight A img stk Statics Run)) :
    subroutine_ok P e (mainSpec A img stk Statics Run) := by
  refine subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun g R s0 sf hp => ?_)
    (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ he => (not_satisfies_false_sepConj he).elim)
    (fun _ _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
  simp only [mainSpecTight, mainSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨Or.inl hp.1, hp.2⟩

/-- Composes `MuslHarness`, `SymtabGhost`, and `mainSpecTight`: either the binary produces `MainResult.Observed`, or it aborts with `RunAllocFails`. -/
theorem outcome_of_main_or_oom {elf : ElfImage} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {A : RustAlloc} {stk : Nat} {Statics Fr : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hE : ElfStaticOk elf)
    (hH : MuslHarness elf (cliProg img ext) (entryOf img mainName) Fr
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPre img A stk Statics))
    (hG : SymtabGhost (cliProg img ext))
    (hmain : subroutine_ok (cliProg img ext) (entryOf img mainName)
      (mainSpecTight A img stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    (∃ res, outcomeOf elf (cliProg img ext) (cliInputs i) = some res ∧
      MainResult.Observed i.files r res) ∨
    (outcomeOf elf (cliProg img ext) (cliInputs i) = some .aborted ∧
      RunAllocFails elf (cliProg img ext) i) := by
  obtain ⟨s0, sm, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ := hH hE i ⟨hi, hl⟩
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [mainEntryPre, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hFL, hsp⟩, hmem⟩ := hmem
  let sm' : State := { sm with symtab := img.symtab }
  have hpre : sm'.mem ⊨ (mainSpecTight A img stk Statics Run).pre ⟨i, r⟩ sm' ∗ Fr := by
    simp only [mainSpecTight, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    have hentry : MainEntryFacts i sm' := by
      unfold MainEntryFacts; exact ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩
    exact ⟨⟨hFL.of_mem_eq rfl, rfl⟩, ⟨hc, hi, hentry, hsp⟩, hmem⟩
  have hcode : (cliProg img ext).CodeLoaded sm'.mem := hFL.codeLoaded_ofImage _ _
  obtain ⟨sf', hsteps1', hout, _⟩ := hmain.no_fault_before_outcome ⟨i, r⟩ Fr sm' hpc hrun hpre hal hcode
  let sf : State := { sf' with symtab := sm.symtab }
  have hsteps1 : Steps (cliProg img ext) sm sf := by
    have h := hG sm.symtab hsteps1'
    exact h
  have hsteps01 := hsteps0.trans hsteps1
  have hAF : allocFailedIn sm' sf' → RunAllocFails elf (cliProg img ext) i :=
    fun h => ⟨s0, sf, hload, hsteps01, List.mem_of_mem_drop h⟩
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  ·
    simp only [mainSpecTight, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨code, w, out, rfl, hw0, hfiles, hout⟩, hpost⟩ := hpost
    rw [← sepConj_assoc] at hpost
    have hret' : Returned sm sf := hret
    obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
      hexit sf hsteps1 hret' (exit_frame hstk hstk' hpost)
    have hle := hc.code_le rfl
    have hw0' : (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code := hw0
    have hfiles' : sf.fs.files = (MainPost.writeAll sm'.fs w).files := hfiles
    have hout' : ProcessOutcome.traceStreamBytes .stdout sf.trace = out := hout
    refine Or.inl ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
    dsimp only [MainResult.Observed]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw0', signExtend_ofNat_small hle]
    · rw [htrx, hout']
    · rw [hfsx, fsView_congr hfiles']
      change fsView (MainPost.writeAll sm.fs w) = _
      rw [hfs, hfs0]
      exact fsView_writeAll_initFsState i w hc.commitOk
  ·
    simp only [mainSpecTight, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hpan' : sf.status = .Panicked := hpan
    have habort := outcomeOf_eq_aborted hload hsteps01 hpan'
    rcases hpost.1 with rfl | hA
    · exact Or.inl ⟨_, habort, trivial⟩
    · exact Or.inr ⟨habort, hAF hA⟩
  ·
    exact (not_satisfies_false_sepConj hpost).elim
  ·
    exact (not_satisfies_false_sepConj hpost).elim

/-- Specialization of `outcome_of_main_or_oom` to `cliExterns W`, discharging `SymtabGhost` via `symtabGhost_ofImage_cliExterns`. -/
theorem outcome_of_main_cliExterns_or_oom {elf : ElfImage} {img : Obj.Image} {W : CliHooks}
    {A : RustAlloc} {stk : Nat} {Statics Fr : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hE : ElfStaticOk elf)
    (hH : MuslHarness elf (cliProg img (cliExterns W)) (entryOf img mainName) Fr
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPre img A stk Statics))
    (hmain : subroutine_ok (cliProg img (cliExterns W)) (entryOf img mainName)
      (mainSpecTight A img stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    (∃ res, outcomeOf elf (cliProg img (cliExterns W)) (cliInputs i) = some res ∧
      MainResult.Observed i.files r res) ∨
    (outcomeOf elf (cliProg img (cliExterns W)) (cliInputs i) = some .aborted ∧
      RunAllocFails elf (cliProg img (cliExterns W)) i) :=
  outcome_of_main_or_oom hE hH (symtabGhost_ofImage_cliExterns img W) hmain hstk hstk' hi hl hc
/-- Under `MainResult.Observed`, `toOutcome` of `MainResult.ofAnswer a` equals `observe files a`. -/
theorem MainResult.observed_ofAnswer (files : List (String × List (BitVec 8))) (a : RunAnswer)
    (res : ProcessResult) (h : MainResult.Observed files (MainResult.ofAnswer a) res) :
    toOutcome res = observe files a := by
  cases a with
  | none =>
    cases res with
    | exited _ _ _ => cases h
    | aborted => rfl
  | some a' =>
    cases a' with
    | none =>
      cases res with
      | exited c o fs =>
        obtain ⟨rfl, rfl, hfs⟩ := h
        simp only [toOutcome, observe, List.append_nil] at hfs ⊢
        rw [hfs]
        rfl
      | aborted => cases h
    | some p =>
      obtain ⟨w, out⟩ := p
      cases res with
      | exited c o fs =>
        obtain ⟨rfl, rfl, hfs⟩ := h
        simp only [toOutcome, observe]
        rw [hfs]
        rfl
      | aborted => cases h

theorem MainResult.observed_usage (files : List (String × List (BitVec 8))) (res : ProcessResult)
    (h : MainResult.Observed files (.ret 2 [] []) res) :
    toOutcome res = .exited 2 [] (filesOf files) := by
  cases res with
  | exited c o fs =>
    obtain ⟨rfl, rfl, hfs⟩ := h
    simp only [toOutcome, List.append_nil] at hfs ⊢
    rw [hfs]
    rfl
  | aborted => cases h

theorem MainResult.observed_sendOverCap (files : List (String × List (BitVec 8)))
    (res : ProcessResult) (h : MainResult.Observed files (.ret 1 [] []) res) :
    toOutcome res = .exited 1 [] (filesOf files) :=
  MainResult.observed_ofAnswer files (some none) res h

end CryptoVerification.SignalSession.Cli
