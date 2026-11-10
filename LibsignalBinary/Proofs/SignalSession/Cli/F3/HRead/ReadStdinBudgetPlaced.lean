/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1PlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budgeted `read_stdin` and `.rodata` `read_file` Ghost Hooks

Defines `CompiledReadStdinEnv` and `readStdinBudgetEvents` across both `bs.length ≤ 1048576` and
`1048576 < bs.length`, lifts `readStdinBudgetCondSpec` to `readStdinSpecOfPlaced` and
`readStdinSpecPlaced`, constructs call-entry (`readStdinGhostHook`) and `stripS keep`
(`readStdinLinkedGhostHook`, `readFileFullLinkedGhostHook`) ghost hooks with `GhostExternReplays`,
and derives `MainIoPlaced ∧ MainIoBoundedPlaced` on `withReadHooks rfh rsh`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced

open scoped CryptoVerification.RustHeap
open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement LsBlockBound
   libsignalMutatedBlocks libsignalSessionExterns ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_rocl_of_plain withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName memmoveName memsetName)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced cliHookTablePlaced cliPanicSymbolsPlaced isCliPanicSymbolPlaced
   lsFromUtf8Sym lsMemrchrSym lsReadFileSym lsReadStdinSym lsWriteFileSym lsWriteStdoutSym
   readStdinResult writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli (ReadFileGhost ioVecAt)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (IoModel ReadFileLitGhost ReadStdinGhost cliExternsPlaced_writeFile cliExternsPlaced_writeStdout
   cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks FsTHooks IsFsC cliGhostExterns cliGhostExterns_other)
open CryptoVerification.SignalSession.CliExt (ReadFileCall bytesAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (ReadFileEnv ReadStdinEnv cliIoCap cliIoCapIdx cliIoCapsEvents cliIoReadScheduleCaps
   vmPreserved_writeFileHook vmPreserved_writeStdoutHook writeFileEnv_nil writeStdoutEnv_nil)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (BaseHelperRows CliGhostAllocHooks CliGhostSpqrAllocHooks ExecFrozen GhostExternReplays
   StubReachesTarget allocContractsFsPlaced_of_ghost allocContractsXCliPlaced_of_ghost
   cliExternsPlaced_baseHelperRows fsTHooks_cliGhostExterns satisfies_of_stripExecOutside
   satisfies_stripExecOutside stepsUntil_of_stripS_standard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (AllocCapNullInEvents CallerLrUnmapped CliIoFilesOomPreserved FdsGe3Closed OverCapFile
   ReadFileRuleEnvFixed allocFd_ne_none_of_fdsGe3Closed fitsEvents_readFile_of_fitsEnv_not_overCap
   not_allocCapNullInEvents_of_fitsEvents readFileBudgetCondSpec readFileBudgetEvents
   readFileRuleEnv_events_of_not_overCap withReadFileHook withReadFileHook_ne withReadFileHook_self)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoBoundedPlaced MainIoOfPlaced ReadStdinBoundedEnv mainIoBoundedPlaced_iff_mainIoPlaced
   readStdinSpecOfPlaced readStdinSpecOfPlaced_eq_readStdinSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced MainIoPlaced ReadFileRuleEnv
   readFileLitSpecPlaced readFileSpecPlaced readStdinSpecPlaced writeFileSpecPlaced
   writeStdoutSpecPlaced)

/-! ## `CompiledReadStdinEnv` and `readStdinBudgetEvents` -/

/-- Allocator event list emitted by compiled `signal_session_io::read_stdin` on the over-cap
    (`1048576 < bs.length`) `vecErr` / exit-`2` path (`9`-cap doubling growth up to `1 MiB`, followed
    by freeing the `1 MiB` buffer before returning `Err(IoError)`). -/
def readStdinOverCapEvents : List AllocEvent :=
  cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 1048576) ++ rustDeallocEvents 1048576 1

/-- Deterministic allocator event list of compiled `signal_session_io::read_stdin` across all inputs
    `bs : List (BitVec 8)` (both `bs.length ≤ 1048576` and `1048576 < bs.length`). -/
def readStdinBudgetEvents (bs : List (BitVec 8)) : List AllocEvent :=
  if bs.length ≤ 1048576 then
    cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 bs.length)
  else
    readStdinOverCapEvents

/-- Exact allocator-event envelope of compiled `signal_session_io::read_stdin` (`9`-cap doubling
    schedule `4 KiB .. 1 MiB` on `bs.length ≤ 1048576`, plus over-cap `rustDeallocEvents 1048576 1`
    on `1048576 < bs.length`; definitionally identical to `B2MainRemainingHopsInst.CompiledReadStdinEnv`). -/
def CompiledReadStdinEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  (bs.length ≤ 1048576 ∧ evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 bs.length)) ∨
  (1048576 < bs.length ∧
    evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 1048576) ++ rustDeallocEvents 1048576 1)

/-- `readStdinBudgetEvents bs` inhabits `CompiledReadStdinEnv bs` across both within-cap
(`bs.length ≤ 1048576`) and over-cap (`1048576 < bs.length`) stdin inputs. -/
theorem compiledReadStdinEnv_events (bs : List (BitVec 8)) :
    CompiledReadStdinEnv bs (readStdinBudgetEvents bs) := by
  unfold readStdinBudgetEvents readStdinOverCapEvents
  by_cases hle : bs.length ≤ 1048576
  · simp only [hle, ↓reduceIte]
    exact Or.inl ⟨hle, rfl⟩
  · simp only [hle, ↓reduceIte]
    exact Or.inr ⟨Nat.lt_of_not_ge hle, rfl⟩

theorem compiledReadStdinEnv_cliIoCaps8_ok {bs : List (BitVec 8)} (hle : bs.length ≤ 1048576) :
    CompiledReadStdinEnv bs (cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 bs.length)) :=
  Or.inl ⟨hle, rfl⟩

theorem compiledReadStdinEnv_cliIoCaps8_overCap {bs : List (BitVec 8)} (hgt : 1048576 < bs.length) :
    CompiledReadStdinEnv bs
      (cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 bs.length) ++ rustDeallocEvents 1048576 1) := by
  have h8 : cliIoCapIdx 8 bs.length = 8 := by
    unfold cliIoCapIdx
    simp only [show ¬ bs.length ≤ cliIoCap 7 by change ¬ bs.length ≤ 524288; omega, ↓reduceIte]
  have hcap : cliIoReadScheduleCaps 8 bs.length = cliIoReadScheduleCaps 8 1048576 := by
    unfold cliIoReadScheduleCaps
    simp only [show bs.length ≠ 0 by omega, h8, ↓reduceIte]
    rfl
  rw [hcap]
  exact Or.inr ⟨hgt, rfl⟩

theorem compiledReadStdinEnv_sub_bounded {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : CompiledReadStdinEnv bs evs) : ReadStdinBoundedEnv bs evs :=
  Or.inr h

theorem compiledReadStdinEnv_sub_readStdinEnv {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : CompiledReadStdinEnv bs evs) : ReadStdinEnv bs evs :=
  Or.inr h

theorem readStdinBoundedEnv_events (bs : List (BitVec 8)) :
    ReadStdinBoundedEnv bs (readStdinBudgetEvents bs) :=
  compiledReadStdinEnv_sub_bounded (compiledReadStdinEnv_events bs)

theorem readStdinEnv_events (bs : List (BitVec 8)) :
    ReadStdinEnv bs (readStdinBudgetEvents bs) :=
  compiledReadStdinEnv_sub_readStdinEnv (compiledReadStdinEnv_events bs)

theorem fitsEnv_compiled_of_sub {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {bs : List (BitVec 8)} {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hsub : ∀ evs, CompiledReadStdinEnv bs evs → StdinEnv bs evs)
    (h : FitsEnv M lim st (StdinEnv bs)) :
    FitsEnv M lim st (CompiledReadStdinEnv bs) :=
  fun evs hevs => h evs (hsub evs hevs)

theorem fitsEvents_readStdin_of_fitsEnv_compiled {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {bs : List (BitVec 8)}
    (h : FitsEnv M lim st (CompiledReadStdinEnv bs)) :
    FitsEvents M lim st (readStdinBudgetEvents bs) :=
  h (readStdinBudgetEvents bs) (compiledReadStdinEnv_events bs)

theorem fitsEvents_readStdin_of_fitsEnv_bounded {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {bs : List (BitVec 8)}
    (h : FitsEnv M lim st (ReadStdinBoundedEnv bs)) :
    FitsEvents M lim st (readStdinBudgetEvents bs) :=
  h (readStdinBudgetEvents bs) (readStdinBoundedEnv_events bs)

theorem fitsEvents_readStdin_of_fitsEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {bs : List (BitVec 8)}
    (h : FitsEnv M lim st (ReadStdinEnv bs)) :
    FitsEvents M lim st (readStdinBudgetEvents bs) :=
  h (readStdinBudgetEvents bs) (readStdinEnv_events bs)

/-! ## Conditional-OOM to `readStdinSpecOfPlaced` and `readFileAny*` Lifts -/

private theorem stackAt_le_two_pow_64_of_sep {m : Memory} {p sp : BitVec 64} {n stk : Nat}
    {R : SepProp} (hn : 0 < n) (hstk : 0 < stk)
    (h : m ⊨ memRegion p n ∗ (stackAt sp stk ∗ R)) : stk ≤ 2 ^ 64 := by
  have hdisj := (IsBlock.memRegion p n).disjoint
    (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) hn hstk h
  have hlt := (p - (sp - BitVec.ofNat 64 stk)).isLt
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hdisj.2 hlt)

/-- Conditional-OOM budget-threaded contract for compiled `signal_session_io::read_stdin`: reads
`fd 0` while preserving `FdsGe3Closed`, `fs.files`, and `trace` across both `bs.length ≤ 1048576`
and `1048576 < bs.length`. -/
def readStdinBudgetCondSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (ReadStdinGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.ret ∧ cliIo.stdin s.fs = some x.bs⌝ ∗
      memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    let evs := readStdinBudgetEvents x.bs
    ⌜sf.fs.files = s0.fs.files ∧ sf.trace = s0.trace ∧
      (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs)⌝ ∗
      ioVecAt A.repAlloc x.ret (readStdinResult x.bs) ∗
      stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf
  onPanic := fun (x, _) s0 sf =>
    ⌜AllocCapNullInEvents (readStdinBudgetEvents x.bs) ∧
      sf.fs.files = s0.fs.files ∧ sf.trace = s0.trace⌝ ∗ anyHeap
  onOom := fun (x, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (readStdinBudgetEvents x.bs) ∧
      CliIoFilesOomPreserved s0 sf⌝

/-- Deterministic-event `NoOom` specialization of `readStdinBudgetCondSpec` under
    `FitsEvents M lim st (readStdinBudgetEvents x.bs)` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def readStdinBudgetNoOomSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (ReadStdinGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.ret ∧ cliIo.stdin s.fs = some x.bs ∧
      FitsEvents M lim st (readStdinBudgetEvents x.bs)⌝ ∗
      memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    let evs := readStdinBudgetEvents x.bs
    ⌜sf.fs.files = s0.fs.files ∧ sf.trace = s0.trace ∧
      (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs)⌝ ∗
      ioVecAt A.repAlloc x.ret (readStdinResult x.bs) ∗
      stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

/-- Stack-budget widening for `readStdinBudgetCondSpec`: lifts `extHookStack` (`16384`) to any
    `stk ≥ extHookStack` (deriving `stk ≤ 2 ^ 64` from `memRegion x.ret 24 ∗ stackAt s0.sp stk`). -/
theorem subroutine_ok_readStdinBudgetCondSpec_of_extHookStack {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {entry : BitVec 64}
    (hstk : extHookStack ≤ stk)
    (h : subroutine_ok P entry (readStdinBudgetCondSpec A lim extHookStack)) :
    subroutine_ok P entry (readStdinBudgetCondSpec A lim stk) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [readStdinBudgetCondSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hstdin⟩, hmem⟩
  have hmem_disj : s0.mem ⊨ memRegion x.ret 24 ∗
      (stackAt s0.sp stk ∗ (A.pool lim st s0 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hpos_ext : 0 < extHookStack := by unfold extHookStack; omega
  have hstk64 : stk ≤ 2 ^ 64 :=
    stackAt_le_two_pow_64_of_sep (by omega) (Nat.lt_of_lt_of_le hpos_ext hstk) hmem_disj
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ stackAt s0.sp extHookStack := by
    have hs := stackAt_split_bottom s0.sp extHookStack (stk - extHookStack) (by omega)
    rwa [Nat.add_sub_of_le hstk] at hs
  let F : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack)
  have hpreE : s0.mem ⊨ (readStdinBudgetCondSpec A lim extHookStack).pre (x, st) s0 ∗ (F ∗ R) := by
    dsimp only [readStdinBudgetCondSpec, F]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx8, hstdin⟩, ?_⟩
    rw [hsplit] at hmem
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine subroutine_ok.mono_outcome h (x, st) (F ∗ R) s0 hpc hrun hpreE hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [readStdinBudgetCondSpec, F] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hp, ?_⟩)
    dsimp only [readStdinBudgetCondSpec, F] at hpan ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan ⊢
    refine ⟨hpan.1, ?_⟩
    have h1 : sf.mem ⊨ (anyHeap ∗ F) ∗ R :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpan.2
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) h1
  · dsimp only [readStdinBudgetCondSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    dsimp only [readStdinBudgetCondSpec, F] at hoom ⊢
    rw [satisfies_pure_sepConj] at hoom ⊢
    have hoomR : sf.mem ⊨ R ∗ F :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hoom.2
    exact ⟨hoom.1, Satisfies.of_sep_left hoomR⟩

/-- Lift `readStdinBudgetCondSpec` to `readStdinBudgetNoOomSpec`: `FitsEvents` discharges both
    `onPanic` (`AllocCapNullInEvents`) and `onOom` (`¬ FitsEvents`). -/
theorem subroutine_ok_readStdinNoOom_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (readStdinBudgetCondSpec A lim stk)) :
    subroutine_ok P entry (readStdinBudgetNoOomSpec A lim stk) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [readStdinBudgetNoOomSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hstdin, hFit⟩, hrest⟩
  have hpreC : s0.mem ⊨ (readStdinBudgetCondSpec A lim stk).pre (x, st) s0 ∗ R := by
    dsimp only [readStdinBudgetCondSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hstdin⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (x, st) R s0 hpc hrun hpreC hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨c, hc, hex⟩ | ⟨_, hoom⟩)
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exfalso
    dsimp only [readStdinBudgetCondSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact not_allocCapNullInEvents_of_fitsEvents hFit hpan.1.1
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exfalso
    dsimp only [readStdinBudgetCondSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.1 hFit

/-- Lift `readStdinBudgetCondSpec` unconditionally to `readStdinSpecOfPlaced` for any envelope
    `StdinEnv` containing `readStdinBudgetEvents bs` (including `CompiledReadStdinEnv`,
    `ReadStdinBoundedEnv`, and `ReadStdinEnv`). -/
theorem subroutine_ok_readStdinSpecOfPlaced_of_cond [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {P : Program} {entry : BitVec 64}
    (hEnv : ∀ bs, StdinEnv bs (readStdinBudgetEvents bs))
    (h : subroutine_ok P entry (readStdinBudgetCondSpec A lim stk)) :
    subroutine_ok P entry (readStdinSpecOfPlaced cliIo A lim stk StdinEnv) := by
  have hNoOom := subroutine_ok_readStdinNoOom_of_cond h
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [readStdinSpecOfPlaced] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hstdin, hFitsEnv, _hlr⟩, hrest⟩
  have hFit : FitsEvents M lim st (readStdinBudgetEvents x.bs) :=
    hFitsEnv (readStdinBudgetEvents x.bs) (hEnv x.bs)
  have hpreN : s0.mem ⊨ (readStdinBudgetNoOomSpec A lim stk).pre (x, st) s0 ∗ R := by
    dsimp only [readStdinBudgetNoOomSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hstdin, hFit⟩, hrest⟩
  refine subroutine_ok.mono_outcome hNoOom (x, st) R s0 hpc hrun hpreN hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [readStdinBudgetNoOomSpec] at hpost
    dsimp only [readStdinSpecOfPlaced]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hfiles, htr, _⟩, hmem⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨readStdinBudgetEvents x.bs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hEnv x.bs, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨readStdinResult x.bs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hfiles, rfl, htr⟩, by simpa only [sepConj_assoc] using hmem⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem HookOk.readStdin_mono_env [LibsignalPlacement] {M : AllocCostModel} {io : IoModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {StdinEnv₁ StdinEnv₂ : List (BitVec 8) → List AllocEvent → Prop}
    {f : State → State}
    (hsub : ∀ bs evs, StdinEnv₁ bs evs → StdinEnv₂ bs evs)
    (hok : HookOk f (readStdinSpecOfPlaced io A lim stk StdinEnv₁)) :
    HookOk f (readStdinSpecOfPlaced io A lim stk StdinEnv₂) := by
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hpre₁ : s0.mem ⊨ (readStdinSpecOfPlaced io A lim stk StdinEnv₁).pre (x, st) s0 ∗ R := by
    dsimp only [readStdinSpecOfPlaced] at hpre ⊢
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1,
      fun evs hevs => hpre.1.2.2.1 evs (hsub x.bs evs hevs), hpre.1.2.2.2⟩, hpre.2⟩
  obtain ⟨hkf, hsym, hout⟩ := hok (x, st) R s0 hrun hpre₁ hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [readStdinSpecOfPlaced] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    obtain ⟨evs, hpost⟩ := hpost
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hsub x.bs evs hpost.1, hpost.2⟩
  · exact Or.inr hrest

/-- Unified (`ro : Bool`) `read_file` specification at stack budget `stk`, covering both
`ro = false` (`↦ₛ`, `readFileSpecPlaced`) and `ro = true` (`↦ᵣ`, `readFileLitSpecPlaced`). -/
def readFileAnySpecPlaced {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv cliIo.rd) :
    Spec (ReadFileCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ cliIo.pathOk x.path ∧
      FitsEnv M lim st (ReadEnv s.fs.files x.path)⌝ ∗
      bytesAt x.ro x.pathA x.path ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ReadEnv s0.fs.files x.path evs⌝ ∗
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜sf.fs.files = s0.fs.files ∧ r = cliIo.rd s0.fs.files x.path ∧ sf.trace = s0.trace⌝ ∗
            ioVecAt A.repAlloc x.ret r) ∗
        bytesAt x.ro x.pathA x.path ∗ stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

/-- Conditional-OOM budget-threaded contract for compiled `signal_session_io::read_file`
    parameterized by `x : ReadFileCall` (`ro = false` for `↦ₛ`, `ro = true` for `.rodata` `↦ᵣ`)
    under `cliIo.pathOk x.path` and `s.fs.allocFd ≠ none`. -/
def readFileAnyBudgetCondSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (ReadFileCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ cliIo.pathOk x.path ∧
      s.fs.allocFd ≠ none⌝ ∗
      bytesAt x.ro x.pathA x.path ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    let evs := readFileBudgetEvents s0.fs.files x.path
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      ioVecAt A.repAlloc x.ret (cliIo.rd s0.fs.files x.path) ∗
      bytesAt x.ro x.pathA x.path ∗ stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf
  onPanic := fun (x, _) s0 sf =>
    ⌜AllocCapNullInEvents (readFileBudgetEvents s0.fs.files x.path) ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ anyHeap
  onOom := fun (x, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (readFileBudgetEvents s0.fs.files x.path) ∧
      CliIoFilesOomPreserved s0 sf⌝

def readFileAnyBudgetNoOomSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (ReadFileCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ cliIo.pathOk x.path ∧
      s.fs.allocFd ≠ none ∧
      FitsEvents M lim st (readFileBudgetEvents s.fs.files x.path)⌝ ∗
      bytesAt x.ro x.pathA x.path ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    let evs := readFileBudgetEvents s0.fs.files x.path
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      ioVecAt A.repAlloc x.ret (cliIo.rd s0.fs.files x.path) ∗
      bytesAt x.ro x.pathA x.path ∗ stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

theorem subroutine_ok_readFileAnyBudgetCondSpec_of_extHookStack {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {entry : BitVec 64}
    (hstk : extHookStack ≤ stk)
    (h : subroutine_ok P entry (readFileAnyBudgetCondSpec A lim extHookStack)) :
    subroutine_ok P entry (readFileAnyBudgetCondSpec A lim stk) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [readFileAnyBudgetCondSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  have hmem_disj : s0.mem ⊨ memRegion x.ret 24 ∗
      (stackAt s0.sp stk ∗ (bytesAt x.ro x.pathA x.path ∗ A.pool lim st s0 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hpos_ext : 0 < extHookStack := by unfold extHookStack; omega
  have hstk64 : stk ≤ 2 ^ 64 :=
    stackAt_le_two_pow_64_of_sep (by omega) (Nat.lt_of_lt_of_le hpos_ext hstk) hmem_disj
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ stackAt s0.sp extHookStack := by
    have hs := stackAt_split_bottom s0.sp extHookStack (stk - extHookStack) (by omega)
    rwa [Nat.add_sub_of_le hstk] at hs
  let F : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack)
  have hpreE : s0.mem ⊨ (readFileAnyBudgetCondSpec A lim extHookStack).pre (x, st) s0 ∗ (F ∗ R) := by
    dsimp only [readFileAnyBudgetCondSpec, F]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpure, ?_⟩
    rw [hsplit] at hmem
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine subroutine_ok.mono_outcome h (x, st) (F ∗ R) s0 hpc hrun hpreE hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [readFileAnyBudgetCondSpec, F] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hp, ?_⟩)
    dsimp only [readFileAnyBudgetCondSpec, F] at hpan ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan ⊢
    refine ⟨hpan.1, ?_⟩
    have h1 : sf.mem ⊨ (anyHeap ∗ F) ∗ R :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpan.2
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) h1
  · dsimp only [readFileAnyBudgetCondSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    dsimp only [readFileAnyBudgetCondSpec, F] at hoom ⊢
    rw [satisfies_pure_sepConj] at hoom ⊢
    have hoomR : sf.mem ⊨ R ∗ F :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hoom.2
    exact ⟨hoom.1, Satisfies.of_sep_left hoomR⟩

theorem subroutine_ok_readFileAnyNoOom_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (readFileAnyBudgetCondSpec A lim stk)) :
    subroutine_ok P entry (readFileAnyBudgetNoOomSpec A lim stk) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [readFileAnyBudgetNoOomSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlt32, hpok, hallocFd, hFit⟩, hrest⟩
  have hpreC : s0.mem ⊨ (readFileAnyBudgetCondSpec A lim stk).pre (x, st) s0 ∗ R := by
    dsimp only [readFileAnyBudgetCondSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt32, hpok, hallocFd⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (x, st) R s0 hpc hrun hpreC hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨c, hc, hex⟩ | ⟨_, hoom⟩)
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exfalso
    dsimp only [readFileAnyBudgetCondSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact not_allocCapNullInEvents_of_fitsEvents hFit hpan.1.1
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exfalso
    dsimp only [readFileAnyBudgetCondSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.1 hFit

theorem hookOk_readFileSpecPlaced_of_any {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {f : State → State}
    (hf : HookOk f (readFileAnySpecPlaced A lim stk ReadEnv)) :
    HookOk f (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv) := by
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  let y : ReadFileCall × M.σ := (⟨x.pathA, false, x.path, x.ret⟩, st)
  have hpreAny : s0.mem ⊨ (readFileAnySpecPlaced A lim stk ReadEnv).pre y s0 ∗ R := by
    dsimp only [readFileAnySpecPlaced, y, bytesAt]
    dsimp only [readFileSpecPlaced] at hpre
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, hpre.1.2.2.2.1, hpre.1.2.2.2.2.1.1,
      hpre.1.2.2.2.2.2⟩, hpre.2⟩
  obtain ⟨hkf, hsym, hout⟩ := hf y R s0 hrun hpreAny hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [readFileAnySpecPlaced, y, bytesAt] at hpost
    dsimp only [readFileSpecPlaced]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    obtain ⟨evs, hpost⟩ := hpost
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨hevs, hpost⟩ := hpost
    refine ⟨hevs, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists] at hpost ⊢
    obtain ⟨r, hpost⟩ := hpost
    refine ⟨r, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.2.1, hpost.1.2.2⟩, hpost.2⟩
  · dsimp only [readFileAnySpecPlaced] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [readFileAnySpecPlaced] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [readFileAnySpecPlaced] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem hookOk_readFileLitSpecPlaced_of_any {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {f : State → State}
    (hf : HookOk f (readFileAnySpecPlaced A lim stk ReadEnv)) :
    HookOk f (readFileLitSpecPlaced cliIo A lim stk ReadEnv) := by
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  let y : ReadFileCall × M.σ := (⟨x.pathA, true, x.path, x.ret⟩, st)
  have hpreAny : s0.mem ⊨ (readFileAnySpecPlaced A lim stk ReadEnv).pre y s0 ∗ R := by
    simpa only [readFileAnySpecPlaced, readFileLitSpecPlaced, y, bytesAt, ↓reduceIte] using hpre
  obtain ⟨hkf, hsym, hout⟩ := hf y R s0 hrun hpreAny hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨hret, hcc,
      by simpa only [readFileAnySpecPlaced, readFileLitSpecPlaced, y, bytesAt, ↓reduceIte] using hpost⟩
  · dsimp only [readFileAnySpecPlaced] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [readFileAnySpecPlaced] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [readFileAnySpecPlaced] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-! ## `withReadStdinHook` and `withReadHooks` Overlay -/

/-- `ext`-parametric `lsReadStdinSym` hook overlay (leaves every symbol `s ≠ lsReadStdinSym`
    equal to `ext s`). -/
def withReadStdinHook (rsh : State → State) (ext : LibsignalHooks) : LibsignalHooks :=
  fun s => if s == lsReadStdinSym then some rsh else ext s

/-- Combined `lsReadFileSym` + `lsReadStdinSym` ghost-hook overlay on `ext : LibsignalHooks`. -/
def withReadHooks (rfh rsh : State → State) (ext : LibsignalHooks) : LibsignalHooks :=
  withReadStdinHook rsh (withReadFileHook rfh ext)

@[simp]
theorem withReadStdinHook_self (rsh : State → State) (ext : LibsignalHooks) :
    withReadStdinHook rsh ext lsReadStdinSym = some rsh := by
  simp [withReadStdinHook]

theorem withReadStdinHook_ne (rsh : State → State) (ext : LibsignalHooks) {s : String}
    (hne : s ≠ lsReadStdinSym) :
    withReadStdinHook rsh ext s = ext s := by
  simp [withReadStdinHook, beq_eq_false_iff_ne.mpr hne]

@[simp]
theorem withReadHooks_readStdin (rfh rsh : State → State) (ext : LibsignalHooks) :
    withReadHooks rfh rsh ext lsReadStdinSym = some rsh :=
  withReadStdinHook_self rsh (withReadFileHook rfh ext)

@[simp]
theorem withReadHooks_readFile (rfh rsh : State → State) (ext : LibsignalHooks) :
    withReadHooks rfh rsh ext lsReadFileSym = some rfh := by
  unfold withReadHooks
  rw [withReadStdinHook_ne rsh _ (by decide), withReadFileHook_self]

theorem withReadHooks_other (rfh rsh : State → State) (ext : LibsignalHooks) {s : String}
    (hneStdin : s ≠ lsReadStdinSym) (hneFile : s ≠ lsReadFileSym) :
    withReadHooks rfh rsh ext s = ext s := by
  unfold withReadHooks
  rw [withReadStdinHook_ne rsh _ hneStdin, withReadFileHook_ne rfh ext hneFile]

@[simp]
theorem isPanicSymbol_lsReadStdinSym : Rust.isPanicSymbol lsReadStdinSym = false := by
  simp [Rust.isPanicSymbol, lsReadStdinSym]

@[simp]
theorem withPanics_lsReadStdinSym (ext : LibsignalHooks) :
    Rust.withPanics ext lsReadStdinSym = ext lsReadStdinSym := by
  simp [Rust.withPanics, isPanicSymbol_lsReadStdinSym]

@[simp]
theorem withPanics_withReadStdinHook (rsh : State → State) (ext : LibsignalHooks) :
    Rust.withPanics (withReadStdinHook rsh ext) = withReadStdinHook rsh (Rust.withPanics ext) := by
  funext s
  unfold Rust.withPanics withReadStdinHook
  by_cases hs : s = lsReadStdinSym
  · subst hs; simp [isPanicSymbol_lsReadStdinSym]
  · simp [beq_eq_false_iff_ne.mpr hs]

@[simp]
theorem withPanics_withReadHooks (rfh rsh : State → State) (ext : LibsignalHooks) :
    Rust.withPanics (withReadHooks rfh rsh ext) =
      withReadHooks rfh rsh (Rust.withPanics ext) := by
  simp [withReadHooks]

theorem hookSat_withReadHooks_readFile {α : Type} (rfh rsh : State → State) (ext : LibsignalHooks)
    {spec : Spec α} (hok : HookOk rfh spec) :
    HookSat (withReadHooks rfh rsh ext) lsReadFileSym spec :=
  ⟨rfh, withReadHooks_readFile rfh rsh ext, hok⟩

theorem hookSat_withPanics_withReadHooks_readFile {α : Type} (rfh rsh : State → State)
    (ext : LibsignalHooks) {spec : Spec α} (hok : HookOk rfh spec) :
    HookSat (Rust.withPanics (withReadHooks rfh rsh ext)) lsReadFileSym spec :=
  ⟨rfh, by simp, hok⟩

theorem hookSat_withReadHooks_readStdin {α : Type} (rfh rsh : State → State) (ext : LibsignalHooks)
    {spec : Spec α} (hok : HookOk rsh spec) :
    HookSat (withReadHooks rfh rsh ext) lsReadStdinSym spec :=
  ⟨rsh, withReadHooks_readStdin rfh rsh ext, hok⟩

/-- `cliExternsPlaced mmpl W` maps `lsReadFileSym` to `none`. -/
theorem cliExternsPlaced_readFile_none (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W lsReadFileSym = none := by
  have hp : isCliPanicSymbolPlaced lsReadFileSym = false := by
    simp [isCliPanicSymbolPlaced, cliPanicSymbolsPlaced, Rust.isPanicSymbol, lsReadFileSym]
  unfold cliExternsPlaced
  rw [hp]
  rfl

/-- `cliExternsPlaced mmpl W` maps `lsReadStdinSym` to `none`. -/
theorem cliExternsPlaced_readStdin_none (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W lsReadStdinSym = none := by
  have hp : isCliPanicSymbolPlaced lsReadStdinSym = false := by
    simp [isCliPanicSymbolPlaced, cliPanicSymbolsPlaced, Rust.isPanicSymbol, lsReadStdinSym]
  unfold cliExternsPlaced
  rw [hp]
  rfl

theorem cliGhostExterns_readFile_of_none (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hrf : g.readFile = none := by rfl) :
    cliGhostExterns g baseExt lsReadFileSym = baseExt lsReadFileSym :=
  CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_readFile_none g baseExt hrf

theorem cliGhostExterns_readStdin_of_none (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hrs : g.readStdin = none := by rfl) :
    cliGhostExterns g baseExt lsReadStdinSym = baseExt lsReadStdinSym :=
  CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_readStdin_none g baseExt hrs

theorem cliGhostExterns_readFile_none (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (g : CliGhostHooks) (hrf : g.readFile = none := by rfl) :
    cliGhostExterns g (cliExternsPlaced mmpl W) lsReadFileSym = none :=
  (cliGhostExterns_readFile_of_none g (cliExternsPlaced mmpl W) hrf).trans
    (cliExternsPlaced_readFile_none mmpl W)

theorem cliGhostExterns_readStdin_none (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (g : CliGhostHooks) (hrs : g.readStdin = none := by rfl) :
    cliGhostExterns g (cliExternsPlaced mmpl W) lsReadStdinSym = none :=
  (cliGhostExterns_readStdin_of_none g (cliExternsPlaced mmpl W) hrs).trans
    (cliExternsPlaced_readStdin_none mmpl W)

/-- Every symbol mapped to `none` in `withReadHooks rfh rsh ext` is mapped to `none` in `ext`. -/
theorem no_new_hooks_withReadHooks {rfh rsh : State → State} {ext realExt : LibsignalHooks}
    (h : ∀ sym, ext sym = none → realExt sym = none) :
    ∀ sym, withReadHooks rfh rsh ext sym = none → realExt sym = none := by
  intro sym hnone
  by_cases h1 : sym = lsReadStdinSym
  · subst h1; simp at hnone
  · by_cases h2 : sym = lsReadFileSym
    · subst h2; simp at hnone
    · rw [withReadHooks_other rfh rsh ext h1 h2] at hnone
      exact h sym hnone

/-- Every symbol mapped to `none` in `withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))`
is mapped to `none` in `cliExternsPlaced mmpl W`. -/
theorem no_new_hooks_ghost_to_real (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (rfh rsh : State → State) (g : CliGhostHooks) :
    ∀ sym,
      withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W)) sym = none →
      cliExternsPlaced mmpl W sym = none := by
  refine no_new_hooks_withReadHooks fun sym hnone => ?_
  unfold cliGhostExterns at hnone
  split at hnone
  · cases hnone
  · split at hnone
    · cases hnone
    · split at hnone
      · cases hnone
      · split at hnone
        · cases hnone
        · split at hnone
          · cases hnone
          · split at hnone
            · cases hsc : g.stringClone with
              | some _ => rw [hsc] at hnone; cases hnone
              | none => rw [hsc] at hnone; exact hnone
            · split at hnone
              · cases hrf : g.readFile with
                | some _ => rw [hrf] at hnone; cases hnone
                | none => rw [hrf] at hnone; exact hnone
              · split at hnone
                · cases hrs : g.readStdin with
                  | some _ => rw [hrs] at hnone; cases hnone
                  | none => rw [hrs] at hnone; exact hnone
                · split at hnone
                  · cases hms : g.memset with
                    | some _ => rw [hms] at hnone; cases hnone
                    | none => rw [hms] at hnone; exact hnone
                  · split at hnone
                    · cases hmc : g.memcpy with
                      | some _ => rw [hmc] at hnone; cases hnone
                      | none => rw [hmc] at hnone; exact hnone
                    · exact hnone

theorem baseHelperRows_withReadHooks {mmpl : Obj.MultiPlacement} {W : CliHooks}
    {baseExt : LibsignalHooks} (rfh rsh : State → State)
    (hBase : BaseHelperRows mmpl W baseExt) :
    BaseHelperRows mmpl W (withReadHooks rfh rsh baseExt) where
  memmove_eq := (withReadHooks_other rfh rsh baseExt (by decide) (by decide)).trans hBase.memmove_eq
  bcmp_eq := (withReadHooks_other rfh rsh baseExt (by decide) (by decide)).trans hBase.bcmp_eq
  utf8_eq := (withReadHooks_other rfh rsh baseExt (by decide) (by decide)).trans hBase.utf8_eq
  memrchr_eq := (withReadHooks_other rfh rsh baseExt (by decide) (by decide)).trans hBase.memrchr_eq
  panics := fun sym hmem => by
    have h1 : sym ≠ lsReadStdinSym := by intro he; subst he; exact nomatch hmem
    have h2 : sym ≠ lsReadFileSym := by intro he; subst he; exact nomatch hmem
    rw [withReadHooks_other rfh rsh baseExt h1 h2]
    exact hBase.panics sym hmem

theorem withReadHooks_cliGhostExterns_comm_strip (rfh rsh : State → State) (g : CliGhostHooks)
    (baseExt : LibsignalHooks) :
    withReadHooks rfh rsh (cliGhostExterns g baseExt) =
      cliGhostExterns { g with readFile := none, readStdin := none }
        (withReadHooks rfh rsh baseExt) := by
  funext sym
  by_cases h1 : sym = lsReadStdinSym
  · subst h1
    rw [withReadHooks_readStdin,
      cliGhostExterns_readStdin_of_none { g with readFile := none, readStdin := none } _ rfl,
      withReadHooks_readStdin]
  · by_cases h2 : sym = lsReadFileSym
    · subst h2
      rw [withReadHooks_readFile,
        cliGhostExterns_readFile_of_none { g with readFile := none, readStdin := none } _ rfl,
        withReadHooks_readFile]
    · rw [withReadHooks_other rfh rsh _ h1 h2]
      unfold cliGhostExterns
      dsimp only
      split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split
              · rfl
              · split
                · cases g.stringClone with
                  | some _ => rfl
                  | none => exact (withReadHooks_other rfh rsh baseExt h1 h2).symm
                · split
                  · exfalso; simp_all
                  · split
                    · exfalso; simp_all
                    · split
                      · cases g.memset with
                        | some _ => rfl
                        | none => exact (withReadHooks_other rfh rsh baseExt h1 h2).symm
                      · split
                        · cases g.memcpy with
                          | some _ => rfl
                          | none => exact (withReadHooks_other rfh rsh baseExt h1 h2).symm
                        · exact (withReadHooks_other rfh rsh baseExt h1 h2).symm

theorem withReadHooks_cliGhostExterns_comm (rfh rsh : State → State) (g : CliGhostHooks)
    (baseExt : LibsignalHooks)
    (hrf : g.readFile = none := by rfl) (hrs : g.readStdin = none := by rfl) :
    withReadHooks rfh rsh (cliGhostExterns g baseExt) =
      cliGhostExterns g (withReadHooks rfh rsh baseExt) := by
  have hge : { g with readFile := none, readStdin := none } = g := by
    cases g; simp_all
  simpa [hge] using withReadHooks_cliGhostExterns_comm_strip rfh rsh g baseExt

theorem allocContractsFsPlaced_withReadHooks_ghost [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (rfh rsh : State → State) (g : CliGhostHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    AllocContractsFsPlaced A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) := by
  rw [withReadHooks_cliGhostExterns_comm_strip]
  exact allocContractsFsPlaced_of_ghost mmpl W
    (withReadHooks rfh rsh (cliExternsPlaced mmpl W))
    { g with readFile := none, readStdin := none }
    (baseHelperRows_withReadHooks rfh rsh (cliExternsPlaced_baseHelperRows mmpl W))
    ⟨hG.alloc, hG.dealloc, hG.realloc, hG.alloc_fs, hG.dealloc_fs, hG.realloc_fs,
      hG.alloc_fsT, hG.dealloc_fsT, hG.realloc_fsT, hG.shim_eq, hG.memset, hG.memcpy,
      hG.memcpy_exact, hG.memset_acp⟩

theorem allocContractsXCliPlaced_withReadHooks_ghost [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (rfh rsh : State → State) (g : CliGhostHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    AllocContractsXCliPlaced A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) := by
  rw [withReadHooks_cliGhostExterns_comm_strip]
  exact allocContractsXCliPlaced_of_ghost mmpl W
    (withReadHooks rfh rsh (cliExternsPlaced mmpl W))
    { g with readFile := none, readStdin := none }
    (baseHelperRows_withReadHooks rfh rsh (cliExternsPlaced_baseHelperRows mmpl W))
    ⟨hG.alloc, hG.dealloc, hG.realloc, hG.alloc_fs, hG.dealloc_fs, hG.realloc_fs,
      hG.alloc_fsT, hG.dealloc_fsT, hG.realloc_fsT, hG.shim_eq, hG.memset, hG.memcpy,
      hG.memcpy_exact, hG.memset_acp⟩

theorem fsTHooks_withReadHooks {rfh rsh : State → State} {ext : LibsignalHooks}
    (hRfh : HookFsTraced IsFsC rfh)
    (hRsh : HookFsTraced IsFsC rsh)
    (hExt : FsTHooks ext) :
    FsTHooks (withReadHooks rfh rsh ext) := by
  intro sym f h
  by_cases h1 : sym = lsReadStdinSym
  · subst h1; rw [withReadHooks_readStdin] at h; cases h; exact hRsh
  · by_cases h2 : sym = lsReadFileSym
    · subst h2; rw [withReadHooks_readFile] at h; cases h; exact hRfh
    · rw [withReadHooks_other rfh rsh ext h1 h2] at h
      exact hExt sym f h

theorem fsTHooks_withReadHooks_ghost [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {rfh rsh : State → State} {g : CliGhostHooks} {baseExt : LibsignalHooks}
    (hRfh : HookFsTraced IsFsC rfh)
    (hRsh : HookFsTraced IsFsC rsh)
    (hG : CliGhostSpqrAllocHooks M A lim g)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hBase : FsTHooks baseExt) :
    FsTHooks (withReadHooks rfh rsh (cliGhostExterns g baseExt)) :=
  fsTHooks_withReadHooks hRfh hRsh (fsTHooks_cliGhostExterns hG hStrFsT hBase)

/-! ## Call-Entry `P_io` Ghost Hooks (`readStdinGhostHook`) -/

private theorem setPC_mem (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl
private theorem setPC_fs (s : State) (pc : BitVec 64) : (s.setPC pc).fs = s.fs := by
  cases s; rfl
private theorem setPC_trace (s : State) (pc : BitVec 64) : (s.setPC pc).trace = s.trace := by
  cases s; rfl
private theorem setPC_symtab (s : State) (pc : BitVec 64) : (s.setPC pc).symtab = s.symtab := by
  cases s; rfl
private theorem setPC_sp (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by
  cases s; rfl
private theorem setPC_status (s : State) (pc : BitVec 64) : (s.setPC pc).status = s.status := by
  cases s; rfl
private theorem setPC_spAligned (s : State) (pc : BitVec 64) :
    (s.setPC pc).spAligned = s.spAligned := by
  cases s; rfl
private theorem setPC_pc (s : State) (pc : BitVec 64) : (s.setPC pc).pc = pc := by
  cases s; rfl
private theorem setPC_readReg64 (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := by
  cases s; rfl
private theorem returned_setPC (s0 sf : State) (pc : BitVec 64) :
    Returned (s0.setPC pc) sf = Returned s0 sf := by
  cases s0; rfl
private theorem ccPreserved_setPC (s0 sf : State) (pc : BitVec 64) :
    CallingConventionPreserved (s0.setPC pc) sf = CallingConventionPreserved s0 sf := by
  cases s0; rfl

private theorem step_status_running {P : Program} {s1 s2 : State} (h : Step P s1 s2) :
    s1.status = .Running := by
  cases h <;> assumption

private theorem steps_eq_of_not_running {P : Program} {s1 s2 : State}
    (hnr : s1.status ≠ .Running) (h : Steps P s1 s2) : s1 = s2 := by
  cases h with
  | refl => rfl
  | step h1 _ => exact absurd (step_status_running h1) hnr

private theorem firstStop_eq_of_callerLrUnmapped {P_io : Program} {entry_io : BitVec 64}
    {s0 sf : State}
    (hsteps : Steps P_io (s0.setPC entry_io) sf)
    (hret : Returned s0 sf)
    (hLr : CallerLrUnmapped P_io s0) :
    StepsUntil P_io (SubroutineStop s0) (s0.setPC entry_io) sf ∧ SubroutineStop s0 sf := by
  obtain ⟨sm, huntil, hstop_m, hrest⟩ :=
    hsteps.toStepsUntil (stop := SubroutineStop s0) (Or.inl hret)
  have hkf_m : s0.mem.KeepsFrozen sm.mem := by
    simpa only [setPC_mem] using huntil.toSteps.keepsFrozen
  have hsm_eq : sm = sf := by
    rcases hstop_m with hret_m | hpan_m | ⟨code, hex_m⟩ | hoom_m
    · cases hrest with
      | refl => rfl
      | @step _ s2 _ h1 h2 =>
        obtain ⟨hfetch_none, hext_none⟩ := hLr sm.mem hkf_m
        rw [← hret_m.1] at hfetch_none hext_none
        cases h1 with
        | exec _ hfetch => rw [hfetch_none] at hfetch; cases hfetch
        | halt_unmapped _ _ _ =>
          have hs2_eq : { sm with status := .Halted } = sf :=
            steps_eq_of_not_running (by simp) h2
          have hsf_halt : sf.status = .Halted := hs2_eq ▸ rfl
          rw [hret.2.2] at hsf_halt
          cases hsf_halt
        | extern _ hext => rw [hext_none] at hext; cases hext
        | extern_fault _ hext => rw [hext_none] at hext; cases hext
    · exact steps_eq_of_not_running (by rw [hpan_m]; exact ExecStatus.noConfusion) hrest
    · exact steps_eq_of_not_running (by rw [hex_m]; exact ExecStatus.noConfusion) hrest
    · exact steps_eq_of_not_running (by rw [hoom_m]; exact ExecStatus.noConfusion) hrest
  subst hsm_eq
  exact ⟨huntil, Or.inl hret⟩

/-- Precondition witness at `lsReadStdinSym` call entry (`s0` satisfies
    `readStdinSpecOfPlaced … CompiledReadStdinEnv` for some ghost pair `(x, st)` and frame `R`;
    implied by both `ReadStdinBoundedEnv` and `ReadStdinEnv` via `CompiledReadStdinEnv ⊆ ·`). -/
def ActiveReadStdinPre [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) (s0 : State) : Prop :=
  s0.status = .Running ∧ s0.spAligned = true ∧
    ∃ (g : ReadStdinGhost × M.σ) (R : SepProp),
      s0.mem ⊨ (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv).pre g s0 ∗ R

/-- Deterministic first-stop execution witness of compiled `P_io` from `s0.setPC entry_io` under
`P_io.CodeLoaded s0.mem ∧ CallerLrUnmapped P_io s0`. -/
def ActiveReadStdinRun (P_io : Program) (entry_io : BitVec 64) (s0 : State) : Prop :=
  P_io.CodeLoaded s0.mem ∧ CallerLrUnmapped P_io s0 ∧
    ∃ sf : State,
      StepsUntil P_io (SubroutineStop s0) (s0.setPC entry_io) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs.files = s0.fs.files ∧
      sf.trace = s0.trace ∧
      (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs)

/-- From `subroutine_ok P_io entry_io (readStdinBudgetCondSpec A lim stk)`, any call-entry state
    `s0` satisfying `(readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv).pre (x, st) s0 ∗ R`,
    `P_io.CodeLoaded s0.mem`, and `CallerLrUnmapped P_io s0` deterministically executes `P_io`
    to a first-stop state `sf` across both `x.bs.length ≤ 1048576` and `1048576 < x.bs.length`. -/
theorem compiled_readStdin_run_of_cond [LibsignalPlacement] {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hCond : subroutine_ok P_io entry_io (readStdinBudgetCondSpec A lim stk))
    {x : ReadStdinGhost} {st : M.σ} {R : SepProp} {s0 : State}
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨
      (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv).pre (x, st) s0 ∗ R)
    (hCode : P_io.CodeLoaded s0.mem)
    (hLr : CallerLrUnmapped P_io s0) :
    ∃ sf : State,
      StepsUntil P_io (SubroutineStop s0) (s0.setPC entry_io) sf ∧
      SubroutineStop s0 sf ∧
      s0.mem.KeepsFrozen sf.mem ∧
      sf.symtab = s0.symtab ∧
      sf.fs.files = s0.fs.files ∧
      sf.trace = s0.trace ∧
      (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs) ∧
      SubroutineOutcome
        (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)
        (x, st) R s0 sf := by
  have hNoOom := subroutine_ok_readStdinNoOom_of_cond hCond
  let s1 := s0.setPC entry_io
  dsimp only [readStdinSpecOfPlaced] at hPre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hPre
  rcases hPre with ⟨⟨hx8, hstdin, hEnv, _hlr⟩, hrest⟩
  have hFit : FitsEvents M lim st (readStdinBudgetEvents x.bs) :=
    fitsEvents_readStdin_of_fitsEnv_compiled hEnv
  have hPre1 : s1.mem ⊨ (readStdinBudgetNoOomSpec A lim stk).pre (x, st) s1 ∗ R := by
    dsimp only [readStdinBudgetNoOomSpec, s1]
    simp only [setPC_mem, setPC_readReg64, setPC_fs, setPC_sp, RustCliAllocBudget.pool_setPC]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hstdin, hFit⟩, hrest⟩
  obtain ⟨sf, hsteps, hout1, -⟩ :=
    hNoOom.no_fault_before_outcome (x, st) R s1
      (setPC_pc s0 entry_io) (by simpa only [s1, setPC_status] using hRun)
      hPre1 (by simpa only [s1, setPC_spAligned] using hSp)
      (by simpa only [s1, setPC_mem] using hCode)
  rcases hout1 with ⟨hret1, hcc1, hpost1⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · have hret0 : Returned s0 sf := (returned_setPC s0 sf entry_io) ▸ hret1
    have hcc0 : CallingConventionPreserved s0 sf := (ccPreserved_setPC s0 sf entry_io) ▸ hcc1
    obtain ⟨huntil, hstop⟩ := firstStop_eq_of_callerLrUnmapped hsteps hret0 hLr
    dsimp only [readStdinBudgetNoOomSpec, s1] at hpost1
    simp only [setPC_fs, setPC_trace, setPC_sp] at hpost1
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨⟨hfiles, htr, hfds⟩, hmem⟩
    have hkf : s0.mem.KeepsFrozen sf.mem := by
      simpa only [s1, setPC_mem] using hsteps.keepsFrozen
    have hsym : sf.symtab = s0.symtab := by
      simpa only [s1, setPC_symtab] using hsteps.symtab_eq
    refine ⟨sf, huntil, hstop, hkf, hsym, hfiles, htr, hfds, Or.inl ⟨hret0, hcc0, ?_⟩⟩
    dsimp only [readStdinSpecOfPlaced]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨readStdinBudgetEvents x.bs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨compiledReadStdinEnv_events x.bs, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨readStdinResult x.bs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hfiles, rfl, htr⟩, by simpa only [sepConj_assoc] using hmem⟩
  · dsimp only [readStdinBudgetNoOomSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [readStdinBudgetNoOomSpec] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [readStdinBudgetNoOomSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

open Classical in
/-- Terminating `FsTraced IsFsC`-preserving fallback wrapper for `read_stdin` / `read_file` hooks:
    keeps `fallback s0` unchanged whenever `(fallback s0).fs.files = s0.fs.files ∧
    (fallback s0).trace = s0.trace` (which holds on every `Returned` outcome of
    `readStdinSpecOfPlaced` and `readFileAnySpecPlaced`). -/
noncomputable def keepFilesTrace (fallback : State → State) (s0 : State) : State :=
  let sf := fallback s0
  if sf.fs.files = s0.fs.files ∧ sf.trace = s0.trace then sf
  else { sf with fs := s0.fs, trace := s0.trace }

theorem keepFilesTrace_fsT (fallback : State → State) :
    HookFsTraced IsFsC (keepFilesTrace fallback) := by
  classical
  intro s0
  unfold keepFilesTrace
  dsimp only
  split
  · rename_i h
    exact FsTraced.of_eq h.2 h.1
  · exact FsTraced.of_eq rfl rfl

theorem keepFilesTrace_ok_readStdin [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {fallback : State → State}
    (hfb : HookOk fallback (readStdinSpecOfPlaced cliIo A lim stk StdinEnv)) :
    HookOk (keepFilesTrace fallback) (readStdinSpecOfPlaced cliIo A lim stk StdinEnv) := by
  classical
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hfb (x, st) R s0 hrun hpre hsp
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · have hft : (fallback s0).fs.files = s0.fs.files ∧ (fallback s0).trace = s0.trace := by
      dsimp only [readStdinSpecOfPlaced] at hpost
      rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
      obtain ⟨evs, hpost⟩ := hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨_, hpost⟩ := hpost
      rw [sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpost
      obtain ⟨r, hpost⟩ := hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact ⟨hpost.1.1, hpost.1.2.2⟩
    have heq : keepFilesTrace fallback s0 = fallback s0 := by
      unfold keepFilesTrace; simp [hft]
    rw [heq]
    exact ⟨hkf, hsym, Or.inl ⟨hret, hcc, hpost⟩⟩
  · dsimp only [readStdinSpecOfPlaced] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [readStdinSpecOfPlaced] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [readStdinSpecOfPlaced] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem keepFilesTrace_ok_readFileAny {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {fallback : State → State}
    (hfb : HookOk fallback (readFileAnySpecPlaced A lim stk ReadEnv)) :
    HookOk (keepFilesTrace fallback) (readFileAnySpecPlaced A lim stk ReadEnv) := by
  classical
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hfb (x, st) R s0 hrun hpre hsp
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · have hft : (fallback s0).fs.files = s0.fs.files ∧ (fallback s0).trace = s0.trace := by
      dsimp only [readFileAnySpecPlaced] at hpost
      rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
      obtain ⟨evs, hpost⟩ := hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨_, hpost⟩ := hpost
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left,
        satisfies_sepExists] at hpost
      obtain ⟨r, hpost⟩ := hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact ⟨hpost.1.1, hpost.1.2.2⟩
    have heq : keepFilesTrace fallback s0 = fallback s0 := by
      unfold keepFilesTrace; simp [hft]
    rw [heq]
    exact ⟨hkf, hsym, Or.inl ⟨hret, hcc, hpost⟩⟩
  · dsimp only [readFileAnySpecPlaced] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [readFileAnySpecPlaced] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [readFileAnySpecPlaced] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

open Classical in
/-- Call-entry ghost hook for `read_stdin`: executes compiled `P_io` when
`P_io.CodeLoaded s0.mem ∧ CallerLrUnmapped P_io s0`, delegates to `keepFilesTrace fallback`
outside `ActiveReadStdinRun`, and sets `.Exception` outside `ActiveReadStdinPre`. -/
noncomputable def readStdinGhostHook [LibsignalPlacement] {M : AllocCostModel}
    (P_io : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) (s0 : State) : State :=
  if _ : ActiveReadStdinPre A lim stk s0 then
    if hRun : ActiveReadStdinRun P_io entry_io s0 then
      Classical.choose hRun.2.2
    else
      keepFilesTrace fallback s0
  else
    { s0 with status := .Exception "read_stdin ghost-hook precondition violated" }

theorem readStdinGhostHook_fsT [LibsignalPlacement] {M : AllocCostModel}
    (P_io : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) :
    HookFsTraced IsFsC (readStdinGhostHook P_io entry_io A lim stk fallback) := by
  classical
  intro s0
  unfold readStdinGhostHook
  split
  · split
    · rename_i hRun
      have hspec := Classical.choose_spec hRun.2.2
      exact FsTraced.of_eq hspec.2.2.2.1 hspec.2.2.1
    · exact keepFilesTrace_fsT fallback s0
  · exact FsTraced.of_eq rfl rfl

theorem readStdinGhostHook_ok_compiled [LibsignalPlacement] {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hCond : subroutine_ok P_io entry_io (readStdinBudgetCondSpec A lim stk))
    (hFallback : HookOk fallback (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    HookOk (readStdinGhostHook P_io entry_io A lim stk fallback)
      (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv) := by
  classical
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hActPre : ActiveReadStdinPre A lim stk s0 := ⟨hrun, hsp, (x, st), R, hpre⟩
  unfold readStdinGhostHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hActRun : ActiveReadStdinRun P_io entry_io s0
  · simp only [hActRun, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hkf, hsym, _, _, _, hout⟩ :=
      compiled_readStdin_run_of_cond hCond hrun hsp hpre hActRun.1 hActRun.2.1
    have hchoose := Classical.choose_spec hActRun.2.2
    have hdet : Classical.choose hActRun.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨hkf, hsym, hout⟩
  · simp only [hActRun, ↓reduceDIte]
    exact keepFilesTrace_ok_readStdin hFallback (x, st) R s0 hrun hpre hsp

theorem readStdinGhostHook_ok_bounded [LibsignalPlacement] {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hCond : subroutine_ok P_io entry_io (readStdinBudgetCondSpec A lim stk))
    (hFallback : HookOk fallback (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    HookOk (readStdinGhostHook P_io entry_io A lim stk fallback)
      (readStdinSpecOfPlaced cliIo A lim stk ReadStdinBoundedEnv) :=
  HookOk.readStdin_mono_env (fun _ _ => compiledReadStdinEnv_sub_bounded)
    (readStdinGhostHook_ok_compiled hCond hFallback)

theorem readStdinGhostHook_ok [LibsignalPlacement] {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hCond : subroutine_ok P_io entry_io (readStdinBudgetCondSpec A lim stk))
    (hFallback : HookOk fallback (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    HookOk (readStdinGhostHook P_io entry_io A lim stk fallback)
      (readStdinSpecPlaced cliIo A lim stk) := by
  rw [← readStdinSpecOfPlaced_eq_readStdinSpecPlaced]
  exact HookOk.readStdin_mono_env (fun _ _ => compiledReadStdinEnv_sub_readStdinEnv)
    (readStdinGhostHook_ok_compiled hCond hFallback)

/-- At any call entry `s0` under `P_io.CodeLoaded s0.mem` and `CallerLrUnmapped P_io s0` where
`readStdinGhostHook` does not fault to `.Exception`, `readStdinGhostHook` executes
`Steps P_io (s0.setPC entry_io) (rsh s0)` and preserves `FdsGe3Closed`. -/
theorem readStdinGhostHook_steps_of_callEntry [LibsignalPlacement] {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State} {s0 : State}
    (hCond : subroutine_ok P_io entry_io (readStdinBudgetCondSpec A lim stk))
    (hnoex : ∀ msg,
      (readStdinGhostHook P_io entry_io A lim stk fallback s0).status ≠ .Exception msg)
    (hCode : P_io.CodeLoaded s0.mem)
    (hLr : CallerLrUnmapped P_io s0) :
    Steps P_io (s0.setPC entry_io) (readStdinGhostHook P_io entry_io A lim stk fallback s0) ∧
      SubroutineStop s0 (readStdinGhostHook P_io entry_io A lim stk fallback s0) ∧
      (readStdinGhostHook P_io entry_io A lim stk fallback s0).fs.files = s0.fs.files ∧
      (readStdinGhostHook P_io entry_io A lim stk fallback s0).trace = s0.trace ∧
      (FdsGe3Closed s0.fs →
        FdsGe3Closed (readStdinGhostHook P_io entry_io A lim stk fallback s0).fs) := by
  classical
  have hActPre : ActiveReadStdinPre A lim stk s0 := by
    by_contra hnPre
    have hex : (readStdinGhostHook P_io entry_io A lim stk fallback s0).status =
        .Exception "read_stdin ghost-hook precondition violated" := by
      unfold readStdinGhostHook; simp [hnPre]
    exact hnoex _ hex
  have ⟨hrun, hsp, ⟨x, st⟩, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, _, hfiles, htr, hfds, _⟩ :=
    compiled_readStdin_run_of_cond hCond hrun hsp hpre hCode hLr
  have hActRun : ActiveReadStdinRun P_io entry_io s0 :=
    ⟨hCode, hLr, sf, huntil, hstop, hfiles, htr, hfds⟩
  have hchoose := Classical.choose_spec hActRun.2.2
  have heq : readStdinGhostHook P_io entry_io A lim stk fallback s0 =
      Classical.choose hActRun.2.2 := by
    unfold readStdinGhostHook; simp [hActPre, hActRun]
  rw [heq]
  exact ⟨hchoose.1.toSteps, hchoose.2.1, hchoose.2.2.1, hchoose.2.2.2.1, hchoose.2.2.2.2⟩

/-! ## `stripS keep` Linked Ghost Hooks and `GhostExternReplays` -/

private theorem stripS_mem_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).mem = stripExecOutside keep s.mem := by cases s; rfl
private theorem stripS_fs_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).fs = s.fs := by cases s; rfl
private theorem stripS_trace_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).trace = s.trace := by cases s; rfl
private theorem stripS_sp_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).sp = s.sp := by cases s; rfl
private theorem stripS_spAligned_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).spAligned = s.spAligned := by cases s; rfl
private theorem stripS_pc_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).pc = s.pc := by cases s; rfl
private theorem stripS_status_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).status = s.status := by cases s; rfl
private theorem stripS_r64_eq (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (stripS keep s).readReg64 r = s.readReg64 r := by cases s; rfl

private theorem subroutineOutcome_not_halted {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : sf.status ≠ .Halted := by
  rcases h with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
  · rw [hr]; decide
  · rw [hp]; decide
  · rw [he]; nofun
  · rw [ho]; decide

private theorem subroutineOutcome_to_stop {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : SubroutineStop s0 sf := by
  rcases h with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, he, _⟩ | ⟨ho, _⟩
  · exact Or.inl hret
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he⟩))
  · exact Or.inr (Or.inr (Or.inr ho))

/-- Active execution witness for `readStdinLinkedGhostHook` under `ExecFrozen s0.mem`,
`keep (s0.readReg64 .lr) = false`, and `P_sub.CodeLoaded (stripExecOutside keep s0.mem)`. -/
def ActiveReadStdinLinkedRun (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entry_io : BitVec 64) (s0 : State) : Prop :=
  ExecFrozen s0.mem ∧ keep (s0.readReg64 .lr) = false ∧
    P_sub.CodeLoaded (stripExecOutside keep s0.mem) ∧
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entry_io) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs.files = s0.fs.files ∧
      sf.trace = s0.trace ∧
      (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs) ∧
      ExecFrozen sf.mem

/-- Lift `subroutine_ok P_sub entry_io (readStdinBudgetCondSpec A lim stk)` across `stripS keep`
to `StepsUntil P_real (SubroutineStop s0) (s0.setPC entry_io) sf` preserving `ExecFrozen`. -/
theorem real_readStdin_run_of_stripS [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readStdinBudgetCondSpec A lim stk))
    {x : ReadStdinGhost} {st : M.σ} {R : SepProp} {s0 : State}
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨
      (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv).pre (x, st) s0 ∗ R)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entry_io) sf ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome
        (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)
        (x, st) R s0 sf ∧
      sf.fs.files = s0.fs.files ∧
      sf.trace = s0.trace ∧
      (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs) ∧
      ExecFrozen sf.mem := by
  have hNoOom := subroutine_ok_readStdinNoOom_of_cond hCond
  let s1 := s0.setPC entry_io
  let s1' := stripS keep s1
  dsimp only [readStdinSpecOfPlaced] at hPre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hPre
  rcases hPre with ⟨⟨hx8, hstdin, hEnv, _hlr⟩, hrest⟩
  have hFit : FitsEvents M lim st (readStdinBudgetEvents x.bs) :=
    fitsEvents_readStdin_of_fitsEnv_compiled hEnv
  have hs1'_pre : s1'.mem ⊨ (readStdinBudgetNoOomSpec A lim stk).pre (x, st) s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hrest
    dsimp only [readStdinBudgetNoOomSpec, s1', s1]
    simp only [stripS_mem_eq, stripS_r64_eq, stripS_fs_eq, stripS_sp_eq,
      setPC_mem, setPC_readReg64, setPC_fs, setPC_sp,
      hPoolStrip st (s0.setPC entry_io), RustCliAllocBudget.pool_setPC]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hstdin, hFit⟩, hsat⟩
  obtain ⟨sf', hsteps', hout', -⟩ :=
    hNoOom.no_fault_before_outcome (x, st) R s1'
      (by simp [s1', s1, stripS_pc_eq])
      (by simpa [s1', s1, stripS_status_eq, setPC_status] using hRun)
      hs1'_pre
      (by simpa [s1', s1, stripS_spAligned_eq, setPC_spAligned] using hSp)
      (by simpa [s1', s1, stripS_mem_eq, setPC_mem] using hCodeSub)
  have hstop1' : SubroutineStop s1' sf' := subroutineOutcome_to_stop hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted hout'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
    stepsUntil_of_stripS_standard (s0 := s0)
      hsvc_real hsvc_sub hreal_no
      (fun pc _ he => nomatch hsub_no pc ▸ he)
      hlr_out hsteps' hstop0' hnhalt' s1 rfl hFr
  rw [hsf_eq] at hout'
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hpan'⟩ | ⟨_, _, hex'⟩ | ⟨_, hoom'⟩
  · have hret0 : Returned s0 sf := by
      cases s0; cases sf; exact hret'
    have hcc0 : CallingConventionPreserved s0 sf := by
      cases s0; cases sf; exact hcc'
    dsimp only [readStdinBudgetNoOomSpec, s1', s1] at hpost'
    simp only [stripS_fs_eq, stripS_trace_eq, stripS_sp_eq,
      setPC_fs, setPC_trace, setPC_sp, hPoolStrip] at hpost'
    have hpost_unstrip : sf.mem ⊨
        (⌜sf.fs.files = s0.fs.files ∧ sf.trace = s0.trace ∧
          (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs)⌝ ∗
          ioVecAt A.repAlloc x.ret (readStdinResult x.bs) ∗
          stackAt s0.sp stk ∗
          A.pool lim (M.stepEvents (readStdinBudgetEvents x.bs) st) sf) ∗ R :=
      satisfies_of_stripExecOutside hfr_sf (by simpa only [stripS_mem_eq] using hpost')
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost_unstrip
    rcases hpost_unstrip with ⟨⟨hfiles, htr, hfds⟩, hmem⟩
    refine ⟨sf, huntil, hstop_sf, Or.inl ⟨hret0, hcc0, ?_⟩, hfiles, htr, hfds, hfr_sf⟩
    dsimp only [readStdinSpecOfPlaced]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨readStdinBudgetEvents x.bs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨compiledReadStdinEnv_events x.bs, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨readStdinResult x.bs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hfiles, rfl, htr⟩, by simpa only [sepConj_assoc] using hmem⟩
  · dsimp only [readStdinBudgetNoOomSpec] at hpan'
    rw [satisfies_pure_sepConj] at hpan'; exact False.elim hpan'.1
  · dsimp only [readStdinBudgetNoOomSpec] at hex'
    rw [satisfies_pure_sepConj] at hex'; exact False.elim hex'.1
  · dsimp only [readStdinBudgetNoOomSpec] at hoom'
    rw [satisfies_pure_sepConj] at hoom'; exact False.elim hoom'.1

open Classical in
/-- Real-ELF `stripS keep` ghost hook for `lsReadStdinSym`: executes `P_real` from
`s0.setPC entry_io` under `ActiveReadStdinLinkedRun`, delegates to `keepFilesTrace fallback`
outside `ActiveReadStdinLinkedRun`, and sets `.Exception` outside `ActiveReadStdinPre`. -/
noncomputable def readStdinLinkedGhostHook [LibsignalPlacement] {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) (s0 : State) : State :=
  if _ : ActiveReadStdinPre A lim stk s0 then
    if hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io s0 then
      Classical.choose hReal.2.2.2
    else
      keepFilesTrace fallback s0
  else
    { s0 with status := .Exception "read_stdin ghost-hook precondition violated" }

theorem readStdinLinkedGhostHook_fsT [LibsignalPlacement] {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) :
    HookFsTraced IsFsC (readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback) := by
  classical
  intro s0
  unfold readStdinLinkedGhostHook
  split
  · split
    · rename_i hReal
      have hspec := Classical.choose_spec hReal.2.2.2
      exact FsTraced.of_eq hspec.2.2.2.1 hspec.2.2.1
    · exact keepFilesTrace_fsT fallback s0
  · exact FsTraced.of_eq rfl rfl

theorem readStdinLinkedGhostHook_ok_compiled [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readStdinBudgetCondSpec A lim stk))
    (hFallback : HookOk fallback (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    HookOk (readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback)
      (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv) := by
  classical
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hActPre : ActiveReadStdinPre A lim stk s0 := ⟨hrun, hsp, (x, st), R, hpre⟩
  unfold readStdinLinkedGhostHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hout, _, _, _, _⟩ :=
      real_readStdin_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hCond
        hrun hsp hpre hReal.1 hReal.2.1 hReal.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    have hkf : s0.mem.KeepsFrozen sf.mem := by
      simpa only [setPC_mem] using huntil.toSteps.keepsFrozen
    have hsym : sf.symtab = s0.symtab := by
      simpa only [setPC_symtab] using huntil.toSteps.symtab_eq
    exact ⟨hkf, hsym, hout⟩
  · simp only [hReal, ↓reduceDIte]
    exact keepFilesTrace_ok_readStdin hFallback (x, st) R s0 hrun hpre hsp

theorem readStdinLinkedGhostHook_ok_bounded [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readStdinBudgetCondSpec A lim stk))
    (hFallback : HookOk fallback (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    HookOk (readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback)
      (readStdinSpecOfPlaced cliIo A lim stk ReadStdinBoundedEnv) :=
  HookOk.readStdin_mono_env (fun _ _ => compiledReadStdinEnv_sub_bounded)
    (readStdinLinkedGhostHook_ok_compiled hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hCond
      hFallback)

theorem readStdinLinkedGhostHook_ok [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readStdinBudgetCondSpec A lim stk))
    (hFallback : HookOk fallback (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    HookOk (readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback)
      (readStdinSpecPlaced cliIo A lim stk) := by
  rw [← readStdinSpecOfPlaced_eq_readStdinSpecPlaced]
  exact HookOk.readStdin_mono_env (fun _ _ => compiledReadStdinEnv_sub_readStdinEnv)
    (readStdinLinkedGhostHook_ok_compiled hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hCond
      hFallback)

/-- `GhostExternReplays` discharge for `readStdinLinkedGhostHook`: along any non-`.Exception`
call step `u` at `stubPc` under `ExecFrozen u.mem`, `keep (u.readReg64 .lr) = false`, and
`P_sub.CodeLoaded (stripExecOutside keep u.mem)`, replays as `Steps P_real u (rsh u)` preserving
`ExecFrozen` and `FdsGe3Closed`. -/
theorem ghostExternReplays_of_readStdinLinkedGhostHook [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {P_real P_sub : Program} {stubPc entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTarget P_real stubPc entry_io)
    (hInvCode : ∀ m : Memory, ExecFrozen m → Inv m → P_sub.CodeLoaded (stripExecOutside keep m))
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readStdinBudgetCondSpec A lim stk)) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps P_real u
          (readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u) ∧
        ExecFrozen
          (readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u).mem := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  classical
  have hActPre : ActiveReadStdinPre A lim stk u := by
    by_contra hnPre
    have hex : (readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u).status =
        .Exception "read_stdin ghost-hook precondition violated" := by
      unfold readStdinLinkedGhostHook; simp [hnPre]
    exact hnoex _ hex
  have ⟨_, hsp, ⟨x, st⟩, R, hpre⟩ := hActPre
  have hCodeSub := hInvCode u.mem hfr hinv
  obtain ⟨sf, huntil, hstop, _, hfiles, htr, hfds, hfr_sf⟩ :=
    real_readStdin_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hCond
      hrun hsp hpre hfr hlr hCodeSub
  have hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io u :=
    ⟨hfr, hlr, hCodeSub, sf, huntil, hstop, hfiles, htr, hfds, hfr_sf⟩
  have heq : readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u =
      Classical.choose hReal.2.2.2 := by
    unfold readStdinLinkedGhostHook; simp [hActPre, hReal]
  rw [heq]
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hStubSteps : Steps P_real u (u.setPC entry_io) := hStub u hpc hrun hfr
  exact ⟨hStubSteps.trans hchoose.1.toSteps, hchoose.2.2.2.2.2⟩

theorem fdsGe3Closed_readStdinLinkedGhostHook_of_call [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State} {u : State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readStdinBudgetCondSpec A lim stk))
    (hnoex : ∀ msg,
      (readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u).status ≠
        .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hlr : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hClosed : FdsGe3Closed u.fs) :
    FdsGe3Closed (readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u).fs ∧
      (readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u).fs.files =
        u.fs.files := by
  classical
  have hActPre : ActiveReadStdinPre A lim stk u := by
    by_contra hnPre
    have hex : (readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u).status =
        .Exception "read_stdin ghost-hook precondition violated" := by
      unfold readStdinLinkedGhostHook; simp [hnPre]
    exact hnoex _ hex
  have ⟨hrun, hsp, ⟨x, st⟩, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfiles, htr, hfds, hfr_sf⟩ :=
    real_readStdin_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hCond
      hrun hsp hpre hfr hlr hCodeSub
  have hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io u :=
    ⟨hfr, hlr, hCodeSub, sf, huntil, hstop, hfiles, htr, hfds, hfr_sf⟩
  have heq : readStdinLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u =
      Classical.choose hReal.2.2.2 := by
    unfold readStdinLinkedGhostHook; simp [hActPre, hReal]
  rw [heq]
  have hchoose := Classical.choose_spec hReal.2.2.2
  exact ⟨hchoose.2.2.2.2.1 hClosed, hchoose.2.2.1⟩

/-- Unified (`ro : Bool`) call-entry guard for compiled `read_file` covering both `cliWrOk` (`Run`)
    and `cliIo.pathOk` (Block-`617` `.rodata` `"address"`): `FdsGe3Closed s.fs` and no over-cap
    regular file (`> 2 MiB`) at any `cliIo.pathOk` path. -/
def ReadFileAnyCallGuard (s : State) : Prop :=
  FdsGe3Closed s.fs ∧ ∀ p, cliIo.pathOk p → ¬ OverCapFile s.fs.files p

/-- Unified (`ro : Bool`) precondition witness for `lsReadFileSym` (satisfied by both
    `readFileSpecPlaced` and Block-`617` `readFileLitSpecPlaced`). -/
def ActiveReadFileAnyPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) (s0 : State) : Prop :=
  s0.status = .Running ∧ s0.spAligned = true ∧
    ∃ (y : ReadFileCall × M.σ) (R : SepProp),
      s0.mem ⊨ (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd)).pre y s0 ∗ R

def ActiveReadFileLinkedRun (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entry_io : BitVec 64) (s0 : State) : Prop :=
  ExecFrozen s0.mem ∧ keep (s0.readReg64 .lr) = false ∧
    ReadFileAnyCallGuard s0 ∧
    P_sub.CodeLoaded (stripExecOutside keep s0.mem) ∧
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entry_io) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ∧
      ExecFrozen sf.mem

theorem real_readFileAny_run_of_stripS {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readFileAnyBudgetCondSpec A lim stk))
    {x : ReadFileCall} {st : M.σ} {R : SepProp} {s0 : State}
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨
      (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd)).pre (x, st) s0 ∗ R)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hGuard : ReadFileAnyCallGuard s0)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entry_io) sf ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome
        (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd))
        (x, st) R s0 sf ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ∧
      ExecFrozen sf.mem := by
  have hNoOom := subroutine_ok_readFileAnyNoOom_of_cond hCond
  let s1 := s0.setPC entry_io
  let s1' := stripS keep s1
  have hallocFd : s0.fs.allocFd ≠ none := allocFd_ne_none_of_fdsGe3Closed hGuard.1
  dsimp only [readFileAnySpecPlaced] at hPre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hPre
  rcases hPre with ⟨⟨hx0, hx1, hx8, hlt32, hpok, hEnv⟩, hrest⟩
  have hnoOver : ¬ OverCapFile s0.fs.files x.path := hGuard.2 x.path hpok
  have hFit : FitsEvents M lim st (readFileBudgetEvents s0.fs.files x.path) :=
    fitsEvents_readFile_of_fitsEnv_not_overCap hnoOver hEnv
  have hs1'_pre : s1'.mem ⊨ (readFileAnyBudgetNoOomSpec A lim stk).pre (x, st) s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hrest
    dsimp only [readFileAnyBudgetNoOomSpec, s1', s1]
    simp only [stripS_mem_eq, stripS_r64_eq, stripS_fs_eq, stripS_sp_eq,
      setPC_mem, setPC_readReg64, setPC_fs, setPC_sp,
      hPoolStrip st (s0.setPC entry_io), RustCliAllocBudget.pool_setPC]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt32, hpok, hallocFd, hFit⟩, hsat⟩
  obtain ⟨sf', hsteps', hout', -⟩ :=
    hNoOom.no_fault_before_outcome (x, st) R s1'
      (by simp [s1', s1, stripS_pc_eq])
      (by simpa [s1', s1, stripS_status_eq, setPC_status] using hRun)
      hs1'_pre
      (by simpa [s1', s1, stripS_spAligned_eq, setPC_spAligned] using hSp)
      (by simpa [s1', s1, stripS_mem_eq, setPC_mem] using hCodeSub)
  have hstop1' : SubroutineStop s1' sf' := subroutineOutcome_to_stop hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted hout'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
    stepsUntil_of_stripS_standard (s0 := s0)
      hsvc_real hsvc_sub hreal_no
      (fun pc _ he => nomatch hsub_no pc ▸ he)
      hlr_out hsteps' hstop0' hnhalt' s1 rfl hFr
  rw [hsf_eq] at hout'
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hpan'⟩ | ⟨_, _, hex'⟩ | ⟨_, hoom'⟩
  · have hret0 : Returned s0 sf := by
      cases s0; cases sf; exact hret'
    have hcc0 : CallingConventionPreserved s0 sf := by
      cases s0; cases sf; exact hcc'
    dsimp only [readFileAnyBudgetNoOomSpec, s1', s1] at hpost'
    simp only [stripS_fs_eq, stripS_trace_eq, stripS_sp_eq,
      setPC_fs, setPC_trace, setPC_sp, hPoolStrip] at hpost'
    have hpost_unstrip : sf.mem ⊨
        (⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
          ioVecAt A.repAlloc x.ret (cliIo.rd s0.fs.files x.path) ∗
          bytesAt x.ro x.pathA x.path ∗ stackAt s0.sp stk ∗
          A.pool lim (M.stepEvents (readFileBudgetEvents s0.fs.files x.path) st) sf) ∗ R :=
      satisfies_of_stripExecOutside hfr_sf (by simpa only [stripS_mem_eq] using hpost')
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpost_unstrip
    rcases hpost_unstrip with ⟨⟨htr, hfs⟩, hmem⟩
    refine ⟨sf, huntil, hstop_sf, Or.inl ⟨hret0, hcc0, ?_⟩, hfs, htr, hfr_sf⟩
    dsimp only [readFileAnySpecPlaced]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨readFileBudgetEvents s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨readFileRuleEnv_events_of_not_overCap hnoOver, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨cliIo.rd s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨congrArg FsState.files hfs, rfl, htr⟩, by simpa only [sepConj_assoc] using hmem⟩
  · dsimp only [readFileAnyBudgetNoOomSpec] at hpan'
    rw [satisfies_pure_sepConj] at hpan'; exact False.elim hpan'.1
  · dsimp only [readFileAnyBudgetNoOomSpec] at hex'
    rw [satisfies_pure_sepConj] at hex'; exact False.elim hex'.1
  · dsimp only [readFileAnyBudgetNoOomSpec] at hoom'
    rw [satisfies_pure_sepConj] at hoom'; exact False.elim hoom'.1

open Classical in
/-- Unified (`ro : Bool`) real-ELF `stripS keep` ghost hook for `lsReadFileSym`: satisfies both
`HookOk rfh (readFileSpecPlaced …)` and `HookOk rfh (readFileLitSpecPlaced …)`, preserves `.fs`,
and replays as `Steps P_real` preserving `ExecFrozen` under `ReadFileAnyCallGuard`. -/
noncomputable def readFileFullLinkedGhostHook {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) (s0 : State) : State :=
  if _ : ActiveReadFileAnyPre A lim stk s0 then
    if hReal : ActiveReadFileLinkedRun keep P_real P_sub entry_io s0 then
      Classical.choose hReal.2.2.2.2
    else
      let sf := fallback s0
      { sf with fs := s0.fs, trace := s0.trace }
  else
    { s0 with status := .Exception "read_file ghost-hook precondition violated" }

theorem readFileFullLinkedGhostHook_fs {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) (s0 : State) :
    (readFileFullLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback s0).fs = s0.fs := by
  classical
  unfold readFileFullLinkedGhostHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.1
    · rfl
  · rfl

theorem readFileFullLinkedGhostHook_fsT {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) :
    HookFsTraced IsFsC
      (readFileFullLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback) := by
  classical
  intro s0
  unfold readFileFullLinkedGhostHook
  split
  · split
    · rename_i hReal
      have hspec := Classical.choose_spec hReal.2.2.2.2
      exact FsTraced.of_eq hspec.2.2.2.1 (congrArg FsState.files hspec.2.2.1)
    · exact FsTraced.of_eq rfl rfl
  · exact FsTraced.of_eq rfl rfl

theorem readFileFullLinkedGhostHook_ok_any {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readFileAnyBudgetCondSpec A lim stk))
    (hFallback : HookOk fallback (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hFallbackFs : ∀ y R s0,
      SubroutineOutcome (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd))
        y R s0 (fallback s0) →
        (fallback s0).fs = s0.fs ∧ (fallback s0).trace = s0.trace) :
    HookOk (readFileFullLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback)
      (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd)) := by
  classical
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hActPre : ActiveReadFileAnyPre A lim stk s0 := ⟨hrun, hsp, (x, st), R, hpre⟩
  unfold readFileFullLinkedGhostHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveReadFileLinkedRun keep P_real P_sub entry_io s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hout, _, _, _⟩ :=
      real_readFileAny_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hCond
        hrun hsp hpre hReal.1 hReal.2.1 hReal.2.2.1 hReal.2.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2.2
    have hdet : Classical.choose hReal.2.2.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    have hkf : s0.mem.KeepsFrozen sf.mem := by
      simpa only [setPC_mem] using huntil.toSteps.keepsFrozen
    have hsym : sf.symtab = s0.symtab := by
      simpa only [setPC_symtab] using huntil.toSteps.symtab_eq
    exact ⟨hkf, hsym, hout⟩
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨hkf, hsym, hout⟩ := hFallback (x, st) R s0 hrun hpre hsp
    obtain ⟨hfs, htr⟩ := hFallbackFs (x, st) R s0 hout
    have heq : { fallback s0 with fs := s0.fs, trace := s0.trace } = fallback s0 := by
      cases h : fallback s0
      rw [h] at hfs htr
      dsimp only at hfs htr ⊢
      subst hfs htr; rfl
    rw [heq]
    exact ⟨hkf, hsym, hout⟩

theorem readFileFullLinkedGhostHook_ok_rw {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readFileAnyBudgetCondSpec A lim stk))
    (hFallback : HookOk fallback (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hFallbackFs : ∀ y R s0,
      SubroutineOutcome (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd))
        y R s0 (fallback s0) →
        (fallback s0).fs = s0.fs ∧ (fallback s0).trace = s0.trace) :
    HookOk (readFileFullLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)) :=
  hookOk_readFileSpecPlaced_of_any
    (readFileFullLinkedGhostHook_ok_any hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hCond
      hFallback hFallbackFs)

theorem readFileFullLinkedGhostHook_ok_lit {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readFileAnyBudgetCondSpec A lim stk))
    (hFallback : HookOk fallback (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hFallbackFs : ∀ y R s0,
      SubroutineOutcome (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd))
        y R s0 (fallback s0) →
        (fallback s0).fs = s0.fs ∧ (fallback s0).trace = s0.trace) :
    HookOk (readFileFullLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback)
      (readFileLitSpecPlaced cliIo A lim stk (ReadFileRuleEnv cliIo.rd)) :=
  hookOk_readFileLitSpecPlaced_of_any
    (readFileFullLinkedGhostHook_ok_any hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hCond
      hFallback hFallbackFs)

/-- Real-ELF-memory step replay for `readFileFullLinkedGhostHook` under `ReadFileAnyCallGuard u`
    (`FdsGe3Closed u.fs ∧ ∀ p, cliIo.pathOk p → ¬ OverCapFile u.fs.files p`). -/
theorem readFileFullLinkedGhostHook_steps_of_call {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State} {u : State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hStub : StubReachesTarget P_real stubPc entry_io)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readFileAnyBudgetCondSpec A lim stk))
    (hpc : u.pc = stubPc)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (readFileFullLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u).status ≠
        .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hlr : keep (u.readReg64 .lr) = false)
    (hGuard : ReadFileAnyCallGuard u)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    Steps P_real u
        (readFileFullLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u) ∧
      ExecFrozen
        (readFileFullLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u).mem ∧
      (readFileFullLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u).fs = u.fs := by
  classical
  have hActPre : ActiveReadFileAnyPre A lim stk u := by
    by_contra hnPre
    have hex :
        (readFileFullLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u).status =
          .Exception "read_file ghost-hook precondition violated" := by
      unfold readFileFullLinkedGhostHook; simp [hnPre]
    exact hnoex _ hex
  have ⟨_, hsp, ⟨x, st⟩, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, htr, hfr_sf⟩ :=
    real_readFileAny_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hCond
      hrun hsp hpre hfr hlr hGuard hCodeSub
  have hReal : ActiveReadFileLinkedRun keep P_real P_sub entry_io u :=
    ⟨hfr, hlr, hGuard, hCodeSub, sf, huntil, hstop, hfs, htr, hfr_sf⟩
  have heq : readFileFullLinkedGhostHook keep P_real P_sub entry_io A lim stk fallback u =
      Classical.choose hReal.2.2.2.2 := by
    unfold readFileFullLinkedGhostHook; simp [hActPre, hReal]
  rw [heq]
  have hchoose := Classical.choose_spec hReal.2.2.2.2
  have hStubSteps : Steps P_real u (u.setPC entry_io) := hStub u hpc hrun hfr
  exact ⟨hStubSteps.trans hchoose.1.toSteps, hchoose.2.2.2.2, hchoose.2.2.1⟩

/-! ## `MainIoPlaced ∧ MainIoBoundedPlaced` on `withReadHooks` -/

theorem writeStdoutHook_ok_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    HookOk writeStdoutHook (writeStdoutSpecPlaced A lim stk) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  dsimp only [writeStdoutSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, _⟩, hmem⟩
  have hpre0 : s0.mem ⊨
      (CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced stk).pre x s0 ∗
        (A.pool lim st s0 ∗ R) := by
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, by simpa only [sepConj_assoc] using hmem⟩
  rcases CryptoVerification.SignalSession.Cli.MainHops.writeStdoutHook_ok_placed stk x
      (A.pool lim st s0 ∗ R) s0 hrun hpre0 hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hres, hrest⟩
    dsimp only [writeStdoutSpecPlaced]
    have hpool : A.pool lim (M.stepEvents [] st) (writeStdoutHook s0) = A.pool lim st s0 :=
      A.pool_transport lim st s0 (writeStdoutHook s0) (vmPreserved_writeStdoutHook s0)
    have hrest' : (writeStdoutHook s0).mem ⊨
        ((x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ A.pool lim st s0) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    refine Satisfies.mono
      (sepConj_mono_left (Entails.sepExists_right ([] : List AllocEvent) ?_)) hrest'
    rw [hpool]
    exact Entails.pure_right ⟨writeStdoutEnv_nil, hres⟩ (Entails.refl _)
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem writeFileHook_ok_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    HookOk writeFileHook (writeFileSpecPlaced cliIo A lim stk) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  dsimp only [writeFileSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, _⟩, hmem⟩
  have hpre0 : s0.mem ⊨
      (CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced cliIo stk).pre x s0 ∗
        (A.pool lim st s0 ∗ R) := by
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk⟩, by simpa only [sepConj_assoc] using hmem⟩
  rcases CryptoVerification.SignalSession.Cli.MainHops.writeFileHook_ok_placed stk x
      (A.pool lim st s0 ∗ R) s0 hrun hpre0 hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hres, hrest⟩
    dsimp only [writeFileSpecPlaced]
    have hpool : A.pool lim (M.stepEvents [] st) (writeFileHook s0) = A.pool lim st s0 :=
      A.pool_transport lim st s0 (writeFileHook s0) (vmPreserved_writeFileHook s0)
    have hrest' : (writeFileHook s0).mem ⊨
        ((x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ A.pool lim st s0) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    refine Satisfies.mono
      (sepConj_mono_left (Entails.sepExists_right ([] : List AllocEvent) ?_)) hrest'
    rw [hpool]
    exact Entails.pure_right ⟨writeFileEnv_nil x.path.length, hres⟩ (Entails.refl _)
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem writeStdoutHook_preserves_execFrozen {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (writeStdoutHook u).mem :=
  ExecFrozen.of_perm_eq hfr (vmPreserved_writeStdoutHook u).perm_eq

theorem writeFileHook_preserves_execFrozen {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (writeFileHook u).mem :=
  ExecFrozen.of_perm_eq hfr (vmPreserved_writeFileHook u).perm_eq

private theorem ls_hook_placed_rocl_ok [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ sym) (withLsRoCl lsmpl spec) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hsat hmem

/-- Generic `MainIoOfPlaced` constructor on `withReadHooks rfh rsh H0` over any `H0` mapping
    `lsWriteFileSym` to `writeFileHook` and `lsWriteStdoutSym` to `writeStdoutHook`. -/
theorem mainIoOfPlaced_withReadHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H0 : LibsignalHooks} {rfh rsh : State → State} {stk : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hWriteFile : H0 lsWriteFileSym = some writeFileHook)
    (hWriteStdout : H0 lsWriteStdoutSym = some writeStdoutHook)
    (hReadFile : HookOk rfh (readFileLitSpecPlaced cliIo A lim stk ReadEnv))
    (hReadStdin : HookOk rsh (readStdinSpecOfPlaced cliIo A lim stk StdinEnv)) :
    MainIoOfPlaced A lim (withReadHooks rfh rsh H0) cliIo stk StdinEnv ReadEnv where
  readStdin := ls_hook_placed_rocl_ok (hookSat_withReadHooks_readStdin rfh rsh H0 hReadStdin)
  readFile := ls_hook_placed_rocl_ok (hookSat_withReadHooks_readFile rfh rsh H0 hReadFile)
  writeFile := ls_hook_placed_rocl_ok
    ⟨writeFileHook,
      (withReadHooks_other rfh rsh H0 (by decide) (by decide)).trans hWriteFile,
      writeFileHook_ok_placed A lim stk⟩
  writeStdout := ls_hook_placed_rocl_ok
    ⟨writeStdoutHook,
      (withReadHooks_other rfh rsh H0 (by decide) (by decide)).trans hWriteStdout,
      writeStdoutHook_ok_placed A lim stk⟩

theorem cliGhostExterns_writeFile (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (g : CliGhostHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W) lsWriteFileSym = some writeFileHook :=
  (cliGhostExterns_other g (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (cliExternsPlaced_writeFile mmpl W)

theorem cliGhostExterns_writeStdout (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (g : CliGhostHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W) lsWriteStdoutSym = some writeStdoutHook :=
  (cliGhostExterns_other g (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (cliExternsPlaced_writeStdout mmpl W)

/-- Derive both `SpecsPlacedBudget.MainIoPlaced` and `M24.MainIoBoundedPlaced` on
`withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))` from `HookOk rfh` at
`readFileLitSpecPlaced` and `HookOk rsh` at `CompiledReadStdinEnv`. -/
theorem mainIoPlaced_and_bounded_withReadHooks_ghost [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {rfh rsh : State → State} (stk : Nat)
    (hReadFile : HookOk rfh (readFileLitSpecPlaced cliIo A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hReadStdin : HookOk rsh (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    MainIoPlaced A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk ∧
    MainIoBoundedPlaced A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk
      ReadStdinBoundedEnv := by
  let H0 := cliGhostExterns g (cliExternsPlaced mmpl W)
  have hWf := cliGhostExterns_writeFile mmpl W g
  have hWs := cliGhostExterns_writeStdout mmpl W g
  have hUnbounded : MainIoBoundedPlaced A lim (withReadHooks rfh rsh H0) cliIo stk ReadStdinEnv :=
    mainIoOfPlaced_withReadHooks hWf hWs hReadFile
      (HookOk.readStdin_mono_env (fun _ _ => compiledReadStdinEnv_sub_readStdinEnv) hReadStdin)
  have hBounded :
      MainIoBoundedPlaced A lim (withReadHooks rfh rsh H0) cliIo stk ReadStdinBoundedEnv :=
    mainIoOfPlaced_withReadHooks hWf hWs hReadFile
      (HookOk.readStdin_mono_env (fun _ _ => compiledReadStdinEnv_sub_bounded) hReadStdin)
  exact ⟨(mainIoBoundedPlaced_iff_mainIoPlaced A lim (withReadHooks rfh rsh H0) cliIo stk).mp
    hUnbounded, hBounded⟩

theorem mainIoPlaced_and_bounded_of_readStdinGhostHook [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (g : CliGhostHooks)
    {M : AllocCostModel} {P_io : Program} {entry_stdin : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {rfh fbStdin : State → State}
    (hReadFile : HookOk rfh (readFileLitSpecPlaced cliIo A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hStdinCond : subroutine_ok P_io entry_stdin (readStdinBudgetCondSpec A lim stk))
    (hFbStdin : HookOk fbStdin (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    let rsh := readStdinGhostHook P_io entry_stdin A lim stk fbStdin
    MainIoPlaced A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk ∧
    MainIoBoundedPlaced A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk
      ReadStdinBoundedEnv :=
  mainIoPlaced_and_bounded_withReadHooks_ghost mmpl W g stk hReadFile
    (readStdinGhostHook_ok_compiled hStdinCond hFbStdin)

theorem mainIoPlaced_and_bounded_of_linkedReadGhostHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (g : CliGhostHooks)
    {M : AllocCostModel} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry_file entry_stdin : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fbFile fbStdin : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hFileCond : subroutine_ok P_sub entry_file (readFileAnyBudgetCondSpec A lim stk))
    (hFbFile : HookOk fbFile (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hFbFileFs : ∀ y R s0,
      SubroutineOutcome (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd))
        y R s0 (fbFile s0) →
        (fbFile s0).fs = s0.fs ∧ (fbFile s0).trace = s0.trace)
    (hStdinCond : subroutine_ok P_sub entry_stdin (readStdinBudgetCondSpec A lim stk))
    (hFbStdin : HookOk fbStdin (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    let rfh := readFileFullLinkedGhostHook keep P_real P_sub entry_file A lim stk fbFile
    let rsh := readStdinLinkedGhostHook keep P_real P_sub entry_stdin A lim stk fbStdin
    MainIoPlaced A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk ∧
    MainIoBoundedPlaced A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk
      ReadStdinBoundedEnv :=
  mainIoPlaced_and_bounded_withReadHooks_ghost mmpl W g stk
    (readFileFullLinkedGhostHook_ok_lit hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hFileCond
      hFbFile hFbFileFs)
    (readStdinLinkedGhostHook_ok_compiled hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hStdinCond
      hFbStdin)

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
