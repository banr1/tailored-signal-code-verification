/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `(γ, tp)`-Independent `read_file` Ghost Hooks and `mallocng` Fallback

Unified (`ro : Bool`) `read_file` budget contracts (`readFileAnySpecPlaced`,
`readFileAnyBudgetCondSpec`, `readFileAnyBudgetNoOomSpec`), a closed `(γ, tp)`-independent
`mallocng` fallback (`f3ReadFileFallback mmpl`), and `(γ, tp)`-independent `stripS keep` ghost
hooks for `ReadFileRuleEnv cliIo.rd` (`f3ReadFileGhostHook`) and `ReadFileRuleEnvFixed cliIo.rd`
(`f3ReadFileFixedGhostHook`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook

open scoped CryptoVerification.RustHeap
open Arm64 Arm64.Process ProofLib ProofLib.SepLogic SepProp
open Arm64.Obj hiding bytesAt
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement LsBlockBound
   libsignalMutatedBlocks ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.E2E (stepRustAlloc1 writeVecHeader)
open CryptoVerification.E2E.HooksE.HooksOkAux
  (keepsFrozen_write64_of_pointsTo64 satisfies_write64_of_pointsTo64)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession (lsReadFileSym)
open CryptoVerification.SignalSession.Cli (ReadFileGhost getResultAt ioVecAt)
open CryptoVerification.SignalSession.Cli.MainHops (ReadFileLitGhost cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (ReadFileCall bytesAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents
   RustCliAllocBudget StaticMappedCover mallocngBudgetPoolAt mallocngBudgetPoolInv
   rustAllocEvents)
open LibsignalBinary.Heap.Fine
  (fineCostModel fineCostModelIface fineCostModelSound)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (CodeBlocksPermRX CodeBlocksPermRXMem allocCallPreserved_refl
   cc_retHook_setMem_sameRegs fineHookRustCliAllocBudget
   mallocngHookBudgetPool mallocngHookBudgetPool_transport mallocngHookRustCliAllocBudget
   vmPreserved_retHook_setMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers
  (fitsEvent_of_fitsAlloc1 rustAllocEvents_one stepRustAlloc1_budget_cps
   write_empty_vecU8 write_vecU8_from_alloc)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen StubReachesTarget hookOk_frame_extra keepFsTrace keepFsTrace_fs
   keepFsTrace_fsT keepFsTrace_trace linkedGhostBudget linkedGhostBudget_pool_stripS
   satisfies_of_stripExecOutside satisfies_stripExecOutside
   stepsUntil_of_stripS_standard subroutine_ok_frame_extra)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (AllocCapNullInEvents CliIoFilesOomPreserved FdsGe3Closed OverCapFile
   ReadFileRuleEnvFixed allocFd_ne_none_of_fdsGe3Closed cliRd_ok_le_fileCap
   fitsEvents_readFile_of_fitsEnv_fixed fitsEvents_readFile_of_fitsEnv_not_overCap
   hRead_of_hookSat hookSat_readFile_of_hookOk hookSat_withPanics_readFile_of_hookOk
   not_allocCapNullInEvents_of_fitsEvents readFileBudgetEvents
   readFileRuleEnvFixed_events readFileRuleEnv_events_of_not_overCap)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv readFileLitSpecPlaced readFileSpecPlaced)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## Call-Entry Path Reader and `stripS` Pool Invariance -/

private theorem stackAt_le_two_pow_64_of_sep {m : Memory} {p sp : BitVec 64} {n stk : Nat}
    {R : SepProp} (hn : 0 < n) (hstk : 0 < stk)
    (h : m ⊨ memRegion p n ∗ (stackAt sp stk ∗ R)) : stk ≤ 2 ^ 64 := by
  have hdisj := (IsBlock.memRegion p n).disjoint
    (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) hn hstk h
  have hlt := (p - (sp - BitVec.ofNat 64 stk)).isLt
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hdisj.2 hlt)

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
private theorem stripS_pma_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).physMemAvail = s.physMemAvail := by cases s; rfl
private theorem stripS_brkStart_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).brkStart = s.brkStart := by cases s; rfl
private theorem stripS_brk_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).brk = s.brk := by cases s; rfl

@[simp] private theorem setPC_mem (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := rfl
@[simp] private theorem setPC_readReg64 (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := rfl
@[simp] private theorem setPC_fs (s : State) (pc : BitVec 64) : (s.setPC pc).fs = s.fs := rfl
@[simp] private theorem setPC_sp (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := rfl
@[simp] private theorem setPC_status (s : State) (pc : BitVec 64) :
    (s.setPC pc).status = s.status := rfl
@[simp] private theorem setPC_spAligned (s : State) (pc : BitVec 64) :
    (s.setPC pc).spAligned = s.spAligned := rfl
@[simp] private theorem setPC_trace (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := rfl
@[simp] private theorem setPC_symtab (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := rfl

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

/-- Path byte slice read from `(x0, x1)` at an `lsReadFileSym` call boundary (`(γ, tp)`-free). -/
def callPathBytes (s : State) : List (BitVec 8) :=
  s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat

@[simp]
theorem callPathBytes_setPC (s : State) (pc : BitVec 64) :
    callPathBytes (s.setPC pc) = callPathBytes s := rfl

/-- Either permission (`ro = false` `↦ₛ` or `ro = true` `↦ᵣ`) of `CliExt.bytesAt ro p bs` fixes
    `m.readBytes p bs.length = bs`. -/
theorem cliBytesAt_readBytes {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)} {m : Memory}
    {R : SepProp} (h : m ⊨ bytesAt ro p bs ∗ R) (hlen : bs.length ≤ 2 ^ 64) :
    m.readBytes p bs.length = bs := by
  cases ro
  · exact ((IsBlock.pointsToBytes p bs).read h).2
  · exact (IsBlockRO.pointsToBytesRO p bs hlen).read h

/-- Under `s.readReg64 .x0 = pathA`, `(s.readReg64 .x1).toNat = path.length`, and
    `s.mem ⊨ bytesAt ro pathA path ∗ R`, `callPathBytes s = path`. -/
theorem callPathBytes_eq_of_bytesAt {ro : Bool} {pathA : BitVec 64} {path : List (BitVec 8)}
    {s : State} {R : SepProp}
    (hx0 : s.readReg64 .x0 = pathA)
    (hx1 : (s.readReg64 .x1).toNat = path.length)
    (hmem : s.mem ⊨ bytesAt ro pathA path ∗ R) :
    callPathBytes s = path := by
  have hlen : path.length ≤ 2 ^ 64 := by
    have := (s.readReg64 .x1).isLt
    omega
  unfold callPathBytes
  rw [hx0, hx1]
  exact cliBytesAt_readBytes hmem hlen

private theorem strip_countPerm_rw (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (a : BitVec 64) (n : Nat),
      (stripExecOutside keep m).countPerm (· == some Perm.rw) a n =
        m.countPerm (· == some Perm.rw) a n
  | _, 0 => rfl
  | a, n + 1 => by
    have hrw :
        ((stripExecOutside keep m).perm a == some Perm.rw) = (m.perm a == some Perm.rw) := by
      cases h1 : (stripExecOutside keep m).perm a == some Perm.rw <;>
        cases h2 : m.perm a == some Perm.rw
      · rfl
      · exfalso
        exact Bool.eq_false_iff.mp h1
          (beq_iff_eq.mpr ((strip_perm_props keep m a).2.2.2.mpr (beq_iff_eq.mp h2)))
      · exfalso
        exact Bool.eq_false_iff.mp h2
          (beq_iff_eq.mpr ((strip_perm_props keep m a).2.2.2.mp (beq_iff_eq.mp h1)))
      · rfl
    simp only [Memory.countPerm, hrw, strip_countPerm_rw keep m (a + 1#64) n]

private theorem strip_rwBytes_eq (keep : BitVec 64 → Bool) (m : Memory) :
    ProofLib.rwBytes (stripExecOutside keep m) = ProofLib.rwBytes m := by
  unfold ProofLib.rwBytes Memory.countRw
  exact strip_countPerm_rw keep m 0#64 (2 ^ 64)

private theorem strip_physPlusRw_eq (keep : BitVec 64 → Bool) (s : State) :
    ProofLib.physPlusRw (stripS keep s) = ProofLib.physPlusRw s := by
  unfold ProofLib.physPlusRw
  simp only [stripS_pma_eq, stripS_mem_eq, strip_rwBytes_eq]

private theorem strip_staticMappedCover_eq (keep : BitVec 64 → Bool)
    (lim : BudgetLimits) (staticIvs ivs : List (BitVec 64 × Nat)) (m : Memory) :
    StaticMappedCover lim staticIvs ivs (stripExecOutside keep m) =
      StaticMappedCover lim staticIvs ivs m := by
  apply propext
  unfold StaticMappedCover
  simp only [(strip_perm_props keep m _).2.2.1]

/-- Under `keep` retaining all `mallocngLib` code-block bytes (`mmpl`),
    `(fineHookRustCliAllocBudget γ mmpl tp brkStart).pool` is invariant under `stripS keep`. -/
theorem fineHookRustCliAllocBudget_pool_stripS
    {keep : BitVec 64 → Bool}
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) (st : fineCostModel.σ) (s : State) :
    (fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim st (stripS keep s) =
      (fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim st s := by
  have hPermRX : CodeBlocksPermRX mmpl (stripS keep s) = CodeBlocksPermRX mmpl s := by
    apply propext
    unfold CodeBlocksPermRX CodeBlocksPermRXMem
    constructor <;> intro h a ha
    · have ha' := h a ha
      rwa [stripS_mem_eq, strip_perm_of_keep (hKeepMallocng a ha)] at ha'
    · rw [stripS_mem_eq, strip_perm_of_keep (hKeepMallocng a ha)]
      exact h a ha
  have hinv : ∀ staticIvs ivs,
      mallocngBudgetPoolInv lim staticIvs ivs (stripS keep s) =
        mallocngBudgetPoolInv lim staticIvs ivs s := by
    intro staticIvs ivs
    apply propext
    unfold mallocngBudgetPoolInv
    simp only [stripS_mem_eq, strip_staticMappedCover_eq, strip_physPlusRw_eq]
  have hpool :
      mallocngBudgetPoolAt fineCostModel fineCostModelIface γ (mallocngAddrsOfPlacement mmpl)
        tp brkStart lim st (stripS keep s) =
      mallocngBudgetPoolAt fineCostModel fineCostModelIface γ (mallocngAddrsOfPlacement mmpl)
        tp brkStart lim st s := by
    unfold mallocngBudgetPoolAt LibsignalBinary.Heap.MallocngModelEnv
    simp only [hinv, stripS_brkStart_eq, stripS_brk_eq]
    cases s; rfl
  change VerifiedLibraries.mallocngLib.codeRO mmpl ∗
      mallocngBudgetPoolAt fineCostModel fineCostModelIface γ (mallocngAddrsOfPlacement mmpl)
        tp brkStart lim st (stripS keep s) ∗
      ⌜lim.enforced = true → CodeBlocksPermRX mmpl (stripS keep s)⌝ =
    VerifiedLibraries.mallocngLib.codeRO mmpl ∗
      mallocngBudgetPoolAt fineCostModel fineCostModelIface γ (mallocngAddrsOfPlacement mmpl)
        tp brkStart lim st s ∗
      ⌜lim.enforced = true → CodeBlocksPermRX mmpl s⌝
  rw [hpool, hPermRX]

/-! ## Unified (`ro : Bool`) `readFileAny*` Contracts and Framing Lifts -/

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

/-- Deterministic-event `NoOom` specialization of `readFileAnyBudgetCondSpec` under `FitsEvents`. -/
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

/-- Frame an invariant `Extra : SepProp` onto `readFileAnyBudgetCondSpec`'s pool when
    `A1.repAlloc = A0.repAlloc` and `A1.pool lim st s = Extra ∗ A0.pool lim st s`. -/
theorem subroutine_ok_readFileAnyBudgetCondSpec_frame_extra {M : AllocCostModel}
    {A0 A1 : RustCliAllocBudget M} (Extra : SepProp)
    (hpool : ∀ lim st s, A1.pool lim st s = Extra ∗ A0.pool lim st s)
    (hrep : A1.repAlloc = A0.repAlloc)
    {lim : BudgetLimits} {stk : Nat} {P : Program} {entry : BitVec 64}
    (h0 : subroutine_ok P entry (readFileAnyBudgetCondSpec A0 lim stk)) :
    subroutine_ok P entry (readFileAnyBudgetCondSpec A1 lim stk) :=
  subroutine_ok_frame_extra Extra h0
    (fun ⟨_, _⟩ _ => Entails.of_eq (by
      dsimp only [readFileAnyBudgetCondSpec]; rw [hpool]; sep_ac_rfl))
    (fun ⟨_, _⟩ _ _ => Entails.of_eq (by
      dsimp only [readFileAnyBudgetCondSpec]; rw [hpool, hrep]; sep_ac_rfl))
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)

theorem linkedGhostReadFileAny_subroutine_ok
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} {stk : Nat} {P : Program} {entry : BitVec 64}
    (h0 : subroutine_ok P entry
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)) :
    subroutine_ok P entry
      (readFileAnyBudgetCondSpec
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim stk) :=
  subroutine_ok_readFileAnyBudgetCondSpec_frame_extra
    (A0 := fineHookRustCliAllocBudget γ mmpl tp brkStart)
    (A1 := linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart)
    (allocLib.codeRO allocMpl) (fun _ _ _ => rfl) rfl h0

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

/-! ## Closed `(γ, tp)`-Independent `mallocng` Fallback -/

/-- Raw `(γ, tp)`-independent `mallocng` `read_file` fallback: writes `errTag` on `.error ()`,
empty `(0, 1, 0)` on `.ok []`, or allocates `bs.length` bytes via `stepRustAlloc1` on non-empty
`.ok bs`. -/
noncomputable def f3ReadFileFallbackRaw (mmpl : Obj.MultiPlacement) (s0 : State) : State :=
  match cliIo.rd s0.fs.files (callPathBytes s0) with
  | .error () =>
    retHook (fun s => s.setMem (s.mem.write64 (s.readReg64 .x8) 0xFFFFFFFFFFFFFFFF#64)) s0
  | .ok bs =>
    if bs.length = 0 then
      retHook (fun s => s.setMem (writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)) s0
    else
      stepRustAlloc1 mmpl false 0 bs.length
        (fun s1 p =>
          retHook (fun s => s.setMem
            (writeVecHeader (s.mem.writeBytes p bs) (s.readReg64 .x8)
              (BitVec.ofNat 64 bs.length) p (BitVec.ofNat 64 bs.length))) s1)
        s0

/-- Closed `(γ, tp)`-independent `read_file` fallback wrapped with `keepFsTrace` so `.fs` and `.trace`
    are preserved definitionally on every state. -/
noncomputable def f3ReadFileFallback (mmpl : Obj.MultiPlacement) (s0 : State) : State :=
  keepFsTrace (f3ReadFileFallbackRaw mmpl) s0

@[simp]
theorem f3ReadFileFallback_fs (mmpl : Obj.MultiPlacement) (s0 : State) :
    (f3ReadFileFallback mmpl s0).fs = s0.fs :=
  keepFsTrace_fs (f3ReadFileFallbackRaw mmpl) s0

@[simp]
theorem f3ReadFileFallback_trace (mmpl : Obj.MultiPlacement) (s0 : State) :
    (f3ReadFileFallback mmpl s0).trace = s0.trace :=
  keepFsTrace_trace (f3ReadFileFallbackRaw mmpl) s0

theorem f3ReadFileFallback_fsT (mmpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (f3ReadFileFallback mmpl) :=
  keepFsTrace_fsT (f3ReadFileFallbackRaw mmpl)

private theorem write_ioVecErr_at_ret {m : Memory} {ret : BitVec 64} {Frame : SepProp}
    (hmem : m ⊨ memRegion ret 24 ∗ Frame) :
    let mf := m.write64 ret 0xFFFFFFFFFFFFFFFF#64
    m.KeepsFrozen mf ∧ (mf.perm = m.perm) ∧
      (mf ⊨ ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (ret + 8#64) 16) ∗ Frame) := by
  have hsplit : memRegion ret 24 =
      (∃∗ w0 : BitVec 64, ret ↦₆₄ w0) ∗ memRegion (ret + 8#64) 16 := by
    rw [memRegion_split' (n := 8) (k := 16) rfl rfl (by decide), memRegion_eight ret]
  rw [hsplit, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hmem
  rcases hmem with ⟨w0, hmem0'⟩
  refine ⟨keepsFrozen_write64_of_pointsTo64 0xFFFFFFFFFFFFFFFF#64 hmem0',
    Memory.perm_write64 m ret 0xFFFFFFFFFFFFFFFF#64, ?_⟩
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
    (satisfies_write64_of_pointsTo64 0xFFFFFFFFFFFFFFFF#64 hmem0')

/-- `f3ReadFileFallback mmpl` satisfies `readFileAnySpecPlaced` at
`fineHookRustCliAllocBudget γ mmpl tp brkStart` for any `ReadEnv` containing
`ReadFileRuleEnv cliIo.rd`. -/
theorem f3ReadFileFallback_ok_of_env
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) {stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hstk : extHookStack ≤ stk)
    (hSubEnv : ∀ F path evs, ReadFileRuleEnv cliIo.rd F path evs → ReadEnv F path evs) :
    HookOk (f3ReadFileFallback mmpl)
      (readFileAnySpecPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk ReadEnv) := by
  let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hMain :
      (s0.mem.KeepsFrozen (f3ReadFileFallbackRaw mmpl s0).mem ∧
        (f3ReadFileFallbackRaw mmpl s0).symtab = s0.symtab ∧
        SubroutineOutcome (readFileAnySpecPlaced A lim stk ReadEnv) (x, st) R s0
          (f3ReadFileFallbackRaw mmpl s0)) ∧
      (f3ReadFileFallbackRaw mmpl s0).fs = s0.fs ∧
      (f3ReadFileFallbackRaw mmpl s0).trace = s0.trace := by
    dsimp only [readFileAnySpecPlaced, A, fineHookRustCliAllocBudget,
      mallocngHookRustCliAllocBudget] at hpre
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, hx8, _hlt32, _hpok, hFitEnv⟩, hmem⟩
    have hpath : callPathBytes s0 = x.path :=
      callPathBytes_eq_of_bytesAt hx0 hx1
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem)
    have hmem_disj : s0.mem ⊨ memRegion x.ret 24 ∗
        (stackAt s0.sp stk ∗
          (bytesAt x.ro x.pathA x.path ∗
            mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim st s0 ∗ R)) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    have hpos_ext : 0 < extHookStack := by unfold extHookStack; omega
    have hstk64 : stk ≤ 2 ^ 64 :=
      stackAt_le_two_pow_64_of_sep (by omega) (Nat.lt_of_lt_of_le hpos_ext hstk) hmem_disj
    have hsplit_stk : stackAt s0.sp stk =
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
          stackAt s0.sp extHookStack := by
      have hs := stackAt_split_bottom s0.sp extHookStack (stk - extHookStack) (by omega)
      rwa [Nat.add_sub_of_le hstk] at hs
    let SlackStk : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack)
    unfold f3ReadFileFallbackRaw
    rw [hpath]
    cases hrd : cliIo.rd s0.fs.files x.path with
    | error u =>
      cases u
      dsimp only []
      have hmem_ret : s0.mem ⊨ memRegion x.ret 24 ∗
          (bytesAt x.ro x.pathA x.path ∗ stackAt s0.sp stk ∗
            mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim st s0 ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
      obtain ⟨hkf_w, hperm_w, herr_mem⟩ := write_ioVecErr_at_ret hmem_ret
      let mf := s0.mem.write64 x.ret 0xFFFFFFFFFFFFFFFF#64
      rw [show retHook (fun s => s.setMem (s.mem.write64 (s.readReg64 .x8) 0xFFFFFFFFFFFFFFFF#64)) s0 =
          retHook (fun s => s.setMem mf) s0 by simp [retHook, hx8, mf]]
      obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf rfl rfl rfl hrun
      refine ⟨⟨hkf_w, rfl, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩, rfl, rfl⟩
      have henv0 : ReadFileRuleEnv cliIo.rd s0.fs.files x.path [] := by
        simp [ReadFileRuleEnv, hrd]
      have hpool_f :
          A.pool lim (fineCostModel.stepEvents [] st) (retHook (fun s => s.setMem mf) s0) =
            mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim st s0 :=
        mallocngHookBudgetPool_transport fineCostModel fineCostModelIface γ mmpl tp brkStart lim st
          (vmPreserved_retHook_setMem hperm_w)
      dsimp only [readFileAnySpecPlaced]
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨[], ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hSubEnv _ _ _ henv0, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.error (), ?_⟩
      rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨rfl, hrd.symm, rfl⟩,
        Satisfies.mono (Entails.of_eq (by dsimp only [ioVecAt, getResultAt])) herr_mem⟩
    | ok bs =>
      dsimp only []
      by_cases hbs0 : bs.length = 0
      · simp only [hbs0, ↓reduceIte]
        have hbs_nil : bs = [] := List.eq_nil_of_length_eq_zero hbs0
        subst hbs_nil
        have hmem_ret : s0.mem ⊨ memRegion x.ret 24 ∗
            (bytesAt x.ro x.pathA x.path ∗ stackAt s0.sp stk ∗
              mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim st s0 ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
        obtain ⟨hkf_w, hperm_w, hemp_mem⟩ :=
          write_empty_vecU8 (A := A.repAlloc) hmem_ret
        let mf := writeVecHeader s0.mem x.ret 0#64 1#64 0#64
        rw [show retHook (fun s => s.setMem (writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)) s0 =
            retHook (fun s => s.setMem mf) s0 by simp [retHook, hx8, mf]]
        obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf rfl rfl rfl hrun
        refine ⟨⟨hkf_w, rfl, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩, rfl, rfl⟩
        have henv0 : ReadFileRuleEnv cliIo.rd s0.fs.files x.path [] := by
          unfold ReadFileRuleEnv; rw [hrd]; exact Or.inl (by simp [allocBytes1Events])
        have hpool_f :
            A.pool lim (fineCostModel.stepEvents [] st) (retHook (fun s => s.setMem mf) s0) =
              mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim st s0 :=
          mallocngHookBudgetPool_transport fineCostModel fineCostModelIface γ mmpl tp brkStart lim st
            (vmPreserved_retHook_setMem hperm_w)
        dsimp only [readFileAnySpecPlaced]
        rw [sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨[], ?_⟩
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨hSubEnv _ _ _ henv0, ?_⟩
        rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨.ok [], ?_⟩
        rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨rfl, hrd.symm, rfl⟩,
          Satisfies.mono (Entails.of_eq (by dsimp only [ioVecAt, getResultAt])) hemp_mem⟩
      · simp only [hbs0, ↓reduceIte]
        have hpos : 1 ≤ bs.length := Nat.pos_of_ne_zero hbs0
        have hcap_le : bs.length ≤ 2097152 := cliRd_ok_le_fileCap hrd
        have hcap_lt : bs.length < 2 ^ 63 := by omega
        have hevs_eq : allocBytes1Events bs = rustAllocEvents bs.length 1 := by
          simp [allocBytes1Events, hbs0]
        have henv_ab : ReadFileRuleEnv cliIo.rd s0.fs.files x.path (rustAllocEvents bs.length 1) := by
          unfold ReadFileRuleEnv; rw [hrd]; exact Or.inl hevs_eq.symm
        have hFit : FitsEvent fineCostModel lim st (.alloc bs.length) :=
          fitsEvent_of_fitsAlloc1 hpos (hFitEnv (rustAllocEvents bs.length 1) (hSubEnv _ _ _ henv_ab))
        have hmem0 : s0.mem ⊨
            (mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim st s0 ∗
              stackAt s0.sp extHookStack ∗
              (SlackStk ∗ bytesAt x.ro x.pathA x.path ∗ memRegion x.ret 24)) ∗ R := by
          dsimp only [SlackStk]
          rw [hsplit_stk] at hmem
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
        let kBody : State → BitVec 64 → State := fun s1 p =>
          retHook (fun s => s.setMem
            (writeVecHeader (s.mem.writeBytes p bs) (s.readReg64 .x8)
              (BitVec.ofNat 64 bs.length) p (BitVec.ofNat 64 bs.length))) s1
        let specStrong : Spec (ReadFileCall × fineCostModel.σ) :=
          { (readFileAnySpecPlaced A lim stk ReadEnv) with
            post := fun y s_init sf =>
              ⌜sf.fs = s_init.fs ∧ sf.trace = s_init.trace⌝ ∗
                (readFileAnySpecPlaced A lim stk ReadEnv).post y s_init sf }
        have hcps := stepRustAlloc1_budget_cps fineCostModelSound hPl
          (spec := specStrong) (x := (x, st)) (R := R)
          (Rest := SlackStk ∗ bytesAt x.ro x.pathA x.path ∗ memRegion x.ret 24)
          false 0 bs.length (by decide) (by decide) hFit hrun rfl rfl rfl hsp
          (Memory.KeepsFrozen.refl _) rfl (allocCallPreserved_refl s0) hmem0 kBody
        have hk_ok :
            s0.mem.KeepsFrozen (stepRustAlloc1 mmpl false 0 bs.length kBody s0).mem ∧
              (stepRustAlloc1 mmpl false 0 bs.length kBody s0).symtab = s0.symtab ∧
              SubroutineOutcome specStrong (x, st) R s0
                (stepRustAlloc1 mmpl false 0 bs.length kBody s0) := by
          refine hcps ?_
          intro s1 p hp_ne hp_al16 hp_fit64 hs1_run hs1_sp hs1_regs hs1_vregs hkf1 hsym1 hpres1 hmem1
          simp only [Bool.false_eq_true, ↓reduceIte] at hmem1
          have hs1_x8 : s1.readReg64 .x8 = x.ret := by
            simp [State.readReg64, hs1_regs] at hx8 ⊢; exact hx8
          have hm_prep : s1.mem ⊨
              fineCostModelIface.BlockM γ p bs.length 16 ∗ memRegion p bs.length ∗ memRegion x.ret 24 ∗
                (SlackStk ∗ bytesAt x.ro x.pathA x.path ∗
                  mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim
                    (fineCostModel.step (.alloc bs.length) st) s1 ∗
                  stackAt s0.sp extHookStack ∗ R) :=
            Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1
          obtain ⟨hkf_w, hperm_w, hvec⟩ :=
            write_vecU8_from_alloc fineCostModelSound (mpl := mmpl) (tp := tp) (brkStart := brkStart)
              (bs := bs) hp_ne hp_al16 hp_fit64 (by omega) hcap_lt (Nat.le_refl _) hm_prep
          let mf := writeVecHeader (s1.mem.writeBytes p bs) x.ret
            (BitVec.ofNat 64 bs.length) p (BitVec.ofNat 64 bs.length)
          have hk_eq : kBody s1 p = retHook (fun s => s.setMem mf) s1 := by
            simp [kBody, retHook, hs1_x8, mf]
          rw [hk_eq]
          obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf hs1_regs hs1_vregs hs1_sp hs1_run
          refine ⟨hkf1.trans hkf_w, hsym1, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
          have hev_step :
              fineCostModel.stepEvents (rustAllocEvents bs.length 1) st =
                fineCostModel.step (.alloc bs.length) st := by
            rw [rustAllocEvents_one hpos]; rfl
          have hfs_f : (retHook (fun s => s.setMem mf) s1).fs = s0.fs := hpres1.1
          have htr_f : (retHook (fun s => s.setMem mf) s1).trace = s0.trace := hpres1.2.1
          have hpool_f :
              A.pool lim (fineCostModel.stepEvents (rustAllocEvents bs.length 1) st)
                (retHook (fun s => s.setMem mf) s1) =
              mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim
                (fineCostModel.step (.alloc bs.length) st) s1 := by
            rw [hev_step]
            exact mallocngHookBudgetPool_transport fineCostModel fineCostModelIface γ mmpl
              tp brkStart lim _ (vmPreserved_retHook_setMem hperm_w)
          dsimp only [specStrong, readFileAnySpecPlaced]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hfs_f, htr_f⟩, ?_⟩
          rw [sepExists_sepConj_left, satisfies_sepExists]
          refine ⟨rustAllocEvents bs.length 1, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨hSubEnv _ _ _ henv_ab, ?_⟩
          rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left,
            satisfies_sepExists]
          refine ⟨.ok bs, ?_⟩
          rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨congrArg FsState.files hfs_f, hrd.symm, htr_f⟩, ?_⟩
          rw [hsplit_stk]
          exact Satisfies.mono
            (Entails.of_eq (by dsimp only [SlackStk, getResultAt, A, fineHookRustCliAllocBudget]; sep_ac_rfl))
            hvec
        rcases hk_ok with ⟨hkf_f, hsym_f, hout_s⟩
        rcases hout_s with ⟨hret_f, hcc_f, hpost_s⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
        · dsimp only [specStrong] at hpost_s
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_s
          exact ⟨⟨hkf_f, hsym_f, Or.inl ⟨hret_f, hcc_f, hpost_s.2⟩⟩, hpost_s.1.1, hpost_s.1.2⟩
        · dsimp only [specStrong, readFileAnySpecPlaced] at hp
          rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
        · dsimp only [specStrong, readFileAnySpecPlaced] at he
          rw [satisfies_pure_sepConj] at he; exact False.elim he.1
        · dsimp only [specStrong, readFileAnySpecPlaced] at ho
          rw [satisfies_pure_sepConj] at ho; exact False.elim ho.1
  obtain ⟨⟨hkf, hsym, hout⟩, hfs, htr⟩ := hMain
  have heq : f3ReadFileFallback mmpl s0 = f3ReadFileFallbackRaw mmpl s0 := by
    unfold f3ReadFileFallback keepFsTrace
    cases h : f3ReadFileFallbackRaw mmpl s0
    rw [h] at hfs htr
    dsimp only at hfs htr ⊢
    subst hfs htr
    rfl
  rw [heq]
  exact ⟨hkf, hsym, hout⟩

theorem f3ReadFileFallback_ok_fine
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) {stk : Nat}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hstk : extHookStack ≤ stk) :
    HookOk (f3ReadFileFallback mmpl)
      (readFileAnySpecPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk
        (ReadFileRuleEnv cliIo.rd)) :=
  f3ReadFileFallback_ok_of_env γ tp brkStart lim hPl hstk (fun _ _ _ h => h)

theorem f3ReadFileFallback_ok_fine_fixed
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) {stk : Nat}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hstk : extHookStack ≤ stk) :
    HookOk (f3ReadFileFallback mmpl)
      (readFileAnySpecPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk
        (ReadFileRuleEnvFixed cliIo.rd)) :=
  f3ReadFileFallback_ok_of_env γ tp brkStart lim hPl hstk (fun _ _ _ h => Or.inl h)

theorem hookOk_readFileAnySpecPlaced_frame_extra {M : AllocCostModel}
    {A0 A1 : RustCliAllocBudget M} (Extra : SepProp)
    (hpool : ∀ lim st s, A1.pool lim st s = Extra ∗ A0.pool lim st s)
    (hrep : A1.repAlloc = A0.repAlloc)
    {lim : BudgetLimits} {stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {f : State → State}
    (h0 : HookOk f (readFileAnySpecPlaced A0 lim stk ReadEnv)) :
    HookOk f (readFileAnySpecPlaced A1 lim stk ReadEnv) := by
  refine hookOk_frame_extra Extra h0
    (fun ⟨_, _⟩ _ => Entails.of_eq (by
      dsimp only [readFileAnySpecPlaced]; rw [hpool]; sep_ac_rfl))
    (fun ⟨_, _⟩ _ _ => ?_)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
  dsimp only [readFileAnySpecPlaced]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun evs => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro evs)
  rw [hpool, hrep]
  exact Entails.of_eq (by sep_ac_rfl)

theorem f3ReadFileFallback_ok_linked
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) {stk : Nat}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hstk : extHookStack ≤ stk) :
    HookOk (f3ReadFileFallback mmpl)
      (readFileAnySpecPlaced (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim stk
        (ReadFileRuleEnv cliIo.rd)) :=
  hookOk_readFileAnySpecPlaced_frame_extra
    (A0 := fineHookRustCliAllocBudget γ mmpl tp brkStart)
    (A1 := linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart)
    (allocLib.codeRO allocMpl) (fun _ _ _ => rfl) rfl
    (f3ReadFileFallback_ok_fine γ tp brkStart lim hPl hstk)

theorem f3ReadFileFallback_ok_linked_fixed
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) {stk : Nat}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hstk : extHookStack ≤ stk) :
    HookOk (f3ReadFileFallback mmpl)
      (readFileAnySpecPlaced (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim stk
        (ReadFileRuleEnvFixed cliIo.rd)) :=
  hookOk_readFileAnySpecPlaced_frame_extra
    (A0 := fineHookRustCliAllocBudget γ mmpl tp brkStart)
    (A1 := linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart)
    (allocLib.codeRO allocMpl) (fun _ _ _ => rfl) rfl
    (f3ReadFileFallback_ok_fine_fixed γ tp brkStart lim hPl hstk)

/-! ## `(γ, tp)`-Independent Linked `read_file` Ghost Hooks -/

/-- Per-call guard for `ReadFileRuleEnv cliIo.rd`: `FdsGe3Closed s0.fs` and `callPathBytes s0` is
not an over-cap regular file (`> 2 MiB`). -/
def F3ReadFileCallGuard (s0 : State) : Prop :=
  FdsGe3Closed s0.fs ∧ ¬ OverCapFile s0.fs.files (callPathBytes s0)

/-- Call guard for `ReadFileRuleEnvFixed cliIo.rd`: `FdsGe3Closed s0.fs`. -/
def F3ReadFileFixedCallGuard (s0 : State) : Prop :=
  FdsGe3Closed s0.fs

/-- `(γ, tp)`-quantified precondition witness at an `lsReadFileSym` call boundary: `s0` satisfies
    `(readFileAnySpecPlaced (AOf γ tp) lim stk ReadEnv).pre` for some `(γ, tp, y, R)`. -/
def ActiveF3ReadFilePre {M : AllocCostModel}
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (s0 : State) : Prop :=
  s0.status = .Running ∧ s0.spAligned = true ∧
    ∃ (γ : GhostName) (tp : BitVec 64) (y : ReadFileCall × M.σ) (R : SepProp),
      s0.mem ⊨ (readFileAnySpecPlaced (AOf γ tp) lim stk ReadEnv).pre y s0 ∗ R

/-- `(γ, tp)`-independent active real-ELF execution witness for `lsReadFileSym`. -/
def ActiveF3ReadFileRun (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entry_io : BitVec 64) (Guard : State → Prop) (s0 : State) : Prop :=
  ExecFrozen s0.mem ∧ keep (s0.readReg64 .lr) = false ∧
    Guard s0 ∧
    P_sub.CodeLoaded (stripExecOutside keep s0.mem) ∧
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entry_io) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ∧
      ExecFrozen sf.mem

open Classical in
/-- Unified `(γ, tp)`-independent linked ghost-hook schema for `lsReadFileSym` parameterized by
    `(ReadEnv, Guard)` and `fallback`. -/
noncomputable def f3ReadFileLinkedHook {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (Guard : State → Prop)
    (fallback : State → State) (s0 : State) : State :=
  if _ : ActiveF3ReadFilePre AOf lim stk ReadEnv s0 then
    if hReal : ActiveF3ReadFileRun keep P_real P_sub entry_io Guard s0 then
      Classical.choose hReal.2.2.2.2
    else
      keepFsTrace fallback s0
  else
    { s0 with status := .Exception "read_file ghost-hook precondition violated" }

theorem f3ReadFileLinkedHook_fs {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (Guard : State → Prop)
    (fallback : State → State) (s0 : State) :
    (f3ReadFileLinkedHook keep P_real P_sub entry_io AOf lim stk ReadEnv Guard fallback s0).fs =
      s0.fs := by
  classical
  unfold f3ReadFileLinkedHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.1
    · rfl
  · rfl

theorem f3ReadFileLinkedHook_fsT {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (Guard : State → Prop)
    (fallback : State → State) :
    HookFsTraced IsFsC
      (f3ReadFileLinkedHook keep P_real P_sub entry_io AOf lim stk ReadEnv Guard fallback) := by
  classical
  intro s0
  unfold f3ReadFileLinkedHook
  split
  · split
    · rename_i hReal
      have hspec := Classical.choose_spec hReal.2.2.2.2
      exact FsTraced.of_eq hspec.2.2.2.1 (congrArg FsState.files hspec.2.2.1)
    · exact FsTraced.of_eq rfl rfl
  · exact FsTraced.of_eq rfl rfl

/-- `(γ, tp)`-independent real-ELF ghost hook for `ReadFileRuleEnv cliIo.rd`, guarded by
`F3ReadFileCallGuard`. -/
noncomputable def f3ReadFileGhostHook {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) : State → State :=
  f3ReadFileLinkedHook keep P_real P_sub entry_io AOf lim stk
    (ReadFileRuleEnv cliIo.rd) F3ReadFileCallGuard fallback

/-- `(γ, tp)`-independent real-ELF ghost hook for `ReadFileRuleEnvFixed cliIo.rd`, guarded by
`FdsGe3Closed s0.fs`. -/
noncomputable def f3ReadFileFixedGhostHook {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) : State → State :=
  f3ReadFileLinkedHook keep P_real P_sub entry_io AOf lim stk
    (ReadFileRuleEnvFixed cliIo.rd) F3ReadFileFixedCallGuard fallback

noncomputable def f3ReadFileGhostHookFine
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) : State → State :=
  f3ReadFileGhostHook keep P_real P_sub entry_io
    (fun γ tp => fineHookRustCliAllocBudget γ mmpl tp brkStart)
    lim stk (f3ReadFileFallback mmpl)

noncomputable def f3ReadFileFixedGhostHookFine
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) : State → State :=
  f3ReadFileFixedGhostHook keep P_real P_sub entry_io
    (fun γ tp => fineHookRustCliAllocBudget γ mmpl tp brkStart)
    lim stk (f3ReadFileFallback mmpl)

noncomputable def f3ReadFileGhostHookLinked
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (allocLib : Obj.MultiPlacedLib) (allocMpl mmpl : Obj.MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) : State → State :=
  f3ReadFileGhostHook keep P_real P_sub entry_io
    (fun γ tp => linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart)
    lim stk (f3ReadFileFallback mmpl)

noncomputable def f3ReadFileFixedGhostHookLinked
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (allocLib : Obj.MultiPlacedLib) (allocMpl mmpl : Obj.MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) : State → State :=
  f3ReadFileFixedGhostHook keep P_real P_sub entry_io
    (fun γ tp => linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart)
    lim stk (f3ReadFileFallback mmpl)

@[simp]
theorem f3ReadFileGhostHook_fs {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) (fallback : State → State) (s0 : State) :
    (f3ReadFileGhostHook keep P_real P_sub entry_io AOf lim stk fallback s0).fs = s0.fs :=
  f3ReadFileLinkedHook_fs keep P_real P_sub entry_io AOf lim stk _ _ fallback s0

@[simp]
theorem f3ReadFileFixedGhostHook_fs {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) (fallback : State → State) (s0 : State) :
    (f3ReadFileFixedGhostHook keep P_real P_sub entry_io AOf lim stk fallback s0).fs = s0.fs :=
  f3ReadFileLinkedHook_fs keep P_real P_sub entry_io AOf lim stk _ _ fallback s0

theorem f3ReadFileGhostHook_fsT {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) (fallback : State → State) :
    HookFsTraced IsFsC (f3ReadFileGhostHook keep P_real P_sub entry_io AOf lim stk fallback) :=
  f3ReadFileLinkedHook_fsT keep P_real P_sub entry_io AOf lim stk _ _ fallback

theorem f3ReadFileFixedGhostHook_fsT {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) (fallback : State → State) :
    HookFsTraced IsFsC (f3ReadFileFixedGhostHook keep P_real P_sub entry_io AOf lim stk fallback) :=
  f3ReadFileLinkedHook_fsT keep P_real P_sub entry_io AOf lim stk _ _ fallback

noncomputable def f3ReadFileGhostHookSub {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) (fallback : State → State) :
    { f : State → State // HookFsTraced IsFsC f } :=
  ⟨f3ReadFileGhostHook keep P_real P_sub entry_io AOf lim stk fallback,
   f3ReadFileGhostHook_fsT keep P_real P_sub entry_io AOf lim stk fallback⟩

noncomputable def f3ReadFileFixedGhostHookSub {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) (fallback : State → State) :
    { f : State → State // HookFsTraced IsFsC f } :=
  ⟨f3ReadFileFixedGhostHook keep P_real P_sub entry_io AOf lim stk fallback,
   f3ReadFileFixedGhostHook_fsT keep P_real P_sub entry_io AOf lim stk fallback⟩

noncomputable def f3ReadFileGhostHookFineSub
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) :
    { f : State → State // HookFsTraced IsFsC f } :=
  f3ReadFileGhostHookSub keep P_real P_sub entry_io
    (fun γ tp => fineHookRustCliAllocBudget γ mmpl tp brkStart)
    lim stk (f3ReadFileFallback mmpl)

noncomputable def f3ReadFileFixedGhostHookFineSub
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) :
    { f : State → State // HookFsTraced IsFsC f } :=
  f3ReadFileFixedGhostHookSub keep P_real P_sub entry_io
    (fun γ tp => fineHookRustCliAllocBudget γ mmpl tp brkStart)
    lim stk (f3ReadFileFallback mmpl)

/-! ## `stripS` Real-ELF Lifting, `HookOk`, and Replay Theorems -/

/-- Lift `subroutine_ok P_sub entry_io (readFileAnyBudgetCondSpec A lim stk)` across `stripS keep`
under `F3ReadFileCallGuard s0`. -/
theorem real_f3ReadFile_run_of_stripS {M : AllocCostModel}
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
    (hGuard : F3ReadFileCallGuard s0)
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
  have hpath : callPathBytes s0 = x.path :=
    callPathBytes_eq_of_bytesAt hx0 hx1
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest)
  have hnoOver : ¬ OverCapFile s0.fs.files x.path := hpath ▸ hGuard.2
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
  · have hret0 : Returned s0 sf := by cases s0; cases sf; exact hret'
    have hcc0 : CallingConventionPreserved s0 sf := by cases s0; cases sf; exact hcc'
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

/-- Lift `subroutine_ok P_sub entry_io (readFileAnyBudgetCondSpec A lim stk)` across `stripS keep`
under `F3ReadFileFixedCallGuard s0`. -/
theorem real_f3ReadFileFixed_run_of_stripS {M : AllocCostModel}
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
      (readFileAnySpecPlaced A lim stk (ReadFileRuleEnvFixed cliIo.rd)).pre (x, st) s0 ∗ R)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hGuard : F3ReadFileFixedCallGuard s0)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entry_io) sf ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome
        (readFileAnySpecPlaced A lim stk (ReadFileRuleEnvFixed cliIo.rd))
        (x, st) R s0 sf ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ∧
      ExecFrozen sf.mem := by
  have hNoOom := subroutine_ok_readFileAnyNoOom_of_cond hCond
  let s1 := s0.setPC entry_io
  let s1' := stripS keep s1
  have hallocFd : s0.fs.allocFd ≠ none := allocFd_ne_none_of_fdsGe3Closed hGuard
  dsimp only [readFileAnySpecPlaced] at hPre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hPre
  rcases hPre with ⟨⟨hx0, hx1, hx8, hlt32, hpok, hEnv⟩, hrest⟩
  have hFit : FitsEvents M lim st (readFileBudgetEvents s0.fs.files x.path) :=
    fitsEvents_readFile_of_fitsEnv_fixed hEnv
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
  · have hret0 : Returned s0 sf := by cases s0; cases sf; exact hret'
    have hcc0 : CallingConventionPreserved s0 sf := by cases s0; cases sf; exact hcc'
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
    refine ⟨readFileRuleEnvFixed_events s0.fs.files x.path, ?_⟩
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

theorem f3ReadFileGhostHook_ok_any {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {AOf : GhostName → BitVec 64 → RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ γ tp st s, (AOf γ tp).pool lim st (stripS keep s) = (AOf γ tp).pool lim st s)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io (readFileAnyBudgetCondSpec (AOf γ tp) lim stk))
    (hFallback : ∀ γ tp, HookOk (keepFsTrace fallback)
      (readFileAnySpecPlaced (AOf γ tp) lim stk (ReadFileRuleEnv cliIo.rd))) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      HookOk (f3ReadFileGhostHook keep P_real P_sub entry_io AOf lim stk fallback)
        (readFileAnySpecPlaced (AOf γ tp) lim stk (ReadFileRuleEnv cliIo.rd)) := by
  classical
  rintro γ tp ⟨x, st⟩ R s0 hrun hpre hsp
  have hActPre : ActiveF3ReadFilePre AOf lim stk (ReadFileRuleEnv cliIo.rd) s0 :=
    ⟨hrun, hsp, γ, tp, (x, st), R, hpre⟩
  unfold f3ReadFileGhostHook f3ReadFileLinkedHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveF3ReadFileRun keep P_real P_sub entry_io F3ReadFileCallGuard s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hout, _, _, _⟩ :=
      real_f3ReadFile_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no (hPoolStrip γ tp)
        (hCond γ tp) hrun hsp hpre hReal.1 hReal.2.1 hReal.2.2.1 hReal.2.2.2.1
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
    exact hFallback γ tp (x, st) R s0 hrun hpre hsp

theorem f3ReadFileFixedGhostHook_ok_any {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {AOf : GhostName → BitVec 64 → RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ γ tp st s, (AOf γ tp).pool lim st (stripS keep s) = (AOf γ tp).pool lim st s)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io (readFileAnyBudgetCondSpec (AOf γ tp) lim stk))
    (hFallback : ∀ γ tp, HookOk (keepFsTrace fallback)
      (readFileAnySpecPlaced (AOf γ tp) lim stk (ReadFileRuleEnvFixed cliIo.rd))) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      HookOk (f3ReadFileFixedGhostHook keep P_real P_sub entry_io AOf lim stk fallback)
        (readFileAnySpecPlaced (AOf γ tp) lim stk (ReadFileRuleEnvFixed cliIo.rd)) := by
  classical
  rintro γ tp ⟨x, st⟩ R s0 hrun hpre hsp
  have hActPre : ActiveF3ReadFilePre AOf lim stk (ReadFileRuleEnvFixed cliIo.rd) s0 :=
    ⟨hrun, hsp, γ, tp, (x, st), R, hpre⟩
  unfold f3ReadFileFixedGhostHook f3ReadFileLinkedHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveF3ReadFileRun keep P_real P_sub entry_io F3ReadFileFixedCallGuard s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hout, _, _, _⟩ :=
      real_f3ReadFileFixed_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no (hPoolStrip γ tp)
        (hCond γ tp) hrun hsp hpre hReal.1 hReal.2.1 hReal.2.2.1 hReal.2.2.2.1
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
    exact hFallback γ tp (x, st) R s0 hrun hpre hsp

private theorem keepFsTrace_f3ReadFileFallback_eq (mmpl : Obj.MultiPlacement) :
    keepFsTrace (f3ReadFileFallback mmpl) = f3ReadFileFallback mmpl := by
  funext s0
  unfold f3ReadFileFallback keepFsTrace
  rfl

/-- Closed `∀ γ tp, HookOk` for `f3ReadFileGhostHookFine` at `readFileAnySpecPlaced`
(`ReadFileRuleEnv cliIo.rd`). -/
theorem f3ReadFileGhostHookFine_ok_any
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack)) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      HookOk (f3ReadFileGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk)
        (readFileAnySpecPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk
          (ReadFileRuleEnv cliIo.rd)) :=
  f3ReadFileGhostHook_ok_any hsvc_real hsvc_sub hreal_no hsub_no
    (fun γ tp st s => fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st s)
    (fun γ tp => subroutine_ok_readFileAnyBudgetCondSpec_of_extHookStack hstk (hCond γ tp))
    (fun γ tp => by
      rw [keepFsTrace_f3ReadFileFallback_eq]
      exact f3ReadFileFallback_ok_fine γ tp brkStart lim hPl hstk)

theorem f3ReadFileGhostHookFine_ok_placed
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack)) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      HookOk (f3ReadFileGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk)
        (readFileSpecPlaced cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk (ReadFileRuleEnv cliIo.rd)) :=
  fun γ tp => hookOk_readFileSpecPlaced_of_any
    (f3ReadFileGhostHookFine_ok_any hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng hstk hCond γ tp)

theorem f3ReadFileGhostHookFine_ok_lit
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack)) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      HookOk (f3ReadFileGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk)
        (readFileLitSpecPlaced cliIo
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk (ReadFileRuleEnv cliIo.rd)) :=
  fun γ tp => hookOk_readFileLitSpecPlaced_of_any
    (f3ReadFileGhostHookFine_ok_any hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng hstk hCond γ tp)

/-- Closed `∀ γ tp, HookOk` for `f3ReadFileFixedGhostHookFine` at `readFileAnySpecPlaced`
(`ReadFileRuleEnvFixed cliIo.rd`). -/
theorem f3ReadFileFixedGhostHookFine_ok_any
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack)) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      HookOk (f3ReadFileFixedGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk)
        (readFileAnySpecPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk
          (ReadFileRuleEnvFixed cliIo.rd)) :=
  f3ReadFileFixedGhostHook_ok_any hsvc_real hsvc_sub hreal_no hsub_no
    (fun γ tp st s => fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st s)
    (fun γ tp => subroutine_ok_readFileAnyBudgetCondSpec_of_extHookStack hstk (hCond γ tp))
    (fun γ tp => by
      rw [keepFsTrace_f3ReadFileFallback_eq]
      exact f3ReadFileFallback_ok_fine_fixed γ tp brkStart lim hPl hstk)

theorem f3ReadFileFixedGhostHookFine_ok_placed
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack)) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      HookOk (f3ReadFileFixedGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk)
        (readFileSpecPlaced cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk (ReadFileRuleEnvFixed cliIo.rd)) :=
  fun γ tp => hookOk_readFileSpecPlaced_of_any
    (f3ReadFileFixedGhostHookFine_ok_any hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng hstk hCond γ tp)

theorem f3ReadFileFixedGhostHookFine_ok_lit
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack)) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      HookOk (f3ReadFileFixedGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk)
        (readFileLitSpecPlaced cliIo
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk (ReadFileRuleEnvFixed cliIo.rd)) :=
  fun γ tp => hookOk_readFileLitSpecPlaced_of_any
    (f3ReadFileFixedGhostHookFine_ok_any hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng hstk hCond γ tp)

theorem f3ReadFileGhostHookLinked_ok_any
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {allocLib : Obj.MultiPlacedLib} {allocMpl mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack)) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      HookOk (f3ReadFileGhostHookLinked keep P_real P_sub entry_io allocLib allocMpl mmpl brkStart lim stk)
        (readFileAnySpecPlaced (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim stk
          (ReadFileRuleEnv cliIo.rd)) :=
  f3ReadFileGhostHook_ok_any hsvc_real hsvc_sub hreal_no hsub_no
    (fun γ tp st s => linkedGhostBudget_pool_stripS allocLib allocMpl γ mmpl tp brkStart hKeepMallocng lim st s)
    (fun γ tp => linkedGhostReadFileAny_subroutine_ok allocLib allocMpl γ mmpl tp brkStart
      (subroutine_ok_readFileAnyBudgetCondSpec_of_extHookStack hstk (hCond γ tp)))
    (fun γ tp => by
      rw [keepFsTrace_f3ReadFileFallback_eq]
      exact f3ReadFileFallback_ok_linked allocLib allocMpl γ tp brkStart lim hPl hstk)

theorem f3ReadFileFixedGhostHookLinked_ok_any
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {allocLib : Obj.MultiPlacedLib} {allocMpl mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack)) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      HookOk (f3ReadFileFixedGhostHookLinked keep P_real P_sub entry_io allocLib allocMpl mmpl brkStart lim stk)
        (readFileAnySpecPlaced (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim stk
          (ReadFileRuleEnvFixed cliIo.rd)) :=
  f3ReadFileFixedGhostHook_ok_any hsvc_real hsvc_sub hreal_no hsub_no
    (fun γ tp st s => linkedGhostBudget_pool_stripS allocLib allocMpl γ mmpl tp brkStart hKeepMallocng lim st s)
    (fun γ tp => linkedGhostReadFileAny_subroutine_ok allocLib allocMpl γ mmpl tp brkStart
      (subroutine_ok_readFileAnyBudgetCondSpec_of_extHookStack hstk (hCond γ tp)))
    (fun γ tp => by
      rw [keepFsTrace_f3ReadFileFallback_eq]
      exact f3ReadFileFallback_ok_linked_fixed allocLib allocMpl γ tp brkStart lim hPl hstk)

theorem hRead_of_f3ReadFileGhostHookFine [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i ext] [LsBlockBound bi]
    (hlookup : ext lsReadFileSym =
      some (f3ReadFileGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk))
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack))
    (γ : GhostName) (tp : BitVec 64)
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk (ReadFileRuleEnv cliIo.rd)) :=
  hRead_of_hookSat
    (hookSat_readFile_of_hookOk hlookup
      (f3ReadFileGhostHookFine_ok_placed hsvc_real hsvc_sub hreal_no hsub_no
        hPl hKeepMallocng hstk hCond γ tp))
    hi hunmut

theorem hRead_withPanics_of_f3ReadFileGhostHookFine [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)] [LsBlockBound bi]
    (hlookup : ext lsReadFileSym =
      some (f3ReadFileGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk))
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack))
    (γ : GhostName) (tp : BitVec 64)
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk (ReadFileRuleEnv cliIo.rd)) :=
  hRead_of_hookSat
    (hookSat_withPanics_readFile_of_hookOk hlookup
      (f3ReadFileGhostHookFine_ok_placed hsvc_real hsvc_sub hreal_no hsub_no
        hPl hKeepMallocng hstk hCond γ tp))
    hi hunmut

theorem hRead_of_f3ReadFileFixedGhostHookFine [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i ext] [LsBlockBound bi]
    (hlookup : ext lsReadFileSym =
      some (f3ReadFileFixedGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk))
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack))
    (γ : GhostName) (tp : BitVec 64)
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk (ReadFileRuleEnvFixed cliIo.rd)) :=
  hRead_of_hookSat
    (hookSat_readFile_of_hookOk hlookup
      (f3ReadFileFixedGhostHookFine_ok_placed hsvc_real hsvc_sub hreal_no hsub_no
        hPl hKeepMallocng hstk hCond γ tp))
    hi hunmut

theorem hRead_withPanics_of_f3ReadFileFixedGhostHookFine [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)] [LsBlockBound bi]
    (hlookup : ext lsReadFileSym =
      some (f3ReadFileFixedGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk))
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack))
    (γ : GhostName) (tp : BitVec 64)
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk (ReadFileRuleEnvFixed cliIo.rd)) :=
  hRead_of_hookSat
    (hookSat_withPanics_readFile_of_hookOk hlookup
      (f3ReadFileFixedGhostHookFine_ok_placed hsvc_real hsvc_sub hreal_no hsub_no
        hPl hKeepMallocng hstk hCond γ tp))
    hi hunmut

/-- Real-ELF step replay for `f3ReadFileGhostHook`: along any non-`.Exception` call step at
`u.pc = stubPc` under `ExecFrozen u.mem`, `keep (u.readReg64 .lr) = false`,
`P_sub.CodeLoaded (stripExecOutside keep u.mem)`, and `F3ReadFileCallGuard u`, replays as
`Steps P_real u (rfh u)` preserving `ExecFrozen` and `.fs`. -/
theorem f3ReadFileGhostHook_steps_of_call {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entry_io : BitVec 64}
    {AOf : GhostName → BitVec 64 → RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hStub : StubReachesTarget P_real stubPc entry_io)
    (hPoolStrip : ∀ γ tp st s, (AOf γ tp).pool lim st (stripS keep s) = (AOf γ tp).pool lim st s)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io (readFileAnyBudgetCondSpec (AOf γ tp) lim stk))
    {u : State}
    (hpc : u.pc = stubPc)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3ReadFileGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).status ≠
        .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hlr : keep (u.readReg64 .lr) = false)
    (hGuard : F3ReadFileCallGuard u)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    Steps P_real u (f3ReadFileGhostHook keep P_real P_sub entry_io AOf lim stk fallback u) ∧
      ExecFrozen (f3ReadFileGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).mem ∧
      (f3ReadFileGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).fs = u.fs := by
  classical
  have hActPre : ActiveF3ReadFilePre AOf lim stk (ReadFileRuleEnv cliIo.rd) u := by
    by_contra hnPre
    have hex :
        (f3ReadFileGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).status =
          .Exception "read_file ghost-hook precondition violated" := by
      unfold f3ReadFileGhostHook f3ReadFileLinkedHook
      simp [hnPre]
    exact hnoex _ hex
  obtain ⟨_, hsp, γ, tp, ⟨x, st⟩, R, hpre⟩ := id hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, htr, hfr_sf⟩ :=
    real_f3ReadFile_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no (hPoolStrip γ tp)
      (hCond γ tp) hrun hsp hpre hfr hlr hGuard hCodeSub
  have hReal : ActiveF3ReadFileRun keep P_real P_sub entry_io F3ReadFileCallGuard u :=
    ⟨hfr, hlr, hGuard, hCodeSub, sf, huntil, hstop, hfs, htr, hfr_sf⟩
  have heq :
      f3ReadFileGhostHook keep P_real P_sub entry_io AOf lim stk fallback u =
        Classical.choose hReal.2.2.2.2 := by
    unfold f3ReadFileGhostHook f3ReadFileLinkedHook
    simp [hActPre, hReal]
  rw [heq]
  have hchoose := Classical.choose_spec hReal.2.2.2.2
  have hStubSteps : Steps P_real u (u.setPC entry_io) := hStub u hpc hrun hfr
  exact ⟨hStubSteps.trans hchoose.1.toSteps, hchoose.2.2.2.2, hchoose.2.2.1⟩

/-- Real-ELF step replay for `f3ReadFileFixedGhostHook` under `FdsGe3Closed u.fs`. -/
theorem f3ReadFileFixedGhostHook_steps_of_call {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entry_io : BitVec 64}
    {AOf : GhostName → BitVec 64 → RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hStub : StubReachesTarget P_real stubPc entry_io)
    (hPoolStrip : ∀ γ tp st s, (AOf γ tp).pool lim st (stripS keep s) = (AOf γ tp).pool lim st s)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io (readFileAnyBudgetCondSpec (AOf γ tp) lim stk))
    {u : State}
    (hpc : u.pc = stubPc)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3ReadFileFixedGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).status ≠
        .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hlr : keep (u.readReg64 .lr) = false)
    (hGuard : F3ReadFileFixedCallGuard u)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    Steps P_real u (f3ReadFileFixedGhostHook keep P_real P_sub entry_io AOf lim stk fallback u) ∧
      ExecFrozen (f3ReadFileFixedGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).mem ∧
      (f3ReadFileFixedGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).fs = u.fs := by
  classical
  have hActPre : ActiveF3ReadFilePre AOf lim stk (ReadFileRuleEnvFixed cliIo.rd) u := by
    by_contra hnPre
    have hex :
        (f3ReadFileFixedGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).status =
          .Exception "read_file ghost-hook precondition violated" := by
      unfold f3ReadFileFixedGhostHook f3ReadFileLinkedHook
      simp [hnPre]
    exact hnoex _ hex
  obtain ⟨_, hsp, γ, tp, ⟨x, st⟩, R, hpre⟩ := id hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, htr, hfr_sf⟩ :=
    real_f3ReadFileFixed_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no (hPoolStrip γ tp)
      (hCond γ tp) hrun hsp hpre hfr hlr hGuard hCodeSub
  have hReal : ActiveF3ReadFileRun keep P_real P_sub entry_io F3ReadFileFixedCallGuard u :=
    ⟨hfr, hlr, hGuard, hCodeSub, sf, huntil, hstop, hfs, htr, hfr_sf⟩
  have heq :
      f3ReadFileFixedGhostHook keep P_real P_sub entry_io AOf lim stk fallback u =
        Classical.choose hReal.2.2.2.2 := by
    unfold f3ReadFileFixedGhostHook f3ReadFileLinkedHook
    simp [hActPre, hReal]
  rw [heq]
  have hchoose := Classical.choose_spec hReal.2.2.2.2
  have hStubSteps : Steps P_real u (u.setPC entry_io) := hStub u hpc hrun hfr
  exact ⟨hStubSteps.trans hchoose.1.toSteps, hchoose.2.2.2.2, hchoose.2.2.1⟩

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
