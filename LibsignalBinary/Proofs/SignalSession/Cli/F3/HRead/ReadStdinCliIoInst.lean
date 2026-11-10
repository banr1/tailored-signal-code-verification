/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FinishGrowBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinSteps
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import ProofLib.ProgramReflection
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Compiled `signal_session_io::read_stdin` Budgeted Proof and Ghost Hooks

Verifies `readStdinBudgetCondSpec A lim stk` on `signalSessionIoMultiLib` block 0
(`signal_session_io::read_stdin`, `436` B / `109` insns) and block 4 (`finish_grow`) for any
`RustCliAllocBudget M` and `stk ≥ extHookStack`, and instantiates `readStdinCliIoGhostHook`,
`readStdinCliIoLinkedGhostHook`, and `(lim, stk)`-independent `readStdinAnyLinkedGhostHook`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinCliIoInst

open scoped CryptoVerification.RustHeap
open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (LibsignalHooks LibsignalPlacement signalSessionIoMultiLib)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsReadStdinSym readStdinResult stdinCapBytes)
open CryptoVerification.SignalSession.Cli (ioVecAt)
open CryptoVerification.SignalSession.Cli.MainHops (ReadStdinGhost cliIo cliStdin)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC cliGhostExterns)
open VerifiedLibraries.RustStd (SameCpuState vecHeader)
open VerifiedLibraries.RustStd.Io (SameCpuOracleState)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents NullAllowed OomPreserved
   RustCliAllocBudget VmPreserved fitsEvents_append rustAllocEvents rustDeallocEvents
   rustReallocEvents rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase rustCliReallocBudgetSpecBase)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (ReadStdinEnv cliIoCapsEvents cliIoReadScheduleCaps)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen StubReachesTarget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FinishGrowBudget
  (allocCallPreserved_trans cliIoCapsEvents_range_succ cliIoCapsEvents_range_zero
   cliIoFinishGrowBudgetEvents cliIoFinishGrowBudgetSpec cliIoFinishGrow_budget_ok_withCodeLoaded
   cliIoVecBuf cliIoVecBuf_entails_dealloc_mem cliIoVecBuf_repack_chunk cliIoVecBuf_unpack_pos
   cliIoVecBuf_zero_intro oomPreserved_of_allocCallPreserved vecHeader_cliIoVecBuf_entails_ioVecAt_ok
   vecHeader_to_ioVecAt_err vmPreserved_of_seg
   vmPreserved_of_syscallPreserved_fds)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (CliIoFilesOomPreserved FdsGe3Closed fdsGe3Closed_setFd_lt3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
  (ActiveReadStdinLinkedRun CompiledReadStdinEnv compiledReadStdinEnv_events
   compiledReadStdinEnv_sub_bounded compiledReadStdinEnv_sub_readStdinEnv
   fdsGe3Closed_readStdinLinkedGhostHook_of_call ghostExternReplays_of_readStdinLinkedGhostHook
   keepFilesTrace keepFilesTrace_fsT keepFilesTrace_ok_readStdin
   mainIoPlaced_and_bounded_of_linkedReadGhostHooks mainIoPlaced_and_bounded_of_readStdinGhostHook
   mainIoPlaced_and_bounded_withReadHooks_ghost readFileFullLinkedGhostHook
   readStdinBudgetCondSpec readStdinBudgetEvents readStdinBudgetNoOomSpec readStdinGhostHook
   readStdinGhostHook_fsT readStdinGhostHook_ok readStdinGhostHook_ok_bounded
   readStdinGhostHook_ok_compiled readStdinGhostHook_steps_of_callEntry readStdinLinkedGhostHook
   readStdinLinkedGhostHook_fsT readStdinLinkedGhostHook_ok readStdinLinkedGhostHook_ok_bounded
   readStdinLinkedGhostHook_ok_compiled readStdinOverCapEvents real_readStdin_run_of_stripS
   subroutine_ok_readStdinBudgetCondSpec_of_extHookStack subroutine_ok_readStdinNoOom_of_cond
   subroutine_ok_readStdinSpecOfPlaced_of_cond withReadHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoBoundedPlaced ReadStdinBoundedEnv readStdinSpecOfPlaced
   readStdinSpecOfPlaced_eq_readStdinSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (MainIoPlaced ReadFileRuleEnv readFileLitSpecPlaced readStdinSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin (
  muslReadStdin32Spec sp_sub_4224_va_bound
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon
  (bit63_eq_zero_of_lt bv64_beq_ofNat_false bv64_shiftLeft1_ofNat bv64_sub_ofNat
   bv64_ult_ofNat_false bv64_ult_ofNat_true cliIoCap cliIoCapIdx cliIoCapIdx_cap_self
   cliIoCapIdx_eq_of_bounds cliIoCapIdx_le cliIoCap_lt_pow63 cliIoCap_lt_pow64 cliIoCap_mono
   cliIoCap_pos cliIoCap_strictMono cliIoCap_succ cliIoCap_zero cliIoFinalCap cliIoFinalCap_pos
   cliIoFinalCap_zero cliIoReadStdin_stack_refold cliIoReadStdin_stack_split cliIoSavedRegs12
   cliIoStdinCap dvd_4096_preserved grow_step_bounds le_cliIoCap_cliIoCapIdx
   memRegion4096_refold_probe32 memRegion4096_split_probe32 no_grow_capIdx_eq
   overCap_forces_eq_max stackBuf4096_repack wantBytes wantBytes_csel_bv wantBytes_le_4096
   wantBytes_pos)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinSteps
  (cliIo0_lt cliIoReadStdin_dealloc_pc cliIoReadStdin_grow_pc cliIoReadStdin_memcpy_pc
   cliIoReadStdin_read_pc)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym
  (CliIoBlockNoExtern CliIoPlacement cliIoBlockNoSvc0_00 cliIoFinishGrowSym cliIoMemcpySym
   cliIoMpl cliIoPC00 cliIoPl00 cliIoReadStdinSym cliIoReadStdin_lookup cliIoReadSym
   cliIoResolve_eq_base cliIoRustAllocSym cliIoRustDeallocSym cliIoRustNoAllocShimSym
   cliIoRustReallocSym cliIoWithCodeLoaded sepWP_seg_cliIo_block_pure
   subroutine_ok_of_cliIoWithCodeLoaded)

/-! ## Schedule, `FitsEvents`, `cliIo.stdin`, and `FdsGe3Closed` Algebra -/

private theorem cliIoCap_eq_specBudget :
    cliIoCap = LibsignalBinary.Heap.SpecBudget.cliIoCap := rfl

private theorem cliIoCapIdx_eq_specBudget :
    ∀ (K r : Nat), cliIoCapIdx K r = LibsignalBinary.Heap.SpecBudget.cliIoCapIdx K r
  | 0, _ => rfl
  | K + 1, r => by
    unfold cliIoCapIdx LibsignalBinary.Heap.SpecBudget.cliIoCapIdx
    rw [cliIoCap_eq_specBudget, cliIoCapIdx_eq_specBudget K r]

private theorem not_nullAllowed_cliIoCap_budget {j : Nat} (hj : j ≤ 9) :
    ¬ NullAllowed (cliIoCap j) 1 := by
  have hle : cliIoCap j ≤ 2097152 := cliIoCap_mono hj
  have hpow : 2097153 ≤ 2 ^ 62 := by decide
  unfold NullAllowed
  omega

private def schedEvents (j : Nat) : List AllocEvent :=
  cliIoCapsEvents 0 ((List.range (j + 1)).map LibsignalBinary.Heap.SpecBudget.cliIoCap)

private theorem schedEvents_zero :
    schedEvents 0 = rustAllocEvents (cliIoCap 0) 1 :=
  cliIoCapsEvents_range_zero

private theorem schedEvents_succ (j : Nat) :
    schedEvents (j + 1) =
      schedEvents j ++ rustReallocEvents (cliIoCap j) (cliIoCap (j + 1)) 1 :=
  cliIoCapsEvents_range_succ j

private theorem schedEvents_prefix {j J : Nat} (hle : j ≤ J) :
    ∃ tail : List AllocEvent, schedEvents J = schedEvents j ++ tail := by
  induction J with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0
    exact ⟨[], by simp⟩
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact ⟨[], by simp⟩
    · obtain ⟨t, ht⟩ := ih (Nat.lt_succ_iff.mp hlt)
      refine ⟨t ++ rustReallocEvents (cliIoCap k) (cliIoCap (k + 1)) 1, ?_⟩
      rw [schedEvents_succ, ht, List.append_assoc]

private def stdinLoopEvents (len : Nat) : List AllocEvent :=
  cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 len)

private theorem stdinLoopEvents_zero : stdinLoopEvents 0 = [] := by
  simp [stdinLoopEvents, cliIoReadScheduleCaps, cliIoCapsEvents]

private theorem stdinLoopEvents_pos {len : Nat} (hlen : 0 < len) :
    stdinLoopEvents len = schedEvents (cliIoCapIdx 8 len) := by
  have hne : len ≠ 0 := by omega
  unfold stdinLoopEvents cliIoReadScheduleCaps schedEvents
  rw [← cliIoCapIdx_eq_specBudget 8 len]
  simp [hne]

private theorem cliIoCapIdx8_of_gt_cap {r : Nat} (hgt : 1048576 < r) :
    cliIoCapIdx 8 r = 8 := by
  unfold cliIoCapIdx
  have hnot : ¬ r ≤ cliIoCap 7 := by
    change ¬ r ≤ 524288
    omega
  simp [hnot]

private theorem readStdinBudgetEvents_of_le {bs : List (BitVec 8)} (hle : bs.length ≤ 1048576) :
    readStdinBudgetEvents bs = stdinLoopEvents bs.length := by
  simp [readStdinBudgetEvents, stdinLoopEvents, hle]

private theorem readStdinBudgetEvents_of_gt {bs : List (BitVec 8)} (hgt : 1048576 < bs.length) :
    readStdinBudgetEvents bs =
      stdinLoopEvents 1048576 ++ rustDeallocEvents (cliIoCap 8) 1 := by
  have hnot : ¬ bs.length ≤ 1048576 := by omega
  simp only [readStdinBudgetEvents, hnot, ↓reduceIte, readStdinOverCapEvents, stdinLoopEvents]
  rfl

private theorem readStdinBudgetEvents_sched_prefix {bs : List (BitVec 8)} {j : Nat}
    (hpos : 0 < bs.length) (hj : j ≤ cliIoCapIdx 8 bs.length) :
    ∃ tail : List AllocEvent, readStdinBudgetEvents bs = schedEvents j ++ tail := by
  obtain ⟨t1, ht1⟩ := schedEvents_prefix hj
  by_cases hle : bs.length ≤ 1048576
  · refine ⟨t1, ?_⟩
    rw [readStdinBudgetEvents_of_le hle, stdinLoopEvents_pos hpos, ht1]
  · have hgt : 1048576 < bs.length := by omega
    have hidx8 : cliIoCapIdx 8 bs.length = 8 := cliIoCapIdx8_of_gt_cap hgt
    have hidx_max : cliIoCapIdx 8 1048576 = 8 := by
      change cliIoCapIdx 8 (cliIoCap 8) = 8
      exact cliIoCapIdx_cap_self 8
    refine ⟨t1 ++ rustDeallocEvents (cliIoCap 8) 1, ?_⟩
    rw [readStdinBudgetEvents_of_gt hgt, stdinLoopEvents_pos (by decide : 0 < 1048576),
      hidx_max, ← hidx8, ht1, List.append_assoc]

private theorem finishGrowBudgetEvents_pos {j : Nat} (hj : j ≤ 9) :
    cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1)) =
      rustReallocEvents (cliIoCap j) (cliIoCap (j + 1)) 1 := by
  have hlt64 : cliIoCap j < 2 ^ 64 := cliIoCap_lt_pow64 hj
  have hpos : 0 < cliIoCap j := cliIoCap_pos j
  have hto : (BitVec.ofNat 64 (cliIoCap j)).toNat = cliIoCap j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hne : BitVec.ofNat 64 (cliIoCap j) ≠ 0#64 := by
    intro heq
    have := congrArg BitVec.toNat heq
    rw [hto] at this
    simp at this
    omega
  simp [cliIoFinishGrowBudgetEvents, hne, hto]

private theorem not_fitsEvents_budget_of_grow_zero {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {bs : List (BitVec 8)}
    (hpos : 0 < bs.length)
    (hnot : ¬ FitsEvents M lim st (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0))) :
    ¬ FitsEvents M lim st (readStdinBudgetEvents bs) := by
  intro hfit
  obtain ⟨tail, htail⟩ := readStdinBudgetEvents_sched_prefix hpos (Nat.zero_le _)
  rw [htail, schedEvents_zero, fitsEvents_append] at hfit
  exact hnot (by simpa [cliIoFinishGrowBudgetEvents] using hfit.1)

private theorem not_fitsEvents_budget_of_grow_pos {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {bs : List (BitVec 8)} {len j : Nat}
    (hlen : 0 < len) (hbs : 0 < bs.length) (hj : j ≤ 8)
    (hj_eq : j = cliIoCapIdx 8 len)
    (hj1_r : j + 1 ≤ cliIoCapIdx 8 bs.length)
    (hnot : ¬ FitsEvents M lim (M.stepEvents (stdinLoopEvents len) st)
      (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1)))) :
    ¬ FitsEvents M lim st (readStdinBudgetEvents bs) := by
  intro hfit
  obtain ⟨tail, htail⟩ := readStdinBudgetEvents_sched_prefix hbs hj1_r
  have hfit_j1 : FitsEvents M lim st (schedEvents (j + 1)) :=
    ((fitsEvents_append M lim (schedEvents (j + 1)) tail st).mp (htail ▸ hfit)).1
  rw [schedEvents_succ, fitsEvents_append] at hfit_j1
  rw [stdinLoopEvents_pos hlen, ← hj_eq, finishGrowBudgetEvents_pos (by omega)] at hnot
  exact hnot hfit_j1.2

private theorem stepEvents_grow_zero {M : AllocCostModel} (st : M.σ) {n : Nat}
    (hn : 0 < n) (hidx0 : cliIoCapIdx 8 n = 0) :
    M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) st =
      M.stepEvents (stdinLoopEvents n) st := by
  rw [stdinLoopEvents_pos hn, hidx0, schedEvents_zero]
  simp [cliIoFinishGrowBudgetEvents]

private theorem stepEvents_grow_pos {M : AllocCostModel} (st : M.σ) {len len' j : Nat}
    (hlen : 0 < len) (hlen' : 0 < len') (hj : j ≤ 8)
    (hj_eq : j = cliIoCapIdx 8 len) (hidx1 : cliIoCapIdx 8 len' = j + 1) :
    M.stepEvents
        (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1)))
        (M.stepEvents (stdinLoopEvents len) st) =
      M.stepEvents (stdinLoopEvents len') st := by
  rw [finishGrowBudgetEvents_pos (by omega), stdinLoopEvents_pos hlen, ← hj_eq,
    ← AllocCostModel.stepEvents_append, ← schedEvents_succ,
    stdinLoopEvents_pos hlen', hidx1]

private theorem stepEvents_overcap_dealloc {M : AllocCostModel} (st : M.σ)
    {bs : List (BitVec 8)} (hgt : 1048576 < bs.length) :
    M.stepEvents (rustDeallocEvents (cliIoCap 8) 1)
        (M.stepEvents (stdinLoopEvents 1048576) st) =
      M.stepEvents (readStdinBudgetEvents bs) st := by
  rw [← AllocCostModel.stepEvents_append, ← readStdinBudgetEvents_of_gt hgt]

private theorem cliStdin_eq_some {fs : FsState} {bs : List (BitVec 8)}
    (h : cliIo.stdin fs = some bs) :
    ∃ d0 : FdEntry,
      fs.fds 0#64 = some d0 ∧
      d0.kind = .stdio ∧
      d0.accMode.canRead = true ∧
      bs = fs.stdin.drop d0.offset := by
  change cliStdin fs = some bs at h
  unfold cliStdin at h
  cases hfds : fs.fds 0#64 with
  | none => rw [hfds] at h; cases h
  | some d0 =>
    rw [hfds] at h
    dsimp only at h
    by_cases hc : (d0.kind == .stdio && d0.accMode.canRead) = true
    · simp only [hc, ↓reduceIte] at h
      injection h with hbs
      rcases Bool.and_eq_true_iff.mp hc with ⟨hk, hr⟩
      have hkind : d0.kind = .stdio := by
        cases hdk : d0.kind <;> rw [hdk] at hk <;> first | rfl | cases hk
      exact ⟨d0, rfl, hkind, hr, hbs.symm⟩
    · simp only [hc] at h; cases h

private theorem setFd_files_eq (fs : FsState) (fd : BitVec 64) (e : Option FdEntry) :
    (fs.setFd fd e).files = fs.files := by
  cases fs; rfl

private theorem setFd_offset_add_zero {fs : FsState} {fd : BitVec 64} {d0 : FdEntry}
    (h : fs.fds fd = some d0) :
    fs = fs.setFd fd (some { d0 with offset := d0.offset + 0 }) := by
  have hd : ({ d0 with offset := d0.offset + 0 } : FdEntry) = d0 := by
    cases d0; simp
  rw [hd]
  cases fs
  dsimp only [FsState.setFd] at h ⊢
  congr
  funext k
  by_cases hkf : k = fd
  · subst hkf; simp [h]
  · simp [beq_false_of_ne hkf]

private theorem readStdinResult_eq_ok_of_le {bs : List (BitVec 8)} (hle : bs.length ≤ 1048576) :
    readStdinResult bs = .ok bs := by
  have hle' : bs.length ≤ stdinCapBytes := hle
  simp [readStdinResult, hle']

private theorem readStdinResult_eq_err_of_gt {bs : List (BitVec 8)} (hgt : 1048576 < bs.length) :
    readStdinResult bs = .error () := by
  have hnot : ¬ bs.length ≤ stdinCapBytes := by
    change ¬ bs.length ≤ 1048576
    omega
  simp [readStdinResult, hnot]

private abbrev StdinMidPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions

private theorem StdinMidPreserved.trans {a b c : State}
    (h1 : StdinMidPreserved a b) (h2 : StdinMidPreserved b c) : StdinMidPreserved a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

private theorem StdinMidPreserved.of_alloc {s0 sf : State} (h : AllocCallPreserved s0 sf) :
    StdinMidPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1⟩


/-! ## Budget-Threaded `signal_session_io::read_stdin` Step Lemmas -/

section
arm64_proof_prelude

private theorem memRegion24_eq_exists_vecHeader (sret : BitVec 64) :
    memRegion sret 24 = ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      vecHeader sret v0 v1 v2 := by
  rw [show (24 : Nat) = 8 * 3 by decide, VerifiedLibraries.RustStd.memRegion_cells sret 3 (by decide)]
  dsimp only [VerifiedLibraries.RustStd.cells, vecHeader]
  simp only [sepConj_emp, sepExists_sepConj_right, bv_lin_norm]

private theorem cliIoStdin_cap_clamp_bv {j : Nat} (hj : j ≤ 8) :
    (if (BitVec.ofNat 64 (cliIoCap j)).ult 1048576#64 = true
     then BitVec.ofNat 64 (cliIoCap j)
     else 1048576#64) = BitVec.ofNat 64 (cliIoCap j) := by
  have h1048 : (1048576#64 : BitVec 64) = BitVec.ofNat 64 1048576 := rfl
  rw [h1048]
  rcases Nat.lt_or_eq_of_le hj with hlt | rfl
  · have hlt_cap : cliIoCap j < 1048576 := cliIoCap_strictMono hlt
    rw [bv64_ult_ofNat_true hlt_cap (by decide)]
    rfl
  · rfl

private theorem sepConj_pure_mid (P Q : SepProp) (φ : Prop) :
    P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) := by
  rw [← sepConj_assoc, sepConj_comm P ⌜φ⌝, sepConj_assoc]

/-- Budget-threaded `Ok(bs)` epilogue of `read_stdin` (`+0x138 = 312#64 .. +0x160 = 352#64`). -/
private theorem cliIoReadStdin_ok_epilogue_b [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    {s0 se : State} {sret v0 v1 v2 cap ptr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4224 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl00.base + 312#64)
    (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : se.sp = s0.sp - 4224#64)
    (hx19 : se.readReg64 (.gpr 19#5) = sret)
    (hx20 : se.readReg64 (.gpr 20#5) = ptr)
    (hx21 : se.readReg64 (.gpr 21#5) = cap)
    (hx25 : se.readReg64 (.gpr 25#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      AllocCallPreserved se sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.ok bs) ∗
          A.pool lim st_cur sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc cap ptr bs ∗
        A.pool lim st_cur se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl00.base + 312#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 4224#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = sret := (hcpu_e.readReg64 _).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = ptr := (hcpu_e.readReg64 _).trans hx20
  have hx21_e' : se'.readReg64 (.gpr 21#5) = cap := (hcpu_e.readReg64 _).trans hx21
  have hx25_e' : se'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 bs.length :=
    (hcpu_e.readReg64 _).trans hx25
  wp_conv_pre => dsimp only [cliIoSavedRegs12]; rw [show vecHeader sret v0 v1 v2 =
    (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
  have hcpu_f := hcpu_f0.1
  have ⟨hacp_ef, hvm_ef⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f hsym_f
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool lim st_cur se = A.pool lim st_cur sf :=
    (A.pool_transport lim st_cur se sf hvm_ef).symm
  have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
  have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
  have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · exact hcpu_f.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))
  refine SepWP.done hpc_f hrun_f (hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_ef ?_)
  have hstk_back := cliIoReadStdin_stack_refold s0 hlo hhi st0 st1 st2 st3
  dsimp only [cliIoSavedRegs12] at hstk_back
  have hvec_ok := vecHeader_cliIoVecBuf_entails_ioVecAt_ok A.repAlloc sret cap ptr bs
  dsimp only [vecHeader] at hvec_ok
  rw [hpool_eq]
  refine Entails.trans ?_ (sepConj_mono hstk_back (sepConj_mono_left hvec_ok))
  sep_entail

/-- Budget-threaded over-cap `Err(())` epilogue of `read_stdin` (`+0x164 = 356#64 .. +0x1a0 = 416#64`):
    writes `0xFFFFFFFFFFFFFFFF#64` to `[sret]`, restores `sp` and `x19..x30`, and tail-calls
    `__rust_dealloc(ptr, cap, 1)`, advancing `st_cur` by `rustDeallocEvents cap 1`. -/
private theorem cliIoReadStdin_err_epilogue_b [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    {s0 se : State} {sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {cap stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4224 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcap_pos : 0 < cap) (hcap_lt63 : cap < 2 ^ 63)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl00.base + 356#64)
    (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : se.sp = s0.sp - 4224#64)
    (hx19 : se.readReg64 (.gpr 19#5) = sret)
    (hx20 : se.readReg64 (.gpr 20#5) = ptr)
    (hx21 : se.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      AllocCallPreserved se sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.error ()) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents cap 1) st_cur) sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr bs ∗
        A.pool lim st_cur se)
      post oomProp := by
  have hlo4224 : 4224 ≤ stackBytes := by omega
  have hcap_lt64 : cap < 2 ^ 64 := Nat.lt_trans hcap_lt63 (by decide)
  have hcap_beq0 : (BitVec.ofNat 64 cap == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) hcap_lt64 (by decide)
  have hcap_toNat : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64]
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl00.base + 356#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 4224#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = sret := (hcpu_e.readReg64 _).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = ptr := (hcpu_e.readReg64 _).trans hx20
  have hx21_e' : se'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_e.readReg64 _).trans hx21
  wp_conv_pre => dsimp only [cliIoSavedRegs12]; rw [show vecHeader sret v0 v1 v2 =
    (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done cliIoReadStdin_dealloc_pc (by simpa [arm64_norm] using hrun_e')
    fun sm_dl hcpu_dl0 hcl_dl hnsp_dl hsym_dl => ?_
  have hcpu_dl := hcpu_dl0.1
  have ⟨hacp_edl, hvm_edl⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_dl0 hnsp_dl hsym_dl
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_edl : A.pool lim st_cur se = A.pool lim st_cur sm_dl :=
    (A.pool_transport lim st_cur se sm_dl hvm_edl).symm
  have hpc_dl : sm_dl.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym :=
    hcpu_dl.pc_eq.trans cliIoReadStdin_dealloc_pc
  have hrun_dl : sm_dl.status = .Running := hcpu_dl.status_eq.trans hrun_e'
  have hsp_dl_eq : sm_dl.sp = s0.sp := hcpu_dl.sp_eq.trans (by simp [arm64_norm])
  have hsp_dl : sm_dl.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_dl_eq]; exact hsp0
  have hlr_dl : sm_dl.readReg64 .lr = s0.readReg64 .lr :=
    (hcpu_dl.readReg64 .lr).trans (by simp [arm64_norm])
  have hx0_dl : sm_dl.readReg64 .x0 = ptr :=
    (hcpu_dl.readReg64 .x0).trans (by simp [arm64_norm])
  have hx1_dl : (sm_dl.readReg64 .x1).toNat = cap := by
    rw [hcpu_dl.readReg64 .x1]; simpa [arm64_norm] using hcap_toNat
  have hx2_dl : (sm_dl.readReg64 .x2).toNat = 1 := by
    rw [hcpu_dl.readReg64 .x2]; simp [arm64_norm]
  have hcs_0dl : CalleeSavedPreserved s0 sm_dl := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · exact hcpu_dl.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))
  have hhk_le : allocHookStack ≤ stackBytes := by omega
  let T_dl : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stackBytes) (stackBytes - allocHookStack) ∗
      ioVecAt A.repAlloc sret (.error ())
  apply seqCodeLoaded hcl_dl (mid := s0.readReg64 .lr)
  apply (SepWP.call_subroutine_frame (F := T_dl) hdealloc
    (x := (ptr, cap, 1, st_cur))
    hpc_dl hrun_dl hsp_dl hlr_dl
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [rustCliDeallocBudgetSpecBase, T_dl]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0_dl, hx1_dl, hx2_dl⟩, ?_⟩
    have hstk_back := cliIoReadStdin_stack_refold s0 hlo4224 hhi st0 st1 st2 st3
    dsimp only [cliIoSavedRegs12] at hstk_back
    have herr_sret := vecHeader_to_ioVecAt_err A.repAlloc sret v1 v2
    dsimp only [vecHeader] at herr_sret
    have hde_mem : cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr bs ⊢
        A.live ptr cap 1 ∗ memRegion ptr cap :=
      cliIoVecBuf_entails_dealloc_mem A.repAlloc (ptr := ptr) (bs := bs) hcap_pos hcap_lt63
    refine Satisfies.mono ?_ hm'
    rw [hpool_eq_edl, hsp_dl_eq]
    have h1 :
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
          memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
          ((s0.sp - 104#64) ↦₆₄ st3) ∗
          (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
            ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
            ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)))) ∗
        ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2)) ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr bs ⊢
        (memRegion (s0.sp - BitVec.ofNat 64 stackBytes) (stackBytes - allocHookStack) ∗
          stackAt s0.sp allocHookStack) ∗
        ioVecAt A.repAlloc sret (.error ()) ∗
        (A.live ptr cap 1 ∗ memRegion ptr cap) := by
      rw [← stackAt_shrink s0.sp stackBytes allocHookStack hhk_le hhi]
      exact sepConj_mono hstk_back (sepConj_mono herr_sret hde_mem)
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := A.pool lim st_cur sm_dl ∗ R') h1) ?_)
    · sep_entail
    · sep_entail
  · intro sf hpc_f hrun_f hsp_f hcs_dlf
    refine SepWP.done hpc_f hrun_f fun hcl_f => ?_
    wp_conv_pre => dsimp only [rustCliDeallocBudgetSpecBase, T_dl]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hacp_dlf, _⟩
    have hsp_f_eq : sf.sp = s0.sp := hsp_f.trans hsp_dl_eq
    have hcs_0f : CalleeSavedPreserved s0 sf := hcs_0dl.trans hcs_dlf
    have hacp_ef : AllocCallPreserved se sf := allocCallPreserved_trans hacp_edl hacp_dlf
    refine SepWP.done hpc_f hrun_f (hcont sf hpc_f hrun_f hsp_f_eq hcs_0f hcl_f hacp_ef ?_)
    rw [hsp_dl_eq, stackAt_shrink s0.sp stackBytes allocHookStack hhk_le hhi]
    sep_entail

/-- Post-`read` EOF (`x0 = 0#64`) branch `+0x58 → +0x138 .. +0x160`: jumps to `Ok` epilogue. -/
private theorem cliIoReadStdin_after_read_eof_b [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    {s0 sr : State} {sret v0 v1 v2 cap ptr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4224 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl00.base + 88#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 4224#64)
    (hx0 : sr.readReg64 .x0 = 0#64)
    (hx19 : sr.readReg64 (.gpr 19#5) = sret) (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = cap)
    (hx25 : sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      StdinMidPreserved sr sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.ok bs) ∗
          A.pool lim st_cur sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sr
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc cap ptr bs ∗ A.pool lim st_cur sr)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := cliIoPl00.base + 312#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl00.base + 88#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = 0#64 := (hcpu_r.readReg64 _).trans hx0
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
  have hcpu_e := hcpu_e0.1
  have ⟨hacp_re, hvm_re⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_e0 hnsp_e hsym_e
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool lim st_cur sr = A.pool lim st_cur se :=
    (A.pool_transport lim st_cur sr se hvm_re).symm
  rw [hpool_eq]
  exact cliIoReadStdin_ok_epilogue_b A lim hext0 hlo hhi hcl_e
    (hcpu_e.pc_eq.trans (by simp [arm64_norm])) (hcpu_e.status_eq.trans hrun_r') hsp0
    (hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx19)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx21)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx25)
    (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_ef _ hent =>
      hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
        ((StdinMidPreserved.of_alloc hacp_re).trans (StdinMidPreserved.of_alloc hacp_ef)) hent

/-- Post-`read` over-cap (`len = 1048576`, `n = 1`, `want = 1`) branch `+0x58 .. +0x84 → +0x164`. -/
private theorem cliIoReadStdin_after_read_overcap_b [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    {s0 sr : State} {sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4224 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl00.base + 88#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 4224#64)
    (hx0 : sr.readReg64 .x0 = 1#64)
    (hx19 : sr.readReg64 (.gpr 19#5) = sret) (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap 8))
    (hx23 : sr.readReg64 (.gpr 23#5) = 1#64)
    (hx25 : sr.readReg64 (.gpr 25#5) = 1048576#64)
    (hx26 : sr.readReg64 (.gpr 26#5) = 1048576#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      StdinMidPreserved sr sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.error ()) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents (cliIoCap 8) 1) st_cur) sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sr
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap 8)) ptr bs ∗
        A.pool lim st_cur sr)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := cliIoPl00.base + 356#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl00.base + 88#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = 1#64 := (hcpu_r.readReg64 _).trans hx0
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = 1#64 := (hcpu_r.readReg64 _).trans hx23
  have hx25_r' : sr'.readReg64 (.gpr 25#5) = 1048576#64 := (hcpu_r.readReg64 _).trans hx25
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_r.readReg64 _).trans hx26
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
  have hcpu_e := hcpu_e0.1
  have ⟨hacp_re, hvm_re⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_e0 hnsp_e hsym_e
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool lim st_cur sr = A.pool lim st_cur se :=
    (A.pool_transport lim st_cur sr se hvm_re).symm
  rw [hpool_eq]
  exact cliIoReadStdin_err_epilogue_b A lim hext0 hdealloc hlo hhi
    (cliIoCap_pos 8) (cliIoCap_lt_pow63 (by decide)) hcl_e
    (hcpu_e.pc_eq.trans (by simp [arm64_norm])) (hcpu_e.status_eq.trans hrun_r') hsp0
    (hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx19)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx21)
    (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_ef _ hent =>
      hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
        ((StdinMidPreserved.of_alloc hacp_re).trans (StdinMidPreserved.of_alloc hacp_ef)) hent

/-- Post-`read` in-cap no-grow (`0 < n ≤ want`, `len + n ≤ cap ≤ 1048576`) branch
    `+0x58 .. +0x90 → +0xc4 .. +0xc8 → +0xcc = 204#64`. -/
private theorem cliIoReadStdin_after_read_nogrow_b [CliIoPlacement]
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    {s0 sr : State} {sret ptr : BitVec 64} {Pre : SepProp}
    {cap len want n : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hn_pos : 0 < n) (hn_le_want : n ≤ want) (hwant_le : want ≤ 4096)
    (hlen_cap : len + n ≤ cap) (hcap_max : cap ≤ 1048576)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl00.base + 88#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 4224#64)
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 n)
    (hx19 : sr.readReg64 (.gpr 19#5) = sret) (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx23 : sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sr.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sr.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sr.readReg64 (.gpr 27#5) = 1048577#64)
    (hx29 : sr.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sc : State,
      sc.pc = cliIoPl00.base + 204#64 → sc.status = .Running → sc.sp = s0.sp - 4224#64 →
      sc.readReg64 (.gpr 19#5) = sret → sc.readReg64 (.gpr 20#5) = ptr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = 4096#64 → sc.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 26#5) = 1048576#64 → sc.readReg64 (.gpr 27#5) = 1048577#64 →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem →
      AllocCallPreserved sr sc → VmPreserved sr sc →
      SepWP P (s0.readReg64 .lr) sc Pre post oomProp) :
    SepWP P (s0.readReg64 .lr) sr Pre post oomProp := by
  have hn_beq0 : (BitVec.ofNat 64 n == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) (by omega) (by decide)
  have hbit63 : (BitVec.ofNat 64 n).getLsbD 63 = false := bit63_eq_zero_of_lt (by omega)
  have hule_w : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 want) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat]; omega
  have hult_w : (BitVec.ofNat 64 want).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le_want (by omega)
  have hsub26 : 1048576#64 - BitVec.ofNat 64 len = BitVec.ofNat 64 (1048576 - len) :=
    bv64_sub_ofNat (by omega)
  have hule_rem : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (1048576 - len)) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat]; omega
  have hult_rem : (BitVec.ofNat 64 (1048576 - len)).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false (by omega) (by omega)
  have hadd28 : BitVec.ofNat 64 n + BitVec.ofNat 64 len = BitVec.ofNat 64 (len + n) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hule_cap : (BitVec.ofNat 64 (len + n)).ule (BitVec.ofNat 64 cap) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat]; omega
  have hult_cap : (BitVec.ofNat 64 cap).ult (BitVec.ofNat 64 (len + n)) = false :=
    bv64_ult_ofNat_false hlen_cap (by omega)
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := cliIoPl00.base + 204#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl00.base + 88#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_r.readReg64 _).trans hx0
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_r.readReg64 _).trans hx21
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_r.readReg64 _).trans hx23
  have hx25_r' : sr'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len := (hcpu_r.readReg64 _).trans hx25
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_r.readReg64 _).trans hx26
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun sc hcpu_c0 hcl_c hnsp_c hsym_c => ?_
  have hcpu_c := hcpu_c0.1
  have ⟨hacp_rc, hvm_rc⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_c0 hnsp_c hsym_c
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  exact hcont sc (hcpu_c.pc_eq.trans (by simp [arm64_norm])) (hcpu_c.status_eq.trans hrun_r')
    (hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx19)
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm, hx25_r'])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm, hx26_r'])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx27)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx29)
    (hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    hcl_c hacp_rc hvm_rc

/-- Post-`read` in-cap grow (`0 < n ≤ want`, `cap < len + n ≤ 1048576`) branch
    `+0x58 .. +0x90 → +0x94 = 148#64`. -/
private theorem cliIoReadStdin_after_read_grow_b [CliIoPlacement]
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    {s0 sr : State} {sret ptr : BitVec 64} {Pre : SepProp}
    {cap len want n : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hn_pos : 0 < n) (hn_le_want : n ≤ want) (hwant_le : want ≤ 4096)
    (hgt_cap : cap < len + n) (hlen_max : len + n ≤ 1048576)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl00.base + 88#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 4224#64)
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 n)
    (hx19 : sr.readReg64 (.gpr 19#5) = sret) (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx23 : sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sr.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sr.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sr.readReg64 (.gpr 27#5) = 1048577#64)
    (hx29 : sr.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sg : State,
      sg.pc = cliIoPl00.base + 148#64 → sg.status = .Running → sg.sp = s0.sp - 4224#64 →
      sg.readReg64 .x0 = BitVec.ofNat 64 n →
      sg.readReg64 (.gpr 19#5) = sret → sg.readReg64 (.gpr 20#5) = ptr →
      sg.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sg.readReg64 (.gpr 24#5) = 4096#64 → sg.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sg.readReg64 (.gpr 26#5) = 1048576#64 → sg.readReg64 (.gpr 27#5) = 1048577#64 →
      sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) →
      sg.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sg = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sg.mem →
      AllocCallPreserved sr sg → VmPreserved sr sg →
      SepWP P (s0.readReg64 .lr) sg Pre post oomProp) :
    SepWP P (s0.readReg64 .lr) sr Pre post oomProp := by
  have hn_beq0 : (BitVec.ofNat 64 n == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) (by omega) (by decide)
  have hbit63 : (BitVec.ofNat 64 n).getLsbD 63 = false := bit63_eq_zero_of_lt (by omega)
  have hule_w : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 want) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat]; omega
  have hult_w : (BitVec.ofNat 64 want).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le_want (by omega)
  have hsub26 : 1048576#64 - BitVec.ofNat 64 len = BitVec.ofNat 64 (1048576 - len) :=
    bv64_sub_ofNat (by omega)
  have hule_rem : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (1048576 - len)) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat]; omega
  have hult_rem : (BitVec.ofNat 64 (1048576 - len)).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false (by omega) (by omega)
  have hadd28 : BitVec.ofNat 64 n + BitVec.ofNat 64 len = BitVec.ofNat 64 (len + n) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hule_cap : (BitVec.ofNat 64 (len + n)).ule (BitVec.ofNat 64 cap) = false := by
    simp [BitVec.ule, BitVec.toNat_ofNat]; omega
  have hult_cap : (BitVec.ofNat 64 cap).ult (BitVec.ofNat 64 (len + n)) = true :=
    bv64_ult_ofNat_true hgt_cap (by omega)
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := cliIoPl00.base + 148#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl00.base + 88#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_r.readReg64 _).trans hx0
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_r.readReg64 _).trans hx21
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_r.readReg64 _).trans hx23
  have hx25_r' : sr'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len := (hcpu_r.readReg64 _).trans hx25
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_r.readReg64 _).trans hx26
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun sg hcpu_g0 hcl_g hnsp_g hsym_g => ?_
  have hcpu_g := hcpu_g0.1
  have ⟨hacp_rg, hvm_rg⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_g0 hnsp_g hsym_g
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  exact hcont sg (hcpu_g.pc_eq.trans (by simp [arm64_norm])) (hcpu_g.status_eq.trans hrun_r')
    (hcpu_g.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx0_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx19)
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx21_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx25_r'])
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx26_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx27)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx29)
    (hcpu_g.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    hcl_g hacp_rg hvm_rg

/-- Step `+0x48 .. +0x54` and call `muslReadStdin32Spec`, landing at `+0x58 = 88#64`. -/
private theorem cliIoReadStdin_do_read_b [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadStdin32Spec)
    {s0 sl : State} {d0 : FdEntry} {sret ptr cap_bv : BitVec 64} {R_frame : SepProp}
    {len want stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4256 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hwant_le : want ≤ 4096)
    (hkind : d0.kind = .stdio) (hcanr : d0.accMode.canRead = true)
    (hfs : sl.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + len }))
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sl.mem)
    (hpc : sl.pc = cliIoPl00.base + 72#64) (hrun : sl.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sl.sp = s0.sp - 4224#64)
    (hx19 : sl.readReg64 (.gpr 19#5) = sret) (hx20 : sl.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sl.readReg64 (.gpr 21#5) = cap_bv)
    (hx23 : sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sl.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sl.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sl.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sl.readReg64 (.gpr 27#5) = 1048577#64)
    (hx29 : sl.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sl = calleeSavedVRegs s0)
    (hcont : ∀ (sr : State) (oldBuf : List (BitVec 8)),
      let rem := s0.fs.stdin.drop d0.offset
      let chunk := (rem.drop len).take want
      oldBuf.length = want →
      sr.pc = cliIoPl00.base + 88#64 → sr.status = .Running → sr.sp = s0.sp - 4224#64 →
      sr.readReg64 .x0 = BitVec.ofNat 64 chunk.length →
      sr.readReg64 (.gpr 19#5) = sret → sr.readReg64 (.gpr 20#5) = ptr →
      sr.readReg64 (.gpr 21#5) = cap_bv →
      sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want →
      sr.readReg64 (.gpr 24#5) = 4096#64 →
      sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sr.readReg64 (.gpr 26#5) = 1048576#64 →
      sr.readReg64 (.gpr 27#5) = 1048577#64 →
      sr.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs sr = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem →
      sr.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + (len + chunk.length) }) →
      sr.trace = sl.trace → sr.sigActions = sl.sigActions →
      SepWP P (s0.readReg64 .lr) sr
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
          (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
            memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want)) ∗
          R_frame ∗ A.pool lim st_cur sr)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sl
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        R_frame ∗ A.pool lim st_cur sl)
      post oomProp := by
  have hwant_toNat : (BitVec.ofNat 64 want).toNat = want := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  wp_conv_pre =>
    rw [memRegion_split_le (s0.sp - 4224#64) want 4096 hwant_le (by decide),
      memRegion_eq_exists_bytes (s0.sp - 4224#64) want (by omega)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro oldBuf
  wp_conv_pre =>
    rw [← sepConj_assoc (stackAt _ _), sepConj_comm (stackAt _ _) ⌜oldBuf.length = want⌝]
    simp only [sepConj_assoc]
  apply SepWP.pure_elim; intro hold_len
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
  intro sl' hcpu_l0
  have hcpu_l := hcpu_l0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_l' : sl'.pc = cliIoPl00.base + 72#64 := hcpu_l.pc_eq.trans hpc
  have hrun_l' : sl'.status = .Running := hcpu_l.status_eq.trans hrun
  have hsp_l_in : sl'.sp = s0.sp - 4224#64 := hcpu_l.sp_eq.trans hsp_eq
  have hsp_l' : sl'.spAligned = true := by
    rw [hcpu_l.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx23_l' : sl'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_l.readReg64 _).trans hx23
  wp_sym_steps
  refine SepWP.done cliIoReadStdin_read_pc (by simpa [arm64_norm] using hrun_l')
    fun sm_rd hcpu_rd0 hcl_rd hnsp_rd hsym_rd => ?_
  have hcpu_rd := hcpu_rd0.1
  have ⟨hacp_lrd, hvm_lrd⟩ :=
    vmPreserved_of_seg hcpu_l0 hcpu_rd0 hnsp_rd hsym_rd
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_lrd : A.pool lim st_cur sl = A.pool lim st_cur sm_rd :=
    (A.pool_transport lim st_cur sl sm_rd hvm_lrd).symm
  have hpc_rd : sm_rd.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym :=
    hcpu_rd.pc_eq.trans cliIoReadStdin_read_pc
  have hrun_rd : sm_rd.status = .Running := hcpu_rd.status_eq.trans hrun_l'
  have hsp_rd_eq : sm_rd.sp = s0.sp - 4224#64 :=
    hcpu_rd.sp_eq.trans ((by simp [arm64_norm] : _ = sl'.sp).trans hsp_l_in)
  have hsp_rd : sm_rd.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_rd_eq]; exact s0.spAligned_sub 4224#64 hsp0
  have hlr_rd : sm_rd.readReg64 .lr = cliIoPl00.base + 88#64 := by
    rw [hcpu_rd.readReg64 .lr]; simp [arm64_norm]
  have hx0_rd : sm_rd.readReg32 .x0 = 0#32 := by
    simp only [State.readReg32]; rw [hcpu_rd.readReg64 .x0]; simp [arm64_norm]
  have hx1_rd : sm_rd.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_rd.readReg64 .x1]; simp [arm64_norm]
  have hx2_rd : sm_rd.readReg64 .x2 = BitVec.ofNat 64 want := by
    rw [hcpu_rd.readReg64 .x2]; simp [arm64_norm]
  have hfs_rd : sm_rd.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + len }) :=
    hacp_lrd.1.trans hfs
  have hfds_rd : sm_rd.fs.fds 0#64 = some { d0 with offset := d0.offset + len } := by
    rw [hfs_rd]; simp [FsState.setFd]
  rw [hpool_eq_lrd]
  let d_cur : FdEntry := { d0 with offset := d0.offset + len }
  apply seqCodeLoaded hcl_rd (mid := cliIoPl00.base + 88#64)
  apply (SepWP.call_subroutine_frame hread
    (x := (s0.sp - 4224#64, BitVec.ofNat 64 want, d_cur, oldBuf))
    hpc_rd hrun_rd hsp_rd hlr_rd
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslReadStdin32Spec]
    rw [hsp_rd_eq, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_rd, hx1_rd, hx2_rd,
      by rw [hwant_toNat]; simp only [Arm64.MAX_RW_COUNT]; omega,
      by rw [hwant_toNat]; exact sp_sub_4224_va_bound (by omega) hsp_va hwant_le,
      by rw [hwant_toNat]; exact hold_len, hfds_rd, hkind, hcanr⟩, ?_⟩
    rw [stackAt_shrink (s0.sp - 4224#64) (stackBytes - 4224) 32 (by omega) (by omega)] at hm'
    exact Satisfies.mono (by sep_frame) hm'
  · intro sr hpc_sr hrun_sr hsp_sr hcs_rdsr
    refine SepWP.done hpc_sr hrun_sr fun hcl_sr => ?_
    wp_conv_pre => dsimp only [muslReadStdin32Spec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_sr, hfs_sr, htr_sr, hsys_sr⟩
    have hpool_eq_sr : A.pool lim st_cur sm_rd = A.pool lim st_cur sr :=
      (A.pool_transport lim st_cur sm_rd sr
        (vmPreserved_of_syscallPreserved_fds hsys_sr fun fd hlo hhi => by
          have hne : (BitVec.ofNat 64 fd == 0#64) = false := by
            rw [beq_eq_false_iff_ne]
            intro heq
            have hEqNat := congrArg BitVec.toNat heq
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : fd < 2 ^ 64)] at hEqNat
            omega
          rw [hfs_sr]
          dsimp only [FsState.setFd]
          rw [hne]
          simp only [Bool.false_eq_true, ↓reduceIte])).symm
    have hchunk_eq :
        (sm_rd.fs.stdin.drop d_cur.offset).take (BitVec.ofNat 64 want).toNat =
          ((s0.fs.stdin.drop d0.offset).drop len).take want := by
      rw [hfs_rd, FsState.stdin_setFd, hwant_toNat]
      dsimp only [d_cur]
      rw [← List.drop_drop]
    have hfs_sr' : sr.fs = s0.fs.setFd 0#64
        (some { d0 with offset := d0.offset + (len + (((s0.fs.stdin.drop d0.offset).drop len).take want).length) }) := by
      rw [hfs_sr, hchunk_eq, hfs_rd, FsState.setFd_setFd_same]
      dsimp only [d_cur]
      rw [Nat.add_assoc]
    have hsp_sr_eq : sr.sp = s0.sp - 4224#64 := hsp_sr.trans hsp_rd_eq
    refine SepWP.weaken_pre ?_
      (hcont sr oldBuf hold_len hpc_sr hrun_sr hsp_sr_eq
        (by rwa [hchunk_eq] at hx0_sr)
        (by rw [hcs_rdsr.readReg64_x19, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx19)
        (by rw [hcs_rdsr.readReg64_x20, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx20)
        (by rw [hcs_rdsr.readReg64_x21, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx21)
        (by rw [hcs_rdsr.readReg64_x23, hcpu_rd.readReg64]; simp only [arm64_norm]; exact hx23_l')
        (by rw [hcs_rdsr.readReg64_x24, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx24)
        (by rw [hcs_rdsr.readReg64_x25, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx25)
        (by rw [hcs_rdsr.readReg64_x26, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx26)
        (by rw [hcs_rdsr.readReg64_x27, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx27)
        (by rw [hcs_rdsr.readReg64_x29, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx29)
        (hcs_rdsr.vregs.trans (hcpu_rd.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs sl').trans (hcpu_l.calleeSavedVRegs.trans hvregs))))
        hcl_sr hfs_sr' (htr_sr.trans hacp_lrd.2.1) (hsys_sr.2.1.trans hacp_lrd.2.2.1))
    rw [hpool_eq_sr, hchunk_eq, hsp_rd_eq,
      stackAt_shrink (s0.sp - 4224#64) (stackBytes - 4224) 32 (by omega) (by omega)]
    sep_entail

/-- Shared budget-threaded `finish_grow` call + `+0x11c .. +0x12c → +0xcc` (`204#64`) join. -/
private theorem cliIoReadStdin_post_grow_b [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    {s0 sm_fg : State} {sret v0 v1 v2 oldCap oldPtr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {R_buf : SepProp}
    {newCap len n stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4256 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hnew_pos : 0 < newCap) (hnew_lt63 : newCap < 2 ^ 63)
    (hbs_le : bs.length ≤ newCap) (hno_null : ¬ NullAllowed newCap 1)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sm_fg.mem)
    (hpc : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
    (hrun : sm_fg.status = .Running) (hsp0 : s0.spAligned = true)
    (hsp_eq : sm_fg.sp = s0.sp - 4224#64) (hlr : sm_fg.readReg64 .lr = cliIoPl00.base + 284#64)
    (hx0 : sm_fg.readReg64 .x0 = s0.sp - 128#64)
    (hx1 : sm_fg.readReg64 .x1 = oldCap) (hx2 : sm_fg.readReg64 .x2 = oldPtr)
    (hx3 : sm_fg.readReg64 .x3 = BitVec.ofNat 64 newCap)
    (hx19 : sm_fg.readReg64 (.gpr 19#5) = sret)
    (hx22 : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap)
    (hx23 : sm_fg.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n)
    (hx24 : sm_fg.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sm_fg.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sm_fg.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sm_fg.readReg64 (.gpr 27#5) = 1048577#64)
    (hx28 : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n))
    (hx29 : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sm_fg = calleeSavedVRegs s0)
    (hoom_fg : ¬ FitsEvents M lim st_in (cliIoFinishGrowBudgetEvents oldCap newCap) →
      ∀ sf_oom : State, OomPreserved sm_fg sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl00.base + 204#64 → sc.status = .Running → sc.sp = s0.sp - 4224#64 →
      sc.readReg64 (.gpr 19#5) = sret → sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = 4096#64 → sc.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 26#5) = 1048576#64 → sc.readReg64 (.gpr 27#5) = 1048577#64 →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem → AllocCallPreserved sm_fg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 newCap) newPtr bs ∗
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st_in) sc)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sm_fg
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ cliIoVecBuf A.repAlloc oldCap oldPtr bs ∗
        A.pool lim st_in sm_fg)
      post oomProp := by
  have hnew_lt64 : newCap < 2 ^ 64 := Nat.lt_trans hnew_lt63 (by decide)
  have hsp_fg : sm_fg.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_eq]; exact s0.spAligned_sub 4224#64 hsp0
  have hfg_stk_le : 32 + allocHookStack ≤ stackBytes - 4224 := by omega
  have hfg_stk_hi : stackBytes - 4224 ≤ 2 ^ 64 := by omega
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 4224#64) (stackBytes - 4224) (32 + allocHookStack)
      hfg_stk_le hfg_stk_hi]
  apply seqCodeLoaded hcl (mid := cliIoPl00.base + 284#64)
  apply (SepWP.call_subroutine_frame hfg
    (x := (s0.sp - 128#64, st0, st1, st2, oldCap, oldPtr, bs, newCap, st_in))
    hpc hrun hsp_fg hlr
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun R_oom sf_oom _ hm_oom => by
      have hm' := Satisfies.drop_mid hm_oom
      dsimp only [MultiPlacedLib.withCodeLoaded, cliIoFinishGrowBudgetSpec] at hm'
      rcases (satisfies_pure_sepConj _ _ _).mp hm' with ⟨⟨_, hnot_fit, hoom_s⟩, hm_r⟩
      have hent := hoom_fg hnot_fit sf_oom hoom_s
      rw [← emp_sepConj R_oom] at hm_r
      exact Satisfies.mono (sepConj_mono_left hent) hm_r))
  · intro R' hm'
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoFinishGrowBudgetSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnew_pos, hnew_lt64, hbs_le⟩, ?_⟩
    rw [hsp_eq]
    have hcl_true : (⌜signalSessionIoMultiLib.CodeLoaded cliIoMpl sm_fg.mem⌝ : SepProp) = emp := by
      simp [hcl]
    rw [hcl_true, emp_sepConj]
    exact Satisfies.mono (by sep_frame) hm'
  · intro sm_fg' hpc_fg' hrun_fg' hsp_fg' hcs_fg'
    refine SepWP.done hpc_fg' hrun_fg' fun hcl_fg' => ?_
    wp_conv_pre =>
      dsimp only [MultiPlacedLib.withCodeLoaded, cliIoFinishGrowBudgetSpec]
      simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_left; intro isErr
    apply SepWP.exists_left; intro newPtr
    apply SepWP.exists_left; intro errW1
    apply SepWP.exists_left; intro errW2
    apply SepWP.pure_elim; intro hacp_fg
    cases isErr with
    | true =>
      wp_conv_pre =>
        simp only [↓reduceIte, sepConj_assoc]
        rw [sepConj_comm (stackAt sm_fg.sp (32 + allocHookStack)), sepConj_assoc]
      apply SepWP.pure_elim; intro hnull
      exact False.elim (hno_null hnull)
    | false =>
      wp_conv_pre =>
        simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        rw [sepConj_comm (stackAt sm_fg.sp (32 + allocHookStack)), sepConj_assoc]
      apply SepWP.pure_elim; intro _hnew_lt63'
      have hsp_fg'_eq : sm_fg'.sp = s0.sp - 4224#64 := hsp_fg'.trans hsp_eq
      have hx29_fg' : sm_fg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 :=
        hcs_fg'.readReg64_x29.trans hx29
      apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl_fg'
        (mid := cliIoPl00.base + 204#64)
      intro sj' hcpu_j0
      have hcpu_j := hcpu_j0.1
      change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
      have hpc_j' : sj'.pc = cliIoPl00.base + 284#64 := hcpu_j.pc_eq.trans hpc_fg'
      have hrun_j' : sj'.status = .Running := hcpu_j.status_eq.trans hrun_fg'
      have hsp_j' : sj'.spAligned = true := by
        rw [hcpu_j.spAligned]; simp only [State.spAligned]; rw [hsp_fg'_eq]
        exact s0.spAligned_sub 4224#64 hsp0
      have hx29_j' : sj'.readReg64 (.gpr 29#5) = s0.sp - 96#64 :=
        (hcpu_j.readReg64 _).trans hx29_fg'
      wp_conv_pre =>
        rw [show vecHeader (s0.sp - 128#64) 0#64 newPtr (BitVec.ofNat 64 newCap) =
          ((s0.sp - 128#64) ↦₆₄ 0#64) ∗ ((s0.sp - 120#64) ↦₆₄ newPtr) ∗
          ((s0.sp - 112#64) ↦₆₄ BitVec.ofNat 64 newCap) by
            simp only [vecHeader, bv_lin_norm]]
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_j')
        fun sc hcpu_c0 hcl_c hnsp_c hsym_c => ?_
      have hcpu_c := hcpu_c0.1
      have ⟨hacp_jc, hvm_jc⟩ :=
        vmPreserved_of_seg hcpu_j0 hcpu_c0 hnsp_c hsym_c
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_jc :
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st_in) sm_fg' =
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st_in) sc :=
        (A.pool_transport lim _ sm_fg' sc hvm_jc).symm
      have hpc_c : sc.pc = cliIoPl00.base + 204#64 := hcpu_c.pc_eq.trans (by simp [arm64_norm])
      have hrun_c : sc.status = .Running := hcpu_c.status_eq.trans hrun_j'
      have hsp_c : sc.sp = s0.sp - 4224#64 :=
        hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = sj'.sp).trans (hcpu_j.sp_eq.trans hsp_fg'_eq))
      have hx19_c : sc.readReg64 (.gpr 19#5) = sret := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x19.trans hx19)
      have hx20_c : sc.readReg64 (.gpr 20#5) = newPtr := by
        rw [hcpu_c.readReg64]; simp [arm64_norm]
      have hx22_c : sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x22.trans hx22)
      have hx23_c : sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x23.trans hx23)
      have hx24_c : sc.readReg64 (.gpr 24#5) = 4096#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x24.trans hx24)
      have hx25_c : sc.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x25.trans hx25)
      have hx26_c : sc.readReg64 (.gpr 26#5) = 1048576#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x26.trans hx26)
      have hx27_c : sc.readReg64 (.gpr 27#5) = 1048577#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x27.trans hx27)
      have hx28_c : sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x28.trans hx28)
      have hx29_c : sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact hx29_j'
      have hvregs_c : calleeSavedVRegs sc = calleeSavedVRegs s0 :=
        hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sj').trans
          (hcpu_j.calleeSavedVRegs.trans (hcs_fg'.2.2.2.2.2.2.2.2.2.2.2.trans hvregs)))
      have hacp_fg_c : AllocCallPreserved sm_fg sc := allocCallPreserved_trans hacp_fg hacp_jc
      refine SepWP.weaken_pre ?_
        (hcont sc newPtr newPtr (BitVec.ofNat 64 newCap)
          hpc_c hrun_c hsp_c hx19_c hx20_c hx22_c hx23_c hx24_c hx25_c hx26_c hx27_c hx28_c hx29_c
          hvregs_c hcl_c hacp_fg_c)
      rw [hpool_eq_jc, hsp_eq,
        stackAt_shrink (s0.sp - 4224#64) (stackBytes - 4224) (32 + allocHookStack) hfg_stk_le hfg_stk_hi]
      simp only [vecHeader, bv_lin_norm]
      sep_entail

/-- `cap = 0` growth branch (`+0x94 = 148#64 .. +0x118 = 280#64` → `cliIoReadStdin_post_grow_b` → `+0xcc = 204#64`):
    steps `0 → 4096` (`0` inner back-edges) and calls `finish_grow`. -/
private theorem cliIoReadStdin_grow_from_zero_b [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    {s0 sg : State} {sret v0 v1 v2 oldPtr st0 st1 st2 st3 : BitVec 64}
    {R_buf : SepProp} {n stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4256 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (_hn_pos : 0 < n) (hn_le : n ≤ 4096)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sg.mem)
    (hpc : sg.pc = cliIoPl00.base + 148#64)
    (hrun : sg.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : sg.sp = s0.sp - 4224#64)
    (hx0 : sg.readReg64 .x0 = BitVec.ofNat 64 n)
    (hx19 : sg.readReg64 (.gpr 19#5) = sret)
    (hx20 : sg.readReg64 (.gpr 20#5) = oldPtr)
    (hx21 : sg.readReg64 (.gpr 21#5) = 0#64)
    (hx24 : sg.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sg.readReg64 (.gpr 25#5) = 0#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sg.readReg64 (.gpr 27#5) = 1048577#64)
    (hx28 : sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 n)
    (hx29 : sg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sg = calleeSavedVRegs s0)
    (hoom_sg : ¬ FitsEvents M lim st_in (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) →
      ∀ sf_oom : State, OomPreserved sg sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl00.base + 204#64 → sc.status = .Running →
      sc.sp = s0.sp - 4224#64 →
      sc.readReg64 (.gpr 19#5) = sret →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap 0) →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = 4096#64 →
      sc.readReg64 (.gpr 25#5) = 0#64 →
      sc.readReg64 (.gpr 26#5) = 1048576#64 →
      sc.readReg64 (.gpr 27#5) = 1048577#64 →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem →
      AllocCallPreserved sg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
          R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗
          ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗
          vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap 0)) newPtr [] ∗
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) st_in) sc)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sg
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
        R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc 0#64 oldPtr [] ∗
        A.pool lim st_in sg)
      post oomProp := by
  have hult_false : (4096#64 : BitVec 64).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le (by decide)
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
  intro sg' hcpu_g0
  have hcpu_g := hcpu_g0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_g' : sg'.pc = cliIoPl00.base + 148#64 := hcpu_g.pc_eq.trans hpc
  have hrun_g' : sg'.status = .Running := hcpu_g.status_eq.trans hrun
  have hsp_g' : sg'.spAligned = true := by
    rw [hcpu_g.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_g' : sg'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx0
  have hx19_g' : sg'.readReg64 (.gpr 19#5) = sret := (hcpu_g.readReg64 _).trans hx19
  have hx20_g' : sg'.readReg64 (.gpr 20#5) = oldPtr := (hcpu_g.readReg64 _).trans hx20
  have hx21_g' : sg'.readReg64 (.gpr 21#5) = 0#64 := (hcpu_g.readReg64 _).trans hx21
  have hx24_g' : sg'.readReg64 (.gpr 24#5) = 4096#64 := (hcpu_g.readReg64 _).trans hx24
  have hx25_g' : sg'.readReg64 (.gpr 25#5) = 0#64 := (hcpu_g.readReg64 _).trans hx25
  have hx26_g' : sg'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_g.readReg64 _).trans hx26
  have hx27_g' : sg'.readReg64 (.gpr 27#5) = 1048577#64 := (hcpu_g.readReg64 _).trans hx27
  have hx28_g' : sg'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx28
  have hx29_g' : sg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 := (hcpu_g.readReg64 _).trans hx29
  wp_sym_steps
  refine SepWP.done cliIoReadStdin_grow_pc (by simpa [arm64_norm] using hrun_g')
    fun sm_fg hcpu_fg0 hcl_fg hnsp_fg hsym_fg => ?_
  have hcpu_fg := hcpu_fg0.1
  have ⟨hacp_gfg, hvm_gfg⟩ :=
    vmPreserved_of_seg hcpu_g0 hcpu_fg0 hnsp_fg hsym_fg
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_gfg : A.pool lim st_in sg = A.pool lim st_in sm_fg :=
    (A.pool_transport lim st_in sg sm_fg hvm_gfg).symm
  have hpc_fg : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym :=
    hcpu_fg.pc_eq.trans cliIoReadStdin_grow_pc
  have hrun_fg : sm_fg.status = .Running := hcpu_fg.status_eq.trans hrun_g'
  have hsp_fg : sm_fg.sp = s0.sp - 4224#64 :=
    hcpu_fg.sp_eq.trans ((by simp [arm64_norm] : _ = sg'.sp).trans (hcpu_g.sp_eq.trans hsp_eq))
  have hlr_fg : sm_fg.readReg64 .lr = cliIoPl00.base + 284#64 := by
    rw [hcpu_fg.readReg64 .lr]; simp [arm64_norm]
  have hx0_fg : sm_fg.readReg64 .x0 = s0.sp - 128#64 := by
    rw [hcpu_fg.readReg64 .x0]; simp [arm64_norm]
  have hx1_fg : sm_fg.readReg64 .x1 = 0#64 := by
    rw [hcpu_fg.readReg64 .x1]; simp [arm64_norm]
  have hx2_fg : sm_fg.readReg64 .x2 = oldPtr := by
    rw [hcpu_fg.readReg64 .x2]; simp [arm64_norm]
  have hx3_fg : sm_fg.readReg64 .x3 = BitVec.ofNat 64 (cliIoCap 0) := by
    rw [hcpu_fg.readReg64 .x3]; simp [arm64_norm, cliIoCap_zero]
  have hx19_fg : sm_fg.readReg64 (.gpr 19#5) = sret := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx19_g']
  have hx22_fg : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap 0) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, cliIoCap_zero]
  have hx23_fg : sm_fg.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx24_fg : sm_fg.readReg64 (.gpr 24#5) = 4096#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx24_g']
  have hx25_fg : sm_fg.readReg64 (.gpr 25#5) = BitVec.ofNat 64 0 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx25_g']
  have hx26_fg : sm_fg.readReg64 (.gpr 26#5) = 1048576#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx26_g']
  have hx27_fg : sm_fg.readReg64 (.gpr 27#5) = 1048577#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx27_g']
  have hx28_fg : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (0 + n) := by
    rw [hcpu_fg.readReg64]; simpa [arm64_norm] using hx28_g'
  have hx29_fg : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx29_g']
  have hvregs_fg : calleeSavedVRegs sm_fg = calleeSavedVRegs s0 :=
    hcpu_fg.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sg').trans
      (hcpu_g.calleeSavedVRegs.trans hvregs))
  rw [hpool_eq_gfg]
  exact cliIoReadStdin_post_grow_b A lim hext0 hfg hlo hhi
    (by decide : 0 < cliIoCap 0) (cliIoCap_lt_pow63 (by decide))
    (Nat.zero_le _) (not_nullAllowed_cliIoCap_budget (by decide))
    hcl_fg hpc_fg hrun_fg hsp0 hsp_fg hlr_fg
    hx0_fg hx1_fg hx2_fg hx3_fg hx19_fg hx22_fg hx23_fg hx24_fg hx25_fg hx26_fg hx27_fg hx28_fg hx29_fg
    hvregs_fg
    (fun hnot sf_oom hoom_pres =>
      hoom_sg hnot sf_oom (oomPreserved_of_allocCallPreserved hacp_gfg hoom_pres))
    (fun sc newPtr st1' st2' hpc_c hrun_c hsp_c hx19_c hx20_c hx22_c hx23_c hx24_c hx25_c
        hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c hacp_fgc =>
      hcont sc newPtr st1' st2' hpc_c hrun_c hsp_c hx19_c hx20_c hx22_c hx23_c hx24_c
        (by simpa using hx25_c) hx26_c hx27_c (by simpa using hx28_c) hx29_c hvregs_c hcl_c
        (allocCallPreserved_trans hacp_gfg hacp_fgc))

/-- `cap = cliIoCap j` growth branch (`+0x94 = 148#64 .. +0x118 = 280#64` → `cliIoReadStdin_post_grow_b` → `+0xcc = 204#64`):
    steps `cliIoCap j → cliIoCap (j + 1)` (`1` inner back-edge) and calls `finish_grow`. -/
private theorem cliIoReadStdin_grow_from_pos_b [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    {s0 sg : State} {sret v0 v1 v2 oldPtr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {R_buf : SepProp}
    {j len n stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4256 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hj1 : j + 1 ≤ 8)
    (hlen_le_cap : len ≤ cliIoCap j)
    (hbs_len : bs.length = len)
    (hgt_cap : cliIoCap j < len + n)
    (hle_next : len + n ≤ cliIoCap (j + 1))
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sg.mem)
    (hpc : sg.pc = cliIoPl00.base + 148#64)
    (hrun : sg.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : sg.sp = s0.sp - 4224#64)
    (hx0 : sg.readReg64 .x0 = BitVec.ofNat 64 n)
    (hx19 : sg.readReg64 (.gpr 19#5) = sret)
    (hx20 : sg.readReg64 (.gpr 20#5) = oldPtr)
    (hx21 : sg.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap j))
    (hx24 : sg.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sg.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sg.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sg.readReg64 (.gpr 27#5) = 1048577#64)
    (hx28 : sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n))
    (hx29 : sg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sg = calleeSavedVRegs s0)
    (hoom_sg :
      ¬ FitsEvents M lim st_in
          (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1))) →
      ∀ sf_oom : State, OomPreserved sg sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl00.base + 204#64 → sc.status = .Running →
      sc.sp = s0.sp - 4224#64 →
      sc.readReg64 (.gpr 19#5) = sret →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap (j + 1)) →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = 4096#64 →
      sc.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 26#5) = 1048576#64 →
      sc.readReg64 (.gpr 27#5) = 1048577#64 →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem →
      AllocCallPreserved sg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
          R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗
          ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗
          vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap (j + 1))) newPtr bs ∗
          A.pool lim
            (M.stepEvents
              (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1)))
              st_in) sc)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sg
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
        R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap j)) oldPtr bs ∗
        A.pool lim st_in sg)
      post oomProp := by
  have hj9 : j ≤ 9 := by omega
  have hj1_9 : j + 1 ≤ 9 := by omega
  have hcap_pos : 0 < cliIoCap j := cliIoCap_pos j
  have hcap_lt64 : cliIoCap j < 2 ^ 64 := cliIoCap_lt_pow64 hj9
  have hnext_lt64 : cliIoCap (j + 1) < 2 ^ 64 := cliIoCap_lt_pow64 hj1_9
  have hcap_beq0 : (BitVec.ofNat 64 (cliIoCap j) == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) hcap_lt64 (by decide)
  have hlsl1 : (BitVec.ofNat 64 (cliIoCap j)) <<< 1 = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [bv64_shiftLeft1_ofNat (by rw [← cliIoCap_succ]; exact hnext_lt64), ← cliIoCap_succ]
  have hult1 : (BitVec.ofNat 64 (cliIoCap j)).ult (BitVec.ofNat 64 (len + n)) = true :=
    bv64_ult_ofNat_true hgt_cap (Nat.lt_of_le_of_lt hle_next hnext_lt64)
  have hult2 : (BitVec.ofNat 64 (cliIoCap (j + 1))).ult (BitVec.ofNat 64 (len + n)) = false :=
    bv64_ult_ofNat_false hle_next hnext_lt64
  have hclamp :
      (if (BitVec.ofNat 64 (cliIoCap (j + 1))).ult 1048576#64 = true
       then BitVec.ofNat 64 (cliIoCap (j + 1))
       else 1048576#64) = BitVec.ofNat 64 (cliIoCap (j + 1)) :=
    cliIoStdin_cap_clamp_bv hj1
  have hcap_lt_next : cliIoCap j < cliIoCap (j + 1) := cliIoCap_strictMono (Nat.lt_succ_self j)
  have hsub_hi :
      (BitVec.ofNat 64 (cliIoCap j) - BitVec.ofNat 64 len).ult
        (BitVec.ofNat 64 (cliIoCap (j + 1)) - BitVec.ofNat 64 len) = true := by
    rw [bv64_sub_ofNat hlen_le_cap,
      bv64_sub_ofNat (Nat.le_trans hlen_le_cap (Nat.le_of_lt hcap_lt_next))]
    exact bv64_ult_ofNat_true (by omega) (by omega)
  have hnext_ult_len : (BitVec.ofNat 64 (cliIoCap (j + 1))).ult (BitVec.ofNat 64 len) = false :=
    bv64_ult_ofNat_false (Nat.le_trans hlen_le_cap (Nat.le_of_lt hcap_lt_next)) hnext_lt64
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
  intro sg' hcpu_g0
  have hcpu_g := hcpu_g0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_g' : sg'.pc = cliIoPl00.base + 148#64 := hcpu_g.pc_eq.trans hpc
  have hrun_g' : sg'.status = .Running := hcpu_g.status_eq.trans hrun
  have hsp_g' : sg'.spAligned = true := by
    rw [hcpu_g.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_g' : sg'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx0
  have hx19_g' : sg'.readReg64 (.gpr 19#5) = sret := (hcpu_g.readReg64 _).trans hx19
  have hx20_g' : sg'.readReg64 (.gpr 20#5) = oldPtr := (hcpu_g.readReg64 _).trans hx20
  have hx21_g' : sg'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap j) :=
    (hcpu_g.readReg64 _).trans hx21
  have hx24_g' : sg'.readReg64 (.gpr 24#5) = 4096#64 := (hcpu_g.readReg64 _).trans hx24
  have hx25_g' : sg'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len := (hcpu_g.readReg64 _).trans hx25
  have hx26_g' : sg'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_g.readReg64 _).trans hx26
  have hx27_g' : sg'.readReg64 (.gpr 27#5) = 1048577#64 := (hcpu_g.readReg64 _).trans hx27
  have hx28_g' : sg'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) :=
    (hcpu_g.readReg64 _).trans hx28
  have hx29_g' : sg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 := (hcpu_g.readReg64 _).trans hx29
  wp_sym_steps
  refine SepWP.done cliIoReadStdin_grow_pc (by simpa [arm64_norm] using hrun_g')
    fun sm_fg hcpu_fg0 hcl_fg hnsp_fg hsym_fg => ?_
  have hcpu_fg := hcpu_fg0.1
  have ⟨hacp_gfg, hvm_gfg⟩ :=
    vmPreserved_of_seg hcpu_g0 hcpu_fg0 hnsp_fg hsym_fg
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_gfg : A.pool lim st_in sg = A.pool lim st_in sm_fg :=
    (A.pool_transport lim st_in sg sm_fg hvm_gfg).symm
  have hpc_fg : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym :=
    hcpu_fg.pc_eq.trans cliIoReadStdin_grow_pc
  have hrun_fg : sm_fg.status = .Running := hcpu_fg.status_eq.trans hrun_g'
  have hsp_fg : sm_fg.sp = s0.sp - 4224#64 :=
    hcpu_fg.sp_eq.trans ((by simp [arm64_norm] : _ = sg'.sp).trans (hcpu_g.sp_eq.trans hsp_eq))
  have hlr_fg : sm_fg.readReg64 .lr = cliIoPl00.base + 284#64 := by
    rw [hcpu_fg.readReg64 .lr]; simp [arm64_norm]
  have hx0_fg : sm_fg.readReg64 .x0 = s0.sp - 128#64 := by
    rw [hcpu_fg.readReg64 .x0]; simp [arm64_norm]
  have hx1_fg : sm_fg.readReg64 .x1 = BitVec.ofNat 64 (cliIoCap j) := by
    rw [hcpu_fg.readReg64 .x1]; simp [arm64_norm]
  have hx2_fg : sm_fg.readReg64 .x2 = oldPtr := by
    rw [hcpu_fg.readReg64 .x2]; simp [arm64_norm]
  have hx3_fg : sm_fg.readReg64 .x3 = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [hcpu_fg.readReg64 .x3]; simp [arm64_norm]
  have hx19_fg : sm_fg.readReg64 (.gpr 19#5) = sret := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx19_g']
  have hx22_fg : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx23_fg : sm_fg.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx24_fg : sm_fg.readReg64 (.gpr 24#5) = 4096#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx24_g']
  have hx25_fg : sm_fg.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx25_g']
  have hx26_fg : sm_fg.readReg64 (.gpr 26#5) = 1048576#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx26_g']
  have hx27_fg : sm_fg.readReg64 (.gpr 27#5) = 1048577#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx27_g']
  have hx28_fg : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx28_g']
  have hx29_fg : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx29_g']
  have hvregs_fg : calleeSavedVRegs sm_fg = calleeSavedVRegs s0 :=
    hcpu_fg.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sg').trans
      (hcpu_g.calleeSavedVRegs.trans hvregs))
  rw [hpool_eq_gfg]
  exact cliIoReadStdin_post_grow_b A lim hext0 hfg hlo hhi
    (cliIoCap_pos (j + 1)) (cliIoCap_lt_pow63 hj1_9)
    (by rw [hbs_len]; omega) (not_nullAllowed_cliIoCap_budget hj1_9)
    hcl_fg hpc_fg hrun_fg hsp0 hsp_fg hlr_fg
    hx0_fg hx1_fg hx2_fg hx3_fg hx19_fg hx22_fg hx23_fg hx24_fg hx25_fg hx26_fg hx27_fg hx28_fg hx29_fg
    hvregs_fg
    (fun hnot sf_oom hoom_pres =>
      hoom_sg hnot sf_oom (oomPreserved_of_allocCallPreserved hacp_gfg hoom_pres))
    (fun sc newPtr st1' st2' hpc_c hrun_c hsp_c hx19_c hx20_c hx22_c hx23_c hx24_c hx25_c
        hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c hacp_fgc =>
      hcont sc newPtr st1' st2' hpc_c hrun_c hsp_c hx19_c hx20_c hx22_c hx23_c hx24_c
        hx25_c hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c
        (allocCallPreserved_trans hacp_gfg hacp_fgc))

/-- Shared `memcpy(ptr + len, sp, chunk)` + back-edge `+0xdc .. +0xf4 → +0x48 = 72#64` join. -/
private theorem cliIoReadStdin_memcpy_backedge_b [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
      allocMemcpyVmSpec)
    {s0 sc : State} {sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {rem chunk oldBuf : List (BitVec 8)}
    {cap len want stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcap_pos : 0 < cap) (hcap_lt63 : cap < 2 ^ 63)
    (hlen_r : len + chunk.length ≤ rem.length)
    (hlen_cap : len + chunk.length ≤ cap)
    (hlen_max : len + chunk.length ≤ 1048576)
    (hwant_le : want ≤ 4096)
    (hold_len : oldBuf.length = want)
    (hn_le_want : chunk.length ≤ want)
    (hchunk_eq : chunk = (rem.drop len).take want)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem)
    (hpc : sc.pc = cliIoPl00.base + 204#64)
    (hrun : sc.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : sc.sp = s0.sp - 4224#64)
    (hx19 : sc.readReg64 (.gpr 19#5) = sret)
    (hx20 : sc.readReg64 (.gpr 20#5) = ptr)
    (hx22 : sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap)
    (hx23 : sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 chunk.length)
    (hx24 : sc.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sc.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sc.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sc.readReg64 (.gpr 27#5) = 1048577#64)
    (hx28 : sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + chunk.length))
    (hx29 : sc.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sc = calleeSavedVRegs s0)
    (hcont : ∀ sn : State,
      sn.pc = cliIoPl00.base + 72#64 → sn.status = .Running → sn.sp = s0.sp - 4224#64 →
      sn.readReg64 (.gpr 19#5) = sret → sn.readReg64 (.gpr 20#5) = ptr →
      sn.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sn.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 1048576 (len + chunk.length)) →
      sn.readReg64 (.gpr 24#5) = 4096#64 →
      sn.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (len + chunk.length) →
      sn.readReg64 (.gpr 26#5) = 1048576#64 → sn.readReg64 (.gpr 27#5) = 1048577#64 →
      sn.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sn = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sn.mem → StdinMidPreserved sc sn →
      SepWP P (s0.readReg64 .lr) sn
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take (len + chunk.length)) ∗
          A.pool lim st_cur sn)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sc
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
        (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
          memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want)) ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take len) ∗
        A.pool lim st_cur sc)
      post oomProp := by
  have hcap_lt64 : cap < 2 ^ 64 := Nat.lt_trans hcap_lt63 (by decide)
  have htake_len : (rem.take len).length = len := List.length_take_of_le (by omega)
  wp_conv_pre =>
    rw [cliIoVecBuf_unpack_pos A.repAlloc hcap_pos hcap_lt63]
    simp only [sepConj_assoc, sepConj_pure_mid]
  apply SepWP.pure_elim; rintro ⟨_, _, hptr_ne0⟩
  wp_conv_pre =>
    rw [htake_len,
      memRegion_split_le (ptr + BitVec.ofNat 64 len) chunk.length (cap - len) (by omega) (by omega),
      show ptr + BitVec.ofNat 64 len + BitVec.ofNat 64 chunk.length =
        ptr + BitVec.ofNat 64 (len + chunk.length) by rw [BitVec.ofNat_add]; bv_lin,
      show cap - len - chunk.length = cap - (len + chunk.length) by omega,
      pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
    simp only [sepConj_assoc]
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
  intro sc' hcpu_c0
  have hcpu_c := hcpu_c0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_c' : sc'.pc = cliIoPl00.base + 204#64 := hcpu_c.pc_eq.trans hpc
  have hrun_c' : sc'.status = .Running := hcpu_c.status_eq.trans hrun
  have hsp_c_in : sc'.sp = s0.sp - 4224#64 := hcpu_c.sp_eq.trans hsp_eq
  have hsp_c' : sc'.spAligned = true := by
    rw [hcpu_c.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx20_c' : sc'.readReg64 (.gpr 20#5) = ptr := (hcpu_c.readReg64 _).trans hx20
  have hx23_c' : sc'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 chunk.length :=
    (hcpu_c.readReg64 _).trans hx23
  have hx25_c' : sc'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len :=
    (hcpu_c.readReg64 _).trans hx25
  wp_sym_steps
  refine SepWP.done cliIoReadStdin_memcpy_pc (by simpa [arm64_norm] using hrun_c')
    fun sm_mc hcpu_mc0 hcl_mc hnsp_mc hsym_mc => ?_
  have hcpu_mc := hcpu_mc0.1
  have ⟨hacp_cmc, hvm_cmc⟩ :=
    vmPreserved_of_seg hcpu_c0 hcpu_mc0 hnsp_mc hsym_mc
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_cmc : A.pool lim st_cur sc = A.pool lim st_cur sm_mc :=
    (A.pool_transport lim st_cur sc sm_mc hvm_cmc).symm
  have hpc_mc : sm_mc.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym :=
    hcpu_mc.pc_eq.trans cliIoReadStdin_memcpy_pc
  have hrun_mc : sm_mc.status = .Running := hcpu_mc.status_eq.trans hrun_c'
  have hsp_mc_eq : sm_mc.sp = s0.sp - 4224#64 :=
    hcpu_mc.sp_eq.trans ((by simp [arm64_norm] : _ = sc'.sp).trans hsp_c_in)
  have hsp_mc : sm_mc.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_mc_eq]; exact s0.spAligned_sub 4224#64 hsp0
  have hlr_mc : sm_mc.readReg64 .lr = cliIoPl00.base + 220#64 := by
    rw [hcpu_mc.readReg64 .lr]; simp [arm64_norm]
  have hx0_mc : sm_mc.readReg64 .x0 = ptr + BitVec.ofNat 64 len := by
    rw [hcpu_mc.readReg64 .x0]; simp [arm64_norm]
  have hx1_mc : sm_mc.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_mc.readReg64 .x1]; simp [arm64_norm]
  have hx2_mc : sm_mc.readReg64 .x2 = BitVec.ofNat 64 chunk.length := by
    rw [hcpu_mc.readReg64 .x2]; simp [arm64_norm, hchunk_eq]
  apply seqCodeLoaded hcl_mc (mid := cliIoPl00.base + 220#64)
  apply (SepWP.call_subroutine_frame hmemcpy
    (x := (ptr + BitVec.ofNat 64 len, s0.sp - 4224#64, chunk))
    hpc_mc hrun_mc hsp_mc hlr_mc
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [allocMemcpyVmSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    have hchunk_lt64 : chunk.length < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.le_trans hn_le_want hwant_le) (by decide)
    refine ⟨⟨hx0_mc, hx1_mc, hx2_mc, hchunk_lt64⟩, ?_⟩
    rw [hpool_eq_cmc] at hm'
    exact Satisfies.mono (by sep_frame) hm'
  · intro sm_mc' hpc_mc' hrun_mc' hsp_mc' hcs_mc'
    refine SepWP.done hpc_mc' hrun_mc' fun hcl_mc' => ?_
    wp_conv_pre => dsimp only [allocMemcpyVmSpec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hacp_mc, hvm_mc⟩
    have hmid_mc : StdinMidPreserved sm_mc sm_mc' := StdinMidPreserved.of_alloc hacp_mc
    have hpool_eq_mc : A.pool lim st_cur sm_mc = A.pool lim st_cur sm_mc' :=
      (A.pool_transport lim st_cur sm_mc sm_mc' hvm_mc).symm
    have hsp_mc'_eq : sm_mc'.sp = s0.sp - 4224#64 := hsp_mc'.trans hsp_mc_eq
    have hx22_mc' : sm_mc'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap :=
      hcs_mc'.readReg64_x22.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 22#5)).trans
          ((hcpu_c.readReg64 _).trans hx22)))
    have hx24_mc' : sm_mc'.readReg64 (.gpr 24#5) = 4096#64 :=
      hcs_mc'.readReg64_x24.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 24#5)).trans
          ((hcpu_c.readReg64 _).trans hx24)))
    have hx27_mc' : sm_mc'.readReg64 (.gpr 27#5) = 1048577#64 :=
      hcs_mc'.readReg64_x27.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 27#5)).trans
          ((hcpu_c.readReg64 _).trans hx27)))
    have hx28_mc' : sm_mc'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + chunk.length) :=
      hcs_mc'.readReg64_x28.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 28#5)).trans
          ((hcpu_c.readReg64 _).trans hx28)))
    have hsub27 :
        1048577#64 - BitVec.ofNat 64 (len + chunk.length) =
          BitVec.ofNat 64 (1048576 + 1 - (len + chunk.length)) := by
      change BitVec.ofNat 64 1048577 - BitVec.ofNat 64 (len + chunk.length) = _
      exact bv64_sub_ofNat (by omega)
    have hule :
        (BitVec.ofNat 64 (len + ((rem.drop len).take want).length)).ule 1048576#64 = true := by
      rw [← hchunk_eq]
      simp [BitVec.ule, BitVec.toNat_ofNat]; omega
    apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl_mc'
      (mid := cliIoPl00.base + 72#64)
    intro sb' hcpu_b0
    have hcpu_b := hcpu_b0.1
    change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
    have hpc_b' : sb'.pc = cliIoPl00.base + 220#64 := hcpu_b.pc_eq.trans hpc_mc'
    have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_mc'
    have hsp_b' : sb'.spAligned = true := by
      rw [hcpu_b.spAligned]; simp only [State.spAligned]; rw [hsp_mc'_eq]
      exact s0.spAligned_sub 4224#64 hsp0
    have hx22_b' : sb'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap :=
      (hcpu_b.readReg64 _).trans hx22_mc'
    have hx24_b' : sb'.readReg64 (.gpr 24#5) = 4096#64 :=
      (hcpu_b.readReg64 _).trans hx24_mc'
    have hx27_b' : sb'.readReg64 (.gpr 27#5) = 1048577#64 :=
      (hcpu_b.readReg64 _).trans hx27_mc'
    have hx28_b' : sb'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + chunk.length) :=
      (hcpu_b.readReg64 _).trans hx28_mc'
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
      fun sn hcpu_n0 hcl_n hnsp_n hsym_n => ?_
    have hcpu_n := hcpu_n0.1
    have ⟨hacp_bn, hvm_bn⟩ :=
      vmPreserved_of_seg hcpu_b0 hcpu_n0 hnsp_n hsym_n
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_bn : A.pool lim st_cur sm_mc' = A.pool lim st_cur sn :=
      (A.pool_transport lim st_cur sm_mc' sn hvm_bn).symm
    have hpc_n : sn.pc = cliIoPl00.base + 72#64 := by
      rw [hcpu_n.pc_eq]; simp [arm64_norm]
    have hrun_n : sn.status = .Running := hcpu_n.status_eq.trans hrun_b'
    have hsp_n : sn.sp = s0.sp - 4224#64 :=
      hcpu_n.sp_eq.trans ((by simp [arm64_norm] : _ = sb'.sp).trans (hcpu_b.sp_eq.trans hsp_mc'_eq))
    have hx19_n : sn.readReg64 (.gpr 19#5) = sret := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x19, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx19
    have hx20_n : sn.readReg64 (.gpr 20#5) = ptr := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x20, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact hx20_c'
    have hx21_n : sn.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := by
      rw [hcpu_n.readReg64]; simp [arm64_norm]
    have hx23_n : sn.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 1048576 (len + chunk.length)) := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]; rw [← hchunk_eq, hsub27]
      exact wantBytes_csel_bv hlen_max (by decide)
    have hx24_n : sn.readReg64 (.gpr 24#5) = 4096#64 := by
      rw [hcpu_n.readReg64]; simp [arm64_norm, hx24_b']
    have hx25_n : sn.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (len + chunk.length) := by
      rw [hcpu_n.readReg64]; simp [arm64_norm, hchunk_eq]
    have hx26_n : sn.readReg64 (.gpr 26#5) = 1048576#64 := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x26, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx26
    have hx27_n : sn.readReg64 (.gpr 27#5) = 1048577#64 := by
      rw [hcpu_n.readReg64]; simp [arm64_norm, hx27_b']
    have hx29_n : sn.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x29, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx29
    have hvregs_n : calleeSavedVRegs sn = calleeSavedVRegs s0 :=
      hcpu_n.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
        (hcpu_b.calleeSavedVRegs.trans (hcs_mc'.vregs.trans
          (hcpu_mc.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sc').trans
            (hcpu_c.calleeSavedVRegs.trans hvregs))))))
    have hmid_cn : StdinMidPreserved sc sn :=
      (StdinMidPreserved.of_alloc hacp_cmc).trans
        (hmid_mc.trans (StdinMidPreserved.of_alloc hacp_bn))
    refine SepWP.weaken_pre ?_
      (hcont sn hpc_n hrun_n hsp_n hx19_n hx20_n hx21_n hx23_n hx24_n hx25_n hx26_n hx27_n hx29_n
        hvregs_n hcl_n hmid_cn)
    rw [hpool_eq_mc, hpool_eq_bn]
    have hvec_back :
        A.live ptr cap 1 ∗
          (ptr ↦ₛ rem.take len) ∗
          ((ptr + BitVec.ofNat 64 len) ↦ₛ chunk) ∗
          memRegion (ptr + BitVec.ofNat 64 (len + chunk.length)) (cap - (len + chunk.length)) ⊢
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take (len + chunk.length)) :=
      cliIoVecBuf_repack_chunk A.repAlloc hcap_pos hcap_lt63 hptr_ne0 hlen_r hlen_cap hchunk_eq
    have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
    let Rest : SepProp :=
      stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        A.pool lim st_cur sn
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := Rest) (sepConj_mono hvec_back hbuf_back))
        (by dsimp only [Rest]; sep_entail))
    dsimp only [Rest]; sep_entail


/-- Full bounded `4096`-byte `read_stdin` loop from header `+0x48 = 72#64` by strong induction on
    `fuel = cliIoStdinCap + 1 - len`, threading `(M : AllocCostModel) (A : RustCliAllocBudget M)`. -/
private theorem cliIoReadStdin_loop_b [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
      allocMemcpyVmSpec)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    {s0 : State} {d0 : FdEntry} {sret v0 v1 v2 : BitVec 64}
    {stackBytes : Nat} {st : M.σ}
    {post : State → SepProp → Prop}
    (hlo : 4256 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hsp0 : s0.spAligned = true)
    (hkind : d0.kind = .stdio) (hcanr : d0.accMode.canRead = true)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢
          let bs := s0.fs.stdin.drop d0.offset
          ⌜sf.fs.files = s0.fs.files ∧ sf.trace = s0.trace ∧
            (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs)⌝ ∗
            ioVecAt A.repAlloc sret (readStdinResult bs) ∗
            stackAt s0.sp stackBytes ∗
            A.pool lim (M.stepEvents (readStdinBudgetEvents bs) st) sf) →
        post sf Pre_f) :
    ∀ (fuel : Nat) (sl : State) (ptr st0 st1 st2 st3 : BitVec 64) (cap len : Nat) (st_cur : M.σ),
      cliIoStdinCap + 1 - len ≤ fuel →
      len ≤ min (s0.fs.stdin.drop d0.offset).length cliIoStdinCap →
      (len < (s0.fs.stdin.drop d0.offset).length → 4096 ∣ len) →
      cap = cliIoFinalCap 8 len →
      st_cur = M.stepEvents (stdinLoopEvents len) st →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sl.mem →
      sl.pc = cliIoPl00.base + 72#64 → sl.status = .Running → sl.sp = s0.sp - 4224#64 →
      sl.readReg64 (.gpr 19#5) = sret → sl.readReg64 (.gpr 20#5) = ptr →
      sl.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 1048576 len) →
      sl.readReg64 (.gpr 24#5) = 4096#64 → sl.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sl.readReg64 (.gpr 26#5) = 1048576#64 → sl.readReg64 (.gpr 27#5) = 1048577#64 →
      sl.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sl = calleeSavedVRegs s0 →
      sl.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + len }) →
      sl.trace = s0.trace → sl.sigActions = s0.sigActions →
      SepWP P (s0.readReg64 .lr) sl
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr ((s0.fs.stdin.drop d0.offset).take len) ∗
          A.pool lim st_cur sl)
        post
        (fun sf =>
          ⌜¬ FitsEvents M lim st (readStdinBudgetEvents (s0.fs.stdin.drop d0.offset)) ∧
            CliIoFilesOomPreserved s0 sf⌝) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro sl ptr st0 st1 st2 st3 cap len st_cur
      hfuel hlen_le hdvd hcap_eq hst_eq hcl hpc hrun hsp_eq
      hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx29 hvregs
      hfs_sl htr_sl hsig_sl
    let rem := s0.fs.stdin.drop d0.offset
    have hrem_def : rem = s0.fs.stdin.drop d0.offset := rfl
    let want := wantBytes 1048576 len
    have hwant_def : want = wantBytes 1048576 len := rfl
    have hcap1048 : cliIoStdinCap = 1048576 := rfl
    have hlen_max : len ≤ cliIoStdinCap := Nat.le_trans hlen_le (Nat.min_le_right _ _)
    have hlen_rem : len ≤ rem.length := Nat.le_trans hlen_le (Nat.min_le_left _ _)
    have hwant_le : want ≤ 4096 := wantBytes_le_4096 1048576 len
    let R_fr : SepProp :=
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take len)
    refine SepWP.weaken_pre (by dsimp only [R_fr]; sep_entail)
      (cliIoReadStdin_do_read_b A lim hext0 hread (R_frame := R_fr) (by omega) hhi hsp_lo hsp_va
        hwant_le hkind hcanr hfs_sl hcl hpc hrun hsp0 hsp_eq
        hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx29 hvregs
        fun sr oldBuf hold_len hpc_sr hrun_sr hsp_sr hx0_sr hx19_sr hx20_sr hx21_sr hx23_sr
            hx24_sr hx25_sr hx26_sr hx27_sr hx29_sr hvregs_sr hcl_sr hfs_sr htr_sr hsig_sr => ?_)
    dsimp only [R_fr]
    let chunk := (rem.drop len).take want
    have hchunk_def : chunk = (rem.drop len).take want := rfl
    have hn_min : chunk.length = min (rem.length - len) want := by
      rw [hchunk_def, List.length_take, List.length_drop, Nat.min_comm]
    have hn_le_want : chunk.length ≤ want := by rw [hn_min]; exact Nat.min_le_right _ _
    have hn_le_rem : len + chunk.length ≤ rem.length := by rw [hn_min]; omega
    rcases Nat.eq_zero_or_pos chunk.length with hn0 | hn_pos
    · -- EOF (`chunk.length = 0`, so `len = rem.length ≤ 1048576`)
      have hwant_pos : 0 < want := wantBytes_pos (by omega : len ≤ 1048576)
      have hlen_eq_rem : len = rem.length := by omega
      have hrem_le_cap : rem.length ≤ 1048576 := by omega
      have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
      have htake_rem : rem.take len = rem := by rw [hlen_eq_rem, List.take_length]
      have hx0_0 : sr.readReg64 .x0 = 0#64 := by rw [hx0_sr, ← hchunk_def, hn0]
      have hx25_rem : sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 rem.length := by
        rw [hx25_sr, hlen_eq_rem]
      refine SepWP.weaken_pre ?_
        (cliIoReadStdin_after_read_eof_b A lim hext0
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
          (st_cur := st_cur)
          (by omega) hhi hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
          hx0_0 hx19_sr hx20_sr hx21_sr hx25_rem hvregs_sr
          fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hmid_srf Pre_f hent =>
            hpost sf hpc_f hrun_f hsp_f hcs_f hcl_f (Entails.trans hent ?_))
      · rw [htake_rem]
        let Rest : SepProp :=
          stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
            ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
            cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr rem ∗ A.pool lim st_cur sr
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q := Rest) hbuf_back) (by dsimp only [Rest]; sep_entail))
        rw [← hrem_def, ← hchunk_def,
          pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
        dsimp only [Rest]; sep_entail
      · have hfs_f : sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + rem.length }) := by
          rw [hmid_srf.1, hfs_sr, ← hchunk_def, hn0, Nat.add_zero, hlen_eq_rem]
        have hfiles : sf.fs.files = s0.fs.files :=
          (congrArg FsState.files hfs_f).trans (setFd_files_eq s0.fs 0#64 _)
        have htr : sf.trace = s0.trace := hmid_srf.2.1.trans (htr_sr.trans htr_sl)
        have hfds : FdsGe3Closed s0.fs → FdsGe3Closed sf.fs := fun hcl0 =>
          hfs_f ▸ fdsGe3Closed_setFd_lt3 (by decide : (0#64 : BitVec 64).toNat < 3) _ hcl0
        have hst_f : st_cur = M.stepEvents (readStdinBudgetEvents rem) st := by
          rw [hst_eq, hlen_eq_rem, ← readStdinBudgetEvents_of_le hrem_le_cap]
        dsimp only
        rw [← hrem_def, readStdinResult_eq_ok_of_le hrem_le_cap, ← hst_f,
          pure_sepConj_of_true ⟨hfiles, htr, hfds⟩]
        sep_entail
    · -- `0 < chunk.length`
      by_cases hover : cliIoStdinCap < len + chunk.length
      · -- Over-cap (`len = cliIoStdinCap = cliIoCap 8`, `chunk.length = 1`, `1048576 < rem.length`)
        have ⟨hlen_eq, hn_eq1, hrem_gt⟩ :=
          overCap_forces_eq_max (K := 8) hlen_le hdvd hn_min hn_pos hover
        have hrem_gt' : 1048576 < rem.length := hrem_gt
        have hwant_eq1 : want = 1 := by rw [hwant_def, hlen_eq]; rfl
        have hidx8 : cliIoCapIdx 8 len = 8 := by rw [hlen_eq]; exact cliIoCapIdx_cap_self 8
        have hcap8 : cap = cliIoCap 8 := by rw [hcap_eq, cliIoFinalCap_pos (by omega), hidx8]
        have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
        refine SepWP.weaken_pre ?_
          (cliIoReadStdin_after_read_overcap_b A lim hext0 hdealloc
            (v0 := v0) (v1 := v1) (v2 := v2)
            (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (bs := rem.take len) (st_cur := st_cur)
            (by omega) hhi hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            (by rw [hx0_sr, ← hchunk_def, hn_eq1]) hx19_sr hx20_sr
            (by rw [hx21_sr, hcap8]) (by rw [hx23_sr, hwant_eq1])
            (by rw [hx25_sr, hlen_eq]; rfl) hx26_sr hvregs_sr
            fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hmid_srf Pre_f hent =>
              hpost sf hpc_f hrun_f hsp_f hcs_f hcl_f (Entails.trans hent ?_))
        · rw [hcap8]
          let Rest : SepProp :=
            stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
              ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
              cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap 8)) ptr (rem.take len) ∗
              A.pool lim st_cur sr
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono_left (Q := Rest) hbuf_back) (by dsimp only [Rest]; sep_entail))
          rw [← hrem_def, ← hchunk_def,
            pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
          dsimp only [Rest]; sep_entail
        · have hfs_f : sf.fs = s0.fs.setFd 0#64
              (some { d0 with offset := d0.offset + (cliIoStdinCap + 1) }) := by
            rw [hmid_srf.1, hfs_sr, ← hchunk_def, hn_eq1, hlen_eq]; rfl
          have hfiles : sf.fs.files = s0.fs.files :=
            (congrArg FsState.files hfs_f).trans (setFd_files_eq s0.fs 0#64 _)
          have htr : sf.trace = s0.trace := hmid_srf.2.1.trans (htr_sr.trans htr_sl)
          have hfds : FdsGe3Closed s0.fs → FdsGe3Closed sf.fs := fun hcl0 =>
            hfs_f ▸ fdsGe3Closed_setFd_lt3 (by decide : (0#64 : BitVec 64).toNat < 3) _ hcl0
          have hst_f :
              M.stepEvents (rustDeallocEvents (cliIoCap 8) 1) st_cur =
                M.stepEvents (readStdinBudgetEvents rem) st := by
            rw [hst_eq, hlen_eq]
            exact stepEvents_overcap_dealloc st hrem_gt'
          dsimp only
          rw [← hrem_def, readStdinResult_eq_err_of_gt hrem_gt', hst_f,
            pure_sepConj_of_true ⟨hfiles, htr, hfds⟩]
          sep_entail
      · -- In-cap (`len + chunk.length ≤ cliIoStdinCap`)
        have hlen'_max : len + chunk.length ≤ cliIoStdinCap := by omega
        have hlen'_le : len + chunk.length ≤ min rem.length cliIoStdinCap :=
          Nat.le_min.mpr ⟨hn_le_rem, hlen'_max⟩
        have hdvd' : len + chunk.length < rem.length → 4096 ∣ (len + chunk.length) :=
          dvd_4096_preserved (K := 8) hlen_le hdvd hn_min hn_pos hlen'_max
        have hm_lt : cliIoStdinCap + 1 - (len + chunk.length) < fuel := by omega
        by_cases hnogrow : len + chunk.length ≤ cap
        · -- No grow (`0 < len`, `cap = cliIoCap j`)
          have hlen_pos : 0 < len := by
            rcases Nat.eq_zero_or_pos len with rfl | hp
            · rw [cliIoFinalCap_zero] at hcap_eq; omega
            · exact hp
          let j := cliIoCapIdx 8 len
          have hj : j ≤ 8 := cliIoCapIdx_le 8 len
          have hcap_j : cap = cliIoCap j := by rw [hcap_eq, cliIoFinalCap_pos hlen_pos]
          have hcap_le_max : cap ≤ 1048576 := by rw [hcap_j]; exact cliIoCap_mono hj
          have hidx_eq : cliIoCapIdx 8 (len + chunk.length) = j :=
            no_grow_capIdx_eq hlen_pos (by omega) (by rwa [← hcap_j])
          have hcap'_eq : cap = cliIoFinalCap 8 (len + chunk.length) := by
            rw [cliIoFinalCap_pos (by omega), hidx_eq, hcap_j]
          have hst_eq_idx : stdinLoopEvents (len + chunk.length) = stdinLoopEvents len := by
            rw [stdinLoopEvents_pos (by omega), stdinLoopEvents_pos hlen_pos, hidx_eq]
          refine cliIoReadStdin_after_read_nogrow_b hext0 hn_pos hn_le_want hwant_le
            hnogrow hcap_le_max hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            hx0_sr hx19_sr hx20_sr hx21_sr hx23_sr hx24_sr hx25_sr hx26_sr hx27_sr hx29_sr hvregs_sr
            fun sc hpc_sc hrun_sc hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc hx24_sc hx25_sc
                hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_srsc hvm_srsc => ?_
          have hpool_srsc : A.pool lim st_cur sr = A.pool lim st_cur sc :=
            (A.pool_transport lim st_cur sr sc hvm_srsc).symm
          refine SepWP.weaken_pre (by rw [hpool_srsc]; sep_entail)
            (cliIoReadStdin_memcpy_backedge_b A lim hext0 hmemcpy
              (by rw [hcap_j]; exact cliIoCap_pos j)
              (by rw [hcap_j]; exact cliIoCap_lt_pow63 (by omega))
              hn_le_rem hnogrow hlen'_max hwant_le hold_len hn_le_want rfl
              hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc hx24_sc
              hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc
              fun sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                  hx26_sn hx27_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                ih (cliIoStdinCap + 1 - (len + chunk.length)) hm_lt sn ptr st0 st1 st2 st3
                  cap (len + chunk.length) st_cur (Nat.le_refl _)
                  hlen'_le hdvd' hcap'_eq
                  (by rw [hst_eq_idx]; exact hst_eq)
                  hcl_sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                  hx26_sn hx27_sn hx29_sn hvregs_sn
                  (hmid_scsn.1.trans (hacp_srsc.1.trans hfs_sr))
                  (hmid_scsn.2.1.trans (hacp_srsc.2.1.trans (htr_sr.trans htr_sl)))
                  (hmid_scsn.2.2.trans (hacp_srsc.2.2.1.trans (hsig_sr.trans hsig_sl))))
        · -- Grow (`cap < len + chunk.length ≤ cliIoStdinCap`)
          have hgt_cap : cap < len + chunk.length := by omega
          refine cliIoReadStdin_after_read_grow_b hext0 hn_pos hn_le_want hwant_le
            hgt_cap hlen'_max hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            hx0_sr hx19_sr hx20_sr hx21_sr hx23_sr hx24_sr hx25_sr hx26_sr hx27_sr hx29_sr hvregs_sr
            fun sg hpc_sg hrun_sg hsp_sg hx0_sg hx19_sg hx20_sg hx21_sg hx24_sg hx25_sg
                hx26_sg hx27_sg hx28_sg hx29_sg hvregs_sg hcl_sg hacp_srsg hvm_srsg => ?_
          have hpool_srsg : A.pool lim st_cur sr = A.pool lim st_cur sg :=
            (A.pool_transport lim st_cur sr sg hvm_srsg).symm
          have hfs_sg : sg.fs = s0.fs.setFd 0#64
              (some { d0 with offset := d0.offset + (len + chunk.length) }) :=
            hacp_srsg.1.trans hfs_sr
          have htr_sg : sg.trace = s0.trace := hacp_srsg.2.1.trans (htr_sr.trans htr_sl)
          have hsig_sg : sg.sigActions = s0.sigActions := hacp_srsg.2.2.1.trans (hsig_sr.trans hsig_sl)
          have hoom_files_of : ∀ sf_oom : State, OomPreserved sg sf_oom → CliIoFilesOomPreserved s0 sf_oom :=
            fun sf_oom hoom_m =>
              ⟨(congrArg FsState.files (hoom_m.1.trans hfs_sg)).trans (setFd_files_eq s0.fs 0#64 _),
                hoom_m.2.1.trans htr_sg, hoom_m.2.2.trans hsig_sg⟩
          rcases Nat.eq_zero_or_pos len with rfl | hlen_pos
          · -- `len = 0`, `cap = 0 → cliIoCap 0 = 4096`
            have hcap0 : cap = 0 := hcap_eq
            subst hcap0
            have hst0 : st_cur = st := by rw [hst_eq, stdinLoopEvents_zero]; rfl
            have hidx0 : cliIoCapIdx 8 chunk.length = 0 :=
              cliIoCapIdx_eq_of_bounds (Nat.zero_le 8) (Or.inl rfl) (Nat.le_trans hn_le_want hwant_le)
            refine SepWP.weaken_pre (by rw [hpool_srsg, hst0]; sep_entail)
              (cliIoReadStdin_grow_from_zero_b A lim hext0 hfg hlo hhi hn_pos
                (Nat.le_trans hn_le_want hwant_le) hcl_sg hpc_sg hrun_sg hsp0 hsp_sg
                hx0_sg hx19_sg hx20_sg hx21_sg hx24_sg hx25_sg hx26_sg hx27_sg
                (by rw [Nat.zero_add] at hx28_sg; exact hx28_sg) hx29_sg hvregs_sg
                (fun hnot sf_oom hoom_m =>
                  Entails.pure_right_only
                    ⟨not_fitsEvents_budget_of_grow_zero (by omega : 0 < rem.length) hnot,
                      hoom_files_of sf_oom hoom_m⟩
                    (Entails.refl _))
                fun sc newPtr st1' st2' hpc_sc hrun_sc hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc
                    hx24_sc hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_sgsc =>
                  cliIoReadStdin_memcpy_backedge_b A lim hext0 hmemcpy
                    (cliIoCap_pos 0) (cliIoCap_lt_pow63 (by decide))
                    hn_le_rem (Nat.le_trans (by rw [Nat.zero_add]; exact hn_le_want) hwant_le)
                    hlen'_max hwant_le hold_len hn_le_want rfl
                    hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc hx24_sc
                    hx25_sc hx26_sc hx27_sc (by rw [Nat.zero_add]; exact hx28_sc) hx29_sc hvregs_sc
                    fun sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                        hx26_sn hx27_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                      ih (cliIoStdinCap + 1 - (0 + chunk.length)) hm_lt sn newPtr 0#64 st1' st2' st3
                        (cliIoCap 0) (0 + chunk.length)
                        (M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) st)
                        (Nat.le_refl _) hlen'_le hdvd'
                        (by simp [cliIoFinalCap_pos hn_pos, hidx0])
                        (by rw [Nat.zero_add]; exact stepEvents_grow_zero st hn_pos hidx0)
                        hcl_sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn
                        hx25_sn hx26_sn hx27_sn hx29_sn hvregs_sn
                        (hmid_scsn.1.trans (hacp_sgsc.1.trans hfs_sg))
                        (hmid_scsn.2.1.trans (hacp_sgsc.2.1.trans htr_sg))
                        (hmid_scsn.2.2.trans (hacp_sgsc.2.2.1.trans hsig_sg)))
          · -- `0 < len`, `cap = cliIoCap j → cliIoCap (j + 1)`
            let j := cliIoCapIdx 8 len
            have hj : j ≤ 8 := cliIoCapIdx_le 8 len
            have hcap_j : cap = cliIoCap j := by rw [hcap_eq, cliIoFinalCap_pos hlen_pos]
            have hlen_le_j : len ≤ cliIoCap j := le_cliIoCap_cliIoCapIdx hlen_max
            have ⟨hj1, hj1_r, hidx_j1, hle_j1, _⟩ :=
              grow_step_bounds (K := 8) (by decide) hj hlen_le_j
                (Nat.le_trans hn_le_want hwant_le) hn_le_rem hlen'_max (by rwa [← hcap_j])
            refine SepWP.weaken_pre (by rw [hpool_srsg, hcap_j]; sep_entail)
              (cliIoReadStdin_grow_from_pos_b A lim hext0 hfg hlo hhi hj1 hlen_le_j
                (List.length_take_of_le hlen_rem) (by rwa [← hcap_j]) hle_j1
                hcl_sg hpc_sg hrun_sg hsp0 hsp_sg
                hx0_sg hx19_sg hx20_sg (by rw [hx21_sg, hcap_j]) hx24_sg hx25_sg
                hx26_sg hx27_sg hx28_sg hx29_sg hvregs_sg
                (fun hnot sf_oom hoom_m =>
                  Entails.pure_right_only
                    ⟨not_fitsEvents_budget_of_grow_pos hlen_pos (by omega : 0 < rem.length) hj rfl
                      hj1_r (hst_eq ▸ hnot),
                      hoom_files_of sf_oom hoom_m⟩
                    (Entails.refl _))
                fun sc newPtr st1' st2' hpc_sc hrun_sc hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc
                    hx24_sc hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_sgsc =>
                  cliIoReadStdin_memcpy_backedge_b A lim hext0 hmemcpy
                    (cliIoCap_pos (j + 1)) (cliIoCap_lt_pow63 (by omega))
                    hn_le_rem hle_j1 hlen'_max hwant_le hold_len hn_le_want rfl
                    hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc hx24_sc
                    hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc
                    fun sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                        hx26_sn hx27_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                      ih (cliIoStdinCap + 1 - (len + chunk.length)) hm_lt sn newPtr 0#64 st1' st2' st3
                        (cliIoCap (j + 1)) (len + chunk.length)
                        (M.stepEvents
                          (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1)))
                          st_cur)
                        (Nat.le_refl _) hlen'_le hdvd'
                        (by rw [cliIoFinalCap_pos (by omega), hidx_j1])
                        (by rw [hst_eq]; exact stepEvents_grow_pos st hlen_pos (by omega) hj rfl hidx_j1)
                        hcl_sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn
                        hx25_sn hx26_sn hx27_sn hx29_sn hvregs_sn
                        (hmid_scsn.1.trans (hacp_sgsc.1.trans hfs_sg))
                        (hmid_scsn.2.1.trans (hacp_sgsc.2.1.trans htr_sg))
                        (hmid_scsn.2.2.trans (hacp_sgsc.2.2.1.trans hsig_sg)))


private def cliIoReadStdinRawSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stackBytes : Nat) : Spec (ReadStdinGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜4256 + allocHookStack ≤ stackBytes ∧
      stackBytes ≤ 2 ^ 64 ∧
      stackBytes ≤ s.sp.toNat ∧
      s.sp.toNat ≤ Arm64.USER_VA_LIMIT ∧
      s.readReg64 .x8 = x.ret ∧
      cliIo.stdin s.fs = some x.bs⌝ ∗
      (stackAt s.sp stackBytes ∗ memRegion x.ret 24 ∗ A.pool lim st s)
  post    := (readStdinBudgetCondSpec A lim stackBytes).post
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := (readStdinBudgetCondSpec A lim stackBytes).onOom

/-- Placement-generic conditional-OOM proof of `signal_session_io::read_stdin` (`block[0]`) over
any `RustCliAllocBudget M` and `BudgetLimits`. -/
private theorem cliIoReadStdin_raw_ok {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stackBytes : Nat}
    (hext0 : CliIoBlockNoExtern mpl P 0)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      allocMemcpyVmSpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (cliIoWithCodeLoaded mpl (cliIoReadStdinRawSpec A lim stackBytes)) := by
  have hfg := cliIoFinishGrow_budget_ok_withCodeLoaded A lim hpl hext4 hshim halloc hrealloc
  letI : CliIoPlacement := ⟨mpl, hpl⟩
  rw [cliIoResolve_eq_base hpl 0 cliIoReadStdinSym cliIo0_lt cliIoReadStdin_lookup]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp0
  dsimp only [cliIoWithCodeLoaded, MultiPlacedLib.withCodeLoaded, cliIoReadStdinRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hlo, hhi, hsp_lo, hsp_va, hx8, hstdin⟩, hmem⟩
  obtain ⟨d0, hfds0, hkind, hcanr, hbs_eq⟩ := cliStdin_eq_some hstdin
  refine ⟨_, hmem, ?_⟩
  dsimp only [readStdinBudgetCondSpec]
  rw [hbs_eq]
  wp_conv_pre =>
    rw [cliIoReadStdin_stack_split s0.sp (by omega) hhi,
      memRegion24_eq_exists_vecHeader x.ret,
      memRegion4096_split_probe32 (s0.sp - 4224#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, bv_lin_norm]
  refine SepWP.exists_elim fun v0 => SepWP.exists_elim fun v1 =>
    SepWP.exists_elim fun v2 =>
    SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 =>
    SepWP.exists_elim fun r0 => SepWP.exists_elim fun r1 =>
    SepWP.exists_elim fun r2 => SepWP.exists_elim fun r3 =>
    SepWP.exists_elim fun r4 => SepWP.exists_elim fun r5 =>
    SepWP.exists_elim fun r6 => SepWP.exists_elim fun r7 =>
    SepWP.exists_elim fun r8 => SepWP.exists_elim fun r9 =>
    SepWP.exists_elim fun r10 => SepWP.exists_elim fun r11 =>
    SepWP.exists_elim fun w_probe => ?_
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl0
    (mid := cliIoPl00.base + 72#64)
  intro s1' hcpu1_0
  have hcpu1 := hcpu1_0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc1' : s1'.pc = cliIoPl00.base := hcpu1.pc_eq.trans hpc
  have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
  have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
  have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
  have hx8_1' : s1'.readReg64 .x8 = x.ret := (hcpu1.readReg64 .x8).trans hx8
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1')
    fun sl hcpu_l0 hcl_l hnsp_l hsym_l => ?_
  have hcpu_l := hcpu_l0.1
  have ⟨hacp_0l, hvm_0l⟩ :=
    vmPreserved_of_seg hcpu1_0 hcpu_l0 hnsp_l hsym_l
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_0l : A.pool lim st s0 = A.pool lim st sl :=
    (A.pool_transport lim st s0 sl hvm_0l).symm
  have hpc_l : sl.pc = cliIoPl00.base + 72#64 := hcpu_l.pc_eq.trans (by simp [arm64_norm])
  have hrun_l : sl.status = .Running := hcpu_l.status_eq.trans hrun1'
  have hsp_l : sl.sp = s0.sp - 4224#64 := hcpu_l.sp_eq.trans (by simp [arm64_norm])
  have hfs_l : sl.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + 0 }) :=
    hacp_0l.1.trans (setFd_offset_add_zero hfds0)
  refine SepWP.weaken_pre ?_
    (cliIoReadStdin_loop_b A lim hext0 hread hmemcpy hfg hdealloc
      (sret := x.ret) (v0 := v0) (v1 := v1) (v2 := v2)
      hlo hhi hsp_lo hsp_va hsp0 hkind hcanr
      (fun sf _hpc_f _hrun_f hsp_f hcs_f hcl_f {_Pre_f} hent =>
        ⟨fun hm_out => by
          change signalSessionIoMultiLib.CodeLoaded mpl sf.mem at hcl_f
          rw [pure_sepConj_of_true hcl_f]
          exact Satisfies.mono (sepConj_mono_left hent) hm_out,
        hsp_f, hcs_f⟩)
      (cliIoStdinCap + 1) sl 1#64 st0 st1 st2 st3 0 0 st
      (Nat.le_refl _) (Nat.zero_le _) (fun _ => Nat.dvd_zero 4096) rfl
      (by rw [stdinLoopEvents_zero]; rfl)
      hcl_l hpc_l hrun_l hsp_l
      (by rw [hcpu_l.readReg64]; simp only [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp only [arm64_norm])
      (hcpu_l.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs))
      hfs_l hacp_0l.2.1 hacp_0l.2.2.1)
  have hrefold_probe :
      memRegion (s0.sp - 4224#64) 32 ∗ ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 4184#64) 4056 ⊢ memRegion (s0.sp - 4224#64) 4096 := by
    simpa only [bv_lin_norm] using memRegion4096_refold_probe32 (s0.sp - 4224#64) 0#64
  have hvec0 : emp ⊢ cliIoVecBuf A.repAlloc (BitVec.ofNat 64 0) 1#64
      ((s0.fs.stdin.drop d0.offset).take 0) :=
    cliIoVecBuf_zero_intro A.repAlloc (ptr := 1#64) (by decide)
  rw [hpool_eq_0l,
    hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
    hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 27#5),
    hcpu1.readReg64 (.gpr 26#5), hcpu1.readReg64 (.gpr 25#5),
    hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
    hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
    hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5)]
  dsimp only [cliIoSavedRegs12]
  simp only [bv_lin_norm]
  let SavedAndRest : SepProp :=
    stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
      vecHeader x.ret v0 v1 v2 ∗ A.pool lim st sl
  have hwith_vec :
      SavedAndRest ⊢ SavedAndRest ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 0) 1#64 ((s0.fs.stdin.drop d0.offset).take 0) := by
    simpa only [sepConj_emp] using sepConj_mono_right (P := SavedAndRest) hvec0
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono hrefold_probe hwith_vec)
      (by dsimp only [SavedAndRest]; sep_entail))
  dsimp only [SavedAndRest]; sep_entail

end


/-! ## Discharging `readStdinBudgetCondSpec` and Lifted Specifications -/

private theorem stackAt_le_two_pow_64_of_sep {m : Memory} {p sp : BitVec 64} {n stk : Nat}
    {R : SepProp} (hn : 0 < n) (hstk : 0 < stk)
    (h : m ⊨ memRegion p n ∗ (stackAt sp stk ∗ R)) : stk ≤ 2 ^ 64 := by
  have hdisj := (IsBlock.memRegion p n).disjoint
    (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) hn hstk h
  have hlt := (p - (sp - BitVec.ofNat 64 stk)).isLt
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hdisj.2 hlt)

private theorem stackAt_sp_le_userVa_of_mapped {m : Memory} {sp : BitVec 64} {stk : Nat}
    {R : SepProp} (hpos : 0 < stk) (hle : stk ≤ 2 ^ 64)
    (hmapVa : ∀ a : BitVec 64, (m.perm a).mapped = true → a.toNat < Arm64.USER_VA_LIMIT)
    (hsat : m ⊨ stackAt sp stk ∗ R) :
    sp.toNat ≤ Arm64.USER_VA_LIMIT := by
  by_cases hsp0 : sp = 0#64
  · subst hsp0; decide
  · have hspPos : 1 ≤ sp.toNat := by
      rcases Nat.eq_zero_or_pos sp.toNat with hz | hp
      · exact False.elim (hsp0 (BitVec.eq_of_toNat_eq hz))
      · exact hp
    have hcw : m.canWrite ((sp - BitVec.ofNat 64 stk) + BitVec.ofNat 64 (stk - 1)) 1 = true :=
      memRegion_canWrite1 hsat (by omega) hle
    have hAddr : (sp - BitVec.ofNat 64 stk) + BitVec.ofNat 64 (stk - 1) = sp - 1#64 := by
      have hstkEq : BitVec.ofNat 64 stk = 1#64 + BitVec.ofNat 64 (stk - 1) := by
        change BitVec.ofNat 64 stk = BitVec.ofNat 64 1 + BitVec.ofNat 64 (stk - 1)
        rw [← BitVec.ofNat_add]; congr 1; omega
      rw [hstkEq, ← BitVec.sub_sub, BitVec.sub_add_cancel]
    rw [hAddr] at hcw
    have hmap : (m.perm (sp - 1#64)).mapped = true := by
      unfold Memory.canWrite Memory.allPerm at hcw
      cases hp : m.perm (sp - 1#64) with
      | none => rw [hp] at hcw; cases hcw
      | some _ => rfl
    have hlt := hmapVa (sp - 1#64) hmap
    have hsub : (sp - 1#64).toNat = sp.toNat - 1 := by
      have h64 := sp.isLt
      rw [BitVec.toNat_sub]
      change (2 ^ 64 - 1 + sp.toNat) % 2 ^ 64 = sp.toNat - 1
      have h1 : 2 ^ 64 - 1 + sp.toNat = 2 ^ 64 + (sp.toNat - 1) := by omega
      rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega

private theorem stackAt_bounds_of_mapped {m : Memory} {sp : BitVec 64} {stk : Nat} {R : SepProp}
    (hpos : 0 < stk) (hle : stk ≤ 2 ^ 64)
    (hmapVa : ∀ a : BitVec 64, (m.perm a).mapped = true → a.toNat < Arm64.USER_VA_LIMIT)
    (hsat : m ⊨ stackAt sp stk ∗ R) :
    stk ≤ sp.toNat ∧ sp.toNat ≤ Arm64.USER_VA_LIMIT := by
  refine ⟨?_, stackAt_sp_le_userVa_of_mapped hpos hle hmapVa hsat⟩
  exact Classical.byContradiction fun hlt_stk => by
    have hsp_lt : sp.toNat < stk := Nat.lt_of_not_ge hlt_stk
    let k := stk - 1 - sp.toNat
    have hk_lt : k < stk := by omega
    have hcw : m.canWrite ((sp - BitVec.ofNat 64 stk) + BitVec.ofNat 64 k) 1 = true :=
      memRegion_canWrite1 hsat hk_lt hle
    have hspEq : sp = BitVec.ofNat 64 sp.toNat :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sp.isLt])
    have hstkEq : BitVec.ofNat 64 stk = (sp + 1#64) + BitVec.ofNat 64 k := by
      conv => rhs; arg 1; arg 1; rw [hspEq]
      change BitVec.ofNat 64 stk =
        (BitVec.ofNat 64 sp.toNat + BitVec.ofNat 64 1) + BitVec.ofNat 64 k
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 1; omega
    have hSubSelf : sp - sp = 0#64 := BitVec.eq_of_toNat_eq (by simp)
    have hAddr : (sp - BitVec.ofNat 64 stk) + BitVec.ofNat 64 k = 0#64 - 1#64 := by
      rw [hstkEq, ← BitVec.sub_sub, BitVec.sub_add_cancel, ← BitVec.sub_sub, hSubSelf]
    rw [hAddr] at hcw
    have hmap : (m.perm (0#64 - 1#64)).mapped = true := by
      unfold Memory.canWrite Memory.allPerm at hcw
      cases hp : m.perm (0#64 - 1#64) with
      | none => rw [hp] at hcw; cases hcw
      | some _ => rfl
    have hlt := hmapVa (0#64 - 1#64) hmap
    have hLim : Arm64.USER_VA_LIMIT = 2 ^ 48 := rfl
    have hVal : (0#64 - 1#64 : BitVec 64).toNat = 2 ^ 64 - 1 := by decide
    omega

private theorem cliIoReadStdin_budgetCond_ok_extHookStack_withCodeLoaded
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hext0 : CliIoBlockNoExtern mpl P 0)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      allocMemcpyVmSpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hPoolVa : ∀ {st : M.σ} {s : State} {R : SepProp} {a : BitVec 64},
      (s.mem ⊨ A.pool lim st s ∗ R) → (s.mem.perm a).mapped = true →
        a.toNat < Arm64.USER_VA_LIMIT) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl (readStdinBudgetCondSpec A lim extHookStack)) := by
  have hRaw0 := subroutine_ok_of_cliIoWithCodeLoaded
    (cliIoReadStdin_raw_ok A lim hpl hext0 hext4 hread hmemcpy hshim halloc hrealloc hdealloc
      (stackBytes := extHookStack))
  have hlo : 4256 + allocHookStack ≤ extHookStack := by
    unfold extHookStack allocHookStack; decide
  have hhi : extHookStack ≤ 2 ^ 64 := by
    unfold extHookStack; decide
  have hpos_ext : 0 < extHookStack := by
    unfold extHookStack; decide
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  have hpreR : s0.mem ⊨
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (cliIoReadStdinRawSpec A lim extHookStack)).pre (x, st) s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadStdinRawSpec]
    dsimp only [MultiPlacedLib.withCodeLoaded, readStdinBudgetCondSpec] at hpre
    rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    refine ⟨hpre.1, ?_⟩
    have hp := hpre.2
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
    have ⟨hsp_lo, hsp_va⟩ : extHookStack ≤ s0.sp.toNat ∧ s0.sp.toNat ≤ Arm64.USER_VA_LIMIT :=
      stackAt_bounds_of_mapped hpos_ext hhi
        (fun _ hmap => hPoolVa
          (R := memRegion x.ret 24 ∗ stackAt s0.sp extHookStack ∗ R)
          (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp.2) hmap)
        (R := memRegion x.ret 24 ∗ A.pool lim st s0 ∗ R)
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp.2)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hlo, hhi, hsp_lo, hsp_va, hp.1.1, hp.1.2⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp.2⟩
  refine subroutine_ok.mono_outcome hRaw0 (x, st) R s0 hpc hrun hpreR hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨ho, hoom⟩)
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadStdinRawSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadStdinRawSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-- `signalSessionIoMultiLib.withCodeLoaded` form of `readStdinBudgetCondSpec` for
`extHookStack ≤ stk`. -/
theorem cliIoReadStdin_budgetCond_ok_withCodeLoaded
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hstk : extHookStack ≤ stk)
    (hext0 : CliIoBlockNoExtern mpl P 0)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      allocMemcpyVmSpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hPoolVa : ∀ {st : M.σ} {s : State} {R : SepProp} {a : BitVec 64},
      (s.mem ⊨ A.pool lim st s ∗ R) → (s.mem.perm a).mapped = true →
        a.toNat < Arm64.USER_VA_LIMIT) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl (readStdinBudgetCondSpec A lim stk)) := by
  have hE := cliIoReadStdin_budgetCond_ok_extHookStack_withCodeLoaded
    A lim hpl hext0 hext4 hread hmemcpy hshim halloc hrealloc hdealloc hPoolVa
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [MultiPlacedLib.withCodeLoaded, readStdinBudgetCondSpec] at hpre
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre0⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx8, hstdin⟩, hmem⟩
  have hmem_disj : s0.mem ⊨ memRegion x.ret 24 ∗
      (stackAt s0.sp stk ∗ (A.pool lim st s0 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hpos_ext : 0 < extHookStack := by unfold extHookStack; decide
  have hstk64 : stk ≤ 2 ^ 64 :=
    stackAt_le_two_pow_64_of_sep (by decide) (Nat.lt_of_lt_of_le hpos_ext hstk) hmem_disj
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ stackAt s0.sp extHookStack := by
    have hs := stackAt_split_bottom s0.sp extHookStack (stk - extHookStack) (by omega)
    rwa [Nat.add_sub_of_le hstk] at hs
  let F : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack)
  have hpreE : s0.mem ⊨
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (readStdinBudgetCondSpec A lim extHookStack)).pre (x, st) s0 ∗ (F ∗ R) := by
    dsimp only [MultiPlacedLib.withCodeLoaded, readStdinBudgetCondSpec, F]
    rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx8, hstdin⟩, ?_⟩
    rw [hsplit] at hmem
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine subroutine_ok.mono_outcome hE (x, st) (F ∗ R) s0 hpc hrun hpreE hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨_, _, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, readStdinBudgetCondSpec, F] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hp, ?_⟩)
    dsimp only [MultiPlacedLib.withCodeLoaded, readStdinBudgetCondSpec, F] at hpan ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan ⊢
    refine ⟨hpan.1, ?_⟩
    have h1 : sf.mem ⊨ (anyHeap ∗ F) ∗ R :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpan.2
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) h1
  · dsimp only [MultiPlacedLib.withCodeLoaded, readStdinBudgetCondSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    dsimp only [MultiPlacedLib.withCodeLoaded, readStdinBudgetCondSpec, F] at hoom ⊢
    rw [satisfies_pure_sepConj] at hoom ⊢
    have hoomR : sf.mem ⊨ R ∗ F :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hoom.2
    exact ⟨hoom.1, Satisfies.of_sep_left hoomR⟩

/-- Compiled `signalSessionIoMultiLib` discharges `readStdinBudgetCondSpec A lim stk` when
`P.CodeLoaded m → signalSessionIoMultiLib.CodeLoaded mpl m` and `extHookStack ≤ stk`. -/
theorem cliIoReadStdin_budgetCond_ok
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hstk : extHookStack ≤ stk)
    (hCodeLib : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoaded mpl m)
    (hext0 : CliIoBlockNoExtern mpl P 0)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      allocMemcpyVmSpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hPoolVa : ∀ {st : M.σ} {s : State} {R : SepProp} {a : BitVec 64},
      (s.mem ⊨ A.pool lim st s ∗ R) → (s.mem.perm a).mapped = true →
        a.toNat < Arm64.USER_VA_LIMIT) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (readStdinBudgetCondSpec A lim stk) := by
  have hWith := cliIoReadStdin_budgetCond_ok_extHookStack_withCodeLoaded
    A lim hpl hext0 hext4 hread hmemcpy hshim halloc hrealloc hdealloc hPoolVa
  refine subroutine_ok_readStdinBudgetCondSpec_of_extHookStack hstk ?_
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp hCodeP
  have hpreL : s0.mem ⊨
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (readStdinBudgetCondSpec A lim extHookStack)).pre (x, st) s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨hCodeLib s0.mem hCodeP, hpre⟩
  exact subroutine_ok.mono_outcome hWith (x, st) R s0 hpc hrun hpreL hsp fun _ hout => hout


/-- Bundled subroutine + block-purity assumptions for compiled `signalSessionIoMultiLib`
    `read_stdin` (`block[0]`) + `finish_grow` (`block[4]`) on sub-program `P` at `(A, lim, mpl)`. -/
structure CliIoReadStdinSubroutines {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (mpl : MultiPlacement) (P : Program) : Prop where
  placeable  : signalSessionIoMultiLib.Placeable mpl
  codeLoaded : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoaded mpl m
  noExt0     : CliIoBlockNoExtern mpl P 0
  noExt4     : CliIoBlockNoExtern mpl P 4
  read       : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
                 muslReadStdin32Spec
  memcpy     : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
                 allocMemcpyVmSpec
  shim       : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
                 rustAllocShimVmSpec
  alloc      : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
                 (rustCliAllocBudgetSpecBase M A lim false)
  realloc    : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
                 (rustCliReallocBudgetSpecBase M A lim)
  dealloc    : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
                 (rustCliDeallocBudgetSpecBase M A lim)
  poolVa     : ∀ {st : M.σ} {s : State} {R : SepProp} {a : BitVec 64},
                 (s.mem ⊨ A.pool lim st s ∗ R) → (s.mem.perm a).mapped = true →
                   a.toNat < Arm64.USER_VA_LIMIT

theorem CliIoReadStdinSubroutines.budgetCond_ok {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {mpl : MultiPlacement} {P : Program}
    (hS : CliIoReadStdinSubroutines A lim mpl P) (hstk : extHookStack ≤ stk) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (readStdinBudgetCondSpec A lim stk) :=
  cliIoReadStdin_budgetCond_ok A lim hS.placeable hstk hS.codeLoaded hS.noExt0 hS.noExt4
    hS.read hS.memcpy hS.shim hS.alloc hS.realloc hS.dealloc hS.poolVa

theorem cliIoReadStdin_noOom_ok {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {mpl : MultiPlacement} {P : Program}
    (hS : CliIoReadStdinSubroutines A lim mpl P) (hstk : extHookStack ≤ stk) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (readStdinBudgetNoOomSpec A lim stk) :=
  subroutine_ok_readStdinNoOom_of_cond (hS.budgetCond_ok hstk)

theorem cliIoReadStdin_specOfPlaced_compiled_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {mpl : MultiPlacement} {P : Program}
    (hS : CliIoReadStdinSubroutines A lim mpl P) (hstk : extHookStack ≤ stk) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv) :=
  subroutine_ok_readStdinSpecOfPlaced_of_cond compiledReadStdinEnv_events (hS.budgetCond_ok hstk)

theorem cliIoReadStdin_specOfPlaced_bounded_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {mpl : MultiPlacement} {P : Program}
    (hS : CliIoReadStdinSubroutines A lim mpl P) (hstk : extHookStack ≤ stk) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (readStdinSpecOfPlaced cliIo A lim stk ReadStdinBoundedEnv) :=
  subroutine_ok_readStdinSpecOfPlaced_of_cond
    (fun bs => compiledReadStdinEnv_sub_bounded (compiledReadStdinEnv_events bs))
    (hS.budgetCond_ok hstk)

theorem cliIoReadStdin_specPlaced_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {mpl : MultiPlacement} {P : Program}
    (hS : CliIoReadStdinSubroutines A lim mpl P) (hstk : extHookStack ≤ stk) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (readStdinSpecPlaced cliIo A lim stk) := by
  rw [← readStdinSpecOfPlaced_eq_readStdinSpecPlaced]
  exact subroutine_ok_readStdinSpecOfPlaced_of_cond
    (fun bs => compiledReadStdinEnv_sub_readStdinEnv (compiledReadStdinEnv_events bs))
    (hS.budgetCond_ok hstk)

/-! ## Ghost-Hook Specializations -/

noncomputable abbrev readStdinCliIoGhostHook [LibsignalPlacement] {M : AllocCostModel}
    (P_io : Program) (mpl : MultiPlacement)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) : State → State :=
  readStdinGhostHook P_io (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym) A lim stk fallback

noncomputable abbrev readStdinCliIoLinkedGhostHook [LibsignalPlacement] {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (mpl : MultiPlacement)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) : State → State :=
  readStdinLinkedGhostHook keep P_real P_sub
    (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym) A lim stk fallback

/-- `(lim, stk)`-independent precondition witness (`extHookStack ≤ stk`) for `lsReadStdinSym`. -/
def ActiveAnyLimStkReadStdinPre [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (s0 : State) : Prop :=
  s0.status = .Running ∧ s0.spAligned = true ∧
    ∃ (lim : BudgetLimits) (stk : Nat) (_ : extHookStack ≤ stk)
      (y : ReadStdinGhost × M.σ) (R : SepProp),
      s0.mem ⊨ (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv).pre y s0 ∗ R

open Classical in
/-- `(lim, stk)`-independent real-ELF ghost hook for `lsReadStdinSym`, executing `P_real` from
`s0.setPC entry_io` across all `stk ≥ extHookStack` and `lim : BudgetLimits`. -/
noncomputable def readStdinAnyLinkedGhostHook [LibsignalPlacement] {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (fallback : State → State) (s0 : State) : State :=
  if _ : ActiveAnyLimStkReadStdinPre A s0 then
    if hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io s0 then
      Classical.choose hReal.2.2.2
    else
      keepFilesTrace fallback s0
  else
    { s0 with status := .Exception "read_stdin ghost-hook precondition violated" }

private theorem setPC_mem (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl

private theorem setPC_symtab (s : State) (pc : BitVec 64) : (s.setPC pc).symtab = s.symtab := by
  cases s; rfl

theorem readStdinAnyLinkedGhostHook_fsT [LibsignalPlacement] {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (fallback : State → State) :
    HookFsTraced IsFsC (readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback) := by
  classical
  intro s0
  unfold readStdinAnyLinkedGhostHook
  split
  · split
    · rename_i hReal
      have hspec := Classical.choose_spec hReal.2.2.2
      exact FsTraced.of_eq hspec.2.2.2.1 hspec.2.2.1
    · exact keepFilesTrace_fsT fallback s0
  · exact FsTraced.of_eq rfl rfl

theorem readStdinAnyLinkedGhostHook_ok_compiled [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hstk : extHookStack ≤ stk)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readStdinBudgetCondSpec A lim extHookStack))
    (hFallback : HookOk fallback (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    HookOk (readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback)
      (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv) := by
  classical
  have hCondStk := subroutine_ok_readStdinBudgetCondSpec_of_extHookStack hstk hCond
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hActPre : ActiveAnyLimStkReadStdinPre A s0 :=
    ⟨hrun, hsp, lim, stk, hstk, (x, st), R, hpre⟩
  unfold readStdinAnyLinkedGhostHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hout, _, _, _, _⟩ :=
      real_readStdin_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hCondStk
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

theorem readStdinAnyLinkedGhostHook_ok_bounded [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hstk : extHookStack ≤ stk)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readStdinBudgetCondSpec A lim extHookStack))
    (hFallback : HookOk fallback (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    HookOk (readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback)
      (readStdinSpecOfPlaced cliIo A lim stk ReadStdinBoundedEnv) :=
  ReadStdinBudgetPlaced.HookOk.readStdin_mono_env (fun _ _ => compiledReadStdinEnv_sub_bounded)
    (readStdinAnyLinkedGhostHook_ok_compiled hstk hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip
      hCond hFallback)

theorem readStdinAnyLinkedGhostHook_ok [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hstk : extHookStack ≤ stk)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readStdinBudgetCondSpec A lim extHookStack))
    (hFallback : HookOk fallback (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    HookOk (readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback)
      (readStdinSpecPlaced cliIo A lim stk) := by
  rw [← readStdinSpecOfPlaced_eq_readStdinSpecPlaced]
  exact ReadStdinBudgetPlaced.HookOk.readStdin_mono_env
    (fun _ _ => compiledReadStdinEnv_sub_readStdinEnv)
    (readStdinAnyLinkedGhostHook_ok_compiled hstk hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip
      hCond hFallback)

theorem ghostExternReplays_of_readStdinAnyLinkedGhostHook [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {P_real P_sub : Program} {stubPc entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTarget P_real stubPc entry_io)
    (hInvCode : ∀ m : Memory, ExecFrozen m → Inv m → P_sub.CodeLoaded (stripExecOutside keep m))
    (hPoolStrip : ∀ lim st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : ∀ lim, subroutine_ok P_sub entry_io (readStdinBudgetCondSpec A lim extHookStack)) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps P_real u
          (readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback u) ∧
        ExecFrozen
          (readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback u).mem := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  classical
  have hActPre : ActiveAnyLimStkReadStdinPre A u := by
    by_contra hnPre
    have hex : (readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback u).status =
        .Exception "read_stdin ghost-hook precondition violated" := by
      unfold readStdinAnyLinkedGhostHook; simp [hnPre]
    exact hnoex _ hex
  have ⟨_, hsp, lim, stk, hstk, ⟨x, st⟩, R, hpre⟩ := hActPre
  have hCondStk := subroutine_ok_readStdinBudgetCondSpec_of_extHookStack hstk (hCond lim)
  have hCodeSub := hInvCode u.mem hfr hinv
  obtain ⟨sf, huntil, hstop, _, hfiles, htr, hfds, hfr_sf⟩ :=
    real_readStdin_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no (hPoolStrip lim) hCondStk
      hrun hsp hpre hfr hlr hCodeSub
  have hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io u :=
    ⟨hfr, hlr, hCodeSub, sf, huntil, hstop, hfiles, htr, hfds, hfr_sf⟩
  have heq : readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback u =
      Classical.choose hReal.2.2.2 := by
    unfold readStdinAnyLinkedGhostHook; simp [hActPre, hReal]
  rw [heq]
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hStubSteps : Steps P_real u (u.setPC entry_io) := hStub u hpc hrun hfr
  exact ⟨hStubSteps.trans hchoose.1.toSteps, hchoose.2.2.2.2.2⟩

theorem fdsGe3Closed_readStdinAnyLinkedGhostHook_of_call [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {fallback : State → State} {u : State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ lim st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hCond : ∀ lim, subroutine_ok P_sub entry_io (readStdinBudgetCondSpec A lim extHookStack))
    (hnoex : ∀ msg,
      (readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback u).status ≠
        .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hlr : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hClosed : FdsGe3Closed u.fs) :
    FdsGe3Closed (readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback u).fs ∧
      (readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback u).fs.files =
        u.fs.files := by
  classical
  have hActPre : ActiveAnyLimStkReadStdinPre A u := by
    by_contra hnPre
    have hex : (readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback u).status =
        .Exception "read_stdin ghost-hook precondition violated" := by
      unfold readStdinAnyLinkedGhostHook; simp [hnPre]
    exact hnoex _ hex
  have ⟨hrun, hsp, lim, stk, hstk, ⟨x, st⟩, R, hpre⟩ := hActPre
  have hCondStk := subroutine_ok_readStdinBudgetCondSpec_of_extHookStack hstk (hCond lim)
  obtain ⟨sf, huntil, hstop, _, hfiles, htr, hfds, hfr_sf⟩ :=
    real_readStdin_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no (hPoolStrip lim) hCondStk
      hrun hsp hpre hfr hlr hCodeSub
  have hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io u :=
    ⟨hfr, hlr, hCodeSub, sf, huntil, hstop, hfiles, htr, hfds, hfr_sf⟩
  have heq : readStdinAnyLinkedGhostHook keep P_real P_sub entry_io A fallback u =
      Classical.choose hReal.2.2.2 := by
    unfold readStdinAnyLinkedGhostHook; simp [hActPre, hReal]
  rw [heq]
  have hchoose := Classical.choose_spec hReal.2.2.2
  exact ⟨hchoose.2.2.2.2.1 hClosed, hchoose.2.2.1⟩

theorem mainIoPlaced_and_bounded_of_readStdinAnyLinkedGhostHook [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (g : CliGhostHooks)
    {M : AllocCostModel} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry_stdin : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {rfh fbStdin : State → State}
    (hstk : extHookStack ≤ stk)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hReadFile : HookOk rfh (readFileLitSpecPlaced cliIo A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hStdinCond : subroutine_ok P_sub entry_stdin (readStdinBudgetCondSpec A lim extHookStack))
    (hFbStdin : HookOk fbStdin (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv)) :
    let rsh := readStdinAnyLinkedGhostHook keep P_real P_sub entry_stdin A fbStdin
    MainIoPlaced A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk ∧
    MainIoBoundedPlaced A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk
      ReadStdinBoundedEnv :=
  mainIoPlaced_and_bounded_withReadHooks_ghost mmpl W g stk hReadFile
    (readStdinAnyLinkedGhostHook_ok_compiled hstk hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip
      hStdinCond hFbStdin)

/-! ## Read-Only Block Subset `{0, 3, 4}` (`CliIoReadsCodeLoaded`) Variants -/

section
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  cliIoReadsKeep CliIoReadsCodeLoaded cliIoWithReadsCodeLoaded
  subroutine_ok_of_cliIoWithReadsCodeLoaded sepWP_seg_cliIo_block_pure_reads
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FinishGrowBudget (
  cliIoFinishGrow_budget_ok_withReadsCodeLoaded
)
open VerifiedLibraries.RustStd (seqCodeLoadedWhere)

section
arm64_proof_prelude

/-- Budget-threaded `Ok(bs)` epilogue of `read_stdin` (`+0x138 = 312#64 .. +0x160 = 352#64`). -/
private theorem cliIoReadStdin_ok_epilogue_b_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    {s0 se : State} {sret v0 v1 v2 cap ptr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4224 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl : CliIoReadsCodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl00.base + 312#64)
    (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : se.sp = s0.sp - 4224#64)
    (hx19 : se.readReg64 (.gpr 19#5) = sret)
    (hx20 : se.readReg64 (.gpr 20#5) = ptr)
    (hx21 : se.readReg64 (.gpr 21#5) = cap)
    (hx25 : se.readReg64 (.gpr 25#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      AllocCallPreserved se sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.ok bs) ∗
          A.pool lim st_cur sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc cap ptr bs ∗
        A.pool lim st_cur se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl00.base + 312#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 4224#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = sret := (hcpu_e.readReg64 _).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = ptr := (hcpu_e.readReg64 _).trans hx20
  have hx21_e' : se'.readReg64 (.gpr 21#5) = cap := (hcpu_e.readReg64 _).trans hx21
  have hx25_e' : se'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 bs.length :=
    (hcpu_e.readReg64 _).trans hx25
  wp_conv_pre => dsimp only [cliIoSavedRegs12]; rw [show vecHeader sret v0 v1 v2 =
    (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
  have hcpu_f := hcpu_f0.1
  have ⟨hacp_ef, hvm_ef⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f hsym_f
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool lim st_cur se = A.pool lim st_cur sf :=
    (A.pool_transport lim st_cur se sf hvm_ef).symm
  have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
  have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
  have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · exact hcpu_f.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))
  refine SepWP.done hpc_f hrun_f (hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_ef ?_)
  have hstk_back := cliIoReadStdin_stack_refold s0 hlo hhi st0 st1 st2 st3
  dsimp only [cliIoSavedRegs12] at hstk_back
  have hvec_ok := vecHeader_cliIoVecBuf_entails_ioVecAt_ok A.repAlloc sret cap ptr bs
  dsimp only [vecHeader] at hvec_ok
  rw [hpool_eq]
  refine Entails.trans ?_ (sepConj_mono hstk_back (sepConj_mono_left hvec_ok))
  sep_entail

/-- Budget-threaded over-cap `Err(())` epilogue of `read_stdin` (`+0x164 = 356#64 .. +0x1a0 = 416#64`):
    writes `0xFFFFFFFFFFFFFFFF#64` to `[sret]`, restores `sp` and `x19..x30`, and tail-calls
    `__rust_dealloc(ptr, cap, 1)`, advancing `st_cur` by `rustDeallocEvents cap 1`. -/
private theorem cliIoReadStdin_err_epilogue_b_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    {s0 se : State} {sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {cap stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4224 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcap_pos : 0 < cap) (hcap_lt63 : cap < 2 ^ 63)
    (hcl : CliIoReadsCodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl00.base + 356#64)
    (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : se.sp = s0.sp - 4224#64)
    (hx19 : se.readReg64 (.gpr 19#5) = sret)
    (hx20 : se.readReg64 (.gpr 20#5) = ptr)
    (hx21 : se.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      AllocCallPreserved se sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.error ()) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents cap 1) st_cur) sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr bs ∗
        A.pool lim st_cur se)
      post oomProp := by
  have hlo4224 : 4224 ≤ stackBytes := by omega
  have hcap_lt64 : cap < 2 ^ 64 := Nat.lt_trans hcap_lt63 (by decide)
  have hcap_beq0 : (BitVec.ofNat 64 cap == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) hcap_lt64 (by decide)
  have hcap_toNat : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64]
  apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl00.base + 356#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 4224#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = sret := (hcpu_e.readReg64 _).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = ptr := (hcpu_e.readReg64 _).trans hx20
  have hx21_e' : se'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_e.readReg64 _).trans hx21
  wp_conv_pre => dsimp only [cliIoSavedRegs12]; rw [show vecHeader sret v0 v1 v2 =
    (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done cliIoReadStdin_dealloc_pc (by simpa [arm64_norm] using hrun_e')
    fun sm_dl hcpu_dl0 hcl_dl hnsp_dl hsym_dl => ?_
  have hcpu_dl := hcpu_dl0.1
  have ⟨hacp_edl, hvm_edl⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_dl0 hnsp_dl hsym_dl
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_edl : A.pool lim st_cur se = A.pool lim st_cur sm_dl :=
    (A.pool_transport lim st_cur se sm_dl hvm_edl).symm
  have hpc_dl : sm_dl.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym :=
    hcpu_dl.pc_eq.trans cliIoReadStdin_dealloc_pc
  have hrun_dl : sm_dl.status = .Running := hcpu_dl.status_eq.trans hrun_e'
  have hsp_dl_eq : sm_dl.sp = s0.sp := hcpu_dl.sp_eq.trans (by simp [arm64_norm])
  have hsp_dl : sm_dl.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_dl_eq]; exact hsp0
  have hlr_dl : sm_dl.readReg64 .lr = s0.readReg64 .lr :=
    (hcpu_dl.readReg64 .lr).trans (by simp [arm64_norm])
  have hx0_dl : sm_dl.readReg64 .x0 = ptr :=
    (hcpu_dl.readReg64 .x0).trans (by simp [arm64_norm])
  have hx1_dl : (sm_dl.readReg64 .x1).toNat = cap := by
    rw [hcpu_dl.readReg64 .x1]; simpa [arm64_norm] using hcap_toNat
  have hx2_dl : (sm_dl.readReg64 .x2).toNat = 1 := by
    rw [hcpu_dl.readReg64 .x2]; simp [arm64_norm]
  have hcs_0dl : CalleeSavedPreserved s0 sm_dl := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · rw [hcpu_dl.readReg64]; simp [arm64_norm]
    · exact hcpu_dl.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))
  have hhk_le : allocHookStack ≤ stackBytes := by omega
  let T_dl : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stackBytes) (stackBytes - allocHookStack) ∗
      ioVecAt A.repAlloc sret (.error ())
  apply seqCodeLoadedWhere hcl_dl (mid := s0.readReg64 .lr)
  apply (SepWP.call_subroutine_frame (F := T_dl) hdealloc
    (x := (ptr, cap, 1, st_cur))
    hpc_dl hrun_dl hsp_dl hlr_dl
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [rustCliDeallocBudgetSpecBase, T_dl]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0_dl, hx1_dl, hx2_dl⟩, ?_⟩
    have hstk_back := cliIoReadStdin_stack_refold s0 hlo4224 hhi st0 st1 st2 st3
    dsimp only [cliIoSavedRegs12] at hstk_back
    have herr_sret := vecHeader_to_ioVecAt_err A.repAlloc sret v1 v2
    dsimp only [vecHeader] at herr_sret
    have hde_mem : cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr bs ⊢
        A.live ptr cap 1 ∗ memRegion ptr cap :=
      cliIoVecBuf_entails_dealloc_mem A.repAlloc (ptr := ptr) (bs := bs) hcap_pos hcap_lt63
    refine Satisfies.mono ?_ hm'
    rw [hpool_eq_edl, hsp_dl_eq]
    have h1 :
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
          memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
          ((s0.sp - 104#64) ↦₆₄ st3) ∗
          (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
            ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
            ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)))) ∗
        ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2)) ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr bs ⊢
        (memRegion (s0.sp - BitVec.ofNat 64 stackBytes) (stackBytes - allocHookStack) ∗
          stackAt s0.sp allocHookStack) ∗
        ioVecAt A.repAlloc sret (.error ()) ∗
        (A.live ptr cap 1 ∗ memRegion ptr cap) := by
      rw [← stackAt_shrink s0.sp stackBytes allocHookStack hhk_le hhi]
      exact sepConj_mono hstk_back (sepConj_mono herr_sret hde_mem)
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := A.pool lim st_cur sm_dl ∗ R') h1) ?_)
    · sep_entail
    · sep_entail
  · intro sf hpc_f hrun_f hsp_f hcs_dlf
    refine SepWP.done hpc_f hrun_f fun hcl_f => ?_
    wp_conv_pre => dsimp only [rustCliDeallocBudgetSpecBase, T_dl]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hacp_dlf, _⟩
    have hsp_f_eq : sf.sp = s0.sp := hsp_f.trans hsp_dl_eq
    have hcs_0f : CalleeSavedPreserved s0 sf := hcs_0dl.trans hcs_dlf
    have hacp_ef : AllocCallPreserved se sf := allocCallPreserved_trans hacp_edl hacp_dlf
    refine SepWP.done hpc_f hrun_f (hcont sf hpc_f hrun_f hsp_f_eq hcs_0f hcl_f hacp_ef ?_)
    rw [hsp_dl_eq, stackAt_shrink s0.sp stackBytes allocHookStack hhk_le hhi]
    sep_entail

/-- Post-`read` EOF (`x0 = 0#64`) branch `+0x58 → +0x138 .. +0x160`: jumps to `Ok` epilogue. -/
private theorem cliIoReadStdin_after_read_eof_b_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    {s0 sr : State} {sret v0 v1 v2 cap ptr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4224 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl00.base + 88#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 4224#64)
    (hx0 : sr.readReg64 .x0 = 0#64)
    (hx19 : sr.readReg64 (.gpr 19#5) = sret) (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = cap)
    (hx25 : sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      StdinMidPreserved sr sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.ok bs) ∗
          A.pool lim st_cur sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sr
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc cap ptr bs ∗ A.pool lim st_cur sr)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl
    (mid := cliIoPl00.base + 312#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl00.base + 88#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = 0#64 := (hcpu_r.readReg64 _).trans hx0
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
  have hcpu_e := hcpu_e0.1
  have ⟨hacp_re, hvm_re⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_e0 hnsp_e hsym_e
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool lim st_cur sr = A.pool lim st_cur se :=
    (A.pool_transport lim st_cur sr se hvm_re).symm
  rw [hpool_eq]
  exact cliIoReadStdin_ok_epilogue_b_reads A lim hext0 hlo hhi hcl_e
    (hcpu_e.pc_eq.trans (by simp [arm64_norm])) (hcpu_e.status_eq.trans hrun_r') hsp0
    (hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx19)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx21)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx25)
    (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_ef _ hent =>
      hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
        ((StdinMidPreserved.of_alloc hacp_re).trans (StdinMidPreserved.of_alloc hacp_ef)) hent

/-- Post-`read` over-cap (`len = 1048576`, `n = 1`, `want = 1`) branch `+0x58 .. +0x84 → +0x164`. -/
private theorem cliIoReadStdin_after_read_overcap_b_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    {s0 sr : State} {sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4224 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl00.base + 88#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 4224#64)
    (hx0 : sr.readReg64 .x0 = 1#64)
    (hx19 : sr.readReg64 (.gpr 19#5) = sret) (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap 8))
    (hx23 : sr.readReg64 (.gpr 23#5) = 1#64)
    (hx25 : sr.readReg64 (.gpr 25#5) = 1048576#64)
    (hx26 : sr.readReg64 (.gpr 26#5) = 1048576#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      StdinMidPreserved sr sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.error ()) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents (cliIoCap 8) 1) st_cur) sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sr
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap 8)) ptr bs ∗
        A.pool lim st_cur sr)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl
    (mid := cliIoPl00.base + 356#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl00.base + 88#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = 1#64 := (hcpu_r.readReg64 _).trans hx0
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = 1#64 := (hcpu_r.readReg64 _).trans hx23
  have hx25_r' : sr'.readReg64 (.gpr 25#5) = 1048576#64 := (hcpu_r.readReg64 _).trans hx25
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_r.readReg64 _).trans hx26
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
  have hcpu_e := hcpu_e0.1
  have ⟨hacp_re, hvm_re⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_e0 hnsp_e hsym_e
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool lim st_cur sr = A.pool lim st_cur se :=
    (A.pool_transport lim st_cur sr se hvm_re).symm
  rw [hpool_eq]
  exact cliIoReadStdin_err_epilogue_b_reads A lim hext0 hdealloc hlo hhi
    (cliIoCap_pos 8) (cliIoCap_lt_pow63 (by decide)) hcl_e
    (hcpu_e.pc_eq.trans (by simp [arm64_norm])) (hcpu_e.status_eq.trans hrun_r') hsp0
    (hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx19)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx21)
    (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_ef _ hent =>
      hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
        ((StdinMidPreserved.of_alloc hacp_re).trans (StdinMidPreserved.of_alloc hacp_ef)) hent

/-- Post-`read` in-cap no-grow (`0 < n ≤ want`, `len + n ≤ cap ≤ 1048576`) branch
    `+0x58 .. +0x90 → +0xc4 .. +0xc8 → +0xcc = 204#64`. -/
private theorem cliIoReadStdin_after_read_nogrow_b_reads [CliIoPlacement]
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    {s0 sr : State} {sret ptr : BitVec 64} {Pre : SepProp}
    {cap len want n : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hn_pos : 0 < n) (hn_le_want : n ≤ want) (hwant_le : want ≤ 4096)
    (hlen_cap : len + n ≤ cap) (hcap_max : cap ≤ 1048576)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl00.base + 88#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 4224#64)
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 n)
    (hx19 : sr.readReg64 (.gpr 19#5) = sret) (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx23 : sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sr.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sr.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sr.readReg64 (.gpr 27#5) = 1048577#64)
    (hx29 : sr.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sc : State,
      sc.pc = cliIoPl00.base + 204#64 → sc.status = .Running → sc.sp = s0.sp - 4224#64 →
      sc.readReg64 (.gpr 19#5) = sret → sc.readReg64 (.gpr 20#5) = ptr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = 4096#64 → sc.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 26#5) = 1048576#64 → sc.readReg64 (.gpr 27#5) = 1048577#64 →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sc.mem →
      AllocCallPreserved sr sc → VmPreserved sr sc →
      SepWP P (s0.readReg64 .lr) sc Pre post oomProp) :
    SepWP P (s0.readReg64 .lr) sr Pre post oomProp := by
  have hn_beq0 : (BitVec.ofNat 64 n == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) (by omega) (by decide)
  have hbit63 : (BitVec.ofNat 64 n).getLsbD 63 = false := bit63_eq_zero_of_lt (by omega)
  have hule_w : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 want) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat]; omega
  have hult_w : (BitVec.ofNat 64 want).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le_want (by omega)
  have hsub26 : 1048576#64 - BitVec.ofNat 64 len = BitVec.ofNat 64 (1048576 - len) :=
    bv64_sub_ofNat (by omega)
  have hule_rem : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (1048576 - len)) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat]; omega
  have hult_rem : (BitVec.ofNat 64 (1048576 - len)).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false (by omega) (by omega)
  have hadd28 : BitVec.ofNat 64 n + BitVec.ofNat 64 len = BitVec.ofNat 64 (len + n) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hule_cap : (BitVec.ofNat 64 (len + n)).ule (BitVec.ofNat 64 cap) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat]; omega
  have hult_cap : (BitVec.ofNat 64 cap).ult (BitVec.ofNat 64 (len + n)) = false :=
    bv64_ult_ofNat_false hlen_cap (by omega)
  apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl
    (mid := cliIoPl00.base + 204#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl00.base + 88#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_r.readReg64 _).trans hx0
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_r.readReg64 _).trans hx21
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_r.readReg64 _).trans hx23
  have hx25_r' : sr'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len := (hcpu_r.readReg64 _).trans hx25
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_r.readReg64 _).trans hx26
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun sc hcpu_c0 hcl_c hnsp_c hsym_c => ?_
  have hcpu_c := hcpu_c0.1
  have ⟨hacp_rc, hvm_rc⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_c0 hnsp_c hsym_c
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  exact hcont sc (hcpu_c.pc_eq.trans (by simp [arm64_norm])) (hcpu_c.status_eq.trans hrun_r')
    (hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx19)
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm, hx25_r'])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm, hx26_r'])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx27)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx29)
    (hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    hcl_c hacp_rc hvm_rc

/-- Post-`read` in-cap grow (`0 < n ≤ want`, `cap < len + n ≤ 1048576`) branch
    `+0x58 .. +0x90 → +0x94 = 148#64`. -/
private theorem cliIoReadStdin_after_read_grow_b_reads [CliIoPlacement]
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    {s0 sr : State} {sret ptr : BitVec 64} {Pre : SepProp}
    {cap len want n : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hn_pos : 0 < n) (hn_le_want : n ≤ want) (hwant_le : want ≤ 4096)
    (hgt_cap : cap < len + n) (hlen_max : len + n ≤ 1048576)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl00.base + 88#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 4224#64)
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 n)
    (hx19 : sr.readReg64 (.gpr 19#5) = sret) (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx23 : sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sr.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sr.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sr.readReg64 (.gpr 27#5) = 1048577#64)
    (hx29 : sr.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sg : State,
      sg.pc = cliIoPl00.base + 148#64 → sg.status = .Running → sg.sp = s0.sp - 4224#64 →
      sg.readReg64 .x0 = BitVec.ofNat 64 n →
      sg.readReg64 (.gpr 19#5) = sret → sg.readReg64 (.gpr 20#5) = ptr →
      sg.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sg.readReg64 (.gpr 24#5) = 4096#64 → sg.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sg.readReg64 (.gpr 26#5) = 1048576#64 → sg.readReg64 (.gpr 27#5) = 1048577#64 →
      sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) →
      sg.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sg = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sg.mem →
      AllocCallPreserved sr sg → VmPreserved sr sg →
      SepWP P (s0.readReg64 .lr) sg Pre post oomProp) :
    SepWP P (s0.readReg64 .lr) sr Pre post oomProp := by
  have hn_beq0 : (BitVec.ofNat 64 n == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) (by omega) (by decide)
  have hbit63 : (BitVec.ofNat 64 n).getLsbD 63 = false := bit63_eq_zero_of_lt (by omega)
  have hule_w : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 want) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat]; omega
  have hult_w : (BitVec.ofNat 64 want).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le_want (by omega)
  have hsub26 : 1048576#64 - BitVec.ofNat 64 len = BitVec.ofNat 64 (1048576 - len) :=
    bv64_sub_ofNat (by omega)
  have hule_rem : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (1048576 - len)) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat]; omega
  have hult_rem : (BitVec.ofNat 64 (1048576 - len)).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false (by omega) (by omega)
  have hadd28 : BitVec.ofNat 64 n + BitVec.ofNat 64 len = BitVec.ofNat 64 (len + n) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hule_cap : (BitVec.ofNat 64 (len + n)).ule (BitVec.ofNat 64 cap) = false := by
    simp [BitVec.ule, BitVec.toNat_ofNat]; omega
  have hult_cap : (BitVec.ofNat 64 cap).ult (BitVec.ofNat 64 (len + n)) = true :=
    bv64_ult_ofNat_true hgt_cap (by omega)
  apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl
    (mid := cliIoPl00.base + 148#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl00.base + 88#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_r.readReg64 _).trans hx0
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_r.readReg64 _).trans hx21
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_r.readReg64 _).trans hx23
  have hx25_r' : sr'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len := (hcpu_r.readReg64 _).trans hx25
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_r.readReg64 _).trans hx26
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun sg hcpu_g0 hcl_g hnsp_g hsym_g => ?_
  have hcpu_g := hcpu_g0.1
  have ⟨hacp_rg, hvm_rg⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_g0 hnsp_g hsym_g
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  exact hcont sg (hcpu_g.pc_eq.trans (by simp [arm64_norm])) (hcpu_g.status_eq.trans hrun_r')
    (hcpu_g.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx0_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx19)
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx21_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx25_r'])
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx26_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx27)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx29)
    (hcpu_g.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    hcl_g hacp_rg hvm_rg

/-- Step `+0x48 .. +0x54` and call `muslReadStdin32Spec`, landing at `+0x58 = 88#64`. -/
private theorem cliIoReadStdin_do_read_b_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadStdin32Spec)
    {s0 sl : State} {d0 : FdEntry} {sret ptr cap_bv : BitVec 64} {R_frame : SepProp}
    {len want stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4256 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hwant_le : want ≤ 4096)
    (hkind : d0.kind = .stdio) (hcanr : d0.accMode.canRead = true)
    (hfs : sl.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + len }))
    (hcl : CliIoReadsCodeLoaded cliIoMpl sl.mem)
    (hpc : sl.pc = cliIoPl00.base + 72#64) (hrun : sl.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sl.sp = s0.sp - 4224#64)
    (hx19 : sl.readReg64 (.gpr 19#5) = sret) (hx20 : sl.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sl.readReg64 (.gpr 21#5) = cap_bv)
    (hx23 : sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sl.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sl.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sl.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sl.readReg64 (.gpr 27#5) = 1048577#64)
    (hx29 : sl.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sl = calleeSavedVRegs s0)
    (hcont : ∀ (sr : State) (oldBuf : List (BitVec 8)),
      let rem := s0.fs.stdin.drop d0.offset
      let chunk := (rem.drop len).take want
      oldBuf.length = want →
      sr.pc = cliIoPl00.base + 88#64 → sr.status = .Running → sr.sp = s0.sp - 4224#64 →
      sr.readReg64 .x0 = BitVec.ofNat 64 chunk.length →
      sr.readReg64 (.gpr 19#5) = sret → sr.readReg64 (.gpr 20#5) = ptr →
      sr.readReg64 (.gpr 21#5) = cap_bv →
      sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want →
      sr.readReg64 (.gpr 24#5) = 4096#64 →
      sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sr.readReg64 (.gpr 26#5) = 1048576#64 →
      sr.readReg64 (.gpr 27#5) = 1048577#64 →
      sr.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs sr = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sr.mem →
      sr.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + (len + chunk.length) }) →
      sr.trace = sl.trace → sr.sigActions = sl.sigActions →
      SepWP P (s0.readReg64 .lr) sr
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
          (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
            memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want)) ∗
          R_frame ∗ A.pool lim st_cur sr)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sl
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        R_frame ∗ A.pool lim st_cur sl)
      post oomProp := by
  have hwant_toNat : (BitVec.ofNat 64 want).toNat = want := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  wp_conv_pre =>
    rw [memRegion_split_le (s0.sp - 4224#64) want 4096 hwant_le (by decide),
      memRegion_eq_exists_bytes (s0.sp - 4224#64) want (by omega)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro oldBuf
  wp_conv_pre =>
    rw [← sepConj_assoc (stackAt _ _), sepConj_comm (stackAt _ _) ⌜oldBuf.length = want⌝]
    simp only [sepConj_assoc]
  apply SepWP.pure_elim; intro hold_len
  apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
  intro sl' hcpu_l0
  have hcpu_l := hcpu_l0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_l' : sl'.pc = cliIoPl00.base + 72#64 := hcpu_l.pc_eq.trans hpc
  have hrun_l' : sl'.status = .Running := hcpu_l.status_eq.trans hrun
  have hsp_l_in : sl'.sp = s0.sp - 4224#64 := hcpu_l.sp_eq.trans hsp_eq
  have hsp_l' : sl'.spAligned = true := by
    rw [hcpu_l.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx23_l' : sl'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_l.readReg64 _).trans hx23
  wp_sym_steps
  refine SepWP.done cliIoReadStdin_read_pc (by simpa [arm64_norm] using hrun_l')
    fun sm_rd hcpu_rd0 hcl_rd hnsp_rd hsym_rd => ?_
  have hcpu_rd := hcpu_rd0.1
  have ⟨hacp_lrd, hvm_lrd⟩ :=
    vmPreserved_of_seg hcpu_l0 hcpu_rd0 hnsp_rd hsym_rd
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_lrd : A.pool lim st_cur sl = A.pool lim st_cur sm_rd :=
    (A.pool_transport lim st_cur sl sm_rd hvm_lrd).symm
  have hpc_rd : sm_rd.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym :=
    hcpu_rd.pc_eq.trans cliIoReadStdin_read_pc
  have hrun_rd : sm_rd.status = .Running := hcpu_rd.status_eq.trans hrun_l'
  have hsp_rd_eq : sm_rd.sp = s0.sp - 4224#64 :=
    hcpu_rd.sp_eq.trans ((by simp [arm64_norm] : _ = sl'.sp).trans hsp_l_in)
  have hsp_rd : sm_rd.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_rd_eq]; exact s0.spAligned_sub 4224#64 hsp0
  have hlr_rd : sm_rd.readReg64 .lr = cliIoPl00.base + 88#64 := by
    rw [hcpu_rd.readReg64 .lr]; simp [arm64_norm]
  have hx0_rd : sm_rd.readReg32 .x0 = 0#32 := by
    simp only [State.readReg32]; rw [hcpu_rd.readReg64 .x0]; simp [arm64_norm]
  have hx1_rd : sm_rd.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_rd.readReg64 .x1]; simp [arm64_norm]
  have hx2_rd : sm_rd.readReg64 .x2 = BitVec.ofNat 64 want := by
    rw [hcpu_rd.readReg64 .x2]; simp [arm64_norm]
  have hfs_rd : sm_rd.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + len }) :=
    hacp_lrd.1.trans hfs
  have hfds_rd : sm_rd.fs.fds 0#64 = some { d0 with offset := d0.offset + len } := by
    rw [hfs_rd]; simp [FsState.setFd]
  rw [hpool_eq_lrd]
  let d_cur : FdEntry := { d0 with offset := d0.offset + len }
  apply seqCodeLoadedWhere hcl_rd (mid := cliIoPl00.base + 88#64)
  apply (SepWP.call_subroutine_frame hread
    (x := (s0.sp - 4224#64, BitVec.ofNat 64 want, d_cur, oldBuf))
    hpc_rd hrun_rd hsp_rd hlr_rd
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslReadStdin32Spec]
    rw [hsp_rd_eq, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_rd, hx1_rd, hx2_rd,
      by rw [hwant_toNat]; simp only [Arm64.MAX_RW_COUNT]; omega,
      by rw [hwant_toNat]; exact sp_sub_4224_va_bound (by omega) hsp_va hwant_le,
      by rw [hwant_toNat]; exact hold_len, hfds_rd, hkind, hcanr⟩, ?_⟩
    rw [stackAt_shrink (s0.sp - 4224#64) (stackBytes - 4224) 32 (by omega) (by omega)] at hm'
    exact Satisfies.mono (by sep_frame) hm'
  · intro sr hpc_sr hrun_sr hsp_sr hcs_rdsr
    refine SepWP.done hpc_sr hrun_sr fun hcl_sr => ?_
    wp_conv_pre => dsimp only [muslReadStdin32Spec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_sr, hfs_sr, htr_sr, hsys_sr⟩
    have hpool_eq_sr : A.pool lim st_cur sm_rd = A.pool lim st_cur sr :=
      (A.pool_transport lim st_cur sm_rd sr
        (vmPreserved_of_syscallPreserved_fds hsys_sr fun fd hlo hhi => by
          have hne : (BitVec.ofNat 64 fd == 0#64) = false := by
            rw [beq_eq_false_iff_ne]
            intro heq
            have hEqNat := congrArg BitVec.toNat heq
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : fd < 2 ^ 64)] at hEqNat
            omega
          rw [hfs_sr]
          dsimp only [FsState.setFd]
          rw [hne]
          simp only [Bool.false_eq_true, ↓reduceIte])).symm
    have hchunk_eq :
        (sm_rd.fs.stdin.drop d_cur.offset).take (BitVec.ofNat 64 want).toNat =
          ((s0.fs.stdin.drop d0.offset).drop len).take want := by
      rw [hfs_rd, FsState.stdin_setFd, hwant_toNat]
      dsimp only [d_cur]
      rw [← List.drop_drop]
    have hfs_sr' : sr.fs = s0.fs.setFd 0#64
        (some { d0 with offset := d0.offset + (len + (((s0.fs.stdin.drop d0.offset).drop len).take want).length) }) := by
      rw [hfs_sr, hchunk_eq, hfs_rd, FsState.setFd_setFd_same]
      dsimp only [d_cur]
      rw [Nat.add_assoc]
    have hsp_sr_eq : sr.sp = s0.sp - 4224#64 := hsp_sr.trans hsp_rd_eq
    refine SepWP.weaken_pre ?_
      (hcont sr oldBuf hold_len hpc_sr hrun_sr hsp_sr_eq
        (by rwa [hchunk_eq] at hx0_sr)
        (by rw [hcs_rdsr.readReg64_x19, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx19)
        (by rw [hcs_rdsr.readReg64_x20, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx20)
        (by rw [hcs_rdsr.readReg64_x21, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx21)
        (by rw [hcs_rdsr.readReg64_x23, hcpu_rd.readReg64]; simp only [arm64_norm]; exact hx23_l')
        (by rw [hcs_rdsr.readReg64_x24, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx24)
        (by rw [hcs_rdsr.readReg64_x25, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx25)
        (by rw [hcs_rdsr.readReg64_x26, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx26)
        (by rw [hcs_rdsr.readReg64_x27, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx27)
        (by rw [hcs_rdsr.readReg64_x29, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx29)
        (hcs_rdsr.vregs.trans (hcpu_rd.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs sl').trans (hcpu_l.calleeSavedVRegs.trans hvregs))))
        hcl_sr hfs_sr' (htr_sr.trans hacp_lrd.2.1) (hsys_sr.2.1.trans hacp_lrd.2.2.1))
    rw [hpool_eq_sr, hchunk_eq, hsp_rd_eq,
      stackAt_shrink (s0.sp - 4224#64) (stackBytes - 4224) 32 (by omega) (by omega)]
    sep_entail

/-- Shared budget-threaded `finish_grow` call + `+0x11c .. +0x12c → +0xcc` (`204#64`) join. -/
private theorem cliIoReadStdin_post_grow_b_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    {s0 sm_fg : State} {sret v0 v1 v2 oldCap oldPtr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {R_buf : SepProp}
    {newCap len n stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4256 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hnew_pos : 0 < newCap) (hnew_lt63 : newCap < 2 ^ 63)
    (hbs_le : bs.length ≤ newCap) (hno_null : ¬ NullAllowed newCap 1)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sm_fg.mem)
    (hpc : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
    (hrun : sm_fg.status = .Running) (hsp0 : s0.spAligned = true)
    (hsp_eq : sm_fg.sp = s0.sp - 4224#64) (hlr : sm_fg.readReg64 .lr = cliIoPl00.base + 284#64)
    (hx0 : sm_fg.readReg64 .x0 = s0.sp - 128#64)
    (hx1 : sm_fg.readReg64 .x1 = oldCap) (hx2 : sm_fg.readReg64 .x2 = oldPtr)
    (hx3 : sm_fg.readReg64 .x3 = BitVec.ofNat 64 newCap)
    (hx19 : sm_fg.readReg64 (.gpr 19#5) = sret)
    (hx22 : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap)
    (hx23 : sm_fg.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n)
    (hx24 : sm_fg.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sm_fg.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sm_fg.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sm_fg.readReg64 (.gpr 27#5) = 1048577#64)
    (hx28 : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n))
    (hx29 : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sm_fg = calleeSavedVRegs s0)
    (hoom_fg : ¬ FitsEvents M lim st_in (cliIoFinishGrowBudgetEvents oldCap newCap) →
      ∀ sf_oom : State, OomPreserved sm_fg sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl00.base + 204#64 → sc.status = .Running → sc.sp = s0.sp - 4224#64 →
      sc.readReg64 (.gpr 19#5) = sret → sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = 4096#64 → sc.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 26#5) = 1048576#64 → sc.readReg64 (.gpr 27#5) = 1048577#64 →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sc.mem → AllocCallPreserved sm_fg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 newCap) newPtr bs ∗
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st_in) sc)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sm_fg
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ cliIoVecBuf A.repAlloc oldCap oldPtr bs ∗
        A.pool lim st_in sm_fg)
      post oomProp := by
  have hnew_lt64 : newCap < 2 ^ 64 := Nat.lt_trans hnew_lt63 (by decide)
  have hsp_fg : sm_fg.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_eq]; exact s0.spAligned_sub 4224#64 hsp0
  have hfg_stk_le : 32 + allocHookStack ≤ stackBytes - 4224 := by omega
  have hfg_stk_hi : stackBytes - 4224 ≤ 2 ^ 64 := by omega
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 4224#64) (stackBytes - 4224) (32 + allocHookStack)
      hfg_stk_le hfg_stk_hi]
  apply seqCodeLoadedWhere hcl (mid := cliIoPl00.base + 284#64)
  apply (SepWP.call_subroutine_frame hfg
    (x := (s0.sp - 128#64, st0, st1, st2, oldCap, oldPtr, bs, newCap, st_in))
    hpc hrun hsp_fg hlr
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun R_oom sf_oom _ hm_oom => by
      have hm' := Satisfies.drop_mid hm_oom
      dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoFinishGrowBudgetSpec] at hm'
      rcases (satisfies_pure_sepConj _ _ _).mp hm' with ⟨⟨_, hnot_fit, hoom_s⟩, hm_r⟩
      have hent := hoom_fg hnot_fit sf_oom hoom_s
      rw [← emp_sepConj R_oom] at hm_r
      exact Satisfies.mono (sepConj_mono_left hent) hm_r))
  · intro R' hm'
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoFinishGrowBudgetSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnew_pos, hnew_lt64, hbs_le⟩, ?_⟩
    rw [hsp_eq]
    have hcl_true : (⌜CliIoReadsCodeLoaded cliIoMpl sm_fg.mem⌝ : SepProp) = emp := by
      simp [hcl]
    rw [hcl_true, emp_sepConj]
    exact Satisfies.mono (by sep_frame) hm'
  · intro sm_fg' hpc_fg' hrun_fg' hsp_fg' hcs_fg'
    refine SepWP.done hpc_fg' hrun_fg' fun hcl_fg' => ?_
    wp_conv_pre =>
      dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoFinishGrowBudgetSpec]
      simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_left; intro isErr
    apply SepWP.exists_left; intro newPtr
    apply SepWP.exists_left; intro errW1
    apply SepWP.exists_left; intro errW2
    apply SepWP.pure_elim; intro hacp_fg
    cases isErr with
    | true =>
      wp_conv_pre =>
        simp only [↓reduceIte, sepConj_assoc]
        rw [sepConj_comm (stackAt sm_fg.sp (32 + allocHookStack)), sepConj_assoc]
      apply SepWP.pure_elim; intro hnull
      exact False.elim (hno_null hnull)
    | false =>
      wp_conv_pre =>
        simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        rw [sepConj_comm (stackAt sm_fg.sp (32 + allocHookStack)), sepConj_assoc]
      apply SepWP.pure_elim; intro _hnew_lt63'
      have hsp_fg'_eq : sm_fg'.sp = s0.sp - 4224#64 := hsp_fg'.trans hsp_eq
      have hx29_fg' : sm_fg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 :=
        hcs_fg'.readReg64_x29.trans hx29
      apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl_fg'
        (mid := cliIoPl00.base + 204#64)
      intro sj' hcpu_j0
      have hcpu_j := hcpu_j0.1
      change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
      have hpc_j' : sj'.pc = cliIoPl00.base + 284#64 := hcpu_j.pc_eq.trans hpc_fg'
      have hrun_j' : sj'.status = .Running := hcpu_j.status_eq.trans hrun_fg'
      have hsp_j' : sj'.spAligned = true := by
        rw [hcpu_j.spAligned]; simp only [State.spAligned]; rw [hsp_fg'_eq]
        exact s0.spAligned_sub 4224#64 hsp0
      have hx29_j' : sj'.readReg64 (.gpr 29#5) = s0.sp - 96#64 :=
        (hcpu_j.readReg64 _).trans hx29_fg'
      wp_conv_pre =>
        rw [show vecHeader (s0.sp - 128#64) 0#64 newPtr (BitVec.ofNat 64 newCap) =
          ((s0.sp - 128#64) ↦₆₄ 0#64) ∗ ((s0.sp - 120#64) ↦₆₄ newPtr) ∗
          ((s0.sp - 112#64) ↦₆₄ BitVec.ofNat 64 newCap) by
            simp only [vecHeader, bv_lin_norm]]
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_j')
        fun sc hcpu_c0 hcl_c hnsp_c hsym_c => ?_
      have hcpu_c := hcpu_c0.1
      have ⟨hacp_jc, hvm_jc⟩ :=
        vmPreserved_of_seg hcpu_j0 hcpu_c0 hnsp_c hsym_c
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_jc :
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st_in) sm_fg' =
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st_in) sc :=
        (A.pool_transport lim _ sm_fg' sc hvm_jc).symm
      have hpc_c : sc.pc = cliIoPl00.base + 204#64 := hcpu_c.pc_eq.trans (by simp [arm64_norm])
      have hrun_c : sc.status = .Running := hcpu_c.status_eq.trans hrun_j'
      have hsp_c : sc.sp = s0.sp - 4224#64 :=
        hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = sj'.sp).trans (hcpu_j.sp_eq.trans hsp_fg'_eq))
      have hx19_c : sc.readReg64 (.gpr 19#5) = sret := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x19.trans hx19)
      have hx20_c : sc.readReg64 (.gpr 20#5) = newPtr := by
        rw [hcpu_c.readReg64]; simp [arm64_norm]
      have hx22_c : sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x22.trans hx22)
      have hx23_c : sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x23.trans hx23)
      have hx24_c : sc.readReg64 (.gpr 24#5) = 4096#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x24.trans hx24)
      have hx25_c : sc.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x25.trans hx25)
      have hx26_c : sc.readReg64 (.gpr 26#5) = 1048576#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x26.trans hx26)
      have hx27_c : sc.readReg64 (.gpr 27#5) = 1048577#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x27.trans hx27)
      have hx28_c : sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x28.trans hx28)
      have hx29_c : sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact hx29_j'
      have hvregs_c : calleeSavedVRegs sc = calleeSavedVRegs s0 :=
        hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sj').trans
          (hcpu_j.calleeSavedVRegs.trans (hcs_fg'.2.2.2.2.2.2.2.2.2.2.2.trans hvregs)))
      have hacp_fg_c : AllocCallPreserved sm_fg sc := allocCallPreserved_trans hacp_fg hacp_jc
      refine SepWP.weaken_pre ?_
        (hcont sc newPtr newPtr (BitVec.ofNat 64 newCap)
          hpc_c hrun_c hsp_c hx19_c hx20_c hx22_c hx23_c hx24_c hx25_c hx26_c hx27_c hx28_c hx29_c
          hvregs_c hcl_c hacp_fg_c)
      rw [hpool_eq_jc, hsp_eq,
        stackAt_shrink (s0.sp - 4224#64) (stackBytes - 4224) (32 + allocHookStack) hfg_stk_le hfg_stk_hi]
      simp only [vecHeader, bv_lin_norm]
      sep_entail

/-- `cap = 0` growth branch (`+0x94 = 148#64 .. +0x118 = 280#64` → `cliIoReadStdin_post_grow_b_reads` → `+0xcc = 204#64`):
    steps `0 → 4096` (`0` inner back-edges) and calls `finish_grow`. -/
private theorem cliIoReadStdin_grow_from_zero_b_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    {s0 sg : State} {sret v0 v1 v2 oldPtr st0 st1 st2 st3 : BitVec 64}
    {R_buf : SepProp} {n stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4256 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (_hn_pos : 0 < n) (hn_le : n ≤ 4096)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sg.mem)
    (hpc : sg.pc = cliIoPl00.base + 148#64)
    (hrun : sg.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : sg.sp = s0.sp - 4224#64)
    (hx0 : sg.readReg64 .x0 = BitVec.ofNat 64 n)
    (hx19 : sg.readReg64 (.gpr 19#5) = sret)
    (hx20 : sg.readReg64 (.gpr 20#5) = oldPtr)
    (hx21 : sg.readReg64 (.gpr 21#5) = 0#64)
    (hx24 : sg.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sg.readReg64 (.gpr 25#5) = 0#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sg.readReg64 (.gpr 27#5) = 1048577#64)
    (hx28 : sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 n)
    (hx29 : sg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sg = calleeSavedVRegs s0)
    (hoom_sg : ¬ FitsEvents M lim st_in (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) →
      ∀ sf_oom : State, OomPreserved sg sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl00.base + 204#64 → sc.status = .Running →
      sc.sp = s0.sp - 4224#64 →
      sc.readReg64 (.gpr 19#5) = sret →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap 0) →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = 4096#64 →
      sc.readReg64 (.gpr 25#5) = 0#64 →
      sc.readReg64 (.gpr 26#5) = 1048576#64 →
      sc.readReg64 (.gpr 27#5) = 1048577#64 →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs sc = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sc.mem →
      AllocCallPreserved sg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
          R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗
          ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗
          vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap 0)) newPtr [] ∗
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) st_in) sc)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sg
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
        R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc 0#64 oldPtr [] ∗
        A.pool lim st_in sg)
      post oomProp := by
  have hult_false : (4096#64 : BitVec 64).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le (by decide)
  apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
  intro sg' hcpu_g0
  have hcpu_g := hcpu_g0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_g' : sg'.pc = cliIoPl00.base + 148#64 := hcpu_g.pc_eq.trans hpc
  have hrun_g' : sg'.status = .Running := hcpu_g.status_eq.trans hrun
  have hsp_g' : sg'.spAligned = true := by
    rw [hcpu_g.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_g' : sg'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx0
  have hx19_g' : sg'.readReg64 (.gpr 19#5) = sret := (hcpu_g.readReg64 _).trans hx19
  have hx20_g' : sg'.readReg64 (.gpr 20#5) = oldPtr := (hcpu_g.readReg64 _).trans hx20
  have hx21_g' : sg'.readReg64 (.gpr 21#5) = 0#64 := (hcpu_g.readReg64 _).trans hx21
  have hx24_g' : sg'.readReg64 (.gpr 24#5) = 4096#64 := (hcpu_g.readReg64 _).trans hx24
  have hx25_g' : sg'.readReg64 (.gpr 25#5) = 0#64 := (hcpu_g.readReg64 _).trans hx25
  have hx26_g' : sg'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_g.readReg64 _).trans hx26
  have hx27_g' : sg'.readReg64 (.gpr 27#5) = 1048577#64 := (hcpu_g.readReg64 _).trans hx27
  have hx28_g' : sg'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx28
  have hx29_g' : sg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 := (hcpu_g.readReg64 _).trans hx29
  wp_sym_steps
  refine SepWP.done cliIoReadStdin_grow_pc (by simpa [arm64_norm] using hrun_g')
    fun sm_fg hcpu_fg0 hcl_fg hnsp_fg hsym_fg => ?_
  have hcpu_fg := hcpu_fg0.1
  have ⟨hacp_gfg, hvm_gfg⟩ :=
    vmPreserved_of_seg hcpu_g0 hcpu_fg0 hnsp_fg hsym_fg
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_gfg : A.pool lim st_in sg = A.pool lim st_in sm_fg :=
    (A.pool_transport lim st_in sg sm_fg hvm_gfg).symm
  have hpc_fg : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym :=
    hcpu_fg.pc_eq.trans cliIoReadStdin_grow_pc
  have hrun_fg : sm_fg.status = .Running := hcpu_fg.status_eq.trans hrun_g'
  have hsp_fg : sm_fg.sp = s0.sp - 4224#64 :=
    hcpu_fg.sp_eq.trans ((by simp [arm64_norm] : _ = sg'.sp).trans (hcpu_g.sp_eq.trans hsp_eq))
  have hlr_fg : sm_fg.readReg64 .lr = cliIoPl00.base + 284#64 := by
    rw [hcpu_fg.readReg64 .lr]; simp [arm64_norm]
  have hx0_fg : sm_fg.readReg64 .x0 = s0.sp - 128#64 := by
    rw [hcpu_fg.readReg64 .x0]; simp [arm64_norm]
  have hx1_fg : sm_fg.readReg64 .x1 = 0#64 := by
    rw [hcpu_fg.readReg64 .x1]; simp [arm64_norm]
  have hx2_fg : sm_fg.readReg64 .x2 = oldPtr := by
    rw [hcpu_fg.readReg64 .x2]; simp [arm64_norm]
  have hx3_fg : sm_fg.readReg64 .x3 = BitVec.ofNat 64 (cliIoCap 0) := by
    rw [hcpu_fg.readReg64 .x3]; simp [arm64_norm, cliIoCap_zero]
  have hx19_fg : sm_fg.readReg64 (.gpr 19#5) = sret := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx19_g']
  have hx22_fg : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap 0) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, cliIoCap_zero]
  have hx23_fg : sm_fg.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx24_fg : sm_fg.readReg64 (.gpr 24#5) = 4096#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx24_g']
  have hx25_fg : sm_fg.readReg64 (.gpr 25#5) = BitVec.ofNat 64 0 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx25_g']
  have hx26_fg : sm_fg.readReg64 (.gpr 26#5) = 1048576#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx26_g']
  have hx27_fg : sm_fg.readReg64 (.gpr 27#5) = 1048577#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx27_g']
  have hx28_fg : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (0 + n) := by
    rw [hcpu_fg.readReg64]; simpa [arm64_norm] using hx28_g'
  have hx29_fg : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx29_g']
  have hvregs_fg : calleeSavedVRegs sm_fg = calleeSavedVRegs s0 :=
    hcpu_fg.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sg').trans
      (hcpu_g.calleeSavedVRegs.trans hvregs))
  rw [hpool_eq_gfg]
  exact cliIoReadStdin_post_grow_b_reads A lim hext0 hfg hlo hhi
    (by decide : 0 < cliIoCap 0) (cliIoCap_lt_pow63 (by decide))
    (Nat.zero_le _) (not_nullAllowed_cliIoCap_budget (by decide))
    hcl_fg hpc_fg hrun_fg hsp0 hsp_fg hlr_fg
    hx0_fg hx1_fg hx2_fg hx3_fg hx19_fg hx22_fg hx23_fg hx24_fg hx25_fg hx26_fg hx27_fg hx28_fg hx29_fg
    hvregs_fg
    (fun hnot sf_oom hoom_pres =>
      hoom_sg hnot sf_oom (oomPreserved_of_allocCallPreserved hacp_gfg hoom_pres))
    (fun sc newPtr st1' st2' hpc_c hrun_c hsp_c hx19_c hx20_c hx22_c hx23_c hx24_c hx25_c
        hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c hacp_fgc =>
      hcont sc newPtr st1' st2' hpc_c hrun_c hsp_c hx19_c hx20_c hx22_c hx23_c hx24_c
        (by simpa using hx25_c) hx26_c hx27_c (by simpa using hx28_c) hx29_c hvregs_c hcl_c
        (allocCallPreserved_trans hacp_gfg hacp_fgc))

/-- `cap = cliIoCap j` growth branch (`+0x94 = 148#64 .. +0x118 = 280#64` → `cliIoReadStdin_post_grow_b_reads` → `+0xcc = 204#64`):
    steps `cliIoCap j → cliIoCap (j + 1)` (`1` inner back-edge) and calls `finish_grow`. -/
private theorem cliIoReadStdin_grow_from_pos_b_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    {s0 sg : State} {sret v0 v1 v2 oldPtr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {R_buf : SepProp}
    {j len n stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4256 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hj1 : j + 1 ≤ 8)
    (hlen_le_cap : len ≤ cliIoCap j)
    (hbs_len : bs.length = len)
    (hgt_cap : cliIoCap j < len + n)
    (hle_next : len + n ≤ cliIoCap (j + 1))
    (hcl : CliIoReadsCodeLoaded cliIoMpl sg.mem)
    (hpc : sg.pc = cliIoPl00.base + 148#64)
    (hrun : sg.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : sg.sp = s0.sp - 4224#64)
    (hx0 : sg.readReg64 .x0 = BitVec.ofNat 64 n)
    (hx19 : sg.readReg64 (.gpr 19#5) = sret)
    (hx20 : sg.readReg64 (.gpr 20#5) = oldPtr)
    (hx21 : sg.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap j))
    (hx24 : sg.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sg.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sg.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sg.readReg64 (.gpr 27#5) = 1048577#64)
    (hx28 : sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n))
    (hx29 : sg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sg = calleeSavedVRegs s0)
    (hoom_sg :
      ¬ FitsEvents M lim st_in
          (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1))) →
      ∀ sf_oom : State, OomPreserved sg sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl00.base + 204#64 → sc.status = .Running →
      sc.sp = s0.sp - 4224#64 →
      sc.readReg64 (.gpr 19#5) = sret →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap (j + 1)) →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = 4096#64 →
      sc.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 26#5) = 1048576#64 →
      sc.readReg64 (.gpr 27#5) = 1048577#64 →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs sc = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sc.mem →
      AllocCallPreserved sg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
          R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗
          ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗
          vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap (j + 1))) newPtr bs ∗
          A.pool lim
            (M.stepEvents
              (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1)))
              st_in) sc)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sg
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
        R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap j)) oldPtr bs ∗
        A.pool lim st_in sg)
      post oomProp := by
  have hj9 : j ≤ 9 := by omega
  have hj1_9 : j + 1 ≤ 9 := by omega
  have hcap_pos : 0 < cliIoCap j := cliIoCap_pos j
  have hcap_lt64 : cliIoCap j < 2 ^ 64 := cliIoCap_lt_pow64 hj9
  have hnext_lt64 : cliIoCap (j + 1) < 2 ^ 64 := cliIoCap_lt_pow64 hj1_9
  have hcap_beq0 : (BitVec.ofNat 64 (cliIoCap j) == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) hcap_lt64 (by decide)
  have hlsl1 : (BitVec.ofNat 64 (cliIoCap j)) <<< 1 = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [bv64_shiftLeft1_ofNat (by rw [← cliIoCap_succ]; exact hnext_lt64), ← cliIoCap_succ]
  have hult1 : (BitVec.ofNat 64 (cliIoCap j)).ult (BitVec.ofNat 64 (len + n)) = true :=
    bv64_ult_ofNat_true hgt_cap (Nat.lt_of_le_of_lt hle_next hnext_lt64)
  have hult2 : (BitVec.ofNat 64 (cliIoCap (j + 1))).ult (BitVec.ofNat 64 (len + n)) = false :=
    bv64_ult_ofNat_false hle_next hnext_lt64
  have hclamp :
      (if (BitVec.ofNat 64 (cliIoCap (j + 1))).ult 1048576#64 = true
       then BitVec.ofNat 64 (cliIoCap (j + 1))
       else 1048576#64) = BitVec.ofNat 64 (cliIoCap (j + 1)) :=
    cliIoStdin_cap_clamp_bv hj1
  have hcap_lt_next : cliIoCap j < cliIoCap (j + 1) := cliIoCap_strictMono (Nat.lt_succ_self j)
  have hsub_hi :
      (BitVec.ofNat 64 (cliIoCap j) - BitVec.ofNat 64 len).ult
        (BitVec.ofNat 64 (cliIoCap (j + 1)) - BitVec.ofNat 64 len) = true := by
    rw [bv64_sub_ofNat hlen_le_cap,
      bv64_sub_ofNat (Nat.le_trans hlen_le_cap (Nat.le_of_lt hcap_lt_next))]
    exact bv64_ult_ofNat_true (by omega) (by omega)
  have hnext_ult_len : (BitVec.ofNat 64 (cliIoCap (j + 1))).ult (BitVec.ofNat 64 len) = false :=
    bv64_ult_ofNat_false (Nat.le_trans hlen_le_cap (Nat.le_of_lt hcap_lt_next)) hnext_lt64
  apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
  intro sg' hcpu_g0
  have hcpu_g := hcpu_g0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_g' : sg'.pc = cliIoPl00.base + 148#64 := hcpu_g.pc_eq.trans hpc
  have hrun_g' : sg'.status = .Running := hcpu_g.status_eq.trans hrun
  have hsp_g' : sg'.spAligned = true := by
    rw [hcpu_g.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_g' : sg'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx0
  have hx19_g' : sg'.readReg64 (.gpr 19#5) = sret := (hcpu_g.readReg64 _).trans hx19
  have hx20_g' : sg'.readReg64 (.gpr 20#5) = oldPtr := (hcpu_g.readReg64 _).trans hx20
  have hx21_g' : sg'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap j) :=
    (hcpu_g.readReg64 _).trans hx21
  have hx24_g' : sg'.readReg64 (.gpr 24#5) = 4096#64 := (hcpu_g.readReg64 _).trans hx24
  have hx25_g' : sg'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len := (hcpu_g.readReg64 _).trans hx25
  have hx26_g' : sg'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_g.readReg64 _).trans hx26
  have hx27_g' : sg'.readReg64 (.gpr 27#5) = 1048577#64 := (hcpu_g.readReg64 _).trans hx27
  have hx28_g' : sg'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) :=
    (hcpu_g.readReg64 _).trans hx28
  have hx29_g' : sg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 := (hcpu_g.readReg64 _).trans hx29
  wp_sym_steps
  refine SepWP.done cliIoReadStdin_grow_pc (by simpa [arm64_norm] using hrun_g')
    fun sm_fg hcpu_fg0 hcl_fg hnsp_fg hsym_fg => ?_
  have hcpu_fg := hcpu_fg0.1
  have ⟨hacp_gfg, hvm_gfg⟩ :=
    vmPreserved_of_seg hcpu_g0 hcpu_fg0 hnsp_fg hsym_fg
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_gfg : A.pool lim st_in sg = A.pool lim st_in sm_fg :=
    (A.pool_transport lim st_in sg sm_fg hvm_gfg).symm
  have hpc_fg : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym :=
    hcpu_fg.pc_eq.trans cliIoReadStdin_grow_pc
  have hrun_fg : sm_fg.status = .Running := hcpu_fg.status_eq.trans hrun_g'
  have hsp_fg : sm_fg.sp = s0.sp - 4224#64 :=
    hcpu_fg.sp_eq.trans ((by simp [arm64_norm] : _ = sg'.sp).trans (hcpu_g.sp_eq.trans hsp_eq))
  have hlr_fg : sm_fg.readReg64 .lr = cliIoPl00.base + 284#64 := by
    rw [hcpu_fg.readReg64 .lr]; simp [arm64_norm]
  have hx0_fg : sm_fg.readReg64 .x0 = s0.sp - 128#64 := by
    rw [hcpu_fg.readReg64 .x0]; simp [arm64_norm]
  have hx1_fg : sm_fg.readReg64 .x1 = BitVec.ofNat 64 (cliIoCap j) := by
    rw [hcpu_fg.readReg64 .x1]; simp [arm64_norm]
  have hx2_fg : sm_fg.readReg64 .x2 = oldPtr := by
    rw [hcpu_fg.readReg64 .x2]; simp [arm64_norm]
  have hx3_fg : sm_fg.readReg64 .x3 = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [hcpu_fg.readReg64 .x3]; simp [arm64_norm]
  have hx19_fg : sm_fg.readReg64 (.gpr 19#5) = sret := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx19_g']
  have hx22_fg : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx23_fg : sm_fg.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx24_fg : sm_fg.readReg64 (.gpr 24#5) = 4096#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx24_g']
  have hx25_fg : sm_fg.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx25_g']
  have hx26_fg : sm_fg.readReg64 (.gpr 26#5) = 1048576#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx26_g']
  have hx27_fg : sm_fg.readReg64 (.gpr 27#5) = 1048577#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx27_g']
  have hx28_fg : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx28_g']
  have hx29_fg : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx29_g']
  have hvregs_fg : calleeSavedVRegs sm_fg = calleeSavedVRegs s0 :=
    hcpu_fg.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sg').trans
      (hcpu_g.calleeSavedVRegs.trans hvregs))
  rw [hpool_eq_gfg]
  exact cliIoReadStdin_post_grow_b_reads A lim hext0 hfg hlo hhi
    (cliIoCap_pos (j + 1)) (cliIoCap_lt_pow63 hj1_9)
    (by rw [hbs_len]; omega) (not_nullAllowed_cliIoCap_budget hj1_9)
    hcl_fg hpc_fg hrun_fg hsp0 hsp_fg hlr_fg
    hx0_fg hx1_fg hx2_fg hx3_fg hx19_fg hx22_fg hx23_fg hx24_fg hx25_fg hx26_fg hx27_fg hx28_fg hx29_fg
    hvregs_fg
    (fun hnot sf_oom hoom_pres =>
      hoom_sg hnot sf_oom (oomPreserved_of_allocCallPreserved hacp_gfg hoom_pres))
    (fun sc newPtr st1' st2' hpc_c hrun_c hsp_c hx19_c hx20_c hx22_c hx23_c hx24_c hx25_c
        hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c hacp_fgc =>
      hcont sc newPtr st1' st2' hpc_c hrun_c hsp_c hx19_c hx20_c hx22_c hx23_c hx24_c
        hx25_c hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c
        (allocCallPreserved_trans hacp_gfg hacp_fgc))

/-- Shared `memcpy(ptr + len, sp, chunk)` + back-edge `+0xdc .. +0xf4 → +0x48 = 72#64` join. -/
private theorem cliIoReadStdin_memcpy_backedge_b_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
      allocMemcpyVmSpec)
    {s0 sc : State} {sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {rem chunk oldBuf : List (BitVec 8)}
    {cap len want stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcap_pos : 0 < cap) (hcap_lt63 : cap < 2 ^ 63)
    (hlen_r : len + chunk.length ≤ rem.length)
    (hlen_cap : len + chunk.length ≤ cap)
    (hlen_max : len + chunk.length ≤ 1048576)
    (hwant_le : want ≤ 4096)
    (hold_len : oldBuf.length = want)
    (hn_le_want : chunk.length ≤ want)
    (hchunk_eq : chunk = (rem.drop len).take want)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sc.mem)
    (hpc : sc.pc = cliIoPl00.base + 204#64)
    (hrun : sc.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : sc.sp = s0.sp - 4224#64)
    (hx19 : sc.readReg64 (.gpr 19#5) = sret)
    (hx20 : sc.readReg64 (.gpr 20#5) = ptr)
    (hx22 : sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap)
    (hx23 : sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 chunk.length)
    (hx24 : sc.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sc.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sc.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sc.readReg64 (.gpr 27#5) = 1048577#64)
    (hx28 : sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + chunk.length))
    (hx29 : sc.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sc = calleeSavedVRegs s0)
    (hcont : ∀ sn : State,
      sn.pc = cliIoPl00.base + 72#64 → sn.status = .Running → sn.sp = s0.sp - 4224#64 →
      sn.readReg64 (.gpr 19#5) = sret → sn.readReg64 (.gpr 20#5) = ptr →
      sn.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sn.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 1048576 (len + chunk.length)) →
      sn.readReg64 (.gpr 24#5) = 4096#64 →
      sn.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (len + chunk.length) →
      sn.readReg64 (.gpr 26#5) = 1048576#64 → sn.readReg64 (.gpr 27#5) = 1048577#64 →
      sn.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sn = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sn.mem → StdinMidPreserved sc sn →
      SepWP P (s0.readReg64 .lr) sn
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take (len + chunk.length)) ∗
          A.pool lim st_cur sn)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sc
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
        (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
          memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want)) ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take len) ∗
        A.pool lim st_cur sc)
      post oomProp := by
  have hcap_lt64 : cap < 2 ^ 64 := Nat.lt_trans hcap_lt63 (by decide)
  have htake_len : (rem.take len).length = len := List.length_take_of_le (by omega)
  wp_conv_pre =>
    rw [cliIoVecBuf_unpack_pos A.repAlloc hcap_pos hcap_lt63]
    simp only [sepConj_assoc, sepConj_pure_mid]
  apply SepWP.pure_elim; rintro ⟨_, _, hptr_ne0⟩
  wp_conv_pre =>
    rw [htake_len,
      memRegion_split_le (ptr + BitVec.ofNat 64 len) chunk.length (cap - len) (by omega) (by omega),
      show ptr + BitVec.ofNat 64 len + BitVec.ofNat 64 chunk.length =
        ptr + BitVec.ofNat 64 (len + chunk.length) by rw [BitVec.ofNat_add]; bv_lin,
      show cap - len - chunk.length = cap - (len + chunk.length) by omega,
      pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
    simp only [sepConj_assoc]
  apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
  intro sc' hcpu_c0
  have hcpu_c := hcpu_c0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_c' : sc'.pc = cliIoPl00.base + 204#64 := hcpu_c.pc_eq.trans hpc
  have hrun_c' : sc'.status = .Running := hcpu_c.status_eq.trans hrun
  have hsp_c_in : sc'.sp = s0.sp - 4224#64 := hcpu_c.sp_eq.trans hsp_eq
  have hsp_c' : sc'.spAligned = true := by
    rw [hcpu_c.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx20_c' : sc'.readReg64 (.gpr 20#5) = ptr := (hcpu_c.readReg64 _).trans hx20
  have hx23_c' : sc'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 chunk.length :=
    (hcpu_c.readReg64 _).trans hx23
  have hx25_c' : sc'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len :=
    (hcpu_c.readReg64 _).trans hx25
  wp_sym_steps
  refine SepWP.done cliIoReadStdin_memcpy_pc (by simpa [arm64_norm] using hrun_c')
    fun sm_mc hcpu_mc0 hcl_mc hnsp_mc hsym_mc => ?_
  have hcpu_mc := hcpu_mc0.1
  have ⟨hacp_cmc, hvm_cmc⟩ :=
    vmPreserved_of_seg hcpu_c0 hcpu_mc0 hnsp_mc hsym_mc
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_cmc : A.pool lim st_cur sc = A.pool lim st_cur sm_mc :=
    (A.pool_transport lim st_cur sc sm_mc hvm_cmc).symm
  have hpc_mc : sm_mc.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym :=
    hcpu_mc.pc_eq.trans cliIoReadStdin_memcpy_pc
  have hrun_mc : sm_mc.status = .Running := hcpu_mc.status_eq.trans hrun_c'
  have hsp_mc_eq : sm_mc.sp = s0.sp - 4224#64 :=
    hcpu_mc.sp_eq.trans ((by simp [arm64_norm] : _ = sc'.sp).trans hsp_c_in)
  have hsp_mc : sm_mc.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_mc_eq]; exact s0.spAligned_sub 4224#64 hsp0
  have hlr_mc : sm_mc.readReg64 .lr = cliIoPl00.base + 220#64 := by
    rw [hcpu_mc.readReg64 .lr]; simp [arm64_norm]
  have hx0_mc : sm_mc.readReg64 .x0 = ptr + BitVec.ofNat 64 len := by
    rw [hcpu_mc.readReg64 .x0]; simp [arm64_norm]
  have hx1_mc : sm_mc.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_mc.readReg64 .x1]; simp [arm64_norm]
  have hx2_mc : sm_mc.readReg64 .x2 = BitVec.ofNat 64 chunk.length := by
    rw [hcpu_mc.readReg64 .x2]; simp [arm64_norm, hchunk_eq]
  apply seqCodeLoadedWhere hcl_mc (mid := cliIoPl00.base + 220#64)
  apply (SepWP.call_subroutine_frame hmemcpy
    (x := (ptr + BitVec.ofNat 64 len, s0.sp - 4224#64, chunk))
    hpc_mc hrun_mc hsp_mc hlr_mc
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [allocMemcpyVmSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    have hchunk_lt64 : chunk.length < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.le_trans hn_le_want hwant_le) (by decide)
    refine ⟨⟨hx0_mc, hx1_mc, hx2_mc, hchunk_lt64⟩, ?_⟩
    rw [hpool_eq_cmc] at hm'
    exact Satisfies.mono (by sep_frame) hm'
  · intro sm_mc' hpc_mc' hrun_mc' hsp_mc' hcs_mc'
    refine SepWP.done hpc_mc' hrun_mc' fun hcl_mc' => ?_
    wp_conv_pre => dsimp only [allocMemcpyVmSpec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hacp_mc, hvm_mc⟩
    have hmid_mc : StdinMidPreserved sm_mc sm_mc' := StdinMidPreserved.of_alloc hacp_mc
    have hpool_eq_mc : A.pool lim st_cur sm_mc = A.pool lim st_cur sm_mc' :=
      (A.pool_transport lim st_cur sm_mc sm_mc' hvm_mc).symm
    have hsp_mc'_eq : sm_mc'.sp = s0.sp - 4224#64 := hsp_mc'.trans hsp_mc_eq
    have hx22_mc' : sm_mc'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap :=
      hcs_mc'.readReg64_x22.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 22#5)).trans
          ((hcpu_c.readReg64 _).trans hx22)))
    have hx24_mc' : sm_mc'.readReg64 (.gpr 24#5) = 4096#64 :=
      hcs_mc'.readReg64_x24.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 24#5)).trans
          ((hcpu_c.readReg64 _).trans hx24)))
    have hx27_mc' : sm_mc'.readReg64 (.gpr 27#5) = 1048577#64 :=
      hcs_mc'.readReg64_x27.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 27#5)).trans
          ((hcpu_c.readReg64 _).trans hx27)))
    have hx28_mc' : sm_mc'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + chunk.length) :=
      hcs_mc'.readReg64_x28.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 28#5)).trans
          ((hcpu_c.readReg64 _).trans hx28)))
    have hsub27 :
        1048577#64 - BitVec.ofNat 64 (len + chunk.length) =
          BitVec.ofNat 64 (1048576 + 1 - (len + chunk.length)) := by
      change BitVec.ofNat 64 1048577 - BitVec.ofNat 64 (len + chunk.length) = _
      exact bv64_sub_ofNat (by omega)
    have hule :
        (BitVec.ofNat 64 (len + ((rem.drop len).take want).length)).ule 1048576#64 = true := by
      rw [← hchunk_eq]
      simp [BitVec.ule, BitVec.toNat_ofNat]; omega
    apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl_mc'
      (mid := cliIoPl00.base + 72#64)
    intro sb' hcpu_b0
    have hcpu_b := hcpu_b0.1
    change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
    have hpc_b' : sb'.pc = cliIoPl00.base + 220#64 := hcpu_b.pc_eq.trans hpc_mc'
    have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_mc'
    have hsp_b' : sb'.spAligned = true := by
      rw [hcpu_b.spAligned]; simp only [State.spAligned]; rw [hsp_mc'_eq]
      exact s0.spAligned_sub 4224#64 hsp0
    have hx22_b' : sb'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap :=
      (hcpu_b.readReg64 _).trans hx22_mc'
    have hx24_b' : sb'.readReg64 (.gpr 24#5) = 4096#64 :=
      (hcpu_b.readReg64 _).trans hx24_mc'
    have hx27_b' : sb'.readReg64 (.gpr 27#5) = 1048577#64 :=
      (hcpu_b.readReg64 _).trans hx27_mc'
    have hx28_b' : sb'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + chunk.length) :=
      (hcpu_b.readReg64 _).trans hx28_mc'
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
      fun sn hcpu_n0 hcl_n hnsp_n hsym_n => ?_
    have hcpu_n := hcpu_n0.1
    have ⟨hacp_bn, hvm_bn⟩ :=
      vmPreserved_of_seg hcpu_b0 hcpu_n0 hnsp_n hsym_n
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_bn : A.pool lim st_cur sm_mc' = A.pool lim st_cur sn :=
      (A.pool_transport lim st_cur sm_mc' sn hvm_bn).symm
    have hpc_n : sn.pc = cliIoPl00.base + 72#64 := by
      rw [hcpu_n.pc_eq]; simp [arm64_norm]
    have hrun_n : sn.status = .Running := hcpu_n.status_eq.trans hrun_b'
    have hsp_n : sn.sp = s0.sp - 4224#64 :=
      hcpu_n.sp_eq.trans ((by simp [arm64_norm] : _ = sb'.sp).trans (hcpu_b.sp_eq.trans hsp_mc'_eq))
    have hx19_n : sn.readReg64 (.gpr 19#5) = sret := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x19, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx19
    have hx20_n : sn.readReg64 (.gpr 20#5) = ptr := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x20, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact hx20_c'
    have hx21_n : sn.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := by
      rw [hcpu_n.readReg64]; simp [arm64_norm]
    have hx23_n : sn.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 1048576 (len + chunk.length)) := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]; rw [← hchunk_eq, hsub27]
      exact wantBytes_csel_bv hlen_max (by decide)
    have hx24_n : sn.readReg64 (.gpr 24#5) = 4096#64 := by
      rw [hcpu_n.readReg64]; simp [arm64_norm, hx24_b']
    have hx25_n : sn.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (len + chunk.length) := by
      rw [hcpu_n.readReg64]; simp [arm64_norm, hchunk_eq]
    have hx26_n : sn.readReg64 (.gpr 26#5) = 1048576#64 := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x26, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx26
    have hx27_n : sn.readReg64 (.gpr 27#5) = 1048577#64 := by
      rw [hcpu_n.readReg64]; simp [arm64_norm, hx27_b']
    have hx29_n : sn.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x29, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx29
    have hvregs_n : calleeSavedVRegs sn = calleeSavedVRegs s0 :=
      hcpu_n.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
        (hcpu_b.calleeSavedVRegs.trans (hcs_mc'.vregs.trans
          (hcpu_mc.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sc').trans
            (hcpu_c.calleeSavedVRegs.trans hvregs))))))
    have hmid_cn : StdinMidPreserved sc sn :=
      (StdinMidPreserved.of_alloc hacp_cmc).trans
        (hmid_mc.trans (StdinMidPreserved.of_alloc hacp_bn))
    refine SepWP.weaken_pre ?_
      (hcont sn hpc_n hrun_n hsp_n hx19_n hx20_n hx21_n hx23_n hx24_n hx25_n hx26_n hx27_n hx29_n
        hvregs_n hcl_n hmid_cn)
    rw [hpool_eq_mc, hpool_eq_bn]
    have hvec_back :
        A.live ptr cap 1 ∗
          (ptr ↦ₛ rem.take len) ∗
          ((ptr + BitVec.ofNat 64 len) ↦ₛ chunk) ∗
          memRegion (ptr + BitVec.ofNat 64 (len + chunk.length)) (cap - (len + chunk.length)) ⊢
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take (len + chunk.length)) :=
      cliIoVecBuf_repack_chunk A.repAlloc hcap_pos hcap_lt63 hptr_ne0 hlen_r hlen_cap hchunk_eq
    have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
    let Rest : SepProp :=
      stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        A.pool lim st_cur sn
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := Rest) (sepConj_mono hvec_back hbuf_back))
        (by dsimp only [Rest]; sep_entail))
    dsimp only [Rest]; sep_entail


/-- Full bounded `4096`-byte `read_stdin` loop from header `+0x48 = 72#64` by strong induction on
    `fuel = cliIoStdinCap + 1 - len`, threading `(M : AllocCostModel) (A : RustCliAllocBudget M)`. -/
private theorem cliIoReadStdin_loop_b_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
      allocMemcpyVmSpec)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    {s0 : State} {d0 : FdEntry} {sret v0 v1 v2 : BitVec 64}
    {stackBytes : Nat} {st : M.σ}
    {post : State → SepProp → Prop}
    (hlo : 4256 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hsp0 : s0.spAligned = true)
    (hkind : d0.kind = .stdio) (hcanr : d0.accMode.canRead = true)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢
          let bs := s0.fs.stdin.drop d0.offset
          ⌜sf.fs.files = s0.fs.files ∧ sf.trace = s0.trace ∧
            (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs)⌝ ∗
            ioVecAt A.repAlloc sret (readStdinResult bs) ∗
            stackAt s0.sp stackBytes ∗
            A.pool lim (M.stepEvents (readStdinBudgetEvents bs) st) sf) →
        post sf Pre_f) :
    ∀ (fuel : Nat) (sl : State) (ptr st0 st1 st2 st3 : BitVec 64) (cap len : Nat) (st_cur : M.σ),
      cliIoStdinCap + 1 - len ≤ fuel →
      len ≤ min (s0.fs.stdin.drop d0.offset).length cliIoStdinCap →
      (len < (s0.fs.stdin.drop d0.offset).length → 4096 ∣ len) →
      cap = cliIoFinalCap 8 len →
      st_cur = M.stepEvents (stdinLoopEvents len) st →
      CliIoReadsCodeLoaded cliIoMpl sl.mem →
      sl.pc = cliIoPl00.base + 72#64 → sl.status = .Running → sl.sp = s0.sp - 4224#64 →
      sl.readReg64 (.gpr 19#5) = sret → sl.readReg64 (.gpr 20#5) = ptr →
      sl.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 1048576 len) →
      sl.readReg64 (.gpr 24#5) = 4096#64 → sl.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sl.readReg64 (.gpr 26#5) = 1048576#64 → sl.readReg64 (.gpr 27#5) = 1048577#64 →
      sl.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sl = calleeSavedVRegs s0 →
      sl.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + len }) →
      sl.trace = s0.trace → sl.sigActions = s0.sigActions →
      SepWP P (s0.readReg64 .lr) sl
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr ((s0.fs.stdin.drop d0.offset).take len) ∗
          A.pool lim st_cur sl)
        post
        (fun sf =>
          ⌜¬ FitsEvents M lim st (readStdinBudgetEvents (s0.fs.stdin.drop d0.offset)) ∧
            CliIoFilesOomPreserved s0 sf⌝) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro sl ptr st0 st1 st2 st3 cap len st_cur
      hfuel hlen_le hdvd hcap_eq hst_eq hcl hpc hrun hsp_eq
      hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx29 hvregs
      hfs_sl htr_sl hsig_sl
    let rem := s0.fs.stdin.drop d0.offset
    have hrem_def : rem = s0.fs.stdin.drop d0.offset := rfl
    let want := wantBytes 1048576 len
    have hwant_def : want = wantBytes 1048576 len := rfl
    have hcap1048 : cliIoStdinCap = 1048576 := rfl
    have hlen_max : len ≤ cliIoStdinCap := Nat.le_trans hlen_le (Nat.min_le_right _ _)
    have hlen_rem : len ≤ rem.length := Nat.le_trans hlen_le (Nat.min_le_left _ _)
    have hwant_le : want ≤ 4096 := wantBytes_le_4096 1048576 len
    let R_fr : SepProp :=
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take len)
    refine SepWP.weaken_pre (by dsimp only [R_fr]; sep_entail)
      (cliIoReadStdin_do_read_b_reads A lim hext0 hread (R_frame := R_fr) (by omega) hhi hsp_lo
        hsp_va hwant_le hkind hcanr hfs_sl hcl hpc hrun hsp0 hsp_eq
        hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx29 hvregs
        fun sr oldBuf hold_len hpc_sr hrun_sr hsp_sr hx0_sr hx19_sr hx20_sr hx21_sr hx23_sr
            hx24_sr hx25_sr hx26_sr hx27_sr hx29_sr hvregs_sr hcl_sr hfs_sr htr_sr hsig_sr => ?_)
    dsimp only [R_fr]
    let chunk := (rem.drop len).take want
    have hchunk_def : chunk = (rem.drop len).take want := rfl
    have hn_min : chunk.length = min (rem.length - len) want := by
      rw [hchunk_def, List.length_take, List.length_drop, Nat.min_comm]
    have hn_le_want : chunk.length ≤ want := by rw [hn_min]; exact Nat.min_le_right _ _
    have hn_le_rem : len + chunk.length ≤ rem.length := by rw [hn_min]; omega
    rcases Nat.eq_zero_or_pos chunk.length with hn0 | hn_pos
    · -- EOF (`chunk.length = 0`, so `len = rem.length ≤ 1048576`)
      have hwant_pos : 0 < want := wantBytes_pos (by omega : len ≤ 1048576)
      have hlen_eq_rem : len = rem.length := by omega
      have hrem_le_cap : rem.length ≤ 1048576 := by omega
      have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
      have htake_rem : rem.take len = rem := by rw [hlen_eq_rem, List.take_length]
      have hx0_0 : sr.readReg64 .x0 = 0#64 := by rw [hx0_sr, ← hchunk_def, hn0]
      have hx25_rem : sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 rem.length := by
        rw [hx25_sr, hlen_eq_rem]
      refine SepWP.weaken_pre ?_
        (cliIoReadStdin_after_read_eof_b_reads A lim hext0
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
          (st_cur := st_cur)
          (by omega) hhi hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
          hx0_0 hx19_sr hx20_sr hx21_sr hx25_rem hvregs_sr
          fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hmid_srf Pre_f hent =>
            hpost sf hpc_f hrun_f hsp_f hcs_f hcl_f (Entails.trans hent ?_))
      · rw [htake_rem]
        let Rest : SepProp :=
          stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
            ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
            cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr rem ∗ A.pool lim st_cur sr
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q := Rest) hbuf_back) (by dsimp only [Rest]; sep_entail))
        rw [← hrem_def, ← hchunk_def,
          pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
        dsimp only [Rest]; sep_entail
      · have hfs_f : sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + rem.length }) := by
          rw [hmid_srf.1, hfs_sr, ← hchunk_def, hn0, Nat.add_zero, hlen_eq_rem]
        have hfiles : sf.fs.files = s0.fs.files :=
          (congrArg FsState.files hfs_f).trans (setFd_files_eq s0.fs 0#64 _)
        have htr : sf.trace = s0.trace := hmid_srf.2.1.trans (htr_sr.trans htr_sl)
        have hfds : FdsGe3Closed s0.fs → FdsGe3Closed sf.fs := fun hcl0 =>
          hfs_f ▸ fdsGe3Closed_setFd_lt3 (by decide : (0#64 : BitVec 64).toNat < 3) _ hcl0
        have hst_f : st_cur = M.stepEvents (readStdinBudgetEvents rem) st := by
          rw [hst_eq, hlen_eq_rem, ← readStdinBudgetEvents_of_le hrem_le_cap]
        dsimp only
        rw [← hrem_def, readStdinResult_eq_ok_of_le hrem_le_cap, ← hst_f,
          pure_sepConj_of_true ⟨hfiles, htr, hfds⟩]
        sep_entail
    · -- `0 < chunk.length`
      by_cases hover : cliIoStdinCap < len + chunk.length
      · -- Over-cap (`len = cliIoStdinCap = cliIoCap 8`, `chunk.length = 1`, `1048576 < rem.length`)
        have ⟨hlen_eq, hn_eq1, hrem_gt⟩ :=
          overCap_forces_eq_max (K := 8) hlen_le hdvd hn_min hn_pos hover
        have hrem_gt' : 1048576 < rem.length := hrem_gt
        have hwant_eq1 : want = 1 := by rw [hwant_def, hlen_eq]; rfl
        have hidx8 : cliIoCapIdx 8 len = 8 := by rw [hlen_eq]; exact cliIoCapIdx_cap_self 8
        have hcap8 : cap = cliIoCap 8 := by rw [hcap_eq, cliIoFinalCap_pos (by omega), hidx8]
        have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
        refine SepWP.weaken_pre ?_
          (cliIoReadStdin_after_read_overcap_b_reads A lim hext0 hdealloc
            (v0 := v0) (v1 := v1) (v2 := v2)
            (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (bs := rem.take len) (st_cur := st_cur)
            (by omega) hhi hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            (by rw [hx0_sr, ← hchunk_def, hn_eq1]) hx19_sr hx20_sr
            (by rw [hx21_sr, hcap8]) (by rw [hx23_sr, hwant_eq1])
            (by rw [hx25_sr, hlen_eq]; rfl) hx26_sr hvregs_sr
            fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hmid_srf Pre_f hent =>
              hpost sf hpc_f hrun_f hsp_f hcs_f hcl_f (Entails.trans hent ?_))
        · rw [hcap8]
          let Rest : SepProp :=
            stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
              ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
              cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap 8)) ptr (rem.take len) ∗
              A.pool lim st_cur sr
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono_left (Q := Rest) hbuf_back) (by dsimp only [Rest]; sep_entail))
          rw [← hrem_def, ← hchunk_def,
            pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
          dsimp only [Rest]; sep_entail
        · have hfs_f : sf.fs = s0.fs.setFd 0#64
              (some { d0 with offset := d0.offset + (cliIoStdinCap + 1) }) := by
            rw [hmid_srf.1, hfs_sr, ← hchunk_def, hn_eq1, hlen_eq]; rfl
          have hfiles : sf.fs.files = s0.fs.files :=
            (congrArg FsState.files hfs_f).trans (setFd_files_eq s0.fs 0#64 _)
          have htr : sf.trace = s0.trace := hmid_srf.2.1.trans (htr_sr.trans htr_sl)
          have hfds : FdsGe3Closed s0.fs → FdsGe3Closed sf.fs := fun hcl0 =>
            hfs_f ▸ fdsGe3Closed_setFd_lt3 (by decide : (0#64 : BitVec 64).toNat < 3) _ hcl0
          have hst_f :
              M.stepEvents (rustDeallocEvents (cliIoCap 8) 1) st_cur =
                M.stepEvents (readStdinBudgetEvents rem) st := by
            rw [hst_eq, hlen_eq]
            exact stepEvents_overcap_dealloc st hrem_gt'
          dsimp only
          rw [← hrem_def, readStdinResult_eq_err_of_gt hrem_gt', hst_f,
            pure_sepConj_of_true ⟨hfiles, htr, hfds⟩]
          sep_entail
      · -- In-cap (`len + chunk.length ≤ cliIoStdinCap`)
        have hlen'_max : len + chunk.length ≤ cliIoStdinCap := by omega
        have hlen'_le : len + chunk.length ≤ min rem.length cliIoStdinCap :=
          Nat.le_min.mpr ⟨hn_le_rem, hlen'_max⟩
        have hdvd' : len + chunk.length < rem.length → 4096 ∣ (len + chunk.length) :=
          dvd_4096_preserved (K := 8) hlen_le hdvd hn_min hn_pos hlen'_max
        have hm_lt : cliIoStdinCap + 1 - (len + chunk.length) < fuel := by omega
        by_cases hnogrow : len + chunk.length ≤ cap
        · -- No grow (`0 < len`, `cap = cliIoCap j`)
          have hlen_pos : 0 < len := by
            rcases Nat.eq_zero_or_pos len with rfl | hp
            · rw [cliIoFinalCap_zero] at hcap_eq; omega
            · exact hp
          let j := cliIoCapIdx 8 len
          have hj : j ≤ 8 := cliIoCapIdx_le 8 len
          have hcap_j : cap = cliIoCap j := by rw [hcap_eq, cliIoFinalCap_pos hlen_pos]
          have hcap_le_max : cap ≤ 1048576 := by rw [hcap_j]; exact cliIoCap_mono hj
          have hidx_eq : cliIoCapIdx 8 (len + chunk.length) = j :=
            no_grow_capIdx_eq hlen_pos (by omega) (by rwa [← hcap_j])
          have hcap'_eq : cap = cliIoFinalCap 8 (len + chunk.length) := by
            rw [cliIoFinalCap_pos (by omega), hidx_eq, hcap_j]
          have hst_eq_idx : stdinLoopEvents (len + chunk.length) = stdinLoopEvents len := by
            rw [stdinLoopEvents_pos (by omega), stdinLoopEvents_pos hlen_pos, hidx_eq]
          refine cliIoReadStdin_after_read_nogrow_b_reads hext0 hn_pos hn_le_want hwant_le
            hnogrow hcap_le_max hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            hx0_sr hx19_sr hx20_sr hx21_sr hx23_sr hx24_sr hx25_sr hx26_sr hx27_sr hx29_sr hvregs_sr
            fun sc hpc_sc hrun_sc hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc hx24_sc hx25_sc
                hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_srsc hvm_srsc => ?_
          have hpool_srsc : A.pool lim st_cur sr = A.pool lim st_cur sc :=
            (A.pool_transport lim st_cur sr sc hvm_srsc).symm
          refine SepWP.weaken_pre (by rw [hpool_srsc]; sep_entail)
            (cliIoReadStdin_memcpy_backedge_b_reads A lim hext0 hmemcpy
              (by rw [hcap_j]; exact cliIoCap_pos j)
              (by rw [hcap_j]; exact cliIoCap_lt_pow63 (by omega))
              hn_le_rem hnogrow hlen'_max hwant_le hold_len hn_le_want rfl
              hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc hx24_sc
              hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc
              fun sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                  hx26_sn hx27_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                ih (cliIoStdinCap + 1 - (len + chunk.length)) hm_lt sn ptr st0 st1 st2 st3
                  cap (len + chunk.length) st_cur (Nat.le_refl _)
                  hlen'_le hdvd' hcap'_eq
                  (by rw [hst_eq_idx]; exact hst_eq)
                  hcl_sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                  hx26_sn hx27_sn hx29_sn hvregs_sn
                  (hmid_scsn.1.trans (hacp_srsc.1.trans hfs_sr))
                  (hmid_scsn.2.1.trans (hacp_srsc.2.1.trans (htr_sr.trans htr_sl)))
                  (hmid_scsn.2.2.trans (hacp_srsc.2.2.1.trans (hsig_sr.trans hsig_sl))))
        · -- Grow (`cap < len + chunk.length ≤ cliIoStdinCap`)
          have hgt_cap : cap < len + chunk.length := by omega
          refine cliIoReadStdin_after_read_grow_b_reads hext0 hn_pos hn_le_want hwant_le
            hgt_cap hlen'_max hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            hx0_sr hx19_sr hx20_sr hx21_sr hx23_sr hx24_sr hx25_sr hx26_sr hx27_sr hx29_sr hvregs_sr
            fun sg hpc_sg hrun_sg hsp_sg hx0_sg hx19_sg hx20_sg hx21_sg hx24_sg hx25_sg
                hx26_sg hx27_sg hx28_sg hx29_sg hvregs_sg hcl_sg hacp_srsg hvm_srsg => ?_
          have hpool_srsg : A.pool lim st_cur sr = A.pool lim st_cur sg :=
            (A.pool_transport lim st_cur sr sg hvm_srsg).symm
          have hfs_sg : sg.fs = s0.fs.setFd 0#64
              (some { d0 with offset := d0.offset + (len + chunk.length) }) :=
            hacp_srsg.1.trans hfs_sr
          have htr_sg : sg.trace = s0.trace := hacp_srsg.2.1.trans (htr_sr.trans htr_sl)
          have hsig_sg : sg.sigActions = s0.sigActions := hacp_srsg.2.2.1.trans (hsig_sr.trans hsig_sl)
          have hoom_files_of : ∀ sf_oom : State, OomPreserved sg sf_oom → CliIoFilesOomPreserved s0 sf_oom :=
            fun sf_oom hoom_m =>
              ⟨(congrArg FsState.files (hoom_m.1.trans hfs_sg)).trans (setFd_files_eq s0.fs 0#64 _),
                hoom_m.2.1.trans htr_sg, hoom_m.2.2.trans hsig_sg⟩
          rcases Nat.eq_zero_or_pos len with rfl | hlen_pos
          · -- `len = 0`, `cap = 0 → cliIoCap 0 = 4096`
            have hcap0 : cap = 0 := hcap_eq
            subst hcap0
            have hst0 : st_cur = st := by rw [hst_eq, stdinLoopEvents_zero]; rfl
            have hidx0 : cliIoCapIdx 8 chunk.length = 0 :=
              cliIoCapIdx_eq_of_bounds (Nat.zero_le 8) (Or.inl rfl) (Nat.le_trans hn_le_want hwant_le)
            refine SepWP.weaken_pre (by rw [hpool_srsg, hst0]; sep_entail)
              (cliIoReadStdin_grow_from_zero_b_reads A lim hext0 hfg hlo hhi hn_pos
                (Nat.le_trans hn_le_want hwant_le) hcl_sg hpc_sg hrun_sg hsp0 hsp_sg
                hx0_sg hx19_sg hx20_sg hx21_sg hx24_sg hx25_sg hx26_sg hx27_sg
                (by rw [Nat.zero_add] at hx28_sg; exact hx28_sg) hx29_sg hvregs_sg
                (fun hnot sf_oom hoom_m =>
                  Entails.pure_right_only
                    ⟨not_fitsEvents_budget_of_grow_zero (by omega : 0 < rem.length) hnot,
                      hoom_files_of sf_oom hoom_m⟩
                    (Entails.refl _))
                fun sc newPtr st1' st2' hpc_sc hrun_sc hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc
                    hx24_sc hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_sgsc =>
                  cliIoReadStdin_memcpy_backedge_b_reads A lim hext0 hmemcpy
                    (cliIoCap_pos 0) (cliIoCap_lt_pow63 (by decide))
                    hn_le_rem (Nat.le_trans (by rw [Nat.zero_add]; exact hn_le_want) hwant_le)
                    hlen'_max hwant_le hold_len hn_le_want rfl
                    hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc hx24_sc
                    hx25_sc hx26_sc hx27_sc (by rw [Nat.zero_add]; exact hx28_sc) hx29_sc hvregs_sc
                    fun sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                        hx26_sn hx27_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                      ih (cliIoStdinCap + 1 - (0 + chunk.length)) hm_lt sn newPtr 0#64 st1' st2' st3
                        (cliIoCap 0) (0 + chunk.length)
                        (M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) st)
                        (Nat.le_refl _) hlen'_le hdvd'
                        (by simp [cliIoFinalCap_pos hn_pos, hidx0])
                        (by rw [Nat.zero_add]; exact stepEvents_grow_zero st hn_pos hidx0)
                        hcl_sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn
                        hx25_sn hx26_sn hx27_sn hx29_sn hvregs_sn
                        (hmid_scsn.1.trans (hacp_sgsc.1.trans hfs_sg))
                        (hmid_scsn.2.1.trans (hacp_sgsc.2.1.trans htr_sg))
                        (hmid_scsn.2.2.trans (hacp_sgsc.2.2.1.trans hsig_sg)))
          · -- `0 < len`, `cap = cliIoCap j → cliIoCap (j + 1)`
            let j := cliIoCapIdx 8 len
            have hj : j ≤ 8 := cliIoCapIdx_le 8 len
            have hcap_j : cap = cliIoCap j := by rw [hcap_eq, cliIoFinalCap_pos hlen_pos]
            have hlen_le_j : len ≤ cliIoCap j := le_cliIoCap_cliIoCapIdx hlen_max
            have ⟨hj1, hj1_r, hidx_j1, hle_j1, _⟩ :=
              grow_step_bounds (K := 8) (by decide) hj hlen_le_j
                (Nat.le_trans hn_le_want hwant_le) hn_le_rem hlen'_max (by rwa [← hcap_j])
            refine SepWP.weaken_pre (by rw [hpool_srsg, hcap_j]; sep_entail)
              (cliIoReadStdin_grow_from_pos_b_reads A lim hext0 hfg hlo hhi hj1 hlen_le_j
                (List.length_take_of_le hlen_rem) (by rwa [← hcap_j]) hle_j1
                hcl_sg hpc_sg hrun_sg hsp0 hsp_sg
                hx0_sg hx19_sg hx20_sg (by rw [hx21_sg, hcap_j]) hx24_sg hx25_sg
                hx26_sg hx27_sg hx28_sg hx29_sg hvregs_sg
                (fun hnot sf_oom hoom_m =>
                  Entails.pure_right_only
                    ⟨not_fitsEvents_budget_of_grow_pos hlen_pos (by omega : 0 < rem.length) hj rfl
                      hj1_r (hst_eq ▸ hnot),
                      hoom_files_of sf_oom hoom_m⟩
                    (Entails.refl _))
                fun sc newPtr st1' st2' hpc_sc hrun_sc hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc
                    hx24_sc hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_sgsc =>
                  cliIoReadStdin_memcpy_backedge_b_reads A lim hext0 hmemcpy
                    (cliIoCap_pos (j + 1)) (cliIoCap_lt_pow63 (by omega))
                    hn_le_rem hle_j1 hlen'_max hwant_le hold_len hn_le_want rfl
                    hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc hx24_sc
                    hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc
                    fun sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                        hx26_sn hx27_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                      ih (cliIoStdinCap + 1 - (len + chunk.length)) hm_lt sn newPtr 0#64 st1' st2' st3
                        (cliIoCap (j + 1)) (len + chunk.length)
                        (M.stepEvents
                          (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1)))
                          st_cur)
                        (Nat.le_refl _) hlen'_le hdvd'
                        (by rw [cliIoFinalCap_pos (by omega), hidx_j1])
                        (by rw [hst_eq]; exact stepEvents_grow_pos st hlen_pos (by omega) hj rfl hidx_j1)
                        hcl_sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn
                        hx25_sn hx26_sn hx27_sn hx29_sn hvregs_sn
                        (hmid_scsn.1.trans (hacp_sgsc.1.trans hfs_sg))
                        (hmid_scsn.2.1.trans (hacp_sgsc.2.1.trans htr_sg))
                        (hmid_scsn.2.2.trans (hacp_sgsc.2.2.1.trans hsig_sg)))


/-- Placement-generic conditional-OOM proof of `signal_session_io::read_stdin` (`block[0]`)
    over `(M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)` (`0` `StdErrnoCell`,
    `0` `P.svc`, `0` `ExternPreservesOracleSymtab`). -/
private theorem cliIoReadStdin_raw_ok_reads {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stackBytes : Nat}
    (hext0 : CliIoBlockNoExtern mpl P 0)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      allocMemcpyVmSpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (cliIoWithReadsCodeLoaded mpl (cliIoReadStdinRawSpec A lim stackBytes)) := by
  have hfg := cliIoFinishGrow_budget_ok_withReadsCodeLoaded A lim hpl hext4 hshim halloc hrealloc
  letI : CliIoPlacement := ⟨mpl, hpl⟩
  rw [cliIoResolve_eq_base hpl 0 cliIoReadStdinSym cliIo0_lt cliIoReadStdin_lookup]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp0
  dsimp only [cliIoWithReadsCodeLoaded, MultiPlacedLib.withCodeLoadedWhere, cliIoReadStdinRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜CliIoReadsCodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hlo, hhi, hsp_lo, hsp_va, hx8, hstdin⟩, hmem⟩
  obtain ⟨d0, hfds0, hkind, hcanr, hbs_eq⟩ := cliStdin_eq_some hstdin
  refine ⟨_, hmem, ?_⟩
  dsimp only [readStdinBudgetCondSpec]
  rw [hbs_eq]
  wp_conv_pre =>
    rw [cliIoReadStdin_stack_split s0.sp (by omega) hhi,
      memRegion24_eq_exists_vecHeader x.ret,
      memRegion4096_split_probe32 (s0.sp - 4224#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, bv_lin_norm]
  refine SepWP.exists_elim fun v0 => SepWP.exists_elim fun v1 =>
    SepWP.exists_elim fun v2 =>
    SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 =>
    SepWP.exists_elim fun r0 => SepWP.exists_elim fun r1 =>
    SepWP.exists_elim fun r2 => SepWP.exists_elim fun r3 =>
    SepWP.exists_elim fun r4 => SepWP.exists_elim fun r5 =>
    SepWP.exists_elim fun r6 => SepWP.exists_elim fun r7 =>
    SepWP.exists_elim fun r8 => SepWP.exists_elim fun r9 =>
    SepWP.exists_elim fun r10 => SepWP.exists_elim fun r11 =>
    SepWP.exists_elim fun w_probe => ?_
  apply sepWP_seg_cliIo_block_pure_reads 0 cliIo0_lt rfl hext0 cliIoBlockNoSvc0_00 hcl0
    (mid := cliIoPl00.base + 72#64)
  intro s1' hcpu1_0
  have hcpu1 := hcpu1_0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc1' : s1'.pc = cliIoPl00.base := hcpu1.pc_eq.trans hpc
  have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
  have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
  have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
  have hx8_1' : s1'.readReg64 .x8 = x.ret := (hcpu1.readReg64 .x8).trans hx8
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1')
    fun sl hcpu_l0 hcl_l hnsp_l hsym_l => ?_
  have hcpu_l := hcpu_l0.1
  have ⟨hacp_0l, hvm_0l⟩ :=
    vmPreserved_of_seg hcpu1_0 hcpu_l0 hnsp_l hsym_l
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_0l : A.pool lim st s0 = A.pool lim st sl :=
    (A.pool_transport lim st s0 sl hvm_0l).symm
  have hpc_l : sl.pc = cliIoPl00.base + 72#64 := hcpu_l.pc_eq.trans (by simp [arm64_norm])
  have hrun_l : sl.status = .Running := hcpu_l.status_eq.trans hrun1'
  have hsp_l : sl.sp = s0.sp - 4224#64 := hcpu_l.sp_eq.trans (by simp [arm64_norm])
  have hfs_l : sl.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + 0 }) :=
    hacp_0l.1.trans (setFd_offset_add_zero hfds0)
  refine SepWP.weaken_pre ?_
    (cliIoReadStdin_loop_b_reads A lim hext0 hread hmemcpy hfg hdealloc
      (sret := x.ret) (v0 := v0) (v1 := v1) (v2 := v2)
      hlo hhi hsp_lo hsp_va hsp0 hkind hcanr
      (fun sf _hpc_f _hrun_f hsp_f hcs_f hcl_f {_Pre_f} hent =>
        ⟨fun hm_out => by
          change CliIoReadsCodeLoaded mpl sf.mem at hcl_f
          rw [pure_sepConj_of_true hcl_f]
          exact Satisfies.mono (sepConj_mono_left hent) hm_out,
        hsp_f, hcs_f⟩)
      (cliIoStdinCap + 1) sl 1#64 st0 st1 st2 st3 0 0 st
      (Nat.le_refl _) (Nat.zero_le _) (fun _ => Nat.dvd_zero 4096) rfl
      (by rw [stdinLoopEvents_zero]; rfl)
      hcl_l hpc_l hrun_l hsp_l
      (by rw [hcpu_l.readReg64]; simp only [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp only [arm64_norm])
      (hcpu_l.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs))
      hfs_l hacp_0l.2.1 hacp_0l.2.2.1)
  have hrefold_probe :
      memRegion (s0.sp - 4224#64) 32 ∗ ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 4184#64) 4056 ⊢ memRegion (s0.sp - 4224#64) 4096 := by
    simpa only [bv_lin_norm] using memRegion4096_refold_probe32 (s0.sp - 4224#64) 0#64
  have hvec0 : emp ⊢ cliIoVecBuf A.repAlloc (BitVec.ofNat 64 0) 1#64
      ((s0.fs.stdin.drop d0.offset).take 0) :=
    cliIoVecBuf_zero_intro A.repAlloc (ptr := 1#64) (by decide)
  rw [hpool_eq_0l,
    hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
    hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 27#5),
    hcpu1.readReg64 (.gpr 26#5), hcpu1.readReg64 (.gpr 25#5),
    hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
    hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
    hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5)]
  dsimp only [cliIoSavedRegs12]
  simp only [bv_lin_norm]
  let SavedAndRest : SepProp :=
    stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
      vecHeader x.ret v0 v1 v2 ∗ A.pool lim st sl
  have hwith_vec :
      SavedAndRest ⊢ SavedAndRest ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 0) 1#64 ((s0.fs.stdin.drop d0.offset).take 0) := by
    simpa only [sepConj_emp] using sepConj_mono_right (P := SavedAndRest) hvec0
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono hrefold_probe hwith_vec)
      (by dsimp only [SavedAndRest]; sep_entail))
  dsimp only [SavedAndRest]; sep_entail


end

private theorem cliIoReadStdin_budgetCond_ok_extHookStack_withReadsCodeLoaded
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hext0 : CliIoBlockNoExtern mpl P 0)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      allocMemcpyVmSpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hPoolVa : ∀ {st : M.σ} {s : State} {R : SepProp} {a : BitVec 64},
      (s.mem ⊨ A.pool lim st s ∗ R) → (s.mem.perm a).mapped = true →
        a.toNat < Arm64.USER_VA_LIMIT) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl (readStdinBudgetCondSpec A lim extHookStack)) := by
  have hRaw0 := subroutine_ok_of_cliIoWithReadsCodeLoaded
    (cliIoReadStdin_raw_ok_reads A lim hpl hext0 hext4 hread hmemcpy hshim halloc hrealloc hdealloc
      (stackBytes := extHookStack))
  have hlo : 4256 + allocHookStack ≤ extHookStack := by
    unfold extHookStack allocHookStack; decide
  have hhi : extHookStack ≤ 2 ^ 64 := by
    unfold extHookStack; decide
  have hpos_ext : 0 < extHookStack := by
    unfold extHookStack; decide
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  have hpreR : s0.mem ⊨
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl
        (cliIoReadStdinRawSpec A lim extHookStack)).pre (x, st) s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoReadStdinRawSpec]
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, readStdinBudgetCondSpec] at hpre
    rw [sepConj_comm _ ⌜CliIoReadsCodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    refine ⟨hpre.1, ?_⟩
    have hp := hpre.2
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
    have ⟨hsp_lo, hsp_va⟩ : extHookStack ≤ s0.sp.toNat ∧ s0.sp.toNat ≤ Arm64.USER_VA_LIMIT :=
      stackAt_bounds_of_mapped hpos_ext hhi
        (fun _ hmap => hPoolVa
          (R := memRegion x.ret 24 ∗ stackAt s0.sp extHookStack ∗ R)
          (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp.2) hmap)
        (R := memRegion x.ret 24 ∗ A.pool lim st s0 ∗ R)
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp.2)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hlo, hhi, hsp_lo, hsp_va, hp.1.1, hp.1.2⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp.2⟩
  refine subroutine_ok.mono_outcome hRaw0 (x, st) R s0 hpc hrun hpreR hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨ho, hoom⟩)
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoReadStdinRawSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoReadStdinRawSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-- **`signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep` form of `readStdinBudgetCondSpec` (`extHookStack ≤ stk`)**:
    compiled `signal_session_io::read_stdin` (`block[0]`) + `finish_grow` (`block[4]`) satisfies
    `readStdinBudgetCondSpec A lim stk` for any `(M : AllocCostModel) (A : RustCliAllocBudget M)`
    and `stk ≥ extHookStack`. -/
theorem cliIoReadStdin_budgetCond_ok_withReadsCodeLoaded
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hstk : extHookStack ≤ stk)
    (hext0 : CliIoBlockNoExtern mpl P 0)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      allocMemcpyVmSpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hPoolVa : ∀ {st : M.σ} {s : State} {R : SepProp} {a : BitVec 64},
      (s.mem ⊨ A.pool lim st s ∗ R) → (s.mem.perm a).mapped = true →
        a.toNat < Arm64.USER_VA_LIMIT) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl (readStdinBudgetCondSpec A lim stk)) := by
  have hE := cliIoReadStdin_budgetCond_ok_extHookStack_withReadsCodeLoaded
    A lim hpl hext0 hext4 hread hmemcpy hshim halloc hrealloc hdealloc hPoolVa
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, readStdinBudgetCondSpec] at hpre
  rw [sepConj_comm _ ⌜CliIoReadsCodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre0⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx8, hstdin⟩, hmem⟩
  have hmem_disj : s0.mem ⊨ memRegion x.ret 24 ∗
      (stackAt s0.sp stk ∗ (A.pool lim st s0 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hpos_ext : 0 < extHookStack := by unfold extHookStack; decide
  have hstk64 : stk ≤ 2 ^ 64 :=
    stackAt_le_two_pow_64_of_sep (by decide) (Nat.lt_of_lt_of_le hpos_ext hstk) hmem_disj
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ stackAt s0.sp extHookStack := by
    have hs := stackAt_split_bottom s0.sp extHookStack (stk - extHookStack) (by omega)
    rwa [Nat.add_sub_of_le hstk] at hs
  let F : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack)
  have hpreE : s0.mem ⊨
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl
        (readStdinBudgetCondSpec A lim extHookStack)).pre (x, st) s0 ∗ (F ∗ R) := by
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, readStdinBudgetCondSpec, F]
    rw [sepConj_comm _ ⌜CliIoReadsCodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx8, hstdin⟩, ?_⟩
    rw [hsplit] at hmem
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine subroutine_ok.mono_outcome hE (x, st) (F ∗ R) s0 hpc hrun hpreE hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨_, _, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, readStdinBudgetCondSpec, F] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hp, ?_⟩)
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, readStdinBudgetCondSpec, F] at hpan ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan ⊢
    refine ⟨hpan.1, ?_⟩
    have h1 : sf.mem ⊨ (anyHeap ∗ F) ∗ R :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpan.2
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) h1
  · dsimp only [MultiPlacedLib.withCodeLoadedWhere, readStdinBudgetCondSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, readStdinBudgetCondSpec, F] at hoom ⊢
    rw [satisfies_pure_sepConj] at hoom ⊢
    have hoomR : sf.mem ⊨ R ∗ F :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hoom.2
    exact ⟨hoom.1, Satisfies.of_sep_left hoomR⟩

/-- **Main `GHOST-STDIN` Commit 2b theorem (`cliIoReadStdin_budgetCond_ok_of_readsCodeLoaded`)**:
    when `P.CodeLoaded m → CliIoReadsCodeLoaded mpl m` and `extHookStack ≤ stk`,
    compiled `signalSessionIoMultiLib` discharges `readStdinBudgetCondSpec A lim stk`. -/
theorem cliIoReadStdin_budgetCond_ok_of_readsCodeLoaded
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hstk : extHookStack ≤ stk)
    (hCodeLib : ∀ m : Memory, P.CodeLoaded m → CliIoReadsCodeLoaded mpl m)
    (hext0 : CliIoBlockNoExtern mpl P 0)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      allocMemcpyVmSpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hPoolVa : ∀ {st : M.σ} {s : State} {R : SepProp} {a : BitVec 64},
      (s.mem ⊨ A.pool lim st s ∗ R) → (s.mem.perm a).mapped = true →
        a.toNat < Arm64.USER_VA_LIMIT) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (readStdinBudgetCondSpec A lim stk) := by
  have hWith := cliIoReadStdin_budgetCond_ok_extHookStack_withReadsCodeLoaded
    A lim hpl hext0 hext4 hread hmemcpy hshim halloc hrealloc hdealloc hPoolVa
  refine subroutine_ok_readStdinBudgetCondSpec_of_extHookStack hstk ?_
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp hCodeP
  have hpreL : s0.mem ⊨
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl
        (readStdinBudgetCondSpec A lim extHookStack)).pre (x, st) s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoadedWhere]
    rw [sepConj_comm _ ⌜CliIoReadsCodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨hCodeLib s0.mem hCodeP, hpre⟩
  exact subroutine_ok.mono_outcome hWith (x, st) R s0 hpc hrun hpreL hsp fun _ hout => hout


/-- Bundled subroutine + block-purity assumptions for compiled `signalSessionIoMultiLib`
    `read_stdin` (`block[0]`) + `finish_grow` (`block[4]`) on sub-program `P` at `(A, lim, mpl)`. -/
structure CliIoReadStdinReadsSubroutines {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (mpl : MultiPlacement) (P : Program) : Prop where
  placeable  : signalSessionIoMultiLib.Placeable mpl
  codeLoaded : ∀ m : Memory, P.CodeLoaded m → CliIoReadsCodeLoaded mpl m
  noExt0     : CliIoBlockNoExtern mpl P 0
  noExt4     : CliIoBlockNoExtern mpl P 4
  read       : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
                 muslReadStdin32Spec
  memcpy     : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
                 allocMemcpyVmSpec
  shim       : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
                 rustAllocShimVmSpec
  alloc      : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
                 (rustCliAllocBudgetSpecBase M A lim false)
  realloc    : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
                 (rustCliReallocBudgetSpecBase M A lim)
  dealloc    : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
                 (rustCliDeallocBudgetSpecBase M A lim)
  poolVa     : ∀ {st : M.σ} {s : State} {R : SepProp} {a : BitVec 64},
                 (s.mem ⊨ A.pool lim st s ∗ R) → (s.mem.perm a).mapped = true →
                   a.toNat < Arm64.USER_VA_LIMIT

theorem CliIoReadStdinReadsSubroutines.budgetCond_ok {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {mpl : MultiPlacement} {P : Program}
    (hS : CliIoReadStdinReadsSubroutines A lim mpl P) (hstk : extHookStack ≤ stk) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (readStdinBudgetCondSpec A lim stk) :=
  cliIoReadStdin_budgetCond_ok_of_readsCodeLoaded A lim hS.placeable hstk hS.codeLoaded hS.noExt0 hS.noExt4
    hS.read hS.memcpy hS.shim hS.alloc hS.realloc hS.dealloc hS.poolVa

end

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinCliIoInst
