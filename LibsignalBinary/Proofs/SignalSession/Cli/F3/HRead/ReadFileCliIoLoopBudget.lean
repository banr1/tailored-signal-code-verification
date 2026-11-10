/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinSteps
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps
public import LibsignalBinary.Proofs.SignalSession.CliIo.BridgePlaced
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadHookAlign
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FinishGrowBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import ProofLib.ProgramReflection

/-!
# Budget-Threaded `signal_session_io::read_file` `.localFile` Loop and Shared Epilogues

Proves `VmPreserved`-parametric epilogues and the budget-threaded `4096`-byte `.localFile` chunk
loop (`cliIoReadFile_file_loop_budget`) for `signalSessionIoMultiLib` block 3
(`signal_session_io::read_file`), stepping `st0` along `cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 rem.length)`
on `≤ 2 MiB` and `readFileOverCapEvents` on `> 2 MiB`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoLoopBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SignalSession.Cli (ioVecAt)
open VerifiedLibraries.RustStd (SameCpuState vecHeader IoFrame)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FdsHiFrame FitsEvents
  NullAllowed OomPreserved PoolPreserved RustCliAllocBudget VmMemPreserved VmPreserved
  fitsEvents_append rustAllocEvents rustDeallocEvents rustReallocEvents
  rustCliDeallocBudgetSpecBase
)
open LibsignalBinary.Heap.SpecBudget (cliIoCapsEvents cliIoReadScheduleCaps)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  sepWP_seg_cliIo_block_pure
  cliIoCloseSym cliIoReadSym cliIoMemcpySym cliIoFinishGrowSym cliIoRustDeallocSym
  cliIoPl03 cliIoPC03 cliIoBlockNoSvc0_03
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  ioFrame_trans
  cliIoFileCap cliIoCap cliIoCap_zero cliIoCap_succ cliIoCap_mono cliIoCap_strictMono
  cliIoCap_pos cliIoCap_lt_pow63 cliIoCap_lt_pow64 not_nullAllowed_cliIoCap
  cliIoCapIdx cliIoCapIdx_le le_cliIoCap_cliIoCapIdx
  cliIoCapIdx_eq_of_bounds cliIoCapIdx_cap_self
  cliIoReadCaps cliIoFinalCap cliIoFinalCap_zero cliIoFinalCap_pos
  wantBytes wantBytes_pos wantBytes_le_4096 wantBytes_csel_bv
  overCap_forces_eq_max dvd_4096_preserved no_grow_capIdx_eq grow_step_bounds
  bit63_eq_zero_of_lt bv64_ult_ofNat_true bv64_ult_ofNat_false
  bv64_beq_ofNat_false bv64_shiftLeft1_ofNat bv64_sub_ofNat
  cliIoSavedRegs12 cliIoReadFile_stack_refold
  vecHeader_to_err_sret stackBuf4096_repack
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (muslClose48LocalSpec)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin (
  muslReadFileOrStdio32Spec sp_sub_4224_va_bound
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic (setFd_none_setFd_of_fds_none)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinSteps (CliIoMidPreserved)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps (
  cliIo3_lt cliIoReadFile_read_pc cliIoReadFile_memcpy_pc cliIoReadFile_grow_pc
  cliIoReadFile_dealloc_pc cliIoReadFile_close_pc readReg32_of_readReg64_eq
)
open LibsignalBinary.Proofs.SignalSession.CliIo.BridgePlaced (
  CliIoFilesOomPreserved
  cliIoCap_eq cliIoCapIdx_eq cliIoReadScheduleCaps_eq_cliIoReadCaps
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadHookAlign (ioResultErr_eq_ioVecAt_err)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FinishGrowBudget (
  allocCallPreserved_refl allocCallPreserved_trans oomPreserved_of_allocCallPreserved
  vmPreserved_of_seg vmMemPreserved_of_syscallPreserved
  cliIoVecBuf cliIoVecBuf_zero_intro cliIoVecBuf_unpack_pos cliIoVecBuf_repack_chunk
  cliIoVecBuf_entails_dealloc_mem vecHeader_cliIoVecBuf_entails_ioVecAt_ok
  cliIoCapsEvents_range_succ
  cliIoFinishGrowBudgetEvents cliIoFinishGrowBudgetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  readFileOverCapEvents
)

/-! ## State-Preservation and Schedule-Event Helpers -/

theorem vmPreserved_of_stdState {s s' : State} (h : StdStatePreserved s s') :
    VmPreserved s s' :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
    FdsHiFrame.of_fs_eq h.1⟩

theorem cliIoMidPreserved_of_acp {s1 s2 : State} (h : AllocCallPreserved s1 s2) :
    CliIoMidPreserved s1 s2 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem ioFrame_of_acp {s1 s2 : State} (h : AllocCallPreserved s1 s2) : IoFrame s1 s2 :=
  ⟨h.2.1, h.2.2.1⟩

private theorem sepConj_pure_mid (P Q : SepProp) (φ : Prop) :
    P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) := by
  rw [← sepConj_assoc, sepConj_comm P ⌜φ⌝, sepConj_assoc]

private theorem cliIoFile_cap_clamp_bv {j : Nat} (hj : j ≤ 9) :
    (if (BitVec.ofNat 64 (cliIoCap j)).ult 2097152#64 = true
     then BitVec.ofNat 64 (cliIoCap j)
     else 2097152#64) = BitVec.ofNat 64 (cliIoCap j) := by
  have h2097 : (2097152#64 : BitVec 64) = BitVec.ofNat 64 2097152 := rfl
  rw [h2097]
  rcases Nat.lt_or_eq_of_le hj with hlt | rfl
  · have hlt_cap : cliIoCap j < 2097152 := cliIoCap_strictMono hlt
    rw [bv64_ult_ofNat_true hlt_cap (by decide)]
    rfl
  · rfl

theorem cliIoCapIdx_mono_le : ∀ (K : Nat) {a b : Nat}, a ≤ b →
    cliIoCapIdx K a ≤ cliIoCapIdx K b
  | 0, _, _, _ => Nat.le_refl _
  | K + 1, a, b, hab => by
    unfold cliIoCapIdx
    by_cases hb : b ≤ cliIoCap K
    · have ha : a ≤ cliIoCap K := Nat.le_trans hab hb
      simp only [ha, hb, ↓reduceIte]
      exact cliIoCapIdx_mono_le K hab
    · simp only [hb, ↓reduceIte]
      by_cases ha : a ≤ cliIoCap K
      · simp only [ha, ↓reduceIte]
        exact Nat.le_trans (cliIoCapIdx_le K a) (Nat.le_succ K)
      · simp only [ha, ↓reduceIte]
        exact Nat.le_refl _

/-- Deterministic allocator event sequence of the `.localFile` loop on `rem`. -/
def cliIoFileLoopBudgetEvents (rem : List (BitVec 8)) : List AllocEvent :=
  if rem.length ≤ cliIoFileCap then
    cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 rem.length)
  else
    readFileOverCapEvents

/-- Deterministic `Result<Vec<u8>, ()>` output of the `.localFile` loop on `rem`. -/
def cliIoFileLoopBudgetOut (rem : List (BitVec 8)) : Except Unit (List (BitVec 8)) :=
  if rem.length ≤ cliIoFileCap then .ok rem else .error ()


theorem cliIoCapsEvents_range_succ' (j : Nat) :
    cliIoCapsEvents 0 ((List.range (j + 2)).map cliIoCap) =
      cliIoCapsEvents 0 ((List.range (j + 1)).map cliIoCap) ++
        rustReallocEvents (cliIoCap j) (cliIoCap (j + 1)) 1 := by
  change cliIoCapsEvents 0 ((List.range (j + 2)).map LibsignalBinary.Heap.SpecBudget.cliIoCap) = _
  exact cliIoCapsEvents_range_succ j

theorem cliIoCapsEvents_range_prefix {k : Nat} : ∀ {K : Nat}, k ≤ K →
    ∃ tail : List AllocEvent,
      cliIoCapsEvents 0 ((List.range (K + 1)).map cliIoCap) =
        cliIoCapsEvents 0 ((List.range (k + 1)).map cliIoCap) ++ tail := by
  intro K hk
  obtain ⟨d, rfl⟩ : ∃ d, K = k + d := ⟨K - k, (Nat.add_sub_of_le hk).symm⟩
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    rcases ih (Nat.le_add_right k d) with ⟨tail, htail⟩
    refine ⟨tail ++ rustReallocEvents (cliIoCap (k + d)) (cliIoCap (k + d + 1)) 1, ?_⟩
    rw [show k + (d + 1) + 1 = (k + d) + 2 by omega, cliIoCapsEvents_range_succ' (k + d),
      htail, List.append_assoc]

theorem cliIoFileLoopBudgetEvents_prefix_of_idx {rem : List (BitVec 8)} {k : Nat}
    (hrem_pos : 0 < rem.length) (hk9 : k ≤ 9)
    (hk_in : rem.length ≤ cliIoFileCap → k ≤ cliIoCapIdx 9 rem.length) :
    ∃ tail : List AllocEvent,
      cliIoFileLoopBudgetEvents rem =
        cliIoCapsEvents 0 ((List.range (k + 1)).map cliIoCap) ++ tail := by
  unfold cliIoFileLoopBudgetEvents
  by_cases hle : rem.length ≤ cliIoFileCap
  · simp only [hle, ↓reduceIte, cliIoReadScheduleCaps_eq_cliIoReadCaps]
    have hne : rem.length ≠ 0 := by omega
    unfold cliIoReadCaps
    simp only [hne, ↓reduceIte]
    exact cliIoCapsEvents_range_prefix (hk_in hle)
  · simp only [hle, ↓reduceIte]
    unfold readFileOverCapEvents
    rw [cliIoReadScheduleCaps_eq_cliIoReadCaps]
    have hcaps9 : cliIoReadCaps 9 2097152 = (List.range (9 + 1)).map cliIoCap := rfl
    rw [hcaps9]
    rcases cliIoCapsEvents_range_prefix hk9 with ⟨tail, htail⟩
    exact ⟨tail ++ rustDeallocEvents 2097152 1, by rw [htail, List.append_assoc]⟩

theorem not_fitsEvents_loop_of_grow_zero {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {rem : List (BitVec 8)} (hrem_pos : 0 < rem.length)
    (hnf : ¬ FitsEvents M lim st0 (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0))) :
    ¬ FitsEvents M lim st0 (cliIoFileLoopBudgetEvents rem) := by
  rcases cliIoFileLoopBudgetEvents_prefix_of_idx hrem_pos (Nat.zero_le 9)
    (fun _ => Nat.zero_le _) with ⟨tail, htail⟩
  have hfg0 : cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0) =
      cliIoCapsEvents 0 ((List.range 1).map cliIoCap) := rfl
  intro hfit
  rw [htail] at hfit
  exact hnf (hfg0 ▸ ((fitsEvents_append M lim _ tail st0).mp hfit).1)

theorem not_fitsEvents_loop_of_grow_pos {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {rem : List (BitVec 8)} {len n j : Nat}
    (hlen_pos : 0 < len) (hj_eq : j = cliIoCapIdx 9 len) (hj1 : j + 1 ≤ 9)
    (hn_le_rem : len + n ≤ rem.length)
    (hidx_j1 : cliIoCapIdx 9 (len + n) = j + 1)
    (hnf : ¬ FitsEvents M lim
      (M.stepEvents (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 len)) st0)
      (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1)))) :
    ¬ FitsEvents M lim st0 (cliIoFileLoopBudgetEvents rem) := by
  have hrem_pos : 0 < rem.length := by omega
  have hj1_in : rem.length ≤ cliIoFileCap → j + 1 ≤ cliIoCapIdx 9 rem.length := by
    intro _
    rw [← hidx_j1]
    exact cliIoCapIdx_mono_le 9 hn_le_rem
  rcases cliIoFileLoopBudgetEvents_prefix_of_idx hrem_pos hj1 hj1_in with ⟨tail, htail⟩
  have hj9 : j ≤ 9 := by omega
  have hcap_pos : 0 < cliIoCap j := cliIoCap_pos j
  have hcap_lt64 : cliIoCap j < 2 ^ 64 := cliIoCap_lt_pow64 hj9
  have hcap_ne0 : BitVec.ofNat 64 (cliIoCap j) ≠ 0#64 := by
    have hbeq : (BitVec.ofNat 64 (cliIoCap j) == 0#64) = false :=
      bv64_beq_ofNat_false (by omega) hcap_lt64 (by decide)
    exact beq_eq_false_iff_ne.mp hbeq
  have hcap_toNat : (BitVec.ofNat 64 (cliIoCap j)).toNat = cliIoCap j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64]
  have hfg_eq :
      cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1)) =
        rustReallocEvents (cliIoCap j) (cliIoCap (j + 1)) 1 := by
    unfold cliIoFinishGrowBudgetEvents
    simp [hcap_ne0, hcap_toNat]
  have hsched_len :
      cliIoReadScheduleCaps 9 len = (List.range (j + 1)).map cliIoCap := by
    rw [cliIoReadScheduleCaps_eq_cliIoReadCaps]
    unfold cliIoReadCaps
    have hne : len ≠ 0 := by omega
    simp [hne, ← hj_eq]
  intro hfit
  rw [htail, show j + 1 + 1 = j + 2 by omega, cliIoCapsEvents_range_succ' j,
    ← hsched_len, ← hfg_eq] at hfit
  have hfit12 := ((fitsEvents_append M lim _ tail st0).mp hfit).1
  exact hnf ((fitsEvents_append M lim _ _ st0).mp hfit12).2

theorem stepEvents_dealloc_overCap (M : AllocCostModel) (st0 : M.σ) {len : Nat}
    (hlen : len = 2097152) :
    M.stepEvents (rustDeallocEvents (cliIoCap 9) 1)
      (M.stepEvents (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 len)) st0) =
      M.stepEvents readFileOverCapEvents st0 := by
  subst hlen
  unfold readFileOverCapEvents
  rw [M.stepEvents_append]
  rfl

/-! ## Shared `VmPreserved`-Parametric Epilogues (`+0x1d4`, `+0x1f4`, `+0x208`) -/

section
arm64_proof_prelude

/-- Stack-restore + `ret` epilogue of `read_file` (`+0x208 = 520#64 .. +0x228 = 552#64`)
    parametric in any `VmPreserved`-invariant pool assertion `P_pool`. -/
theorem cliIoReadFile_ret_epilogue_vm [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    {P_pool : State → SepProp}
    (hP_vm : ∀ {s s' : State}, VmMemPreserved s s' → P_pool s' = P_pool s)
    {s0 se : State} {st0 st1 st2 st3 : BitVec 64}
    {R_out : SepProp} {stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 520#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      AllocCallPreserved se sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ R_out ∗ P_pool sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        R_out ∗
        P_pool se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 520#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 8320#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  wp_conv_pre => dsimp only [cliIoSavedRegs12]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
  have hcpu_f := hcpu_f0.1
  have ⟨hacp_ef, hvm_ef⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f hsym_f
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : P_pool se = P_pool sf := (hP_vm hvm_ef.toVmMemPreserved).symm
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
  have hstk_back := cliIoReadFile_stack_refold s0 hlo hhi st0 st1 st2 st3
  dsimp only [cliIoSavedRegs12] at hstk_back
  rw [hpool_eq]
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_left (Q := R_out ∗ P_pool sf) hstk_back) (by sep_entail))
  sep_entail

/-- Unconditional `close(w19)` + stack-restore + `ret` epilogue (`+0x1f4 = 500#64 .. +0x228 = 552#64`)
    parametric in any `VmPreserved`-invariant pool assertion `P_pool`. -/
theorem cliIoReadFile_close_epilogue_vm [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {P_pool : State → SepProp}
    (hP_vm : ∀ {s s' : State}, VmMemPreserved s s' → P_pool s' = P_pool s)
    {s0 se : State} {fd : BitVec 64} {desc : FdEntry} {st0 st1 st2 st3 : BitVec 64}
    {R_out : SepProp} {stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : se.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 500#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hw19 : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = se.fs.setFd fd none →
      sf.trace = se.trace → sf.sigActions = se.sigActions →
      sf.tpidrEl0 = se.tpidrEl0 → sf.brkStart = se.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ R_out ∗ P_pool sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        R_out ∗
        P_pool se)
      post oomProp := by
  have h48_le : 48 ≤ stackBytes - 8320 := by omega
  have hsb_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 48 h48_le hsb_hi]
    simp only [sepConj_assoc]
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 500#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  wp_sym_steps
  refine SepWP.done cliIoReadFile_close_pc (by simpa [arm64_norm] using hrun_e')
    fun sm_cl hcpu_cl0 hcl_cl hnsp_cl hsym_cl => ?_
  have hcpu_cl := hcpu_cl0.1
  have ⟨hacp_ecl, hvm_ecl⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_cl0 hnsp_cl hsym_cl
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ecl : P_pool se = P_pool sm_cl := (hP_vm hvm_ecl.toVmMemPreserved).symm
  have hpc_cl : sm_cl.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym :=
    hcpu_cl.pc_eq.trans cliIoReadFile_close_pc
  have hrun_cl : sm_cl.status = .Running := hcpu_cl.status_eq.trans hrun_e'
  have hsp_cl_eq : sm_cl.sp = s0.sp - 8320#64 :=
    hcpu_cl.sp_eq.trans ((by simp [arm64_norm] : _ = se'.sp).trans (hcpu_e.sp_eq.trans hsp_eq))
  have hsp_cl : sm_cl.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_cl_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_cl : sm_cl.readReg64 .lr = cliIoPl03.base + 508#64 := by
    rw [hcpu_cl.readReg64 .lr]; simp [arm64_norm]
  have hx0_cl : (sm_cl.readReg32 .x0).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_cl.readReg64 .x0)]
    simp only [arm64_norm]
    rw [hcpu_e.readReg64 (.gpr 19#5)]
    exact hw19
  have hfds_cl : sm_cl.fs.fds fd = some desc := by rw [hacp_ecl.1]; exact hfds
  let T_cl : SepProp :=
    memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 48) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗
      memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗
      R_out ∗
      P_pool sm_cl
  apply seqCodeLoaded hcl_cl (mid := cliIoPl03.base + 508#64)
  apply (SepWP.call_subroutine_frame hclose (F := T_cl) (x := (fd, desc))
    hpc_cl hrun_cl hsp_cl hlr_cl
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslClose48LocalSpec, T_cl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_cl, hfd_lt, hfds_cl, hkind⟩, ?_⟩
    rw [hpool_eq_ecl] at hm'
    rw [hsp_cl_eq]
    exact Satisfies.mono (by sep_frame) hm'
  · intro sm_cl' hpc_cl' hrun_cl' hsp_cl' hcs_cl'
    refine SepWP.done hpc_cl' hrun_cl' fun hcl_cl' => ?_
    wp_conv_pre => dsimp only [muslClose48LocalSpec, T_cl]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hfs_cl', htr_cl', hsys_cl'⟩
    have hpool_eq_cl' : P_pool sm_cl = P_pool sm_cl' :=
      (hP_vm (vmMemPreserved_of_syscallPreserved hsys_cl')).symm
    have hsp_cl'_eq : sm_cl'.sp = s0.sp - 8320#64 := hsp_cl'.trans hsp_cl_eq
    have hvregs_cl' : calleeSavedVRegs sm_cl' = calleeSavedVRegs s0 :=
      hcs_cl'.vregs.trans (hcpu_cl.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs)))
    apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_cl'
      (mid := cliIoPl03.base + 520#64)
    intro sb' hcpu_b0
    have hcpu_b := hcpu_b0.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc_b' : sb'.pc = cliIoPl03.base + 508#64 := hcpu_b.pc_eq.trans hpc_cl'
    have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_cl'
    have hsp_b' : sb'.spAligned = true := by
      rw [hcpu_b.spAligned]; simp only [State.spAligned]; rw [hsp_cl'_eq]
      exact s0.spAligned_sub 8320#64 hsp0
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
      fun sr_ret hcpu_r0 hcl_r hnsp_r hsym_r => ?_
    have hcpu_r := hcpu_r0.1
    have ⟨hacp_br, hvm_br⟩ :=
      vmPreserved_of_seg hcpu_b0 hcpu_r0 hnsp_r hsym_r
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_br : P_pool sm_cl' = P_pool sr_ret := (hP_vm hvm_br.toVmMemPreserved).symm
    have hsp_r : sr_ret.sp = s0.sp - 8320#64 :=
      hcpu_r.sp_eq.trans ((by simp [arm64_norm] : _ = sb'.sp).trans (hcpu_b.sp_eq.trans hsp_cl'_eq))
    have hvregs_r : calleeSavedVRegs sr_ret = calleeSavedVRegs s0 :=
      hcpu_r.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
        (hcpu_b.calleeSavedVRegs.trans hvregs_cl'))
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_ret_epilogue_vm hext3 hP_vm (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
        (R_out := R_out)
        (by omega) hhi hcl_r (hcpu_r.pc_eq.trans (by simp [arm64_norm]))
        (hcpu_r.status_eq.trans hrun_b') hsp0 hsp_r hvregs_r
        fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_rf _ hent =>
          hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
            (hacp_rf.1.trans (hacp_br.1.trans (hfs_cl'.trans (congrArg (fun f => f.setFd fd none) hacp_ecl.1))))
            (hacp_rf.2.1.trans (hacp_br.2.1.trans (htr_cl'.trans hacp_ecl.2.1)))
            (hacp_rf.2.2.1.trans (hacp_br.2.2.1.trans (hsys_cl'.2.1.trans hacp_ecl.2.2.1)))
            (hacp_rf.2.2.2.1.trans (hacp_br.2.2.2.1.trans (hsys_cl'.1.trans hacp_ecl.2.2.2.1)))
            (hacp_rf.2.2.2.2.1.trans (hacp_br.2.2.2.2.1.trans (hsys_cl'.2.2.brkStart_eq.trans hacp_ecl.2.2.2.2.1)))
            hent)
    rw [hpool_eq_cl', hpool_eq_br, hsp_cl_eq,
      stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 48 h48_le hsb_hi]
    sep_entail

/-- `Err(())` epilogue when `cap = 0` (`+0x1d4 = 468#64 → +0x1f4 = 500#64 → ret`),
    parametric in `P_pool` and arbitrary frame `R_extra` (`cbz x22, 0x1f4` skips `__rust_dealloc`). -/
theorem cliIoReadFile_err_cap0_epilogue_vm [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {P_pool : State → SepProp}
    (hP_vm : ∀ {s s' : State}, VmMemPreserved s s' → P_pool s' = P_pool s)
    {s0 se : State} {fd sret v0 v1 v2 st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {R_extra : SepProp} {stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : se.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 468#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hw19 : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx21 : se.readReg64 (.gpr 21#5) = 0#64)
    (hx24 : se.readReg64 (.gpr 24#5) = sret)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = se.fs.setFd fd none →
      sf.trace = se.trace → sf.sigActions = se.sigActions →
      sf.tpidrEl0 = se.tpidrEl0 → sf.brkStart = se.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          (((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗ R_extra) ∗
          P_pool sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        R_extra ∗
        P_pool se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 500#64)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 468#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx21_e' : se'.readReg64 (.gpr 21#5) = 0#64 := (hcpu_e.readReg64 _).trans hx21
  have hx24_e' : se'.readReg64 (.gpr 24#5) = sret := (hcpu_e.readReg64 _).trans hx24
  wp_conv_pre =>
    rw [show vecHeader sret v0 v1 v2 =
      (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sc_cl hcpu_c0 hcl_c hnsp_c hsym_c => ?_
  have hcpu_c := hcpu_c0.1
  have ⟨hacp_ec, hvm_ec⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_c0 hnsp_c hsym_c
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ec : P_pool se = P_pool sc_cl := (hP_vm hvm_ec.toVmMemPreserved).symm
  have hw19_c : (sc_cl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_c.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_e.readReg64 (.gpr 19#5)]
    exact hw19
  have herr_sret := vecHeader_to_err_sret sret v1 v2
  dsimp only [vecHeader] at herr_sret
  refine SepWP.weaken_pre ?_
    (cliIoReadFile_close_epilogue_vm hext3 hclose hP_vm
      (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
      (R_out := ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗ R_extra)
      hlo hhi hfd_lt (by rw [hacp_ec.1]; exact hfds) hkind hcl_c
      (hcpu_c.pc_eq.trans (by simp [arm64_norm])) (hcpu_c.status_eq.trans hrun_e') hsp0
      (hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = se'.sp).trans (hcpu_e.sp_eq.trans hsp_eq)))
      hw19_c
      (hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
        (hcpu_e.calleeSavedVRegs.trans hvregs)))
      fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
        hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
          (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_ec.1))
          (htr_f.trans hacp_ec.2.1) (hsig_f.trans hacp_ec.2.2.1)
          (htp_f.trans hacp_ec.2.2.2.1) (hbs_f.trans hacp_ec.2.2.2.2.1) hent)
  rw [hpool_eq_ec]
  let Rest : SepProp :=
    stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 8320#64) 4096 ∗
      memRegion (s0.sp - 4224#64) 4096 ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗ R_extra ∗ P_pool sc_cl
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_left (Q := Rest) herr_sret) (by dsimp only [Rest]; sep_entail))
  dsimp only [Rest]; sep_entail

/-! ## Budget-Threaded `.localFile` Epilogues and Growth Steps -/

/-- `Ok(bs)` epilogue (`+0x1c8 = 456#64 → +0x1f4 = 500#64 → ret`) over `A.pool lim st_cur`. -/
theorem cliIoReadFile_ok_epilogue_budget [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hA_mem : ∀ st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 se : State} {fd sret v0 v1 v2 cap ptr st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {bs : List (BitVec 8)} {stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : se.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 456#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hw19 : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : se.readReg64 (.gpr 20#5) = ptr)
    (hx21 : se.readReg64 (.gpr 21#5) = cap)
    (hx24 : se.readReg64 (.gpr 24#5) = sret)
    (hx28 : se.readReg64 (.gpr 28#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = se.fs.setFd fd none →
      sf.trace = se.trace → sf.sigActions = se.sigActions →
      sf.tpidrEl0 = se.tpidrEl0 → sf.brkStart = se.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.ok bs) ∗
          A.pool lim st_cur sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc cap ptr bs ∗
        A.pool lim st_cur se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 500#64)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 456#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx20_e' : se'.readReg64 (.gpr 20#5) = ptr := (hcpu_e.readReg64 _).trans hx20
  have hx21_e' : se'.readReg64 (.gpr 21#5) = cap := (hcpu_e.readReg64 _).trans hx21
  have hx24_e' : se'.readReg64 (.gpr 24#5) = sret := (hcpu_e.readReg64 _).trans hx24
  have hx28_e' : se'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 bs.length :=
    (hcpu_e.readReg64 _).trans hx28
  wp_conv_pre =>
    rw [show vecHeader sret v0 v1 v2 =
      (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sc_cl hcpu_c0 hcl_c hnsp_c hsym_c => ?_
  have hcpu_c := hcpu_c0.1
  have ⟨hacp_ec, hvm_ec⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_c0 hnsp_c hsym_c
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ec : A.pool lim st_cur se = A.pool lim st_cur sc_cl :=
    (A.pool_transport lim st_cur se sc_cl hvm_ec).symm
  have hw19_c : (sc_cl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_c.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_e.readReg64 (.gpr 19#5)]
    exact hw19
  have hvec_ok := vecHeader_cliIoVecBuf_entails_ioVecAt_ok A.repAlloc sret cap ptr bs
  dsimp only [vecHeader] at hvec_ok
  refine SepWP.weaken_pre ?_
    (cliIoReadFile_close_epilogue_vm hext3 hclose
      (P_pool := A.pool lim st_cur) (fun h => hA_mem st_cur h)
      (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
      (R_out := ioVecAt A.repAlloc sret (.ok bs))
      hlo hhi hfd_lt (by rw [hacp_ec.1]; exact hfds) hkind hcl_c
      (hcpu_c.pc_eq.trans (by simp [arm64_norm])) (hcpu_c.status_eq.trans hrun_e') hsp0
      (hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = se'.sp).trans (hcpu_e.sp_eq.trans hsp_eq)))
      hw19_c
      (hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
        (hcpu_e.calleeSavedVRegs.trans hvregs)))
      fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
        hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
          (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_ec.1))
          (htr_f.trans hacp_ec.2.1) (hsig_f.trans hacp_ec.2.2.1)
          (htp_f.trans hacp_ec.2.2.2.1) (hbs_f.trans hacp_ec.2.2.2.2.1) hent)
  rw [hpool_eq_ec]
  let Rest : SepProp :=
    stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 8320#64) 4096 ∗
      memRegion (s0.sp - 4224#64) 4096 ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗ A.pool lim st_cur sc_cl
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_left (Q := Rest) hvec_ok) (by dsimp only [Rest]; sep_entail))
  dsimp only [Rest]; sep_entail

/-- Over-cap `Err(())` epilogue (`+0x1d4 = 468#64 → bl __rust_dealloc → close → ret`),
    stepping `st_in` by `rustDeallocEvents cap 1` before `close(w19)`. -/
theorem cliIoReadFile_err_dealloc_epilogue_budget [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hA_mem : ∀ st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 se : State} {fd sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {bs : List (BitVec 8)} {cap stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcap_pos : 0 < cap) (hcap_lt63 : cap < 2 ^ 63)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : se.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 468#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hw19 : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : se.readReg64 (.gpr 20#5) = ptr)
    (hx21 : se.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx24 : se.readReg64 (.gpr 24#5) = sret)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = se.fs.setFd fd none →
      sf.trace = se.trace → sf.sigActions = se.sigActions →
      sf.tpidrEl0 = se.tpidrEl0 → sf.brkStart = se.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.error ()) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents cap 1) st_in) sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr bs ∗
        A.pool lim st_in se)
      post oomProp := by
  have hlo8368 : 8368 ≤ stackBytes := by dsimp [allocHookStack] at hlo; omega
  have hhk_le : allocHookStack ≤ stackBytes - 8320 := by omega
  have hsb_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
  have hcap_lt64 : cap < 2 ^ 64 := Nat.lt_trans hcap_lt63 (by decide)
  have hcap_beq0 : (BitVec.ofNat 64 cap == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) hcap_lt64 (by decide)
  have hcap_toNat : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64]
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) allocHookStack hhk_le hsb_hi]
    simp only [sepConj_assoc]
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 468#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx20_e' : se'.readReg64 (.gpr 20#5) = ptr := (hcpu_e.readReg64 _).trans hx20
  have hx21_e' : se'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_e.readReg64 _).trans hx21
  have hx24_e' : se'.readReg64 (.gpr 24#5) = sret := (hcpu_e.readReg64 _).trans hx24
  wp_conv_pre =>
    rw [show vecHeader sret v0 v1 v2 =
      (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done cliIoReadFile_dealloc_pc (by simpa [arm64_norm] using hrun_e')
    fun sm_dl hcpu_dl0 hcl_dl hnsp_dl hsym_dl => ?_
  have hcpu_dl := hcpu_dl0.1
  have ⟨hacp_edl, hvm_edl⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_dl0 hnsp_dl hsym_dl
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_edl : A.pool lim st_in se = A.pool lim st_in sm_dl :=
    (A.pool_transport lim st_in se sm_dl hvm_edl).symm
  have hpc_dl : sm_dl.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym :=
    hcpu_dl.pc_eq.trans cliIoReadFile_dealloc_pc
  have hrun_dl : sm_dl.status = .Running := hcpu_dl.status_eq.trans hrun_e'
  have hsp_dl_eq : sm_dl.sp = s0.sp - 8320#64 :=
    hcpu_dl.sp_eq.trans ((by simp [arm64_norm] : _ = se'.sp).trans (hcpu_e.sp_eq.trans hsp_eq))
  have hsp_dl : sm_dl.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_dl_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_dl : sm_dl.readReg64 .lr = cliIoPl03.base + 500#64 := by
    rw [hcpu_dl.readReg64 .lr]; simp [arm64_norm]
  have hx0_dl : sm_dl.readReg64 .x0 = ptr :=
    (hcpu_dl.readReg64 .x0).trans (by simp [arm64_norm])
  have hx1_dl : (sm_dl.readReg64 .x1).toNat = cap := by
    rw [hcpu_dl.readReg64 .x1]; simpa [arm64_norm] using hcap_toNat
  have hx2_dl : (sm_dl.readReg64 .x2).toNat = 1 := by
    rw [hcpu_dl.readReg64 .x2]; simp [arm64_norm]
  have herr_sret :
      ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2)) ⊢
        ioVecAt A.repAlloc sret (.error ()) :=
    vecHeader_to_err_sret sret v1 v2
  have hde_mem :
      cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr bs ⊢ A.live ptr cap 1 ∗ memRegion ptr cap :=
    cliIoVecBuf_entails_dealloc_mem A.repAlloc (ptr := ptr) (bs := bs) hcap_pos hcap_lt63
  let T_dl : SepProp :=
    memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320))
        (stackBytes - 8320 - allocHookStack) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗
      memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗
      ioVecAt A.repAlloc sret (.error ())
  apply seqCodeLoaded hcl_dl (mid := cliIoPl03.base + 500#64)
  apply (SepWP.call_subroutine_frame (F := T_dl) hdealloc
    (x := (ptr, cap, 1, st_in))
    hpc_dl hrun_dl hsp_dl hlr_dl
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [rustCliDeallocBudgetSpecBase, T_dl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_dl, hx1_dl, hx2_dl⟩, ?_⟩
    refine Satisfies.mono ?_ hm'
    rw [hpool_eq_edl, hsp_dl_eq]
    let Rest : SepProp :=
      memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320))
          (stackBytes - 8320 - allocHookStack) ∗
        stackAt (s0.sp - 8320#64) allocHookStack ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        A.pool lim st_in sm_dl ∗ R'
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := Rest) (sepConj_mono herr_sret hde_mem))
        (by dsimp only [Rest]; sep_entail))
    dsimp only [Rest]; sep_entail
  · intro sm_dl' hpc_dl' hrun_dl' hsp_dl' hcs_dl'
    refine SepWP.done hpc_dl' hrun_dl' fun hcl_dl' => ?_
    wp_conv_pre => dsimp only [rustCliDeallocBudgetSpecBase, T_dl]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hacp_dl', _⟩
    have hsp_dl'_eq : sm_dl'.sp = s0.sp - 8320#64 := hsp_dl'.trans hsp_dl_eq
    have hw19_dl' : (sm_dl'.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
      rw [readReg32_of_readReg64_eq hcs_dl'.readReg64_x19,
        readReg32_of_readReg64_eq (hcpu_dl.readReg64 (.gpr 19#5))]
      simp only [arm64_norm]
      rw [hcpu_e.readReg64 (.gpr 19#5)]
      exact hw19
    have hvregs_dl' : calleeSavedVRegs sm_dl' = calleeSavedVRegs s0 :=
      hcs_dl'.vregs.trans (hcpu_dl.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs)))
    have hacp_edl' : AllocCallPreserved se sm_dl' := allocCallPreserved_trans hacp_edl hacp_dl'
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_close_epilogue_vm hext3 hclose
        (P_pool := A.pool lim (M.stepEvents (rustDeallocEvents cap 1) st_in))
        (fun h => hA_mem _ h)
        (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
        (R_out := ioVecAt A.repAlloc sret (.error ()))
        hlo8368 hhi hfd_lt (by rw [hacp_edl'.1]; exact hfds) hkind hcl_dl'
        hpc_dl' hrun_dl' hsp0 hsp_dl'_eq hw19_dl' hvregs_dl'
        fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
          hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
            (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_edl'.1))
            (htr_f.trans hacp_edl'.2.1) (hsig_f.trans hacp_edl'.2.2.1)
            (htp_f.trans hacp_edl'.2.2.2.1) (hbs_f.trans hacp_edl'.2.2.2.2.1) hent)
    rw [hsp_dl_eq,
      stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) allocHookStack hhk_le hsb_hi]
    sep_entail

/-- Shared `finish_grow` call + `+0x1b4 .. +0x1c4 → +0x15c = 348#64` join over `A.pool lim st_in`. -/
theorem cliIoReadFile_post_grow_budget [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    {s0 sm_fg : State} {fd sret v0 v1 v2 oldCap oldPtr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {R_buf : SepProp}
    {newCap len n stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8352 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hnew_pos : 0 < newCap) (hnew_lt63 : newCap < 2 ^ 63)
    (hbs_le : bs.length ≤ newCap) (hno_null : ¬ NullAllowed newCap 1)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sm_fg.mem)
    (hpc : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
    (hrun : sm_fg.status = .Running) (hsp0 : s0.spAligned = true)
    (hsp_eq : sm_fg.sp = s0.sp - 8320#64) (hlr : sm_fg.readReg64 .lr = cliIoPl03.base + 436#64)
    (hx0 : sm_fg.readReg64 .x0 = s0.sp - 128#64)
    (hx1 : sm_fg.readReg64 .x1 = oldCap) (hx2 : sm_fg.readReg64 .x2 = oldPtr)
    (hx3 : sm_fg.readReg64 .x3 = BitVec.ofNat 64 newCap)
    (hw19 : (sm_fg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx22 : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap)
    (hx23 : sm_fg.readReg64 .x23 = BitVec.ofNat 64 n)
    (hx24 : sm_fg.readReg64 (.gpr 24#5) = sret)
    (hx25 : sm_fg.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sm_fg.readReg64 (.gpr 26#5) = 2097152#64)
    (hx27 : sm_fg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n))
    (hx28 : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sm_fg = calleeSavedVRegs s0)
    (hoom_fg : ∀ sf_oom : State,
      ¬ FitsEvents M lim st_in (cliIoFinishGrowBudgetEvents oldCap newCap) →
      OomPreserved sm_fg sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl03.base + 348#64 → sc.status = .Running → sc.sp = s0.sp - 8320#64 →
      (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = sret →
      sc.readReg64 (.gpr 25#5) = 4096#64 → sc.readReg64 (.gpr 26#5) = 2097152#64 →
      sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem → AllocCallPreserved sm_fg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 newCap) newPtr bs ∗
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st_in) sc)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sm_fg
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ cliIoVecBuf A.repAlloc oldCap oldPtr bs ∗
        A.pool lim st_in sm_fg)
      post oomProp := by
  have hnew_lt64 : newCap < 2 ^ 64 := Nat.lt_trans hnew_lt63 (by decide)
  have hsp_fg : sm_fg.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hfg_stk_le : 32 + allocHookStack ≤ stackBytes - 8320 := by
    dsimp [allocHookStack] at *; omega
  have hfg_stk_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) (32 + allocHookStack)
      hfg_stk_le hfg_stk_hi]
  apply seqCodeLoaded hcl (mid := cliIoPl03.base + 436#64)
  apply (SepWP.call_subroutine_frame hfg
    (x := (s0.sp - 128#64, st0, st1, st2, oldCap, oldPtr, bs, newCap, st_in))
    hpc hrun hsp_fg hlr
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun R_oom sf_oom _ hm_oom => by
      have hm' := Satisfies.drop_mid hm_oom
      dsimp only [MultiPlacedLib.withCodeLoaded, cliIoFinishGrowBudgetSpec] at hm'
      rcases (satisfies_pure_sepConj _ _ _).mp hm' with ⟨⟨_, hnf, hoom_s⟩, hm_r⟩
      have hent := hoom_fg sf_oom hnf hoom_s
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
      have hsp_fg'_eq : sm_fg'.sp = s0.sp - 8320#64 := hsp_fg'.trans hsp_eq
      have hx29_fg' : sm_fg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 :=
        hcs_fg'.readReg64_x29.trans hx29
      apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_fg'
        (mid := cliIoPl03.base + 348#64)
      intro sj' hcpu_j0
      have hcpu_j := hcpu_j0.1
      change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
      have hpc_j' : sj'.pc = cliIoPl03.base + 436#64 := hcpu_j.pc_eq.trans hpc_fg'
      have hrun_j' : sj'.status = .Running := hcpu_j.status_eq.trans hrun_fg'
      have hsp_j' : sj'.spAligned = true := by
        rw [hcpu_j.spAligned]; simp only [State.spAligned]; rw [hsp_fg'_eq]
        exact s0.spAligned_sub 8320#64 hsp0
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
      have hpc_c : sc.pc = cliIoPl03.base + 348#64 := hcpu_c.pc_eq.trans (by simp [arm64_norm])
      have hrun_c : sc.status = .Running := hcpu_c.status_eq.trans hrun_j'
      have hsp_c : sc.sp = s0.sp - 8320#64 :=
        hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = sj'.sp).trans (hcpu_j.sp_eq.trans hsp_fg'_eq))
      have hw19_c : (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
        rw [readReg32_of_readReg64_eq (hcpu_c.readReg64 (.gpr 19#5))]
        simp only [arm64_norm]
        rw [hcpu_j.readReg64 (.gpr 19#5), hcs_fg'.readReg64_x19]
        exact hw19
      have hx20_c : sc.readReg64 (.gpr 20#5) = newPtr := by
        rw [hcpu_c.readReg64]; simp [arm64_norm]
      have hx22_c : sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x22.trans hx22)
      have hx23_c : sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x23.trans hx23)
      have hx24_c : sc.readReg64 (.gpr 24#5) = sret := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x24.trans hx24)
      have hx25_c : sc.readReg64 (.gpr 25#5) = 4096#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x25.trans hx25)
      have hx26_c : sc.readReg64 (.gpr 26#5) = 2097152#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x26.trans hx26)
      have hx27_c : sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x27.trans hx27)
      have hx28_c : sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x28.trans hx28)
      have hx29_c : sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
        rw [hcpu_c.readReg64]; simp [arm64_norm, hx29_j']
      have hvregs_c : calleeSavedVRegs sc = calleeSavedVRegs s0 :=
        hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sj').trans
          (hcpu_j.calleeSavedVRegs.trans (hcs_fg'.vregs.trans hvregs)))
      have hacp_all : AllocCallPreserved sm_fg sc := allocCallPreserved_trans hacp_fg hacp_jc
      refine SepWP.weaken_pre ?_
        (hcont sc newPtr newPtr (BitVec.ofNat 64 newCap)
          hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c hx25_c hx26_c hx27_c hx28_c hx29_c
          hvregs_c hcl_c hacp_all)
      rw [hpool_eq_jc, hsp_eq,
        stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) (32 + allocHookStack)
          hfg_stk_le hfg_stk_hi,
        show ((s0.sp - 128#64) ↦₆₄ 0#64) ∗ ((s0.sp - 120#64) ↦₆₄ newPtr) ∗
            ((s0.sp - 112#64) ↦₆₄ BitVec.ofNat 64 newCap) =
          vecHeader (s0.sp - 128#64) 0#64 newPtr (BitVec.ofNat 64 newCap) by
            simp only [vecHeader, bv_lin_norm]]
      sep_entail

/-- `cap = 0` growth branch (`+0x124 = 292#64 .. +0x1b0` → `post_grow_budget` → `+0x15c = 348#64`). -/
theorem cliIoReadFile_grow_from_zero_budget [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    {s0 sg : State} {fd sret v0 v1 v2 oldPtr st0 st1 st2 st3 : BitVec 64}
    {R_buf : SepProp} {n stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8352 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (_hn_pos : 0 < n) (hn_le : n ≤ 4096)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sg.mem)
    (hpc : sg.pc = cliIoPl03.base + 292#64) (hrun : sg.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sg.sp = s0.sp - 8320#64)
    (hx0 : sg.readReg64 .x0 = BitVec.ofNat 64 n)
    (hw19 : (sg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sg.readReg64 (.gpr 20#5) = oldPtr)
    (hx21 : sg.readReg64 (.gpr 21#5) = 0#64)
    (hx24 : sg.readReg64 (.gpr 24#5) = sret)
    (hx25 : sg.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = 2097152#64)
    (hx27 : sg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 n)
    (hx28 : sg.readReg64 (.gpr 28#5) = 0#64)
    (hx29 : sg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sg = calleeSavedVRegs s0)
    (hoom_sg : ∀ sf_oom : State,
      ¬ FitsEvents M lim st_in (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) →
      OomPreserved sg sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl03.base + 348#64 → sc.status = .Running → sc.sp = s0.sp - 8320#64 →
      (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap 0) →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = sret →
      sc.readReg64 (.gpr 25#5) = 4096#64 → sc.readReg64 (.gpr 26#5) = 2097152#64 →
      sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 28#5) = 0#64 →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem → AllocCallPreserved sg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap 0)) newPtr [] ∗
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) st_in) sc)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sg
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ cliIoVecBuf A.repAlloc 0#64 oldPtr [] ∗
        A.pool lim st_in sg)
      post oomProp := by
  have hult_false : (4096#64 : BitVec 64).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le (by decide)
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
  intro sg' hcpu_g0
  have hcpu_g := hcpu_g0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_g' : sg'.pc = cliIoPl03.base + 292#64 := hcpu_g.pc_eq.trans hpc
  have hrun_g' : sg'.status = .Running := hcpu_g.status_eq.trans hrun
  have hsp_g' : sg'.spAligned = true := by
    rw [hcpu_g.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_g' : sg'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx0
  have hx20_g' : sg'.readReg64 (.gpr 20#5) = oldPtr := (hcpu_g.readReg64 _).trans hx20
  have hx21_g' : sg'.readReg64 (.gpr 21#5) = 0#64 := (hcpu_g.readReg64 _).trans hx21
  have hx24_g' : sg'.readReg64 (.gpr 24#5) = sret := (hcpu_g.readReg64 _).trans hx24
  have hx25_g' : sg'.readReg64 (.gpr 25#5) = 4096#64 := (hcpu_g.readReg64 _).trans hx25
  have hx26_g' : sg'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_g.readReg64 _).trans hx26
  have hx27_g' : sg'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx27
  have hx28_g' : sg'.readReg64 (.gpr 28#5) = 0#64 := (hcpu_g.readReg64 _).trans hx28
  have hx29_g' : sg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 := (hcpu_g.readReg64 _).trans hx29
  wp_sym_steps
  refine SepWP.done cliIoReadFile_grow_pc (by simpa [arm64_norm] using hrun_g')
    fun sm_fg hcpu_fg0 hcl_fg hnsp_fg hsym_fg => ?_
  have hcpu_fg := hcpu_fg0.1
  have ⟨hacp_gfg, hvm_gfg⟩ :=
    vmPreserved_of_seg hcpu_g0 hcpu_fg0 hnsp_fg hsym_fg
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_gfg : A.pool lim st_in sg = A.pool lim st_in sm_fg :=
    (A.pool_transport lim st_in sg sm_fg hvm_gfg).symm
  have hpc_fg : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym :=
    hcpu_fg.pc_eq.trans cliIoReadFile_grow_pc
  have hrun_fg : sm_fg.status = .Running := hcpu_fg.status_eq.trans hrun_g'
  have hsp_fg : sm_fg.sp = s0.sp - 8320#64 :=
    hcpu_fg.sp_eq.trans ((by simp [arm64_norm] : _ = sg'.sp).trans (hcpu_g.sp_eq.trans hsp_eq))
  have hlr_fg : sm_fg.readReg64 .lr = cliIoPl03.base + 436#64 := by
    rw [hcpu_fg.readReg64 .lr]; simp [arm64_norm]
  have hx0_fg : sm_fg.readReg64 .x0 = s0.sp - 128#64 := by
    rw [hcpu_fg.readReg64 .x0]; simp [arm64_norm]
  have hx1_fg : sm_fg.readReg64 .x1 = 0#64 := by
    rw [hcpu_fg.readReg64 .x1]; simp [arm64_norm]
  have hx2_fg : sm_fg.readReg64 .x2 = oldPtr := by
    rw [hcpu_fg.readReg64 .x2]; simp [arm64_norm]
  have hx3_fg : sm_fg.readReg64 .x3 = BitVec.ofNat 64 (cliIoCap 0) := by
    rw [hcpu_fg.readReg64 .x3]; simp [arm64_norm, cliIoCap_zero]
  have hw19_fg : (sm_fg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_fg.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_g.readReg64 (.gpr 19#5)]
    exact hw19
  have hx22_fg : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap 0) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, cliIoCap_zero]
  have hx23_fg : sm_fg.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx24_fg : sm_fg.readReg64 (.gpr 24#5) = sret := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx24_g']
  have hx25_fg : sm_fg.readReg64 (.gpr 25#5) = 4096#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx25_g']
  have hx26_fg : sm_fg.readReg64 (.gpr 26#5) = 2097152#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx26_g']
  have hx27_fg : sm_fg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (0 + n) := by
    rw [hcpu_fg.readReg64]; simpa [arm64_norm] using hx27_g'
  have hx28_fg : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 0 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx28_g']
  have hx29_fg : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx29_g']
  have hvregs_fg : calleeSavedVRegs sm_fg = calleeSavedVRegs s0 :=
    hcpu_fg.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sg').trans
      (hcpu_g.calleeSavedVRegs.trans hvregs))
  rw [hpool_eq_gfg]
  exact cliIoReadFile_post_grow_budget A lim hext3 hfg hlo hhi
    (by decide : 0 < cliIoCap 0) (cliIoCap_lt_pow63 (by decide))
    (Nat.zero_le _) (not_nullAllowed_cliIoCap (by decide))
    hcl_fg hpc_fg hrun_fg hsp0 hsp_fg hlr_fg
    hx0_fg hx1_fg hx2_fg hx3_fg hw19_fg hx22_fg hx23_fg hx24_fg hx25_fg hx26_fg hx27_fg hx28_fg hx29_fg
    hvregs_fg
    (fun sf_oom hnf hoom_s =>
      hoom_sg sf_oom hnf (oomPreserved_of_allocCallPreserved hacp_gfg hoom_s))
    (fun sc newPtr st1' st2' hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c hx25_c
        hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c hacp_fgc => by
      simpa [Nat.zero_add] using
        hcont sc newPtr st1' st2' hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c
          hx25_c hx26_c (by simpa using hx27_c) (by simpa using hx28_c) hx29_c hvregs_c hcl_c
          (allocCallPreserved_trans hacp_gfg hacp_fgc))

/-- `cap = cliIoCap j` growth branch (`+0x124 = 292#64 .. +0x1b0` → `post_grow_budget` → `+0x15c = 348#64`). -/
theorem cliIoReadFile_grow_from_pos_budget [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    {s0 sg : State} {fd sret v0 v1 v2 oldPtr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {R_buf : SepProp}
    {j len n stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8352 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hj1 : j + 1 ≤ 9)
    (hlen_le_cap : len ≤ cliIoCap j)
    (hbs_len : bs.length = len)
    (hgt_cap : cliIoCap j < len + n)
    (hle_next : len + n ≤ cliIoCap (j + 1))
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sg.mem)
    (hpc : sg.pc = cliIoPl03.base + 292#64) (hrun : sg.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sg.sp = s0.sp - 8320#64)
    (hx0 : sg.readReg64 .x0 = BitVec.ofNat 64 n)
    (hw19 : (sg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sg.readReg64 (.gpr 20#5) = oldPtr)
    (hx21 : sg.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap j))
    (hx24 : sg.readReg64 (.gpr 24#5) = sret)
    (hx25 : sg.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = 2097152#64)
    (hx27 : sg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n))
    (hx28 : sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sg = calleeSavedVRegs s0)
    (hoom_sg : ∀ sf_oom : State,
      ¬ FitsEvents M lim st_in
        (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1))) →
      OomPreserved sg sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl03.base + 348#64 → sc.status = .Running → sc.sp = s0.sp - 8320#64 →
      (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap (j + 1)) →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = sret →
      sc.readReg64 (.gpr 25#5) = 4096#64 → sc.readReg64 (.gpr 26#5) = 2097152#64 →
      sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem → AllocCallPreserved sg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap (j + 1))) newPtr bs ∗
          A.pool lim
            (M.stepEvents
              (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1))) st_in)
            sc)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sg
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap j)) oldPtr bs ∗
        A.pool lim st_in sg)
      post oomProp := by
  have hj9 : j ≤ 9 := by omega
  have hcap_lt64 : cliIoCap j < 2 ^ 64 := cliIoCap_lt_pow64 hj9
  have hnext_lt64 : cliIoCap (j + 1) < 2 ^ 64 := cliIoCap_lt_pow64 hj1
  have hcap_beq0 : (BitVec.ofNat 64 (cliIoCap j) == 0#64) = false :=
    bv64_beq_ofNat_false (by have := cliIoCap_pos j; omega) hcap_lt64 (by decide)
  have hlsl1 : (BitVec.ofNat 64 (cliIoCap j)) <<< 1 = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [bv64_shiftLeft1_ofNat (by rw [← cliIoCap_succ]; exact hnext_lt64), ← cliIoCap_succ]
  have hult1 : (BitVec.ofNat 64 (cliIoCap j)).ult (BitVec.ofNat 64 (len + n)) = true :=
    bv64_ult_ofNat_true hgt_cap (Nat.lt_of_le_of_lt hle_next hnext_lt64)
  have hult2 : (BitVec.ofNat 64 (cliIoCap (j + 1))).ult (BitVec.ofNat 64 (len + n)) = false :=
    bv64_ult_ofNat_false hle_next hnext_lt64
  have hclamp :
      (if (BitVec.ofNat 64 (cliIoCap (j + 1))).ult 2097152#64 = true
       then BitVec.ofNat 64 (cliIoCap (j + 1))
       else 2097152#64) = BitVec.ofNat 64 (cliIoCap (j + 1)) :=
    cliIoFile_cap_clamp_bv hj1
  have hcap_lt_next : cliIoCap j < cliIoCap (j + 1) := cliIoCap_strictMono (Nat.lt_succ_self j)
  have hsub_hi :
      (BitVec.ofNat 64 (cliIoCap j) - BitVec.ofNat 64 len).ult
        (BitVec.ofNat 64 (cliIoCap (j + 1)) - BitVec.ofNat 64 len) = true := by
    rw [bv64_sub_ofNat hlen_le_cap, bv64_sub_ofNat (Nat.le_trans hlen_le_cap (Nat.le_of_lt hcap_lt_next))]
    exact bv64_ult_ofNat_true (by omega) (by omega)
  have hnext_ult_len : (BitVec.ofNat 64 (cliIoCap (j + 1))).ult (BitVec.ofNat 64 len) = false :=
    bv64_ult_ofNat_false (Nat.le_trans hlen_le_cap (Nat.le_of_lt hcap_lt_next)) hnext_lt64
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
  intro sg' hcpu_g0
  have hcpu_g := hcpu_g0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_g' : sg'.pc = cliIoPl03.base + 292#64 := hcpu_g.pc_eq.trans hpc
  have hrun_g' : sg'.status = .Running := hcpu_g.status_eq.trans hrun
  have hsp_g' : sg'.spAligned = true := by
    rw [hcpu_g.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_g' : sg'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx0
  have hx20_g' : sg'.readReg64 (.gpr 20#5) = oldPtr := (hcpu_g.readReg64 _).trans hx20
  have hx21_g' : sg'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap j) :=
    (hcpu_g.readReg64 _).trans hx21
  have hx24_g' : sg'.readReg64 (.gpr 24#5) = sret := (hcpu_g.readReg64 _).trans hx24
  have hx25_g' : sg'.readReg64 (.gpr 25#5) = 4096#64 := (hcpu_g.readReg64 _).trans hx25
  have hx26_g' : sg'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_g.readReg64 _).trans hx26
  have hx27_g' : sg'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) :=
    (hcpu_g.readReg64 _).trans hx27
  have hx28_g' : sg'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := (hcpu_g.readReg64 _).trans hx28
  have hx29_g' : sg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 := (hcpu_g.readReg64 _).trans hx29
  wp_sym_steps
  refine SepWP.done cliIoReadFile_grow_pc (by simpa [arm64_norm] using hrun_g')
    fun sm_fg hcpu_fg0 hcl_fg hnsp_fg hsym_fg => ?_
  have hcpu_fg := hcpu_fg0.1
  have ⟨hacp_gfg, hvm_gfg⟩ :=
    vmPreserved_of_seg hcpu_g0 hcpu_fg0 hnsp_fg hsym_fg
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_gfg : A.pool lim st_in sg = A.pool lim st_in sm_fg :=
    (A.pool_transport lim st_in sg sm_fg hvm_gfg).symm
  have hpc_fg : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym :=
    hcpu_fg.pc_eq.trans cliIoReadFile_grow_pc
  have hrun_fg : sm_fg.status = .Running := hcpu_fg.status_eq.trans hrun_g'
  have hsp_fg : sm_fg.sp = s0.sp - 8320#64 :=
    hcpu_fg.sp_eq.trans ((by simp [arm64_norm] : _ = sg'.sp).trans (hcpu_g.sp_eq.trans hsp_eq))
  have hlr_fg : sm_fg.readReg64 .lr = cliIoPl03.base + 436#64 := by
    rw [hcpu_fg.readReg64 .lr]; simp [arm64_norm]
  have hx0_fg : sm_fg.readReg64 .x0 = s0.sp - 128#64 := by
    rw [hcpu_fg.readReg64 .x0]; simp [arm64_norm]
  have hx1_fg : sm_fg.readReg64 .x1 = BitVec.ofNat 64 (cliIoCap j) := by
    rw [hcpu_fg.readReg64 .x1]; simp [arm64_norm]
  have hx2_fg : sm_fg.readReg64 .x2 = oldPtr := by
    rw [hcpu_fg.readReg64 .x2]; simp [arm64_norm]
  have hx3_fg : sm_fg.readReg64 .x3 = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [hcpu_fg.readReg64 .x3]; simp [arm64_norm]
  have hw19_fg : (sm_fg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_fg.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_g.readReg64 (.gpr 19#5)]
    exact hw19
  have hx22_fg : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx23_fg : sm_fg.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx24_fg : sm_fg.readReg64 (.gpr 24#5) = sret := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx24_g']
  have hx25_fg : sm_fg.readReg64 (.gpr 25#5) = 4096#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx25_g']
  have hx26_fg : sm_fg.readReg64 (.gpr 26#5) = 2097152#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx26_g']
  have hx27_fg : sm_fg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx27_g']
  have hx28_fg : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx28_g']
  have hx29_fg : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx29_g']
  have hvregs_fg : calleeSavedVRegs sm_fg = calleeSavedVRegs s0 :=
    hcpu_fg.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sg').trans
      (hcpu_g.calleeSavedVRegs.trans hvregs))
  rw [hpool_eq_gfg]
  exact cliIoReadFile_post_grow_budget A lim hext3 hfg hlo hhi
    (cliIoCap_pos (j + 1)) (cliIoCap_lt_pow63 hj1)
    (by rw [hbs_len]; omega) (not_nullAllowed_cliIoCap hj1)
    hcl_fg hpc_fg hrun_fg hsp0 hsp_fg hlr_fg
    hx0_fg hx1_fg hx2_fg hx3_fg hw19_fg hx22_fg hx23_fg hx24_fg hx25_fg hx26_fg hx27_fg hx28_fg hx29_fg
    hvregs_fg
    (fun sf_oom hnf hoom_s =>
      hoom_sg sf_oom hnf (oomPreserved_of_allocCallPreserved hacp_gfg hoom_s))
    (fun sc newPtr st1' st2' hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c hx25_c
        hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c hacp_fgc =>
      hcont sc newPtr st1' st2' hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c
        hx25_c hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c
        (allocCallPreserved_trans hacp_gfg hacp_fgc))

/-- Shared `memcpy(ptr + len, sp + 4096, chunk)` + back-edge `+0x16c .. +0x18c → +0xd8 = 216#64` join. -/
theorem cliIoReadFile_memcpy_backedge_budget [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym) stdMemcpySpec)
    {s0 sc : State} {fd sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {R_path : SepProp}
    {rem chunk oldBuf : List (BitVec 8)}
    {cap len want stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcap_pos : 0 < cap) (hcap_lt63 : cap < 2 ^ 63)
    (hlen_r : len + chunk.length ≤ rem.length)
    (hlen_cap : len + chunk.length ≤ cap)
    (hlen_max : len + chunk.length ≤ 2097152)
    (hwant_le : want ≤ 4096)
    (hold_len : oldBuf.length = want)
    (hn_le_want : chunk.length ≤ want)
    (hchunk_eq : chunk = (rem.drop len).take want)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem)
    (hpc : sc.pc = cliIoPl03.base + 348#64) (hrun : sc.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sc.sp = s0.sp - 8320#64)
    (hw19 : (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sc.readReg64 (.gpr 20#5) = ptr)
    (hx22 : sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap)
    (hx23 : sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 chunk.length)
    (hx24 : sc.readReg64 (.gpr 24#5) = sret)
    (hx25 : sc.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sc.readReg64 (.gpr 26#5) = 2097152#64)
    (hx27 : sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + chunk.length))
    (hx28 : sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sc.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sc = calleeSavedVRegs s0)
    (hcont : ∀ sn : State,
      sn.pc = cliIoPl03.base + 216#64 → sn.status = .Running → sn.sp = s0.sp - 8320#64 →
      (sn.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sn.readReg64 (.gpr 20#5) = ptr →
      sn.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sn.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 2097152 (len + chunk.length)) →
      sn.readReg64 (.gpr 24#5) = sret →
      sn.readReg64 (.gpr 25#5) = 4096#64 →
      sn.readReg64 (.gpr 26#5) = 2097152#64 →
      sn.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + chunk.length) →
      sn.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sn = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sn.mem → CliIoMidPreserved sc sn →
      SepWP P (s0.readReg64 .lr) sn
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_path ∗
          memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take (len + chunk.length)) ∗
          A.pool lim st_cur sn)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sc
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_path ∗
        (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
          memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want)) ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take len) ∗
        A.pool lim st_cur sc)
      post oomProp := by
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
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
  intro sc' hcpu_c0
  have hcpu_c := hcpu_c0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_c' : sc'.pc = cliIoPl03.base + 348#64 := hcpu_c.pc_eq.trans hpc
  have hrun_c' : sc'.status = .Running := hcpu_c.status_eq.trans hrun
  have hsp_c_in : sc'.sp = s0.sp - 8320#64 := hcpu_c.sp_eq.trans hsp_eq
  have hsp_c' : sc'.spAligned = true := by
    rw [hcpu_c.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx20_c' : sc'.readReg64 (.gpr 20#5) = ptr := (hcpu_c.readReg64 _).trans hx20
  have hx23_c' : sc'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 chunk.length :=
    (hcpu_c.readReg64 _).trans hx23
  have hx28_c' : sc'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len :=
    (hcpu_c.readReg64 _).trans hx28
  wp_sym_steps
  refine SepWP.done cliIoReadFile_memcpy_pc (by simpa [arm64_norm] using hrun_c')
    fun sm_mc hcpu_mc0 hcl_mc hnsp_mc hsym_mc => ?_
  have hcpu_mc := hcpu_mc0.1
  have ⟨hacp_cmc, hvm_cmc⟩ :=
    vmPreserved_of_seg hcpu_c0 hcpu_mc0 hnsp_mc hsym_mc
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_cmc : A.pool lim st_cur sc = A.pool lim st_cur sm_mc :=
    (A.pool_transport lim st_cur sc sm_mc hvm_cmc).symm
  have hpc_mc : sm_mc.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym :=
    hcpu_mc.pc_eq.trans cliIoReadFile_memcpy_pc
  have hrun_mc : sm_mc.status = .Running := hcpu_mc.status_eq.trans hrun_c'
  have hsp_mc_eq : sm_mc.sp = s0.sp - 8320#64 :=
    hcpu_mc.sp_eq.trans ((by simp [arm64_norm] : _ = sc'.sp).trans hsp_c_in)
  have hsp_mc : sm_mc.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_mc_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_mc : sm_mc.readReg64 .lr = cliIoPl03.base + 364#64 := by
    rw [hcpu_mc.readReg64 .lr]; simp [arm64_norm]
  have hx0_mc : sm_mc.readReg64 .x0 = ptr + BitVec.ofNat 64 len := by
    rw [hcpu_mc.readReg64 .x0]; simp [arm64_norm]
  have hx1_mc : sm_mc.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_mc.readReg64 .x1]; simp only [arm64_norm]
  have hx2_mc : sm_mc.readReg64 .x2 = BitVec.ofNat 64 chunk.length := by
    rw [hcpu_mc.readReg64 .x2]; simp [arm64_norm, hchunk_eq]
  apply seqCodeLoaded hcl_mc (mid := cliIoPl03.base + 364#64)
  apply (SepWP.call_subroutine_frame hmemcpy
    (x := (ptr + BitVec.ofNat 64 len, s0.sp - 4224#64, chunk))
    hpc_mc hrun_mc hsp_mc hlr_mc
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [stdMemcpySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    have hchunk_lt64 : chunk.length < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.le_trans hn_le_want hwant_le) (by decide)
    refine ⟨⟨hx0_mc, hx1_mc, hx2_mc, hchunk_lt64⟩, ?_⟩
    rw [hpool_eq_cmc] at hm'
    exact Satisfies.mono (by sep_frame) hm'
  · intro sm_mc' hpc_mc' hrun_mc' hsp_mc' hcs_mc'
    refine SepWP.done hpc_mc' hrun_mc' fun hcl_mc' => ?_
    wp_conv_pre => dsimp only [stdMemcpySpec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hstd_mc⟩
    have hmid_mc : CliIoMidPreserved sm_mc sm_mc' := CliIoMidPreserved.of_std hstd_mc
    have hpool_eq_mc : A.pool lim st_cur sm_mc = A.pool lim st_cur sm_mc' :=
      (A.pool_transport lim st_cur sm_mc sm_mc' (vmPreserved_of_stdState hstd_mc)).symm
    have hsp_mc'_eq : sm_mc'.sp = s0.sp - 8320#64 := hsp_mc'.trans hsp_mc_eq
    have hx22_mc' : sm_mc'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap :=
      hcs_mc'.readReg64_x22.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 22#5)).trans
          ((hcpu_c.readReg64 _).trans hx22)))
    have hx25_mc' : sm_mc'.readReg64 (.gpr 25#5) = 4096#64 :=
      hcs_mc'.readReg64_x25.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 25#5)).trans
          ((hcpu_c.readReg64 _).trans hx25)))
    have hx27_mc' : sm_mc'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + chunk.length) :=
      hcs_mc'.readReg64_x27.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 27#5)).trans
          ((hcpu_c.readReg64 _).trans hx27)))
    have hsub8 :
        2097153#64 - BitVec.ofNat 64 (len + chunk.length) =
          BitVec.ofNat 64 (2097152 + 1 - (len + chunk.length)) := by
      change BitVec.ofNat 64 2097153 - BitVec.ofNat 64 (len + chunk.length) = _
      exact bv64_sub_ofNat (by omega)
    have hule :
        (BitVec.ofNat 64 (len + ((rem.drop len).take want).length)).ule 2097152#64 = true := by
      rw [← hchunk_eq]
      have hlt64 : len + chunk.length < 2 ^ 64 := by omega
      apply decide_eq_true
      change (BitVec.ofNat 64 (len + chunk.length)).toNat ≤ (2097152#64 : BitVec 64).toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
      exact hlen_max
    apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_mc'
      (mid := cliIoPl03.base + 216#64)
    intro sb' hcpu_b0
    have hcpu_b := hcpu_b0.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc_b' : sb'.pc = cliIoPl03.base + 364#64 := hcpu_b.pc_eq.trans hpc_mc'
    have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_mc'
    have hsp_b' : sb'.spAligned = true := by
      rw [hcpu_b.spAligned]; simp only [State.spAligned]; rw [hsp_mc'_eq]
      exact s0.spAligned_sub 8320#64 hsp0
    have hx22_b' : sb'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap :=
      (hcpu_b.readReg64 _).trans hx22_mc'
    have hx25_b' : sb'.readReg64 (.gpr 25#5) = 4096#64 :=
      (hcpu_b.readReg64 _).trans hx25_mc'
    have hx27_b' : sb'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + chunk.length) :=
      (hcpu_b.readReg64 _).trans hx27_mc'
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
      fun sn hcpu_n0 hcl_n hnsp_n hsym_n => ?_
    have hcpu_n := hcpu_n0.1
    have ⟨hacp_bn, hvm_bn⟩ :=
      vmPreserved_of_seg hcpu_b0 hcpu_n0 hnsp_n hsym_n
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_bn : A.pool lim st_cur sm_mc' = A.pool lim st_cur sn :=
      (A.pool_transport lim st_cur sm_mc' sn hvm_bn).symm
    have hpc_n : sn.pc = cliIoPl03.base + 216#64 := by
      rw [hcpu_n.pc_eq]; simp [arm64_norm]
    have hrun_n : sn.status = .Running := hcpu_n.status_eq.trans hrun_b'
    have hsp_n : sn.sp = s0.sp - 8320#64 :=
      hcpu_n.sp_eq.trans ((by simp [arm64_norm] : _ = sb'.sp).trans (hcpu_b.sp_eq.trans hsp_mc'_eq))
    have hw19_n : (sn.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
      rw [readReg32_of_readReg64_eq (hcpu_n.readReg64 (.gpr 19#5))]
      simp only [arm64_norm]
      rw [hcpu_b.readReg64 (.gpr 19#5), hcs_mc'.readReg64_x19,
        hcpu_mc.readReg64 (.gpr 19#5)]
      simp only [arm64_norm]
      rw [hcpu_c.readReg64 (.gpr 19#5)]
      exact hw19
    have hx20_n : sn.readReg64 (.gpr 20#5) = ptr := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x20, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact hx20_c'
    have hx21_n : sn.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := by
      rw [hcpu_n.readReg64]; simp [arm64_norm]
    have hx23_n : sn.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 2097152 (len + chunk.length)) := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]; rw [← hchunk_eq, hsub8]
      exact wantBytes_csel_bv hlen_max (by decide)
    have hx24_n : sn.readReg64 (.gpr 24#5) = sret := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x24, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx24
    have hx25_n : sn.readReg64 (.gpr 25#5) = 4096#64 := by
      rw [hcpu_n.readReg64]; simp [arm64_norm, hx25_b']
    have hx26_n : sn.readReg64 (.gpr 26#5) = 2097152#64 := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x26, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx26
    have hx28_n : sn.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + chunk.length) := by
      rw [hcpu_n.readReg64]; simp [arm64_norm, hchunk_eq]
    have hx29_n : sn.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x29, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx29
    have hvregs_n : calleeSavedVRegs sn = calleeSavedVRegs s0 :=
      hcpu_n.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
        (hcpu_b.calleeSavedVRegs.trans (hcs_mc'.vregs.trans
          (hcpu_mc.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sc').trans
            (hcpu_c.calleeSavedVRegs.trans hvregs))))))
    have hmid_cn : CliIoMidPreserved sc sn :=
      (cliIoMidPreserved_of_acp hacp_cmc).trans
        (hmid_mc.trans (cliIoMidPreserved_of_acp hacp_bn))
    refine SepWP.weaken_pre ?_
      (hcont sn hpc_n hrun_n hsp_n hw19_n hx20_n hx21_n hx23_n hx24_n hx25_n hx26_n hx28_n hx29_n
        hvregs_n hcl_n hmid_cn)
    rw [hpool_eq_mc, hpool_eq_bn]
    have hvec_back :=
      cliIoVecBuf_repack_chunk A.repAlloc hcap_pos hcap_lt63 hptr_ne0 hlen_r hlen_cap hchunk_eq
    have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
    let Rest : SepProp :=
      stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_path ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        A.pool lim st_cur sn
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := Rest) (sepConj_mono hvec_back hbuf_back))
        (by dsimp only [Rest]; sep_entail))
    dsimp only [Rest, RustCliAllocBudget.repAlloc] at hvec_back ⊢
    sep_entail

/-! ## Budget-Threaded Post-`read` Branches and `do_read` (`+0xd8 → +0xe8`) -/

private theorem cliIoReadFile_after_read_eof_budget [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hA_mem : ∀ st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 sr : State} {fd sret v0 v1 v2 cap ptr st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {bs : List (BitVec 8)} {stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : sr.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl03.base + 232#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 8320#64)
    (hx0 : sr.readReg64 .x0 = 0#64)
    (hw19 : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = cap)
    (hx24 : sr.readReg64 (.gpr 24#5) = sret)
    (hx28 : sr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = sr.fs.setFd fd none →
      sf.trace = sr.trace → sf.sigActions = sr.sigActions →
      sf.tpidrEl0 = sr.tpidrEl0 → sf.brkStart = sr.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.ok bs) ∗
          A.pool lim st_cur sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sr
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc cap ptr bs ∗ A.pool lim st_cur sr)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 456#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
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
  have hw19_e : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_e.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_r.readReg64 (.gpr 19#5)]
    exact hw19
  rw [hpool_eq]
  exact cliIoReadFile_ok_epilogue_budget A lim hA_mem hext3 hclose hlo hhi hfd_lt
    (by rw [hacp_re.1]; exact hfds) hkind hcl_e
    (hcpu_e.pc_eq.trans (by simp [arm64_norm])) (hcpu_e.status_eq.trans hrun_r') hsp0
    (hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    hw19_e
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx21)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx28)
    (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
      hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
        (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_re.1))
        (htr_f.trans hacp_re.2.1) (hsig_f.trans hacp_re.2.2.1)
        (htp_f.trans hacp_re.2.2.2.1) (hbs_f.trans hacp_re.2.2.2.2.1) hent

private theorem cliIoReadFile_after_read_overcap_budget [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hA_mem : ∀ st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 sr : State} {fd sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {bs : List (BitVec 8)} {stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : sr.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl03.base + 232#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 8320#64)
    (hx0 : sr.readReg64 .x0 = 1#64)
    (hw19 : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap 9))
    (hx23 : sr.readReg64 (.gpr 23#5) = 1#64)
    (hx24 : sr.readReg64 (.gpr 24#5) = sret)
    (hx26 : sr.readReg64 (.gpr 26#5) = 2097152#64)
    (hx28 : sr.readReg64 (.gpr 28#5) = 2097152#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = sr.fs.setFd fd none →
      sf.trace = sr.trace → sf.sigActions = sr.sigActions →
      sf.tpidrEl0 = sr.tpidrEl0 → sf.brkStart = sr.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.error ()) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents (cliIoCap 9) 1) st_in) sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sr
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap 9)) ptr bs ∗
        A.pool lim st_in sr)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 468#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = 1#64 := (hcpu_r.readReg64 _).trans hx0
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = 1#64 := (hcpu_r.readReg64 _).trans hx23
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_r.readReg64 _).trans hx26
  have hx28_r' : sr'.readReg64 (.gpr 28#5) = 2097152#64 := (hcpu_r.readReg64 _).trans hx28
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
  have hcpu_e := hcpu_e0.1
  have ⟨hacp_re, hvm_re⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_e0 hnsp_e hsym_e
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool lim st_in sr = A.pool lim st_in se :=
    (A.pool_transport lim st_in sr se hvm_re).symm
  have hw19_e : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_e.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_r.readReg64 (.gpr 19#5)]
    exact hw19
  rw [hpool_eq]
  exact cliIoReadFile_err_dealloc_epilogue_budget A lim hA_mem hext3 hdealloc hclose hlo hhi
    (cliIoCap_pos 9) (cliIoCap_lt_pow63 (by decide)) hfd_lt
    (by rw [hacp_re.1]; exact hfds) hkind hcl_e
    (hcpu_e.pc_eq.trans (by simp [arm64_norm])) (hcpu_e.status_eq.trans hrun_r') hsp0
    (hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    hw19_e
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx21)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
      hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
        (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_re.1))
        (htr_f.trans hacp_re.2.1) (hsig_f.trans hacp_re.2.2.1)
        (htp_f.trans hacp_re.2.2.2.1) (hbs_f.trans hacp_re.2.2.2.2.1) hent

private theorem cliIoReadFile_after_read_nogrow_vm [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    {s0 sr : State} {fd sret ptr : BitVec 64} {Pre : SepProp}
    {cap len want n : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hn_pos : 0 < n) (hn_le_want : n ≤ want) (hwant_le : want ≤ 4096)
    (hlen_cap : len + n ≤ cap) (hcap_max : cap ≤ 2097152)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl03.base + 232#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 8320#64)
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 n)
    (hw19 : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx23 : sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sr.readReg64 (.gpr 24#5) = sret)
    (hx25 : sr.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sr.readReg64 (.gpr 26#5) = 2097152#64)
    (hx28 : sr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sr.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sc : State,
      sc.pc = cliIoPl03.base + 348#64 → sc.status = .Running → sc.sp = s0.sp - 8320#64 →
      (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sc.readReg64 (.gpr 20#5) = ptr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = sret →
      sc.readReg64 (.gpr 25#5) = 4096#64 → sc.readReg64 (.gpr 26#5) = 2097152#64 →
      sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem →
      AllocCallPreserved sr sc → VmPreserved sr sc →
      SepWP P (s0.readReg64 .lr) sc Pre post oomProp) :
    SepWP P (s0.readReg64 .lr) sr Pre post oomProp := by
  have hn_beq0 : (BitVec.ofNat 64 n == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) (by omega) (by decide)
  have hbit63 : (BitVec.ofNat 64 n).getLsbD 63 = false := bit63_eq_zero_of_lt (by omega)
  have hule_w : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 want) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_w : (BitVec.ofNat 64 want).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le_want (by omega)
  have hsub26 : 2097152#64 - BitVec.ofNat 64 len = BitVec.ofNat 64 (2097152 - len) :=
    bv64_sub_ofNat (by omega)
  have hule_rem : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (2097152 - len)) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_rem : (BitVec.ofNat 64 (2097152 - len)).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false (by omega) (by omega)
  have hadd27 : BitVec.ofNat 64 n + BitVec.ofNat 64 len = BitVec.ofNat 64 (len + n) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hule_cap : (BitVec.ofNat 64 (len + n)).ule (BitVec.ofNat 64 cap) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_cap : (BitVec.ofNat 64 cap).ult (BitVec.ofNat 64 (len + n)) = false :=
    bv64_ult_ofNat_false hlen_cap (by omega)
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 348#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_r.readReg64 _).trans hx0
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_r.readReg64 _).trans hx21
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_r.readReg64 _).trans hx23
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_r.readReg64 _).trans hx26
  have hx28_r' : sr'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := (hcpu_r.readReg64 _).trans hx28
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun sc hcpu_c0 hcl_c hnsp_c hsym_c => ?_
  have hcpu_c := hcpu_c0.1
  have ⟨hacp_rc, hvm_rc⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_c0 hnsp_c hsym_c
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hw19_c : (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_c.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_r.readReg64 (.gpr 19#5)]
    exact hw19
  exact hcont sc (hcpu_c.pc_eq.trans (by simp [arm64_norm])) (hcpu_c.status_eq.trans hrun_r')
    (hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    hw19_c
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx25)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm, hx26_r'])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm, hx28_r'])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx29)
    (hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    hcl_c hacp_rc hvm_rc

private theorem cliIoReadFile_after_read_grow_vm [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    {s0 sr : State} {fd sret ptr : BitVec 64} {Pre : SepProp}
    {cap len want n : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hn_pos : 0 < n) (hn_le_want : n ≤ want) (hwant_le : want ≤ 4096)
    (hgt_cap : cap < len + n) (hlen_max : len + n ≤ 2097152)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl03.base + 232#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 8320#64)
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 n)
    (hw19 : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx23 : sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sr.readReg64 (.gpr 24#5) = sret)
    (hx25 : sr.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sr.readReg64 (.gpr 26#5) = 2097152#64)
    (hx28 : sr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sr.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sg : State,
      sg.pc = cliIoPl03.base + 292#64 → sg.status = .Running → sg.sp = s0.sp - 8320#64 →
      sg.readReg64 .x0 = BitVec.ofNat 64 n →
      (sg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sg.readReg64 (.gpr 20#5) = ptr →
      sg.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sg.readReg64 (.gpr 24#5) = sret →
      sg.readReg64 (.gpr 25#5) = 4096#64 → sg.readReg64 (.gpr 26#5) = 2097152#64 →
      sg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) →
      sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sg.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sg = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sg.mem →
      AllocCallPreserved sr sg → VmPreserved sr sg →
      SepWP P (s0.readReg64 .lr) sg Pre post oomProp) :
    SepWP P (s0.readReg64 .lr) sr Pre post oomProp := by
  have hn_beq0 : (BitVec.ofNat 64 n == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) (by omega) (by decide)
  have hbit63 : (BitVec.ofNat 64 n).getLsbD 63 = false := bit63_eq_zero_of_lt (by omega)
  have hule_w : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 want) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_w : (BitVec.ofNat 64 want).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le_want (by omega)
  have hsub26 : 2097152#64 - BitVec.ofNat 64 len = BitVec.ofNat 64 (2097152 - len) :=
    bv64_sub_ofNat (by omega)
  have hule_rem : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (2097152 - len)) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_rem : (BitVec.ofNat 64 (2097152 - len)).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false (by omega) (by omega)
  have hadd27 : BitVec.ofNat 64 n + BitVec.ofNat 64 len = BitVec.ofNat 64 (len + n) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hule_cap : (BitVec.ofNat 64 (len + n)).ule (BitVec.ofNat 64 cap) = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hult_cap : (BitVec.ofNat 64 cap).ult (BitVec.ofNat 64 (len + n)) = true :=
    bv64_ult_ofNat_true hgt_cap (by omega)
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 292#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_r.readReg64 _).trans hx0
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_r.readReg64 _).trans hx21
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_r.readReg64 _).trans hx23
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_r.readReg64 _).trans hx26
  have hx28_r' : sr'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := (hcpu_r.readReg64 _).trans hx28
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun sg hcpu_g0 hcl_g hnsp_g hsym_g => ?_
  have hcpu_g := hcpu_g0.1
  have ⟨hacp_rg, hvm_rg⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_g0 hnsp_g hsym_g
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hw19_g : (sg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_g.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_r.readReg64 (.gpr 19#5)]
    exact hw19
  exact hcont sg (hcpu_g.pc_eq.trans (by simp [arm64_norm])) (hcpu_g.status_eq.trans hrun_r')
    (hcpu_g.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx0_r'])
    hw19_g
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx21_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx25)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx26_r'])
    (by rw [hcpu_g.readReg64]; simp [arm64_norm])
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx28_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx29)
    (hcpu_g.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    hcl_g hacp_rg hvm_rg

private theorem cliIoReadFile_do_read_budget [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hA_mem : ∀ st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    {s0 sl : State} {d0 : FdEntry} {fd sret ptr cap_bv : BitVec 64} {R_frame : SepProp}
    {len want stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8352 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hwant_le : want ≤ 4096)
    (hoff_le : d0.offset + len + want ≤ Arm64.MAX_LFS_FILESIZE)
    (hkind : d0.kind = .localFile) (hcanr : d0.accMode.canRead = true)
    (hfs : sl.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + len }))
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sl.mem)
    (hpc : sl.pc = cliIoPl03.base + 216#64) (hrun : sl.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sl.sp = s0.sp - 8320#64)
    (hw19 : (sl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sl.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sl.readReg64 (.gpr 21#5) = cap_bv)
    (hx23 : sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sl.readReg64 (.gpr 24#5) = sret)
    (hx25 : sl.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sl.readReg64 (.gpr 26#5) = 2097152#64)
    (hx28 : sl.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sl.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sl = calleeSavedVRegs s0)
    (hcont : ∀ (sr : State) (oldBuf : List (BitVec 8)),
      let rem := (s0.fs.fdBytes d0).drop d0.offset
      let chunk := (rem.drop len).take want
      oldBuf.length = want →
      sr.pc = cliIoPl03.base + 232#64 → sr.status = .Running → sr.sp = s0.sp - 8320#64 →
      sr.readReg64 .x0 = BitVec.ofNat 64 chunk.length →
      (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sr.readReg64 (.gpr 20#5) = ptr →
      sr.readReg64 (.gpr 21#5) = cap_bv →
      sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want →
      sr.readReg64 (.gpr 24#5) = sret →
      sr.readReg64 (.gpr 25#5) = 4096#64 →
      sr.readReg64 (.gpr 26#5) = 2097152#64 →
      sr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sr.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs sr = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem →
      sr.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + (len + chunk.length) }) →
      sr.trace = sl.trace → sr.sigActions = sl.sigActions →
      sr.tpidrEl0 = sl.tpidrEl0 → sr.brkStart = sl.brkStart →
      SepWP P (s0.readReg64 .lr) sr
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
            memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want)) ∗
          R_frame ∗ A.pool lim st_cur sr)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sl
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
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
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
  intro sl' hcpu_l0
  have hcpu_l := hcpu_l0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_l' : sl'.pc = cliIoPl03.base + 216#64 := hcpu_l.pc_eq.trans hpc
  have hrun_l' : sl'.status = .Running := hcpu_l.status_eq.trans hrun
  have hsp_l_in : sl'.sp = s0.sp - 8320#64 := hcpu_l.sp_eq.trans hsp_eq
  have hsp_l' : sl'.spAligned = true := by
    rw [hcpu_l.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx23_l' : sl'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_l.readReg64 _).trans hx23
  wp_sym_steps
  refine SepWP.done cliIoReadFile_read_pc (by simpa [arm64_norm] using hrun_l')
    fun sm_rd hcpu_rd0 hcl_rd hnsp_rd hsym_rd => ?_
  have hcpu_rd := hcpu_rd0.1
  have ⟨hacp_lrd, hvm_lrd⟩ :=
    vmPreserved_of_seg hcpu_l0 hcpu_rd0 hnsp_rd hsym_rd
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_lrd : A.pool lim st_cur sl = A.pool lim st_cur sm_rd :=
    (A.pool_transport lim st_cur sl sm_rd hvm_lrd).symm
  have hpc_rd : sm_rd.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym :=
    hcpu_rd.pc_eq.trans cliIoReadFile_read_pc
  have hrun_rd : sm_rd.status = .Running := hcpu_rd.status_eq.trans hrun_l'
  have hsp_rd_eq : sm_rd.sp = s0.sp - 8320#64 :=
    hcpu_rd.sp_eq.trans ((by simp [arm64_norm] : _ = sl'.sp).trans hsp_l_in)
  have hsp_rd : sm_rd.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_rd_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_rd : sm_rd.readReg64 .lr = cliIoPl03.base + 232#64 := by
    rw [hcpu_rd.readReg64 .lr]; simp [arm64_norm]
  have hx0_rd : (sm_rd.readReg32 .x0).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_rd.readReg64 .x0)]
    simp only [arm64_norm]
    rw [hcpu_l.readReg64 (.gpr 19#5)]
    exact hw19
  have hx1_rd : sm_rd.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_rd.readReg64 .x1]; simp only [arm64_norm]
  have hx2_rd : sm_rd.readReg64 .x2 = BitVec.ofNat 64 want := by
    rw [hcpu_rd.readReg64 .x2]; simp [arm64_norm]
  have hfs_rd : sm_rd.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + len }) :=
    hacp_lrd.1.trans hfs
  have hfds_rd : sm_rd.fs.fds fd = some { d0 with offset := d0.offset + len } := by
    rw [hfs_rd]; simp [FsState.setFd]
  rw [hpool_eq_lrd]
  let d_cur : FdEntry := { d0 with offset := d0.offset + len }
  have hkind_or : (d_cur.kind == .localFile || d_cur.kind == .stdio) = true := by
    dsimp only [d_cur]; rw [hkind]; rfl
  apply seqCodeLoaded hcl_rd (mid := cliIoPl03.base + 232#64)
  apply (SepWP.call_subroutine_frame hread
    (x := (fd, s0.sp - 4224#64, BitVec.ofNat 64 want, d_cur, oldBuf))
    hpc_rd hrun_rd hsp_rd hlr_rd
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslReadFileOrStdio32Spec]
    rw [hsp_rd_eq, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_rd, hfd_lt, hx1_rd, hx2_rd,
      by rw [hwant_toNat]; simp only [Arm64.MAX_RW_COUNT]; omega,
      by rw [hwant_toNat]; exact sp_sub_4224_va_bound (by omega) hsp_va hwant_le,
      fun _ => by dsimp only [d_cur]; rw [hwant_toNat]; exact hoff_le,
      by rw [hwant_toNat]; exact hold_len, hfds_rd, hkind_or, hcanr⟩, ?_⟩
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 32 (by omega) (by omega)] at hm'
    exact Satisfies.mono (by sep_frame) hm'
  · intro sr hpc_sr hrun_sr hsp_sr hcs_rdsr
    refine SepWP.done hpc_sr hrun_sr fun hcl_sr => ?_
    wp_conv_pre => dsimp only [muslReadFileOrStdio32Spec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_sr, hfs_sr, htr_sr, hsys_sr⟩
    have hpool_eq_sr : A.pool lim st_cur sm_rd = A.pool lim st_cur sr :=
      (hA_mem st_cur (vmMemPreserved_of_syscallPreserved hsys_sr)).symm
    have hchunk_eq :
        ((sm_rd.fs.fdBytes d_cur).drop d_cur.offset).take (BitVec.ofNat 64 want).toNat =
          (((s0.fs.fdBytes d0).drop d0.offset).drop len).take want := by
      rw [hfs_rd, hwant_toNat]
      dsimp only [FsState.setFd, FsState.fdBytes, FsState.files, FsState.getEntry, d_cur]
      rw [← List.drop_drop]
    have hfs_sr' : sr.fs = s0.fs.setFd fd
        (some { d0 with offset := d0.offset + (len + ((((s0.fs.fdBytes d0).drop d0.offset).drop len).take want).length) }) := by
      rw [hfs_sr, hchunk_eq, hfs_rd, FsState.setFd_setFd_same]
      dsimp only [d_cur]
      rw [Nat.add_assoc]
    have hsp_sr_eq : sr.sp = s0.sp - 8320#64 := hsp_sr.trans hsp_rd_eq
    have hw19_sr : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
      rw [readReg32_of_readReg64_eq hcs_rdsr.readReg64_x19,
        readReg32_of_readReg64_eq (hcpu_rd.readReg64 (.gpr 19#5))]
      simp only [arm64_norm]
      rw [hcpu_l.readReg64 (.gpr 19#5)]
      exact hw19
    refine SepWP.weaken_pre ?_
      (hcont sr oldBuf hold_len hpc_sr hrun_sr hsp_sr_eq
        (by rwa [hchunk_eq] at hx0_sr)
        hw19_sr
        (by rw [hcs_rdsr.readReg64_x20, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx20)
        (by rw [hcs_rdsr.readReg64_x21, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx21)
        (by rw [hcs_rdsr.readReg64_x23, hcpu_rd.readReg64]; simp only [arm64_norm]; exact hx23_l')
        (by rw [hcs_rdsr.readReg64_x24, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx24)
        (by rw [hcs_rdsr.readReg64_x25, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx25)
        (by rw [hcs_rdsr.readReg64_x26, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx26)
        (by rw [hcs_rdsr.readReg64_x28, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx28)
        (by rw [hcs_rdsr.readReg64_x29, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx29)
        (hcs_rdsr.vregs.trans (hcpu_rd.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs sl').trans (hcpu_l.calleeSavedVRegs.trans hvregs))))
        hcl_sr hfs_sr' (htr_sr.trans hacp_lrd.2.1) (hsys_sr.2.1.trans hacp_lrd.2.2.1)
        (hsys_sr.1.trans hacp_lrd.2.2.2.1) (hsys_sr.2.2.brkStart_eq.trans hacp_lrd.2.2.2.2.1))
    rw [hpool_eq_sr, hchunk_eq, hsp_rd_eq,
      stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 32 (by omega) (by omega)]
    sep_entail

/-! ## Budget-Threaded `4096`-B `read_file` `.localFile` Loop (`+0xd8`) -/

/-- Budget-threaded `4096`-byte `read_file` `.localFile` loop from `+0xd8 = 216#64` over whole
    `A.pool lim st_cur sl` (`0` `StdErrnoCell`), stepping `stInit` by `cliIoFileLoopBudgetEvents`
    and returning `ioVecAt A.repAlloc sret (cliIoFileLoopBudgetOut rem)` with `sf.fs = s0.fs`. -/
theorem cliIoReadFile_file_loop_budget [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hA_mem : ∀ st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
      stdMemcpySpec)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 : State} {d0 : FdEntry} {fd sret v0 v1 v2 : BitVec 64}
    {stackBytes : Nat} {stInit : M.σ}
    {post : State → SepProp → Prop}
    (hlo : 8368 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hsp0 : s0.spAligned = true)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds_none : s0.fs.fds fd = none)
    (hkind : d0.kind = .localFile) (hcanr : d0.accMode.canRead = true) (hoff0 : d0.offset = 0)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs →
      sf.trace = s0.trace → sf.sigActions = s0.sigActions →
      sf.tpidrEl0 = s0.tpidrEl0 → sf.brkStart = s0.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          ioVecAt A.repAlloc sret
            (cliIoFileLoopBudgetOut ((s0.fs.fdBytes d0).drop d0.offset)) ∗
          A.pool lim
            (M.stepEvents
              (cliIoFileLoopBudgetEvents ((s0.fs.fdBytes d0).drop d0.offset)) stInit) sf) →
        post sf Pre_f) :
    ∀ (fuel : Nat) (sl : State) (ptr st0 st1 st2 st3 : BitVec 64) (cap len : Nat) (st_cur : M.σ),
      cliIoFileCap + 1 - len ≤ fuel →
      len ≤ min ((s0.fs.fdBytes d0).drop d0.offset).length cliIoFileCap →
      (len < ((s0.fs.fdBytes d0).drop d0.offset).length → 4096 ∣ len) →
      cap = cliIoFinalCap 9 len →
      st_cur = M.stepEvents (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 len)) stInit →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sl.mem →
      sl.pc = cliIoPl03.base + 216#64 → sl.status = .Running → sl.sp = s0.sp - 8320#64 →
      (sl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd → sl.readReg64 (.gpr 20#5) = ptr →
      sl.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 2097152 len) →
      sl.readReg64 (.gpr 24#5) = sret →
      sl.readReg64 (.gpr 25#5) = 4096#64 → sl.readReg64 (.gpr 26#5) = 2097152#64 →
      sl.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sl.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sl = calleeSavedVRegs s0 →
      sl.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + len }) →
      sl.trace = s0.trace → sl.sigActions = s0.sigActions →
      sl.tpidrEl0 = s0.tpidrEl0 → sl.brkStart = s0.brkStart →
      SepWP P (s0.readReg64 .lr) sl
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr
            (((s0.fs.fdBytes d0).drop d0.offset).take len) ∗
          A.pool lim st_cur sl)
        post
        (fun sf_oom =>
          ⌜¬ FitsEvents M lim stInit
              (cliIoFileLoopBudgetEvents ((s0.fs.fdBytes d0).drop d0.offset)) ∧
            CliIoFilesOomPreserved s0 sf_oom⌝) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro sl ptr st0 st1 st2 st3 cap len st_cur
      hfuel hlen_le hdvd hcap_eq hst_eq hcl hpc hrun hsp_eq
      hw19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hx29 hvregs
      hfs_sl htr_sl hsig_sl htp_sl hbs_sl
    let rem := (s0.fs.fdBytes d0).drop d0.offset
    have hrem_def : rem = (s0.fs.fdBytes d0).drop d0.offset := rfl
    let want := wantBytes 2097152 len
    have hwant_def : want = wantBytes 2097152 len := rfl
    have hcap2097 : cliIoFileCap = 2097152 := rfl
    have hlen_max : len ≤ cliIoFileCap := Nat.le_trans hlen_le (Nat.min_le_right _ _)
    have hlen_rem : len ≤ rem.length := Nat.le_trans hlen_le (Nat.min_le_left _ _)
    have hwant_le : want ≤ 4096 := wantBytes_le_4096 2097152 len
    let R_fr : SepProp :=
      memRegion (s0.sp - 8320#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take len)
    refine SepWP.weaken_pre (by dsimp only [R_fr]; sep_entail)
      (cliIoReadFile_do_read_budget A lim hA_mem hext3 hread (R_frame := R_fr) (by dsimp [allocHookStack] at hlo; omega)
        hhi hsp_lo hsp_va hfd_lt hwant_le (by simp only [Arm64.MAX_LFS_FILESIZE, hoff0]; omega)
        hkind hcanr hfs_sl hcl hpc hrun hsp0 hsp_eq
        hw19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hx29 hvregs
        fun sr oldBuf hold_len hpc_sr hrun_sr hsp_sr hx0_sr hw19_sr hx20_sr hx21_sr hx23_sr
            hx24_sr hx25_sr hx26_sr hx28_sr hx29_sr hvregs_sr hcl_sr hfs_sr htr_sr hsig_sr
            htp_sr hbs_sr => ?_)
    dsimp only [R_fr]
    let chunk := (rem.drop len).take want
    have hchunk_def : chunk = (rem.drop len).take want := rfl
    have hn_min : chunk.length = min (rem.length - len) want := by
      rw [hchunk_def, List.length_take, List.length_drop, Nat.min_comm]
    have hn_le_want : chunk.length ≤ want := by rw [hn_min]; exact Nat.min_le_right _ _
    have hn_le_rem : len + chunk.length ≤ rem.length := by rw [hn_min]; omega
    let d_sr : FdEntry := { d0 with offset := d0.offset + (len + chunk.length) }
    have hfds_sr : sr.fs.fds fd = some d_sr := by
      rw [hfs_sr]; simp only [FsState.setFd, beq_self_eq_true, ↓reduceIte]; rfl
    have hkind_sr : d_sr.kind = .localFile ∨ d_sr.kind = .localDir := Or.inl hkind
    rcases Nat.eq_zero_or_pos chunk.length with hn0 | hn_pos
    · have hwant_pos : 0 < want := wantBytes_pos (by omega : len ≤ 2097152)
      have hlen_eq_rem : len = rem.length := by omega
      have hrem_le_cap : rem.length ≤ cliIoFileCap := by omega
      have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
      have htake_rem : rem.take len = rem := by rw [hlen_eq_rem, List.take_length]
      refine SepWP.weaken_pre ?_
        (cliIoReadFile_after_read_eof_budget A lim hA_mem hext3 hclose
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
          (st_cur := st_cur)
          (by dsimp [allocHookStack] at hlo; omega) hhi hfd_lt hfds_sr hkind_sr hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
          (by rw [hx0_sr, ← hchunk_def, hn0]) hw19_sr hx20_sr hx21_sr hx24_sr
          (by rw [hx28_sr, hlen_eq_rem]) hvregs_sr
          fun sf hpc_f hrun_f hsp_f hcs_f _ hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
            hpost sf hpc_f hrun_f hsp_f hcs_f
              (by rw [hfs_f, hfs_sr]; exact setFd_none_setFd_of_fds_none hfds_none)
              (htr_f.trans (htr_sr.trans htr_sl))
              (hsig_f.trans (hsig_sr.trans hsig_sl))
              (htp_f.trans (htp_sr.trans htp_sl))
              (hbs_f.trans (hbs_sr.trans hbs_sl))
              (Entails.trans hent ?_))
      · rw [htake_rem]
        let Rest : SepProp :=
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 8320#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
            cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr rem ∗ A.pool lim st_cur sr
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q := Rest) hbuf_back) (by dsimp only [Rest]; sep_entail))
        rw [← hrem_def, ← hchunk_def,
          pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
        dsimp only [Rest]; sep_entail
      · unfold cliIoFileLoopBudgetOut cliIoFileLoopBudgetEvents
        rw [← hrem_def]
        simp only [hrem_le_cap, ↓reduceIte]
        rw [hst_eq, hlen_eq_rem]
        exact Entails.refl _
    · by_cases hover : cliIoFileCap < len + chunk.length
      · have ⟨hlen_eq, hn_eq1, _⟩ :=
          overCap_forces_eq_max (K := 9) hlen_le hdvd hn_min hn_pos hover
        have hwant_eq1 : want = 1 := by rw [hwant_def, hlen_eq]; rfl
        have hidx9 : cliIoCapIdx 9 len = 9 := by rw [hlen_eq]; exact cliIoCapIdx_cap_self 9
        have hcap9 : cap = cliIoCap 9 := by rw [hcap_eq, cliIoFinalCap_pos (by omega), hidx9]
        have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
        refine SepWP.weaken_pre ?_
          (cliIoReadFile_after_read_overcap_budget A lim hA_mem hext3 hdealloc hclose
            (v0 := v0) (v1 := v1) (v2 := v2)
            (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (bs := rem.take len) (st_in := st_cur)
            (by omega) hhi hfd_lt hfds_sr hkind_sr hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            (by rw [hx0_sr, ← hchunk_def, hn_eq1]) hw19_sr hx20_sr
            (by rw [hx21_sr, hcap9]) (by rw [hx23_sr, hwant_eq1]) hx24_sr hx26_sr
            (by rw [hx28_sr, hlen_eq]; rfl) hvregs_sr
            fun sf hpc_f hrun_f hsp_f hcs_f _ hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
              hpost sf hpc_f hrun_f hsp_f hcs_f
                (by rw [hfs_f, hfs_sr]; exact setFd_none_setFd_of_fds_none hfds_none)
                (htr_f.trans (htr_sr.trans htr_sl))
                (hsig_f.trans (hsig_sr.trans hsig_sl))
                (htp_f.trans (htp_sr.trans htp_sl))
                (hbs_f.trans (hbs_sr.trans hbs_sl))
                (Entails.trans hent ?_))
        · rw [hcap9]
          let Rest : SepProp :=
            stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 8320#64) 4096 ∗
              vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
              cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
              cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap 9)) ptr (rem.take len) ∗
              A.pool lim st_cur sr
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono_left (Q := Rest) hbuf_back) (by dsimp only [Rest]; sep_entail))
          rw [← hrem_def, ← hchunk_def,
            pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
          dsimp only [Rest]; sep_entail
        · unfold cliIoFileLoopBudgetOut cliIoFileLoopBudgetEvents
          have hnot_le : ¬ rem.length ≤ cliIoFileCap := by omega
          rw [← hrem_def]
          simp only [hnot_le, ↓reduceIte]
          rw [hst_eq, stepEvents_dealloc_overCap M stInit hlen_eq]
          exact Entails.refl _
      · have hlen'_max : len + chunk.length ≤ cliIoFileCap := by omega
        have hlen'_le : len + chunk.length ≤ min rem.length cliIoFileCap :=
          Nat.le_min.mpr ⟨hn_le_rem, hlen'_max⟩
        have hdvd' : len + chunk.length < rem.length → 4096 ∣ (len + chunk.length) :=
          dvd_4096_preserved (K := 9) hlen_le hdvd hn_min hn_pos hlen'_max
        have hm_lt : cliIoFileCap + 1 - (len + chunk.length) < fuel := by omega
        by_cases hnogrow : len + chunk.length ≤ cap
        · have hlen_pos : 0 < len := by
            rcases Nat.eq_zero_or_pos len with rfl | hp
            · rw [cliIoFinalCap_zero] at hcap_eq; omega
            · exact hp
          let j := cliIoCapIdx 9 len
          have hj : j ≤ 9 := cliIoCapIdx_le 9 len
          have hcap_j : cap = cliIoCap j := by rw [hcap_eq, cliIoFinalCap_pos hlen_pos]
          have hcap_le_max : cap ≤ 2097152 := by rw [hcap_j]; exact cliIoCap_mono hj
          have hidx_eq : cliIoCapIdx 9 (len + chunk.length) = j :=
            no_grow_capIdx_eq hlen_pos (by omega) (by rwa [← hcap_j])
          have hcap'_eq : cap = cliIoFinalCap 9 (len + chunk.length) := by
            rw [cliIoFinalCap_pos (by omega), hidx_eq, hcap_j]
          have hsched_eq :
              cliIoReadScheduleCaps 9 (len + chunk.length) = cliIoReadScheduleCaps 9 len := by
            rw [cliIoReadScheduleCaps_eq_cliIoReadCaps, cliIoReadScheduleCaps_eq_cliIoReadCaps]
            unfold cliIoReadCaps
            have hne1 : len + chunk.length ≠ 0 := by omega
            have hne0 : len ≠ 0 := by omega
            dsimp only [j] at hidx_eq
            simp only [hne1, hne0, ↓reduceIte, hidx_eq]
          refine cliIoReadFile_after_read_nogrow_vm hext3 hn_pos hn_le_want hwant_le
            hnogrow hcap_le_max hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            hx0_sr hw19_sr hx20_sr hx21_sr hx23_sr hx24_sr hx25_sr hx26_sr hx28_sr hx29_sr hvregs_sr
            fun sc hpc_sc hrun_sc hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc hx24_sc hx25_sc
                hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_srsc hvm_srsc => ?_
          have hpool_srsc : A.pool lim st_cur sr = A.pool lim st_cur sc :=
            (A.pool_transport lim st_cur sr sc hvm_srsc).symm
          refine SepWP.weaken_pre (by rw [hpool_srsc]; sep_entail)
            (cliIoReadFile_memcpy_backedge_budget A lim hext3 hmemcpy
              (R_path := memRegion (s0.sp - 8320#64) 4096)
              (by rw [hcap_j]; exact cliIoCap_pos j) (by rw [hcap_j]; exact cliIoCap_lt_pow63 (by omega))
              hn_le_rem hnogrow hlen'_max hwant_le hold_len hn_le_want rfl
              hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc hx24_sc
              hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc
              fun sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                  hx26_sn hx28_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                ih (cliIoFileCap + 1 - (len + chunk.length)) hm_lt sn ptr st0 st1 st2 st3
                  cap (len + chunk.length) st_cur (Nat.le_refl _)
                  hlen'_le hdvd' hcap'_eq (by rw [hsched_eq]; exact hst_eq)
                  hcl_sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                  hx26_sn hx28_sn hx29_sn hvregs_sn
                  (hmid_scsn.1.trans (hacp_srsc.1.trans hfs_sr))
                  (hmid_scsn.2.1.trans (hacp_srsc.2.1.trans (htr_sr.trans htr_sl)))
                  (hmid_scsn.2.2.1.trans (hacp_srsc.2.2.1.trans (hsig_sr.trans hsig_sl)))
                  (hmid_scsn.2.2.2.1.trans (hacp_srsc.2.2.2.1.trans (htp_sr.trans htp_sl)))
                  (hmid_scsn.2.2.2.2.trans (hacp_srsc.2.2.2.2.1.trans (hbs_sr.trans hbs_sl))))
        · have hgt_cap : cap < len + chunk.length := by omega
          refine cliIoReadFile_after_read_grow_vm hext3 hn_pos hn_le_want hwant_le
            hgt_cap hlen'_max hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            hx0_sr hw19_sr hx20_sr hx21_sr hx23_sr hx24_sr hx25_sr hx26_sr hx28_sr hx29_sr hvregs_sr
            fun sg hpc_sg hrun_sg hsp_sg hx0_sg hw19_sg hx20_sg hx21_sg hx24_sg hx25_sg
                hx26_sg hx27_sg hx28_sg hx29_sg hvregs_sg hcl_sg hacp_srsg hvm_srsg => ?_
          have hpool_srsg : A.pool lim st_cur sr = A.pool lim st_cur sg :=
            (A.pool_transport lim st_cur sr sg hvm_srsg).symm
          have hfs_sg : sg.fs = s0.fs.setFd fd
              (some { d0 with offset := d0.offset + (len + chunk.length) }) :=
            hacp_srsg.1.trans hfs_sr
          have htr_sg : sg.trace = s0.trace := hacp_srsg.2.1.trans (htr_sr.trans htr_sl)
          have hsig_sg : sg.sigActions = s0.sigActions := hacp_srsg.2.2.1.trans (hsig_sr.trans hsig_sl)
          have htp_sg : sg.tpidrEl0 = s0.tpidrEl0 := hacp_srsg.2.2.2.1.trans (htp_sr.trans htp_sl)
          have hbs_sg : sg.brkStart = s0.brkStart := hacp_srsg.2.2.2.2.1.trans (hbs_sr.trans hbs_sl)
          have hoom_pres_sg : ∀ sf_oom : State, OomPreserved sg sf_oom → CliIoFilesOomPreserved s0 sf_oom := by
            intro sf_oom hoom_s
            have hfiles : sf_oom.fs.files = s0.fs.files := by
              rw [hoom_s.1, hfs_sg]; rfl
            exact ⟨hfiles, hoom_s.2.1.trans htr_sg, hoom_s.2.2.trans hsig_sg⟩
          let R_buf : SepProp :=
            memRegion (s0.sp - 8320#64) 4096 ∗
              (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
                memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want))
          rcases Nat.eq_zero_or_pos len with rfl | hlen_pos
          · have hcap0 : cap = 0 := hcap_eq
            subst hcap0
            have hst0 : st_cur = stInit := by
              rw [hst_eq, cliIoReadScheduleCaps_eq_cliIoReadCaps]
              rfl
            have hidx0 : cliIoCapIdx 9 chunk.length = 0 :=
              cliIoCapIdx_eq_of_bounds (Nat.zero_le 9) (Or.inl rfl) (Nat.le_trans hn_le_want hwant_le)
            have hst_next0 :
                M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) stInit =
                  M.stepEvents (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 (0 + chunk.length))) stInit := by
              rw [Nat.zero_add, cliIoReadScheduleCaps_eq_cliIoReadCaps]
              unfold cliIoReadCaps cliIoFinishGrowBudgetEvents
              have hne : chunk.length ≠ 0 := by omega
              simp only [hne, ↓reduceIte, hidx0]
              rfl
            refine SepWP.weaken_pre (by rw [hpool_srsg, hst0]; dsimp only [R_buf]; sep_entail)
              (cliIoReadFile_grow_from_zero_budget A lim hext3 hfg (R_buf := R_buf) (st_in := stInit)
                (by omega) hhi hn_pos (Nat.le_trans hn_le_want hwant_le)
                hcl_sg hpc_sg hrun_sg hsp0 hsp_sg
                hx0_sg hw19_sg hx20_sg hx21_sg hx24_sg hx25_sg hx26_sg
                (by rw [Nat.zero_add] at hx27_sg; exact hx27_sg) hx28_sg hx29_sg hvregs_sg
                (fun sf_oom hnf hoom_s =>
                  Entails.pure_right_only
                    ⟨not_fitsEvents_loop_of_grow_zero (by omega : 0 < rem.length) hnf,
                      hoom_pres_sg sf_oom hoom_s⟩
                    (Entails.refl _))
                fun sc newPtr st1' st2' hpc_sc hrun_sc hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc
                    hx24_sc hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_sgsc =>
                  SepWP.weaken_pre (by dsimp only [R_buf]; sep_entail)
                    (cliIoReadFile_memcpy_backedge_budget A lim hext3 hmemcpy
                      (R_path := memRegion (s0.sp - 8320#64) 4096)
                      (cliIoCap_pos 0) (cliIoCap_lt_pow63 (by decide))
                      hn_le_rem (Nat.le_trans (by rw [Nat.zero_add]; exact hn_le_want) hwant_le)
                      hlen'_max hwant_le hold_len hn_le_want rfl
                      hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc hx24_sc
                      hx25_sc hx26_sc (by rw [Nat.zero_add]; exact hx27_sc) hx28_sc hx29_sc hvregs_sc
                      fun sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                          hx26_sn hx28_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                        ih (cliIoFileCap + 1 - (0 + chunk.length)) hm_lt sn newPtr 0#64 st1' st2' st3
                          (cliIoCap 0) (0 + chunk.length)
                          (M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) stInit)
                          (Nat.le_refl _) hlen'_le hdvd'
                          (by simp [cliIoFinalCap_pos hn_pos, hidx0]) hst_next0
                          hcl_sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn
                          hx25_sn hx26_sn hx28_sn hx29_sn hvregs_sn
                          (hmid_scsn.1.trans (hacp_sgsc.1.trans hfs_sg))
                          (hmid_scsn.2.1.trans (hacp_sgsc.2.1.trans htr_sg))
                          (hmid_scsn.2.2.1.trans (hacp_sgsc.2.2.1.trans hsig_sg))
                          (hmid_scsn.2.2.2.1.trans (hacp_sgsc.2.2.2.1.trans htp_sg))
                          (hmid_scsn.2.2.2.2.trans (hacp_sgsc.2.2.2.2.1.trans hbs_sg))))
          · let j := cliIoCapIdx 9 len
            have hj : j ≤ 9 := cliIoCapIdx_le 9 len
            have hcap_j : cap = cliIoCap j := by rw [hcap_eq, cliIoFinalCap_pos hlen_pos]
            have hlen_le_j : len ≤ cliIoCap j := le_cliIoCap_cliIoCapIdx hlen_max
            have ⟨hj1, _, hidx_j1, hle_j1, _⟩ :=
              grow_step_bounds (K := 9) (by decide) hj hlen_le_j
                (Nat.le_trans hn_le_want hwant_le) hn_le_rem hlen'_max (by rwa [← hcap_j])
            have hcap_lt64 : cliIoCap j < 2 ^ 64 := cliIoCap_lt_pow64 hj
            have hcap_ne0 : BitVec.ofNat 64 (cliIoCap j) ≠ 0#64 :=
              beq_eq_false_iff_ne.mp
                (bv64_beq_ofNat_false (by have := cliIoCap_pos j; omega) hcap_lt64 (by decide))
            have hcap_toNat : (BitVec.ofNat 64 (cliIoCap j)).toNat = cliIoCap j := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64]
            have hst_next_pos :
                M.stepEvents
                    (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1))) st_cur =
                  M.stepEvents
                    (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 (len + chunk.length))) stInit := by
              rw [hst_eq, ← M.stepEvents_append, cliIoReadScheduleCaps_eq_cliIoReadCaps,
                cliIoReadScheduleCaps_eq_cliIoReadCaps]
              unfold cliIoReadCaps cliIoFinishGrowBudgetEvents
              have hne1 : len + chunk.length ≠ 0 := by omega
              have hne0 : len ≠ 0 := by omega
              have hj_def : cliIoCapIdx 9 len = j := rfl
              simp only [hne1, hne0, ↓reduceIte, hidx_j1, hj_def, hcap_ne0, hcap_toNat]
              rw [show j + 1 + 1 = j + 2 by omega, cliIoCapsEvents_range_succ' j]
            refine SepWP.weaken_pre (by rw [hpool_srsg, hcap_j]; dsimp only [R_buf]; sep_entail)
              (cliIoReadFile_grow_from_pos_budget A lim hext3 hfg (R_buf := R_buf) (st_in := st_cur)
                (by omega) hhi hj1 hlen_le_j
                (List.length_take_of_le hlen_rem) (by rwa [← hcap_j]) hle_j1
                hcl_sg hpc_sg hrun_sg hsp0 hsp_sg
                hx0_sg hw19_sg hx20_sg (by rw [hx21_sg, hcap_j]) hx24_sg hx25_sg
                hx26_sg hx27_sg hx28_sg hx29_sg hvregs_sg
                (fun sf_oom hnf hoom_s =>
                  Entails.pure_right_only
                    ⟨not_fitsEvents_loop_of_grow_pos hlen_pos rfl hj1 hn_le_rem hidx_j1
                      (hst_eq ▸ hnf),
                      hoom_pres_sg sf_oom hoom_s⟩
                    (Entails.refl _))
                fun sc newPtr st1' st2' hpc_sc hrun_sc hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc
                    hx24_sc hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_sgsc =>
                  SepWP.weaken_pre (by dsimp only [R_buf]; sep_entail)
                    (cliIoReadFile_memcpy_backedge_budget A lim hext3 hmemcpy
                      (R_path := memRegion (s0.sp - 8320#64) 4096)
                      (cliIoCap_pos (j + 1)) (cliIoCap_lt_pow63 (by omega))
                      hn_le_rem hle_j1 hlen'_max hwant_le hold_len hn_le_want rfl
                      hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc hx24_sc
                      hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc
                      fun sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                          hx26_sn hx28_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                        ih (cliIoFileCap + 1 - (len + chunk.length)) hm_lt sn newPtr 0#64 st1' st2' st3
                          (cliIoCap (j + 1)) (len + chunk.length)
                          (M.stepEvents
                            (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1)))
                            st_cur)
                          (Nat.le_refl _) hlen'_le hdvd'
                          (by rw [cliIoFinalCap_pos (by omega), hidx_j1]) hst_next_pos
                          hcl_sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn
                          hx25_sn hx26_sn hx28_sn hx29_sn hvregs_sn
                          (hmid_scsn.1.trans (hacp_sgsc.1.trans hfs_sg))
                          (hmid_scsn.2.1.trans (hacp_sgsc.2.1.trans htr_sg))
                          (hmid_scsn.2.2.1.trans (hacp_sgsc.2.2.1.trans hsig_sg))
                          (hmid_scsn.2.2.2.1.trans (hacp_sgsc.2.2.2.1.trans htp_sg))
                          (hmid_scsn.2.2.2.2.trans (hacp_sgsc.2.2.2.2.1.trans hbs_sg))))

end

/-! ## Read-Only Block Subset `{0, 3, 4}` (`CliIoReadsCodeLoaded`) Variants -/

section
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  cliIoReadsKeep CliIoReadsCodeLoaded sepWP_seg_cliIo_block_pure_reads
)
open VerifiedLibraries.RustStd (seqCodeLoadedWhere)
arm64_proof_prelude

theorem cliIoReadFile_ret_epilogue_vm_reads [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    {P_pool : State → SepProp}
    (hP_vm : ∀ {s s' : State}, VmMemPreserved s s' → P_pool s' = P_pool s)
    {s0 se : State} {st0 st1 st2 st3 : BitVec 64}
    {R_out : SepProp} {stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl : CliIoReadsCodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 520#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      AllocCallPreserved se sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ R_out ∗ P_pool sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        R_out ∗
        P_pool se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 520#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 8320#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  wp_conv_pre => dsimp only [cliIoSavedRegs12]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
  have hcpu_f := hcpu_f0.1
  have ⟨hacp_ef, hvm_ef⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f hsym_f
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : P_pool se = P_pool sf := (hP_vm hvm_ef.toVmMemPreserved).symm
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
  have hstk_back := cliIoReadFile_stack_refold s0 hlo hhi st0 st1 st2 st3
  dsimp only [cliIoSavedRegs12] at hstk_back
  rw [hpool_eq]
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_left (Q := R_out ∗ P_pool sf) hstk_back) (by sep_entail))
  sep_entail

/-- Unconditional `close(w19)` + stack-restore + `ret` epilogue (`+0x1f4 = 500#64 .. +0x228 = 552#64`)
    parametric in any `VmPreserved`-invariant pool assertion `P_pool`. -/
theorem cliIoReadFile_close_epilogue_vm_reads [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {P_pool : State → SepProp}
    (hP_vm : ∀ {s s' : State}, VmMemPreserved s s' → P_pool s' = P_pool s)
    {s0 se : State} {fd : BitVec 64} {desc : FdEntry} {st0 st1 st2 st3 : BitVec 64}
    {R_out : SepProp} {stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : se.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : CliIoReadsCodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 500#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hw19 : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      sf.fs = se.fs.setFd fd none →
      sf.trace = se.trace → sf.sigActions = se.sigActions →
      sf.tpidrEl0 = se.tpidrEl0 → sf.brkStart = se.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ R_out ∗ P_pool sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        R_out ∗
        P_pool se)
      post oomProp := by
  have h48_le : 48 ≤ stackBytes - 8320 := by omega
  have hsb_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 48 h48_le hsb_hi]
    simp only [sepConj_assoc]
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 500#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  wp_sym_steps
  refine SepWP.done cliIoReadFile_close_pc (by simpa [arm64_norm] using hrun_e')
    fun sm_cl hcpu_cl0 hcl_cl hnsp_cl hsym_cl => ?_
  have hcpu_cl := hcpu_cl0.1
  have ⟨hacp_ecl, hvm_ecl⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_cl0 hnsp_cl hsym_cl
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ecl : P_pool se = P_pool sm_cl := (hP_vm hvm_ecl.toVmMemPreserved).symm
  have hpc_cl : sm_cl.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym :=
    hcpu_cl.pc_eq.trans cliIoReadFile_close_pc
  have hrun_cl : sm_cl.status = .Running := hcpu_cl.status_eq.trans hrun_e'
  have hsp_cl_eq : sm_cl.sp = s0.sp - 8320#64 :=
    hcpu_cl.sp_eq.trans ((by simp [arm64_norm] : _ = se'.sp).trans (hcpu_e.sp_eq.trans hsp_eq))
  have hsp_cl : sm_cl.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_cl_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_cl : sm_cl.readReg64 .lr = cliIoPl03.base + 508#64 := by
    rw [hcpu_cl.readReg64 .lr]; simp [arm64_norm]
  have hx0_cl : (sm_cl.readReg32 .x0).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_cl.readReg64 .x0)]
    simp only [arm64_norm]
    rw [hcpu_e.readReg64 (.gpr 19#5)]
    exact hw19
  have hfds_cl : sm_cl.fs.fds fd = some desc := by rw [hacp_ecl.1]; exact hfds
  let T_cl : SepProp :=
    memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 48) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗
      memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗
      R_out ∗
      P_pool sm_cl
  apply seqCodeLoadedWhere hcl_cl (mid := cliIoPl03.base + 508#64)
  apply (SepWP.call_subroutine_frame hclose (F := T_cl) (x := (fd, desc))
    hpc_cl hrun_cl hsp_cl hlr_cl
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslClose48LocalSpec, T_cl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_cl, hfd_lt, hfds_cl, hkind⟩, ?_⟩
    rw [hpool_eq_ecl] at hm'
    rw [hsp_cl_eq]
    exact Satisfies.mono (by sep_frame) hm'
  · intro sm_cl' hpc_cl' hrun_cl' hsp_cl' hcs_cl'
    refine SepWP.done hpc_cl' hrun_cl' fun hcl_cl' => ?_
    wp_conv_pre => dsimp only [muslClose48LocalSpec, T_cl]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hfs_cl', htr_cl', hsys_cl'⟩
    have hpool_eq_cl' : P_pool sm_cl = P_pool sm_cl' :=
      (hP_vm (vmMemPreserved_of_syscallPreserved hsys_cl')).symm
    have hsp_cl'_eq : sm_cl'.sp = s0.sp - 8320#64 := hsp_cl'.trans hsp_cl_eq
    have hvregs_cl' : calleeSavedVRegs sm_cl' = calleeSavedVRegs s0 :=
      hcs_cl'.vregs.trans (hcpu_cl.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs)))
    apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl_cl'
      (mid := cliIoPl03.base + 520#64)
    intro sb' hcpu_b0
    have hcpu_b := hcpu_b0.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc_b' : sb'.pc = cliIoPl03.base + 508#64 := hcpu_b.pc_eq.trans hpc_cl'
    have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_cl'
    have hsp_b' : sb'.spAligned = true := by
      rw [hcpu_b.spAligned]; simp only [State.spAligned]; rw [hsp_cl'_eq]
      exact s0.spAligned_sub 8320#64 hsp0
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
      fun sr_ret hcpu_r0 hcl_r hnsp_r hsym_r => ?_
    have hcpu_r := hcpu_r0.1
    have ⟨hacp_br, hvm_br⟩ :=
      vmPreserved_of_seg hcpu_b0 hcpu_r0 hnsp_r hsym_r
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_br : P_pool sm_cl' = P_pool sr_ret := (hP_vm hvm_br.toVmMemPreserved).symm
    have hsp_r : sr_ret.sp = s0.sp - 8320#64 :=
      hcpu_r.sp_eq.trans ((by simp [arm64_norm] : _ = sb'.sp).trans (hcpu_b.sp_eq.trans hsp_cl'_eq))
    have hvregs_r : calleeSavedVRegs sr_ret = calleeSavedVRegs s0 :=
      hcpu_r.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
        (hcpu_b.calleeSavedVRegs.trans hvregs_cl'))
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_ret_epilogue_vm_reads hext3 hP_vm (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
        (R_out := R_out)
        (by omega) hhi hcl_r (hcpu_r.pc_eq.trans (by simp [arm64_norm]))
        (hcpu_r.status_eq.trans hrun_b') hsp0 hsp_r hvregs_r
        fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_rf _ hent =>
          hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
            (hacp_rf.1.trans (hacp_br.1.trans (hfs_cl'.trans (congrArg (fun f => f.setFd fd none) hacp_ecl.1))))
            (hacp_rf.2.1.trans (hacp_br.2.1.trans (htr_cl'.trans hacp_ecl.2.1)))
            (hacp_rf.2.2.1.trans (hacp_br.2.2.1.trans (hsys_cl'.2.1.trans hacp_ecl.2.2.1)))
            (hacp_rf.2.2.2.1.trans (hacp_br.2.2.2.1.trans (hsys_cl'.1.trans hacp_ecl.2.2.2.1)))
            (hacp_rf.2.2.2.2.1.trans (hacp_br.2.2.2.2.1.trans (hsys_cl'.2.2.brkStart_eq.trans hacp_ecl.2.2.2.2.1)))
            hent)
    rw [hpool_eq_cl', hpool_eq_br, hsp_cl_eq,
      stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 48 h48_le hsb_hi]
    sep_entail

/-- `Err(())` epilogue when `cap = 0` (`+0x1d4 = 468#64 → +0x1f4 = 500#64 → ret`),
    parametric in `P_pool` and arbitrary frame `R_extra` (`cbz x22, 0x1f4` skips `__rust_dealloc`). -/
theorem cliIoReadFile_err_cap0_epilogue_vm_reads [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {P_pool : State → SepProp}
    (hP_vm : ∀ {s s' : State}, VmMemPreserved s s' → P_pool s' = P_pool s)
    {s0 se : State} {fd sret v0 v1 v2 st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {R_extra : SepProp} {stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : se.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : CliIoReadsCodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 468#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hw19 : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx21 : se.readReg64 (.gpr 21#5) = 0#64)
    (hx24 : se.readReg64 (.gpr 24#5) = sret)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      sf.fs = se.fs.setFd fd none →
      sf.trace = se.trace → sf.sigActions = se.sigActions →
      sf.tpidrEl0 = se.tpidrEl0 → sf.brkStart = se.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          (((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗ R_extra) ∗
          P_pool sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        R_extra ∗
        P_pool se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 500#64)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 468#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx21_e' : se'.readReg64 (.gpr 21#5) = 0#64 := (hcpu_e.readReg64 _).trans hx21
  have hx24_e' : se'.readReg64 (.gpr 24#5) = sret := (hcpu_e.readReg64 _).trans hx24
  wp_conv_pre =>
    rw [show vecHeader sret v0 v1 v2 =
      (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sc_cl hcpu_c0 hcl_c hnsp_c hsym_c => ?_
  have hcpu_c := hcpu_c0.1
  have ⟨hacp_ec, hvm_ec⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_c0 hnsp_c hsym_c
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ec : P_pool se = P_pool sc_cl := (hP_vm hvm_ec.toVmMemPreserved).symm
  have hw19_c : (sc_cl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_c.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_e.readReg64 (.gpr 19#5)]
    exact hw19
  have herr_sret := vecHeader_to_err_sret sret v1 v2
  dsimp only [vecHeader] at herr_sret
  refine SepWP.weaken_pre ?_
    (cliIoReadFile_close_epilogue_vm_reads hext3 hclose hP_vm
      (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
      (R_out := ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗ R_extra)
      hlo hhi hfd_lt (by rw [hacp_ec.1]; exact hfds) hkind hcl_c
      (hcpu_c.pc_eq.trans (by simp [arm64_norm])) (hcpu_c.status_eq.trans hrun_e') hsp0
      (hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = se'.sp).trans (hcpu_e.sp_eq.trans hsp_eq)))
      hw19_c
      (hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
        (hcpu_e.calleeSavedVRegs.trans hvregs)))
      fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
        hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
          (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_ec.1))
          (htr_f.trans hacp_ec.2.1) (hsig_f.trans hacp_ec.2.2.1)
          (htp_f.trans hacp_ec.2.2.2.1) (hbs_f.trans hacp_ec.2.2.2.2.1) hent)
  rw [hpool_eq_ec]
  let Rest : SepProp :=
    stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 8320#64) 4096 ∗
      memRegion (s0.sp - 4224#64) 4096 ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗ R_extra ∗ P_pool sc_cl
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_left (Q := Rest) herr_sret) (by dsimp only [Rest]; sep_entail))
  dsimp only [Rest]; sep_entail

/-! ## 3. Budget-Threaded `.localFile` Epilogues & Growth Steps (Zero `StdErrnoCell`) -/

/-- `Ok(bs)` epilogue (`+0x1c8 = 456#64 → +0x1f4 = 500#64 → ret`) over `A.pool lim st_cur`. -/
theorem cliIoReadFile_ok_epilogue_budget_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hA_mem : ∀ st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 se : State} {fd sret v0 v1 v2 cap ptr st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {bs : List (BitVec 8)} {stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : se.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : CliIoReadsCodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 456#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hw19 : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : se.readReg64 (.gpr 20#5) = ptr)
    (hx21 : se.readReg64 (.gpr 21#5) = cap)
    (hx24 : se.readReg64 (.gpr 24#5) = sret)
    (hx28 : se.readReg64 (.gpr 28#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      sf.fs = se.fs.setFd fd none →
      sf.trace = se.trace → sf.sigActions = se.sigActions →
      sf.tpidrEl0 = se.tpidrEl0 → sf.brkStart = se.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.ok bs) ∗
          A.pool lim st_cur sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc cap ptr bs ∗
        A.pool lim st_cur se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 500#64)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 456#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx20_e' : se'.readReg64 (.gpr 20#5) = ptr := (hcpu_e.readReg64 _).trans hx20
  have hx21_e' : se'.readReg64 (.gpr 21#5) = cap := (hcpu_e.readReg64 _).trans hx21
  have hx24_e' : se'.readReg64 (.gpr 24#5) = sret := (hcpu_e.readReg64 _).trans hx24
  have hx28_e' : se'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 bs.length :=
    (hcpu_e.readReg64 _).trans hx28
  wp_conv_pre =>
    rw [show vecHeader sret v0 v1 v2 =
      (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sc_cl hcpu_c0 hcl_c hnsp_c hsym_c => ?_
  have hcpu_c := hcpu_c0.1
  have ⟨hacp_ec, hvm_ec⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_c0 hnsp_c hsym_c
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ec : A.pool lim st_cur se = A.pool lim st_cur sc_cl :=
    (A.pool_transport lim st_cur se sc_cl hvm_ec).symm
  have hw19_c : (sc_cl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_c.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_e.readReg64 (.gpr 19#5)]
    exact hw19
  have hvec_ok := vecHeader_cliIoVecBuf_entails_ioVecAt_ok A.repAlloc sret cap ptr bs
  dsimp only [vecHeader] at hvec_ok
  refine SepWP.weaken_pre ?_
    (cliIoReadFile_close_epilogue_vm_reads hext3 hclose
      (P_pool := A.pool lim st_cur) (fun h => hA_mem st_cur h)
      (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
      (R_out := ioVecAt A.repAlloc sret (.ok bs))
      hlo hhi hfd_lt (by rw [hacp_ec.1]; exact hfds) hkind hcl_c
      (hcpu_c.pc_eq.trans (by simp [arm64_norm])) (hcpu_c.status_eq.trans hrun_e') hsp0
      (hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = se'.sp).trans (hcpu_e.sp_eq.trans hsp_eq)))
      hw19_c
      (hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
        (hcpu_e.calleeSavedVRegs.trans hvregs)))
      fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
        hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
          (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_ec.1))
          (htr_f.trans hacp_ec.2.1) (hsig_f.trans hacp_ec.2.2.1)
          (htp_f.trans hacp_ec.2.2.2.1) (hbs_f.trans hacp_ec.2.2.2.2.1) hent)
  rw [hpool_eq_ec]
  let Rest : SepProp :=
    stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 8320#64) 4096 ∗
      memRegion (s0.sp - 4224#64) 4096 ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗ A.pool lim st_cur sc_cl
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_left (Q := Rest) hvec_ok) (by dsimp only [Rest]; sep_entail))
  dsimp only [Rest]; sep_entail

/-- Over-cap `Err(())` epilogue (`+0x1d4 = 468#64 → bl __rust_dealloc → close → ret`),
    stepping `st_in` by `rustDeallocEvents cap 1` before `close(w19)`. -/
theorem cliIoReadFile_err_dealloc_epilogue_budget_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hA_mem : ∀ st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 se : State} {fd sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {bs : List (BitVec 8)} {cap stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcap_pos : 0 < cap) (hcap_lt63 : cap < 2 ^ 63)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : se.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : CliIoReadsCodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 468#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hw19 : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : se.readReg64 (.gpr 20#5) = ptr)
    (hx21 : se.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx24 : se.readReg64 (.gpr 24#5) = sret)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      sf.fs = se.fs.setFd fd none →
      sf.trace = se.trace → sf.sigActions = se.sigActions →
      sf.tpidrEl0 = se.tpidrEl0 → sf.brkStart = se.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.error ()) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents cap 1) st_in) sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr bs ∗
        A.pool lim st_in se)
      post oomProp := by
  have hlo8368 : 8368 ≤ stackBytes := by dsimp [allocHookStack] at hlo; omega
  have hhk_le : allocHookStack ≤ stackBytes - 8320 := by omega
  have hsb_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
  have hcap_lt64 : cap < 2 ^ 64 := Nat.lt_trans hcap_lt63 (by decide)
  have hcap_beq0 : (BitVec.ofNat 64 cap == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) hcap_lt64 (by decide)
  have hcap_toNat : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64]
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) allocHookStack hhk_le hsb_hi]
    simp only [sepConj_assoc]
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 468#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx20_e' : se'.readReg64 (.gpr 20#5) = ptr := (hcpu_e.readReg64 _).trans hx20
  have hx21_e' : se'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_e.readReg64 _).trans hx21
  have hx24_e' : se'.readReg64 (.gpr 24#5) = sret := (hcpu_e.readReg64 _).trans hx24
  wp_conv_pre =>
    rw [show vecHeader sret v0 v1 v2 =
      (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done cliIoReadFile_dealloc_pc (by simpa [arm64_norm] using hrun_e')
    fun sm_dl hcpu_dl0 hcl_dl hnsp_dl hsym_dl => ?_
  have hcpu_dl := hcpu_dl0.1
  have ⟨hacp_edl, hvm_edl⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_dl0 hnsp_dl hsym_dl
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_edl : A.pool lim st_in se = A.pool lim st_in sm_dl :=
    (A.pool_transport lim st_in se sm_dl hvm_edl).symm
  have hpc_dl : sm_dl.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym :=
    hcpu_dl.pc_eq.trans cliIoReadFile_dealloc_pc
  have hrun_dl : sm_dl.status = .Running := hcpu_dl.status_eq.trans hrun_e'
  have hsp_dl_eq : sm_dl.sp = s0.sp - 8320#64 :=
    hcpu_dl.sp_eq.trans ((by simp [arm64_norm] : _ = se'.sp).trans (hcpu_e.sp_eq.trans hsp_eq))
  have hsp_dl : sm_dl.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_dl_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_dl : sm_dl.readReg64 .lr = cliIoPl03.base + 500#64 := by
    rw [hcpu_dl.readReg64 .lr]; simp [arm64_norm]
  have hx0_dl : sm_dl.readReg64 .x0 = ptr :=
    (hcpu_dl.readReg64 .x0).trans (by simp [arm64_norm])
  have hx1_dl : (sm_dl.readReg64 .x1).toNat = cap := by
    rw [hcpu_dl.readReg64 .x1]; simpa [arm64_norm] using hcap_toNat
  have hx2_dl : (sm_dl.readReg64 .x2).toNat = 1 := by
    rw [hcpu_dl.readReg64 .x2]; simp [arm64_norm]
  have herr_sret :
      ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2)) ⊢
        ioVecAt A.repAlloc sret (.error ()) :=
    vecHeader_to_err_sret sret v1 v2
  have hde_mem :
      cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr bs ⊢ A.live ptr cap 1 ∗ memRegion ptr cap :=
    cliIoVecBuf_entails_dealloc_mem A.repAlloc (ptr := ptr) (bs := bs) hcap_pos hcap_lt63
  let T_dl : SepProp :=
    memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320))
        (stackBytes - 8320 - allocHookStack) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗
      memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗
      ioVecAt A.repAlloc sret (.error ())
  apply seqCodeLoadedWhere hcl_dl (mid := cliIoPl03.base + 500#64)
  apply (SepWP.call_subroutine_frame (F := T_dl) hdealloc
    (x := (ptr, cap, 1, st_in))
    hpc_dl hrun_dl hsp_dl hlr_dl
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [rustCliDeallocBudgetSpecBase, T_dl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_dl, hx1_dl, hx2_dl⟩, ?_⟩
    refine Satisfies.mono ?_ hm'
    rw [hpool_eq_edl, hsp_dl_eq]
    let Rest : SepProp :=
      memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320))
          (stackBytes - 8320 - allocHookStack) ∗
        stackAt (s0.sp - 8320#64) allocHookStack ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        A.pool lim st_in sm_dl ∗ R'
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := Rest) (sepConj_mono herr_sret hde_mem))
        (by dsimp only [Rest]; sep_entail))
    dsimp only [Rest]; sep_entail
  · intro sm_dl' hpc_dl' hrun_dl' hsp_dl' hcs_dl'
    refine SepWP.done hpc_dl' hrun_dl' fun hcl_dl' => ?_
    wp_conv_pre => dsimp only [rustCliDeallocBudgetSpecBase, T_dl]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hacp_dl', _⟩
    have hsp_dl'_eq : sm_dl'.sp = s0.sp - 8320#64 := hsp_dl'.trans hsp_dl_eq
    have hw19_dl' : (sm_dl'.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
      rw [readReg32_of_readReg64_eq hcs_dl'.readReg64_x19,
        readReg32_of_readReg64_eq (hcpu_dl.readReg64 (.gpr 19#5))]
      simp only [arm64_norm]
      rw [hcpu_e.readReg64 (.gpr 19#5)]
      exact hw19
    have hvregs_dl' : calleeSavedVRegs sm_dl' = calleeSavedVRegs s0 :=
      hcs_dl'.vregs.trans (hcpu_dl.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs)))
    have hacp_edl' : AllocCallPreserved se sm_dl' := allocCallPreserved_trans hacp_edl hacp_dl'
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_close_epilogue_vm_reads hext3 hclose
        (P_pool := A.pool lim (M.stepEvents (rustDeallocEvents cap 1) st_in))
        (fun h => hA_mem _ h)
        (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
        (R_out := ioVecAt A.repAlloc sret (.error ()))
        hlo8368 hhi hfd_lt (by rw [hacp_edl'.1]; exact hfds) hkind hcl_dl'
        hpc_dl' hrun_dl' hsp0 hsp_dl'_eq hw19_dl' hvregs_dl'
        fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
          hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
            (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_edl'.1))
            (htr_f.trans hacp_edl'.2.1) (hsig_f.trans hacp_edl'.2.2.1)
            (htp_f.trans hacp_edl'.2.2.2.1) (hbs_f.trans hacp_edl'.2.2.2.2.1) hent)
    rw [hsp_dl_eq,
      stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) allocHookStack hhk_le hsb_hi]
    sep_entail

/-- Shared `finish_grow` call + `+0x1b4 .. +0x1c4 → +0x15c = 348#64` join over `A.pool lim st_in`. -/
theorem cliIoReadFile_post_grow_budget_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    {s0 sm_fg : State} {fd sret v0 v1 v2 oldCap oldPtr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {R_buf : SepProp}
    {newCap len n stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8352 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hnew_pos : 0 < newCap) (hnew_lt63 : newCap < 2 ^ 63)
    (hbs_le : bs.length ≤ newCap) (hno_null : ¬ NullAllowed newCap 1)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sm_fg.mem)
    (hpc : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
    (hrun : sm_fg.status = .Running) (hsp0 : s0.spAligned = true)
    (hsp_eq : sm_fg.sp = s0.sp - 8320#64) (hlr : sm_fg.readReg64 .lr = cliIoPl03.base + 436#64)
    (hx0 : sm_fg.readReg64 .x0 = s0.sp - 128#64)
    (hx1 : sm_fg.readReg64 .x1 = oldCap) (hx2 : sm_fg.readReg64 .x2 = oldPtr)
    (hx3 : sm_fg.readReg64 .x3 = BitVec.ofNat 64 newCap)
    (hw19 : (sm_fg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx22 : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap)
    (hx23 : sm_fg.readReg64 .x23 = BitVec.ofNat 64 n)
    (hx24 : sm_fg.readReg64 (.gpr 24#5) = sret)
    (hx25 : sm_fg.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sm_fg.readReg64 (.gpr 26#5) = 2097152#64)
    (hx27 : sm_fg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n))
    (hx28 : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sm_fg = calleeSavedVRegs s0)
    (hoom_fg : ∀ sf_oom : State,
      ¬ FitsEvents M lim st_in (cliIoFinishGrowBudgetEvents oldCap newCap) →
      OomPreserved sm_fg sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl03.base + 348#64 → sc.status = .Running → sc.sp = s0.sp - 8320#64 →
      (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = sret →
      sc.readReg64 (.gpr 25#5) = 4096#64 → sc.readReg64 (.gpr 26#5) = 2097152#64 →
      sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sc.mem → AllocCallPreserved sm_fg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 newCap) newPtr bs ∗
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st_in) sc)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sm_fg
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ cliIoVecBuf A.repAlloc oldCap oldPtr bs ∗
        A.pool lim st_in sm_fg)
      post oomProp := by
  have hnew_lt64 : newCap < 2 ^ 64 := Nat.lt_trans hnew_lt63 (by decide)
  have hsp_fg : sm_fg.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hfg_stk_le : 32 + allocHookStack ≤ stackBytes - 8320 := by
    dsimp [allocHookStack] at *; omega
  have hfg_stk_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) (32 + allocHookStack)
      hfg_stk_le hfg_stk_hi]
  apply seqCodeLoadedWhere hcl (mid := cliIoPl03.base + 436#64)
  apply (SepWP.call_subroutine_frame hfg
    (x := (s0.sp - 128#64, st0, st1, st2, oldCap, oldPtr, bs, newCap, st_in))
    hpc hrun hsp_fg hlr
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun R_oom sf_oom _ hm_oom => by
      have hm' := Satisfies.drop_mid hm_oom
      dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoFinishGrowBudgetSpec] at hm'
      rcases (satisfies_pure_sepConj _ _ _).mp hm' with ⟨⟨_, hnf, hoom_s⟩, hm_r⟩
      have hent := hoom_fg sf_oom hnf hoom_s
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
      have hsp_fg'_eq : sm_fg'.sp = s0.sp - 8320#64 := hsp_fg'.trans hsp_eq
      have hx29_fg' : sm_fg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 :=
        hcs_fg'.readReg64_x29.trans hx29
      apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl_fg'
        (mid := cliIoPl03.base + 348#64)
      intro sj' hcpu_j0
      have hcpu_j := hcpu_j0.1
      change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
      have hpc_j' : sj'.pc = cliIoPl03.base + 436#64 := hcpu_j.pc_eq.trans hpc_fg'
      have hrun_j' : sj'.status = .Running := hcpu_j.status_eq.trans hrun_fg'
      have hsp_j' : sj'.spAligned = true := by
        rw [hcpu_j.spAligned]; simp only [State.spAligned]; rw [hsp_fg'_eq]
        exact s0.spAligned_sub 8320#64 hsp0
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
      have hpc_c : sc.pc = cliIoPl03.base + 348#64 := hcpu_c.pc_eq.trans (by simp [arm64_norm])
      have hrun_c : sc.status = .Running := hcpu_c.status_eq.trans hrun_j'
      have hsp_c : sc.sp = s0.sp - 8320#64 :=
        hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = sj'.sp).trans (hcpu_j.sp_eq.trans hsp_fg'_eq))
      have hw19_c : (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
        rw [readReg32_of_readReg64_eq (hcpu_c.readReg64 (.gpr 19#5))]
        simp only [arm64_norm]
        rw [hcpu_j.readReg64 (.gpr 19#5), hcs_fg'.readReg64_x19]
        exact hw19
      have hx20_c : sc.readReg64 (.gpr 20#5) = newPtr := by
        rw [hcpu_c.readReg64]; simp [arm64_norm]
      have hx22_c : sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x22.trans hx22)
      have hx23_c : sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x23.trans hx23)
      have hx24_c : sc.readReg64 (.gpr 24#5) = sret := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x24.trans hx24)
      have hx25_c : sc.readReg64 (.gpr 25#5) = 4096#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x25.trans hx25)
      have hx26_c : sc.readReg64 (.gpr 26#5) = 2097152#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x26.trans hx26)
      have hx27_c : sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x27.trans hx27)
      have hx28_c : sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x28.trans hx28)
      have hx29_c : sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
        rw [hcpu_c.readReg64]; simp [arm64_norm, hx29_j']
      have hvregs_c : calleeSavedVRegs sc = calleeSavedVRegs s0 :=
        hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sj').trans
          (hcpu_j.calleeSavedVRegs.trans (hcs_fg'.vregs.trans hvregs)))
      have hacp_all : AllocCallPreserved sm_fg sc := allocCallPreserved_trans hacp_fg hacp_jc
      refine SepWP.weaken_pre ?_
        (hcont sc newPtr newPtr (BitVec.ofNat 64 newCap)
          hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c hx25_c hx26_c hx27_c hx28_c hx29_c
          hvregs_c hcl_c hacp_all)
      rw [hpool_eq_jc, hsp_eq,
        stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) (32 + allocHookStack)
          hfg_stk_le hfg_stk_hi,
        show ((s0.sp - 128#64) ↦₆₄ 0#64) ∗ ((s0.sp - 120#64) ↦₆₄ newPtr) ∗
            ((s0.sp - 112#64) ↦₆₄ BitVec.ofNat 64 newCap) =
          vecHeader (s0.sp - 128#64) 0#64 newPtr (BitVec.ofNat 64 newCap) by
            simp only [vecHeader, bv_lin_norm]]
      sep_entail

/-- `cap = 0` growth branch (`+0x124 = 292#64 .. +0x1b0` → `post_grow_budget` → `+0x15c = 348#64`). -/
theorem cliIoReadFile_grow_from_zero_budget_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    {s0 sg : State} {fd sret v0 v1 v2 oldPtr st0 st1 st2 st3 : BitVec 64}
    {R_buf : SepProp} {n stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8352 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (_hn_pos : 0 < n) (hn_le : n ≤ 4096)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sg.mem)
    (hpc : sg.pc = cliIoPl03.base + 292#64) (hrun : sg.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sg.sp = s0.sp - 8320#64)
    (hx0 : sg.readReg64 .x0 = BitVec.ofNat 64 n)
    (hw19 : (sg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sg.readReg64 (.gpr 20#5) = oldPtr)
    (hx21 : sg.readReg64 (.gpr 21#5) = 0#64)
    (hx24 : sg.readReg64 (.gpr 24#5) = sret)
    (hx25 : sg.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = 2097152#64)
    (hx27 : sg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 n)
    (hx28 : sg.readReg64 (.gpr 28#5) = 0#64)
    (hx29 : sg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sg = calleeSavedVRegs s0)
    (hoom_sg : ∀ sf_oom : State,
      ¬ FitsEvents M lim st_in (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) →
      OomPreserved sg sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl03.base + 348#64 → sc.status = .Running → sc.sp = s0.sp - 8320#64 →
      (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap 0) →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = sret →
      sc.readReg64 (.gpr 25#5) = 4096#64 → sc.readReg64 (.gpr 26#5) = 2097152#64 →
      sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 28#5) = 0#64 →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sc.mem → AllocCallPreserved sg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap 0)) newPtr [] ∗
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) st_in) sc)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sg
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ cliIoVecBuf A.repAlloc 0#64 oldPtr [] ∗
        A.pool lim st_in sg)
      post oomProp := by
  have hult_false : (4096#64 : BitVec 64).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le (by decide)
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
  intro sg' hcpu_g0
  have hcpu_g := hcpu_g0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_g' : sg'.pc = cliIoPl03.base + 292#64 := hcpu_g.pc_eq.trans hpc
  have hrun_g' : sg'.status = .Running := hcpu_g.status_eq.trans hrun
  have hsp_g' : sg'.spAligned = true := by
    rw [hcpu_g.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_g' : sg'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx0
  have hx20_g' : sg'.readReg64 (.gpr 20#5) = oldPtr := (hcpu_g.readReg64 _).trans hx20
  have hx21_g' : sg'.readReg64 (.gpr 21#5) = 0#64 := (hcpu_g.readReg64 _).trans hx21
  have hx24_g' : sg'.readReg64 (.gpr 24#5) = sret := (hcpu_g.readReg64 _).trans hx24
  have hx25_g' : sg'.readReg64 (.gpr 25#5) = 4096#64 := (hcpu_g.readReg64 _).trans hx25
  have hx26_g' : sg'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_g.readReg64 _).trans hx26
  have hx27_g' : sg'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx27
  have hx28_g' : sg'.readReg64 (.gpr 28#5) = 0#64 := (hcpu_g.readReg64 _).trans hx28
  have hx29_g' : sg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 := (hcpu_g.readReg64 _).trans hx29
  wp_sym_steps
  refine SepWP.done cliIoReadFile_grow_pc (by simpa [arm64_norm] using hrun_g')
    fun sm_fg hcpu_fg0 hcl_fg hnsp_fg hsym_fg => ?_
  have hcpu_fg := hcpu_fg0.1
  have ⟨hacp_gfg, hvm_gfg⟩ :=
    vmPreserved_of_seg hcpu_g0 hcpu_fg0 hnsp_fg hsym_fg
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_gfg : A.pool lim st_in sg = A.pool lim st_in sm_fg :=
    (A.pool_transport lim st_in sg sm_fg hvm_gfg).symm
  have hpc_fg : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym :=
    hcpu_fg.pc_eq.trans cliIoReadFile_grow_pc
  have hrun_fg : sm_fg.status = .Running := hcpu_fg.status_eq.trans hrun_g'
  have hsp_fg : sm_fg.sp = s0.sp - 8320#64 :=
    hcpu_fg.sp_eq.trans ((by simp [arm64_norm] : _ = sg'.sp).trans (hcpu_g.sp_eq.trans hsp_eq))
  have hlr_fg : sm_fg.readReg64 .lr = cliIoPl03.base + 436#64 := by
    rw [hcpu_fg.readReg64 .lr]; simp [arm64_norm]
  have hx0_fg : sm_fg.readReg64 .x0 = s0.sp - 128#64 := by
    rw [hcpu_fg.readReg64 .x0]; simp [arm64_norm]
  have hx1_fg : sm_fg.readReg64 .x1 = 0#64 := by
    rw [hcpu_fg.readReg64 .x1]; simp [arm64_norm]
  have hx2_fg : sm_fg.readReg64 .x2 = oldPtr := by
    rw [hcpu_fg.readReg64 .x2]; simp [arm64_norm]
  have hx3_fg : sm_fg.readReg64 .x3 = BitVec.ofNat 64 (cliIoCap 0) := by
    rw [hcpu_fg.readReg64 .x3]; simp [arm64_norm, cliIoCap_zero]
  have hw19_fg : (sm_fg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_fg.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_g.readReg64 (.gpr 19#5)]
    exact hw19
  have hx22_fg : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap 0) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, cliIoCap_zero]
  have hx23_fg : sm_fg.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx24_fg : sm_fg.readReg64 (.gpr 24#5) = sret := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx24_g']
  have hx25_fg : sm_fg.readReg64 (.gpr 25#5) = 4096#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx25_g']
  have hx26_fg : sm_fg.readReg64 (.gpr 26#5) = 2097152#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx26_g']
  have hx27_fg : sm_fg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (0 + n) := by
    rw [hcpu_fg.readReg64]; simpa [arm64_norm] using hx27_g'
  have hx28_fg : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 0 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx28_g']
  have hx29_fg : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx29_g']
  have hvregs_fg : calleeSavedVRegs sm_fg = calleeSavedVRegs s0 :=
    hcpu_fg.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sg').trans
      (hcpu_g.calleeSavedVRegs.trans hvregs))
  rw [hpool_eq_gfg]
  exact cliIoReadFile_post_grow_budget_reads A lim hext3 hfg hlo hhi
    (by decide : 0 < cliIoCap 0) (cliIoCap_lt_pow63 (by decide))
    (Nat.zero_le _) (not_nullAllowed_cliIoCap (by decide))
    hcl_fg hpc_fg hrun_fg hsp0 hsp_fg hlr_fg
    hx0_fg hx1_fg hx2_fg hx3_fg hw19_fg hx22_fg hx23_fg hx24_fg hx25_fg hx26_fg hx27_fg hx28_fg hx29_fg
    hvregs_fg
    (fun sf_oom hnf hoom_s =>
      hoom_sg sf_oom hnf (oomPreserved_of_allocCallPreserved hacp_gfg hoom_s))
    (fun sc newPtr st1' st2' hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c hx25_c
        hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c hacp_fgc => by
      simpa [Nat.zero_add] using
        hcont sc newPtr st1' st2' hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c
          hx25_c hx26_c (by simpa using hx27_c) (by simpa using hx28_c) hx29_c hvregs_c hcl_c
          (allocCallPreserved_trans hacp_gfg hacp_fgc))

/-- `cap = cliIoCap j` growth branch (`+0x124 = 292#64 .. +0x1b0` → `post_grow_budget` → `+0x15c = 348#64`). -/
theorem cliIoReadFile_grow_from_pos_budget_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    {s0 sg : State} {fd sret v0 v1 v2 oldPtr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {R_buf : SepProp}
    {j len n stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8352 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hj1 : j + 1 ≤ 9)
    (hlen_le_cap : len ≤ cliIoCap j)
    (hbs_len : bs.length = len)
    (hgt_cap : cliIoCap j < len + n)
    (hle_next : len + n ≤ cliIoCap (j + 1))
    (hcl : CliIoReadsCodeLoaded cliIoMpl sg.mem)
    (hpc : sg.pc = cliIoPl03.base + 292#64) (hrun : sg.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sg.sp = s0.sp - 8320#64)
    (hx0 : sg.readReg64 .x0 = BitVec.ofNat 64 n)
    (hw19 : (sg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sg.readReg64 (.gpr 20#5) = oldPtr)
    (hx21 : sg.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap j))
    (hx24 : sg.readReg64 (.gpr 24#5) = sret)
    (hx25 : sg.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = 2097152#64)
    (hx27 : sg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n))
    (hx28 : sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sg = calleeSavedVRegs s0)
    (hoom_sg : ∀ sf_oom : State,
      ¬ FitsEvents M lim st_in
        (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1))) →
      OomPreserved sg sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl03.base + 348#64 → sc.status = .Running → sc.sp = s0.sp - 8320#64 →
      (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap (j + 1)) →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = sret →
      sc.readReg64 (.gpr 25#5) = 4096#64 → sc.readReg64 (.gpr 26#5) = 2097152#64 →
      sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sc.mem → AllocCallPreserved sg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap (j + 1))) newPtr bs ∗
          A.pool lim
            (M.stepEvents
              (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1))) st_in)
            sc)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sg
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap j)) oldPtr bs ∗
        A.pool lim st_in sg)
      post oomProp := by
  have hj9 : j ≤ 9 := by omega
  have hcap_lt64 : cliIoCap j < 2 ^ 64 := cliIoCap_lt_pow64 hj9
  have hnext_lt64 : cliIoCap (j + 1) < 2 ^ 64 := cliIoCap_lt_pow64 hj1
  have hcap_beq0 : (BitVec.ofNat 64 (cliIoCap j) == 0#64) = false :=
    bv64_beq_ofNat_false (by have := cliIoCap_pos j; omega) hcap_lt64 (by decide)
  have hlsl1 : (BitVec.ofNat 64 (cliIoCap j)) <<< 1 = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [bv64_shiftLeft1_ofNat (by rw [← cliIoCap_succ]; exact hnext_lt64), ← cliIoCap_succ]
  have hult1 : (BitVec.ofNat 64 (cliIoCap j)).ult (BitVec.ofNat 64 (len + n)) = true :=
    bv64_ult_ofNat_true hgt_cap (Nat.lt_of_le_of_lt hle_next hnext_lt64)
  have hult2 : (BitVec.ofNat 64 (cliIoCap (j + 1))).ult (BitVec.ofNat 64 (len + n)) = false :=
    bv64_ult_ofNat_false hle_next hnext_lt64
  have hclamp :
      (if (BitVec.ofNat 64 (cliIoCap (j + 1))).ult 2097152#64 = true
       then BitVec.ofNat 64 (cliIoCap (j + 1))
       else 2097152#64) = BitVec.ofNat 64 (cliIoCap (j + 1)) :=
    cliIoFile_cap_clamp_bv hj1
  have hcap_lt_next : cliIoCap j < cliIoCap (j + 1) := cliIoCap_strictMono (Nat.lt_succ_self j)
  have hsub_hi :
      (BitVec.ofNat 64 (cliIoCap j) - BitVec.ofNat 64 len).ult
        (BitVec.ofNat 64 (cliIoCap (j + 1)) - BitVec.ofNat 64 len) = true := by
    rw [bv64_sub_ofNat hlen_le_cap, bv64_sub_ofNat (Nat.le_trans hlen_le_cap (Nat.le_of_lt hcap_lt_next))]
    exact bv64_ult_ofNat_true (by omega) (by omega)
  have hnext_ult_len : (BitVec.ofNat 64 (cliIoCap (j + 1))).ult (BitVec.ofNat 64 len) = false :=
    bv64_ult_ofNat_false (Nat.le_trans hlen_le_cap (Nat.le_of_lt hcap_lt_next)) hnext_lt64
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
  intro sg' hcpu_g0
  have hcpu_g := hcpu_g0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_g' : sg'.pc = cliIoPl03.base + 292#64 := hcpu_g.pc_eq.trans hpc
  have hrun_g' : sg'.status = .Running := hcpu_g.status_eq.trans hrun
  have hsp_g' : sg'.spAligned = true := by
    rw [hcpu_g.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_g' : sg'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx0
  have hx20_g' : sg'.readReg64 (.gpr 20#5) = oldPtr := (hcpu_g.readReg64 _).trans hx20
  have hx21_g' : sg'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap j) :=
    (hcpu_g.readReg64 _).trans hx21
  have hx24_g' : sg'.readReg64 (.gpr 24#5) = sret := (hcpu_g.readReg64 _).trans hx24
  have hx25_g' : sg'.readReg64 (.gpr 25#5) = 4096#64 := (hcpu_g.readReg64 _).trans hx25
  have hx26_g' : sg'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_g.readReg64 _).trans hx26
  have hx27_g' : sg'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) :=
    (hcpu_g.readReg64 _).trans hx27
  have hx28_g' : sg'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := (hcpu_g.readReg64 _).trans hx28
  have hx29_g' : sg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 := (hcpu_g.readReg64 _).trans hx29
  wp_sym_steps
  refine SepWP.done cliIoReadFile_grow_pc (by simpa [arm64_norm] using hrun_g')
    fun sm_fg hcpu_fg0 hcl_fg hnsp_fg hsym_fg => ?_
  have hcpu_fg := hcpu_fg0.1
  have ⟨hacp_gfg, hvm_gfg⟩ :=
    vmPreserved_of_seg hcpu_g0 hcpu_fg0 hnsp_fg hsym_fg
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_gfg : A.pool lim st_in sg = A.pool lim st_in sm_fg :=
    (A.pool_transport lim st_in sg sm_fg hvm_gfg).symm
  have hpc_fg : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym :=
    hcpu_fg.pc_eq.trans cliIoReadFile_grow_pc
  have hrun_fg : sm_fg.status = .Running := hcpu_fg.status_eq.trans hrun_g'
  have hsp_fg : sm_fg.sp = s0.sp - 8320#64 :=
    hcpu_fg.sp_eq.trans ((by simp [arm64_norm] : _ = sg'.sp).trans (hcpu_g.sp_eq.trans hsp_eq))
  have hlr_fg : sm_fg.readReg64 .lr = cliIoPl03.base + 436#64 := by
    rw [hcpu_fg.readReg64 .lr]; simp [arm64_norm]
  have hx0_fg : sm_fg.readReg64 .x0 = s0.sp - 128#64 := by
    rw [hcpu_fg.readReg64 .x0]; simp [arm64_norm]
  have hx1_fg : sm_fg.readReg64 .x1 = BitVec.ofNat 64 (cliIoCap j) := by
    rw [hcpu_fg.readReg64 .x1]; simp [arm64_norm]
  have hx2_fg : sm_fg.readReg64 .x2 = oldPtr := by
    rw [hcpu_fg.readReg64 .x2]; simp [arm64_norm]
  have hx3_fg : sm_fg.readReg64 .x3 = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [hcpu_fg.readReg64 .x3]; simp [arm64_norm]
  have hw19_fg : (sm_fg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_fg.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_g.readReg64 (.gpr 19#5)]
    exact hw19
  have hx22_fg : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx23_fg : sm_fg.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx24_fg : sm_fg.readReg64 (.gpr 24#5) = sret := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx24_g']
  have hx25_fg : sm_fg.readReg64 (.gpr 25#5) = 4096#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx25_g']
  have hx26_fg : sm_fg.readReg64 (.gpr 26#5) = 2097152#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx26_g']
  have hx27_fg : sm_fg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx27_g']
  have hx28_fg : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx28_g']
  have hx29_fg : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx29_g']
  have hvregs_fg : calleeSavedVRegs sm_fg = calleeSavedVRegs s0 :=
    hcpu_fg.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sg').trans
      (hcpu_g.calleeSavedVRegs.trans hvregs))
  rw [hpool_eq_gfg]
  exact cliIoReadFile_post_grow_budget_reads A lim hext3 hfg hlo hhi
    (cliIoCap_pos (j + 1)) (cliIoCap_lt_pow63 hj1)
    (by rw [hbs_len]; omega) (not_nullAllowed_cliIoCap hj1)
    hcl_fg hpc_fg hrun_fg hsp0 hsp_fg hlr_fg
    hx0_fg hx1_fg hx2_fg hx3_fg hw19_fg hx22_fg hx23_fg hx24_fg hx25_fg hx26_fg hx27_fg hx28_fg hx29_fg
    hvregs_fg
    (fun sf_oom hnf hoom_s =>
      hoom_sg sf_oom hnf (oomPreserved_of_allocCallPreserved hacp_gfg hoom_s))
    (fun sc newPtr st1' st2' hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c hx25_c
        hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c hacp_fgc =>
      hcont sc newPtr st1' st2' hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c
        hx25_c hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c
        (allocCallPreserved_trans hacp_gfg hacp_fgc))

/-- Shared `memcpy(ptr + len, sp + 4096, chunk)` + back-edge `+0x16c .. +0x18c → +0xd8 = 216#64` join. -/
theorem cliIoReadFile_memcpy_backedge_budget_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym) stdMemcpySpec)
    {s0 sc : State} {fd sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {R_path : SepProp}
    {rem chunk oldBuf : List (BitVec 8)}
    {cap len want stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcap_pos : 0 < cap) (hcap_lt63 : cap < 2 ^ 63)
    (hlen_r : len + chunk.length ≤ rem.length)
    (hlen_cap : len + chunk.length ≤ cap)
    (hlen_max : len + chunk.length ≤ 2097152)
    (hwant_le : want ≤ 4096)
    (hold_len : oldBuf.length = want)
    (hn_le_want : chunk.length ≤ want)
    (hchunk_eq : chunk = (rem.drop len).take want)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sc.mem)
    (hpc : sc.pc = cliIoPl03.base + 348#64) (hrun : sc.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sc.sp = s0.sp - 8320#64)
    (hw19 : (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sc.readReg64 (.gpr 20#5) = ptr)
    (hx22 : sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap)
    (hx23 : sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 chunk.length)
    (hx24 : sc.readReg64 (.gpr 24#5) = sret)
    (hx25 : sc.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sc.readReg64 (.gpr 26#5) = 2097152#64)
    (hx27 : sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + chunk.length))
    (hx28 : sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sc.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sc = calleeSavedVRegs s0)
    (hcont : ∀ sn : State,
      sn.pc = cliIoPl03.base + 216#64 → sn.status = .Running → sn.sp = s0.sp - 8320#64 →
      (sn.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sn.readReg64 (.gpr 20#5) = ptr →
      sn.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sn.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 2097152 (len + chunk.length)) →
      sn.readReg64 (.gpr 24#5) = sret →
      sn.readReg64 (.gpr 25#5) = 4096#64 →
      sn.readReg64 (.gpr 26#5) = 2097152#64 →
      sn.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + chunk.length) →
      sn.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sn = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sn.mem → CliIoMidPreserved sc sn →
      SepWP P (s0.readReg64 .lr) sn
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_path ∗
          memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take (len + chunk.length)) ∗
          A.pool lim st_cur sn)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sc
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_path ∗
        (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
          memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want)) ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take len) ∗
        A.pool lim st_cur sc)
      post oomProp := by
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
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
  intro sc' hcpu_c0
  have hcpu_c := hcpu_c0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_c' : sc'.pc = cliIoPl03.base + 348#64 := hcpu_c.pc_eq.trans hpc
  have hrun_c' : sc'.status = .Running := hcpu_c.status_eq.trans hrun
  have hsp_c_in : sc'.sp = s0.sp - 8320#64 := hcpu_c.sp_eq.trans hsp_eq
  have hsp_c' : sc'.spAligned = true := by
    rw [hcpu_c.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx20_c' : sc'.readReg64 (.gpr 20#5) = ptr := (hcpu_c.readReg64 _).trans hx20
  have hx23_c' : sc'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 chunk.length :=
    (hcpu_c.readReg64 _).trans hx23
  have hx28_c' : sc'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len :=
    (hcpu_c.readReg64 _).trans hx28
  wp_sym_steps
  refine SepWP.done cliIoReadFile_memcpy_pc (by simpa [arm64_norm] using hrun_c')
    fun sm_mc hcpu_mc0 hcl_mc hnsp_mc hsym_mc => ?_
  have hcpu_mc := hcpu_mc0.1
  have ⟨hacp_cmc, hvm_cmc⟩ :=
    vmPreserved_of_seg hcpu_c0 hcpu_mc0 hnsp_mc hsym_mc
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_cmc : A.pool lim st_cur sc = A.pool lim st_cur sm_mc :=
    (A.pool_transport lim st_cur sc sm_mc hvm_cmc).symm
  have hpc_mc : sm_mc.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym :=
    hcpu_mc.pc_eq.trans cliIoReadFile_memcpy_pc
  have hrun_mc : sm_mc.status = .Running := hcpu_mc.status_eq.trans hrun_c'
  have hsp_mc_eq : sm_mc.sp = s0.sp - 8320#64 :=
    hcpu_mc.sp_eq.trans ((by simp [arm64_norm] : _ = sc'.sp).trans hsp_c_in)
  have hsp_mc : sm_mc.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_mc_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_mc : sm_mc.readReg64 .lr = cliIoPl03.base + 364#64 := by
    rw [hcpu_mc.readReg64 .lr]; simp [arm64_norm]
  have hx0_mc : sm_mc.readReg64 .x0 = ptr + BitVec.ofNat 64 len := by
    rw [hcpu_mc.readReg64 .x0]; simp [arm64_norm]
  have hx1_mc : sm_mc.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_mc.readReg64 .x1]; simp only [arm64_norm]
  have hx2_mc : sm_mc.readReg64 .x2 = BitVec.ofNat 64 chunk.length := by
    rw [hcpu_mc.readReg64 .x2]; simp [arm64_norm, hchunk_eq]
  apply seqCodeLoadedWhere hcl_mc (mid := cliIoPl03.base + 364#64)
  apply (SepWP.call_subroutine_frame hmemcpy
    (x := (ptr + BitVec.ofNat 64 len, s0.sp - 4224#64, chunk))
    hpc_mc hrun_mc hsp_mc hlr_mc
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [stdMemcpySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    have hchunk_lt64 : chunk.length < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.le_trans hn_le_want hwant_le) (by decide)
    refine ⟨⟨hx0_mc, hx1_mc, hx2_mc, hchunk_lt64⟩, ?_⟩
    rw [hpool_eq_cmc] at hm'
    exact Satisfies.mono (by sep_frame) hm'
  · intro sm_mc' hpc_mc' hrun_mc' hsp_mc' hcs_mc'
    refine SepWP.done hpc_mc' hrun_mc' fun hcl_mc' => ?_
    wp_conv_pre => dsimp only [stdMemcpySpec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hstd_mc⟩
    have hmid_mc : CliIoMidPreserved sm_mc sm_mc' := CliIoMidPreserved.of_std hstd_mc
    have hpool_eq_mc : A.pool lim st_cur sm_mc = A.pool lim st_cur sm_mc' :=
      (A.pool_transport lim st_cur sm_mc sm_mc' (vmPreserved_of_stdState hstd_mc)).symm
    have hsp_mc'_eq : sm_mc'.sp = s0.sp - 8320#64 := hsp_mc'.trans hsp_mc_eq
    have hx22_mc' : sm_mc'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap :=
      hcs_mc'.readReg64_x22.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 22#5)).trans
          ((hcpu_c.readReg64 _).trans hx22)))
    have hx25_mc' : sm_mc'.readReg64 (.gpr 25#5) = 4096#64 :=
      hcs_mc'.readReg64_x25.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 25#5)).trans
          ((hcpu_c.readReg64 _).trans hx25)))
    have hx27_mc' : sm_mc'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + chunk.length) :=
      hcs_mc'.readReg64_x27.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 27#5)).trans
          ((hcpu_c.readReg64 _).trans hx27)))
    have hsub8 :
        2097153#64 - BitVec.ofNat 64 (len + chunk.length) =
          BitVec.ofNat 64 (2097152 + 1 - (len + chunk.length)) := by
      change BitVec.ofNat 64 2097153 - BitVec.ofNat 64 (len + chunk.length) = _
      exact bv64_sub_ofNat (by omega)
    have hule :
        (BitVec.ofNat 64 (len + ((rem.drop len).take want).length)).ule 2097152#64 = true := by
      rw [← hchunk_eq]
      have hlt64 : len + chunk.length < 2 ^ 64 := by omega
      apply decide_eq_true
      change (BitVec.ofNat 64 (len + chunk.length)).toNat ≤ (2097152#64 : BitVec 64).toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
      exact hlen_max
    apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl_mc'
      (mid := cliIoPl03.base + 216#64)
    intro sb' hcpu_b0
    have hcpu_b := hcpu_b0.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc_b' : sb'.pc = cliIoPl03.base + 364#64 := hcpu_b.pc_eq.trans hpc_mc'
    have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_mc'
    have hsp_b' : sb'.spAligned = true := by
      rw [hcpu_b.spAligned]; simp only [State.spAligned]; rw [hsp_mc'_eq]
      exact s0.spAligned_sub 8320#64 hsp0
    have hx22_b' : sb'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap :=
      (hcpu_b.readReg64 _).trans hx22_mc'
    have hx25_b' : sb'.readReg64 (.gpr 25#5) = 4096#64 :=
      (hcpu_b.readReg64 _).trans hx25_mc'
    have hx27_b' : sb'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + chunk.length) :=
      (hcpu_b.readReg64 _).trans hx27_mc'
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
      fun sn hcpu_n0 hcl_n hnsp_n hsym_n => ?_
    have hcpu_n := hcpu_n0.1
    have ⟨hacp_bn, hvm_bn⟩ :=
      vmPreserved_of_seg hcpu_b0 hcpu_n0 hnsp_n hsym_n
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_bn : A.pool lim st_cur sm_mc' = A.pool lim st_cur sn :=
      (A.pool_transport lim st_cur sm_mc' sn hvm_bn).symm
    have hpc_n : sn.pc = cliIoPl03.base + 216#64 := by
      rw [hcpu_n.pc_eq]; simp [arm64_norm]
    have hrun_n : sn.status = .Running := hcpu_n.status_eq.trans hrun_b'
    have hsp_n : sn.sp = s0.sp - 8320#64 :=
      hcpu_n.sp_eq.trans ((by simp [arm64_norm] : _ = sb'.sp).trans (hcpu_b.sp_eq.trans hsp_mc'_eq))
    have hw19_n : (sn.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
      rw [readReg32_of_readReg64_eq (hcpu_n.readReg64 (.gpr 19#5))]
      simp only [arm64_norm]
      rw [hcpu_b.readReg64 (.gpr 19#5), hcs_mc'.readReg64_x19,
        hcpu_mc.readReg64 (.gpr 19#5)]
      simp only [arm64_norm]
      rw [hcpu_c.readReg64 (.gpr 19#5)]
      exact hw19
    have hx20_n : sn.readReg64 (.gpr 20#5) = ptr := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x20, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact hx20_c'
    have hx21_n : sn.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := by
      rw [hcpu_n.readReg64]; simp [arm64_norm]
    have hx23_n : sn.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 2097152 (len + chunk.length)) := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]; rw [← hchunk_eq, hsub8]
      exact wantBytes_csel_bv hlen_max (by decide)
    have hx24_n : sn.readReg64 (.gpr 24#5) = sret := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x24, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx24
    have hx25_n : sn.readReg64 (.gpr 25#5) = 4096#64 := by
      rw [hcpu_n.readReg64]; simp [arm64_norm, hx25_b']
    have hx26_n : sn.readReg64 (.gpr 26#5) = 2097152#64 := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x26, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx26
    have hx28_n : sn.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + chunk.length) := by
      rw [hcpu_n.readReg64]; simp [arm64_norm, hchunk_eq]
    have hx29_n : sn.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x29, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx29
    have hvregs_n : calleeSavedVRegs sn = calleeSavedVRegs s0 :=
      hcpu_n.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
        (hcpu_b.calleeSavedVRegs.trans (hcs_mc'.vregs.trans
          (hcpu_mc.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sc').trans
            (hcpu_c.calleeSavedVRegs.trans hvregs))))))
    have hmid_cn : CliIoMidPreserved sc sn :=
      (cliIoMidPreserved_of_acp hacp_cmc).trans
        (hmid_mc.trans (cliIoMidPreserved_of_acp hacp_bn))
    refine SepWP.weaken_pre ?_
      (hcont sn hpc_n hrun_n hsp_n hw19_n hx20_n hx21_n hx23_n hx24_n hx25_n hx26_n hx28_n hx29_n
        hvregs_n hcl_n hmid_cn)
    rw [hpool_eq_mc, hpool_eq_bn]
    have hvec_back :=
      cliIoVecBuf_repack_chunk A.repAlloc hcap_pos hcap_lt63 hptr_ne0 hlen_r hlen_cap hchunk_eq
    have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
    let Rest : SepProp :=
      stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_path ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        A.pool lim st_cur sn
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := Rest) (sepConj_mono hvec_back hbuf_back))
        (by dsimp only [Rest]; sep_entail))
    dsimp only [Rest, RustCliAllocBudget.repAlloc] at hvec_back ⊢
    sep_entail

/-! ## 4. Budget-Threaded Post-`read` Branches & `do_read` (`+0xd8 → +0xe8`) -/

private theorem cliIoReadFile_after_read_eof_budget_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hA_mem : ∀ st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 sr : State} {fd sret v0 v1 v2 cap ptr st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {bs : List (BitVec 8)} {stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : sr.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl03.base + 232#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 8320#64)
    (hx0 : sr.readReg64 .x0 = 0#64)
    (hw19 : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = cap)
    (hx24 : sr.readReg64 (.gpr 24#5) = sret)
    (hx28 : sr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      sf.fs = sr.fs.setFd fd none →
      sf.trace = sr.trace → sf.sigActions = sr.sigActions →
      sf.tpidrEl0 = sr.tpidrEl0 → sf.brkStart = sr.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.ok bs) ∗
          A.pool lim st_cur sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sr
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc cap ptr bs ∗ A.pool lim st_cur sr)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 456#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
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
  have hw19_e : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_e.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_r.readReg64 (.gpr 19#5)]
    exact hw19
  rw [hpool_eq]
  exact cliIoReadFile_ok_epilogue_budget_reads A lim hA_mem hext3 hclose hlo hhi hfd_lt
    (by rw [hacp_re.1]; exact hfds) hkind hcl_e
    (hcpu_e.pc_eq.trans (by simp [arm64_norm])) (hcpu_e.status_eq.trans hrun_r') hsp0
    (hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    hw19_e
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx21)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx28)
    (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
      hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
        (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_re.1))
        (htr_f.trans hacp_re.2.1) (hsig_f.trans hacp_re.2.2.1)
        (htp_f.trans hacp_re.2.2.2.1) (hbs_f.trans hacp_re.2.2.2.2.1) hent

private theorem cliIoReadFile_after_read_overcap_budget_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hA_mem : ∀ st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 sr : State} {fd sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {bs : List (BitVec 8)} {stackBytes : Nat} {st_in : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : sr.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl03.base + 232#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 8320#64)
    (hx0 : sr.readReg64 .x0 = 1#64)
    (hw19 : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap 9))
    (hx23 : sr.readReg64 (.gpr 23#5) = 1#64)
    (hx24 : sr.readReg64 (.gpr 24#5) = sret)
    (hx26 : sr.readReg64 (.gpr 26#5) = 2097152#64)
    (hx28 : sr.readReg64 (.gpr 28#5) = 2097152#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      sf.fs = sr.fs.setFd fd none →
      sf.trace = sr.trace → sf.sigActions = sr.sigActions →
      sf.tpidrEl0 = sr.tpidrEl0 → sf.brkStart = sr.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioVecAt A.repAlloc sret (.error ()) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents (cliIoCap 9) 1) st_in) sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sr
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap 9)) ptr bs ∗
        A.pool lim st_in sr)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 468#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = 1#64 := (hcpu_r.readReg64 _).trans hx0
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = 1#64 := (hcpu_r.readReg64 _).trans hx23
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_r.readReg64 _).trans hx26
  have hx28_r' : sr'.readReg64 (.gpr 28#5) = 2097152#64 := (hcpu_r.readReg64 _).trans hx28
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
  have hcpu_e := hcpu_e0.1
  have ⟨hacp_re, hvm_re⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_e0 hnsp_e hsym_e
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool lim st_in sr = A.pool lim st_in se :=
    (A.pool_transport lim st_in sr se hvm_re).symm
  have hw19_e : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_e.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_r.readReg64 (.gpr 19#5)]
    exact hw19
  rw [hpool_eq]
  exact cliIoReadFile_err_dealloc_epilogue_budget_reads A lim hA_mem hext3 hdealloc hclose hlo hhi
    (cliIoCap_pos 9) (cliIoCap_lt_pow63 (by decide)) hfd_lt
    (by rw [hacp_re.1]; exact hfds) hkind hcl_e
    (hcpu_e.pc_eq.trans (by simp [arm64_norm])) (hcpu_e.status_eq.trans hrun_r') hsp0
    (hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    hw19_e
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx21)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
      hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
        (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_re.1))
        (htr_f.trans hacp_re.2.1) (hsig_f.trans hacp_re.2.2.1)
        (htp_f.trans hacp_re.2.2.2.1) (hbs_f.trans hacp_re.2.2.2.2.1) hent

private theorem cliIoReadFile_after_read_nogrow_vm_reads [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    {s0 sr : State} {fd sret ptr : BitVec 64} {Pre : SepProp}
    {cap len want n : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hn_pos : 0 < n) (hn_le_want : n ≤ want) (hwant_le : want ≤ 4096)
    (hlen_cap : len + n ≤ cap) (hcap_max : cap ≤ 2097152)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl03.base + 232#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 8320#64)
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 n)
    (hw19 : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx23 : sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sr.readReg64 (.gpr 24#5) = sret)
    (hx25 : sr.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sr.readReg64 (.gpr 26#5) = 2097152#64)
    (hx28 : sr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sr.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sc : State,
      sc.pc = cliIoPl03.base + 348#64 → sc.status = .Running → sc.sp = s0.sp - 8320#64 →
      (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sc.readReg64 (.gpr 20#5) = ptr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = sret →
      sc.readReg64 (.gpr 25#5) = 4096#64 → sc.readReg64 (.gpr 26#5) = 2097152#64 →
      sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sc.mem →
      AllocCallPreserved sr sc → VmPreserved sr sc →
      SepWP P (s0.readReg64 .lr) sc Pre post oomProp) :
    SepWP P (s0.readReg64 .lr) sr Pre post oomProp := by
  have hn_beq0 : (BitVec.ofNat 64 n == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) (by omega) (by decide)
  have hbit63 : (BitVec.ofNat 64 n).getLsbD 63 = false := bit63_eq_zero_of_lt (by omega)
  have hule_w : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 want) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_w : (BitVec.ofNat 64 want).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le_want (by omega)
  have hsub26 : 2097152#64 - BitVec.ofNat 64 len = BitVec.ofNat 64 (2097152 - len) :=
    bv64_sub_ofNat (by omega)
  have hule_rem : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (2097152 - len)) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_rem : (BitVec.ofNat 64 (2097152 - len)).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false (by omega) (by omega)
  have hadd27 : BitVec.ofNat 64 n + BitVec.ofNat 64 len = BitVec.ofNat 64 (len + n) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hule_cap : (BitVec.ofNat 64 (len + n)).ule (BitVec.ofNat 64 cap) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_cap : (BitVec.ofNat 64 cap).ult (BitVec.ofNat 64 (len + n)) = false :=
    bv64_ult_ofNat_false hlen_cap (by omega)
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 348#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_r.readReg64 _).trans hx0
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_r.readReg64 _).trans hx21
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_r.readReg64 _).trans hx23
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_r.readReg64 _).trans hx26
  have hx28_r' : sr'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := (hcpu_r.readReg64 _).trans hx28
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun sc hcpu_c0 hcl_c hnsp_c hsym_c => ?_
  have hcpu_c := hcpu_c0.1
  have ⟨hacp_rc, hvm_rc⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_c0 hnsp_c hsym_c
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hw19_c : (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_c.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_r.readReg64 (.gpr 19#5)]
    exact hw19
  exact hcont sc (hcpu_c.pc_eq.trans (by simp [arm64_norm])) (hcpu_c.status_eq.trans hrun_r')
    (hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    hw19_c
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx25)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm, hx26_r'])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm, hx28_r'])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx29)
    (hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    hcl_c hacp_rc hvm_rc

private theorem cliIoReadFile_after_read_grow_vm_reads [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    {s0 sr : State} {fd sret ptr : BitVec 64} {Pre : SepProp}
    {cap len want n : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hn_pos : 0 < n) (hn_le_want : n ≤ want) (hwant_le : want ≤ 4096)
    (hgt_cap : cap < len + n) (hlen_max : len + n ≤ 2097152)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl03.base + 232#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 8320#64)
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 n)
    (hw19 : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx23 : sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sr.readReg64 (.gpr 24#5) = sret)
    (hx25 : sr.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sr.readReg64 (.gpr 26#5) = 2097152#64)
    (hx28 : sr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sr.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sg : State,
      sg.pc = cliIoPl03.base + 292#64 → sg.status = .Running → sg.sp = s0.sp - 8320#64 →
      sg.readReg64 .x0 = BitVec.ofNat 64 n →
      (sg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sg.readReg64 (.gpr 20#5) = ptr →
      sg.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sg.readReg64 (.gpr 24#5) = sret →
      sg.readReg64 (.gpr 25#5) = 4096#64 → sg.readReg64 (.gpr 26#5) = 2097152#64 →
      sg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) →
      sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sg.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sg = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sg.mem →
      AllocCallPreserved sr sg → VmPreserved sr sg →
      SepWP P (s0.readReg64 .lr) sg Pre post oomProp) :
    SepWP P (s0.readReg64 .lr) sr Pre post oomProp := by
  have hn_beq0 : (BitVec.ofNat 64 n == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) (by omega) (by decide)
  have hbit63 : (BitVec.ofNat 64 n).getLsbD 63 = false := bit63_eq_zero_of_lt (by omega)
  have hule_w : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 want) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_w : (BitVec.ofNat 64 want).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le_want (by omega)
  have hsub26 : 2097152#64 - BitVec.ofNat 64 len = BitVec.ofNat 64 (2097152 - len) :=
    bv64_sub_ofNat (by omega)
  have hule_rem : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (2097152 - len)) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_rem : (BitVec.ofNat 64 (2097152 - len)).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false (by omega) (by omega)
  have hadd27 : BitVec.ofNat 64 n + BitVec.ofNat 64 len = BitVec.ofNat 64 (len + n) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hule_cap : (BitVec.ofNat 64 (len + n)).ule (BitVec.ofNat 64 cap) = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hult_cap : (BitVec.ofNat 64 cap).ult (BitVec.ofNat 64 (len + n)) = true :=
    bv64_ult_ofNat_true hgt_cap (by omega)
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 292#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_r.readReg64 _).trans hx0
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_r.readReg64 _).trans hx21
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_r.readReg64 _).trans hx23
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_r.readReg64 _).trans hx26
  have hx28_r' : sr'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := (hcpu_r.readReg64 _).trans hx28
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun sg hcpu_g0 hcl_g hnsp_g hsym_g => ?_
  have hcpu_g := hcpu_g0.1
  have ⟨hacp_rg, hvm_rg⟩ :=
    vmPreserved_of_seg hcpu_r0 hcpu_g0 hnsp_g hsym_g
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hw19_g : (sg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_g.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_r.readReg64 (.gpr 19#5)]
    exact hw19
  exact hcont sg (hcpu_g.pc_eq.trans (by simp [arm64_norm])) (hcpu_g.status_eq.trans hrun_r')
    (hcpu_g.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx0_r'])
    hw19_g
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx21_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx25)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx26_r'])
    (by rw [hcpu_g.readReg64]; simp [arm64_norm])
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx28_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx29)
    (hcpu_g.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    hcl_g hacp_rg hvm_rg

private theorem cliIoReadFile_do_read_budget_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hA_mem : ∀ st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    {s0 sl : State} {d0 : FdEntry} {fd sret ptr cap_bv : BitVec 64} {R_frame : SepProp}
    {len want stackBytes : Nat} {st_cur : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8352 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hwant_le : want ≤ 4096)
    (hoff_le : d0.offset + len + want ≤ Arm64.MAX_LFS_FILESIZE)
    (hkind : d0.kind = .localFile) (hcanr : d0.accMode.canRead = true)
    (hfs : sl.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + len }))
    (hcl : CliIoReadsCodeLoaded cliIoMpl sl.mem)
    (hpc : sl.pc = cliIoPl03.base + 216#64) (hrun : sl.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sl.sp = s0.sp - 8320#64)
    (hw19 : (sl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sl.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sl.readReg64 (.gpr 21#5) = cap_bv)
    (hx23 : sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sl.readReg64 (.gpr 24#5) = sret)
    (hx25 : sl.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sl.readReg64 (.gpr 26#5) = 2097152#64)
    (hx28 : sl.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sl.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sl = calleeSavedVRegs s0)
    (hcont : ∀ (sr : State) (oldBuf : List (BitVec 8)),
      let rem := (s0.fs.fdBytes d0).drop d0.offset
      let chunk := (rem.drop len).take want
      oldBuf.length = want →
      sr.pc = cliIoPl03.base + 232#64 → sr.status = .Running → sr.sp = s0.sp - 8320#64 →
      sr.readReg64 .x0 = BitVec.ofNat 64 chunk.length →
      (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sr.readReg64 (.gpr 20#5) = ptr →
      sr.readReg64 (.gpr 21#5) = cap_bv →
      sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want →
      sr.readReg64 (.gpr 24#5) = sret →
      sr.readReg64 (.gpr 25#5) = 4096#64 →
      sr.readReg64 (.gpr 26#5) = 2097152#64 →
      sr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sr.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs sr = calleeSavedVRegs s0 →
      CliIoReadsCodeLoaded cliIoMpl sr.mem →
      sr.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + (len + chunk.length) }) →
      sr.trace = sl.trace → sr.sigActions = sl.sigActions →
      sr.tpidrEl0 = sl.tpidrEl0 → sr.brkStart = sl.brkStart →
      SepWP P (s0.readReg64 .lr) sr
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
            memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want)) ∗
          R_frame ∗ A.pool lim st_cur sr)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sl
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
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
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
  intro sl' hcpu_l0
  have hcpu_l := hcpu_l0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_l' : sl'.pc = cliIoPl03.base + 216#64 := hcpu_l.pc_eq.trans hpc
  have hrun_l' : sl'.status = .Running := hcpu_l.status_eq.trans hrun
  have hsp_l_in : sl'.sp = s0.sp - 8320#64 := hcpu_l.sp_eq.trans hsp_eq
  have hsp_l' : sl'.spAligned = true := by
    rw [hcpu_l.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx23_l' : sl'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_l.readReg64 _).trans hx23
  wp_sym_steps
  refine SepWP.done cliIoReadFile_read_pc (by simpa [arm64_norm] using hrun_l')
    fun sm_rd hcpu_rd0 hcl_rd hnsp_rd hsym_rd => ?_
  have hcpu_rd := hcpu_rd0.1
  have ⟨hacp_lrd, hvm_lrd⟩ :=
    vmPreserved_of_seg hcpu_l0 hcpu_rd0 hnsp_rd hsym_rd
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_lrd : A.pool lim st_cur sl = A.pool lim st_cur sm_rd :=
    (A.pool_transport lim st_cur sl sm_rd hvm_lrd).symm
  have hpc_rd : sm_rd.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym :=
    hcpu_rd.pc_eq.trans cliIoReadFile_read_pc
  have hrun_rd : sm_rd.status = .Running := hcpu_rd.status_eq.trans hrun_l'
  have hsp_rd_eq : sm_rd.sp = s0.sp - 8320#64 :=
    hcpu_rd.sp_eq.trans ((by simp [arm64_norm] : _ = sl'.sp).trans hsp_l_in)
  have hsp_rd : sm_rd.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_rd_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_rd : sm_rd.readReg64 .lr = cliIoPl03.base + 232#64 := by
    rw [hcpu_rd.readReg64 .lr]; simp [arm64_norm]
  have hx0_rd : (sm_rd.readReg32 .x0).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_rd.readReg64 .x0)]
    simp only [arm64_norm]
    rw [hcpu_l.readReg64 (.gpr 19#5)]
    exact hw19
  have hx1_rd : sm_rd.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_rd.readReg64 .x1]; simp only [arm64_norm]
  have hx2_rd : sm_rd.readReg64 .x2 = BitVec.ofNat 64 want := by
    rw [hcpu_rd.readReg64 .x2]; simp [arm64_norm]
  have hfs_rd : sm_rd.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + len }) :=
    hacp_lrd.1.trans hfs
  have hfds_rd : sm_rd.fs.fds fd = some { d0 with offset := d0.offset + len } := by
    rw [hfs_rd]; simp [FsState.setFd]
  rw [hpool_eq_lrd]
  let d_cur : FdEntry := { d0 with offset := d0.offset + len }
  have hkind_or : (d_cur.kind == .localFile || d_cur.kind == .stdio) = true := by
    dsimp only [d_cur]; rw [hkind]; rfl
  apply seqCodeLoadedWhere hcl_rd (mid := cliIoPl03.base + 232#64)
  apply (SepWP.call_subroutine_frame hread
    (x := (fd, s0.sp - 4224#64, BitVec.ofNat 64 want, d_cur, oldBuf))
    hpc_rd hrun_rd hsp_rd hlr_rd
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslReadFileOrStdio32Spec]
    rw [hsp_rd_eq, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_rd, hfd_lt, hx1_rd, hx2_rd,
      by rw [hwant_toNat]; simp only [Arm64.MAX_RW_COUNT]; omega,
      by rw [hwant_toNat]; exact sp_sub_4224_va_bound (by omega) hsp_va hwant_le,
      fun _ => by dsimp only [d_cur]; rw [hwant_toNat]; exact hoff_le,
      by rw [hwant_toNat]; exact hold_len, hfds_rd, hkind_or, hcanr⟩, ?_⟩
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 32 (by omega) (by omega)] at hm'
    exact Satisfies.mono (by sep_frame) hm'
  · intro sr hpc_sr hrun_sr hsp_sr hcs_rdsr
    refine SepWP.done hpc_sr hrun_sr fun hcl_sr => ?_
    wp_conv_pre => dsimp only [muslReadFileOrStdio32Spec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_sr, hfs_sr, htr_sr, hsys_sr⟩
    have hpool_eq_sr : A.pool lim st_cur sm_rd = A.pool lim st_cur sr :=
      (hA_mem st_cur (vmMemPreserved_of_syscallPreserved hsys_sr)).symm
    have hchunk_eq :
        ((sm_rd.fs.fdBytes d_cur).drop d_cur.offset).take (BitVec.ofNat 64 want).toNat =
          (((s0.fs.fdBytes d0).drop d0.offset).drop len).take want := by
      rw [hfs_rd, hwant_toNat]
      dsimp only [FsState.setFd, FsState.fdBytes, FsState.files, FsState.getEntry, d_cur]
      rw [← List.drop_drop]
    have hfs_sr' : sr.fs = s0.fs.setFd fd
        (some { d0 with offset := d0.offset + (len + ((((s0.fs.fdBytes d0).drop d0.offset).drop len).take want).length) }) := by
      rw [hfs_sr, hchunk_eq, hfs_rd, FsState.setFd_setFd_same]
      dsimp only [d_cur]
      rw [Nat.add_assoc]
    have hsp_sr_eq : sr.sp = s0.sp - 8320#64 := hsp_sr.trans hsp_rd_eq
    have hw19_sr : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
      rw [readReg32_of_readReg64_eq hcs_rdsr.readReg64_x19,
        readReg32_of_readReg64_eq (hcpu_rd.readReg64 (.gpr 19#5))]
      simp only [arm64_norm]
      rw [hcpu_l.readReg64 (.gpr 19#5)]
      exact hw19
    refine SepWP.weaken_pre ?_
      (hcont sr oldBuf hold_len hpc_sr hrun_sr hsp_sr_eq
        (by rwa [hchunk_eq] at hx0_sr)
        hw19_sr
        (by rw [hcs_rdsr.readReg64_x20, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx20)
        (by rw [hcs_rdsr.readReg64_x21, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx21)
        (by rw [hcs_rdsr.readReg64_x23, hcpu_rd.readReg64]; simp only [arm64_norm]; exact hx23_l')
        (by rw [hcs_rdsr.readReg64_x24, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx24)
        (by rw [hcs_rdsr.readReg64_x25, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx25)
        (by rw [hcs_rdsr.readReg64_x26, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx26)
        (by rw [hcs_rdsr.readReg64_x28, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx28)
        (by rw [hcs_rdsr.readReg64_x29, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx29)
        (hcs_rdsr.vregs.trans (hcpu_rd.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs sl').trans (hcpu_l.calleeSavedVRegs.trans hvregs))))
        hcl_sr hfs_sr' (htr_sr.trans hacp_lrd.2.1) (hsys_sr.2.1.trans hacp_lrd.2.2.1)
        (hsys_sr.1.trans hacp_lrd.2.2.2.1) (hsys_sr.2.2.brkStart_eq.trans hacp_lrd.2.2.2.2.1))
    rw [hpool_eq_sr, hchunk_eq, hsp_rd_eq,
      stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 32 (by omega) (by omega)]
    sep_entail

/-! ## 5. Full Budget-Threaded `4096`-B `read_file` `.localFile` Loop (`+0xd8`) -/

/-- Budget-threaded `4096`-byte `read_file` `.localFile` loop from `+0xd8 = 216#64` over whole
    `A.pool lim st_cur sl` (`0` `StdErrnoCell`), stepping `stInit` by `cliIoFileLoopBudgetEvents`
    and returning `ioVecAt A.repAlloc sret (cliIoFileLoopBudgetOut rem)` with `sf.fs = s0.fs`. -/
theorem cliIoReadFile_file_loop_budget_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hA_mem : ∀ st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
      stdMemcpySpec)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 : State} {d0 : FdEntry} {fd sret v0 v1 v2 : BitVec 64}
    {stackBytes : Nat} {stInit : M.σ}
    {post : State → SepProp → Prop}
    (hlo : 8368 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hsp0 : s0.spAligned = true)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds_none : s0.fs.fds fd = none)
    (hkind : d0.kind = .localFile) (hcanr : d0.accMode.canRead = true) (hoff0 : d0.offset = 0)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs →
      sf.trace = s0.trace → sf.sigActions = s0.sigActions →
      sf.tpidrEl0 = s0.tpidrEl0 → sf.brkStart = s0.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          ioVecAt A.repAlloc sret
            (cliIoFileLoopBudgetOut ((s0.fs.fdBytes d0).drop d0.offset)) ∗
          A.pool lim
            (M.stepEvents
              (cliIoFileLoopBudgetEvents ((s0.fs.fdBytes d0).drop d0.offset)) stInit) sf) →
        post sf Pre_f) :
    ∀ (fuel : Nat) (sl : State) (ptr st0 st1 st2 st3 : BitVec 64) (cap len : Nat) (st_cur : M.σ),
      cliIoFileCap + 1 - len ≤ fuel →
      len ≤ min ((s0.fs.fdBytes d0).drop d0.offset).length cliIoFileCap →
      (len < ((s0.fs.fdBytes d0).drop d0.offset).length → 4096 ∣ len) →
      cap = cliIoFinalCap 9 len →
      st_cur = M.stepEvents (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 len)) stInit →
      CliIoReadsCodeLoaded cliIoMpl sl.mem →
      sl.pc = cliIoPl03.base + 216#64 → sl.status = .Running → sl.sp = s0.sp - 8320#64 →
      (sl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd → sl.readReg64 (.gpr 20#5) = ptr →
      sl.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 2097152 len) →
      sl.readReg64 (.gpr 24#5) = sret →
      sl.readReg64 (.gpr 25#5) = 4096#64 → sl.readReg64 (.gpr 26#5) = 2097152#64 →
      sl.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sl.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sl = calleeSavedVRegs s0 →
      sl.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + len }) →
      sl.trace = s0.trace → sl.sigActions = s0.sigActions →
      sl.tpidrEl0 = s0.tpidrEl0 → sl.brkStart = s0.brkStart →
      SepWP P (s0.readReg64 .lr) sl
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr
            (((s0.fs.fdBytes d0).drop d0.offset).take len) ∗
          A.pool lim st_cur sl)
        post
        (fun sf_oom =>
          ⌜¬ FitsEvents M lim stInit
              (cliIoFileLoopBudgetEvents ((s0.fs.fdBytes d0).drop d0.offset)) ∧
            CliIoFilesOomPreserved s0 sf_oom⌝) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro sl ptr st0 st1 st2 st3 cap len st_cur
      hfuel hlen_le hdvd hcap_eq hst_eq hcl hpc hrun hsp_eq
      hw19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hx29 hvregs
      hfs_sl htr_sl hsig_sl htp_sl hbs_sl
    let rem := (s0.fs.fdBytes d0).drop d0.offset
    have hrem_def : rem = (s0.fs.fdBytes d0).drop d0.offset := rfl
    let want := wantBytes 2097152 len
    have hwant_def : want = wantBytes 2097152 len := rfl
    have hcap2097 : cliIoFileCap = 2097152 := rfl
    have hlen_max : len ≤ cliIoFileCap := Nat.le_trans hlen_le (Nat.min_le_right _ _)
    have hlen_rem : len ≤ rem.length := Nat.le_trans hlen_le (Nat.min_le_left _ _)
    have hwant_le : want ≤ 4096 := wantBytes_le_4096 2097152 len
    let R_fr : SepProp :=
      memRegion (s0.sp - 8320#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr (rem.take len)
    refine SepWP.weaken_pre (by dsimp only [R_fr]; sep_entail)
      (cliIoReadFile_do_read_budget_reads A lim hA_mem hext3 hread (R_frame := R_fr) (by dsimp [allocHookStack] at hlo; omega)
        hhi hsp_lo hsp_va hfd_lt hwant_le (by simp only [Arm64.MAX_LFS_FILESIZE, hoff0]; omega)
        hkind hcanr hfs_sl hcl hpc hrun hsp0 hsp_eq
        hw19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hx29 hvregs
        fun sr oldBuf hold_len hpc_sr hrun_sr hsp_sr hx0_sr hw19_sr hx20_sr hx21_sr hx23_sr
            hx24_sr hx25_sr hx26_sr hx28_sr hx29_sr hvregs_sr hcl_sr hfs_sr htr_sr hsig_sr
            htp_sr hbs_sr => ?_)
    dsimp only [R_fr]
    let chunk := (rem.drop len).take want
    have hchunk_def : chunk = (rem.drop len).take want := rfl
    have hn_min : chunk.length = min (rem.length - len) want := by
      rw [hchunk_def, List.length_take, List.length_drop, Nat.min_comm]
    have hn_le_want : chunk.length ≤ want := by rw [hn_min]; exact Nat.min_le_right _ _
    have hn_le_rem : len + chunk.length ≤ rem.length := by rw [hn_min]; omega
    let d_sr : FdEntry := { d0 with offset := d0.offset + (len + chunk.length) }
    have hfds_sr : sr.fs.fds fd = some d_sr := by
      rw [hfs_sr]; simp only [FsState.setFd, beq_self_eq_true, ↓reduceIte]; rfl
    have hkind_sr : d_sr.kind = .localFile ∨ d_sr.kind = .localDir := Or.inl hkind
    rcases Nat.eq_zero_or_pos chunk.length with hn0 | hn_pos
    · have hwant_pos : 0 < want := wantBytes_pos (by omega : len ≤ 2097152)
      have hlen_eq_rem : len = rem.length := by omega
      have hrem_le_cap : rem.length ≤ cliIoFileCap := by omega
      have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
      have htake_rem : rem.take len = rem := by rw [hlen_eq_rem, List.take_length]
      refine SepWP.weaken_pre ?_
        (cliIoReadFile_after_read_eof_budget_reads A lim hA_mem hext3 hclose
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
          (st_cur := st_cur)
          (by dsimp [allocHookStack] at hlo; omega) hhi hfd_lt hfds_sr hkind_sr hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
          (by rw [hx0_sr, ← hchunk_def, hn0]) hw19_sr hx20_sr hx21_sr hx24_sr
          (by rw [hx28_sr, hlen_eq_rem]) hvregs_sr
          fun sf hpc_f hrun_f hsp_f hcs_f _ hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
            hpost sf hpc_f hrun_f hsp_f hcs_f
              (by rw [hfs_f, hfs_sr]; exact setFd_none_setFd_of_fds_none hfds_none)
              (htr_f.trans (htr_sr.trans htr_sl))
              (hsig_f.trans (hsig_sr.trans hsig_sl))
              (htp_f.trans (htp_sr.trans htp_sl))
              (hbs_f.trans (hbs_sr.trans hbs_sl))
              (Entails.trans hent ?_))
      · rw [htake_rem]
        let Rest : SepProp :=
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 8320#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
            cliIoVecBuf A.repAlloc (BitVec.ofNat 64 cap) ptr rem ∗ A.pool lim st_cur sr
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q := Rest) hbuf_back) (by dsimp only [Rest]; sep_entail))
        rw [← hrem_def, ← hchunk_def,
          pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
        dsimp only [Rest]; sep_entail
      · unfold cliIoFileLoopBudgetOut cliIoFileLoopBudgetEvents
        rw [← hrem_def]
        simp only [hrem_le_cap, ↓reduceIte]
        rw [hst_eq, hlen_eq_rem]
        exact Entails.refl _
    · by_cases hover : cliIoFileCap < len + chunk.length
      · have ⟨hlen_eq, hn_eq1, _⟩ :=
          overCap_forces_eq_max (K := 9) hlen_le hdvd hn_min hn_pos hover
        have hwant_eq1 : want = 1 := by rw [hwant_def, hlen_eq]; rfl
        have hidx9 : cliIoCapIdx 9 len = 9 := by rw [hlen_eq]; exact cliIoCapIdx_cap_self 9
        have hcap9 : cap = cliIoCap 9 := by rw [hcap_eq, cliIoFinalCap_pos (by omega), hidx9]
        have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
        refine SepWP.weaken_pre ?_
          (cliIoReadFile_after_read_overcap_budget_reads A lim hA_mem hext3 hdealloc hclose
            (v0 := v0) (v1 := v1) (v2 := v2)
            (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (bs := rem.take len) (st_in := st_cur)
            (by omega) hhi hfd_lt hfds_sr hkind_sr hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            (by rw [hx0_sr, ← hchunk_def, hn_eq1]) hw19_sr hx20_sr
            (by rw [hx21_sr, hcap9]) (by rw [hx23_sr, hwant_eq1]) hx24_sr hx26_sr
            (by rw [hx28_sr, hlen_eq]; rfl) hvregs_sr
            fun sf hpc_f hrun_f hsp_f hcs_f _ hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
              hpost sf hpc_f hrun_f hsp_f hcs_f
                (by rw [hfs_f, hfs_sr]; exact setFd_none_setFd_of_fds_none hfds_none)
                (htr_f.trans (htr_sr.trans htr_sl))
                (hsig_f.trans (hsig_sr.trans hsig_sl))
                (htp_f.trans (htp_sr.trans htp_sl))
                (hbs_f.trans (hbs_sr.trans hbs_sl))
                (Entails.trans hent ?_))
        · rw [hcap9]
          let Rest : SepProp :=
            stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 8320#64) 4096 ∗
              vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
              cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
              cliIoVecBuf A.repAlloc (BitVec.ofNat 64 (cliIoCap 9)) ptr (rem.take len) ∗
              A.pool lim st_cur sr
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono_left (Q := Rest) hbuf_back) (by dsimp only [Rest]; sep_entail))
          rw [← hrem_def, ← hchunk_def,
            pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
          dsimp only [Rest]; sep_entail
        · unfold cliIoFileLoopBudgetOut cliIoFileLoopBudgetEvents
          have hnot_le : ¬ rem.length ≤ cliIoFileCap := by omega
          rw [← hrem_def]
          simp only [hnot_le, ↓reduceIte]
          rw [hst_eq, stepEvents_dealloc_overCap M stInit hlen_eq]
          exact Entails.refl _
      · have hlen'_max : len + chunk.length ≤ cliIoFileCap := by omega
        have hlen'_le : len + chunk.length ≤ min rem.length cliIoFileCap :=
          Nat.le_min.mpr ⟨hn_le_rem, hlen'_max⟩
        have hdvd' : len + chunk.length < rem.length → 4096 ∣ (len + chunk.length) :=
          dvd_4096_preserved (K := 9) hlen_le hdvd hn_min hn_pos hlen'_max
        have hm_lt : cliIoFileCap + 1 - (len + chunk.length) < fuel := by omega
        by_cases hnogrow : len + chunk.length ≤ cap
        · have hlen_pos : 0 < len := by
            rcases Nat.eq_zero_or_pos len with rfl | hp
            · rw [cliIoFinalCap_zero] at hcap_eq; omega
            · exact hp
          let j := cliIoCapIdx 9 len
          have hj : j ≤ 9 := cliIoCapIdx_le 9 len
          have hcap_j : cap = cliIoCap j := by rw [hcap_eq, cliIoFinalCap_pos hlen_pos]
          have hcap_le_max : cap ≤ 2097152 := by rw [hcap_j]; exact cliIoCap_mono hj
          have hidx_eq : cliIoCapIdx 9 (len + chunk.length) = j :=
            no_grow_capIdx_eq hlen_pos (by omega) (by rwa [← hcap_j])
          have hcap'_eq : cap = cliIoFinalCap 9 (len + chunk.length) := by
            rw [cliIoFinalCap_pos (by omega), hidx_eq, hcap_j]
          have hsched_eq :
              cliIoReadScheduleCaps 9 (len + chunk.length) = cliIoReadScheduleCaps 9 len := by
            rw [cliIoReadScheduleCaps_eq_cliIoReadCaps, cliIoReadScheduleCaps_eq_cliIoReadCaps]
            unfold cliIoReadCaps
            have hne1 : len + chunk.length ≠ 0 := by omega
            have hne0 : len ≠ 0 := by omega
            dsimp only [j] at hidx_eq
            simp only [hne1, hne0, ↓reduceIte, hidx_eq]
          refine cliIoReadFile_after_read_nogrow_vm_reads hext3 hn_pos hn_le_want hwant_le
            hnogrow hcap_le_max hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            hx0_sr hw19_sr hx20_sr hx21_sr hx23_sr hx24_sr hx25_sr hx26_sr hx28_sr hx29_sr hvregs_sr
            fun sc hpc_sc hrun_sc hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc hx24_sc hx25_sc
                hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_srsc hvm_srsc => ?_
          have hpool_srsc : A.pool lim st_cur sr = A.pool lim st_cur sc :=
            (A.pool_transport lim st_cur sr sc hvm_srsc).symm
          refine SepWP.weaken_pre (by rw [hpool_srsc]; sep_entail)
            (cliIoReadFile_memcpy_backedge_budget_reads A lim hext3 hmemcpy
              (R_path := memRegion (s0.sp - 8320#64) 4096)
              (by rw [hcap_j]; exact cliIoCap_pos j) (by rw [hcap_j]; exact cliIoCap_lt_pow63 (by omega))
              hn_le_rem hnogrow hlen'_max hwant_le hold_len hn_le_want rfl
              hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc hx24_sc
              hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc
              fun sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                  hx26_sn hx28_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                ih (cliIoFileCap + 1 - (len + chunk.length)) hm_lt sn ptr st0 st1 st2 st3
                  cap (len + chunk.length) st_cur (Nat.le_refl _)
                  hlen'_le hdvd' hcap'_eq (by rw [hsched_eq]; exact hst_eq)
                  hcl_sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                  hx26_sn hx28_sn hx29_sn hvregs_sn
                  (hmid_scsn.1.trans (hacp_srsc.1.trans hfs_sr))
                  (hmid_scsn.2.1.trans (hacp_srsc.2.1.trans (htr_sr.trans htr_sl)))
                  (hmid_scsn.2.2.1.trans (hacp_srsc.2.2.1.trans (hsig_sr.trans hsig_sl)))
                  (hmid_scsn.2.2.2.1.trans (hacp_srsc.2.2.2.1.trans (htp_sr.trans htp_sl)))
                  (hmid_scsn.2.2.2.2.trans (hacp_srsc.2.2.2.2.1.trans (hbs_sr.trans hbs_sl))))
        · have hgt_cap : cap < len + chunk.length := by omega
          refine cliIoReadFile_after_read_grow_vm_reads hext3 hn_pos hn_le_want hwant_le
            hgt_cap hlen'_max hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            hx0_sr hw19_sr hx20_sr hx21_sr hx23_sr hx24_sr hx25_sr hx26_sr hx28_sr hx29_sr hvregs_sr
            fun sg hpc_sg hrun_sg hsp_sg hx0_sg hw19_sg hx20_sg hx21_sg hx24_sg hx25_sg
                hx26_sg hx27_sg hx28_sg hx29_sg hvregs_sg hcl_sg hacp_srsg hvm_srsg => ?_
          have hpool_srsg : A.pool lim st_cur sr = A.pool lim st_cur sg :=
            (A.pool_transport lim st_cur sr sg hvm_srsg).symm
          have hfs_sg : sg.fs = s0.fs.setFd fd
              (some { d0 with offset := d0.offset + (len + chunk.length) }) :=
            hacp_srsg.1.trans hfs_sr
          have htr_sg : sg.trace = s0.trace := hacp_srsg.2.1.trans (htr_sr.trans htr_sl)
          have hsig_sg : sg.sigActions = s0.sigActions := hacp_srsg.2.2.1.trans (hsig_sr.trans hsig_sl)
          have htp_sg : sg.tpidrEl0 = s0.tpidrEl0 := hacp_srsg.2.2.2.1.trans (htp_sr.trans htp_sl)
          have hbs_sg : sg.brkStart = s0.brkStart := hacp_srsg.2.2.2.2.1.trans (hbs_sr.trans hbs_sl)
          have hoom_pres_sg : ∀ sf_oom : State, OomPreserved sg sf_oom → CliIoFilesOomPreserved s0 sf_oom := by
            intro sf_oom hoom_s
            have hfiles : sf_oom.fs.files = s0.fs.files := by
              rw [hoom_s.1, hfs_sg]; rfl
            exact ⟨hfiles, hoom_s.2.1.trans htr_sg, hoom_s.2.2.trans hsig_sg⟩
          let R_buf : SepProp :=
            memRegion (s0.sp - 8320#64) 4096 ∗
              (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
                memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want))
          rcases Nat.eq_zero_or_pos len with rfl | hlen_pos
          · have hcap0 : cap = 0 := hcap_eq
            subst hcap0
            have hst0 : st_cur = stInit := by
              rw [hst_eq, cliIoReadScheduleCaps_eq_cliIoReadCaps]
              rfl
            have hidx0 : cliIoCapIdx 9 chunk.length = 0 :=
              cliIoCapIdx_eq_of_bounds (Nat.zero_le 9) (Or.inl rfl) (Nat.le_trans hn_le_want hwant_le)
            have hst_next0 :
                M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) stInit =
                  M.stepEvents (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 (0 + chunk.length))) stInit := by
              rw [Nat.zero_add, cliIoReadScheduleCaps_eq_cliIoReadCaps]
              unfold cliIoReadCaps cliIoFinishGrowBudgetEvents
              have hne : chunk.length ≠ 0 := by omega
              simp only [hne, ↓reduceIte, hidx0]
              rfl
            refine SepWP.weaken_pre (by rw [hpool_srsg, hst0]; dsimp only [R_buf]; sep_entail)
              (cliIoReadFile_grow_from_zero_budget_reads A lim hext3 hfg (R_buf := R_buf) (st_in := stInit)
                (by omega) hhi hn_pos (Nat.le_trans hn_le_want hwant_le)
                hcl_sg hpc_sg hrun_sg hsp0 hsp_sg
                hx0_sg hw19_sg hx20_sg hx21_sg hx24_sg hx25_sg hx26_sg
                (by rw [Nat.zero_add] at hx27_sg; exact hx27_sg) hx28_sg hx29_sg hvregs_sg
                (fun sf_oom hnf hoom_s =>
                  Entails.pure_right_only
                    ⟨not_fitsEvents_loop_of_grow_zero (by omega : 0 < rem.length) hnf,
                      hoom_pres_sg sf_oom hoom_s⟩
                    (Entails.refl _))
                fun sc newPtr st1' st2' hpc_sc hrun_sc hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc
                    hx24_sc hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_sgsc =>
                  SepWP.weaken_pre (by dsimp only [R_buf]; sep_entail)
                    (cliIoReadFile_memcpy_backedge_budget_reads A lim hext3 hmemcpy
                      (R_path := memRegion (s0.sp - 8320#64) 4096)
                      (cliIoCap_pos 0) (cliIoCap_lt_pow63 (by decide))
                      hn_le_rem (Nat.le_trans (by rw [Nat.zero_add]; exact hn_le_want) hwant_le)
                      hlen'_max hwant_le hold_len hn_le_want rfl
                      hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc hx24_sc
                      hx25_sc hx26_sc (by rw [Nat.zero_add]; exact hx27_sc) hx28_sc hx29_sc hvregs_sc
                      fun sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                          hx26_sn hx28_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                        ih (cliIoFileCap + 1 - (0 + chunk.length)) hm_lt sn newPtr 0#64 st1' st2' st3
                          (cliIoCap 0) (0 + chunk.length)
                          (M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 (cliIoCap 0)) stInit)
                          (Nat.le_refl _) hlen'_le hdvd'
                          (by simp [cliIoFinalCap_pos hn_pos, hidx0]) hst_next0
                          hcl_sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn
                          hx25_sn hx26_sn hx28_sn hx29_sn hvregs_sn
                          (hmid_scsn.1.trans (hacp_sgsc.1.trans hfs_sg))
                          (hmid_scsn.2.1.trans (hacp_sgsc.2.1.trans htr_sg))
                          (hmid_scsn.2.2.1.trans (hacp_sgsc.2.2.1.trans hsig_sg))
                          (hmid_scsn.2.2.2.1.trans (hacp_sgsc.2.2.2.1.trans htp_sg))
                          (hmid_scsn.2.2.2.2.trans (hacp_sgsc.2.2.2.2.1.trans hbs_sg))))
          · let j := cliIoCapIdx 9 len
            have hj : j ≤ 9 := cliIoCapIdx_le 9 len
            have hcap_j : cap = cliIoCap j := by rw [hcap_eq, cliIoFinalCap_pos hlen_pos]
            have hlen_le_j : len ≤ cliIoCap j := le_cliIoCap_cliIoCapIdx hlen_max
            have ⟨hj1, _, hidx_j1, hle_j1, _⟩ :=
              grow_step_bounds (K := 9) (by decide) hj hlen_le_j
                (Nat.le_trans hn_le_want hwant_le) hn_le_rem hlen'_max (by rwa [← hcap_j])
            have hcap_lt64 : cliIoCap j < 2 ^ 64 := cliIoCap_lt_pow64 hj
            have hcap_ne0 : BitVec.ofNat 64 (cliIoCap j) ≠ 0#64 :=
              beq_eq_false_iff_ne.mp
                (bv64_beq_ofNat_false (by have := cliIoCap_pos j; omega) hcap_lt64 (by decide))
            have hcap_toNat : (BitVec.ofNat 64 (cliIoCap j)).toNat = cliIoCap j := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64]
            have hst_next_pos :
                M.stepEvents
                    (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1))) st_cur =
                  M.stepEvents
                    (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 (len + chunk.length))) stInit := by
              rw [hst_eq, ← M.stepEvents_append, cliIoReadScheduleCaps_eq_cliIoReadCaps,
                cliIoReadScheduleCaps_eq_cliIoReadCaps]
              unfold cliIoReadCaps cliIoFinishGrowBudgetEvents
              have hne1 : len + chunk.length ≠ 0 := by omega
              have hne0 : len ≠ 0 := by omega
              have hj_def : cliIoCapIdx 9 len = j := rfl
              simp only [hne1, hne0, ↓reduceIte, hidx_j1, hj_def, hcap_ne0, hcap_toNat]
              rw [show j + 1 + 1 = j + 2 by omega, cliIoCapsEvents_range_succ' j]
            refine SepWP.weaken_pre (by rw [hpool_srsg, hcap_j]; dsimp only [R_buf]; sep_entail)
              (cliIoReadFile_grow_from_pos_budget_reads A lim hext3 hfg (R_buf := R_buf) (st_in := st_cur)
                (by omega) hhi hj1 hlen_le_j
                (List.length_take_of_le hlen_rem) (by rwa [← hcap_j]) hle_j1
                hcl_sg hpc_sg hrun_sg hsp0 hsp_sg
                hx0_sg hw19_sg hx20_sg (by rw [hx21_sg, hcap_j]) hx24_sg hx25_sg
                hx26_sg hx27_sg hx28_sg hx29_sg hvregs_sg
                (fun sf_oom hnf hoom_s =>
                  Entails.pure_right_only
                    ⟨not_fitsEvents_loop_of_grow_pos hlen_pos rfl hj1 hn_le_rem hidx_j1
                      (hst_eq ▸ hnf),
                      hoom_pres_sg sf_oom hoom_s⟩
                    (Entails.refl _))
                fun sc newPtr st1' st2' hpc_sc hrun_sc hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc
                    hx24_sc hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_sgsc =>
                  SepWP.weaken_pre (by dsimp only [R_buf]; sep_entail)
                    (cliIoReadFile_memcpy_backedge_budget_reads A lim hext3 hmemcpy
                      (R_path := memRegion (s0.sp - 8320#64) 4096)
                      (cliIoCap_pos (j + 1)) (cliIoCap_lt_pow63 (by omega))
                      hn_le_rem hle_j1 hlen'_max hwant_le hold_len hn_le_want rfl
                      hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc hx24_sc
                      hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc
                      fun sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                          hx26_sn hx28_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                        ih (cliIoFileCap + 1 - (len + chunk.length)) hm_lt sn newPtr 0#64 st1' st2' st3
                          (cliIoCap (j + 1)) (len + chunk.length)
                          (M.stepEvents
                            (cliIoFinishGrowBudgetEvents (BitVec.ofNat 64 (cliIoCap j)) (cliIoCap (j + 1)))
                            st_cur)
                          (Nat.le_refl _) hlen'_le hdvd'
                          (by rw [cliIoFinalCap_pos (by omega), hidx_j1]) hst_next_pos
                          hcl_sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn
                          hx25_sn hx26_sn hx28_sn hx29_sn hvregs_sn
                          (hmid_scsn.1.trans (hacp_sgsc.1.trans hfs_sg))
                          (hmid_scsn.2.1.trans (hacp_sgsc.2.1.trans htr_sg))
                          (hmid_scsn.2.2.1.trans (hacp_sgsc.2.2.1.trans hsig_sg))
                          (hmid_scsn.2.2.2.1.trans (hacp_sgsc.2.2.2.1.trans htp_sg))
                          (hmid_scsn.2.2.2.2.trans (hacp_sgsc.2.2.2.2.1.trans hbs_sg))))


end

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoLoopBudget
