/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.AllocZeroedHelpersFine
public import LibsignalBinary.Heap.IfaceBudgetBase

/-!
# Placed `__rustc::__rdl_alloc_zeroed` Verification

Verifies placed `__rustc::__rdl_alloc_zeroed` (tail-calling `calloc(size, 1)` when
`align ≤ 16 ∧ align ≤ size`, and calling `posix_memalign` + `memset` otherwise) together with its
1-instruction `B`-thunk (`__rust_alloc_zeroed`) against `rustAllocZeroedBudgetSpec`, instantiated at
both parametric `AllocCostModel` and `fineCostModel`.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj Arm64.CType ProofLib.SepLogic ProofLib.ProgramReflection ProofLib.StdStartup
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries
open VerifiedLibraries.Mallocng hiding AllocCostModel AllocEvent MallocngCostModelIface
  MallocngCostModelSound MallocngModelEnv MallocngModelPlacedEntryContracts
  MallocngModelPostEnv MallocngStepOomCond
open VerifiedLibraries.Mallocng.Proofs (
  ProgContainsMallocng effAlign_props isPow2Align_alignedAllocOk
  isPow2Align_of_toNat_pow2 not_layoutFit_imp_gt_2pow62
  pow2_dvd_16_of_le_16 pow2_dvd_max16
)
open VerifiedLibraries.RustStd (
  MallocngCEntryAddrs RustStdRdlShimCode RustStdThunkCode
  allocCallPreserved_trans fetch_instr_at fetch_instr_at0
  hookFrame_eq_stack1024 mallocngPlacedCAddrs
)
open LibsignalBinary.Heap
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpecBase)
open AllocZeroedHelpers

attribute [local simp] Memory.perm_write8 Memory.perm_write16 Memory.perm_write32
  Memory.perm_write64 Memory.perm_writeBytes

/-! ## Placed `__rdl_alloc_zeroed` Verification -/

private theorem rdlAllocZeroed_budget_fast_path {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart callocAddr : BitVec 64} {lim : BudgetLimits}
    (hCalloc : subroutine_ok P callocAddr (mallocngBudgetCallocCSpec M I γ mAddrs tp brkStart lim))
    (sizeBv alignBv : BitVec 64) (st : M.σ) (R : SepProp) (s0 s1 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAl16 : alignBv.toNat ≤ 16)
    (hAlSz : alignBv.toNat ≤ sizeBv.toNat)
    (hpc1 : s1.pc = callocAddr) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp) (hx0_1 : s1.readReg64 .x0 = sizeBv) (hx1_1 : s1.readReg64 .x1 = 1#64)
    (hlr1 : s1.readReg64 Reg.lr = s0.readReg64 Reg.lr)
    (hcs1 : CalleeSavedPreserved s0 s1)
    (hpres01 : AllocCallPreserved s0 s1) (hvm01 : VmPreserved s0 s1) :
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let xR := (sizeBv.toNat, alignBv.toNat, st)
    SepWP P (s0.readReg64 Reg.lr) s1
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗ Rust.hookFrame s0.sp)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustCliAllocBudgetSpecBase M A lim true).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustCliAllocBudgetSpecBase M A lim true).onOom xR s0 sf) := by
  intro A xR
  have hTot : sizeBv.toNat * (1#64).toNat = sizeBv.toNat := Nat.mul_one sizeBv.toNat
  have hEvs : rustAllocEvents sizeBv.toNat alignBv.toNat = [.alloc sizeBv.toNat] := by
    unfold rustAllocEvents; simp [hAl16, hAlSz]
  have hEff : mallocngAlignedEffSize alignBv.toNat sizeBv.toNat = sizeBv.toNat := by
    unfold mallocngAlignedEffSize; simp [hAl16]
  have hOkEq :
      decide (sizeBv.toNat ≤ MallocngMaxAllocSize) = decide (MallocngLayoutFit sizeBv alignBv) := by
    simp [MallocngLayoutFit, hEff]
  have hPool1 :
      mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 =
        mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s1 :=
    (mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st hvm01).symm
  let F := stackFrameAt (s0.sp - 1024#64) 3072
  refine SepWP.call_subroutine_frame (F := F) (x := (sizeBv, 1#64, st)) hCalloc
    (ret_pc := s0.readReg64 Reg.lr)
    hpc1 hrun1 (by simpa [State.spAligned, hsp1] using hsp_align) hlr1
    (fun R' hsat => ?_)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun R' sf _ ho => ?_)
  · dsimp only [mallocngBudgetCallocCSpec, F]
    rw [hookFrame_eq_stack1024 s0.sp, hPool1] at hsat
    rw [hsp1]
    have hsat' : s1.mem ⊨
        (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s1 ∗
          stackFrameAt s0.sp mallocngStackBytes) ∗
        (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R') :=
      Satisfies.mono (Entails.of_eq (by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s1 = Ppool
        generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
        ac_rfl)) hsat
    exact Satisfies.mono (sepConj_mono_left (Entails.pure_right ⟨hx0_1, hx1_1⟩ (Entails.refl _))) hsat'
  · refine SepWP.done hpc_f hrun_f
      ⟨fun hsat => ?_, hsp_f.trans hsp1, calleeSavedPreserved_trans hcs1 hcs_f⟩
    dsimp only [mallocngBudgetCallocCSpec, F] at hsat
    dsimp only [rustCliAllocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt, xR]
    rw [hTot, hOkEq, hsp1] at hsat
    rw [hEvs, stackAt_eq_hookFrame s0.sp]
    by_cases hFit : MallocngLayoutFit sizeBv alignBv
    · rw [decide_eq_true hFit] at hsat
      simp only [↓reduceIte] at hsat ⊢
      refine Satisfies.mono ?_ hsat
      have hPull :
          ((⌜AllocCallPreserved s1 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim (M.step (.alloc sizeBv.toNat) st) sf ∗
            stackFrameAt s0.sp mallocngStackBytes ∗
            (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + sizeBv.toNat < 2 ^ 64⌝ ∗
              I.BlockM γ (sf.readReg64 .x0) sizeBv.toNat 16 ∗
              (sf.readReg64 .x0 ↦ₛ List.replicate sizeBv.toNat 0#8))) ∗
           stackFrameAt (s0.sp - 1024#64) 3072) ∗ R =
          ⌜AllocCallPreserved s1 sf⌝ ∗
            (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + sizeBv.toNat < 2 ^ 64⌝ ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim (M.step (.alloc sizeBv.toNat) st) sf ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ stackFrameAt (s0.sp - 1024#64) 3072) ∗
                I.BlockM γ (sf.readReg64 .x0) sizeBv.toNat 16 ∗
                (sf.readReg64 .x0 ↦ₛ List.replicate sizeBv.toNat 0#8) ∗ R)) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim
          (M.step (.alloc sizeBv.toNat) st) sf = Ppool
        generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
        ac_rfl
      rw [hPull, ← hookFrame_eq_stack1024 s0.sp]
      refine Entails.pure_left fun hAcc1 => Entails.pure_left fun ⟨hNe, h16, hFit64⟩ => ?_
      have hNe0 : sf.readReg64 .x0 ≠ 0 := hNe
      simp only [hNe0, ↓reduceIte, AllocCostModel.stepEvents_cons,
        AllocCostModel.stepEvents_nil]
      have hAlDvd : alignBv.toNat ∣ (sf.readReg64 .x0).toNat :=
        Nat.dvd_trans (pow2_dvd_16_of_le_16 hPow2 hAl16) h16
      have hMod : (sf.readReg64 .x0).toNat % alignBv.toNat = 0 := Nat.mod_eq_zero_of_dvd hAlDvd
      have hPres0f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres01 hAcc1
      have hLive := packLiveM_16 (M := M) (I := I) γ hAl16 hNe hAlDvd h16 hFit64 hLayout
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hLive))) ?_
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim (M.step (.alloc sizeBv.toNat) st) sf ∗
            Rust.hookFrame s0.sp ∗
            (⌜(sf.readReg64 .x0).toNat % alignBv.toNat = 0⌝ ∗
              mallocngLiveM M I γ (sf.readReg64 .x0) sizeBv.toNat alignBv.toNat ∗
              (sf.readReg64 .x0 ↦ₛ List.replicate sizeBv.toNat 0#8))) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜(sf.readReg64 .x0).toNat % alignBv.toNat = 0⌝ ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim (M.step (.alloc sizeBv.toNat) st) sf ∗
                (Rust.hookFrame s0.sp ∗
                  (mallocngLiveM M I γ (sf.readReg64 .x0) sizeBv.toNat alignBv.toNat ∗
                    ((sf.readReg64 .x0 ↦ₛ List.replicate sizeBv.toNat 0#8) ∗ R))))) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim
          (M.step (.alloc sizeBv.toNat) st) sf = Ppool
        generalize Rust.hookFrame s0.sp = Phook
        generalize mallocngLiveM M I γ (sf.readReg64 .x0) sizeBv.toNat alignBv.toNat = Plive
        ac_rfl
      rw [hGoalEq]
      exact Entails.pure_right hPres0f (Entails.pure_right hMod (Entails.refl _))
    · rw [decide_eq_false hFit] at hsat
      simp only [Bool.false_eq_true, ↓reduceIte] at hsat
      have hNull : NullAllowed sizeBv.toNat alignBv.toNat := not_layoutFit_imp_gt_2pow62 hFit
      refine Satisfies.mono ?_ hsat
      have hPull :
          ((⌜AllocCallPreserved s1 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
            stackFrameAt s0.sp mallocngStackBytes ∗
            ⌜sf.readReg64 .x0 = 0#64⌝) ∗
           stackFrameAt (s0.sp - 1024#64) 3072) ∗ R =
          ⌜AllocCallPreserved s1 sf⌝ ∗
            (⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ stackFrameAt (s0.sp - 1024#64) 3072) ∗ R)) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf = Ppool
        generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
        ac_rfl
      rw [hPull, ← hookFrame_eq_stack1024 s0.sp]
      refine Entails.pure_left fun hAcc1 => Entails.pure_left fun hret0 => ?_
      have hret0' : sf.readReg64 .x0 = 0 := hret0
      simp only [hret0', ↓reduceIte]
      have hPres0f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres01 hAcc1
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
            Rust.hookFrame s0.sp ∗
            ⌜NullAllowed sizeBv.toNat alignBv.toNat⌝) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
                (Rust.hookFrame s0.sp ∗ R))) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf = Ppool
        generalize Rust.hookFrame s0.sp = Phook
        ac_rfl
      rw [hGoalEq]
      exact Entails.pure_right hPres0f (Entails.pure_right hNull (Entails.refl _))
  · dsimp only [mallocngBudgetCallocCSpec] at ho
    dsimp only [rustCliAllocBudgetSpecBase, A, xR]
    rw [hTot] at ho
    rw [hEvs]
    rw [satisfies_pure_sepConj] at ho ⊢
    obtain ⟨⟨hNotFit, hOom1f⟩, hFR⟩ := ho
    have hNotEvs : ¬ FitsEvents M lim st [.alloc sizeBv.toNat] := fun h => hNotFit h.1
    exact ⟨⟨hNotEvs, oomPreserved_of_allocCallPreserved hpres01 hOom1f⟩, Satisfies.drop_left hFR⟩

private theorem rdlAllocZeroed_budget_epilogue {P : Program}
    {allocZeroedAddr callocAddr posixMemalignAddr memsetAddr : BitVec 64}
    (hCode : hasInstrs P allocZeroedAddr
      (rdlAllocZeroedInstrs allocZeroedAddr callocAddr posixMemalignAddr memsetAddr))
    (s0 s4 : State) (w0 qSlot retVal : BitVec 64) (Rest : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp)
    (hsp_align : s0.spAligned = true)
    (hpc4 : s4.pc = allocZeroedAddr + 0x80#64)
    (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = s0.sp - 48#64)
    (hx0_4 : s4.readReg64 .x0 = retVal)
    (hcs4 : ∀ r ∈ ([.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      s4.readReg64 r = s0.readReg64 r)
    (hv4 : calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hpost : ∀ sf : State,
      sf.readReg64 .x0 = retVal →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      AllocCallPreserved s4 sf →
      VmPreserved s4 sf →
      post sf (Rust.hookFrame s0.sp ∗ Rest)) :
    SepWP P (s0.readReg64 Reg.lr) s4
      ((((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ qSlot) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
       (stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 48#64 - 1024#64) 3024) ∗ Rest)
      post oom := by
  have hf32 := fetch_instr_at 32 hCode
  have hf33 := fetch_instr_at 33 hCode
  have hf34 := fetch_instr_at 34 hCode
  have hf35 := fetch_instr_at 35 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl48 : decide (s4.sp &&& 15#64 = 0#64) = true := by
    rw [hsp4]; exact decide_eq_true (beq_iff_eq.mp (spAligned_sub48 hspAl0))
  wp_step; wp_step; wp_step; wp_step
  have hRepack :
      ((((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ qSlot) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
       (stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 48#64 - 1024#64) 3024) ∗ Rest) ⊢
      Rust.hookFrame s0.sp ∗ Rest := by
    rw [← sepConj_assoc]
    exact sepConj_mono_left (repack_hookFrame_48 s0.sp w0 qSlot _ _ _ _)
  refine SepWP.weaken_pre hRepack ?_
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun4]) ?_
  refine hpost _ (by simp [arm64_norm, hx0_4]) (by simp [arm64_norm]) ?_
    (by unfold AllocCallPreserved; simp [arm64_norm])
    (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
  refine ⟨by simp [arm64_norm],
    by simp [arm64_norm],
    by simpa [arm64_norm] using hcs4 .x21 (by simp),
    by simpa [arm64_norm] using hcs4 .x22 (by simp),
    by simpa [arm64_norm] using hcs4 .x23 (by simp),
    by simpa [arm64_norm] using hcs4 .x24 (by simp),
    by simpa [arm64_norm] using hcs4 .x25 (by simp),
    by simpa [arm64_norm] using hcs4 .x26 (by simp),
    by simpa [arm64_norm] using hcs4 .x27 (by simp),
    by simpa [arm64_norm] using hcs4 .x28 (by simp),
    by simp [arm64_norm], by simpa [calleeSavedVRegs, arm64_norm] using hv4⟩

private theorem rdlAllocZeroed_budget_memset_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart callocAddr memsetAddr : BitVec 64}
    {cAddrs : MallocngCEntryAddrs} {lim : BudgetLimits} (allocZeroedAddr : BitVec 64)
    (hCode : hasInstrs P allocZeroedAddr
      (rdlAllocZeroedInstrs allocZeroedAddr callocAddr cAddrs.posixMemalign memsetAddr))
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec)
    (sizeBv alignBv w0 q : BitVec 64) (st stOk : M.σ) (R : SepProp) (s0 s3 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv)
    (hEvs : rustAllocEvents sizeBv.toNat alignBv.toNat =
      [.aligned (max alignBv.toNat 8) sizeBv.toNat])
    (hstOk : stOk = M.step (.aligned (max alignBv.toNat 8) sizeBv.toNat) st)
    (hqNe : q ≠ 0#64) (hqDvd : max alignBv.toNat 16 ∣ q.toNat)
    (hqFit64 : q.toNat + sizeBv.toNat < 2 ^ 64)
    (hw0_3 : s3.readReg32 .x0 = 0#32)
    (hpc3 : s3.pc = allocZeroedAddr + 0x58#64) (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 48#64) (hx19_3 : s3.readReg64 .x19 = sizeBv)
    (hcs3 : ∀ r ∈ ([.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      s3.readReg64 r = s0.readReg64 r)
    (hv3 : calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hpres03 : AllocCallPreserved s0 s3) :
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let xR := (sizeBv.toNat, alignBv.toNat, st)
    SepWP P (s0.readReg64 Reg.lr) s3
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 ∗
        stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 ∗
        ((s0.sp - 48#64) ↦₆₄ w0) ∗
        ((s0.sp - 40#64) ↦₆₄ q) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        I.BlockM γ q sizeBv.toNat (max alignBv.toNat 16) ∗
        memRegion q sizeBv.toNat)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustCliAllocBudgetSpecBase M A lim true).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustCliAllocBudgetSpecBase M A lim true).onOom xR s0 sf) := by
  intro A xR
  have hf22 := fetch_instr_at 22 hCode
  have hf23 := fetch_instr_at 23 hCode
  have hf24 := fetch_instr_at 24 hCode
  have hf25 := fetch_instr_at 25 hCode
  have hf26 := fetch_instr_at 26 hCode
  have hf27 := fetch_instr_at 27 hCode
  have hf28 := fetch_instr_at 28 hCode
  have hf29 := fetch_instr_at 29 hCode
  have hf30 := fetch_instr_at 30 hCode
  have hf31 := fetch_instr_at 31 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  have hspAl48 : decide (s3.sp &&& 15#64 = 0#64) = true := by
    rw [hsp3]; exact decide_eq_true (beq_iff_eq.mp hspAl48b)
  have ha40_3 : s3.sp + 8#64 = s0.sp - 40#64 := by rw [hsp3]; bv_omega
  wp_step; wp_step; wp_step
  have hcbnz0 : (BitVec.zeroExtend 64 (BitVec.truncate 32 (s3.readReg64 (.gpr 0#5))) == 0#64) = true := by
    have hw32 : BitVec.truncate 32 (s3.readReg64 (.gpr 0#5)) = 0#32 := hw0_3
    rw [hw32]; rfl
  conv => arg 3; simp only [arm64_norm, hcbnz0, not_true_eq_false, Bool.false_eq_true, ↓reduceIte]
  wp_step; wp_step
  have hqBeq : (q == 0#64) = false := beq_eq_false_iff_ne.mpr hqNe
  conv => arg 3; simp only [arm64_norm, hqBeq, Bool.false_eq_true, ↓reduceIte]
  wp_step; wp_step; wp_step; wp_step
  let retMemsetPC := allocZeroedAddr + 0x7c#64
  let FrameM :=
    (((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ q) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
    (stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
      stackFrameAt (s0.sp - 48#64 - 1024#64) 3024) ∗
    mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 ∗
    I.BlockM γ q sizeBv.toNat (max alignBv.toNat 16)
  have hMemsetPre :
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 ∗
        stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 ∗
        ((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ q) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        I.BlockM γ q sizeBv.toNat (max alignBv.toNat 16) ∗
        memRegion q sizeBv.toNat) =
      (memRegion q sizeBv.toNat ∗ FrameM) := by
    dsimp only [FrameM]
    generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 = Ppool
    generalize stackFrameAt (s0.sp - 48#64) mallocngStackBytes = Pstk1
    generalize stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 = Pstk2
    ac_rfl
  rw [hMemsetPre]
  refine SepWP.call_subroutine_frame (F := FrameM) (x := (q, 0#8, sizeBv.toNat)) hMemset
    (ret_pc := retMemsetPC)
    (by simp only [arm64_norm]; bv_omega)
    (by simp [arm64_norm, hrun3])
    (by simpa [State.spAligned, arm64_norm, hsp3] using hspAl48b)
    (by simp [arm64_norm, retMemsetPC])
    (fun R' hsat => ?_)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun s5 hpc5 hrun5 hsp5 hcs5 => ?_)
    (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  · dsimp only [allocMemsetVmSpec]
    rw [sepConj_assoc] at hsat
    refine Satisfies.mono (sepConj_mono_left ?_) hsat
    refine Entails.pure_right ⟨by simp [arm64_norm], by simp [arm64_norm], ?_, sizeBv.isLt⟩ (Entails.refl _)
    simp [arm64_norm, BitVec.ofNat_toNat]
  · dsimp only [allocMemsetVmSpec, retMemsetPC] at hpc5 ⊢
    simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_hx0_5, hpres45, hvm45⟩
    obtain ⟨_, e20, e21, e22, e23, e24, e25, e26, e27, e28, _, ev⟩ := hcs5
    have hx20_5 : s5.readReg64 .x20 = q := by simpa [arm64_norm] using e20
    have hsp50 : s5.sp = s0.sp - 48#64 := by simpa [arm64_norm] using hsp5.trans hsp3
    have hcs5_regs : ∀ r ∈ ([.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
        s5.readReg64 r = s0.readReg64 r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact e21.trans (by simpa [arm64_norm] using hcs3 .x21 (by simp))
      · exact e22.trans (by simpa [arm64_norm] using hcs3 .x22 (by simp))
      · exact e23.trans (by simpa [arm64_norm] using hcs3 .x23 (by simp))
      · exact e24.trans (by simpa [arm64_norm] using hcs3 .x24 (by simp))
      · exact e25.trans (by simpa [arm64_norm] using hcs3 .x25 (by simp))
      · exact e26.trans (by simpa [arm64_norm] using hcs3 .x26 (by simp))
      · exact e27.trans (by simpa [arm64_norm] using hcs3 .x27 (by simp))
      · exact e28.trans (by simpa [arm64_norm] using hcs3 .x28 (by simp))
    have hv5 : calleeSavedVRegs s5 = calleeSavedVRegs s0 :=
      ev.trans (by simpa [calleeSavedVRegs, arm64_norm] using hv3)
    have hpres35 : AllocCallPreserved s3 s5 :=
      allocCallPreserved_trans
        (allocCallPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]))
        hpres45
    have hvm35 : VmPreserved s3 s5 :=
      vmPreserved_trans
        (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]))
        hvm45
    let RestZero :=
      mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 ∗
        I.BlockM γ q sizeBv.toNat (max alignBv.toNat 16) ∗
        (q ↦ₛ List.replicate sizeBv.toNat 0#8)
    have hPreEp :
        ((q ↦ₛ List.replicate sizeBv.toNat 0#8) ∗ FrameM) =
        ((((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ q) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
         (stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
          stackFrameAt (s0.sp - 48#64 - 1024#64) 3024) ∗ RestZero) := by
      dsimp only [FrameM, RestZero]
      generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 = Ppool
      generalize stackFrameAt (s0.sp - 48#64) mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 = Pstk2
      ac_rfl
    rw [hPreEp]
    wp_step
    refine rdlAllocZeroed_budget_epilogue hCode s0 _ w0 q q RestZero _ _ hsp_align
      (by simp only [arm64_norm]) (by simp [arm64_norm, hrun5])
      (by simp [arm64_norm, hsp50]) (by simp [arm64_norm])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simpa [arm64_norm] using hcs5_regs _ (by simp))
      (by simpa [calleeSavedVRegs, arm64_norm] using hv5)
      fun sf hx0f hspf hcsf hpres6f hvm6f => ?_
    refine ⟨fun hsat => ?_, hspf, hcsf⟩
    have hpres5f : AllocCallPreserved s5 sf :=
      allocCallPreserved_trans
        (allocCallPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]))
        hpres6f
    have hvm5f : VmPreserved s5 sf :=
      vmPreserved_trans
        (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]))
        hvm6f
    have hPres0f : AllocCallPreserved s0 sf :=
      allocCallPreserved_trans hpres03 (allocCallPreserved_trans hpres35 hpres5f)
    have hvm3f : VmPreserved s3 sf := vmPreserved_trans hvm35 hvm5f
    have hPoolSf :
        mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 =
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf :=
      (mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim stOk hvm3f).symm
    have hqNe0 : q ≠ 0 := hqNe
    have hAlDvd : alignBv.toNat ∣ q.toNat := Nat.dvd_trans (pow2_dvd_max16 hPow2) hqDvd
    have h16Dvd : 16 ∣ q.toNat := Nat.dvd_trans (sixteen_dvd_max16_of_layoutOk hLayout) hqDvd
    have hMod : q.toNat % alignBv.toNat = 0 := Nat.mod_eq_zero_of_dvd hAlDvd
    dsimp only [rustCliAllocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt, xR, RestZero] at hsat ⊢
    rw [hEvs, stackAt_eq_hookFrame s0.sp]
    simp only [hx0f, hqNe0, ↓reduceIte, AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil, ← hstOk]
    rw [hPoolSf] at hsat
    refine Satisfies.mono (sepConj_mono_left ?_) hsat
    have hLive := packLiveM (M := M) (I := I) γ hqNe hAlDvd h16Dvd hqFit64 hLayout
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hLive))) ?_
    have hGoalEq :
        ⌜AllocCallPreserved s0 sf⌝ ∗
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf ∗
          Rust.hookFrame s0.sp ∗
          (⌜q.toNat % alignBv.toNat = 0⌝ ∗
            mallocngLiveM M I γ q sizeBv.toNat alignBv.toNat ∗
            (q ↦ₛ List.replicate sizeBv.toNat 0#8)) =
        ⌜AllocCallPreserved s0 sf⌝ ∗
          (⌜q.toNat % alignBv.toNat = 0⌝ ∗
            (Rust.hookFrame s0.sp ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf ∗
                (mallocngLiveM M I γ q sizeBv.toNat alignBv.toNat ∗
                  (q ↦ₛ List.replicate sizeBv.toNat 0#8))))) := by
      generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf = Ppool
      generalize Rust.hookFrame s0.sp = Phook
      generalize mallocngLiveM M I γ q sizeBv.toNat alignBv.toNat = Plive
      ac_rfl
    rw [hGoalEq]
    exact Entails.pure_right hPres0f (Entails.pure_right hMod (Entails.refl _))

private theorem rdlAllocZeroed_budget_posix_call {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart callocAddr memsetAddr : BitVec 64}
    {cAddrs : MallocngCEntryAddrs} {lim : BudgetLimits} (allocZeroedAddr : BitVec 64)
    (hCode : hasInstrs P allocZeroedAddr
      (rdlAllocZeroedInstrs allocZeroedAddr callocAddr cAddrs.posixMemalign memsetAddr))
    (hPosix : subroutine_ok P cAddrs.posixMemalign
      (mallocngBudgetPosixMemalignCSpec M I γ mAddrs tp brkStart lim))
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec)
    (sizeBv alignBv w0 : BitVec 64) (st : M.σ) (R : SepProp) (s0 s2 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign)
    (hSlow : ¬ (alignBv.toNat ≤ 16 ∧ alignBv.toNat ≤ sizeBv.toNat)) :
    let effAlign := if ConditionHolds .HI (subsPState64 alignBv 8#64) then alignBv else 8#64
    let retPC := allocZeroedAddr + 0x58#64
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let xR := (sizeBv.toNat, alignBv.toNat, st)
    s2.pc = cAddrs.posixMemalign →
    s2.status = .Running →
    s2.sp = s0.sp - 48#64 →
    s2.readReg64 .x0 = s0.sp - 40#64 →
    s2.readReg64 .x1 = effAlign →
    s2.readReg64 .x2 = sizeBv →
    s2.readReg64 .x19 = sizeBv →
    s2.readReg64 Reg.lr = retPC →
    (∀ r ∈ ([.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      s2.readReg64 r = s0.readReg64 r) →
    calleeSavedVRegs s2 = calleeSavedVRegs s0 →
    AllocCallPreserved s0 s2 →
    VmPreserved s0 s2 →
    SepWP P (s0.readReg64 Reg.lr) s2
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
        stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 ∗
        ((s0.sp - 48#64) ↦₆₄ w0) ∗
        ((s0.sp - 40#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustCliAllocBudgetSpecBase M A lim true).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustCliAllocBudgetSpecBase M A lim true).onOom xR s0 sf) := by
  intro effAlign retPC A xR hpc2 hrun2 hsp2 hx0_2 hx1_2 hx2_2 hx19_2 hlr2 hcs2 hv2 hpres02 hvm02
  have hEvs :
      rustAllocEvents sizeBv.toNat alignBv.toNat =
        [.aligned (max alignBv.toNat 8) sizeBv.toNat] := by
    unfold rustAllocEvents; simp [hSlow]
  obtain ⟨hEffNat, hEffGe8, hEffMax, hPowEff, hEffMax16, _hEffSz, hPosixOk, hPosixRet⟩ :=
    effAlign_props (size := sizeBv) hPow2 hAlMax
  change effAlign.toNat = max alignBv.toNat 8 at hEffNat
  change 8 ≤ effAlign.toNat at hEffGe8
  change effAlign.toNat ≤ MaxAlignedAllocAlign at hEffMax
  change IsPow2Align effAlign at hPowEff
  change max effAlign.toNat 16 = max alignBv.toNat 16 at hEffMax16
  change mallocngPosixMemalignOk effAlign sizeBv = _ at hPosixOk
  change mallocngPosixMemalignRet effAlign sizeBv = _ at hPosixRet
  have hEffAlOk : alignedAllocAlignOk effAlign = true := isPow2Align_alignedAllocOk hPowEff
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  let FrameF := stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 ∗
    ((s0.sp - 48#64) ↦₆₄ w0) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  let xP := (s0.sp - 40#64, effAlign, sizeBv, st)
  refine SepWP.call_subroutine_frame (F := FrameF) (x := xP) hPosix (ret_pc := retPC)
    hpc2 hrun2 (by simpa [State.spAligned, hsp2] using hspAl48b) hlr2
    (fun R' hsat => ?_)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun s3 hpc3 hrun3 hsp3 hcs3 => ?_)
    (fun R' sf _ ho => ?_)
  · dsimp only [mallocngBudgetPosixMemalignCSpec, xP, FrameF]
    have hPool2 :
        mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 =
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s2 :=
      (mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st hvm02).symm
    rw [hPool2] at hsat
    rw [hsp2]
    have hsat' : s2.mem ⊨
        (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s2 ∗
          ((s0.sp - 40#64) ↦₆₄ 0#64) ∗
          stackFrameAt (s0.sp - 48#64) mallocngStackBytes) ∗
        (FrameF ∗ R') :=
      Satisfies.mono (Entails.of_eq (by
        dsimp only [FrameF]
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s2 = Ppool
        generalize stackFrameAt (s0.sp - 48#64) mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 = Pstk2
        ac_rfl)) hsat
    refine Satisfies.mono (sepConj_mono_left ?_) hsat'
    refine Entails.pure_right ⟨hx0_2, hx1_2, hx2_2, hEffMax⟩ ?_
    exact sepConj_mono_right (sepConj_mono_left ((IsBlock.pointsTo64 (s0.sp - 40#64) 0#64).entails_memRegion))
  · obtain ⟨d19, _, d21, d22, d23, d24, d25, d26, d27, d28, _, dv⟩ := hcs3
    have hx19_3 : s3.readReg64 .x19 = sizeBv := d19.trans hx19_2
    have hcs3_regs : ∀ r ∈ ([.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
        s3.readReg64 r = s0.readReg64 r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact d21.trans (hcs2 .x21 (by simp))
      · exact d22.trans (hcs2 .x22 (by simp))
      · exact d23.trans (hcs2 .x23 (by simp))
      · exact d24.trans (hcs2 .x24 (by simp))
      · exact d25.trans (hcs2 .x25 (by simp))
      · exact d26.trans (hcs2 .x26 (by simp))
      · exact d27.trans (hcs2 .x27 (by simp))
      · exact d28.trans (hcs2 .x28 (by simp))
    have hv3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := dv.trans hv2
    have hsp3' : s3.sp = s0.sp - 48#64 := hsp3.trans hsp2
    dsimp only [retPC] at hpc3
    dsimp only [mallocngBudgetPosixMemalignCSpec, xP]
    rw [hPosixOk, hPosixRet, hEffMax16, hEffNat, hsp2]
    simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hAcc23, hw0_3⟩
    have hpres03 : AllocCallPreserved s0 s3 := allocCallPreserved_trans hpres02 hAcc23
    by_cases hFit : MallocngLayoutFit sizeBv alignBv
    · rw [decide_eq_true hFit]
      simp only [hFit, ↓reduceIte, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] at hw0_3 ⊢
      apply SepWP.exists_elim; intro q
      let stOk := M.step (.aligned (max alignBv.toNat 8) sizeBv.toNat) st
      have hPullQ :
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 ∗
            stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
            ⌜q ≠ 0#64 ∧ max alignBv.toNat 16 ∣ q.toNat ∧ q.toNat + sizeBv.toNat < 2 ^ 64⌝ ∗
            ((s0.sp - 40#64) ↦₆₄ q) ∗
            I.BlockM γ q sizeBv.toNat (max alignBv.toNat 16) ∗
            memRegion q sizeBv.toNat ∗ FrameF =
          ⌜q ≠ 0#64 ∧ max alignBv.toNat 16 ∣ q.toNat ∧ q.toNat + sizeBv.toNat < 2 ^ 64⌝ ∗
            (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 ∗
              stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
              stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 ∗
              ((s0.sp - 48#64) ↦₆₄ w0) ∗
              ((s0.sp - 40#64) ↦₆₄ q) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
              ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
              ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
              I.BlockM γ q sizeBv.toNat (max alignBv.toNat 16) ∗
              memRegion q sizeBv.toNat) := by
        dsimp only [FrameF]
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 = Ppool
        generalize stackFrameAt (s0.sp - 48#64) mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 = Pstk2
        ac_rfl
      rw [hPullQ]
      apply SepWP.pure_elim; rintro ⟨hqNe, hqDvd, hqFit64⟩
      exact rdlAllocZeroed_budget_memset_ok hS γ allocZeroedAddr hCode hMemset
        sizeBv alignBv w0 q st stOk R s0 s3
        hsp_align hLayout hPow2 hEvs rfl hqNe hqDvd hqFit64 hw0_3
        hpc3 hrun3 hsp3' hx19_3 hcs3_regs hv3 hpres03
    · rw [decide_eq_false hFit]
      simp only [hFit, Bool.false_eq_true, ↓reduceIte] at hw0_3 ⊢
      have hNull : NullAllowed sizeBv.toNat alignBv.toNat := not_layoutFit_imp_gt_2pow62 hFit
      apply SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (memRegion8_entails_pointsTo64 (s0.sp - 40#64)))))
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro q
      let RestFail := mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s3
      have hCollapseFail :
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s3 ∗
            (stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
              (((s0.sp - 40#64) ↦₆₄ q) ∗ FrameF)) ⊢
          ((((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ q) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
           (stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
            stackFrameAt (s0.sp - 48#64 - 1024#64) 3024) ∗ RestFail) := by
        dsimp only [FrameF, RestFail]
        exact Entails.of_eq (by
          generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s3 = Ppool
          generalize stackFrameAt (s0.sp - 48#64) mallocngStackBytes = Pstk1
          generalize stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 = Pstk2
          ac_rfl)
      refine SepWP.weaken_pre hCollapseFail ?_
      have hf22 := fetch_instr_at 22 hCode
      have hf23 := fetch_instr_at 23 hCode
      have hf24 := fetch_instr_at 24 hCode
      wp_step; wp_step; wp_step
      have hcbnz12 : (BitVec.zeroExtend 64 (BitVec.truncate 32 (s3.readReg64 (.gpr 0#5))) == 0#64) = false := by
        have hw32 : BitVec.truncate 32 (s3.readReg64 (.gpr 0#5)) = 12#32 := hw0_3
        rw [hw32]; rfl
      refine rdlAllocZeroed_budget_epilogue hCode s0 _ w0 q 0#64 RestFail _ _ hsp_align
        (by simp only [arm64_norm, hcbnz12, Bool.false_eq_true, not_false_eq_true, ↓reduceIte])
        (by simp [arm64_norm, hrun3]) (by simp [arm64_norm, hsp3']) (by simp [arm64_norm])
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simpa [arm64_norm] using hcs3_regs _ (by simp))
        (by simpa [calleeSavedVRegs, arm64_norm] using hv3)
        fun sf hx0f hspf hcsf hpres4f hvm4f => ?_
      refine ⟨fun hsat => ?_, hspf, hcsf⟩
      have hpres3f : AllocCallPreserved s3 sf :=
        allocCallPreserved_trans
          (allocCallPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) (by simp [arm64_norm]))
          hpres4f
      have hvm3f : VmPreserved s3 sf :=
        vmPreserved_trans
          (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) (by simp [arm64_norm]))
          hvm4f
      have hPres0f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres03 hpres3f
      have hPoolSf :
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s3 =
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf :=
        (mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st hvm3f).symm
      have hx0_0 : sf.readReg64 .x0 = 0 := hx0f
      dsimp only [rustCliAllocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt, xR, RestFail] at hsat ⊢
      rw [stackAt_eq_hookFrame s0.sp]
      simp only [hx0_0, ↓reduceIte]
      rw [hPoolSf] at hsat
      refine Satisfies.mono (sepConj_mono_left ?_) hsat
      have hGoalEq :
          ⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
            Rust.hookFrame s0.sp ∗
            ⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ ∗
              (Rust.hookFrame s0.sp ∗
                mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf)) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf = Ppool
        generalize Rust.hookFrame s0.sp = Phook
        ac_rfl
      rw [hGoalEq]
      exact Entails.pure_right hPres0f (Entails.pure_right hNull (Entails.refl _))
  · dsimp only [mallocngBudgetPosixMemalignCSpec, xP] at ho
    dsimp only [rustCliAllocBudgetSpecBase, A, xR]
    rw [hEvs]
    rw [satisfies_pure_sepConj] at ho ⊢
    obtain ⟨⟨hNotPosix, hOom2f⟩, hFR⟩ := ho
    have hNotEvs : ¬ FitsEvents M lim st [.aligned (max alignBv.toNat 8) sizeBv.toNat] := by
      intro hFitEvs
      refine hNotPosix ⟨hEffGe8, hEffAlOk, ?_⟩
      rw [hEffNat]
      exact hFitEvs.1
    exact ⟨⟨hNotEvs, oomPreserved_of_allocCallPreserved hpres02 hOom2f⟩, Satisfies.drop_left hFR⟩

private theorem rdlAllocZeroed_budget_posix_args {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart callocAddr memsetAddr : BitVec 64}
    {cAddrs : MallocngCEntryAddrs} {lim : BudgetLimits} (allocZeroedAddr : BitVec 64)
    (hCode : hasInstrs P allocZeroedAddr
      (rdlAllocZeroedInstrs allocZeroedAddr callocAddr cAddrs.posixMemalign memsetAddr))
    (hPosix : subroutine_ok P cAddrs.posixMemalign
      (mallocngBudgetPosixMemalignCSpec M I γ mAddrs tp brkStart lim))
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec)
    (sizeBv alignBv w0 w1 : BitVec 64) (st : M.σ) (R : SepProp) (s0 s1 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign)
    (hSlow : ¬ (alignBv.toNat ≤ 16 ∧ alignBv.toNat ≤ sizeBv.toNat))
    (hpc1 : s1.pc = allocZeroedAddr + 0x3c#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 48#64)
    (hx1_1 : s1.readReg64 .x1 = alignBv) (hx19_1 : s1.readReg64 .x19 = sizeBv)
    (hcs1 : ∀ r ∈ ([.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      s1.readReg64 r = s0.readReg64 r)
    (hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hpres01 : AllocCallPreserved s0 s1) (hvm01 : VmPreserved s0 s1) :
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let xR := (sizeBv.toNat, alignBv.toNat, st)
    SepWP P (s0.readReg64 Reg.lr) s1
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
        stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 ∗
        ((s0.sp - 48#64) ↦₆₄ w0) ∗
        ((s0.sp - 40#64) ↦₆₄ w1) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustCliAllocBudgetSpecBase M A lim true).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustCliAllocBudgetSpecBase M A lim true).onOom xR s0 sf) := by
  intro A xR
  have hf15 := fetch_instr_at 15 hCode
  have hf16 := fetch_instr_at 16 hCode
  have hf17 := fetch_instr_at 17 hCode
  have hf18 := fetch_instr_at 18 hCode
  have hf19 := fetch_instr_at 19 hCode
  have hf20 := fetch_instr_at 20 hCode
  have hf21 := fetch_instr_at 21 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl48 : decide (s1.sp &&& 15#64 = 0#64) = true := by
    rw [hsp1]; exact decide_eq_true (beq_iff_eq.mp (spAligned_sub48 hspAl0))
  have ha_sp8 : s1.sp + 8#64 = s0.sp - 40#64 := by rw [hsp1]; bv_omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_str64 hf20 m hm; wp_step
  have hm0 : m.perm = s1.mem.perm := by simpa using hm
  exact rdlAllocZeroed_budget_posix_call hS γ allocZeroedAddr hCode hPosix hMemset
    sizeBv alignBv w0 st R s0 _
    hsp_align hLayout hPow2 hAlMax hSlow
    (by simp only [arm64_norm]; bv_omega)
    (by simp [arm64_norm, hrun1])
    (by simp [arm64_norm, hsp1])
    (by simp only [arm64_norm])
    (by simp [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hx19_1])
    (by simp only [arm64_norm])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa only [arm64_norm] using hcs1 _ (by simp))
    (by simpa only [calleeSavedVRegs, arm64_norm] using hv1)
    (allocCallPreserved_trans hpres01
      (allocCallPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])))
    (vmPreserved_trans hvm01
      (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm, hm0])))

/-- Placed `rustc 1.98.1` `__rustc::__rdl_alloc_zeroed` (`36` instructions: `rdlAllocZeroedInstrs`)
    satisfies `rustAllocZeroedBudgetSpec` (`= rustCliAllocBudgetSpec M A lim true`) over
    `mallocngRustCliAllocBudgetAt`. -/
theorem rdlAllocZeroed_budget_placed_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart : BitVec 64}
    {cAddrs : MallocngCEntryAddrs} {callocAddr memsetAddr : BitVec 64}
    (allocZeroedAddr : BitVec 64) (lim : BudgetLimits)
    (hCode : hasInstrs P allocZeroedAddr
      (rdlAllocZeroedInstrs allocZeroedAddr callocAddr cAddrs.posixMemalign memsetAddr))
    (hC : MallocngProgBudgetCContracts M I γ mAddrs tp brkStart P cAddrs callocAddr)
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec) :
    subroutine_ok P allocZeroedAddr
      (rustAllocZeroedBudgetSpecBase M (mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart) lim) := by
  let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
  apply subroutine_ok_of_sepWP_init
  rintro ⟨size, align, st⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [rustAllocZeroedBudgetSpecBase, rustCliAllocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hLayout⟩, hpre⟩ := hpre
  let sizeBv := s0.readReg64 .x0
  let alignBv := s0.readReg64 .x1
  have hx0_bv : s0.readReg64 .x0 = sizeBv := rfl
  have hx1_bv : s0.readReg64 .x1 = alignBv := rfl
  change sizeBv.toNat = size at hx0
  change alignBv.toNat = align at hx1
  subst hx0; subst hx1
  have ⟨⟨_hSzPos, ⟨k, hk⟩, _hSum63⟩, hAlMax⟩ := hLayout
  have hPow2 : IsPow2Align alignBv := isPow2Align_of_toNat_pow2 hk
  have hAlMax' : alignBv.toNat ≤ MaxAlignedAllocAlign := hAlMax
  rw [stackAt_eq_hookFrame s0.sp] at hpre
  refine ⟨_, hpre, ?_⟩
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  have hspAl48 : decide ((s0.sp - 48#64) &&& 15#64 = 0#64) = true :=
    decide_eq_true (beq_iff_eq.mp hspAl48b)
  have hUnpack :
      mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗ Rust.hookFrame s0.sp =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
          stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
          stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 ∗
          ((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ w1) ∗
          ((s0.sp - 32#64) ↦₆₄ w2) ∗ ((s0.sp - 24#64) ↦₆₄ w3) ∗
          ((s0.sp - 16#64) ↦₆₄ w4) ∗ ((s0.sp - 8#64) ↦₆₄ w5)) := by
    rw [hookFrame_eq_stack48_1024 s0.sp, stackFrameAt48_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ => by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 = Ppool
        generalize stackFrameAt (s0.sp - 48#64) mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 = Pstk2
        ac_rfl))))))
  rw [hUnpack]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4
  apply SepWP.exists_elim; intro w5
  have hf0 := fetch_instr_at0 hCode
  have hf1 := fetch_instr_at 1 hCode
  have hf2 := fetch_instr_at 2 hCode
  have hf3 := fetch_instr_at 3 hCode
  have hf4 := fetch_instr_at 4 hCode
  have hf5 := fetch_instr_at 5 hCode
  have hf6 := fetch_instr_at 6 hCode
  have hf7 := fetch_instr_at 7 hCode
  have hf8 := fetch_instr_at 8 hCode
  have hf9 := fetch_instr_at 9 hCode
  have hf10 := fetch_instr_at 10 hCode
  have hf11 := fetch_instr_at 11 hCode
  have hf12 := fetch_instr_at 12 hCode
  have hf13 := fetch_instr_at 13 hCode
  have hf14 := fetch_instr_at 14 hCode
  wp_step; wp_stp64 hf1 m1 hm1; wp_stp64 hf2 m2 hm2; wp_step; wp_step; wp_step
  have hm20 : m2.perm = s0.mem.perm := (by simpa using hm2 : m2.perm = m1.perm).trans (by simpa using hm1)
  by_cases hAl16 : alignBv.toNat ≤ 16
  · have hHi1 : ConditionHolds .HI (subsPState64 alignBv 16#64) = false :=
      Bool.eq_false_iff.mpr fun h => by
        have := (VerifiedLibraries.Mallocng.Proofs.RdlAllocH.cond_hi_subs64_iff_lt alignBv 16#64).mp h
        change 16 < alignBv.toNat at this; omega
    wp_step; wp_step
    by_cases hAlSz : alignBv.toNat ≤ sizeBv.toNat
    · have hHi2 : ConditionHolds .HI (subsPState64 alignBv sizeBv) = false :=
        Bool.eq_false_iff.mpr fun h => by
          have := (VerifiedLibraries.Mallocng.Proofs.RdlAllocH.cond_hi_subs64_iff_lt alignBv sizeBv).mp h
          omega
      wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
      have hRepackFast :
          (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
            stackFrameAt (s0.sp - 48#64) mallocngStackBytes ∗
            stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 ∗
            ((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ w1) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ⊢
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗ Rust.hookFrame s0.sp := by
        refine Entails.trans (Entails.of_eq ?_)
          (sepConj_mono_right
            (repack_hookFrame_48 s0.sp w0 w1
              (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
              (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))))
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 = Ppool
        generalize stackFrameAt (s0.sp - 48#64) mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 48#64 - 1024#64) 3024 = Pstk2
        ac_rfl
      refine SepWP.weaken_pre hRepackFast ?_
      exact rdlAllocZeroed_budget_fast_path hS γ (hC.calloc_ok lim)
        sizeBv alignBv st R s0 _
        hsp_align hLayout hPow2 hAl16 hAlSz
        (by simp only [arm64_norm]; bv_omega)
        (by simp [arm64_norm, hrun])
        (by simp only [arm64_norm])
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        (by unfold CalleeSavedPreserved; simp [arm64_norm, calleeSavedVRegs])
        (by unfold AllocCallPreserved; simp [arm64_norm])
        (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm, hm20]))
    · have hHi2 : ConditionHolds .HI (subsPState64 alignBv sizeBv) = true :=
        (VerifiedLibraries.Mallocng.Proofs.RdlAllocH.cond_hi_subs64_iff_lt alignBv sizeBv).mpr (by omega)
      wp_step
      exact rdlAllocZeroed_budget_posix_args hS γ allocZeroedAddr hCode
        (hC.posixMemalign_ok lim) hMemset
        sizeBv alignBv w0 w1 st R s0 _
        hsp_align hLayout hPow2 hAlMax' (fun h => hAlSz h.2)
        (by simp only [arm64_norm])
        (by simp [arm64_norm, hrun])
        (by simp [arm64_norm])
        (by simp [arm64_norm, hx1_bv])
        (by simp [arm64_norm])
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm])
        (by simp [calleeSavedVRegs, arm64_norm])
        (by unfold AllocCallPreserved; simp [arm64_norm])
        (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm, hm20]))
  · have hHi1 : ConditionHolds .HI (subsPState64 alignBv 16#64) = true :=
      (VerifiedLibraries.Mallocng.Proofs.RdlAllocH.cond_hi_subs64_iff_lt alignBv 16#64).mpr
        (by change 16 < alignBv.toNat; omega)
    wp_step
    exact rdlAllocZeroed_budget_posix_args hS γ allocZeroedAddr hCode
      (hC.posixMemalign_ok lim) hMemset
      sizeBv alignBv w0 w1 st R s0 _
      hsp_align hLayout hPow2 hAlMax' (fun h => hAl16 h.1)
      (by simp only [arm64_norm])
      (by simp [arm64_norm, hrun])
      (by simp [arm64_norm])
      (by simp [arm64_norm, hx1_bv])
      (by simp [arm64_norm])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm])
      (by simp [calleeSavedVRegs, arm64_norm])
      (by unfold AllocCallPreserved; simp [arm64_norm])
      (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm, hm20]))

/-! ## `B`-Thunk Lift and `fineCostModel` Instantiations -/

/-- Lift `subroutine_ok P targetAddr (rustAllocZeroedBudgetSpec M A lim)` across a 1-instruction
    unconditional `B` thunk (`__rustc::__rust_alloc_zeroed → b __rustc::__rdl_alloc_zeroed`). -/
theorem rustCliAllocZeroedBudget_of_b_thunk {M : AllocCostModel} {A : RustCliAllocBudget M}
    {P : Program} {thunkAddr targetAddr : BitVec 64} {lim : BudgetLimits}
    (hThunk : hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ])
    (hok : subroutine_ok P targetAddr (rustAllocZeroedBudgetSpecBase M A lim)) :
    subroutine_ok P thunkAddr (rustAllocZeroedBudgetSpecBase M A lim) :=
  rustCliAllocBudget_of_b_thunk (zeroed := true) hThunk hok

/-- Placed `__rustc::__rdl_alloc_zeroed` satisfies `rustAllocZeroedBudgetSpec fineCostModel` on any
    program `P` containing `VerifiedLibraries.mallocngLib` at `mpl`. -/
theorem fineRdlAllocZeroed_budget_placed_ok
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart allocZeroedAddr memsetAddr : BitVec 64)
    (lim : BudgetLimits)
    (hCode : hasInstrs P allocZeroedAddr
      (rdlAllocZeroedInstrs allocZeroedAddr (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc")
        (mallocngPlacedCAddrs mpl).posixMemalign memsetAddr))
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec) :
    subroutine_ok P allocZeroedAddr
      (rustAllocZeroedBudgetSpecBase fineCostModel (fineRustCliAllocBudget γ mpl tp brkStart) lim) :=
  rdlAllocZeroed_budget_placed_ok fineCostModelSound γ allocZeroedAddr lim hCode
    (mallocngProgBudgetCContracts_of_placed fineCostModelSound hP γ tp brkStart) hMemset

/-- 1-instruction `B`-thunk (`__rustc::__rust_alloc_zeroed → b __rustc::__rdl_alloc_zeroed`) lift of
    `fineRdlAllocZeroed_budget_placed_ok`. -/
theorem fineRustCliAllocZeroedBudget_thunk_ok
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart thunkAddr rdlAddr memsetAddr : BitVec 64)
    (lim : BudgetLimits)
    (hThunk : hasInstrs P thunkAddr [ .b (rdlAddr - thunkAddr) ])
    (hCode : hasInstrs P rdlAddr
      (rdlAllocZeroedInstrs rdlAddr (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc")
        (mallocngPlacedCAddrs mpl).posixMemalign memsetAddr))
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec) :
    subroutine_ok P thunkAddr
      (rustAllocZeroedBudgetSpecBase fineCostModel (fineRustCliAllocBudget γ mpl tp brkStart) lim) :=
  rustCliAllocZeroedBudget_of_b_thunk hThunk
    (fineRdlAllocZeroed_budget_placed_ok hP γ tp brkStart rdlAddr memsetAddr lim hCode hMemset)

/-- Total-correctness (`onOom := ⌜False⌝`, non-null return under `FitsEvents`) specialization of
    `fineRdlAllocZeroed_budget_placed_ok`. -/
theorem fineRdlAllocZeroed_noOom_placed_ok
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart allocZeroedAddr memsetAddr : BitVec 64)
    (lim : BudgetLimits)
    (hCode : hasInstrs P allocZeroedAddr
      (rdlAllocZeroedInstrs allocZeroedAddr (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc")
        (mallocngPlacedCAddrs mpl).posixMemalign memsetAddr))
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec) :
    subroutine_ok P allocZeroedAddr
      (rustCliAllocNoOomSpecBase fineCostModel (fineRustCliAllocBudget γ mpl tp brkStart) lim true) :=
  subroutine_ok_allocNoOom_of_budgetBase
    (fineRdlAllocZeroed_budget_placed_ok hP γ tp brkStart allocZeroedAddr memsetAddr lim hCode hMemset)

/-- Total-correctness (`onOom := ⌜False⌝`) specialization of `fineRustCliAllocZeroedBudget_thunk_ok`. -/
theorem fineRustCliAllocZeroedNoOom_thunk_ok
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart thunkAddr rdlAddr memsetAddr : BitVec 64)
    (lim : BudgetLimits)
    (hThunk : hasInstrs P thunkAddr [ .b (rdlAddr - thunkAddr) ])
    (hCode : hasInstrs P rdlAddr
      (rdlAllocZeroedInstrs rdlAddr (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc")
        (mallocngPlacedCAddrs mpl).posixMemalign memsetAddr))
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec) :
    subroutine_ok P thunkAddr
      (rustCliAllocNoOomSpecBase fineCostModel (fineRustCliAllocBudget γ mpl tp brkStart) lim true) :=
  subroutine_ok_allocNoOom_of_budgetBase
    (fineRustCliAllocZeroedBudget_thunk_ok hP γ tp brkStart thunkAddr rdlAddr memsetAddr lim
      hThunk hCode hMemset)

/-- Startup initialization and 4-entry Rust allocator assembly (`__rdl_{alloc,dealloc,realloc,alloc_zeroed}`)
    over `fineRustCliAllocBudget`. -/
theorem fineRustCliAllocZeroedBudget_of_placed_init
    {P : Program} {mpl : Obj.MultiPlacement}
    {addrs : RustAllocAddrs} {allocZeroedAddr memcpyAddr memsetAddr : BitVec 64}
    (tp brkStart auxvPtr : BitVec 64) (lim : BudgetLimits)
    (staticIvs : List (BitVec 64 × Nat)) (R : SepProp) (s0 : State)
    (hP : ProgContainsMallocng P mpl)
    (hShims : RustStdRdlShimCode P addrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hZeroedCode : hasInstrs P allocZeroedAddr
      (rdlAllocZeroedInstrs allocZeroedAddr (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc")
        (mallocngPlacedCAddrs mpl).posixMemalign memsetAddr))
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec)
    (htpLo : 0xa4 ≤ tp.toNat) (htpHi : tp.toNat ≤ 2 ^ 48)
    (hbrkWf : MallocngBrkStartWf brkStart)
    (htp : s0.tpidrEl0 = tp) (hbrkStart : s0.brkStart = brkStart) (hbrk : s0.brk = brkStart)
    (hInv : mallocngBudgetPoolInv lim staticIvs [] s0)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) tp ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ mpl tp brkStart
      (s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R) ∧
      RustCliAllocBudgetEntriesBase fineCostModel A P addrs ∧
      (∀ k : BudgetLimits,
        subroutine_ok P allocZeroedAddr (rustAllocZeroedBudgetSpecBase fineCostModel A k)) := by
  obtain ⟨γ, hPool, hEntries⟩ :=
    fineRustCliAllocBudgetEntries_of_placed_init tp brkStart auxvPtr lim staticIvs R s0
      hP hShims hMemcpy htpLo htpHi hbrkWf htp hbrkStart hbrk hInv hmem
  exact ⟨γ, hPool, hEntries, fun k =>
    fineRdlAllocZeroed_budget_placed_ok hP γ tp brkStart allocZeroedAddr memsetAddr k
      hZeroedCode hMemset⟩

/-- 1-instruction `B`-thunk (`__rust_{alloc,dealloc,realloc,alloc_zeroed}`) counterpart of
    `fineRustCliAllocZeroedBudget_of_placed_init`. -/
theorem fineRustCliAllocZeroedBudget_thunk_of_placed_init
    {P : Program} {mpl : Obj.MultiPlacement}
    {thunkAddrs rdlAddrs : RustAllocAddrs}
    {thunkZeroedAddr rdlZeroedAddr memcpyAddr memsetAddr : BitVec 64}
    (tp brkStart auxvPtr : BitVec 64) (lim : BudgetLimits)
    (staticIvs : List (BitVec 64 × Nat)) (R : SepProp) (s0 : State)
    (hP : ProgContainsMallocng P mpl)
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hZeroedThunk : hasInstrs P thunkZeroedAddr [ .b (rdlZeroedAddr - thunkZeroedAddr) ])
    (hZeroedCode : hasInstrs P rdlZeroedAddr
      (rdlAllocZeroedInstrs rdlZeroedAddr (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc")
        (mallocngPlacedCAddrs mpl).posixMemalign memsetAddr))
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec)
    (htpLo : 0xa4 ≤ tp.toNat) (htpHi : tp.toNat ≤ 2 ^ 48)
    (hbrkWf : MallocngBrkStartWf brkStart)
    (htp : s0.tpidrEl0 = tp) (hbrkStart : s0.brkStart = brkStart) (hbrk : s0.brk = brkStart)
    (hInv : mallocngBudgetPoolInv lim staticIvs [] s0)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) tp ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ mpl tp brkStart
      (s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R) ∧
      RustCliAllocBudgetEntriesBase fineCostModel A P thunkAddrs ∧
      (∀ k : BudgetLimits,
        subroutine_ok P thunkZeroedAddr (rustAllocZeroedBudgetSpecBase fineCostModel A k)) := by
  obtain ⟨γ, hPool, hEntries⟩ :=
    fineRustCliAllocBudgetEntries_thunks_of_placed_init tp brkStart auxvPtr lim staticIvs R s0
      hP hThunks hShims hMemcpy htpLo htpHi hbrkWf htp hbrkStart hbrk hInv hmem
  exact ⟨γ, hPool, hEntries, fun k =>
    fineRustCliAllocZeroedBudget_thunk_ok hP γ tp brkStart thunkZeroedAddr rdlZeroedAddr memsetAddr
      k hZeroedThunk hZeroedCode hMemset⟩

end LibsignalBinary.Heap.Fine
