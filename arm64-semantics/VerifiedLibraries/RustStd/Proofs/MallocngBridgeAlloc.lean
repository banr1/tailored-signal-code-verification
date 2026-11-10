/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.BV
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.Mallocng.Proofs.RdlAllocProof
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.MallocngInst
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon

/-!
# Placed `__rdl_alloc` and `__rdl_dealloc` Verification

Verifies placed `__rustc::__rdl_alloc` and `__rustc::__rdl_dealloc` shims against
`rustStdAllocSpec` and `rustStdDeallocSpec` over `mallocngRustCliAllocWithOf`, together with
lifting lemmas across 1-instruction unconditional `B` thunks (`__rustc::__rust_{alloc,dealloc}`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.CType ProofLib.SepLogic ProofLib.StdStartup
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Placed `__rustc::__rdl_dealloc` -/

theorem free_satisfies_rustStdDeallocSpec {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {freeAddr : BitVec 64}
    (hFree : subroutine_ok P freeAddr
      (withExtra extra (ToBaseSpec.toSpec (mallocngFreeSpec J γ mAddrs) P.base))) :
    subroutine_ok P freeAddr
      (rustStdDeallocSpec (mallocngRustCliAllocWithOf J hIf extra γ mAddrs)) := by
  let A := mallocngRustCliAllocWithOf J hIf extra γ mAddrs
  apply subroutine_ok.of_codeLoaded
  rintro ⟨p, size, align, lb, lk⟩ R s0 hpc hrun hpre hsp _
  dsimp only [rustStdDeallocSpec, A] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, _hx1, _hx2⟩, hpre⟩ := hpre
  change (s0.mem ⊨
    ((mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk s0 ∗
      (⌜p.toNat % align = 0 ∧ RustLayoutOk size align⌝ ∗ J.Block γ p size) ∗
      memRegion p size ∗ StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp) ∗ R) at hpre
  have hArrangePre :
      ((mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk s0 ∗
        (⌜p.toNat % align = 0 ∧ RustLayoutOk size align⌝ ∗ J.Block γ p size) ∗
        memRegion p size ∗ StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp) ∗ R ⊢
      ⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64⌝ ∗
      ((∃∗ b : MallocngBudget, ∃∗ ivs0 : List (BitVec 64 × Nat),
          J.MallocngHeap γ mAddrs s0.tpidrEl0 s0.brkStart s0.brk b ivs0) ∗
        (J.Block γ p size ∗ memRegion p size ∗
         stackFrameAt s0.sp mallocngStackBytes ∗ extra) ∗
        (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R)) := by
    have hEq1 :
        ((mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk s0 ∗
          (⌜p.toNat % align = 0 ∧ RustLayoutOk size align⌝ ∗ J.Block γ p size) ∗
          memRegion p size ∗ StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp) ∗ R =
        (⌜p.toNat % align = 0 ∧ RustLayoutOk size align⌝ ∗
          (J.Block γ p size ∗
            (((mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk s0 ∗
              StdErrnoCell s0.tpidrEl0) ∗
             memRegion p size ∗ Rust.hookFrame s0.sp ∗ R))) := by ac_rfl
    rw [hEq1, mallocngRustCliPoolWithOf_sep_stdErrnoCell_eq hIf extra γ mAddrs lb lk s0,
        hookFrame_eq_stack1024 s0.sp]
    refine Entails.pure_left fun _ => ?_
    refine Entails.trans (sepConj_mono_left (hIf.block_nonnull γ p size)) ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hpNe, h16, hBound48, _⟩ => ?_
    have hBound64 : p.toNat + size < 2 ^ 64 := Nat.lt_of_le_of_lt hBound48 (by decide)
    refine Entails.pure_right ⟨hpNe, h16, hBound64⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  have hpre2 := Satisfies.mono hArrangePre hpre
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨⟨hpNe, h16, hBound64⟩, hpre2⟩ := hpre2
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpre2
  obtain ⟨b, hpre2⟩ := hpre2
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpre2
  obtain ⟨ivs0, hpre2⟩ := hpre2
  let xFree : BitVec 64 × BitVec 64 × Nat × BitVec 64 × BitVec 64 ×
      MallocngBudget × List (BitVec 64 × Nat) :=
    (p, s0.sp, size, s0.tpidrEl0, s0.brkStart, b, ivs0)
  let RFree : SepProp := stackFrameAt (s0.sp - 1024#64) 3072 ∗ R
  have hpreFree : s0.mem ⊨
      (withExtra extra (ToBaseSpec.toSpec (mallocngFreeSpec J γ mAddrs) P.base)).pre xFree s0 ∗
        RFree := by
    dsimp only [withExtra, ToBaseSpec.toSpec, mallocngFreeSpec, xFree, MallocngFreeableBlock, RFree]
    simp only [hpNe, ↓reduceIte]
    have hpre2' : s0.mem ⊨
        (J.MallocngHeap γ mAddrs s0.tpidrEl0 s0.brkStart s0.brk b ivs0 ∗
          J.Block γ p size ∗ memRegion p size ∗
          stackFrameAt s0.sp mallocngStackBytes ∗ extra) ∗
        (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre2
    refine Satisfies.mono (sepConj_mono_left ?_) hpre2'
    unfold MallocngEnv
    have hEnv : J.MallocngHeap γ mAddrs s0.tpidrEl0 s0.brkStart s0.brk b ivs0 ⊢
        ⌜s0.tpidrEl0 = s0.tpidrEl0 ∧ s0.brkStart = s0.brkStart⌝ ∗
          J.MallocngHeap γ mAddrs s0.tpidrEl0 s0.brkStart s0.brk b ivs0 :=
      Entails.pure_right ⟨rfl, rfl⟩ (Entails.refl _)
    refine Entails.trans (sepConj_mono_left hEnv) ?_
    have hComm :
        (⌜s0.tpidrEl0 = s0.tpidrEl0 ∧ s0.brkStart = s0.brkStart⌝ ∗
          J.MallocngHeap γ mAddrs s0.tpidrEl0 s0.brkStart s0.brk b ivs0) ∗
          J.Block γ p size ∗ memRegion p size ∗
          stackFrameAt s0.sp mallocngStackBytes ∗ extra =
        (((J.Block γ p size ∗ memRegion p size) ∗
          ((⌜s0.tpidrEl0 = s0.tpidrEl0 ∧ s0.brkStart = s0.brkStart⌝ ∗
            J.MallocngHeap γ mAddrs s0.tpidrEl0 s0.brkStart s0.brk b ivs0) ∗
           stackFrameAt s0.sp mallocngStackBytes)) ∗ extra) := by ac_rfl
    rw [hComm]
    exact sepConj_mono_left (Entails.pure_right ⟨hx0, trivial, h16, hBound64⟩ (Entails.refl _))
  have hbeqF : (p == 0#64) = false := beq_false_of_ne hpNe
  refine subroutine_ok.mono_outcome hFree xFree RFree s0 hpc hrun hpreFree hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withExtra, ToBaseSpec.toSpec, mallocngFreeSpec, xFree, RFree] at hq
    rw [hbeqF] at hq
    have hPostEnt :
        ((⌜MallocngCallAccounting 0 0 s0 sf⌝ ∗
            (MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart
              (mallocngFreeBudget false size b) ivs0 s0 sf ∗
             stackFrameAt s0.sp mallocngStackBytes)) ∗ extra) ∗
          (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R) ⊢
        (⌜AllocCallPreserved s0 sf⌝ ∗
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb - size) (lk - 1) sf ∗
          StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp) ∗ R := by
      have hEqP :
          ((⌜MallocngCallAccounting 0 0 s0 sf⌝ ∗
              (MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart
                (mallocngFreeBudget false size b) ivs0 s0 sf ∗
               stackFrameAt s0.sp mallocngStackBytes)) ∗ extra) ∗
            (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R) =
          ⌜MallocngCallAccounting 0 0 s0 sf⌝ ∗
            ((MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart
                (mallocngFreeBudget false size b) ivs0 s0 sf ∗ extra) ∗
             (stackFrameAt s0.sp mallocngStackBytes ∗ stackFrameAt (s0.sp - 1024#64) 3072) ∗ R) := by
        ac_rfl
      rw [hEqP, ← hookFrame_eq_stack1024 s0.sp]
      refine Entails.pure_left fun hAcc => ?_
      have hPres : AllocCallPreserved s0 sf := allocCallPreserved_of_mallocngProcPreserved hAcc.1
      have hPool := postEnv_withExtra_entails_errno_pool hIf extra γ mAddrs
        (mallocngFreeBudget false size b) ivs0 (lb - size) (lk - 1) s0 s0 sf
      refine Entails.trans (sepConj_mono_left hPool) ?_
      have hRearr :
          (StdErrnoCell s0.tpidrEl0 ∗
            (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb - size) (lk - 1) sf) ∗
            Rust.hookFrame s0.sp ∗ R =
          ((mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb - size) (lk - 1) sf ∗
            StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp) ∗ R := by ac_rfl
      rw [hRearr]
      exact sepConj_mono_left (Entails.pure_right hPres (Entails.refl _))
    exact Satisfies.mono hPostEnt hq
  · dsimp only [withExtra, ToBaseSpec.toSpec, mallocngFreeSpec] at hpan
    exact False.elim (not_satisfies_false_sepConj hpan)
  · dsimp only [withExtra, ToBaseSpec.toSpec, mallocngFreeSpec] at hex
    exact False.elim (not_satisfies_false_sepConj hex)
  · dsimp only [withExtra, ToBaseSpec.toSpec, mallocngFreeSpec] at hoom
    exact False.elim (not_satisfies_false_sepConj hoom)

theorem rdlDealloc_placed_withExtra_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (deallocAddr : BitVec 64)
    (hCode : hasInstrs P deallocAddr (rdlDeallocInstrs deallocAddr cAddrs.free))
    (hC : MallocngProgCContractsWith J extra P mAddrs cAddrs) :
    subroutine_ok P deallocAddr
      (rustStdDeallocSpec (mallocngRustCliAllocWithOf J hIf extra γ mAddrs)) :=
  subroutine_ok_of_b_thunk (fetch_instr_at0 hCode)
    (hpre_pc := by rintro ⟨_, _, _, _, _⟩ _ _; rfl)
    (hpost_pc := by rintro ⟨_, _, _, _, _⟩ _ _ _; rfl)
    (hoom_pc := by rintro ⟨_, _, _, _, _⟩ _ _ _; rfl)
    (hok := free_satisfies_rustStdDeallocSpec hIf extra γ (hC.free_ok γ))

/-! ## Placed `__rustc::__rdl_alloc` -/

private theorem stackFrameAt32_eq (sp : BitVec 64) :
    stackFrameAt sp 32 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

private theorem pack_stack32 (sp w0 w1 w2 w3 : BitVec 64) :
    (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
     ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢ stackFrameAt sp 32 := by
  rw [stackFrameAt32_eq sp]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))

private theorem rdlAlloc_placed_fast_path {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {mallocAddr : BitVec 64}
    (hMalloc : subroutine_ok P mallocAddr
      (withExtra extra (ToBaseSpec.toSpec (mallocngMallocSpec J Syscall.standard γ mAddrs) P.base)))
    (sizeBv alignBv : BitVec 64) (lb lk : Nat)
    (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (R : SepProp) (s0 s1 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAl16 : alignBv.toNat ≤ 16)
    (hpc1 : s1.pc = mallocAddr) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp) (hx0_1 : s1.readReg64 .x0 = sizeBv)
    (hlr1 : s1.readReg64 Reg.lr = s0.readReg64 Reg.lr)
    (hcs1 : CalleeSavedPreserved s0 s1)
    (hpres01 : AllocCallPreserved s0 s1) (hbrk1 : s1.brk = s0.brk) :
    let A := mallocngRustCliAllocWithOf J hIf extra γ mAddrs
    let xR := (sizeBv.toNat, alignBv.toNat, lb, lk)
    SepWP P (s0.readReg64 Reg.lr) s1
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗
        extra ∗ Rust.hookFrame s0.sp)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustStdAllocSpec A).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustStdAllocSpec A).onOom xR s0 sf) := by
  intro A xR
  have hEff : mallocngAlignedEffSize alignBv.toNat sizeBv.toNat = sizeBv.toNat := by
    unfold mallocngAlignedEffSize; simp [hAl16]
  have hOkEq :
      decide (sizeBv.toNat ≤ MallocngMaxAllocSize) = decide (MallocngLayoutFit sizeBv alignBv) := by
    simp [MallocngLayoutFit, hEff]
  have hEnv1 :
      MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 =
        MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s1 := by
    unfold MallocngEnv; rw [hpres01.2.2.2.1, hpres01.2.2.2.2.1, hbrk1]
  let F := stackFrameAt (s0.sp - 1024#64) 3072
  let xM := (sizeBv, s0.sp, s0.tpidrEl0, s0.brkStart, b, ivs0)
  refine SepWP.call_subroutine_frame (F := F) (x := xM) hMalloc
    (ret_pc := s0.readReg64 Reg.lr)
    hpc1 hrun1 (by simpa [State.spAligned, hsp1] using hsp_align) hlr1
    (fun R' hsat => ?_)
    (fun _ _ _ hp => by
      dsimp only [withExtra, ToBaseSpec.toSpec, mallocngMallocSpec] at hp
      exact not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => by
      dsimp only [withExtra, ToBaseSpec.toSpec, mallocngMallocSpec] at he
      exact not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun R' sf _ ho => ?_)
  · dsimp only [withExtra, ToBaseSpec.toSpec, mallocngMallocSpec, xM, F]
    rw [hookFrame_eq_stack1024 s0.sp, hEnv1] at hsat
    have hsat' : s1.mem ⊨
        ((MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s1 ∗
          stackFrameAt s0.sp mallocngStackBytes) ∗ extra) ∗
        (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R') :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hsat
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hsat'
    exact Entails.pure_right ⟨hx0_1, hsp1, trivial⟩ (Entails.refl _)
  · refine SepWP.done hpc_f hrun_f
      ⟨fun hsat => ?_, hsp_f.trans hsp1, calleeSavedPreserved_trans hcs1 hcs_f⟩
    dsimp only [withExtra, ToBaseSpec.toSpec, mallocngMallocSpec, xM, F] at hsat
    dsimp only [rustStdAllocSpec, A, xR]
    rw [hOkEq] at hsat
    by_cases hFit : MallocngLayoutFit sizeBv alignBv
    · have hOkT : decide (MallocngLayoutFit sizeBv alignBv) = true := decide_eq_true hFit
      rw [hOkT] at hsat
      dsimp only [OptOwn, MallocngBlock] at hsat
      simp only [↓reduceIte] at hsat
      refine Satisfies.mono ?_ hsat
      have hEq1 :
          (((⌜(sf.readReg64 .x0 ≠ 0#64 ∧ sf.readReg64 .x0 ≠ 0#64 ∧
                16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + sizeBv.toNat < 2 ^ 64) ∧
              MallocngCallAccounting 16 (MallocngStepBound sizeBv.toNat b.peakCount) s1 sf⌝ ∗
            (J.Block γ (sf.readReg64 .x0) sizeBv.toNat ∗
              memRegion (sf.readReg64 .x0) sizeBv.toNat) ∗
            (MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart
              (mallocngAllocBudget true sizeBv.toNat b) ivs0 s1 sf ∗
             stackFrameAt s0.sp mallocngStackBytes)) ∗ extra) ∗
           stackFrameAt (s0.sp - 1024#64) 3072) ∗ R =
          ⌜(sf.readReg64 .x0 ≠ 0#64 ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              16 ∣ (sf.readReg64 .x0).toNat ∧
              (sf.readReg64 .x0).toNat + sizeBv.toNat < 2 ^ 64) ∧
            MallocngCallAccounting 16 (MallocngStepBound sizeBv.toNat b.peakCount) s1 sf⌝ ∗
            ((MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart
                (mallocngAllocBudget true sizeBv.toNat b) ivs0 s1 sf ∗ extra) ∗
             (stackFrameAt s0.sp mallocngStackBytes ∗ stackFrameAt (s0.sp - 1024#64) 3072) ∗
             J.Block γ (sf.readReg64 .x0) sizeBv.toNat ∗
             memRegion (sf.readReg64 .x0) sizeBv.toNat ∗ R) := by ac_rfl
      rw [hEq1, ← hookFrame_eq_stack1024 s0.sp]
      refine Entails.pure_left fun ⟨⟨hNe, _, h16, _⟩, hAcc1⟩ => ?_
      have hNe0 : sf.readReg64 .x0 ≠ 0 := hNe
      simp only [hNe0, ↓reduceIte]
      have hMod : (sf.readReg64 .x0).toNat % alignBv.toNat = 0 :=
        Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (pow2_dvd_16_of_le_16 hPow2 hAl16) h16)
      have hPres : AllocCallPreserved s0 sf :=
        allocCallPreserved_trans hpres01 (allocCallPreserved_of_mallocngProcPreserved hAcc1.1)
      have hPool := postEnv_withExtra_entails_errno_pool hIf extra γ mAddrs
        (mallocngAllocBudget true sizeBv.toNat b) ivs0 (lb + sizeBv.toNat) (lk + 1) s0 s1 sf
      refine Entails.trans (sepConj_mono_left hPool) ?_
      have hLiveEq :
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).live
            (sf.readReg64 .x0) sizeBv.toNat alignBv.toNat =
          (⌜(sf.readReg64 .x0).toNat % alignBv.toNat = 0 ∧
            RustLayoutOk sizeBv.toNat alignBv.toNat⌝ ∗
           J.Block γ (sf.readReg64 .x0) sizeBv.toNat) := rfl
      have hCostEq :
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).cost sizeBv.toNat alignBv.toNat =
            sizeBv.toNat := rfl
      rw [hLiveEq, hCostEq]
      have hLive : J.Block γ (sf.readReg64 .x0) sizeBv.toNat ⊢
          ⌜(sf.readReg64 .x0).toNat % alignBv.toNat = 0 ∧
            RustLayoutOk sizeBv.toNat alignBv.toNat⌝ ∗
            J.Block γ (sf.readReg64 .x0) sizeBv.toNat :=
        Entails.pure_right ⟨hMod, hLayout⟩ (Entails.refl _)
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hLive))) ?_
      have hModWrap :
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb + sizeBv.toNat) (lk + 1) sf ⊢
          ⌜(sf.readReg64 .x0).toNat % alignBv.toNat = 0⌝ ∗
            (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb + sizeBv.toNat) (lk + 1) sf :=
        Entails.pure_right hMod (Entails.refl _)
      refine Entails.trans (sepConj_mono_left (sepConj_mono_right hModWrap)) ?_
      have hEq2 :
          (StdErrnoCell s0.tpidrEl0 ∗
            (⌜(sf.readReg64 .x0).toNat % alignBv.toNat = 0⌝ ∗
              (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb + sizeBv.toNat) (lk + 1) sf)) ∗
            Rust.hookFrame s0.sp ∗
            (⌜(sf.readReg64 .x0).toNat % alignBv.toNat = 0 ∧
                RustLayoutOk sizeBv.toNat alignBv.toNat⌝ ∗
              J.Block γ (sf.readReg64 .x0) sizeBv.toNat) ∗
            memRegion (sf.readReg64 .x0) sizeBv.toNat ∗ R =
          (StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp ∗
            (⌜(sf.readReg64 .x0).toNat % alignBv.toNat = 0⌝ ∗
              (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb + sizeBv.toNat) (lk + 1) sf ∗
              (⌜(sf.readReg64 .x0).toNat % alignBv.toNat = 0 ∧
                  RustLayoutOk sizeBv.toNat alignBv.toNat⌝ ∗
                J.Block γ (sf.readReg64 .x0) sizeBv.toNat) ∗
              memRegion (sf.readReg64 .x0) sizeBv.toNat)) ∗ R := by ac_rfl
      rw [hEq2]
      exact sepConj_mono_left (Entails.pure_right hPres (Entails.refl _))
    · have hOkF : decide (MallocngLayoutFit sizeBv alignBv) = false := decide_eq_false hFit
      rw [hOkF] at hsat
      dsimp only [OptOwn, MallocngBlock] at hsat
      simp only [Bool.false_eq_true, ↓reduceIte] at hsat
      have hNull : NullAllowed sizeBv.toNat alignBv.toNat := not_layoutFit_imp_gt_2pow62 hFit
      refine Satisfies.mono ?_ hsat
      have hEq1 :
          (((⌜True ∧ MallocngCallAccounting 16 (MallocngStepBound 0 b.peakCount) s1 sf⌝ ∗
            ⌜sf.readReg64 .x0 = 0#64⌝ ∗
            (MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart
              (mallocngAllocBudget false sizeBv.toNat b) ivs0 s1 sf ∗
             stackFrameAt s0.sp mallocngStackBytes)) ∗ extra) ∗
           stackFrameAt (s0.sp - 1024#64) 3072) ∗ R =
          ⌜True ∧ MallocngCallAccounting 16 (MallocngStepBound 0 b.peakCount) s1 sf⌝ ∗
            (⌜sf.readReg64 .x0 = 0#64⌝ ∗
              ((MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart
                  (mallocngAllocBudget false sizeBv.toNat b) ivs0 s1 sf ∗ extra) ∗
               (stackFrameAt s0.sp mallocngStackBytes ∗ stackFrameAt (s0.sp - 1024#64) 3072) ∗ R)) := by
        ac_rfl
      rw [hEq1, ← hookFrame_eq_stack1024 s0.sp]
      refine Entails.pure_left fun ⟨_, hAcc1⟩ => Entails.pure_left fun hret0 => ?_
      have hret0' : sf.readReg64 .x0 = 0 := hret0
      simp only [hret0', ↓reduceIte]
      have hPres : AllocCallPreserved s0 sf :=
        allocCallPreserved_trans hpres01 (allocCallPreserved_of_mallocngProcPreserved hAcc1.1)
      have hPool := postEnv_withExtra_entails_errno_pool hIf extra γ mAddrs
        (mallocngAllocBudget false sizeBv.toNat b) ivs0 lb lk s0 s1 sf
      refine Entails.trans (sepConj_mono_left hPool) ?_
      have hNullWrap :
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk sf ⊢
          ⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ ∗
            (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk sf :=
        Entails.pure_right hNull (Entails.refl _)
      refine Entails.trans (sepConj_mono_left (sepConj_mono_right hNullWrap)) ?_
      have hEq2 :
          (StdErrnoCell s0.tpidrEl0 ∗
            (⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ ∗
              (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk sf)) ∗
            Rust.hookFrame s0.sp ∗ R =
          (StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp ∗
            (⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ ∗
              (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk sf)) ∗ R := by ac_rfl
      rw [hEq2]
      exact sepConj_mono_left (Entails.pure_right hPres (Entails.refl _))
  · dsimp only [withExtra, ToBaseSpec.toSpec, mallocngMallocSpec, xM] at ho
    dsimp only [rustStdAllocSpec, A, xR]
    rw [satisfies_pure_sepConj] at ho
    obtain ⟨hOom1, hFR⟩ := ho
    have hOom1f := oomCond_imp_preserved hOom1
    have hOom0f : OomPreserved s0 sf :=
      ⟨hOom1f.1.trans hpres01.1, hOom1f.2.1.trans hpres01.2.1, hOom1f.2.2.trans hpres01.2.2.1⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hOom0f, Satisfies.drop_left hFR⟩

private theorem spAligned_sub32 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 32#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_robdd

private theorem rdlAlloc_placed_epilogue {P : Program}
    {allocAddr mallocAddr posixMemalignAddr : BitVec 64}
    (hCode : hasInstrs P allocAddr (rdlAllocInstrs allocAddr mallocAddr posixMemalignAddr))
    (s0 s3 : State) (w0 q : BitVec 64) (Rest : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp)
    (hsp_align : s0.spAligned = true)
    (hpc3 : s3.pc = allocAddr + 0x40#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 32#64)
    (hcs3 : ∀ r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      s3.readReg64 r = s0.readReg64 r)
    (hv3 : calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hpost : ∀ sf : State,
      sf.readReg64 .x0 =
        (if ConditionHolds .EQ (subsPState32 (s3.readReg32 .x0) 0#32) then q else 0#64) →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      AllocCallPreserved s3 sf →
      sf.brk = s3.brk →
      post sf (Rust.hookFrame s0.sp ∗ Rest)) :
    SepWP P (s0.readReg64 Reg.lr) s3
      ((((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
       (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗ Rest)
      post oom := by
  have hf16 := fetch_instr_at 16 hCode
  have hf17 := fetch_instr_at 17 hCode
  have hf18 := fetch_instr_at 18 hCode
  have hf19 := fetch_instr_at 19 hCode
  have hf20 := fetch_instr_at 20 hCode
  have hf21 := fetch_instr_at 21 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl32 : decide (s3.sp &&& 15#64 = 0#64) = true := by
    rw [hsp3]; exact decide_eq_true (beq_iff_eq.mp (spAligned_sub32 hspAl0))
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  have hRepack :
      ((((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
       (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗ Rest) ⊢
      Rust.hookFrame s0.sp ∗ Rest := by
    rw [hookFrame_eq_stack32_1024 s0.sp, ← sepConj_assoc]
    exact sepConj_mono_left (sepConj_mono_left (pack_stack32 s0.sp w0 q _ _))
  refine SepWP.weaken_pre hRepack ?_
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun3]) ?_
  refine hpost _ (by simp [arm64_norm]) (by simp [arm64_norm]) ?_
    ⟨by simp [arm64_norm], by simp [arm64_norm],
     by simp [arm64_norm, sigActions_setPC, sigActions_writeReg64],
     by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
    (by simp [arm64_norm])
  refine ⟨by simpa [arm64_norm] using hcs3 .x19 (by simp),
    by simpa [arm64_norm] using hcs3 .x20 (by simp),
    by simpa [arm64_norm] using hcs3 .x21 (by simp),
    by simpa [arm64_norm] using hcs3 .x22 (by simp),
    by simpa [arm64_norm] using hcs3 .x23 (by simp),
    by simpa [arm64_norm] using hcs3 .x24 (by simp),
    by simpa [arm64_norm] using hcs3 .x25 (by simp),
    by simpa [arm64_norm] using hcs3 .x26 (by simp),
    by simpa [arm64_norm] using hcs3 .x27 (by simp),
    by simpa [arm64_norm] using hcs3 .x28 (by simp),
    by simp [arm64_norm], by simpa [calleeSavedVRegs, arm64_norm] using hv3⟩

private theorem rdlAlloc_placed_posix_call {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (allocAddr : BitVec 64)
    (hCode : hasInstrs P allocAddr
      (rdlAllocInstrs allocAddr cAddrs.malloc cAddrs.posixMemalign))
    (hPosix : subroutine_ok P cAddrs.posixMemalign
      (withExtra extra
        (ToBaseSpec.toSpec (mallocngPosixMemalignSpec J Syscall.standard γ mAddrs) P.base)))
    (sizeBv alignBv w0 : BitVec 64) (lb lk : Nat)
    (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (R : SepProp) (s0 s2 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign) :
    let effAlign := if ConditionHolds .HI (subsPState64 alignBv 8#64) then alignBv else 8#64
    let retPC := allocAddr + 0x40#64
    let A := mallocngRustCliAllocWithOf J hIf extra γ mAddrs
    let xR := (sizeBv.toNat, alignBv.toNat, lb, lk)
    s2.pc = cAddrs.posixMemalign →
    s2.status = .Running →
    s2.sp = s0.sp - 32#64 →
    s2.readReg64 .x0 = s0.sp - 24#64 →
    s2.readReg64 .x1 = effAlign →
    s2.readReg64 .x2 = sizeBv →
    s2.readReg64 Reg.lr = retPC →
    (∀ r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      s2.readReg64 r = s0.readReg64 r) →
    calleeSavedVRegs s2 = calleeSavedVRegs s0 →
    AllocCallPreserved s0 s2 →
    s2.brk = s0.brk →
    SepWP P (s0.readReg64 Reg.lr) s2
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗
        extra ∗
        stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
        ((s0.sp - 32#64) ↦₆₄ w0) ∗
        ((s0.sp - 24#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustStdAllocSpec A).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustStdAllocSpec A).onOom xR s0 sf) := by
  intro effAlign retPC A xR hpc2 hrun2 hsp2 hx0_2 hx1_2 hx2_2 hlr2 hcs2 hv2 hpres02 hbrk2
  obtain ⟨_hEffNat, _hEffGe8, hEffMax, _hPowEff, hEffMax16, hEffSz, hPosixOk, hPosixRet⟩ :=
    effAlign_props (size := sizeBv) hPow2 hAlMax
  change effAlign.toNat ≤ MaxAlignedAllocAlign at hEffMax
  change max effAlign.toNat 16 = max alignBv.toNat 16 at hEffMax16
  change mallocngAlignedEffSize effAlign.toNat sizeBv.toNat = _ at hEffSz
  change mallocngPosixMemalignOk effAlign sizeBv = _ at hPosixOk
  change mallocngPosixMemalignRet effAlign sizeBv = _ at hPosixRet
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl32b : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true := spAligned_sub32 hspAl0
  let FrameF := stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
    ((s0.sp - 32#64) ↦₆₄ w0) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  let xP := (s0.sp - 24#64, effAlign, sizeBv, s0.sp - 32#64, s0.tpidrEl0, s0.brkStart, b, ivs0)
  refine SepWP.call_subroutine_frame (F := FrameF) (x := xP) hPosix (ret_pc := retPC)
    hpc2 hrun2 (by simpa [State.spAligned, hsp2] using hspAl32b) hlr2
    (fun R' hsat => ?_)
    (fun _ _ _ hp => by
      dsimp only [withExtra, ToBaseSpec.toSpec, mallocngPosixMemalignSpec] at hp
      exact not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => by
      dsimp only [withExtra, ToBaseSpec.toSpec, mallocngPosixMemalignSpec] at he
      exact not_satisfies_false_sepConj he)
    (fun s3 hpc3 hrun3 hsp3 hcs3 => ?_)
    (fun R' sf _ ho => ?_)
  · dsimp only [withExtra, ToBaseSpec.toSpec, mallocngPosixMemalignSpec, xP, OptOutPtr, FrameF]
    have hEnv2 :
        MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 =
          MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s2 := by
      unfold MallocngEnv; rw [hpres02.2.2.2.1, hpres02.2.2.2.2.1, hbrk2]
    rw [hEnv2] at hsat
    have hsat' : s2.mem ⊨
        ((((s0.sp - 24#64) ↦₆₄ 0#64) ∗
          (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s2 ∗
           stackFrameAt (s0.sp - 32#64) mallocngStackBytes)) ∗ extra) ∗
        ((stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
          ((s0.sp - 32#64) ↦₆₄ w0) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗ R') :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hsat
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hsat'
    refine Entails.pure_right ⟨hx0_2, hx1_2, hx2_2, hsp2, trivial, trivial, trivial, hEffMax⟩ ?_
    exact sepConj_mono_left (pointsTo64_entails_memRegion8 (s0.sp - 24#64) 0#64)
  · have hcs3_regs : ∀ r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
        s3.readReg64 r = s0.readReg64 r := by
      obtain ⟨d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, _, _⟩ := hcs3
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact d19.trans (hcs2 .x19 (by simp))
      · exact d20.trans (hcs2 .x20 (by simp))
      · exact d21.trans (hcs2 .x21 (by simp))
      · exact d22.trans (hcs2 .x22 (by simp))
      · exact d23.trans (hcs2 .x23 (by simp))
      · exact d24.trans (hcs2 .x24 (by simp))
      · exact d25.trans (hcs2 .x25 (by simp))
      · exact d26.trans (hcs2 .x26 (by simp))
      · exact d27.trans (hcs2 .x27 (by simp))
      · exact d28.trans (hcs2 .x28 (by simp))
    have hv3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hcs3.2.2.2.2.2.2.2.2.2.2.2.trans hv2
    have hsp3' : s3.sp = s0.sp - 32#64 := hsp3.trans hsp2
    dsimp only [withExtra, ToBaseSpec.toSpec, mallocngPosixMemalignSpec, xP, OptOutPtr]
    rw [hPosixOk, hPosixRet, hEffSz, hEffMax16]
    simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hw0_3, hAcc23⟩
    have hpres03 : AllocCallPreserved s0 s3 :=
      allocCallPreserved_trans hpres02 (allocCallPreserved_of_mallocngProcPreserved hAcc23.1)
    by_cases hFit : MallocngLayoutFit sizeBv alignBv
    · have hOkT : decide (MallocngLayoutFit sizeBv alignBv) = true := decide_eq_true hFit
      rw [hOkT]
      simp only [hFit, ↓reduceIte] at hw0_3
      unfold outPtrPost
      dsimp only [MallocngBlock]
      simp only [↓reduceIte, sepExists_sepConj_left, sepConj_assoc]
      apply SepWP.exists_elim; intro q
      apply SepWP.pure_elim; rintro ⟨hqNe, hqDvd, _⟩
      let budT := mallocngAlignedBudget true effAlign.toNat sizeBv.toNat b
      let RestOk :=
        (StdErrnoCell s0.tpidrEl0 ∗
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb + sizeBv.toNat) (lk + 1) s3) ∗
        J.Block γ q sizeBv.toNat ∗ memRegion q sizeBv.toNat
      have hCollapseOk :
          ((s0.sp - 24#64) ↦₆₄ q) ∗ (J.Block γ q sizeBv.toNat ∗
            (memRegion q sizeBv.toNat ∗
              (MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart budT ivs0 s2 s3 ∗
               (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗ (extra ∗ FrameF))))) ⊢
          ((((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
           (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
            stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗ RestOk) := by
        dsimp only [FrameF, RestOk]
        have hEqPre :
            ((s0.sp - 24#64) ↦₆₄ q) ∗ (J.Block γ q sizeBv.toNat ∗
              (memRegion q sizeBv.toNat ∗
                (MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart budT ivs0 s2 s3 ∗
                 (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
                  (extra ∗
                   (stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
                    ((s0.sp - 32#64) ↦₆₄ w0) ∗
                    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
                    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr))))))) =
            ((((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
             (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
              stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗
             ((MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart budT ivs0 s2 s3 ∗ extra) ∗
              J.Block γ q sizeBv.toNat ∗ memRegion q sizeBv.toNat)) := by ac_rfl
        rw [hEqPre]
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (postEnv_withExtra_entails_errno_pool hIf extra γ mAddrs budT ivs0
            (lb + sizeBv.toNat) (lk + 1) s0 s2 s3)))
      refine SepWP.weaken_pre hCollapseOk ?_
      refine rdlAlloc_placed_epilogue hCode s0 s3 w0 q RestOk _ _ hsp_align
        hpc3 hrun3 hsp3' hcs3_regs hv3 fun sf hx0f hspf hcsf hprocf hbrkf => ?_
      refine ⟨fun hsat => ?_, hspf, hcsf⟩
      have hEqTrue : ConditionHolds .EQ (subsPState32 (s3.readReg32 .x0) 0#32) = true := by
        rw [hw0_3]; exact (cond_eq_subs32_iff_eq 0#32 0#32).mpr rfl
      have hx0_q : sf.readReg64 .x0 = q := by rw [hx0f, hEqTrue]; rfl
      have hqNe0 : q ≠ 0 := hqNe
      have hMod : q.toNat % alignBv.toNat = 0 :=
        Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (pow2_dvd_max16 hPow2) hqDvd)
      have hPres0f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres03 hprocf
      have hPoolSf :
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb + sizeBv.toNat) (lk + 1) s3 =
            (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb + sizeBv.toNat) (lk + 1) sf :=
        ((mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool_transport
          (lb + sizeBv.toNat) (lk + 1) s3 sf ⟨hprocf.2.2.2.2.1, hbrkf, hprocf.2.2.2.1⟩).symm
      dsimp only [rustStdAllocSpec, A, xR, RestOk] at hsat ⊢
      simp only [hx0_q, hqNe0, ↓reduceIte]
      have hLiveEq :
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).live q sizeBv.toNat alignBv.toNat =
          (⌜q.toNat % alignBv.toNat = 0 ∧ RustLayoutOk sizeBv.toNat alignBv.toNat⌝ ∗
           J.Block γ q sizeBv.toNat) := rfl
      have hCostEq :
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).cost sizeBv.toNat alignBv.toNat =
            sizeBv.toNat := rfl
      rw [hLiveEq, hCostEq]
      rw [hPoolSf] at hsat
      refine Satisfies.mono (sepConj_mono_left ?_) hsat
      have hLive : J.Block γ q sizeBv.toNat ⊢
          ⌜q.toNat % alignBv.toNat = 0 ∧ RustLayoutOk sizeBv.toNat alignBv.toNat⌝ ∗
            J.Block γ q sizeBv.toNat :=
        Entails.pure_right ⟨hMod, hLayout⟩ (Entails.refl _)
      have hModWrap :
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb + sizeBv.toNat) (lk + 1) sf ⊢
          ⌜q.toNat % alignBv.toNat = 0⌝ ∗
            (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb + sizeBv.toNat) (lk + 1) sf :=
        Entails.pure_right hMod (Entails.refl _)
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right hModWrap))) ?_
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hLive))) ?_
      have hEqPost :
          Rust.hookFrame s0.sp ∗
            ((StdErrnoCell s0.tpidrEl0 ∗
              (⌜q.toNat % alignBv.toNat = 0⌝ ∗
                (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb + sizeBv.toNat) (lk + 1) sf)) ∗
             (⌜q.toNat % alignBv.toNat = 0 ∧ RustLayoutOk sizeBv.toNat alignBv.toNat⌝ ∗
              J.Block γ q sizeBv.toNat) ∗
             memRegion q sizeBv.toNat) =
          StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp ∗
            (⌜q.toNat % alignBv.toNat = 0⌝ ∗
              (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool (lb + sizeBv.toNat) (lk + 1) sf ∗
              (⌜q.toNat % alignBv.toNat = 0 ∧ RustLayoutOk sizeBv.toNat alignBv.toNat⌝ ∗
                J.Block γ q sizeBv.toNat) ∗
              memRegion q sizeBv.toNat) := by ac_rfl
      rw [hEqPost]
      exact Entails.pure_right hPres0f (Entails.refl _)
    · have hOkF : decide (MallocngLayoutFit sizeBv alignBv) = false := decide_eq_false hFit
      rw [hOkF]
      simp only [hFit, ↓reduceIte] at hw0_3
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hNull : NullAllowed sizeBv.toNat alignBv.toNat := not_layoutFit_imp_gt_2pow62 hFit
      apply SepWP.weaken_pre
        (sepConj_mono_left (RdlAllocH.memRegion8_entails_exists_pointsTo64 (s0.sp - 24#64)))
      simp only [sepExists_sepConj_left]
      apply SepWP.exists_elim; intro q
      let budF := mallocngAlignedBudget false effAlign.toNat sizeBv.toNat b
      let RestFail :=
        StdErrnoCell s0.tpidrEl0 ∗
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk s3
      have hCollapseFail :
          ((s0.sp - 24#64) ↦₆₄ q) ∗
            (MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart budF ivs0 s2 s3 ∗
             (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗ (extra ∗ FrameF))) ⊢
          ((((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
           (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
            stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗ RestFail) := by
        dsimp only [FrameF, RestFail]
        have hEqPre :
            ((s0.sp - 24#64) ↦₆₄ q) ∗
              (MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart budF ivs0 s2 s3 ∗
               (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
                (extra ∗
                 (stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
                  ((s0.sp - 32#64) ↦₆₄ w0) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
                  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr))))) =
            ((((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
             (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
              stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗
             (MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart budF ivs0 s2 s3 ∗ extra)) := by
          ac_rfl
        rw [hEqPre]
        exact sepConj_mono_right (sepConj_mono_right
          (postEnv_withExtra_entails_errno_pool hIf extra γ mAddrs budF ivs0 lb lk s0 s2 s3))
      refine SepWP.weaken_pre hCollapseFail ?_
      refine rdlAlloc_placed_epilogue hCode s0 s3 w0 q RestFail _ _ hsp_align
        hpc3 hrun3 hsp3' hcs3_regs hv3 fun sf hx0f hspf hcsf hprocf hbrkf => ?_
      refine ⟨fun hsat => ?_, hspf, hcsf⟩
      have hEqFalse : ConditionHolds .EQ (subsPState32 (s3.readReg32 .x0) 0#32) = false := by
        rw [hw0_3]; exact Bool.eq_false_iff.mpr fun h =>
          absurd ((cond_eq_subs32_iff_eq 12#32 0#32).mp h) (by decide)
      have hx0_0 : sf.readReg64 .x0 = 0 := by rw [hx0f, hEqFalse]; rfl
      have hPres0f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres03 hprocf
      have hPoolSf :
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk s3 =
            (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk sf :=
        ((mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool_transport
          lb lk s3 sf ⟨hprocf.2.2.2.2.1, hbrkf, hprocf.2.2.2.1⟩).symm
      dsimp only [rustStdAllocSpec, A, xR, RestFail] at hsat ⊢
      simp only [hx0_0, ↓reduceIte]
      rw [hPoolSf] at hsat
      refine Satisfies.mono (sepConj_mono_left ?_) hsat
      have hNullWrap :
          (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk sf ⊢
          ⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ ∗
            (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk sf :=
        Entails.pure_right hNull (Entails.refl _)
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right hNullWrap)) ?_
      have hEqPost :
          Rust.hookFrame s0.sp ∗
            (StdErrnoCell s0.tpidrEl0 ∗
              (⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ ∗
                (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk sf)) =
          StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp ∗
            (⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ ∗
              (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk sf) := by ac_rfl
      rw [hEqPost]
      exact Entails.pure_right hPres0f (Entails.refl _)
  · dsimp only [withExtra, ToBaseSpec.toSpec, mallocngPosixMemalignSpec, xP] at ho
    dsimp only [rustStdAllocSpec, A, xR]
    rw [satisfies_pure_sepConj] at ho
    obtain ⟨hOom2, hFR⟩ := ho
    have hOom2f := oomCond_imp_preserved hOom2
    have hOom0f : OomPreserved s0 sf :=
      ⟨hOom2f.1.trans hpres02.1, hOom2f.2.1.trans hpres02.2.1, hOom2f.2.2.trans hpres02.2.2.1⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hOom0f, Satisfies.drop_left hFR⟩

private theorem rdlAlloc_placed_posix_args {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (allocAddr : BitVec 64)
    (hCode : hasInstrs P allocAddr
      (rdlAllocInstrs allocAddr cAddrs.malloc cAddrs.posixMemalign))
    (hPosix : subroutine_ok P cAddrs.posixMemalign
      (withExtra extra
        (ToBaseSpec.toSpec (mallocngPosixMemalignSpec J Syscall.standard γ mAddrs) P.base)))
    (sizeBv alignBv w0 w1 : BitVec 64) (lb lk : Nat)
    (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (R : SepProp) (s0 sm : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign)
    (hpcm : sm.pc = allocAddr + 0x2c#64) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 32#64)
    (hpstm : sm.pstate = subsPState64 alignBv 8#64)
    (hx1_m : sm.readReg64 .x1 = alignBv) (hx2_m : sm.readReg64 .x2 = sizeBv)
    (hcsm : ∀ r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      sm.readReg64 r = s0.readReg64 r)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hpres0m : AllocCallPreserved s0 sm) (hbrkm : sm.brk = s0.brk) :
    let A := mallocngRustCliAllocWithOf J hIf extra γ mAddrs
    let xR := (sizeBv.toNat, alignBv.toNat, lb, lk)
    SepWP P (s0.readReg64 Reg.lr) sm
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗
        extra ∗
        stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
        ((s0.sp - 32#64) ↦₆₄ w0) ∗
        ((s0.sp - 24#64) ↦₆₄ w1) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustStdAllocSpec A).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustStdAllocSpec A).onOom xR s0 sf) := by
  intro A xR
  have hf11 := fetch_instr_at 11 hCode
  have hf12 := fetch_instr_at 12 hCode
  have hf13 := fetch_instr_at 13 hCode
  have hf14 := fetch_instr_at 14 hCode
  have hf15 := fetch_instr_at 15 hCode
  have ha_sp8 : sm.sp + 8#64 = s0.sp - 24#64 := by rw [hspm]; bv_omega
  wp_step; wp_step; wp_step; wp_step; wp_step
  exact rdlAlloc_placed_posix_call hIf extra γ allocAddr hCode hPosix
    sizeBv alignBv w0 lb lk b ivs0 R s0 _
    hsp_align hLayout hPow2 hAlMax
    (by simp only [arm64_norm]; bv_omega)
    (by simp [arm64_norm, hrunm])
    (by simp [arm64_norm, hspm])
    (by simp only [arm64_norm])
    (by simp [arm64_norm])
    (by simp only [arm64_norm, hx2_m])
    (by simp only [arm64_norm])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa only [arm64_norm] using hcsm _ (by simp))
    (by simpa only [calleeSavedVRegs, arm64_norm] using hvm)
    (allocCallPreserved_trans hpres0m
      ⟨by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm, sigActions_setPC, sigActions_setMem, sigActions_writeReg64],
       by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm]⟩)
    (by simp [arm64_norm, hbrkm])

private theorem rdlAlloc_placed_posix_path {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (allocAddr : BitVec 64)
    (hCode : hasInstrs P allocAddr
      (rdlAllocInstrs allocAddr cAddrs.malloc cAddrs.posixMemalign))
    (hPosix : subroutine_ok P cAddrs.posixMemalign
      (withExtra extra
        (ToBaseSpec.toSpec (mallocngPosixMemalignSpec J Syscall.standard γ mAddrs) P.base)))
    (sizeBv alignBv : BitVec 64) (lb lk : Nat)
    (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (R : SepProp) (s0 s1 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign)
    (hpc1 : s1.pc = allocAddr + 0x1c#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp)
    (hx1_1 : s1.readReg64 .x1 = alignBv) (hx2_1 : s1.readReg64 .x2 = sizeBv)
    (hlr1 : s1.readReg64 Reg.lr = s0.readReg64 Reg.lr)
    (hcs1 : CalleeSavedPreserved s0 s1)
    (hpres01 : AllocCallPreserved s0 s1) (hbrk1 : s1.brk = s0.brk) :
    let A := mallocngRustCliAllocWithOf J hIf extra γ mAddrs
    let xR := (sizeBv.toNat, alignBv.toNat, lb, lk)
    SepWP P (s0.readReg64 Reg.lr) s1
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗
        extra ∗ Rust.hookFrame s0.sp)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustStdAllocSpec A).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustStdAllocSpec A).onOom xR s0 sf) := by
  intro A xR
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl32b : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true := spAligned_sub32 hspAl0
  have hspAl32 : decide ((s0.sp - 32#64) &&& 15#64 = 0#64) = true :=
    decide_eq_true (beq_iff_eq.mp hspAl32b)
  have hUnpack :
      MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗
        extra ∗ Rust.hookFrame s0.sp =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗ extra ∗
          stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
          stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
          ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗
          ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3)) := by
    rw [hookFrame_eq_stack32_1024 s0.sp, stackFrameAt32_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ => by ac_rfl))))
  rw [hUnpack]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  have hf7 := fetch_instr_at 7 hCode
  have hf8 := fetch_instr_at 8 hCode
  have hf9 := fetch_instr_at 9 hCode
  have hf10 := fetch_instr_at 10 hCode
  have ha_sp : s1.sp + (-32#64) = s0.sp - 32#64 := by rw [hsp1]; bv_omega
  obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩ := hcs1
  have _ : s1.readReg64 (.gpr 29#5) = s0.readReg64 .x29 := c29
  wp_step; wp_step; wp_step; wp_step
  exact rdlAlloc_placed_posix_args hIf extra γ allocAddr hCode hPosix
    sizeBv alignBv w0 w1 lb lk b ivs0 R s0 _
    hsp_align hLayout hPow2 hAlMax
    (by simp [arm64_norm])
    (by simp [arm64_norm, hrun1])
    (by simp [arm64_norm])
    (by simp [arm64_norm])
    (by simp [arm64_norm, hx1_1])
    (by simp [arm64_norm, hx2_1])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa only [arm64_norm] using c19
      · simpa only [arm64_norm] using c20
      · simpa only [arm64_norm] using c21
      · simpa only [arm64_norm] using c22
      · simpa only [arm64_norm] using c23
      · simpa only [arm64_norm] using c24
      · simpa only [arm64_norm] using c25
      · simpa only [arm64_norm] using c26
      · simpa only [arm64_norm] using c27
      · simpa only [arm64_norm] using c28)
    (by simpa only [calleeSavedVRegs, arm64_norm] using cv)
    (allocCallPreserved_trans hpres01
      ⟨by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm, sigActions_setPC, sigActions_setMem, sigActions_writeReg64],
       by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm]⟩)
    (by simp [arm64_norm, hbrk1])

theorem rdlAlloc_placed_withExtra_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (allocAddr : BitVec 64)
    (hCode : hasInstrs P allocAddr
      (rdlAllocInstrs allocAddr cAddrs.malloc cAddrs.posixMemalign))
    (hC : MallocngProgCContractsWith J extra P mAddrs cAddrs) :
    subroutine_ok P allocAddr
      (rustStdAllocSpec (mallocngRustCliAllocWithOf J hIf extra γ mAddrs)) := by
  let A := mallocngRustCliAllocWithOf J hIf extra γ mAddrs
  apply subroutine_ok_of_sepWP_init
  rintro ⟨size, align, lb, lk⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [rustStdAllocSpec, A] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hLayout, _hCan⟩, hpre⟩ := hpre
  let sizeBv := s0.readReg64 .x0
  let alignBv := s0.readReg64 .x1
  have hx0_bv : s0.readReg64 .x0 = sizeBv := rfl
  have hx1_bv : s0.readReg64 .x1 = alignBv := rfl
  change sizeBv.toNat = size at hx0
  change alignBv.toNat = align at hx1
  subst hx0; subst hx1
  have ⟨_hSzPos, ⟨k, hk⟩, _hSum63, hAlMax⟩ := hLayout
  have hPow2 : IsPow2Align alignBv := isPow2Align_of_toNat_pow2 hk
  have hAlMax' : alignBv.toNat ≤ MaxAlignedAllocAlign := hAlMax
  have hPoolEq :
      ((mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk s0 ∗
        StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp) ∗ R =
      ((∃∗ b : MallocngBudget, ∃∗ ivs0 : List (BitVec 64 × Nat),
          J.MallocngHeap γ mAddrs s0.tpidrEl0 s0.brkStart s0.brk b ivs0) ∗
        extra ∗ Rust.hookFrame s0.sp) ∗ R := by
    rw [← sepConj_assoc ((mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk s0),
        mallocngRustCliPoolWithOf_sep_stdErrnoCell_eq hIf extra γ mAddrs lb lk s0,
        sepConj_assoc (∃∗ b : MallocngBudget, _)]
  rw [hPoolEq] at hpre
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hpre
  obtain ⟨b, hpre⟩ := hpre
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hpre
  obtain ⟨ivs0, hpre⟩ := hpre
  have hEnvPre : s0.mem ⊨
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗
        extra ∗ Rust.hookFrame s0.sp) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
    unfold MallocngEnv
    exact Entails.pure_right ⟨rfl, rfl⟩ (Entails.refl _)
  refine ⟨_, hEnvPre, ?_⟩
  have hf0 := fetch_instr_at0 hCode
  have hf1 := fetch_instr_at 1 hCode
  have hf2 := fetch_instr_at 2 hCode
  have hf3 := fetch_instr_at 3 hCode
  have hf4 := fetch_instr_at 4 hCode
  have hf5 := fetch_instr_at 5 hCode
  have hf6 := fetch_instr_at 6 hCode
  wp_step; wp_step
  by_cases hAl16 : alignBv.toNat ≤ 16
  · have hHi1 : ConditionHolds .HI (subsPState64 alignBv 16#64) = false :=
      Bool.eq_false_iff.mpr fun h => by
        have := (RdlAllocH.cond_hi_subs64_iff_lt alignBv 16#64).mp h
        change 16 < alignBv.toNat at this; omega
    wp_step; wp_step
    by_cases hAlSz : alignBv.toNat ≤ sizeBv.toNat
    · have hHi2 : ConditionHolds .HI (subsPState64 alignBv sizeBv) = false :=
        Bool.eq_false_iff.mpr fun h => by
          have := (RdlAllocH.cond_hi_subs64_iff_lt alignBv sizeBv).mp h; omega
      wp_step; wp_step; wp_step
      exact rdlAlloc_placed_fast_path hIf extra γ (hC.malloc_ok γ)
        sizeBv alignBv lb lk b ivs0 R s0 _
        hsp_align hLayout hPow2 hAl16
        (by simp only [State.pc_setPC]; bv_omega)
        (by simp [arm64_norm, hrun])
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        (by unfold CalleeSavedPreserved; simp [arm64_norm, calleeSavedVRegs])
        ⟨by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm, sigActions_setPC, sigActions_writeReg64],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
        (by simp [arm64_norm])
    · have hHi2 : ConditionHolds .HI (subsPState64 alignBv sizeBv) = true :=
        (RdlAllocH.cond_hi_subs64_iff_lt alignBv sizeBv).mpr (by omega)
      wp_step
      exact rdlAlloc_placed_posix_path hIf extra γ allocAddr hCode (hC.posixMemalign_ok γ)
        sizeBv alignBv lb lk b ivs0 R s0 _
        hsp_align hLayout hPow2 hAlMax'
        (by simp only [State.pc_setPC])
        (by simp [arm64_norm, hrun])
        (by simp [arm64_norm])
        (by simp [arm64_norm, hx1_bv])
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        (by unfold CalleeSavedPreserved; simp [arm64_norm, calleeSavedVRegs])
        ⟨by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm, sigActions_setPC, sigActions_writeReg64],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
        (by simp [arm64_norm])
  · have hHi1 : ConditionHolds .HI (subsPState64 alignBv 16#64) = true :=
      (RdlAllocH.cond_hi_subs64_iff_lt alignBv 16#64).mpr (by change 16 < alignBv.toNat; omega)
    wp_step
    exact rdlAlloc_placed_posix_path hIf extra γ allocAddr hCode (hC.posixMemalign_ok γ)
      sizeBv alignBv lb lk b ivs0 R s0 _
      hsp_align hLayout hPow2 hAlMax'
      (by simp only [State.pc_setPC])
      (by simp [arm64_norm, hrun])
      (by simp [arm64_norm])
      (by simp [arm64_norm, hx1_bv])
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (by unfold CalleeSavedPreserved; simp [arm64_norm, calleeSavedVRegs])
      ⟨by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm, sigActions_setPC, sigActions_writeReg64],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
      (by simp [arm64_norm])

/-! ## `B`-Thunk Corollaries -/

theorem rustStdAlloc_of_b_thunk (A : RustStdAlloc OomPreserved)
    {P : Program} (thunkAddr targetAddr : BitVec 64)
    (hThunk : hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ])
    (hTarget : subroutine_ok P targetAddr (rustStdAllocSpec A)) :
    subroutine_ok P thunkAddr (rustStdAllocSpec A) :=
  subroutine_ok_of_b_thunk (fetch_instr_at0 hThunk)
    (hpre_pc := by
      rintro ⟨size, align, lb, lk⟩ s pc'
      dsimp only [rustStdAllocSpec]
      rw [A.pool_transport lb lk s (s.setPC pc') ⟨rfl, rfl, rfl⟩]
      rfl)
    (hpost_pc := by rintro ⟨_, _, _, _⟩ _ _ _; rfl)
    (hoom_pc := by rintro ⟨_, _, _, _⟩ _ _ _; rfl)
    (hok := hTarget)

theorem rustStdDealloc_of_b_thunk {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (thunkAddr targetAddr : BitVec 64)
    (hThunk : hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ])
    (hTarget : subroutine_ok P targetAddr (rustStdDeallocSpec A)) :
    subroutine_ok P thunkAddr (rustStdDeallocSpec A) :=
  subroutine_ok_of_b_thunk (fetch_instr_at0 hThunk)
    (hpre_pc := by
      rintro ⟨p, size, align, lb, lk⟩ s pc'
      dsimp only [rustStdDeallocSpec]
      rw [A.pool_transport lb lk s (s.setPC pc') ⟨rfl, rfl, rfl⟩]
      rfl)
    (hpost_pc := by rintro ⟨_, _, _, _, _⟩ _ _ _; rfl)
    (hoom_pc := by rintro ⟨_, _, _, _, _⟩ _ _ _; rfl)
    (hok := hTarget)

theorem rdlAlloc_thunk_withExtra_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (thunkAddr targetAddr : BitVec 64)
    (hThunk : hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ])
    (hCode : hasInstrs P targetAddr
      (rdlAllocInstrs targetAddr cAddrs.malloc cAddrs.posixMemalign))
    (hC : MallocngProgCContractsWith J extra P mAddrs cAddrs) :
    subroutine_ok P thunkAddr
      (rustStdAllocSpec (mallocngRustCliAllocWithOf J hIf extra γ mAddrs)) :=
  rustStdAlloc_of_b_thunk _ thunkAddr targetAddr hThunk
    (rdlAlloc_placed_withExtra_ok hIf extra γ targetAddr hCode hC)

theorem rdlDealloc_thunk_withExtra_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (thunkAddr targetAddr : BitVec 64)
    (hThunk : hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ])
    (hCode : hasInstrs P targetAddr (rdlDeallocInstrs targetAddr cAddrs.free))
    (hC : MallocngProgCContractsWith J extra P mAddrs cAddrs) :
    subroutine_ok P thunkAddr
      (rustStdDeallocSpec (mallocngRustCliAllocWithOf J hIf extra γ mAddrs)) :=
  rustStdDealloc_of_b_thunk _ thunkAddr targetAddr hThunk
    (rdlDealloc_placed_withExtra_ok hIf extra γ targetAddr hCode hC)

end VerifiedLibraries.RustStd
