/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.AlignedReframeFine
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Fine-Grained Placed `aligned_alloc` and `posix_memalign`

Placed entrypoint verification for `aligned_alloc` (`blk12`) and `posix_memalign` (`blk11`) over
`FineBudget`, threading an internal 736-byte stack contract (`alignedAllocFineErrnoSpec`) that
exposes the TLS `errno` cell (`EINVAL = 22` or `ENOMEM = 12`) on `NULL` return so `posix_memalign`
can read `*__errno_location()`.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.CType Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.ProgramReflection
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open AlignedStage1 AlignedReframeHelpers

/-! ## Separation-Logic Focus Helpers -/

private theorem sepWP_pure_left {prog : Program} {tgt : BitVec 64} {s : State}
    {p : Prop} {Q : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : p → SepWP prog tgt s Q post oom) :
    SepWP prog tgt s (⌜p⌝ ∗ Q) post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact SepWP.to_reaches_pc (h hm.1) hm.2

private theorem sepWP_let_state {prog : Program} {tgt : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ sc : State, sc = s → SepWP prog tgt sc P post oom) :
    SepWP prog tgt s P post oom :=
  h s rfl

private theorem stackFrame_eq_stackFrameAt (s : State) (n : Nat) (hn : n ≤ 2 ^ 64 := by omega) :
    stackFrame s n = stackFrameAt s.sp n :=
  (stackFrameAt_eq_memRegion s.sp n hn).symm

local macro "cells_unfold_pre" : tactic =>
  `(tactic| conv => arg 4; simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub,
    ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left])

local macro "proc_preserved_step" : tactic =>
  `(tactic| exact ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩)

private theorem sepWP_call_errno [MallocngMultiPlacement] {P : Program} {tgt ret_pc : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (herr : subroutine_ok P (mbase 0) (withCL mmpl {
      pre := fun (_ : Unit) _ => emp
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm ∧
         sf.readReg64 .x0 = s0.tpidrEl0 - 0xa4#64⌝ }))
    (hpc : s.pc = mbase 0) (hrun : s.status = .Running)
    (hspAl : (s.sp &&& 15#64 == 0#64) = true) (hlr : s.readReg64 .x30 = ret_pc)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hk : ∀ se : State, se.pc = ret_pc → se.status = .Running → se.sp = s.sp →
      CalleeSavedPreserved s se → VerifiedLibraries.mallocngLib.CodeLoaded mmpl se.mem →
      MallocngProcPreserved s se → se.brk = s.brk → se.mem.perm = s.mem.perm →
      se.readReg64 .x0 = s.tpidrEl0 - 0xa4#64 →
      SepWP P tgt se F post oom) :
    SepWP P tgt s F post oom := by
  refine SepWP.call_subroutine_frame (F := F) (x := ()) (ret_pc := ret_pc)
    herr hpc hrun (by simpa [State.spAligned] using hspAl) hlr
    (fun R' hm => by
      dsimp only [withCL]; rw [emp_sepConj, pure_sepConj_of_true hcl]; exact hm)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun se hpc_e hrun_e hsp_e hcs_e => ?_)
    (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  dsimp only [withCL] at *
  refine SepWP.weaken_pre (P' := ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl se.mem⌝ ∗
    ⌜MallocngProcPreserved s se ∧ se.brk = s.brk ∧ se.mem.perm = s.mem.perm ∧
      se.readReg64 .x0 = s.tpidrEl0 - 0xa4#64⌝ ∗ F) (Entails.of_eq (by ac_rfl)) ?_
  exact sepWP_pure_left fun hcl_e => sepWP_pure_left fun ⟨hproc_e, hbrk_e, hperm_e, hx0_e⟩ =>
    hk se hpc_e hrun_e hsp_e hcs_e hcl_e hproc_e hbrk_e hperm_e hx0_e

private theorem fineEnv_focus_replaced (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (b : FineBudget) (ivs : List (BitVec 64 × Nat)) (s : State) :
    ∃ RestEnv : SepProp,
      FineEnv γ A tp brkStart b ivs s = ((A.replaced ↦₃₂ 0#32) ∗ RestEnv) := by
  let body := fun (st : MallocngSt) (alignMap : BitVec 64 → Option Nat) (liveCost peakCost : Nat) =>
    ⌜MallocngFineInv 0 b ivs alignMap st⌝ ∗
    ghostMapAuth (fineAlignGam γ) alignMap ∗
    ⌜MallocngWFInflight 0 A.base brkStart s.brk liveCost peakCost st⌝ ∗
    MallocngLiveAuth (fineBaseGam γ) st.liveMap ∗
    (A.ctx ↦ₛ st.ctx.toBytes) ∗ (A.lock ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
    MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
    MappedSet st.masterDom (OwnedMappedByte st)
  refine ⟨⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
    MallocngRoTablesA A ∗ MallocngRuntime A tp ∗
    (∃∗ st, ∃∗ alignMap, ∃∗ liveCost, ∃∗ peakCost, body st alignMap liveCost peakCost), ?_⟩
  dsimp only [FineEnv]
  rw [FineHeapImpl_eq, FineCoreImpl_eq]
  have hEx :
      (∃∗ st, ∃∗ alignMap, ∃∗ liveCost, ∃∗ peakCost,
        FineCoreStInflightA 0 γ A brkStart s.brk b ivs alignMap liveCost peakCost st) =
      ((A.replaced ↦₃₂ 0#32) ∗
        ∃∗ st, ∃∗ alignMap, ∃∗ liveCost, ∃∗ peakCost, body st alignMap liveCost peakCost) := by
    rw [sepExists_sepConj_right]; refine sepExists_congr fun st => ?_
    rw [sepExists_sepConj_right]; refine sepExists_congr fun alignMap => ?_
    rw [sepExists_sepConj_right]; refine sepExists_congr fun liveCost => ?_
    rw [sepExists_sepConj_right]; refine sepExists_congr fun peakCost => ?_
    dsimp only [FineCoreStInflightA, MallocngCoreStInflightA, body]
    ac_rfl
  rw [hEx]; ac_rfl

private theorem ccmp_ovf_hi_iff {align len : BitVec 64} (hMax : align.toNat ≤ MaxAlignedAllocAlign) :
    ConditionHolds .HI
      (if ConditionHolds .CS (subsPState64 (~~~align) len) then subsPState64 align 0x7ffffffff#64
       else PState.ofBits4 2#4) = decide (2 ^ 64 ≤ len.toNat + align.toNat) := by
  obtain ⟨hUltFalse, hUleIff⟩ := alignedAlloc_ovf_iff (len := len) hMax
  have hCs : ConditionHolds .CS (subsPState64 (~~~align) len) = len.ule (~~~align) :=
    conditionHolds_cs_subsPState64 _ _
  have hHiSub : ConditionHolds .HI (subsPState64 align 0x7ffffffff#64) = false := by
    have hhi : ConditionHolds .HI (subsPState64 align 0x7ffffffff#64) =
        (0x7ffffffff#64).ult align := by simp [arm64_norm]
    rw [hhi, hUltFalse]
  rw [hCs]
  cases hUle : len.ule (~~~align)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hOvf : 2 ^ 64 ≤ len.toNat + align.toNat := hUleIff.mp hUle
    simp only [decide_eq_true hOvf]; rfl
  · simp only [↓reduceIte, hHiSub]
    have hNoOvf : ¬ 2 ^ 64 ≤ len.toNat + align.toNat := fun h => by
      have hf := hUleIff.mpr h; rw [hUle] at hf; cases hf
    simp [hNoOvf]

/-! ## Internal `aligned_alloc` Errno Contract -/

/-- Internal 736-byte stack contract for `aligned_alloc(align, len)` (`blk12`) over `FineBudget`,
    exposing the TLS `errno` cell (`22#32` when `!alignedAllocAlignOk align`, else `12#32`) on
    `NULL` return. -/
noncomputable def alignedAllocFineErrnoSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart align len : BitVec 64)
    (b : FineBudget) (ivs0 : List (BitVec 64 × Nat)) : Spec Unit :=
  let ok := mallocngAlignedAllocOk align len
  let ev := FineEvent.aligned align.toNat len.toNat
  let bf := if ok then FineBudget.step ev b else b
  let stepB := if ok then fineStepReserve ev b else fineStepReserve (.alloc 0) b
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = align ∧ s0.readReg64 .x1 = len ∧
       align.toNat ≤ MaxAlignedAllocAlign⌝ ∗
      stackFrame s0 736 ∗
      FineEnv γ maddrs tp brkStart b ivs0 s0
    post := fun _ s0 sf =>
      ⌜MallocngCallAccounting 16 stepB s0 sf⌝ ∗
      stackFrame s0 736 ∗
      if ok then
        ∃∗ q : BitVec 64,
          ⌜sf.readReg64 .x0 = q ∧
           (FineBlockSem γ).pureWf q (len.toNat, max align.toNat 16)⌝ ∗
          FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
          (FineBlockSem γ).interp q (len.toNat, max align.toNat 16)
      else
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
         MallocngNoOrphanMappings ivs0 ivs0 s0.mem sf.mem⌝ ∗
        FineCoreImpl γ maddrs brkStart sf.brk bf ivs0 ∗
        ((tp - 0xa4#64) ↦₃₂ (if !alignedAllocAlignOk align then 22#32 else 12#32)) ∗
        ((maddrs.libc + 3#64) ↦₈ 0#8) ∗
        ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
    onOom := fun _ s0 sf =>
      ⌜FineStepOomCond msvc stepB s0 sf⌝
  }

set_option maxHeartbeats 400000 in
private theorem blk12_alignedAlloc_fine_errno (hImplRaw : LibcMallocImplFineRawStmt)
    [MallocngMultiPlacement] (γ : GhostName) (tp brkStart align len : BitVec 64)
    (bud : FineBudget) (ivs0 : List (BitVec 64 × Nat)) :
    subroutine_ok (mallocngBlockProg mmpl 12 msvc) (mbase 12)
      (alignedAllocFineErrnoSpec γ tp brkStart align len bud ivs0) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have hfn : ∀ c, (blkPC_b12.rebase c (fun _ => none)).fnAddr "aligned_alloc" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase, Program.fnOff, Program.findSymbol?, blkPC_b12, PlacedLib.program]
    rw [blkSymsEq_b12]
    have hf : (toStringSymbols blkSymChars_b12).find? (·.1 == "aligned_alloc") =
        some ("aligned_alloc", 0) := by decide
    rw [hf]; exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b12 (hfn (mbase 12)) fun b hb => ?_
  have hprog_b12 : blkPC_b12.rebase b (fun _ => none) = mallocngBlockProg mmpl 12 msvc := by
    rw [mallocngBlockProg_eq_b12, hb]
  rw [hfn b]
  have herr := placed_errnoLocation_perm_ok (P := blkPC_b12.rebase b (fun _ => none))
    (externAt?_placedProgram_rebase_none _ _ _ _) rfl
  apply subroutine_ok_of_sepWP_init
  rintro ⟨⟩ R s0 hpc hrun hpre hspAl0
  dsimp only [alignedAllocFineErrnoSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨rfl, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hAlignMax⟩, hpre⟩ := hpre
  have ⟨htp0, hbrks0⟩ : s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart := by
    have hm0 := hpre
    dsimp only [FineEnv] at hm0
    simp only [sepConj_comm (stackFrame s0 736), sepConj_assoc, satisfies_pure_sepConj] at hm0
    exact hm0.1
  refine ⟨stackFrame s0 736 ∗ FineEnv γ maddrs tp brkStart bud ivs0 s0,
    by simpa [sepConj_assoc] using hpre, ?_⟩
  rw [stackFrame_eq_stackFrameAt s0 736, stackFrameAt_736_split s0.sp]
  cells_unfold_pre
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  have hspAl32 : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true := s0.spAligned_sub 32#64 hspAl0
  wp_stp64_cl m1 hm1 hcl0 hcl1
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_if hAlignNe
  ·
    have hAlignFalse : alignedAllocAlignOk align = false := by
      have h0 : (align &&& ~~~(0#64 - align) == 0#64) = false := by
        cases hb0 : (align &&& ~~~(0#64 - align) == 0#64)
        · rfl
        · exfalso; apply hAlignNe; simpa [arm64_norm, hx0, beq_iff_eq] using hb0
      rwa [bics_neg_eq_zero_iff_alignOk] at h0
    have hOkFalse : mallocngAlignedAllocOk align len = false := by
      simp [mallocngAlignedAllocOk, hAlignFalse]
    conv => arg 4; dsimp only [FineEnv]
    conv => arg 4; rw [FineHeapImpl_eq, pure_sepConj_of_true ⟨htp0, hbrks0⟩]
    conv => arg 4; dsimp only [MallocngRuntime]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro ev
    wp_step
    have hpc_bl0 : b + 0x90#64 + (mbase 0 - mbase 12 - 0x90#64) = mbase 0 := by rw [hb]; bv_arith
    conv => arg 3; simp only [hpc_bl0]
    refine sepWP_call_errno (ret_pc := b + 0x94#64) herr (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simpa [arm64_norm] using hspAl32) (by simp [arm64_norm]) hcl1
      fun se hpc_e hrun_e hsp_e hcs_e hcl_e hproc_e hbrk_e hperm_e hx0_e => ?_
    have hsp_se : se.sp = s0.sp - 32#64 := by simpa [arm64_norm] using hsp_e
    have hx0_se : se.readReg64 (.gpr 0#5) = tp - 0xa4#64 := by simpa [arm64_norm, htp0] using hx0_e
    have hProc0_se : MallocngProcPreserved s0 se :=
      alignedProcPreserved_trans (by proc_preserved_step) hproc_e
    have hbrk_se : se.brk = s0.brk := hbrk_e.trans (by simp [arm64_norm])
    wp_step; wp_step; wp_step
    wp_str32_cl m2 hm2 hcl_e hcl2
    have _hspAl_se : (se.sp &&& 15#64 == 0#64) = true := by rw [hsp_se]; exact hspAl32
    have ha8 : se.sp + 8#64 = s0.sp - 24#64 := by rw [hsp_se]; bv_arith
    have ha32 : se.sp + 32#64 = s0.sp := by rw [hsp_se]; bv_arith
    wp_step; wp_step
    have hPermAll : m2.perm = s0.mem.perm := hm2.trans (hperm_e.trans hm1)
    refine sepWP_let_state fun sf hsf => ?_
    have hbrk_f : sf.brk = s0.brk := by subst hsf; simp [arm64_norm, hbrk_se]
    refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun_e]) ⟨fun hm => ?_, ?_, ?_⟩
    · refine Satisfies.mono (sepConj_mono_left ?_) hm
      simp only [hOkFalse, Bool.false_eq_true, ↓reduceIte, hAlignFalse, Bool.not_false, hbrk_f]
      have htp_f : se.tpidrEl0 = tp := hProc0_se.2.2.1.trans htp0
      have hbrks_f : se.brkStart = brkStart := hProc0_se.2.2.2.1.trans hbrks0
      rw [pure_sepConj_of_true ⟨alignedProcPreserved_trans hProc0_se (by subst hsf; proc_preserved_step),
            AlignedStage1.mappedDelta_of_perm_eq (by subst hsf; simpa [arm64_norm] using hPermAll)⟩,
        pure_sepConj_of_true ⟨by subst hsf; simp [arm64_norm], by subst hsf; simp [arm64_norm, htp_f],
          by subst hsf; simp [arm64_norm, hbrks_f],
          noOrphanMappings_refl_of_perm_eq (by subst hsf; simpa [arm64_norm] using hPermAll)⟩]
      cells_unfold; sep_frame
    · subst hsf; have _ := ha32; simp [arm64_norm]
    · subst hsf
      exact ⟨by simpa [arm64_norm] using hcs_e.readReg64_x19, by simpa [arm64_norm] using hcs_e.readReg64_x20,
        by simpa [arm64_norm] using hcs_e.readReg64_x21, by simpa [arm64_norm] using hcs_e.readReg64_x22,
        by simpa [arm64_norm] using hcs_e.readReg64_x23, by simpa [arm64_norm] using hcs_e.readReg64_x24,
        by simpa [arm64_norm] using hcs_e.readReg64_x25, by simpa [arm64_norm] using hcs_e.readReg64_x26,
        by simpa [arm64_norm] using hcs_e.readReg64_x27, by simpa [arm64_norm] using hcs_e.readReg64_x28,
        by simp [arm64_norm], by simpa [arm64_norm] using hcs_e.vregs⟩
  ·
    have hAlignOk : alignedAllocAlignOk align = true := by
      rw [← bics_neg_eq_zero_iff_alignOk]
      simpa [BitVec.zero_sub, beq_iff_eq] using hAlignNe
    have hNegAnd : -align &&& align = align := by
      simpa [BitVec.zero_sub] using neg_and_self_of_alignOk hAlignOk
    have ha16_sp : s0.sp - 32#64 + 16#64 = s0.sp - 16#64 := by bv_arith
    have ha24_sp : s0.sp - 16#64 + 8#64 = s0.sp - 8#64 := by bv_arith
    wp_step
    wp_stp64_cl m2 hm2 hcl1 hcl2
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_if hOvfHi
    ·
      have hOvf : 2 ^ 64 ≤ len.toNat + align.toNat := by
        have hCond : ConditionHolds .HI
            (if ConditionHolds .CS (subsPState64 (~~~align) len) then subsPState64 align 0x7ffffffff#64
             else PState.ofBits4 2#4) = true := by
          simpa [arm64_norm, hx0, hx1, hNegAnd] using hOvfHi
        rwa [ccmp_ovf_hi_iff hAlignMax, decide_eq_true_eq] at hCond
      have hEffGt : ¬ mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize := by
        unfold mallocngAlignedEffSize MallocngMaxAllocSize MaxAlignedAllocAlign at *; split <;> omega
      have hOkFalse : mallocngAlignedAllocOk align len = false := by
        simp [mallocngAlignedAllocOk, hEffGt]
      conv => arg 4; dsimp only [FineEnv]
      conv => arg 4; rw [FineHeapImpl_eq, pure_sepConj_of_true ⟨htp0, hbrks0⟩]
      conv => arg 4; dsimp only [MallocngRuntime]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro ev
      wp_step
      have hpc_bl0 : b + 0xac#64 + (mbase 0 - mbase 12 - 0xac#64) = mbase 0 := by rw [hb]; bv_arith
      conv => arg 3; simp only [hpc_bl0]
      refine sepWP_call_errno (ret_pc := b + 0xb0#64) herr (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simpa [arm64_norm] using hspAl32) (by simp [arm64_norm]) hcl2
        fun se hpc_e hrun_e hsp_e hcs_e hcl_e hproc_e hbrk_e hperm_e hx0_e => ?_
      have hsp_se : se.sp = s0.sp - 32#64 := by simpa [arm64_norm] using hsp_e
      have hx0_se : se.readReg64 (.gpr 0#5) = tp - 0xa4#64 := by simpa [arm64_norm, htp0] using hx0_e
      have hProc0_se : MallocngProcPreserved s0 se :=
        alignedProcPreserved_trans (by proc_preserved_step) hproc_e
      have hbrk_se : se.brk = s0.brk := hbrk_e.trans (by simp [arm64_norm])
      wp_step; wp_step; wp_step
      wp_str32_cl m3 hm3 hcl_e hcl3
      have _hspAl_se : (se.sp &&& 15#64 == 0#64) = true := by rw [hsp_se]; exact hspAl32
      have ha16_se : se.sp + 16#64 = s0.sp - 16#64 := by rw [hsp_se]; bv_arith
      have ha24_se : se.sp + 16#64 + 8#64 = s0.sp - 8#64 := by rw [hsp_se]; bv_arith
      have ha8 : se.sp + 8#64 = s0.sp - 24#64 := by rw [hsp_se]; bv_arith
      have ha32 : se.sp + 32#64 = s0.sp := by rw [hsp_se]; bv_arith
      wp_step; wp_step; wp_step; wp_step
      have hPermAll : m3.perm = s0.mem.perm := hm3.trans (hperm_e.trans (hm2.trans hm1))
      refine sepWP_let_state fun sf hsf => ?_
      have hbrk_f : sf.brk = s0.brk := by subst hsf; simp [arm64_norm, hbrk_se]
      refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun_e]) ⟨fun hm => ?_, ?_, ?_⟩
      · refine Satisfies.mono (sepConj_mono_left ?_) hm
        simp only [hOkFalse, Bool.false_eq_true, ↓reduceIte, hAlignOk, Bool.not_true, hbrk_f]
        have htp_f : se.tpidrEl0 = tp := hProc0_se.2.2.1.trans htp0
        have hbrks_f : se.brkStart = brkStart := hProc0_se.2.2.2.1.trans hbrks0
        rw [pure_sepConj_of_true ⟨alignedProcPreserved_trans hProc0_se (by subst hsf; proc_preserved_step),
              AlignedStage1.mappedDelta_of_perm_eq (by subst hsf; simpa [arm64_norm] using hPermAll)⟩,
          pure_sepConj_of_true ⟨by subst hsf; simp [arm64_norm], by subst hsf; simp [arm64_norm, htp_f],
            by subst hsf; simp [arm64_norm, hbrks_f],
            noOrphanMappings_refl_of_perm_eq (by subst hsf; simpa [arm64_norm] using hPermAll)⟩]
        cells_unfold; sep_frame
      · subst hsf; have _ := ha32; simp [arm64_norm]
      · subst hsf
        exact ⟨by simp [arm64_norm], by simp [arm64_norm],
          by simpa [arm64_norm] using hcs_e.readReg64_x21, by simpa [arm64_norm] using hcs_e.readReg64_x22,
          by simpa [arm64_norm] using hcs_e.readReg64_x23, by simpa [arm64_norm] using hcs_e.readReg64_x24,
          by simpa [arm64_norm] using hcs_e.readReg64_x25, by simpa [arm64_norm] using hcs_e.readReg64_x26,
          by simpa [arm64_norm] using hcs_e.readReg64_x27, by simpa [arm64_norm] using hcs_e.readReg64_x28,
          by simp [arm64_norm], by simpa [arm64_norm] using hcs_e.vregs⟩
    ·
      have hNoOvf : len.toNat + align.toNat < 2 ^ 64 := by
        refine Classical.byContradiction fun hNot => hOvfHi ?_
        have hCond := (ccmp_ovf_hi_iff (len := len) hAlignMax).trans (decide_eq_true (by omega))
        simpa [arm64_norm, hx0, hx1, hNegAnd] using hCond
      obtain ⟨RestEnv, hFocusRep⟩ := fineEnv_focus_replaced γ maddrs tp brkStart bud ivs0 s0
      have _hPageRep := pageOf_add_lo12Of maddrs.replaced
      conv => arg 4; rw [hFocusRep]
      wp_step; wp_step; wp_step
      · conv => arg 4; rw [← hFocusRep]
        wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
        have hpc_bl9 : b + 0x60#64 + (mbase 9 - mbase 12 - 0x60#64) = mbase 9 := by rw [hb]; bv_arith
        conv => arg 3; simp only [hpc_bl9]
        let eff := mallocngAlignedEffSize align.toNat len.toNat
        have ⟨_, hEffReg⟩ := alignedAlloc_effReg_toNat (align := align) (len := len) hNoOvf
        refine sepWP_let_state fun sc hsc => ?_
        have hsc_sp : sc.sp = s0.sp - 32#64 := by subst hsc; simp [arm64_norm]
        have hsc_brk : sc.brk = s0.brk := by subst hsc; simp [arm64_norm]
        have hsc_mem : sc.mem = m2 := by subst hsc; simp [arm64_norm]
        have hsc_tp : sc.tpidrEl0 = tp := by subst hsc; simp [arm64_norm, htp0]
        have hsc_brks : sc.brkStart = brkStart := by subst hsc; simp [arm64_norm, hbrks0]
        have hsc_proc : MallocngProcPreserved s0 sc := by subst hsc; proc_preserved_step
        by_cases hEffFit : eff ≤ MallocngMaxAllocSize
        ·
          have hOkTrue : mallocngAlignedAllocOk align len = true := by
            simp [mallocngAlignedAllocOk, hAlignOk, eff, hEffFit]
          have hStepResEq : fineStepReserve (.alloc eff) bud =
              fineStepReserve (.aligned align.toNat len.toNat) bud :=
            fineStepReserve_aligned_eq align.toNat len.toNat bud
          have hMallocSub := call_placed_libcMallocImpl_fine_raw hImplRaw
            (P := blkPC_b12.rebase b (fun _ => none))
            γ tp brkStart bud ivs0 eff (externAt?_placedProgram_rebase_none _ _ _ _) rfl
          refine SepWP.call_subroutine_frame (F := AlignedSpillSlots s0.sp s0) (x := ())
            (ret_pc := b + 0x64#64) hMallocSub (by subst hsc; simp [arm64_norm])
            (by subst hsc; simp [arm64_norm, hrun])
            (by simpa [State.spAligned, hsc_sp] using hspAl32) (by subst hsc; simp [arm64_norm])
            (fun R' hm => by
              refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
              dsimp only [libcMallocImplFineRawSpec, withCL, stackFrame, AlignedSpillSlots, FineEnv]
              simp only [hsc_sp, hsc_brk, hsc_mem, ← stackFrameAt_eq_memRegion (s0.sp - 32#64) 704, sepConj_assoc]
              rw [pure_sepConj_of_true ⟨htp0, hbrks0⟩,
                  pure_sepConj_of_true (by subst hsc; simpa [arm64_norm, hx0, hx1] using hEffReg),
                  pure_sepConj_of_true ⟨hsc_tp, hsc_brks⟩,
                  pure_sepConj_of_true hcl2]
              sep_frame)
            (fun _ _ _ hp => not_satisfies_false_sepConj hp)
            (fun _ _ _ _ he => not_satisfies_false_sepConj he)
            (fun sm hpc_m hrun_m hsp_m hcs_m => ?_)
            (fun R' soom _ ho => by
              refine Satisfies.mono (sepConj_mono_left (Entails.pure_mono fun hOom => ?_)) (Satisfies.drop_mid ho)
              simp only [eff, hEffFit, decide_true, ↓reduceIte] at hOom
              simp only [hOkTrue, ↓reduceIte]
              rw [← hStepResEq]
              subst hsc
              exact EntryHelpers.fineOomCond_of_pre_perm (by simp [arm64_norm]) (by simp [arm64_norm])
                (by simp [arm64_norm]) (by simp only [arm64_norm]; exact hm2.trans hm1) hOom)
          dsimp only [libcMallocImplFineRawSpec, withCL, stackFrame] at *
          rw [hsc_sp, hsc_mem, ← stackFrameAt_eq_memRegion (s0.sp - 32#64) 704]
          simp only [eff, hEffFit, decide_true, ↓reduceIte]
          have hsp_sm : sm.sp = s0.sp - 32#64 := hsp_m.trans hsc_sp
          have hx19_sm : sm.readReg64 .x19 =
              if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64 := by
            simpa [hsc, arm64_norm, hx0] using hcs_m.readReg64_x19
          have hx20_sm : sm.readReg64 .x20 = len := by simpa [hsc, arm64_norm, hx1] using hcs_m.readReg64_x20
          have hcs21_sm : CalleeSaved21_28 s0 sm :=
            ⟨by simpa [hsc, arm64_norm] using hcs_m.readReg64_x21, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x22,
             by simpa [hsc, arm64_norm] using hcs_m.readReg64_x23, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x24,
             by simpa [hsc, arm64_norm] using hcs_m.readReg64_x25, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x26,
             by simpa [hsc, arm64_norm] using hcs_m.readReg64_x27, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x28,
             by simpa [hsc, arm64_norm] using hcs_m.vregs⟩
          conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWP.exists_elim; intro p
          apply SepWP.exists_elim; intro bs
          apply SepWP.exists_elim; intro st0
          apply SepWP.exists_elim; intro alignMap0
          apply SepWP.exists_elim; intro st'
          apply SepWP.exists_elim; intro g'
          apply SepWP.exists_elim; intro idx
          apply SepWP.exists_elim; intro bCoarse
          refine SepWP.weaken_pre (P' :=
            ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
            ⌜MallocngProcPreserved sc sm ∧
              MallocngMappedDelta 16 (fineStepReserve (.alloc eff) bud) m2 sm.mem⌝ ∗
            ⌜sm.readReg64 .x0 = p ∧ sm.tpidrEl0 = tp ∧ sm.brkStart = brkStart ∧
              MallocngBlockWf p eff ∧ bs.length = eff ∧
              MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') m2 sm.mem ∧
              MallocngWF maddrs.base brkStart sm.brk bCoarse.liveCost bCoarse.peakCost st' ∧
              MallocngCountIvsWF bCoarse (dynamicRootRegions st') st' ∧
              MallocImplFineRawRel maddrs.base brkStart bud ivs0 alignMap0 st0 st' g' idx eff p ∧
              (g'.isMmapped = true → bs = List.replicate eff 0#8)⌝ ∗
            (MallocngRoTablesA maddrs ∗
             ghostMapAuth (fineAlignGam γ) alignMap0 ∗
             MallocngCoreStA (fineBaseGam γ) maddrs brkStart sm.brk bCoarse.liveCost bCoarse.peakCost st' ∗
             MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ MallocngBlockToken (fineBaseGam γ) p eff ∗
             stackFrameAt (s0.sp - 32#64) 704 ∗ AlignedSpillSlots s0.sp s0))
            (by dsimp only [eff]; exact Entails.of_eq (by ac_rfl)) ?_
          refine sepWP_pure_left fun hcl_sm => sepWP_pure_left fun ⟨hproc_sm, hmd_sm⟩ =>
            sepWP_pure_left fun ⟨hx0_sm, _htp_sm, _hbrks_sm, hBlkP, hBsLen,
              hNoOrph_sm, hwf', _hCnt', hRaw, _⟩ => ?_
          have ⟨_, _, _, _, hg', ⟨hIdx, hSlot⟩, _, _, _, _⟩ := hRaw
          wp_step
          wp_if hpZero
          · exfalso; exact hBlkP.1 (by simpa [arm64_norm, hx0_sm] using hpZero)
          ·
            let RestGM :=
              ghostMapAuth (fineAlignGam γ) alignMap0 ∗
              MallocngLiveAuth (fineBaseGam γ) st'.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
              (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
              ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState (fineBaseGam γ) st'.auxvPtr st'.auxvSnap ∗
              ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
              MappedSet st'.masterDom (OwnedMappedByte st') ∗
              MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ MallocngBlockToken (fineBaseGam γ) p eff ∗
              stackFrameAt (s0.sp - 32#64) 704 ∗ AlignedSpillSlots s0.sp s0
            have hToGM :
                (MallocngRoTablesA maddrs ∗
                  ghostMapAuth (fineAlignGam γ) alignMap0 ∗
                  MallocngCoreStA (fineBaseGam γ) maddrs brkStart sm.brk bCoarse.liveCost bCoarse.peakCost st' ∗
                  MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ MallocngBlockToken (fineBaseGam γ) p eff ∗
                  stackFrameAt (s0.sp - 32#64) 704 ∗ AlignedSpillSlots s0.sp s0) ⊢
                alignedGetMetaPre maddrs st' RestGM := by
              dsimp only [alignedGetMetaPre, MallocngRoTablesA, MallocngCoreStA, MallocngCoreStInflightA, RestGM]
              rw [pure_sepConj_of_true hwf']; sep_frame
            refine SepWP.weaken_pre hToGM ?_
            have hF := liveUserBlockFacts_of hwf' hg' hIdx hSlot
            refine SepWP.seq (alignedAlloc_getMeta_getStride_ok (Rest := RestGM) hb hprog_b12 hF
              (by simp [arm64_norm]) (by simp [arm64_norm, hrun_m]) (by simp [arm64_norm, hx0_sm])) ?_
            rintro s4 P4 hpc4 hrun4 hPost4
            obtain ⟨⟨⟨hm4, hbrk4, hproc4, hsp4, _, _, hcs4⟩, hx0_4, hx2_4, hx4_4, hx6_4⟩, hEnt4⟩ := hPost4
            refine SepWP.weaken_pre hEnt4 ?_
            have hFromGM : alignedGetMetaPre maddrs st' RestGM ⊢
                (ghostMapAuth (fineAlignGam γ) alignMap0 ∗ MallocngRoTablesA maddrs ∗
                  MallocngCoreStA (fineBaseGam γ) maddrs brkStart s4.brk bCoarse.liveCost bCoarse.peakCost st' ∗
                  MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ MallocngBlockToken (fineBaseGam γ) p eff ∗
                  stackFrameAt (s0.sp - 32#64) 704 ∗ AlignedSpillSlots s0.sp s0) := by
              have hbrk_eq : s4.brk = sm.brk := hbrk4
              rw [hbrk_eq]
              dsimp only [alignedGetMetaPre, MallocngRoTablesA, MallocngCoreStA, MallocngCoreStInflightA, RestGM]
              rw [pure_sepConj_of_true hwf']; sep_frame
            refine SepWP.weaken_pre hFromGM ?_
            have hcl4 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem := by
              simpa [hm4] using hcl_sm
            have hx19_4 : s4.readReg64 .x19 =
                if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64 := by
              calc s4.readReg64 .x19 = _ := hcs4.1
                _ = sm.readReg64 .x19 := by simp [arm64_norm]
                _ = _ := hx19_sm
            have hx20_4 : s4.readReg64 .x20 = len := by
              calc s4.readReg64 .x20 = _ := hcs4.2.1
                _ = sm.readReg64 .x20 := by simp [arm64_norm]
                _ = len := hx20_sm
            have hcs21_4 : CalleeSaved21_28 s0 s4 :=
              ⟨hcs4.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.1),
               hcs4.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.1),
               hcs4.2.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.2.1),
               hcs4.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.2.2.1),
               hcs4.2.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.2.2.2.1),
               hcs4.2.2.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.2.2.2.2.1),
               hcs4.2.2.2.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.2.2.2.2.2.1),
               hcs4.2.2.2.2.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.2.2.2.2.2.2.1),
               hcs4.2.2.2.2.2.2.2.2.2.2.2.trans (by simpa [arm64_norm] using hcs21_sm.2.2.2.2.2.2.2.2)⟩
            have hsp4_eq : s4.sp = s0.sp - 32#64 := hsp4.trans (by simpa [arm64_norm] using hsp_sm)
            have hwf4 : MallocngWF maddrs.base brkStart s4.brk bCoarse.liveCost bCoarse.peakCost st' := by
              rwa [hbrk4]
            refine SepWP.mono
              (alignedAlloc_reframe_fine_ok (tp := tp) hb hprog_b12 γ hwf4 hRaw hBsLen
                hAlignOk hAlignMax hNoOvf hpc4 hrun4 hcl4 hsp4_eq rfl hspAl0
                hx0_4 hx2_4 hx4_4 hx6_4 hx19_4 hx20_4 hcs21_4) ?_
            rintro sf Pf _hpc_f _hrun_f ⟨⟨new_p, hx0_f, hPureWf, hEntF⟩, _hcl_f, hperm_f, _hbrk_f, hproc_f, hsp_f, hcs_f⟩
            refine ⟨fun hmF => ?_, hsp_f, hcs_f⟩
            refine Satisfies.mono (sepConj_mono_left (Entails.trans hEntF ?_)) hmF
            simp only [hOkTrue, ↓reduceIte]
            have hPerm4_sm : s4.mem.perm = sm.mem.perm := congrArg Memory.perm hm4
            have hPermF_sm : sf.mem.perm = sm.mem.perm := hperm_f.trans hPerm4_sm
            have hPerm2_0 : m2.perm = s0.mem.perm := hm2.trans hm1
            have hProc0_sm : MallocngProcPreserved s0 sm := alignedProcPreserved_trans hsc_proc hproc_sm
            have hProc_sm_4 : MallocngProcPreserved sm s4 := alignedProcPreserved_trans (by proc_preserved_step) hproc4
            have hProcAll : MallocngProcPreserved s0 sf :=
              alignedProcPreserved_trans hProc0_sm (alignedProcPreserved_trans hProc_sm_4 hproc_f)
            have hAcct : MallocngCallAccounting 16 (fineStepReserve (.aligned align.toNat len.toNat) bud) s0 sf := by
              rw [← hStepResEq]
              exact ⟨hProcAll, mappedDelta_congr_perm hPerm2_0 hmd_sm hPermF_sm⟩
            have hNoOrphAll : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem :=
              noOrphanMappings_congr_perm hPerm2_0 hNoOrph_sm hPermF_sm
            have htp_f : sf.tpidrEl0 = tp := hProcAll.2.2.1.trans htp0
            have hbrks_f : sf.brkStart = brkStart := hProcAll.2.2.2.1.trans hbrks0
            rw [pure_sepConj_of_true hAcct, stackFrameAt_736_split s0.sp]
            refine Entails.trans ?_ (sepConj_mono_right (Entails.sepExists_intro new_p))
            rw [pure_sepConj_of_true ⟨hx0_f, hPureWf⟩]
            let bf := FineBudget.stepAligned align.toNat len.toNat bud
            have hPostEnv :
                (FineCoreImpl γ maddrs brkStart sf.brk bf (dynamicRootRegions st') ∗
                 MallocngRuntime maddrs tp) ⊢
                FinePostEnv γ maddrs tp brkStart (FineBudget.step (.aligned align.toNat len.toNat) bud) ivs0 s0 sf := by
              dsimp only [FinePostEnv, FineEnv, FineBudget.step, bf]
              refine Entails.trans ?_ (Entails.sepExists_intro (dynamicRootRegions st'))
              rw [FineHeapImpl_eq, pure_sepConj_of_true hNoOrphAll, pure_sepConj_of_true ⟨htp_f, hbrks_f⟩]
              sep_frame
            exact Entails.trans (by sep_frame) (sepConj_mono_right (sepConj_mono_left hPostEnv))
        ·
          have hEffGt : MallocngMaxAllocSize < eff := by omega
          have hOkFalse : mallocngAlignedAllocOk align len = false := by
            simp [mallocngAlignedAllocOk, eff, hEffFit]
          let sp1 := s0.sp - 32#64
          conv => arg 4; dsimp only [FineEnv]
          conv => arg 4; rw [FineHeapImpl_eq, pure_sepConj_of_true ⟨htp0, hbrks0⟩, stackFrameAt_704_split_80 sp1]
          conv => arg 4; dsimp only [MallocngRuntime]
          cells_unfold_pre
          apply SepWP.exists_elim; intro ev
          apply SepWP.exists_elim; intro u0; apply SepWP.exists_elim; intro u1
          let Rest3 :=
            stackFrameAt (sp1 - 80#64) 624 ∗ stackFrameAt sp1 64 ∗ AlignedSpillSlots s0.sp s0 ∗
            FineCoreImpl γ maddrs brkStart s0.brk bud ivs0 ∗
            ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
          have hOvfSub := placed_libcMallocImpl_overflow_errno_ok
            (P := blkPC_b12.rebase b (fun _ => none)) (externAt?_placedProgram_rebase_none _ _ _ _) rfl
          refine SepWP.call_subroutine_frame (F := Rest3) (x := (tp, u0, u1, ev))
            (ret_pc := b + 0x64#64) hOvfSub (by subst hsc; simp [arm64_norm])
            (by subst hsc; simp [arm64_norm, hrun])
            (by simpa [State.spAligned, hsc_sp] using hspAl32) (by subst hsc; simp [arm64_norm])
            (fun R' hm => by
              refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
              dsimp only [withCL, Rest3, AlignedSpillSlots, sp1]
              simp only [hsc_sp, hsc_mem, sepConj_assoc]
              rw [pure_sepConj_of_true hcl2,
                  pure_sepConj_of_true ⟨hsc_tp, by
                    have hEq : (sc.readReg64 .x0).toNat = eff := by subst hsc; simpa [arm64_norm, hx0, hx1] using hEffReg
                    omega⟩]
              sep_frame)
            (fun _ _ _ hp => not_satisfies_false_sepConj hp)
            (fun _ _ _ _ he => not_satisfies_false_sepConj he)
            (fun sm hpc_m hrun_m hsp_m hcs_m => ?_)
            (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
          dsimp only [withCL] at *
          rw [hsc_sp, hsc_brk, hsc_mem, show s0.sp - 32#64 = sp1 from rfl]
          have hsp_sm : sm.sp = sp1 := hsp_m.trans hsc_sp
          conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWP.exists_elim; intro w0'; apply SepWP.exists_elim; intro w1'
          refine SepWP.weaken_pre (P' :=
            ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
            ⌜MallocngProcPreserved sc sm ∧ sm.brk = s0.brk ∧ sm.mem.perm = m2.perm ∧ sm.readReg64 .x0 = 0#64⌝ ∗
            (((sp1 - 80#64) ↦₆₄ w0') ∗ ((sp1 - 72#64) ↦₆₄ w1') ∗ ((tp - 0xa4#64) ↦₃₂ 12#32) ∗ Rest3))
            (Entails.of_eq (by ac_rfl)) ?_
          refine sepWP_pure_left fun _hcl_sm => sepWP_pure_left fun ⟨hproc_sm, hbrk_sm, hperm_sm, hx0_sm⟩ => ?_
          wp_step
          conv => arg 4; dsimp only [Rest3, AlignedSpillSlots]
          have _hspAl_sm : (sm.sp &&& 15#64 == 0#64) = true := by rw [hsp_sm]; exact hspAl32
          have ha16_sm : sm.sp + 16#64 = s0.sp - 16#64 := by rw [hsp_sm]; dsimp only [sp1]; bv_arith
          have ha24_sm : sm.sp + 16#64 + 8#64 = s0.sp - 8#64 := by rw [hsp_sm]; dsimp only [sp1]; bv_arith
          have ha8_sm : sm.sp + 8#64 = s0.sp - 24#64 := by rw [hsp_sm]; dsimp only [sp1]; bv_arith
          have ha32_sm : sm.sp + 32#64 = s0.sp := by rw [hsp_sm]; dsimp only [sp1]; bv_arith
          wp_step; wp_step; wp_step; wp_step
          have hPermAll : sm.mem.perm = s0.mem.perm := hperm_sm.trans (hm2.trans hm1)
          have hProc0_sm : MallocngProcPreserved s0 sm := alignedProcPreserved_trans hsc_proc hproc_sm
          refine sepWP_let_state fun sf hsf => ?_
          have hbrk_f : sf.brk = s0.brk := by subst hsf; simp [arm64_norm, hbrk_sm]
          refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun_m]) ⟨fun hm => ?_, ?_, ?_⟩
          · refine Satisfies.mono (sepConj_mono_left ?_) hm
            simp only [hOkFalse, Bool.false_eq_true, ↓reduceIte, hAlignOk, Bool.not_true, hbrk_f]
            have htp_f : sm.tpidrEl0 = tp := hProc0_sm.2.2.1.trans htp0
            have hbrks_f : sm.brkStart = brkStart := hProc0_sm.2.2.2.1.trans hbrks0
            rw [pure_sepConj_of_true ⟨alignedProcPreserved_trans hProc0_sm (by subst hsf; proc_preserved_step),
                  AlignedStage1.mappedDelta_of_perm_eq (by subst hsf; simpa [arm64_norm] using hPermAll)⟩,
              stackFrameAt_704_split_80 sp1,
              pure_sepConj_of_true ⟨by subst hsf; simp [arm64_norm, hx0_sm], by subst hsf; simp [arm64_norm, htp_f],
                by subst hsf; simp [arm64_norm, hbrks_f],
                noOrphanMappings_refl_of_perm_eq (by subst hsf; simpa [arm64_norm] using hPermAll)⟩]
            dsimp only [sp1]; cells_unfold; sep_frame
          · subst hsf; have _ := ha32_sm; simp [arm64_norm]
          · subst hsf
            exact ⟨by simp [arm64_norm], by simp [arm64_norm],
              by simpa [hsc, arm64_norm] using hcs_m.readReg64_x21, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x22,
              by simpa [hsc, arm64_norm] using hcs_m.readReg64_x23, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x24,
              by simpa [hsc, arm64_norm] using hcs_m.readReg64_x25, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x26,
              by simpa [hsc, arm64_norm] using hcs_m.readReg64_x27, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x28,
              by simp [arm64_norm], by simpa [hsc, arm64_norm] using hcs_m.vregs⟩

/-- Cross-block subroutine correctness for `alignedAllocFineErrnoSpec`. -/
theorem placed_alignedAlloc_fine_errno_ok (hImplRaw : LibcMallocImplFineRawStmt)
    [MallocngMultiPlacement] {P : Program}
    (γ : GhostName) (tp brkStart align len : BitVec 64)
    (b : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 12) (alignedAllocFineErrnoSpec γ tp brkStart align len b ivs0) :=
  subroutine_ok_block_to_block (j := 12) (by decide)
    (blk12_alignedAlloc_fine_errno hImplRaw γ tp brkStart align len b ivs0) hext hsvc

/-! ## Placed `aligned_alloc` Entrypoint -/

private theorem blk12_alignedAlloc_fine (hImplRaw : LibcMallocImplFineRawStmt)
    [MallocngMultiPlacement] (γ : GhostName) :
    subroutine_ok (mallocngBlockProg mmpl 12 msvc) (mbase 12)
      (withCL mmpl (ToBaseSpec.toSpec (fineAlignedAllocSpec msvc γ maddrs) (mbase 12))) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨align, len, sp0, tp, brkStart, bud, ivs0⟩ R s0 hpc hrun hpre hspAl0
  dsimp only [ToBaseSpec.toSpec, fineAlignedAllocSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨rfl, ⟨hx0, hx1, hsp_eq, _, _, hCaveat⟩, hpre⟩ := hpre
  rw [← sepConj_assoc] at hpre
  refine ⟨_, hpre, ?_⟩
  have hSplit1024 : stackFrameAt s0.sp mallocngStackBytes =
      (stackFrameAt (s0.sp - 736#64) 288 ∗ stackFrame s0 736) := by
    rw [stackFrame_eq_stackFrameAt s0 736]
    change stackFrameAt s0.sp 1024 = (stackFrameAt (s0.sp - 736#64) 288 ∗ stackFrameAt s0.sp 736)
    rw [stackFrameAt_split s0.sp 736 288]; ac_rfl
  rw [← hsp_eq, hSplit1024]
  have hSub := blk12_alignedAlloc_fine_errno hImplRaw γ tp brkStart align len bud ivs0
  refine SepWP.call_subroutine_frame (F := stackFrameAt (s0.sp - 736#64) 288) (x := ())
    (ret_pc := s0.readReg64 .x30) hSub hpc hrun hspAl0 rfl
    (fun R' hm => by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
      dsimp only [alignedAllocFineErrnoSpec, withCL]
      rw [sepConj_assoc, pure_sepConj_of_true hcl0, pure_sepConj_of_true ⟨hx0, hx1, hCaveat⟩]
      sep_frame)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun R' soom _ ho => Satisfies.drop_mid ho)
  dsimp only [alignedAllocFineErrnoSpec, withCL] at *
  by_cases hOk : mallocngAlignedAllocOk align len = true
  · simp only [hOk, ↓reduceIte]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro q
    refine SepWP.weaken_pre (P' :=
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
      ⌜MallocngCallAccounting 16 (fineStepReserve (.aligned align.toNat len.toNat) bud) s0 sf⌝ ∗
      ⌜sf.readReg64 .x0 = q ∧ q ≠ 0#64 ∧ max align.toNat 16 ∣ q.toNat ∧ q.toNat + len.toNat < 2 ^ 64⌝ ∗
      (FinePostEnv γ maddrs tp brkStart (FineBudget.step (.aligned align.toNat len.toNat) bud) ivs0 s0 sf ∗
       (FineBlockSem γ).interp q (len.toNat, max align.toNat 16) ∗
       stackFrame s0 736 ∗ stackFrameAt (s0.sp - 736#64) 288))
      (by dsimp only [FineBlockSem]; exact Entails.of_eq (by ac_rfl)) ?_
    refine sepWP_pure_left fun _hcl_f => sepWP_pure_left fun hAcct =>
      sepWP_pure_left fun ⟨hq, hqNe, hqDvd, hqBound⟩ => ?_
    have hPureQ : (FineBlockSem γ).pureWf q (len.toNat, max align.toNat 16) :=
      ⟨hqNe, hqDvd, hqBound⟩
    refine SepWP.done hpc_f hrun_f ⟨fun hmF => ?_, hsp_f, hcs_f⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hmF
    simp only [OptOwn_pureWf_some, OptOwn_interp_some]
    rw [hq, pure_sepConj_of_true ⟨⟨hqNe, hPureQ⟩, hAcct⟩]
    sep_frame
  · have hOkF : mallocngAlignedAllocOk align len = false := Bool.eq_false_iff.mpr hOk
    simp only [hOkF, Bool.false_eq_true, ↓reduceIte]
    refine SepWP.weaken_pre (P' :=
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
      ⌜MallocngCallAccounting 16 (fineStepReserve (.alloc 0) bud) s0 sf⌝ ∗
      ⌜sf.readReg64 .x0 = 0#64 ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
       MallocngNoOrphanMappings ivs0 ivs0 s0.mem sf.mem⌝ ∗
      (FineCoreImpl γ maddrs brkStart sf.brk bud ivs0 ∗
       (((tp - 0xa4#64) ↦₃₂ (if !alignedAllocAlignOk align then 22#32 else 12#32)) ∗
        ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ∗
       stackFrame s0 736 ∗ stackFrameAt (s0.sp - 736#64) 288)) (Entails.of_eq (by ac_rfl)) ?_
    refine sepWP_pure_left fun _hcl_f => sepWP_pure_left fun hAcct =>
      sepWP_pure_left fun ⟨hx0_f, htp_f, hbrks_f, hNoOrph⟩ => ?_
    refine SepWP.done hpc_f hrun_f ⟨fun hmF => ?_, hsp_f, hcs_f⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hmF
    rw [hx0_f]
    simp only [OptOwn_pureWf_none, OptOwn_interp_none]
    rw [pure_sepConj_of_true ⟨True.intro, hAcct⟩, pure_sepConj_of_true True.intro]
    have hRt :
        (((tp - 0xa4#64) ↦₃₂ (if !alignedAllocAlignOk align then 22#32 else 12#32)) ∗
         ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ⊢
        MallocngRuntime maddrs tp := by
      dsimp only [MallocngRuntime]
      simp only [sepExists_sepConj_left]
      refine Entails.trans ?_ (Entails.sepExists_intro (if !alignedAllocAlignOk align then 22#32 else 12#32))
      sep_frame
    have hPostEnv0 :
        (FineCoreImpl γ maddrs brkStart sf.brk bud ivs0 ∗
         MallocngRuntime maddrs tp) ⊢
        FinePostEnv γ maddrs tp brkStart bud ivs0 s0 sf := by
      dsimp only [FinePostEnv, FineEnv]
      refine Entails.trans ?_ (Entails.sepExists_intro ivs0)
      rw [FineHeapImpl_eq, pure_sepConj_of_true hNoOrph, pure_sepConj_of_true ⟨htp_f, hbrks_f⟩]
      sep_frame
    exact Entails.trans (by sep_frame) (sepConj_mono_left (Entails.trans (sepConj_mono_right hRt) hPostEnv0))

/-- Placed fine-model entrypoint contract for `"aligned_alloc"` (`blk12`). -/
theorem placed_alignedAlloc_fine_entry_ok (hImplRaw : LibcMallocImplFineRawStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "aligned_alloc"
      (fineAlignedAllocSpec svc γ (mallocngAddrsOfPlacement mpl)) := by
  let _ : MallocngMultiPlacement := ⟨mpl, svc, hPlace, hSvc⟩
  refine ⟨by decide +kernel, 12, 0, by decide +kernel, ?_⟩
  rw [fnAddr_aligned_alloc]
  exact withCL_to_withCodeLoaded (blk12_alignedAlloc_fine hImplRaw γ)

/-! ## Placed `posix_memalign` Entrypoint -/

private theorem posixRet_of_ge8_ok {align len : BitVec 64} (hGe8 : 8 ≤ align.toNat)
    (hOk : mallocngAlignedAllocOk align len = true) :
    mallocngPosixMemalignRet align len = 0#32 := by
  have ⟨hAl, hFit⟩ : alignedAllocAlignOk align = true ∧
      mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize := by
    simpa [mallocngAlignedAllocOk] using hOk
  have hPow2 : isPow2Align align = true := by rwa [← alignOk_eq_isPow2_of_ge8 hGe8]
  have hNotLt : ¬ align.toNat < 8 := by omega
  simp [mallocngPosixMemalignRet, hNotLt, hPow2, hFit]

private theorem posixRet_of_ge8_fail {align len : BitVec 64} (hGe8 : 8 ≤ align.toNat)
    (hFail : mallocngAlignedAllocOk align len = false) :
    (if !alignedAllocAlignOk align then 22#32 else 12#32) =
      mallocngPosixMemalignRet align len := by
  have hNotLt : ¬ align.toNat < 8 := by omega
  have hEqPow := alignOk_eq_isPow2_of_ge8 hGe8
  cases hAl : alignedAllocAlignOk align
  · have hPowF : isPow2Align align = false := by rw [← hEqPow]; exact hAl
    simp [mallocngPosixMemalignRet, hNotLt, hPowF]
  · have hPowT : isPow2Align align = true := by rw [← hEqPow]; exact hAl
    have hNotFit : ¬ mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize := by
      intro hFit; simp [mallocngAlignedAllocOk, hAl, hFit] at hFail
    simp [mallocngPosixMemalignRet, hNotLt, hPowT, hNotFit]

private theorem stackFrameAt_1024_split_pm (sp0 : BitVec 64) :
    stackFrameAt sp0 mallocngStackBytes =
      (stackFrameAt (sp0 - 32#64 - 736#64) 256 ∗
       stackFrameAt (sp0 - 32#64) 736 ∗
       cells (sp0 - 32#64) 4) := by
  change stackFrameAt sp0 1024 = _
  rw [stackFrameAt_split sp0 32 992, stackFrameAt_split (sp0 - 32#64) 736 256,
    stackFrameAt_eq_memRegion sp0 32, memRegion_cells (sp0 - 32#64) 4 (by decide)]
  ac_rfl

set_option maxHeartbeats 400000 in
private theorem blk11_posixMemalign_fine (hImplRaw : LibcMallocImplFineRawStmt)
    [MallocngMultiPlacement] (γ : GhostName) :
    subroutine_ok (mallocngBlockProg mmpl 11 msvc) (mbase 11)
      (withCL mmpl (ToBaseSpec.toSpec (finePosixMemalignSpec msvc γ maddrs) (mbase 11))) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have hfn : ∀ c, (blkPC_b11.rebase c (fun _ => none)).fnAddr "posix_memalign" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase, Program.fnOff, Program.findSymbol?, blkPC_b11, PlacedLib.program]
    rw [blkSymsEq_b11]
    have hf : (toStringSymbols blkSymChars_b11).find? (·.1 == "posix_memalign") =
        some ("posix_memalign", 0) := by decide
    rw [hf]; exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b11 (hfn (mbase 11)) fun b hb => ?_
  have _ := hb
  rw [hfn b]
  have herr := placed_errnoLocation_perm_ok (P := blkPC_b11.rebase b (fun _ => none))
    (externAt?_placedProgram_rebase_none _ _ _ _) rfl
  apply subroutine_ok_of_sepWP_init
  rintro ⟨res, align, len, sp0, tp, brkStart, bud, ivs0⟩ R s0 hpc hrun hpre hspAl0
  dsimp only [ToBaseSpec.toSpec, finePosixMemalignSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨rfl, ⟨hx0, hx1, hx2, hsp_eq, _, _, _, hCaveat⟩, hpre⟩ := hpre
  subst hsp_eq
  change s0.readReg64 (.gpr 0#5) = res at hx0
  change s0.readReg64 (.gpr 1#5) = align at hx1
  change s0.readReg64 (.gpr 2#5) = len at hx2
  have ⟨htp0, hbrks0⟩ : s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart := by
    have hm0 : s0.mem ⊨ ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
        ((OptOutPtr (FineBlockSem γ)).interp res none ∗
         FineHeapImpl γ maddrs tp brkStart s0.brk bud ivs0 ∗
         stackFrameAt s0.sp mallocngStackBytes ∗ R) := by
      dsimp only [FineEnv] at hpre
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hm0; exact hm0.1
  refine ⟨(OptOutPtr (FineBlockSem γ)).interp res none ∗
    FineEnv γ maddrs tp brkStart bud ivs0 s0 ∗
    stackFrameAt s0.sp mallocngStackBytes, by simpa [sepConj_assoc] using hpre, ?_⟩
  wp_step; wp_step
  wp_if hLs7
  ·
    have hLt8 : align.toNat < 8 := by
      have hUle : align.ule 7#64 = true := by simpa [arm64_norm, hx1] using hLs7
      rw [BitVec.ule, decide_eq_true_eq] at hUle
      change align.toNat ≤ 7 at hUle; omega
    have hPmOkF : mallocngPosixMemalignOk align len = false := by
      simp [mallocngPosixMemalignOk, show ¬ 8 ≤ align.toNat by omega]
    have hRetEq : (22#32 : BitVec 32) = mallocngPosixMemalignRet align len := by
      simp [mallocngPosixMemalignRet, hLt8]
    wp_step; wp_step
    refine sepWP_let_state fun sf hsf => ?_
    have hbrk_f : sf.brk = s0.brk := by subst hsf; simp [arm64_norm]
    refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun]) ⟨fun hm => ?_, ?_, ?_⟩
    · refine Satisfies.mono (sepConj_mono_left ?_) hm
      simp only [hPmOkF, Bool.false_eq_true, ↓reduceIte, OptOutPtr_pureWf]
      rw [pure_sepConj_of_true ⟨True.intro, by subst hsf; simpa [arm64_norm] using hRetEq,
            ⟨by subst hsf; proc_preserved_step, AlignedStage1.mappedDelta_of_perm_eq (by subst hsf; simp [arm64_norm])⟩⟩]
      have hEnvToPost :
          FineEnv γ maddrs tp brkStart bud ivs0 s0 ⊢
          FinePostEnv γ maddrs tp brkStart bud ivs0 s0 sf := by
        dsimp only [FinePostEnv, FineEnv]
        refine Entails.trans ?_ (Entails.sepExists_intro ivs0)
        rw [pure_sepConj_of_true (noOrphanMappings_refl_of_perm_eq (by subst hsf; simp [arm64_norm])),
          pure_sepConj_of_true ⟨htp0, hbrks0⟩, pure_sepConj_of_true ⟨by subst hsf; simp [arm64_norm, htp0],
            by subst hsf; simp [arm64_norm, hbrks0]⟩, hbrk_f]
        sep_frame
      exact Entails.trans (by sep_frame) (sepConj_mono_right (sepConj_mono_left hEnvToPost))
    · subst hsf; simp [arm64_norm]
    · subst hsf
      exact ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
        by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
        by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  ·
    have hGe8 : 8 ≤ align.toNat := by
      have hNotUle : align.ule 7#64 = false := by
        cases hb7 : align.ule 7#64
        · rfl
        · exfalso; simp [arm64_norm, hb7] at hLs7
      rw [BitVec.ule, decide_eq_false_iff_not] at hNotUle
      change ¬ align.toNat ≤ 7 at hNotUle; omega
    have hPmEqAa : mallocngPosixMemalignOk align len = mallocngAlignedAllocOk align len := by
      simp [mallocngPosixMemalignOk, hGe8]
    conv => arg 4; rw [stackFrameAt_1024_split_pm s0.sp]
    cells_unfold_pre
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    let sp1 := s0.sp - 32#64
    have ha16_sp : sp1 + 16#64 = s0.sp - 16#64 := by dsimp only [sp1]; bv_arith
    have ha8_sp : sp1 + 8#64 = s0.sp - 24#64 := by dsimp only [sp1]; bv_arith
    have ha32_sp : sp1 + 32#64 = s0.sp := by dsimp only [sp1]; bv_arith
    have hspAl32 : (sp1 &&& 15#64 == 0#64) = true := s0.spAligned_sub 32#64 hspAl0
    wp_stp64_cl m1 hm1 hcl0 hcl1
    wp_step; wp_step; wp_step
    wp_str64_cl m2 hm2 hcl1 hcl2
    wp_step; wp_step; wp_step
    have hpc_bl12 : b + 0x24#64 + (mbase 12 - mbase 11 - 0x24#64) = mbase 12 := by rw [hb]; bv_arith
    conv => arg 3; simp only [hpc_bl12]
    refine sepWP_let_state fun sc hsc => ?_
    have hsc_sp : sc.sp = sp1 := by subst hsc; simp [arm64_norm, sp1]
    have hsc_sf736 : stackFrame sc 736 = stackFrameAt sp1 736 := by
      unfold stackFrame; rw [hsc_sp, ← stackFrameAt_eq_memRegion sp1 736]
    have hsc_brk : sc.brk = s0.brk := by subst hsc; simp [arm64_norm]
    have hsc_mem : sc.mem = m2 := by subst hsc; simp [arm64_norm]
    have hsc_tp : sc.tpidrEl0 = tp := by subst hsc; simp [arm64_norm, htp0]
    have hsc_brks : sc.brkStart = brkStart := by subst hsc; simp [arm64_norm, hbrks0]
    have hsc_proc : MallocngProcPreserved s0 sc := by subst hsc; proc_preserved_step
    let FramePM :=
      memRegion res 8 ∗ stackFrameAt (sp1 - 736#64) 256 ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ w3)
    have hAaSub := placed_alignedAlloc_fine_errno_ok hImplRaw
      (P := blkPC_b11.rebase b (fun _ => none))
      γ tp brkStart align len bud ivs0 (externAt?_placedProgram_rebase_none _ _ _ _) rfl
    refine SepWP.call_subroutine_frame (F := FramePM) (x := ())
      (ret_pc := b + 0x28#64) hAaSub (by subst hsc; simp [arm64_norm]) (by subst hsc; simp [arm64_norm, hrun])
      (by simpa [State.spAligned, hsc_sp] using hspAl32) (by subst hsc; simp [arm64_norm])
      (fun R' hm => by
        refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
        dsimp only [alignedAllocFineErrnoSpec, withCL, FramePM, FineEnv, OptOutPtr]
        simp only [hsc_sf736, hsc_brk, hsc_mem, sepConj_assoc]
        rw [pure_sepConj_of_true ⟨htp0, hbrks0⟩,
            pure_sepConj_of_true ⟨by subst hsc; simp [arm64_norm], by subst hsc; simp [arm64_norm], hCaveat⟩,
            pure_sepConj_of_true ⟨hsc_tp, hsc_brks⟩,
            pure_sepConj_of_true hcl2]
        dsimp only [sp1]; sep_frame)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun sm hpc_m hrun_m hsp_m hcs_m => ?_)
      (fun R' soom _ ho => by
        refine Satisfies.mono (sepConj_mono_left (Entails.pure_mono fun hOom => ?_)) (Satisfies.drop_mid ho)
        rw [hPmEqAa]; subst hsc
        exact EntryHelpers.fineOomCond_of_pre_perm (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp only [arm64_norm]; exact hm2.trans hm1) hOom)
    dsimp only [alignedAllocFineErrnoSpec, withCL] at *
    rw [hsc_sf736]
    have hsp_sm : sm.sp = sp1 := hsp_m.trans hsc_sp
    have _hspAl_sm : (sm.sp &&& 15#64 == 0#64) = true := by rw [hsp_sm]; exact hspAl32
    have hx19_sm : sm.readReg64 (.gpr 19#5) = res :=
      hcs_m.readReg64_x19.trans (by subst hsc; simp [arm64_norm])
    have hPerm2_0 : m2.perm = s0.mem.perm := hm2.trans hm1
    by_cases hAaOk : mallocngAlignedAllocOk align len = true
    ·
      simp only [hAaOk, ↓reduceIte]
      have hPmOkT : mallocngPosixMemalignOk align len = true := hPmEqAa.trans hAaOk
      have hRet0 := posixRet_of_ge8_ok (len := len) hGe8 hAaOk
      let ev := FineEvent.aligned align.toNat len.toNat
      let bf := FineBudget.step ev bud
      conv => arg 4; dsimp only [FramePM]; rw [memRegion_eight res]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro oldRes
      apply SepWP.exists_elim; intro q
      refine SepWP.weaken_pre (P' :=
        ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
        ⌜MallocngCallAccounting 16 (fineStepReserve ev bud) sc sm⌝ ∗
        ⌜sm.readReg64 .x0 = q ∧ q ≠ 0#64 ∧ max align.toNat 16 ∣ q.toNat ∧ q.toNat + len.toNat < 2 ^ 64⌝ ∗
        ((res ↦₆₄ oldRes) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ w3) ∗
         stackFrameAt sp1 736 ∗ stackFrameAt (sp1 - 736#64) 256 ∗
         FinePostEnv γ maddrs tp brkStart bf ivs0 sc sm ∗
         (FineBlockSem γ).interp q (len.toNat, max align.toNat 16)))
        (by dsimp only [FineBlockSem, ev, bf]; exact Entails.of_eq (by ac_rfl)) ?_
      refine sepWP_pure_left fun hcl_sm => sepWP_pure_left fun ⟨hproc_sm, hmd_sm⟩ =>
        sepWP_pure_left fun ⟨hx0_sm, hqNe, hqDvd, hqBound⟩ => ?_
      have hPureQ : (FineBlockSem γ).pureWf q (len.toNat, max align.toNat 16) :=
        ⟨hqNe, hqDvd, hqBound⟩
      wp_step; wp_step
      wp_if hqZero
      · exfalso; exact hPureQ.1 (by simpa [arm64_norm, hx0_sm] using hqZero)
      · have ha16_sm : sm.sp + 16#64 = s0.sp - 16#64 := by rw [hsp_sm]; exact ha16_sp
        have ha8_sm : sm.sp + 8#64 = s0.sp - 24#64 := by rw [hsp_sm]; exact ha8_sp
        have ha32_sm : sm.sp + 32#64 = s0.sp := by rw [hsp_sm]; exact ha32_sp
        wp_step
        wp_str64_cl m3 hm3 hcl_sm _hcl3
        wp_step; wp_step; wp_step
        refine sepWP_let_state fun sf hsf => ?_
        have hPerm3_sm : sf.mem.perm = sm.mem.perm := by subst hsf; simpa [arm64_norm] using hm3
        have hbrk_f : sf.brk = sm.brk := by subst hsf; simp [arm64_norm]
        have hProcAll : MallocngProcPreserved s0 sf :=
          alignedProcPreserved_trans
            (alignedProcPreserved_trans hsc_proc hproc_sm)
            (by subst hsf; proc_preserved_step)
        have hAcctAll : MallocngCallAccounting 16 (fineStepReserve ev bud) s0 sf :=
          ⟨hProcAll, mappedDelta_congr_perm (hsc_mem ▸ hPerm2_0) hmd_sm hPerm3_sm⟩
        refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun_m]) ⟨fun hmF => ?_, ?_, ?_⟩
        · refine Satisfies.mono (sepConj_mono_left ?_) hmF
          simp only [hPmOkT, ↓reduceIte, OptOutPtr_interp_some, OptOutPtr_pureWf]
          rw [pure_sepConj_of_true ⟨True.intro, by subst hsf; simpa [arm64_norm] using hRet0.symm, hAcctAll⟩,
            stackFrameAt_1024_split_pm s0.sp]
          have hPostEnvCongr :
              FinePostEnv γ maddrs tp brkStart bf ivs0 sc sm ⊢
              FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf := by
            dsimp only [FinePostEnv, FineEnv]
            refine Entails.sepExists_elim fun ivsf => Entails.trans ?_ (Entails.sepExists_intro ivsf)
            refine Entails.pure_left fun hNoOrph => Entails.pure_left fun ⟨htp_sm, hbrks_sm⟩ => ?_
            rw [pure_sepConj_of_true (noOrphanMappings_congr_perm (hsc_mem ▸ hPerm2_0) hNoOrph hPerm3_sm),
              pure_sepConj_of_true ⟨by subst hsf; simp [arm64_norm, htp_sm], by subst hsf; simp [arm64_norm, hbrks_sm]⟩,
              hbrk_f]
            sep_frame
          have hOutPtr :
              ((res ↦₆₄ q) ∗ (FineBlockSem γ).interp q (len.toNat, max align.toNat 16)) ⊢
              outPtrPost (FineBlockSem γ) res (len.toNat, max align.toNat 16) := by
            rw [outPtrPost_def]
            refine Entails.trans ?_ (Entails.sepExists_intro q)
            rw [pure_sepConj_of_true hPureQ]; sep_frame
          dsimp only [sp1]; cells_unfold
          refine Entails.trans (Entails.of_eq (show _ =
              ((res ↦₆₄ q) ∗ (FineBlockSem γ).interp q (len.toNat, max align.toNat 16)) ∗
              FinePostEnv γ maddrs tp brkStart bf ivs0 sc sm ∗
              (((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
               ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
               ((s0.sp - 8#64) ↦₆₄ w3) ∗
               stackFrameAt (s0.sp - 32#64) 736 ∗ stackFrameAt (s0.sp - 32#64 - 736#64) 256) by
            dsimp only [FineBlockSem, bf]; ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hOutPtr)
            (Entails.trans (sepConj_mono_right (sepConj_mono_left hPostEnvCongr)) (by sep_frame))
        · subst hsf; have _ := ha32_sm; simp [arm64_norm]
        · subst hsf
          exact ⟨by simp [arm64_norm],
            by simpa [hsc, arm64_norm] using hcs_m.readReg64_x20, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x21,
            by simpa [hsc, arm64_norm] using hcs_m.readReg64_x22, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x23,
            by simpa [hsc, arm64_norm] using hcs_m.readReg64_x24, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x25,
            by simpa [hsc, arm64_norm] using hcs_m.readReg64_x26, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x27,
            by simpa [hsc, arm64_norm] using hcs_m.readReg64_x28,
            by simp [arm64_norm], by simpa [hsc, arm64_norm] using hcs_m.vregs⟩
    ·
      have hAaF : mallocngAlignedAllocOk align len = false := Bool.eq_false_iff.mpr hAaOk
      have hPmOkF : mallocngPosixMemalignOk align len = false := hPmEqAa.trans hAaF
      have hRetFail := posixRet_of_ge8_fail (len := len) hGe8 hAaF
      simp only [hAaF, Bool.false_eq_true, ↓reduceIte]
      let evVal : BitVec 32 := if !alignedAllocAlignOk align then 22#32 else 12#32
      refine SepWP.weaken_pre (P' :=
        ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
        ⌜MallocngCallAccounting 16 (fineStepReserve (.alloc 0) bud) sc sm⌝ ∗
        ⌜sm.readReg64 .x0 = 0#64 ∧ sm.tpidrEl0 = tp ∧ sm.brkStart = brkStart ∧
         MallocngNoOrphanMappings ivs0 ivs0 sc.mem sm.mem⌝ ∗
        (((tp - 0xa4#64) ↦₃₂ evVal) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ w3) ∗
         memRegion res 8 ∗ stackFrameAt sp1 736 ∗ stackFrameAt (sp1 - 736#64) 256 ∗
         FineCoreImpl γ maddrs brkStart sm.brk bud ivs0 ∗
         ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)))
        (by dsimp only [FramePM, evVal]; exact Entails.of_eq (by ac_rfl)) ?_
      refine sepWP_pure_left fun hcl_sm => sepWP_pure_left fun ⟨hproc_sm, hmd_sm⟩ =>
        sepWP_pure_left fun ⟨hx0_sm, htp_sm, hbrks_sm, hNoOrph_sm⟩ => ?_
      wp_step; wp_step; wp_step
      have hpc_bl0 : b + 0x44#64 + (mbase 0 - mbase 11 - 0x44#64) = mbase 0 := by rw [hb]; bv_arith
      conv => arg 3; simp only [hpc_bl0]
      refine sepWP_call_errno (ret_pc := b + 0x48#64) herr (by simp [arm64_norm]) (by simp [arm64_norm, hrun_m])
        (by simpa [arm64_norm, hsp_sm] using hspAl32) (by simp [arm64_norm]) hcl_sm
        fun se hpc_e hrun_e hsp_e hcs_e _hcl_e hproc_e hbrk_e hperm_e hx0_e => ?_
      have hsp_se : se.sp = sp1 := (by simpa [arm64_norm] using hsp_e : se.sp = sm.sp).trans hsp_sm
      have _hspAl_se : (se.sp &&& 15#64 == 0#64) = true := by rw [hsp_se]; exact hspAl32
      have ha16_se : se.sp + 16#64 = s0.sp - 16#64 := by rw [hsp_se]; exact ha16_sp
      have ha8_se : se.sp + 8#64 = s0.sp - 24#64 := by rw [hsp_se]; exact ha8_sp
      have ha32_se : se.sp + 32#64 = s0.sp := by rw [hsp_se]; exact ha32_sp
      have hx0_se : se.readReg64 (.gpr 0#5) = tp - 0xa4#64 := by simpa [arm64_norm, htp_sm] using hx0_e
      have hbrk_se : se.brk = sm.brk := hbrk_e.trans (by simp [arm64_norm])
      have hperm_se : se.mem.perm = sm.mem.perm := hperm_e.trans (by simp [arm64_norm])
      have hProc0_se : MallocngProcPreserved s0 se :=
        alignedProcPreserved_trans
          (alignedProcPreserved_trans hsc_proc hproc_sm)
          (alignedProcPreserved_trans (by proc_preserved_step) hproc_e)
      wp_step; wp_step; wp_step; wp_step; wp_step
      refine sepWP_let_state fun sf hsf => ?_
      have hperm_f : sf.mem.perm = sm.mem.perm := by subst hsf; simpa [arm64_norm] using hperm_se
      have hbrk_f : sf.brk = sm.brk := by subst hsf; simpa [arm64_norm] using hbrk_se
      have hNoOrphAll : MallocngNoOrphanMappings ivs0 ivs0 s0.mem sf.mem :=
        noOrphanMappings_congr_perm (hsc_mem ▸ hPerm2_0) hNoOrph_sm hperm_f
      have hAcctAll : MallocngCallAccounting 16 (fineStepReserve (.alloc 0) bud) s0 sf :=
        ⟨alignedProcPreserved_trans hProc0_se (by subst hsf; proc_preserved_step),
         mappedDelta_congr_perm (hsc_mem ▸ hPerm2_0) hmd_sm hperm_f⟩
      refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun_e]) ⟨fun hmF => ?_, ?_, ?_⟩
      · refine Satisfies.mono (sepConj_mono_left ?_) hmF
        simp only [hPmOkF, Bool.false_eq_true, ↓reduceIte, OptOutPtr_interp_none, OptOutPtr_pureWf]
        rw [pure_sepConj_of_true ⟨True.intro, by subst hsf; simpa [arm64_norm, evVal] using hRetFail, hAcctAll⟩,
          stackFrameAt_1024_split_pm s0.sp]
        have hRt :
            (((tp - 0xa4#64) ↦₃₂ evVal) ∗
             ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ⊢
            MallocngRuntime maddrs tp := by
          dsimp only [MallocngRuntime]
          simp only [sepExists_sepConj_left]
          exact Entails.trans (by sep_frame) (Entails.sepExists_intro evVal)
        have hPostEnv0 :
            (FineCoreImpl γ maddrs brkStart sm.brk bud ivs0 ∗
             MallocngRuntime maddrs tp) ⊢
            FinePostEnv γ maddrs tp brkStart bud ivs0 s0 sf := by
          dsimp only [FinePostEnv, FineEnv]
          refine Entails.trans ?_ (Entails.sepExists_intro ivs0)
          have htp_f : se.tpidrEl0 = tp := hProc0_se.2.2.1.trans htp0
          have hbrks_f : se.brkStart = brkStart := hProc0_se.2.2.2.1.trans hbrks0
          rw [FineHeapImpl_eq, pure_sepConj_of_true hNoOrphAll,
            pure_sepConj_of_true ⟨by subst hsf; simp [arm64_norm, htp_f], by subst hsf; simp [arm64_norm, hbrks_f]⟩,
            hbrk_f]
          sep_frame
        dsimp only [sp1]; cells_unfold
        refine Entails.trans (Entails.of_eq (show _ =
            (FineCoreImpl γ maddrs brkStart sm.brk bud ivs0 ∗
             (((tp - 0xa4#64) ↦₃₂ evVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) ∗
            (((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
             ((s0.sp - 8#64) ↦₆₄ w3) ∗
             memRegion res 8 ∗ stackFrameAt (s0.sp - 32#64) 736 ∗ stackFrameAt (s0.sp - 32#64 - 736#64) 256) by
          dsimp only [evVal]; ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left (Entails.trans (sepConj_mono_right hRt) hPostEnv0)) (by sep_frame)
      · subst hsf; have _ := ha32_se; simp [arm64_norm]
      · subst hsf
        exact ⟨by simp [arm64_norm],
          by simpa [arm64_norm] using hcs_e.readReg64_x20.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x20),
          by simpa [arm64_norm] using hcs_e.readReg64_x21.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x21),
          by simpa [arm64_norm] using hcs_e.readReg64_x22.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x22),
          by simpa [arm64_norm] using hcs_e.readReg64_x23.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x23),
          by simpa [arm64_norm] using hcs_e.readReg64_x24.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x24),
          by simpa [arm64_norm] using hcs_e.readReg64_x25.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x25),
          by simpa [arm64_norm] using hcs_e.readReg64_x26.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x26),
          by simpa [arm64_norm] using hcs_e.readReg64_x27.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x27),
          by simpa [arm64_norm] using hcs_e.readReg64_x28.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x28),
          by simp [arm64_norm],
          by simpa [arm64_norm] using hcs_e.vregs.trans (by simpa [hsc, arm64_norm] using hcs_m.vregs)⟩

/-- Placed fine-model entrypoint contract for `"posix_memalign"` (`blk11`). -/
theorem placed_posixMemalign_fine_entry_ok (hImplRaw : LibcMallocImplFineRawStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (finePosixMemalignSpec svc γ (mallocngAddrsOfPlacement mpl)) := by
  let _ : MallocngMultiPlacement := ⟨mpl, svc, hPlace, hSvc⟩
  refine ⟨by decide +kernel, 11, 0, by decide +kernel, ?_⟩
  rw [fnAddr_posix_memalign]
  exact withCL_to_withCodeLoaded (blk11_posixMemalign_fine hImplRaw γ)

end LibsignalBinary.Heap.Fine
