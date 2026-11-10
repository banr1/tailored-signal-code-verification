/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAlignedAllocProof
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Placed `posix_memalign` Verification

Proves the cross-block `subroutine_ok` specification (`placed_posixMemalign_ok`) and top-level
`mallocngMultiEntryOk` entry theorems (`posixMemalignPlaced_entry_tok_ok`,
`posixMemalignPlaced_entry_tight_ok`) for `mallocng` `posix_memalign` (`blk11`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.CType Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

private theorem sepWP_pure_left_pm {prog : Program} {tgt : BitVec 64} {s : State}
    {p : Prop} {Q : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : p → SepWP prog tgt s Q post oom) :
    SepWP prog tgt s (⌜p⌝ ∗ Q) post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact SepWP.to_reaches_pc (h hm.1) hm.2

private theorem sepWP_let_state_pm {prog : Program} {tgt : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ s' : State, s' = s → SepWP prog tgt s' P post oom) :
    SepWP prog tgt s P post oom :=
  h s rfl

local macro "cells_unfold_pre" : tactic =>
  `(tactic| conv => arg 4; simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub,
    ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left])

local macro "proc_preserved_step" : tactic =>
  `(tactic| exact ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩)

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
private theorem blk11_posixMemalign (hMalloc : LibcMallocImplPlaced24Stmt)
    [MallocngMultiPlacement] {B : GhostName → BitVec 64 → Nat → Nat → SepProp} (hB : ∀ γ p n a, MallocngTightBlock γ p n a ⊢ B γ p n a) (γ : GhostName) :
    subroutine_ok (mallocngBlockProg mmpl 11 msvc) (mbase 11)
      (withCL mmpl (ToBaseSpec.toSpec (mallocngPosixMemalignTokSpec B msvc γ maddrs) (mbase 11))) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have hfn : ∀ c, (blkPC_b11.rebase c (fun _ => none)).fnAddr "posix_memalign" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase, Program.fnOff, Program.findSymbol?, blkPC_b11, PlacedLib.program]
    rw [blkSymsEq_b11]
    have hf : (ProofLib.ProgramReflection.toStringSymbols blkSymChars_b11).find? (·.1 == "posix_memalign") =
        some ("posix_memalign", 0) := by decide
    rw [hf]; exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b11 (hfn (mbase 11)) fun b hb => ?_
  have _ := hb
  rw [hfn b]
  have herr := placed_errnoLocation_perm_ok (P := blkPC_b11.rebase b (fun _ => none))
    (externAt?_placedProgram_rebase_none _ _ _ _) rfl
  apply subroutine_ok_of_sepWP_init
  rintro ⟨res, align, len, sp0, tp, brkStart, bud, ivs0⟩ R s0 hpc hrun hpre hspAl0
  dsimp only [ToBaseSpec.toSpec, mallocngPosixMemalignTokSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨rfl, ⟨hx0, hx1, hx2, hsp_eq, _, _, _, hCaveat⟩, hpre⟩ := hpre
  subst hsp_eq
  change s0.readReg64 (.gpr 0#5) = res at hx0
  change s0.readReg64 (.gpr 1#5) = align at hx1
  change s0.readReg64 (.gpr 2#5) = len at hx2
  have ⟨htp0, hbrks0⟩ : s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart := by
    have hm0 : s0.mem ⊨ ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
        ((OptOutPtr (MallocngTokBlock (B γ))).interp res none ∗
         mallocngIface.MallocngHeap γ maddrs tp brkStart s0.brk bud ivs0 ∗
         stackFrameAt s0.sp mallocngStackBytes ∗ R) := by
      dsimp only [MallocngEnv] at hpre
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hm0; exact hm0.1
  refine ⟨(OptOutPtr (MallocngTokBlock (B γ))).interp res none ∗
    MallocngEnv mallocngIface γ maddrs tp brkStart bud ivs0 s0 ∗
    stackFrameAt s0.sp mallocngStackBytes, by simpa [sepConj_assoc] using hpre, ?_⟩
  wp_step; wp_step
  wp_if hLs7
  · -- Early exit (`align.toNat < 8`)
    have hLt8 : align.toNat < 8 := by
      have hUle : align.ule 7#64 = true := by simpa [arm64_norm, hx1] using hLs7
      rw [BitVec.ule, decide_eq_true_eq] at hUle
      change align.toNat ≤ 7 at hUle; omega
    have hPmOkF : mallocngPosixMemalignOk align len = false := by
      simp [mallocngPosixMemalignOk, show ¬ 8 ≤ align.toNat by omega]
    have hRetEq : (22#32 : BitVec 32) = mallocngPosixMemalignRet align len := by
      simp [mallocngPosixMemalignRet, hLt8]
    wp_step; wp_step
    refine sepWP_let_state_pm fun sf hsf => ?_
    have hbrk_f : sf.brk = s0.brk := by subst hsf; simp [arm64_norm]
    refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun]) ⟨fun hm => ?_, ?_, ?_⟩
    · refine Satisfies.mono (sepConj_mono_left ?_) hm
      simp only [hPmOkF, Bool.false_eq_true, ↓reduceIte, OptOutPtr_pureWf, mallocngAlignedBudget]
      rw [pure_sepConj_of_true ⟨True.intro, by subst hsf; simpa [arm64_norm] using hRetEq,
            ⟨by subst hsf; proc_preserved_step, mappedDelta_of_perm_eq (by subst hsf; simp [arm64_norm])⟩⟩]
      have hEnvToPost :
          MallocngEnv mallocngIface γ maddrs tp brkStart bud ivs0 s0 ⊢
          MallocngPostEnv mallocngIface γ maddrs tp brkStart bud ivs0 s0 sf := by
        dsimp only [MallocngPostEnv, MallocngEnv]
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
  · -- `8 ≤ align.toNat`: prologue and `bl aligned_alloc`
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
    refine sepWP_let_state_pm fun sc hsc => ?_
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
    have hAaSub := placed_alignedAlloc_errno_ok hMalloc
      (P := blkPC_b11.rebase b (fun _ => none)) hB
      γ tp brkStart align len bud ivs0 (externAt?_placedProgram_rebase_none _ _ _ _) rfl
    refine SepWP.call_subroutine_frame (F := FramePM) (x := ())
      (ret_pc := b + 0x28#64) hAaSub (by subst hsc; simp [arm64_norm]) (by subst hsc; simp [arm64_norm, hrun])
      (by simpa [State.spAligned, hsc_sp] using hspAl32) (by subst hsc; simp [arm64_norm])
      (fun R' hm => by
        refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
        dsimp only [alignedAllocErrnoSpec, withCL, FramePM, MallocngEnv, OptOutPtr]
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
        exact mallocngTightOomCond_of_perm_eq (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (fun _ => by simp only [arm64_norm]; rw [hm2.trans hm1]) hOom)
    dsimp only [alignedAllocErrnoSpec, withCL] at *
    rw [hsc_sf736]
    have hsp_sm : sm.sp = sp1 := hsp_m.trans hsc_sp
    have _hspAl_sm : (sm.sp &&& 15#64 == 0#64) = true := by rw [hsp_sm]; exact hspAl32
    have hx19_sm : sm.readReg64 (.gpr 19#5) = res :=
      hcs_m.readReg64_x19.trans (by subst hsc; simp [arm64_norm])
    have hPerm2_0 : m2.perm = s0.mem.perm := hm2.trans hm1
    by_cases hAaOk : mallocngAlignedAllocOk align len = true
    · -- Success (`hAaOk = true`)
      simp only [hAaOk, ↓reduceIte]
      have hPmOkT : mallocngPosixMemalignOk align len = true := hPmEqAa.trans hAaOk
      have hRet0 := posixRet_of_ge8_ok (len := len) hGe8 hAaOk
      let eff := mallocngAlignedEffSize align.toNat len.toNat
      let bf := mallocngAlignedBudget true align.toNat len.toNat bud
      conv => arg 4; dsimp only [FramePM]; rw [memRegion_eight res]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro oldRes
      apply SepWP.exists_elim; intro q
      refine SepWP.weaken_pre (P' :=
        ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
        ⌜MallocngCallAccounting 16 (MallocngTightStepBound eff bud.peakCount) sc sm⌝ ∗
        ⌜sm.readReg64 .x0 = q ∧ q ≠ 0#64 ∧ max align.toNat 16 ∣ q.toNat ∧ len.toNat + q.toNat < 2 ^ 64⌝ ∗
        ((res ↦₆₄ oldRes) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ w3) ∗
         stackFrameAt sp1 736 ∗ stackFrameAt (sp1 - 736#64) 256 ∗
         MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 sc sm ∗
         (MallocngTokBlock (B γ)).interp q (len.toNat, max align.toNat 16)))
        (by dsimp only [MallocngTokBlock, eff, bf]; exact Entails.of_eq (by ac_rfl)) ?_
      refine sepWP_pure_left_pm fun hcl_sm => sepWP_pure_left_pm fun ⟨hproc_sm, hmd_sm⟩ =>
        sepWP_pure_left_pm fun ⟨hx0_sm, hqNe, hqDvd, hqBound⟩ => ?_
      have hPureQ : (MallocngTokBlock (B γ)).pureWf q (len.toNat, max align.toNat 16) :=
        ⟨hqNe, hqDvd, by omega⟩
      wp_step; wp_step
      wp_if hqZero
      · exfalso; exact hPureQ.1 (by simpa [arm64_norm, hx0_sm] using hqZero)
      · -- Success: `q != 0`
        have ha16_sm : sm.sp + 16#64 = s0.sp - 16#64 := by rw [hsp_sm]; exact ha16_sp
        have ha8_sm : sm.sp + 8#64 = s0.sp - 24#64 := by rw [hsp_sm]; exact ha8_sp
        have ha32_sm : sm.sp + 32#64 = s0.sp := by rw [hsp_sm]; exact ha32_sp
        wp_step
        wp_str64_cl m3 hm3 hcl_sm _hcl3
        wp_step; wp_step; wp_step
        refine sepWP_let_state_pm fun sf hsf => ?_
        have hPerm3_sm : sf.mem.perm = sm.mem.perm := by subst hsf; simpa [arm64_norm] using hm3
        have hbrk_f : sf.brk = sm.brk := by subst hsf; simp [arm64_norm]
        have hProcAll : MallocngProcPreserved s0 sf :=
          alignedProcPreserved_trans
            (alignedProcPreserved_trans hsc_proc hproc_sm)
            (by subst hsf; proc_preserved_step)
        have hAcctAll : MallocngCallAccounting 16 (MallocngTightStepBound eff bud.peakCount) s0 sf :=
          ⟨hProcAll, mappedDelta_congr_perm (hsc_mem ▸ hPerm2_0) hmd_sm hPerm3_sm⟩
        refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun_m]) ⟨fun hmF => ?_, ?_, ?_⟩
        · refine Satisfies.mono (sepConj_mono_left ?_) hmF
          simp only [hPmOkT, ↓reduceIte, OptOutPtr_interp_some, OptOutPtr_pureWf]
          rw [pure_sepConj_of_true ⟨True.intro, by subst hsf; simpa [arm64_norm] using hRet0.symm, hAcctAll⟩,
            stackFrameAt_1024_split_pm s0.sp]
          have hPostEnvCongr :
              MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 sc sm ⊢
              MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf := by
            dsimp only [MallocngPostEnv, MallocngEnv]
            refine Entails.sepExists_elim fun ivsf => Entails.trans ?_ (Entails.sepExists_intro ivsf)
            refine Entails.pure_left fun hNoOrph => Entails.pure_left fun ⟨htp_sm, hbrks_sm⟩ => ?_
            rw [pure_sepConj_of_true (noOrphanMappings_congr_perm (hsc_mem ▸ hPerm2_0) hNoOrph hPerm3_sm),
              pure_sepConj_of_true ⟨by subst hsf; simp [arm64_norm, htp_sm], by subst hsf; simp [arm64_norm, hbrks_sm]⟩,
              hbrk_f]
            sep_frame
          have hOutPtr :
              ((res ↦₆₄ q) ∗ (MallocngTokBlock (B γ)).interp q (len.toNat, max align.toNat 16)) ⊢
              outPtrPost (MallocngTokBlock (B γ)) res (len.toNat, max align.toNat 16) := by
            rw [outPtrPost_def]
            refine Entails.trans ?_ (Entails.sepExists_intro q)
            rw [pure_sepConj_of_true hPureQ]; sep_frame
          dsimp only [sp1]; cells_unfold
          refine Entails.trans (Entails.of_eq (show _ =
              ((res ↦₆₄ q) ∗ (MallocngTokBlock (B γ)).interp q (len.toNat, max align.toNat 16)) ∗
              MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 sc sm ∗
              (((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
               ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
               ((s0.sp - 8#64) ↦₆₄ w3) ∗
               stackFrameAt (s0.sp - 32#64) 736 ∗ stackFrameAt (s0.sp - 32#64 - 736#64) 256) by
            dsimp only [MallocngTokBlock, bf]; ac_rfl)) ?_
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
    · -- Failure (`hAaOk = false`)
      have hAaF : mallocngAlignedAllocOk align len = false := Bool.eq_false_iff.mpr hAaOk
      have hPmOkF : mallocngPosixMemalignOk align len = false := hPmEqAa.trans hAaF
      have hRetFail := posixRet_of_ge8_fail (len := len) hGe8 hAaF
      simp only [hAaF, Bool.false_eq_true, ↓reduceIte, mallocngAlignedBudget]
      let evVal : BitVec 32 := if !alignedAllocAlignOk align then 22#32 else 12#32
      refine SepWP.weaken_pre (P' :=
        ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
        ⌜MallocngCallAccounting 16 (MallocngTightStepBound 0 bud.peakCount) sc sm⌝ ∗
        ⌜sm.readReg64 .x0 = 0#64 ∧ sm.tpidrEl0 = tp ∧ sm.brkStart = brkStart ∧
         MallocngNoOrphanMappings ivs0 ivs0 sc.mem sm.mem⌝ ∗
        (((tp - 0xa4#64) ↦₃₂ evVal) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ w3) ∗
         memRegion res 8 ∗ stackFrameAt sp1 736 ∗ stackFrameAt (sp1 - 736#64) 256 ∗
         MallocngCoreImpl γ maddrs brkStart sm.brk bud ivs0 ∗
         ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)))
        (by dsimp only [FramePM, evVal]; exact Entails.of_eq (by ac_rfl)) ?_
      refine sepWP_pure_left_pm fun hcl_sm => sepWP_pure_left_pm fun ⟨hproc_sm, hmd_sm⟩ =>
        sepWP_pure_left_pm fun ⟨hx0_sm, htp_sm, hbrks_sm, hNoOrph_sm⟩ => ?_
      wp_step; wp_step
      conv => arg 3; simp only [arm64_norm, show sm.readReg64 (.gpr 0#5) = 0#64 from hx0_sm,
        beq_self_eq_true, ↓reduceIte]
      wp_step
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
      refine sepWP_let_state_pm fun sf hsf => ?_
      have hperm_f : sf.mem.perm = sm.mem.perm := by subst hsf; simpa [arm64_norm] using hperm_se
      have hbrk_f : sf.brk = sm.brk := by subst hsf; simpa [arm64_norm] using hbrk_se
      have hNoOrphAll : MallocngNoOrphanMappings ivs0 ivs0 s0.mem sf.mem :=
        noOrphanMappings_congr_perm (hsc_mem ▸ hPerm2_0) hNoOrph_sm hperm_f
      have hAcctAll : MallocngCallAccounting 16 (MallocngTightStepBound 0 bud.peakCount) s0 sf :=
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
            (MallocngCoreImpl γ maddrs brkStart sm.brk bud ivs0 ∗
             MallocngRuntime maddrs tp) ⊢
            MallocngPostEnv mallocngIface γ maddrs tp brkStart bud ivs0 s0 sf := by
          dsimp only [MallocngPostEnv, MallocngEnv, mallocngIface]
          refine Entails.trans ?_ (Entails.sepExists_intro ivs0)
          have htp_f : se.tpidrEl0 = tp := hProc0_se.2.2.1.trans htp0
          have hbrks_f : se.brkStart = brkStart := hProc0_se.2.2.2.1.trans hbrks0
          rw [MallocngHeapImpl_eq, pure_sepConj_of_true hNoOrphAll,
            pure_sepConj_of_true ⟨by subst hsf; simp [arm64_norm, htp_f], by subst hsf; simp [arm64_norm, hbrks_f]⟩,
            hbrk_f]
          sep_frame
        dsimp only [sp1]; cells_unfold
        refine Entails.trans (Entails.of_eq (show _ =
            (MallocngCoreImpl γ maddrs brkStart sm.brk bud ivs0 ∗
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

theorem placed_posixMemalign_ok (hMalloc : LibcMallocImplPlaced24Stmt)
    [MallocngMultiPlacement] {P : Program} {B : GhostName → BitVec 64 → Nat → Nat → SepProp} (hB : ∀ γ p n a, MallocngTightBlock γ p n a ⊢ B γ p n a) (γ : GhostName)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 11)
      (withCL mmpl (ToBaseSpec.toSpec (mallocngPosixMemalignTokSpec B msvc γ maddrs) (mbase 11))) :=
  subroutine_ok_block_to_block (j := 11) (by decide) (blk11_posixMemalign hMalloc hB γ) hext hsvc

theorem posixMemalignPlaced_entry_tok_ok {B : GhostName → BitVec 64 → Nat → Nat → SepProp} (hB : ∀ γ p n a, MallocngTightBlock γ p n a ⊢ B γ p n a)
    (hMalloc : LibcMallocImplPlaced24Stmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (mallocngPosixMemalignTokSpec B svc γ (mallocngAddrsOfPlacement mpl)) := by
  let _ : MallocngMultiPlacement := ⟨mpl, svc, hPlace, hSvc⟩
  refine ⟨by decide +kernel, 11, 0, by decide +kernel, ?_⟩
  rw [fnAddr_posix_memalign]
  exact withCL_to_withCodeLoaded (blk11_posixMemalign hMalloc hB γ)

theorem posixMemalignPlaced_entry_tight_ok (hMalloc : LibcMallocImplPlaced24Stmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (mallocngPosixMemalignTightSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) :=
  posixMemalignPlaced_entry_tok_ok (B := mallocngOldTok)
    (fun γ p n a => mallocngTightBlock_to_token γ p n a) hMalloc mpl svc hPlace hSvc γ

end VerifiedLibraries.Mallocng.Proofs
