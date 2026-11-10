/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocNullPath

/-!
# Placed `__libc_realloc` and `realloc` Proofs

Proves `placed_libcRealloc_ok` for `__libc_realloc` (`blk14`) across the null, `ENOMEM`, in-place,
`mremap`, and out-of-place paths, and `reallocPlaced_entry_ok` for exported `"realloc"` (`blk13`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Non-Null Path -/

private theorem procPreserved_setPState_setPC {s0 s : State} (ps : PState) (pc : BitVec 64)
    (h : MallocngProcPreserved s0 s) :
    MallocngProcPreserved s0 ((s.setPState ps).setPC pc) := h

private theorem untouchedCS_setPState_setPC {s0 s : State} (ps : PState) (pc : BitVec 64)
    (h : ReallocUntouchedCS s0 s) :
    ReallocUntouchedCS s0 ((s.setPState ps).setPC pc) :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem realloc_post_sc_ok [MallocngMultiPlacement]
    (hImpl : LibcMallocImplPlacedTightKStmt) (hFree : LibcFreePlacedStmt)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart p : BitVec 64) (a : Nat)
    (oldSz oldEff newSz : Nat) (origBs tailBs : List (BitVec 8))
    (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 sSc : State) (st : MallocngSt)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hpNe : p ≠ 0#64)
    (hOrigLe : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hF : LiveUserBlockFacts st g idx p oldSz oldEff)
    (hNewMax : newSz ≤ MallocngMaxAllocSize) (hNew131 : newSz ≤ 131051)
    (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hpcSc : sSc.pc = b + 0x258#64) (hrunSc : sSc.status = .Running)
    (hPermSc : sSc.mem.perm = s0.mem.perm) (hclSc : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sSc.mem)
    (hbrkSc0 : sSc.brk = s0.brk) (hprocSc0 : MallocngProcPreserved s0 sSc)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hspSc0 : sSc.sp = s0.sp - 80#64) (hspMask0 : s0.sp &&& 15#64 = 0#64)
    (hw2_sc : sSc.readReg32 .x2 = BitVec.ofNat 32 (sizeToClassUnits ((newSz + 3) / 16) + 1))
    (hx3Sc0 : sSc.readReg64 .x3 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat))
    (hx4Sc0 : sSc.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx5Sc0 : sSc.readReg64 .x5 = g.slotEnd idx)
    (hx6Sc0 : sSc.readReg64 .x6 = BitVec.ofNat 64 g.sc)
    (hx19Sc0 : sSc.readReg64 .x19 = p)
    (hx21_sc : sSc.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hx23Sc0 : sSc.readReg64 .x23 = p + BitVec.ofNat 64 oldSz)
    (hcsSc0 : ReallocUntouchedCS s0 sSc)
    {post : State → SepProp → Prop}
    (hFinishPost : ∀ sf Pf,
      (∃ q : BitVec 64,
        MallocngCallAccounting 16
          (MallocngTightStepBound (mallocngReallocRes a newSz) bgt.peakCount) s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
        (Pf ⊢ stackFrame s0 800 ∗
          MallocngPostEnv mallocngIface γ maddrs tp brkStart
            (mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt) ivs0 s0 sf ∗
          ⌜(MallocngTightInitBlock γ a).pureWf q (newSz, origBs.take newSz)⌝ ∗
          (MallocngTightInitBlock γ a).interp q (newSz, origBs.take newSz) ∗ emp)) →
      post sf Pf) :
    let sp1 := s0.sp - 80#64
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) sSc
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
       MallocngTightBlock γ p oldSz a ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ emp)
      post
      (fun sf => ⌜MallocngTightOomCond msvc newSz bgt.peakCount s0 sf⌝) := by
  intro sp1; have _ := hb
  apply sepWP_abstract_all; intro PG postG oomG hPG hPostG hOomG
  generalize hw2Val : BitVec.ofNat 32 (sizeToClassUnits ((newSz + 3) / 16) + 1) = w2v at hw2_sc
  wp_step; wp_step
  wp_if hleSc
  · subst hPG hPostG hOomG
    have hScLt31 : g.sc < 2 ^ 31 := by rcases hF.sc_cases with h | h <;> omega
    have hUnitsLt48 := sizeToClassUnits_lt_48 (u := (newSz + 3) / 16) (by omega)
    have hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1 := by
      have hTrunc6 : BitVec.truncate 32 (BitVec.ofNat 64 g.sc) = BitVec.ofNat 32 g.sc := by bv_omega
      dsimp only [State.readReg32] at hw2_sc
      try rw [hx6Sc0] at hleSc
      try rw [hw2_sc] at hleSc
      rw [hTrunc6, ← hw2Val, bv32_sle_iff_of_lt31 hScLt31 (by omega), decide_eq_true_eq] at hleSc
      exact hleSc
    apply sepWP_bind_state; intro sS2 hsS2
    refine SepWP.mono (realloc_stage2_inplace_ok (al := a) hb
      γ tp brkStart bgt ivs0 s0 sS2 st hg hIdx origBs tailBs
      hOrigLe hTailLen hSlot hNew131 hFit hScLe (Frame := emp)
      (by rw [hsS2, State.pc_setPC])
      (by rw [hsS2, State.status_setPC, State.status_setPState]; exact hrunSc)
      (by rw [hsS2, State.mem_setPC, State.mem_setPState]; exact hPermSc)
      (by rw [hsS2, State.brk_setPC, State.brk_setPState]; exact hbrkSc0)
      (by rw [hsS2]; exact procPreserved_setPState_setPC _ _ hprocSc0) htp0 hbrks0
      (by rw [hsS2, State.sp_setPC, State.sp_setPState]; exact hspSc0)
      (spAligned_of_sub80 (by rw [hsS2, State.sp_setPC, State.sp_setPState]; exact hspSc0) hspMask0)
      hspMask0
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx3Sc0)
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx4Sc0)
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx5Sc0)
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx19Sc0)
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx21_sc)
      (by rw [hsS2]; exact untouchedCS_setPState_setPC _ _ hcsSc0)) ?_
    intro sf Pf _ _ ⟨hPermSf, _, hProcSf, hspSf, hcsSf, hx0Sf, hPf⟩
    exact hFinishPost sf Pf
      ⟨p, ⟨hProcSf, mallocngMappedDelta_of_perm_eq hPermSf⟩, hspSf, hcsSf, hx0Sf, hPf⟩
  · subst hPG hPostG hOomG
    apply sepWP_bind_state; intro sS4 hsS4
    have hmS4 : sS4.mem = sSc.mem := by rw [hsS4, State.mem_setPC, State.mem_setPState]
    have hbrkS4 : sS4.brk = s0.brk := by rw [hsS4, State.brk_setPC, State.brk_setPState]; exact hbrkSc0
    have hprocS4 : MallocngProcPreserved s0 sS4 := by
      rw [hsS4]; exact procPreserved_setPState_setPC _ _ hprocSc0
    refine SepWP.weaken_pre (repack_read_to_stage4 (al := a) γ tp brkStart bgt ivs0 s0 sS4 st
      origBs tailBs hTailLen hbrkS4 (hprocS4.2.2.1.trans htp0) (hprocS4.2.2.2.1.trans hbrks0)
      sp1 emp) ?_
    refine SepWP.mono (realloc_stage4_oop_ok (al := a) hImpl hFree hb
      γ tp brkStart bgt ivs0 s0 sS4 origBs (Frame := emp)
      hpNe (Nat.le_trans hF.p_add_n_le_end hF.stride_bounds.2.2.2.2.2) hOrigLe hNewMax
      (by rw [hsS4, State.pc_setPC])
      (by rw [hsS4, State.status_setPC, State.status_setPState]; exact hrunSc)
      (by rw [hmS4]; exact hPermSc) hprocS4
      (by rw [hsS4, State.sp_setPC, State.sp_setPState]; exact hspSc0)
      (spAligned_of_sub80 (by rw [hsS4, State.sp_setPC, State.sp_setPState]; exact hspSc0) hspMask0)
      hspMask0
      (by rw [hsS4, State.readReg64_setPC, State.readReg64_setPState]; exact hx19Sc0)
      (by rw [hsS4, State.readReg64_setPC, State.readReg64_setPState]; exact hx21_sc)
      (by rw [hsS4, State.readReg64_setPC, State.readReg64_setPState]; exact hx23Sc0)
      (by rw [hsS4]; exact untouchedCS_setPState_setPC _ _ hcsSc0)
      (by rw [hmS4]; exact hclSc))
      (fun sf Pf _ _ hPost => hFinishPost sf Pf hPost)

set_option maxHeartbeats 400000 in
private theorem realloc_nonnull_path_ok [MallocngMultiPlacement]
    (hImpl : LibcMallocImplPlacedTightKStmt) (hFree : LibcFreePlacedStmt)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart p newSize : BitVec 64) (a : Nat)
    (oldSz : Nat) (origBs : List (BitVec 8))
    (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 : State) (R : SepProp)
    (hpWf : (MallocngTightInitBlock γ a).pureWf p (oldSz, origBs))
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = newSize)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem) :
    let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
    let keptBs := origBs.take newSize.toNat
    let bf := mallocngReallocBudget ok (some (oldSz, origBs)) newSize.toNat bgt
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) s0
      (stackFrame s0 800 ∗ MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 ∗
       (MallocngTightInitBlock γ a).interp p (oldSz, origBs))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R →
          sf.mem ⊨
            ((⌜MallocngCallAccounting 16
                (MallocngTightStepBound (if ok then mallocngReallocRes a newSize.toNat else 0) bgt.peakCount)
                s0 sf⌝ ∗
              stackFrame s0 800 ∗
              MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
              if ok then
                ∃∗ q : BitVec 64,
                  ⌜sf.readReg64 .x0 = q ∧
                   (MallocngTightInitBlock γ a).pureWf q (newSize.toNat, keptBs)⌝ ∗
                  (MallocngTightInitBlock γ a).interp q (newSize.toNat, keptBs)
              else
                ⌜sf.readReg64 .x0 = 0#64⌝ ∗
                (MallocngTightInitBlock γ a).interp p (oldSz, origBs)) ∗
             ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf =>
        ⌜MallocngTightOomCond msvc (if ok then newSize.toNat else 0) bgt.peakCount s0 sf⌝) := by
  intro ok keptBs bf; have _ := hb
  obtain ⟨hpNe, hpAlign, hpOld64, hOrigLe⟩ := hpWf
  have hspMask0 : s0.sp &&& 15#64 = 0#64 := of_decide_eq_true hsp0
  have hspAlign80 : (s0.sp - 80#64) &&& 15#64 = 0#64 := by revert hspMask0; bv_robdd
  let sp1 := s0.sp - 80#64
  refine sepWP_mono_cl (post := fun sf Pf =>
      (sf.mem ⊨ Pf ∗ R →
        sf.mem ⊨
          (⌜MallocngCallAccounting 16
              (MallocngTightStepBound (if ok then mallocngReallocRes a newSize.toNat else 0) bgt.peakCount)
              s0 sf⌝ ∗
            stackFrame s0 800 ∗
            MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
            if ok then
              ∃∗ q : BitVec 64,
                ⌜sf.readReg64 .x0 = q ∧
                 (MallocngTightInitBlock γ a).pureWf q (newSize.toNat, keptBs)⌝ ∗
                (MallocngTightInitBlock γ a).interp q (newSize.toNat, keptBs)
            else
              ⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (MallocngTightInitBlock γ a).interp p (oldSz, origBs)) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    hcl0 ?_ (fun sf Pf _ _ hclSf ⟨hq, hspF, hcsF⟩ =>
      ⟨fun hm => Satisfies.mono (sepConj_mono_left
        (Entails.trans (Entails.pure_right hclSf (Entails.refl _))
          (Entails.of_eq (sepConj_comm _ _)))) (hq hm), hspF, hcsF⟩)
  refine SepWP.weaken_pre (sepConj_mono_left (stackFrame800_entails_exists_cells s0)) ?_
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro v0; apply SepWP.exists_left; intro v1
  apply SepWP.exists_left; intro v2; apply SepWP.exists_left; intro v3
  apply SepWP.exists_left; intro v4; apply SepWP.exists_left; intro v5
  apply SepWP.exists_left; intro v6; apply SepWP.exists_left; intro v7
  apply SepWP.exists_left; intro v8; apply SepWP.exists_left; intro v9
  wp_stp64_cl m1 hm1 hcl0 hcl1
  wp_step
  wp_stp64_cl m2 hm2 hcl1 hcl2
  wp_step; wp_step
  wp_if hzP
  ·
    exact absurd hzP hpNe
  ·
    wp_stp64_cl m3 hm3 hcl2 hcl3
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_if hhiMax
    ·
      have hNotLe : ¬ (newSize.toNat ≤ MallocngMaxAllocSize) :=
        (ult_maxAllocBv_iff newSize).mp hhiMax
      have hOkFalse : ok = false := decide_eq_false hNotLe
      have hBfEq : bf = bgt := by dsimp only [bf, mallocngReallocBudget]; simp [hOkFalse]
      apply sepWP_bind_state; intro sEn hsEn
      have hPermEn : sEn.mem.perm = s0.mem.perm := by
        have hmEq : sEn.mem = m3 := by rw [hsEn]; rfl
        rw [hmEq, hm3, hm2, hm1]
      have hclEn : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sEn.mem := by
        have hmEq : sEn.mem = m3 := by rw [hsEn]; rfl
        rwa [hmEq]
      have hEnvEn : MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 =
          MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 sEn := by
        unfold MallocngEnv; rw [hsEn]; rfl
      have hLoPack :
          (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
           ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
           ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
           ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
           ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ⊢
          ReallocSavedLo s0 sp1 ∗ (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
            memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) := by
        dsimp only [ReallocSavedLo, sp1]
        rw [show s0.sp - 80#64 + 8#64 = s0.sp - 72#64 by bv_lin, show s0.sp - 80#64 + 16#64 = s0.sp - 64#64 by bv_lin,
            show s0.sp - 80#64 + 24#64 = s0.sp - 56#64 by bv_lin, show s0.sp - 80#64 + 32#64 = s0.sp - 48#64 by bv_lin,
            show s0.sp - 80#64 + 40#64 = s0.sp - 40#64 by bv_lin, show s0.sp - 80#64 + 48#64 = s0.sp - 32#64 by bv_lin,
            show s0.sp - 80#64 + 56#64 = s0.sp - 24#64 by bv_lin, show s0.sp - 80#64 + 64#64 = s0.sp - 16#64 by bv_lin,
            show s0.sp - 80#64 + 72#64 = s0.sp - 8#64 by bv_lin]
        have hGrp :
            (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
             ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) =
            ((((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
              ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22)) ∗
             (((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
              ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9))) := by ac_rfl
        rw [hGrp]
        exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))
      rw [hEnvEn]
      refine SepWP.weaken_pre (P' := ReallocSavedLo s0 sp1 ∗
          (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
           memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
          stackFrameAt sp1 720 ∗ MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 sEn ∗
          (MallocngTightInitBlock γ a).interp p (oldSz, origBs))
        (Entails.trans (sepConj_mono_left (sepConj_mono_left hLoPack))
          (Entails.of_eq (by
            dsimp only [MallocngTightInitBlock, sp1]
            generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 sEn) = PEnv
            ac_rfl))) ?_
      refine SepWP.mono (realloc_enomem_ok hb γ tp brkStart bgt ivs0 s0 sEn
        (Rest := (MallocngTightInitBlock γ a).interp p (oldSz, origBs))
        (by rw [hsEn]; simp) (by rw [hsEn]; simp [hrun]) hPermEn (by rw [hsEn]; rfl)
        (by rw [hsEn]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (by rw [hsEn]; simp)
        (spAligned_of_sub80 (by rw [hsEn]; simp) hspMask0) hspMask0
        (by rw [hsEn]; simp) (by rw [hsEn]; simp) (by rw [hsEn]; simp) (by rw [hsEn]; simp)
        (by rw [hsEn]; exact ⟨by simp, by simp, by simp [calleeSavedVRegs]⟩) hclEn) ?_
      intro sf Pf _ _ ⟨hPermSf, _, hProcSf, hspSf, hcsSf, hx0Sf, hPf⟩
      refine ⟨fun hm => ?_, hspSf, hcsSf⟩
      have hAcc : MallocngCallAccounting 16
          (MallocngTightStepBound (if ok then mallocngReallocRes a newSize.toNat else 0) bgt.peakCount)
          s0 sf := ⟨hProcSf, mallocngMappedDelta_of_perm_eq hPermSf⟩
      simp only [hOkFalse, Bool.false_eq_true, ↓reduceIte, hBfEq] at hAcc ⊢
      refine Satisfies.mono ?_ (Satisfies.mono (sepConj_mono_left hPf) hm)
      refine Entails.trans (sepConj_mono_left (Entails.pure_right hAcc
        (sepConj_mono_right (sepConj_mono_right (Entails.pure_right hx0Sf (Entails.refl _)))))) ?_
      exact Entails.of_eq (by
        dsimp only [MallocngTightInitBlock]
        try ac_rfl)
    ·
      have hNewMax : newSize.toNat ≤ MallocngMaxAllocSize :=
        Classical.not_not.mp (mt (ult_maxAllocBv_iff newSize).mpr hhiMax)
      have hOkTrue : ok = true := decide_eq_true hNewMax
      let newSz := newSize.toNat
      have hNewBv : newSize = BitVec.ofNat 64 newSz := (BitVec.ofNat_toNat 64 newSize).symm
      wp_stp64_cl m4 hm4 hcl3 hcl4; wp_step; wp_stp64_cl m5 hm5 hcl4 hcl5; wp_step
      wp_if hneAlign
      · exact absurd (align16_and15_eq_zero hpAlign) hneAlign
      · apply sepWP_bind_state; intro s1 hs1
        have hPerm1 : s1.mem.perm = s0.mem.perm := by
          have hmEq : s1.mem = m5 := by rw [hs1]; rfl
          rw [hmEq, hm5, hm4, hm3, hm2, hm1]
        have hcl1' : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem := by
          have hmEq : s1.mem = m5 := by rw [hs1]; rfl
          rwa [hmEq]
        have hSavedEq :
            (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x24) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x26)) =
            (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1) := by
          dsimp only [ReallocSavedLo, ReallocSavedHi, sp1]
          rw [show s0.sp - 80#64 + 8#64 = s0.sp - 72#64 by bv_lin, show s0.sp - 80#64 + 16#64 = s0.sp - 64#64 by bv_lin,
              show s0.sp - 80#64 + 24#64 = s0.sp - 56#64 by bv_lin, show s0.sp - 80#64 + 32#64 = s0.sp - 48#64 by bv_lin,
              show s0.sp - 80#64 + 40#64 = s0.sp - 40#64 by bv_lin, show s0.sp - 80#64 + 48#64 = s0.sp - 32#64 by bv_lin,
              show s0.sp - 80#64 + 56#64 = s0.sp - 24#64 by bv_lin, show s0.sp - 80#64 + 64#64 = s0.sp - 16#64 by bv_lin,
              show s0.sp - 80#64 + 72#64 = s0.sp - 8#64 by bv_lin]
          ac_rfl
        have hUnpackPre :
            ((ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1) ∗ stackFrameAt sp1 720) ∗
            MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 ∗
            (MallocngTightInitBlock γ a).interp p (oldSz, origBs) ⊢
            ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
            ∃∗ st : MallocngSt, ∃∗ g : GroupDesc, ∃∗ idx : Nat, ∃∗ oldEff : Nat,
            ∃∗ tailBs : List (BitVec 8),
              ⌜(g ∈ st.groups ∧
                (∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveUser p oldSz oldEff) ∧
                LiveUserBlockFacts st g idx p oldSz oldEff) ∧
               tailBs.length = oldSz - origBs.length⌝ ∗
              reallocReadPre maddrs st
                (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
                 MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
                 MallocngTightBlock γ p oldSz a ∗ (p ↦ₛ (origBs ++ tailBs))) := by
          dsimp only [MallocngEnv, MallocngTightInitBlock]
          have hUnpackH := mallocngHeap_read_liveUser_unpackTight γ maddrs tp brkStart s0.brk bgt ivs0 p oldSz a
          have hTailE := memRegion_entails_exists_pointsToBytes (oldSz - origBs.length)
            (p + BitVec.ofNat 64 origBs.length) (by omega)
          refine Entails.trans (Q :=
              ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
              (mallocngIface.MallocngHeap γ maddrs tp brkStart s0.brk bgt ivs0 ∗
               MallocngTightBlock γ p oldSz a) ∗
              (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
              (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720))
            (Entails.of_eq (by
              generalize (ReallocSavedLo s0 sp1) = PLo
              generalize (ReallocSavedHi s0 sp1) = PHi
              ac_rfl)) ?_
          refine sepConj_mono_right ?_
          refine Entails.trans (sepConj_mono hUnpackH (sepConj_mono_right (sepConj_mono_left hTailE))) ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun st => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun g => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun idx => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun oldEff => ?_
          rw [sepExists_sepConj_left]; rw [sepExists_sepConj_right]; rw [sepExists_sepConj_right]
          refine Entails.sepExists_mono fun tailBs => ?_
          refine Entails.trans (Q :=
              ⌜g ∈ st.groups ∧
                (∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveUser p oldSz oldEff) ∧
                LiveUserBlockFacts st g idx p oldSz oldEff ∧ st.liveMap.ov p ≤ a - 16⌝ ∗
              ⌜tailBs.length = oldSz - origBs.length⌝ ∗
              ((p ↦ₛ origBs) ∗ ((p + BitVec.ofNat 64 origBs.length) ↦ₛ tailBs)) ∗
              MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
              ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
              ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
              MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
              MallocngTightBlock γ p oldSz a)
            (Entails.of_eq (by
              generalize (MallocngRoTablesAt maddrs) = PRo
              generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
              generalize (ReallocSavedLo s0 sp1) = PLo
              generalize (ReallocSavedHi s0 sp1) = PHi
              ac_rfl)) ?_
          refine Entails.pure_left fun ⟨hF1, hF2, hF3, _⟩ => Entails.pure_left fun hTLen => ?_
          refine Entails.pure_right ⟨⟨hF1, hF2, hF3⟩, hTLen⟩ ?_
          rw [← pointsToBytes_append p origBs tailBs]
          unfold reallocReadPre
          exact Entails.of_eq (by
            generalize (MallocngRoTablesAt maddrs) = PRo
            generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
            generalize (ReallocSavedLo s0 sp1) = PLo
            generalize (ReallocSavedHi s0 sp1) = PHi
            ac_rfl)
        rw [hSavedEq]
        refine SepWP.weaken_pre hUnpackPre ?_
        apply SepWP.pure_elim; rintro ⟨htp0, hbrks0⟩
        apply SepWP.exists_left; intro st; apply SepWP.exists_left; intro g
        apply SepWP.exists_left; intro idx; apply SepWP.exists_left; intro oldEff
        apply SepWP.exists_left; intro tailBs
        apply SepWP.pure_elim; rintro ⟨⟨hg, ⟨hIdx, hSlot⟩, hF⟩, hTailLen⟩
        apply SepWP.seq (realloc_stage1_read_ok hb hF
          (by rw [hs1]; simp) (by rw [hs1]; simp [hrun])
          (by rw [hs1]; simp) (by rw [hs1]))
        intro s7 P7 hpc7 hrun7
          ⟨⟨hP17, hx0_7, hx1_7, hx3_7, hx4_7, hx5_7, hx6_7, hx7_7, hx19_7, hx20_7, hx21_7, hx22_7, hx23_7, hx24_7⟩, hEnt7⟩
        refine SepWP.weaken_pre hEnt7 ?_
        obtain ⟨hmem17, hbrk17, hproc17, hsp17, _, _, _, hcs17⟩ := hP17
        have hPerm7 : s7.mem.perm = s0.mem.perm := by rw [hmem17, hPerm1]
        have hcl7 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s7.mem := by rwa [hmem17]
        have hbrk7 : s7.brk = s0.brk := hbrk17.trans (by rw [hs1]; rfl)
        have hproc7 : MallocngProcPreserved s0 s7 :=
          mallocngProcPreserved_trans (by rw [hs1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hproc17
        have hsp7 : s7.sp = s0.sp - 80#64 := hsp17.trans (by rw [hs1]; simp)
        have hal7 : s7.spAligned = true := spAligned_of_sub80 hsp7 hspMask0
        have hcs7 : ReallocUntouchedCS s0 s7 := by
          obtain ⟨h27, h28, hv⟩ := hcs17
          exact ⟨h27.trans (by rw [hs1]; simp), h28.trans (by rw [hs1]; simp),
            hv.trans (by rw [hs1]; simp [calleeSavedVRegs])⟩
        refine SepWP.weaken_pre (P' :=
            ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
            MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
            ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
            MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
            MallocngTightBlock γ p oldSz a ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ emp)
          (Entails.of_eq (by
            unfold reallocReadPre
            generalize (MallocngRoTablesAt maddrs) = PRo
            generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
            generalize (ReallocSavedLo s0 sp1) = PLo
            generalize (ReallocSavedHi s0 sp1) = PHi
            simp only [sepConj_emp]; ac_rfl)) ?_
        have hFinishPost : ∀ sf Pf,
            (∃ q : BitVec 64,
              MallocngCallAccounting 16
                (MallocngTightStepBound (mallocngReallocRes a newSz) bgt.peakCount) s0 sf ∧
              sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
              (Pf ⊢ stackFrame s0 800 ∗
                MallocngPostEnv mallocngIface γ maddrs tp brkStart
                  (mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt) ivs0 s0 sf ∗
                ⌜(MallocngTightInitBlock γ a).pureWf q (newSz, keptBs)⌝ ∗
                (MallocngTightInitBlock γ a).interp q (newSz, keptBs) ∗ emp)) →
            (sf.mem ⊨ Pf ∗ R →
              sf.mem ⊨
                (⌜MallocngCallAccounting 16
                    (MallocngTightStepBound (if ok then mallocngReallocRes a newSize.toNat else 0) bgt.peakCount)
                    s0 sf⌝ ∗
                  stackFrame s0 800 ∗
                  MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
                  if ok then
                    ∃∗ q : BitVec 64,
                      ⌜sf.readReg64 .x0 = q ∧
                       (MallocngTightInitBlock γ a).pureWf q (newSize.toNat, keptBs)⌝ ∗
                      (MallocngTightInitBlock γ a).interp q (newSize.toNat, keptBs)
                  else
                    ⌜sf.readReg64 .x0 = 0#64⌝ ∗
                    (MallocngTightInitBlock γ a).interp p (oldSz, origBs)) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
          rintro sf Pf ⟨q, hAcc, hspSf, hcsSf, hx0Q, hPf⟩
          refine ⟨fun hm => ?_, hspSf, hcsSf⟩
          have hBfTrue : mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt = bf := by
            dsimp only [bf, newSz]; rw [hOkTrue]
          simp only [hOkTrue, ↓reduceIte]
          change sf.mem ⊨ _ at hm
          refine Satisfies.mono ?_ (Satisfies.mono (sepConj_mono_left hPf) hm)
          rw [hBfTrue, sepConj_emp]
          have hRetEnt :
              ⌜(MallocngTightInitBlock γ a).pureWf q (newSz, keptBs)⌝ ∗
              (MallocngTightInitBlock γ a).interp q (newSz, keptBs) ⊢
              ∃∗ q' : BitVec 64,
                ⌜sf.readReg64 .x0 = q' ∧
                 (MallocngTightInitBlock γ a).pureWf q' (newSz, keptBs)⌝ ∗
                (MallocngTightInitBlock γ a).interp q' (newSz, keptBs) :=
            Entails.sepExists_right q
              (Entails.pure_left fun hWfQ => Entails.pure_right ⟨hx0Q, hWfQ⟩ (Entails.refl _))
          exact sepConj_mono_left
            (Entails.pure_right hAcc (sepConj_mono_right (sepConj_mono_right hRetEnt)))
        have hOomEq :
            (fun sf => ⌜MallocngTightOomCond msvc
              (if ok then newSize.toNat else 0) bgt.peakCount s0 sf⌝) =
            (fun sf => ⌜MallocngTightOomCond msvc newSz bgt.peakCount s0 sf⌝) := by
          funext sf; simp only [hOkTrue, ↓reduceIte]; rfl
        rw [hOomEq]
        have hlr0 : s0.readReg64 Reg.lr = s0.readReg64 .x30 := rfl
        rw [hlr0]
        have _ := hx3_7; have _ := hx21_7
        wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
        wp_if hhiStage3
        ·
          apply sepWP_bind_state; intro sS3 hsS3
          refine SepWP.mono (realloc_stage3_mremap_ok (al := a) hImpl hFree hb
            γ tp brkStart bgt ivs0 s0 sS3 st hg hIdx origBs tailBs
            hpNe hOrigLe hTailLen hSlot hF hNewMax
            (Frame := emp)
            (by rw [hsS3]; simp) (by rw [hsS3]; simp [hrun7])
            (by rw [hsS3]; simpa using hPerm7) (by rw [hsS3]; simpa using hbrk7)
            (by rw [hsS3]; exact hproc7) htp0 hbrks0
            (by rw [hsS3]; simpa using hsp7)
            (spAligned_of_sub80 (by rw [hsS3]; simpa using hsp7) hspMask0) hspMask0
            (by rw [hsS3]; simpa using hx0_7) (by rw [hsS3]; simpa using hx1_7)
            (by rw [hsS3]; simp) (by rw [hsS3]; simpa using hx6_7)
            (by rw [hsS3]; simpa using hx7_7) (by rw [hsS3]; simpa using hx19_7)
            (by rw [hsS3]; simpa using hx20_7) (by rw [hsS3]; simpa [newSz] using hx21_7)
            (by rw [hsS3]; simpa using hx22_7) (by rw [hsS3]; simpa using hx23_7)
            (by rw [hsS3]; simpa using hx24_7)
            (by rw [hsS3]; exact ⟨hcs7.1, hcs7.2.1, hcs7.2.2⟩)
            (by rw [hsS3]; exact hcl7))
            (fun sf Pf _ _ hPost => hFinishPost sf Pf hPost)
        ·
          have hP7Cond : ¬ ((if (BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat)).ule 131051#64 then
              BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat) else 131051#64).ult
              (BitVec.ofNat 64 newSz) = true) := hhiStage3
          have ⟨hNew131, hFit⟩ := not_stage3_hi_bounds
            (Nat.le_trans (Nat.le_add_right _ _) hF.p_add_n_le_end)
            hF.stride_bounds.2.2.2.2.2 hNewMax hP7Cond
          apply sepWP_bind_state; intro sSc0 hsSc0
          refine SepWP.weaken_pre (P' :=
              MallocngRoTablesAt maddrs ∗
              (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
               (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
               ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
               MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
               MallocngTightBlock γ p oldSz a ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ emp))
            (Entails.of_eq (by
              generalize (MallocngRoTablesAt maddrs) = PRo
              generalize (ReallocSavedLo s0 sp1) = PLo
              generalize (ReallocSavedHi s0 sp1) = PHi
              ac_rfl)) ?_
          apply SepWP.seq (realloc_sizeToClass_ok hb (newSize := BitVec.ofNat 64 newSz) rfl hNew131
            (by rw [hsSc0]; simp) (by rw [hsSc0]; simp [hrun7])
            (by rw [hsSc0]; simpa using hx21_7))
          intro sSc PSc hpcSc hrunSc
            ⟨⟨hPSc, hw2_sc, hx3_sc, hx4_sc, hx5_sc, hx6_sc, hx19_sc, _, hx21_sc, _, hx23_sc, _⟩, hEntSc⟩
          refine SepWP.weaken_pre hEntSc ?_
          refine SepWP.weaken_pre (P' :=
              ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
              MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
              ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
              MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
              MallocngTightBlock γ p oldSz a ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ emp)
            (Entails.of_eq (by
              generalize (MallocngRoTablesAt maddrs) = PRo
              generalize (ReallocSavedLo s0 sp1) = PLo
              generalize (ReallocSavedHi s0 sp1) = PHi
              ac_rfl)) ?_
          obtain ⟨hmemSc, hbrkSc, hprocSc, hspSc, _, _, _, hcsSc⟩ := hPSc
          have hPermSc : sSc.mem.perm = s0.mem.perm := by rw [hmemSc, hsSc0]; exact hPerm7
          have hclSc : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sSc.mem := by rw [hmemSc, hsSc0]; exact hcl7
          have hbrkSc0 : sSc.brk = s0.brk := hbrkSc.trans (by rw [hsSc0]; exact hbrk7)
          have hprocSc0 : MallocngProcPreserved s0 sSc :=
            mallocngProcPreserved_trans (by rw [hsSc0]; exact hproc7) hprocSc
          have hspSc0 : sSc.sp = s0.sp - 80#64 := hspSc.trans (by rw [hsSc0]; exact hsp7)
          have hcsSc0 : ReallocUntouchedCS s0 sSc :=
            ⟨hcsSc.1.trans (by rw [hsSc0]; exact hcs7.1),
              hcsSc.2.1.trans (by rw [hsSc0]; exact hcs7.2.1),
              hcsSc.2.2.trans (by rw [hsSc0]; exact hcs7.2.2)⟩
          exact realloc_post_sc_ok hImpl hFree hb γ tp brkStart p a oldSz oldEff newSz origBs tailBs
            bgt ivs0 s0 sSc st hg hIdx hpNe hOrigLe hTailLen hSlot hF hNewMax hNew131 hFit
            hpcSc hrunSc hPermSc hclSc hbrkSc0 hprocSc0 htp0 hbrks0 hspSc0 hspMask0 hw2_sc
            (hx3_sc.trans (by rw [hsSc0]; simpa using hx3_7))
            (hx4_sc.trans (by rw [hsSc0]; simpa using hx4_7))
            (hx5_sc.trans (by rw [hsSc0]; simpa using hx5_7))
            (hx6_sc.trans (by rw [hsSc0]; simpa using hx6_7))
            (hx19_sc.trans (by rw [hsSc0]; simpa using hx19_7))
            hx21_sc
            (hx23_sc.trans (by rw [hsSc0]; simpa using hx23_7))
            hcsSc0 hFinishPost

/-! ## Placed `__libc_realloc` and Exported `realloc` -/

private theorem optInitBlock_to_tight (γ : GhostName) (p : BitVec 64)
    (oldBlk : Option (Nat × List (BitVec 8))) (F : SepProp) :
    (OptOwn (MallocngInitBlock mallocngIface γ)).interp p oldBlk ∗ F ⊢
      ∃∗ a : Nat, (OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk ∗ F := by
  cases oldBlk with
  | none => exact Entails.sepExists_right 16 (Entails.refl _)
  | some blk =>
    rcases blk with ⟨sz, bs⟩
    simp only [OptOwn_interp_some]
    try dsimp only [MallocngInitBlock, MallocngTightInitBlock]
    change (MallocngBlockToken γ p sz ∗ _) ∗ F ⊢ _
    unfold MallocngBlockToken
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    refine Entails.sepExists_elim fun k => Entails.sepExists_right (k + 16) ?_
    exact sepConj_mono_left (sepConj_mono_left
      (mallocngBlockTokenK_to_tight γ p sz k (k + 16) (by omega)))

private theorem tightInitBlock_to_init (γ : GhostName) (a : Nat) (q : BitVec 64)
    (m : Nat × List (BitVec 8)) :
    (MallocngTightInitBlock γ a).interp q m ⊢ (MallocngInitBlock mallocngIface γ).interp q m := by
  rcases m with ⟨sz, bs⟩
  dsimp only [MallocngInitBlock, MallocngTightInitBlock]
  exact sepConj_mono_left (mallocngTightBlock_to_token γ q sz a)

private theorem optTightInitBlock_to_init (γ : GhostName) (a : Nat) (q : BitVec 64)
    (m : Option (Nat × List (BitVec 8))) :
    (OptOwn (MallocngTightInitBlock γ a)).interp q m ⊢
      (OptOwn (MallocngInitBlock mallocngIface γ)).interp q m := by
  cases m with
  | none => exact Entails.refl _
  | some m => exact tightInitBlock_to_init γ a q m

private theorem callAccounting_mono {k m m' : Nat} {s0 sf : State} (h : m ≤ m')
    (hA : MallocngCallAccounting k m s0 sf) : MallocngCallAccounting k m' s0 sf :=
  ⟨hA.1, MallocngMappedDelta.mono (Nat.le_refl _) h hA.2⟩

/-- Placed `__libc_realloc(p, newSize)` (`blk14`, `800` B stack). -/
theorem placed_libcRealloc_ok
    (hImpl : LibcMallocImplPlacedTightKStmt) (hFree : LibcFreePlacedStmt) :
    LibcReallocPlacedStmt := by
  intro _ γ tp brkStart p newSize a oldBlk bgt ivs0
  have hfn : ∀ c, (blkPC_b14.rebase c (fun _ => none)).fnAddr "__libc_realloc" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase]
    change c + BitVec.ofNat 64 (blkPC_b14.fnOff "__libc_realloc") = c
    rw [blkPC_b14_fnOff_0x0]
    exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b14 (hfn (mbase 14)) fun b hb => ?_
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre hsp
  rw [hfn b] at hpc
  have hpre' : s0.mem ⊨
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ ∗
      ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
       (OptOwn (MallocngTightInitBlock γ a)).pureWf p oldBlk⌝ ∗
      (stackFrame s0 800 ∗ MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 ∗
       (OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk) ∗ R := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    dsimp only [libcReallocPlacedSpec, withCL]
    generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0) = PEnv
    generalize ((OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk) = POld
    ac_rfl
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcl0, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx1, hpWf⟩, hpre'⟩ := hpre'
  cases oldBlk with
  | none =>
    rw [OptOwn_interp_none] at hpre'
    have hpre'' : s0.mem ⊨ ⌜p = 0#64⌝ ∗
        (stackFrame s0 800 ∗ MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0) ∗ R :=
      Satisfies.mono (Entails.of_eq (by
        generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0) = PEnv
        ac_rfl)) hpre'
    rw [satisfies_pure_sepConj] at hpre''; obtain ⟨hp0, hpre''⟩ := hpre''; subst hp0
    refine ⟨stackFrame s0 800 ∗ MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0, hpre'',
      SepWP.mono (realloc_null_path_ok hImpl hb γ tp brkStart newSize a bgt ivs0 s0 R hpc hrun hsp hx0 hx1 hcl0)
        fun sf Pf _ _ ⟨hq, hspF, hcsF⟩ => ⟨fun hm => Satisfies.mono ?_ (hq hm), hspF, hcsF⟩⟩
    dsimp only [libcReallocPlacedSpec, withCL, Option.map, Option.getD]
    simp only [List.take_nil]
    refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))))
    split
    · exact Entails.refl _
    · refine sepConj_mono_right ?_
      rw [OptOwn_interp_none, ← sepConj_emp ⌜(0#64 : BitVec 64) = 0#64⌝]
      exact Entails.pure_right rfl (Entails.refl emp)
  | some blk =>
    rcases blk with ⟨oldSz, origBs⟩
    exact ⟨stackFrame s0 800 ∗ MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 ∗
      (MallocngTightInitBlock γ a).interp p (oldSz, origBs), hpre',
      realloc_nonnull_path_ok hImpl hFree hb γ tp brkStart p newSize a oldSz origBs bgt ivs0 s0 R
        hpWf.2 hpc hrun hsp hx0 hx1 hcl0⟩

/-- Exported `"realloc"` (`blk13`, 1-instruction `b __libc_realloc` tail-call) at tight OOM bound. -/
theorem reallocPlaced_entry_tight_ok
    (hImpl : LibcMallocImplPlacedTightKStmt) (hFree : LibcFreePlacedStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "realloc"
      (mallocngReallocTightSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) := by
  letI : MallocngMultiPlacement := ⟨mpl, svc, hPlace, hSvc⟩
  refine ⟨by decide, 13, 0, by decide +kernel, ?_⟩
  rw [fnAddr_realloc mpl]
  apply withCL_to_withCodeLoaded
  have hfn : ∀ c, (blkPC_b13.rebase c (fun _ => none)).fnAddr "realloc" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase]
    change c + BitVec.ofNat 64 (blkPC_b13.fnOff "realloc") = c
    rw [blkPC_b13_fnOff_0x0]
    exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b13 (hfn (mbase 13)) fun b hb => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, newSize, sp, oldBlk, tp, brkStart, bgt, ivs0⟩ R s0 hpc hrun hpre hsp
  rw [hfn b] at hpc
  have _ := hb
  have hpre' : s0.mem ⊨
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ ∗
      ⌜s0.sp = sp ∧ s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
       (OptOwn (MallocngInitBlock mallocngIface γ)).pureWf p oldBlk⌝ ∗
      (stackFrameAt sp 1024 ∗ MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 ∗
       (OptOwn (MallocngInitBlock mallocngIface γ)).interp p oldBlk) ∗ R := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    dsimp only [withCL, mallocngReallocTightSpec, ToBaseSpec.toSpec, CType.CondOwn, mallocngStackBytes]
    generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0) = PEnv
    generalize ((OptOwn (MallocngInitBlock mallocngIface γ)).interp p oldBlk) = POld
    ac_rfl
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcl0, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hspEq, hx0, hx1, hpWf⟩, hpre'⟩ := hpre'
  have hSf1024 : stackFrameAt sp 1024 = (stackFrame s0 800 ∗ stackFrameAt (sp - 800#64) 224) := by
    rw [show (1024 : Nat) = 800 + 224 from rfl, stackFrameAt_split sp 800 224]
    congr 1; unfold stackFrame; rw [hspEq, stackFrameAt_eq_memRegion sp 800]
  rw [hSf1024] at hpre'
  obtain ⟨a, hpreA⟩ : ∃ a : Nat, s0.mem ⊨ ((stackFrame s0 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
      MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 ∗
      (OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk) ∗ R := by
    have hReord : ((stackFrame s0 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
        MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 ∗
        (OptOwn (MallocngInitBlock mallocngIface γ)).interp p oldBlk) ∗ R =
        (OptOwn (MallocngInitBlock mallocngIface γ)).interp p oldBlk ∗
        (((stackFrame s0 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
          MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0) ∗ R) := by
      generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0) = PEnv
      generalize ((OptOwn (MallocngInitBlock mallocngIface γ)).interp p oldBlk) = POld
      ac_rfl
    rw [hReord] at hpre'
    have h1 := Satisfies.mono (optInitBlock_to_tight γ p oldBlk _) hpre'
    rw [satisfies_sepExists] at h1
    obtain ⟨a, h1⟩ := h1
    refine ⟨a, Satisfies.mono (Entails.of_eq ?_) h1⟩
    generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0) = PEnv
    generalize ((OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk) = POld
    ac_rfl
  have hpWfA : (OptOwn (MallocngTightInitBlock γ a)).pureWf p oldBlk := hpWf
  refine ⟨(stackFrame s0 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
    MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 ∗
    (OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk, hpreA, ?_⟩
  wp_step
  apply sepWP_bind_state; intro s1 hs1
  have hRealloc := call_placed_libcRealloc (placed_libcRealloc_ok hImpl hFree)
    (P := blkPC_b13.rebase b (fun _ => none))
    γ tp brkStart p newSize a oldBlk bgt ivs0 (by intro pc; simp) rfl
  have hEnv1 : MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 =
      MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s1 := by
    unfold MallocngEnv; rw [hs1]; rfl
  have hSf1 : stackFrame s0 800 = stackFrame s1 800 := by unfold stackFrame; rw [hs1]; simp
  rw [hEnv1, hSf1]
  refine SepWP.call_subroutine_frame hRealloc (x := ()) (F := stackFrameAt (sp - 800#64) 224)
    (ret_pc := s0.readReg64 Reg.lr)
    (by rw [hs1]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by rw [hs1]; simp [hrun])
    (by unfold State.spAligned at hsp ⊢; rw [hs1]; simpa using hsp)
    (by rw [hs1]; simp)
    (fun R' hm => by
      have hcl1 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem := by rw [hs1]; exact hcl0
      have hPure1 : s1.readReg64 .x0 = p ∧ s1.readReg64 .x1 = newSize ∧
          (OptOwn (MallocngTightInitBlock γ a)).pureWf p oldBlk :=
        ⟨by rw [hs1]; simpa using hx0, by rw [hs1]; simpa using hx1, hpWfA⟩
      refine Satisfies.mono ?_ hm
      dsimp only [libcReallocPlacedSpec, withCL]
      refine Entails.trans (Entails.pure_right hcl1 (Entails.pure_right hPure1 (Entails.refl _))) ?_
      exact Entails.of_eq (by
        generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s1) = PEnv
        generalize ((OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk) = POld
        ac_rfl))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpcSf hrunSf hspSf hcsSf => ?_)
    (fun R' sf _ hOom => ?_)
  · have hspSf0 : sf.sp = s0.sp := hspSf.trans (by rw [hs1]; simp)
    have hcsSf0 : CalleeSavedPreserved s0 sf := CalleeSavedPreserved.trans (by
      rw [hs1]; exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp [calleeSavedVRegs]⟩) hcsSf
    refine SepWP.done hpcSf hrunSf ⟨fun hm => ?_, hspSf0, hcsSf0⟩
    dsimp only [libcReallocPlacedSpec, withCL] at hm
    have hs1Mem : s1.mem = s0.mem := by rw [hs1]; rfl
    have hAccCongr : ∀ k m, MallocngCallAccounting k m s1 sf → MallocngCallAccounting k m s0 sf := by
      intro k m ⟨hPr, hDl⟩
      exact ⟨mallocngProcPreserved_trans (by rw [hs1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hPr,
        by rwa [hs1Mem] at hDl⟩
    have hPostCongr : ∀ bf', MallocngPostEnv mallocngIface γ maddrs tp brkStart bf' ivs0 s1 sf =
        MallocngPostEnv mallocngIface γ maddrs tp brkStart bf' ivs0 s0 sf := fun bf' => by
      unfold MallocngPostEnv MallocngNoOrphanMappings; rw [hs1Mem]
    have hSfCombine : stackFrame s1 800 ∗ stackFrameAt (sp - 800#64) 224 = stackFrameAt sp 1024 := by
      rw [← hSf1, ← hSf1024]
    rw [hPostCongr] at hm
    dsimp only [withCL, mallocngReallocTightSpec, ToBaseSpec.toSpec, CType.CondOwn, mallocngStackBytes]
    by_cases hLe : newSize.toNat ≤ MallocngMaxAllocSize
    · simp only [decide_eq_true hLe, ↓reduceIte] at hm ⊢
      have hm' : sf.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          ⌜MallocngCallAccounting 16
             (MallocngTightStepBound (mallocngReallocRes a newSize.toNat) bgt.peakCount) s1 sf⌝ ∗
          (∃∗ q : BitVec 64, ⌜sf.readReg64 .x0 = q ∧
             (MallocngTightInitBlock γ a).pureWf q
               (newSize.toNat, ((oldBlk.map Prod.snd).getD []).take newSize.toNat)⌝ ∗
            (MallocngTightInitBlock γ a).interp q
              (newSize.toNat, ((oldBlk.map Prod.snd).getD []).take newSize.toNat)) ∗
          (stackFrame s1 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
          MallocngPostEnv mallocngIface γ maddrs tp brkStart
            (mallocngReallocBudget true oldBlk newSize.toNat bgt) ivs0 s0 sf ∗ R := by
        refine Satisfies.mono (Entails.of_eq ?_) hm; dsimp only [MallocngTightInitBlock]
        generalize (∃∗ q : BitVec 64, _) = PRet
        generalize (MallocngPostEnv mallocngIface γ maddrs tp brkStart _ ivs0 s0 sf) = PPost; ac_rfl
      rw [hSfCombine, satisfies_pure_sepConj] at hm'; obtain ⟨hclSf, hm'⟩ := hm'
      rw [satisfies_pure_sepConj] at hm'; obtain ⟨hAcc1, hm'⟩ := hm'
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm'; obtain ⟨q, hm'⟩ := hm'
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm'; obtain ⟨⟨hx0Q, hWfQ⟩, hm'⟩ := hm'
      have hAcc0 := hAccCongr _ _ hAcc1; rw [← hx0Q] at hWfQ hm'
      have hPurePost : (True : Prop) ∧
          (OptOwn (MallocngInitBlock mallocngIface γ)).pureWf (sf.readReg64 .x0)
            (some (newSize.toNat, ((oldBlk.map Prod.snd).getD []).take newSize.toNat)) ∧
          MallocngCallAccounting 16
            (MallocngStepBound (newSize.toNat + MaxAlignedAllocAlign) bgt.peakCount) s0 sf :=
        ⟨trivial, ⟨hWfQ.1, hWfQ⟩,
          callAccounting_mono (MallocngTightStepBound_reallocRes_le _ _ _) hAcc0⟩
      refine Satisfies.mono (Entails.trans
        (Entails.pure_right hclSf (Entails.pure_right hPurePost
          (sepConj_mono_left (tightInitBlock_to_init γ a _ _)))) ?_) hm'
      exact Entails.of_eq (by
        dsimp only [OptOwn, MallocngInitBlock]
        generalize (MallocngPostEnv mallocngIface γ maddrs tp brkStart _ ivs0 s0 sf) = PPost
        simp only [emp_sepConj]; ac_rfl)
    · simp only [decide_eq_false hLe, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      have hm' : sf.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          ⌜MallocngCallAccounting 16 (MallocngTightStepBound 0 bgt.peakCount) s1 sf⌝ ∗
          ⌜sf.readReg64 .x0 = 0#64⌝ ∗ (OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk ∗
          (stackFrame s1 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
          MallocngPostEnv mallocngIface γ maddrs tp brkStart
            (mallocngReallocBudget false oldBlk newSize.toNat bgt) ivs0 s0 sf ∗ R := by
        refine Satisfies.mono (Entails.of_eq ?_) hm
        generalize ((OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk) = POld
        generalize (MallocngPostEnv mallocngIface γ maddrs tp brkStart _ ivs0 s0 sf) = PPost; ac_rfl
      rw [hSfCombine, satisfies_pure_sepConj] at hm'; obtain ⟨hclSf, hm'⟩ := hm'
      rw [satisfies_pure_sepConj] at hm'; obtain ⟨hAcc1, hm'⟩ := hm'
      have hPurePost : (OptOwn (MallocngInitBlock mallocngIface γ)).pureWf p oldBlk ∧
          (OptOwn (MallocngInitBlock mallocngIface γ)).pureWf (sf.readReg64 .x0) none ∧
          MallocngCallAccounting 16 (MallocngStepBound 0 bgt.peakCount) s0 sf :=
        ⟨hpWf, trivial, callAccounting_mono (MallocngTightStepBound_le_stepBound _ _)
          (hAccCongr _ _ hAcc1)⟩
      refine Satisfies.mono (Entails.trans
        (Entails.pure_right hclSf (Entails.pure_right hPurePost
          (sepConj_mono_right (sepConj_mono_left (optTightInitBlock_to_init γ a p oldBlk))))) ?_) hm'
      exact Entails.of_eq (by
        dsimp only [OptOwn]
        generalize ((OptOwn (MallocngInitBlock mallocngIface γ)).interp p oldBlk) = POld
        generalize (MallocngPostEnv mallocngIface γ maddrs tp brkStart _ ivs0 s0 sf) = PPost; ac_rfl)
  · have hOom' := Satisfies.drop_mid hOom
    dsimp only [libcReallocPlacedSpec, withCL, mallocngReallocTightSpec, ToBaseSpec.toSpec] at hOom' ⊢
    rw [satisfies_pure_sepConj] at hOom' ⊢; obtain ⟨hOom1, hR'⟩ := hOom'
    exact ⟨rdlRealloc_tightOom_congr (Nat.le_refl _)
      (by rw [hs1]; rfl) (by rw [hs1]; rfl) (by rw [hs1]; rfl) (by rw [hs1]; rfl) hOom1, hR'⟩

/-- Exported `"realloc"` (`blk13`) at the alignment-indexed tight reserve
    (`mallocngReallocTightBlockSpec`). -/
theorem reallocPlaced_entry_tightBlock_ok
    (hImpl : LibcMallocImplPlacedTightKStmt) (hFree : LibcFreePlacedStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "realloc"
      (mallocngReallocTightBlockSpec svc γ (mallocngAddrsOfPlacement mpl)) := by
  letI : MallocngMultiPlacement := ⟨mpl, svc, hPlace, hSvc⟩
  refine ⟨by decide, 13, 0, by decide +kernel, ?_⟩
  rw [fnAddr_realloc mpl]
  apply withCL_to_withCodeLoaded
  have hfn : ∀ c, (blkPC_b13.rebase c (fun _ => none)).fnAddr "realloc" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase]
    change c + BitVec.ofNat 64 (blkPC_b13.fnOff "realloc") = c
    rw [blkPC_b13_fnOff_0x0]
    exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b13 (hfn (mbase 13)) fun b hb => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, newSize, sp, a, oldBlk, tp, brkStart, bgt, ivs0⟩ R s0 hpc hrun hpre hsp
  rw [hfn b] at hpc
  have _ := hb
  have hpre' : s0.mem ⊨
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ ∗
      ⌜s0.sp = sp ∧ s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
       (OptOwn (MallocngTightInitBlock γ a)).pureWf p oldBlk⌝ ∗
      (stackFrameAt sp 1024 ∗ MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 ∗
       (OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk) ∗ R := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    dsimp only [withCL, mallocngReallocTightBlockSpec, ToBaseSpec.toSpec, CType.CondOwn, mallocngStackBytes]
    generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0) = PEnv
    generalize ((OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk) = POld
    ac_rfl
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcl0, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hspEq, hx0, hx1, hpWf⟩, hpre'⟩ := hpre'
  have hSf1024 : stackFrameAt sp 1024 = (stackFrame s0 800 ∗ stackFrameAt (sp - 800#64) 224) := by
    rw [show (1024 : Nat) = 800 + 224 from rfl, stackFrameAt_split sp 800 224]
    congr 1; unfold stackFrame; rw [hspEq, stackFrameAt_eq_memRegion sp 800]
  rw [hSf1024] at hpre'
  have hpWfA := hpWf
  have hpreA := hpre'
  refine ⟨(stackFrame s0 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
    MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 ∗
    (OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk, hpreA, ?_⟩
  wp_step
  apply sepWP_bind_state; intro s1 hs1
  have hRealloc := call_placed_libcRealloc (placed_libcRealloc_ok hImpl hFree)
    (P := blkPC_b13.rebase b (fun _ => none))
    γ tp brkStart p newSize a oldBlk bgt ivs0 (by intro pc; simp) rfl
  have hEnv1 : MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 =
      MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s1 := by
    unfold MallocngEnv; rw [hs1]; rfl
  have hSf1 : stackFrame s0 800 = stackFrame s1 800 := by unfold stackFrame; rw [hs1]; simp
  rw [hEnv1, hSf1]
  refine SepWP.call_subroutine_frame hRealloc (x := ()) (F := stackFrameAt (sp - 800#64) 224)
    (ret_pc := s0.readReg64 Reg.lr)
    (by rw [hs1]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by rw [hs1]; simp [hrun])
    (by unfold State.spAligned at hsp ⊢; rw [hs1]; simpa using hsp)
    (by rw [hs1]; simp)
    (fun R' hm => by
      have hcl1 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem := by rw [hs1]; exact hcl0
      have hPure1 : s1.readReg64 .x0 = p ∧ s1.readReg64 .x1 = newSize ∧
          (OptOwn (MallocngTightInitBlock γ a)).pureWf p oldBlk :=
        ⟨by rw [hs1]; simpa using hx0, by rw [hs1]; simpa using hx1, hpWfA⟩
      refine Satisfies.mono ?_ hm
      dsimp only [libcReallocPlacedSpec, withCL]
      refine Entails.trans (Entails.pure_right hcl1 (Entails.pure_right hPure1 (Entails.refl _))) ?_
      exact Entails.of_eq (by
        generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s1) = PEnv
        generalize ((OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk) = POld
        ac_rfl))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpcSf hrunSf hspSf hcsSf => ?_)
    (fun R' sf _ hOom => ?_)
  · have hspSf0 : sf.sp = s0.sp := hspSf.trans (by rw [hs1]; simp)
    have hcsSf0 : CalleeSavedPreserved s0 sf := CalleeSavedPreserved.trans (by
      rw [hs1]; exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp [calleeSavedVRegs]⟩) hcsSf
    refine SepWP.done hpcSf hrunSf ⟨fun hm => ?_, hspSf0, hcsSf0⟩
    dsimp only [libcReallocPlacedSpec, withCL] at hm
    have hs1Mem : s1.mem = s0.mem := by rw [hs1]; rfl
    have hAccCongr : ∀ k m, MallocngCallAccounting k m s1 sf → MallocngCallAccounting k m s0 sf := by
      intro k m ⟨hPr, hDl⟩
      exact ⟨mallocngProcPreserved_trans (by rw [hs1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hPr,
        by rwa [hs1Mem] at hDl⟩
    have hPostCongr : ∀ bf', MallocngPostEnv mallocngIface γ maddrs tp brkStart bf' ivs0 s1 sf =
        MallocngPostEnv mallocngIface γ maddrs tp brkStart bf' ivs0 s0 sf := fun bf' => by
      unfold MallocngPostEnv MallocngNoOrphanMappings; rw [hs1Mem]
    have hSfCombine : stackFrame s1 800 ∗ stackFrameAt (sp - 800#64) 224 = stackFrameAt sp 1024 := by
      rw [← hSf1, ← hSf1024]
    rw [hPostCongr] at hm
    dsimp only [withCL, mallocngReallocTightBlockSpec, ToBaseSpec.toSpec, CType.CondOwn, mallocngStackBytes]
    by_cases hLe : newSize.toNat ≤ MallocngMaxAllocSize
    · simp only [decide_eq_true hLe, ↓reduceIte] at hm ⊢
      have hm' : sf.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          ⌜MallocngCallAccounting 16
             (MallocngTightStepBound (mallocngReallocRes a newSize.toNat) bgt.peakCount) s1 sf⌝ ∗
          (∃∗ q : BitVec 64, ⌜sf.readReg64 .x0 = q ∧
             (MallocngTightInitBlock γ a).pureWf q
               (newSize.toNat, ((oldBlk.map Prod.snd).getD []).take newSize.toNat)⌝ ∗
            (MallocngTightInitBlock γ a).interp q
              (newSize.toNat, ((oldBlk.map Prod.snd).getD []).take newSize.toNat)) ∗
          (stackFrame s1 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
          MallocngPostEnv mallocngIface γ maddrs tp brkStart
            (mallocngReallocBudget true oldBlk newSize.toNat bgt) ivs0 s0 sf ∗ R := by
        refine Satisfies.mono (Entails.of_eq ?_) hm; dsimp only [MallocngTightInitBlock]
        generalize (∃∗ q : BitVec 64, _) = PRet
        generalize (MallocngPostEnv mallocngIface γ maddrs tp brkStart _ ivs0 s0 sf) = PPost; ac_rfl
      rw [hSfCombine, satisfies_pure_sepConj] at hm'; obtain ⟨hclSf, hm'⟩ := hm'
      rw [satisfies_pure_sepConj] at hm'; obtain ⟨hAcc1, hm'⟩ := hm'
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm'; obtain ⟨q, hm'⟩ := hm'
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm'; obtain ⟨⟨hx0Q, hWfQ⟩, hm'⟩ := hm'
      have hAcc0 := hAccCongr _ _ hAcc1; rw [← hx0Q] at hWfQ hm'
      have hPurePost : (True : Prop) ∧
          (OptOwn (MallocngTightInitBlock γ a)).pureWf (sf.readReg64 .x0)
            (some (newSize.toNat, ((oldBlk.map Prod.snd).getD []).take newSize.toNat)) ∧
          MallocngCallAccounting 16
            (MallocngTightStepBound (mallocngReallocRes a newSize.toNat) bgt.peakCount) s0 sf :=
        ⟨trivial, ⟨hWfQ.1, hWfQ⟩,
          hAcc0⟩
      refine Satisfies.mono (Entails.trans
        (Entails.pure_right hclSf (Entails.pure_right hPurePost (Entails.refl _))) ?_) hm'
      exact Entails.of_eq (by
        dsimp only [OptOwn, MallocngTightInitBlock]
        generalize (MallocngPostEnv mallocngIface γ maddrs tp brkStart _ ivs0 s0 sf) = PPost
        simp only [emp_sepConj]; ac_rfl)
    · simp only [decide_eq_false hLe, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      have hm' : sf.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          ⌜MallocngCallAccounting 16 (MallocngTightStepBound 0 bgt.peakCount) s1 sf⌝ ∗
          ⌜sf.readReg64 .x0 = 0#64⌝ ∗ (OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk ∗
          (stackFrame s1 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
          MallocngPostEnv mallocngIface γ maddrs tp brkStart
            (mallocngReallocBudget false oldBlk newSize.toNat bgt) ivs0 s0 sf ∗ R := by
        refine Satisfies.mono (Entails.of_eq ?_) hm
        generalize ((OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk) = POld
        generalize (MallocngPostEnv mallocngIface γ maddrs tp brkStart _ ivs0 s0 sf) = PPost; ac_rfl
      rw [hSfCombine, satisfies_pure_sepConj] at hm'; obtain ⟨hclSf, hm'⟩ := hm'
      rw [satisfies_pure_sepConj] at hm'; obtain ⟨hAcc1, hm'⟩ := hm'
      have hPurePost : (OptOwn (MallocngTightInitBlock γ a)).pureWf p oldBlk ∧
          (OptOwn (MallocngTightInitBlock γ a)).pureWf (sf.readReg64 .x0) none ∧
          MallocngCallAccounting 16 (MallocngTightStepBound 0 bgt.peakCount) s0 sf :=
        ⟨hpWf, trivial, hAccCongr _ _ hAcc1⟩
      refine Satisfies.mono (Entails.trans
        (Entails.pure_right hclSf (Entails.pure_right hPurePost (Entails.refl _))) ?_) hm'
      exact Entails.of_eq (by
        dsimp only [OptOwn]
        generalize ((OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk) = POld
        generalize (MallocngPostEnv mallocngIface γ maddrs tp brkStart _ ivs0 s0 sf) = PPost; ac_rfl)
  · have hOom' := Satisfies.drop_mid hOom
    dsimp only [libcReallocPlacedSpec, withCL, mallocngReallocTightBlockSpec, ToBaseSpec.toSpec] at hOom' ⊢
    rw [satisfies_pure_sepConj] at hOom' ⊢; obtain ⟨hOom1, hR'⟩ := hOom'
    exact ⟨rdlRealloc_tightOom_congr (Nat.le_refl _)
      (by rw [hs1]; rfl) (by rw [hs1]; rfl) (by rw [hs1]; rfl) (by rw [hs1]; rfl) hOom1, hR'⟩

/-- Exported `"realloc"` (`blk13`, 1-instruction `b __libc_realloc` tail-call). -/
theorem reallocPlaced_entry_ok
    (hImpl : LibcMallocImplPlacedTightKStmt) (hFree : LibcFreePlacedStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "realloc"
      (mallocngReallocSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ :=
    reallocPlaced_entry_tight_ok hImpl hFree mpl svc hPlace hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_mono hsub (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)
    (hoom := fun _ _ _ _ ho => ?_)⟩
  dsimp only [MultiPlacedLib.withCodeLoaded, mallocngReallocTightSpec, mallocngReallocSpec,
    ToBaseSpec.toSpec] at ho ⊢
  rw [satisfies_pure_sepConj] at ho ⊢
  exact ⟨ho.1.to_oomCond (by split <;> omega), ho.2⟩

end VerifiedLibraries.Mallocng.Proofs
