/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.PlacedNontrivialFreeStage6
import VerifiedLibraries.Mallocng.Proofs.PlacedLibcFreeHelpers

/-!
# Placed Proof for `nontrivial_free`

Fuel-indexed (`fuel <= 6`) verification of `nontrivial_free` (`blk05`, `blk05_nontrivialFree_fuel`)
across non-all-free exits, active-queue classification, root retirement, and nested self-recursive
retirement, culminating in `placed_nontrivialFree_ok` and `placed_nontrivialFree_keep_ok`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.ProgramReflection VerifiedLibraries.Mallocng

/-! ## Prologue Bitfield and Stack Unpack Lemmas -/

private theorem unpack_nfStack (sp0 : BitVec 64) (fuel : Nat) (hFuel : fuel ≤ 6) :
    stackFrameAt sp0 (32 * (fuel + 1)) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        stackFrameAt (sp0 - 32#64) (32 * fuel) ∗
        ((sp0 - 32#64) ↦₆₄ w0) ∗ ((sp0 - 24#64) ↦₆₄ w1) ∗
        ((sp0 - 16#64) ↦₆₄ w2) ∗ ((sp0 - 8#64) ↦₆₄ w3) := by
  rw [stackFrameAt_succ_split sp0 fuel hFuel]; cells_unfold; exact Entails.refl _

private theorem prologue_packedWord_props (g : GroupDesc) (hLast : g.lastIdx ≤ 31) (hSc : g.sc < 64) :
    ((g.packedWord.truncate 8).zeroExtend 32) &&& 0x1f#32 = BitVec.ofNat 32 g.lastIdx ∧
    ((g.packedWord.truncate 8).zeroExtend 64) &&& 0x1f#64 = BitVec.ofNat 64 g.lastIdx ∧
    (((g.packedWord.truncate 16).zeroExtend 64) >>> 6) &&& 0x3f#64 = BitVec.ofNat 64 g.sc := by
  unfold GroupDesc.packedWord
  have h1 :
      ∀ a b c : BitVec 64,
        (((((a &&& 0x1f#64) ||| (1#64 <<< 5) ||| ((b &&& 0x3f#64) <<< 6) ||| (c <<< 12)).truncate 8).zeroExtend 32) &&&
          0x1f#32) = (a &&& 0x1f#64).truncate 32 := by
    intro a b c; bv_robdd
  have h2 :
      ∀ a b c : BitVec 64,
        (((((a &&& 0x1f#64) ||| (1#64 <<< 5) ||| ((b &&& 0x3f#64) <<< 6) ||| (c <<< 12)).truncate 8).zeroExtend 64) &&&
          0x1f#64) = a &&& 0x1f#64 := by
    intro a b c; bv_robdd
  have h3 :
      ∀ a b c : BitVec 64,
        ((((((a &&& 0x1f#64) ||| (1#64 <<< 5) ||| ((b &&& 0x3f#64) <<< 6) ||| (c <<< 12)).truncate 16).zeroExtend 64) >>> 6) &&&
          0x3f#64) = b &&& 0x3f#64 := by
    intro a b c; bv_robdd
  rw [h1, h2, h3]
  have hL : (BitVec.ofNat 64 g.lastIdx).ult 32#64 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change g.lastIdx % 2 ^ 64 < 32; omega
  have hS : (BitVec.ofNat 64 g.sc).ult 64#64 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change g.sc % 2 ^ 64 < 64; omega
  rw [show BitVec.ofNat 32 g.lastIdx = (BitVec.ofNat 64 g.lastIdx).truncate 32 by bv_omega]
  exact ⟨by revert hL; bv_robdd, by revert hL; bv_robdd, by revert hS; bv_robdd⟩

private theorem lsl32_fin :
    ∀ k : Fin 32,
      (BitVec.ofNat 64 k.val).truncate 32 = BitVec.ofNat 32 k.val ∧
      (1#32 <<< ((BitVec.ofNat 32 k.val).toNat % 32)) = 1#32 <<< k.val ∧
      (1#32 <<< ((BitVec.ofNat 32 k.val % 32#32).toNat)) = 1#32 <<< k.val ∧
      (1#32 <<< ((BitVec.ofNat 32 k.val &&& 31#32).toNat)) = 1#32 <<< k.val ∧
      (2#32 <<< ((BitVec.ofNat 32 k.val).toNat % 32)) = 2#32 <<< k.val ∧
      (2#32 <<< ((BitVec.ofNat 32 k.val % 32#32).toNat)) = 2#32 <<< k.val ∧
      (2#32 <<< ((BitVec.ofNat 32 k.val &&& 31#32).toNat)) = 2#32 <<< k.val := by
  decide

private theorem groupNestBound_pos_of_maplen_zero {g : GroupDesc} (hMap0 : g.maplen = 0) :
    1 ≤ groupNestBound g := by
  unfold groupNestBound
  simp only [hMap0, Nat.lt_irrefl, ↓reduceIte]
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals omega

/-! ## Fuel Induction for `nontrivial_free` -/

set_option maxHeartbeats 800000 in
private theorem blk05_nontrivialFree_body [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    (hBound : groupNestBound g ≤ fuel)
    (hKeep : EmptyGroupKeepWf st) (hFull : FullQueueKeepWf st)
    (hNested : g.maplen = 0 →
      ∃ fuel', fuel = fuel' + 1 ∧
        ∀ (st1 : MallocngSt) (pg1 : GroupDesc) (pIdx : Nat),
          groupNestBound pg1 ≤ fuel' → EmptyGroupKeepWf st1 → FullQueueKeepWf st1 →
          subroutine_ok (blkPC_b05.rebase b (fun _ => none)) b
            (nontrivialFreeFuelPlainSpec (k + 1) fuel' γ brkStart bud st1 pg1 pIdx)) :
    subroutine_ok (blkPC_b05.rebase b (fun _ => none)) b
      (nontrivialFreeFuelPlainSpec k fuel γ brkStart bud st g idx) := by
  have _ := hb
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre hspAl0
  have hpre1 : s0.mem ⊨
      ⌜s0.readReg64 .x0 = g.metaPtr ∧
       s0.readReg64 .x1 = BitVec.ofNat 64 idx ∧
       g ∈ st.groups ∧
       ∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .claimed⌝ ∗
      (MallocngCoreStInflightA (k + 1) γ maddrs brkStart s0.brk bud.liveCost bud.peakCost st ∗
       stackFrameAt s0.sp (32 * (fuel + 1)) ∗
       MallocngRoTablesA maddrs ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [nontrivialFreeFuelPlainSpec]
    refine Entails.trans (Entails.of_eq (sepConj_assoc _ _ _)) ?_
    refine sepConj_mono_right ?_
    sep_frame
  rw [satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨hx0, hx1, hg, hIdx, hClaimed⟩, hpre2⟩ := hpre1
  have hpreSpatial : s0.mem ⊨
      ⌜MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st⌝ ∗
      ((stackFrameAt s0.sp (32 * (fuel + 1)) ∗
        MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st ∗
        (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st)) ∗ R) := by
    refine Satisfies.mono ?_ hpre2
    rw [coreStInflightA_eq_nfParts]
    refine Entails.trans (Entails.of_eq (sepConj_assoc _ _ _)) ?_
    refine sepConj_mono_right ?_
    sep_frame
  rw [satisfies_pure_sepConj] at hpreSpatial
  obtain ⟨hwf, hpreSpatial⟩ := hpreSpatial
  refine ⟨_, hpreSpatial, ?_⟩
  refine SepWP.mono (post := NfFuelPost k fuel γ brkStart bud st s0) ?_
    (fun sf P_f _ _ ⟨hEnt, hspF, hcsF⟩ =>
      ⟨fun hm => Satisfies.mono (sepConj_mono_left hEnt) hm, hspF, hcsF⟩)
  refine SepWP.weaken_pre (sepConj_mono_left (unpack_nfStack s0.sp fuel hFuel)) ?_
  refine SepWP.of_sepExists_left fun w0 => ?_
  refine SepWP.of_sepExists_left fun w1 => ?_
  refine SepWP.of_sepExists_left fun w2 => ?_
  refine SepWP.of_sepExists_left fun w3 => ?_
  have hLast31 : g.lastIdx ≤ 31 := (hwf.groups_wf g hg).2.1
  have hIdx31 : idx ≤ 31 := by
    have := (hwf.groups_wf g hg).2.2.1; unfold GroupDesc.cnt at this; omega
  have hSc64 : g.sc < 64 := by rcases (hwf.groups_wf g hg).1 with h | h <;> omega
  obtain ⟨hPwLow32, hPwLow64, hPwSc64⟩ := prologue_packedWord_props g hLast31 hSc64
  have hLslIdx := lsl32_fin ⟨idx, by omega⟩
  have hLslLast := lsl32_fin ⟨g.lastIdx, by omega⟩
  dsimp only at hLslIdx hLslLast
  obtain ⟨_, _, _, hReadG, hOwnG⟩ := meta_ownedRw_of_mem_groups hwf hg
  apply step_stp64_perm_kf (pc := b) (ea := s0.sp - 32#64) (ea2 := s0.sp - 24#64)
    (v1 := s0.readReg64 .x29) (v2 := s0.readReg64 .x30)
  · exact hpc
  · exact hrun
  · wp_close_fetch_cl
  · simpa only [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, arm64_norm] using hspAl0
  · simp only [evalAddrMode, arm64_norm]
    exact Prod.ext (by bv_arith) (congrArg some (Prod.ext rfl (by bv_arith)))
  · bv_arith
  · rfl
  · rfl
  · wp_sep_access_fast
  · wp_sep_access_fast
  · rfl
  intro m1 hm1 _
  wp_step
  wp_step
  apply step_stp64_perm_kf (pc := b + 0xc#64) (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64)
    (v1 := s0.readReg64 .x19) (v2 := s0.readReg64 .x20)
  · simp only [arm64_norm]
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · simpa only [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, arm64_norm] using hspAl0
  · simp only [evalAddrMode, arm64_norm]
    exact Prod.ext (by dsimp only; bv_arith) rfl
  · bv_arith
  · simp only [arm64_norm]
  · simp only [arm64_norm]
  · wp_sep_access_fast
  · wp_sep_access_fast
  · rfl
  intro m2 hm2 _
  wp_step
  wp_step
  wp_step
  have hBmG0 := (byteMap_update40 hwf.masterDom_wf.1 st.byteVal (P := OwnedRwByte st)
    (m := g.metaPtr) (bs := g.metaBytes) (GroupDesc.metaBytes_length _) hOwnG).1
  rw [hBmG0, hReadG, metaBytes_eq_cells g]
  apply step_ldr8_64_fast (b + 0x1c#64) (b + 0x20#64) (g.metaPtr + 32#64) g.packedWord
  · simp only [arm64_norm]
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm]
  · wp_sep_access_fast
  · bv_omega
  apply step_ldr32_fast (b + 0x20#64) (b + 0x24#64) (g.metaPtr + 28#64) g.freedMask
  · rfl
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm]
  · wp_sep_access_fast
  · bv_omega
  apply step_ldr32_fast (b + 0x24#64) (b + 0x28#64) (g.metaPtr + 24#64) g.availMask
  · rfl
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm]
  · wp_sep_access_fast
  · bv_omega
  wp_step
  obtain ⟨R16, hS16⟩ := pointsTo64_focus16 (g.metaPtr + 32#64) g.packedWord
  rw [hS16]
  apply step_ldr16_fast (b + 0x2c#64) (b + 0x30#64)
    (g.metaPtr + 32#64) (g.packedWord.truncate 16)
  · simp only [arm64_norm]
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm]
  · wp_sep_access_fast
  · bv_omega
  rw [← hS16, ← metaBytes_eq_cells g, ← hReadG, ← hBmG0]
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  have hAnd31_32 : ∀ v : BitVec 8,
      BitVec.truncate 32 (BitVec.zeroExtend 64 v &&& 0x1f0000001f#64) =
      BitVec.zeroExtend 32 v &&& 31#32 := by decide
  have hLastMod : g.lastIdx % 32 = g.lastIdx := Nat.mod_eq_of_lt (by omega)
  wp_if_nd hAllFreeBr
  ·
    have hAllFree : (g.availMask ||| g.freedMask) + (1#32 <<< idx) = (2#32 <<< g.lastIdx) - 1#32 := by
      simp [arm64_norm, hPwLow64, hLastMod,
        hLslLast.1] at hAllFreeBr
      rw [BitVec.add_comm, BitVec.or_comm]
      exact hAllFreeBr
    refine SepWP.weaken_pre ?_ (sepWP_nf_allFree_to_1d4 hb hFuel
      (s0 := s0) (idx := idx)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (by simp [arm64_norm, BitVec.or_comm])
      (by simpa [arm64_norm, hAnd31_32] using hPwLow32)
      (by simp [arm64_norm])
      (by simp [arm64_norm]) hspAl0
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (by simp [arm64_norm]) (hm2.trans hm1)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      hwf hKeep hg hIdx hClaimed ?_)
    · dsimp only [NfAllFreeFrame, nfStackSaved]
      sep_frame
    · intro active1 usage1 actLists1 gsDeq bvDeq sDeq hDeq hpcD hrunD hx0D hx19D hspD hbrkD hpermD hProcD hcsD
      have hspD' : sDeq.sp = s0.sp - 32#64 := hspD.trans (by simp [arm64_norm])
      have hbrkD' : sDeq.brk = s0.brk := hbrkD.trans (by simp [arm64_norm])
      have hpermD' : sDeq.mem.perm = s0.mem.perm := hpermD.trans (hm2.trans hm1)
      by_cases hMpPos : 0 < g.maplen
      · exact sepWP_nf_retire_root hb hFuel hpcD hrunD hx0D hx19D hspD' hspAl0
          hProcD hbrkD' hpermD' hcsD hwf hg hIdx hClaimed hAllFree hMpPos hDeq
      · have hMap0 : g.maplen = 0 := by omega
        obtain ⟨fuel', hFuelEq, hRec⟩ := hNested hMap0
        subst hFuelEq
        exact sepWP_nf_retire_nested hb hFuel hpcD hrunD hx19D hspD' hspAl0
          hProcD hbrkD' hpermD' hcsD hwf hKeep hFull hg hIdx hClaimed hAllFree hMap0 hBound hDeq hRec
  ·
    have hNotAll : (g.availMask ||| g.freedMask) + (1#32 <<< idx) ≠ (2#32 <<< g.lastIdx) - 1#32 := by
      intro hEq
      apply hAllFreeBr
      simp [arm64_norm, hPwLow64, hLastMod,
        hLslLast.1]
      rw [BitVec.add_comm, BitVec.or_comm]
      exact hEq
    refine SepWP.weaken_pre ?_ (sepWP_nf_nonAllFree hb hFuel
      (s0 := s0) (idx := idx)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (by simp [arm64_norm]) hspAl0
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (by simp [arm64_norm]) (hm2.trans hm1)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      hwf hFull hg hIdx hClaimed hNotAll)
    dsimp only [nfStackSaved]
    sep_frame

theorem blk05_nontrivialFree_fuel [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) (fuel : Nat) (hFuel : fuel ≤ 6)
    (k : Nat) (γ : GhostName) (brkStart : BitVec 64) (bud : MallocngBudget)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat)
    (hBound : groupNestBound g ≤ fuel)
    (hKeep : EmptyGroupKeepWf st) (hFull : FullQueueKeepWf st) :
    subroutine_ok (blkPC_b05.rebase b (fun _ => none)) b
      (nontrivialFreeFuelPlainSpec k fuel γ brkStart bud st g idx) := by
  induction fuel generalizing k st g idx with
  | zero =>
    refine blk05_nontrivialFree_body hb hFuel hBound hKeep hFull fun hMap0 => ?_
    have hGe1 := groupNestBound_pos_of_maplen_zero hMap0
    omega
  | succ fuel' ih =>
    refine blk05_nontrivialFree_body hb hFuel hBound hKeep hFull fun _ =>
      ⟨fuel', rfl, fun st1 pg1 pIdx hB1 hK1 hF1 =>
        ih (by omega) (k + 1) st1 pg1 pIdx hB1 hK1 hF1⟩

/-! ## Top-Level Placed Soundness -/

theorem placed_nontrivialFree_ok : NontrivialFreeTopPlacedStmt := by
  intro _ γ brkStart b st g idx
  unfold nontrivialFreeTopPlacedSpec
  refine subroutine_ok_withCL_of_cl fun m0 _hcl0 => ?_
  rw [mallocngBlockProg_eq_b05]
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre hspAl0
  let fuel := groupNestBound g
  have hFuel : fuel ≤ 6 := groupNestBound_le_six g
  have hb5 : BlkBase 5 (mbase 5) := rfl
  have hSp224 :
      stackFrame s0 224 =
        (memRegion (s0.sp - 224#64) (224 - 32 * (fuel + 1)) ∗ stackFrameAt s0.sp (32 * (fuel + 1))) := by
    unfold stackFrame
    rw [← stackFrameAt_eq_memRegion s0.sp 224]
    exact stack224_split_fuel s0.sp fuel hFuel
  have hpre' : s0.mem ⊨
      ((nontrivialFreeFuelPlainSpec 0 fuel γ brkStart b st g idx).pre () s0 ∗
       memRegion (s0.sp - 224#64) (224 - 32 * (fuel + 1))) ∗ R := by
    refine Satisfies.mono ?_ hpre
    dsimp only [nontrivialFreeFuelPlainSpec]
    rw [hSp224]
    try rw [sepConj_assoc]
    refine Entails.pure_left fun _ => ?_
    try rw [sepConj_assoc]
    refine Entails.pure_left fun hp => ?_
    rw [pure_sepConj_of_true hp]
    sep_frame
  have hwf : MallocngWFInflight 1 maddrs.base brkStart s0.brk b.liveCost b.peakCost st := by
    have h1 : s0.mem ⊨
        ⌜MallocngWFInflight (0 + 1) maddrs.base brkStart s0.brk b.liveCost b.peakCost st⌝ ∗
        ((⌜s0.readReg64 .x0 = g.metaPtr ∧ s0.readReg64 .x1 = BitVec.ofNat 64 idx ∧
           g ∈ st.groups ∧ ∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .claimed⌝ ∗
          stackFrameAt s0.sp (32 * (fuel + 1)) ∗ MallocngRoTablesA maddrs ∗
          NfStaticRest γ maddrs st ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st) ∗
          memRegion (s0.sp - 224#64) (224 - 32 * (fuel + 1))) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by
        dsimp only [nontrivialFreeFuelPlainSpec]
        rw [coreStInflightA_eq_nfParts]
        ac_rfl)) hpre'
    rw [satisfies_pure_sepConj] at h1
    exact h1.1
  have hSub := blk05_nontrivialFree_fuel hb5 fuel hFuel 0 γ brkStart b st g idx (Nat.le_refl _)
    (emptyGroupKeepWf_of_wf hwf) trivial
  refine ⟨_, hpre', ?_⟩
  refine SepWP.call_subroutine_frame (x := ()) (ret_pc := s0.readReg64 .lr)
    (F := memRegion (s0.sp - 224#64) (224 - 32 * (fuel + 1)))
    hSub hpc hrun hspAl0 rfl
    (fun R' hm => by rwa [sepConj_assoc] at hm)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpcF hrunF hspF hcsF => ?_)
    (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  refine SepWP.done hpcF hrunF ⟨fun hm => ?_, hspF, hcsF⟩
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [nontrivialFreeFuelPlainSpec, NfRetSep, MallocngCoreStA]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_mono fun st' => ?_
  try rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hProc, hBrk, hTp, hPerm, _, hMa, hCnt, hDynLen, hGrp⟩ => ?_
  have hDelta : MallocngMappedDelta 0 0 s0.mem sf.mem :=
    ⟨[], by decide, by decide, fun a ha => Or.inl (by rwa [← hPerm])⟩
  have hMaLe : st'.metaAreas.length ≤ st.metaAreas.length := by rw [hMa]; exact Nat.le_refl _
  refine Entails.pure_right ⟨hProc, hBrk, hTp, hPerm, hDelta, hCnt, hDynLen, hMaLe, hGrp⟩ ?_
  rw [hSp224]
  sep_frame

theorem placed_nontrivialFree_keep_ok [MallocngMultiPlacement]
    (γ : GhostName) (brkStart : BitVec 64) (b : MallocngBudget)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat) :
    EmptyGroupKeepWf st → FullQueueKeepWf st →
    subroutine_ok (mallocngBlockProg mmpl 5 msvc) (mbase 5)
      (nontrivialFreeTopPlacedSpec γ brkStart b st g idx) :=
  fun _ _ => placed_nontrivialFree_ok γ brkStart b st g idx

end VerifiedLibraries.Mallocng.Proofs
