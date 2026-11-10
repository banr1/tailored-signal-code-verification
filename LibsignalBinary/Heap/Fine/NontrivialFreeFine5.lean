/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.NontrivialFreeFine4
public import LibsignalBinary.Heap.Fine.VendorFree.PlacedNontrivialFreeProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedLibcFreeHelpers

/-!
# Fine-Grained Placed `nontrivial_free` Top-Level Verification

Fuel-indexed (`fuel ≤ 6`) entry-to-exit verification of `nontrivial_free` (`blk05`, 224-byte stack)
preserving `SameLiveUserSub st' st`, exporting `placed_nontrivialFree_fine_ok` and
`call_placed_nontrivialFree_fine`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.ProgramReflection
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open LibsignalBinary.Heap.Fine.VendorFree
open scoped LibsignalBinary.Heap.Fine.VendorFree

/-! ## Prologue Bitvector and Nesting-Bound Helpers -/

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

/-! ## Fuel-Indexed Entry-to-Exit Verification -/

set_option maxHeartbeats 800000 in
theorem blk05_nontrivialFree_body_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    (hBound : groupNestBound g ≤ fuel)
    (hKeep : EmptyGroupKeepWf st) (hFull : FullQueueKeepWf st)
    (hNested : g.maplen = 0 →
      ∃ fuel', fuel = fuel' + 1 ∧
        ∀ (st1 : MallocngSt) (pg1 : GroupDesc) (pIdx : Nat),
          groupNestBound pg1 ≤ fuel' → EmptyGroupKeepWf st1 → FullQueueKeepWf st1 →
          subroutine_ok (blkPC_b05.rebase b (fun _ => none)) b
            (nontrivialFreeFuelFinePlainSpec (k + 1) fuel' γ brkStart liveCost peakCost st1 pg1 pIdx)) :
    subroutine_ok (blkPC_b05.rebase b (fun _ => none)) b
      (nontrivialFreeFuelFinePlainSpec k fuel γ brkStart liveCost peakCost st g idx) := by
  have _ := hb
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre hspAl0
  have hpre1 : s0.mem ⊨
      ⌜s0.readReg64 .x0 = g.metaPtr ∧
       s0.readReg64 .x1 = BitVec.ofNat 64 idx ∧
       g ∈ st.groups ∧
       ∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .claimed⌝ ∗
      (MallocngCoreStInflightA (k + 1) γ maddrs brkStart s0.brk liveCost peakCost st ∗
       stackFrameAt s0.sp (32 * (fuel + 1)) ∗
       MallocngRoTablesA maddrs ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [nontrivialFreeFuelFinePlainSpec]
    refine Entails.trans (Entails.of_eq (sepConj_assoc _ _ _)) ?_
    refine sepConj_mono_right ?_
    sep_frame
  rw [satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨hx0, hx1, hg, hIdx, hClaimed⟩, hpre2⟩ := hpre1
  have hpreSpatial : s0.mem ⊨
      ⌜MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk liveCost peakCost st⌝ ∗
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
  refine SepWP.mono (post := NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) ?_
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
      simp [arm64_norm, hPwLow64, hLastMod, hLslLast.1] at hAllFreeBr
      rw [BitVec.add_comm, BitVec.or_comm]
      exact hAllFreeBr
    refine SepWP.weaken_pre ?_ (sepWP_nf_allFree_to_1d4_fine hb hFuel
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
      · exact sepWP_nf_retire_root_fine hb hFuel hpcD hrunD hx0D hx19D hspD' hspAl0
          hProcD hbrkD' hpermD' hcsD hwf hg hIdx hClaimed hAllFree hMpPos hDeq
      · have hMap0 : g.maplen = 0 := by omega
        obtain ⟨fuel', hFuelEq, hRec⟩ := hNested hMap0
        subst hFuelEq
        exact sepWP_nf_retire_nested_fine hb hFuel hpcD hrunD hx19D hspD' hspAl0
          hProcD hbrkD' hpermD' hcsD hwf hKeep hFull hg hIdx hClaimed hAllFree hMap0 hBound hDeq hRec
  ·
    have hNotAll : (g.availMask ||| g.freedMask) + (1#32 <<< idx) ≠ (2#32 <<< g.lastIdx) - 1#32 := by
      intro hEq
      apply hAllFreeBr
      simp [arm64_norm, hPwLow64, hLastMod, hLslLast.1]
      rw [BitVec.add_comm, BitVec.or_comm]
      exact hEq
    refine SepWP.weaken_pre ?_ (sepWP_nf_nonAllFree_fine hb hFuel
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

theorem blk05_nontrivialFree_fuel_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) (fuel : Nat) (hFuel : fuel ≤ 6)
    (k : Nat) (γ : GhostName) (brkStart : BitVec 64) (liveCost peakCost : Nat)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat)
    (hBound : groupNestBound g ≤ fuel)
    (hKeep : EmptyGroupKeepWf st) (hFull : FullQueueKeepWf st) :
    subroutine_ok (blkPC_b05.rebase b (fun _ => none)) b
      (nontrivialFreeFuelFinePlainSpec k fuel γ brkStart liveCost peakCost st g idx) := by
  induction fuel generalizing k st g idx with
  | zero =>
    refine blk05_nontrivialFree_body_fine hb hFuel hBound hKeep hFull fun hMap0 => ?_
    have hGe1 := groupNestBound_pos_of_maplen_zero hMap0
    omega
  | succ fuel' ih =>
    refine blk05_nontrivialFree_body_fine hb hFuel hBound hKeep hFull fun _ =>
      ⟨fuel', rfl, fun st1 pg1 pIdx hB1 hK1 hF1 =>
        ih (by omega) (k + 1) st1 pg1 pIdx hB1 hK1 hF1⟩

/-! ## Placed `nontrivial_free` Contract -/

noncomputable def nontrivialFreeFinePlacedSpec [MallocngMultiPlacement]
    (γ : GhostName) (brkStart : BitVec 64) (liveCost peakCost : Nat)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat) : Spec Unit :=
  { pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = g.metaPtr ∧
       s0.readReg64 .x1 = BitVec.ofNat 64 idx ∧
       g ∈ st.groups ∧
       ∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .claimed⌝ ∗
      stackFrame s0 224 ∗
      MallocngRoTablesA maddrs ∗
      MallocngCoreStInflightA 1 γ maddrs brkStart s0.brk liveCost peakCost st
    post := fun (_ : Unit) s0 sf =>
      ∃∗ st' : MallocngSt,
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         SameLiveUserSub st' st ∧
         totalLiveCount st' ≤ totalLiveCount st ∧
         (dynamicRootRegions st').length ≤ (dynamicRootRegions st).length⌝ ∗
        stackFrame s0 224 ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStA γ maddrs brkStart s0.brk liveCost peakCost st' ∗
        VendorFree.NfRetSep st st' (sf.readReg64 .x0) (sf.readReg64 .x1) }

theorem placed_nontrivialFree_fine_ok [MallocngMultiPlacement]
    (γ : GhostName) (brkStart : BitVec 64) (liveCost peakCost : Nat)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat) :
    subroutine_ok (mallocngBlockProg mmpl 5 msvc) (mbase 5)
      (withCL mmpl (nontrivialFreeFinePlacedSpec γ brkStart liveCost peakCost st g idx)) := by
  unfold nontrivialFreeFinePlacedSpec
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
      ((nontrivialFreeFuelFinePlainSpec 0 fuel γ brkStart liveCost peakCost st g idx).pre () s0 ∗
       memRegion (s0.sp - 224#64) (224 - 32 * (fuel + 1))) ∗ R := by
    refine Satisfies.mono ?_ hpre
    dsimp only [nontrivialFreeFuelFinePlainSpec]
    rw [hSp224]
    try rw [sepConj_assoc]
    refine Entails.pure_left fun _ => ?_
    try rw [sepConj_assoc]
    refine Entails.pure_left fun hp => ?_
    rw [pure_sepConj_of_true hp]
    sep_frame
  have hwf : MallocngWFInflight 1 maddrs.base brkStart s0.brk liveCost peakCost st := by
    have h1 : s0.mem ⊨
        ⌜MallocngWFInflight (0 + 1) maddrs.base brkStart s0.brk liveCost peakCost st⌝ ∗
        ((⌜s0.readReg64 .x0 = g.metaPtr ∧ s0.readReg64 .x1 = BitVec.ofNat 64 idx ∧
           g ∈ st.groups ∧ ∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .claimed⌝ ∗
          stackFrameAt s0.sp (32 * (fuel + 1)) ∗ MallocngRoTablesA maddrs ∗
          NfStaticRest γ maddrs st ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st) ∗
          memRegion (s0.sp - 224#64) (224 - 32 * (fuel + 1))) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by
        dsimp only [nontrivialFreeFuelFinePlainSpec]
        rw [coreStInflightA_eq_nfParts]
        ac_rfl)) hpre'
    rw [satisfies_pure_sepConj] at h1
    exact h1.1
  have hSub := blk05_nontrivialFree_fuel_fine hb5 fuel hFuel 0 γ brkStart liveCost peakCost st g idx
    (Nat.le_refl _) (emptyGroupKeepWf_of_wf hwf) trivial
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
  dsimp only [nontrivialFreeFuelFinePlainSpec, MallocngCoreStA]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_mono fun st' => ?_
  try rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hProc, hBrk, hTp, hPerm, _, _hMa, hSubSt, hCnt, hDynLen⟩ => ?_
  have hDelta : MallocngMappedDelta 0 0 s0.mem sf.mem :=
    ⟨[], by decide, by decide, fun a ha => Or.inl (by rwa [← hPerm])⟩
  refine Entails.pure_right ⟨hProc, hBrk, hTp, hPerm, hDelta, hSubSt, hCnt, hDynLen⟩ ?_
  rw [hSp224]
  sep_frame

theorem call_placed_nontrivialFree_fine [MallocngMultiPlacement]
    {P : Program} (γ : GhostName) (brkStart : BitVec 64) (liveCost peakCost : Nat)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 5)
      (withCL mmpl (nontrivialFreeFinePlacedSpec γ brkStart liveCost peakCost st g idx)) :=
  subroutine_ok_block_to_block (j := 5) (by decide)
    (placed_nontrivialFree_fine_ok γ brkStart liveCost peakCost st g idx) hext hsvc

end LibsignalBinary.Heap.Fine
