/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.LoopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `bsearchReplace` and `bsearchPush` for `<PolyDecoder as Decoder>::add_chunk`

Relocatable `[LibsignalPlacement]` proofs of `bsearchReplace` (`+236 → +64`) and `bsearchPush`
(`+128 → +64`) on Block `419` threading `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification (LibsignalPlacement blkPC_419 blkPl_419 lsmpl)
open CryptoVerification.LibsignalSpqrV1 (Pt SortedSetPt)
open CryptoVerification.LibsignalTripleRatchet (sessionMemmoveSpec)
open CryptoVerification.SpqrV1.Alloc (growOneStack spqrMemmoveSym)
open CryptoVerification.SpqrV1.Poly (ptAt ptSliceAt sortedSetPtOf)
open CryptoVerification.SpqrV1.Poly.AddChunk (
  bsearchLoop bsearchLoop_bounds bsearchPush bsearchReplace
  bv32_bne_zeroExtend16 bv32_ule_zeroExtend16 bv64_beq_cap_ofNat
  bv64_lsl2_ofNat bv64_ne_zero_of_pos bv64_ule_succ cinc_insertIdx_eq
  dropLast_append_singleton_eq_set memRegion_spare_split_one
  ptr_add_len_sub2 ptr_add_len_sub4 ptSliceAt_focus
  reassemble_sortedSetPtOf_set reassemble_sortedSetPtOf_snoc
  sortedSetPtGrownAt sortedSetPtOf_expose
)
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm (
  calleeSavedVRegs_setMem_setPC_pre calleeSavedVRegs_setPC_pre
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv
  FitsEvents RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (
  growOnePtFullSpec growOnePtSpec
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (
  allocCallPreserved_trans withAllocVmPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (
  AddChunkSlotEnv growOnePtEvents
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.LoopPlacedBudget (
  bsearch_insert_at_336_acp_placed_sepWP bsearch_insert_at_452_acp_placed_sepWP
  bsearch_push_empty_at_216_placed_sepWP bsearch_to_296_placed_sepWP
  call_grow_one_pt_empty_acp_placed_wpp call_grow_one_pt_full_acp_placed_wpp
  withAllocCallPreserved
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  calleeSavedVRegs_setPC_pre calleeSavedVRegs_setMem_setPC_pre

private theorem align_pre_vm {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (h : P ⊢ P') (hwp : SepWP prog target s P' post) :
    SepWP prog target s P post :=
  SepWP.weaken_pre h hwp

theorem sepWP_with_vm {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → post sm Pm))) :
    SepWP (P.rebase b Hk) target_pc s Pre post :=
  SepWP.mono hwp fun _ _ _ _ ⟨hvm, hf⟩ => hf hvm

theorem sepWP_seq_with_vm {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (VmPreserved s sm → SepWP (P.rebase b Hk) target_pc sm Pm post))) :
    SepWP (P.rebase b Hk) target_pc s Pre post :=
  SepWP.seq hwp fun _ _ _ _ ⟨hvm, hf⟩ => hf hvm

/-! ## Placed `bsearchReplace` (`+236 -> +64`) -/

theorem bsearchReplace_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtFullSpec M A lim)))
    {target_pc : BitVec 64} {s0 st : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (v cap ptr : BitVec 64) (s : SortedSetPt) (pt : Pt) (curSt : M.σ)
    (h1 : 1 ≤ s.vec.length) (hlen : s.vec.length ≤ 65536)
    (hle_cap : s.vec.length ≤ cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (hfits : FitsEnv M lim curSt (AddChunkSlotEnv s))
    (hpc : st.pc = (blkPl_419).base + 236#64)
    (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true)
    (htr : st.trace = s0.trace)
    (hx8 : st.readReg64 .x8 = ptr)
    (hx14 : st.readReg64 .x14 = 1#64)
    (hx21 : st.readReg64 .x21 = v)
    (hx24 : st.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx27 : st.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : st.readReg64 .x28 = BitVec.ofNat 64 s.vec.length)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      AddChunkSlotEnv s evs →
      sf.pc = (blkPl_419).base + 64#64 →
      sf.status = .Running →
      AllocCallPreserved st sf →
      sf.sp = st.sp →
      sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 →
      sf.readReg64 .x19 = st.readReg64 .x19 →
      sf.readReg64 .x20 = st.readReg64 .x20 →
      sf.readReg64 .x23 = st.readReg64 .x23 →
      sf.readReg64 .x24 = st.readReg64 .x24 →
      sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x29 = st.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtOf A.repAlloc v (bsearchReplace s pt) ∗
          A.pool lim (M.stepEvents evs curSt) sf ∗ stackAt st.sp growOneStack ∗ F)
        Q Qp) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc st
      (ptSliceAt ptr s.vec ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗
        memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
        A.pool lim curSt st ∗ stackAt st.sp growOneStack ∗ F)
      Q Qp := by
  apply SepWPp.of_sepWP (mid := (blkPl_419).base + 296#64)
  refine bsearch_to_296_placed_sepWP h1 (by omega) st _ _ hpc hrun hx8 hx24 hx28
    (fun s1 hpc1 hrun1 hvm1 hacp1 hsp1 htr1 hx8_1 hx9_1 hx14_1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 _ hvregs_1 => ?_)
  apply SepWP.done hpc1 hrun1
  rw [← A.pool_of_vmPreserved hvm1]
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rwa [hsp1]
  let base := bsearchLoop s.vec pt.x.value 0 s.vec.length
  change s1.readReg64 .x9 = BitVec.ofNat 64 base at hx9_1
  have ⟨_, hb_lt0⟩ := bsearchLoop_bounds s.vec pt.x.value 0 s.vec.length h1 (by omega)
  have hb_lt : base < s.vec.length := by omega
  have hb_get : s.vec[base]?.getD default = s.vec[base]'hb_lt := by
    rw [List.getElem?_eq_getElem hb_lt, Option.getD_some]
  let baseX := (s.vec[base]'hb_lt).x.value
  have hlsl_base : (BitVec.ofNat 64 base) <<< 2 = BitVec.ofNat 64 (4 * base) :=
    bv64_lsl2_ofNat (by omega)
  unfold bsearchReplace at hnext
  dsimp only at hnext
  rw [hb_get] at hnext
  by_cases heq : ((s.vec[base]'hb_lt).x.value == pt.x.value) = true
  · simp only [heq, ↓reduceIte] at hnext
    have hbaseX_eq : (s.vec[base]'hb_lt).x.value = pt.x.value := beq_iff_eq.mp heq
    have hreasm := reassemble_sortedSetPtOf_set A.repAlloc v cap ptr s.vec base pt hb_lt hle_cap hcap hptr
    apply SepWPp.of_sepWP (mid := (blkPl_419).base + 64#64)
    rw [ptSliceAt_focus s.vec base ptr hb_lt]
    unfold ptAt
    apply sepWP_with_vm
    by_vm_steps
      wp_steps 6
      refine SepWP.weaken_pre
        (show (((ptSliceAt ptr (List.take base s.vec) ∗
            ((ptr + BitVec.ofNat 64 (4 * base)) ↦₁₆ (s.vec[base]'hb_lt).x.value ∗
              (ptr + BitVec.ofNat 64 (4 * base) + 2#64) ↦₁₆ pt.y.value) ∗
            ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗
            (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
            A.live ptr (cap.toNat * 4) 2 ∗
            memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
            A.pool lim curSt s1 ∗ stackAt st.sp growOneStack ∗ F)) ⊢
          sortedSetPtOf A.repAlloc v { vec := s.vec.set base pt } ∗
            A.pool lim curSt s1 ∗ stackAt st.sp growOneStack ∗ F by
          rw [hbaseX_eq]
          refine Entails.trans ?_ (sepConj_mono_left hreasm)
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        ⟨by simp [wp_norm, arm64_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      refine hnext _ [] (Or.inl rfl)
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun1])
        (allocCallPreserved_trans hacp1 (by simp [AllocCallPreserved, wp_norm, arm64_norm]))
        (by simpa [wp_norm, arm64_norm] using hsp1)
        (by simpa [wp_norm, arm64_norm] using htr1')
        (by simpa [wp_norm, arm64_norm, hx14] using hx14_1)
        (by simpa [wp_norm, arm64_norm] using hx19_1)
        (by simpa [wp_norm, arm64_norm] using hx20_1)
        (by simpa [wp_norm, arm64_norm] using hx23_1)
        (by simpa [wp_norm, arm64_norm] using hx24_1)
        (by simpa [wp_norm, arm64_norm] using hx25_1)
        (by simpa [wp_norm, arm64_norm] using hx29_1)
        (by simpa [wp_norm, arm64_norm] using hvregs_1)
  · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hnext
    let insertIdx := if baseX.toNat < pt.x.value.toNat then base + 1 else base
    have hins_le : insertIdx ≤ s.vec.length := by dsimp [insertIdx]; split_ifs <;> omega
    have hfold_slice : ∀ poolP : SepProp,
        ((ptSliceAt ptr (List.take base s.vec) ∗
          ((ptr + BitVec.ofNat 64 (4 * base)) ↦₁₆ (s.vec[base]'hb_lt).x.value ∗
            (ptr + BitVec.ofNat 64 (4 * base) + 2#64) ↦₁₆ (s.vec[base]'hb_lt).y.value) ∗
          ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
          A.live ptr (cap.toNat * 4) 2 ∗
          memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
          poolP ∗ stackAt st.sp growOneStack ∗ F) =
        (ptSliceAt ptr s.vec ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
          A.live ptr (cap.toNat * 4) 2 ∗
          memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
          poolP ∗ stackAt st.sp growOneStack ∗ F) := by
      intro poolP
      change ((ptSliceAt ptr (List.take base s.vec) ∗
        ptAt (s.vec[base]'hb_lt) (ptr + BitVec.ofNat 64 (4 * base)) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗ _) = _
      rw [← ptSliceAt_focus s.vec base ptr hb_lt]
    by_cases hlt_cap : s.vec.length < cap.toNat
    · have hcap_ne : ¬ s.vec.length = cap.toNat := by omega
      apply SepWPp.of_sepWP (mid := (blkPl_419).base + 336#64)
      rw [ptSliceAt_focus s.vec base ptr hb_lt]
      unfold ptAt
      apply sepWP_with_vm
      by_vm_steps
        wp_steps 4
        rw [bv32_bne_zeroExtend16, show ((s.vec[base]'hb_lt).x.value == pt.x.value) = false from
          Bool.eq_false_iff.mpr heq]
        simp only [Bool.not_false, ↓reduceIte]
        wp_steps 4
        rw [bv64_beq_cap_ofNat (by omega),
          show decide (s.vec.length = cap.toNat) = false from decide_eq_false hcap_ne]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine SepWP.done (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun1])
          ⟨by simp [wp_norm, arm64_norm], fun hvm_pre => ?_⟩
        rw [hfold_slice, ← A.pool_of_vmPreserved hvm_pre]
        have hins336 := @bsearch_insert_at_336_acp_placed_sepWP _ M A ext hmemmove_sat v cap ptr
          (BitVec.ofNat 64 s.vec.length) s.vec insertIdx pt hins_le hlt_cap hcap hptr
        apply SepWPp.of_sepWP (mid := (blkPl_419).base + 64#64)
        refine SepWP.weaken_pre (by rw [← hsp1]; exact Entails.of_eq (by sep_ac_rfl))
          (hins336 _ (A.pool lim curSt _ ∗ F) _
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun1])
            (by simpa [wp_norm, arm64_norm] using hsp1_al)
            (by simp [wp_norm, arm64_norm, hx8_1])
            (by simp [wp_norm, arm64_norm, hx14_1, hx14])
            (by simp [wp_norm, arm64_norm, hx21_1, hx21])
            (by simp [wp_norm, arm64_norm, hx24_1, hx24])
            (by simp only [wp_norm, arm64_norm]; exact cinc_insertIdx_eq baseX pt.x.value base)
            (by simp [wp_norm, arm64_norm, hx27_1, hx27])
            (by simp [wp_norm, arm64_norm, hx28_1, hx28])
            (fun sf hpc_f hrun_f hvm_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
        apply SepWP.done hpc_f hrun_f
        rw [← A.pool_of_vmPreserved hvm_f]
        have hsp_f' : sf.sp = st.sp := by
          simpa [wp_norm, arm64_norm, hsp1] using hsp_f
        rw [← hsp_f, hsp_f']
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext sf [] (Or.inl rfl) hpc_f hrun_f
            (allocCallPreserved_trans hacp1
              (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]) hacp_f))
            hsp_f'
            (by simpa [wp_norm, arm64_norm, htr1'] using htr_f)
            hx14_f
            (by simpa [wp_norm, arm64_norm, hx19_1] using hx19_f)
            (by simpa [wp_norm, arm64_norm, hx20_1] using hx20_f)
            (by simpa [wp_norm, arm64_norm, hx23_1] using hx23_f)
            (by simpa [wp_norm, arm64_norm, hx24_1] using hx24_f)
            (by simpa [wp_norm, arm64_norm, hx25_1] using hx25_f)
            (by simpa [wp_norm, arm64_norm, hx29_1] using hx29_f)
            (by simpa [wp_norm, arm64_norm, hvregs_1] using hvregs_f))
    · have hcap_eq : cap.toNat = s.vec.length := by omega
      have hfits_grow : FitsEvents M lim curSt (growOnePtEvents s.vec.length) :=
        hfits _ (Or.inr rfl)
      have hcall := @call_grow_one_pt_full_acp_placed_wpp _ M A lim ext hgrow_full
        ((blkPl_419).base + 452#64) target_pc s0
      have hins452 := @bsearch_insert_at_452_acp_placed_sepWP _ M A ext hmemmove_sat v s.vec insertIdx pt hins_le
      apply SepWPp.of_sepWP (mid := lsmpl.base 357)
      rw [ptSliceAt_focus s.vec base ptr hb_lt]
      unfold ptAt
      apply sepWP_with_vm
      by_vm_steps
        wp_steps 4
        rw [bv32_bne_zeroExtend16, show ((s.vec[base]'hb_lt).x.value == pt.x.value) = false from
          Bool.eq_false_iff.mpr heq]
        simp only [Bool.not_false, ↓reduceIte]
        wp_steps 4
        rw [hfold_slice, bv64_beq_cap_ofNat (by omega),
          show decide (s.vec.length = cap.toNat) = true from decide_eq_true (by omega)]
        simp only [↓reduceIte]
        wp_steps 2
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
          ⟨by simp [wp_norm, arm64_norm], fun hvm_pre => ?_⟩
        rw [← A.pool_of_vmPreserved hvm_pre]
        have hmem_zero :
            memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) = emp := by
          rw [hcap_eq, Nat.sub_self, Nat.zero_mul, memRegion_zero]
        rw [hmem_zero, ← hsp1]
        simp only [emp_sepConj]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hcall (F := F) v cap ptr s.vec curSt h1 hlen hcap_eq hptr hfits_grow
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun1])
            (by simpa [wp_norm, arm64_norm] using hsp1_al)
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simpa [wp_norm, arm64_norm] using htr1')
            (fun s2 hpc2 hrun2 hacp2 hsp2 htr2 hcs2 => ?_))
        have hsp2' : s2.sp = st.sp := by
          rw [hsp2]; simpa [wp_norm, arm64_norm] using hsp1
        have hsp2_al : s2.spAligned = true := by
          unfold State.spAligned at hsp_al ⊢; rwa [hsp2']
        rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
        have hx26_s2 : s2.readReg64 .x26 = BitVec.ofNat 64 insertIdx := by
          rw [hx26_2]
          simp only [wp_norm, arm64_norm]
          exact cinc_insertIdx_eq baseX pt.x.value base
        rw [← hsp2]
        apply SepWPp.of_sepWP (mid := (blkPl_419).base + 64#64)
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hins452 s2 (A.pool lim (M.stepEvents (growOnePtEvents s.vec.length) curSt) s2 ∗ F) _
            hpc2 hrun2 hsp2_al
            (by rw [hx21_2]; simpa [wp_norm, arm64_norm, hx21] using hx21_1)
            (by rw [hx24_2]; simpa [wp_norm, arm64_norm, hx24] using hx24_1)
            hx26_s2
            (by rw [hx27_2]; simpa [wp_norm, arm64_norm, hx27] using hx27_1)
            (by rw [hx28_2]; simpa [wp_norm, arm64_norm, hx28] using hx28_1)
            (fun sf hpc_f hrun_f hvm_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
        apply SepWP.done hpc_f hrun_f
        rw [← A.pool_of_vmPreserved hvm_f, hsp2']
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext sf (growOnePtEvents s.vec.length) (Or.inr rfl) hpc_f hrun_f
            (allocCallPreserved_trans hacp1
              (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])
                (allocCallPreserved_trans hacp2 hacp_f)))
            (hsp_f.trans hsp2') (htr_f.trans htr2) hx14_f
            (by rw [hx19_f, hx19_2]; simpa [wp_norm, arm64_norm] using hx19_1)
            (by rw [hx20_f, hx20_2]; simpa [wp_norm, arm64_norm] using hx20_1)
            (by rw [hx23_f, hx23_2]; simpa [wp_norm, arm64_norm] using hx23_1)
            (by rw [hx24_f, hx24_2]; simpa [wp_norm, arm64_norm] using hx24_1)
            (by rw [hx25_f, hx25_2]; simpa [wp_norm, arm64_norm] using hx25_1)
            (by rw [hx29_f, hx29_2]; simpa [wp_norm, arm64_norm] using hx29_1)
            (by rw [hvregs_f, hvregs_2]; simpa [wp_norm, arm64_norm] using hvregs_1))

/-! ## Placed `bsearchPush` (`+128 -> +64`) -/

theorem bsearch_push_grown_at_412_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {ext : String → Option (State → State)}
    (v : BitVec 64) (vec : List Pt) (pt : Pt)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_419).base + 412#64)
    (hstat : s.status = .Running)
    (hx21 : s.readReg64 .x21 = v)
    (hx24 : s.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 vec.length)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_419).base + 64#64 →
      sf.status = .Running →
      VmPreserved s sf →
      AllocCallPreserved s sf →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
        ((blkPl_419).base + 64#64)
        sf
        (sortedSetPtOf A.repAlloc v { vec := vec ++ [pt] } ∗ P)
        post) :
    SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      ((blkPl_419).base + 64#64)
      s
      (sortedSetPtGrownAt A.repAlloc v vec ∗ P)
      post := by
  unfold sortedSetPtGrownAt
  wp_pull_exists
  rename_i cap ptr
  apply SepWP.focus_pure (by sep_focus)
  rintro ⟨hlt, hptr, hcap⟩
  have hlsl_len : (BitVec.ofNat 64 vec.length) <<< 2 = BitVec.ofNat 64 (4 * vec.length) :=
    bv64_lsl2_ofNat (by omega)
  rw [memRegion_spare_split_one ptr hlt hcap]
  wp_pull_exists
  rename_i v1 v0
  have hreasm := reassemble_sortedSetPtOf_snoc A.repAlloc v cap ptr vec pt hlt hcap hptr
  apply sepWP_seq_with_vm
  by_vm_steps
    wp_steps 8
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
      ⟨by simp [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine align_pre_vm (P' := sortedSetPtOf A.repAlloc v { vec := vec ++ [pt] } ∗ P)
      (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
          exact Entails.of_eq (by sep_ac_rfl)) ?_
    exact hcont _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      hvm
      (by simp [AllocCallPreserved, wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])

theorem bsearchPush_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtFullSpec M A lim)))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtSpec M A lim)))
    {target_pc : BitVec 64} {s0 st : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (v : BitVec 64) (s : SortedSetPt) (pt : Pt) (curSt : M.σ)
    (hlen : s.vec.length ≤ 65536)
    (hfits : FitsEnv M lim curSt (AddChunkSlotEnv s))
    (hpc : st.pc = (blkPl_419).base + 128#64)
    (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true)
    (htr : st.trace = s0.trace)
    (hx14 : st.readReg64 .x14 = 1#64)
    (hx21 : st.readReg64 .x21 = v)
    (hx24 : st.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx27 : st.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : st.readReg64 .x28 = BitVec.ofNat 64 s.vec.length)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      AddChunkSlotEnv s evs →
      sf.pc = (blkPl_419).base + 64#64 →
      sf.status = .Running →
      AllocCallPreserved st sf →
      sf.sp = st.sp →
      sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 →
      sf.readReg64 .x19 = st.readReg64 .x19 →
      sf.readReg64 .x20 = st.readReg64 .x20 →
      sf.readReg64 .x23 = st.readReg64 .x23 →
      sf.readReg64 .x24 = st.readReg64 .x24 →
      sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x29 = st.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtOf A.repAlloc v (bsearchPush s pt) ∗
          A.pool lim (M.stepEvents evs curSt) sf ∗ stackAt st.sp growOneStack ∗ F)
        Q Qp) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc st
      (sortedSetPtOf A.repAlloc v s ∗ A.pool lim curSt st ∗ stackAt st.sp growOneStack ∗ F)
      Q Qp := by
  refine SepWPp.weaken_pre (sepConj_mono_left (sortedSetPtOf_expose A.repAlloc v s)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_elim; rintro ⟨hle_cap, hcap, hptr⟩
  rcases Nat.eq_zero_or_pos s.vec.length with hlen0 | h1
  · have hvec_nil : s.vec = [] := List.eq_nil_of_length_eq_zero hlen0
    have hpush_nil : bsearchPush s pt = { vec := [pt] } := by
      unfold bsearchPush; rw [hvec_nil]; rfl
    rw [hpush_nil] at hnext
    rw [hlen0] at hx28
    have hslice_nil : ptSliceAt ptr [] = emp := rfl
    simp only [hvec_nil, List.length_nil, Nat.zero_mul, Nat.sub_zero,
      BitVec.add_zero, hslice_nil, emp_sepConj]
    by_cases hcap0 : cap = 0#64
    · subst hcap0
      simp only [↓reduceIte, emp_sepConj]
      have hfits_empty : FitsEvents M lim curSt (growOnePtEvents 0) := by
        rw [← hlen0]; exact hfits _ (Or.inr rfl)
      have hslot_empty : AddChunkSlotEnv s (growOnePtEvents 0) := by
        right; rw [hlen0]
      have hcall := @call_grow_one_pt_empty_acp_placed_wpp _ M A lim ext hgrow_empty
        ((blkPl_419).base + 396#64) target_pc s0
      have hpush216 := @bsearch_push_empty_at_216_placed_sepWP _ M A ext v 4#64
      apply SepWPp.of_sepWP (mid := lsmpl.base 357)
      apply sepWP_with_vm
      by_vm_steps
        wp_steps 5
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          ⟨by simp [wp_norm, arm64_norm], fun hvm1 => ?_⟩
        rw [← A.pool_of_vmPreserved hvm1]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hcall (F := F) v ptr 0#64 curSt hptr hfits_empty
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun])
            (by simpa [wp_norm, arm64_norm] using hsp_al)
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simpa [wp_norm, arm64_norm] using htr)
            (fun s2 p' hp' hpc2 hrun2 hacp2 hsp2 htr2 hcs2 => ?_))
        have hsp2' : s2.sp = st.sp := by
          simpa [wp_norm, arm64_norm] using hsp2
        rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, _, hx27_2, _, hx29_2, hvregs_2⟩
        rw [← hsp2]
        apply SepWPp.of_sepWP (mid := (blkPl_419).base + 216#64)
        apply sepWP_with_vm
        by_vm_steps
          wp_steps 2
          refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2])
            ⟨by simp [wp_norm, arm64_norm], fun hvm_mid => ?_⟩
          rw [← A.pool_of_vmPreserved hvm_mid]
          have h4_16 : (4#64 : BitVec 64).toNat * 4 = 16 := rfl
          apply SepWPp.of_sepWP (mid := (blkPl_419).base + 64#64)
          refine SepWP.weaken_pre (by rw [h4_16]; exact Entails.of_eq (by sep_ac_rfl))
            (hpush216 p' 0#64 pt (by decide) (by decide) hp' _
              (A.pool lim (M.stepEvents (growOnePtEvents 0) curSt) _ ∗ stackAt s2.sp growOneStack ∗ F) _
              (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm, hrun2])
              (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm, hx21_2, hx21])
              (by simp [wp_norm, arm64_norm, hx24_2, hx24])
              (by simp [wp_norm, arm64_norm, hx27_2, hx27])
              (fun sf hpc_f hrun_f hvm_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
          apply SepWP.done hpc_f hrun_f
          rw [← A.pool_of_vmPreserved hvm_f]
          have hsp_f' : sf.sp = st.sp := by
            simpa [wp_norm, arm64_norm, hsp2'] using hsp_f
          rw [hsp2']
          refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (hnext sf (growOnePtEvents 0) hslot_empty hpc_f hrun_f
              (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])
                (allocCallPreserved_trans hacp2
                  (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]) hacp_f)))
              hsp_f'
              (by simpa [wp_norm, arm64_norm, htr2] using htr_f)
              hx14_f
              (by simpa [wp_norm, arm64_norm, hx19_2] using hx19_f)
              (by simpa [wp_norm, arm64_norm, hx20_2] using hx20_f)
              (by simpa [wp_norm, arm64_norm, hx23_2] using hx23_f)
              (by simpa [wp_norm, arm64_norm, hx24_2] using hx24_f)
              (by simpa [wp_norm, arm64_norm, hx25_2] using hx25_f)
              (by simpa [wp_norm, arm64_norm, hx29_2] using hx29_f)
              (by simpa [wp_norm, arm64_norm, hvregs_2] using hvregs_f))
    · simp only [hcap0, ↓reduceIte]
      have hlt0 : 0 < cap.toNat := by
        by_contra hle0
        apply hcap0
        apply BitVec.eq_of_toNat_eq
        change cap.toNat = 0; omega
      have hbeq0 : (cap == 0#64) = false := beq_false_of_ne hcap0
      have hpush216 := @bsearch_push_empty_at_216_placed_sepWP _ M A ext v cap ptr 0#64 pt hlt0 hcap hptr
      apply SepWPp.of_sepWP (mid := (blkPl_419).base + 216#64)
      apply sepWP_with_vm
      by_vm_steps
        wp_steps 3
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          ⟨by simp [wp_norm, arm64_norm], fun hvm1 => ?_⟩
        rw [← A.pool_of_vmPreserved hvm1]
        apply SepWPp.of_sepWP (mid := (blkPl_419).base + 64#64)
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hpush216 _ (A.pool lim curSt _ ∗ stackAt st.sp growOneStack ∗ F) _
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun])
            (by simp [wp_norm, arm64_norm, hx14])
            (by simp [wp_norm, arm64_norm, hx21])
            (by simp [wp_norm, arm64_norm, hx24])
            (by simp [wp_norm, arm64_norm, hx27])
            (fun sf hpc_f hrun_f hvm_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
        apply SepWP.done hpc_f hrun_f
        rw [← A.pool_of_vmPreserved hvm_f]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext sf [] (Or.inl rfl) hpc_f hrun_f
            (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]) hacp_f)
            (by simpa [wp_norm, arm64_norm] using hsp_f)
            (by simpa [wp_norm, arm64_norm, htr] using htr_f)
            hx14_f
            (by simpa [wp_norm, arm64_norm] using hx19_f)
            (by simpa [wp_norm, arm64_norm] using hx20_f)
            (by simpa [wp_norm, arm64_norm] using hx23_f)
            (by simpa [wp_norm, arm64_norm] using hx24_f)
            (by simpa [wp_norm, arm64_norm] using hx25_f)
            (by simpa [wp_norm, arm64_norm] using hx29_f)
            (by simpa [wp_norm, arm64_norm] using hvregs_f))
  · have hcap0 : cap ≠ 0#64 := by
      intro hc; subst hc
      have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
      omega
    simp only [hcap0, ↓reduceIte]
    let lastIdx := s.vec.length - 1
    have hlast_lt : lastIdx < s.vec.length := by omega
    let lastPt := s.vec[lastIdx]'hlast_lt
    have hlast_eq : s.vec.getLast? = some lastPt := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlast_lt]
    have hne0 : (BitVec.ofNat 64 s.vec.length == 0#64) = false := bv64_ne_zero_of_pos h1 hlen
    have hlsl_len : (BitVec.ofNat 64 s.vec.length) <<< 2 = BitVec.ofNat 64 (4 * s.vec.length) :=
      bv64_lsl2_ofNat (by omega)
    have hsub4 := ptr_add_len_sub4 ptr h1 hlen
    have hsub2 := ptr_add_len_sub2 ptr h1 hlen
    unfold bsearchPush at hnext
    rw [hlast_eq] at hnext
    dsimp only at hnext
    cases hcmp : Pt.cmp pt lastPt with
    | eq =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hset_eq : s.vec.dropLast ++ [pt] = s.vec.set lastIdx pt :=
        dropLast_append_singleton_eq_set s.vec pt h1
      rw [hset_eq] at hnext
      have hcmp' : pt.x.value.toNat = (s.vec[lastIdx]'hlast_lt).x.value.toNat :=
        compare_eq_iff_eq.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      have hule2 :
          (BitVec.zeroExtend 32 pt.x.value).ule
            (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      apply SepWPp.of_sepWP (mid := (blkPl_419).base + 64#64)
      rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      apply sepWP_with_vm
      by_vm_steps
        wp_steps 11
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          ⟨by simp [wp_norm, arm64_norm], fun hvm => ?_⟩
        rw [hsub4, hsub2, ← A.pool_of_vmPreserved hvm]
        have hreasm := reassemble_sortedSetPtOf_set A.repAlloc v cap ptr s.vec lastIdx pt hlast_lt hle_cap hcap hptr
        refine SepWPp.weaken_pre
          (P' := sortedSetPtOf A.repAlloc v { vec := s.vec.set lastIdx pt } ∗
            A.pool lim curSt _ ∗ stackAt st.sp growOneStack ∗ F)
          (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
              exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ [] (Or.inl rfl)
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun])
            (by simp [AllocCallPreserved, wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simpa [wp_norm, arm64_norm] using htr)
            (by simp [wp_norm, arm64_norm, hx14])
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm]))
    | lt =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hcmp' : pt.x.value.toNat < (s.vec[lastIdx]'hlast_lt).x.value.toNat :=
        compare_lt_iff_lt.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = false := by
        rw [bv32_ule_zeroExtend16, decide_eq_false_iff_not]; omega
      have hrep := @bsearchReplace_placed_wpp _ M A lim ext hmemmove_sat hgrow_full target_pc s0
      apply SepWPp.of_sepWP (mid := (blkPl_419).base + 236#64)
      rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      apply sepWP_with_vm
      by_vm_steps
        wp_steps 11
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          ⟨by simp [wp_norm, arm64_norm], fun hvm1 => ?_⟩
        rw [hsub4, hsub2, ← A.pool_of_vmPreserved hvm1]
        have hfold_slice :
            ptSliceAt ptr (s.vec.take lastIdx) ∗
              (((ptr + BitVec.ofNat 64 (4 * lastIdx)) ↦₁₆ (s.vec[lastIdx]'hlast_lt).x.value) ∗
                ((ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64) ↦₁₆ (s.vec[lastIdx]'hlast_lt).y.value)) ∗
              ptSliceAt (ptr + BitVec.ofNat 64 (4 * (lastIdx + 1))) (s.vec.drop (lastIdx + 1)) =
            ptSliceAt ptr s.vec := by
          rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]; rfl
        rw [hfold_slice]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hrep (F := F) v cap ptr s pt curSt h1 hlen hle_cap hcap hptr hfits
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun])
            (by simpa [wp_norm, arm64_norm] using hsp_al)
            (by simpa [wp_norm, arm64_norm] using htr)
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hx14])
            (by simp [wp_norm, arm64_norm, hx21])
            (by simp [wp_norm, arm64_norm, hx24])
            (by simp [wp_norm, arm64_norm, hx27])
            (by simp [wp_norm, arm64_norm, hx28])
            (fun sf evs hevs hpc_f hrun_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
        have hsp_f' : sf.sp = st.sp := by
          simpa [wp_norm, arm64_norm] using hsp_f
        simp only [wp_norm, arm64_norm]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext sf evs hevs hpc_f hrun_f
            (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]) hacp_f)
            hsp_f' htr_f hx14_f
            (by simpa [wp_norm, arm64_norm] using hx19_f)
            (by simpa [wp_norm, arm64_norm] using hx20_f)
            (by simpa [wp_norm, arm64_norm] using hx23_f)
            (by simpa [wp_norm, arm64_norm] using hx24_f)
            (by simpa [wp_norm, arm64_norm] using hx25_f)
            (by simpa [wp_norm, arm64_norm] using hx29_f)
            (by simpa [wp_norm, arm64_norm] using hvregs_f))
    | gt =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hcmp' : (s.vec[lastIdx]'hlast_lt).x.value.toNat < pt.x.value.toNat :=
        compare_gt_iff_gt.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      have hule2 :
          (BitVec.zeroExtend 32 pt.x.value).ule
            (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value) = false := by
        rw [bv32_ule_zeroExtend16, decide_eq_false_iff_not]; omega
      have hfold_slice :
          ptSliceAt ptr (s.vec.take lastIdx) ∗
            (((ptr + BitVec.ofNat 64 (4 * lastIdx)) ↦₁₆ (s.vec[lastIdx]'hlast_lt).x.value) ∗
              ((ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64) ↦₁₆ (s.vec[lastIdx]'hlast_lt).y.value)) ∗
            ptSliceAt (ptr + BitVec.ofNat 64 (4 * (lastIdx + 1))) (s.vec.drop (lastIdx + 1)) =
          ptSliceAt ptr s.vec := by
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]; rfl
      by_cases hlt_cap : s.vec.length < cap.toNat
      · have hbeq_cap : (BitVec.ofNat 64 s.vec.length == cap) = false := by
          rw [bv64_beq_cap_ofNat (by omega), decide_eq_false_iff_not]; omega
        have hule_succ :
            (BitVec.ofNat 64 s.vec.length).ule (BitVec.ofNat 64 (s.vec.length + 1)) = true :=
          bv64_ule_succ (by omega)
        apply SepWPp.of_sepWP (mid := (blkPl_419).base + 64#64)
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
        unfold ptAt
        rw [← hsub2, ← hsub4]
        rw [memRegion_spare_split_one ptr hlt_cap hcap]
        wp_pull_exists
        rename_i v1 v0
        apply sepWP_with_vm
        by_vm_steps
          wp_steps 19
          refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
            ⟨by simp [wp_norm, arm64_norm], fun hvm => ?_⟩
          rw [hsub4, hsub2, ← A.pool_of_vmPreserved hvm]
          have hreasm := reassemble_sortedSetPtOf_snoc A.repAlloc v cap ptr s.vec pt hlt_cap hcap hptr
          rw [← hfold_slice] at hreasm
          refine SepWPp.weaken_pre
            (P' := sortedSetPtOf A.repAlloc v { vec := s.vec ++ [pt] } ∗
              A.pool lim curSt _ ∗ stackAt st.sp growOneStack ∗ F)
            (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
                exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ [] (Or.inl rfl)
              (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm, hrun])
              (by simp [AllocCallPreserved, wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm])
              (by simpa [wp_norm, arm64_norm] using htr)
              (by simp [wp_norm, arm64_norm, hx14])
              (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm]))
      · have hbeq_cap : (BitVec.ofNat 64 s.vec.length == cap) = true := by
          rw [bv64_beq_cap_ofNat (by omega), decide_eq_true_eq]; omega
        have hcap_eq : cap.toNat = s.vec.length := by omega
        have hfits_grow : FitsEvents M lim curSt (growOnePtEvents s.vec.length) :=
          hfits _ (Or.inr rfl)
        have hcall := @call_grow_one_pt_full_acp_placed_wpp _ M A lim ext hgrow_full
          ((blkPl_419).base + 412#64) target_pc s0
        have hgrown := @bsearch_push_grown_at_412_placed_sepWP _ M A ext v s.vec pt
        apply SepWPp.of_sepWP (mid := lsmpl.base 357)
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
        unfold ptAt
        rw [← hsub2, ← hsub4]
        apply sepWP_with_vm
        by_vm_steps
          wp_steps 16
          refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
            ⟨by simp [wp_norm, arm64_norm], fun hvm1 => ?_⟩
          rw [hsub4, hsub2, hfold_slice, ← A.pool_of_vmPreserved hvm1]
          have hmem_zero :
              memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) = emp := by
            rw [hcap_eq, Nat.sub_self, Nat.zero_mul, memRegion_zero]
          rw [hmem_zero]
          refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (hcall (F := F) v cap ptr s.vec curSt h1 hlen hcap_eq hptr hfits_grow
              (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm, hrun])
              (by simpa [wp_norm, arm64_norm] using hsp_al)
              (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm])
              (by simpa [wp_norm, arm64_norm] using htr)
              (fun s2 hpc2 hrun2 hacp2 hsp2 htr2 hcs2 => ?_))
          have hsp2' : s2.sp = st.sp := by
            simpa [wp_norm, arm64_norm] using hsp2
          rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, _, hx27_2, hx28_2, hx29_2, hvregs_2⟩
          rw [← hsp2]
          apply SepWPp.of_sepWP (mid := (blkPl_419).base + 64#64)
          refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (hgrown s2 (A.pool lim (M.stepEvents (growOnePtEvents s.vec.length) curSt) s2 ∗ stackAt s2.sp growOneStack ∗ F) _
              hpc2 hrun2
              (by rw [hx21_2]; simp [wp_norm, arm64_norm, hx21])
              (by rw [hx24_2]; simp [wp_norm, arm64_norm, hx24])
              (by rw [hx27_2]; simp [wp_norm, arm64_norm, hx27])
              (by rw [hx28_2]; simp [wp_norm, arm64_norm, hx28])
              (fun sf hpc_f hrun_f hvm_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
          apply SepWP.done hpc_f hrun_f
          rw [← A.pool_of_vmPreserved hvm_f]
          have hsp_f' : sf.sp = st.sp := by
            simpa [wp_norm, arm64_norm, hsp2'] using hsp_f
          rw [hsp2']
          refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (hnext sf (growOnePtEvents s.vec.length) (Or.inr rfl) hpc_f hrun_f
              (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])
                (allocCallPreserved_trans hacp2 hacp_f))
              hsp_f'
              (by simpa [wp_norm, arm64_norm, htr2] using htr_f)
              hx14_f
              (by rw [hx19_f, hx19_2]; simp [wp_norm, arm64_norm])
              (by rw [hx20_f, hx20_2]; simp [wp_norm, arm64_norm])
              (by rw [hx23_f, hx23_2]; simp [wp_norm, arm64_norm])
              (by rw [hx24_f, hx24_2]; simp [wp_norm, arm64_norm])
              (by rw [hx25_f, hx25_2]; simp [wp_norm, arm64_norm])
              (by rw [hx29_f, hx29_2]; simp [wp_norm, arm64_norm])
              (by rw [hvregs_f, hvregs_2]; simp [wp_norm, arm64_norm]))

end LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudgetAux
