/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Main Proof for `<PolyDecoder as Decoder>::add_chunk`

Threads `RustCliAllocBudget M` through the 16-iteration outer loop and proves
`add_chunk_bsearch_placed_ok_ext`, `add_chunk_placed_ok_ext`, and `add_chunk_placed_ok_x` on
Block `419`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification (LibsignalPlacement blkPC_419 blkPl_419 lsmpl)
open CryptoVerification.LibsignalSpqrV1 (Chunk GF16 NUM_POLYS PolyDecoder Pt SortedSetPt)
open CryptoVerification.LibsignalTripleRatchet (sessionMemmoveSpec)
open CryptoVerification.SpqrV1.Alloc (growOneStack spqrMemmoveSym)
open CryptoVerification.SpqrV1.Poly (
  boolByte chunkAt chunkIndexOff polyDecoderAt polyDecoderIsCompleteOff
  polyDecoderPadOff polyDecoderPadSize polyDecoderPtsNeededOff
  sortedSetPtListOf sortedSetPtOf
)
open CryptoVerification.SpqrV1.Poly.AddChunk (
  AddChunkGhost PolyDecoderStrictSorted addChunkBsearch
  addChunkBsearchLoop addChunkBsearchStep addChunkBsearchStep_getElem_after
  addChunkBsearchStep_ptsNeeded addChunkBsearchStep_pts_length
  addChunkBsearch_eq_addChunkTotal addChunkStack addChunkStackX
  addChunkTotal addChunk_polyIdx_eq addChunk_poly_eq
  addChunk_skip_cond_eq addChunk_x_eq bsearchPush bv64_add1_beq16
  bv64_and15_ofNat bv64_lsl1_ofNat bv64_lsr4_ofNat bv64_madd24_ofNat
  chunk_data_focus16 cinc_necessaryPoints_eq necessaryPoints_lt
  ptListStrictSorted_length_le
  sortedSetPtListOf_focus sortedSetPtListOf_set sortedSetPtOf_eq_len_sep
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
  FitsEvents RustCliAllocBudget SeqEnv VmPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (
  growOnePtFullSpec growOnePtSpec
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (
  allocCallPreserved_trans withAllocVmPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (
  AddChunkEnv AddChunkPlacedOkExt AddChunkPlacedOkX AddChunkSlotEnv
  AddChunkSlotsEnv addChunkBsearchSpec addChunkSlotsEnv_nil addChunkSpec
  addChunkSpecX
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.LoopPlacedBudget (
  addChunkBsearch_isComplete addChunkBsearch_ptsNeeded
  addChunkBsearch_pts_length rev16_64_pair stackAt_addChunk_split
  withAllocCallPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudgetAux (
  bsearchPush_placed_wpp bsearchReplace_placed_wpp
  bsearch_push_grown_at_412_placed_sepWP sepWP_seq_with_vm sepWP_with_vm
)

export LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudgetAux (
  bsearchReplace_placed_wpp
  bsearch_push_grown_at_412_placed_sepWP
  bsearchPush_placed_wpp
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  calleeSavedVRegs_setPC_pre calleeSavedVRegs_setMem_setPC_pre

/-! ## Placed Outer 16-Iteration Loop (`addChunk_body_placed_wpp`, `addChunk_loop_placed_wpp`) -/

private theorem acp_of_vm_chain {s0 s1 s2 sf : State} (_ : VmPreserved s2 sf)
    (h01 : AllocCallPreserved s0 s1) (h12 : AllocCallPreserved s1 s2)
    (h2f : AllocCallPreserved s2 sf) : AllocCallPreserved s0 sf :=
  allocCallPreserved_trans h01 (allocCallPreserved_trans h12 h2f)

private theorem drop_eq_cons_drop_succ {α : Type} (xs : List α) {i : Nat} (hi : i < xs.length) :
    xs.drop i = (xs[i]'hi) :: xs.drop (i + 1) :=
  List.drop_eq_getElem_cons hi

private theorem addChunkBsearchStep_drop_after (chunk : Chunk) (self : PolyDecoder) {i : Nat}
    (hi : i < 16) (hpts_len : self.pts.length = 16) :
    (addChunkBsearchStep chunk i self).pts.drop (i + 1) = self.pts.drop (i + 1) := by
  apply List.ext_getElem
  · simp [addChunkBsearchStep_pts_length, hpts_len]
  · intro k hk1 hk2
    simp only [List.getElem_drop]
    have hj0 : i + 1 + k < self.pts.length := by
      simp only [List.length_drop, hpts_len] at hk2; omega
    exact addChunkBsearchStep_getElem_after chunk self hi (by omega) hj0

theorem addChunk_body_placed_wpp [LibsignalPlacement]
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
    (decA chunkA : BitVec 64) (self : PolyDecoder) (chunk : Chunk) (i : Nat) (curSt : M.σ)
    (hi : i < 16) (hpts_len : self.pts.length = 16) (hneed : self.ptsNeeded < 2 ^ 64)
    (hcap_i : (self.pts[i]'(by omega)).vec.length ≤ 65536)
    (hfits_i : FitsEnv M lim curSt (AddChunkSlotEnv (self.pts[i]'(by omega))))
    (hpc : st.pc = (blkPl_419).base + 76#64)
    (hrun : st.status = .Running) (hsp_al : st.spAligned = true) (htr : st.trace = s0.trace)
    (hx14 : st.readReg64 .x14 = 1#64) (hx19 : st.readReg64 .x19 = chunkA) (hx20 : st.readReg64 .x20 = decA)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 i) (hx24 : st.readReg64 .x24 = chunk.index.zeroExtend 64)
    (hx25 : st.readReg64 .x25 = 24#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      AddChunkSlotEnv (self.pts[i]'(by omega)) evs →
      sf.pc = (blkPl_419).base + 64#64 →
      sf.status = .Running → AllocCallPreserved st sf → sf.sp = st.sp → sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = chunkA → sf.readReg64 .x20 = decA →
      sf.readReg64 .x23 = BitVec.ofNat 64 i → sf.readReg64 .x24 = chunk.index.zeroExtend 64 →
      sf.readReg64 .x25 = 24#64 → sf.readReg64 .x29 = st.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtListOf A.repAlloc decA (addChunkBsearchStep chunk i self).pts ∗
          ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
          (chunkA ↦ₛ chunk.data.toList) ∗
          A.pool lim (M.stepEvents evs curSt) sf ∗ stackAt st.sp growOneStack ∗ F)
        Q Qp) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc st
      (sortedSetPtListOf A.repAlloc decA self.pts ∗
        ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
        (chunkA ↦ₛ chunk.data.toList) ∗
        A.pool lim curSt st ∗ stackAt st.sp growOneStack ∗ F)
      Q Qp := by
  have hi_pts : i < self.pts.length := by omega
  let nec := self.necessaryPoints i
  have hnec : nec < 2 ^ 64 := necessaryPoints_lt self i hneed
  have hmadd : decA + BitVec.ofNat 64 i * 24#64 = decA + BitVec.ofNat 64 (24 * i) :=
    bv64_madd24_ofNat decA hi
  have _hlsr4 : (BitVec.ofNat 64 self.ptsNeeded) >>> 4 = BitVec.ofNat 64 (self.ptsNeeded / 16) :=
    bv64_lsr4_ofNat hneed
  have _hand15 : (BitVec.ofNat 64 self.ptsNeeded) &&& 15#64 = BitVec.ofNat 64 (self.ptsNeeded % 16) :=
    bv64_and15_ofNat hneed
  have _hcinc_nec := cinc_necessaryPoints_eq self hi hneed
  have hskip_cond := addChunk_skip_cond_eq chunk.index hnec
    (by omega : (self.pts[i]'hi_pts).vec.length < 2 ^ 64)
  have hget_i : self.pts[(chunk.index.toNat * 16 + i) % 16]?.getD SortedSetPt.new = self.pts[i]'hi_pts := by
    rw [addChunk_poly_eq chunk hi, List.getElem?_eq_getElem hi_pts, Option.getD_some]
  by_cases hcond : (decide (chunk.index.toNat < nec) || decide ((self.pts[i]'hi_pts).vec.length < nec)) = true
  · have hstep_eq :
        (addChunkBsearchStep chunk i self).pts =
          self.pts.set i
            (bsearchPush (self.pts[i]'hi_pts)
              { x := GF16.new chunk.index
                y := GF16.new
                  (((chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩).zeroExtend 16 <<< 8) +
                    (chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩).zeroExtend 16) }) := by
      unfold addChunkBsearchStep SortedSetPt.len
      dsimp only
      rw [hget_i, addChunk_poly_eq chunk hi, addChunk_x_eq chunk hi, addChunk_polyIdx_eq chunk hi, hcond]
      rfl
    rw [hstep_eq] at hnext
    let y1 := chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    let y2 := chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    let y := GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
    let pt : Pt := { x := GF16.new chunk.index, y := y }
    have hlsl1 : (BitVec.ofNat 64 i) <<< 1 = BitVec.ofNat 64 (i * 2) := bv64_lsl1_ofNat hi
    have hpush := @bsearchPush_placed_wpp _ M A lim ext hmemmove_sat hgrow_full hgrow_empty target_pc s0
    apply SepWPp.of_sepWP (mid := (blkPl_419).base + 128#64)
    dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat] at hpush hpc hnext ⊢
    have _hbr_false :
        (if (if (BitVec.ofNat 64 (self.necessaryPoints i)).ule (BitVec.zeroExtend 64 chunk.index) = true then
            (BitVec.ofNat 64 (self.necessaryPoints i)).ule (BitVec.ofNat 64 (self.pts[i]'hi_pts).vec.length)
          else ConditionHolds CondCode.CS { }) = true then
          (blkPl_419).base + 64#64
        else (blkPl_419).base + 116#64) = (blkPl_419).base + 116#64 := by
      change (if (if (BitVec.ofNat 64 nec).ule (BitVec.zeroExtend 64 chunk.index) = true then
          (BitVec.ofNat 64 nec).ule (BitVec.ofNat 64 (self.pts[i]'hi_pts).vec.length) else false) = true then
          (blkPl_419).base + 64#64 else (blkPl_419).base + 116#64) = (blkPl_419).base + 116#64
      rw [hskip_cond, hcond]; rfl
    rw [sortedSetPtListOf_focus A.repAlloc self.pts i decA hi_pts]
    rw [sortedSetPtOf_eq_len_sep A.repAlloc (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts), ← hmadd]
    rw [chunk_data_focus16 chunkA chunk i hi]
    rw [← hlsl1]
    apply sepWP_with_vm
    by_vm_steps
      wp_steps 13
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
        ⟨by simp [wp_norm, arm64_norm], fun hvm1 => ?_⟩
      rw [hmadd, ← sortedSetPtOf_eq_len_sep A.repAlloc (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts),
        hlsl1, ← A.pool_of_vmPreserved hvm1]
      have hfold_chunk :
          ((chunkA ↦ₛ chunk.data.toList.take (i * 2)) ∗
            ((chunkA + BitVec.ofNat 64 (i * 2)) ↦₁₆ (y2 ++ y1)) ∗
            ((chunkA + BitVec.ofNat 64 (i * 2 + 2)) ↦ₛ chunk.data.toList.drop (i * 2 + 2))) =
          (chunkA ↦ₛ chunk.data.toList) :=
        (chunk_data_focus16 chunkA chunk i hi).symm
      refine SepWPp.weaken_pre
        (by rw [← hfold_chunk]; dsimp only [y1, y2]; simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl))
        (hpush (F := sortedSetPtListOf A.repAlloc decA (self.pts.take i) ∗
            sortedSetPtListOf A.repAlloc (decA + BitVec.ofNat 64 (24 * (i + 1))) (self.pts.drop (i + 1)) ∗
            ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
            (chunkA ↦ₛ chunk.data.toList) ∗ F)
          (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts) pt curSt hcap_i hfits_i
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun])
          (by simpa [wp_norm, arm64_norm] using hsp_al)
          (by simpa [wp_norm, arm64_norm] using htr)
          (by simp [wp_norm, arm64_norm, hx14])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hx24, pt, GF16.new])
          (by simp only [wp_norm, arm64_norm, pt, y, GF16.new]; exact rev16_64_pair y1 y2)
          (by simp [wp_norm, arm64_norm])
          (fun sf evs hevs hpc_f hrun_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
      have hsp_f' : sf.sp = st.sp := by
        simpa [wp_norm, arm64_norm] using hsp_f
      simp only [wp_norm, arm64_norm]
      refine SepWPp.weaken_pre
        (by rw [sortedSetPtListOf_set A.repAlloc self.pts i (bsearchPush (self.pts[i]'hi_pts) pt) decA hi_pts]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext sf evs hevs hpc_f hrun_f
          (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]) hacp_f)
          hsp_f' htr_f hx14_f
          (by simpa [wp_norm, arm64_norm, hx19] using hx19_f)
          (by simpa [wp_norm, arm64_norm, hx20] using hx20_f)
          (by simpa [wp_norm, arm64_norm, hx23] using hx23_f)
          (by simpa [wp_norm, arm64_norm, hx24] using hx24_f)
          (by simpa [wp_norm, arm64_norm, hx25] using hx25_f)
          (by simpa [wp_norm, arm64_norm] using hx29_f)
          (by simpa [wp_norm, arm64_norm] using hvregs_f))
  · have hcond_f : (decide (chunk.index.toNat < nec) || decide ((self.pts[i]'hi_pts).vec.length < nec)) = false :=
       Bool.eq_false_iff.mpr hcond
    have hstep_eq : (addChunkBsearchStep chunk i self).pts = self.pts := by
      unfold addChunkBsearchStep SortedSetPt.len
      dsimp only
      rw [hget_i, addChunk_polyIdx_eq chunk hi, hcond_f]
      rfl
    rw [hstep_eq] at hnext
    apply SepWPp.of_sepWP (mid := (blkPl_419).base + 64#64)
    dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
    rw [sortedSetPtListOf_focus A.repAlloc self.pts i decA hi_pts]
    rw [sortedSetPtOf_eq_len_sep A.repAlloc (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts), ← hmadd]
    apply sepWP_with_vm
    by_vm_steps
      wp_steps 10
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm]
            change (if (if (BitVec.ofNat 64 nec).ule (BitVec.zeroExtend 64 chunk.index) = true then
                (BitVec.ofNat 64 nec).ule (BitVec.ofNat 64 (self.pts[i]'hi_pts).vec.length) else false) = true then
                (blkPl_419).base + 64#64 else (blkPl_419).base + 116#64) = (blkPl_419).base + 64#64
            rw [hskip_cond, hcond_f]; rfl)
        (by simp [wp_norm, arm64_norm, hrun])
        ⟨by simp [wp_norm, arm64_norm], fun hvm => ?_⟩
      rw [hmadd, ← sortedSetPtOf_eq_len_sep A.repAlloc (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts),
        ← A.pool_of_vmPreserved hvm]
      refine SepWPp.weaken_pre
        (by rw [sortedSetPtListOf_focus A.repAlloc self.pts i decA hi_pts]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ [] (Or.inl rfl)
          (by simp only [wp_norm, arm64_norm]
              change (if (if (BitVec.ofNat 64 nec).ule (BitVec.zeroExtend 64 chunk.index) = true then
                  (BitVec.ofNat 64 nec).ule (BitVec.ofNat 64 (self.pts[i]'hi_pts).vec.length) else false) = true then
                  (blkPl_419).base + 64#64 else (blkPl_419).base + 116#64) = (blkPl_419).base + 64#64
              rw [hskip_cond, hcond_f]; rfl)
          (by simp [wp_norm, arm64_norm, hrun])
          (by simp [AllocCallPreserved, wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simpa [wp_norm, arm64_norm] using htr)
          (by simp [wp_norm, arm64_norm, hx14])
          (by simp [wp_norm, arm64_norm, hx19])
          (by simp [wp_norm, arm64_norm, hx20])
          (by simp [wp_norm, arm64_norm, hx23])
          (by simp [wp_norm, arm64_norm, hx24])
          (by simp [wp_norm, arm64_norm, hx25])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]))

theorem addChunk_loop_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtFullSpec M A lim)))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtSpec M A lim)))
    {target_pc : BitVec 64} {s0 : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (decA chunkA sp : BitVec 64) (chunk : Chunk)
    (rem : Nat) :
    ∀ (i : Nat) (self : PolyDecoder) (curSt : M.σ) (st : State),
      i + (rem + 1) = 16 →
      self.pts.length = 16 →
      self.ptsNeeded < 2 ^ 64 →
      (∀ j (hj : j < self.pts.length), i ≤ j → (self.pts[j]'hj).vec.length ≤ 65536) →
      FitsEnv M lim curSt (AddChunkSlotsEnv (self.pts.drop i)) →
      st.pc = (blkPl_419).base + 76#64 →
      st.status = .Running →
      st.sp = sp →
      st.spAligned = true →
      st.trace = s0.trace →
      st.readReg64 .x14 = 1#64 →
      st.readReg64 .x19 = chunkA →
      st.readReg64 .x20 = decA →
      st.readReg64 .x23 = BitVec.ofNat 64 i →
      st.readReg64 .x24 = chunk.index.zeroExtend 64 →
      st.readReg64 .x25 = 24#64 →
      (∀ (sf : State) (evs : List AllocEvent),
        AddChunkSlotsEnv (self.pts.drop i) evs →
        sf.pc = (blkPl_419).base + 476#64 →
        sf.status = .Running →
        AllocCallPreserved st sf →
        sf.sp = sp →
        sf.trace = s0.trace →
        sf.readReg64 .x29 = st.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs st →
        SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
          (sortedSetPtListOf A.repAlloc decA (addChunkBsearchLoop chunk i (rem + 1) self).pts ∗
            ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
            (chunkA ↦ₛ chunk.data.toList) ∗
            A.pool lim (M.stepEvents evs curSt) sf ∗ stackAt sp growOneStack ∗ F)
          Q Qp) →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc st
        (sortedSetPtListOf A.repAlloc decA self.pts ∗
          ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
          (chunkA ↦ₛ chunk.data.toList) ∗
          A.pool lim curSt st ∗ stackAt sp growOneStack ∗ F)
        Q Qp := by
  induction rem with
  | zero =>
    intro i self curSt st hirem hpts_len hneed hcap hfits hpc hrun hsp hsp_al htr hx14 hx19 hx20 hx23 hx24 hx25 hnext
    have hi : i < 16 := by omega
    have hi_pts : i < self.pts.length := by omega
    have hcap_i : (self.pts[i]'hi_pts).vec.length ≤ 65536 := hcap i hi_pts (Nat.le_refl i)
    have hdrop_cons : self.pts.drop i = (self.pts[i]'hi_pts) :: self.pts.drop (i + 1) :=
      drop_eq_cons_drop_succ self.pts hi_pts
    have hfits_i : FitsEnv M lim curSt (AddChunkSlotEnv (self.pts[i]'hi_pts)) := by
      have hseq : FitsEnv M lim curSt
          (SeqEnv (AddChunkSlotEnv (self.pts[i]'hi_pts)) (AddChunkSlotsEnv (self.pts.drop (i + 1)))) := by
        simpa only [hdrop_cons, AddChunkSlotsEnv] using hfits
      exact hseq.seq_left
    have _hbeq16 : (BitVec.ofNat 64 (i + 1) == 16#64) = true := by
      rw [bv64_add1_beq16 hi, decide_eq_true_eq]; omega
    rw [← hsp]
    refine addChunk_body_placed_wpp hmemmove_sat hgrow_full hgrow_empty decA chunkA self chunk i curSt
      hi hpts_len hneed hcap_i hfits_i
      hpc hrun hsp_al htr hx14 hx19 hx20 hx23 hx24 hx25
      (fun s1 evs1 hevs1 hpc1 hrun1 hacp1 hsp1 htr1 _hx14_1 _hx19_1 _hx20_1 _hx23_1 _hx24_1 _hx25_1 hx29_1 hvregs_1 => ?_)
    rw [hsp]
    have hslots : AddChunkSlotsEnv (self.pts.drop i) evs1 := by
      rw [hdrop_cons]
      exact SeqEnv.inl hevs1
    apply SepWPp.of_sepWP (mid := (blkPl_419).base + 476#64)
    apply sepWP_with_vm
    by_vm_steps
      wp_steps 3
      refine SepWP.done
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun1])
        ⟨by simp [wp_norm, arm64_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      exact hnext _ evs1 hslots
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun1])
        (allocCallPreserved_trans hacp1 (by simp [AllocCallPreserved, wp_norm, arm64_norm]))
        (by simpa [wp_norm, arm64_norm, hsp] using hsp1)
        (by simpa [wp_norm, arm64_norm] using htr1)
        (by simpa [wp_norm, arm64_norm] using hx29_1)
        (by simpa [wp_norm, arm64_norm] using hvregs_1)
  | succ rem ih =>
    intro i self curSt st hirem hpts_len hneed hcap hfits hpc hrun hsp hsp_al htr hx14 hx19 hx20 hx23 hx24 hx25 hnext
    have hi : i < 16 := by omega
    have hi_pts : i < self.pts.length := by omega
    have hcap_i : (self.pts[i]'hi_pts).vec.length ≤ 65536 := hcap i hi_pts (Nat.le_refl i)
    have hdrop_cons : self.pts.drop i = (self.pts[i]'hi_pts) :: self.pts.drop (i + 1) :=
      drop_eq_cons_drop_succ self.pts hi_pts
    have hseq : FitsEnv M lim curSt
        (SeqEnv (AddChunkSlotEnv (self.pts[i]'hi_pts)) (AddChunkSlotsEnv (self.pts.drop (i + 1)))) := by
      simpa only [hdrop_cons, AddChunkSlotsEnv] using hfits
    have hfits_i : FitsEnv M lim curSt (AddChunkSlotEnv (self.pts[i]'hi_pts)) := hseq.seq_left
    have _hbeq16 : (BitVec.ofNat 64 (i + 1) == 16#64) = false := by
      rw [bv64_add1_beq16 hi, decide_eq_false_iff_not]; omega
    rw [← hsp]
    refine addChunk_body_placed_wpp hmemmove_sat hgrow_full hgrow_empty decA chunkA self chunk i curSt
      hi hpts_len hneed hcap_i hfits_i
      hpc hrun hsp_al htr hx14 hx19 hx20 hx23 hx24 hx25
      (fun s1 evs1 hevs1 hpc1 hrun1 hacp1 hsp1 htr1 hx14_1 hx19_1 hx20_1 _hx23_1 hx24_1 hx25_1 hx29_1 hvregs_1 => ?_)
    rw [hsp]
    have hsp_al1 : s1.spAligned = true := by
      unfold State.spAligned at hsp_al ⊢
      rwa [hsp1]
    have hpts_len' : (addChunkBsearchStep chunk i self).pts.length = 16 := by
      rw [addChunkBsearchStep_pts_length]; exact hpts_len
    have hneed' : (addChunkBsearchStep chunk i self).ptsNeeded < 2 ^ 64 := by
      rw [addChunkBsearchStep_ptsNeeded]; exact hneed
    have hcap' : ∀ j (hj : j < (addChunkBsearchStep chunk i self).pts.length),
        i + 1 ≤ j → ((addChunkBsearchStep chunk i self).pts[j]'hj).vec.length ≤ 65536 := by
      intro j hj hij
      have hj0 : j < self.pts.length := by rw [← addChunkBsearchStep_pts_length chunk i self]; exact hj
      rw [addChunkBsearchStep_getElem_after chunk self hi (by omega) hj0]
      exact hcap j hj0 (by omega)
    have hdrop_after := addChunkBsearchStep_drop_after chunk self hi hpts_len
    have hfits_rest : FitsEnv M lim (M.stepEvents evs1 curSt)
        (AddChunkSlotsEnv ((addChunkBsearchStep chunk i self).pts.drop (i + 1))) := by
      rw [hdrop_after]
      exact hseq.seq_right hevs1
    have hstep := ih (i + 1) (addChunkBsearchStep chunk i self) (M.stepEvents evs1 curSt)
    apply SepWPp.of_sepWP (mid := (blkPl_419).base + 76#64)
    apply sepWP_with_vm
    by_vm_steps
      wp_steps 3
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        ⟨by simp [wp_norm, arm64_norm], fun hvm_mid => ?_⟩
      rw [← A.pool_of_vmPreserved hvm_mid, ← addChunkBsearchStep_ptsNeeded chunk i self]
      refine hstep _ (by omega) hpts_len' hneed' hcap' hfits_rest
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        (by simpa [wp_norm, arm64_norm, hsp] using hsp1) (by simpa [wp_norm, arm64_norm] using hsp_al1)
        (by simpa [wp_norm, arm64_norm] using htr1) (by simp [wp_norm, arm64_norm, hx14_1])
        (by simp [wp_norm, arm64_norm, hx19_1]) (by simp [wp_norm, arm64_norm, hx20_1])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx24_1])
        (by simp [wp_norm, arm64_norm, hx25_1])
        (fun sf evs2 hevs2 hpc_f hrun_f hacp_f hsp_f htr_f hx29_f hvregs_f => ?_)
      rw [addChunkBsearchStep_ptsNeeded chunk i self]
      rw [hdrop_after] at hevs2
      have hslots : AddChunkSlotsEnv (self.pts.drop i) (evs1 ++ evs2) := by
        rw [hdrop_cons]
        exact SeqEnv.append hevs1 hevs2
      have hstep_ev : M.stepEvents evs2 (M.stepEvents evs1 curSt) = M.stepEvents (evs1 ++ evs2) curSt := by
        rw [M.stepEvents_append]
      rw [hstep_ev]
      exact hnext sf (evs1 ++ evs2) hslots hpc_f hrun_f
        (allocCallPreserved_trans hacp1
          (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]) hacp_f))
        hsp_f htr_f
        (by simpa [wp_norm, arm64_norm, hx29_1] using hx29_f)
        (by simpa [wp_norm, arm64_norm, hvregs_1] using hvregs_f)

/-! ## Placed Top-Level Theorems (`add_chunk_bsearch_placed_ok_ext`, `add_chunk_placed_ok_ext`, `add_chunk_placed_ok_x`) -/

private theorem addChunk_epilogue_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {R : SepProp} (x : AddChunkGhost) (st0 : M.σ) (evs : List AllocEvent)
    (s0 s1 sf : State)
    (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hpts_len : x.dec.pts.length = 16)
    (hneed : x.dec.ptsNeeded < 2 ^ 64)
    (hevs_env : AddChunkEnv x evs)
    (hacp01 : AllocCallPreserved s0 s1)
    (hacp1f : AllocCallPreserved s1 sf)
    (hpc_f : sf.pc = (blkPl_419).base + 476#64)
    (hrun_f : sf.status = .Running)
    (hsp_f : sf.sp = s0.sp - 96#64)
    (htr_f : sf.trace = s0.trace)
    (hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) (s0.readReg64 .lr) sf
      (sortedSetPtListOf A.repAlloc x.decA (addChunkBsearch x.dec x.chunk).pts ∗
        ((x.decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
        (x.chunkA ↦ₛ x.chunk.data.toList) ∗
        A.pool lim (M.stepEvents evs st0) sf ∗
        stackAt (s0.sp - 96#64) growOneStack ∗
        (((x.decA + polyDecoderIsCompleteOff) ↦₈ boolByte x.dec.isComplete) ∗
          memRegion (x.decA + polyDecoderPadOff) polyDecoderPadSize ∗ ((x.chunkA + 32#64) ↦₁₆ x.chunk.index) ∗
          ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (fun sf' P_f =>
        ((sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ (addChunkBsearchSpec M A lim).post (x, st0) s0 sf' ∗ R)) ∧
        sf'.sp = s0.sp ∧ CalleeSavedPreserved s0 sf')
      (fun sf' P_f =>
        (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ (addChunkBsearchSpec M A lim).onPanic (x, st0) s0 sf' ∗ R))
      (fun sf' => (addChunkBsearchSpec M A lim).onOom (x, st0) s0 sf') := by
  apply SepWPp.of_sepWP_ret
  apply sepWP_seq_with_vm
  by_vm_steps (
    wp_steps 7
    refine SepWP.done (by simp [hpc_f, hsp_f, hsp0, wp_norm, arm64_norm])
      (by simp [hsp_f, hsp0, wp_norm, arm64_norm, hrun_f])
      ⟨by simp [wp_norm, arm64_norm], fun hvm_ep => ?_⟩
    rw [← A.pool_of_vmPreserved hvm_ep]
    have hacp_tot := acp_of_vm_chain hvm_ep hacp01 hacp1f
      (by simp [AllocCallPreserved, wp_norm, arm64_norm])
    refine SepWP.done (by simp [hpc_f, hsp_f, hsp0, wp_norm, arm64_norm])
      (by simp [hsp_f, hsp0, wp_norm, arm64_norm, hrun_f])
      ⟨fun hm => by
         dsimp only [addChunkBsearchSpec]
         rw [sepExists_sepConj_left, satisfies_sepExists]
         refine ⟨evs, Satisfies.mono (sepConj_mono_left ?_) hm⟩
         refine Entails.pure_right ⟨by simp [htr_f, wp_norm, arm64_norm], hacp_tot, hevs_env⟩ ?_
         unfold polyDecoderAt chunkAt
         dsimp only [chunkIndexOff, NUM_POLYS]
         rw [addChunkBsearch_pts_length, addChunkBsearch_ptsNeeded, addChunkBsearch_isComplete,
             stackAt_addChunk_split s0.sp, sepConj_assoc]
         refine Entails.pure_right ⟨hpts_len, hneed⟩ ?_
         generalize (addChunkBsearch x.dec x.chunk).pts = pts_out
         sep_frame,
       by simp [hsp_f, wp_norm, arm64_norm],
       ⟨by simp [hsp_f, wp_norm, arm64_norm], by simp [hsp_f, wp_norm, arm64_norm],
        by simp [hsp_f, wp_norm, arm64_norm], by simp [hsp_f, wp_norm, arm64_norm],
        by simp [hsp_f, wp_norm, arm64_norm], by simp [hsp_f, wp_norm, arm64_norm],
        by simp [hsp_f, wp_norm, arm64_norm], by simp [hsp_f, wp_norm, arm64_norm],
        by simp [hsp_f, wp_norm, arm64_norm], by simp [hsp_f, wp_norm, arm64_norm],
        by simp [hsp_f, wp_norm, arm64_norm],
        by simpa [CalleeSavedVRegsPreserved, calleeSavedVRegs, wp_norm, arm64_norm] using hvregs_f⟩⟩)

set_option maxHeartbeats 800000 in
theorem add_chunk_bsearch_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtFullSpec M A lim)))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtSpec M A lim))) :
    subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (addChunkBsearchSpec M A lim) := by
  refine subroutine_ok_of_sepWPp_init fun ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align => ?_
  dsimp only [addChunkBsearchSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hcap, hfits⟩, hpre_sp⟩
  refine ⟨_, hpre_sp, ?_⟩
  unfold polyDecoderAt chunkAt
  dsimp only [chunkIndexOff, NUM_POLYS]
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨hpts_len, hneed⟩ => ?_
  rw [stackAt_addChunk_split s0.sp]
  have hsp0 : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_align
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = x.decA := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = x.chunkA := hx1
  have hloop := @addChunk_loop_placed_wpp _ M A lim ext hmemmove_sat hgrow_full hgrow_empty (s0.readReg64 .lr) s0
  apply SepWPp.of_sepWP (mid := (blkPl_419).base + 76#64)
  apply sepWP_with_vm
  by_vm_steps (
    wp_pull_exists
    wp_steps 14
    refine SepWP.done (by simp [hpc, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      ⟨by simp [wp_norm, arm64_norm], fun hvm0 => ?_⟩
    rw [← A.pool_of_vmPreserved hvm0]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hloop (F := ((x.decA + polyDecoderIsCompleteOff) ↦₈ boolByte x.dec.isComplete) ∗
          memRegion (x.decA + polyDecoderPadOff) polyDecoderPadSize ∗ ((x.chunkA + 32#64) ↦₁₆ x.chunk.index) ∗
          ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        x.decA x.chunkA (s0.sp - 96#64) x.chunk 15 0 x.dec st0 _ rfl hpts_len hneed
        (fun j hj _ => hcap (x.dec.pts[j]'hj) (List.getElem_mem hj))
        (hfits : FitsEnv M lim st0 (AddChunkSlotsEnv x.dec.pts))
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
        (by simp [State.spAligned, wp_norm, arm64_norm, hsp0]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [hx1', wp_norm, arm64_norm]) (by simp [hx0', wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (fun sf evs hevs hpc_f hrun_f hacp_f hsp_f htr_f _hx29_f hvregs_f => ?_))
    exact addChunk_epilogue_placed_wpp x st0 evs s0 _ sf hsp0 hpts_len hneed
      (by simpa [AddChunkEnv] using hevs)
      (by simp [AllocCallPreserved, wp_norm, arm64_norm])
      hacp_f hpc_f hrun_f hsp_f htr_f
      (by simpa [wp_norm, arm64_norm] using hvregs_f))

theorem add_chunk_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtFullSpec M A lim)))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtSpec M A lim))) :
    AddChunkPlacedOkExt M A lim ext := by
  refine subroutine_ok_outcome_intro fun ⟨x, st0⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [addChunkSpec, polyDecoderAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hsort, hfits⟩, ⟨hlen, hneed⟩, hmem⟩
  have hcap : ∀ s ∈ x.dec.pts, s.vec.length ≤ 65536 :=
    fun s hs => ptListStrictSorted_length_le (hsort s hs)
  have hpre_b : s0.mem ⊨ (addChunkBsearchSpec M A lim).pre (x, st0) s0 ∗ R := by
    simp only [addChunkBsearchSpec, polyDecoderAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hcap, hfits⟩, ⟨hlen, hneed⟩, hmem⟩
  refine (add_chunk_bsearch_placed_ok_ext hmemmove_sat hgrow_full hgrow_empty).mono_outcome (x, st0) R s0 hpc hrun hpre_b hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hb_eq, hsort'⟩ := addChunkBsearch_eq_addChunkTotal x.dec x.chunk hlen hsort
    simp only [addChunkBsearchSpec, addChunkSpec, hb_eq, sepExists_sepConj_left,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨evs, ⟨htr, hacp, hevs⟩, hmem_f⟩
    exact ⟨evs, ⟨htr, hacp, hevs, hsort'⟩, hmem_f⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact (not_satisfies_false_sepConj hq).elim

/-- `addChunkSpec M A lim` entails `addChunkSpecX M A lim` by framing the unused bottom stack region. -/
theorem addChunkSpecX_of_addChunkSpec {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok P addr (addChunkSpec M A lim)) :
    subroutine_ok P addr (addChunkSpecX M A lim) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hle : addChunkStack ≤ addChunkStackX := by decide
  have hsplit : stackAt s0.sp addChunkStackX =
      memRegion (s0.sp - BitVec.ofNat 64 addChunkStackX)
        (addChunkStackX - addChunkStack) ∗
        stackAt s0.sp addChunkStack := by
    have h1 := stackAt_split_bottom s0.sp addChunkStack
      (addChunkStackX - addChunkStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 addChunkStackX)
      (addChunkStackX - addChunkStack) ∗ R
  have hpre' : s0.mem ⊨ (addChunkSpec M A lim).pre x s0 ∗ R' := by
    dsimp only [addChunkSpecX, addChunkSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    convert hpre using 1; sep_ac_rfl
  refine (h.to_outcome x R' s0 hpc hrun hpre' hal).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [addChunkSpecX, addChunkSpec, R'] at hpost ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    convert hpost using 1; sep_ac_rfl
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem add_chunk_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtFullSpec M A lim)))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtSpec M A lim))) :
    AddChunkPlacedOkX M A lim ext :=
  addChunkSpecX_of_addChunkSpec (add_chunk_placed_ok_ext hmemmove_sat hgrow_full hgrow_empty)

end LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudget
