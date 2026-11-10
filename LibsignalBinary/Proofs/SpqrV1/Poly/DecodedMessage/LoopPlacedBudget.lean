/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Loop
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Loop Lemmas for `<PolyDecoder as Decoder>::decoded_message`

Threads `RustCliAllocBudget M` (`A.repAlloc`) and `VmPreserved` across the binary-search and
`collectPointsVecs` loops on Block `418`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.LoopPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkPC_418 blkPl_418)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalSpqrV1 (PolyDecoder Pt)
open CryptoVerification.SpqrV1.Poly (
  ptAt ptSliceAt sortedSetPtListPinAt
)
open CryptoVerification.SpqrV1.Poly.AddChunk (
  bsearchLoop bsearchLoop_bounds bv32_ult_zeroExtend16 bv64_beq_one_ofNat bv64_lsl2_ofNat
  bv64_lsr1_ofNat bv64_madd24_ofNat bv64_sub_ofNat bv64_ule_ofNat bv64_ult_ofNat
  bv64_ult_one_ofNat cinc_necessaryPoints_eq necessaryPoints_lt ptSliceAt_focus
)
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  bv64_beq_15_ofNat bv64_beq_16_ofNat bv64_bne_16_ofNat bv64_lsl4_ofNat
  memRegion_16_mul_split_one memRegion_256_focus16 memRegion_256_unfocus16
  ptSliceRefAt ptSliceRefListAt ptSliceRefListAt_take_succ
  sortedSetPtListPinAt_focus sortedSetPtPinAt_eq_slice sortedSetPtPinRest
  sp672_aligned traceVRegs
)
open LibsignalBinary.Heap (AllocCostModel RustCliAllocBudget VmPreserved)
open scoped CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

/-! ## Binary Search Loop (`(blkPl_418).base + 568#64` to `(blkPl_418).base + 624#64`) -/

theorem bsearchLoop_decodedMessage_placed_sepWP [LibsignalPlacement] {ext : String → Option (State → State)}
    {ret_pc : BitVec 64}
    (vec : List Pt) (ptr : BitVec 64) (xVal : BitVec 16)
    (hlen_bound : 4 * vec.length < 2 ^ 64) :
    ∀ (size base : Nat) (s : State) (P : SepProp) (post : State → SepProp → Prop),
      1 < size →
      base + size ≤ vec.length →
      s.pc = (blkPl_418).base + 584#64 →
      s.status = .Running →
      s.readReg64 .x8 = ptr →
      s.readReg64 .x9 = xVal.zeroExtend 64 →
      s.readReg64 .x10 = BitVec.ofNat 64 size →
      s.readReg64 .x11 = BitVec.ofNat 64 base →
      (∀ (sf : State),
        sf.pc = (blkPl_418).base + 620#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        traceVRegs sf = traceVRegs s →
        VmPreserved s sf →
        sf.readReg64 .x0 = s.readReg64 .x0 →
        sf.readReg64 .x8 = ptr →
        sf.readReg64 .x9 = xVal.zeroExtend 64 →
        sf.readReg64 .x11 = BitVec.ofNat 64 (bsearchLoop vec xVal base size) →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x22 = s.readReg64 .x22 →
        sf.readReg64 .x23 = s.readReg64 .x23 →
        sf.readReg64 .x24 = s.readReg64 .x24 →
        sf.readReg64 .x25 = s.readReg64 .x25 →
        sf.readReg64 .x26 = s.readReg64 .x26 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        sf.readReg64 .x30 = s.readReg64 .x30 →
        SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf (ptSliceAt ptr vec ∗ P) post) →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s (ptSliceAt ptr vec ∗ P) post := by
  try dsimp only [BitVec.ofNat_eq_ofNat]
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro base s P post hgt hle hpc hstat hx8 hx9 hx10 hx11 hcont
    have hhalf_pos : 0 < size / 2 := Nat.div_pos (by omega) (by decide)
    have hmid_lt : base + size / 2 < vec.length := by omega
    have hsize_lt64 : size < 2 ^ 64 := by omega
    have hlsr : (BitVec.ofNat 64 size) >>> 1 = BitVec.ofNat 64 (size / 2) :=
      bv64_lsr1_ofNat hsize_lt64
    have hadd_mid : BitVec.ofNat 64 (size / 2) + BitVec.ofNat 64 base =
        BitVec.ofNat 64 (base + size / 2) := by
      rw [← BitVec.ofNat_add, Nat.add_comm]
    have hsub_size : BitVec.ofNat 64 size - BitVec.ofNat 64 (size / 2) =
        BitVec.ofNat 64 (size - size / 2) :=
      bv64_sub_ofNat (by omega) hsize_lt64
    have hlsl_mid : (BitVec.ofNat 64 (base + size / 2)) <<< 2 =
        BitVec.ofNat 64 (4 * (base + size / 2)) :=
      bv64_lsl2_ofNat (by omega)
    have hmid_get : vec[base + size / 2]?.getD default = vec[base + size / 2]'hmid_lt := by
      rw [List.getElem?_eq_getElem hmid_lt, Option.getD_some]
    let base' := if xVal.toNat < (vec[base + size / 2]'hmid_lt).x.value.toNat then base else base + size / 2
    have hcsel :
        (if (BitVec.zeroExtend 32 xVal).ult
            (BitVec.zeroExtend 32 (vec[base + size / 2]'hmid_lt).x.value) = true then
          BitVec.ofNat 64 base
        else BitVec.ofNat 64 (base + size / 2)) = BitVec.ofNat 64 base' := by
      rw [bv32_ult_zeroExtend16]
      by_cases hlt : xVal.toNat < (vec[base + size / 2]'hmid_lt).x.value.toNat <;> simp [base', hlt]
    have hfold_slice :
        ((ptSliceAt ptr (List.take (base + size / 2) vec) ∗
          ((ptr + BitVec.ofNat 64 (4 * (base + size / 2))) ↦₁₆ (vec[base + size / 2]'hmid_lt).x.value ∗
            (ptr + BitVec.ofNat 64 (4 * (base + size / 2)) + 2#64) ↦₁₆ (vec[base + size / 2]'hmid_lt).y.value) ∗
          ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + size / 2 + 1))) (List.drop (base + size / 2 + 1) vec)) ∗
          P) = (ptSliceAt ptr vec ∗ P) := by
      change ((ptSliceAt ptr (List.take (base + size / 2) vec) ∗
        ptAt (vec[base + size / 2]'hmid_lt) (ptr + BitVec.ofNat 64 (4 * (base + size / 2))) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + size / 2 + 1))) (List.drop (base + size / 2 + 1) vec)) ∗
        P) = (ptSliceAt ptr vec ∗ P)
      rw [← ptSliceAt_focus vec (base + size / 2) ptr hmid_lt]
    rw [ptSliceAt_focus vec (base + size / 2) ptr hmid_lt]
    unfold ptAt
    wp_steps
    rw [hfold_slice, bv64_ult_one_ofNat (by omega)]
    have hbs_step : bsearchLoop vec xVal base size = bsearchLoop vec xVal base' (size - size / 2) := by
      conv_lhs => rw [bsearchLoop]
      simp only [hgt, ↓reduceDIte, hmid_get]
      rfl
    by_cases hgt' : 1 < size - size / 2
    · simp only [hgt', decide_true, ↓reduceIte]
      refine ih (size - size / 2) (by omega) base' _ P post hgt' (by dsimp [base']; split_ifs <;> omega)
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hstat])
        (by simp [wp_norm, arm64_norm, hx8])
        (by simp [wp_norm, arm64_norm, hx9])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm])
        (fun sf hpc_f hstat_f hsp_f htr_f hvm_f hx0_f hx8_f hx9_f hx11_f hx20_f hx22_f hx23_f hx24_f hx25_f hx26_f hx29_f hx30_f => ?_)
      apply hcont sf hpc_f hstat_f
      · simpa [wp_norm, arm64_norm] using hsp_f
      · simpa [wp_norm, arm64_norm] using htr_f
      · exact (by simp [wp_norm, arm64_norm] : VmPreserved s _).trans hvm_f
      · simpa [wp_norm, arm64_norm] using hx0_f
      · exact hx8_f
      · exact hx9_f
      · rw [hbs_step]; exact hx11_f
      · simpa [wp_norm, arm64_norm] using hx20_f
      · simpa [wp_norm, arm64_norm] using hx22_f
      · simpa [wp_norm, arm64_norm] using hx23_f
      · simpa [wp_norm, arm64_norm] using hx24_f
      · simpa [wp_norm, arm64_norm] using hx25_f
      · simpa [wp_norm, arm64_norm] using hx26_f
      · simpa [wp_norm, arm64_norm] using hx29_f
      · simpa [wp_norm, arm64_norm] using hx30_f
    · simp only [hgt', decide_false, Bool.false_eq_true, ↓reduceIte]
      have hbs_done : bsearchLoop vec xVal base size = base' := by
        rw [hbs_step, bsearchLoop]
        simp [hgt']
      apply hcont
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hstat]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hx8]
      · simp [wp_norm, arm64_norm, hx9]
      · rw [hbs_done]; simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]

theorem bsearch_to_624_placed_sepWP [LibsignalPlacement] {ext : String → Option (State → State)}
    {ret_pc : BitVec 64}
    {ptr : BitVec 64} {vec : List Pt} {xVal : BitVec 16}
    (h1 : 1 ≤ vec.length) (hlen : vec.length ≤ 65536)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 572#64)
    (hstat : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = xVal.zeroExtend 64)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 vec.length)
    (hcont : ∀ (sf : State),
      sf.pc = (blkPl_418).base + 624#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      traceVRegs sf = traceVRegs s →
      VmPreserved s sf →
      sf.readReg64 .x0 = s.readReg64 .x0 →
      sf.readReg64 .x8 = ptr + BitVec.ofNat 64 (4 * bsearchLoop vec xVal 0 vec.length) →
      sf.readReg64 .x9 = xVal.zeroExtend 64 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.readReg64 .x30 = s.readReg64 .x30 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf (ptSliceAt ptr vec ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s (ptSliceAt ptr vec ∗ P) post := by
  have hloop := @bsearchLoop_decodedMessage_placed_sepWP _ ext ret_pc vec ptr xVal (by omega)
  try dsimp only [BitVec.ofNat_eq_ofNat] at hloop hpc hcont ⊢
  wp_steps 2
  rw [bv64_beq_one_ofNat (by omega)]
  by_cases heq1 : vec.length = 1
  · simp only [heq1, decide_true, ↓reduceIte]
    have hbs1 : bsearchLoop vec xVal 0 vec.length = 0 := by
      rw [heq1, bsearchLoop]; simp
    apply hcont
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hstat]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hx8, hbs1]
    · simp [wp_norm, arm64_norm, hx9]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
  · simp only [heq1, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_steps 1
    refine hloop vec.length 0 _ P post (by omega) (by omega)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      (by simp [wp_norm, arm64_norm, hx8])
      (by simp [wp_norm, arm64_norm, hx9])
      (by simp [wp_norm, arm64_norm, hx10])
      (by simp [wp_norm, arm64_norm])
      (fun s1 hpc1 hstat1 hsp1 htr1 hvm1 hx0_1 hx8_1 hx9_1 hx11_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx29_1 hx30_1 => ?_)
    have ⟨_, hb_lt⟩ := bsearchLoop_bounds vec xVal 0 vec.length h1 (by omega)
    have hlsl_b : (BitVec.ofNat 64 (bsearchLoop vec xVal 0 vec.length)) <<< 2 =
        BitVec.ofNat 64 (4 * bsearchLoop vec xVal 0 vec.length) :=
      bv64_lsl2_ofNat (by omega)
    have hvm01 : VmPreserved s s1 :=
      (by simp [wp_norm, arm64_norm] : VmPreserved s _).trans hvm1
    wp_steps 1
    apply hcont
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hstat1]
    · simpa [wp_norm, arm64_norm] using hsp1
    · simpa [wp_norm, arm64_norm] using htr1
    · exact hvm01.trans (by simp [wp_norm, arm64_norm])
    · simpa [wp_norm, arm64_norm] using hx0_1
    · simp [wp_norm, arm64_norm, hx8_1, hlsl_b]
    · simpa [wp_norm, arm64_norm] using hx9_1
    · simpa [wp_norm, arm64_norm] using hx20_1
    · simpa [wp_norm, arm64_norm] using hx22_1
    · simpa [wp_norm, arm64_norm] using hx23_1
    · simpa [wp_norm, arm64_norm] using hx24_1
    · simpa [wp_norm, arm64_norm] using hx25_1
    · simpa [wp_norm, arm64_norm] using hx26_1
    · simpa [wp_norm, arm64_norm] using hx29_1
    · simpa [wp_norm, arm64_norm] using hx30_1

/-! ## `collectPointsVecs` When `.1 = false` (`(blkPl_418).base + 128#64` to `(blkPl_418).base + 352#64`) -/

theorem collectPointsVecs_ok_step_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (dec : PolyDecoder) (decA pv_ptr sp0 : BitVec 64) (pins : List VecPin) (i : Nat)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16) (hi : i < 16)
    (hneed : dec.ptsNeeded < 2 ^ 64)
    (hlen_bound : ∀ s ∈ dec.pts, s.vec.length ≤ 65536)
    (hge : dec.necessaryPoints i ≤ (dec.pts[i]'(by rw [hpts]; exact hi)).len)
    (hsp0 : sp0 &&& 15#64 = 0#64)
    (s : State) (pvLenOld : BitVec 64) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 128#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx0 : s.readReg64 .x0 = pv_ptr)
    (hx20 : s.readReg64 .x20 = decA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 i)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (dec.ptsNeeded / 16))
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (dec.ptsNeeded % 16))
    (hx24 : s.readReg64 .x24 = decA + 40#64)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 i)
    (hcont : ∀ sf : State,
      sf.pc = (if i + 1 = 16 then
        (blkPl_418).base + 284#64
      else
        (blkPl_418).base + 128#64) →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      VmPreserved s sf →
      sf.readReg64 .x0 = pv_ptr →
      sf.readReg64 .x20 = decA →
      sf.readReg64 .x21 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x22 = BitVec.ofNat 64 (dec.ptsNeeded / 16) →
      sf.readReg64 .x23 = BitVec.ofNat 64 (dec.ptsNeeded % 16) →
      sf.readReg64 .x24 = decA + 40#64 →
      sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = 0#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.readReg64 .x30 = s.readReg64 .x30 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((sp0 - 624#64) ↦₆₄ 16#64) ∗
          ((sp0 - 608#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
          sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
          ptSliceRefListAt dec 0 pv_ptr (pins.take (i + 1)) ∗
          memRegion (pv_ptr + BitVec.ofNat 64 (16 * (i + 1))) (16 * (16 - (i + 1))) ∗ P)
        post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (((sp0 - 624#64) ↦₆₄ 16#64) ∗
        ((sp0 - 608#64) ↦₆₄ pvLenOld) ∗
        sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
        ptSliceRefListAt dec 0 pv_ptr (pins.take i) ∗
        memRegion (pv_ptr + BitVec.ofNat 64 (16 * i)) (16 * (16 - i)) ∗ P)
      post := by
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have hi_pts : i < dec.pts.length := by rw [hpts]; exact hi
  have hi_pins : i < pins.length := by omega
  have hmem_pts : dec.pts[i]'hi_pts ∈ dec.pts := List.getElem_mem hi_pts
  have hlen_le : (dec.pts[i]'hi_pts).vec.length ≤ 65536 := hlen_bound _ hmem_pts
  have hnec_lt : dec.necessaryPoints i < 2 ^ 64 := necessaryPoints_lt dec i hneed
  have hcinc := cinc_necessaryPoints_eq dec hi hneed
  have hmadd := bv64_madd24_ofNat decA hi
  have hule_len :
      (BitVec.ofNat 64 (dec.necessaryPoints i)).ule
        (BitVec.ofNat 64 (dec.pts[i]'hi_pts).vec.length) = true := by
    rw [bv64_ule_ofNat hnec_lt (by omega), decide_eq_true_eq]
    exact hge
  have hbeq16 : (BitVec.ofNat 64 i == 16#64) = false := by
    rw [bv64_beq_16_ofNat (by omega), decide_eq_false_iff_not]; omega
  have hlsl4 : (BitVec.ofNat 64 i) <<< 4 = BitVec.ofNat 64 (16 * i) :=
    bv64_lsl4_ofNat (by omega)
  have hadd1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hbne16 : (BitVec.ofNat 64 (i + 1) != 16#64) = decide (i + 1 ≠ 16) :=
    bv64_bne_16_ofNat (by omega)
  have hreasm_pts :
      sortedSetPtListPinAt A.repAlloc decA (pins.take i) (dec.pts.take i) ∗
        (((decA + BitVec.ofNat 64 (24 * i)) ↦₆₄ (pins[i]'hi_pins).cap) ∗
          ((decA + BitVec.ofNat 64 (24 * i) + 8#64) ↦₆₄ (pins[i]'hi_pins).ptr) ∗
          ((decA + BitVec.ofNat 64 (24 * i) + 16#64) ↦₆₄ BitVec.ofNat 64 (dec.pts[i]'hi_pts).vec.length) ∗
          ptSliceAt (pins[i]'hi_pins).ptr (dec.pts[i]'hi_pts).vec ∗
          sortedSetPtPinRest A.repAlloc (pins[i]'hi_pins) (dec.pts[i]'hi_pts)) ∗
        sortedSetPtListPinAt A.repAlloc (decA + BitVec.ofNat 64 (24 * (i + 1)))
          (pins.drop (i + 1)) (dec.pts.drop (i + 1)) =
      sortedSetPtListPinAt A.repAlloc decA pins dec.pts := by
    rw [← sortedSetPtPinAt_eq_slice A.repAlloc (pins[i]'hi_pins) (dec.pts[i]'hi_pts) (decA + BitVec.ofNat 64 (24 * i)),
      ← sortedSetPtListPinAt_focus A.repAlloc pins dec.pts i decA (by rw [hpins, hpts]) hi_pts]
  have hreasm_ref :
      ptSliceRefListAt dec 0 pv_ptr (pins.take i) ∗
        (((pv_ptr + BitVec.ofNat 64 (16 * i)) ↦₆₄ (pins[i]'hi_pins).ptr) ∗
          ((pv_ptr + BitVec.ofNat 64 (16 * i) + 8#64) ↦₆₄ BitVec.ofNat 64 (dec.necessaryPoints i))) =
      ptSliceRefListAt dec 0 pv_ptr (pins.take (i + 1)) := by
    change ptSliceRefListAt dec 0 pv_ptr (pins.take i) ∗
      ptSliceRefAt (pv_ptr + BitVec.ofNat 64 (16 * i)) (pins[i]'hi_pins).ptr (dec.necessaryPoints i) = _
    exact ptSliceRefListAt_take_succ dec pins i pv_ptr hi_pins
  rw [sortedSetPtListPinAt_focus A.repAlloc pins dec.pts i decA (by rw [hpins, hpts]) hi_pts,
    sortedSetPtPinAt_eq_slice A.repAlloc (pins[i]'hi_pins) (dec.pts[i]'hi_pts) (decA + BitVec.ofNat 64 (24 * i)),
    memRegion_16_mul_split_one pv_ptr hi]
  wp_pull_exists
  refine seq_vm_clean
    (mid := if i + 1 = 16 then (blkPl_418).base + 284#64 else (blkPl_418).base + 128#64)
    (P_mid :=
      ((sp0 - 624#64) ↦₆₄ 16#64) ∗
        ((sp0 - 608#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
        sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
        ptSliceRefListAt dec 0 pv_ptr (pins.take (i + 1)) ∗
        memRegion (pv_ptr + BitVec.ofNat 64 (16 * (i + 1))) (16 * (16 - (i + 1))) ∗ P)
    (Q := fun sf =>
      sf.sp = sp0 - 672#64 ∧
      traceVRegs sf = traceVRegs s ∧
      sf.readReg64 .x0 = pv_ptr ∧
      sf.readReg64 .x20 = decA ∧
      sf.readReg64 .x21 = BitVec.ofNat 64 (i + 1) ∧
      sf.readReg64 .x22 = BitVec.ofNat 64 (dec.ptsNeeded / 16) ∧
      sf.readReg64 .x23 = BitVec.ofNat 64 (dec.ptsNeeded % 16) ∧
      sf.readReg64 .x24 = decA + 40#64 ∧
      sf.readReg64 .x25 = 24#64 ∧
      sf.readReg64 .x26 = 0#64 ∧
      sf.readReg64 .x27 = BitVec.ofNat 64 (i + 1) ∧
      sf.readReg64 .x29 = s.readReg64 .x29 ∧
      sf.readReg64 .x30 = s.readReg64 .x30)
    ?_ ?_
  · by_vm_steps (
      try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
      wp_steps 19
      refine SepWP.weaken_pre
        (show _ ⊢
            ((sp0 - 624#64) ↦₆₄ 16#64) ∗
              ((sp0 - 608#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
              sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
              ptSliceRefListAt dec 0 pv_ptr (pins.take (i + 1)) ∗
              memRegion (pv_ptr + BitVec.ofNat 64 (16 * (i + 1))) (16 * (16 - (i + 1))) ∗ P by
          rw [← hreasm_pts, ← hreasm_ref]
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      by_cases hi16 : i + 1 = 16
      · have hdec : decide (i + 1 ≠ 16) = false := by simp [hi16]
        exact SepWP.done (by simp [wp_norm, arm64_norm, hdec]; try omega) (by simp [wp_norm, arm64_norm, hstat])
          ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *]⟩
      · have hdec : decide (i + 1 ≠ 16) = true := by simp [hi16]
        exact SepWP.done (by simp [wp_norm, arm64_norm, hdec]; try omega) (by simp [wp_norm, arm64_norm, hstat])
          ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *]⟩)
  · rintro sf hpc_f hstat_f hvm_f ⟨hsp_f, htr_f, hx0_f, hx20_f, hx21_f, hx22_f, hx23_f,
      hx24_f, hx25_f, hx26_f, hx27_f, hx29_f, hx30_f⟩
    exact hcont sf hpc_f hstat_f hsp_f htr_f hvm_f hx0_f hx20_f hx21_f hx22_f hx23_f
      hx24_f hx25_f hx26_f hx27_f hx29_f hx30_f

theorem collectPointsVecs_ok_loop_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (dec : PolyDecoder) (decA pv_ptr sp0 : BitVec 64) (pins : List VecPin)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hneed : dec.ptsNeeded < 2 ^ 64)
    (hlen_bound : ∀ s ∈ dec.pts, s.vec.length ≤ 65536)
    (hge : ∀ i (hi : i < 16), dec.necessaryPoints i ≤ (dec.pts[i]'(by rw [hpts]; exact hi)).len)
    (hsp0 : sp0 &&& 15#64 = 0#64) :
    ∀ (rem i : Nat) (s : State) (pvLenOld : BitVec 64) (P : SepProp) (post : State → SepProp → Prop),
      i + (rem + 1) = 16 →
      s.pc = (blkPl_418).base + 128#64 →
      s.status = .Running →
      s.sp = sp0 - 672#64 →
      s.readReg64 .x0 = pv_ptr →
      s.readReg64 .x20 = decA →
      s.readReg64 .x21 = BitVec.ofNat 64 i →
      s.readReg64 .x22 = BitVec.ofNat 64 (dec.ptsNeeded / 16) →
      s.readReg64 .x23 = BitVec.ofNat 64 (dec.ptsNeeded % 16) →
      s.readReg64 .x24 = decA + 40#64 →
      s.readReg64 .x25 = 24#64 →
      s.readReg64 .x26 = 0#64 →
      s.readReg64 .x27 = BitVec.ofNat 64 i →
      (∀ sf : State,
        sf.pc = (blkPl_418).base + 352#64 →
        sf.status = .Running →
        sf.sp = sp0 - 672#64 →
        traceVRegs sf = traceVRegs s →
        VmPreserved s sf →
        sf.readReg64 .x0 = pv_ptr →
        sf.readReg64 .x20 = decA →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        sf.readReg64 .x30 = s.readReg64 .x30 →
        SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
          (((sp0 - 624#64) ↦₆₄ 16#64) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗ P)
          post) →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
        (((sp0 - 624#64) ↦₆₄ 16#64) ∗
          ((sp0 - 608#64) ↦₆₄ pvLenOld) ∗
          sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
          ptSliceRefListAt dec 0 pv_ptr (pins.take i) ∗
          memRegion (pv_ptr + BitVec.ofNat 64 (16 * i)) (16 * (16 - i)) ∗ P)
        post
  | 0, i, s, pvLenOld, P, post, hsum, hpc, hstat, hsp, hx0, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hcont => by
    have hi15 : i = 15 := by omega
    subst hi15
    have hstep := collectPointsVecs_ok_step_placed_sepWP (A := A) (ext := ext) (ret_pc := ret_pc)
      dec decA pv_ptr sp0 pins 15 hpts hpins (by decide) hneed hlen_bound (hge 15 (by decide)) hsp0
      s pvLenOld P post hpc hstat hsp hx0 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27
    simp only [show 15 + 1 = 16 from rfl, ↓reduceIte] at hstep
    refine hstep (fun s1 hpc1 hstat1 hsp1 htr1 hvm1 hx0_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx29_1 hx30_1 => ?_)
    try dsimp only [BitVec.ofNat_eq_ofNat] at hpc1 hcont ⊢
    have htake16 : pins.take 16 = pins := List.take_of_length_le (by omega)
    rw [htake16, show 16 * (16 - 16) = 0 from rfl, memRegion_zero, emp_sepConj]
    wp_steps 1
    apply hcont
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hstat1]
    · simpa [wp_norm, arm64_norm] using hsp1
    · simpa [wp_norm, arm64_norm] using htr1
    · exact hvm1.trans (by simp [wp_norm, arm64_norm])
    · simpa [wp_norm, arm64_norm] using hx0_1
    · simpa [wp_norm, arm64_norm] using hx20_1
    · simpa [wp_norm, arm64_norm] using hx29_1
    · simpa [wp_norm, arm64_norm] using hx30_1
  | rem + 1, i, s, pvLenOld, P, post, hsum, hpc, hstat, hsp, hx0, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hcont => by
    have hi : i < 16 := by omega
    have hne16 : i + 1 ≠ 16 := by omega
    have hstep := collectPointsVecs_ok_step_placed_sepWP (A := A) (ext := ext) (ret_pc := ret_pc)
      dec decA pv_ptr sp0 pins i hpts hpins hi hneed hlen_bound (hge i hi) hsp0
      s pvLenOld P post hpc hstat hsp hx0 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27
    simp only [hne16, ↓reduceIte] at hstep
    refine hstep (fun s1 hpc1 hstat1 hsp1 htr1 hvm1 hx0_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx29_1 hx30_1 => ?_)
    refine collectPointsVecs_ok_loop_placed_sepWP dec decA pv_ptr sp0 pins hpts hpins hneed hlen_bound hge hsp0
      rem (i + 1) s1 (BitVec.ofNat 64 (i + 1)) P post (by omega)
      hpc1 hstat1 hsp1 hx0_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1
      (fun sf hpc_f hstat_f hsp_f htr_f hvm_f hx0_f hx20_f hx29_f hx30_f => ?_)
    exact hcont sf hpc_f hstat_f hsp_f (htr_f.trans htr1) (hvm1.trans hvm_f) hx0_f hx20_f
      (hx29_f.trans hx29_1) (hx30_f.trans hx30_1)

/-! ## `collectPointsVecs` When `.1 = true` (`(blkPl_418).base + 128#64` to `(blkPl_418).base + 288#64`) -/

theorem scanNextValidPoly_loop_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (dec : PolyDecoder) (decA : BitVec 64) (pins : List VecPin)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hneed : dec.ptsNeeded < 2 ^ 64)
    (hlen_bound : ∀ s ∈ dec.pts, s.vec.length ≤ 65536) :
    ∀ (rem j : Nat) (s : State) (P : SepProp) (post : State → SepProp → Prop),
      j + rem = 15 →
      s.pc = (blkPl_418).base + 160#64 →
      s.status = .Running →
      s.readReg64 .x8 = BitVec.ofNat 64 j →
      s.readReg64 .x9 = decA + BitVec.ofNat 64 (24 * (j + 1)) + 16#64 →
      s.readReg64 .x22 = BitVec.ofNat 64 (dec.ptsNeeded / 16) →
      s.readReg64 .x23 = BitVec.ofNat 64 (dec.ptsNeeded % 16) →
      (∀ sf : State,
        sf.pc = (blkPl_418).base + 288#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        traceVRegs sf = traceVRegs s →
        VmPreserved s sf →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        sf.readReg64 .x30 = s.readReg64 .x30 →
        SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf (sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗ P) post) →
      (∀ (sf : State) (idx' : Nat),
        j < idx' →
        idx' < 16 →
        sf.pc = (blkPl_418).base + 192#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        traceVRegs sf = traceVRegs s →
        VmPreserved s sf →
        sf.readReg64 .x0 = s.readReg64 .x0 →
        sf.readReg64 .x8 = BitVec.ofNat 64 idx' →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x21 = s.readReg64 .x21 →
        sf.readReg64 .x22 = s.readReg64 .x22 →
        sf.readReg64 .x23 = s.readReg64 .x23 →
        sf.readReg64 .x24 = s.readReg64 .x24 →
        sf.readReg64 .x25 = s.readReg64 .x25 →
        sf.readReg64 .x26 = s.readReg64 .x26 →
        sf.readReg64 .x28 = BitVec.ofNat 64 (dec.necessaryPoints idx') →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        sf.readReg64 .x30 = s.readReg64 .x30 →
        SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf (sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗ P) post) →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s (sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗ P) post := by
  try dsimp only [BitVec.ofNat_eq_ofNat]
  intro rem
  induction rem with
  | zero =>
    intro j s P post hj_eq hpc hstat hx8 hx9 hx22 hx23 hcont_exit _
    have hj15 : j = 15 := by omega
    subst hj15
    wp_steps 2
    apply hcont_exit
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hstat]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
  | succ rem ih =>
    intro j s P post hj_eq hpc hstat hx8 hx9 hx22 hx23 hcont_exit hcont_found
    have hj15 : j ≠ 15 := by omega
    have hj_lt : j < 15 := by omega
    have hj1_lt : j + 1 < 16 := by omega
    have hj1_pts : j + 1 < dec.pts.length := by rw [hpts]; exact hj1_lt
    have hj1_pins : j + 1 < pins.length := by omega
    have hmem_pts : dec.pts[j + 1]'hj1_pts ∈ dec.pts := List.getElem_mem hj1_pts
    have hlen_le : (dec.pts[j + 1]'hj1_pts).vec.length ≤ 65536 := hlen_bound _ hmem_pts
    have hnec_lt : dec.necessaryPoints (j + 1) < 2 ^ 64 := necessaryPoints_lt dec (j + 1) hneed
    have hcinc := cinc_necessaryPoints_eq dec hj1_lt hneed
    have hbeq15 : (BitVec.ofNat 64 j == 15#64) = false := by
      rw [bv64_beq_15_ofNat (by omega), decide_eq_false_iff_not]; exact hj15
    have hadd1 : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
    have haddr_next : decA + BitVec.ofNat 64 (24 * (j + 1)) + 40#64 =
        decA + BitVec.ofNat 64 (24 * (j + 1 + 1)) + 16#64 := by
      rw [show (40#64 : BitVec 64) = 24#64 + 16#64 from rfl, ← BitVec.add_assoc,
        BitVec.add_assoc decA, show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_add]
      congr 2
    have hreasm_pts :
        (sortedSetPtListPinAt A.repAlloc decA (pins.take (j + 1)) (dec.pts.take (j + 1)) ∗
          (((decA + BitVec.ofNat 64 (24 * (j + 1))) ↦₆₄ (pins[j + 1]'hj1_pins).cap) ∗
            ((decA + BitVec.ofNat 64 (24 * (j + 1)) + 8#64) ↦₆₄ (pins[j + 1]'hj1_pins).ptr) ∗
            ((decA + BitVec.ofNat 64 (24 * (j + 1)) + 16#64) ↦₆₄ BitVec.ofNat 64 (dec.pts[j + 1]'hj1_pts).vec.length) ∗
            ptSliceAt (pins[j + 1]'hj1_pins).ptr (dec.pts[j + 1]'hj1_pts).vec ∗
            sortedSetPtPinRest A.repAlloc (pins[j + 1]'hj1_pins) (dec.pts[j + 1]'hj1_pts)) ∗
          sortedSetPtListPinAt A.repAlloc (decA + BitVec.ofNat 64 (24 * (j + 1 + 1))) (pins.drop (j + 1 + 1)) (dec.pts.drop (j + 1 + 1))) ∗ P =
        sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗ P := by
      rw [← sortedSetPtPinAt_eq_slice A.repAlloc (pins[j + 1]'hj1_pins) (dec.pts[j + 1]'hj1_pts) (decA + BitVec.ofNat 64 (24 * (j + 1))),
        ← sortedSetPtListPinAt_focus A.repAlloc pins dec.pts (j + 1) decA (by rw [hpins, hpts]) hj1_pts]
    rw [sortedSetPtListPinAt_focus A.repAlloc pins dec.pts (j + 1) decA (by rw [hpins, hpts]) hj1_pts,
      sortedSetPtPinAt_eq_slice A.repAlloc (pins[j + 1]'hj1_pins) (dec.pts[j + 1]'hj1_pts) (decA + BitVec.ofNat 64 (24 * (j + 1)))]
    by_cases hlt : (dec.pts[j + 1]'hj1_pts).vec.length < dec.necessaryPoints (j + 1)
    · have hult_true :
          ((BitVec.ofNat 64 (dec.pts[j + 1]'hj1_pts).vec.length).ult
            (BitVec.ofNat 64 (dec.necessaryPoints (j + 1)))) = true := by
        rw [bv64_ult_ofNat (by omega) hnec_lt, decide_eq_true_eq]; exact hlt
      wp_steps 8
      rw [hreasm_pts]
      refine ih (j + 1) _ P post (by omega)
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hstat])
        (by simp [wp_norm, arm64_norm, hadd1])
        (by simp [wp_norm, arm64_norm, haddr_next])
        (by simp [wp_norm, arm64_norm, hx22])
        (by simp [wp_norm, arm64_norm, hx23])
        (fun sf hpc_f hstat_f hsp_f htr_f hvm_f hx29_f hx30_f => ?_)
        (fun sf idx' hgt_idx hlt_idx hpc_f hstat_f hsp_f htr_f hvm_f hx0_f hx8_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hx26_f hx28_f hx29_f hx30_f => ?_)
      · apply hcont_exit sf hpc_f hstat_f
        · simpa [wp_norm, arm64_norm] using hsp_f
        · simpa [wp_norm, arm64_norm] using htr_f
        · exact (by simp [wp_norm, arm64_norm] : VmPreserved s _).trans hvm_f
        · simpa [wp_norm, arm64_norm] using hx29_f
        · simpa [wp_norm, arm64_norm] using hx30_f
      · apply hcont_found sf idx' (by omega) hlt_idx hpc_f hstat_f
        · simpa [wp_norm, arm64_norm] using hsp_f
        · simpa [wp_norm, arm64_norm] using htr_f
        · exact (by simp [wp_norm, arm64_norm] : VmPreserved s _).trans hvm_f
        · simpa [wp_norm, arm64_norm] using hx0_f
        · exact hx8_f
        · simpa [wp_norm, arm64_norm] using hx20_f
        · simpa [wp_norm, arm64_norm] using hx21_f
        · simpa [wp_norm, arm64_norm] using hx22_f
        · simpa [wp_norm, arm64_norm] using hx23_f
        · simpa [wp_norm, arm64_norm] using hx24_f
        · simpa [wp_norm, arm64_norm] using hx25_f
        · simpa [wp_norm, arm64_norm] using hx26_f
        · exact hx28_f
        · simpa [wp_norm, arm64_norm] using hx29_f
        · simpa [wp_norm, arm64_norm] using hx30_f
    · have hult_false :
          ((BitVec.ofNat 64 (dec.pts[j + 1]'hj1_pts).vec.length).ult
            (BitVec.ofNat 64 (dec.necessaryPoints (j + 1)))) = false := by
        rw [bv64_ult_ofNat (by omega) hnec_lt, decide_eq_false_iff_not]; exact hlt
      wp_steps 8
      rw [hreasm_pts]
      apply hcont_found _ (j + 1) (by omega) hj1_lt
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hstat]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hadd1]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hx22]
      · simp [wp_norm, arm64_norm, hx23]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hcinc]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]

theorem collectPointsVecs_none_loop_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (dec : PolyDecoder) (decA pv_ptr sp0 : BitVec 64) (pins : List VecPin)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hneed : dec.ptsNeeded < 2 ^ 64)
    (hlen_bound : ∀ s ∈ dec.pts, s.vec.length ≤ 65536)
    (hsp0 : sp0 &&& 15#64 = 0#64) :
    ∀ (rem i pvLen : Nat) (anyMissing : Bool) (s : State) (pvLenOld : BitVec 64)
      (P : SepProp) (post : State → SepProp → Prop),
      i + (rem + 1) = 16 →
      pvLen ≤ i →
      (anyMissing = true ∨
        ∃ k, i ≤ k ∧ ∃ hk : k < 16, (dec.pts[k]'(by rw [hpts]; exact hk)).len < dec.necessaryPoints k) →
      s.pc = (blkPl_418).base + 128#64 →
      s.status = .Running →
      s.sp = sp0 - 672#64 →
      s.readReg64 .x0 = pv_ptr →
      s.readReg64 .x20 = decA →
      s.readReg64 .x21 = BitVec.ofNat 64 pvLen →
      s.readReg64 .x22 = BitVec.ofNat 64 (dec.ptsNeeded / 16) →
      s.readReg64 .x23 = BitVec.ofNat 64 (dec.ptsNeeded % 16) →
      s.readReg64 .x24 = decA + 40#64 →
      s.readReg64 .x25 = 24#64 →
      s.readReg64 .x26 = (if anyMissing then 1#64 else 0#64) →
      s.readReg64 .x27 = BitVec.ofNat 64 i →
      (∀ (sf : State) (pvLenFinal : BitVec 64),
        sf.pc = (blkPl_418).base + 288#64 →
        sf.status = .Running →
        sf.sp = sp0 - 672#64 →
        traceVRegs sf = traceVRegs s →
        VmPreserved s sf →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        sf.readReg64 .x30 = s.readReg64 .x30 →
        SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
          (((sp0 - 624#64) ↦₆₄ 16#64) ∗
            ((sp0 - 608#64) ↦₆₄ pvLenFinal) ∗
            sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
            memRegion pv_ptr 256 ∗ P)
          post) →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
        (((sp0 - 624#64) ↦₆₄ 16#64) ∗
          ((sp0 - 608#64) ↦₆₄ pvLenOld) ∗
          sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
          memRegion pv_ptr 256 ∗ P)
        post := by
  have hscan := @scanNextValidPoly_loop_placed_sepWP _ M A ext ret_pc dec decA pins hpts hpins hneed hlen_bound
  try dsimp only [BitVec.ofNat_eq_ofNat] at hscan ⊢
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro i pvLen anyMissing s pvLenOld P post hsum hpv_le hinv
      hpc hstat hsp hx0 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hcont
    have hsp_align : s.sp &&& 15#64 = 0#64 := by
      rw [hsp]; exact sp672_aligned sp0 hsp0
    have hi : i < 16 := by omega
    have hi_pts : i < dec.pts.length := by rw [hpts]; exact hi
    have hi_pins : i < pins.length := by omega
    have hpv_lt : pvLen < 16 := by omega
    have hmem_pts : dec.pts[i]'hi_pts ∈ dec.pts := List.getElem_mem hi_pts
    have hlen_le : (dec.pts[i]'hi_pts).vec.length ≤ 65536 := hlen_bound _ hmem_pts
    have hnec_lt : dec.necessaryPoints i < 2 ^ 64 := necessaryPoints_lt dec i hneed
    have hcinc := cinc_necessaryPoints_eq dec hi hneed
    have hmadd := bv64_madd24_ofNat decA hi
    by_cases hge : dec.necessaryPoints i ≤ (dec.pts[i]'hi_pts).len
    · have hule_true :
          (BitVec.ofNat 64 (dec.necessaryPoints i)).ule
            (BitVec.ofNat 64 (dec.pts[i]'hi_pts).vec.length) = true := by
        rw [bv64_ule_ofNat hnec_lt (by omega), decide_eq_true_eq]; exact hge
      have hbeq16 : (BitVec.ofNat 64 pvLen == 16#64) = false := by
        rw [bv64_beq_16_ofNat (by omega), decide_eq_false_iff_not]; omega
      have hlsl4 : (BitVec.ofNat 64 pvLen) <<< 4 = BitVec.ofNat 64 (16 * pvLen) :=
        bv64_lsl4_ofNat (by omega)
      have hadd1_i : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
        rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
      have hadd1_pv : BitVec.ofNat 64 pvLen + 1#64 = BitVec.ofNat 64 (pvLen + 1) := by
        rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
      have hbne16 : (BitVec.ofNat 64 (i + 1) != 16#64) = decide (i + 1 ≠ 16) :=
        bv64_bne_16_ofNat (by omega)
      have hinv' :
          anyMissing = true ∨
            ∃ k, i + 1 ≤ k ∧ ∃ hk : k < 16, (dec.pts[k]'(by rw [hpts]; exact hk)).len < dec.necessaryPoints k := by
        rcases hinv with hmiss | ⟨k, hik, hk16, hlt_k⟩
        · exact Or.inl hmiss
        · have hne_ki : k ≠ i := by intro hki; subst hki; omega
          exact Or.inr ⟨k, by omega, hk16, hlt_k⟩
      have hreasm_pts :
          sortedSetPtListPinAt A.repAlloc decA (pins.take i) (dec.pts.take i) ∗
            (((decA + BitVec.ofNat 64 (24 * i)) ↦₆₄ (pins[i]'hi_pins).cap) ∗
              ((decA + BitVec.ofNat 64 (24 * i) + 8#64) ↦₆₄ (pins[i]'hi_pins).ptr) ∗
              ((decA + BitVec.ofNat 64 (24 * i) + 16#64) ↦₆₄ BitVec.ofNat 64 (dec.pts[i]'hi_pts).vec.length) ∗
              ptSliceAt (pins[i]'hi_pins).ptr (dec.pts[i]'hi_pts).vec ∗
              sortedSetPtPinRest A.repAlloc (pins[i]'hi_pins) (dec.pts[i]'hi_pts)) ∗
            sortedSetPtListPinAt A.repAlloc (decA + BitVec.ofNat 64 (24 * (i + 1))) (pins.drop (i + 1)) (dec.pts.drop (i + 1)) =
          sortedSetPtListPinAt A.repAlloc decA pins dec.pts := by
        rw [← sortedSetPtPinAt_eq_slice A.repAlloc (pins[i]'hi_pins) (dec.pts[i]'hi_pts) (decA + BitVec.ofNat 64 (24 * i)),
          ← sortedSetPtListPinAt_focus A.repAlloc pins dec.pts i decA (by rw [hpins, hpts]) hi_pts]
      rw [sortedSetPtListPinAt_focus A.repAlloc pins dec.pts i decA (by rw [hpins, hpts]) hi_pts,
        sortedSetPtPinAt_eq_slice A.repAlloc (pins[i]'hi_pins) (dec.pts[i]'hi_pts) (decA + BitVec.ofNat 64 (24 * i)),
        memRegion_256_focus16 pv_ptr hpv_lt]
      wp_pull_exists
      by_cases hi16 : i + 1 = 16
      · have hmiss : anyMissing = true := by
          rcases hinv' with hmiss | ⟨k, hik, hk16, _⟩
          · exact hmiss
          · omega
        refine seq_vm_clean (mid := (blkPl_418).base + 288#64)
          (P_mid :=
            ((sp0 - 624#64) ↦₆₄ 16#64) ∗
              ((sp0 - 608#64) ↦₆₄ BitVec.ofNat 64 (pvLen + 1)) ∗
              sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
              memRegion pv_ptr 256 ∗ P)
          (Q := fun sf =>
            sf.sp = sp0 - 672#64 ∧
            traceVRegs sf = traceVRegs s ∧
            sf.readReg64 .x29 = s.readReg64 .x29 ∧
            sf.readReg64 .x30 = s.readReg64 .x30)
          ?_ ?_
        · by_vm_steps (
            wp_steps 19
            refine SepWP.weaken_pre
              (show _ ⊢
                (((sp0 - 624#64) ↦₆₄ 16#64) ∗
                  ((sp0 - 608#64) ↦₆₄ BitVec.ofNat 64 (pvLen + 1)) ∗
                  sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
                  (memRegion pv_ptr (16 * pvLen) ∗
                    (((pv_ptr + BitVec.ofNat 64 (16 * pvLen)) ↦₆₄ (pins[i]'hi_pins).ptr) ∗
                      ((pv_ptr + BitVec.ofNat 64 (16 * pvLen) + 8#64) ↦₆₄ BitVec.ofNat 64 (dec.necessaryPoints i))) ∗
                    memRegion (pv_ptr + BitVec.ofNat 64 (16 * (pvLen + 1))) (256 - 16 * (pvLen + 1))) ∗ P) by
                rw [← hreasm_pts]
                exact Entails.of_eq (by sep_ac_rfl)) ?_
            refine SepWP.weaken_pre
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (memRegion_256_unfocus16 pv_ptr hpv_lt _ _))))) ?_
            simp only [hi16, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, hmiss] at hx26 ⊢
            wp_steps 1
            exact SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, hstat])
              ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
               by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
               by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *]⟩)
        · rintro sf hpc_f hstat_f hvm_f ⟨hsp_f, htr_f, hx29_f, hx30_f⟩
          exact hcont sf (BitVec.ofNat 64 (pvLen + 1)) hpc_f hstat_f hsp_f htr_f hvm_f hx29_f hx30_f
      · refine seq_vm_clean (mid := (blkPl_418).base + 128#64)
          (P_mid :=
            ((sp0 - 624#64) ↦₆₄ 16#64) ∗
              ((sp0 - 608#64) ↦₆₄ BitVec.ofNat 64 (pvLen + 1)) ∗
              sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
              memRegion pv_ptr 256 ∗ P)
          (Q := fun s1 =>
            s1.sp = sp0 - 672#64 ∧
            traceVRegs s1 = traceVRegs s ∧
            s1.readReg64 .x0 = pv_ptr ∧
            s1.readReg64 .x20 = decA ∧
            s1.readReg64 .x21 = BitVec.ofNat 64 (pvLen + 1) ∧
            s1.readReg64 .x22 = BitVec.ofNat 64 (dec.ptsNeeded / 16) ∧
            s1.readReg64 .x23 = BitVec.ofNat 64 (dec.ptsNeeded % 16) ∧
            s1.readReg64 .x24 = decA + 40#64 ∧
            s1.readReg64 .x25 = 24#64 ∧
            s1.readReg64 .x26 = (if anyMissing then 1#64 else 0#64) ∧
            s1.readReg64 .x27 = BitVec.ofNat 64 (i + 1) ∧
            s1.readReg64 .x29 = s.readReg64 .x29 ∧
            s1.readReg64 .x30 = s.readReg64 .x30)
          ?_ ?_
        · by_vm_steps (
            wp_steps 19
            refine SepWP.weaken_pre
              (show _ ⊢
                (((sp0 - 624#64) ↦₆₄ 16#64) ∗
                  ((sp0 - 608#64) ↦₆₄ BitVec.ofNat 64 (pvLen + 1)) ∗
                  sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
                  (memRegion pv_ptr (16 * pvLen) ∗
                    (((pv_ptr + BitVec.ofNat 64 (16 * pvLen)) ↦₆₄ (pins[i]'hi_pins).ptr) ∗
                      ((pv_ptr + BitVec.ofNat 64 (16 * pvLen) + 8#64) ↦₆₄ BitVec.ofNat 64 (dec.necessaryPoints i))) ∗
                    memRegion (pv_ptr + BitVec.ofNat 64 (16 * (pvLen + 1))) (256 - 16 * (pvLen + 1))) ∗ P) by
                rw [← hreasm_pts]
                exact Entails.of_eq (by sep_ac_rfl)) ?_
            refine SepWP.weaken_pre
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (memRegion_256_unfocus16 pv_ptr hpv_lt _ _))))) ?_
            simp only [hi16, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
            exact SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, hstat])
              ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
               by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
               by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
               by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
               by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
               by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
               by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
               by simp [wp_norm, arm64_norm, *]⟩)
        · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, htr1, hx0_1, hx20_1, hx21_1, hx22_1, hx23_1,
            hx24_1, hx25_1, hx26_1, hx27_1, hx29_1, hx30_1⟩
          refine ih (rem - 1) (by omega) (i + 1) (pvLen + 1) anyMissing s1 (BitVec.ofNat 64 (pvLen + 1)) P post
            (by omega) (by omega) hinv'
            hpc1 hstat1 hsp1 hx0_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1
            (fun sf pvLenFinal hpc_f hstat_f hsp_f htr_f hvm_f hx29_f hx30_f => ?_)
          exact hcont sf pvLenFinal hpc_f hstat_f hsp_f (htr_f.trans htr1) (hvm1.trans hvm_f)
            (hx29_f.trans hx29_1) (hx30_f.trans hx30_1)
    · have hule_false :
          (BitVec.ofNat 64 (dec.necessaryPoints i)).ule
            (BitVec.ofNat 64 (dec.pts[i]'hi_pts).vec.length) = false := by
        rw [bv64_ule_ofNat hnec_lt (by omega), decide_eq_false_iff_not]; exact hge
      have hmadd_scan : decA + 40#64 + BitVec.ofNat 64 i * 24#64 =
          decA + BitVec.ofNat 64 (24 * (i + 1)) + 16#64 := by
        rw [bv64_madd24_ofNat (decA + 40#64) hi, BitVec.add_assoc,
          show (40#64 : BitVec 64) + BitVec.ofNat 64 (24 * i) =
            BitVec.ofNat 64 (24 * (i + 1)) + 16#64 by
            rw [show (40#64 : BitVec 64) = 16#64 + BitVec.ofNat 64 24 from rfl,
              BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_comm 16#64]
            congr 2
            omega, ← BitVec.add_assoc]
      rw [sortedSetPtListPinAt_focus A.repAlloc pins dec.pts i decA (by rw [hpins, hpts]) hi_pts,
        sortedSetPtPinAt_eq_slice A.repAlloc (pins[i]'hi_pins) (dec.pts[i]'hi_pts) (decA + BitVec.ofNat 64 (24 * i))]
      wp_steps 8
      have hreasm_pts :
          sortedSetPtListPinAt A.repAlloc decA (pins.take i) (dec.pts.take i) ∗
            (((decA + BitVec.ofNat 64 (24 * i)) ↦₆₄ (pins[i]'hi_pins).cap) ∗
              ((decA + BitVec.ofNat 64 (24 * i) + 8#64) ↦₆₄ (pins[i]'hi_pins).ptr) ∗
              ((decA + BitVec.ofNat 64 (24 * i) + 16#64) ↦₆₄ BitVec.ofNat 64 (dec.pts[i]'hi_pts).vec.length) ∗
              ptSliceAt (pins[i]'hi_pins).ptr (dec.pts[i]'hi_pts).vec ∗
              sortedSetPtPinRest A.repAlloc (pins[i]'hi_pins) (dec.pts[i]'hi_pts)) ∗
            sortedSetPtListPinAt A.repAlloc (decA + BitVec.ofNat 64 (24 * (i + 1))) (pins.drop (i + 1)) (dec.pts.drop (i + 1)) =
          sortedSetPtListPinAt A.repAlloc decA pins dec.pts := by
        rw [← sortedSetPtPinAt_eq_slice A.repAlloc (pins[i]'hi_pins) (dec.pts[i]'hi_pts) (decA + BitVec.ofNat 64 (24 * i)),
          ← sortedSetPtListPinAt_focus A.repAlloc pins dec.pts i decA (by rw [hpins, hpts]) hi_pts]
      refine SepWP.weaken_pre
        (show _ ⊢
          (sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
            (((sp0 - 624#64) ↦₆₄ 16#64) ∗ ((sp0 - 608#64) ↦₆₄ pvLenOld) ∗ memRegion pv_ptr 256 ∗ P)) by
          rw [← hreasm_pts]
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine hscan (15 - i) i _ (((sp0 - 624#64) ↦₆₄ 16#64) ∗ ((sp0 - 608#64) ↦₆₄ pvLenOld) ∗ memRegion pv_ptr 256 ∗ P) post
        (by omega)
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hstat])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hmadd_scan])
        (by simp [wp_norm, arm64_norm, hx22])
        (by simp [wp_norm, arm64_norm, hx23])
        (fun sf hpc_f hstat_f hsp_f htr_f hvm_f hx29_f hx30_f => ?_)
        (fun s1 idx' hidx_gt_i hidx_lt16 hpc1 hstat1 hsp1 htr1 hvm1 hx0_1 hx8_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 hx30_1 => ?_)
      · rw [show sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
              (((sp0 - 624#64) ↦₆₄ 16#64) ∗ ((sp0 - 608#64) ↦₆₄ pvLenOld) ∗ memRegion pv_ptr 256 ∗ P) =
            ((sp0 - 624#64) ↦₆₄ 16#64) ∗
              ((sp0 - 608#64) ↦₆₄ pvLenOld) ∗
              sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
              memRegion pv_ptr 256 ∗ P by sep_ac_rfl]
        apply hcont sf pvLenOld hpc_f hstat_f
        · simpa [wp_norm, arm64_norm, hsp] using hsp_f
        · simpa [wp_norm, arm64_norm] using htr_f
        · exact (by simp [wp_norm, arm64_norm] : VmPreserved s _).trans hvm_f
        · simpa [wp_norm, arm64_norm] using hx29_f
        · simpa [wp_norm, arm64_norm] using hx30_f
      · have hvm_s_s1 : VmPreserved s s1 :=
          (by simp [wp_norm, arm64_norm] : VmPreserved s _).trans hvm1
        have hidx_pts : idx' < dec.pts.length := by rw [hpts]; exact hidx_lt16
        have hidx_pins : idx' < pins.length := by omega
        have hmadd_idx := bv64_madd24_ofNat decA hidx_lt16
        have hadd1_idx : BitVec.ofNat 64 idx' + 1#64 = BitVec.ofNat 64 (idx' + 1) := by
          rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
        have hbne_pv16 : (BitVec.ofNat 64 pvLen != 16#64) = true := by
          rw [bv64_bne_16_ofNat (by omega), decide_eq_true_eq]; omega
        have hlsl4 : (BitVec.ofNat 64 pvLen) <<< 4 = BitVec.ofNat 64 (16 * pvLen) :=
          bv64_lsl4_ofNat (by omega)
        have hadd1_pv : BitVec.ofNat 64 pvLen + 1#64 = BitVec.ofNat 64 (pvLen + 1) := by
          rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
        have hbne_idx16 : (BitVec.ofNat 64 (idx' + 1) != 16#64) = decide (idx' + 1 ≠ 16) :=
          bv64_bne_16_ofNat (by omega)
        have hsp1' : s1.sp = sp0 - 672#64 := by simpa [wp_norm, arm64_norm, hsp] using hsp1
        have hsp1_align : s1.sp &&& 15#64 = 0#64 := by
          rw [hsp1']; exact sp672_aligned sp0 hsp0
        have hx0_1' : s1.readReg64 .x0 = pv_ptr := by simpa [wp_norm, arm64_norm, hx0] using hx0_1
        have hx20_1' : s1.readReg64 .x20 = decA := by simpa [wp_norm, arm64_norm, hx20] using hx20_1
        have hx21_1' : s1.readReg64 .x21 = BitVec.ofNat 64 pvLen := by simpa [wp_norm, arm64_norm, hx21] using hx21_1
        have hx22_1' : s1.readReg64 .x22 = BitVec.ofNat 64 (dec.ptsNeeded / 16) := by simpa [wp_norm, arm64_norm, hx22] using hx22_1
        have hx23_1' : s1.readReg64 .x23 = BitVec.ofNat 64 (dec.ptsNeeded % 16) := by simpa [wp_norm, arm64_norm, hx23] using hx23_1
        have hx24_1' : s1.readReg64 .x24 = decA + 40#64 := by simpa [wp_norm, arm64_norm, hx24] using hx24_1
        have hx25_1' : s1.readReg64 .x25 = 24#64 := by simpa [wp_norm, arm64_norm, hx25] using hx25_1
        have htr1' : traceVRegs s1 = traceVRegs s := by simpa [wp_norm, arm64_norm] using htr1
        have hx29_1' : s1.readReg64 .x29 = s.readReg64 .x29 := by simpa [wp_norm, arm64_norm] using hx29_1
        have hx30_1' : s1.readReg64 .x30 = s.readReg64 .x30 := by simpa [wp_norm, arm64_norm] using hx30_1
        have hreasm_pts2 :
            sortedSetPtListPinAt A.repAlloc decA (pins.take idx') (dec.pts.take idx') ∗
              (((decA + BitVec.ofNat 64 (24 * idx')) ↦₆₄ (pins[idx']'hidx_pins).cap) ∗
                ((decA + BitVec.ofNat 64 (24 * idx') + 8#64) ↦₆₄ (pins[idx']'hidx_pins).ptr) ∗
                ((decA + BitVec.ofNat 64 (24 * idx') + 16#64) ↦₆₄ BitVec.ofNat 64 (dec.pts[idx']'hidx_pts).vec.length) ∗
                ptSliceAt (pins[idx']'hidx_pins).ptr (dec.pts[idx']'hidx_pts).vec ∗
                sortedSetPtPinRest A.repAlloc (pins[idx']'hidx_pins) (dec.pts[idx']'hidx_pts)) ∗
              sortedSetPtListPinAt A.repAlloc (decA + BitVec.ofNat 64 (24 * (idx' + 1))) (pins.drop (idx' + 1)) (dec.pts.drop (idx' + 1)) =
            sortedSetPtListPinAt A.repAlloc decA pins dec.pts := by
          rw [← sortedSetPtPinAt_eq_slice A.repAlloc (pins[idx']'hidx_pins) (dec.pts[idx']'hidx_pts) (decA + BitVec.ofNat 64 (24 * idx')),
            ← sortedSetPtListPinAt_focus A.repAlloc pins dec.pts idx' decA (by rw [hpins, hpts]) hidx_pts]
        rw [sortedSetPtListPinAt_focus A.repAlloc pins dec.pts idx' decA (by rw [hpins, hpts]) hidx_pts,
          sortedSetPtPinAt_eq_slice A.repAlloc (pins[idx']'hidx_pins) (dec.pts[idx']'hidx_pts) (decA + BitVec.ofNat 64 (24 * idx')),
          memRegion_256_focus16 pv_ptr hpv_lt]
        wp_pull_exists
        by_cases hidx16 : idx' + 1 = 16
        · refine seq_vm_clean (mid := (blkPl_418).base + 288#64)
            (P_mid :=
              ((sp0 - 624#64) ↦₆₄ 16#64) ∗
                ((sp0 - 608#64) ↦₆₄ BitVec.ofNat 64 (pvLen + 1)) ∗
                sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
                memRegion pv_ptr 256 ∗ P)
            (Q := fun sf =>
              sf.sp = sp0 - 672#64 ∧
              traceVRegs sf = traceVRegs s1 ∧
              sf.readReg64 .x29 = s1.readReg64 .x29 ∧
              sf.readReg64 .x30 = s1.readReg64 .x30)
            ?_ ?_
          · by_vm_steps (
              wp_steps 13
              refine SepWP.weaken_pre
                (show _ ⊢
                  (((sp0 - 624#64) ↦₆₄ 16#64) ∗
                    ((sp0 - 608#64) ↦₆₄ BitVec.ofNat 64 (pvLen + 1)) ∗
                    sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
                    (memRegion pv_ptr (16 * pvLen) ∗
                      (((pv_ptr + BitVec.ofNat 64 (16 * pvLen)) ↦₆₄ (pins[idx']'hidx_pins).ptr) ∗
                        ((pv_ptr + BitVec.ofNat 64 (16 * pvLen) + 8#64) ↦₆₄ BitVec.ofNat 64 (dec.necessaryPoints idx'))) ∗
                      memRegion (pv_ptr + BitVec.ofNat 64 (16 * (pvLen + 1))) (256 - 16 * (pvLen + 1))) ∗ P) by
                  rw [← hreasm_pts2]
                  exact Entails.of_eq (by sep_ac_rfl)) ?_
              refine SepWP.weaken_pre
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                  (memRegion_256_unfocus16 pv_ptr hpv_lt _ _))))) ?_
              try simp only [hidx16, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
              wp_steps 1
              exact SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, hstat1])
                ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
                 by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
                 by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *]⟩)
          · rintro sf hpc_f hstat_f hvm2 ⟨hsp_f, htr_f, hx29_f, hx30_f⟩
            exact hcont sf (BitVec.ofNat 64 (pvLen + 1)) hpc_f hstat_f hsp_f
              (htr_f.trans htr1') (hvm_s_s1.trans hvm2) (hx29_f.trans hx29_1') (hx30_f.trans hx30_1')
        · refine seq_vm_clean (mid := (blkPl_418).base + 128#64)
            (P_mid :=
              ((sp0 - 624#64) ↦₆₄ 16#64) ∗
                ((sp0 - 608#64) ↦₆₄ BitVec.ofNat 64 (pvLen + 1)) ∗
                sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
                memRegion pv_ptr 256 ∗ P)
            (Q := fun s2 =>
              s2.sp = sp0 - 672#64 ∧
              traceVRegs s2 = traceVRegs s1 ∧
              s2.readReg64 .x0 = pv_ptr ∧
              s2.readReg64 .x20 = decA ∧
              s2.readReg64 .x21 = BitVec.ofNat 64 (pvLen + 1) ∧
              s2.readReg64 .x22 = BitVec.ofNat 64 (dec.ptsNeeded / 16) ∧
              s2.readReg64 .x23 = BitVec.ofNat 64 (dec.ptsNeeded % 16) ∧
              s2.readReg64 .x24 = decA + 40#64 ∧
              s2.readReg64 .x25 = 24#64 ∧
              s2.readReg64 .x26 = 1#64 ∧
              s2.readReg64 .x27 = BitVec.ofNat 64 (idx' + 1) ∧
              s2.readReg64 .x29 = s1.readReg64 .x29 ∧
              s2.readReg64 .x30 = s1.readReg64 .x30)
            ?_ ?_
          · by_vm_steps (
              wp_steps 13
              refine SepWP.weaken_pre
                (show _ ⊢
                  (((sp0 - 624#64) ↦₆₄ 16#64) ∗
                    ((sp0 - 608#64) ↦₆₄ BitVec.ofNat 64 (pvLen + 1)) ∗
                    sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
                    (memRegion pv_ptr (16 * pvLen) ∗
                      (((pv_ptr + BitVec.ofNat 64 (16 * pvLen)) ↦₆₄ (pins[idx']'hidx_pins).ptr) ∗
                        ((pv_ptr + BitVec.ofNat 64 (16 * pvLen) + 8#64) ↦₆₄ BitVec.ofNat 64 (dec.necessaryPoints idx'))) ∗
                      memRegion (pv_ptr + BitVec.ofNat 64 (16 * (pvLen + 1))) (256 - 16 * (pvLen + 1))) ∗ P) by
                  rw [← hreasm_pts2]
                  exact Entails.of_eq (by sep_ac_rfl)) ?_
              refine SepWP.weaken_pre
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                  (memRegion_256_unfocus16 pv_ptr hpv_lt _ _))))) ?_
              simp only [hidx16, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
              exact SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, hstat1])
                ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
                 by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
                 by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
                 by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
                 by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
                 by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
                 by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
                 by simp [wp_norm, arm64_norm, *]⟩)
          · rintro s2 hpc2 hstat2 hvm2 ⟨hsp2, htr2, hx0_2, hx20_2, hx21_2, hx22_2, hx23_2,
              hx24_2, hx25_2, hx26_2, hx27_2, hx29_2, hx30_2⟩
            refine ih (15 - (idx' + 1)) (by omega) (idx' + 1) (pvLen + 1) true s2
              (BitVec.ofNat 64 (pvLen + 1)) P post
              (by omega) (by omega) (Or.inl rfl)
              hpc2 hstat2 hsp2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2
              (fun sf pvLenFinal hpc_f hstat_f hsp_f htr_f hvm_f hx29_f hx30_f => ?_)
            exact hcont sf pvLenFinal hpc_f hstat_f hsp_f
              (htr_f.trans (htr2.trans htr1'))
              (hvm_s_s1.trans (hvm2.trans hvm_f))
              (hx29_f.trans (hx29_2.trans hx29_1'))
              (hx30_f.trans (hx30_2.trans hx30_1'))

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.LoopPlacedBudget
