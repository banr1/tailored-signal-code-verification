/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.LoopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoop
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Main Loop Sub-Steps for `<PolyDecoder as Decoder>::decoded_message`

Pure `DecodedMessageLoopEnv` decomposition lemmas and `VmPreserved` / `ComputeAtCallEnv` sub-step
proofs (`bsearchStep`, `computeAtStep`, `pushTwoBytes`) on Block `418`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement blkPC_418 blkPl_418 lsmpl)
open scoped CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly PolyDecoder SortedSetPt u16ToBeBytes)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (gf16SliceAt ptAt ptSliceAt sortedSetPtListPinAt)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (PolyDecoderStrictSorted SortedSetPtStrictSorted bsearchLoop bsearchLoop_bounds ptSliceAt_focus)
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.ComputeAt (ComputeAtArgs computeAtPure computeAtStack)
open CryptoVerification.SpqrV1.Poly.DecodedMessage
  (bsearchLoop_eq_binarySearch bv16_bne_zeroExtend32 bv16_lsr8_zeroExtend64_truncate8
   bv64_and15_ofNat bv64_beq_ofNat
   bv64_bne_ofNat bv64_lsr4_truncate16_ofNat bv64_ofNat_mul2_comm bv64_ofNat_one_add_mul2
   bv64_orr_w0_truncate8 bv64_ubfx_8_8_truncate8 bv64_umaddl24_mod16 collectedSlices
   collectedSlices_getD_eq_take lagrangeInterpolateTotal memRegion_out_split2 optPolyCacheSlotAt
   pointsToBytes_append_u16ToBeBytes sortedSetPtListPinAt_focus sortedSetPtPinAt_eq_slice
   sortedSetPtPinRest sp672_aligned sp96_sub104 sp96_sub112 sp96_sub120 traceVRegs)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget SeqEnv VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget
  (computeAtEvents computeAtPlacedSpec computeAtScratchCap)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (ComputeAtCallEnv DecodedMessageLoopEnv LagrangeInterpolateInlinedEnv
   LagrangeInterpolateMissEnv computeAtCallEnv_of_dealloc)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.LoopPlacedBudget
  (bsearch_to_624_placed_sepWP)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  sp96_sub120 sp96_sub112 sp96_sub104
  bv64_and15_ofNat bv64_umaddl24_mod16
  bv64_ofNat_mul2_comm bv64_ofNat_one_add_mul2

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

/-! ## Pure Envelope Lemmas for `DecodedMessageLoopEnv` -/

theorem computeAtAllocEvents_eq_defsBudget (len : Nat) :
    LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget.computeAtAllocEvents len =
      LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget.computeAtAllocEvents len :=
  rfl

theorem computeAtEvents_mem_callEnv (len : Nat) :
    ComputeAtCallEnv len (computeAtEvents len) := by
  dsimp only [computeAtEvents]
  rw [computeAtAllocEvents_eq_defsBudget]
  exact computeAtCallEnv_of_dealloc len (computeAtScratchCap len)

theorem fitsEvents_of_fitsEnv_computeAtCall {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {len : Nat} (h : FitsEnv M lim st (ComputeAtCallEnv len)) :
    FitsEvents M lim st
      (LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget.computeAtAllocEvents len) := by
  rw [computeAtAllocEvents_eq_defsBudget]
  exact h _ (Or.inl rfl)

theorem decodedMessageLoopEnv_step_found (self : PolyDecoder) (hpts : self.pts.length = 16)
    (hsort : PolyDecoderStrictSorted self)
    {i rem : Nat} {polys : List (Option Poly)}
    {bIdx : Nat}
    (hb_eq : bIdx = bsearchLoop
      (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec
      (BitVec.ofNat 16 (i / 16)) 0
      (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hb_lt : bIdx < (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hfound : (((self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec[bIdx]'hb_lt).x.value ==
      BitVec.ofNat 16 (i / 16)) = true) :
    DecodedMessageLoopEnv self (collectedSlices self 0 16) i (rem + 1) polys =
      DecodedMessageLoopEnv self (collectedSlices self 0 16) (i + 1) rem polys := by
  ext evs
  have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
  have hpoly_pts : i % 16 < self.pts.length := by omega
  have hget_pts : self.pts[i % 16]?.getD SortedSetPt.new = self.pts[i % 16]'hpoly_pts := by
    rw [List.getElem?_eq_getElem hpoly_pts, Option.getD_some]
  have hs_sort : SortedSetPtStrictSorted (self.pts[i % 16]'hpoly_pts) :=
    hsort (self.pts[i % 16]'hpoly_pts) (List.getElem_mem hpoly_pts)
  have hs_ne : (self.pts[i % 16]'hpoly_pts).vec ≠ [] :=
    List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hb_lt)
  have hbs := bsearchLoop_eq_binarySearch (self.pts[i % 16]'hpoly_pts)
    { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO } hs_sort hs_ne hb_eq hb_lt
  change (if ((self.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt).x.value == BitVec.ofNat 16 (i / 16)
    then _ else _) at hbs
  simp only [hfound, ite_true] at hbs
  conv_lhs => rw [DecodedMessageLoopEnv]
  simp only [hget_pts, hbs]

theorem decodedMessageLoopEnv_not_found_split {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (self : PolyDecoder) (hpts : self.pts.length = 16)
    (hsort : PolyDecoderStrictSorted self)
    {i rem : Nat} {polys : List (Option Poly)} (hpolys : polys.length = 16)
    {bIdx : Nat}
    (hb_eq : bIdx = bsearchLoop
      (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec
      (BitVec.ofNat 16 (i / 16)) 0
      (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hb_lt : bIdx < (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hnot_found : (((self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec[bIdx]'hb_lt).x.value ==
      BitVec.ofNat 16 (i / 16)) = false)
    (hfit : FitsEnv M lim st
      (DecodedMessageLoopEnv self (collectedSlices self 0 16) i (rem + 1) polys)) :
    let poly := i % 16
    let hpoly_pts : poly < self.pts.length := by have := Nat.mod_lt i (by decide : 0 < 16); omega
    let hpoly_p : poly < polys.length := by have := Nat.mod_lt i (by decide : 0 < 16); omega
    let ptsSlice := (self.pts[poly]'hpoly_pts).vec.take (self.necessaryPoints poly)
    let optPoly := polys[poly]'hpoly_p
    let pInterp := optPoly.getD (lagrangeInterpolateTotal ptsSlice)
    FitsEnv M lim st (LagrangeInterpolateInlinedEnv optPoly ptsSlice.length) ∧
      ∀ evs1, LagrangeInterpolateInlinedEnv optPoly ptsSlice.length evs1 →
        FitsEnv M lim (M.stepEvents evs1 st) (ComputeAtCallEnv pInterp.coefficients.length) ∧
        ∀ evs2, ComputeAtCallEnv pInterp.coefficients.length evs2 →
          FitsEnv M lim (M.stepEvents evs2 (M.stepEvents evs1 st))
            (DecodedMessageLoopEnv self (collectedSlices self 0 16) (i + 1) rem
              (polys.set poly (some pInterp))) ∧
          ∀ evs3,
            DecodedMessageLoopEnv self (collectedSlices self 0 16) (i + 1) rem
              (polys.set poly (some pInterp)) evs3 →
            DecodedMessageLoopEnv self (collectedSlices self 0 16) i (rem + 1) polys
              (evs1 ++ evs2 ++ evs3) := by
  have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
  have hpoly_pts : i % 16 < self.pts.length := by omega
  have hpoly_p : i % 16 < polys.length := by omega
  have hget_pts : self.pts[i % 16]?.getD SortedSetPt.new = self.pts[i % 16]'hpoly_pts := by
    rw [List.getElem?_eq_getElem hpoly_pts, Option.getD_some]
  have hs_sort : SortedSetPtStrictSorted (self.pts[i % 16]'hpoly_pts) :=
    hsort (self.pts[i % 16]'hpoly_pts) (List.getElem_mem hpoly_pts)
  have hs_ne : (self.pts[i % 16]'hpoly_pts).vec ≠ [] :=
    List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hb_lt)
  have hbs := bsearchLoop_eq_binarySearch (self.pts[i % 16]'hpoly_pts)
    { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO } hs_sort hs_ne hb_eq hb_lt
  change (if ((self.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt).x.value == BitVec.ofNat 16 (i / 16)
    then _ else _) at hbs
  simp only [hnot_found, Bool.false_eq_true, ite_false] at hbs
  have hget_p : polys[i % 16]?.getD none = polys[i % 16]'hpoly_p := by
    rw [List.getElem?_eq_getElem hpoly_p, Option.getD_some]
  have hget_slice := collectedSlices_getD_eq_take self hpts hpoly_lt
  have henv_eq :
      DecodedMessageLoopEnv self (collectedSlices self 0 16) i (rem + 1) polys =
        match polys[i % 16]'hpoly_p with
        | some p =>
          SeqEnv (ComputeAtCallEnv p.coefficients.length)
            (DecodedMessageLoopEnv self (collectedSlices self 0 16) (i + 1) rem polys)
        | none =>
          let ptsSlice := (self.pts[i % 16]'hpoly_pts).vec.take (self.necessaryPoints (i % 16))
          let interp := lagrangeInterpolateTotal ptsSlice
          SeqEnv (LagrangeInterpolateMissEnv ptsSlice.length)
            (SeqEnv (ComputeAtCallEnv interp.coefficients.length)
              (DecodedMessageLoopEnv self (collectedSlices self 0 16) (i + 1) rem
                (polys.set (i % 16) (some interp)))) := by
    ext evs
    conv_lhs => rw [DecodedMessageLoopEnv]
    simp only [hget_pts, hbs, hget_p, hget_slice]
    cases polys[i % 16]'hpoly_p <;> rfl
  dsimp only
  cases hopt : polys[i % 16]'hpoly_p with
  | some p0 =>
    have hset_self : polys.set (i % 16) (some p0) = polys := by
      rw [← hopt, List.set_getElem_self]
    rw [henv_eq, hopt] at hfit
    refine ⟨?_, ?_⟩
    · rintro _ rfl; trivial
    · rintro evs1 rfl
      simp only [Option.getD_some, AllocCostModel.stepEvents_nil, List.nil_append, hset_self]
      refine ⟨hfit.seq_left, fun evs2 he2 => ⟨hfit.seq_right he2, fun evs3 he3 => ?_⟩⟩
      rw [henv_eq, hopt]
      exact SeqEnv.append he2 he3
  | none =>
    rw [henv_eq, hopt] at hfit
    simp only [Option.getD_none, LagrangeInterpolateInlinedEnv]
    refine ⟨hfit.seq_left, fun evs1 he1 => ?_⟩
    have hfit1 := hfit.seq_right he1
    refine ⟨hfit1.seq_left, fun evs2 he2 => ⟨hfit1.seq_right he2, fun evs3 he3 => ?_⟩⟩
    rw [henv_eq, hopt, List.append_assoc]
    exact SeqEnv.append he1 (SeqEnv.append he2 he3)

/-! ## Budget-Threaded Sub-Steps of One Iteration of `decodedMessageLoop` -/

/-- Step 1 of the main loop (`[LibsignalPlacement]`):
    Looks up `xVal = BitVec.ofNat 16 (i / 16)` in `dec.pts[i % 16]` via binary search,
    preserving `VmPreserved s sf`. -/
theorem decodedMessage_bsearchStep_placed_sepWP [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (dec : PolyDecoder) (sp0 pts_base : BitVec 64) (pins : List VecPin) (i : Nat)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hi_lt : i < dec.ptsNeeded) (hneed_le : dec.ptsNeeded ≤ 16 * 65536)
    (hge_len : 1 ≤ (dec.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hle_len : (dec.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length ≤ 65536)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 548#64)
    (hstat : s.status = .Running)
    (hx20 : s.readReg64 .x20 = pts_base)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (2 * i))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = sp0 - 600#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont_found :
      let poly := i % 16
      let hpoly_pts : poly < dec.pts.length := by have := Nat.mod_lt i (by decide : 0 < 16); omega
      let sPt := dec.pts[poly]'hpoly_pts
      let xVal := BitVec.ofNat 16 (i / 16)
      let bIdx := bsearchLoop sPt.vec xVal 0 sPt.vec.length
      ∀ (hb_lt : bIdx < sPt.vec.length),
        ((sPt.vec[bIdx]'hb_lt).x.value == xVal) = true →
        ∀ (sf : State),
          sf.pc = (blkPl_418).base + 1328#64 →
          sf.status = .Running →
          sf.sp = s.sp →
          traceVRegs sf = traceVRegs s →
          VmPreserved s sf →
          BitVec.truncate 8 (sf.readReg64 .x19) =
            BitVec.truncate 8 ((sPt.vec[bIdx]'hb_lt).y.value >>> 8) →
          BitVec.truncate 8 (sf.readReg64 .x21) =
            BitVec.truncate 8 (sPt.vec[bIdx]'hb_lt).y.value →
          sf.readReg64 .x20 = pts_base →
          sf.readReg64 .x22 = BitVec.ofNat 64 i →
          sf.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
          sf.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded →
          sf.readReg64 .x25 = 24#64 →
          sf.readReg64 .x26 = sp0 - 600#64 →
          sf.readReg64 .x29 = sp0 - 96#64 →
          SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
            (sortedSetPtListPinAt A pts_base pins dec.pts ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P)
            post)
    (hcont_miss :
      let poly := i % 16
      let hpoly_pts : poly < dec.pts.length := by have := Nat.mod_lt i (by decide : 0 < 16); omega
      let sPt := dec.pts[poly]'hpoly_pts
      let xVal := BitVec.ofNat 16 (i / 16)
      let bIdx := bsearchLoop sPt.vec xVal 0 sPt.vec.length
      ∀ (hb_lt : bIdx < sPt.vec.length),
        ((sPt.vec[bIdx]'hb_lt).x.value == xVal) = false →
        ∀ (sf : State),
          sf.pc = (blkPl_418).base + 660#64 →
          sf.status = .Running →
          sf.sp = s.sp →
          traceVRegs sf = traceVRegs s →
          VmPreserved s sf →
          sf.readReg64 .x0 = BitVec.ofNat 64 poly →
          sf.readReg64 .x20 = pts_base →
          sf.readReg64 .x22 = BitVec.ofNat 64 i →
          sf.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded →
          sf.readReg64 .x25 = 24#64 →
          sf.readReg64 .x26 = sp0 - 600#64 →
          sf.readReg64 .x29 = sp0 - 96#64 →
          SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
            (sortedSetPtListPinAt A pts_base pins dec.pts ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P)
            post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (sortedSetPtListPinAt A pts_base pins dec.pts ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P)
      post := by
  have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
  have hpoly_pts : i % 16 < dec.pts.length := by omega
  have hpoly_pins : i % 16 < pins.length := by omega
  have hbsearch := @bsearch_to_624_placed_sepWP lsmpl ext ret_pc (pins[i % 16]'hpoly_pins).ptr
    (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) hge_len hle_len
  try dsimp only [BitVec.ofNat_eq_ofNat] at hbsearch hpc hcont_found hcont_miss ⊢
  have hlen_ne0 : (BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length == 0#64) = false := by
    rw [bv64_beq_ofNat (by omega) (by decide), decide_eq_false_iff_not]; omega
  rw [sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
    sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
      (pts_base + BitVec.ofNat 64 (24 * (i % 16)))]
  wp_steps 6
  refine SepWP.weaken_pre
    (show _ ⊢
      ptSliceAt (pins[i % 16]'hpoly_pins).ptr (dec.pts[i % 16]'hpoly_pts).vec ∗
        (sortedSetPtListPinAt A pts_base (pins.take (i % 16)) (dec.pts.take (i % 16)) ∗
          ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
          ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄ (pins[i % 16]'hpoly_pins).ptr) ∗
          ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄
            BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
          sortedSetPtPinRest A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts) ∗
          sortedSetPtListPinAt A (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1)))
            (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P) by
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine hbsearch _ _ post
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hstat])
    (by simp [wp_norm, arm64_norm])
    (by
      simp only [wp_norm, arm64_norm]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.zeroExtend, BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
        BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega)
    (by simp [wp_norm, arm64_norm])
    (fun s1 hpc1 hstat1 hsp1 htr1 hvm1 hx0_1 hx8_1 hx9_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1
      hx26_1 hx29_1 _ => ?_)
  have hvm_s1 : VmPreserved s s1 :=
    (by simp [wp_norm, arm64_norm] : VmPreserved s _).trans hvm1
  have ⟨_, hb_lt0⟩ := bsearchLoop_bounds (dec.pts[i % 16]'hpoly_pts).vec
    (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length hge_len (by omega)
  have hb_lt : bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0
      (dec.pts[i % 16]'hpoly_pts).vec.length < (dec.pts[i % 16]'hpoly_pts).vec.length := by
    omega
  have hx0_1' : s1.readReg64 .x0 = BitVec.ofNat 64 (i % 16) := by
    simpa [wp_norm, arm64_norm, hx22] using hx0_1
  have hx9_32 : s1.readReg32 .x9 = BitVec.zeroExtend 32 (BitVec.ofNat 16 (i / 16)) := by
    rw [State.readReg32, hx9_1]
    bv_bits
  have hx20_1' : s1.readReg64 .x20 = pts_base := by simpa [wp_norm, arm64_norm, hx20] using hx20_1
  have hx22_1' : s1.readReg64 .x22 = BitVec.ofNat 64 i := by
    simpa [wp_norm, arm64_norm, hx22] using hx22_1
  have hx23_1' : s1.readReg64 .x23 = BitVec.ofNat 64 (2 * i) := by
    simpa [wp_norm, arm64_norm, hx23] using hx23_1
  have hx24_1' : s1.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded := by
    simpa [wp_norm, arm64_norm, hx24] using hx24_1
  have hx25_1' : s1.readReg64 .x25 = 24#64 := by simpa [wp_norm, arm64_norm, hx25] using hx25_1
  have hx26_1' : s1.readReg64 .x26 = sp0 - 600#64 := by
    simpa [wp_norm, arm64_norm, hx26] using hx26_1
  have hx29_1' : s1.readReg64 .x29 = sp0 - 96#64 := by
    simpa [wp_norm, arm64_norm, hx29] using hx29_1
  let bIdx := bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0
    (dec.pts[i % 16]'hpoly_pts).vec.length
  rw [ptSliceAt_focus (dec.pts[i % 16]'hpoly_pts).vec bIdx (pins[i % 16]'hpoly_pins).ptr hb_lt]
  unfold ptAt
  wp_steps 3
  rw [bv16_bne_zeroExtend32 ((dec.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt).x.value
    (BitVec.ofNat 16 (i / 16))]
  cases hbeq : ((dec.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt).x.value == BitVec.ofNat 16 (i / 16)
  · simp only [Bool.not_false, ↓reduceIte]
    refine SepWP.weaken_pre
      (show _ ⊢
        (sortedSetPtListPinAt A pts_base pins dec.pts ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P) by
        rw [sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
          sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
            (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
          ptSliceAt_focus (dec.pts[i % 16]'hpoly_pts).vec bIdx (pins[i % 16]'hpoly_pins).ptr hb_lt]
        unfold ptAt
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    apply hcont_miss hb_lt hbeq
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hstat1]
    · simpa [wp_norm, arm64_norm] using hsp1
    · simpa [wp_norm, arm64_norm] using htr1
    · exact hvm_s1.trans (by simp [wp_norm, arm64_norm])
    · simp [wp_norm, arm64_norm, hx0_1']
    · simp [wp_norm, arm64_norm, hx20_1']
    · simp [wp_norm, arm64_norm, hx22_1']
    · simp [wp_norm, arm64_norm, hx24_1']
    · simp [wp_norm, arm64_norm, hx25_1']
    · simp [wp_norm, arm64_norm, hx26_1']
    · simp [wp_norm, arm64_norm, hx29_1']
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have h2i_ne : (BitVec.ofNat 64 (2 * i) == BitVec.ofNat 64 (2 * dec.ptsNeeded)) = false := by
      rw [bv64_beq_ofNat (by omega) (by omega), decide_eq_false_iff_not]; omega
    wp_steps 6
    refine SepWP.weaken_pre
      (show _ ⊢
        (sortedSetPtListPinAt A pts_base pins dec.pts ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P) by
        rw [sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
          sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
            (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
          ptSliceAt_focus (dec.pts[i % 16]'hpoly_pts).vec bIdx (pins[i % 16]'hpoly_pins).ptr hb_lt]
        unfold ptAt
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    apply hcont_found hb_lt hbeq
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hstat1]
    · simpa [wp_norm, arm64_norm] using hsp1
    · simpa [wp_norm, arm64_norm] using htr1
    · exact hvm_s1.trans (by simp [wp_norm, arm64_norm])
    · simp [wp_norm, arm64_norm, bv16_lsr8_zeroExtend64_truncate8]; rfl
    · simp [wp_norm, arm64_norm]; rfl
    · simp [wp_norm, arm64_norm, hx20_1']
    · simp [wp_norm, arm64_norm, hx22_1']
    · simp [wp_norm, arm64_norm, hx23_1']
    · simp [wp_norm, arm64_norm, hx24_1']
    · simp [wp_norm, arm64_norm, hx25_1']
    · simp [wp_norm, arm64_norm, hx26_1']
    · simp [wp_norm, arm64_norm, hx29_1']

/-- Step 2b of the main loop (`[LibsignalPlacement]`, `SepWP`):
    Loads `(ptr_p, len_p)` from `slot`, evaluates `computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))`
    via `computeAtPlacedSpec M A lim`, and prepares `w19`/`w21`/`x23` at `entry + 1328#64`. -/
theorem decodedMessage_computeAtStep_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (computeAtPlacedSpec M A lim))
    (sp0 slot : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (i ptsNeeded : Nat) (p : Poly)
    (hi_lt : i < ptsNeeded) (hneed_le : ptsNeeded ≤ 16 * 65536)
    (st : M.σ) (hfit : FitsEnv M lim st (ComputeAtCallEnv p.coefficients.length))
    (s0 s : State) (F : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 1284#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (htr : traceVRegs s = traceVRegs s0)
    (hx19 : s.readReg64 .x19 = slot)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      ComputeAtCallEnv p.coefficients.length evs →
      sf.pc = (blkPl_418).base + 1328#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 →
      BitVec.truncate 8 (sf.readReg64 .x19) =
        BitVec.truncate 8 ((computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value >>> 8) →
      BitVec.truncate 8 (sf.readReg64 .x21) =
        BitVec.truncate 8 (computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = BitVec.ofNat 64 i →
      sf.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (optPolyCacheSlotAt A.repAlloc slot (some p) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (optPolyCacheSlotAt A.repAlloc slot (some p) ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
        stackAt (sp0 - 672#64) computeAtStack ∗ F)
      post := by
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
  have hslot16 : slot + 8#64 + 8#64 = slot + 16#64 := by bv_omega
  have h2i_ne : (BitVec.ofNat 64 (2 * i) != BitVec.ofNat 64 (2 * ptsNeeded)) = true := by
    rw [bv64_bne_ofNat (by omega) (by omega), decide_eq_true_eq]; omega
  have hfits_ev := fitsEvents_of_fitsEnv_computeAtCall hfit
  unfold optPolyCacheSlotAt
  rw [sepExists_sepConj_left]; apply SepWP.exists_elim; intro ptr_p
  rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hp_ge1, hp_le, hptr_p_ne⟩
  wp_steps 3
  refine SepWP.transport_budgetPool ?_ (hnext := ?_)
  · simp [wp_norm, arm64_norm]
  let a : ComputeAtArgs := {
    p_coeffs := ptr_p
    poly := p
    x := GF16.new (BitVec.ofNat 16 (i / 16))
  }
  refine SepWP.call_subroutine_frame (x := (a, st)) (ret_pc := (blkPl_418).base + 1296#64)
    (F := (slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      ((slot + 8#64) ↦₆₄ ptr_p) ∗
      ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      A.live ptr_p (2 * p.coefficients.length) 2 ∗
      ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
      ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗ F)
    hcomp_at
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hstat])
    (by
      unfold State.spAligned
      simp only [wp_norm, arm64_norm, hsp, sp672_aligned sp0 hsp0])
    (by simp [wp_norm, arm64_norm])
    (fun R' hm => ?_)
    (fun R' sf _ hm => ?_)
    (fun R' code sf _ hex => ?_)
    (fun sf_c hpc_c hrun_c hsp_c hcs_c => ?_)
  · have hx2_trunc :
        BitVec.truncate 16 ((BitVec.ofNat 64 i) >>> 4) =
          (GF16.new (BitVec.ofNat 16 (i / 16))).value :=
      bv64_lsr4_truncate16_ofNat (by omega)
    dsimp only [computeAtPlacedSpec, a]
    simp only [wp_norm, arm64_norm, hsp, sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx2_trunc, by omega, hfits_ev⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · dsimp only [computeAtPlacedSpec] at hm
    exact not_satisfies_false_sepConj hm
  · dsimp only [computeAtPlacedSpec, Spec.onExit] at hex
    exact not_satisfies_false_sepConj hex
  · conv => arg 4; dsimp only [computeAtPlacedSpec, a]; simp only [wp_norm, arm64_norm, htr_tr, hsp]
    rcases hcs_c with ⟨_, hx20_c, _, hx22_c, _, hx24_c, hx25_c, hx26_c, _, _, hx29_c, hvregs_c⟩
    apply SepWP.pure_elim; rintro ⟨htr_c, hx0_c⟩
    have hsp_c' : sf_c.sp = sp0 - 672#64 := by simpa [wp_norm, arm64_norm, hsp] using hsp_c
    have hx20_c' : sf_c.readReg64 .x20 = s.readReg64 .x20 := by
      simpa [wp_norm, arm64_norm] using hx20_c
    have hx22_c' : sf_c.readReg64 .x22 = BitVec.ofNat 64 i := by
      simpa [wp_norm, arm64_norm, hx22] using hx22_c
    have hx24_c' : sf_c.readReg64 .x24 = s.readReg64 .x24 := by
      simpa [wp_norm, arm64_norm] using hx24_c
    have hx25_c' : sf_c.readReg64 .x25 = s.readReg64 .x25 := by
      simpa [wp_norm, arm64_norm] using hx25_c
    have hx26_c' : sf_c.readReg64 .x26 = s.readReg64 .x26 := by
      simpa [wp_norm, arm64_norm] using hx26_c
    have hx29_c' : sf_c.readReg64 .x29 = sp0 - 96#64 := by
      simpa [wp_norm, arm64_norm, hx29] using hx29_c
    wp_steps 6
    refine SepWP.transport_budgetPool ?_ (hnext := ?_)
    · simp [wp_norm, arm64_norm]
    refine SepWP.weaken_pre ?_
      (hnext _ (computeAtEvents p.coefficients.length) (computeAtEvents_mem_callEnv _)
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun_c])
        (by simp [wp_norm, arm64_norm, hsp_c'])
        (by simp [traceVRegs, wp_norm, arm64_norm, htr_c, hvregs_c, htr_vr])
        (by simp only [wp_norm, arm64_norm]; exact bv64_ubfx_8_8_truncate8 hx0_c)
        (by simp only [wp_norm, arm64_norm]; exact bv64_orr_w0_truncate8 hx0_c)
        (by simp [wp_norm, arm64_norm, hx20_c'])
        (by simp [wp_norm, arm64_norm, hx22_c'])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx24_c'])
        (by simp [wp_norm, arm64_norm, hx25_c'])
        (by simp [wp_norm, arm64_norm, hx26_c'])
        (by simp [wp_norm, arm64_norm, hx29_c']))
    dsimp only [optPolyCacheSlotAt, RustCliAllocBudget.repAlloc_live]
    refine Entails.trans ?_
      (sepConj_mono_left
        (Entails.sepExists_right ptr_p
          (Entails.pure_right ⟨hp_ge1, hp_le, hptr_p_ne⟩ (Entails.of_eq rfl))))
    exact Entails.of_eq (by sep_ac_rfl)

theorem decodedMessage_computeAtStep_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (computeAtPlacedSpec M A lim))
    (sp0 slot : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (i ptsNeeded : Nat) (p : Poly)
    (hi_lt : i < ptsNeeded) (hneed_le : ptsNeeded ≤ 16 * 65536)
    (st : M.σ) (hfit : FitsEnv M lim st (ComputeAtCallEnv p.coefficients.length))
    (s0 s : State) (F : SepProp)
    (Q Qp : State → SepProp → Prop) (oom : State → SepProp := fun _ => ⌜False⌝)
    (hpc : s.pc = (blkPl_418).base + 1284#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (htr : traceVRegs s = traceVRegs s0)
    (hx19 : s.readReg64 .x19 = slot)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      ComputeAtCallEnv p.coefficients.length evs →
      sf.pc = (blkPl_418).base + 1328#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 →
      BitVec.truncate 8 (sf.readReg64 .x19) =
        BitVec.truncate 8 ((computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value >>> 8) →
      BitVec.truncate 8 (sf.readReg64 .x21) =
        BitVec.truncate 8 (computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = BitVec.ofNat 64 i →
      sf.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (optPolyCacheSlotAt A.repAlloc slot (some p) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (optPolyCacheSlotAt A.repAlloc slot (some p) ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
        stackAt (sp0 - 672#64) computeAtStack ∗ F)
      Q Qp oom := by
  apply SepWPp.of_sepWP (mid := (blkPl_418).base + 1328#64)
  refine SepWP.mono (oom := fun _ => ⌜False⌝) ?_ (fun _ _ _ _ hp => hp)
  refine decodedMessage_computeAtStep_placed_sepWP hcomp_at sp0 slot hsp0 i ptsNeeded p
    hi_lt hneed_le st hfit s0 s F _ hpc hstat hsp htr hx19 hx22 hx29 ?_
  intro sf evs hevs hpc_f hrun_f hsp_f htr_f hx19_f hx21_f hx20_f hx22_f hx23_f hx24_f hx25_f
    hx26_f hx29_f
  exact SepWP.done hpc_f hrun_f
    (hnext sf evs hevs hpc_f hrun_f hsp_f htr_f hx19_f hx21_f hx20_f hx22_f hx23_f hx24_f hx25_f
      hx26_f hx29_f)

/-- Step 3 of the main loop (`[LibsignalPlacement]`):
    Appends `u16ToBeBytes yVal` to `out` at `out_ptr + 2 * i`, increments `i` and `2 * i`,
    and establishes `VmPreserved s sf`. -/
theorem decodedMessage_pushTwoBytes_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (sp0 out_ptr old_len_slot : BitVec 64) (i ptsNeeded : Nat)
    (out : List (BitVec 8)) (yVal : BitVec 16)
    (hi_lt : i < ptsNeeded) (hneed_le : ptsNeeded ≤ 16 * 65536)
    (hout_len : out.length = 2 * i)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 1328#64)
    (hstat : s.status = .Running)
    (hx19 : BitVec.truncate 8 (s.readReg64 .x19) = BitVec.truncate 8 (yVal >>> 8))
    (hx21 : BitVec.truncate 8 (s.readReg64 .x21) = BitVec.truncate 8 yVal)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (2 * i))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (if i + 1 = ptsNeeded then
        (blkPl_418).base + 1404#64
      else
        (blkPl_418).base + 548#64) →
      sf.status = .Running →
      sf.sp = s.sp →
      traceVRegs sf = traceVRegs s →
      VmPreserved s sf →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x23 = BitVec.ofNat 64 (2 * (i + 1)) →
      sf.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
          ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
          (out_ptr ↦ₛ (out ++ u16ToBeBytes yVal)) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (2 * (ptsNeeded - (i + 1))) ∗ P)
        post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
        ((sp0 - 200#64) ↦₆₄ old_len_slot) ∗
        (out_ptr ↦ₛ out) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (ptsNeeded - i)) ∗ P)
      post := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  have h2i_add1 : BitVec.ofNat 64 (2 * i) + 1#64 = BitVec.ofNat 64 (2 * i + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have h2i1_ne : (BitVec.ofNat 64 (2 * i + 1) != BitVec.ofNat 64 (2 * ptsNeeded)) = true := by
    rw [bv64_bne_ofNat (by omega) (by omega), decide_eq_true_eq]; omega
  have hi_add1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have h2i2 : 2 * i + 2 = 2 * (i + 1) := by omega
  have h2i_add2 : BitVec.ofNat 64 (2 * i) + 2#64 = BitVec.ofNat 64 (2 * (i + 1)) := by
    rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, h2i2]
  have hi1_eq : (BitVec.ofNat 64 (i + 1) == BitVec.ofNat 64 ptsNeeded) = decide (i + 1 = ptsNeeded) :=
    bv64_beq_ofNat (by omega) (by omega)
  refine seq_vm_clean
    (mid := if i + 1 = ptsNeeded then (blkPl_418).base + 1404#64 else (blkPl_418).base + 548#64)
    (P_mid := ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
      ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
      ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
      (out_ptr ↦ₛ (out ++ u16ToBeBytes yVal)) ∗
      memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (2 * (ptsNeeded - (i + 1))) ∗ P)
    (Q := fun sf =>
      sf.sp = s.sp ∧
      traceVRegs sf = traceVRegs s ∧
      sf.readReg64 .x20 = s.readReg64 .x20 ∧
      sf.readReg64 .x22 = BitVec.ofNat 64 (i + 1) ∧
      sf.readReg64 .x23 = BitVec.ofNat 64 (2 * (i + 1)) ∧
      sf.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded ∧
      sf.readReg64 .x25 = s.readReg64 .x25 ∧
      sf.readReg64 .x26 = s.readReg64 .x26 ∧
      sf.readReg64 .x29 = sp0 - 96#64) ?_ ?_
  · by_vm_steps (
      rw [memRegion_out_split2 out_ptr hi_lt (by omega)]
      wp_pull_exists
      wp_steps 14
      refine SepWP.done
        (by by_cases heq : i + 1 = ptsNeeded <;> simp [wp_norm, arm64_norm, heq])
        (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm],
         by
           rw [← pointsToBytes_append_u16ToBeBytes out_ptr out yVal, hout_len]
           exact Entails.of_eq (by sep_ac_rfl),
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm, hx24],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm, hx29]⟩)
  · rintro sf hpc_f hrun_f hvm_f
      ⟨hsp_f, htr_f, hx20_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx29_f⟩
    exact hcont sf hpc_f hrun_f hsp_f htr_f hvm_f hx20_f hx22_f hx23_f hx24_f hx25_f hx26_f hx29_f

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlacedBudgetAux
