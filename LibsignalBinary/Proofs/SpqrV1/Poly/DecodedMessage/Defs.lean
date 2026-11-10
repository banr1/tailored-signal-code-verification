/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Defs
public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: Definitions and Specifications

Total pure characterizations (`collectPointsVecsTotal`, `lagrangeInterpolateTotal`,
`decodedMessageTotal`), `Option<Poly>` cache layout (`optPolyCacheSlotAt`), and separation-logic
contracts (`decodedMessageSpec`, `decodedMessagePlacedSpec`) for `decoded_message` (`0x6bb80`,
Block `418`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L31
open Lean Meta Elab Command Arm64 CryptoVerification.CodeLayout
scoped syntax (name := genFnDecodesL31) "gen_fn_decodes " ident ident " [" str,* "]" : command
@[command_elab genFnDecodesL31] meta def elabGenFnDecodesL31 : CommandElab := fun stx => do
  match stx with
  | `(gen_fn_decodes $tree:ident $pfx:ident [$syms:str,*]) =>
    let codeName := `CryptoVerification.libsignalSessionCode
    let fnEntries ← liftTermElabM <| ProofLib.CodeLookup.entries codeName .fnOff
    let stubEntries ← liftTermElabM <| ProofLib.CodeLookup.entries codeName .stubOff
    let allOffs := (fnEntries ++ stubEntries).map (·.val)
    let mut ranges : Array (TSyntax `decodeRange) := #[]
    for sym in syms.getElems do
      let e ← liftTermElabM <| ProofLib.CodeLookup.lookupOff codeName sym.getString
      let a := e.val
      let greater := allOffs.filter (· > a)
      let some nextOff := greater.foldl (fun acc x => match acc with | none => some x | some m => some (min m x)) none
        | throwErrorAt sym "gen_fn_decodes: no symbol after {sym}"
      let (aLit, bLit) := (Syntax.mkNumLit (toString a), Syntax.mkNumLit (toString nextOff))
      ranges := ranges.push (← `(decodeRange| $aLit:num → $bLit:num))
    elabCommand (← `(gen_decodes $tree $pfx [$ranges,*]))
  | _ => throwUnsupportedSyntax
end CryptoVerification.SpqrV1.Layout.L31

namespace CryptoVerification.SpqrV1.Poly.DecodedMessage

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L31

/-! ## Symbol Name, Decode Tree, and Stack Budget -/

abbrev decodedMessageName : String :=
  "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"

abbrev spqrRustDeallocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

theorem decodedMessage_fnOff :
    libsignalSessionCode.fnOff decodedMessageName =
      num% (ls_off% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message") :=
  ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"

gen_fn_decodes libsignalSessionCode_tree decodedMessageBin [
  "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
]

/-- Own stack frame of `decoded_message` (`672` bytes) + `extHookStack` (`16384` bytes). -/
abbrev decodedMessageStack : Nat := 672 + extHookStack

/-! ## Total Pure Characterization of `collectPointsVecs` -/

/-- Total version of `PolyDecoder.collectPointsVecs` when `self.pts.length = 16`. -/
def collectPointsVecsTotal (self : PolyDecoder) :
    Nat → Nat → Bool → List (List Pt) → Bool × List (List Pt)
  | _, 0, retNone, pointsVecs => (retNone, pointsVecs)
  | i, rem + 1, retNone, pointsVecs =>
    let pts := self.pts[i]?.getD SortedSetPt.new
    let nec := self.necessaryPoints i
    if pts.len < nec then
      collectPointsVecsTotal self (i + 1) rem true pointsVecs
    else
      collectPointsVecsTotal self (i + 1) rem retNone (pointsVecs ++ [pts.asSlice.take nec])

theorem collectPointsVecs_eq_ok (self : PolyDecoder) :
    ∀ (rem i : Nat) (retNone : Bool) (pointsVecs : List (List Pt)),
      i + rem ≤ self.pts.length →
      PolyDecoder.collectPointsVecs self i rem retNone pointsVecs =
        .ok (collectPointsVecsTotal self i rem retNone pointsVecs)
  | 0, _, retNone, pointsVecs, _ => by
    simp [PolyDecoder.collectPointsVecs, collectPointsVecsTotal]
  | rem + 1, i, retNone, pointsVecs, hle => by
    have hi_lt : i < self.pts.length := by omega
    have hget : self.pts[i]? = some (self.pts[i]'hi_lt) := List.getElem?_eq_getElem hi_lt
    simp only [PolyDecoder.collectPointsVecs, collectPointsVecsTotal, hget, Option.getD_some]
    split
    · exact collectPointsVecs_eq_ok self rem (i + 1) true pointsVecs (by omega)
    · exact collectPointsVecs_eq_ok self rem (i + 1) retNone
        (pointsVecs ++ [(self.pts[i]'hi_lt).asSlice.take (self.necessaryPoints i)]) (by omega)

theorem collectPointsVecsTotal_fst_true (self : PolyDecoder) :
    ∀ (rem i : Nat) (pointsVecs : List (List Pt)),
      (collectPointsVecsTotal self i rem true pointsVecs).1 = true
  | 0, _, _ => rfl
  | rem + 1, i, pointsVecs => by
    simp only [collectPointsVecsTotal]
    split <;> exact collectPointsVecsTotal_fst_true self rem (i + 1) _

theorem collectPointsVecsTotal_of_fst_false (self : PolyDecoder) :
    ∀ (rem i : Nat) (retNone : Bool) (pointsVecs : List (List Pt)),
      (collectPointsVecsTotal self i rem retNone pointsVecs).1 = false →
      retNone = false ∧
        (collectPointsVecsTotal self i rem retNone pointsVecs).2.length = pointsVecs.length + rem ∧
        (∀ k, k < i + rem → i ≤ k →
          self.necessaryPoints k ≤ (self.pts[k]?.getD SortedSetPt.new).len)
  | 0, i, retNone, pointsVecs, hfalse => by
    simp only [collectPointsVecsTotal] at hfalse ⊢
    refine ⟨hfalse, by omega, ?_⟩
    intro k hk1 hk2
    omega
  | rem + 1, i, retNone, pointsVecs, hfalse => by
    simp only [collectPointsVecsTotal] at hfalse ⊢
    split_ifs at hfalse ⊢ with hlt
    · rw [collectPointsVecsTotal_fst_true] at hfalse
      contradiction
    · have ih := collectPointsVecsTotal_of_fst_false self rem (i + 1) retNone
        (pointsVecs ++ [(self.pts[i]?.getD SortedSetPt.new).asSlice.take (self.necessaryPoints i)])
        hfalse
      refine ⟨ih.1, ?_, ?_⟩
      · rw [ih.2.1, List.length_append, List.length_singleton]
        omega
      · intro k hk1 hk2
        by_cases hki : k = i
        · subst hki
          omega
        · exact ih.2.2 k (by omega) (by omega)

theorem necessaryPoints_le (self : PolyDecoder) (poly : Nat) :
    self.necessaryPoints poly ≤ self.ptsNeeded / 16 + 1 := by
  unfold PolyDecoder.necessaryPoints
  dsimp only
  split <;> omega

theorem collectPointsVecsTotal_elem_length_le (self : PolyDecoder) :
    ∀ (rem i : Nat) (retNone : Bool) (pointsVecs : List (List Pt)),
      (∀ k < pointsVecs.length, (pointsVecs[k]?.getD []).length ≤ self.ptsNeeded / 16 + 1) →
      ∀ k < (collectPointsVecsTotal self i rem retNone pointsVecs).2.length,
        ((collectPointsVecsTotal self i rem retNone pointsVecs).2[k]?.getD []).length ≤
          self.ptsNeeded / 16 + 1
  | 0, _, _, pointsVecs, hinit, k, hk => hinit k hk
  | rem + 1, i, retNone, pointsVecs, hinit, k, hk => by
    simp only [collectPointsVecsTotal] at hk ⊢
    split_ifs at hk ⊢ with hlt
    · exact collectPointsVecsTotal_elem_length_le self rem (i + 1) true pointsVecs hinit k hk
    · apply collectPointsVecsTotal_elem_length_le self rem (i + 1) retNone _ _ k hk
      intro j hj
      rw [List.length_append, List.length_singleton] at hj
      by_cases hjl : j < pointsVecs.length
      · rw [List.getElem?_append_left hjl]
        exact hinit j hjl
      · have hjeq : j = pointsVecs.length := by omega
        subst hjeq
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.getD_some, List.length_take]
        have hnec := necessaryPoints_le self i
        omega

/-- Total pure version of `Poly.lagrangeAccumulateCoeffs`. -/
def lagrangeAccumulateCoeffsTotal : Nat → Nat → List GF16 → List GF16 → List GF16
  | _, 0, outCoeffs, _ => outCoeffs
  | j, rem + 1, outCoeffs, workingCoeffs =>
    let o := outCoeffs[j]?.getD GF16.ZERO
    let w := workingCoeffs[j + 1]?.getD GF16.ZERO
    lagrangeAccumulateCoeffsTotal (j + 1) rem (outCoeffs.set j (GF16.add o w)) workingCoeffs

@[simp]
theorem lagrangeAccumulateCoeffsTotal_length :
    ∀ (rem j : Nat) (outCoeffs workingCoeffs : List GF16),
      (lagrangeAccumulateCoeffsTotal j rem outCoeffs workingCoeffs).length = outCoeffs.length
  | 0, _, outCoeffs, _ => rfl
  | rem + 1, j, outCoeffs, workingCoeffs => by
    simp only [lagrangeAccumulateCoeffsTotal, lagrangeAccumulateCoeffsTotal_length, List.length_set]

theorem lagrangeAccumulateCoeffs_eq_ok :
    ∀ (rem j : Nat) (outCoeffs workingCoeffs : List GF16),
      j + rem ≤ outCoeffs.length →
      outCoeffs.length + 1 ≤ workingCoeffs.length →
      outCoeffs.length ≤ USIZE_MAX →
      Poly.lagrangeAccumulateCoeffs j rem outCoeffs workingCoeffs =
        .ok (lagrangeAccumulateCoeffsTotal j rem outCoeffs workingCoeffs)
  | 0, _, outCoeffs, workingCoeffs, _, _, _ => by
    simp [Poly.lagrangeAccumulateCoeffs, lagrangeAccumulateCoeffsTotal]
  | rem + 1, j, outCoeffs, workingCoeffs, hj, hw, husize => by
    have hj_lt : j < outCoeffs.length := by omega
    have hjw_lt : j + 1 < workingCoeffs.length := by omega
    have hnot_ovf : ¬ (j + 1 > USIZE_MAX) := by omega
    have hget_o : outCoeffs[j]? = some (outCoeffs[j]'hj_lt) := List.getElem?_eq_getElem hj_lt
    have hget_w : workingCoeffs[j + 1]? = some (workingCoeffs[j + 1]'hjw_lt) :=
      List.getElem?_eq_getElem hjw_lt
    simp only [Poly.lagrangeAccumulateCoeffs, lagrangeAccumulateCoeffsTotal,
      hnot_ovf, ↓reduceIte, hget_o, hget_w, Option.getD_some]
    exact lagrangeAccumulateCoeffs_eq_ok rem (j + 1)
      (outCoeffs.set j (GF16.add (outCoeffs[j]'hj_lt) (workingCoeffs[j + 1]'hjw_lt)))
      workingCoeffs
      (by simp [List.length_set]; omega)
      (by simp [List.length_set]; omega)
      (by simp [List.length_set]; omega)

/-- Total pure version of `Poly.lagrangeInterpolateLoop`. -/
def lagrangeInterpolateLoopTotal (template : Poly) (pts : List Pt) :
    Nat → Nat → List GF16 → List GF16
  | _, 0, outCoeffs => outCoeffs
  | i, rem + 1, outCoeffs =>
    let working := lagrangeCompletePure template pts i
    let outCoeffs' := lagrangeAccumulateCoeffsTotal 0 outCoeffs.length outCoeffs working.coefficients
    lagrangeInterpolateLoopTotal template pts (i + 1) rem outCoeffs'

@[simp]
theorem lagrangeInterpolateLoopTotal_length (template : Poly) (pts : List Pt) :
    ∀ (rem i : Nat) (outCoeffs : List GF16),
      (lagrangeInterpolateLoopTotal template pts i rem outCoeffs).length = outCoeffs.length
  | 0, _, outCoeffs => rfl
  | rem + 1, i, outCoeffs => by
    simp only [lagrangeInterpolateLoopTotal, lagrangeInterpolateLoopTotal_length,
      lagrangeAccumulateCoeffsTotal_length]

theorem lagrangeInterpolateLoop_eq_ok (template : Poly) (pts : List Pt) :
    ∀ (rem i : Nat) (outCoeffs : List GF16),
      i + rem ≤ pts.length →
      outCoeffs.length + 1 ≤ template.coefficients.length →
      outCoeffs.length ≤ USIZE_MAX →
      Poly.lagrangeInterpolateLoop template pts i rem outCoeffs =
        .ok (lagrangeInterpolateLoopTotal template pts i rem outCoeffs)
  | 0, _, outCoeffs, _, _, _ => by
    simp [Poly.lagrangeInterpolateLoop, lagrangeInterpolateLoopTotal]
  | rem + 1, i, outCoeffs, hi, hlen, husize => by
    have hi_lt : i < pts.length := by omega
    unfold Poly.lagrangeInterpolateLoop lagrangeInterpolateLoopTotal
    change (do
      let working ← template.lagrangeInterpolateComplete pts i
      let outCoeffs' ← Poly.lagrangeAccumulateCoeffs 0 outCoeffs.length outCoeffs working.coefficients
      Poly.lagrangeInterpolateLoop template pts (i + 1) rem outCoeffs') = _
    rw [lagrangeInterpolateComplete_eq_ok hi_lt]
    dsimp only [Bind.bind, Except.bind]
    rw [lagrangeAccumulateCoeffs_eq_ok outCoeffs.length 0 outCoeffs
      (lagrangeCompletePure template pts i).coefficients (by omega)
      (by rw [lagrangeCompletePure_length]; exact hlen) husize]
    dsimp only [Bind.bind, Except.bind]
    exact lagrangeInterpolateLoop_eq_ok template pts rem (i + 1) _
      (by omega)
      (by rw [lagrangeAccumulateCoeffsTotal_length]; exact hlen)
      (by rw [lagrangeAccumulateCoeffsTotal_length]; exact husize)

/-- Total pure version of `Poly.lagrangeInterpolate`. -/
def lagrangeInterpolateTotal (pts : List Pt) : Poly :=
  if pts.isEmpty then
    Poly.zero pts.length
  else
    let template := lagrangePreparePure pts
    let working0 := lagrangeCompletePure template pts 0
    let rest0 := working0.coefficients.tail
    let outCoeffs := lagrangeInterpolateLoopTotal template pts 1 (pts.length - 1) rest0
    { coefficients := outCoeffs }

@[simp]
theorem lagrangeInterpolateTotal_length (pts : List Pt) :
    (lagrangeInterpolateTotal pts).coefficients.length = pts.length := by
  unfold lagrangeInterpolateTotal
  cases pts with
  | nil => rfl
  | cons p ps =>
    simp [lagrangeCompletePure_length, lagrangePreparePure_length]

theorem lagrangeInterpolate_eq_ok (pts : List Pt)
    (hlen : pts.length + 1 ≤ USIZE_MAX) :
    Poly.lagrangeInterpolate pts = .ok (lagrangeInterpolateTotal pts) := by
  unfold Poly.lagrangeInterpolate lagrangeInterpolateTotal
  cases pts with
  | nil => rfl
  | cons p ps =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    change (do
      let template ← Poly.lagrangeInterpolatePrepare (p :: ps)
      let working0 ← template.lagrangeInterpolateComplete (p :: ps) 0
      match working0.coefficients with
      | [] => .error .sliceIndexFail
      | _ :: rest0 => do
        let outCoeffs ← Poly.lagrangeInterpolateLoop template (p :: ps) 1 ((p :: ps).length - 1) rest0
        pure ({ coefficients := outCoeffs } : Poly)) = _
    rw [lagrangeInterpolatePrepare_eq_ok (p :: ps) hlen]
    dsimp only [Bind.bind, Except.bind]
    have h0_lt : 0 < (p :: ps).length := by simp
    rw [lagrangeInterpolateComplete_eq_ok h0_lt]
    dsimp only [Bind.bind, Except.bind]
    have hw_len : (lagrangeCompletePure (lagrangePreparePure (p :: ps)) (p :: ps) 0).coefficients.length =
        (p :: ps).length + 1 := by
      rw [lagrangeCompletePure_length, lagrangePreparePure_length]
    cases hcoeffs : (lagrangeCompletePure (lagrangePreparePure (p :: ps)) (p :: ps) 0).coefficients with
    | nil =>
      rw [hcoeffs] at hw_len
      simp at hw_len
    | cons c0 rest0 =>
      have hrest_len : rest0.length = (p :: ps).length := by
        rw [hcoeffs, List.length_cons, Nat.add_right_cancel_iff] at hw_len
        exact hw_len
      dsimp only [List.tail_cons]
      rw [lagrangeInterpolateLoop_eq_ok (lagrangePreparePure (p :: ps)) (p :: ps)
        ((p :: ps).length - 1) 1 rest0 (by omega)
        (by rw [hrest_len, lagrangePreparePure_length]) (by omega)]
      rfl

/-! ## Total Pure Characterization of `decodedMessageLoop` and `decodedMessage` -/

theorem binarySearchAux_ok_lt (target : Pt) :
    ∀ (pts : List Pt) (idx found : Nat),
      SortedSetPt.binarySearchAux target idx pts = .ok found →
      idx ≤ found ∧ found < idx + pts.length
  | [], _, _, h => by simp [SortedSetPt.binarySearchAux] at h
  | pt :: rest, idx, found, h => by
    simp only [SortedSetPt.binarySearchAux] at h
    split at h
    · have ih := binarySearchAux_ok_lt target rest (idx + 1) found h
      simp only [List.length_cons]
      omega
    · injection h with h_eq
      subst h_eq
      simp only [List.length_cons]
      omega
    · contradiction

theorem binarySearch_ok_lt (s : SortedSetPt) (target : Pt) (found : Nat)
    (h : s.binarySearch target = .ok found) :
    found < s.vec.length := by
  have haux := binarySearchAux_ok_lt target s.vec 0 found h
  omega

/-- Total pure version of `PolyDecoder.decodedMessageLoop`. -/
def decodedMessageLoopTotal (self : PolyDecoder) (pointsVecs : List (List Pt)) :
    Nat → Nat → List (Option Poly) → List (BitVec 8) →
      List (Option Poly) × List (BitVec 8)
  | _, 0, polys, out => (polys, out)
  | i, rem + 1, polys, out =>
    let poly := i % 16
    let polyIdx := i / 16
    let pt : Pt := { x := GF16.new (BitVec.ofNat 16 polyIdx), y := GF16.ZERO }
    let polyPts := self.pts[poly]?.getD SortedSetPt.new
    let (polys', y) :=
      match polyPts.binarySearch pt with
      | .ok idx =>
        let foundPt := polyPts.vec[idx]?.getD { x := GF16.ZERO, y := GF16.ZERO }
        (polys, foundPt.y)
      | .error _ =>
        let optPoly := polys[poly]?.getD none
        let (polys1, p) :=
          match optPoly with
          | some p => (polys, p)
          | none =>
            let ptsSlice := pointsVecs[poly]?.getD []
            let interp := lagrangeInterpolateTotal ptsSlice
            (polys.set poly (some interp), interp)
        let yVal := computeAtPure p pt.x
        (polys1, yVal)
    let out' := out ++ u16ToBeBytes y.value
    decodedMessageLoopTotal self pointsVecs (i + 1) rem polys' out'

theorem decodedMessageLoop_eq_ok (self : PolyDecoder) (pointsVecs : List (List Pt))
    (hpts_len : self.pts.length = 16)
    (hpv_len : pointsVecs.length = 16)
    (hpv_bound : ∀ k < 16, (pointsVecs[k]?.getD []).length + 1 ≤ USIZE_MAX) :
    ∀ (rem i : Nat) (polys : List (Option Poly)) (out : List (BitVec 8)),
      polys.length = 16 →
      PolyDecoder.decodedMessageLoop self pointsVecs i rem polys out =
        .ok (decodedMessageLoopTotal self pointsVecs i rem polys out)
  | 0, _, polys, out, _ => by
    simp [PolyDecoder.decodedMessageLoop, decodedMessageLoopTotal]
  | rem + 1, i, polys, out, hpolys_len => by
    have hpoly_lt : i % 16 < 16 := Nat.mod_lt _ (by decide)
    have hpoly_pts : i % 16 < self.pts.length := by omega
    have hget_pts : self.pts[i % 16]? = some (self.pts[i % 16]'hpoly_pts) :=
      List.getElem?_eq_getElem hpoly_pts
    unfold PolyDecoder.decodedMessageLoop decodedMessageLoopTotal
    simp only [hget_pts, Option.getD_some]
    cases hb : (self.pts[i % 16]'hpoly_pts).binarySearch
        { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO } with
    | ok idx =>
      have hidx_lt : idx < (self.pts[i % 16]'hpoly_pts).vec.length :=
        binarySearch_ok_lt (self.pts[i % 16]'hpoly_pts)
          { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO } idx hb
      have hget_found : (self.pts[i % 16]'hpoly_pts).vec[idx]? =
          some ((self.pts[i % 16]'hpoly_pts).vec[idx]'hidx_lt) :=
        List.getElem?_eq_getElem hidx_lt
      simp only [hget_found, Option.getD_some, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact decodedMessageLoop_eq_ok self pointsVecs hpts_len hpv_len hpv_bound rem (i + 1) polys _
        hpolys_len
    | error insIdx =>
      have hpoly_p : i % 16 < polys.length := by omega
      have hget_p : polys[i % 16]? = some (polys[i % 16]'hpoly_p) :=
        List.getElem?_eq_getElem hpoly_p
      simp only [hget_p, Option.getD_some]
      cases hopt : polys[i % 16]'hpoly_p with
      | some p =>
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, hget_p, hopt,
          computeAt_eq_ok p (GF16.new (BitVec.ofNat 16 (i / 16)))]
        exact decodedMessageLoop_eq_ok self pointsVecs hpts_len hpv_len hpv_bound rem (i + 1) polys _
          hpolys_len
      | none =>
        have hpoly_pv : i % 16 < pointsVecs.length := by omega
        have hget_pv : pointsVecs[i % 16]? = some (pointsVecs[i % 16]'hpoly_pv) :=
          List.getElem?_eq_getElem hpoly_pv
        have hbound_pv : (pointsVecs[i % 16]'hpoly_pv).length + 1 ≤ USIZE_MAX := by
          have hb0 := hpv_bound (i % 16) hpoly_lt
          simpa [hget_pv] using hb0
        have hset_get :
            (polys.set (i % 16) (some (lagrangeInterpolateTotal (pointsVecs[i % 16]'hpoly_pv))))[i % 16]? =
              some (some (lagrangeInterpolateTotal (pointsVecs[i % 16]'hpoly_pv))) := by
          rw [List.getElem?_set_self hpoly_p]
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, hget_pv, Option.getD_some,
          lagrangeInterpolate_eq_ok (pointsVecs[i % 16]'hpoly_pv) hbound_pv, hset_get,
          computeAt_eq_ok (lagrangeInterpolateTotal (pointsVecs[i % 16]'hpoly_pv))
            (GF16.new (BitVec.ofNat 16 (i / 16)))]
        exact decodedMessageLoop_eq_ok self pointsVecs hpts_len hpv_len hpv_bound rem (i + 1)
          (polys.set (i % 16) (some (lagrangeInterpolateTotal (pointsVecs[i % 16]'hpoly_pv)))) _
          (by simp [List.length_set, hpolys_len])

/-- Total pure version of `PolyDecoder.decodedMessage`. -/
def decodedMessageTotal (self : PolyDecoder) : Option (List (BitVec 8)) :=
  if self.isComplete then
    none
  else
    let (retNone, pointsVecs) := collectPointsVecsTotal self 0 self.pts.length false []
    if retNone then
      none
    else
      let initPolys : List (Option Poly) := List.replicate 16 none
      let (_, out) := decodedMessageLoopTotal self pointsVecs 0 self.ptsNeeded initPolys []
      some out

theorem div16_lt_necessaryPoints (self : PolyDecoder) {i : Nat} (hi : i < self.ptsNeeded) :
    i / 16 < self.necessaryPoints (i % 16) := by
  unfold PolyDecoder.necessaryPoints
  dsimp only
  split <;> omega

theorem necessaryPoints_pos_of_lt (self : PolyDecoder) {i : Nat} (hi : i < self.ptsNeeded) :
    1 ≤ self.necessaryPoints (i % 16) := by
  have := div16_lt_necessaryPoints self hi
  omega

theorem ptsNeeded_le_of_necessaryPoints_zero_le (self : PolyDecoder) {n : Nat}
    (h0 : self.necessaryPoints 0 ≤ n) :
    self.ptsNeeded ≤ 16 * n := by
  by_contra hgt
  have hi : 16 * n < self.ptsNeeded := by omega
  have hlt := div16_lt_necessaryPoints self hi
  have hdiv : (16 * n) / 16 = n := by omega
  have hmod : (16 * n) % 16 = 0 := by omega
  rw [hdiv, hmod] at hlt
  omega

theorem polyDecoderStrictSorted_elem_length_le {self : PolyDecoder}
    (hsort : PolyDecoderStrictSorted self) {k : Nat} (hk : k < self.pts.length) :
    (self.pts[k]'hk).vec.length ≤ 65536 :=
  ptListStrictSorted_length_le (hsort (self.pts[k]'hk) (List.getElem_mem hk))

theorem bsearchLoop_eq_binarySearch (s : SortedSetPt) (element : Pt)
    (hsort : SortedSetPtStrictSorted s) (hne : s.vec ≠ [])
    {b : Nat} (hb_eq : b = bsearchLoop s.vec element.x.value 0 s.vec.length)
    (hb_lt : b < s.vec.length) :
    if (s.vec[b]'hb_lt).x.value == element.x.value then
      s.binarySearch element = .ok b
    else
      s.binarySearch element = .error
        (if (s.vec[b]'hb_lt).x.value.toNat < element.x.value.toNat then b + 1 else b) := by
  subst hb_eq
  have hlen_ge1 : 1 ≤ s.vec.length := List.length_pos_iff.mpr hne
  have hb_get :
      s.vec[bsearchLoop s.vec element.x.value 0 s.vec.length]?.getD default =
        s.vec[bsearchLoop s.vec element.x.value 0 s.vec.length]'hb_lt := by
    rw [List.getElem?_eq_getElem hb_lt, Option.getD_some]
  have ⟨hL, hR⟩ := bsearchLoop_sorted_inv hsort element.x.value 0 s.vec.length hlen_ge1 (by omega)
    (Or.inl rfl) (fun k hk hge => by omega)
  have hlt_before : ∀ k (hk : k < bsearchLoop s.vec element.x.value 0 s.vec.length),
      (s.vec[k]'(Nat.lt_trans hk hb_lt)).x.value.toNat < element.x.value.toNat := by
    intro k hk
    rcases hL with hb0 | hle_b
    · omega
    · rw [hb_get] at hle_b
      have hkb := ptListStrictSorted_getElem_lt hsort (Nat.lt_trans hk hb_lt) hb_lt hk
      omega
  have hbs_drop := binarySearchAux_eq_drop s.vec element
    (bsearchLoop s.vec element.x.value 0 s.vec.length) (Nat.le_of_lt hb_lt) hlt_before
  unfold SortedSetPt.binarySearch
  rw [hbs_drop, List.drop_eq_getElem_cons hb_lt, SortedSetPt.binarySearchAux]
  split_ifs with heq hlt
  · have hnat_eq :
        (s.vec[bsearchLoop s.vec element.x.value 0 s.vec.length]'hb_lt).x.value.toNat =
          element.x.value.toNat := by
      rw [beq_iff_eq] at heq
      rw [heq]
    have hcmp :
        Pt.cmp (s.vec[bsearchLoop s.vec element.x.value 0 s.vec.length]'hb_lt) element = .eq := by
      unfold Pt.cmp
      exact compare_eq_iff_eq.mpr hnat_eq
    rw [hcmp]
  · have hcmp :
        Pt.cmp (s.vec[bsearchLoop s.vec element.x.value 0 s.vec.length]'hb_lt) element = .lt := by
      unfold Pt.cmp
      exact compare_lt_iff_lt.mpr hlt
    have hbs_b1 :
        SortedSetPt.binarySearchAux element
          (bsearchLoop s.vec element.x.value 0 s.vec.length + 1)
          (s.vec.drop (bsearchLoop s.vec element.x.value 0 s.vec.length + 1)) =
          .error (bsearchLoop s.vec element.x.value 0 s.vec.length + 1) := by
      by_cases hb1 : bsearchLoop s.vec element.x.value 0 s.vec.length + 1 < s.vec.length
      · rw [List.drop_eq_getElem_cons hb1, SortedSetPt.binarySearchAux]
        have hgt1 :
            Pt.cmp (s.vec[bsearchLoop s.vec element.x.value 0 s.vec.length + 1]'hb1) element = .gt := by
          unfold Pt.cmp
          exact compare_gt_iff_gt.mpr (hR _ hb1 (Nat.le_refl _))
        rw [hgt1]
      · have hdrop_nil :
            s.vec.drop (bsearchLoop s.vec element.x.value 0 s.vec.length + 1) = [] :=
          List.drop_eq_nil_of_le (by omega)
        rw [hdrop_nil, SortedSetPt.binarySearchAux]
    rw [hcmp, hbs_b1]
  · have hnat_ne :
        (s.vec[bsearchLoop s.vec element.x.value 0 s.vec.length]'hb_lt).x.value.toNat ≠
          element.x.value.toNat := by
      intro h
      exact heq (beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h))
    have hgt :
        element.x.value.toNat <
          (s.vec[bsearchLoop s.vec element.x.value 0 s.vec.length]'hb_lt).x.value.toNat := by
      omega
    have hcmp :
        Pt.cmp (s.vec[bsearchLoop s.vec element.x.value 0 s.vec.length]'hb_lt) element = .gt := by
      unfold Pt.cmp
      exact compare_gt_iff_gt.mpr hgt
    rw [hcmp]

theorem decodedMessage_eq_ok (self : PolyDecoder)
    (hpts_len : self.pts.length = 16)
    (hsort : PolyDecoderStrictSorted self) :
    self.decodedMessage = .ok (decodedMessageTotal self) := by
  unfold PolyDecoder.decodedMessage decodedMessageTotal
  cases hcomp : self.isComplete with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    change (do
      let (retNone, pointsVecs) ← self.collectPointsVecs 0 self.pts.length false []
      if retNone = true then
        pure none
      else if self.ptsNeeded * 2 > USIZE_MAX then
        .error .mulOverflow
      else do
        let initPolys : List (Option Poly) := List.replicate 16 none
        let (_, out) ← self.decodedMessageLoop pointsVecs 0 self.ptsNeeded initPolys []
        pure (some out)) = _
    rw [collectPointsVecs_eq_ok self self.pts.length 0 false [] (by omega)]
    dsimp only [Bind.bind, Except.bind]
    cases hret : (collectPointsVecsTotal self 0 self.pts.length false []).1 with
    | true => rfl
    | false =>
      have hpv_info := collectPointsVecsTotal_of_fst_false self self.pts.length 0 false [] hret
      have hpv_len : (collectPointsVecsTotal self 0 self.pts.length false []).2.length = 16 := by
        rw [hpv_info.2.1]
        simp [hpts_len]
      have hnec_le : ∀ k (hk : k < 16), self.necessaryPoints k ≤ 65536 := by
        intro k hk
        have hk_pts : k < self.pts.length := by omega
        have h1 := hpv_info.2.2 k (by omega) (by omega)
        rw [List.getElem?_eq_getElem hk_pts, Option.getD_some] at h1
        have h2 := polyDecoderStrictSorted_elem_length_le hsort hk_pts
        unfold SortedSetPt.len at h1
        omega
      have hpts_le : self.ptsNeeded ≤ 16 * 65536 :=
        ptsNeeded_le_of_necessaryPoints_zero_le self (hnec_le 0 (by decide))
      have hpv_bound : ∀ k < 16,
          ((collectPointsVecsTotal self 0 self.pts.length false []).2[k]?.getD []).length + 1 ≤
            USIZE_MAX := by
        intro k hk
        have hlt_len : k < (collectPointsVecsTotal self 0 self.pts.length false []).2.length := by
          omega
        have hle := collectPointsVecsTotal_elem_length_le self self.pts.length 0 false []
          (by intro j hj; simp at hj) k hlt_len
        have husize : USIZE_MAX = 0xffffffffffffffff := rfl
        omega
      have husize : USIZE_MAX = 0xffffffffffffffff := rfl
      have hnot_ovf : ¬ (self.ptsNeeded * 2 > USIZE_MAX) := by omega
      simp only [Bool.false_eq_true, ↓reduceIte, hnot_ovf]
      rw [decodedMessageLoop_eq_ok self (collectPointsVecsTotal self 0 self.pts.length false []).2
        hpts_len hpv_len hpv_bound self.ptsNeeded 0 (List.replicate 16 none) [] (by simp)]
      rfl

/-! ## Separation-Logic Predicates and Specifications for `decoded_message` (`0x6bb80`) -/

/-- Unpinned `Option<Vec<u8>>` at `a` (`24` bytes, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16` (`cap = usize::MAX` niche)
    * `some bs`: `vecU8 A a bs` -/
def optVecU8Of (A : RustAlloc) (a : BitVec 64) : Option (List (BitVec 8)) → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16
  | some bs => vecU8 A a bs

/-- A single 24-byte `Option<Poly>` cache slot in `polys: [Option<Poly>; 16]` on the stack of
    `decoded_message`:
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16`
    * `some p`: `1 ≤ p.coefficients.length ≤ 65536` and exact-capacity `Poly` header + buffer at `a` -/
def optPolyCacheSlotAt (A : RustAlloc) (a : BitVec 64) : Option Poly → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16
  | some p =>
    ∃∗ ptr : BitVec 64,
      ⌜1 ≤ p.coefficients.length ∧ p.coefficients.length ≤ 65536 ∧ ptr ≠ 0#64⌝ ∗
        (a ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
        ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
        A.live ptr (2 * p.coefficients.length) 2 ∗
        gf16SliceAt ptr p.coefficients

/-- Contiguous array of `Option<Poly>` cache slots at `base` with stride `24` bytes. -/
def optPolyCacheListAt (A : RustAlloc) : BitVec 64 → List (Option Poly) → SepProp :=
  arrayAt (fun opt a => optPolyCacheSlotAt A a opt) vecHeaderBytes

structure DecodedMessageGhost where
  out : BitVec 64
  decA : BitVec 64
  dec : PolyDecoder

def decodedMessageSpec (A : RustAlloc) (b : BitVec 64) : Spec DecodedMessageGhost where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧ s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.decA ∧
      PolyDecoderStrictSorted x.dec⌝ ∗
      memRegion x.out vecHeaderBytes ∗ polyDecoderAt A x.decA x.dec ∗
      tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt s.sp decodedMessageStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ optVecU8Of A x.out (decodedMessageTotal x.dec) ∗
      polyDecoderAt A x.decA x.dec ∗ tokenInitAt b ∗ reduceTableAt b ∗
      A.pool ∗ stackAt s0.sp decodedMessageStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def DecodedMessageOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decodedMessageName)
    (decodedMessageSpec A b)

def decodedMessagePlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec DecodedMessageGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.decA ∧ PolyDecoderStrictSorted x.dec⌝ ∗
      memRegion x.out vecHeaderBytes ∗ polyDecoderAt A x.decA x.dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s.sp decodedMessageStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ optVecU8Of A x.out (decodedMessageTotal x.dec) ∗
      polyDecoderAt A x.decA x.dec ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp decodedMessageStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def DecodedMessagePlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
    (lsmpl.base 418)
    (decodedMessagePlacedSpec A)

/-! ## Pure and Separation-Logic Helpers for `Loop.lean` and `Proof.lean` -/

/-- The list of `rem` point slices `[ (dec.pts[i]).vec.take (dec.necessaryPoints i), ... ]`
    collected by `collectPointsVecsTotal` when all `pts[k].len ≥ necessaryPoints k`. -/
def collectedSlices (dec : PolyDecoder) : Nat → Nat → List (List Pt)
  | _, 0 => []
  | i, rem + 1 =>
    let pts := dec.pts[i]?.getD SortedSetPt.new
    pts.asSlice.take (dec.necessaryPoints i) :: collectedSlices dec (i + 1) rem

@[simp]
theorem collectedSlices_length (dec : PolyDecoder) :
    ∀ (rem i : Nat), (collectedSlices dec i rem).length = rem
  | 0, _ => rfl
  | rem + 1, i => by simp [collectedSlices, collectedSlices_length]

theorem collectPointsVecsTotal_snd_eq_collectedSlices (dec : PolyDecoder) :
    ∀ (rem i : Nat) (pointsVecs : List (List Pt)),
      (collectPointsVecsTotal dec i rem false pointsVecs).1 = false →
      (collectPointsVecsTotal dec i rem false pointsVecs).2 =
        pointsVecs ++ collectedSlices dec i rem
  | 0, _, pointsVecs, _ => by
    simp [collectPointsVecsTotal, collectedSlices]
  | rem + 1, i, pointsVecs, hfalse => by
    simp only [collectPointsVecsTotal, collectedSlices] at hfalse ⊢
    split_ifs at hfalse ⊢ with hlt
    · rw [collectPointsVecsTotal_fst_true] at hfalse
      contradiction
    · rw [collectPointsVecsTotal_snd_eq_collectedSlices dec rem (i + 1) _ hfalse]
      simp [List.append_assoc]

theorem collectedSlices_getElem (dec : PolyDecoder) :
    ∀ (rem i k : Nat) (hk : k < rem),
      (collectedSlices dec i rem)[k]'(by rw [collectedSlices_length]; exact hk) =
        (dec.pts[i + k]?.getD SortedSetPt.new).vec.take (dec.necessaryPoints (i + k))
  | 0, _, _, hk => by omega
  | rem + 1, i, 0, _ => by
    simp [collectedSlices, SortedSetPt.asSlice]
  | rem + 1, i, k + 1, hk => by
    have hk' : k < rem := Nat.lt_of_succ_lt_succ hk
    change (collectedSlices dec (i + 1) rem)[k]'(by rw [collectedSlices_length]; exact hk') = _
    rw [collectedSlices_getElem dec rem (i + 1) k hk']
    have hadd : i + 1 + k = i + (k + 1) := by omega
    rw [hadd]

theorem collectPointsVecsTotal_getElem?_of_fst_false (dec : PolyDecoder)
    (hpts : dec.pts.length = 16)
    (hfalse : (collectPointsVecsTotal dec 0 16 false []).1 = false)
    {k : Nat} (hk : k < 16) :
    (collectPointsVecsTotal dec 0 16 false []).2[k]? =
      some ((dec.pts[k]'(by omega)).vec.take (dec.necessaryPoints k)) := by
  have hsnd := collectPointsVecsTotal_snd_eq_collectedSlices dec 16 0 [] hfalse
  rw [List.nil_append] at hsnd
  have hk_len : k < (collectedSlices dec 0 16).length := by
    rw [collectedSlices_length]; exact hk
  have hk_pts : k < dec.pts.length := by omega
  rw [hsnd, List.getElem?_eq_getElem hk_len, collectedSlices_getElem dec 16 0 k hk,
    Nat.zero_add, List.getElem?_eq_getElem hk_pts, Option.getD_some]

/-- Total pure mirror of the inner scan loop (`0x6bc20..0x6bc3c`) inside `collectPointsVecs`:
    scans forward from `j` up to `15` while `pts[j + 1].len < necessaryPoints (j + 1)`. -/
def scanNextValidPolyTotal (dec : PolyDecoder) : Nat → Nat → Nat
  | j, 0 => j
  | j, rem + 1 =>
    if j == 15 then 15
    else
      let pts := dec.pts[j + 1]?.getD SortedSetPt.new
      if pts.len < dec.necessaryPoints (j + 1) then
        scanNextValidPolyTotal dec (j + 1) rem
      else
        j + 1

theorem scanNextValidPolyTotal_bounds (dec : PolyDecoder) :
    ∀ (j rem : Nat), j + rem ≤ 15 →
      j ≤ scanNextValidPolyTotal dec j rem ∧ scanNextValidPolyTotal dec j rem ≤ 15
  | j, 0, hle => by simp [scanNextValidPolyTotal]; omega
  | j, rem + 1, hle => by
    simp only [scanNextValidPolyTotal]
    split_ifs with hj15 hlt
    · exact ⟨by omega, Nat.le_refl 15⟩
    · have ⟨hlo, hhi⟩ := scanNextValidPolyTotal_bounds dec (j + 1) rem (by omega)
      exact ⟨by omega, hhi⟩
    · exact ⟨by omega, by omega⟩

theorem scanNextValidPolyTotal_gt_of_lt15 (dec : PolyDecoder) :
    ∀ (rem j : Nat),
      j + rem ≤ 15 → (j < 15 → 1 ≤ rem) →
      scanNextValidPolyTotal dec j rem < 15 →
      j < scanNextValidPolyTotal dec j rem
  | 0, j, hle, hrem, hlt15 => by
    simp only [scanNextValidPolyTotal] at hlt15
    have := hrem hlt15
    omega
  | rem + 1, j, hle, _, hlt15 => by
    simp only [scanNextValidPolyTotal] at hlt15 ⊢
    split_ifs at hlt15 ⊢ with hj15 hlt
    · omega
    · have ⟨hlo, _⟩ := scanNextValidPolyTotal_bounds dec (j + 1) rem (by omega)
      omega
    · omega

theorem collectPointsVecsTotal_fst_false_of_all_ge (dec : PolyDecoder)
    (hpts : dec.pts.length = 16) :
    ∀ (rem i : Nat) (acc : List (List Pt)),
      i + rem ≤ 16 →
      (∀ k (hk : k < 16), i ≤ k → dec.necessaryPoints k ≤ (dec.pts[k]'(by rw [hpts]; exact hk)).len) →
      (collectPointsVecsTotal dec i rem false acc).1 = false
  | 0, _, _, _, _ => rfl
  | rem + 1, i, acc, hle, hall => by
    have hi : i < 16 := by omega
    have hi_pts : i < dec.pts.length := by rw [hpts]; exact hi
    have hget : dec.pts[i]?.getD SortedSetPt.new = dec.pts[i]'hi_pts := by
      rw [List.getElem?_eq_getElem hi_pts, Option.getD_some]
    have hge := hall i hi (Nat.le_refl i)
    have hnot_lt : ¬ (dec.pts[i]'hi_pts).len < dec.necessaryPoints i := by omega
    simp only [collectPointsVecsTotal, hget, hnot_lt, ↓reduceIte]
    exact collectPointsVecsTotal_fst_false_of_all_ge dec hpts rem (i + 1) _ (by omega)
      (fun k hk hik => hall k hk (by omega))

theorem exists_lt_of_collectPointsVecsTotal_fst_true (dec : PolyDecoder)
    (hpts : dec.pts.length = 16)
    (htrue : (collectPointsVecsTotal dec 0 16 false []).1 = true) :
    ∃ k, 0 ≤ k ∧ ∃ hk : k < 16, (dec.pts[k]'(by rw [hpts]; exact hk)).len < dec.necessaryPoints k := by
  by_contra hno
  have hfalse := collectPointsVecsTotal_fst_false_of_all_ge dec hpts 16 0 [] (by omega)
    (fun k hk hk0 => by
      by_contra hlt
      exact hno ⟨k, hk0, hk, Nat.lt_of_not_le hlt⟩)
  rw [hfalse] at htrue
  contradiction

theorem lagrangeAccumulateCoeffsTotal_succ {j rem : Nat} {outCoeffs workingCoeffs : List GF16}
    (hj : j < outCoeffs.length) (hjw : j + 1 < workingCoeffs.length) :
    lagrangeAccumulateCoeffsTotal j (rem + 1) outCoeffs workingCoeffs =
      lagrangeAccumulateCoeffsTotal (j + 1) rem
        (outCoeffs.set j ⟨(outCoeffs[j]'hj).value ^^^ (workingCoeffs[j + 1]'hjw).value⟩)
        workingCoeffs := by
  conv_lhs => rw [lagrangeAccumulateCoeffsTotal]
  rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjw]
  rfl

theorem lagrangeInterpolateTotal_of_pos {pts : List Pt} (hpos : 1 ≤ pts.length) :
    lagrangeInterpolateTotal pts =
      let template := lagrangePreparePure pts
      let working0 := lagrangeCompletePure template pts 0
      { coefficients :=
          lagrangeInterpolateLoopTotal template pts 1 (pts.length - 1)
            (working0.coefficients.drop 1) } := by
  have htail : ∀ (l : List GF16), l.tail = l.drop 1
    | [] => rfl
    | _ :: _ => rfl
  unfold lagrangeInterpolateTotal
  cases pts with
  | nil => simp at hpos
  | cons p ps =>
    dsimp only
    rw [htail]
    rfl

/-- Little-endian 2-byte encoding of a `GF16` element in memory. -/
def gf16LeBytes (g : GF16) : List (BitVec 8) :=
  [g.value.extractLsb' 0 8, g.value.extractLsb' 8 8]

/-- Little-endian byte list of a `List GF16` in memory. -/
def gf16ListBytes (cs : List GF16) : List (BitVec 8) :=
  cs.flatMap gf16LeBytes

@[simp] theorem gf16LeBytes_length (g : GF16) : (gf16LeBytes g).length = 2 := rfl

@[simp] theorem gf16ListBytes_length :
    ∀ (cs : List GF16), (gf16ListBytes cs).length = 2 * cs.length
  | [] => rfl
  | c :: cs => by
    change (gf16LeBytes c ++ gf16ListBytes cs).length = 2 * (cs.length + 1)
    rw [List.length_append, gf16ListBytes_length cs, gf16LeBytes_length]
    omega

theorem gf16At_eq_pointsToBytes (g : GF16) (a : BitVec 64) :
    gf16At g a = (a ↦ₛ gf16LeBytes g) := by
  unfold gf16At gf16LeBytes
  rw [pointsTo16_split8 a g.value]
  simp [pointsToBytes_cons, pointsToBytes_nil]

theorem gf16SliceAt_eq_pointsToBytes :
    ∀ (cs : List GF16) (ptr : BitVec 64),
      gf16SliceAt ptr cs = (ptr ↦ₛ gf16ListBytes cs)
  | [], ptr => by
    simp [gf16SliceAt, arrayAt, gf16ListBytes, pointsToBytes_nil]
  | c :: cs, ptr => by
    change gf16At c ptr ∗ gf16SliceAt (ptr + 2#64) cs =
      (ptr ↦ₛ (gf16LeBytes c ++ gf16ListBytes cs))
    rw [pointsToBytes_append, gf16At_eq_pointsToBytes, gf16SliceAt_eq_pointsToBytes cs (ptr + 2#64)]
    rfl

theorem gf16SliceAt_split_first {cs : List GF16} (hpos : 1 ≤ cs.length) (ptr : BitVec 64) :
    gf16SliceAt ptr cs =
      (ptr ↦₁₆ (cs[0]'(by omega)).value) ∗
        ((ptr + 2#64) ↦ₛ gf16ListBytes (cs.drop 1)) := by
  cases cs with
  | nil => simp at hpos
  | cons c rest =>
    change (ptr ↦₁₆ c.value) ∗ gf16SliceAt (ptr + 2#64) rest = _
    rw [gf16SliceAt_eq_pointsToBytes]
    rfl

theorem pointsToBytes_append_u16ToBeBytes (ptr : BitVec 64) (out : List (BitVec 8)) (y : BitVec 16) :
    (ptr ↦ₛ out) ∗
      ((ptr + BitVec.ofNat 64 out.length) ↦₈ BitVec.truncate 8 (y >>> 8)) ∗
      ((ptr + BitVec.ofNat 64 (out.length + 1)) ↦₈ BitVec.truncate 8 y) =
      (ptr ↦ₛ (out ++ u16ToBeBytes y)) := by
  unfold u16ToBeBytes
  rw [pointsToBytes_append, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have haddr : ptr + BitVec.ofNat 64 out.length + 1#64 = ptr + BitVec.ofNat 64 (out.length + 1) := by
    rw [BitVec.add_assoc, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  rw [haddr]

theorem sepProp_eq_of_entails {P Q : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P = Q :=
  ProofLib.sepProp_eq_of_entails h1 h2

theorem sortedSetPtOf_eq_exists_pin (A : RustAlloc) (v : BitVec 64) (s : SortedSetPt) :
    sortedSetPtOf A v s = ∃∗ pin : VecPin, sortedSetPtPinAt A pin s v := by
  unfold sortedSetPtOf vecOf sortedSetPtPinAt sortedSetPtAt
  apply sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    exact Entails.sepExists_right ⟨cap, ptr⟩ (Entails.refl _)
  · apply Entails.sepExists_elim; intro pin
    exact Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr (Entails.refl _))

theorem sortedSetPtListOf_eq_exists_pins (A : RustAlloc) :
    ∀ (ss : List SortedSetPt) (base : BitVec 64),
      sortedSetPtListOf A base ss =
        ∃∗ pins : List VecPin,
          ⌜pins.length = ss.length⌝ ∗ sortedSetPtListPinAt A base pins ss
  | [], base => by
    change emp = _
    apply sepProp_eq_of_entails
    · exact Entails.sepExists_right [] (Entails.pure_right rfl (Entails.refl _))
    · apply Entails.sepExists_elim; intro pins
      apply Entails.pure_left; intro hlen
      cases pins with
      | nil => exact Entails.refl _
      | cons _ _ => simp at hlen
  | s :: ss, base => by
    change sortedSetPtOf A base s ∗ sortedSetPtListOf A (base + 24#64) ss = _
    rw [sortedSetPtOf_eq_exists_pin A base s, sortedSetPtListOf_eq_exists_pins A ss (base + 24#64)]
    apply sepProp_eq_of_entails
    · rw [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro pin
      rw [sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro pins
      rw [← sepConj_assoc, sepConj_comm (sortedSetPtPinAt A pin s base), sepConj_assoc]
      apply Entails.pure_left; intro hlen
      refine Entails.sepExists_right (pin :: pins) ?_
      refine Entails.pure_right (by simp [hlen]) ?_
      exact Entails.refl _
    · apply Entails.sepExists_elim; intro pins
      apply Entails.pure_left; intro hlen
      cases pins with
      | nil => simp at hlen
      | cons pin rest =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        change sortedSetPtPinAt A pin s base ∗ sortedSetPtListPinAt A (base + 24#64) rest ss ⊢ _
        refine sepConj_mono (Entails.sepExists_right pin (Entails.refl _)) ?_
        exact Entails.sepExists_right rest (Entails.pure_right hlen (Entails.refl _))

theorem sortedSetPtListPinAt_entails_sortedSetPtListOf (A : RustAlloc) :
    ∀ (pins : List VecPin) (ss : List SortedSetPt) (base : BitVec 64),
      pins.length = ss.length →
      sortedSetPtListPinAt A base pins ss ⊢ sortedSetPtListOf A base ss := by
  intro pins ss base hlen
  rw [sortedSetPtListOf_eq_exists_pins A ss base]
  exact Entails.sepExists_right pins (Entails.pure_right hlen (Entails.refl _))

theorem sortedSetPtListPinAt_append (A : RustAlloc) :
    ∀ (pins1 pins2 : List VecPin) (ss1 ss2 : List SortedSetPt) (base : BitVec 64),
      pins1.length = ss1.length →
      sortedSetPtListPinAt A base (pins1 ++ pins2) (ss1 ++ ss2) =
        sortedSetPtListPinAt A base pins1 ss1 ∗
          sortedSetPtListPinAt A (base + BitVec.ofNat 64 (24 * ss1.length)) pins2 ss2
  | [], pins2, [], ss2, base, _ => by
    simp [sortedSetPtListPinAt]
  | [], _, _ :: _, _, _, hlen => by simp at hlen
  | _ :: _, _, [], _, _, hlen => by simp at hlen
  | pin :: pins1, pins2, s :: ss1, ss2, base, hlen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    change sortedSetPtPinAt A pin s base ∗
        sortedSetPtListPinAt A (base + 24#64) (pins1 ++ pins2) (ss1 ++ ss2) =
      (sortedSetPtPinAt A pin s base ∗ sortedSetPtListPinAt A (base + 24#64) pins1 ss1) ∗
        sortedSetPtListPinAt A (base + BitVec.ofNat 64 (24 * (ss1.length + 1))) pins2 ss2
    rw [sortedSetPtListPinAt_append A pins1 pins2 ss1 ss2 (base + 24#64) hlen, ← sepConj_assoc]
    have haddr : base + 24#64 + BitVec.ofNat 64 (24 * ss1.length) =
        base + BitVec.ofNat 64 (24 * (ss1.length + 1)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    rw [haddr]

theorem sortedSetPtListPinAt_split_take_drop (A : RustAlloc)
    (pins : List VecPin) (ss : List SortedSetPt) (i : Nat) (base : BitVec 64)
    (hpins : pins.length = ss.length) (hi : i ≤ ss.length) :
    sortedSetPtListPinAt A base pins ss =
      sortedSetPtListPinAt A base (pins.take i) (ss.take i) ∗
        sortedSetPtListPinAt A (base + BitVec.ofNat 64 (24 * i)) (pins.drop i) (ss.drop i) := by
  conv_lhs => rw [← List.take_append_drop i pins, ← List.take_append_drop i ss]
  rw [sortedSetPtListPinAt_append A (pins.take i) (pins.drop i) (ss.take i) (ss.drop i) base
    (by simp [hpins]), List.length_take_of_le hi]

theorem sortedSetPtListPinAt_focus (A : RustAlloc)
    (pins : List VecPin) (ss : List SortedSetPt) (i : Nat) (base : BitVec 64)
    (hpins : pins.length = ss.length) (hi : i < ss.length) :
    sortedSetPtListPinAt A base pins ss =
      sortedSetPtListPinAt A base (pins.take i) (ss.take i) ∗
        sortedSetPtPinAt A (pins[i]'(by omega)) (ss[i]'hi) (base + BitVec.ofNat 64 (24 * i)) ∗
        sortedSetPtListPinAt A (base + BitVec.ofNat 64 (24 * (i + 1)))
          (pins.drop (i + 1)) (ss.drop (i + 1)) := by
  have hi_pins : i < pins.length := by omega
  rw [sortedSetPtListPinAt_split_take_drop A pins ss i base hpins (Nat.le_of_lt hi),
    List.drop_eq_getElem_cons hi_pins, List.drop_eq_getElem_cons hi]
  change sortedSetPtListPinAt A base (pins.take i) (ss.take i) ∗
    (sortedSetPtPinAt A (pins[i]'hi_pins) (ss[i]'hi) (base + BitVec.ofNat 64 (24 * i)) ∗
      sortedSetPtListPinAt A (base + BitVec.ofNat 64 (24 * i) + 24#64)
        (pins.drop (i + 1)) (ss.drop (i + 1))) = _
  have haddr : base + BitVec.ofNat 64 (24 * i) + 24#64 = base + BitVec.ofNat 64 (24 * (i + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  rw [haddr, ← sepConj_assoc]

/-- Remainder of `sortedSetPtPinAt A pin s v` after exposing the 24-byte header and `ptSliceAt pin.ptr s.vec`. -/
def sortedSetPtPinRest (A : RustAlloc) (pin : VecPin) (s : SortedSetPt) : SepProp :=
  ⌜s.vec.length ≤ pin.cap.toNat ∧ pin.cap.toNat * 4 < 2 ^ 63 ∧ pin.ptr ≠ 0#64⌝ ∗
    if pin.cap = 0#64 then emp
    else A.live pin.ptr (pin.cap.toNat * 4) 2 ∗
      memRegion (pin.ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((pin.cap.toNat - s.vec.length) * 4)

theorem sortedSetPtPinAt_eq_slice (A : RustAlloc) (pin : VecPin) (s : SortedSetPt) (v : BitVec 64) :
    sortedSetPtPinAt A pin s v =
      (v ↦₆₄ pin.cap) ∗
        ((v + 8#64) ↦₆₄ pin.ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
        ptSliceAt pin.ptr s.vec ∗
        sortedSetPtPinRest A pin s := by
  unfold sortedSetPtPinAt sortedSetPtAt vecAt vecHeader vecBuf ptStride ptAlign sortedSetPtPinRest
  by_cases hcap : pin.cap = 0#64
  · have hcap0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [hcap, hcap0, ↓reduceIte, sepConj_emp]
    let φ : Prop := s.vec.length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 4 < 2 ^ 63 ∧ pin.ptr ≠ 0
    change ((v ↦₆₄ 0) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length)) ∗ ⌜φ⌝ =
      (v ↦₆₄ 0) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
        ptSliceAt pin.ptr s.vec ∗ ⌜φ⌝
    rw [show ((v ↦₆₄ 0) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length)) ∗ ⌜φ⌝ =
        ⌜φ⌝ ∗ ((v ↦₆₄ 0) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length)) by ac_rfl,
      show (v ↦₆₄ 0) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
          ptSliceAt pin.ptr s.vec ∗ ⌜φ⌝ =
        ⌜φ⌝ ∗ ((v ↦₆₄ 0) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
          ptSliceAt pin.ptr s.vec) by ac_rfl]
    apply sepProp_eq_of_entails
    · apply Entails.pure_left; intro hφ
      have hle : s.vec.length ≤ 0 := hφ.1
      have hnil : s.vec = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hnil, ptSliceAt_zero, sepConj_emp]
      exact Entails.pure_right hφ (Entails.of_eq (by ac_rfl))
    · apply Entails.pure_left; intro hφ
      have hle : s.vec.length ≤ 0 := hφ.1
      have hnil : s.vec = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hnil, ptSliceAt_zero, sepConj_emp]
      exact Entails.pure_right hφ (Entails.of_eq (by ac_rfl))
  · have hcap' : pin.cap ≠ 0 := hcap
    simp only [hcap, hcap', ↓reduceIte]
    change (((v ↦₆₄ pin.cap) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length)) ∗
        (⌜s.vec.length ≤ pin.cap.toNat ∧ pin.cap.toNat * 4 < 2 ^ 63 ∧ pin.ptr ≠ 0#64⌝ ∗
          (A.live pin.ptr (pin.cap.toNat * 4) 2 ∗ ptSliceAt pin.ptr s.vec ∗
            memRegion (pin.ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((pin.cap.toNat - s.vec.length) * 4)))) = _
    ac_rfl

/-- A single 16-byte `&[Pt]` fat-pointer element `(ptr, len)` at `a`. -/
def ptSliceRefAt (a ptr : BitVec 64) (len : Nat) : SepProp :=
  (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 len)

/-- Contiguous array of `&[Pt]` fat pointers `(pins[k].ptr, dec.necessaryPoints (start + k))`
    at `base` with stride `16` bytes. -/
def ptSliceRefListAt (dec : PolyDecoder) : Nat → BitVec 64 → List VecPin → SepProp
  | _, _, [] => emp
  | start, base, pin :: pins =>
    ptSliceRefAt base pin.ptr (dec.necessaryPoints start) ∗
      ptSliceRefListAt dec (start + 1) (base + 16#64) pins

theorem ptSliceRefListAt_append (dec : PolyDecoder) :
    ∀ (pins1 pins2 : List VecPin) (start : Nat) (base : BitVec 64),
      ptSliceRefListAt dec start base (pins1 ++ pins2) =
        ptSliceRefListAt dec start base pins1 ∗
          ptSliceRefListAt dec (start + pins1.length) (base + BitVec.ofNat 64 (16 * pins1.length)) pins2
  | [], pins2, start, base => by
    simp [ptSliceRefListAt]
  | pin :: pins1, pins2, start, base => by
    change ptSliceRefAt base pin.ptr (dec.necessaryPoints start) ∗
        ptSliceRefListAt dec (start + 1) (base + 16#64) (pins1 ++ pins2) =
      (ptSliceRefAt base pin.ptr (dec.necessaryPoints start) ∗
        ptSliceRefListAt dec (start + 1) (base + 16#64) pins1) ∗
        ptSliceRefListAt dec (start + (pins1.length + 1))
          (base + BitVec.ofNat 64 (16 * (pins1.length + 1))) pins2
    rw [ptSliceRefListAt_append dec pins1 pins2 (start + 1) (base + 16#64), ← sepConj_assoc]
    have hstart : start + 1 + pins1.length = start + (pins1.length + 1) := by omega
    have haddr : base + 16#64 + BitVec.ofNat 64 (16 * pins1.length) =
        base + BitVec.ofNat 64 (16 * (pins1.length + 1)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    rw [hstart, haddr]

theorem ptSliceRefListAt_take_succ (dec : PolyDecoder) (pins : List VecPin) (i : Nat)
    (base : BitVec 64) (hi : i < pins.length) :
    ptSliceRefListAt dec 0 base (pins.take i) ∗
      ptSliceRefAt (base + BitVec.ofNat 64 (16 * i)) (pins[i]'hi).ptr (dec.necessaryPoints i) =
      ptSliceRefListAt dec 0 base (pins.take (i + 1)) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    ptSliceRefListAt_append, List.length_take_of_le (Nat.le_of_lt hi)]
  simp [ptSliceRefListAt]

theorem ptSliceRefListAt_split_take_drop (dec : PolyDecoder) (pins : List VecPin) (i : Nat)
    (base : BitVec 64) (hi : i ≤ pins.length) :
    ptSliceRefListAt dec 0 base pins =
      ptSliceRefListAt dec 0 base (pins.take i) ∗
        ptSliceRefListAt dec i (base + BitVec.ofNat 64 (16 * i)) (pins.drop i) := by
  conv_lhs => rw [← List.take_append_drop i pins]
  rw [ptSliceRefListAt_append, List.length_take_of_le hi, Nat.zero_add]

theorem ptSliceRefListAt_focus (dec : PolyDecoder) (pins : List VecPin) (i : Nat)
    (base : BitVec 64) (hi : i < pins.length) :
    ptSliceRefListAt dec 0 base pins =
      ptSliceRefListAt dec 0 base (pins.take i) ∗
        ptSliceRefAt (base + BitVec.ofNat 64 (16 * i)) (pins[i]'hi).ptr (dec.necessaryPoints i) ∗
        ptSliceRefListAt dec (i + 1) (base + BitVec.ofNat 64 (16 * (i + 1))) (pins.drop (i + 1)) := by
  rw [ptSliceRefListAt_split_take_drop dec pins i base (Nat.le_of_lt hi),
    List.drop_eq_getElem_cons hi]
  change ptSliceRefListAt dec 0 base (pins.take i) ∗
    (ptSliceRefAt (base + BitVec.ofNat 64 (16 * i)) (pins[i]'hi).ptr (dec.necessaryPoints i) ∗
      ptSliceRefListAt dec (i + 1) (base + BitVec.ofNat 64 (16 * i) + 16#64) (pins.drop (i + 1))) = _
  have haddr : base + BitVec.ofNat 64 (16 * i) + 16#64 = base + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  rw [haddr, ← sepConj_assoc]

theorem ptSliceRefListAt_entails_memRegion (dec : PolyDecoder) :
    ∀ (pins : List VecPin) (start : Nat) (base : BitVec 64),
      16 * pins.length < 2 ^ 64 →
      ptSliceRefListAt dec start base pins ⊢ memRegion base (16 * pins.length)
  | [], _, base, _ => by
    simp [ptSliceRefListAt, memRegion_zero]
    exact Entails.refl _
  | pin :: pins, start, base, hbound => by
    simp only [List.length_cons] at hbound
    change ((base ↦₆₄ pin.ptr) ∗ ((base + 8#64) ↦₆₄ BitVec.ofNat 64 (dec.necessaryPoints start))) ∗
        ptSliceRefListAt dec (start + 1) (base + 16#64) pins ⊢
      memRegion base (16 * (pins.length + 1))
    rw [sepConj_assoc, show 16 * (pins.length + 1) = 8 + (8 + 16 * pins.length) by omega,
      memRegion_split base 8 (8 + 16 * pins.length) (by omega),
      memRegion_split (base + 8#64) 8 (16 * pins.length) (by omega),
      ProofLib.memRegion_eight base, ProofLib.memRegion_eight (base + 8#64),
      BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 from rfl]
    refine sepConj_mono (Entails.sepExists_intro pin.ptr) ?_
    refine sepConj_mono (Entails.sepExists_intro _) ?_
    exact ptSliceRefListAt_entails_memRegion dec pins (start + 1) (base + 16#64) (by omega)

theorem optPolyCacheListAt_append (A : RustAlloc) :
    ∀ (xs ys : List (Option Poly)) (base : BitVec 64),
      optPolyCacheListAt A base (xs ++ ys) =
        optPolyCacheListAt A base xs ∗
          optPolyCacheListAt A (base + BitVec.ofNat 64 (24 * xs.length)) ys
  | [], ys, base => by
    simp [optPolyCacheListAt, arrayAt]
  | x :: xs, ys, base => by
    change optPolyCacheSlotAt A base x ∗ optPolyCacheListAt A (base + 24#64) (xs ++ ys) =
      (optPolyCacheSlotAt A base x ∗ optPolyCacheListAt A (base + 24#64) xs) ∗
        optPolyCacheListAt A (base + BitVec.ofNat 64 (24 * (xs.length + 1))) ys
    rw [optPolyCacheListAt_append A xs ys (base + 24#64), ← sepConj_assoc]
    have haddr : base + 24#64 + BitVec.ofNat 64 (24 * xs.length) =
        base + BitVec.ofNat 64 (24 * (xs.length + 1)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    rw [haddr]

theorem optPolyCacheListAt_split_take_drop (A : RustAlloc) (ps : List (Option Poly)) (i : Nat)
    (base : BitVec 64) (hi : i ≤ ps.length) :
    optPolyCacheListAt A base ps =
      optPolyCacheListAt A base (ps.take i) ∗
        optPolyCacheListAt A (base + BitVec.ofNat 64 (24 * i)) (ps.drop i) := by
  conv_lhs => rw [← List.take_append_drop i ps]
  rw [optPolyCacheListAt_append, List.length_take_of_le hi]

theorem optPolyCacheListAt_focus (A : RustAlloc) (ps : List (Option Poly)) (i : Nat)
    (base : BitVec 64) (hi : i < ps.length) :
    optPolyCacheListAt A base ps =
      optPolyCacheListAt A base (ps.take i) ∗
        optPolyCacheSlotAt A (base + BitVec.ofNat 64 (24 * i)) (ps[i]'hi) ∗
        optPolyCacheListAt A (base + BitVec.ofNat 64 (24 * (i + 1))) (ps.drop (i + 1)) := by
  rw [optPolyCacheListAt_split_take_drop A ps i base (Nat.le_of_lt hi),
    List.drop_eq_getElem_cons hi]
  change optPolyCacheListAt A base (ps.take i) ∗
    (optPolyCacheSlotAt A (base + BitVec.ofNat 64 (24 * i)) (ps[i]'hi) ∗
      optPolyCacheListAt A (base + BitVec.ofNat 64 (24 * i) + 24#64) (ps.drop (i + 1))) = _
  have haddr : base + BitVec.ofNat 64 (24 * i) + 24#64 = base + BitVec.ofNat 64 (24 * (i + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  rw [haddr, ← sepConj_assoc]

theorem optPolyCacheListAt_set (A : RustAlloc) (ps : List (Option Poly)) (i : Nat)
    (opt : Option Poly) (base : BitVec 64) (hi : i < ps.length) :
    optPolyCacheListAt A base (ps.set i opt) =
      optPolyCacheListAt A base (ps.take i) ∗
        optPolyCacheSlotAt A (base + BitVec.ofNat 64 (24 * i)) opt ∗
        optPolyCacheListAt A (base + BitVec.ofNat 64 (24 * (i + 1))) (ps.drop (i + 1)) := by
  have hi' : i < (ps.set i opt).length := by rw [List.length_set]; exact hi
  rw [optPolyCacheListAt_focus A (ps.set i opt) i base hi']
  simp [List.take_set_of_le (Nat.le_refl i), List.drop_set_of_lt (Nat.lt_succ_self i)]

@[simp]
theorem cat128_extractLsb_lo (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_kernel

@[simp]
theorem cat128_extractLsb_hi (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_kernel

end CryptoVerification.SpqrV1.Poly.DecodedMessage
