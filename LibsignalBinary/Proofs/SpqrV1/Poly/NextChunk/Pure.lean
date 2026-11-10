/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Defs

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Pure Loop and Point Characterizations

**Checked by Lean.**

Pure characterizations of `enumeratePts`, `checkCompletePoints`, `PolyEncoder.chunkAtLoop`, and
`Point` evaluation for `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.CodeLayout

gen_decodes libsignalSessionCode_tree polyNextChunkBin [0x64f8c → 0x662bc]

/-! ## 1. `enumeratePts` and `checkCompletePoints` Lemmas -/

@[simp]
theorem enumeratePts_length :
    ∀ (x : Nat) (ys : List GF16), (PolyEncoder.enumeratePts x ys).length = ys.length
  | _, [] => rfl
  | x, _ :: ys => by simp [PolyEncoder.enumeratePts, enumeratePts_length]

theorem checkCompletePoints_enumeratePts :
    ∀ (x : Nat) (ys : List GF16),
      Poly.checkCompletePoints x (PolyEncoder.enumeratePts x ys) = true
  | _, [] => rfl
  | x, _ :: ys => by
    simp [PolyEncoder.enumeratePts, Poly.checkCompletePoints,
      checkCompletePoints_enumeratePts (x + 1) ys]

theorem enumeratePts_getElem? :
    ∀ (x : Nat) (ys : List GF16) (k : Nat),
      (PolyEncoder.enumeratePts x ys)[k]? =
        ys[k]?.map (fun y => { x := GF16.new (BitVec.ofNat 16 (x + k)), y := y })
  | _, [], _ => rfl
  | x, y :: _, 0 => by simp [PolyEncoder.enumeratePts]
  | x, _ :: ys, k + 1 => by
    simp [PolyEncoder.enumeratePts, enumeratePts_getElem? (x + 1) ys k,
      Nat.add_right_comm, Nat.add_assoc]

theorem enumeratePts_map_one :
    ∀ (x : Nat) (ys : List GF16),
      (PolyEncoder.enumeratePts x ys).map (fun pt => { x := pt.x, y := GF16.ONE }) =
        PolyEncoder.enumeratePts x (List.replicate ys.length GF16.ONE)
  | _, [] => rfl
  | x, _ :: ys => by
    simp [PolyEncoder.enumeratePts, List.replicate_succ, enumeratePts_map_one (x + 1) ys]

theorem mul_two_add_two_le_of_mul_two_lt {n cap : Nat}
    (hle : n ≤ cap) (hlt : cap * 2 < 2 ^ 63) :
    2 * n + 2 ≤ 2 ^ 63 := by
  omega

theorem pointsToPolysLoop_length {pts : List Point} :
    ∀ (rem i : Nat) (acc polys : List Poly),
      PolyEncoder.pointsToPolysLoop pts i rem acc = .ok polys →
      polys.length = acc.length + rem
  | 0, _, acc, polys, h => by
    simp only [PolyEncoder.pointsToPolysLoop, Except.ok.injEq] at h
    subst h
    omega
  | rem + 1, i, acc, polys, h => by
    unfold PolyEncoder.pointsToPolysLoop at h
    cases hpt : pts[i]? with
    | none => simp [hpt] at h
    | some ptList =>
      simp only [hpt, Bind.bind, Except.bind] at h
      cases hfc : Poly.fromCompletePoints (PolyEncoder.enumeratePts 0 ptList.value) with
      | error e => simp [hfc] at h
      | ok res =>
        simp only [hfc] at h
        cases res with
        | error u => simp at h
        | ok p =>
          simp only at h
          have ih := pointsToPolysLoop_length rem (i + 1) (acc ++ [p]) polys h
          simp at ih
          omega

theorem pointsToPolysLoop_length_zero {pts : List Point} {polys : List Poly}
    (h : PolyEncoder.pointsToPolysLoop pts 0 NUM_POLYS [] = .ok polys) :
    polys.length = NUM_POLYS := by
  have hlen := pointsToPolysLoop_length NUM_POLYS 0 [] polys h
  simpa using hlen

/-! ## 2. `chunkAtLoop` and `pointAt` Pure Characterization -/

theorem totalIdx_mod_16 (idx : BitVec 16) {i : Nat} (hi : i < 16) :
    (idx.toNat * 16 + i) % 16 = i := by
  omega

theorem totalIdx_div_16 (idx : BitVec 16) {i : Nat} (hi : i < 16) :
    (idx.toNat * 16 + i) / 16 = idx.toNat := by
  omega

@[simp]
theorem ofNat_16_toNat (idx : BitVec 16) :
    BitVec.ofNat 16 idx.toNat = idx := by
  simp

theorem pointAt_polys_eq {idx : BitVec 32} {polys : List Poly} {i : Nat}
    (hi : i < polys.length) :
    PolyEncoder.pointAt { idx := idx, s := .polys polys } i (idx.setWidth 16).toNat =
      .ok ({ idx := idx, s := .polys polys },
        computeAtPure (polys[i]'hi) (GF16.new (idx.setWidth 16))) := by
  have hp : polys[i]? = some (polys[i]'hi) := List.getElem?_eq_getElem hi
  unfold PolyEncoder.pointAt
  simp only [hp, computeAt_eq_ok, ofNat_16_toNat, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Pure byte accumulator for `PolyEncoder.chunkAtLoop` in the `EncoderState.polys` state. -/
def chunkPolysBytes (idx : BitVec 16) (polys : List Poly) : Nat → Nat → List (BitVec 8)
  | _, 0 => []
  | i, rem + 1 =>
    let p : GF16 := match polys[i]? with
      | some poly => computeAtPure poly (GF16.new idx)
      | none => GF16.ZERO
    BitVec.setWidth 8 (p.value >>> 8) :: BitVec.setWidth 8 p.value ::
      chunkPolysBytes idx polys (i + 1) rem

@[simp]
theorem chunkPolysBytes_length (idx : BitVec 16) (polys : List Poly) (i rem : Nat) :
    (chunkPolysBytes idx polys i rem).length = 2 * rem := by
  induction rem generalizing i with
  | zero => simp [chunkPolysBytes]
  | succ rem ih =>
    unfold chunkPolysBytes
    simp only [List.length_cons, ih]
    omega

theorem chunkAtLoop_polys_eq (idx : BitVec 32) (polys : List Poly) :
    ∀ (rem i : Nat),
      i + rem ≤ 16 →
      polys.length = 16 →
      PolyEncoder.chunkAtLoop (idx.setWidth 16) i rem { idx := idx, s := .polys polys } =
        .ok ({ idx := idx, s := .polys polys },
          ⟨chunkPolysBytes (idx.setWidth 16) polys i rem,
            chunkPolysBytes_length (idx.setWidth 16) polys i rem⟩)
  | 0, _, _, _ => by
    simp [PolyEncoder.chunkAtLoop, chunkPolysBytes, List.Vector.nil]
  | rem + 1, i, hle, hlen => by
    have hi16 : i < 16 := by omega
    have hi_len : i < polys.length := by omega
    have hp : polys[i]? = some (polys[i]'hi_len) := List.getElem?_eq_getElem hi_len
    have hmod : ((idx.setWidth 16).toNat * 16 + i) % 16 = i := totalIdx_mod_16 (idx.setWidth 16) hi16
    have hdiv : ((idx.setWidth 16).toNat * 16 + i) / 16 = (idx.setWidth 16).toNat :=
      totalIdx_div_16 (idx.setWidth 16) hi16
    have hpt := pointAt_polys_eq (idx := idx) hi_len
    have ih := chunkAtLoop_polys_eq idx polys rem (i + 1) (by omega) hlen
    unfold PolyEncoder.chunkAtLoop chunkPolysBytes
    simp only [hmod, hdiv, hpt, ih, hp, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl

theorem nextChunk_polys_eq {idx : BitVec 32} {polys : List Poly}
    (hlen : polys.length = 16) :
    PolyEncoder.nextChunk { idx := idx, s := .polys polys } =
      .ok ({ idx := idx + 1#32, s := .polys polys },
        { index := idx.setWidth 16,
          data := ⟨chunkPolysBytes (idx.setWidth 16) polys 0 16,
            chunkPolysBytes_length (idx.setWidth 16) polys 0 16⟩ }) := by
  unfold PolyEncoder.nextChunk PolyEncoder.chunkAt
  rw [chunkAtLoop_polys_eq idx polys 16 0 (by decide) hlen]
  rfl

theorem pointAt_points_lt_eq {idx : BitVec 32} {pts : List Point} {i : Nat}
    (hi : i < pts.length)
    (hlt : (idx.setWidth 16).toNat < (pts[i]'hi).value.length) :
    PolyEncoder.pointAt { idx := idx, s := .points pts } i (idx.setWidth 16).toNat =
      .ok ({ idx := idx, s := .points pts },
        (pts[i]'hi).value[(idx.setWidth 16).toNat]'hlt) := by
  have hpt : pts[i]? = some (pts[i]'hi) := List.getElem?_eq_getElem hi
  have hval : (pts[i]'hi).value[(idx.setWidth 16).toNat]? =
      some ((pts[i]'hi).value[(idx.setWidth 16).toNat]'hlt) := List.getElem?_eq_getElem hlt
  unfold PolyEncoder.pointAt
  simp only [hpt, hval, Pure.pure, Except.pure]

/-- Pure byte accumulator for `PolyEncoder.chunkAtLoop` when `EncoderState.points` has all
`pts[k].value.length > idx`. -/
def chunkPointsBytes (idx : BitVec 16) (pts : List Point) : Nat → Nat → List (BitVec 8)
  | _, 0 => []
  | i, rem + 1 =>
    let p : GF16 := match pts[i]? with
      | some pt => pt.value[idx.toNat]?.getD GF16.ZERO
      | none => GF16.ZERO
    BitVec.setWidth 8 (p.value >>> 8) :: BitVec.setWidth 8 p.value ::
      chunkPointsBytes idx pts (i + 1) rem

@[simp]
theorem chunkPointsBytes_length (idx : BitVec 16) (pts : List Point) (i rem : Nat) :
    (chunkPointsBytes idx pts i rem).length = 2 * rem := by
  induction rem generalizing i with
  | zero => simp [chunkPointsBytes]
  | succ rem ih =>
    unfold chunkPointsBytes
    simp only [List.length_cons, ih]
    omega

theorem chunkAtLoop_points_all_lt_eq (idx : BitVec 32) (pts : List Point) :
    ∀ (rem i : Nat),
      i + rem ≤ 16 →
      pts.length = 16 →
      (∀ k (hk : k < pts.length), i ≤ k → (idx.setWidth 16).toNat < (pts[k]'hk).value.length) →
      PolyEncoder.chunkAtLoop (idx.setWidth 16) i rem { idx := idx, s := .points pts } =
        .ok ({ idx := idx, s := .points pts },
          ⟨chunkPointsBytes (idx.setWidth 16) pts i rem,
            chunkPointsBytes_length (idx.setWidth 16) pts i rem⟩)
  | 0, _, _, _, _ => by
    simp [PolyEncoder.chunkAtLoop, chunkPointsBytes, List.Vector.nil]
  | rem + 1, i, hle, hlen, hall => by
    have hi16 : i < 16 := by omega
    have hi_len : i < pts.length := by omega
    have hlt_i : (idx.setWidth 16).toNat < (pts[i]'hi_len).value.length :=
      hall i hi_len (Nat.le_refl i)
    have hpt_opt : pts[i]? = some (pts[i]'hi_len) := List.getElem?_eq_getElem hi_len
    have hval_opt : (pts[i]'hi_len).value[(idx.setWidth 16).toNat]? =
        some ((pts[i]'hi_len).value[(idx.setWidth 16).toNat]'hlt_i) :=
      List.getElem?_eq_getElem hlt_i
    have hmod : ((idx.setWidth 16).toNat * 16 + i) % 16 = i := totalIdx_mod_16 (idx.setWidth 16) hi16
    have hdiv : ((idx.setWidth 16).toNat * 16 + i) / 16 = (idx.setWidth 16).toNat :=
      totalIdx_div_16 (idx.setWidth 16) hi16
    have hpt := pointAt_points_lt_eq (idx := idx) hi_len hlt_i
    have ih := chunkAtLoop_points_all_lt_eq idx pts rem (i + 1) (by omega) hlen
      (fun k hk hik => hall k hk (by omega))
    unfold PolyEncoder.chunkAtLoop chunkPointsBytes
    simp only [hmod, hdiv, hpt, ih, hpt_opt, hval_opt, Option.getD_some,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl

theorem nextChunk_points_all_lt_eq {idx : BitVec 32} {pts : List Point}
    (hlen : pts.length = 16)
    (hall : ∀ k (hk : k < pts.length), (idx.setWidth 16).toNat < (pts[k]'hk).value.length) :
    PolyEncoder.nextChunk { idx := idx, s := .points pts } =
      .ok ({ idx := idx + 1#32, s := .points pts },
        { index := idx.setWidth 16,
          data := ⟨chunkPointsBytes (idx.setWidth 16) pts 0 16,
            chunkPointsBytes_length (idx.setWidth 16) pts 0 16⟩ }) := by
  unfold PolyEncoder.nextChunk PolyEncoder.chunkAt
  rw [chunkAtLoop_points_all_lt_eq idx pts 16 0 (by decide) hlen (fun k hk _ => hall k hk)]
  rfl

theorem pointAt_points_ge_eq {idx : BitVec 32} {pts : List Point} {polys : List Poly} {i : Nat}
    (hi : i < pts.length)
    (hge : (pts[i]'hi).value.length ≤ (idx.setWidth 16).toNat)
    (hloop : PolyEncoder.pointsToPolysLoop pts 0 NUM_POLYS [] = .ok polys) :
    PolyEncoder.pointAt { idx := idx, s := .points pts } i (idx.setWidth 16).toNat =
      PolyEncoder.pointAt { idx := idx, s := .polys polys } i (idx.setWidth 16).toNat := by
  have hpt : pts[i]? = some (pts[i]'hi) := List.getElem?_eq_getElem hi
  have hval : (pts[i]'hi).value[(idx.setWidth 16).toNat]? = none :=
    List.getElem?_eq_none hge
  unfold PolyEncoder.pointAt
  simp only [hpt, hval, hloop, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem chunkAtLoop_points_ge_eq (idx : BitVec 32) (pts : List Point) (polys : List Poly)
    (rem i : Nat) (hi_rem : i + (rem + 1) ≤ 16)
    (hlen_pts : pts.length = 16)
    (hge : (pts[i]'(by omega)).value.length ≤ (idx.setWidth 16).toNat)
    (hloop : PolyEncoder.pointsToPolysLoop pts 0 NUM_POLYS [] = .ok polys) :
    PolyEncoder.chunkAtLoop (idx.setWidth 16) i (rem + 1) { idx := idx, s := .points pts } =
      .ok ({ idx := idx, s := .polys polys },
        ⟨chunkPolysBytes (idx.setWidth 16) polys i (rem + 1),
          chunkPolysBytes_length (idx.setWidth 16) polys i (rem + 1)⟩) := by
  have hlen_polys : polys.length = 16 := pointsToPolysLoop_length_zero hloop
  have hi16 : i < 16 := by omega
  have hi_pts : i < pts.length := by omega
  have hi_polys : i < polys.length := by omega
  have hp : polys[i]? = some (polys[i]'hi_polys) := List.getElem?_eq_getElem hi_polys
  have hmod : ((idx.setWidth 16).toNat * 16 + i) % 16 = i := totalIdx_mod_16 (idx.setWidth 16) hi16
  have hdiv : ((idx.setWidth 16).toNat * 16 + i) / 16 = (idx.setWidth 16).toNat :=
    totalIdx_div_16 (idx.setWidth 16) hi16
  have hpt_ge := pointAt_points_ge_eq (idx := idx) hi_pts hge hloop
  have hpt_poly := pointAt_polys_eq (idx := idx) hi_polys
  have htail := chunkAtLoop_polys_eq idx polys rem (i + 1) (by omega) hlen_polys
  unfold PolyEncoder.chunkAtLoop chunkPolysBytes
  simp only [hmod, hdiv, hpt_ge, hpt_poly, htail, hp,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

end CryptoVerification.SpqrV1.Poly.NextChunk
