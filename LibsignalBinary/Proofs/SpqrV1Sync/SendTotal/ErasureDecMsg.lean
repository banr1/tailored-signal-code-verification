/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import ProofLib

/-!
# Decoded Message Length on Well-Formed Decoders

Proves that `PolyDecoder.decodedMessage` on a `DecWF n` decoder returns a message of length
`2 * n` bytes (`st_decMsg`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1

private theorem except_bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem decodedMessageLoop_length (d : PolyDecoder) (pv : List (List Pt))
    (i rem : ℕ) (polys polys' : List (Option Poly)) (acc out : List (BitVec 8))
    (h : d.decodedMessageLoop pv i rem polys acc = .ok (polys', out)) :
    out.length = acc.length + 2 * rem := by
  induction rem generalizing i polys acc with
  | zero =>
    simp only [PolyDecoder.decodedMessageLoop, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    omega
  | succ rem ih =>
    have hstep (p1 : List (Option Poly)) (y : GF16)
        (hrec : d.decodedMessageLoop pv (i + 1) rem p1 (acc ++ u16ToBeBytes y.value) =
          .ok (polys', out)) :
        out.length = acc.length + 2 * (rem + 1) := by
      have hlen := ih (i + 1) p1 (acc ++ u16ToBeBytes y.value) hrec
      simp only [List.length_append, u16ToBeBytes, List.length_cons, List.length_nil] at hlen
      omega
    unfold PolyDecoder.decodedMessageLoop at h
    cases hpts : d.pts[i % 16]? with
    | none => simp [hpts] at h
    | some polyPts =>
      simp only [hpts] at h
      let pt : Pt := { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO }
      cases hbs : polyPts.binarySearch pt with
      | ok idx =>
        simp only [pt, hbs] at h
        cases hv : polyPts.vec[idx]? with
        | none => simp [hv, Bind.bind, Except.bind] at h
        | some foundPt =>
          simp only [hv, Bind.bind, Except.bind, pure, Except.pure] at h
          exact hstep polys foundPt.y h
      | error _ =>
        simp only [pt, hbs] at h
        cases hopt : polys[i % 16]? with
        | none => simp [hopt, Bind.bind, Except.bind] at h
        | some optPoly =>
          simp only [hopt] at h
          cases optPoly with
          | some _ =>
            simp only [Bind.bind, Except.bind, pure, Except.pure] at h
            cases hp1 : polys[i % 16]? with
            | none => simp [hp1] at h
            | some op =>
              cases op with
              | none => simp [hp1] at h
              | some p =>
                simp only [hp1] at h
                cases hcomp : p.computeAt (GF16.new (BitVec.ofNat 16 (i / 16))) with
                | error _ => simp [hcomp] at h
                | ok yVal =>
                  simp only [hcomp] at h
                  exact hstep polys yVal h
          | none =>
            cases hpv : pv[i % 16]? with
            | none => simp [hpv, Bind.bind, Except.bind] at h
            | some ptsSlice =>
              simp only [hpv] at h
              cases hinterp : Poly.lagrangeInterpolate ptsSlice with
              | error _ => simp [hinterp, Bind.bind, Except.bind] at h
              | ok interp =>
                simp only [hinterp, Bind.bind, Except.bind, pure, Except.pure] at h
                cases hp1 : (polys.set (i % 16) (some interp))[i % 16]? with
                | none => simp [hp1] at h
                | some op =>
                  cases op with
                  | none => simp [hp1] at h
                  | some p =>
                    simp only [hp1] at h
                    cases hcomp : p.computeAt (GF16.new (BitVec.ofNat 16 (i / 16))) with
                    | error _ => simp [hcomp] at h
                    | ok yVal =>
                      simp only [hcomp] at h
                      exact hstep (polys.set (i % 16) (some interp)) yVal h

/-- Any message returned by `PolyDecoder.decodedMessage` on a `DecWF n` decoder has length
`2 * n`. -/
theorem st_decMsg : DecMsgStmt := by
  intro n d out hwf hmsg
  unfold PolyDecoder.decodedMessage at hmsg
  by_cases hc : d.isComplete
  · simp [hc, pure, Except.pure] at hmsg
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmsg
    obtain ⟨⟨retNone, pv⟩, _, hrest⟩ := except_bind_eq_ok hmsg
    dsimp only at hrest
    by_cases hr : retNone
    · simp [hr, pure, Except.pure] at hrest
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at hrest
      by_cases hm : d.ptsNeeded * 2 > USIZE_MAX
      · simp [hm] at hrest
      · simp only [hm, ↓reduceIte] at hrest
        obtain ⟨⟨polys', out'⟩, hloop, hret⟩ := except_bind_eq_ok hrest
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hret
        subst hret
        have hlen := decodedMessageLoop_length d pv 0 d.ptsNeeded _ polys' [] out' hloop
        rw [List.length_nil, Nat.zero_add, hwf.1] at hlen
        exact hlen

end CryptoVerification.SpqrV1Sync.SendTotal
