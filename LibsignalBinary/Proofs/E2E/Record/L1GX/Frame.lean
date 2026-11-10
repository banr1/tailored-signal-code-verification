/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.MergeField

/-!
# Framing `DeserializeGeneral` `merge_field` leaves into PQXDH scope

Lifts `DeserializeGeneral` `merge_field` contracts (`mergeFieldGenSpec`) to `.base` fields in
`mergeFieldXSpec` when the PQXDH extension fields are at their empty defaults, together with
predicate-weakening and disjunction combinators for `MergeFieldXOk`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

/-- Separates the field predicate `P x.fld` from the `P`-independent spatial precondition of `mergeFieldXSpec`. -/
theorem mergeFieldXSpec_pre_iff {P : GenFieldX → Prop} {x : MergeFieldXGhost} {s : State}
    {R : SepProp} :
    (s.mem ⊨ (mergeFieldXSpec P).pre x s ∗ R) ↔
      P x.fld ∧ (s.mem ⊨ (mergeFieldXSpec (fun _ => True)).pre x s ∗ R) := by
  simp only [mergeFieldXSpec, sepConj_assoc, satisfies_pure_sepConj]
  constructor
  · rintro ⟨⟨h0, h1, h2, h3, h4, hp, hr⟩, hm⟩
    exact ⟨hp, ⟨h0, h1, h2, h3, h4, trivial, hr⟩, hm⟩
  · rintro ⟨hp, ⟨h0, h1, h2, h3, h4, -, hr⟩, hm⟩
    exact ⟨⟨h0, h1, h2, h3, h4, hp, hr⟩, hm⟩

/-- Monotonicity of `MergeFieldXOk` in the field predicate. -/
theorem mergeFieldXOk_of_imp {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {P Q : GenFieldX → Prop} (hP : MergeFieldXOk C ctl P abs)
    (hQP : ∀ fl, Q fl → P fl) : MergeFieldXOk C ctl Q abs := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hq, hpre⟩ := mergeFieldXSpec_pre_iff.mp hpre
  exact subroutine_ok.mono_outcome hP x R s0 hpc hrun
    (mergeFieldXSpec_pre_iff.mpr ⟨hQP _ hq, hpre⟩) hal fun _ hout => hout

/-- Disjunction introduction for `MergeFieldXOk` field predicates. -/
theorem mergeFieldXOk_or {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {P Q : GenFieldX → Prop} (hP : MergeFieldXOk C ctl P abs)
    (hQ : MergeFieldXOk C ctl Q abs) :
    MergeFieldXOk C ctl (fun fl => P fl ∨ Q fl) abs := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hpq, hpre⟩ := mergeFieldXSpec_pre_iff.mp hpre
  rcases hpq with hp | hq
  · exact subroutine_ok.mono_outcome hP x R s0 hpc hrun
      (mergeFieldXSpec_pre_iff.mpr ⟨hp, hpre⟩) hal fun _ hout => hout
  · exact subroutine_ok.mono_outcome hQ x R s0 hpc hrun
      (mergeFieldXSpec_pre_iff.mpr ⟨hq, hpre⟩) hal fun _ hout => hout

/-- Projects `MergeFieldXGhost` to `MergeFieldGenGhost` on its base `SSG` state. -/
def MergeFieldXGhost.toGen (x : MergeFieldXGhost) (f : GenField) : MergeFieldGenGhost :=
  ⟨x.ss, x.v.base, f, x.bufRef, x.slot, x.ptr, x.tail⟩

/-- Lifts a `MergeFieldGenOk` leaf for `P` to `MergeFieldXOk` on `.base f` fields satisfying `P f`. -/
theorem mergeFieldXBase_ok {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {P : GenField → Prop}
    (hP : MergeFieldGenOk C ctl P abs) :
    MergeFieldXOk C ctl (fun fl => ∃ f, fl = .base f ∧ P f) abs := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  rcases x with ⟨ss, ⟨v, e⟩, fld, bufRef, slot, ptr, tail⟩
  simp only [mergeFieldXSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨h0, h1, h2, h3, h4, ⟨f, rfl, hf⟩, hok, ⟨he, hfr⟩, hlen, hfz, hsym⟩, hm⟩ := hpre
  dsimp only at he
  subst he
  rw [prostSSGXAt_empty] at hm
  have hpre' : s0.mem ⊨ (mergeFieldGenSpec P).pre ⟨ss, v, f, bufRef, slot, ptr, tail⟩ s0 ∗ R := by
    simp only [mergeFieldGenSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨h0, h1, h2, h3, h4, hf, hok, hfr, hlen, hfz, hsym⟩, hm⟩
  refine subroutine_ok.mono_outcome hP _ R s0 hpc hrun hpre' hal fun _ hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · left
    refine ⟨hret, hcc, ?_⟩
    have happ : (SSGX.apply ⟨v, ExtraG.empty⟩ (GenFieldX.base f)) = ⟨v.apply f, ExtraG.empty⟩ :=
      rfl
    simp only [mergeFieldXSpec, happ, prostSSGXAt_empty, GenFieldX.payload]
    simpa only [mergeFieldGenSpec] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- Combines all `DeserializeGeneral` leaves into `MergeFieldXOk` over arbitrary `.base` fields. -/
theorem mergeFieldXBaseAll_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (hCh : ChainMergeGenOk C ctl abs) :
    MergeFieldXOk C ctl (fun fl => ∃ f, fl = .base f) abs :=
  mergeFieldXOk_of_imp (mergeFieldXBase_ok (mergeFieldGen_ok C ctl hC hCh))
    (fun _ ⟨f, hf⟩ => ⟨f, hf, trivial⟩)

end CryptoVerification.E2E.Record.L1GX
