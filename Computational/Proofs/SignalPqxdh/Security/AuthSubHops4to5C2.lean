/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C1
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhB
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import VCVio.EvalDist.Monad.Basic

/-!
# `INT-CTXT` Cutoff Step and Primitive Query Bounds

Proves the adjacent step bound for `authIntCutoffExp` and primitive-oracle query bounds
(`PrimBounded`) for the `Auth` `INT-CTXT` reduction helpers.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

theorem drKey_step_bind_congr {S : Setup} {α₁ α₂ β : Type}
    (c : Bool) (m : Option (IdealAuthSession S))
    (ro : List (Bytes × DRKey)) (f : ProbComp (DRKey × List (Bytes × DRKey)))
    (jp₁ : DRKey × List (Bytes × DRKey) → ProbComp α₁)
    (jp₂ : DRKey × List (Bytes × DRKey) → ProbComp α₂)
    (k₁ : α₁ → ProbComp β) (k₂ : α₂ → ProbComp β)
    (hjp : ∀ a, (jp₁ a >>= k₁) = (jp₂ a >>= k₂)) :
    ((if c then
        match m with
        | some s => pure (s.drKey, ro) >>= jp₁
        | none => sampleDRKey96 >>= fun dk => pure (dk, ro) >>= jp₁
      else f >>= jp₁) >>= k₁) =
    ((if c then
        match m with
        | some s => pure (s.drKey, ro) >>= jp₂
        | none => sampleDRKey96 >>= fun dk => pure (dk, ro) >>= jp₂
      else f >>= jp₂) >>= k₂) := by
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]; congr 1; funext a; exact hjp a
  · cases m with
    | none => simp only [↓reduceIte, bind_assoc, pure_bind]; congr 1; funext dk; exact hjp (dk, ro)
    | some s => simp only [↓reduceIte, pure_bind]; exact hjp (s.drKey, ro)

theorem rk_ck_step_bind_congr {S : Setup} {α α₁ α₂ β : Type}
    (c : Bool) (m : Option (IdealAuthSession S)) (sameEph : Bool)
    (sVal : IdealAuthSession S → α) (wrap : Bytes → Bytes → α) (f : ProbComp α)
    (jp₁ : α → ProbComp α₁) (jp₂ : α → ProbComp α₂)
    (k₁ : α₁ → ProbComp β) (k₂ : α₂ → ProbComp β)
    (hjp : ∀ a, (jp₁ a >>= k₁) = (jp₂ a >>= k₂)) :
    ((if c then
        match m with
        | some s =>
          if sameEph then pure (sVal s) >>= jp₁
          else sampleBytes32 >>= fun r => sampleBytes32 >>= fun d => pure (wrap r d) >>= jp₁
        | none => sampleBytes32 >>= fun r => sampleBytes32 >>= fun d => pure (wrap r d) >>= jp₁
      else f >>= jp₁) >>= k₁) =
    ((if c then
        match m with
        | some s =>
          if sameEph then pure (sVal s) >>= jp₂
          else sampleBytes32 >>= fun r => sampleBytes32 >>= fun d => pure (wrap r d) >>= jp₂
        | none => sampleBytes32 >>= fun r => sampleBytes32 >>= fun d => pure (wrap r d) >>= jp₂
      else f >>= jp₂) >>= k₂) := by
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]; congr 1; funext a; exact hjp a
  · cases m with
    | none =>
      simp only [↓reduceIte, bind_assoc, pure_bind]
      congr 1
      funext r
      congr 1
      funext d
      exact hjp (wrap r d)
    | some s =>
      cases sameEph
      · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        congr 1; funext r; congr 1; funext d; exact hjp (wrap r d)
      · simp only [↓reduceIte, pure_bind]; exact hjp (sVal s)

theorem msgKeys_step_bind_congr {S : Setup} {α₁ α₂ β : Type}
    (c : Bool) (m : Option (IdealAuthSession S)) (sameMsgKeys sameEph : Bool)
    (spqrSalt? : Option Bytes) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S) (f : MessageKeys)
    (jp₁ : MessageKeys × AuthMkSaltCache S → ProbComp α₁)
    (jp₂ : MessageKeys × AuthMkSaltCache S → ProbComp α₂)
    (k₁ : α₁ → ProbComp β) (k₂ : α₂ → ProbComp β)
    (hjp : ∀ a, (jp₁ a >>= k₁) = (jp₂ a >>= k₂)) :
    ((if c then
        match m with
        | some s =>
          if sameMsgKeys then pure (s.deriveMessageKeys, mkSaltCache) >>= jp₁
          else if sameEph then
            match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
            | some (_, (_, mk)) => pure (mk, mkSaltCache) >>= jp₁
            | none => sampleMessageKeys80 >>= fun mk =>
                pure (mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache) >>= jp₁
          else sampleMessageKeys80 >>= fun mk => pure (mk, mkSaltCache) >>= jp₁
        | none => sampleMessageKeys80 >>= fun mk => pure (mk, mkSaltCache) >>= jp₁
      else pure (f, mkSaltCache) >>= jp₁) >>= k₁) =
    ((if c then
        match m with
        | some s =>
          if sameMsgKeys then pure (s.deriveMessageKeys, mkSaltCache) >>= jp₂
          else if sameEph then
            match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
            | some (_, (_, mk)) => pure (mk, mkSaltCache) >>= jp₂
            | none => sampleMessageKeys80 >>= fun mk =>
                pure (mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache) >>= jp₂
          else sampleMessageKeys80 >>= fun mk => pure (mk, mkSaltCache) >>= jp₂
        | none => sampleMessageKeys80 >>= fun mk => pure (mk, mkSaltCache) >>= jp₂
      else pure (f, mkSaltCache) >>= jp₂) >>= k₂) := by
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]; exact hjp (f, mkSaltCache)
  · cases m with
    | none =>
      simp only [↓reduceIte, bind_assoc, pure_bind]
      congr 1
      funext mk
      exact hjp (mk, mkSaltCache)
    | some s =>
      cases sameMsgKeys
      · cases sameEph
        · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
          congr 1; funext mk; exact hjp (mk, mkSaltCache)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rcases hFind : mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
            _ | ⟨_, _,
              mk⟩ <;>
            simp only [hFind]
          · simp only [bind_assoc, pure_bind]; congr 1; funext mk; exact hjp _
          · simp only [pure_bind]; exact hjp (mk, mkSaltCache)
      · simp only [↓reduceIte, pure_bind]; exact hjp (s.deriveMessageKeys, mkSaltCache)

theorem RelProbUpToBad.bind_same_of_support {β α : Type} {R : α → α → Prop} {bad : α → Bool}
    (mx : ProbComp β) {f5 f6 : β → ProbComp α}
    (h : ∀ b ∈ support mx, RelProbUpToBad R bad (f5 b) (f6 b)) :
    RelProbUpToBad R bad (mx >>= f5) (mx >>= f6) := by
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · rw [probExpect_bind, probExpect_bind]
    exact probExpect_mono_of_support mx _ _ (fun b hb => (h b hb).1 w5 w6 hw5 hw6 hle)
  · rw [probExpect_bind, probExpect_bind]
    exact probExpect_mono_of_support mx _ _ (fun b hb => (h b hb).2 w6 w5 hw6 hle)

theorem relProbUpToBad_drKey_step {S : Setup} {α : Type}
    {R : α → α → Prop} {bad : α → Bool}
    (c : Bool) (m : Option (IdealAuthSession S))
    (ro : List (Bytes × DRKey)) (f : ProbComp (DRKey × List (Bytes × DRKey)))
    (jp5 jp6 : DRKey × List (Bytes × DRKey) → ProbComp α)
    (hjp : ∀ a, RelProbUpToBad R bad (jp5 a) (jp6 a)) :
    RelProbUpToBad R bad
      (if c then
        match m with
        | some s => pure (s.drKey, ro) >>= jp5
        | none => sampleDRKey96 >>= fun dk => pure (dk, ro) >>= jp5
      else f >>= jp5)
      (if c then
        match m with
        | some s => pure (s.drKey, ro) >>= jp6
        | none => sampleDRKey96 >>= fun dk => pure (dk, ro) >>= jp6
      else f >>= jp6) := by
  cases c
  · exact RelProbUpToBad.bind_same f hjp
  · cases m with
    | none =>
      simp only [↓reduceIte, pure_bind]
      exact RelProbUpToBad.bind_same sampleDRKey96 (fun dk => hjp (dk, ro))
    | some s => simp only [↓reduceIte, pure_bind]; exact hjp (s.drKey, ro)

theorem relProbUpToBad_rk_ck_step {S : Setup} {α β : Type}
    {R : β → β → Prop} {bad : β → Bool}
    (c : Bool) (m : Option (IdealAuthSession S)) (sameEph : Bool)
    (sVal : IdealAuthSession S → α) (wrap : Bytes → Bytes → α) (f : ProbComp α)
    (jp5 jp6 : α → ProbComp β) (hjp : ∀ a, RelProbUpToBad R bad (jp5 a) (jp6 a)) :
    RelProbUpToBad R bad
      (if c then
        match m with
        | some s =>
          if sameEph then pure (sVal s) >>= jp5
          else sampleBytes32 >>= fun r => sampleBytes32 >>= fun d => pure (wrap r d) >>= jp5
        | none => sampleBytes32 >>= fun r => sampleBytes32 >>= fun d => pure (wrap r d) >>= jp5
      else f >>= jp5)
      (if c then
        match m with
        | some s =>
          if sameEph then pure (sVal s) >>= jp6
          else sampleBytes32 >>= fun r => sampleBytes32 >>= fun d => pure (wrap r d) >>= jp6
        | none => sampleBytes32 >>= fun r => sampleBytes32 >>= fun d => pure (wrap r d) >>= jp6
      else f >>= jp6) := by
  cases c
  · exact RelProbUpToBad.bind_same f hjp
  · cases m with
    | none =>
      simp only [↓reduceIte, pure_bind]
      exact RelProbUpToBad.bind_same sampleBytes32 (fun r =>
        RelProbUpToBad.bind_same sampleBytes32 (fun d => hjp (wrap r d)))
    | some s =>
      cases sameEph
      · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
        exact RelProbUpToBad.bind_same sampleBytes32 (fun r =>
          RelProbUpToBad.bind_same sampleBytes32 (fun d => hjp (wrap r d)))
      · simp only [↓reduceIte, pure_bind]; exact hjp (sVal s)

theorem relProbUpToBad_msgKeys_step {S : Setup} {β : Type}
    {R : β → β → Prop} {bad : β → Bool}
    (c : Bool) (m : Option (IdealAuthSession S)) (sameMsgKeys sameEph : Bool)
    (spqrSalt? : Option Bytes) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (f : MessageKeys) (jp5 jp6 : MessageKeys × AuthMkSaltCache S → ProbComp β) :
    (∀ a : MessageKeys × AuthMkSaltCache S,
      (∀ s, m = some s → c = true → sameMsgKeys = true → a.1 = s.deriveMessageKeys) →
      RelProbUpToBad R bad (jp5 a) (jp6 a)) →
    RelProbUpToBad R bad
      (if c then
        match m with
        | some s =>
          if sameMsgKeys then pure (s.deriveMessageKeys, mkSaltCache) >>= jp5
          else if sameEph then
            match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
            | some (_, (_, mk)) => pure (mk, mkSaltCache) >>= jp5
            | none => sampleMessageKeys80 >>= fun mk =>
                pure (mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache) >>= jp5
          else sampleMessageKeys80 >>= fun mk => pure (mk, mkSaltCache) >>= jp5
        | none => sampleMessageKeys80 >>= fun mk => pure (mk, mkSaltCache) >>= jp5
      else pure (f, mkSaltCache) >>= jp5)
      (if c then
        match m with
        | some s =>
          if sameMsgKeys then pure (s.deriveMessageKeys, mkSaltCache) >>= jp6
          else if sameEph then
            match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
            | some (_, (_, mk)) => pure (mk, mkSaltCache) >>= jp6
            | none => sampleMessageKeys80 >>= fun mk =>
                pure (mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache) >>= jp6
          else sampleMessageKeys80 >>= fun mk => pure (mk, mkSaltCache) >>= jp6
        | none => sampleMessageKeys80 >>= fun mk => pure (mk, mkSaltCache) >>= jp6
      else pure (f, mkSaltCache) >>= jp6) := by
  intro hjp
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
    exact hjp (f, mkSaltCache) (fun _ _ hc _ => by cases hc)
  · cases m with
    | none =>
      simp only [↓reduceIte, pure_bind]
      exact RelProbUpToBad.bind_same sampleMessageKeys80 (fun mk =>
        hjp (mk, mkSaltCache) (fun _ hm _ _ => by cases hm))
    | some s =>
      cases sameMsgKeys
      · cases sameEph
        · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
          exact RelProbUpToBad.bind_same sampleMessageKeys80 (fun mk =>
            hjp (mk, mkSaltCache) (fun _ _ _ hsm => by cases hsm))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rcases hFind : mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
            _ | ⟨_, _,
              mk⟩ <;>
            simp only [hFind]
          · simp only [pure_bind]
            exact RelProbUpToBad.bind_same sampleMessageKeys80 (fun mk =>
              hjp _ (fun _ _ _ hsm => by cases hsm))
          · simp only [pure_bind]
            exact hjp (mk, mkSaltCache) (fun _ _ _ hsm => by cases hsm)
      · simp only [↓reduceIte, pure_bind]
        exact hjp (s.deriveMessageKeys, mkSaltCache) (fun s' hs' _ _ => by cases hs'; rfl)

theorem evalDist_outer_bind_abs_sub_le' {β α : Type} (mx : ProbComp β)
    (m5 m6 : β → ProbComp α) (bad : β → α → Bool) (fin5 fin6 : β → α → ProbComp Bool)
    (hle : ∀ b,
      𝒟[m5 b >>= fin5 b] {true} ≤
        𝒟[m6 b >>= fin6 b] {true} + 𝒟[m6 b >>= fun x => pure (bad b x)] {true} ∧
      𝒟[m6 b >>= fin6 b] {true} ≤
        𝒟[m5 b >>= fin5 b] {true} + 𝒟[m6 b >>= fun x => pure (bad b x)] {true}) :
    |(𝒟[mx >>= fun b => m5 b >>= fin5 b] {true}).toReal -
     (𝒟[mx >>= fun b => m6 b >>= fin6 b] {true}).toReal| ≤
      (𝒟[mx >>= fun b => m6 b >>= fun x => pure (bad b x)] {true}).toReal := by
  let _ : MeasurableSpace β := ⊤
  have _ : DiscreteMeasurableSpace β := ⟨fun _ => trivial⟩
  have hEq : ∀ (f : β → ProbComp Bool),
      𝒟[mx >>= f] {true} = probExpect mx (fun b => 𝒟[f b] {true}) := fun f => by
    unfold probExpect
    rw [evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
            Measurable.of_discrete.aemeasurable]
  have h1 : 𝒟[mx >>= fun b => m5 b >>= fin5 b] {true} ≤
      𝒟[mx >>= fun b => m6 b >>= fin6 b] {true} + 𝒟[mx >>= fun b => m6 b >>=
          fun x => pure (bad b x)] {true} := by
    rw [hEq, hEq, hEq]; exact probExpect_add_le mx _ _ _ (fun b => (hle b).1)
  have h2 : 𝒟[mx >>= fun b => m6 b >>= fin6 b] {true} ≤
      𝒟[mx >>= fun b => m5 b >>= fin5 b] {true} + 𝒟[mx >>= fun b => m6 b >>=
          fun x => pure (bad b x)] {true} := by
    rw [hEq, hEq, hEq]; exact probExpect_add_le mx _ _ _ (fun b => (hle b).2)
  have hfin5 : 𝒟[mx >>= fun b => m5 b >>= fin5 b] {true} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top MeasureTheory.prob_le_one
  have hfin6 : 𝒟[mx >>= fun b => m6 b >>= fin6 b] {true} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top MeasureTheory.prob_le_one
  have hfinBad : 𝒟[mx >>= fun b => m6 b >>= fun x => pure (bad b x)] {true} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top MeasureTheory.prob_le_one
  have h1r := (ENNReal.toReal_le_toReal hfin5 (ENNReal.add_ne_top.mpr ⟨hfin6, hfinBad⟩)).mpr h1
  have h2r := (ENNReal.toReal_le_toReal hfin6 (ENNReal.add_ne_top.mpr ⟨hfin5, hfinBad⟩)).mpr h2
  rw [ENNReal.toReal_add hfin6 hfinBad] at h1r; rw [ENNReal.toReal_add hfin5 hfinBad] at h2r
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem primBounded_prepAuthIntSendPrim (S : Setup) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridStateFixed S) :
    PrimBounded (prepAuthIntSendPrim S sid u bundle m0 m1 hst) (S.N_dh * 14 + 16) := by
  unfold prepAuthIntSendPrim
  refine primBounded_ite primBounded_pure' (primBounded_ite primBounded_pure' ?_)
  cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => exact primBounded_pure'
  | some up =>
    rcases up with ⟨_, uEntry⟩; dsimp only
    refine primBounded_bind_le (S.N_dh * 12 + 16)
        (primBounded_findHonestPrincipalPrim S _ bundle.ikB) (fun _ => ?_)
    refine primBounded_ite primBounded_pure' ?_
    refine primBounded_bind_le (S.N_dh * 6 + 13) (primBounded_koskBundleOkPrim S _ _ _ _ bundle)
        (fun _ => ?_)
    refine primBounded_ite primBounded_pure' ?_
    refine primBounded_bind_le (m := 0) (S.N_dh * 6 + 13) (primBounded_embedUnif sampleScalar32 0)
        (fun _ =>
      primBounded_bind_le (m := 0) (S.N_dh * 6 + 13) (primBounded_embedUnif sampleCoins32 0)
          (fun _ =>
      primBounded_bind_le (m := 0) (S.N_dh * 6 + 13) (primBounded_embedUnif sampleScalar32 0)
          (fun _ =>
      primBounded_bind_le (m := 0) (S.N_dh * 6 + 13) (primBounded_embedUnif sampleCoins32 0)
          (fun _ =>
      primBounded_bind_le (S.N_dh * 6 + 12) (primBounded_primQ _) (fun _ =>
      primBounded_bind_le (S.N_dh * 6 + 11) (primBounded_primQ _) (fun _ =>
      primBounded_ite primBounded_pure'
        (primBounded_bind_le (S.N_dh * 6 + 10) (primBounded_primQ _) (fun kemRes => ?_))))))))
    cases kemRes with
    | none => exact primBounded_pure'
    | some sc =>
      rcases sc with ⟨ss, kemCt⟩
      refine primBounded_bind_le (S.N_dh * 6 + 9) (primBounded_primQ _) (fun _ =>
        primBounded_bind_le (S.N_dh * 2 + 9)
            (primBounded_checkBundleProvenanceExactPrim S _ _ _ bundle) (fun ⟨_, _, _⟩ =>
        primBounded_bind_le 9 (primBounded_checkBundleSpkHonIdealPeerPrim S _ _ bundle) (fun _ =>
        primBounded_bind_le 8 (primBounded_primQ _) (fun _ =>
        primBounded_bind_le 7 (primBounded_primQ _) (fun _ =>
        primBounded_bind_le 6 (primBounded_primQ _) (fun _ =>
        primBounded_bind_le 5 (primBounded_primQ _) (fun _ =>
        primBounded_bind_le 4 (primBounded_primQ _) (fun _ =>
        primBounded_bind_le 3 (primBounded_primQ _) (fun _ => ?_)))))))))
      refine primBounded_bind_step 0 3 ?_ (fun _ => ?_)
      · refine primBounded_ite ?_ (primBounded_embedUnif _ 0)
        exact primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleDRKey96 0)
            (fun _ => primBounded_pure')
      refine primBounded_bind_step 0 3 ?_ (fun _ => ?_)
      · refine primBounded_ite ?_ (primBounded_embedUnif _ 0)
        refine primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleBytes32 0) (fun _ => ?_)
        exact primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleBytes32 0)
            (fun _ => primBounded_pure')
      refine primBounded_bind_step 2 1 ?_ (fun _ => ?_)
      · refine primBounded_ite ?_ ?_
        · refine primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleBytes32 0)
            (fun _ => ?_)
          exact primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleBytes32 0)
              (fun _ => primBounded_pure')
        · refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
          exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
      refine primBounded_bind_le 0 (primBounded_primQ _) (fun spqrRes => ?_)
      cases spqrRes with
      | none => exact primBounded_pure'
      | some spqrTriple => rcases spqrTriple with ⟨_, _, _⟩; exact primBounded_pure'

theorem primBounded_finishPrepareAuthRecvPrim (S : Setup) (kVal jVal : Nat)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkSk? opkPk? : Option Bytes)
    (mkFinish : List (Nat × UInt32 × UInt32 × Bytes) → Bool → AuthHybridState S →
      Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
        List ((Bytes × Bytes) × (Bytes × Bytes))) → AuthResponse × AuthHybridState S)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    PrimBounded (finishPrepareAuthRecvPrim S kVal jVal kEntry bEntry opkSk? opkPk? mkFinish msg hst)
      (S.N_dh * 2 + 7) := by
  unfold finishPrepareAuthRecvPrim
  refine primBounded_bind_le (S.N_dh * 2 + 6) (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le (S.N_dh * 2 + 5) (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_ite primBounded_pure' ?_
  refine primBounded_bind_le (S.N_dh * 2 + 4) (primBounded_primQ _) (fun ss? => ?_)
  cases ss? with
  | none => exact primBounded_pure'
  | some ss =>
    dsimp only
    have hDh4 : PrimBounded (match opkSk? with
        | some opkSk => do let d ← primQ (.x25519 opkSk msg.hdr.ekAPk); pure (some d)
        | none => pure none) 1 := by
      cases opkSk? <;>
        [exact primBounded_pure'; exact primBounded_bind_le 0 (primBounded_primQ _)
            (fun _ => primBounded_pure')]
    exact primBounded_bind_le (S.N_dh * 2 + 3) (primBounded_primQ _) (fun _ =>
      primBounded_bind_le (S.N_dh * 2 + 2) (primBounded_primQ _) (fun _ =>
      primBounded_bind_le (S.N_dh * 2 + 1) (primBounded_primQ _) (fun _ =>
      primBounded_bind_le (S.N_dh * 2) hDh4 (fun _ =>
      primBounded_bind_le 0 (primBounded_findHonestPrincipalPrim S _ msg.hdr.ikAPk)
          (fun _ => primBounded_pure')))))
theorem primBounded_prepareAuthRecvOPKPrim (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    PrimBounded (prepareAuthRecvOPKPrim S k j o msg hst) (S.N_dh * 4 + 8) := by
  unfold prepareAuthRecvOPKPrim
  refine primBounded_ite primBounded_pure' (primBounded_ite primBounded_pure' ?_)
  refine primBounded_bind_le (S.N_dh * 2 + 7) (primBounded_koskSenderOkPrim S _ _ msg.hdr.ikAPk)
      (fun _ => ?_)
  refine primBounded_ite primBounded_pure' ?_
  split
  · exact primBounded_ite primBounded_pure' (primBounded_finishPrepareAuthRecvPrim S k.val j.val _ _
      _ _ _ msg hst)
  · exact primBounded_pure'
theorem primBounded_prepareAuthRecvNoOPKPrim (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    PrimBounded (prepareAuthRecvNoOPKPrim S k j l msg hst) (S.N_dh * 4 + 8) := by
  unfold prepareAuthRecvNoOPKPrim
  refine primBounded_ite primBounded_pure' (primBounded_ite primBounded_pure' ?_)
  refine primBounded_bind_le (S.N_dh * 2 + 7) (primBounded_koskSenderOkPrim S _ _ msg.hdr.ikAPk)
      (fun _ => ?_)
  refine primBounded_ite primBounded_pure' ?_
  split
  · exact primBounded_finishPrepareAuthRecvPrim S k.val j.val _ _ _ _ _ msg hst
  · exact primBounded_pure'

theorem primBounded_prepAuthIntRecvSchedPrim (S : Setup) (hstDec : AuthHybridState S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (opkPk? : Option Bytes)
    (secrets : Bytes) (msg : PreKeyMsg) :
    PrimBounded (prepAuthIntRecvSchedPrim S hstDec kEntry bEntry opkPk? secrets msg)
      (S.N_dh * 2 + S.N_sess_tot * 10 + 6) := by
  unfold prepAuthIntRecvSchedPrim
  refine primBounded_bind_le (S.N_sess_tot * 10 + 6)
    (primBounded_findHonestPrincipalPrim S _ msg.hdr.ikAPk) (fun _ => ?_)
  refine primBounded_bind_le 6
    (primBounded_findMPrim_take _ 10 S.N_sess_tot hstDec.idealSessions
      (fun s => primBounded_matchIdealAuthHandshakePrim kEntry.ikAPk bEntry.spkPk opkPk?
          bEntry.pqspkPk msg.hdr s))
    (fun matchedSess? => ?_)
  refine primBounded_bind_step 0 6 ?_ (fun _ => ?_)
  · refine primBounded_ite ?_ (primBounded_embedUnif _ 0)
    cases matchedSess? with
    | some _ => exact primBounded_pure'
    | none =>
      exact primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleDRKey96 0)
          (fun _ => primBounded_pure')
  refine primBounded_bind_le 5 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_step 2 3 ?_ (fun _ => ?_)
  · cases matchedSess? with
    | none => exact primBounded_pure'
    | some _ =>
      refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  refine primBounded_bind_step 0 3 ?_ (fun _ => ?_)
  · refine primBounded_ite ?_ (primBounded_embedUnif _ 0)
    cases matchedSess? with
    | some _ =>
      refine primBounded_ite primBounded_pure' ?_
      refine primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleBytes32 0) (fun _ => ?_)
      exact primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleBytes32 0)
          (fun _ => primBounded_pure')
    | none =>
      refine primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleBytes32 0) (fun _ => ?_)
      exact primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleBytes32 0)
          (fun _ => primBounded_pure')
  refine primBounded_bind_step 2 1 ?_ (fun _ => ?_)
  · refine primBounded_ite ?_ ?_
    · cases matchedSess? with
      | some _ =>
        refine primBounded_ite primBounded_pure' ?_
        refine primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleBytes32 0) (fun _ => ?_)
        exact primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleBytes32 0)
            (fun _ => primBounded_pure')
      | none =>
        refine primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleBytes32 0) (fun _ => ?_)
        exact primBounded_bind_le (m := 0) 0 (primBounded_embedUnif sampleBytes32 0)
            (fun _ => primBounded_pure')
    · refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  refine primBounded_bind_le 0 (primBounded_primQ _) (fun spqrRes => ?_)
  cases spqrRes with
  | none => exact primBounded_pure'
  | some spqrPair => rcases spqrPair with ⟨_, _⟩; exact primBounded_pure'

end SignalPqxdh.Security
