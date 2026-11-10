/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.BlankedPrivRed
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.PubDefs
public import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma18
import Computational.Proofs.CryptoGames.SM.Theorem1
import VCVio.CryptoFoundations.SecExp.Measure
public import Computational.Proofs.CryptoGames.FSAEAD.PubProofDefs

/-!
# Lemma 18 with a blanking map

**Checked by Lean.** Ports ACD19 Lemma 18 (privacy hybrid `H3,i`) to a blanking map
`blank : Msg → Msg` so `ThmB.privRedB` preserves public message parts (DEV-LS13).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory
open CryptoGames.SM CryptoGames.SM.Thm1 CryptoGames.SM.Thm1.L18

namespace CryptoGames.LibsignalSM.Proofs.BlankLemma18

variable {Key St Msg Coins C Pub : Type}

/-! ### Blanked H3 hybrid game -/

section Defs

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)

def challMsgB (i : ℕ) (blank : Msg → Msg) : ℕ → Option (Msg → Msg) :=
  fun t => if t < i then some blank else none

lemma challMsgB_zero (blank : Msg → Msg) :
    challMsgB 0 blank = fun _ => none := by
  funext t
  simp [challMsgB]

def challImplB (challMsg : ℕ → Option (Msg → Msg)) [SampleableType Coins] :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) ProbComp) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if s.win then return none
    let (coins, bad) ← (samIfNec r : ProbComp _)
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !((Config.h2 : Config Msg).challAllowedIn (s₁.epoch P)) then return none
      let m := ((challMsg (s₁.epoch P)).map (· (if s.b then m₁ else m₀))).getD
        (if s.b then m₁ else m₀)
      let out := sm.send (s₁.st P) m coins
      set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
      return some out.2

def oracleImplB (challMsg : ℕ → Option (Msg → Msg))
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] :
    QueryImpl (spec St Msg Coins C) (StateT (GameState St Msg C) ProbComp) :=
  transmitImpl sm Δ qep + challImplB sm Δ qep challMsg + deliverImpl sm Config.h2
    + injectImpl sm Δ qep Config.h2 + (corrImpl : QueryImpl _ (StateT (GameState St Msg C) ProbComp))

abbrev runImplB [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (challMsg : ℕ → Option (Msg → Msg)) :
    QueryImpl (unifSpec + spec St Msg Coins C) (StateT (GameState St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (GameState St Msg C) ProbComp) + oracleImplB sm Δ qep challMsg

def runB [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (challMsg : ℕ → Option (Msg → Msg)) (b : Bool) (A : Adversary St Msg Coins C) :
    ProbComp (Bool × GameState St Msg C) := do
  let k ← $ᵗ Key
  (simulateQ (runImplB sm Δ qep challMsg) A).run (initState sm k b)

def gameB [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (challMsg : ℕ → Option (Msg → Msg)) (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', s) ← runB sm Δ qep challMsg b A
  return (b == b' || s.win)

noncomputable def hybridAdvantageB
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (challMsg : ℕ → Option (Msg → Msg)) (A : Adversary St Msg Coins C) : ℝ≥0∞ :=
  𝒟[gameB sm Δ qep challMsg A].boolBias

lemma hybridAdvantageB_zero
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (blank : Msg → Msg) (A : Adversary St Msg Coins C) :
    hybridAdvantageB sm Δ qep (challMsgB 0 blank) A =
      hybridAdvantage sm Δ qep Config.h2 A := by
  rw [challMsgB_zero]
  rfl

end Defs

/-! ### Final hybrid bias -/

section H3BFinal

variable [DecidableEq Msg] [DecidableEq C] [DecidableEq Pub]
  (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) [SampleableType Coins]

lemma runImplB_h3_final_step (pubOf : Msg → Pub) (blank : Msg → Msg)
    (hblank : ∀ m₀ m₁, pubOf m₀ = pubOf m₁ → blank m₀ = blank m₁)
    (t : (unifSpec + spec St Msg Coins C).Domain)
    (ht : ¬ (unequalPubChall (St := St) (Coins := Coins) (C := C) pubOf t = true))
    (s : GameState St Msg C) (hw : s.win = false)
    {β : Type} (k₁ k₂ : (unifSpec + spec St Msg Coins C).Range t → GameState St Msg C → ProbComp β)
    (hk : ∀ u s', s'.win = false → k₁ u s' = k₂ u (withBFalse s')) :
    ((runImplB sm Δ qep (challMsgB (qep + 1) blank) t).run s >>= fun p => k₁ p.1 p.2) =
      ((runImplB sm Δ qep (challMsgB (qep + 1) blank) t).run (withBFalse s) >>=
        fun p => k₂ p.1 p.2) := by
  rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change (StateT.lift (query (spec := unifSpec) n) : StateT _ ProbComp _).run s >>= _ =
      (StateT.lift (query (spec := unifSpec) n) : StateT _ ProbComp _).run (withBFalse s) >>= _
    simp only [stateT_lift_run, bind_assoc, pure_bind]
    exact bind_congr fun u => hk u s hw
  · change (transmitImpl sm Δ qep (P, m, r)).run s >>= _ =
      (transmitImpl sm Δ qep (P, m, r)).run (withBFalse s) >>= _
    unfold transmitImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, withBFalse_win, hw,
      Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, bind_assoc, epMgmt_withBFalse]
    refine bind_congr fun cb => ?_
    cases hep : s.epMgmt Δ qep P cb.2 with
    | none =>
      simp only [Option.map_none, StateT.run_pure, pure_bind]
      exact hk none s hw
    | some s₁ =>
      have hw₁ : s₁.win = false := (epMgmt_win Δ qep hep).trans hw
      simp only [Option.map_some, withBFalse_st, withBFalse_epoch, withBFalse_idx,
        withBFalse_record, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure]
      exact hk _ _ hw₁
  · change (challImplB sm Δ qep (challMsgB (qep + 1) blank) (P, m₀, m₁, r)).run s >>= _ =
      (challImplB sm Δ qep (challMsgB (qep + 1) blank) (P, m₀, m₁, r)).run (withBFalse s) >>= _
    have hpub : pubOf m₀ = pubOf m₁ := by
      unfold unequalPubChall at ht
      by_contra hne
      exact ht (decide_eq_true hne)
    have hbl : blank m₀ = blank m₁ := hblank m₀ m₁ hpub
    unfold challImplB
    simp only [StateT.run_bind, StateT.run_get, pure_bind, withBFalse_win, hw,
      Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, bind_assoc, epMgmt_withBFalse]
    refine bind_congr fun cb => ?_
    cases hep : s.epMgmt Δ qep P cb.2 with
    | none =>
      simp only [Option.map_none, StateT.run_pure, pure_bind]
      exact hk none s hw
    | some s₁ =>
      have hw₁ : s₁.win = false := (epMgmt_win Δ qep hep).trans hw
      have hle : s₁.epoch P ≤ qep := epMgmt_epoch_le Δ qep hep
      simp only [Option.map_some, withBFalse_safeCh, withBFalse_epoch]
      by_cases hch : (!s₁.safeCh Δ P || !((Config.h2 : Config Msg).challAllowedIn (s₁.epoch P))) = true
      · simp only [hch, ↓reduceIte, StateT.run_pure, pure_bind]
        exact hk none s hw
      · have hm : ∀ b_val : Bool,
            (((challMsgB (qep + 1) blank (s₁.epoch P)).map (· (if b_val then m₁ else m₀))).getD
              (if b_val then m₁ else m₀)) = blank m₀ := by
          intro b_val
          have hlt : s₁.epoch P < qep + 1 := by omega
          cases b_val <;> simp [challMsgB, hlt, hbl]
        simp only [hch, hm, withBFalse_st, withBFalse_idx, withBFalse_record]
        exact hk _ _ hw₁
  · change (deliverImpl sm Config.h2 (P, c)).run s >>= _ =
      (deliverImpl sm Config.h2 (P, c)).run (withBFalse s) >>= _
    unfold deliverImpl
    have hdw : (Config.h2 : Config Msg).deliverWin = false := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, withBFalse_win, hw,
      Bool.false_eq_true, ↓reduceIte, withBFalse_inTransit, hdw, Bool.false_and]
    cases s.inTransit P.other c with
    | none =>
      exact hk none s hw
    | some r =>
      simp only [withBFalse_st]
      cases sm.receive (s.st P) c with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact hk (some .rejected) s hw
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          withBFalse_accept, withBFalse_chall]
        exact hk _ _ hw
  · change (injectImpl sm Δ qep Config.h2 (P, c)).run s >>= _ =
      (injectImpl sm Δ qep Config.h2 (P, c)).run (withBFalse s) >>= _
    unfold injectImpl
    have hij : ∀ t', (Config.h2 : Config Msg).injectFull t' = false := fun _ => rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, withBFalse_win, hw, Bool.false_or,
      withBFalse_inTransit, withBFalse_safeInj, withBFalse_st]
    by_cases hreq : ((s.inTransit P.other c).isSome || !s.safeInj Δ) = true
    · simp only [hreq, ↓reduceIte, StateT.run_pure, pure_bind]
      exact hk none s hw
    · simp only [hreq]
      cases sm.receive (s.st P) c with
      | none =>
        exact hk (some .rejected) s hw
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        dsimp only
        by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte]
          exact hk (some .rejected) s hw
        · simp only [hqep, ↓reduceIte, withBFalse_trivial, hij, Bool.false_eq_true]
          by_cases htriv : s.trivial Δ ⟨P.other, t', i'⟩ = true
          · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
              StateT.run_pure, withBFalse_accept]
            exact hk _ _ hw
          · simp only [htriv]
            exact hk (some .rejected) s hw
  · change (corrImpl (St := St) (Msg := Msg) (C := C) P).run s >>= _ =
      (corrImpl (St := St) (Msg := Msg) (C := C) P).run (withBFalse s) >>= _
    unfold corrImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, withBFalse_win, hw, Bool.false_or,
      withBFalse_corrAllowed]
    by_cases hcorr : (!s.corrAllowed P) = true
    · simp only [hcorr, ↓reduceIte, StateT.run_pure, pure_bind]
      exact hk none s hw
    · simp only [hcorr, withBFalse_afterCorr, withBFalse_st]
      exact hk _ _ hw

lemma simulateQ_h3B_final (pubOf : Msg → Pub) (blank : Msg → Msg)
    (hblank : ∀ m₀ m₁, pubOf m₀ = pubOf m₁ → blank m₀ = blank m₁)
    {α β : Type} (oa : AdversaryComp St Msg Coins C α)
    (hoa : oa.IsQueryBoundP
      (fun t => unequalPubChall (St := St) (Coins := Coins) (C := C) pubOf t = true) 0)
    (s : GameState St Msg C) (hw : s.win = false)
    (k₁ k₂ : α → GameState St Msg C → ProbComp β)
    (hk : ∀ a s', s'.win = false → k₁ a s' = k₂ a (withBFalse s')) :
    ((simulateQ (runImplB sm Δ qep (challMsgB (qep + 1) blank)) oa).run s >>= fun p => k₁ p.1 p.2) =
      ((simulateQ (runImplB sm Δ qep (challMsgB (qep + 1) blank)) oa).run (withBFalse s) >>=
        fun p => k₂ p.1 p.2) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hk a s hw
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ (unequalPubChall (St := St) (Coins := Coins) (C := C) pubOf t = true) := by
      rcases hoa.1 with h | h
      · exact h
      · omega
    have hmx : ∀ u, (mx u).IsQueryBoundP
        (fun t => unequalPubChall (St := St) (Coins := Coins) (C := C) pubOf t = true) 0 := by
      intro u
      have hu := hoa.2 u
      simpa using hu
    simp only [simulateQ_query_bind, StateT.run_bind, bind_assoc]
    exact runImplB_h3_final_step sm Δ qep pubOf blank hblank t ht s hw
      (fun u s' => (simulateQ (runImplB sm Δ qep (challMsgB (qep + 1) blank)) (mx u)).run s' >>=
        fun p => k₁ p.1 p.2)
      (fun u s' => (simulateQ (runImplB sm Δ qep (challMsgB (qep + 1) blank)) (mx u)).run s' >>=
        fun p => k₂ p.1 p.2)
      (fun u s' hs' => ih u (hmx u) s' hs')

theorem h3B_final_proof [SampleableType Key] (pubOf : Msg → Pub) (blank : Msg → Msg)
    (hblank : ∀ m₀ m₁, pubOf m₀ = pubOf m₁ → blank m₀ = blank m₁)
    (A : Adversary St Msg Coins C) (heq : EqualPubChalls pubOf A) :
    hybridAdvantageB sm Δ qep (challMsgB (qep + 1) blank) A = 0 := by
  let real : ProbComp Bool := do
    let (b', _) ← runB sm Δ qep (challMsgB (qep + 1) blank) false A
    return b'
  rw [← Measure.boolDist_self 𝒟[real],
    ← evalDist_boolBias_bind_uniformBool real real]
  unfold hybridAdvantageB gameB
  congr 2
  refine bind_congr fun b => ?_
  have hstep : (runB sm Δ qep (challMsgB (qep + 1) blank) b A >>=
      fun (b', s') => pure (b == b' || s'.win)) =
      (real >>= fun z => pure (b == z)) := by
    unfold real runB
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun k => ?_
    exact simulateQ_h3B_final sm Δ qep pubOf blank hblank A heq (initState sm k b) rfl
      (fun b' s' => pure (b == b' || s'.win))
      (fun b' _ => pure (b == b'))
      (fun b' s' hw => by simp [hw])
  cases b <;> exact hstep

end H3BFinal

/-! ### Relational equivalence for `privRedB` -/

section SimRelB

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)

def challMsgHybB (i : ℕ) (blank : Msg → Msg) (b_priv : Bool) : ℕ → Option (Msg → Msg) :=
  if b_priv then challMsgB i blank else challMsgB (i + 1) blank

lemma challMsgHybB_eq (i : ℕ) (blank : Msg → Msg) (b_priv : Bool) {t : ℕ} (hm : t = i) (mb : Msg) :
    (((challMsgHybB i blank b_priv t).map (· mb)).getD mb) =
      (if b_priv then mb else blank mb) := by
  subst hm
  cases b_priv <;> simp [challMsgHybB, challMsgB]

lemma challMsgHybB_ne (i : ℕ) (blank : Msg → Msg) (b_priv : Bool) {t : ℕ} (hne : t ≠ i) (mb : Msg) :
    (((challMsgHybB i blank b_priv t).map (· mb)).getD mb) =
      (((challMsgB i blank t).map (· mb)).getD mb) := by
  have hiff : (t < i + 1) ↔ (t < i) := by omega
  cases b_priv <;> simp [challMsgHybB, challMsgB, hiff]

variable [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]

lemma simStep_privRedB (i : ℕ) (blank : Msg → Msg) (b_priv : Bool)
    (t : (unifSpec + spec St Msg Coins C).Domain)
    (s : GameState St Msg C) (m : Mirror Msg C) (h : GameState St Msg C)
    (hr : SimRel i b_priv s m h)
    (k₁ : (unifSpec + spec St Msg Coins C).Range t → Mirror Msg C → GameState St Msg C → ProbComp Bool)
    (k₂ : (unifSpec + spec St Msg Coins C).Range t → GameState St Msg C → ProbComp Bool)
    (hk : ∀ u s' m' h', SimRel i b_priv s' m' h' → 𝒟[k₁ u m' s'] = 𝒟[k₂ u h']) :
    𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((ThmB.simImpl (St := St) (Coins := Coins) Δ qep (challMsgB i blank) (some (i, blank)) t).run m)).run s) >>=
        fun p => k₁ p.1.1 p.1.2 p.2] =
      𝒟[((runImplB sm Δ qep (challMsgHybB i blank b_priv) t).run h) >>= fun p => k₂ p.1 p.2] := by
  rcases t with n | ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  ·
    change 𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((ThmB.simCoins (St := St) (Msg := Msg) (Coins := Coins) (C := C) n).run m)).run s) >>= _] =
      𝒟[((StateT.lift (query (spec := unifSpec) n) : StateT _ ProbComp _).run h) >>= _]
    unfold ThmB.simCoins
    simp only [stateT_lift_run, query_eq_liftM, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, pure_bind, bind_assoc]
    change 𝒟[((StateT.lift (query (spec := unifSpec) n) : StateT _ ProbComp _).run s) >>= _] = _
    simp only [stateT_lift_run, bind_assoc, pure_bind]
    exact evalDist_bind_congr _ _ _ fun u => hk u s m h hr
  ·
    change 𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((ThmB.simTransmit (St := St) Δ qep (P, msg, r)).run m)).run s) >>= _] =
      𝒟[((transmitImpl sm Δ qep (P, msg, r)).run h) >>= _]
    unfold ThmB.simTransmit transmitQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc,
      query_eq_liftM, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    change 𝒟[((transmitImpl sm Δ qep (P, msg, r)).run s) >>=
      fun p => ((simulateQ (runImpl sm Δ qep (Config.priv i)) _).run p.2) >>= _] = _
    unfold transmitImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_s, hr.win_h,
      Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, L18.monadLift_self, bind_assoc]
    conv_lhs => rw [samIfNec_bind r]
    conv_rhs => rw [samIfNec_bind r]
    dsimp only
    refine evalDist_bind_congr _ _ _ fun cb => ?_
    cases hep_h : h.epMgmt Δ qep P r.isSome with
    | none =>
      rcases hr.epMgmt_none Δ qep P r.isSome hep_h with ⟨hep_s, hep_m⟩
      rw [hep_s, hep_m]
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      exact hk none s m h hr
    | some h₁ =>
      rcases hr.epMgmt_some Δ qep P r.isSome hep_h with ⟨s₁, m_ep, hep_s, hep_m, hr₁⟩
      rw [hep_s, hep_m]
      simp only [hr₁.st_eq, hr₁.ep_s, hr₁.idx_s, hr₁.ep_m, hr₁.idx_m,
        StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind]
      exact hk _ _ _ _ (hr₁.record_transmit Δ P _ msg _)
  ·
    change 𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((ThmB.simChall (St := St) Δ qep (challMsgB i blank) (some (i, blank)) (P, m₀, m₁, r)).run m)).run s) >>= _] =
      𝒟[((challImplB sm Δ qep (challMsgHybB i blank b_priv) (P, m₀, m₁, r)).run h) >>= _]
    unfold ThmB.simChall challImplB
    have hok_h2 : ∀ t, (Config.h2 : Config Msg).challAllowedIn t = true := fun _ => rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_h, Bool.false_eq_true,
      ↓reduceIte, StateT.run_monadLift, L18.monadLift_self, bind_assoc, hok_h2, Bool.not_true,
      Bool.or_false]
    rw [samIfNec_bind r]
    dsimp only
    cases hep_h : h.epMgmt Δ qep P r.isSome with
    | none =>
      rcases hr.epMgmt_none Δ qep P r.isSome hep_h with ⟨_, hep_m⟩
      simp only [hep_m, StateT.run_pure, simulateQ_pure, pure_bind]
      rw [evalDist_samIfNec_const]
      exact hk none s m h hr
    | some h₁ =>
      rcases hr.epMgmt_some Δ qep P r.isSome hep_h with ⟨s₁, m_ep, hep_s, hep_m, hr₁⟩
      simp only [hep_m, hr₁.safeCh_m]
      cases hsafe : h₁.safeCh Δ P with
      | false =>
        simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
        rw [evalDist_samIfNec_const]
        exact hk none s m h hr
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          stateT_lift_run, bind_assoc, pure_bind, hr.b_m, hr₁.ep_m, StateT.run_set,
          StateT.run_pure]
        unfold ThmB.simSend
        dsimp only
        by_cases hti : h₁.epoch P = i
        ·
          have hchallOK_priv : (Config.priv i : Config Msg).challAllowedIn i = true := by
            simp [Config.priv]
          have hchallMsg_priv : (Config.priv i : Config Msg).challMsg i = none := rfl
          have hsafe_s : s₁.safeCh Δ P = true := (hr₁.safeCh_s Δ P).trans hsafe
          simp only [hti, ↓reduceIte, challQuery, query_eq_liftM, simulateQ_bind, simulateQ_query,
            OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind, bind_assoc]
          change 𝒟[((challImpl sm Δ qep (Config.priv i)
              (P, blank (if h.b then m₁ else m₀), if h.b then m₁ else m₀, r)).run s) >>= _] = _
          unfold challImpl
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_s, Bool.false_eq_true,
            ↓reduceIte, StateT.run_monadLift, L18.monadLift_self, bind_assoc]
          rw [samIfNec_bind r]
          dsimp only
          simp only [hep_s, hsafe_s, hr₁.ep_s, hti, hchallOK_priv, Bool.not_true, Bool.or_self,
            Bool.false_eq_true, ↓reduceIte, hchallMsg_priv, Option.getD_none,
            hr.b_s, hr₁.st_eq, hr₁.idx_s, StateT.run_bind, StateT.run_set,
            StateT.run_pure, simulateQ_pure, pure_bind]
          refine evalDist_bind_congr _ _ _ fun cb => ?_
          rw [challMsgHybB_eq i blank b_priv rfl (if h.b then m₁ else m₀)]
          have hr' := hr₁.record_chall Δ P hsafe
            (sm.send (h₁.st P) (if b_priv then if h.b then m₁ else m₀ else blank (if h.b then m₁ else m₀)) cb.1).1
            (if b_priv then if h.b then m₁ else m₀ else blank (if h.b then m₁ else m₀))
            (if h.b then m₁ else m₀)
            (sm.send (h₁.st P) (if b_priv then if h.b then m₁ else m₀ else blank (if h.b then m₁ else m₀)) cb.1).2
            true
          rw [hti] at hr'
          rw [hr₁.idx_m]
          exact hk _ _ _ _ hr'
        ·
          simp only [hti, ↓reduceIte, transmitQuery, query_eq_liftM, simulateQ_bind,
            simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
            StateT.run_bind, bind_assoc]
          change 𝒟[((transmitImpl sm Δ qep
              (P, ((challMsgB i blank (h₁.epoch P)).map (· (if h.b then m₁ else m₀))).getD
                (if h.b then m₁ else m₀), r)).run s) >>= _] = _
          unfold transmitImpl
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_s, Bool.false_eq_true,
            ↓reduceIte, StateT.run_monadLift, L18.monadLift_self, bind_assoc]
          rw [samIfNec_bind r]
          dsimp only
          simp only [hep_s, hr₁.st_eq, hr₁.ep_s, hr₁.idx_s, StateT.run_bind, StateT.run_set,
            StateT.run_pure, simulateQ_pure, pure_bind]
          refine evalDist_bind_congr _ _ _ fun cb => ?_
          rw [challMsgHybB_ne i blank b_priv hti (if h.b then m₁ else m₀), hr₁.idx_m]
          exact hk _ _ _ _ (hr₁.record_chall Δ P hsafe _ _ _ _ false)
  ·
    change 𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((ThmB.simDeliver (St := St) (Coins := Coins) (P, c)).run m)).run s) >>= _] =
      𝒟[((deliverImpl sm Config.h2 (P, c)).run h) >>= _]
    unfold ThmB.simDeliver deliverQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc,
      query_eq_liftM, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    change 𝒟[((deliverImpl sm (Config.priv i) (P, c)).run s) >>= _] = _
    unfold deliverImpl
    have hdw_priv : (Config.priv i : Config Msg).deliverWin = false := rfl
    have hdw_h2 : (Config.h2 : Config Msg).deliverWin = false := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_s, hr.win_h,
      Bool.false_eq_true, ↓reduceIte, hr.inTransit_s, hdw_priv, hdw_h2, Bool.false_and]
    cases htr_h : h.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      exact hk none s m h hr
    | some r =>
      have htr_m : ∃ rm, m.inTransit P.other c = some rm ∧ rm.pos = r.pos := by
        have hpos := hr.inTransit_m_pos P.other c
        rw [htr_h] at hpos
        cases hm_tr : m.inTransit P.other c with
        | none => simp [hm_tr] at hpos
        | some rm =>
          simp only [hm_tr, Option.map_some, Option.some.injEq] at hpos
          exact ⟨rm, rfl, hpos⟩
      rcases htr_m with ⟨rm, htr_m, hrm_pos⟩
      simp only [hr.st_eq]
      cases sm.receive (h.st P) c with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        exact hk (some .rejected) s m h hr
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, htr_m, hrm_pos,
          simulateQ_pure, deliver_msg_eq hr r.pos m']
        exact hk _ _ _ _ (hr.accept P st' r.pos)
  ·
    change 𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((ThmB.simInject (St := St) (Coins := Coins) (P, c)).run m)).run s) >>= _] =
      𝒟[((injectImpl sm Δ qep Config.h2 (P, c)).run h) >>= _]
    unfold ThmB.simInject injectQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc,
      query_eq_liftM, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    change 𝒟[((injectImpl sm Δ qep (Config.priv i) (P, c)).run s) >>= _] = _
    unfold injectImpl
    have hij_priv : ∀ t', (Config.priv i : Config Msg).injectFull t' = false := fun _ => rfl
    have hij_h2 : ∀ t', (Config.h2 : Config Msg).injectFull t' = false := fun _ => rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_s, hr.win_h, Bool.false_or,
      hr.inTransit_s, hr.safeInj_s, hr.st_eq]
    by_cases hreq : ((h.inTransit P.other c).isSome || !h.safeInj Δ) = true
    · simp only [hreq, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
      exact hk none s m h hr
    · simp only [hreq, Bool.false_eq_true, ↓reduceIte]
      cases sm.receive (h.st P) c with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        exact hk (some .rejected) s m h hr
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        dsimp only
        by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
          exact hk (some .rejected) s m h hr
        · simp only [hqep, ↓reduceIte, hr.trivial_s, hij_priv, hij_h2, Bool.false_eq_true]
          by_cases htriv : h.trivial Δ ⟨P.other, t', i'⟩ = true
          · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              simulateQ_pure, pure_bind]
            exact hk _ _ _ _ (hr.accept P st' ⟨P.other, t', i'⟩)
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
              pure_bind]
            exact hk (some .rejected) s m h hr
  ·
    change 𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((ThmB.simCorr (St := St) (Msg := Msg) (Coins := Coins) (C := C) P).run m)).run s) >>= _] =
      𝒟[((corrImpl (St := St) (Msg := Msg) (C := C) P).run h) >>= _]
    unfold ThmB.simCorr corrQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc,
      query_eq_liftM, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    change 𝒟[((corrImpl (St := St) (Msg := Msg) (C := C) P).run s) >>= _] = _
    unfold corrImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_s, hr.win_h, Bool.false_or,
      hr.corrAllowed_s]
    cases hcorr : h.corrAllowed P with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, Option.isSome_none,
        Bool.false_eq_true, simulateQ_pure, pure_bind]
      exact hk none s m h hr
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
        StateT.run_pure, Option.isSome_some, simulateQ_pure, pure_bind, hr.st_eq]
      exact hk _ _ _ _ (hr.afterCorr P hcorr)

lemma simulateQ_privRedB (i : ℕ) (blank : Msg → Msg) (b_priv : Bool)
    {α : Type} (oa : AdversaryComp St Msg Coins C α)
    (s : GameState St Msg C) (m : Mirror Msg C) (h : GameState St Msg C)
    (hr : SimRel i b_priv s m h)
    (k₁ : α → Mirror Msg C → GameState St Msg C → ProbComp Bool)
    (k₂ : α → GameState St Msg C → ProbComp Bool)
    (hk : ∀ a s' m' h', SimRel i b_priv s' m' h' → 𝒟[k₁ a m' s'] = 𝒟[k₂ a h']) :
    𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((simulateQ (ThmB.simImpl (St := St) (Coins := Coins) Δ qep (challMsgB i blank) (some (i, blank))) oa).run m)).run s) >>=
        fun p => k₁ p.1.1 p.1.2 p.2] =
      𝒟[((simulateQ (runImplB sm Δ qep (challMsgHybB i blank b_priv)) oa).run h) >>=
        fun p => k₂ p.1 p.2] := by
  induction oa using OracleComp.inductionOn generalizing s m h with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hk a s m h hr
  | query_bind t mx ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    exact simStep_privRedB sm Δ qep i blank b_priv t s m h hr
      (fun u m' s' =>
        ((simulateQ (runImpl sm Δ qep (Config.priv i))
          ((simulateQ (ThmB.simImpl Δ qep (challMsgB i blank) (some (i, blank))) (mx u)).run m')).run s') >>=
          fun p => k₁ p.1.1 p.1.2 p.2)
      (fun u h' =>
        ((simulateQ (runImplB sm Δ qep (challMsgHybB i blank b_priv)) (mx u)).run h') >>=
          fun p => k₂ p.1 p.2)
      (fun u s' m' h' hr' => ih u s' m' h' hr')

variable [SampleableType Key]

def hybBranchB (tL : Option ℕ) (i : ℕ) (challMsg : ℕ → Option (Msg → Msg))
    (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', h) ← runB sm Δ qep challMsg b A
  if lastLeakGuessAdmissible Δ tL i && canon i h == tL then return (b == b' || h.win)
  else $ᵗ Bool

lemma evalDist_privRedB_run (tL : Option ℕ) (i : ℕ) (blank : Msg → Msg) (b_priv : Bool)
    (A : Adversary St Msg Coins C) :
    𝒟[do
        let (out, s) ← run sm Δ qep (Config.priv i) b_priv (ThmB.privRedB Δ qep i blank A)
        if lastLeakGuessAdmissible Δ tL i && canon i s == tL then return (b_priv == out)
        else $ᵗ Bool] =
      𝒟[do
        let z ← hybBranchB sm Δ qep tL i (challMsgHybB i blank b_priv) A
        return (b_priv == z)] := by
  unfold hybBranchB runB run ThmB.privRedB ThmB.simRun
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc,
    simulateQ_liftM_unif]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Key : ProbComp Key) ($ᵗ Bool : ProbComp Bool)]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b_sim => ?_
  refine evalDist_bind_congr ($ᵗ Key : ProbComp Key) _ _ fun k => ?_
  refine simulateQ_privRedB sm Δ qep i blank b_priv A
    (initState sm k b_priv)
    ({ st := fun _ => (), b := b_sim } : Mirror Msg C)
    (initState sm k b_sim)
    (SimRel.init sm i k b_priv b_sim)
    (fun b' _ s' =>
      if (lastLeakGuessAdmissible Δ tL i && canon i s' == tL) = true then pure (b_priv == (b_sim == b'))
      else $ᵗ Bool)
    (fun b' h' =>
      (if (lastLeakGuessAdmissible Δ tL i && canon i h' == tL) = true then pure (b_sim == b' || h'.win)
       else $ᵗ Bool) >>= fun z => pure (b_priv == z))
    (fun b' s' m' h' hr' => ?_)
  rw [hr'.canon_s i, hr'.win_h, Bool.or_false]
  by_cases hcond : (lastLeakGuessAdmissible Δ tL i && canon i h' == tL) = true
  · simp [hcond]
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    cases b_priv
    · simpa using (ProbComp.evalDist_bind_not_uniformBool (pure : Bool → ProbComp Bool)).symm
    · simp

theorem privAdvantage_privRedB_eq (tL : Option ℕ) (i : ℕ) (blank : Msg → Msg)
    (A : Adversary St Msg Coins C) :
    privAdvantage sm Δ qep tL i (ThmB.privRedB Δ qep i blank A) =
      𝒟[hybBranchB sm Δ qep tL i (challMsgB i blank) A].boolDist
        𝒟[hybBranchB sm Δ qep tL i (challMsgB (i + 1) blank) A] := by
  rw [← evalDist_boolBias_bind_uniformBool
    (hybBranchB sm Δ qep tL i (challMsgB i blank) A)
    (hybBranchB sm Δ qep tL i (challMsgB (i + 1) blank) A)]
  unfold privAdvantage privGame
  congr 1
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b_priv => ?_
  rw [evalDist_privRedB_run sm Δ qep tL i blank b_priv A]
  cases b_priv <;> rfl

end SimRelB

/-! ### Frozen guess and hybrid telescoping -/

section InvAndMaskB

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]

lemma runImplB_canon_frozen_step (challMsg : ℕ → Option (Msg → Msg)) (i : ℕ)
    (t : (unifSpec + spec St Msg Coins C).Domain)
    (s : GameState St Msg C) (hi : InvEpoch s) (hle : i ≤ max (s.epoch .A) (s.epoch .B))
    {β : Type} (k₁ k₂ : (unifSpec + spec St Msg Coins C).Range t → GameState St Msg C → ProbComp β)
    (hk : ∀ u s', InvEpoch s' → i ≤ max (s'.epoch .A) (s'.epoch .B) →
      canon i s' = canon i s → k₁ u s' = k₂ u s') :
    ((runImplB sm Δ qep challMsg t).run s >>= fun p => k₁ p.1 p.2) =
      ((runImplB sm Δ qep challMsg t).run s >>= fun p => k₂ p.1 p.2) := by
  have hmax_mono : ∀ {s' : GameState St Msg C}, (∀ Q, s.epoch Q ≤ s'.epoch Q) →
      i ≤ max (s'.epoch .A) (s'.epoch .B) := by
    intro s' hm
    have hA := hm .A
    have hB := hm .B
    omega
  rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change (StateT.lift (query (spec := unifSpec) n) : StateT _ ProbComp _).run s >>= _ =
      (StateT.lift (query (spec := unifSpec) n) : StateT _ ProbComp _).run s >>= _
    simp only [stateT_lift_run, bind_assoc, pure_bind]
    exact bind_congr fun u => hk u s hi hle rfl
  · change (transmitImpl sm Δ qep (P, m, r)).run s >>= _ =
      (transmitImpl sm Δ qep (P, m, r)).run s >>= _
    unfold transmitImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hi.win_false, Bool.false_eq_true,
      ↓reduceIte, StateT.run_monadLift, L18.monadLift_self, bind_assoc]
    refine bind_congr fun cb => ?_
    cases hep : s.epMgmt Δ qep P cb.2 with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact hk none s hi hle rfl
    | some s₁ =>
      rcases hi.epMgmt Δ qep hep with ⟨hi₁, hm₁, hcan₁⟩
      rcases hi₁.record Δ P (sm.send (s₁.st P) m cb.1).1 m (sm.send (s₁.st P) m cb.1).2 false
        with ⟨hi₂, hep₂, hcan₂⟩
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      refine hk _ _ hi₂ ?_ ((hcan₂ i).trans (hcan₁ i hle))
      rw [hep₂]
      exact hmax_mono hm₁
  · change (challImplB sm Δ qep challMsg (P, m₀, m₁, r)).run s >>= _ =
      (challImplB sm Δ qep challMsg (P, m₀, m₁, r)).run s >>= _
    unfold challImplB
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hi.win_false, Bool.false_eq_true,
      ↓reduceIte, StateT.run_monadLift, L18.monadLift_self, bind_assoc]
    refine bind_congr fun cb => ?_
    cases hep : s.epMgmt Δ qep P cb.2 with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact hk none s hi hle rfl
    | some s₁ =>
      rcases hi.epMgmt Δ qep hep with ⟨hi₁, hm₁, hcan₁⟩
      by_cases hch : (!s₁.safeCh Δ P || !((Config.h2 : Config Msg).challAllowedIn (s₁.epoch P))) = true
      · simp only [hch, ↓reduceIte, StateT.run_pure, pure_bind]
        exact hk none s hi hle rfl
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind]
        rcases hi₁.record Δ P _ _ _ true with ⟨hi₂, hep₂, hcan₂⟩
        refine hk _ _ hi₂ ?_ ((hcan₂ i).trans (hcan₁ i hle))
        rw [hep₂]
        exact hmax_mono hm₁
  · change (deliverImpl sm Config.h2 (P, c)).run s >>= _ =
      (deliverImpl sm Config.h2 (P, c)).run s >>= _
    unfold deliverImpl
    have hdw : (Config.h2 : Config Msg).deliverWin = false := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hi.win_false, Bool.false_eq_true,
      ↓reduceIte, hdw, Bool.false_and]
    cases htr : s.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact hk none s hi hle rfl
    | some r =>
      rcases inTransit_mem_and_sender htr with ⟨hr_mem, hr_send⟩
      have hpos_le : r.pos.epoch ≤ s.epoch P.other := by
        have h0 := hi.trans_ep r hr_mem
        rwa [hr_send] at h0
      cases sm.receive (s.st P) c with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact hk (some .rejected) s hi hle rfl
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        rcases hi.accept P st' r.pos hpos_le with ⟨hi₁, hm₁, hcan₁⟩
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        exact hk _ _ hi₁ (hmax_mono hm₁) (hcan₁ i)
  · change (injectImpl sm Δ qep Config.h2 (P, c)).run s >>= _ =
      (injectImpl sm Δ qep Config.h2 (P, c)).run s >>= _
    unfold injectImpl
    have hij : ∀ t, (Config.h2 : Config Msg).injectFull t = false := fun _ => rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hi.win_false, Bool.false_or]
    cases hreq : ((s.inTransit P.other c).isSome || !s.safeInj Δ) with
    | true =>
      simp only [↓reduceIte, StateT.run_pure, pure_bind]
      exact hk none s hi hle rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hsafe_inj : s.safeInj Δ = true := by
        cases h : s.safeInj Δ <;> simp [h] at hreq ⊢
      cases sm.receive (s.st P) c with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact hk (some .rejected) s hi hle rfl
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        dsimp only
        by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, pure_bind]
          exact hk (some .rejected) s hi hle rfl
        · simp only [hqep, ↓reduceIte, hij, Bool.false_eq_true]
          cases htriv : s.trivial Δ ⟨P.other, t', i'⟩ with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
            exact hk (some .rejected) s hi hle rfl
          | true =>
            have hpos_le : t' ≤ s.epoch P.other :=
              trivial_epoch_le Δ hi hsafe_inj rfl htriv
            rcases hi.accept P st' ⟨P.other, t', i'⟩ hpos_le with ⟨hi₁, hm₁, hcan₁⟩
            simp only [↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
            exact hk _ _ hi₁ (hmax_mono hm₁) (hcan₁ i)
  · change (corrImpl (St := St) (Msg := Msg) (C := C) P).run s >>= _ =
      (corrImpl (St := St) (Msg := Msg) (C := C) P).run s >>= _
    unfold corrImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hi.win_false, Bool.false_or]
    cases hcorr : (!s.corrAllowed P) with
    | true =>
      simp only [↓reduceIte, StateT.run_pure, pure_bind]
      exact hk none s hi hle rfl
    | false =>
      rcases hi.afterCorr P with ⟨hi₁, hep₁, hcan₁⟩
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind]
      refine hk _ _ hi₁ ?_ (hcan₁ i hle)
      rw [hep₁]
      exact hle

lemma simulateQ_canon_frozenB (challMsg : ℕ → Option (Msg → Msg)) (i : ℕ)
    {α β : Type} (oa : AdversaryComp St Msg Coins C α)
    (s : GameState St Msg C) (hi : InvEpoch s) (hle : i ≤ max (s.epoch .A) (s.epoch .B))
    (k : α → GameState St Msg C → ProbComp β)
    (c₀ : ProbComp β)
    (hk : ∀ a s', InvEpoch s' → i ≤ max (s'.epoch .A) (s'.epoch .B) →
      canon i s' = canon i s → k a s' = c₀) :
    ((simulateQ (runImplB sm Δ qep challMsg) oa).run s >>= fun p => k p.1 p.2) =
      ((simulateQ (runImplB sm Δ qep challMsg) oa).run s >>= fun _ => c₀) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hk a s hi hle rfl
  | query_bind t mx ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    exact runImplB_canon_frozen_step sm Δ qep challMsg i t s hi hle
      (fun u s' => (simulateQ (runImplB sm Δ qep challMsg) (mx u)).run s' >>= fun p => k p.1 p.2)
      (fun u s' => (simulateQ (runImplB sm Δ qep challMsg) (mx u)).run s' >>= fun _ => c₀)
      (fun u s' hi' hle' hcan' =>
        ih u s' hi' hle' (fun a s'' hi'' hle'' hcan'' =>
          hk a s'' hi'' hle'' (hcan''.trans hcan')))

lemma simulateQ_h3B_pre (hΔ : 0 < Δ) (i : ℕ) (blank : Msg → Msg)
    {α : Type} (oa : AdversaryComp St Msg Coins C α)
    (s : GameState St Msg C) (hi : InvEpoch s)
    (k : α → GameState St Msg C → ProbComp Bool)
    (c₀ : ProbComp Bool)
    (hk : ∀ a s', InvEpoch s' → canon i s' ∈ admissibleLastLeakGuesses Δ i → k a s' = c₀) :
    𝒟[(simulateQ (runImplB sm Δ qep (challMsgB i blank)) oa).run s >>= fun p => k p.1 p.2] =
      𝒟[(simulateQ (runImplB sm Δ qep (challMsgB (i + 1) blank)) oa).run s >>=
        fun p => k p.1 p.2] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind t mx ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · change 𝒟[(StateT.lift (query (spec := unifSpec) n) : StateT _ ProbComp _).run s >>= _] =
        𝒟[(StateT.lift (query (spec := unifSpec) n) : StateT _ ProbComp _).run s >>= _]
      simp only [stateT_lift_run, bind_assoc, pure_bind]
      exact evalDist_bind_congr _ _ _ fun u => ih u s hi
    · change 𝒟[(transmitImpl sm Δ qep (P, m, r)).run s >>= _] =
        𝒟[(transmitImpl sm Δ qep (P, m, r)).run s >>= _]
      unfold transmitImpl
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hi.win_false, Bool.false_eq_true,
        ↓reduceIte, StateT.run_monadLift, L18.monadLift_self, bind_assoc]
      refine evalDist_bind_congr _ _ _ fun cb => ?_
      cases hep : s.epMgmt Δ qep P cb.2 with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact ih none s hi
      | some s₁ =>
        rcases hi.epMgmt Δ qep hep with ⟨hi₁, _, _⟩
        rcases hi₁.record Δ P (sm.send (s₁.st P) m cb.1).1 m (sm.send (s₁.st P) m cb.1).2 false
          with ⟨hi₂, _, _⟩
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        exact ih _ _ hi₂
    · change 𝒟[(challImplB sm Δ qep (challMsgB i blank) (P, m₀, m₁, r)).run s >>= _] =
        𝒟[(challImplB sm Δ qep (challMsgB (i + 1) blank) (P, m₀, m₁, r)).run s >>= _]
      unfold challImplB
      have hok : ∀ t, (Config.h2 : Config Msg).challAllowedIn t = true := fun _ => rfl
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hi.win_false, Bool.false_eq_true,
        ↓reduceIte, StateT.run_monadLift, L18.monadLift_self, bind_assoc, hok, Bool.not_true,
        Bool.or_false]
      refine evalDist_bind_congr _ _ _ fun cb => ?_
      cases hep : s.epMgmt Δ qep P cb.2 with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact ih none s hi
      | some s₁ =>
        dsimp only
        rcases hi.epMgmt Δ qep hep with ⟨hi₁, _, _⟩
        cases hsafe : s₁.safeCh Δ P with
        | false =>
          simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, pure_bind]
          exact ih none s hi
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            StateT.run_set, StateT.run_pure, pure_bind]
          by_cases hti : s₁.epoch P = i
          · have hcan_mem : canon i s₁ ∈ admissibleLastLeakGuesses Δ i :=
              canon_mem_targetsL_of_safeCh Δ hΔ hi₁ hsafe hti
            have hle_max : i ≤ max (s₁.epoch .A) (s₁.epoch .B) := by
              cases P <;> omega
            set msg_L := ((challMsgB i blank (s₁.epoch P)).map (· (if s.b then m₁ else m₀))).getD
              (if s.b then m₁ else m₀)
            set res_L := sm.send (s₁.st P) msg_L cb.1
            set s_L := s₁.record Δ P res_L.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, msg_L, res_L.2⟩ true
            set msg_R := ((challMsgB (i + 1) blank (s₁.epoch P)).map (· (if s.b then m₁ else m₀))).getD
              (if s.b then m₁ else m₀)
            set res_R := sm.send (s₁.st P) msg_R cb.1
            set s_R := s₁.record Δ P res_R.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, msg_R, res_R.2⟩ true
            rcases hi₁.record Δ P res_L.1 msg_L res_L.2 true with ⟨hi_L, hep_L, hcan_L⟩
            rcases hi₁.record Δ P res_R.1 msg_R res_R.2 true with ⟨hi_R, hep_R, hcan_R⟩
            have hle_L : i ≤ max (s_L.epoch .A) (s_L.epoch .B) := by
              rw [hep_L]; exact hle_max
            have hle_R : i ≤ max (s_R.epoch .A) (s_R.epoch .B) := by
              rw [hep_R]; exact hle_max
            have hfrz_L := simulateQ_canon_frozenB sm Δ qep (challMsgB i blank) i
              (mx (some res_L.2)) s_L hi_L hle_L k c₀
              (fun a s' hi' _ hcan' => hk a s' hi' (by rw [hcan', hcan_L]; exact hcan_mem))
            have hfrz_R := simulateQ_canon_frozenB sm Δ qep (challMsgB (i + 1) blank) i
              (mx (some res_R.2)) s_R hi_R hle_R k c₀
              (fun a s' hi' _ hcan' => hk a s' hi' (by rw [hcan', hcan_R]; exact hcan_mem))
            rw [hfrz_L, hfrz_R, OracleComp.evalDist_bind_const, OracleComp.evalDist_bind_const]
          · have hmsg : ((challMsgB i blank (s₁.epoch P)).map (· (if s.b then m₁ else m₀))).getD
                (if s.b then m₁ else m₀) =
              ((challMsgB (i + 1) blank (s₁.epoch P)).map (· (if s.b then m₁ else m₀))).getD
                (if s.b then m₁ else m₀) := by
              have hiff : (s₁.epoch P < i + 1) ↔ (s₁.epoch P < i) := by omega
              simp [challMsgB, hiff]
            rw [hmsg]
            rcases hi₁.record Δ P _ _ _ true with ⟨hi₂, _, _⟩
            exact ih _ _ hi₂
    · change 𝒟[(deliverImpl sm Config.h2 (P, c)).run s >>= _] =
        𝒟[(deliverImpl sm Config.h2 (P, c)).run s >>= _]
      unfold deliverImpl
      have hdw : (Config.h2 : Config Msg).deliverWin = false := rfl
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hi.win_false, Bool.false_eq_true,
        ↓reduceIte, hdw, Bool.false_and]
      cases htr : s.inTransit P.other c with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact ih none s hi
      | some r =>
        rcases inTransit_mem_and_sender htr with ⟨hr_mem, hr_send⟩
        have hpos_le : r.pos.epoch ≤ s.epoch P.other := by
          have h0 := hi.trans_ep r hr_mem
          rwa [hr_send] at h0
        cases sm.receive (s.st P) c with
        | none =>
          simp only [StateT.run_pure, pure_bind]
          exact ih (some .rejected) s hi
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          rcases hi.accept P st' r.pos hpos_le with ⟨hi₁, _, _⟩
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
          exact ih _ _ hi₁
    · change 𝒟[(injectImpl sm Δ qep Config.h2 (P, c)).run s >>= _] =
        𝒟[(injectImpl sm Δ qep Config.h2 (P, c)).run s >>= _]
      unfold injectImpl
      have hij : ∀ t, (Config.h2 : Config Msg).injectFull t = false := fun _ => rfl
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hi.win_false, Bool.false_or]
      cases hreq : ((s.inTransit P.other c).isSome || !s.safeInj Δ) with
      | true =>
        simp only [↓reduceIte, StateT.run_pure, pure_bind]
        exact ih none s hi
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hsafe_inj : s.safeInj Δ = true := by
          cases h : s.safeInj Δ <;> simp [h] at hreq ⊢
        cases sm.receive (s.st P) c with
        | none =>
          simp only [StateT.run_pure, pure_bind]
          exact ih (some .rejected) s hi
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          dsimp only
          by_cases hqep : qep + 1 < t'
          · simp only [hqep, ↓reduceIte, StateT.run_pure, pure_bind]
            exact ih (some .rejected) s hi
          · simp only [hqep, ↓reduceIte, hij, Bool.false_eq_true]
            cases htriv : s.trivial Δ ⟨P.other, t', i'⟩ with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
              exact ih (some .rejected) s hi
            | true =>
              have hpos_le : t' ≤ s.epoch P.other :=
                trivial_epoch_le Δ hi hsafe_inj rfl htriv
              rcases hi.accept P st' ⟨P.other, t', i'⟩ hpos_le with ⟨hi₁, _, _⟩
              simp only [↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
              exact ih _ _ hi₁
    · change 𝒟[(corrImpl (St := St) (Msg := Msg) (C := C) P).run s >>= _] =
        𝒟[(corrImpl (St := St) (Msg := Msg) (C := C) P).run s >>= _]
      unfold corrImpl
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hi.win_false, Bool.false_or]
      cases hcorr : (!s.corrAllowed P) with
      | true =>
        simp only [↓reduceIte, StateT.run_pure, pure_bind]
        exact ih none s hi
      | false =>
        rcases hi.afterCorr P with ⟨hi₁, _, _⟩
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind]
        exact ih _ _ hi₁

variable [SampleableType Key]

def gameKillB (i : ℕ) (S : Finset (Option ℕ)) (challMsg : ℕ → Option (Msg → Msg))
    (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', h) ← runB sm Δ qep challMsg b A
  if canon i h ∈ S then $ᵗ Bool
  else return (b == b' || h.win)

lemma gameKillB_empty (i : ℕ) (challMsg : ℕ → Option (Msg → Msg))
    (A : Adversary St Msg Coins C) :
    gameKillB sm Δ qep i ∅ challMsg A = gameB sm Δ qep challMsg A := by
  simp [gameKillB, gameB]

lemma evalDist_gameKillB_targetsL_eq (hΔ : 0 < Δ) (i : ℕ) (blank : Msg → Msg)
    (A : Adversary St Msg Coins C) :
    𝒟[gameKillB sm Δ qep i (admissibleLastLeakGuesses Δ i) (challMsgB i blank) A] =
      𝒟[gameKillB sm Δ qep i (admissibleLastLeakGuesses Δ i) (challMsgB (i + 1) blank) A] := by
  unfold gameKillB runB
  simp only [bind_assoc]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b => ?_
  refine evalDist_bind_congr ($ᵗ Key : ProbComp Key) _ _ fun k => ?_
  exact simulateQ_h3B_pre sm Δ qep hΔ i blank A (initState sm k b) (InvEpoch.init sm k b)
    (fun b' h => if canon i h ∈ admissibleLastLeakGuesses Δ i then $ᵗ Bool else pure (b == b' || h.win))
    ($ᵗ Bool)
    (fun b' h _ hmem => by simp [hmem])

lemma evalDist_select_gameKillB_insert (i : ℕ) (S : Finset (Option ℕ)) (tL : Option ℕ)
    (htL_not : tL ∉ S) (hval : lastLeakGuessAdmissible Δ tL i = true)
    (challMsg : ℕ → Option (Msg → Msg)) (A : Adversary St Msg Coins C) :
    𝒟[do
        let sel ← $ᵗ Bool
        if sel then gameKillB sm Δ qep i S challMsg A else $ᵗ Bool] =
      𝒟[do
        let sel ← $ᵗ Bool
        if sel then gameKillB sm Δ qep i (insert tL S) challMsg A
        else hybBranchB sm Δ qep tL i challMsg A] := by
  have hcoin : 𝒟[do
      let sel ← $ᵗ Bool
      if sel then gameKillB sm Δ qep i S challMsg A else $ᵗ Bool] =
    𝒟[do
      let sel ← $ᵗ Bool
      if sel then gameKillB sm Δ qep i S challMsg A
      else do
        let b ← $ᵗ Bool
        let _ ← runB sm Δ qep challMsg b A
        $ᵗ Bool] := by
    refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun sel => ?_
    cases sel
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← bind_assoc, OracleComp.evalDist_bind_const]
    · rfl
  rw [hcoin]
  unfold gameKillB hybBranchB
  simp only [ite_bind ($ᵗ Bool : ProbComp Bool)]
  conv_lhs =>
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) ($ᵗ Bool : ProbComp Bool)]
  conv_rhs =>
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) ($ᵗ Bool : ProbComp Bool)]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b => ?_
  simp only [ite_bind (runB sm Δ qep challMsg b A)]
  conv_lhs =>
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) (runB sm Δ qep challMsg b A)]
  conv_rhs =>
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) (runB sm Δ qep challMsg b A)]
  refine evalDist_bind_congr (runB sm Δ qep challMsg b A) _ _ fun p => ?_
  by_cases hcan : canon i p.2 = tL
  · simp only [hcan, htL_not, ↓reduceIte, Finset.mem_insert_self, hval, beq_self_eq_true,
      Bool.and_self]
    exact evalDist_select_swap (pure (b == p.1 || p.2.win)) ($ᵗ Bool)
  · have hmem_iff : canon i p.2 ∈ insert tL S ↔ canon i p.2 ∈ S := by
      simp [Finset.mem_insert, hcan]
    have hbeq : (canon i p.2 == tL) = false := beq_false_of_ne hcan
    simp [hmem_iff, hbeq]

lemma gameKillB_boolDist_insert (i : ℕ) (blank : Msg → Msg) (A : Adversary St Msg Coins C)
    (S : Finset (Option ℕ)) (tL : Option ℕ) (htL_not : tL ∉ S)
    (hval : lastLeakGuessAdmissible Δ tL i = true) :
    𝒟[gameKillB sm Δ qep i S (challMsgB i blank) A].boolDist
        𝒟[gameKillB sm Δ qep i S (challMsgB (i + 1) blank) A] ≤
      𝒟[gameKillB sm Δ qep i (insert tL S) (challMsgB i blank) A].boolDist
          𝒟[gameKillB sm Δ qep i (insert tL S) (challMsgB (i + 1) blank) A] +
        privAdvantage sm Δ qep tL i (ThmB.privRedB Δ qep i blank A) := by
  rw [privAdvantage_privRedB_eq]
  exact boolDist_le_of_select_eq _ _ _ _ _ _
    (evalDist_select_gameKillB_insert sm Δ qep i S tL htL_not hval (challMsgB i blank) A)
    (evalDist_select_gameKillB_insert sm Δ qep i S tL htL_not hval (challMsgB (i + 1) blank) A)

lemma gameKillB_boolDist_union_le (i : ℕ) (blank : Msg → Msg) (A : Adversary St Msg Coins C)
    (T : Finset (Option ℕ)) (hval : ∀ tL ∈ T, lastLeakGuessAdmissible Δ tL i = true) :
    ∀ S : Finset (Option ℕ), Disjoint S T →
      𝒟[gameKillB sm Δ qep i S (challMsgB i blank) A].boolDist
          𝒟[gameKillB sm Δ qep i S (challMsgB (i + 1) blank) A] ≤
        𝒟[gameKillB sm Δ qep i (S ∪ T) (challMsgB i blank) A].boolDist
            𝒟[gameKillB sm Δ qep i (S ∪ T) (challMsgB (i + 1) blank) A] +
          ∑ tL ∈ T, privAdvantage sm Δ qep tL i (ThmB.privRedB Δ qep i blank A) := by
  induction T using Finset.induction_on with
  | empty =>
    intro S _
    simp
  | @insert tL T htL_not_T ih =>
    intro S hdisj
    have htL_not_S : tL ∉ S := Finset.disjoint_insert_right.mp hdisj |>.1
    have hdisj' : Disjoint (insert tL S) T := by
      rw [Finset.disjoint_insert_left]
      exact ⟨htL_not_T, Finset.disjoint_insert_right.mp hdisj |>.2⟩
    have hstep := gameKillB_boolDist_insert sm Δ qep i blank A S tL htL_not_S
      (hval tL (Finset.mem_insert_self tL T))
    have hih := ih (fun x hx => hval x (Finset.mem_insert_of_mem hx)) (insert tL S) hdisj'
    have hunion : insert tL S ∪ T = S ∪ insert tL T := by
      ext x; simp
    rw [hunion] at hih
    rw [Finset.sum_insert htL_not_T]
    calc _ ≤ _ := hstep
      _ ≤ (𝒟[gameKillB sm Δ qep i (S ∪ insert tL T) (challMsgB i blank) A].boolDist
            𝒟[gameKillB sm Δ qep i (S ∪ insert tL T) (challMsgB (i + 1) blank) A] +
          ∑ x ∈ T, privAdvantage sm Δ qep x i (ThmB.privRedB Δ qep i blank A)) +
          privAdvantage sm Δ qep tL i (ThmB.privRedB Δ qep i blank A) := add_le_add hih le_rfl
      _ = _ := by ring

theorem lemma18B_proof (hΔ : 0 < Δ) (blank : Msg → Msg) (i : ℕ) (A : Adversary St Msg Coins C) :
    hybridAdvantageB sm Δ qep (challMsgB i blank) A ≤
      hybridAdvantageB sm Δ qep (challMsgB (i + 1) blank) A +
        2 * ∑ tL ∈ admissibleLastLeakGuesses Δ i, privAdvantage sm Δ qep tL i (ThmB.privRedB Δ qep i blank A) := by
  unfold hybridAdvantageB
  refine (boolBias_le_add_two_mul_boolDist
    𝒟[gameB sm Δ qep (challMsgB i blank) A]
    𝒟[gameB sm Δ qep (challMsgB (i + 1) blank) A]).trans ?_
  gcongr
  have hunion := gameKillB_boolDist_union_le sm Δ qep i blank A (admissibleLastLeakGuesses Δ i)
    (fun tL htL => validGuess_of_mem_targetsL Δ hΔ htL) ∅ (Finset.disjoint_empty_left _)
  rw [Finset.empty_union, gameKillB_empty, gameKillB_empty,
    evalDist_gameKillB_targetsL_eq sm Δ qep hΔ i blank A,
    Measure.boolDist_self, zero_add] at hunion
  exact hunion

theorem h3B_telescope (hΔ : 0 < Δ) (blank : Msg → Msg) (A : Adversary St Msg Coins C) (n : ℕ) :
    hybridAdvantage sm Δ qep Config.h2 A ≤
      hybridAdvantageB sm Δ qep (challMsgB n blank) A +
        2 * ∑ i ∈ Finset.range n, ∑ tL ∈ admissibleLastLeakGuesses Δ i,
          privAdvantage sm Δ qep tL i (ThmB.privRedB Δ qep i blank A) := by
  induction n with
  | zero => simp [hybridAdvantageB_zero]
  | succ n ih =>
    refine ih.trans ?_
    have h := lemma18B_proof sm Δ qep hΔ blank n A
    rw [Finset.sum_range_succ, mul_add]
    calc _ ≤ (hybridAdvantageB sm Δ qep (challMsgB (n + 1) blank) A +
            2 * ∑ tL ∈ admissibleLastLeakGuesses Δ n,
              privAdvantage sm Δ qep tL n (ThmB.privRedB Δ qep n blank A)) +
          2 * ∑ i ∈ Finset.range n, ∑ tL ∈ admissibleLastLeakGuesses Δ i,
            privAdvantage sm Δ qep tL i (ThmB.privRedB Δ qep i blank A) := add_le_add h le_rfl
      _ = _ := by ring

theorem theorem1_h1_blank_proof [DecidableEq Pub] (hΔ : 0 < Δ)
    (pubOf : Msg → Pub) (blank : Msg → Msg)
    (hblank : ∀ m₀ m₁, pubOf m₀ = pubOf m₁ → blank m₀ = blank m₁)
    (A : Adversary St Msg Coins C) (heq : EqualPubChalls pubOf A) :
    hybridAdvantage sm Δ qep Config.h1 A ≤
      2 * ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
            authAdvantage sm Δ qep tL t (Thm1.challSim Δ qep A)
        + 2 * ∑ i ∈ Finset.range (qep + 1), ∑ tL ∈ admissibleLastLeakGuesses Δ i,
            privAdvantage sm Δ qep tL i (ThmB.privRedB Δ qep i blank A) := by
  have h17 := Thm1.lemma17 sm Δ qep hΔ A
  have h18 := h3B_telescope sm Δ qep hΔ blank A (qep + 1)
  rw [h3B_final_proof sm Δ qep pubOf blank hblank A heq, zero_add] at h18
  calc hybridAdvantage sm Δ qep Config.h1 A
      ≤ hybridAdvantage sm Δ qep Config.h2 A + _ := h17
    _ ≤ _ + _ := add_le_add h18 le_rfl
    _ = _ := by ring

end InvAndMaskB

end CryptoGames.LibsignalSM.Proofs.BlankLemma18
