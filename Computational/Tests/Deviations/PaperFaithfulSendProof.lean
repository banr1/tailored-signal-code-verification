/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Tests.Deviations.PaperFaithfulSendDefs
import VCVio.OracleComp.EvalDist.Measure

/-!
# Advantage Preservation for `DEV-CKA3`

**Checked by Lean.** Proves `CKA.advantagePaper_eq` by coupling `gamePaper` with `game` running
`fromPaperRed`. Until the first plain `send-P` query in epoch `t*`, both runs agree and the shadow
counter in `fromPaperRed` matches `s.epoch`. Calling `chall-P` in epoch `t*` enters `PastStar tStar`,
after which `fromPaperRed` never aborts; calling plain `send-P` in epoch `t*` causes `fromPaperRed`
to output a uniform bit while `gamePaper` enters `PastStar tStar` without reading `b`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.CKA.PaperFaithfulSendProof

variable {Key State Coins Msg CKey : Type}

def setB (b : Bool) (s : GameState State Msg) : GameState State Msg :=
  { s with b := b }

@[simp] theorem setB_st (b : Bool) (s : GameState State Msg) : (setB b s).st = s.st := rfl
@[simp] theorem setB_epoch (b : Bool) (s : GameState State Msg) : (setB b s).epoch = s.epoch := rfl
@[simp] theorem setB_b (b : Bool) (s : GameState State Msg) : (setB b s).b = b := rfl
@[simp] theorem setB_lastMsg (b : Bool) (s : GameState State Msg) :
    (setB b s).lastMsg = s.lastMsg := rfl
@[simp] theorem setB_canSend (b : Bool) (s : GameState State Msg) (P : Party) :
    (setB b s).canSend P = s.canSend P := rfl
@[simp] theorem setB_canReceive (b : Bool) (s : GameState State Msg) (P : Party) :
    (setB b s).canReceive P = s.canReceive P := rfl
@[simp] theorem setB_allowCorr (b : Bool) (s : GameState State Msg) (tStar : ℕ) :
    (setB b s).allowCorr tStar = s.allowCorr tStar := rfl
@[simp] theorem setB_finished (b : Bool) (s : GameState State Msg) (Δ tStar : ℕ) (P : Party) :
    (setB b s).finished Δ tStar P = s.finished Δ tStar P := rfl
@[simp] theorem setB_afterSend (b : Bool) (s : GameState State Msg) (P : Party) (γ : State)
    (T : Msg) : (setB b s).afterSend P γ T = setB b (s.afterSend P γ T) := rfl
@[simp] theorem setB_afterReceive (b : Bool) (s : GameState State Msg) (P : Party) (γ : State) :
    (setB b s).afterReceive P γ = setB b (s.afterReceive P γ) := rfl

/-- At least one party has reached or passed the challenge epoch `tStar`. -/
def PastStar (tStar : ℕ) (s : GameState State Msg) : Prop :=
  tStar ≤ s.epoch .A ∨ tStar ≤ s.epoch .B

@[simp] theorem pastStar_setB (tStar : ℕ) (b : Bool) (s : GameState State Msg) :
    PastStar tStar (setB b s) ↔ PastStar tStar s := Iff.rfl

theorem pastStar_afterSend {tStar : ℕ} {s : GameState State Msg} (h : PastStar tStar s)
    (P : Party) (γ : State) (T : Msg) : PastStar tStar (s.afterSend P γ T) := by
  rcases h with h | h <;> cases P <;> simp [PastStar, GameState.afterSend] <;> omega

theorem pastStar_afterReceive {tStar : ℕ} {s : GameState State Msg} (h : PastStar tStar s)
    (P : Party) (γ : State) : PastStar tStar (s.afterReceive P γ) := by
  rcases h with h | h <;> cases P <;> simp [PastStar, GameState.afterReceive] <;> omega

theorem pastStar_afterSend_of_eq {tStar : ℕ} {s : GameState State Msg} {P : Party}
    (h : (s.canSend P && s.epoch P + 1 == tStar) = true) (γ : State) (T : Msg) :
    PastStar tStar (s.afterSend P γ T) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  cases P <;> simp [PastStar, GameState.afterSend, h.2]

theorem not_active_of_pastStar {tStar : ℕ} {s : GameState State Msg} (h : PastStar tStar s)
    (P : Party) : (s.canSend P && s.epoch P + 1 == tStar) = false := by
  cases h1 : (s.canSend P && s.epoch P + 1 == tStar)
  · rfl
  · simp only [GameState.canSend, Bool.and_eq_true, beq_iff_eq] at h1
    rcases h1 with ⟨⟨heq, _⟩, hstar⟩
    rcases h with h | h <;> cases P <;> simp [Party.other] at heq <;> omega

theorem evalDist_unifBool_beq (x : Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => pure (b == x)] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by
  change 𝒟[(fun b : Bool => b == x) <$> ($ᵗ Bool : ProbComp Bool)] = 𝒟[($ᵗ Bool : ProbComp Bool)]
  rw [evalDist_map_of_discrete, SampleableType.evalDist_uniformSample]
  exact ProbabilityTheory.map_uniformOn_univ_of_bijective Measurable.of_discrete
    ⟨fun b₁ b₂ h => by cases b₁ <;> cases b₂ <;> cases x <;> simp_all,
     fun b => ⟨b == x, by cases b <;> cases x <;> rfl⟩⟩

theorem evalDist_unifBool_beq_left (x : Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => pure (x == b)] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by
  simp only [Bool.beq_comm (a := x)]
  exact evalDist_unifBool_beq x

theorem evalDist_unifBool_bind_const {α : Type} (c : ProbComp α) (g : α → Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => c >>= fun a => pure (b == g a)] =
      𝒟[($ᵗ Bool : ProbComp Bool)] := by
  rw [OracleComp.evalDist_bind_bind_swap]
  rw [evalDist_bind_congr c _ (fun _ => ($ᵗ Bool : ProbComp Bool))
    (fun a => evalDist_unifBool_beq (g a))]
  exact OracleComp.evalDist_bind_const c ($ᵗ Bool : ProbComp Bool)

section Sim

variable (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ)
  [SampleableType Coins] [SampleableType CKey]

local notation "GameM" => StateT (GameState State Msg) ProbComp
local notation "Comp" => AdversaryComp State Coins Msg CKey

abbrev gameImpl : QueryImpl (unifSpec + spec State Coins Msg CKey) GameM :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget GameM + oracleImpl cka Δ tStar

abbrev gameImplPaper : QueryImpl (unifSpec + spec State Coins Msg CKey) GameM :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget GameM + oracleImplPaper cka Δ tStar

abbrev runPaper {α : Type} (oa : Comp α) (s : GameState State Msg) :
    ProbComp (α × GameState State Msg) :=
  (simulateQ (gameImplPaper cka Δ tStar) oa).run s

abbrev runRed {α : Type} (oa : Comp α) (e? : Option (Party → ℕ)) (s : GameState State Msg) :
    ProbComp ((α × Option (Party → ℕ)) × GameState State Msg) :=
  (simulateQ (gameImpl cka Δ tStar) ((simulateQ (fromPaperImpl tStar) oa).run e?)).run s

abbrev stepRed (t : (unifSpec + spec State Coins Msg CKey).Domain)
    (e? : Option (Party → ℕ)) (s : GameState State Msg) :
    ProbComp (((unifSpec + spec State Coins Msg CKey).Range t × Option (Party → ℕ)) ×
      GameState State Msg) :=
  (simulateQ (gameImpl cka Δ tStar) ((fromPaperImpl tStar t).run e?)).run s

theorem runPaper_query_bind {α : Type}
    (t : (unifSpec + spec State Coins Msg CKey).Domain)
    (k : (unifSpec + spec State Coins Msg CKey).Range t → Comp α)
    (s : GameState State Msg) :
    runPaper cka Δ tStar ((liftM (OracleSpec.query t) : Comp _) >>= k) s =
      (gameImplPaper cka Δ tStar t).run s >>= fun z => runPaper cka Δ tStar (k z.1) z.2 := by
  simp only [runPaper, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind]

theorem runRed_query_bind {α : Type}
    (t : (unifSpec + spec State Coins Msg CKey).Domain)
    (k : (unifSpec + spec State Coins Msg CKey).Range t → Comp α)
    (e? : Option (Party → ℕ)) (s : GameState State Msg) :
    runRed cka Δ tStar ((liftM (OracleSpec.query t) : Comp _) >>= k) e? s =
      stepRed cka Δ tStar t e? s >>= fun z => runRed cka Δ tStar (k z.1.1) z.1.2 z.2 := by
  simp only [runRed, stepRed, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind]

@[simp] theorem simulateQ_sendQuery (P : Party) :
    simulateQ (gameImpl cka Δ tStar) (sendQuery (State := State) (Coins := Coins) P) =
      sendImpl cka tStar P := by
  simp [sendQuery, simulateQ_query]
  rfl

@[simp] theorem simulateQ_sendBadQuery (P : Party) (r : Coins) :
    simulateQ (gameImpl cka Δ tStar) (sendWithAdversaryCoinsQuery (State := State) P r) =
      sendWithAdversaryCoinsImpl cka tStar (P, r) := by
  simp [sendWithAdversaryCoinsQuery, simulateQ_query]
  rfl

@[simp] theorem simulateQ_challQuery (P : Party) :
    simulateQ (gameImpl cka Δ tStar) (challQuery (State := State) (Coins := Coins) P) =
      challImpl cka tStar P := by
  simp [challQuery, simulateQ_query]
  rfl

@[simp] theorem simulateQ_receiveQuery (P : Party) :
    simulateQ (gameImpl cka Δ tStar)
      (receiveQuery (State := State) (Coins := Coins) (Msg := Msg) (CKey := CKey) P) =
      receiveImpl cka P := by
  simp [receiveQuery, simulateQ_query]
  rfl

@[simp] theorem simulateQ_corrQuery (P : Party) :
    simulateQ (gameImpl cka Δ tStar)
      (corrQuery (State := State) (Coins := Coins) (Msg := Msg) (CKey := CKey) P) =
      corrImpl Δ tStar P := by
  simp [corrQuery, simulateQ_query]
  rfl

@[simp] theorem gameImpl_inl_run (n : unifSpec.Domain) (s : GameState State Msg) :
    (gameImpl cka Δ tStar (.inl n)).run s =
      ((liftM (OracleSpec.query n) : ProbComp (unifSpec.Range n)) >>= fun u => pure (u, s)) := by
  change (StateT.lift (liftM (OracleSpec.query n) : ProbComp _)).run s = _
  simp [StateT.run_lift]

@[simp] theorem simulateQ_query_inl_run (n : unifSpec.Domain) (s : GameState State Msg) :
    (simulateQ (gameImpl cka Δ tStar)
      (query (spec := unifSpec + spec State Coins Msg CKey) (.inl n))).run s =
      ((liftM (OracleSpec.query n) : ProbComp (unifSpec.Range n)) >>= fun u => pure (u, s)) := by
  simp only [query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    gameImpl_inl_run]

@[simp] theorem gameImplPaper_inl_run (n : unifSpec.Domain) (s : GameState State Msg) :
    (gameImplPaper cka Δ tStar (.inl n)).run s =
      ((liftM (OracleSpec.query n) : ProbComp (unifSpec.Range n)) >>= fun u => pure (u, s)) := by
  change (StateT.lift (liftM (OracleSpec.query n) : ProbComp _)).run s = _
  simp [StateT.run_lift]

omit [SampleableType CKey] in
theorem sendImplPaper_run (P : Party) (s : GameState State Msg) :
    (sendImplPaper cka P).run s =
      if !(s.canSend P) then pure (none, s)
      else ($ᵗ Coins : ProbComp Coins) >>= fun r =>
        let out := cka.send (s.st P) r
        pure (some out.2, s.afterSend P out.1 out.2.1) := by
  simp only [sendImplPaper, StateT.run_bind, StateT.run_get, pure_bind]
  split <;> simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift]

theorem gameImplPaper_send_run (P : Party) (s : GameState State Msg) :
    (gameImplPaper cka Δ tStar (.inr (.inl (.inl (.inl (.inl P)))))).run s =
      if !(s.canSend P) then pure (none, s)
      else ($ᵗ Coins : ProbComp Coins) >>= fun r =>
        let out := cka.send (s.st P) r
        pure (some out.2, s.afterSend P out.1 out.2.1) :=
  sendImplPaper_run cka P s

omit [SampleableType CKey] in
theorem sendImpl_run (P : Party) (s : GameState State Msg) :
    (sendImpl cka tStar P).run s =
      if !(s.canSend P) || s.epoch P + 1 == tStar then pure (none, s)
      else ($ᵗ Coins : ProbComp Coins) >>= fun r =>
        let out := cka.send (s.st P) r
        pure (some out.2, s.afterSend P out.1 out.2.1) := by
  simp only [sendImpl, StateT.run_bind, StateT.run_get, pure_bind]
  split <;> simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift]

omit [SampleableType Coins] [SampleableType CKey] in
theorem sendBadImpl_run (P : Party) (r : Coins) (s : GameState State Msg) :
    (sendWithAdversaryCoinsImpl cka tStar (P, r)).run s =
      if !(s.canSend P) || !decide (s.epoch P + 1 + 2 ≤ tStar) then pure (none, s)
      else
        let out := cka.send (s.st P) r
        pure (some out.2, s.afterSend P out.1 out.2.1) := by
  simp only [sendWithAdversaryCoinsImpl, StateT.run_bind, StateT.run_get, pure_bind]
  split <;> simp [StateT.run_pure, StateT.run_set]

theorem gameImplPaper_sendBad_run (P : Party) (r : Coins) (s : GameState State Msg) :
    (gameImplPaper cka Δ tStar (.inr (.inl (.inl (.inl (.inr (P, r))))))).run s =
      if !(s.canSend P) || !decide (s.epoch P + 1 + 2 ≤ tStar) then pure (none, s)
      else
        let out := cka.send (s.st P) r
        pure (some out.2, s.afterSend P out.1 out.2.1) :=
  sendBadImpl_run cka tStar P r s

theorem challImpl_run (P : Party) (s : GameState State Msg) :
    (challImpl cka tStar P).run s =
      if !(s.canSend P) || s.epoch P + 1 != tStar then pure (none, s)
      else ($ᵗ Coins : ProbComp Coins) >>= fun r =>
        let out := cka.send (s.st P) r
        if s.b then
          ($ᵗ CKey : ProbComp CKey) >>= fun I' =>
            pure (some (out.2.1, I'), s.afterSend P out.1 out.2.1)
        else
          pure (some out.2, s.afterSend P out.1 out.2.1) := by
  simp only [challImpl, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp [StateT.run_pure]
  · simp [StateT.run_set, StateT.run_monadLift]
  · simp [StateT.run_set, StateT.run_monadLift]

theorem gameImplPaper_chall_run (P : Party) (s : GameState State Msg) :
    (gameImplPaper cka Δ tStar (.inr (.inl (.inl (.inr P))))).run s =
      if !(s.canSend P) || s.epoch P + 1 != tStar then pure (none, s)
      else ($ᵗ Coins : ProbComp Coins) >>= fun r =>
        let out := cka.send (s.st P) r
        if s.b then
          ($ᵗ CKey : ProbComp CKey) >>= fun I' =>
            pure (some (out.2.1, I'), s.afterSend P out.1 out.2.1)
        else
          pure (some out.2, s.afterSend P out.1 out.2.1) :=
  challImpl_run cka tStar P s

omit [SampleableType Coins] [SampleableType CKey] in
theorem receiveImpl_run (P : Party) (s : GameState State Msg) :
    (receiveImpl cka P).run s =
      if !(s.canReceive P) then pure (none, s)
      else match s.lastMsg with
        | none => pure (none, s)
        | some T => pure (some (), s.afterReceive P (cka.receive (s.st P) T).1) := by
  simp only [receiveImpl, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp [StateT.run_pure]
  · cases s.lastMsg <;> simp [StateT.run_pure, StateT.run_set]

theorem gameImplPaper_receive_run (P : Party) (s : GameState State Msg) :
    (gameImplPaper cka Δ tStar (.inr (.inl (.inr P)))).run s =
      if !(s.canReceive P) then pure (none, s)
      else match s.lastMsg with
        | none => pure (none, s)
        | some T => pure (some (), s.afterReceive P (cka.receive (s.st P) T).1) :=
  receiveImpl_run cka P s

omit [SampleableType Coins] [SampleableType CKey] in
theorem corrImpl_run (P : Party) (s : GameState State Msg) :
    (corrImpl Δ tStar P).run s =
      if s.allowCorr tStar || s.finished Δ tStar P then pure (some (s.st P), s)
      else pure (none, s) := by
  simp only [corrImpl, StateT.run_bind, StateT.run_get, pure_bind]
  split <;> simp [StateT.run_pure]

theorem gameImplPaper_corr_run (P : Party) (s : GameState State Msg) :
    (gameImplPaper cka Δ tStar (.inr (.inr P))).run s =
      if s.allowCorr tStar || s.finished Δ tStar P then pure (some (s.st P), s)
      else pure (none, s) :=
  corrImpl_run Δ tStar P s

theorem stepRed_inl_none (n : unifSpec.Domain) (s : GameState State Msg) :
    stepRed cka Δ tStar (.inl n) none s =
      (liftM (OracleSpec.query n) : ProbComp _) >>= fun u => pure ((u, none), s) := by
  change (simulateQ (gameImpl cka Δ tStar)
    ((StateT.lift (query (spec := unifSpec + spec State Coins Msg CKey) (.inl n))).run none)).run s = _
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    simulateQ_query_inl_run, bind_assoc, pure_bind]

theorem evalDist_runRed_none {α : Type} (oa : Comp α) (s : GameState State Msg)
    (g : ProbComp Bool)
    (F : (α × Option (Party → ℕ)) × GameState State Msg → ProbComp Bool)
    (hF : ∀ a, F ((a, none), s) = g) :
    𝒟[runRed cka Δ tStar oa none s >>= F] = 𝒟[g] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [runRed, simulateQ_pure, StateT.run_pure, pure_bind, hF]
  | query_bind t k ih =>
    rw [runRed_query_bind, bind_assoc]
    rcases t with n | ((((P | ⟨P, r⟩) | P) | P) | P)
    · rw [stepRed_inl_none]
      simp only [bind_assoc, pure_bind]
      rw [evalDist_bind_congr (liftM (OracleSpec.query n) : ProbComp _) _ (fun _ => g) ih]
      exact OracleComp.evalDist_bind_const _ g
    · have h0 : stepRed cka Δ tStar (.inr (.inl (.inl (.inl (.inl P))))) none s =
          pure ((none, none), s) := by
        simp [stepRed, fromPaperImpl, fromPaperSend]
      rw [h0, pure_bind]
      exact ih none
    · have h0 : stepRed cka Δ tStar (.inr (.inl (.inl (.inl (.inr (P, r)))))) none s =
          pure ((none, none), s) := by
        simp [stepRed, fromPaperImpl, fromPaperFwd]
      rw [h0, pure_bind]
      exact ih none
    · have h0 : stepRed cka Δ tStar (.inr (.inl (.inl (.inr P)))) none s =
          pure ((none, none), s) := by
        simp [stepRed, fromPaperImpl, fromPaperFwd]
      rw [h0, pure_bind]
      exact ih none
    · have h0 : stepRed cka Δ tStar (.inr (.inl (.inr P))) none s =
          pure ((none, none), s) := by
        simp [stepRed, fromPaperImpl, fromPaperFwd]
      rw [h0, pure_bind]
      exact ih none
    · have h0 : stepRed cka Δ tStar (.inr (.inr P)) none s =
          pure ((none, none), s) := by
        simp [stepRed, fromPaperImpl]
      rw [h0, pure_bind]
      exact ih none

theorem run_fromPaperFwd_some {α β : Type} (P : Party) (q : Comp (Option α))
    (e : Party → ℕ) (s : GameState State Msg)
    (G : (Option α × Option (Party → ℕ)) × GameState State Msg → ProbComp β) :
    ((simulateQ (gameImpl cka Δ tStar) ((fromPaperFwd P q).run (some e))).run s >>= G) =
      ((simulateQ (gameImpl cka Δ tStar) q).run s >>= fun z =>
        G ((z.1, match z.1 with
          | some _ => some (Function.update e P (e P + 1))
          | none => some e), z.2)) := by
  simp only [fromPaperFwd, fromPaperStep, StateT.run_bind, StateT.run_get, Option.isNone_some,
    Bool.false_eq_true, ↓reduceIte, StateT.run_lift, StateT.run_modify, StateT.run_pure,
    bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure]
  refine bind_congr fun z => ?_
  cases z.1 <;> rfl

theorem stepRed_eq_of_not_abort
    {t : (unifSpec + spec State Coins Msg CKey).Domain} {s : GameState State Msg}
    (h : ∀ P, t = .inr (.inl (.inl (.inl (.inl P)))) →
      (s.canSend P && s.epoch P + 1 == tStar) = false)
    {β : Type}
    (G : ((unifSpec + spec State Coins Msg CKey).Range t × Option (Party → ℕ)) ×
      GameState State Msg → ProbComp β) :
    (stepRed cka Δ tStar t (some s.epoch) s >>= G) =
      ((gameImplPaper cka Δ tStar t).run s >>= fun z => G ((z.1, some z.2.epoch), z.2)) := by
  rcases t with n | ((((P | ⟨P, r⟩) | P) | P) | P)
  · change ((simulateQ (gameImpl cka Δ tStar)
      ((StateT.lift (query (spec := unifSpec + spec State Coins Msg CKey) (.inl n))).run
        (some s.epoch))).run s >>= G) = _
    simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      simulateQ_query_inl_run, gameImplPaper_inl_run, bind_assoc, pure_bind]
  · have hP := h P rfl
    have hcond : ((s.epoch P == s.epoch P.other && P.sendsIn (s.epoch P + 1)) &&
        s.epoch P + 1 == tStar) = false := hP
    have hguard : (!(s.canSend P) || s.epoch P + 1 == tStar) = !(s.canSend P) := by
      revert hP
      generalize (s.epoch P + 1 == tStar) = b2
      cases s.canSend P <;> cases b2 <;> simp
    change ((simulateQ (gameImpl cka Δ tStar) ((fromPaperSend tStar P).run (some s.epoch))).run s >>= G) = _
    simp only [fromPaperSend, StateT.run_bind, StateT.run_get, pure_bind]
    rw [ite_eq_right_iff.mpr (fun hc => by simp [hcond] at hc),
      run_fromPaperFwd_some, simulateQ_sendQuery, sendImpl_run, gameImplPaper_send_run, hguard]
    split_ifs
    · simp
    · simp [GameState.afterSend]
  · change ((simulateQ (gameImpl cka Δ tStar)
      ((fromPaperFwd P (sendWithAdversaryCoinsQuery P r)).run (some s.epoch))).run s >>= G) = _
    rw [run_fromPaperFwd_some, simulateQ_sendBadQuery, sendBadImpl_run, gameImplPaper_sendBad_run]
    split_ifs <;> simp [GameState.afterSend]
  · change ((simulateQ (gameImpl cka Δ tStar)
      ((fromPaperFwd P (challQuery P)).run (some s.epoch))).run s >>= G) = _
    rw [run_fromPaperFwd_some, simulateQ_challQuery, challImpl_run, gameImplPaper_chall_run]
    split_ifs
    · simp
    · simp [bind_assoc, GameState.afterSend]
    · simp [GameState.afterSend]
  · change ((simulateQ (gameImpl cka Δ tStar)
      ((fromPaperFwd P (receiveQuery P)).run (some s.epoch))).run s >>= G) = _
    rw [run_fromPaperFwd_some, simulateQ_receiveQuery, receiveImpl_run, gameImplPaper_receive_run]
    split_ifs
    · simp
    · cases s.lastMsg <;> simp [GameState.afterReceive]
  · have hcorr : stepRed cka Δ tStar (.inr (.inr P)) (some s.epoch) s =
        ((corrImpl Δ tStar P).run s >>= fun z => pure ((z.1, some s.epoch), z.2)) := by
      simp [stepRed, fromPaperImpl]
    rw [hcorr, bind_assoc, corrImpl_run, gameImplPaper_corr_run]
    split_ifs <;> simp

theorem gameImplPaper_setB_of_not_chall
    {t : (unifSpec + spec State Coins Msg CKey).Domain} {s : GameState State Msg}
    (h : ∀ P, t = .inr (.inl (.inl (.inr P))) →
      (s.canSend P && s.epoch P + 1 == tStar) = false)
    (b : Bool) {β : Type}
    (G : (unifSpec + spec State Coins Msg CKey).Range t × GameState State Msg → ProbComp β) :
    ((gameImplPaper cka Δ tStar t).run (setB b s) >>= G) =
      ((gameImplPaper cka Δ tStar t).run s >>= fun z => G (z.1, setB b z.2)) := by
  rcases t with n | ((((P | ⟨P, r⟩) | P) | P) | P)
  · rw [gameImplPaper_inl_run, gameImplPaper_inl_run]
    simp only [bind_assoc, pure_bind]
  · rw [gameImplPaper_send_run, gameImplPaper_send_run]
    simp only [setB_canSend, setB_st, setB_afterSend]
    split_ifs <;> simp_all [map_eq_bind_pure_comp, bind_assoc]
  · rw [gameImplPaper_sendBad_run, gameImplPaper_sendBad_run]
    have hdec : decide ((setB b s).epoch P + 1 + 2 ≤ tStar) =
        decide (s.epoch P + 1 + 2 ≤ tStar) := rfl
    simp only [setB_canSend, hdec, setB_st, setB_afterSend]
    split_ifs <;> simp
  · have hP := h P rfl
    have hguard : (!(s.canSend P) || s.epoch P + 1 != tStar) = true := by
      change (!s.canSend P || !(s.epoch P + 1 == tStar)) = true
      revert hP
      generalize (s.epoch P + 1 == tStar) = b2
      cases s.canSend P <;> cases b2 <;> simp
    rw [gameImplPaper_chall_run, gameImplPaper_chall_run]
    simp only [setB_canSend, setB_epoch, hguard, ↓reduceIte, pure_bind]
  · rw [gameImplPaper_receive_run, gameImplPaper_receive_run]
    simp only [setB_canReceive, setB_lastMsg, setB_st, setB_afterReceive]
    split_ifs
    · simp_all
    · cases s.lastMsg <;> simp_all
  · rw [gameImplPaper_corr_run, gameImplPaper_corr_run]
    simp only [setB_allowCorr, setB_finished, setB_st]
    split_ifs <;> simp_all

theorem gameImplPaper_bind_congr_pastStar
    {t : (unifSpec + spec State Coins Msg CKey).Domain} {s : GameState State Msg}
    (h : PastStar tStar s) {β : Type}
    {G₁ G₂ : (unifSpec + spec State Coins Msg CKey).Range t × GameState State Msg → ProbComp β}
    (hG : ∀ u s', PastStar tStar s' → G₁ (u, s') = G₂ (u, s')) :
    ((gameImplPaper cka Δ tStar t).run s >>= G₁) =
      ((gameImplPaper cka Δ tStar t).run s >>= G₂) := by
  rcases t with n | ((((P | ⟨P, r⟩) | P) | P) | P)
  · rw [gameImplPaper_inl_run]
    simp only [bind_assoc, pure_bind]
    exact bind_congr fun u => hG u s h
  · rw [gameImplPaper_send_run]
    split_ifs
    · simp only [pure_bind]
      exact hG none s h
    · simp only [bind_assoc, pure_bind]
      exact bind_congr fun r => hG _ _ (pastStar_afterSend h P _ _)
  · rw [gameImplPaper_sendBad_run]
    split_ifs
    · simp only [pure_bind]
      exact hG none s h
    · simp only [pure_bind]
      exact hG _ _ (pastStar_afterSend h P _ _)
  · rw [gameImplPaper_chall_run]
    split_ifs
    · simp only [pure_bind]
      exact hG none s h
    · simp only [bind_assoc, pure_bind]
      exact bind_congr fun r => bind_congr fun I' => hG _ _ (pastStar_afterSend h P _ _)
    · simp only [bind_assoc, pure_bind]
      exact bind_congr fun r => hG _ _ (pastStar_afterSend h P _ _)
  · rw [gameImplPaper_receive_run]
    split_ifs
    · simp only [pure_bind]
      exact hG none s h
    · cases s.lastMsg with
      | none =>
        simp only [pure_bind]
        exact hG none s h
      | some T =>
        simp only [pure_bind]
        exact hG _ _ (pastStar_afterReceive h P _)
  · rw [gameImplPaper_corr_run]
    split_ifs <;> { simp only [pure_bind]; exact hG _ s h }

theorem runPaper_setB_of_pastStar {α β : Type} (oa : Comp α)
    {s : GameState State Msg} (h : PastStar tStar s) (b : Bool) (f : α → ProbComp β) :
    (runPaper cka Δ tStar oa (setB b s) >>= fun z => f z.1) =
      (runPaper cka Δ tStar oa s >>= fun z => f z.1) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp [runPaper]
  | query_bind t k ih =>
    rw [runPaper_query_bind, runPaper_query_bind, bind_assoc, bind_assoc]
    rw [gameImplPaper_setB_of_not_chall cka Δ tStar (fun P _ => not_active_of_pastStar h P) b]
    exact gameImplPaper_bind_congr_pastStar cka Δ tStar h fun u s' hs' => ih u hs'

theorem runRed_eq_runPaper_of_pastStar {α β : Type} (oa : Comp α)
    {s : GameState State Msg} (h : PastStar tStar s) (g : ProbComp β) (f : α → ProbComp β) :
    (runRed cka Δ tStar oa (some s.epoch) s >>= fun z =>
      match z.1.2 with
      | some _ => f z.1.1
      | none => g) =
      (runPaper cka Δ tStar oa s >>= fun z => f z.1) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp [runRed, runPaper]
  | query_bind t k ih =>
    rw [runRed_query_bind, runPaper_query_bind, bind_assoc, bind_assoc]
    rw [stepRed_eq_of_not_abort cka Δ tStar (fun P _ => not_active_of_pastStar h P)]
    exact gameImplPaper_bind_congr_pastStar cka Δ tStar h fun u s' hs' => ih u hs'

theorem runRed_chall_active {α β : Type} (P : Party)
    (k : Option (Msg × CKey) → Comp α)
    {s : GameState State Msg} (h : (s.canSend P && s.epoch P + 1 == tStar) = true)
    (g : ProbComp β) (f : α → ProbComp β) :
    (runRed cka Δ tStar
      ((liftM (OracleSpec.query (spec := unifSpec + spec State Coins Msg CKey)
        (.inr (.inl (.inl (.inr P))))) : Comp _) >>= k)
      (some s.epoch) s >>= fun z =>
        match z.1.2 with
        | some _ => f z.1.1
        | none => g) =
      (runPaper cka Δ tStar
        ((liftM (OracleSpec.query (spec := unifSpec + spec State Coins Msg CKey)
          (.inr (.inl (.inl (.inr P))))) : Comp _) >>= k) s >>= fun z => f z.1) := by
  rw [runRed_query_bind, runPaper_query_bind, bind_assoc, bind_assoc]
  rw [stepRed_eq_of_not_abort cka Δ tStar (by intro Q hQ; cases hQ)]
  have hguard : (!(s.canSend P) || s.epoch P + 1 != tStar) = false := by
    change (!s.canSend P || !(s.epoch P + 1 == tStar)) = false
    revert h
    generalize (s.epoch P + 1 == tStar) = b2
    cases s.canSend P <;> cases b2 <;> simp
  rw [gameImplPaper_chall_run]
  simp only [hguard, Bool.false_eq_true, ↓reduceIte, bind_assoc]
  refine bind_congr fun r => ?_
  have hps : PastStar tStar (s.afterSend P (cka.send (s.st P) r).1 (cka.send (s.st P) r).2.1) :=
    pastStar_afterSend_of_eq h _ _
  split_ifs
  · simp only [bind_assoc, pure_bind]
    exact bind_congr fun I' => runRed_eq_runPaper_of_pastStar cka Δ tStar (k _) hps g f
  · simp only [pure_bind]
    exact runRed_eq_runPaper_of_pastStar cka Δ tStar (k _) hps g f

theorem runPaper_send_active_setB {α β : Type} (P : Party)
    (k : Option (Msg × CKey) → Comp α)
    {s : GameState State Msg} (h : (s.canSend P && s.epoch P + 1 == tStar) = true)
    (b : Bool) (f : α → ProbComp β) :
    (runPaper cka Δ tStar
      ((liftM (OracleSpec.query (spec := unifSpec + spec State Coins Msg CKey)
        (.inr (.inl (.inl (.inl (.inl P)))))) : Comp _) >>= k) (setB b s) >>= fun z => f z.1) =
      (runPaper cka Δ tStar
        ((liftM (OracleSpec.query (spec := unifSpec + spec State Coins Msg CKey)
          (.inr (.inl (.inl (.inl (.inl P)))))) : Comp _) >>= k) s >>= fun z => f z.1) := by
  rw [runPaper_query_bind, runPaper_query_bind, bind_assoc, bind_assoc]
  rw [gameImplPaper_setB_of_not_chall cka Δ tStar (by intro Q hQ; cases hQ) b]
  have hcan : s.canSend P = true := by
    revert h
    cases s.canSend P <;> simp
  rw [gameImplPaper_send_run]
  simp only [hcan, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  refine bind_congr fun r => ?_
  have hps : PastStar tStar (s.afterSend P (cka.send (s.st P) r).1 (cka.send (s.st P) r).2.1) :=
    pastStar_afterSend_of_eq h _ _
  exact runPaper_setB_of_pastStar cka Δ tStar (k _) hps b f

theorem evalDist_runRed_send_active (P : Party)
    (k : Option (Msg × CKey) → Comp Bool)
    {s : GameState State Msg} (h : (s.canSend P && s.epoch P + 1 == tStar) = true) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
      runRed cka Δ tStar
        ((liftM (OracleSpec.query (spec := unifSpec + spec State Coins Msg CKey)
          (.inr (.inl (.inl (.inl (.inl P)))))) : Comp _) >>= k)
        (some s.epoch) (setB b s) >>= fun z =>
          match z.1.2 with
          | some _ => pure (b == z.1.1)
          | none => ($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b')] =
      𝒟[($ᵗ Bool : ProbComp Bool)] := by
  have hstep : ∀ b : Bool,
      stepRed cka Δ tStar (.inr (.inl (.inl (.inl (.inl P))))) (some s.epoch) (setB b s) =
        pure ((none, none), setB b s) := by
    intro b
    have hcond : ((s.epoch P == s.epoch P.other && P.sendsIn (s.epoch P + 1)) &&
        s.epoch P + 1 == tStar) = true := h
    change (simulateQ (gameImpl cka Δ tStar)
      ((fromPaperSend tStar P).run (some s.epoch))).run (setB b s) = _
    simp only [fromPaperSend, StateT.run_bind, StateT.run_get, pure_bind]
    rw [ite_eq_left_iff.mpr (fun hc => False.elim (hc (by simpa using hcond)))]
    simp [StateT.run_set, StateT.run_pure]
  have hinner : ∀ b : Bool,
      𝒟[runRed cka Δ tStar
        ((liftM (OracleSpec.query (spec := unifSpec + spec State Coins Msg CKey)
          (.inr (.inl (.inl (.inl (.inl P)))))) : Comp _) >>= k)
        (some s.epoch) (setB b s) >>= fun z =>
          match z.1.2 with
          | some _ => pure (b == z.1.1)
          | none => ($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b')] =
        𝒟[($ᵗ Bool : ProbComp Bool)] := by
    intro b
    rw [runRed_query_bind, hstep b, pure_bind]
    rw [evalDist_runRed_none cka Δ tStar (k none) (setB b s)
      (($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b')) _ (fun _ => rfl)]
    exact evalDist_unifBool_beq_left b
  rw [evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ (fun _ => ($ᵗ Bool : ProbComp Bool)) hinner]
  exact OracleComp.evalDist_bind_const ($ᵗ Bool : ProbComp Bool) ($ᵗ Bool : ProbComp Bool)

/-- `runPaper` and `runRed` induce identical hidden-bit guess distributions from any shared state
`s`. -/
theorem evalDist_runPaper_eq_runRed (oa : Comp Bool) (s : GameState State Msg) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
      runPaper cka Δ tStar oa (setB b s) >>= fun z => pure (b == z.1)] =
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
      runRed cka Δ tStar oa (some s.epoch) (setB b s) >>= fun z =>
        match z.1.2 with
        | some _ => pure (b == z.1.1)
        | none => ($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b')] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b' =>
    simp [runPaper, runRed]
  | query_bind t k ih =>
    by_cases hsend : ∃ P, t = .inr (.inl (.inl (.inl (.inl P)))) ∧
        (s.canSend P && s.epoch P + 1 == tStar) = true
    · rcases hsend with ⟨P, rfl, hact⟩
      rw [evalDist_runRed_send_active cka Δ tStar P k hact]
      have hlhs : (fun b : Bool =>
          runPaper cka Δ tStar
            ((liftM (OracleSpec.query (spec := unifSpec + spec State Coins Msg CKey)
              (.inr (.inl (.inl (.inl (.inl P)))))) : Comp _) >>= k) (setB b s) >>=
            fun z => pure (b == z.1)) =
          (fun b : Bool =>
            runPaper cka Δ tStar
              ((liftM (OracleSpec.query (spec := unifSpec + spec State Coins Msg CKey)
                (.inr (.inl (.inl (.inl (.inl P)))))) : Comp _) >>= k) s >>=
              fun z => pure (b == z.1)) := by
        funext b
        exact runPaper_send_active_setB cka Δ tStar P k hact b (fun b' => pure (b == b'))
      rw [hlhs]
      exact evalDist_unifBool_bind_const _ Prod.fst
    · by_cases hchall : ∃ P, t = .inr (.inl (.inl (.inr P))) ∧
          (s.canSend P && s.epoch P + 1 == tStar) = true
      · rcases hchall with ⟨P, rfl, hact⟩
        congr 1
        refine bind_congr fun b => ?_
        have hactB : ((setB b s).canSend P && (setB b s).epoch P + 1 == tStar) = true := hact
        exact (runRed_chall_active cka Δ tStar P k hactB
          (($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b'))
          (fun b' => pure (b == b'))).symm
      · have hnotSend : ∀ P, t = .inr (.inl (.inl (.inl (.inl P)))) →
            (s.canSend P && s.epoch P + 1 == tStar) = false := by
          intro P hP
          cases h1 : (s.canSend P && s.epoch P + 1 == tStar)
          · rfl
          · exact False.elim (hsend ⟨P, hP, h1⟩)
        have hnotChall : ∀ P, t = .inr (.inl (.inl (.inr P))) →
            (s.canSend P && s.epoch P + 1 == tStar) = false := by
          intro P hP
          cases h1 : (s.canSend P && s.epoch P + 1 == tStar)
          · rfl
          · exact False.elim (hchall ⟨P, hP, h1⟩)
        have hlhs : ∀ b : Bool,
            (runPaper cka Δ tStar ((liftM (OracleSpec.query t) : Comp _) >>= k) (setB b s) >>=
              fun z => pure (b == z.1)) =
            ((gameImplPaper cka Δ tStar t).run s >>= fun z =>
              runPaper cka Δ tStar (k z.1) (setB b z.2) >>= fun w => pure (b == w.1)) := by
          intro b
          rw [runPaper_query_bind, bind_assoc,
            gameImplPaper_setB_of_not_chall cka Δ tStar hnotChall b]
        have hrhs : ∀ b : Bool,
            (runRed cka Δ tStar ((liftM (OracleSpec.query t) : Comp _) >>= k)
              (some s.epoch) (setB b s) >>= fun z =>
                match z.1.2 with
                | some _ => pure (b == z.1.1)
                | none => ($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b')) =
            ((gameImplPaper cka Δ tStar t).run s >>= fun z =>
              runRed cka Δ tStar (k z.1) (some z.2.epoch) (setB b z.2) >>= fun w =>
                match w.1.2 with
                | some _ => pure (b == w.1.1)
                | none => ($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b')) := by
          intro b
          rw [runRed_query_bind, bind_assoc]
          have hnotSendB : ∀ P, t = .inr (.inl (.inl (.inl (.inl P)))) →
              ((setB b s).canSend P && (setB b s).epoch P + 1 == tStar) = false := hnotSend
          have hstep := stepRed_eq_of_not_abort cka Δ tStar (s := setB b s) hnotSendB
            (fun z => runRed cka Δ tStar (k z.1.1) z.1.2 z.2 >>= fun w =>
              match w.1.2 with
              | some _ => pure (b == w.1.1)
              | none => ($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b'))
          simp only [setB_epoch] at hstep
          rw [hstep, gameImplPaper_setB_of_not_chall cka Δ tStar hnotChall b]
          simp only [setB_epoch]
        simp only [hlhs, hrhs]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool),
            OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool)]
        exact evalDist_bind_congr ((gameImplPaper cka Δ tStar t).run s) _ _ fun z => ih z.1 z.2

theorem simulateQ_liftM_probComp {α : Type} (p : ProbComp α) (s : GameState State Msg) :
    (simulateQ (gameImpl cka Δ tStar) (liftM p : Comp α)).run s =
      (p >>= fun a => pure (a, s)) := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp
  | query_bind t k ih =>
    simp only [liftM_bind, simulateQ_bind, StateT.run_bind]
    have hq : (simulateQ (gameImpl cka Δ tStar)
        (liftM (liftM (OracleSpec.query t) : ProbComp _) : Comp _)).run s =
        ((liftM (OracleSpec.query t) : ProbComp _) >>= fun u => pure (u, s)) :=
      simulateQ_query_inl_run cka Δ tStar t s
    rw [hq]
    simp only [bind_assoc, pure_bind, ih]

end Sim

theorem run'_eq_run_bind {σ α β : Type} (x : StateT σ ProbComp α) (s : σ)
    (f : α → ProbComp β) :
    (x.run' s >>= f) = (x.run s >>= fun z => f z.1) := by
  simp [StateT.run', StateT.run, map_eq_bind_pure_comp, bind_assoc]

theorem evalDist_gamePaper_eq_game (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ)
    [SampleableType Key] [SampleableType Coins] [SampleableType CKey]
    (A : Adversary State Coins Msg CKey) :
    𝒟[gamePaper cka Δ tStar A] = 𝒟[game cka Δ tStar (fromPaperRed tStar A)] := by
  unfold gamePaper game fromPaperRed
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) ($ᵗ Key : ProbComp Key)]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) ($ᵗ Key : ProbComp Key)]
  refine evalDist_bind_congr ($ᵗ Key : ProbComp Key) _ _ fun k => ?_
  have h1 : (fun b : Bool => do
      let b' ← (simulateQ (gameImplPaper cka Δ tStar) A).run' (initState cka k b)
      pure (b == b')) =
      (fun b : Bool =>
        runPaper cka Δ tStar A (setB b (initState cka k false)) >>= fun z => pure (b == z.1)) := by
    funext b
    rw [run'_eq_run_bind]
    rfl
  have h2 : (fun b : Bool => do
      let b' ← (simulateQ (gameImpl cka Δ tStar)
        (do
          let (b', e?) ← (simulateQ (fromPaperImpl tStar) A).run (some fun _ => 0)
          match e? with
          | some _ => return b'
          | none => (liftM ($ᵗ Bool : ProbComp Bool) : AdversaryComp State Coins Msg CKey Bool))).run'
        (initState cka k b)
      pure (b == b')) =
      (fun b : Bool =>
        runRed cka Δ tStar A (some (initState cka k false).epoch)
          (setB b (initState cka k false)) >>= fun z =>
          match z.1.2 with
          | some _ => pure (b == z.1.1)
          | none => ($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b')) := by
    funext b
    rw [run'_eq_run_bind]
    simp only [runRed, simulateQ_bind, StateT.run_bind, bind_assoc]
    refine bind_congr fun z => ?_
    rcases z with ⟨⟨b', e?⟩, s'⟩
    cases e? with
    | some e =>
      simp [simulateQ_pure, StateT.run_pure]
    | none =>
      rw [simulateQ_liftM_probComp]
      simp
  erw [h1, h2]
  exact evalDist_runPaper_eq_runRed cka Δ tStar A (initState cka k false)

theorem advantagePaper_eq_proof (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ)
    [SampleableType Key] [SampleableType Coins] [SampleableType CKey]
    (A : Adversary State Coins Msg CKey) :
    advantagePaper cka Δ tStar A = advantage cka Δ tStar (fromPaperRed tStar A) := by
  unfold advantagePaper advantage
  rw [evalDist_gamePaper_eq_game]

end CryptoGames.CKA.PaperFaithfulSendProof

namespace CryptoGames.CKA

/-- Converting `A` via `fromPaperRed tStar` preserves CKA advantage between the paper-faithful game
(ACD19, Fig. 3) and `CKA.game` (`DEV-CKA3`). -/
theorem advantagePaper_eq {Key State Coins Msg CKey : Type}
    (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ)
    [SampleableType Key] [SampleableType Coins] [SampleableType CKey]
    (A : Adversary State Coins Msg CKey) :
    advantagePaper cka Δ tStar A = advantage cka Δ tStar (fromPaperRed tStar A) :=
  PaperFaithfulSendProof.advantagePaper_eq_proof cka Δ tStar A

end CryptoGames.CKA
