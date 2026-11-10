/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPqOomGame
import Computational.Proofs.LibsignalCli.Oom.Faithful
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.EvalDist.ProbabilityBounds

public section

set_option autoImplicit false

/-!
# Agreement of `cliPqxdhExpFlagged` off `bad`

**Checked by Lean.** Proves `cliPqxdhExpFlagged_agree`: if `run` and `run₀` agree wherever `bad`
fails, `cliPqxdhExpFlagged` at `run` and `run₀` assign equal probability to every event whose
logged inputs avoid `bad` (`GoodLog bad`).
-/

namespace Computational.Proofs.LibsignalCli.Oom.Agree

open MeasureTheory (Measure lintegral_congr lintegral_indicator)
open OracleComp OracleSpec
open scoped ENNReal
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.SM (ConfigR GameState)
open CryptoVerification.E2E (BHDrvMode BinState CliDriverState CliDrvMT CliGameAdversary
  CliPartyState ModelDriverInstance ModelDriverInstanceMeta PEParams SMSchemeRM
  UnreachedPqxdhPrimitives bhDecodePreKeyMsgE bhDrCtlSpec bhDrvGuard bhDrvInstClean
  bhNoExtWithSpqr challRM cliGameDrSpec cliGameSmSpec cliGameSpec cliOracleImplRM cliPqLenOk
  cliPqxdhExpFlagged cliRunLogged deliverRM injectRM liftQueryImplStateT2 mkBundleEStrict
  mkKeysEStrict mkMeEStrict modelPrims runCliDriverLogged transmitRM)
open CryptoVerification.E2E.Dir (cliDrvImplM cliDrvSMM cliDrvStartM cliPqInitM cliPqReceiveM
  cliPqSchemeM cliRunStdSMM cliStepLocalSMM)
open CryptoVerification.SignalSession (CliRun Inputs)
open Computational.Proofs.LibsignalCli.Oom.Faithful (LogM)

/-- Every logged input avoids `bad`. -/
@[expose] def GoodLog (bad : Inputs → Prop) (w : List Inputs) : Prop :=
  ∀ i ∈ w, ¬ bad i

theorem goodLog_append_iff (bad : Inputs → Prop) (w₁ w₂ : List Inputs) :
    GoodLog bad (w₁ ++ w₂) ↔ GoodLog bad w₁ ∧ GoodLog bad w₂ :=
  List.forall_mem_append

private def AgreeW (bad : Inputs → Prop) {α : Type} (m₁ m₂ : LogM α) : Prop :=
  ∀ p : α × List Inputs → Prop,
    Pr{let z ← m₁.run}[p z ∧ GoodLog bad z.2] =
      Pr{let z ← m₂.run}[p z ∧ GoodLog bad z.2]

private theorem AgreeW.refl {bad : Inputs → Prop} {α : Type} (m : LogM α) : AgreeW bad m m :=
  fun _ => rfl

private theorem AgreeW.map {bad : Inputs → Prop} {α β : Type} (f : α → β) {m₁ m₂ : LogM α}
    (hm : AgreeW bad m₁ m₂) : AgreeW bad (f <$> m₁) (f <$> m₂) := by
  intro p
  simp only [WriterT.run_map, prEvent_map]
  exact hm fun x => p (f x.1, x.2)

private theorem AgreeW.ite {bad : Inputs → Prop} {α : Type} {c : Prop} [Decidable c]
    {t₁ t₂ e₁ e₂ : LogM α} (ht : AgreeW bad t₁ t₂) (he : AgreeW bad e₁ e₂) :
    AgreeW bad (if c then t₁ else e₁) (if c then t₂ else e₂) := by
  split_ifs <;> assumption

private theorem cliRunLogged_run (r : CliRun) (i : Inputs) :
    (cliRunLogged r i).run = pure (r i, [i]) := by
  simp [cliRunLogged, MonadWriter.tell]

private theorem AgreeW.cliRunLogged {bad : Inputs → Prop} {run run₀ : CliRun}
    (hrun : ∀ i, ¬ bad i → run i = run₀ i) (i : Inputs) :
    AgreeW bad (cliRunLogged run i) (cliRunLogged run₀ i) := by
  intro p
  by_cases hi : bad i
  · rw [cliRunLogged_run, cliRunLogged_run]
    rw [prEvent_eq_zero_of_forall_mem_support _ _ (by
          intro z hz ⟨_, hg⟩
          simp only [support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact hg i (List.mem_singleton.mpr rfl) hi),
      prEvent_eq_zero_of_forall_mem_support _ _ (by
          intro z hz ⟨_, hg⟩
          simp only [support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact hg i (List.mem_singleton.mpr rfl) hi)]
  · rw [cliRunLogged_run, cliRunLogged_run, hrun i hi]

private theorem AgreeW.bind {bad : Inputs → Prop} {α β : Type} {m₁ m₂ : LogM α}
    {k₁ k₂ : α → LogM β} (hm : AgreeW bad m₁ m₂) (hk : ∀ a, AgreeW bad (k₁ a) (k₂ a)) :
    AgreeW bad (m₁ >>= k₁) (m₂ >>= k₂) := by
  intro p
  simp only [WriterT.run_bind]
  let : MeasurableSpace (α × List Inputs) := ⊤
  let G : Set (α × List Inputs) := {x | GoodLog bad x.2}
  let F (k : α → LogM β) (x : α × List Inputs) : ℝ≥0∞ :=
    Pr{let z ← (fun (b, w₂) => (b, x.2 ++ w₂)) <$> (k x.1).run}[p z ∧ GoodLog bad z.2]
  have hF_eq (x : α × List Inputs) : F k₁ x = F k₂ x := by
    dsimp only [F]
    rw [prEvent_map, prEvent_map,
      prEvent_congr _ _ (fun y => (p (y.1, x.2 ++ y.2) ∧ GoodLog bad x.2) ∧ GoodLog bad y.2)
        (fun y => by rw [goodLog_append_iff]; tauto),
      prEvent_congr ((k₂ x.1).run) _
        (fun y => (p (y.1, x.2 ++ y.2) ∧ GoodLog bad x.2) ∧ GoodLog bad y.2)
        (fun y => by rw [goodLog_append_iff]; tauto)]
    exact hk x.1 (fun y => p (y.1, x.2 ++ y.2) ∧ GoodLog bad x.2)
  have hF_ind (k : α → LogM β) (x : α × List Inputs) : F k x = G.indicator (F k) x := by
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      dsimp only [F]
      rw [prEvent_map]
      exact prEvent_eq_zero_of_forall_not _ _ fun y ⟨_, hg⟩ =>
        hx ((goodLog_append_iff bad x.2 y.2).mp hg).1
  have hrestrict : 𝒟[m₁.run].restrict G = 𝒟[m₂.run].restrict G := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    change 𝒟[m₁.run] {z | z ∈ A ∧ GoodLog bad z.2} = 𝒟[m₂.run] {z | z ∈ A ∧ GoodLog bad z.2}
    rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete]
    exact hm (· ∈ A)
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  change ∫⁻ x, F k₁ x ∂𝒟[m₁.run] = ∫⁻ x, F k₂ x ∂𝒟[m₂.run]
  calc ∫⁻ x, F k₁ x ∂𝒟[m₁.run]
      = ∫⁻ x, G.indicator (F k₂) x ∂𝒟[m₁.run] :=
          lintegral_congr fun x => by rw [hF_eq x, ← hF_ind k₂ x]
    _ = ∫⁻ x, F k₂ x ∂(𝒟[m₁.run].restrict G) :=
          lintegral_indicator MeasurableSet.of_discrete _
    _ = ∫⁻ x, F k₂ x ∂(𝒟[m₂.run].restrict G) := by rw [hrestrict]
    _ = ∫⁻ x, G.indicator (F k₂) x ∂𝒟[m₂.run] :=
          (lintegral_indicator MeasurableSet.of_discrete _).symm
    _ = ∫⁻ x, F k₂ x ∂𝒟[m₂.run] :=
          lintegral_congr fun x => (hF_ind k₂ x).symm

private theorem AgreeW.bind_same {bad : Inputs → Prop} {α β : Type} (m : LogM α)
    {k₁ k₂ : α → LogM β} (hk : ∀ a, AgreeW bad (k₁ a) (k₂ a)) :
    AgreeW bad (m >>= k₁) (m >>= k₂) :=
  AgreeW.bind (AgreeW.refl m) hk

private def AgreeS1 (bad : Inputs → Prop) {σ α : Type} (m₁ m₂ : StateT σ LogM α) : Prop :=
  ∀ s, AgreeW bad (m₁.run s) (m₂.run s)

private theorem AgreeS1.refl {bad : Inputs → Prop} {σ α : Type} (m : StateT σ LogM α) :
    AgreeS1 bad m m :=
  fun _ => AgreeW.refl _

private theorem AgreeS1.map {bad : Inputs → Prop} {σ α β : Type} (f : α → β)
    {m₁ m₂ : StateT σ LogM α} (hm : AgreeS1 bad m₁ m₂) :
    AgreeS1 bad (f <$> m₁) (f <$> m₂) :=
  fun s => by simp only [StateT.run_map]; exact AgreeW.map _ (hm s)

private theorem AgreeS1.bind {bad : Inputs → Prop} {σ α β : Type}
    {m₁ m₂ : StateT σ LogM α} {k₁ k₂ : α → StateT σ LogM β}
    (hm : AgreeS1 bad m₁ m₂) (hk : ∀ a, AgreeS1 bad (k₁ a) (k₂ a)) :
    AgreeS1 bad (m₁ >>= k₁) (m₂ >>= k₂) :=
  fun s => by simp only [StateT.run_bind]; exact AgreeW.bind (hm s) fun x => hk x.1 x.2

private theorem AgreeS1.bind_same {bad : Inputs → Prop} {σ α β : Type}
    (m : StateT σ LogM α) {k₁ k₂ : α → StateT σ LogM β}
    (hk : ∀ a, AgreeS1 bad (k₁ a) (k₂ a)) :
    AgreeS1 bad (m >>= k₁) (m₂ := m >>= k₂) :=
  AgreeS1.bind (AgreeS1.refl m) hk

private theorem AgreeS1.lift {bad : Inputs → Prop} {σ α : Type} {m₁ m₂ : LogM α}
    (hm : AgreeW bad m₁ m₂) :
    AgreeS1 bad (StateT.lift m₁ : StateT σ LogM α) (StateT.lift m₂ : StateT σ LogM α) :=
  fun _ => by simp only [StateT.run_lift]; exact AgreeW.bind hm fun _ => AgreeW.refl _

private theorem AgreeS1.ite {bad : Inputs → Prop} {σ α : Type} {c : Prop} [Decidable c]
    {t₁ t₂ e₁ e₂ : StateT σ LogM α} (ht : AgreeS1 bad t₁ t₂) (he : AgreeS1 bad e₁ e₂) :
    AgreeS1 bad (if c then t₁ else e₁) (if c then t₂ else e₂) := by
  split_ifs <;> assumption

private def AgreeS2 (bad : Inputs → Prop) {σ₁ σ₂ α : Type}
    (m₁ m₂ : StateT σ₁ (StateT σ₂ LogM) α) : Prop :=
  ∀ s₁, AgreeS1 bad (m₁.run s₁) (m₂.run s₁)

private theorem AgreeS2.refl {bad : Inputs → Prop} {σ₁ σ₂ α : Type}
    (m : StateT σ₁ (StateT σ₂ LogM) α) : AgreeS2 bad m m :=
  fun _ => AgreeS1.refl _

private theorem AgreeS2.pure {bad : Inputs → Prop} {σ₁ σ₂ α : Type} (x : α) :
    AgreeS2 bad (pure x : StateT σ₁ (StateT σ₂ LogM) α) (pure x) :=
  AgreeS2.refl _

private theorem AgreeS2.bind {bad : Inputs → Prop} {σ₁ σ₂ α β : Type}
    {m₁ m₂ : StateT σ₁ (StateT σ₂ LogM) α}
    {k₁ k₂ : α → StateT σ₁ (StateT σ₂ LogM) β}
    (hm : AgreeS2 bad m₁ m₂) (hk : ∀ a, AgreeS2 bad (k₁ a) (k₂ a)) :
    AgreeS2 bad (m₁ >>= k₁) (m₂ >>= k₂) :=
  fun s₁ => by simp only [StateT.run_bind]; exact AgreeS1.bind (hm s₁) fun x => hk x.1 x.2

private theorem AgreeS2.bind_same {bad : Inputs → Prop} {σ₁ σ₂ α β : Type}
    (m : StateT σ₁ (StateT σ₂ LogM) α)
    {k₁ k₂ : α → StateT σ₁ (StateT σ₂ LogM) β}
    (hk : ∀ a, AgreeS2 bad (k₁ a) (k₂ a)) :
    AgreeS2 bad (m >>= k₁) (m >>= k₂) :=
  AgreeS2.bind (AgreeS2.refl m) hk

private theorem AgreeS2.lift {bad : Inputs → Prop} {σ₁ σ₂ α : Type} {m₁ m₂ : StateT σ₂ LogM α}
    (hm : AgreeS1 bad m₁ m₂) :
    AgreeS2 bad (StateT.lift m₁ : StateT σ₁ (StateT σ₂ LogM) α) (StateT.lift m₂) :=
  fun _ => by simp only [StateT.run_lift]; exact AgreeS1.bind hm fun _ => AgreeS1.refl _

private theorem AgreeS2.lift2 {bad : Inputs → Prop} {σ₁ σ₂ α : Type} {m₁ m₂ : LogM α}
    (hm : AgreeW bad m₁ m₂) :
    AgreeS2 bad (StateT.lift (StateT.lift m₁) : StateT σ₁ (StateT σ₂ LogM) α)
      (StateT.lift (StateT.lift m₂)) :=
  AgreeS2.lift (AgreeS1.lift hm)

private theorem AgreeS2.ite {bad : Inputs → Prop} {σ₁ σ₂ α : Type} {c : Prop} [Decidable c]
    {t₁ t₂ e₁ e₂ : StateT σ₁ (StateT σ₂ LogM) α}
    (ht : AgreeS2 bad t₁ t₂) (he : AgreeS2 bad e₁ e₂) :
    AgreeS2 bad (if c then t₁ else e₁) (if c then t₂ else e₂) := by
  split_ifs <;> assumption

private theorem AgreeS2.add {bad : Inputs → Prop} {ι₁ ι₂ σ₁ σ₂ : Type}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {h₁ g₁ : QueryImpl spec₁ (StateT σ₁ (StateT σ₂ LogM))}
    {h₂ g₂ : QueryImpl spec₂ (StateT σ₁ (StateT σ₂ LogM))}
    (hh₁ : ∀ q, AgreeS2 bad (h₁ q) (g₁ q)) (hh₂ : ∀ q, AgreeS2 bad (h₂ q) (g₂ q))
    (q : (spec₁ + spec₂).Domain) :
    AgreeS2 bad ((h₁ + h₂) q) ((g₁ + g₂) q) := by
  rcases q with q₁ | q₂
  · exact hh₁ q₁
  · exact hh₂ q₂


private theorem agreeW_cliPqReceiveM {bad : Inputs → Prop} {run run₀ : CliRun}
    (hrun : ∀ i, ¬ bad i → run i = run₀ i) (l : Nat)
    {S : SignalPqxdh.Setup} {l' : Nat} (bi : ModelDriverInstance S l')
    (s : CliPartyState) (c : List (BitVec 8)) (rc : BitVec 256) :
    AgreeW bad (cliPqReceiveM (cliRunLogged run) l bi s c rc)
      (cliPqReceiveM (cliRunLogged run₀) l bi s c rc) := by
  dsimp only [cliPqReceiveM]
  cases cliPqLenOk c with
  | false => exact AgreeW.refl _
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases s.bin.party with
    | A =>
      dsimp only
      split_ifs
      · exact AgreeW.refl _
      · exact AgreeW.map _ (AgreeW.map _ (AgreeW.cliRunLogged hrun _))
    | B =>
      dsimp only
      cases bhDecodePreKeyMsgE c with
      | none =>
        dsimp only
        split_ifs
        · exact AgreeW.refl _
        · exact AgreeW.map _ (AgreeW.map _ (AgreeW.cliRunLogged hrun _))
        · exact AgreeW.refl _
      | some _ =>
        dsimp only
        split_ifs
        · exact AgreeW.map _ (AgreeW.map _ (AgreeW.cliRunLogged hrun _))
        · exact AgreeW.refl _
        · exact AgreeW.map _ (AgreeW.map _ (AgreeW.cliRunLogged hrun _))
        · exact AgreeW.refl _

private theorem agreeS1_cliOracleImplRM {bad : Inputs → Prop} {Key St' St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (proj : St' → St)
    (sm₁ sm₂ : SMSchemeRM LogM Key St' Msg Coins RCoins C)
    (hsend : ∀ s m coins, AgreeW bad (sm₁.send s m coins) (sm₂.send s m coins))
    (hrecv : ∀ s c rc, AgreeW bad (sm₁.receive s c rc) (sm₂.receive s c rc))
    (Δ qep : ℕ) (cfg : ConfigR St' Msg C) (q : (CryptoGames.SM.spec St Msg Coins C).Domain) :
    AgreeS1 bad (cliOracleImplRM proj sm₁ Δ qep cfg q) (cliOracleImplRM proj sm₂ Δ qep cfg q) := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change AgreeS1 bad (transmitRM sm₁ Δ qep cfg (P, m, r)) (transmitRM sm₂ Δ qep cfg (P, m, r))
    unfold transmitRM
    refine AgreeS1.bind_same _ fun s => ?_
    cases cfg.sendOK s P with
    | false => exact AgreeS1.refl _
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases s.win with
      | true => exact AgreeS1.refl _
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine AgreeS1.bind_same _ fun ⟨coins, bf⟩ => ?_
        cases s.epMgmt Δ qep P bf with
        | none => exact AgreeS1.refl _
        | some s₁ => exact AgreeS1.bind (AgreeS1.lift (hsend _ _ _)) fun _ => AgreeS1.refl _
  · change AgreeS1 bad (challRM sm₁ Δ qep cfg (P, m₀, m₁, r)) (challRM sm₂ Δ qep cfg (P, m₀, m₁, r))
    unfold challRM
    refine AgreeS1.bind_same _ fun s => ?_
    cases cfg.sendOK s P with
    | false => exact AgreeS1.refl _
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases s.win with
      | true => exact AgreeS1.refl _
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine AgreeS1.bind_same _ fun ⟨coins, bf⟩ => ?_
        cases s.epMgmt Δ qep P bf with
        | none => exact AgreeS1.refl _
        | some s₁ =>
          dsimp only
          cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P))) with
          | true => exact AgreeS1.refl _
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact AgreeS1.bind (AgreeS1.lift (hsend _ _ _)) fun _ => AgreeS1.refl _
  · change AgreeS1 bad (deliverRM sm₁ cfg (P, c)) (deliverRM sm₂ cfg (P, c))
    unfold deliverRM
    refine AgreeS1.bind_same _ fun s => ?_
    cases s.win with
    | true => exact AgreeS1.refl _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases s.inTransit P.other c with
      | none => exact AgreeS1.refl _
      | some r =>
        dsimp only
        refine AgreeS1.bind_same _ fun rc => ?_
        exact AgreeS1.bind (AgreeS1.lift (hrecv _ _ _)) fun _ => AgreeS1.refl _
  · change AgreeS1 bad (injectRM sm₁ Δ qep cfg (P, c)) (injectRM sm₂ Δ qep cfg (P, c))
    unfold injectRM
    refine AgreeS1.bind_same _ fun s => ?_
    cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c)) with
    | true => exact AgreeS1.refl _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine AgreeS1.bind_same _ fun rc => ?_
      exact AgreeS1.bind (AgreeS1.lift (hrecv _ _ _)) fun _ => AgreeS1.refl _
  · exact AgreeS1.refl _

private theorem agreeS2_cliRunStdSMM {bad : Inputs → Prop} {run run₀ : CliRun}
    (hrun : ∀ i, ¬ bad i → run i = run₀ i) (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (qep : Nat) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S l) (i : Nat) (bi : ModelDriverInstance S l)
    (im : ModelDriverInstanceMeta S) (gs : GameState CliPartyState (Plain l) (List (BitVec 8)))
    (q : (cliGameSmSpec l (BitVec 512)).Domain) :
    AgreeS2 bad (cliRunStdSMM S l (cliRunLogged run) qep decT encT ds i bi im gs q)
      (cliRunStdSMM S l (cliRunLogged run₀) qep decT encT ds i bi im gs q) := by
  unfold cliRunStdSMM
  refine AgreeS2.bind (AgreeS2.lift2 ?_) fun _ => AgreeS2.refl _
  exact agreeS1_cliOracleImplRM CliPartyState.bin _ _
    (fun s m rs => AgreeW.map _ (AgreeW.cliRunLogged hrun _))
    (fun s c rc => agreeW_cliPqReceiveM hrun l bi s c rc)
    (2 + 1) qep _ q _

private theorem agreeS2_cliStepLocalSMM {bad : Inputs → Prop} {run run₀ : CliRun}
    (hrun : ∀ i, ¬ bad i → run i = run₀ i) (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (qep : Nat) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S l) (i : Nat) (bi : ModelDriverInstance S l)
    (im : ModelDriverInstanceMeta S) (gs : GameState CliPartyState (Plain l) (List (BitVec 8)))
    (q : (cliGameSmSpec l (BitVec 512)).Domain) :
    AgreeS2 bad (cliStepLocalSMM S l (cliRunLogged run) qep decT encT ds i bi im gs q)
      (cliStepLocalSMM S l (cliRunLogged run₀) qep decT encT ds i bi im gs q) := by
  rcases q with (((q₁ | q₂) | ⟨p, c⟩) | ⟨p, c⟩) | q₅
  · exact agreeS2_cliRunStdSMM hrun S l qep decT encT ds i bi im gs _
  · exact agreeS2_cliRunStdSMM hrun S l qep decT encT ds i bi im gs _
  · cases p
    · exact AgreeS2.ite (AgreeS2.pure _)
        (agreeS2_cliRunStdSMM hrun S l qep decT encT ds i bi im gs _)
    · exact AgreeS2.ite (AgreeS2.pure _)
        (agreeS2_cliRunStdSMM hrun S l qep decT encT ds i bi im gs _)
  · cases p
    · exact AgreeS2.ite (AgreeS2.pure _)
        (agreeS2_cliRunStdSMM hrun S l qep decT encT ds i bi im gs _)
    · exact AgreeS2.ite (AgreeS2.pure _)
        (AgreeS2.ite (AgreeS2.pure _)
          (agreeS2_cliRunStdSMM hrun S l qep decT encT ds i bi im gs _))
  · exact agreeS2_cliRunStdSMM hrun S l qep decT encT ds i bi im gs _

private theorem agreeS2_cliDrvStartM {bad : Inputs → Prop} {run run₀ : CliRun}
    (hrun : ∀ i, ¬ bad i → run i = run₀ i) (S : SignalPqxdh.Setup) (l : Nat)
    (P : SignalPqxdh.Primitives) (W : PEParams) (mode : BHDrvMode S)
    (sid : SignalPqxdh.SessionId S) :
    AgreeS2 bad (cliDrvStartM S l P (cliRunLogged run) W mode sid)
      (cliDrvStartM S l P (cliRunLogged run₀) W mode sid) := by
  unfold cliDrvStartM
  refine AgreeS2.bind_same _ fun ds => ?_
  cases bhDrvGuard ds.toModelDriverState sid with
  | none => exact AgreeS2.pure _
  | some g =>
    rcases g with ⟨hdr, bnd, u_resp, j_resp⟩
    dsimp only
    refine AgreeS2.bind_same _ fun st0 => ?_
    refine AgreeS2.bind_same _ fun r1 => ?_
    rcases r1 with ⟨resp1, st1⟩
    cases resp1 <;> try (dsimp only; with_reducible exact AgreeS2.pure _)
    dsimp only
    refine AgreeS2.bind_same _ fun r2 => ?_
    rcases r2 with ⟨resp2, st⟩
    cases resp2 <;> try (dsimp only; with_reducible exact AgreeS2.pure _)
    dsimp only
    refine AgreeS2.bind_same _ fun t_dr => ?_
    cases ds.initTapes.find? (fun (s, _, _, _) => s == sid) with
    | none => exact AgreeS2.pure _
    | some it =>
      rcases it with ⟨_, u_init, _, t_init⟩
      dsimp only
      cases st.principals.find? (fun (idx, _) => idx == u_init.val) with
      | none => exact AgreeS2.pure _
      | some ip =>
        rcases ip with ⟨_, initPrinEntry⟩
        dsimp only
        cases st.principals.find? (fun (idx, _) => idx == u_resp.val) with
        | none => exact AgreeS2.pure _
        | some rp =>
          rcases rp with ⟨_, respPrinEntry⟩
          dsimp only
          cases st.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) with
          | none => exact AgreeS2.pure _
          | some spk =>
            rcases spk with ⟨_, respSpkEntry⟩
            dsimp only
            cases hdr.opkId? with
            | none =>
              dsimp only
              refine AgreeS2.bind_same _ fun opkSk? => ?_
              cases opkSk? with
              | none => exact AgreeS2.pure _
              | some opkOpt =>
                dsimp only
                cases mkMeEStrict u_init.val initPrinEntry.secIKA0 with
                | none => exact AgreeS2.pure _
                | some meA =>
                  dsimp only
                  cases mkMeEStrict u_resp.val respPrinEntry.secIKA0 with
                  | none => exact AgreeS2.pure _
                  | some meB =>
                    dsimp only
                    cases mkKeysEStrict j_resp.val respSpkEntry opkOpt with
                    | none => exact AgreeS2.pure _
                    | some keysB =>
                      dsimp only
                      cases mkBundleEStrict u_resp.val bnd with
                      | none => exact AgreeS2.pure _
                      | some bundleE =>
                        dsimp only
                        refine AgreeS2.bind (AgreeS2.lift2 (AgreeW.map _ (AgreeW.cliRunLogged hrun _)))
                          fun stA0? => ?_
                        cases stA0? with
                        | none => exact AgreeS2.pure _
                        | some stA0 =>
                          dsimp only [SMSchemeRM.initState, cliPqSchemeM]
                          exact AgreeS2.refl _
            | some opkId =>
              dsimp only
              cases st.opkEntries.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val, opkId.toNat)) with
              | none => simp only [pure_bind]; exact AgreeS2.pure _
              | some entry =>
                rcases entry with ⟨_, oe⟩
                dsimp only
                refine AgreeS2.bind_same _ fun opkSk? => ?_
                cases opkSk? with
                | none => exact AgreeS2.pure _
                | some opkOpt =>
                  dsimp only
                  cases mkMeEStrict u_init.val initPrinEntry.secIKA0 with
                  | none => exact AgreeS2.pure _
                  | some meA =>
                    dsimp only
                    cases mkMeEStrict u_resp.val respPrinEntry.secIKA0 with
                    | none => exact AgreeS2.pure _
                    | some meB =>
                      dsimp only
                      cases mkKeysEStrict j_resp.val respSpkEntry opkOpt with
                      | none => exact AgreeS2.pure _
                      | some keysB =>
                        dsimp only
                        cases mkBundleEStrict u_resp.val bnd with
                        | none => exact AgreeS2.pure _
                        | some bundleE =>
                          dsimp only
                          refine AgreeS2.bind (AgreeS2.lift2 (AgreeW.map _ (AgreeW.cliRunLogged hrun _)))
                            fun stA0? => ?_
                          cases stA0? with
                          | none => exact AgreeS2.pure _
                          | some stA0 =>
                            dsimp only [SMSchemeRM.initState, cliPqSchemeM]
                            exact AgreeS2.refl _

private theorem cliDrvImplM_agree {bad : Inputs → Prop} {run run₀ : CliRun}
    (hrun : ∀ i, ¬ bad i → run i = run₀ i) (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (P : SignalPqxdh.Primitives) (W : PEParams) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec l (BitVec 512)) (CliDrvMT S l LogM)) (mode : BHDrvMode S)
    (t : (cliGameSpec S l (BitVec 512)).Domain) :
    AgreeS2 bad (cliDrvImplM S l P (cliRunLogged run) W qep decT encT ext mode t)
      (cliDrvImplM S l P (cliRunLogged run₀) W qep decT encT ext mode t) := by
  refine AgreeS2.add (AgreeS2.add (AgreeS2.add (fun _ => AgreeS2.refl _) (fun _ => AgreeS2.refl _)) ?_) ?_ t
  · intro q
    cases q with
    | startDR sid => exact agreeS2_cliDrvStartM hrun S l P W mode sid
  · intro ⟨i, sq⟩
    dsimp only [cliDrvSMM]
    refine AgreeS2.bind_same _ fun ds => ?_
    refine AgreeS2.ite (AgreeS2.pure _) ?_
    cases ds.bhInsts[i]? with
    | none => exact AgreeS2.pure _
    | some bi =>
      cases ds.instMeta[i]? with
      | none => exact AgreeS2.pure _
      | some im =>
        dsimp only
        refine AgreeS2.ite (AgreeS2.refl _) ?_
        cases ds.instGs[i]? with
        | none => exact AgreeS2.refl _
        | some gsOpt =>
          cases gsOpt with
          | none => exact AgreeS2.refl _
          | some gs => exact agreeS2_cliStepLocalSMM hrun S l qep decT encT ds i bi im gs sq

private theorem AgreeS2.simulateQ {bad : Inputs → Prop} {ι σ₁ σ₂ : Type} {spec : OracleSpec ι}
    (impl₁ impl₂ : QueryImpl spec (StateT σ₁ (StateT σ₂ LogM)))
    (himpl : ∀ t, AgreeS2 bad (impl₁ t) (impl₂ t)) {α : Type}
    (oa : OracleComp spec α) :
    AgreeS2 bad (simulateQ impl₁ oa) (simulateQ impl₂ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure _ => exact AgreeS2.refl _
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query]
    exact AgreeS2.bind (himpl t) ih

/-- `cliPqxdhExpFlagged` agrees on every `GoodLog bad` event when `run` and `run₀` agree off `bad`. -/
theorem cliPqxdhExpFlagged_agree (S : SignalPqxdh.Setup) {run run₀ : CliRun}
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512)) {bad : Inputs → Prop}
    (hrun : ∀ i, ¬ bad i → run i = run₀ i) (p : Bool × List Inputs → Prop) :
    Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[p z ∧ GoodLog bad z.2] =
      Pr{let z ← cliPqxdhExpFlagged S run₀ X W l qep decT encT A}[p z ∧ GoodLog bad z.2] := by
  unfold cliPqxdhExpFlagged runCliDriverLogged
  refine AgreeW.bind_same _ (fun b => ?_) p
  exact AgreeW.bind
    (AgreeS2.simulateQ _ _
      (cliDrvImplM_agree hrun S l (modelPrims X W) W qep decT encT
        (liftQueryImplStateT2 (n := LogM) bhNoExtWithSpqr) (fun _ _ _ _ _ => some b))
      A.run {} (SignalPqxdh.KeyIndState.empty S true))
    (fun _ => AgreeW.refl _)

end Computational.Proofs.LibsignalCli.Oom.Agree
