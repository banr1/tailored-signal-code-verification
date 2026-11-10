/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPqOomGame
import Computational.Proofs.SpecLemmas.Game.StatementPq
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.EvalDist.Monad.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Forgetting the `WriterT` Log of `cliPqxdhExpFlagged`

**Checked by Lean.** Proves `cli_pq_exp_b_faithful_proof : CliPqxdhExpFlaggedFaithful`, showing
that projecting away the `WriterT (List Inputs)` log of `cliPqxdhExpFlagged` yields `cliPqExp`.
-/

namespace Computational.Proofs.LibsignalCli.Oom.Faithful

open OracleComp OracleSpec
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.SM (ConfigR GameState)
open CryptoVerification.E2E (BHDrvM BHDrvMode BinState CliDriverState CliDrvM CliDrvMT
  CliGameAdversary CliPartyState CliPqxdhExpFlaggedFaithful ModelDriverInstance
  ModelDriverInstanceMeta PEParams SMSchemeRM UnreachedPqxdhPrimitives allTestedSessionsFresh
  appendInitiateTape bhDecodePreKeyMsgE bhDrCtlSpec bhDrvGuard bhDrvInstClean bhDrvKeyInd bhIdKeyOf
  bhNoExtWithSpqr bhPartneredInTransitA bhPartneredInnerBytes bhLiftCli bhLiftCliM challRM
  cliGameDrSpec cliGameSmSpec cliGameSpec cliMapGameState cliOracleImplRM cliPartyStateB0
  cliPqLenOk cliPqSigsOf cliPqxdhExpFlagged cliRunLogged cliRunPure deliverRM
  driverSomeInstanceWon injectRM liftQueryImplStateT2 liftStateT mkBundleEStrict mkKeysEStrict
  mkMeEStrict modelPrims runCliDriverLogged transmitRM)
open CryptoVerification.E2E.Dir (cliDrvImpl cliDrvImplM cliDrvSM cliDrvSMM cliDrvStart
  cliDrvStartM cliPqInitM cliPqReceiveM cliPqRecvM cliPqSchemeM cliPqSendM cliRunStdSM
  cliRunStdSMM cliStepLocalSM cliStepLocalSMM runCliDriver)
open CryptoVerification.SignalSession (CliRun Inputs)

instance instLawfulMonadWriterTList {α : Type} {M : Type → Type} [Monad M] [LawfulMonad M] :
    LawfulMonad (WriterT (List α) M) :=
  LawfulMonad.mk'
    (id_map := fun _ => by ext; simp)
    (pure_bind := fun _ _ => by ext; simp)
    (bind_assoc := fun _ _ _ => by ext; simp)
    (bind_pure_comp := fun _ _ => by ext; simp)

/-- The `WriterT` logging monad of `StatementPqOomGame.lean`. -/
abbrev LogM := WriterT (List Inputs) ProbComp

def forgetW {α : Type} (m : LogM α) : ProbComp α :=
  Prod.fst <$> m.run

@[simp] theorem forgetW_pure {α : Type} (a : α) : forgetW (pure a) = pure a := by
  simp [forgetW]

@[simp] theorem forgetW_map {α β : Type} (f : α → β) (m : LogM α) :
    forgetW (f <$> m) = f <$> forgetW m := by
  simp [forgetW, Functor.map_map]

@[simp] theorem forgetW_bind {α β : Type} (m : LogM α) (k : α → LogM β) :
    forgetW (m >>= k) = forgetW m >>= fun a => forgetW (k a) := by
  simp [forgetW, map_eq_bind_pure_comp, bind_assoc]

@[simp] theorem forgetW_liftM {α : Type} (c : ProbComp α) :
    forgetW (liftM c) = c := by
  dsimp [forgetW, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp [Functor.map_map]

@[simp] theorem forgetW_ite {α : Type} (c : Prop) [Decidable c] (t e : LogM α) :
    forgetW (if c then t else e) = if c then forgetW t else forgetW e := by
  split_ifs <;> rfl

@[simp] theorem forgetW_cliRunLogged (run : CliRun) (i : Inputs) :
    forgetW (cliRunLogged run i) = cliRunPure run i := by
  simp [forgetW, cliRunLogged, cliRunPure]

def forgetS1 {σ α : Type} (m : StateT σ LogM α) : StateT σ ProbComp α :=
  fun s => forgetW (m.run s)

@[simp] theorem forgetS1_run {σ α : Type} (m : StateT σ LogM α) (s : σ) :
    (forgetS1 m).run s = forgetW (m.run s) := rfl

@[simp] theorem forgetS1_pure {σ α : Type} (a : α) :
    forgetS1 (pure a : StateT σ LogM α) = pure a := by
  ext s; simp

@[simp] theorem forgetS1_bind {σ α β : Type} (m : StateT σ LogM α) (k : α → StateT σ LogM β) :
    forgetS1 (m >>= k) = forgetS1 m >>= fun a => forgetS1 (k a) := by
  ext s; simp

@[simp] theorem forgetS1_map {σ α β : Type} (f : α → β) (m : StateT σ LogM α) :
    forgetS1 (f <$> m) = f <$> forgetS1 m := by
  ext s; simp

@[simp] theorem forgetS1_get {σ : Type} :
    forgetS1 (get : StateT σ LogM σ) = get := by
  ext s; simp

@[simp] theorem forgetS1_set {σ : Type} (s' : σ) :
    forgetS1 (set s' : StateT σ LogM PUnit) = set s' := by
  ext s; simp

@[simp] theorem forgetS1_lift {σ α : Type} (m : LogM α) :
    forgetS1 (StateT.lift m : StateT σ LogM α) = StateT.lift (forgetW m) := by
  ext s; simp [StateT.run_lift]

@[simp] theorem forgetS1_liftM_prob {σ α : Type} (c : ProbComp α) :
    forgetS1 (liftM c : StateT σ LogM α) = liftM c := by
  ext s
  change forgetW ((StateT.lift (liftM c : LogM α)).run s) = (StateT.lift c).run s
  simp [StateT.run_lift]

@[simp] theorem forgetS1_liftStateT {σ α : Type} (x : StateT σ ProbComp α) :
    forgetS1 (liftStateT (n := LogM) x) = x := by
  ext s; exact forgetW_liftM (x s)

@[simp] theorem forgetS1_ite {σ α : Type} (c : Prop) [Decidable c]
    (t e : StateT σ LogM α) :
    forgetS1 (if c then t else e) = if c then forgetS1 t else forgetS1 e := by
  split_ifs <;> rfl

def forgetS2 {σ₁ σ₂ α : Type} (m : StateT σ₁ (StateT σ₂ LogM) α) :
    StateT σ₁ (StateT σ₂ ProbComp) α :=
  fun s₁ => forgetS1 (m.run s₁)

@[simp] theorem forgetS2_run {σ₁ σ₂ α : Type} (m : StateT σ₁ (StateT σ₂ LogM) α) (s₁ : σ₁) :
    (forgetS2 m).run s₁ = forgetS1 (m.run s₁) := rfl

@[simp] theorem forgetS2_pure {σ₁ σ₂ α : Type} (a : α) :
    forgetS2 (pure a : StateT σ₁ (StateT σ₂ LogM) α) = pure a := by
  ext s₁ s₂; simp

@[simp] theorem forgetS2_bind {σ₁ σ₂ α β : Type}
    (m : StateT σ₁ (StateT σ₂ LogM) α) (k : α → StateT σ₁ (StateT σ₂ LogM) β) :
    forgetS2 (m >>= k) = forgetS2 m >>= fun a => forgetS2 (k a) := by
  ext s₁ s₂; simp

@[simp] theorem forgetS2_map {σ₁ σ₂ α β : Type} (f : α → β)
    (m : StateT σ₁ (StateT σ₂ LogM) α) :
    forgetS2 (f <$> m) = f <$> forgetS2 m := by
  ext s₁ s₂; simp

@[simp] theorem forgetS2_get {σ₁ σ₂ : Type} :
    forgetS2 (get : StateT σ₁ (StateT σ₂ LogM) σ₁) = get := by
  ext s₁ s₂; simp

@[simp] theorem forgetS2_set {σ₁ σ₂ : Type} (s₁' : σ₁) :
    forgetS2 (set s₁' : StateT σ₁ (StateT σ₂ LogM) PUnit) = set s₁' := by
  ext s₁ s₂; simp

@[simp] theorem forgetS2_lift {σ₁ σ₂ α : Type} (m : StateT σ₂ LogM α) :
    forgetS2 (StateT.lift m : StateT σ₁ (StateT σ₂ LogM) α) = StateT.lift (forgetS1 m) := by
  ext s₁ s₂; simp [StateT.run_lift]

@[simp] theorem forgetS2_liftM_prob {σ₁ σ₂ α : Type} (c : ProbComp α) :
    forgetS2 (liftM c : StateT σ₁ (StateT σ₂ LogM) α) = liftM c := by
  change forgetS2 (StateT.lift (liftM c)) = StateT.lift (liftM c)
  rw [forgetS2_lift, forgetS1_liftM_prob]

@[simp] theorem forgetS2_liftQueryImplStateT2 {ι σ₁ σ₂ : Type} {spec : OracleSpec ι}
    (h : QueryImpl spec (StateT σ₁ (StateT σ₂ ProbComp))) (q : spec.Domain) :
    forgetS2 (liftQueryImplStateT2 (n := LogM) h q) = h q := by
  ext s₁ s₂; exact forgetW_liftM (((h q).run s₁).run s₂)

@[simp] theorem forgetS2_bhLiftCliM {S : SignalPqxdh.Setup} {l : Nat} {α : Type}
    (m : BHDrvM S l α) :
    forgetS2 (bhLiftCliM (M := LogM) m) = bhLiftCli m := by
  unfold bhLiftCliM bhLiftCli
  simp only [forgetS2_bind, forgetS2_get]
  congr 1; funext cds
  simp only [forgetS2_lift, forgetS1_liftStateT]
  rfl

@[simp] theorem forgetS2_ite {σ₁ σ₂ α : Type} (c : Prop) [Decidable c]
    (t e : StateT σ₁ (StateT σ₂ LogM) α) :
    forgetS2 (if c then t else e) = if c then forgetS2 t else forgetS2 e := by
  split_ifs <;> rfl

theorem forgetS2_add {ι₁ ι₂ σ₁ σ₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {h₁ : QueryImpl spec₁ (StateT σ₁ (StateT σ₂ LogM))}
    {h₂ : QueryImpl spec₂ (StateT σ₁ (StateT σ₂ LogM))}
    {g₁ : QueryImpl spec₁ (StateT σ₁ (StateT σ₂ ProbComp))}
    {g₂ : QueryImpl spec₂ (StateT σ₁ (StateT σ₂ ProbComp))}
    (hh₁ : ∀ q, forgetS2 (h₁ q) = g₁ q) (hh₂ : ∀ q, forgetS2 (h₂ q) = g₂ q)
    (q : (spec₁ + spec₂).Domain) :
    forgetS2 ((h₁ + h₂) q) = (g₁ + g₂) q := by
  rcases q with q₁ | q₂
  · exact hh₁ q₁
  · exact hh₂ q₂

private theorem forgetW_cliPqReceiveM (run : CliRun) (l : Nat)
    {S : SignalPqxdh.Setup} {l' : Nat} (bi : ModelDriverInstance S l')
    (s : CliPartyState) (c : List (BitVec 8)) (rc : BitVec 256) :
    forgetW (cliPqReceiveM (cliRunLogged run) l bi s c rc) =
      cliPqReceiveM (cliRunPure run) l bi s c rc := by
  dsimp only [cliPqReceiveM]
  cases cliPqLenOk c with
  | false => simp
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases s.bin.party with
    | A =>
      dsimp only
      split_ifs <;> simp [cliPqRecvM]
    | B =>
      dsimp only
      cases bhDecodePreKeyMsgE c with
      | none =>
        dsimp only
        split_ifs <;> simp [cliPqRecvM]
      | some _ =>
        dsimp only
        split_ifs <;> simp [cliPqRecvM]

private theorem forgetS1_transmitRM {Key St Msg Coins RCoins C : Type} [SampleableType Coins]
    (sm₁ : SMSchemeRM LogM Key St Msg Coins RCoins C)
    (sm₂ : SMSchemeRM ProbComp Key St Msg Coins RCoins C)
    (hsend : ∀ s m coins, forgetW (sm₁.send s m coins) = sm₂.send s m coins)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (q : Party × Msg × Option Coins) :
    forgetS1 (transmitRM sm₁ Δ qep cfg q) = transmitRM sm₂ Δ qep cfg q := by
  rcases q with ⟨P, m, r⟩
  unfold transmitRM
  simp only [forgetS1_bind, forgetS1_get]
  congr 1; funext s
  cases cfg.sendOK s P
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases s.win
    · simp only [Bool.false_eq_true, ↓reduceIte, forgetS1_bind, forgetS1_lift, forgetW_liftM]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact forgetS1_pure _
      | some s₁ => simp [hsend]
    · simp

private theorem forgetS1_challRM {Key St Msg Coins RCoins C : Type} [SampleableType Coins]
    (sm₁ : SMSchemeRM LogM Key St Msg Coins RCoins C)
    (sm₂ : SMSchemeRM ProbComp Key St Msg Coins RCoins C)
    (hsend : ∀ s m coins, forgetW (sm₁.send s m coins) = sm₂.send s m coins)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (q : Party × Msg × Msg × Option Coins) :
    forgetS1 (challRM sm₁ Δ qep cfg q) = challRM sm₂ Δ qep cfg q := by
  rcases q with ⟨P, m₀, m₁, r⟩
  unfold challRM
  simp only [forgetS1_bind, forgetS1_get]
  congr 1; funext s
  cases cfg.sendOK s P
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases s.win
    · simp only [Bool.false_eq_true, ↓reduceIte, forgetS1_bind, forgetS1_lift, forgetW_liftM]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact forgetS1_pure _
      | some s₁ =>
        dsimp only
        cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
        · simp [hsend]
        · simp
    · simp

private theorem forgetS1_deliverRM {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (sm₁ : SMSchemeRM LogM Key St Msg Coins RCoins C)
    (sm₂ : SMSchemeRM ProbComp Key St Msg Coins RCoins C)
    (hrecv : ∀ s c rc, forgetW (sm₁.receive s c rc) = sm₂.receive s c rc)
    (cfg : ConfigR St Msg C) (q : Party × C) :
    forgetS1 (deliverRM sm₁ cfg q) = deliverRM sm₂ cfg q := by
  rcases q with ⟨P, c⟩
  unfold deliverRM
  simp only [forgetS1_bind, forgetS1_get]
  congr 1; funext s
  cases s.win
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases s.inTransit P.other c with
    | none => exact forgetS1_pure _
    | some r =>
      dsimp only
      simp only [forgetS1_bind, forgetS1_lift, forgetW_liftM]
      congr 1; funext rc
      rw [hrecv]
      congr 1; funext out
      cases out with
      | none => split_ifs <;> simp
      | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · simp

private theorem forgetS1_injectRM {Key St Msg Coins RCoins C : Type}
    [DecidableEq C] [SampleableType RCoins]
    (sm₁ : SMSchemeRM LogM Key St Msg Coins RCoins C)
    (sm₂ : SMSchemeRM ProbComp Key St Msg Coins RCoins C)
    (hrecv : ∀ s c rc, forgetW (sm₁.receive s c rc) = sm₂.receive s c rc)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (q : Party × C) :
    forgetS1 (injectRM sm₁ Δ qep cfg q) = injectRM sm₂ Δ qep cfg q := by
  rcases q with ⟨P, c⟩
  unfold injectRM
  simp only [forgetS1_bind, forgetS1_get]
  congr 1; funext s
  cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c))
  · simp only [Bool.false_eq_true, ↓reduceIte, forgetS1_bind, forgetS1_lift, forgetW_liftM]
    congr 1; funext rc
    rw [hrecv]
    congr 1; funext out
    cases out with
    | none => exact forgetS1_pure _
    | some x =>
      rcases x with ⟨st', t', i', m'⟩
      dsimp only
      split_ifs <;> simp
  · simp

private theorem forgetS1_cliOracleImplRM_cliPqSchemeM (run : CliRun) (l : Nat)
    {S : SignalPqxdh.Setup} {l' : Nat} (bi : ModelDriverInstance S l')
    (stA0 stB0 : CliPartyState)
    (Δ qep : ℕ) (cfg : ConfigR CliPartyState (Plain l) (List (BitVec 8)))
    (q : (CryptoGames.SM.spec BinState (Plain l) (BitVec 512) (List (BitVec 8))).Domain) :
    forgetS1 (cliOracleImplRM CliPartyState.bin
        (cliPqSchemeM (cliRunLogged run) l bi stA0 stB0) Δ qep cfg q) =
      cliOracleImplRM CliPartyState.bin
        (cliPqSchemeM (cliRunPure run) l bi stA0 stB0) Δ qep cfg q := by
  have hsend : ∀ s (m : Plain l) rs,
      forgetW ((cliPqSchemeM (cliRunLogged run) l bi stA0 stB0).send s m rs) =
        (cliPqSchemeM (cliRunPure run) l bi stA0 stB0).send s m rs := by
    intro s m rs; simp [cliPqSchemeM, cliPqSendM]
  have hrecv : ∀ s c rc,
      forgetW ((cliPqSchemeM (cliRunLogged run) l bi stA0 stB0).receive s c rc) =
        (cliPqSchemeM (cliRunPure run) l bi stA0 stB0).receive s c rc :=
    fun s c rc => forgetW_cliPqReceiveM run l bi s c rc
  rcases q with (((q₁ | q₂) | q₃) | q₄) | q₅
  · exact forgetS1_transmitRM _ _ hsend Δ qep cfg q₁
  · exact forgetS1_challRM _ _ hsend Δ qep cfg q₂
  · exact forgetS1_deliverRM _ _ hrecv cfg q₃
  · exact forgetS1_injectRM _ _ hrecv Δ qep cfg q₄
  · exact forgetS1_liftStateT _

private theorem forgetS2_cliRunStdSMM (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (run : CliRun) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S l) (i : Nat) (bi : ModelDriverInstance S l)
    (im : ModelDriverInstanceMeta S) (gs : GameState CliPartyState (Plain l) (List (BitVec 8)))
    (q : (cliGameSmSpec l (BitVec 512)).Domain) :
    forgetS2 (cliRunStdSMM S l (cliRunLogged run) qep decT encT ds i bi im gs q) =
      cliRunStdSMM S l (cliRunPure run) qep decT encT ds i bi im gs q := by
  unfold cliRunStdSMM
  simp only [forgetS2_bind, forgetS2_lift, forgetS1_lift, ← forgetS1_run,
    forgetS1_cliOracleImplRM_cliPqSchemeM]
  congr 1

private theorem forgetS2_cliStepLocalSMM (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (run : CliRun) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S l) (i : Nat) (bi : ModelDriverInstance S l)
    (im : ModelDriverInstanceMeta S) (gs : GameState CliPartyState (Plain l) (List (BitVec 8)))
    (q : (cliGameSmSpec l (BitVec 512)).Domain) :
    forgetS2 (cliStepLocalSMM S l (cliRunLogged run) qep decT encT ds i bi im gs q) =
      cliStepLocalSM S l run qep decT encT ds i bi im gs q := by
  change forgetS2 (cliStepLocalSMM S l (cliRunLogged run) qep decT encT ds i bi im gs q) =
    cliStepLocalSMM S l (cliRunPure run) qep decT encT ds i bi im gs q
  rcases q with (((q₁ | q₂) | ⟨p, c⟩) | ⟨p, c⟩) | q₅
  · exact forgetS2_cliRunStdSMM S l run qep decT encT ds i bi im gs _
  · exact forgetS2_cliRunStdSMM S l run qep decT encT ds i bi im gs _
  · cases p <;> dsimp only [cliStepLocalSMM] <;> split_ifs <;>
      first | exact forgetS2_pure _ | exact forgetS2_cliRunStdSMM S l run qep decT encT ds i bi im gs _
  · cases p <;> dsimp only [cliStepLocalSMM] <;> split_ifs <;>
      first | exact forgetS2_pure _ | exact forgetS2_cliRunStdSMM S l run qep decT encT ds i bi im gs _
  · exact forgetS2_cliRunStdSMM S l run qep decT encT ds i bi im gs _

private theorem forgetS2_cliDrvSMM (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (run : CliRun) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec l (BitVec 512)) (CliDrvM S l))
    (q : (cliGameDrSpec l (BitVec 512)).Domain) :
    forgetS2 (cliDrvSMM S l (cliRunLogged run) qep decT encT
        (liftQueryImplStateT2 (n := LogM) ext) q) =
      cliDrvSM S l run qep decT encT ext q := by
  rcases q with ⟨i, sq⟩
  unfold cliDrvSM
  dsimp only [cliDrvSMM]
  simp only [forgetS2_bind, forgetS2_get]
  congr 1; funext ds
  split_ifs
  · exact forgetS2_pure _
  · cases ds.bhInsts[i]? with
    | none => exact forgetS2_pure _
    | some bi =>
      cases ds.instMeta[i]? with
      | none => exact forgetS2_pure _
      | some im =>
        dsimp only
        split_ifs
        · simp
        · cases ds.instGs[i]? with
          | none => simp
          | some gsOpt =>
            cases gsOpt with
            | none => simp
            | some gs => exact forgetS2_cliStepLocalSMM S l run qep decT encT ds i bi im gs sq

private theorem forgetS2_cliDrvStartM (S : SignalPqxdh.Setup) (l : Nat) (P : SignalPqxdh.Primitives)
    (run : CliRun) (W : PEParams) (mode : BHDrvMode S) (sid : SignalPqxdh.SessionId S) :
    forgetS2 (cliDrvStartM S l P (cliRunLogged run) W mode sid) =
      cliDrvStart S l P run W mode sid := by
  unfold cliDrvStart cliDrvStartM
  simp only [forgetS2_bind, forgetS2_get]
  congr 1; funext ds
  cases bhDrvGuard ds.toModelDriverState sid with
  | none => exact forgetS2_pure _
  | some g =>
    rcases g with ⟨hdr, bnd, u_resp, j_resp⟩
    dsimp only
    simp only [forgetS2_bind, forgetS2_lift, forgetS1_get]
    congr 1; funext st0
    simp only [forgetS1_liftM_prob]
    congr 1; funext r1
    rcases r1 with ⟨resp1, st1⟩
    cases resp1 <;> try exact forgetS2_pure _
    dsimp only
    simp only [forgetS2_bind, forgetS2_lift, forgetS1_liftM_prob]
    congr 1; funext r2
    rcases r2 with ⟨resp2, st⟩
    cases resp2 <;> try exact forgetS2_pure _
    dsimp only
    simp only [forgetS2_bind, forgetS2_lift, forgetS1_liftM_prob]
    congr 1; funext t_dr
    cases ds.initTapes.find? (fun (s, _, _, _) => s == sid) with
    | none => exact forgetS2_pure _
    | some it =>
      rcases it with ⟨_, u_init, _, t_init⟩
      dsimp only
      cases st.principals.find? (fun (idx, _) => idx == u_init.val) with
      | none => exact forgetS2_pure _
      | some ip =>
        rcases ip with ⟨_, initPrinEntry⟩
        dsimp only
        cases st.principals.find? (fun (idx, _) => idx == u_resp.val) with
        | none => exact forgetS2_pure _
        | some rp =>
          rcases rp with ⟨_, respPrinEntry⟩
          dsimp only
          cases st.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) with
          | none => exact forgetS2_pure _
          | some spk =>
            rcases spk with ⟨_, respSpkEntry⟩
            dsimp only
            have htail : ∀ opkSk? : Option (Option (Nat × SignalPqxdh.Bytes)),
                forgetS2 ((do
                  let some opkOpt := opkSk? | return none
                  let some meA := mkMeEStrict u_init.val initPrinEntry.secIKA0 | return none
                  let some meB := mkMeEStrict u_resp.val respPrinEntry.secIKA0 | return none
                  let some keysB := mkKeysEStrict j_resp.val respSpkEntry opkOpt | return none
                  let some bundleE := mkBundleEStrict u_resp.val bnd | return none
                  let dA :=
                    { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB),
                      session := none, signed := [], oneTime := [], kyberOneTime := [],
                      kyberLastResort := [] }
                  let some stA0 ←
                    StateT.lift (StateT.lift (cliPqInitM (cliRunLogged run) W dA bundleE
                      (appendInitiateTape t_init t_dr)))
                    | return none
                  let stB0Bin : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
                  let bi0 : ModelDriverInstance S l :=
                    { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
                      meA := meA, meB := meB, keysB := keysB, stA0 := stA0.bin, stB0 := stB0Bin, gs := none }
                  let stB0 := cliPartyStateB0 W bi0 (cliPqSigsOf st bi0)
                  let scheme := cliPqSchemeM (cliRunLogged run) l bi0 stA0 stB0
                  let gsDir :=
                    (mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB ‹_›).map
                      (fun b => scheme.initState () b)
                  let gs := gsDir.map (cliMapGameState CliPartyState.bin)
                  let bi : ModelDriverInstance S l := { bi0 with gs := gs }
                  let im0 : ModelDriverInstanceMeta S :=
                    { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := bnd.opkB?.map Prod.fst }
                  StateT.lift (set st)
                  set { ds with bhInsts := ds.bhInsts ++ [bi], instMeta := ds.instMeta ++ [im0],
                                instGs := ds.instGs ++ [gsDir] }
                  return some ds.bhInsts.length) : CliDrvMT S l LogM (Option Nat)) = ((do
                  let some opkOpt := opkSk? | return none
                  let some meA := mkMeEStrict u_init.val initPrinEntry.secIKA0 | return none
                  let some meB := mkMeEStrict u_resp.val respPrinEntry.secIKA0 | return none
                  let some keysB := mkKeysEStrict j_resp.val respSpkEntry opkOpt | return none
                  let some bundleE := mkBundleEStrict u_resp.val bnd | return none
                  let dA :=
                    { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB),
                      session := none, signed := [], oneTime := [], kyberOneTime := [],
                      kyberLastResort := [] }
                  let some stA0 ←
                    StateT.lift (StateT.lift (cliPqInitM (cliRunPure run) W dA bundleE
                      (appendInitiateTape t_init t_dr)))
                    | return none
                  let stB0Bin : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
                  let bi0 : ModelDriverInstance S l :=
                    { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
                      meA := meA, meB := meB, keysB := keysB, stA0 := stA0.bin, stB0 := stB0Bin, gs := none }
                  let stB0 := cliPartyStateB0 W bi0 (cliPqSigsOf st bi0)
                  let scheme := cliPqSchemeM (cliRunPure run) l bi0 stA0 stB0
                  let gsDir :=
                    (mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB ‹_›).map
                      (fun b => scheme.initState () b)
                  let gs := gsDir.map (cliMapGameState CliPartyState.bin)
                  let bi : ModelDriverInstance S l := { bi0 with gs := gs }
                  let im0 : ModelDriverInstanceMeta S :=
                    { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := bnd.opkB?.map Prod.fst }
                  StateT.lift (set st)
                  set { ds with bhInsts := ds.bhInsts ++ [bi], instMeta := ds.instMeta ++ [im0],
                                instGs := ds.instGs ++ [gsDir] }
                  return some ds.bhInsts.length) : CliDrvM S l (Option Nat)) := by
              intro opkSk?
              cases opkSk? with
              | none => exact forgetS2_pure _
              | some opkOpt =>
                dsimp only
                cases mkMeEStrict u_init.val initPrinEntry.secIKA0 with
                | none => exact forgetS2_pure _
                | some meA =>
                  dsimp only
                  cases mkMeEStrict u_resp.val respPrinEntry.secIKA0 with
                  | none => exact forgetS2_pure _
                  | some meB =>
                    dsimp only
                    cases mkKeysEStrict j_resp.val respSpkEntry opkOpt with
                    | none => exact forgetS2_pure _
                    | some keysB =>
                      dsimp only
                      cases mkBundleEStrict u_resp.val bnd with
                      | none => exact forgetS2_pure _
                      | some bundleE =>
                        dsimp only
                        simp only [forgetS2_bind, forgetS2_lift, forgetS1_lift, cliPqInitM,
                          forgetW_map, forgetW_cliRunLogged]
                        congr 1; funext stA0?
                        cases stA0? with
                        | none => exact forgetS2_pure _
                        | some stA0 =>
                          dsimp only
                          simp [SMSchemeRM.initState, cliPqSchemeM]
            cases hdr.opkId? with
            | none =>
              dsimp only
              simp only [pure_bind]
              exact htail (some none)
            | some opkId =>
              dsimp only
              cases st.opkEntries.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val, opkId.toNat)) with
              | none =>
                dsimp only
                simp only [pure_bind]
                exact htail none
              | some oe =>
                dsimp only
                simp only [pure_bind]
                exact htail (some (some (opkId.toNat, oe.2.opkSk)))

theorem cliDrvImplM_forgetS2 (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec l (BitVec 512)) (CliDrvM S l)) (mode : BHDrvMode S)
    (t : (cliGameSpec S l (BitVec 512)).Domain) :
    forgetS2 (cliDrvImplM S l P (cliRunLogged run) W qep decT encT
        (liftQueryImplStateT2 (n := LogM) ext) mode t) =
      cliDrvImpl S l P run W qep decT encT ext mode t := by
  unfold cliDrvImpl
  refine forgetS2_add (forgetS2_add (forgetS2_add ?_ ?_) ?_) ?_ t
  · intro q
    rw [QueryImpl.liftTarget_apply, QueryImpl.liftTarget_apply, forgetS2_liftM_prob]
  · intro q
    exact forgetS2_bhLiftCliM (bhDrvKeyInd S l P false q)
  · intro q
    cases q with
    | startDR sid => exact forgetS2_cliDrvStartM S l P run W mode sid
  · exact forgetS2_cliDrvSMM S l run qep decT encT ext

theorem forgetS2_simulateQ {ι σ₁ σ₂ : Type} {spec : OracleSpec ι}
    (impl₁ : QueryImpl spec (StateT σ₁ (StateT σ₂ LogM)))
    (impl₂ : QueryImpl spec (StateT σ₁ (StateT σ₂ ProbComp)))
    (himpl : ∀ t, forgetS2 (impl₁ t) = impl₂ t) {α : Type}
    (oa : OracleComp spec α) :
    forgetS2 (simulateQ impl₁ oa) = simulateQ impl₂ oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, forgetS2_bind, himpl t,
      simulateQ_bind, simulateQ_spec_query]
    exact congrArg (impl₂ t >>= ·) (funext ih)

private theorem cliPqExp_eq_body' (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512)) :
    CryptoVerification.E2E.cliPqExp S run X W l qep decT encT A = (do
      let P := modelPrims X W
      let b ← $ᵗ Bool
      let ((b', ds), st) ←
        (runCliDriver S l P run W qep decT encT bhNoExtWithSpqr
          (fun _ _ _ _ _ => some b) A).run (SignalPqxdh.KeyIndState.empty S true)
      if !allTestedSessionsFresh P st then $ᵗ Bool
      else return (b' == b || driverSomeInstanceWon ds.toModelDriverState b)) := rfl

/-- Projecting away the log of `cliPqxdhExpFlagged` recovers `cliPqExp` (`CliPqxdhExpFlaggedFaithful`). -/
theorem cli_pq_exp_b_faithful_proof : CliPqxdhExpFlaggedFaithful := by
  intro Pt S run X W l qep decT encT A
  apply congrArg evalDist
  rw [cliPqExp_eq_body']
  change forgetW (do
    let P := modelPrims X W
    let b ← liftM ($ᵗ Bool : ProbComp Bool)
    let ((b', ds), st) ←
      (runCliDriverLogged S l P run W qep decT encT bhNoExtWithSpqr (fun _ _ _ _ _ => some b)
        A).run (SignalPqxdh.KeyIndState.empty S true)
    if !allTestedSessionsFresh P st then liftM ($ᵗ Bool : ProbComp Bool)
    else return (b' == b || driverSomeInstanceWon ds.toModelDriverState b)) = _
  simp only [forgetW_bind, forgetW_liftM]
  congr 1; funext b
  unfold runCliDriverLogged runCliDriver
  rw [← forgetS1_run, ← forgetS2_run,
    forgetS2_simulateQ _ _ (cliDrvImplM_forgetS2 S l (modelPrims X W) run W qep decT encT
      bhNoExtWithSpqr (fun _ _ _ _ _ => some b)) A.run]
  congr 1; funext ⟨⟨b', ds⟩, st⟩
  split_ifs <;> simp

end Computational.Proofs.LibsignalCli.Oom.Faithful
