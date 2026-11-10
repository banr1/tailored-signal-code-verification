/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Proofs.LibsignalCli.MainHaltedDefs
import Computational.Proofs.E2E.Dsl.AtomicLift
import Computational.Proofs.LibsignalCli.CliKemFailCoupling
import Computational.Proofs.LibsignalCli.MainHaltedOnline
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.EvalDist.Measure

/-!
# Halted CLI-to-Model Adapter and Online `KemFailBad` Coupling

Proves `exists_cliHaltedAdapterCoupling`, instantiating the cost-bounded CLI-to-model adapter
`cliToModelAdapterProgTblAtomic` and coupling `cliPqxdhExpFlagged` outside `KemFailBad` to the
`kemFailCoreTracker`-halted model experiment `bhE2EExpWithKiSessionTracked`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Computational.Proofs.LibsignalCli.MainHaltedAdapterBound

open scoped ENNReal BigOperators
open OracleComp OracleSpec
open CryptoGames (Party SMSchemeR)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoGames.CBC (Plain)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh dummyKey)
open CryptoGames.SM (ConfigR GameState corrR deliverR injectR samIfNec)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open CryptoVerification.SignalSession (CliRun CliSpecPqxdh)
open CryptoVerification.E2E (Bytes CliAdapterCostBounded CliGameAdversary
  CliGameAdversaryPerInstanceBounded CliToModelAdapterProg
  MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds PEParams SampledSessionKey UnreachedPqxdhPrimitives
  bhDecodePreKeyMsgE bhTargetGameSpec cliCoinsTape? cliGameAdversaryReassoc cliPqxdhExpFlagged
  deliverRM injectRM liftStateT modelPrims)
open Computational.Proofs.E2E.Dsl.AtomicLift (cliToModelAdapterProgTblAtomic
  cliE2EExpWithKiCoinLogged_cliToModelAdapterProgTblAtomic_eq_L_bh
  cliToModelAdapterProgTblAtomic_perInstanceQueryBounds
  gRedBounded_cliToModelAdapterProgTblAtomic_bhAdapterCostBudget)
open Computational.Proofs.LibsignalCli.CliKemFailCoupling (exists_cliKemFail_e2eCoinLogged_bound)
open Computational.Proofs.LibsignalCli.MainHaltedDefs (TargetAdvPerInstanceBounded
  kemFailCoreTracker validSessionHaltTracker_kemFailCoreTracker)

/-! ## `SessionHaltTracker` bridge -/

private def toCouplingTracker {St Msg Coins C Key τ : Type}
    (T : MainHaltedPrefixCore.SessionHaltTracker St Msg Coins C Key τ) :
    MainHaltedCoupling.SessionHaltTracker St Msg Coins C Key τ where
  init := T.init
  checkSend s₁ P coins tr :=
    let r := T.onSend s₁ P coins tr
    (r.1, r.2.1)
  commitSend s₁ P coins ct tr :=
    (T.onSend s₁ P coins tr).2.2 ct
  onDeliver := T.onDeliver

private theorem validSessionHaltTracker_toCouplingTracker {St Msg Coins C Key τ : Type}
    {badGlobal : List Coins → Bool}
    {T : MainHaltedPrefixCore.SessionHaltTracker St Msg Coins C Key τ}
    {TrInv : τ → List Coins → Prop}
    (hT : MainHaltedPrefixCore.ValidSessionHaltTracker badGlobal T TrInv) :
    MainHaltedCoupling.ValidSessionHaltTracker badGlobal (toCouplingTracker T) TrInv where
  inv_init := hT.inv_init
  inv_mono := hT.inv_mono
  inv_deliver := hT.inv_deliver
  send_good := hT.send_good

private theorem liftM_state_run {τ α : Type} (p : ProbComp α) (tr : τ) :
    (liftM p : StateT τ ProbComp α).run tr = (fun a => (a, tr)) <$> p := by
  show (StateT.lift p).run tr = _
  simp [StateT.run_lift, map_eq_bind_pure_comp]

private theorem liftStateT_run_state {σ τ α : Type} (m : StateT σ ProbComp α) (s : σ) (tr : τ) :
    ((liftStateT m : StateT σ (StateT τ ProbComp) α).run s).run tr =
      (fun x => (x, tr)) <$> m.run s := by
  change (liftM (m.run s) : StateT τ ProbComp (α × σ)).run tr = _
  exact liftM_state_run (m.run s) tr

private theorem rawState_run {τ α : Type} (f : τ → ProbComp (α × τ)) (tr : τ) :
    StateT.run f tr = f tr := rfl

private theorem raw_set_bind {τ β : Type} (x : τ) (f : PUnit → StateT τ ProbComp β) (tr : τ) :
    (set x >>= f) tr = (f ()).run x := rfl

private theorem raw_pure_comp {τ α β : Type} (g : α → β) (a : α) (tr : τ) :
    ((pure ∘ g) a : StateT τ ProbComp β).run tr = pure (g a, tr) := rfl

private theorem raw_pure_apply {τ α : Type} (a : α) (tr : τ) :
    (pure a : StateT τ ProbComp α) tr = pure (a, tr) := rfl

private theorem deliverRM_smSchemeTrackState_eq {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : ConfigR St Msg C) (q : Party × C) :
    deliverRM (MainHaltedPrefixCore.smSchemeTrackState (τ := τ) sm) cfg q =
      liftStateT (deliverR sm cfg q) := by
  rcases q with ⟨P, c⟩; ext s tr
  rw [liftStateT_run_state]
  unfold deliverRM deliverR MainHaltedPrefixCore.smSchemeTrackState
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure]
  cases s.inTransit P.other c with
  | none => simp
  | some _ =>
    dsimp only
    simp only [StateT.run_bind, StateT.run_lift, liftM_state_run, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_apply]
    congr 1; funext rc
    rcases hrecv : sm.receive (s.st P) c rc with _ | ⟨st', t', i', m'⟩ <;>
      simp only [hrecv] <;> split_ifs <;>
      simp [StateT.run_map, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]

private theorem injectRM_smSchemeTrackState_eq {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    injectRM (MainHaltedPrefixCore.smSchemeTrackState (τ := τ) sm) Δ qep cfg =
      fun q => liftStateT (injectR sm Δ qep cfg q) := by
  funext ⟨P, c⟩; ext s tr
  rw [liftStateT_run_state]
  unfold injectRM injectR MainHaltedPrefixCore.smSchemeTrackState
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c))
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, StateT.run_bind,
      StateT.run_lift, liftM_state_run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_apply]
    congr 1; funext rc
    rcases hrecv : sm.receive (s.st P) c rc with _ | ⟨st', t', i', m'⟩ <;>
      simp only [hrecv] <;> (try split_ifs) <;>
      simp [StateT.run_map, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
  · simp [StateT.run_pure, map_eq_bind_pure_comp]

private theorem transmitRSessionTracked_coupling_eq_prefixCore
    {Key St Msg Coins RCoins C τ : Type} [SampleableType Coins]
    (T : MainHaltedPrefixCore.SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    MainHaltedCoupling.transmitRSessionTracked (toCouplingTracker T) sm Δ qep cfg =
      MainHaltedPrefixCore.transmitRSessionTracked T sm Δ qep cfg := by
  rcases T with ⟨init, onSend, onDeliver⟩
  funext ⟨P, m, r⟩; funext s tr
  unfold MainHaltedCoupling.transmitRSessionTracked MainHaltedPrefixCore.transmitRSessionTracked
    toCouplingTracker
  dsimp only
  change StateT.run (StateT.run _ s) tr = StateT.run (StateT.run _ s) tr
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases !(cfg.sendOK s P) <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_map, liftM_state_run,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  congr 1; funext ⟨coins, bad⟩
  rcases hep : s.epMgmt Δ qep P bad with _ | s₁ <;> simp only [hep]
  cases hbad : (onSend s₁ P coins tr).1 <;>
    (simp only [StateT.run_bind, StateT.run_lift, StateT.run_map, StateT.run_get, StateT.run_set,
        StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
        hbad, ↓reduceIte]
     simp [hbad, raw_set_bind, raw_pure_comp, raw_pure_apply, rawState_run, StateT.run_bind,
        StateT.run_lift, StateT.run_map, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp,
        bind_assoc])

private theorem challRSessionTracked_coupling_eq_prefixCore
    {Key St Msg Coins RCoins C τ : Type} [SampleableType Coins]
    (T : MainHaltedPrefixCore.SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    MainHaltedCoupling.challRSessionTracked (toCouplingTracker T) sm Δ qep cfg =
      MainHaltedPrefixCore.challRSessionTracked T sm Δ qep cfg := by
  rcases T with ⟨init, onSend, onDeliver⟩
  funext ⟨P, m₀, m₁, r⟩; funext s tr
  unfold MainHaltedCoupling.challRSessionTracked MainHaltedPrefixCore.challRSessionTracked
    toCouplingTracker
  dsimp only
  change StateT.run (StateT.run _ s) tr = StateT.run (StateT.run _ s) tr
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases !(cfg.sendOK s P) <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_map, liftM_state_run,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  congr 1; funext ⟨coins, bad⟩
  rcases hep : s.epMgmt Δ qep P bad with _ | s₁ <;> simp only [hep]
  cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P))) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  cases hbad : (onSend s₁ P coins tr).1 <;>
    (simp only [StateT.run_bind, StateT.run_lift, StateT.run_map, StateT.run_get, StateT.run_set,
        StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
        hbad, ↓reduceIte]
     simp [hbad, raw_set_bind, raw_pure_comp, raw_pure_apply, rawState_run, StateT.run_bind,
        StateT.run_lift, StateT.run_map, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp,
        bind_assoc])

private theorem deliverRSessionTracked_coupling_eq_prefixCore
    {Key St Msg Coins RCoins C τ : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (T : MainHaltedPrefixCore.SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : ConfigR St Msg C) :
    MainHaltedCoupling.deliverRSessionTracked (toCouplingTracker T) sm cfg =
      MainHaltedPrefixCore.deliverRSessionTracked T sm cfg := by
  funext ⟨P, c⟩
  unfold MainHaltedCoupling.deliverRSessionTracked MainHaltedPrefixCore.deliverRSessionTracked
  simp only [deliverRM_smSchemeTrackState_eq]
  ext s tr
  simp only [toCouplingTracker, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
    StateT.run_pure, liftStateT_run_state, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  simp [rawState_run, bind_assoc]

private theorem oracleImplRSessionTracked_coupling_eq_prefixCore
    {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (T : MainHaltedPrefixCore.SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    MainHaltedCoupling.oracleImplRSessionTracked (toCouplingTracker T) sm Δ qep cfg =
      MainHaltedPrefixCore.oracleImplRSessionTracked T sm Δ qep cfg := by
  unfold MainHaltedCoupling.oracleImplRSessionTracked MainHaltedPrefixCore.oracleImplRSessionTracked
  rw [transmitRSessionTracked_coupling_eq_prefixCore, challRSessionTracked_coupling_eq_prefixCore,
    deliverRSessionTracked_coupling_eq_prefixCore, injectRM_smSchemeTrackState_eq]

private theorem bhE2EStepLocalSmSessionTracked_coupling_eq_prefixCore
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : MainHaltedPrefixCore.SessionHaltTracker
      (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : CryptoVerification.E2E.BHE2EDrvState S ℓ × List τ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    MainHaltedCoupling.bhE2EStepLocalSmSessionTracked (toCouplingTracker T) C K qep decT encT
        σH i q =
      MainHaltedPrefixCore.bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i q := by
  unfold MainHaltedCoupling.bhE2EStepLocalSmSessionTracked
    MainHaltedPrefixCore.bhE2EStepLocalSmSessionTracked
  dsimp only
  by_cases hClean : (!CryptoVerification.E2E.bhE2EDrvInstClean σH.1 i) = true
  · simp only [hClean, ↓reduceIte]
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte]
    cases σH.1.insts[i]? with
    | none => rfl
    | some d =>
      cases σH.1.instMeta[i]? with
      | none => rfl
      | some im =>
        dsimp only
        by_cases hEarly : (!im.bobAccepted && CryptoVerification.E2E.bhIsBobRecvSMQuery q &&
            CryptoVerification.E2E.bhE2EInstIkACorr σH.1 d) = true
        · simp only [hEarly, ↓reduceIte]
        · simp only [hEarly, Bool.false_eq_true, ↓reduceIte]
          cases d.gs with
          | none => rfl
          | some _ =>
            have hInit : (toCouplingTracker T).init = T.init := rfl
            simp only [hInit, oracleImplRSessionTracked_coupling_eq_prefixCore]
            rcases q with (((_ | _) | ⟨P, c⟩) | ⟨P, c⟩) | _
            · rfl
            · rfl
            · cases P <;> dsimp only [MainHaltedCoupling.bhDecodeSmWireQuery]
              · cases (bhDecodePreKeyMsgE c).isSome <;> rfl
              · cases im.bobAccepted
                · cases bhDecodePreKeyMsgE c with
                  | none => rfl
                  | some _ => dsimp only; first | rfl | (split_ifs <;> rfl)
                · cases bhDecodePreKeyMsgE c with
                  | none => rfl
                  | some _ => dsimp only; first | rfl | (split_ifs <;> rfl)
            · cases P <;> dsimp only [MainHaltedCoupling.bhDecodeSmWireQuery]
              · cases (bhDecodePreKeyMsgE c).isSome <;> rfl
              · cases im.bobAccepted
                · rfl
                · cases bhDecodePreKeyMsgE c with
                  | none => rfl
                  | some _ => dsimp only; first | rfl | (split_ifs <;> rfl)
            · rfl

private theorem bhE2EDrvImplWithSessionTracked_coupling_eq_prefixCore
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : MainHaltedPrefixCore.SessionHaltTracker
      (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    MainHaltedCoupling.bhE2EDrvImplWithSessionTracked (toCouplingTracker T) P ki C K qep decT encT =
      MainHaltedPrefixCore.bhE2EDrvImplWithSessionTracked T P ki C K qep decT encT := by
  funext q
  rcases q with _ | ((_ | _) | ⟨_, _⟩)
  · rfl
  · rfl
  · rfl
  · dsimp only [MainHaltedCoupling.bhE2EDrvImplWithSessionTracked,
      MainHaltedPrefixCore.bhE2EDrvImplWithSessionTracked]
    simp only [bhE2EStepLocalSmSessionTracked_coupling_eq_prefixCore]

private theorem bhE2EExpWithKiSessionTracked_coupling_eq_prefixCore
    {τ : Type} {ℓ : ℕ}
    (T : MainHaltedPrefixCore.SessionHaltTracker
      (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (secb : Bool) (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    MainHaltedCoupling.bhE2EExpWithKiSessionTracked (toCouplingTracker T) secb S P ki C K qep
        decT encT B =
      MainHaltedPrefixCore.bhE2EExpWithKiSessionTracked T secb S P ki C K qep decT encT B := by
  unfold MainHaltedCoupling.bhE2EExpWithKiSessionTracked
    MainHaltedPrefixCore.bhE2EExpWithKiSessionTracked
  rw [bhE2EDrvImplWithSessionTracked_coupling_eq_prefixCore]

/-! ## Adapter coupling bound -/

/-- Cost-bounded CLI-to-model adapter transferring `CliGameAdversaryPerInstanceBounded` to
`TargetAdvPerInstanceBounded` and bounding `cliPqxdhExpFlagged` outside `KemFailBad` by
`bhE2EExpWithKiSessionTracked` plus `δ_extra` with `2 * δ_extra ≤ kemDecapsFailureTerm S δ_kem`. -/
theorem exists_cliHaltedAdapterCoupling
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    ∃ (L_cli : ∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CliToModelAdapterProg S ℓ decT encT),
      (∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
        (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
        CliAdapterCostBounded decT encT b qStart qDR (L_cli decT encT)) ∧
      (∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
        (A : CliGameAdversary S ℓ (BitVec 512))
        (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ),
        CliGameAdversaryPerInstanceBounded A b qStart qs →
        TargetAdvPerInstanceBounded
          ((L_cli decT encT).eval (fun _ => cliGameAdversaryReassoc A) ()) b qStart qs) ∧
      ∀ (run : CliRun) (X : UnreachedPqxdhPrimitives) (Wp : PEParams)
        (_hCli : CliSpecPqxdh run X Wp)
        (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds Wp.Q.K)
        (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X Wp))
        (δ_kem : ℝ≥0∞) (_hKemBin : SignalPqxdh.KemDeltaCorrect (modelPrims X Wp) δ_kem)
        (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
        (decT : PublicKey → Option Pt) (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
        (_hDh : Dh.Commutes) (_hX : X25519RealizesDh Wp.C Dh encPt encT)
        (_hdec : ∀ T, decT (encT T) = some T)
        (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
        (_hD : ∀ k x, Wp.C.D k (Wp.C.E k x) = x)
        (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
        (_hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32)
        (A : CliGameAdversary S ℓ (BitVec 512))
        (_hA : CliGameAdversaryPerInstanceBounded A b qStart qs),
        let P := modelPrims X Wp
        let B_A := (L_cli decT encT).eval (fun _ => cliGameAdversaryReassoc A) ()
        let exp_H :=
          MainHaltedPrefixCore.bhE2EExpWithKiSessionTracked (kemFailCoreTracker Wp.C.F Wp.Q.K)
            true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) Wp.C Wp.Q.K qep decT encT B_A
        ∃ δ_extra : ℝ≥0∞,
          2 * δ_extra ≤ SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem ∧
          ∀ v : Bool,
            Pr{let z ← cliPqxdhExpFlagged S run X Wp ℓ qep decT encT A}[
              z.1 = v ∧ ¬ (Wp.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)] ≤
                𝒟[exp_H] {v} + δ_extra := by
  refine ⟨fun decT encT => cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT,
    fun decT encT b qStart qDR =>
      gRedBounded_cliToModelAdapterProgTblAtomic_bhAdapterCostBudget decT encT b qStart qDR,
    fun decT encT A b qStart qs hA =>
      cliToModelAdapterProgTblAtomic_perInstanceQueryBounds decT encT A b qStart qs hA,
    ?_⟩
  intro run X Wp hCli hK_tot hP δ_kem hKemBin Dh encPt encT decT qep hℓ hDh hX hdec
    hdum hz hD b qStart qs hq32 A hA
  let P := modelPrims X Wp
  let B_A := (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).eval
    (fun _ => cliGameAdversaryReassoc A) ()
  let B_Lbh := (CryptoVerification.E2E.L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
    (fun _ => cliGameAdversaryReassoc A) ()
  obtain ⟨δ_extra, hδ_le, hCliCoupl⟩ := exists_cliKemFail_e2eCoinLogged_bound S ℓ run X Wp
    hCli hK_tot hP δ_kem hKemBin Dh encPt encT decT qep hℓ hDh hX hdec hdum hz hD b qStart qs hq32
    A hA
  refine ⟨δ_extra, hδ_le, fun v => ?_⟩
  have hEqAd :
      MainHaltedCoupling.cliE2EExpWithKiCoinLogged true S P
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) Wp.C Wp.Q.K ℓ qep decT encT B_A =
        CliKemFailCoupling.cliE2EExpWithKiCoinLogged true S P
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) Wp.C Wp.Q.K ℓ qep decT encT B_Lbh :=
    cliE2EExpWithKiCoinLogged_cliToModelAdapterProgTblAtomic_eq_L_bh S P
      hP.toWellFormedPrimitivesδ Wp.C Wp.Q.K ℓ qep decT encT A
  have hOnline := MainHaltedOnline.cliE2EExpWithKiCoinLogged_good_not_true_le_sessionTracked_pr
    (MainHaltedCoupling.validBadLog_kemFailBadLog Wp.Q.K)
    (validSessionHaltTracker_toCouplingTracker
      (validSessionHaltTracker_kemFailCoreTracker (St := GhostState Bytes) (Msg := Plain ℓ)
        (C := Bytes) Wp.C.F Wp.Q.K))
    true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) Wp.C Wp.Q.K qep decT encT B_A v
  dsimp only [MainHaltedCoupling.kemFailBadLog] at hOnline
  rw [hEqAd, bhE2EExpWithKiSessionTracked_coupling_eq_prefixCore] at hOnline
  rw [prEvent_eq_evalDist_singleton _ v] at hOnline
  exact (hCliCoupl v).trans (add_le_add hOnline le_rfl)

end Computational.Proofs.LibsignalCli.MainHaltedAdapterBound
