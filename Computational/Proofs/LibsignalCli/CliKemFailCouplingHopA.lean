/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs
import Computational.Proofs.LibsignalCli.CliKemFailCouplingHopAAux
import Computational.Proofs.LibsignalCli.CliPqRetainedDirEq
import Computational.Proofs.LibsignalCli.Oom.Faithful
import Computational.Proofs.E2E.Relabel.GameEq
import Computational.Proofs.SpecLemmas.Game.StatementPq

/-!
# Retained-directory to projected send-coin coupling

Shows that projecting `cliPqxdhExpFlagged`'s input log with `sendTapesOfInputs` equals mapping
`cliPqExpProjCoinLogged`'s send-coin log with `coinBytes` (`DEV-CLI18`), by lifting the
retained-directory projection to `CoinLogM`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.CliKemFailCouplingHopA

open OracleComp OracleSpec
open CryptoGames (Party SMSchemeR SMSchemeR.sendPart)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.SM (ConfigR GameState)
open CryptoVerification.LibsignalSpqrV1 (coinBytes)
open CryptoVerification.SignalSession (CliRun CliSpecPqxdh Inputs)
open CryptoVerification.E2E (BHDrvM BHDrvMode BinState Bytes CliDriverState CliDrvM CliDrvMT
  CliGameAdversary CliPartyDirInv CliPartyState CliRetainedStateInv
  Dir.cliDrvCtl Dir.cliPqScheme ModelDriverInstance ModelDriverInstanceMeta PEParams
  UnreachedPqxdhPrimitives allTestedSessionsFresh bhAlignTransForBob bhConfigSpkS
  bhDecodePreKeyMsgE bhDrCtlSpec bhDrvInstClean bhDrvInstClean_projCliDrv bhDrvKeyInd
  bhDrvKeyInd_step_proj bhExpectedPreKeyMsg bhHdrOfPreKeyMsg bhInstIkACorrupted
  bhIsBobRecvSMQuery bhLiftCli bhMetaAfterSM bhNoExtWithSpqr bhPartneredInTransitA
  bhPartneredInnerBytes bhSmDefaultWithSpqr challRM cliConfigSpkS cliDrvCtl cliDrvStart_step_proj
  cliGameDrSpec cliGameSmSpec cliGameSpec cliMapGameState cliOracleImplR cliOracleImplRM
  cliOracleImplR_step cliPqScheme cliPqSend_dir_eq_proj cliPqSigsOf cliPqxdhExpFlagged
  cliRetainedStateInv_init cliRetainedStateInv_of_spkLookup deliverRM driverSomeInstanceWon
  driverSomeInstanceWon_projCliDrv injectRM liftQueryImplStateT2 liftStateT modelPrims oracleImplRM
  projCliDrv projInsts smSchemeCoinLogged transmitRM wirePrekey wireWhisper)
open CryptoVerification.E2E.Relabel.GameEq (epMgmt_st_trans mapSt mapSt_b mapSt_epMgmt
  mapSt_epoch mapSt_idx mapSt_inTransit mapSt_record mapSt_safeCh mapSt_st mapSt_win)
open Computational.Proofs.LibsignalCli.Oom.Faithful (instLawfulMonadWriterTList)
open Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs (BHDrvMCoinLogged CoinLogM
  cliDrvImplCoinLogged cliDrvSMCoinLogged cliPqExpProjCoinLogged cliRunStdSMCoinLogged
  cliStepLocalSMCoinLogged sendTapesOfInputs)
open Computational.Proofs.LibsignalCli.CliKemFailCouplingHopAAux
  (cliPqxdhExpFlagged_sendTapes_eq_dirCoinLogged dirDrvImplCoinLogged dirDrvSMCoinLogged
  dirPqExpCoinLogged dirRunStdSMCoinLogged dirStepLocalSMCoinLogged)

private theorem cliPartyDirInv_bi_gs {S : SignalPqxdh.Setup} {ℓ : ℕ} (W : PEParams)
    (bi : ModelDriverInstance S ℓ)
    (gs1 gs2 : Option (GameState BinState (Plain ℓ) Bytes))
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (P : Party) (s : CliPartyState) :
    CliPartyDirInv W { bi with gs := gs1 } sigs P s ↔
      CliPartyDirInv W { bi with gs := gs2 } sigs P s := by
  cases P <;> rfl

private theorem cliPartyDirInv_update {S : SignalPqxdh.Setup} {ℓ : ℕ} {W : PEParams}
    {bi : ModelDriverInstance S ℓ}
    {sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64}
    {st : Party → CliPartyState} (hGs : ∀ Q, CliPartyDirInv W bi sigs Q (st Q))
    {P : Party} {s' : CliPartyState} (hs' : CliPartyDirInv W bi sigs P s') :
    ∀ Q, CliPartyDirInv W bi sigs Q (Function.update st P s' Q) := by
  intro Q
  by_cases hQ : Q = P
  · subst hQ; simpa using hs'
  · simp [Function.update_of_ne hQ]; exact hGs Q

private theorem zipWith_getElem?_ret {α β γ : Type} (f : α → β → γ) :
    ∀ (xs : List α) (ys : List β) (i : ℕ),
      (xs.zipWith f ys)[i]? = match xs[i]?, ys[i]? with
        | some x, some y => some (f x y)
        | _, _ => none
  | [], [], _ => by simp
  | [], _ :: _, _ => by simp
  | _ :: _, [], _ => by simp
  | _ :: _, _ :: _, 0 => rfl
  | _ :: xs, _ :: ys, i + 1 => zipWith_getElem?_ret f xs ys i

private theorem zipWith_set_ret {α β γ : Type} (f : α → β → γ) :
    ∀ (xs : List α) (ys : List β) (i : ℕ) (x : α) (y : β),
      (xs.set i x).zipWith f (ys.set i y) = (xs.zipWith f ys).set i (f x y)
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, _, _ => by simp
  | _ :: _, _ :: _, 0, _, _ => rfl
  | _ :: xs, _ :: ys, i + 1, x, y => by simp [zipWith_set_ret f xs ys i x y]

private theorem writerT_run_pure {ω α : Type} (a : α) :
    (pure a : WriterT (List ω) ProbComp α).run = pure (a, []) := rfl

private theorem writerT_run_liftM {ω α : Type} (c : ProbComp α) :
    (liftM c : WriterT (List ω) ProbComp α).run = (fun a => (a, [])) <$> c := rfl

private theorem writerT_run_map {ω α β : Type} (f : α → β)
    (m : WriterT (List ω) ProbComp α) :
    (f <$> m).run = Prod.map f id <$> m.run := rfl

private theorem writerT_run_bind {ω α β : Type}
    (m : WriterT (List ω) ProbComp α) (k : α → WriterT (List ω) ProbComp β) :
    (m >>= k).run = m.run >>= fun x => Prod.map id (x.2 ++ ·) <$> (k x.1).run := by
  rw [WriterT.run_bind]
  simp only [map_eq_bind_pure_comp]
  rfl

private theorem smSchemeCoinLogged_send_run' {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (s : St) (m : Msg) (r : Coins) :
    ((smSchemeCoinLogged sm).send s m r).run = pure (sm.send s m r, [r]) := by
  simp [smSchemeCoinLogged]

private theorem smSchemeCoinLogged_receive_eq_liftM {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (s : St) (c : C) (rc : RCoins) :
    (smSchemeCoinLogged sm).receive s c rc = liftM (pure (sm.receive s c rc) : ProbComp _) := by
  show ((smSchemeCoinLogged sm).receive s c rc).run =
    (liftM (pure (sm.receive s c rc) : ProbComp _) : WriterT (List Coins) ProbComp _).run
  dsimp [smSchemeCoinLogged, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
    WriterT.liftTell]
  simp

private theorem deliverRM_coinLogged_run {Key St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (cfg : ConfigR St Msg C) (q : Party × C) (gs : GameState St Msg C) :
    ((deliverRM (smSchemeCoinLogged sm) cfg q).run gs).run =
      (fun x => (x, ([] : List (BitVec 512)))) <$> (CryptoGames.SM.deliverR sm cfg q).run gs := by
  rcases q with ⟨P, c⟩
  unfold deliverRM CryptoGames.SM.deliverR
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases gs.win
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases gs.inTransit P.other c with
    | none => simp [StateT.run_pure]
    | some r =>
      dsimp only
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_monadLift, monadLift_self,
        smSchemeCoinLogged_receive_eq_liftM, writerT_run_bind, writerT_run_liftM,
        map_bind, bind_map_left, map_pure, bind_assoc, pure_bind, List.nil_append]
      refine bind_congr_of_forall_mem_support _ fun rc _ => ?_
      cases sm.receive (gs.st P) c rc with
      | none =>
        split_ifs <;>
          simp [StateT.run_map, StateT.run_set, StateT.run_pure]
      | some x =>
        rcases x with ⟨st', t', i', m'⟩
        dsimp only
        split_ifs <;>
          simp [StateT.run_map, StateT.run_set]
  · simp [StateT.run_pure]

private theorem injectRM_coinLogged_run {Key St Msg C : Type} [DecidableEq C]
    (sm : SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (q : Party × C) (gs : GameState St Msg C) :
    ((injectRM (smSchemeCoinLogged sm) Δ qep cfg q).run gs).run =
      (fun x => (x, ([] : List (BitVec 512)))) <$>
        (CryptoGames.SM.injectR sm Δ qep cfg q).run gs := by
  rcases q with ⟨P, c⟩
  unfold injectRM CryptoGames.SM.injectR
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (gs.win || (gs.inTransit P.other c).isSome || !(gs.safeInj Δ) || !(cfg.injOK c))
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
      StateT.run_monadLift, monadLift_self, smSchemeCoinLogged_receive_eq_liftM,
      writerT_run_bind, writerT_run_liftM, map_bind, bind_map_left, map_pure,
      bind_assoc, pure_bind, List.nil_append]
    refine bind_congr_of_forall_mem_support _ fun rc _ => ?_
    cases sm.receive (gs.st P) c rc with
    | none => simp [StateT.run_pure]
    | some x =>
      rcases x with ⟨st', t', i', m'⟩
      dsimp only
      split_ifs <;>
        simp [StateT.run_map, StateT.run_set, StateT.run_pure]
  · simp [StateT.run_pure]

private theorem cliOracleImplRM_coinLogged_transmit_step {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (bi : ModelDriverInstance S ℓ)
    (gsProj : Option (GameState BinState (Plain ℓ) Bytes))
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (stA0 stB0 : CliPartyState) (stA0' stB0' : BinState)
    (gs : GameState CliPartyState (Plain ℓ) Bytes)
    (hGs : ∀ P, CliPartyDirInv W bi sigs P (gs.st P))
    (q : Party × Plain ℓ × Option (BitVec 512)) :
    let schemeDir := Dir.cliPqScheme run ℓ bi stA0 stB0
    let schemeProj := cliPqScheme run W ℓ { bi with gs := gsProj } sigs stA0' stB0'
    let cfgDir := cliConfigSpkS (St := CliPartyState) (Msg := Plain ℓ) decT encT
    let cfgProj := bhConfigSpkS (Msg := Plain ℓ) decT encT
    Prod.map (Prod.map id (mapSt CliPartyState.bin)) id <$>
      (((transmitRM (smSchemeCoinLogged schemeDir) (2 + 1) qep cfgDir q).run gs).run) =
      (((transmitRM (smSchemeCoinLogged schemeProj) (2 + 1) qep cfgProj q).run
          (mapSt CliPartyState.bin gs)).run) ∧
    ∀ z ∈ support (((transmitRM (smSchemeCoinLogged schemeDir) (2 + 1) qep cfgDir q).run gs).run),
      ∀ P, CliPartyDirInv W bi sigs P (z.1.2.st P) := by
  rcases q with ⟨P, m, rCoins⟩
  intro schemeDir schemeProj cfgDir cfgProj
  have hsendOK : cfgProj.sendOK (mapSt CliPartyState.bin gs) P = cfgDir.sendOK gs P := rfl
  unfold transmitRM
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK]
  by_cases hok : (!(cfgDir.sendOK gs P)) = true
  · simp [hok, StateT.run_pure, hGs]
  · simp only [Bool.not_eq_true] at hok
    rw [hok]
    simp only [Bool.false_eq_true, ↓reduceIte,
      mapSt_win]
    by_cases hwin : gs.win = true
    · simp [hwin, StateT.run_pure, hGs]
    · simp only [Bool.not_eq_true] at hwin
      simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        writerT_run_bind, writerT_run_liftM, bind_map_left, map_bind,
        bind_assoc, pure_bind, List.nil_append]
      have hm : m.toList.length < 2 ^ 32 := by rw [List.Vector.toList_length]; omega
      refine ⟨bind_congr_of_forall_mem_support _ fun cb _ => ?_, ?_⟩
      · rcases cb with ⟨coins, bad⟩
        dsimp only [Prod.map, id]
        rw [mapSt_epMgmt]
        rcases hep : gs.epMgmt (2 + 1) qep P bad with _ | gs₁
        · simp [StateT.run_pure]
        · dsimp only [Option.map]
          have hst1 : gs₁.st = gs.st := (epMgmt_st_trans hep).1
          obtain ⟨hs1, hs2, _⟩ := cliPqSend_dir_eq_proj hCli (hst1 ▸ hGs P) m.toList hm coins
          have hs_proj :
              (schemeProj.send ((mapSt CliPartyState.bin gs₁).st P) m coins) =
              ((schemeDir.send (gs₁.st P) m coins).1.bin, (schemeDir.send (gs₁.st P) m coins).2) := by
            dsimp only [schemeProj, schemeDir, cliPqScheme, Dir.cliPqScheme, mapSt_st]
            exact Prod.ext hs1.symm hs2.symm
          simp only [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
            writerT_run_bind, smSchemeCoinLogged_send_run', writerT_run_pure,
            pure_bind, map_pure, Prod.map_apply, id_eq, List.append_nil, mapSt_epoch, mapSt_idx]
          rw [hs_proj, ← mapSt_record]
      · intro z hz P'
        rw [mem_support_bind_iff] at hz
        obtain ⟨⟨coins, bad⟩, _, hz⟩ := hz
        dsimp only [Prod.map, id] at hz
        rcases hep : gs.epMgmt (2 + 1) qep P bad with _ | gs₁ <;> rw [hep] at hz
        · simp only [StateT.run_pure, writerT_run_pure, map_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz; exact hGs P'
        · simp only [StateT.run_bind, StateT.run_lift, StateT.run_set,
            writerT_run_bind, smSchemeCoinLogged_send_run', writerT_run_pure,
            pure_bind, map_pure] at hz
          subst hz
          have hst1 : gs₁.st = gs.st := (epMgmt_st_trans hep).1
          obtain ⟨_, _, hinv'⟩ := cliPqSend_dir_eq_proj hCli (hst1 ▸ hGs P) m.toList hm coins
          exact cliPartyDirInv_update (hst1 ▸ hGs) hinv' P'

private theorem cliOracleImplRM_coinLogged_chall_step {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (bi : ModelDriverInstance S ℓ)
    (gsProj : Option (GameState BinState (Plain ℓ) Bytes))
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (stA0 stB0 : CliPartyState) (stA0' stB0' : BinState)
    (gs : GameState CliPartyState (Plain ℓ) Bytes)
    (hGs : ∀ P, CliPartyDirInv W bi sigs P (gs.st P))
    (q : Party × Plain ℓ × Plain ℓ × Option (BitVec 512)) :
    let schemeDir := Dir.cliPqScheme run ℓ bi stA0 stB0
    let schemeProj := cliPqScheme run W ℓ { bi with gs := gsProj } sigs stA0' stB0'
    let cfgDir := cliConfigSpkS (St := CliPartyState) (Msg := Plain ℓ) decT encT
    let cfgProj := bhConfigSpkS (Msg := Plain ℓ) decT encT
    Prod.map (Prod.map id (mapSt CliPartyState.bin)) id <$>
      (((challRM (smSchemeCoinLogged schemeDir) (2 + 1) qep cfgDir q).run gs).run) =
      (((challRM (smSchemeCoinLogged schemeProj) (2 + 1) qep cfgProj q).run
          (mapSt CliPartyState.bin gs)).run) ∧
    ∀ z ∈ support (((challRM (smSchemeCoinLogged schemeDir) (2 + 1) qep cfgDir q).run gs).run),
      ∀ P, CliPartyDirInv W bi sigs P (z.1.2.st P) := by
  rcases q with ⟨P, m₀, m₁, rCoins⟩
  intro schemeDir schemeProj cfgDir cfgProj
  have hsendOK : cfgProj.sendOK (mapSt CliPartyState.bin gs) P = cfgDir.sendOK gs P := rfl
  have hbase : cfgProj.base = cfgDir.base := rfl
  unfold challRM
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK, hbase]
  by_cases hok : (!(cfgDir.sendOK gs P)) = true
  · simp [hok, StateT.run_pure, hGs]
  · simp only [Bool.not_eq_true] at hok
    rw [hok]
    simp only [Bool.false_eq_true, ↓reduceIte,
      mapSt_win]
    by_cases hwin : gs.win = true
    · simp [hwin, StateT.run_pure, hGs]
    · simp only [Bool.not_eq_true] at hwin
      simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        writerT_run_bind, writerT_run_liftM, bind_map_left, map_bind,
        bind_assoc, pure_bind, List.nil_append]
      refine ⟨bind_congr_of_forall_mem_support _ fun cb _ => ?_, ?_⟩
      · rcases cb with ⟨coins, bad⟩
        dsimp only [Prod.map, id]
        rw [mapSt_epMgmt]
        rcases hep : gs.epMgmt (2 + 1) qep P bad with _ | gs₁
        · simp [StateT.run_pure]
        · dsimp only [Option.map]
          simp only [mapSt_safeCh, mapSt_epoch, mapSt_b, mapSt_idx]
          by_cases hch : (!(gs₁.safeCh (2 + 1) P) || !(cfgDir.base.challAllowedIn (gs₁.epoch P))) = true
          · simp [hch, StateT.run_pure]
          · simp only [Bool.not_eq_true] at hch
            have hst1 : gs₁.st = gs.st := (epMgmt_st_trans hep).1
            by_cases hgb : gs.b = true
            · simp only [hch, hgb, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
                StateT.run_set, StateT.run_pure, writerT_run_bind,
                smSchemeCoinLogged_send_run', writerT_run_pure, pure_bind, map_pure, Prod.map_apply,
                id_eq, List.append_nil]
              rw [← mapSt_record]
              have hm : ((cfgDir.base.challMsg (gs₁.epoch P)).getD m₁).toList.length < 2 ^ 32 := by
                rw [List.Vector.toList_length]; omega
              obtain ⟨hs1, hs2, _⟩ := cliPqSend_dir_eq_proj hCli (hst1 ▸ hGs P) _ hm coins
              dsimp only [schemeProj, schemeDir, cliPqScheme, Dir.cliPqScheme, mapSt_st]
              rw [hs1, hs2]; rfl
            · simp only [Bool.not_eq_true] at hgb
              simp only [hch, hgb, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
                StateT.run_set, StateT.run_pure, writerT_run_bind,
                smSchemeCoinLogged_send_run', writerT_run_pure, pure_bind, map_pure, Prod.map_apply,
                id_eq, List.append_nil]
              rw [← mapSt_record]
              have hm : ((cfgDir.base.challMsg (gs₁.epoch P)).getD m₀).toList.length < 2 ^ 32 := by
                rw [List.Vector.toList_length]; omega
              obtain ⟨hs1, hs2, _⟩ := cliPqSend_dir_eq_proj hCli (hst1 ▸ hGs P) _ hm coins
              dsimp only [schemeProj, schemeDir, cliPqScheme, Dir.cliPqScheme, mapSt_st]
              rw [hs1, hs2]; rfl
      · intro z hz P'
        rw [mem_support_bind_iff] at hz
        obtain ⟨⟨coins, bad⟩, _, hz⟩ := hz
        dsimp only [Prod.map, id] at hz
        rcases hep : gs.epMgmt (2 + 1) qep P bad with _ | gs₁ <;> rw [hep] at hz
        · simp only [StateT.run_pure, writerT_run_pure, map_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz; exact hGs P'
        · dsimp only at hz
          by_cases hch : (!(gs₁.safeCh (2 + 1) P) || !(cfgDir.base.challAllowedIn (gs₁.epoch P))) = true
          · simp only [hch, ↓reduceIte, StateT.run_pure, writerT_run_pure, map_pure,
              support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hGs P'
          · simp only [Bool.not_eq_true] at hch
            simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
              StateT.run_set, StateT.run_pure, writerT_run_bind, smSchemeCoinLogged_send_run',
              writerT_run_pure, pure_bind, map_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            set m := (cfgDir.base.challMsg (gs₁.epoch P)).getD (if gs.b then m₁ else m₀)
            have hm : m.toList.length < 2 ^ 32 := by rw [List.Vector.toList_length]; omega
            have hst1 : gs₁.st = gs.st := (epMgmt_st_trans hep).1
            obtain ⟨_, _, hinv'⟩ := cliPqSend_dir_eq_proj hCli (hst1 ▸ hGs P) m.toList hm coins
            exact cliPartyDirInv_update (hst1 ▸ hGs) hinv' P'

private theorem emptyLog_oracle_step {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {W : PEParams} {bi : ModelDriverInstance S ℓ}
    {sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64}
    {mDir : ProbComp (α × GameState CliPartyState (Plain ℓ) Bytes)}
    {mProj : ProbComp (α × GameState BinState (Plain ℓ) Bytes)}
    (hstep : Prod.map id (mapSt CliPartyState.bin) <$> mDir = mProj ∧
      ∀ z ∈ support mDir, ∀ P, CliPartyDirInv W bi sigs P (z.2.st P)) :
    Prod.map (Prod.map id (mapSt CliPartyState.bin)) id <$>
      ((fun x => (x, ([] : List (BitVec 512)))) <$> mDir) =
      ((fun x => (x, ([] : List (BitVec 512)))) <$> mProj) ∧
    ∀ z ∈ support ((fun x => (x, ([] : List (BitVec 512)))) <$> mDir),
      ∀ P, CliPartyDirInv W bi sigs P (z.1.2.st P) := by
  refine ⟨?_, ?_⟩
  · rw [← hstep.1]
    simp [Functor.map_map]
  · intro z hz P
    rw [map_eq_bind_pure_comp, mem_support_bind_iff] at hz
    obtain ⟨u, hu, hz⟩ := hz
    simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hstep.2 u hu P

private theorem cliOracleImplRM_coinLogged_step {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (bi : ModelDriverInstance S ℓ)
    (gsProj : Option (GameState BinState (Plain ℓ) Bytes))
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (stA0 stB0 : CliPartyState) (stA0' stB0' : BinState)
    (gs : GameState CliPartyState (Plain ℓ) Bytes)
    (hGs : ∀ P, CliPartyDirInv W bi sigs P (gs.st P))
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) :
    let schemeDir := Dir.cliPqScheme run ℓ bi stA0 stB0
    let schemeProj := cliPqScheme run W ℓ { bi with gs := gsProj } sigs stA0' stB0'
    let cfgDir := cliConfigSpkS (St := CliPartyState) (Msg := Plain ℓ) decT encT
    let cfgProj := bhConfigSpkS (Msg := Plain ℓ) decT encT
    Prod.map (Prod.map id (mapSt CliPartyState.bin)) id <$>
      (((cliOracleImplRM CliPartyState.bin (smSchemeCoinLogged schemeDir) (2 + 1) qep cfgDir q).run gs).run) =
      (((oracleImplRM (smSchemeCoinLogged schemeProj) (2 + 1) qep cfgProj q).run
          (mapSt CliPartyState.bin gs)).run) ∧
    ∀ z ∈ support
        (((cliOracleImplRM CliPartyState.bin (smSchemeCoinLogged schemeDir) (2 + 1) qep cfgDir q).run gs).run),
      ∀ P, CliPartyDirInv W bi sigs P (z.1.2.st P) := by
  intro schemeDir schemeProj cfgDir cfgProj
  have hPure := cliOracleImplR_step hCli hℓ qep decT encT bi gsProj sigs stA0 stB0 stA0' stB0' gs hGs q
  rcases q with (((q₁ | q₂) | q₃) | q₄) | q₅
  · exact cliOracleImplRM_coinLogged_transmit_step hCli hℓ qep decT encT bi gsProj sigs stA0 stB0 stA0' stB0' gs hGs q₁
  · exact cliOracleImplRM_coinLogged_chall_step hCli hℓ qep decT encT bi gsProj sigs stA0 stB0 stA0' stB0' gs hGs q₂
  · change Prod.map (Prod.map id (mapSt CliPartyState.bin)) id <$>
        (((deliverRM (smSchemeCoinLogged schemeDir) cfgDir q₃).run gs).run) =
        (((deliverRM (smSchemeCoinLogged schemeProj) cfgProj q₃).run
            (mapSt CliPartyState.bin gs)).run) ∧
      ∀ z ∈ support (((deliverRM (smSchemeCoinLogged schemeDir) cfgDir q₃).run gs).run),
        ∀ P, CliPartyDirInv W bi sigs P (z.1.2.st P)
    rw [deliverRM_coinLogged_run, deliverRM_coinLogged_run]
    exact emptyLog_oracle_step hPure
  · change Prod.map (Prod.map id (mapSt CliPartyState.bin)) id <$>
        (((injectRM (smSchemeCoinLogged schemeDir) (2 + 1) qep cfgDir q₄).run gs).run) =
        (((injectRM (smSchemeCoinLogged schemeProj) (2 + 1) qep cfgProj q₄).run
            (mapSt CliPartyState.bin gs)).run) ∧
      ∀ z ∈ support (((injectRM (smSchemeCoinLogged schemeDir) (2 + 1) qep cfgDir q₄).run gs).run),
        ∀ P, CliPartyDirInv W bi sigs P (z.1.2.st P)
    rw [injectRM_coinLogged_run, injectRM_coinLogged_run]
    exact emptyLog_oracle_step hPure
  · dsimp [cliOracleImplRM, oracleImplRM, liftStateT, StateT.run]
    exact emptyLog_oracle_step hPure

private theorem bhAlignTransForBob_mapSt' {St₁ St₂ Msg : Type} (φ : St₁ → St₂)
    (bobAcc : Bool) (regId : BitVec 32) (hdr : SignalPqxdh.HandshakeHdr) (c : Bytes)
    (gs : GameState St₁ Msg Bytes) :
    bhAlignTransForBob bobAcc regId hdr c (mapSt φ gs) =
      mapSt φ (bhAlignTransForBob bobAcc regId hdr c gs) := by
  unfold bhAlignTransForBob
  split_ifs
  · rfl
  · cases bhPartneredInnerBytes true regId hdr c <;> rfl

private theorem bhAlignTransForBob_st' {St Msg : Type}
    (bobAcc : Bool) (regId : BitVec 32) (hdr : SignalPqxdh.HandshakeHdr) (c : Bytes)
    (gs : GameState St Msg Bytes) :
    (bhAlignTransForBob bobAcc regId hdr c gs).st = gs.st := by
  unfold bhAlignTransForBob
  split_ifs
  · rfl
  · cases bhPartneredInnerBytes true regId hdr c <;> rfl

private theorem dirRunStdSMCoinLogged_step_proj {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (cds : CliDriverState S ℓ) (kst : SignalPqxdh.KeyIndState S)
    (hInv : CliRetainedStateInv W cds kst)
    (i : ℕ) (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : GameState CliPartyState (Plain ℓ) Bytes)
    (hbi : cds.bhInsts[i]? = some bi) (higs : cds.instGs[i]? = some (some gs))
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) :
    let biProj : ModelDriverInstance S ℓ := { bi with gs := some (mapSt CliPartyState.bin gs) }
    Prod.map (Prod.map (Prod.map id projCliDrv) id) id <$>
      ((((dirRunStdSMCoinLogged S ℓ run qep decT encT cds i bi im gs q).run cds).run kst).run) =
      ((((cliRunStdSMCoinLogged S ℓ run W qep decT encT (projCliDrv cds) i biProj im
          (mapSt CliPartyState.bin gs) q).run (projCliDrv cds)).run kst).run) ∧
    ∀ z ∈ support
        ((((dirRunStdSMCoinLogged S ℓ run qep decT encT cds i bi im gs q).run cds).run kst).run),
      CliRetainedStateInv W z.1.1.2 z.1.2 := by
  intro biProj
  obtain ⟨_, hsig, hdir_all⟩ := hInv.2 i bi hbi
  have hGs : ∀ P, CliPartyDirInv W bi (cliPqSigsOf kst bi) P (gs.st P) := hdir_all gs higs
  have hsigs_biProj : cliPqSigsOf kst biProj = cliPqSigsOf kst bi := rfl
  have hstep : ∀ (q₀ : (cliGameSmSpec ℓ (BitVec 512)).Domain)
      (gsIn : GameState CliPartyState (Plain ℓ) Bytes)
      (gsProjIn : GameState BinState (Plain ℓ) Bytes)
      (fDir : ((cliGameSmSpec ℓ (BitVec 512)).Range q₀ × GameState CliPartyState (Plain ℓ) Bytes) ×
          List (BitVec 512) → GameState CliPartyState (Plain ℓ) Bytes)
      (fProj : ((cliGameSmSpec ℓ (BitVec 512)).Range q₀ × GameState BinState (Plain ℓ) Bytes) ×
          List (BitVec 512) → GameState BinState (Plain ℓ) Bytes),
      gsProjIn = mapSt CliPartyState.bin gsIn →
      gsIn.st = gs.st →
      (∀ r gsOut w,
        mapSt CliPartyState.bin (fDir ((r, gsOut), w)) = fProj ((r, mapSt CliPartyState.bin gsOut), w) ∧
        (fDir ((r, gsOut), w)).st = gsOut.st) →
      (Prod.map (Prod.map (Prod.map id projCliDrv) id) id <$>
        ((((cliOracleImplRM CliPartyState.bin
            (smSchemeCoinLogged (Dir.cliPqScheme run ℓ bi (gs.st .A) (gs.st .B)))
            (2 + 1) qep (cliConfigSpkS decT encT) q₀).run gsIn).run) >>= fun x =>
          pure (((x.1.1,
            { cds with
              bhInsts := cds.bhInsts.set i { bi with gs := some (cliMapGameState CliPartyState.bin (fDir x)) },
              instMeta := cds.instMeta.set i (bhMetaAfterSM cds.toModelDriverState bi im q₀ x.1.1),
              instGs := cds.instGs.set i (some (fDir x)) }), kst), x.2)) =
       ((((oracleImplRM
            (smSchemeCoinLogged (cliPqScheme run W ℓ biProj (cliPqSigsOf kst bi) biProj.stA0 biProj.stB0))
            (2 + 1) qep (bhConfigSpkS decT encT) q₀).run gsProjIn).run) >>= fun x =>
          pure (((x.1.1,
            { projCliDrv cds with
              bhInsts := (projCliDrv cds).bhInsts.set i { biProj with gs := some (fProj x) },
              instMeta := (projCliDrv cds).instMeta.set i (bhMetaAfterSM (projCliDrv cds) biProj im q₀ x.1.1) }),
            kst), x.2))) ∧
      ∀ z ∈ support
        ((((cliOracleImplRM CliPartyState.bin
            (smSchemeCoinLogged (Dir.cliPqScheme run ℓ bi (gs.st .A) (gs.st .B)))
            (2 + 1) qep (cliConfigSpkS decT encT) q₀).run gsIn).run) >>= fun x =>
          pure (((x.1.1,
            { cds with
              bhInsts := cds.bhInsts.set i { bi with gs := some (cliMapGameState CliPartyState.bin (fDir x)) },
              instMeta := cds.instMeta.set i (bhMetaAfterSM cds.toModelDriverState bi im q₀ x.1.1),
              instGs := cds.instGs.set i (some (fDir x)) }), kst), x.2)),
        CliRetainedStateInv W z.1.1.2 z.1.2 := by
    intro q₀ gsIn gsProjIn fDir fProj hgsIn_map hgsIn_st hpost
    have hGsIn : ∀ P, CliPartyDirInv W bi (cliPqSigsOf kst bi) P (gsIn.st P) := fun P => by
      rw [hgsIn_st]; exact hGs P
    obtain ⟨horacle_eq, horacle_inv⟩ :=
      cliOracleImplRM_coinLogged_step hCli hℓ qep decT encT bi (some (mapSt CliPartyState.bin gs))
        (cliPqSigsOf kst bi) (gs.st .A) (gs.st .B) bi.stA0 bi.stB0 gsIn hGsIn q₀
    subst hgsIn_map
    have hscheme_eq : cliPqScheme run W ℓ biProj (cliPqSigsOf kst bi) biProj.stA0 biProj.stB0 =
        cliPqScheme run W ℓ biProj (cliPqSigsOf kst bi) bi.stA0 bi.stB0 := rfl
    rw [hscheme_eq, ← horacle_eq, map_bind, bind_map_left]
    refine ⟨bind_congr_of_forall_mem_support _ fun ⟨⟨r, gsOut⟩, w⟩ _ => ?_, ?_⟩
    · obtain ⟨hgs'_map, _⟩ := hpost r gsOut w
      have him : bhMetaAfterSM (projCliDrv cds) biProj im q₀ r =
          bhMetaAfterSM cds.toModelDriverState bi im q₀ r := rfl
      simp only [map_pure, Prod.map_apply, id_eq, him]
      congr 4
      unfold projCliDrv projInsts cliMapGameState
      dsimp only [Option.map]
      rw [zipWith_set_ret]
      dsimp only [Option.map]
      rw [hgs'_map]
    · intro z hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨⟨⟨r, gsOut⟩, w⟩, hro, hz⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨_, hgs'_st⟩ := hpost r gsOut w
      have hGsOut := horacle_inv ((r, gsOut), w) hro
      have hlt_bi : i < cds.bhInsts.length := by
        by_contra hcon
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hcon)] at hbi
        cases hbi
      have hlt_gs : i < cds.instGs.length := hInv.1 ▸ hlt_bi
      refine ⟨by simp [hInv.1], fun j bj hj => ?_⟩
      by_cases hji : i = j
      · subst hji
        rw [List.getElem?_set_self hlt_bi] at hj
        simp only [Option.some.injEq] at hj
        subst hj
        rw [List.getElem?_set_self hlt_gs]
        refine ⟨⟨_, rfl, rfl⟩, hsig, fun gs'' hgs'' P => ?_⟩
        simp only [Option.some.injEq] at hgs''
        subst hgs''
        change CliPartyDirInv W
          { bi with gs := some (cliMapGameState CliPartyState.bin (fDir ((r, gsOut), w))) }
          (cliPqSigsOf kst bi) P _
        rw [cliPartyDirInv_bi_gs W bi
          (some (cliMapGameState CliPartyState.bin (fDir ((r, gsOut), w)))) bi.gs, hgs'_st]
        exact hGsOut P
      · rw [List.getElem?_set_ne hji] at hj
        rw [List.getElem?_set_ne hji]
        exact hInv.2 j bj hj
  unfold dirRunStdSMCoinLogged cliRunStdSMCoinLogged
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
    StateT.run_pure, writerT_run_bind, writerT_run_pure, pure_bind, bind_assoc,
    map_pure, Prod.map_apply, id_eq, List.append_nil, hsigs_biProj]
  rcases q with (((q_tr | q_ch) | ⟨p, c⟩) | q_inj) | q_corr
  · dsimp only
    exact hstep _ gs (mapSt CliPartyState.bin gs) (fun x => x.1.2) (fun x => x.1.2)
      rfl rfl (fun _ _ _ => ⟨rfl, rfl⟩)
  · dsimp only
    exact hstep _ gs (mapSt CliPartyState.bin gs) (fun x => x.1.2) (fun x => x.1.2)
      rfl rfl (fun _ _ _ => ⟨rfl, rfl⟩)
  · cases p
    · dsimp only
      exact hstep _ gs (mapSt CliPartyState.bin gs) (fun x => x.1.2) (fun x => x.1.2)
        rfl rfl (fun _ _ _ => ⟨rfl, rfl⟩)
    · refine hstep (.inl (.inl (.inr (.B, c)))) _ _ _ _
        (bhAlignTransForBob_mapSt' CliPartyState.bin im.bobAccepted bi.meA.regId bi.hdr c gs)
        (bhAlignTransForBob_st' im.bobAccepted bi.meA.regId bi.hdr c gs) ?_
      intro r gsOut _
      rcases r with _ | (_ | _)
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · dsimp only
        rw [bhAlignTransForBob_mapSt' CliPartyState.bin im.bobAccepted bi.meA.regId bi.hdr c gs,
          mapSt_inTransit]
        cases (bhAlignTransForBob im.bobAccepted bi.meA.regId bi.hdr c gs).inTransit .A c <;>
          exact ⟨rfl, rfl⟩
  · dsimp only
    exact hstep _ gs (mapSt CliPartyState.bin gs) (fun x => x.1.2) (fun x => x.1.2)
      rfl rfl (fun _ _ _ => ⟨rfl, rfl⟩)
  · dsimp only
    exact hstep _ gs (mapSt CliPartyState.bin gs) (fun x => x.1.2) (fun x => x.1.2)
      rfl rfl (fun _ _ _ => ⟨rfl, rfl⟩)

private theorem dirStepLocalSMCoinLogged_step_proj {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (cds : CliDriverState S ℓ) (kst : SignalPqxdh.KeyIndState S)
    (hInv : CliRetainedStateInv W cds kst)
    (i : ℕ) (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : GameState CliPartyState (Plain ℓ) Bytes)
    (hbi : cds.bhInsts[i]? = some bi) (higs : cds.instGs[i]? = some (some gs))
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) :
    let biProj : ModelDriverInstance S ℓ := { bi with gs := some (mapSt CliPartyState.bin gs) }
    Prod.map (Prod.map (Prod.map id projCliDrv) id) id <$>
      ((((dirStepLocalSMCoinLogged S ℓ run qep decT encT cds i bi im gs q).run cds).run kst).run) =
      ((((cliStepLocalSMCoinLogged S ℓ run W qep decT encT (projCliDrv cds) i biProj im
          (mapSt CliPartyState.bin gs) q).run (projCliDrv cds)).run kst).run) ∧
    ∀ z ∈ support
        ((((dirStepLocalSMCoinLogged S ℓ run qep decT encT cds i bi im gs q).run cds).run kst).run),
      CliRetainedStateInv W z.1.1.2 z.1.2 := by
  rcases q with (((q₁ | q₂) | ⟨p, c⟩) | ⟨p, c⟩) | p
  · exact dirRunStdSMCoinLogged_step_proj hCli hℓ qep decT encT cds kst hInv i bi im gs hbi higs _
  · exact dirRunStdSMCoinLogged_step_proj hCli hℓ qep decT encT cds kst hInv i bi im gs hbi higs _
  · cases p with
    | A =>
      dsimp only [dirStepLocalSMCoinLogged, cliStepLocalSMCoinLogged]
      by_cases hd : (bhDecodePreKeyMsgE c).isSome = true
      · simp only [hd, ↓reduceIte, StateT.run_pure, writerT_run_pure, map_pure, Prod.map_apply,
          id_eq, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
      · simp only [Bool.not_eq_true] at hd; rw [hd]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact dirRunStdSMCoinLogged_step_proj hCli hℓ qep decT encT cds kst hInv i bi im gs hbi higs _
    | B =>
      dsimp only [dirStepLocalSMCoinLogged, cliStepLocalSMCoinLogged]
      by_cases hn : (bhPartneredInnerBytes im.bobAccepted bi.meA.regId bi.hdr c).isNone = true
      · simp only [hn, ↓reduceIte, StateT.run_pure, writerT_run_pure, map_pure, Prod.map_apply,
          id_eq, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
      · simp only [Bool.not_eq_true] at hn; rw [hn]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact dirRunStdSMCoinLogged_step_proj hCli hℓ qep decT encT cds kst hInv i bi im gs hbi higs _
  · cases p with
    | A =>
      dsimp only [dirStepLocalSMCoinLogged, cliStepLocalSMCoinLogged]
      by_cases hd : (bhDecodePreKeyMsgE c).isSome = true
      · simp only [hd, ↓reduceIte, StateT.run_pure, writerT_run_pure, map_pure, Prod.map_apply,
          id_eq, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
      · simp only [Bool.not_eq_true] at hd; rw [hd]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact dirRunStdSMCoinLogged_step_proj hCli hℓ qep decT encT cds kst hInv i bi im gs hbi higs _
    | B =>
      dsimp only [dirStepLocalSMCoinLogged, cliStepLocalSMCoinLogged]
      have hit_eq :
          bhPartneredInTransitA true bi.meA.regId bi.hdr c (mapSt CliPartyState.bin gs) =
            bhPartneredInTransitA true bi.meA.regId bi.hdr c gs := rfl
      rw [hit_eq]
      by_cases hb : (!im.bobAccepted) = true
      · simp only [hb, ↓reduceIte, StateT.run_pure, writerT_run_pure, map_pure, Prod.map_apply,
          id_eq, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
      · simp only [Bool.not_eq_true] at hb; rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hg : ((bhPartneredInnerBytes true bi.meA.regId bi.hdr c).isNone ||
            bhPartneredInTransitA true bi.meA.regId bi.hdr c gs) = true
        · simp only [hg, ↓reduceIte, StateT.run_pure, writerT_run_pure, map_pure, Prod.map_apply,
            id_eq, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
        · simp only [Bool.not_eq_true] at hg; rw [hg]; simp only [Bool.false_eq_true, ↓reduceIte]
          exact dirRunStdSMCoinLogged_step_proj hCli hℓ qep decT encT cds kst hInv i bi im gs hbi higs _
  · exact dirRunStdSMCoinLogged_step_proj hCli hℓ qep decT encT cds kst hInv i bi im gs hbi higs _

private theorem dirDrvSMCoinLogged_step_proj {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (cds : CliDriverState S ℓ) (kst : SignalPqxdh.KeyIndState S)
    (hInv : CliRetainedStateInv W cds kst)
    (tq : (cliGameDrSpec ℓ (BitVec 512)).Domain) :
    Prod.map (Prod.map (Prod.map id projCliDrv) id) id <$>
      ((((dirDrvSMCoinLogged S ℓ run qep decT encT
          (liftQueryImplStateT2 (n := CoinLogM)
            (bhNoExtWithSpqr : QueryImpl _ (CliDrvM S ℓ))) tq).run cds).run kst).run) =
      ((((cliDrvSMCoinLogged S ℓ run W qep decT encT
          (liftQueryImplStateT2 (n := CoinLogM)
            (bhNoExtWithSpqr : QueryImpl _ (BHDrvM S ℓ))) tq).run (projCliDrv cds)).run kst).run) ∧
    ∀ z ∈ support
        ((((dirDrvSMCoinLogged S ℓ run qep decT encT
            (liftQueryImplStateT2 (n := CoinLogM)
              (bhNoExtWithSpqr : QueryImpl _ (CliDrvM S ℓ))) tq).run cds).run kst).run),
      CliRetainedStateInv W z.1.1.2 z.1.2 := by
  rcases tq with ⟨i, q⟩
  have hclean := bhDrvInstClean_projCliDrv hInv.1 i
  have himeta : (projCliDrv cds).instMeta = cds.instMeta := rfl
  unfold dirDrvSMCoinLogged cliDrvSMCoinLogged
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hclean, himeta]
  split_ifs
  · simp only [StateT.run_pure, writerT_run_pure, map_pure, Prod.map_apply, id_eq,
      support_pure, Set.mem_singleton_iff]
    exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
  · rcases hbi : cds.bhInsts[i]? with _ | bi
    · have hproj_none : (projCliDrv cds).bhInsts[i]? = none := by
        unfold projCliDrv projInsts; dsimp only
        rw [zipWith_getElem?_ret, hbi]
      rw [hproj_none]
      simp only [StateT.run_pure, writerT_run_pure, map_pure, Prod.map_apply, id_eq,
        support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
    · obtain ⟨⟨gsOpt, higs, _⟩, _⟩ := hInv.2 i bi hbi
      have hproj_some : (projCliDrv cds).bhInsts[i]? =
          some { bi with gs := gsOpt.map (mapSt CliPartyState.bin) } := by
        unfold projCliDrv projInsts; dsimp only
        rw [zipWith_getElem?_ret, hbi, higs]
      rw [hproj_some, higs]
      rcases cds.instMeta[i]? with _ | im
      · simp only [StateT.run_pure, writerT_run_pure, map_pure, Prod.map_apply, id_eq,
          support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
      · dsimp only
        have hik_eq : bhInstIkACorrupted (projCliDrv cds)
            { bi with gs := gsOpt.map (mapSt CliPartyState.bin) } =
            bhInstIkACorrupted cds.toModelDriverState bi := rfl
        rw [hik_eq]
        split_ifs
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
            writerT_run_pure, pure_bind, map_pure, Prod.map_apply, id_eq]
          refine ⟨rfl, fun z hz => ?_⟩
          simp only [support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact cliRetainedStateInv_of_spkLookup hInv rfl rfl (fun _ _ h => h)
        · cases gsOpt with
          | none =>
            dsimp only [Option.map]
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, writerT_run_bind,
              writerT_run_pure, pure_bind]
            have hext₁ : WriterT.run (((liftQueryImplStateT2 (n := CoinLogM)
                (bhNoExtWithSpqr : QueryImpl _ (CliDrvM S ℓ)) q).run cds).run kst) =
                pure (((bhSmDefaultWithSpqr q, cds), kst), []) := rfl
            have hext₂ : WriterT.run (((liftQueryImplStateT2 (n := CoinLogM)
                (bhNoExtWithSpqr : QueryImpl _ (BHDrvM S ℓ)) q).run (projCliDrv cds)).run kst) =
                pure (((bhSmDefaultWithSpqr q, projCliDrv cds), kst), []) := rfl
            rw [hext₁, hext₂]
            simp only [pure_bind, map_pure, Prod.map_apply, id_eq, List.nil_append]
            have hm_eq : bhMetaAfterSM (projCliDrv cds) { bi with gs := none } im q
                (bhSmDefaultWithSpqr q) =
                bhMetaAfterSM cds.toModelDriverState bi im q (bhSmDefaultWithSpqr q) := rfl
            rw [hm_eq]
            refine ⟨rfl, fun z hz => ?_⟩
            simp only [support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact cliRetainedStateInv_of_spkLookup hInv rfl rfl (fun _ _ h => h)
          | some gs =>
            dsimp only [Option.map]
            exact dirStepLocalSMCoinLogged_step_proj hCli hℓ qep decT encT cds kst hInv i bi im gs hbi higs q

private theorem liftQueryImplStateT2_coinLogged_step_proj {ι : Type} {spec : OracleSpec ι}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {W : PEParams}
    {hDir : QueryImpl spec (CliDrvM S ℓ)} {hProj : QueryImpl spec (BHDrvM S ℓ)}
    {cds : CliDriverState S ℓ} {kst : SignalPqxdh.KeyIndState S} {q : spec.Domain}
    (hstep : Prod.map (Prod.map id projCliDrv) id <$> (((hDir q).run cds).run kst) =
        ((hProj q).run (projCliDrv cds)).run kst ∧
      ∀ z ∈ support (((hDir q).run cds).run kst), CliRetainedStateInv W z.1.2 z.2) :
    Prod.map (Prod.map (Prod.map id projCliDrv) id) id <$>
      ((((liftQueryImplStateT2 (n := CoinLogM) hDir q).run cds).run kst).run) =
      ((((liftQueryImplStateT2 (n := CoinLogM) hProj q).run (projCliDrv cds)).run kst).run) ∧
    ∀ z ∈ support ((((liftQueryImplStateT2 (n := CoinLogM) hDir q).run cds).run kst).run),
      CliRetainedStateInv W z.1.1.2 z.1.2 := by
  change Prod.map (Prod.map (Prod.map id projCliDrv) id) id <$>
      (liftM (((hDir q).run cds).run kst) : CoinLogM _).run =
      (liftM (((hProj q).run (projCliDrv cds)).run kst) : CoinLogM _).run ∧
    ∀ z ∈ support (liftM (((hDir q).run cds).run kst) : CoinLogM _).run,
      CliRetainedStateInv W z.1.1.2 z.1.2
  rw [writerT_run_liftM, writerT_run_liftM]
  refine ⟨?_, ?_⟩
  · rw [← hstep.1]
    simp [Functor.map_map]
  · intro z hz
    rw [map_eq_bind_pure_comp, mem_support_bind_iff] at hz
    obtain ⟨u, hu, hz⟩ := hz
    simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hstep.2 u hu

private theorem dirDrvImplCoinLogged_step_proj {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (P : SignalPqxdh.Primitives) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (mode : BHDrvMode S)
    (cds : CliDriverState S ℓ) (kst : SignalPqxdh.KeyIndState S)
    (hInv : CliRetainedStateInv W cds kst)
    (t : (cliGameSpec S ℓ (BitVec 512)).Domain) :
    Prod.map (Prod.map (Prod.map id projCliDrv) id) id <$>
      ((((dirDrvImplCoinLogged S ℓ P run W qep decT encT bhNoExtWithSpqr mode t).run cds).run kst).run) =
      ((((cliDrvImplCoinLogged S ℓ P run W qep decT encT bhNoExtWithSpqr mode t).run
          (projCliDrv cds)).run kst).run) ∧
    ∀ z ∈ support
        ((((dirDrvImplCoinLogged S ℓ P run W qep decT encT bhNoExtWithSpqr mode t).run cds).run kst).run),
      CliRetainedStateInv W z.1.1.2 z.1.2 := by
  rcases t with ((t_unif | t_ki) | t_ctl) | t_sm
  · change Prod.map (Prod.map (Prod.map id projCliDrv) id) id <$>
        ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (CliDrvMT S ℓ CoinLogM) t_unif).run cds).run kst).run =
        ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (BHDrvMCoinLogged S ℓ) t_unif).run
          (projCliDrv cds)).run kst).run ∧
      ∀ z ∈ support
        ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (CliDrvMT S ℓ CoinLogM) t_unif).run cds).run kst).run,
        CliRetainedStateInv W z.1.1.2 z.1.2
    simp only [QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
    dsimp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
      StateT.lift, StateT.run, StateT.bind, StateT.pure,
      WriterT.run, WriterT.mk, WriterT.liftTell]
    simp only [map_eq_bind_pure_comp]
    refine ⟨rfl, fun z hz => ?_⟩
    change z ∈ support
      ((PFunctor.FreeM.liftObj (OracleSpec.query t_unif) >>=
          pure ∘ fun a => (a, ([] : List (BitVec 512)))) >>=
        fun x => pure (((x.1, cds), kst), x.2)) at hz
    simp only [bind_assoc, Function.comp_apply, pure_bind, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hInv
  · exact liftQueryImplStateT2_coinLogged_step_proj
      (hDir := fun q => bhLiftCli (bhDrvKeyInd S ℓ P false q))
      (hProj := bhDrvKeyInd S ℓ P false)
      (bhDrvKeyInd_step_proj P t_ki cds kst hInv)
  · cases t_ctl with
    | startDR sid =>
      exact liftQueryImplStateT2_coinLogged_step_proj
        (hDir := Dir.cliDrvCtl S ℓ P run W mode)
        (hProj := cliDrvCtl S ℓ P run W mode)
        (cliDrvStart_step_proj hCli P mode sid cds kst hInv)
  · exact dirDrvSMCoinLogged_step_proj hCli hℓ qep decT encT cds kst hInv t_sm

private theorem simulateQ_twoState_coinLogged_proj {ι : Type} {ospec : OracleSpec.{0, 0} ι}
    {α σ₁ σ₂ τ : Type}
    (impl₁ : QueryImpl ospec (StateT σ₁ (StateT τ CoinLogM)))
    (impl₂ : QueryImpl ospec (StateT σ₂ (StateT τ CoinLogM)))
    (inv : σ₁ → τ → Prop) (proj : σ₁ → σ₂)
    (hstep : ∀ t s kst, inv s kst →
      Prod.map (Prod.map (Prod.map id proj) id) id <$> ((((impl₁ t).run s).run kst).run) =
        ((((impl₂ t).run (proj s)).run kst).run) ∧
      ∀ z ∈ support ((((impl₁ t).run s).run kst).run), inv z.1.1.2 z.1.2)
    (oa : OracleComp ospec α) :
    ∀ (s : σ₁) (kst : τ), inv s kst →
      Prod.map (Prod.map (Prod.map id proj) id) id <$>
        ((((simulateQ impl₁ oa).run s).run kst).run) =
        ((((simulateQ impl₂ oa).run (proj s)).run kst).run) ∧
      ∀ z ∈ support ((((simulateQ impl₁ oa).run s).run kst).run), inv z.1.1.2 z.1.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s kst hs
    simp only [simulateQ_pure, StateT.run_pure, writerT_run_pure, map_pure, support_pure,
      Set.mem_singleton_iff]
    exact ⟨rfl, fun z hz => by subst hz; exact hs⟩
  | query_bind t k ih =>
    intro s kst hs
    obtain ⟨hproj_t, hinv_t⟩ := hstep t s kst hs
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, writerT_run_bind, map_bind]
    refine ⟨?_, ?_⟩
    · rw [← hproj_t, bind_map_left]
      exact bind_congr_of_forall_mem_support _ fun z hz => by
        have h_ih := (ih z.1.1.1 z.1.1.2 z.1.2 (hinv_t z hz)).1
        dsimp only [Prod.map, id] at h_ih ⊢
        rw [← h_ih, Functor.map_map, Functor.map_map]
        rfl
    · intro w hw
      rw [mem_support_bind_iff] at hw
      obtain ⟨z, hz, hw⟩ := hw
      rw [map_eq_bind_pure_comp, mem_support_bind_iff] at hw
      obtain ⟨u, hu, hw⟩ := hw
      simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hw
      subst hw
      exact (ih z.1.1.1 z.1.1.2 z.1.2 (hinv_t z hz)).2 u hu

private theorem dirPqExpCoinLogged_eq_projCoinLogged
    {Pt : Type} (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (ℓ qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6) :
    dirPqExpCoinLogged S run X W ℓ qep decT encT A =
      cliPqExpProjCoinLogged S run X W ℓ qep decT encT A := by
  unfold dirPqExpCoinLogged cliPqExpProjCoinLogged
  simp only [writerT_run_bind, writerT_run_liftM, bind_map_left, List.nil_append]
  refine bind_congr_of_forall_mem_support ($ᵗ Bool) fun b _ => ?_
  congr 1
  let mode : BHDrvMode S := fun _ _ _ _ _ => some b
  let kst₀ := SignalPqxdh.KeyIndState.empty S true
  obtain ⟨hsim_eq, hsim_inv⟩ := simulateQ_twoState_coinLogged_proj
    (dirDrvImplCoinLogged S ℓ (modelPrims X W) run W qep decT encT bhNoExtWithSpqr mode)
    (cliDrvImplCoinLogged S ℓ (modelPrims X W) run W qep decT encT bhNoExtWithSpqr mode)
    (CliRetainedStateInv W) projCliDrv
    (fun t cds kst hInv =>
      dirDrvImplCoinLogged_step_proj hCli hℓ (modelPrims X W) qep decT encT mode cds kst hInv t)
    A.run {} kst₀ (cliRetainedStateInv_init W kst₀)
  change (((((simulateQ (dirDrvImplCoinLogged S ℓ (modelPrims X W) run W qep decT encT
          bhNoExtWithSpqr mode) A.run).run {}).run kst₀).run) >>= _) =
    (((((simulateQ (cliDrvImplCoinLogged S ℓ (modelPrims X W) run W qep decT encT
          bhNoExtWithSpqr mode) A.run).run (projCliDrv {})).run kst₀).run) >>= _)
  rw [← hsim_eq, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun z hz => ?_
  have hInv_z := hsim_inv z hz
  dsimp only [Prod.map, id]
  split_ifs
  · rfl
  · simp only [writerT_run_pure, map_pure, Prod.map_apply, id_eq]
    rw [driverSomeInstanceWon_projCliDrv hInv_z b]

/-- Projecting `cliPqxdhExpFlagged`'s input log with `sendTapesOfInputs` equals mapping
`cliPqExpProjCoinLogged`'s send-coin log with `coinBytes` (`DEV-CLI18`). -/
theorem cliPqxdhExpFlagged_sendTapes_eq_projCoinLogged
    {Pt : Type} (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (ℓ qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6) :
    Prod.map id sendTapesOfInputs <$> cliPqxdhExpFlagged S run X W ℓ qep decT encT A =
      Prod.map id (List.map coinBytes) <$> cliPqExpProjCoinLogged S run X W ℓ qep decT encT A := by
  rw [cliPqxdhExpFlagged_sendTapes_eq_dirCoinLogged,
    dirPqExpCoinLogged_eq_projCoinLogged S run X W ℓ qep decT encT A hCli hℓ]

end Computational.Proofs.LibsignalCli.CliKemFailCouplingHopA
