/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPqOomGame
public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Composition.StatementModel
public import Computational.Proofs.LibsignalCli.StatementPqSecure
public import Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs
public import Computational.Proofs.LibsignalCli.CliPqAdapterDefs
public import Computational.Proofs.LibsignalCli.CliPqAdapterRemoteIdInv
import Computational.Proofs.LibsignalCli.Oom.Faithful

/-!
# Two-layer `CoinLogM` combinators and non-send composed adapter reductions

Defines `forgetCoinS2`, `liftCoinS2`, and `cliComposedAdapterImplWithCoinLogged`, and proves
empty-log reductions on non-send/challenge queries.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBCoreAux

open OracleComp OracleSpec
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SignalSession (CliRun)
open CryptoVerification.E2E (BHDrvM BHDrvMode BHE2EDrvState BHE2ESmResp BHModelInst BhShallowRed
  BinState Bytes CliAdapterState CliE2ERemoteIdInv CliGameAdversary L_bh ModelDriverInstance
  ModelDriverInstanceMeta ModelDriverState PEParams bhAlignTransForBob bhConfigSpkS
  bhDecodePreKeyMsgE bhDrvInstClean bhDrvKeyInd bhDrvKiQueryOk bhE2EDrvInstClean bhE2EInstIkACorr
  bhE2EMirror bhE2EStepLocalSm bhExpectedPreKeyMsg bhFwdU bhGameSpec bhHdrOfPreKeyMsg bhInitRegId
  bhInstIkACorrupted bhIsBobAcceptSMResp bhIsBobRecvSMQuery bhMetaAfterSM bhNoOpkRespPromoted
  bhPackSmResp bhPartneredInTransitA bhPartneredInnerBytes bhShallowAdapterGameStep
  bhShallowAdapterImpl bhShallowParsePreKey bhShallowQueryTarget bhShallowSplitWhisper
  bhShallowStepMirrorGuard bhShallowWrapWhisper bhSmDefaultWithSpqr bhTargetGameSpec
  cliAdapterInitState cliAdapterStepImplWith cliComposedAdapterImplWith
  cliComposedAdapterImplWith_preserves_remoteIdInv cliDrvCtl cliDrvImpl cliDrvSM
  cliE2EDrvImplWith cliGameAdversaryReassoc cliGameDrSpec cliGameSmSpec cliGameSpec cliPqScheme
  cliPqSigsOf cliRunStdSM cliStepLocalSM compositionLocalStart configRefuseEarlyBobCorr deliverRM
  injectRM liftQueryImplStateT2 liftStateT oracleImplRM paramsIdsWithSpqr sessionSchemeFixedSpk
  shortCiphertext smSchemeCoinLogged wirePrekey)
open Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs (BHDrvMCoinLogged CoinLogM
  bhE2EStepLocalSmCoinLogged cliDrvImplCoinLogged cliDrvSMCoinLogged cliE2EDrvImplWithCoinLogged
  cliRunStdSMCoinLogged cliStepLocalSMCoinLogged forgetCoinS1 forgetCoinS1_bind
  forgetCoinS1_cliE2EDrvImplWithCoinLogged forgetCoinS1_get forgetCoinS1_lift
  forgetCoinS1_liftM_prob forgetCoinS1_oracleImplRM_smSchemeCoinLogged forgetCoinS1_pure
  forgetCoinS1_run forgetCoinS1_set forgetCoinS1_simulateQ forgetCoinW forgetCoinW_liftM)
open Computational.Proofs.LibsignalCli.Oom.Faithful (instLawfulMonadWriterTList)

/-! ## Two-layer `CoinLogM` forget combinators -/

@[simp] private theorem stateT_run_ite {σ : Type} {m : Type → Type} {α : Type}
    (c : Prop) [Decidable c] (t e : StateT σ m α) (s : σ) :
    (if c then t else e).run s = if c then t.run s else e.run s := by
  split_ifs <;> rfl

def forgetCoinS2 {σ₁ σ₂ α : Type} (m : StateT σ₁ (StateT σ₂ CoinLogM) α) :
    StateT σ₁ (StateT σ₂ ProbComp) α :=
  fun s₁ => forgetCoinS1 (m.run s₁)

@[simp] private theorem forgetCoinS2_run {σ₁ σ₂ α : Type}
    (m : StateT σ₁ (StateT σ₂ CoinLogM) α) (s₁ : σ₁) :
    (forgetCoinS2 m).run s₁ = forgetCoinS1 (m.run s₁) := rfl

@[simp] private theorem forgetCoinS2_pure {σ₁ σ₂ α : Type} (a : α) :
    forgetCoinS2 (pure a : StateT σ₁ (StateT σ₂ CoinLogM) α) = pure a := by
  ext s₁ s₂; simp

@[simp] private theorem forgetCoinS2_map {σ₁ σ₂ α β : Type}
    (f : α → β) (m : StateT σ₁ (StateT σ₂ CoinLogM) α) :
    forgetCoinS2 (f <$> m) = f <$> forgetCoinS2 m := by
  ext s₁ s₂; simp

@[simp] private theorem forgetCoinS2_bind {σ₁ σ₂ α β : Type}
    (m : StateT σ₁ (StateT σ₂ CoinLogM) α) (k : α → StateT σ₁ (StateT σ₂ CoinLogM) β) :
    forgetCoinS2 (m >>= k) = forgetCoinS2 m >>= fun a => forgetCoinS2 (k a) := by
  ext s₁ s₂; simp

@[simp] private theorem forgetCoinS2_get {σ₁ σ₂ : Type} :
    forgetCoinS2 (get : StateT σ₁ (StateT σ₂ CoinLogM) σ₁) = get := by
  ext s₁ s₂; simp

@[simp] private theorem forgetCoinS2_set {σ₁ σ₂ : Type} (s₁' : σ₁) :
    forgetCoinS2 (set s₁' : StateT σ₁ (StateT σ₂ CoinLogM) PUnit) = set s₁' := by
  ext s₁ s₂; simp

@[simp] private theorem forgetCoinS2_lift {σ₁ σ₂ α : Type} (m : StateT σ₂ CoinLogM α) :
    forgetCoinS2 (StateT.lift m : StateT σ₁ (StateT σ₂ CoinLogM) α) = StateT.lift (forgetCoinS1 m) := by
  ext s₁ s₂; simp [StateT.run_lift]

@[simp] private theorem forgetCoinS2_liftM_prob {σ₁ σ₂ α : Type} (c : ProbComp α) :
    forgetCoinS2 (liftM c : StateT σ₁ (StateT σ₂ CoinLogM) α) = liftM c := by
  change forgetCoinS2 (StateT.lift (liftM c)) = StateT.lift (liftM c)
  rw [forgetCoinS2_lift, forgetCoinS1_liftM_prob]

@[simp] private theorem forgetCoinS2_liftQueryImplStateT2 {ι σ₁ σ₂ : Type} {spec : OracleSpec ι}
    (h : QueryImpl spec (StateT σ₁ (StateT σ₂ ProbComp))) (q : spec.Domain) :
    forgetCoinS2 (liftQueryImplStateT2 (n := CoinLogM) h q) = h q := by
  ext s₁ s₂; exact forgetCoinW_liftM (((h q).run s₁).run s₂)

private theorem forgetCoinS2_add {ι₁ ι₂ σ₁ σ₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {h₁ : QueryImpl spec₁ (StateT σ₁ (StateT σ₂ CoinLogM))}
    {h₂ : QueryImpl spec₂ (StateT σ₁ (StateT σ₂ CoinLogM))}
    {g₁ : QueryImpl spec₁ (StateT σ₁ (StateT σ₂ ProbComp))}
    {g₂ : QueryImpl spec₂ (StateT σ₁ (StateT σ₂ ProbComp))}
    (hh₁ : ∀ q, forgetCoinS2 (h₁ q) = g₁ q) (hh₂ : ∀ q, forgetCoinS2 (h₂ q) = g₂ q)
    (q : (spec₁ + spec₂).Domain) :
    forgetCoinS2 ((h₁ + h₂) q) = (g₁ + g₂) q := by
  rcases q with q₁ | q₂
  · exact hh₁ q₁
  · exact hh₂ q₂

private theorem forgetCoinS2_cliRunStdSMCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : ModelDriverState S ℓ) (i : ℕ) (bi : ModelDriverInstance S ℓ)
    (im : ModelDriverInstanceMeta S)
    (gs : CryptoGames.SM.GameState BinState (Plain ℓ) Bytes)
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) :
    forgetCoinS2 (cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs q) =
      cliRunStdSM S ℓ run W qep decT encT ds i bi im gs q := by
  unfold cliRunStdSMCoinLogged cliRunStdSM
  simp only [forgetCoinS2_bind, forgetCoinS2_lift, forgetCoinS1_get]
  congr 1; funext kst
  simp only [forgetCoinS1_lift, ← forgetCoinS1_run,
    forgetCoinS1_oracleImplRM_smSchemeCoinLogged]
  rfl

private theorem forgetCoinS2_cliStepLocalSMCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : ModelDriverState S ℓ) (i : ℕ) (bi : ModelDriverInstance S ℓ)
    (im : ModelDriverInstanceMeta S)
    (gs : CryptoGames.SM.GameState BinState (Plain ℓ) Bytes)
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) :
    forgetCoinS2 (cliStepLocalSMCoinLogged S ℓ run W qep decT encT ds i bi im gs q) =
      cliStepLocalSM S ℓ run W qep decT encT ds i bi im gs q := by
  rcases q with (((q₁ | q₂) | ⟨p, c⟩) | ⟨p, c⟩) | q₅
  · exact forgetCoinS2_cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs _
  · exact forgetCoinS2_cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs _
  · cases p <;> dsimp only [cliStepLocalSMCoinLogged, cliStepLocalSM] <;> split_ifs <;>
      first | exact forgetCoinS2_pure _ |
        exact forgetCoinS2_cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs _
  · cases p <;> dsimp only [cliStepLocalSMCoinLogged, cliStepLocalSM] <;> split_ifs <;>
      first | exact forgetCoinS2_pure _ |
        exact forgetCoinS2_cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs _
  · exact forgetCoinS2_cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs _

private theorem forgetCoinS2_cliDrvSMCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (q : (cliGameDrSpec ℓ (BitVec 512)).Domain) :
    forgetCoinS2 (cliDrvSMCoinLogged S ℓ run W qep decT encT
        (liftQueryImplStateT2 (n := CoinLogM) ext) q) =
      cliDrvSM S ℓ run W qep decT encT ext q := by
  rcases q with ⟨i, sq⟩
  unfold cliDrvSMCoinLogged cliDrvSM
  simp only [forgetCoinS2_bind, forgetCoinS2_get]
  congr 1; funext ds
  split_ifs
  · exact forgetCoinS2_pure _
  · rcases hbi : ds.bhInsts[i]? with _ | bi
    · exact forgetCoinS2_pure _
    · rcases him : ds.instMeta[i]? with _ | im
      · exact forgetCoinS2_pure _
      · dsimp only
        split_ifs
        · simp
        · rcases hgs : bi.gs with _ | gs
          · simp
          · exact forgetCoinS2_cliStepLocalSMCoinLogged S ℓ run W qep decT encT ds i bi im gs sq

theorem forgetCoinS2_cliDrvImplCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ)) (mode : BHDrvMode S)
    (q : (cliGameSpec S ℓ (BitVec 512)).Domain) :
    forgetCoinS2 (cliDrvImplCoinLogged S ℓ P run W qep decT encT ext mode q) =
      cliDrvImpl S ℓ P run W qep decT encT ext mode q := by
  unfold cliDrvImplCoinLogged cliDrvImpl
  refine forgetCoinS2_add (forgetCoinS2_add (forgetCoinS2_add ?_ ?_) ?_) ?_ q
  · intro uq
    rw [QueryImpl.liftTarget_apply, QueryImpl.liftTarget_apply, forgetCoinS2_liftM_prob]
  · intro kq
    exact forgetCoinS2_liftQueryImplStateT2 (bhDrvKeyInd S ℓ P false) kq
  · intro cq
    exact forgetCoinS2_liftQueryImplStateT2 (cliDrvCtl S ℓ P run W mode) cq
  · exact forgetCoinS2_cliDrvSMCoinLogged S ℓ run W qep decT encT ext

/-! ## Empty-log lifts and non-send reductions -/

theorem writerT_run_liftM_prob {α : Type} (c : ProbComp α) :
    WriterT.run (liftM c : CoinLogM α) = (fun a => (a, ([] : List (BitVec 512)))) <$> c := rfl

theorem liftM_prob_pure {α : Type} (a : α) :
    (liftM (pure a : ProbComp α) : CoinLogM α) = pure a := by
  ext
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp

theorem liftM_prob_bind {α β : Type} (c : ProbComp α) (k : α → ProbComp β) :
    (liftM (c >>= k) : CoinLogM β) = (liftM c : CoinLogM α) >>= fun a => liftM (k a) := by
  ext
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp [map_eq_bind_pure_comp, bind_assoc]

def liftCoinS2 {σ₁ σ₂ α : Type} (m : StateT σ₁ (StateT σ₂ ProbComp) α) :
    StateT σ₁ (StateT σ₂ CoinLogM) α :=
  fun s₁ s₂ => liftM ((m.run s₁).run s₂)

theorem writerT_run_liftCoinS2 {σ₁ σ₂ α : Type}
    (m : StateT σ₁ (StateT σ₂ ProbComp) α) (s₁ : σ₁) (s₂ : σ₂) :
    WriterT.run (((liftCoinS2 m).run s₁).run s₂) =
      (fun x => (x, ([] : List (BitVec 512)))) <$> ((m.run s₁).run s₂) := rfl

def isSendOrChallSM {St Msg Coins C : Type} :
    (CryptoGames.SM.spec St Msg Coins C).Domain → Bool
  | .inl (.inl (.inl _)) => true
  | _ => false

def isSendOrChallCli {S : SignalPqxdh.Setup} {ℓ : ℕ} :
    (cliGameSpec S ℓ (BitVec 512)).Domain → Bool
  | .inr ⟨_, sq⟩ => isSendOrChallSM sq
  | _ => false

@[simp] private theorem writerT_run_ite {ω : Type} {m : Type → Type} {α : Type}
    (c : Prop) [Decidable c] (t e : WriterT ω m α) :
    WriterT.run (if c then t else e) = if c then WriterT.run t else WriterT.run e := by
  split_ifs <;> rfl

@[simp] private theorem liftStateT_run {σ α : Type} (m : StateT σ ProbComp α) (s : σ) :
    (liftStateT (n := CoinLogM) m).run s = liftM (m.run s) := rfl

private theorem oracleImplRM_smSchemeCoinLogged_nonSend_eq_liftStateT
    {Key St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (sch : CryptoGames.SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : CryptoGames.SM.ConfigR St Msg C)
    (q : (CryptoGames.SM.spec St Msg (BitVec 512) C).Domain)
    (hNonSend : isSendOrChallSM q = false) :
    oracleImplRM (smSchemeCoinLogged sch) Δ qep cfg q =
      liftStateT (n := CoinLogM) (CryptoGames.SM.oracleImplR sch Δ qep cfg q) := by
  have hrecv : ∀ s c rc, (smSchemeCoinLogged sch).receive s c rc =
      liftM (pure (sch.receive s c rc) : ProbComp _) := by
    intro s c rc; simp [smSchemeCoinLogged, liftM_prob_pure]
  rcases q with (((q₁ | q₂) | ⟨p, c⟩) | ⟨p, c⟩) | p
  · simp [isSendOrChallSM] at hNonSend
  · simp [isSendOrChallSM] at hNonSend
  · change deliverRM (smSchemeCoinLogged sch) cfg (p, c) =
      liftStateT (n := CoinLogM) (CryptoGames.SM.deliverR sch cfg (p, c))
    ext gs
    change WriterT.run ((deliverRM (smSchemeCoinLogged sch) cfg (p, c)).run gs) =
      WriterT.run (liftM ((CryptoGames.SM.deliverR sch cfg (p, c)).run gs) : CoinLogM _)
    unfold deliverRM CryptoGames.SM.deliverR
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases gs.win
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases gs.inTransit p.other c with _ | r
      · simp [StateT.run_pure]
      · simp only [StateT.run_bind, StateT.run_lift, StateT.run_monadLift, monadLift_self,
          hrecv, pure_bind, bind_assoc, writerT_run_liftM_prob, WriterT.run_bind]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        congr 1; funext rc
        rcases sch.receive (gs.st p) c rc with _ | ⟨st', t', i', m'⟩ <;>
          dsimp only <;> split_ifs <;>
          simp [StateT.run_pure, StateT.run_set, WriterT.run_pure]
    · simp [StateT.run_pure]
  · change injectRM (smSchemeCoinLogged sch) Δ qep cfg (p, c) =
      liftStateT (n := CoinLogM) (CryptoGames.SM.injectR sch Δ qep cfg (p, c))
    ext gs
    change WriterT.run ((injectRM (smSchemeCoinLogged sch) Δ qep cfg (p, c)).run gs) =
      WriterT.run (liftM ((CryptoGames.SM.injectR sch Δ qep cfg (p, c)).run gs) : CoinLogM _)
    unfold injectRM CryptoGames.SM.injectR
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases (gs.win || (gs.inTransit p.other c).isSome || !(gs.safeInj Δ) || !(cfg.injOK c))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        StateT.run_monadLift, monadLift_self, hrecv, pure_bind, bind_assoc,
        writerT_run_liftM_prob, WriterT.run_bind]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      congr 1; funext rc
      rcases sch.receive (gs.st p) c rc with _ | ⟨st', t', i', m'⟩ <;> dsimp only
      · simp [StateT.run_pure, WriterT.run_pure]
      · split_ifs <;>
          simp [StateT.run_pure, StateT.run_set, WriterT.run_pure]
    · simp [StateT.run_pure]
  · rfl

private theorem bhE2EStepLocalSmCoinLogged_nonSend_eq_liftM
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hNonSend : isSendOrChallSM q = false) :
    bhE2EStepLocalSmCoinLogged C K qep decT encT σ i q =
      liftM (bhE2EStepLocalSm C K qep decT encT σ i q) := by
  have hPure : ∀ (x : BHE2ESmResp ℓ × BHE2EDrvState S ℓ),
      (pure x : CoinLogM _) = liftM (pure x : ProbComp _) :=
    fun x => (liftM_prob_pure x).symm
  unfold bhE2EStepLocalSmCoinLogged bhE2EStepLocalSm
  cases (!bhE2EDrvInstClean σ i)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases σ.insts[i]? with _ | d
    · exact hPure _
    · rcases σ.instMeta[i]? with _ | im
      · exact hPure _
      · dsimp only
        cases (!im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rcases d.gs with _ | gs
          · exact hPure _
          · dsimp only
            have hRunStd : ∀ (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
                isSendOrChallSM q' = false →
                (do
                  let spqr := spqrV1SessionUniformCoins C.F K
                  let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
                  let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
                  let (r, gs') ← (oracleImplRM (smSchemeCoinLogged sch) (2 + 1) qep cfg q').run gs
                  let accepted := bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                      instMeta := σ.instMeta.set i im' }
                  return (bhPackSmResp q' r, σ1) : CoinLogM _) =
                liftM (do
                  let spqr := spqrV1SessionUniformCoins C.F K
                  let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
                  let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
                  let (r, gs') ← (CryptoGames.SM.oracleImplR sch (2 + 1) qep cfg q').run gs
                  let accepted := bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                      instMeta := σ.instMeta.set i im' }
                  return (bhPackSmResp q' r, σ1)) := by
              intro q' hq'
              dsimp only
              rw [oracleImplRM_smSchemeCoinLogged_nonSend_eq_liftStateT _ _ _ _ q' hq', liftM_prob_bind]
              exact bind_congr fun ⟨r, gs'⟩ => hPure _
            rcases q with (((q₁ | q₂) | ⟨p, c⟩) | ⟨p, c⟩) | p
            · simp [isSendOrChallSM] at hNonSend
            · simp [isSendOrChallSM] at hNonSend
            · cases p <;> dsimp only
              · split_ifs; exact hPure _; exact hRunStd _ rfl
              · split_ifs
                · rcases bhDecodePreKeyMsgE c with _ | m <;> dsimp only
                  · exact hPure _
                  · split_ifs; exact hRunStd _ rfl; exact hPure _
                · rcases bhDecodePreKeyMsgE c with _ | m <;> dsimp only
                  · exact hRunStd _ rfl
                  · split_ifs; exact hRunStd _ rfl; exact hPure _
            · cases p <;> dsimp only
              · split_ifs; exact hPure _; exact hRunStd _ rfl
              · split_ifs
                · exact hPure _
                · rcases bhDecodePreKeyMsgE c with _ | m <;> dsimp only
                  · exact hRunStd _ rfl
                  · split_ifs; exact hRunStd _ rfl; exact hPure _
            · exact hRunStd _ rfl
        · exact hPure _
  · exact hPure _

theorem cliDrvImplCoinLogged_nonSend_eq_liftCoinS2
    (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ)) (mode : BHDrvMode S)
    (q : (cliGameSpec S ℓ (BitVec 512)).Domain)
    (hNonSend : isSendOrChallCli q = false) :
    cliDrvImplCoinLogged S ℓ P run W qep decT encT ext mode q =
      liftCoinS2 (cliDrvImpl S ℓ P run W qep decT encT ext mode q) := by
  rcases q with ((uq | kq) | cq) | ⟨i, sq⟩
  · ext ds0 kst0
    change WriterT.run (((((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (BHDrvMCoinLogged S ℓ)) uq).run ds0).run kst0) =
      WriterT.run (liftM (((((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (BHDrvM S ℓ)) uq).run ds0).run kst0) : CoinLogM _)
    rw [QueryImpl.liftTarget_apply, QueryImpl.liftTarget_apply]
    simp
  · rfl
  · rfl
  · dsimp only [cliDrvImplCoinLogged, cliDrvImpl]
    have hStd : ∀ ds bi im gs (q' : (cliGameSmSpec ℓ (BitVec 512)).Domain),
        isSendOrChallSM q' = false →
        cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs q' =
          liftCoinS2 (cliRunStdSM S ℓ run W qep decT encT ds i bi im gs q') := by
      intro ds bi im gs q' hq'
      ext ds0 kst0
      change WriterT.run (((cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs q').run ds0).run kst0) =
        WriterT.run (liftM (((cliRunStdSM S ℓ run W qep decT encT ds i bi im gs q').run ds0).run kst0) : CoinLogM _)
      unfold cliRunStdSMCoinLogged cliRunStdSM
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_monadLift, monadLift_self,
        StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure,
        oracleImplRM_smSchemeCoinLogged_nonSend_eq_liftStateT _ _ _ _ q' hq', liftStateT_run,
        bind_assoc]
      rw [liftM_prob_bind]
      exact congrArg WriterT.run (bind_congr fun ⟨r, gsOut⟩ => (liftM_prob_pure _).symm)
    have hLoc : ∀ ds bi im gs,
        cliStepLocalSMCoinLogged S ℓ run W qep decT encT ds i bi im gs sq =
          liftCoinS2 (cliStepLocalSM S ℓ run W qep decT encT ds i bi im gs sq) := by
      intro ds bi im gs
      rcases sq with (((q₁ | q₂) | ⟨p, c⟩) | ⟨p, c⟩) | p
      · simp [isSendOrChallCli, isSendOrChallSM] at hNonSend
      · simp [isSendOrChallCli, isSendOrChallSM] at hNonSend
      · cases p <;> dsimp only [cliStepLocalSMCoinLogged, cliStepLocalSM] <;> split_ifs
        · ext ds0 kst0; exact (liftM_prob_pure _).symm
        · exact hStd ds bi im gs _ rfl
        · ext ds0 kst0; exact (liftM_prob_pure _).symm
        · exact hStd ds bi im gs _ rfl
      · cases p <;> dsimp only [cliStepLocalSMCoinLogged, cliStepLocalSM] <;> split_ifs
        · ext ds0 kst0; exact (liftM_prob_pure _).symm
        · exact hStd ds bi im gs _ rfl
        · ext ds0 kst0; exact (liftM_prob_pure _).symm
        · ext ds0 kst0; exact (liftM_prob_pure _).symm
        · exact hStd ds bi im gs _ rfl
      · exact hStd ds bi im gs _ rfl
    ext ds0 kst0
    change WriterT.run (((cliDrvSMCoinLogged S ℓ run W qep decT encT
        (liftQueryImplStateT2 (n := CoinLogM) ext) ⟨i, sq⟩).run ds0).run kst0) =
      WriterT.run (liftM (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, sq⟩).run ds0).run kst0) : CoinLogM _)
    unfold cliDrvSMCoinLogged cliDrvSM
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [StateT.run_pure, liftM_prob_pure]
    · rcases hbi : ds0.bhInsts[i]? with _ | bi
      · simp [StateT.run_pure, liftM_prob_pure]
      · rcases him : ds0.instMeta[i]? with _ | im
        · simp [StateT.run_pure, liftM_prob_pure]
        · dsimp only; split_ifs
          · simp [StateT.run_set, StateT.run_pure, liftM_prob_pure]
          · rcases hgs : bi.gs with _ | gs <;> dsimp only
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
                pure_bind, liftM_prob_bind, liftM_prob_pure]
              rfl
            · rw [hLoc ds0 bi im gs]; rfl

/-! ## Coin-logged composed adapter -/

def cliAdapterStepImplWithCoinLogged {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhGameSpec S ℓ (BitVec 512))
      (StateT (CliAdapterState S) (StateT (BHE2EDrvState S ℓ) CoinLogM)) := fun q =>
  StateT.mk fun σ_ad =>
    simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
      ((bhShallowAdapterImpl S ℓ (BitVec 512) q).run σ_ad)

def cliComposedAdapterImplWithCoinLogged {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (cliGameSpec S ℓ (BitVec 512))
      (StateT (CliAdapterState S) (StateT (BHE2EDrvState S ℓ) CoinLogM)) := fun q =>
  match q with
  | .inl (.inl (.inl n)) =>
    cliAdapterStepImplWithCoinLogged P ki C K qep decT encT (.inl n)
  | .inl (.inl (.inr kq)) =>
    cliAdapterStepImplWithCoinLogged P ki C K qep decT encT (.inr (.inl (.inl kq)))
  | .inl (.inr cq) =>
    cliAdapterStepImplWithCoinLogged P ki C K qep decT encT (.inr (.inl (.inr cq)))
  | .inr dq =>
    cliAdapterStepImplWithCoinLogged P ki C K qep decT encT (.inr (.inr dq))

theorem simulateQ_cliE2EDrvImplWithCoinLogged_L_bh_run
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (σ_e2e : BHE2EDrvState S ℓ) :
    (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
      ((L_bh decT encT).eval (fun _ => cliGameAdversaryReassoc A) ())).run σ_e2e =
    (fun p => (p.1.1, p.2)) <$>
      (((simulateQ (cliComposedAdapterImplWithCoinLogged P ki C K qep decT encT) A.run).run
        (cliAdapterInitState S)).run σ_e2e) := by
  have hAdRun : ∀ {α : Type} (oa : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) α)
      (σ_ad : CliAdapterState S) (σ₀ : BHE2EDrvState S ℓ),
      (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
        ((simulateQ (bhShallowAdapterImpl S ℓ (BitVec 512)) oa).run σ_ad)).run σ₀ =
      (((simulateQ (cliAdapterStepImplWithCoinLogged P ki C K qep decT encT) oa).run σ_ad).run σ₀) := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure a => intro σ_ad σ₀; simp only [simulateQ_pure, StateT.run_pure]
    | query_bind q mx ih =>
      intro σ_ad σ₀
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map]
      dsimp only [cliAdapterStepImplWithCoinLogged]
      exact bind_congr fun ⟨⟨r, σ_ad'⟩, σ_e2e'⟩ => ih r σ_ad' σ_e2e'
  have hReassoc : simulateQ (cliAdapterStepImplWithCoinLogged P ki C K qep decT encT)
      (cliGameAdversaryReassoc A) =
      simulateQ (cliComposedAdapterImplWithCoinLogged P ki C K qep decT encT) A.run := by
    unfold cliGameAdversaryReassoc; generalize A.run = oa
    induction oa using OracleComp.inductionOn with
    | pure a => simp only [simulateQ_pure]
    | query_bind q mx ih =>
      rcases q with ((n | kq) | cq) | dq <;> {
        simp only [simulateQ_bind, simulateQ_query, OracleSpec.query_def,
          cliComposedAdapterImplWithCoinLogged, ih]
        rfl
      }
  have hEval :
      (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => cliGameAdversaryReassoc A) () =
      Prod.fst <$>
        ((simulateQ (bhShallowAdapterImpl S ℓ (BitVec 512)) (cliGameAdversaryReassoc A)).run
          (cliAdapterInitState S)) := by
    dsimp [BhShallowRed.eval, L_bh]
    simp only [pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  rw [hEval]
  simp only [map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure]
  rw [hAdRun, hReassoc]

theorem cliComposedAdapterImplWithCoinLogged_preserves_remoteIdInv
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (cliGameSpec S ℓ (BitVec 512)).Domain)
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ)
    (hInv : CliE2ERemoteIdInv σ_e2e) :
    ∀ yw ∈ support (WriterT.run
        (((cliComposedAdapterImplWithCoinLogged P ki C K qep decT encT q).run σ_ad).run σ_e2e)),
      CliE2ERemoteIdInv yw.1.2 := by
  have hStep : ∀ (gq : (unifSpec + bhGameSpec S ℓ (BitVec 512)).Domain),
      forgetCoinS2 (cliAdapterStepImplWithCoinLogged P ki C K qep decT encT gq) =
      cliAdapterStepImplWith P ki C K qep decT encT gq := by
    intro gq; ext s_ad s_e2e
    exact congrArg (fun m => m.run s_e2e) (forgetCoinS1_simulateQ
      (forgetCoinS1_cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
      ((bhShallowAdapterImpl S ℓ (BitVec 512) gq).run s_ad))
  have hComp : forgetCoinS2 (cliComposedAdapterImplWithCoinLogged P ki C K qep decT encT q) =
      cliComposedAdapterImplWith P ki C K qep decT encT q := by
    rcases q with ((n | kq) | cq) | dq <;> exact hStep _
  intro yw hyw
  have hmem : yw.1 ∈ support (forgetCoinW
      (((cliComposedAdapterImplWithCoinLogged P ki C K qep decT encT q).run σ_ad).run σ_e2e)) := by
    change yw.1 ∈ support (Prod.fst <$> WriterT.run
      (((cliComposedAdapterImplWithCoinLogged P ki C K qep decT encT q).run σ_ad).run σ_e2e))
    rw [support_map]
    exact ⟨yw, hyw, rfl⟩
  rw [← forgetCoinS1_run, ← forgetCoinS2_run, hComp] at hmem
  exact cliComposedAdapterImplWith_preserves_remoteIdInv P ki C K qep decT encT q σ_ad σ_e2e hInv
    yw.1 hmem

private def isSendOrChallTarget {S : SignalPqxdh.Setup} {ℓ : ℕ} :
    (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Bool
  | .inr (.inr ⟨_, sq⟩) => isSendOrChallSM sq
  | _ => false

private theorem cliE2EDrvImplWithCoinLogged_nonSend_eq_liftStateT
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (tq : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (htq : isSendOrChallTarget tq = false) :
    cliE2EDrvImplWithCoinLogged P ki C K qep decT encT tq =
      liftStateT (n := CoinLogM) (cliE2EDrvImplWith P ki C K qep decT encT tq) := by
  rcases tq with n | ((kq | ctlq) | ⟨i, sq⟩)
  · ext σ; rfl
  · ext σ
    change WriterT.run ((cliE2EDrvImplWithCoinLogged P ki C K qep decT encT (.inr (.inl (.inl kq)))).run σ) =
      WriterT.run (liftM ((cliE2EDrvImplWith P ki C K qep decT encT (.inr (.inl (.inl kq)))).run σ) : CoinLogM _)
    unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWith
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases kq <;> dsimp only <;> split_ifs <;>
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_lift, StateT.run_monadLift,
        monadLift_self, StateT.run_set, bind_assoc, pure_bind, liftM_prob_bind, liftM_prob_pure]
  · cases ctlq with
    | startDR sid =>
      ext σ
      change WriterT.run ((cliE2EDrvImplWithCoinLogged P ki C K qep decT encT
          (.inr (.inl (.inr (.startDR sid))))).run σ) =
        WriterT.run (liftM ((cliE2EDrvImplWith P ki C K qep decT encT
          (.inr (.inl (.inr (.startDR sid))))).run σ) : CoinLogM _)
      unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWith
      simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, liftM_prob_bind, liftM_prob_pure]
  · ext σ
    change WriterT.run ((cliE2EDrvImplWithCoinLogged P ki C K qep decT encT (.inr (.inr ⟨i, sq⟩))).run σ) =
      WriterT.run (liftM ((cliE2EDrvImplWith P ki C K qep decT encT (.inr (.inr ⟨i, sq⟩))).run σ) : CoinLogM _)
    unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWith
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure,
      bhE2EStepLocalSmCoinLogged_nonSend_eq_liftM C K qep decT encT σ i sq htq,
      bind_assoc, liftM_prob_bind, liftM_prob_pure]

private theorem simulateQ_cliE2EDrvImplWithCoinLogged_pure
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (a : α) :
    simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
      (pure a : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α) =
    liftStateT (n := CoinLogM)
      (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
        (pure a : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)) := by
  ext σ
  simp [simulateQ_pure, StateT.run_pure, liftStateT_run, liftM_prob_pure]

private theorem simulateQ_cliE2EDrvImplWithCoinLogged_query_bind
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (tq : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (htq : isSendOrChallTarget tq = false)
    (k : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range tq →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (hk : ∀ u, simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT) (k u) =
      liftStateT (n := CoinLogM) (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT) (k u))) :
    simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
      ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query tq) :
        OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _) >>= k) =
    liftStateT (n := CoinLogM)
      (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
        ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query tq) :
          OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _) >>= k)) := by
  ext σ
  change WriterT.run ((simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
      (liftM (OracleSpec.query tq) >>= k)).run σ) =
    WriterT.run (liftM ((simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
      (liftM (OracleSpec.query tq) >>= k)).run σ) : CoinLogM _)
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map,
    cliE2EDrvImplWithCoinLogged_nonSend_eq_liftStateT P ki C K qep decT encT tq htq,
    hk, liftStateT_run, liftM_prob_bind]

theorem cliComposedAdapterImplWithCoinLogged_nonSend_eq_liftCoinS2
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (cliGameSpec S ℓ (BitVec 512)).Domain)
    (hNonSend : isSendOrChallCli q = false) :
    cliComposedAdapterImplWithCoinLogged P ki C K qep decT encT q =
      liftCoinS2 (cliComposedAdapterImplWith P ki C K qep decT encT q) := by
  let hPureQ := fun {α : Type} (a : α) =>
    simulateQ_cliE2EDrvImplWithCoinLogged_pure (S := S) (ℓ := ℓ) P ki C K qep decT encT a
  let hBindQ := fun {α : Type} (tq : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
      (htq : isSendOrChallTarget tq = false)
      (k : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range tq →
        OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (hk : ∀ u, simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT) (k u) =
        liftStateT (n := CoinLogM) (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT) (k u))) =>
    simulateQ_cliE2EDrvImplWithCoinLogged_query_bind P ki C K qep decT encT tq htq k hk
  ext σ_ad σ_e2e
  have hQ0 : ∀ (gq : (unifSpec + bhGameSpec S ℓ (BitVec 512)).Domain),
      (match gq with
      | .inr (.inr ⟨_, sq⟩) => isSendOrChallSM sq
      | _ => false) = false →
      simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
        ((bhShallowAdapterImpl S ℓ (BitVec 512) gq).run σ_ad) =
      liftStateT (n := CoinLogM)
        (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
          ((bhShallowAdapterImpl S ℓ (BitVec 512) gq).run σ_ad)) := by
    intro gq hgq
    rcases gq with n | ((kq | ctlq) | ⟨i, sq⟩)
    · dsimp [bhShallowAdapterImpl, bhFwdU]
      exact hBindQ (Sum.inl n) rfl _ fun _ => hPureQ _
    · dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget]
      exact hBindQ (Sum.inr (Sum.inl (Sum.inl kq))) rfl _ fun _ => hPureQ _
    · cases ctlq with
      | startDR sid =>
        dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget]
        refine hBindQ (Sum.inr (Sum.inl (Sum.inr (.startDR sid)))) rfl _ fun idx? => ?_
        rcases idx? with _ | idx
        · exact hPureQ _
        · rcases hmg : (bhShallowStepMirrorGuard (.inr (σ_ad.2.2, sid))).2 with _ | inst <;>
            simp only [] <;> exact hPureQ _
    · rcases sq with (((q₁ | q₂) | ⟨p, c⟩) | ⟨p, c⟩) | p
      · simp [isSendOrChallSM] at hgq
      · simp [isSendOrChallSM] at hgq
      · cases p <;> dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget]
        · rcases hsw : bhShallowSplitWhisper c with _ | body <;> simp only []
          · rcases hsw2 : bhShallowSplitWhisper (bhShallowWrapWhisper c) with _ | _ <;>
              simp only []
            · exact hBindQ _ rfl _ fun _ => hPureQ _
            · exact hPureQ _
          · rcases hsw2 : bhShallowSplitWhisper (bhShallowWrapWhisper body) with _ | body' <;>
              simp only []
            · exact hPureQ _
            · exact hBindQ _ rfl _ fun _ => hPureQ _
        · rcases hinst : σ_ad.1 i with _ | inst <;> simp only []
          · exact hPureQ _
          · rcases hpk : bhShallowParsePreKey c with _ | hdr_inner <;> simp only []
            · rcases hsw : bhShallowSplitWhisper c with _ | body <;> simp only []
              · exact hBindQ _ rfl _ fun _ => hPureQ _
              · rcases hpk2 : bhShallowParsePreKey body with _ | _ <;> simp only []
                · rcases hsw2 : bhShallowSplitWhisper (bhShallowWrapWhisper body) with _ | _ <;>
                    simp only [] <;> exact hBindQ _ rfl _ fun _ => hPureQ _
                · exact hBindQ _ rfl _ fun _ => hPureQ _
            · rcases hsw : bhShallowSplitWhisper (bhShallowWrapWhisper hdr_inner.2) with _ | _ <;>
                simp only [] <;> exact hBindQ _ rfl _ fun _ => hPureQ _
      · cases p <;> dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget]
        · rcases hsw : bhShallowSplitWhisper c with _ | body <;> simp only []
          · exact hPureQ _
          · split_ifs
            · rcases hpk : bhShallowParsePreKey body with _ | _ <;> simp only []
              · rcases hsw2 : bhShallowSplitWhisper (bhShallowWrapWhisper body) with _ | _ <;>
                  simp only [] <;> exact hBindQ _ rfl _ fun _ => hPureQ _
              · exact hBindQ _ rfl _ fun _ => hPureQ _
            · exact hPureQ _
        · rcases hsw : bhShallowSplitWhisper c with _ | body <;> simp only []
          · rcases hpk : bhShallowParsePreKey c with _ | hdr_inner <;> simp only []
            · exact hBindQ _ rfl _ fun _ => hPureQ _
            · split_ifs
              · rcases hinst : σ_ad.1 i with _ | inst <;> simp only []
                · exact hBindQ _ rfl _ fun _ => hPureQ _
                · rcases hsw2 : bhShallowSplitWhisper (bhShallowWrapWhisper hdr_inner.2) with _ | _ <;>
                    simp only []
                  · split_ifs <;> exact hBindQ _ rfl _ fun _ => hPureQ _
                  · exact hBindQ _ rfl _ fun _ => hPureQ _
              · exact hBindQ _ rfl _ fun _ => hPureQ _
          · split_ifs
            · rcases hpk : bhShallowParsePreKey body with _ | _ <;> simp only []
              · rcases hsw2 : bhShallowSplitWhisper (bhShallowWrapWhisper body) with _ | _ <;>
                  simp only [] <;> exact hBindQ _ rfl _ fun _ => hPureQ _
              · exact hBindQ _ rfl _ fun _ => hPureQ _
            · exact hBindQ _ rfl _ fun _ => hPureQ _
      · dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget]
        rcases hinst : σ_ad.1 i with _ | inst <;> simp only []
        · exact hPureQ _
        · refine hBindQ _ rfl _ fun optG => ?_
          rcases optG with _ | g <;> exact hPureQ _
  rcases q with ((n | kq) | cq) | ⟨i, sq⟩
  · exact congrArg (fun m => m.run σ_e2e) (hQ0 (Sum.inl n) rfl)
  · exact congrArg (fun m => m.run σ_e2e) (hQ0 (Sum.inr (Sum.inl (Sum.inl kq))) rfl)
  · exact congrArg (fun m => m.run σ_e2e) (hQ0 (Sum.inr (Sum.inl (Sum.inr cq))) rfl)
  · exact congrArg (fun m => m.run σ_e2e) (hQ0 (Sum.inr (Sum.inr ⟨i, sq⟩)) hNonSend)

end Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBCoreAux
