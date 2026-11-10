/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.Game.ModelIface
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers
public import Computational.Proofs.E2E.TagSync1KeyReal
import Computational.Proofs.SpecLemmas.Session.ACD19.SM.Theorem8And12Statements
import VCVio.EvalDist.Monad.Basic

/-!
# Tracked and Halted `bhKindRedWith` Coupling

Defines the per-session tracked and coin-log-halted E2E driver states (`BHE2EDrvStateTracked`,
`BHE2EDrvStateHalted`), the shallow `KeyInd` reference reductions (`bhKindRedWithTracked`,
`bhKindRedWithHalted`), and their `KeyInd` coupling and advantage bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.MainHaltedKeyInd

open scoped ENNReal BigOperators
open OracleComp OracleSpec
open CryptoGames (Party SMSchemeR)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (ConfigR GameState corrR initState samIfNec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (BHDRCtlQuery BHModelInst BHE2EDrvState BHE2ESmResp BHTargetQuery
  BHTargetResp BhShallowRed Bytes DrvState DrvTagSyncInv1KeyReal KeyInd1KeyLazyState
  KeyIndAdvantageForHandshake ModelDriverInstanceMeta SMSchemeRM SampledSessionKey
  allTestedSessionsFresh bhDecodePreKeyMsgE bhDrvKiQueryOk bhE2EDrvInstClean bhE2EDrvWon
  bhE2EFinishStartSpk bhE2EGuard bhE2EInstIkACorr bhE2EMirror bhExpectedPreKeyMsg bhFwdU
  bhHdrOfPreKeyMsg bhInitRegId bhIsBobAcceptSMResp bhIsBobRecvSMQuery bhKeySOf bhLiftP
  bhNoOpkRespPromoted
  bhPackSmResp bhShallowImplOfHandle bhTargetGameSpec bhTargetQenc bhTargetRdec
  bhUnpackSmResp composedClean compositionLocalStart configRefuseEarlyBobCorr
  deliverRM injectRM keyIndReductionBudget liftStateT paramsIdsWithSpqr pqxdhKeyIndExpForHandshake
  pqxdhKeyIndTagImpl1KeyReal sessionSchemeFixedSpk shortCiphertext wirePrekey)

/-! ## Tracked and halted driver state and SM step lemmas -/

/-- Model-state E2E driver state augmented with one per-session tracker value of type `τ` per
promoted session instance. -/
abbrev BHE2EDrvStateTracked (τ : Type) (S : SignalPqxdh.Setup) (ℓ : ℕ) : Type :=
  BHE2EDrvState S ℓ × List τ

/-- Model-state E2E driver state augmented with one `BitVec 512` send-coin log per promoted
session instance. -/
abbrev BHE2EDrvStateHalted (S : SignalPqxdh.Setup) (ℓ : ℕ) : Type :=
  BHE2EDrvStateTracked (List (BitVec 512)) S ℓ

def bhE2ELocalStartTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    (σH : BHE2EDrvStateTracked τ S ℓ) (sid : SignalPqxdh.SessionId S) :
    ProbComp (Option ℕ × BHE2EDrvStateTracked τ S ℓ) := do
  let σ := σH.1
  match bhE2EGuard σ sid with
  | none => return (none, σH)
  | some (_, _, (u, j)) =>
    let (kr1, st1) ← (ki (.testSession sid)).run σ.st
    let (kr2, st2) ← (ki (.revealSpkSk u j)).run st1
    let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    let (idx?, σ') := bhE2EFinishStartSpk C K bMode? { σ with st := st2 } sid kr1 kr2 ac
    let tracks' := match idx?, kr1 with
      | some _, .drKeyResp dk => σH.2 ++ [initTrack (bhKeySOf dk ac)]
      | _, _ => σH.2
    return (idx?, (σ', tracks'))

def bhE2ELocalStartHalted {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    (σH : BHE2EDrvStateHalted S ℓ) (sid : SignalPqxdh.SessionId S) :
    ProbComp (Option ℕ × BHE2EDrvStateHalted S ℓ) := do
  let (idx?, σ') ← compositionLocalStart ki C K bMode? σH.1 sid
  let logs' := if idx?.isSome then σH.2 ++ [[]] else σH.2
  return (idx?, (σ', logs'))

def smSchemeCoinState {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) :
    SMSchemeRM (StateT (List Coins) ProbComp) Key St Msg Coins RCoins C where
  initA := sm.initA
  initB := sm.initB
  send st m r := fun log => pure (sm.send st m r, log ++ [r])
  receive st c rc := pure (sm.receive st c rc)

def transmitRHalted {Key St Msg Coins RCoins C : Type} [SampleableType Coins]
    (badLog : List Coins → Bool) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      let isBad ← StateT.lift (fun log => let log' := log ++ [coins]; pure (badLog log', log'))
      if isBad then return none
      else
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
        return some out.2

def challRHalted {Key St Msg Coins RCoins C : Type} [SampleableType Coins]
    (badLog : List Coins → Bool) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
      let isBad ← StateT.lift (fun log => let log' := log ++ [coins]; pure (badLog log', log'))
      if isBad then return none
      else
        let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
        return some out.2

/-- Online-halted R-game oracle handler over `StateT (List Coins) ProbComp`. -/
def oracleImplRHalted {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (badLog : List Coins → Bool) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (CryptoGames.SM.spec St Msg Coins C)
      (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) :=
  transmitRHalted badLog sm Δ qep cfg + challRHalted badLog sm Δ qep cfg +
    deliverRM (smSchemeCoinState sm) cfg + injectRM (smSchemeCoinState sm) Δ qep cfg +
    ((fun P => liftStateT (corrR cfg P)) :
      QueryImpl (Party →ₒ Option St)
        (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)))

/-- Per-session tracked counterpart of `bhE2EStepLocalSm` parameterized over an arbitrary
per-instance stateful SM oracle handler `smImpl`. -/
def bhE2EStepLocalSmTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (σH : BHE2EDrvStateTracked τ S ℓ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    ProbComp (BHE2ESmResp ℓ × BHE2EDrvStateTracked τ S ℓ) := do
  let σ := σH.1
  let logs := σH.2
  if !bhE2EDrvInstClean σ i then return ((none, none, none), σH)
  else
    match σ.insts[i]?, σ.instMeta[i]? with
    | some d, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d then
        let imCorr := { im with bobAccepted := true, ikACorrAtAccept := true }
        let σ' := { σ with instMeta := σ.instMeta.set i imCorr }
        return ((none, none, none), (σ', logs))
      else
        match d.gs with
        | none => return ((none, none, none), σH)
        | some gs =>
          let runTracked (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
              (σ0 : BHE2EDrvState S ℓ) : ProbComp (BHE2ESmResp ℓ × BHE2EDrvStateTracked τ S ℓ) := do
            let tr₀ := (logs[i]?).getD (initTrack default)
            let ((r, gs'), log') ← ((smImpl d q').run gs).run tr₀
            let accepted := bhIsBobAcceptSMResp q' r
            let im' := if !im.bobAccepted && accepted then
                { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ0 d }
              else im
            let σ1 := { σ0 with insts := σ0.insts.set i { d with gs := some gs' },
                                instMeta := σ0.instMeta.set i im' }
            return (bhPackSmResp q' r, (σ1, logs.set i log'))
          match q with
          | .inl (.inl (.inr (.A, c))) =>
            if (bhDecodePreKeyMsgE c).isSome then return ((none, none, none), σH)
            else runTracked q σ
          | .inl (.inr (.A, c)) =>
            if (bhDecodePreKeyMsgE c).isSome then return ((none, none, none), σH)
            else runTracked q σ
          | .inl (.inl (.inr (.B, c))) =>
            if !im.bobAccepted then
              match bhDecodePreKeyMsgE c with
              | some m =>
                if c == wirePrekey ::
                    (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes then
                  runTracked (.inl (.inl (.inr (.B, m.inner)))) σ
                else return ((none, none, none), σH)
              | none => return ((none, none, none), σH)
            else
              match bhDecodePreKeyMsgE c with
              | some m =>
                if bhHdrOfPreKeyMsg m == d.hdr then
                  runTracked (.inl (.inl (.inr (.B, m.inner)))) σ
                else return ((none, none, none), σH)
              | none => runTracked (.inl (.inl (.inr (.B, c)))) σ
          | .inl (.inr (.B, c)) =>
            if !im.bobAccepted then return ((none, none, none), σH)
            else
              match bhDecodePreKeyMsgE c with
              | some m =>
                if bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
                   decide (m.inner.length + 2048 < 2 ^ 32) then
                  runTracked (.inl (.inr (.B, m.inner))) σ
                else return ((none, none, none), σH)
              | none => runTracked (.inl (.inr (.B, c))) σ
          | _ => runTracked q σ
    | _, _ => return ((none, none, none), σH)

abbrev bhHaltedSmImpl {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (badLog : List (BitVec 512) → Bool)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (d : BHModelInst S ℓ) :
    QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
        (StateT (List (BitVec 512)) ProbComp)) :=
  oracleImplRHalted badLog
    (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ
      d.spkCoins)
    (2 + 1) qep
    (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT)

abbrev bhE2EStepLocalSmHalted {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (badLog : List (BitVec 512) → Bool)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvStateHalted S ℓ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    ProbComp (BHE2ESmResp ℓ × BHE2EDrvStateHalted S ℓ) :=
  bhE2EStepLocalSmTracked (fun _ => []) (bhHaltedSmImpl badLog C K qep decT encT) σH i q

/-- Per-session tracked counterpart of `bhE2EDrvImplWith`. -/
def bhE2EDrvImplWithTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvStateTracked τ S ℓ) ProbComp) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => do
    let σH ← get
    let σ := σH.1
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return .noneResp
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return .noneResp
    else
      let (kr, st') ← liftM ((ki kq).run σ.st)
      set (bhE2EMirror { σ with st := st' } kq kr, σH.2)
      return kr
  | .inr (.inl (.inr (.startDR sid))) => do
    let σH ← get
    let (idx?, σH') ← liftM (bhE2ELocalStartTracked initTrack ki C K (some σH.1.b) σH sid)
    set σH'
    return idx?
  | .inr (.inr ⟨i, sq⟩) => do
    let σH ← get
    let (sr, σH') ← liftM (bhE2EStepLocalSmTracked initTrack smImpl σH i sq)
    set σH'
    return bhUnpackSmResp sq sr

/-- Per-session online-halted counterpart of `bhE2EDrvImplWith`. -/
def bhE2EDrvImplWithHalted {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (badLog : List (BitVec 512) → Bool)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvStateHalted S ℓ) ProbComp) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => do
    let σH ← get
    let σ := σH.1
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return .noneResp
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return .noneResp
    else
      let (kr, st') ← liftM ((ki kq).run σ.st)
      set (bhE2EMirror { σ with st := st' } kq kr, σH.2)
      return kr
  | .inr (.inl (.inr (.startDR sid))) => do
    let σH ← get
    let (idx?, σH') ← liftM (bhE2ELocalStartHalted ki C K (some σH.1.b) σH sid)
    set σH'
    return idx?
  | .inr (.inr ⟨i, sq⟩) => do
    let σH ← get
    let (sr, σH') ← liftM (bhE2EStepLocalSmHalted badLog C K qep decT encT σH i sq)
    set σH'
    return bhUnpackSmResp sq sr

/-- Per-session tracked model E2E experiment parameterized by `(τ, initTrack, smImpl)`, `secb`,
and `ki`. -/
def bhE2EExpWithKiTracked {τ : Type} (initTrack : SampledSessionKey → τ)
    {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (secb : Bool) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', σH) ← (simulateQ (bhE2EDrvImplWithTracked initTrack smImpl P ki C K) B).run
    ({ b := b, st := SignalPqxdh.KeyIndState.empty S secb }, [])
  if !allTestedSessionsFresh P σH.1.st then $ᵗ Bool
  else return (b' == b || bhE2EDrvWon σH.1 b)

/-- Per-session online-halted model E2E experiment. -/
def bhE2EExpWithKiHalted (badLog : List (BitVec 512) → Bool) (secb : Bool)
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', σH) ← (simulateQ (bhE2EDrvImplWithHalted badLog P ki C K qep decT encT) B).run
    ({ b := b, st := SignalPqxdh.KeyIndState.empty S secb }, [])
  if !allTestedSessionsFresh P σH.1.st then $ᵗ Bool
  else return (b' == b || bhE2EDrvWon σH.1 b)

private def bhDecodeSmQuery {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    Option (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
  match q with
  | .inl (.inl (.inr (.A, c))) =>
    if (bhDecodePreKeyMsgE c).isSome then none else some q
  | .inl (.inr (.A, c)) =>
    if (bhDecodePreKeyMsgE c).isSome then none else some q
  | .inl (.inl (.inr (.B, c))) =>
    if !im.bobAccepted then
      match bhDecodePreKeyMsgE c with
      | some m =>
        if c == wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes then
          some (.inl (.inl (.inr (.B, m.inner))))
        else none
      | none => none
    else
      match bhDecodePreKeyMsgE c with
      | some m =>
        if bhHdrOfPreKeyMsg m == d.hdr then some (.inl (.inl (.inr (.B, m.inner)))) else none
      | none => some (.inl (.inl (.inr (.B, c))))
  | .inl (.inr (.B, c)) =>
    if !im.bobAccepted then none
    else
      match bhDecodePreKeyMsgE c with
      | some m =>
        if bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
           decide (m.inner.length + 2048 < 2 ^ 32) then
          some (.inl (.inr (.B, m.inner)))
        else none
      | none => some (.inl (.inr (.B, c)))
  | _ => some q

section StepSmLemmas
variable {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
variable (initTrack : SampledSessionKey → τ)
variable (smImpl : BHModelInst S ℓ →
  QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))

private theorem bhE2EStepLocalSmTracked_eq_decode (σH : BHE2EDrvStateTracked τ S ℓ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhE2EStepLocalSmTracked initTrack smImpl σH i q =
      let σ := σH.1; let logs := σH.2
      if !bhE2EDrvInstClean σ i then pure ((none, none, none), σH)
      else match σ.insts[i]?, σ.instMeta[i]? with
        | some d, some im =>
          if !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d then
            let imCorr := { im with bobAccepted := true, ikACorrAtAccept := true }
            pure ((none, none, none), ({ σ with instMeta := σ.instMeta.set i imCorr }, logs))
          else match d.gs, bhDecodeSmQuery d im q with
            | some gs, some q' => do
              let tr₀ := (logs[i]?).getD (initTrack default)
              let ((r, gs'), log') ← ((smImpl d q').run gs).run tr₀
              let accepted := bhIsBobAcceptSMResp q' r
              let im' := if !im.bobAccepted && accepted then
                  { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d } else im
              return (bhPackSmResp q' r,
                ({ σ with insts := σ.insts.set i { d with gs := some gs' },
                          instMeta := σ.instMeta.set i im' }, logs.set i log'))
            | _, _ => pure ((none, none, none), σH)
        | _, _ => pure ((none, none, none), σH) := by
  rcases σH with ⟨σ, logs⟩; unfold bhE2EStepLocalSmTracked; dsimp only
  by_cases hClean : (!bhE2EDrvInstClean σ i) = true
  · simp [hClean]
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte]
    cases σ.insts[i]? with
    | none => rfl
    | some d => cases σ.instMeta[i]? with
      | none => rfl
      | some im =>
        dsimp only
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d) = true
        · simp [hCorr]
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
          cases d.gs with
          | none => rfl
          | some gs =>
            rcases q with (((q1 | q2) | ⟨p, c⟩) | ⟨p, c⟩) | q5
            · rfl
            · rfl
            · cases p with
              | A => dsimp only [bhDecodeSmQuery]; split_ifs <;> rfl
              | B =>
                dsimp only [bhDecodeSmQuery]; split_ifs <;>
                  (cases bhDecodePreKeyMsgE c with | none => rfl | some m => dsimp only; split_ifs <;> rfl)
            · cases p with
              | A => dsimp only [bhDecodeSmQuery]; split_ifs <;> rfl
              | B =>
                dsimp only [bhDecodeSmQuery]; split_ifs
                · rfl
                · cases bhDecodePreKeyMsgE c with | none => rfl | some m => dsimp only; split_ifs <;> rfl
            · rfl

theorem bhE2EStepLocalSmTracked_with_st
    (σH : BHE2EDrvStateTracked τ S ℓ) (st' : SignalPqxdh.KeyIndState S) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhE2EStepLocalSmTracked initTrack smImpl ({ σH.1 with st := st' }, σH.2) i q =
      (fun p => (p.1, ({ p.2.1 with st := st' }, p.2.2))) <$>
        bhE2EStepLocalSmTracked initTrack smImpl σH i q := by
  rw [bhE2EStepLocalSmTracked_eq_decode, bhE2EStepLocalSmTracked_eq_decode]
  rcases σH with ⟨σ, logs⟩; dsimp only
  have hCleanEq : bhE2EDrvInstClean { σ with st := st' } i = bhE2EDrvInstClean σ i := rfl
  rw [hCleanEq]; split_ifs with hClean
  · simp only [map_pure]
  · cases σ.insts[i]? with
    | none => simp only [map_pure]
    | some d => cases σ.instMeta[i]? with
      | none => simp only [map_pure]
      | some im =>
        have hCorrEq : bhE2EInstIkACorr { σ with st := st' } d = bhE2EInstIkACorr σ d := rfl
        dsimp only; rw [hCorrEq]; split_ifs with hCorr
        · simp only [map_pure]
        · cases d.gs with
          | none => simp only [map_pure]
          | some gs => cases bhDecodeSmQuery d im q with
            | none => simp only [map_pure]
            | some q' => simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

theorem bhE2EStepLocalSmTracked_preserves_b (σH : BHE2EDrvStateTracked τ S ℓ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    (fun p => (p.1, ({ p.2.1 with b := σH.1.b }, p.2.2))) <$>
        bhE2EStepLocalSmTracked initTrack smImpl σH i q =
      bhE2EStepLocalSmTracked initTrack smImpl σH i q := by
  rw [bhE2EStepLocalSmTracked_eq_decode]; rcases σH with ⟨σ, logs⟩; dsimp only
  split_ifs with hClean
  · simp only [map_pure]
  · cases σ.insts[i]? with
    | none => simp only [map_pure]
    | some d => cases σ.instMeta[i]? with
      | none => simp only [map_pure]
      | some im =>
        dsimp only; split_ifs with hCorr
        · simp only [map_pure]
        · cases d.gs with
          | none => simp only [map_pure]
          | some gs => cases bhDecodeSmQuery d im q with
            | none => simp only [map_pure]
            | some q' => simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

end StepSmLemmas

theorem bhE2ELocalStartHalted_eq_tracked {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    (σH : BHE2EDrvStateHalted S ℓ) (sid : SignalPqxdh.SessionId S) :
    bhE2ELocalStartHalted ki C K bMode? σH sid =
      bhE2ELocalStartTracked (fun _ => []) ki C K bMode? σH sid := by
  rcases σH with ⟨σ, logs⟩
  unfold bhE2ELocalStartHalted compositionLocalStart bhE2ELocalStartTracked
  dsimp only
  cases hG : bhE2EGuard σ sid with
  | none =>
    simp only [pure_bind]
    rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun ⟨kr1, st1⟩ => bind_congr fun ⟨kr2, st2⟩ => bind_congr fun ac => ?_
    unfold bhE2EFinishStartSpk
    have hG2 : bhE2EGuard { σ with st := st2 } sid = some (hdr, bnd, (u, j)) := hG
    rw [hG2]
    cases kr1 with
    | drKeyResp dk =>
      cases kr2 with
      | spkSkResp spkSk =>
        dsimp only
        by_cases hLen :
          (dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
            dk.pqrKey.length == 32 && spkSk.length == 32) = true <;>
          simp [hLen]
      | _ => rfl
    | _ => rfl

theorem bhE2EDrvImplWithHalted_eq_tracked {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (badLog : List (BitVec 512) → Bool)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    bhE2EDrvImplWithHalted (ℓ := ℓ) badLog P ki C K qep decT encT =
      bhE2EDrvImplWithTracked (ℓ := ℓ) (fun _ => []) (bhHaltedSmImpl badLog C K qep decT encT)
        P ki C K := by
  funext q
  rcases q with n | ((kq | ⟨sid⟩) | ⟨i, sq⟩)
  · rfl
  · rfl
  · ext σH
    dsimp [bhE2EDrvImplWithHalted, bhE2EDrvImplWithTracked]
    simp only [bhE2ELocalStartHalted_eq_tracked]
  · rfl

theorem bhE2EExpWithKiHalted_eq_tracked (badLog : List (BitVec 512) → Bool) (secb : Bool)
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    bhE2EExpWithKiHalted badLog secb S P ki C K ℓ qep decT encT B =
      bhE2EExpWithKiTracked (fun _ => []) (bhHaltedSmImpl badLog C K qep decT encT)
        secb P ki C K B := by
  unfold bhE2EExpWithKiHalted bhE2EExpWithKiTracked
  rw [bhE2EDrvImplWithHalted_eq_tracked]

/-! ## Tracked and halted `bhKindRedWith` coupling and advantage bounds -/

def bhE2EFinishStartSpkTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    (σH : BHE2EDrvStateTracked τ S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    Option ℕ × BHE2EDrvStateTracked τ S ℓ :=
  let (idx?, σ') := bhE2EFinishStartSpk C K bMode? σH.1 sid kr1 kr2 ac
  let tracks' := match idx?, kr1 with
    | some _, .drKeyResp dk => σH.2 ++ [initTrack (bhKeySOf dk ac)]
    | _, _ => σH.2
  (idx?, (σ', tracks'))

def bhKindHandleWithTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives)
    (_ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem)
    (σH : BHE2EDrvStateTracked τ S ℓ) (q : BHTargetQuery S ℓ (BitVec 512)) :
    OracleComp (unifSpec + SignalPqxdh.keyIndSpec S)
      (BHTargetResp ℓ × BHE2EDrvStateTracked τ S ℓ) :=
  match q with
  | .inl (.inl kq) =>
    if bhDrvKiQueryOk P σH.1.toModelDriverBase kq &&
        !(match kq with | .corruptIK u => bhNoOpkRespPromoted σH.1.instMeta u | _ => false) then do
      let kr ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
      return (.inl (.inl kr), (bhE2EMirror σH.1 kq kr, σH.2))
    else
      pure (.inl (.inl .noneResp), σH)
  | .inl (.inr sid) =>
    match (bhE2EGuard σH.1 sid).map (fun (_, _, uj) => uj) with
    | none => pure (.inl (.inr none), σH)
    | some (u, j) => do
      let ts ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr (.testSession sid))) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
      let sk ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr (.revealSpkSk u j))) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
      let bv ← bhLiftP (G := SignalPqxdh.keyIndSpec S) ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let fin := bhE2EFinishStartSpkTracked initTrack C K (some σH.1.b) σH sid ts sk bv
      return (.inl (.inr fin.1), fin.2)
  | .inr (i, sq) => do
    let res ← bhLiftP (G := SignalPqxdh.keyIndSpec S)
      (bhE2EStepLocalSmTracked initTrack smImpl σH i sq)
    return (.inr res.1, res.2)

/-- Tracked shallow 1-stage `KeyInd` reference reduction. -/
def bhKindRedWithTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) :
    BhShallowRed (bhTargetGameSpec S ℓ (BitVec 512))
      (unifSpec + SignalPqxdh.keyIndSpec S)
      Unit Bool Unit Bool (BHE2EDrvStateTracked τ S ℓ) where
  init _ := do
    let drvH ← bhLiftP (G := SignalPqxdh.keyIndSpec S)
      (do let b ← ($ᵗ Bool : ProbComp Bool)
          return (({ b := b } : BHE2EDrvState S ℓ), ([] : List τ)))
    return ((), drvH)
  impl := bhShallowImplOfHandle bhTargetQenc bhTargetRdec
    (bhKindHandleWithTracked initTrack smImpl P ki C K)
  finish drvH aOut := pure (aOut == drvH.1.b || bhE2EDrvWon drvH.1 drvH.1.b)

/-- Per-session coin-log-halted shallow `KeyInd` reduction. -/
abbrev bhKindRedWithHalted {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (badLog : List (BitVec 512) → Bool)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    BhShallowRed (bhTargetGameSpec S ℓ (BitVec 512))
      (unifSpec + SignalPqxdh.keyIndSpec S)
      Unit Bool Unit Bool (BHE2EDrvStateHalted S ℓ) :=
  bhKindRedWithTracked (fun _ => []) (bhHaltedSmImpl badLog C K qep decT encT) P ki C K

abbrev keyIndFullImplWith (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)) :
    QueryImpl (unifSpec + SignalPqxdh.keyIndSpec S)
      (StateT (SignalPqxdh.KeyIndState S) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SignalPqxdh.KeyIndState S) ProbComp) + ki

private abbrev bhKindDummySt (S : SignalPqxdh.Setup) : SignalPqxdh.KeyIndState S :=
  SignalPqxdh.KeyIndState.empty S false

@[simp]
private theorem bhE2EGuard_with_st {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) (st' : SignalPqxdh.KeyIndState S) (sid : SignalPqxdh.SessionId S) :
    bhE2EGuard { σ with st := st' } sid = bhE2EGuard σ sid := rfl

@[simp]
private theorem bhE2EMirror_with_st {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) (st' : SignalPqxdh.KeyIndState S)
    (q : SignalPqxdh.KeyIndQuery S) (r : SignalPqxdh.KeyIndResponse) :
    bhE2EMirror { σ with st := st' } q r = { bhE2EMirror σ q r with st := st' } := rfl

section FinishPrivate
variable {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
variable (C : Crypto) (K : MlKem) (bMode? : Option Bool)

private theorem bhE2EFinishStartSpk_with_st (σ : BHE2EDrvState S ℓ) (st' : SignalPqxdh.KeyIndState S)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    bhE2EFinishStartSpk C K bMode? { σ with st := st' } sid kr1 kr2 ac =
      let p := bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac; (p.1, { p.2 with st := st' }) := by
  unfold bhE2EFinishStartSpk; simp only [bhE2EGuard_with_st]
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩; cases kr1 <;> cases kr2 <;> try rfl
    dsimp only; split_ifs <;> rfl

private theorem bhE2EFinishStartSpk_st_eq (σ : BHE2EDrvState S ℓ)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    (bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac).2.st = σ.st := by
  unfold bhE2EFinishStartSpk
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩; cases kr1 <;> cases kr2 <;> try rfl
    dsimp only; split_ifs <;> rfl

private theorem bhE2EFinishStartSpk_b_eq (σ : BHE2EDrvState S ℓ) (b0 : Bool) (hb : σ.b = b0)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    let p := bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac; (p.1, { p.2 with b := b0 }) = p := by
  subst hb; unfold bhE2EFinishStartSpk
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩; cases kr1 <;> cases kr2 <;> try rfl
    dsimp only; split_ifs <;> rfl

end FinishPrivate

private theorem simulateQ_keyIndFullImplWith_bhLiftP_run {S : SignalPqxdh.Setup} {α : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (mx : ProbComp α) (st : SignalPqxdh.KeyIndState S) :
    (simulateQ (keyIndFullImplWith S ki)
      (bhLiftP (G := SignalPqxdh.keyIndSpec S) mx)).run st =
    (mx >>= fun a => pure (a, st)) := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure x =>
    simp [bhLiftP, simulateQ_pure, StateT.run_pure]
  | query_bind t m ih =>
    simp only [bhLiftP, simulateQ_bind, StateT.run_bind]
    show ((query (spec := unifSpec) t >>= fun u => pure (u, st)) >>= fun y =>
        (simulateQ (keyIndFullImplWith S ki)
          (simulateQ (bhFwdU (G := SignalPqxdh.keyIndSpec S)) (m y.1))).run y.2) =
      ((query (spec := unifSpec) t >>= m) >>= fun a => pure (a, st))
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun u => ih u st

@[simp]
private theorem simulateQ_keyIndFullImplWith_query_inr {S : SignalPqxdh.Setup}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (kq : SignalPqxdh.KeyIndQuery S) :
    simulateQ (keyIndFullImplWith S ki)
      (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) =
    ki kq :=
  QueryImpl.simulateQ_add_query_right _ _ kq

@[simp]
private theorem stateT_run_liftM_with {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

private def bhKiNoOpkRefused {S : SignalPqxdh.Setup}
    (instMeta : List (ModelDriverInstanceMeta S))
    (kq : SignalPqxdh.KeyIndQuery S) : Bool :=
  match kq with
  | .corruptIK u => bhNoOpkRespPromoted instMeta u
  | _ => false

section CouplingPrivate
variable {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} (initTrack : SampledSessionKey → τ)
  (smImpl : BHModelInst S ℓ → QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
  (P : SignalPqxdh.Primitives)
  (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
  (C : Crypto) (K : MlKem)

@[simp] private theorem bhE2EDrvImplWithTracked_run_inl (n : ℕ) (σH : BHE2EDrvStateTracked τ S ℓ) :
    (bhE2EDrvImplWithTracked initTrack smImpl P ki C K (.inl n)).run σH =
      ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u => pure (u, σH)) := rfl

@[simp] private theorem bhE2EDrvImplWithTracked_run_ki
    (kq : SignalPqxdh.KeyIndQuery S) (σH : BHE2EDrvStateTracked τ S ℓ) :
    (bhE2EDrvImplWithTracked initTrack smImpl P ki C K (.inr (.inl (.inl kq)))).run σH =
      if !bhDrvKiQueryOk P σH.1.toModelDriverBase kq then pure (.noneResp, σH)
      else if bhKiNoOpkRefused σH.1.instMeta kq then pure (.noneResp, σH)
      else ((ki kq).run σH.1.st >>= fun p =>
        pure (p.1, (bhE2EMirror { σH.1 with st := p.2 } kq p.1, σH.2))) := by
  unfold bhE2EDrvImplWithTracked bhKiNoOpkRefused
  cases h : bhDrvKiQueryOk P σH.1.toModelDriverBase kq
  · simp only [h, Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
  · cases kq with
    | corruptIK u =>
      cases hRef : bhNoOpkRespPromoted σH.1.instMeta u <;>
        simp only [h, hRef, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          StateT.run_get, StateT.run_pure, stateT_run_liftM_with, StateT.run_set, bind_assoc, pure_bind]
    | _ =>
      simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, StateT.run_pure, stateT_run_liftM_with, StateT.run_set, bind_assoc, pure_bind]

@[simp] private theorem bhE2EDrvImplWithTracked_run_startDR
    (sid : SignalPqxdh.SessionId S) (σH : BHE2EDrvStateTracked τ S ℓ) :
    (bhE2EDrvImplWithTracked initTrack smImpl P ki C K (.inr (.inl (.inr (.startDR sid))))).run σH =
      bhE2ELocalStartTracked initTrack ki C K (some σH.1.b) σH sid := by
  unfold bhE2EDrvImplWithTracked
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, stateT_run_liftM_with, StateT.run_set,
    bind_assoc, pure_bind, Prod.mk.eta, bind_pure]

@[simp] private theorem bhE2EDrvImplWithTracked_run_sm (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σH : BHE2EDrvStateTracked τ S ℓ) :
    (bhE2EDrvImplWithTracked initTrack smImpl P ki C K (.inr (.inr ⟨i, sq⟩))).run σH =
      (bhE2EStepLocalSmTracked initTrack smImpl σH i sq >>= fun p => pure (bhUnpackSmResp sq p.1, p.2)) := by
  unfold bhE2EDrvImplWithTracked
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, stateT_run_liftM_with, StateT.run_set,
    bind_assoc, pure_bind]

private theorem bhKindHandleWithTracked_impl_run_ki
    (kq : SignalPqxdh.KeyIndQuery S) (σH : BHE2EDrvStateTracked τ S ℓ) :
    ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
      (bhKindHandleWithTracked initTrack smImpl P ki C K) (.inr (.inl (.inl kq)))).run σH) =
      (if !bhDrvKiQueryOk P σH.1.toModelDriverBase kq then pure (.noneResp, σH)
      else if bhKiNoOpkRefused σH.1.instMeta kq then pure (.noneResp, σH)
      else (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) >>= fun kr =>
        pure (kr, (bhE2EMirror σH.1 kq kr, σH.2))) := by
  dsimp [bhShallowImplOfHandle, bhKindHandleWithTracked, bhTargetQenc, bhTargetRdec, bhKiNoOpkRefused]
  cases bhDrvKiQueryOk P σH.1.toModelDriverBase kq
  · simp only [Bool.false_and, Bool.false_eq_true, Bool.not_false, ↓reduceIte, pure_bind]
  · cases kq with
    | corruptIK u =>
      dsimp only
      by_cases hRef : bhNoOpkRespPromoted σH.1.instMeta u = true
      · simp only [hRef, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte, pure_bind]
      · simp only [Bool.eq_false_iff.mpr hRef, Bool.not_true, Bool.not_false, Bool.true_and,
          Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
    | _ => simp only [Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
        bind_assoc, pure_bind]

private theorem bhKindHandleWithTracked_impl_run_startDR
    (sid : SignalPqxdh.SessionId S) (σH : BHE2EDrvStateTracked τ S ℓ) :
    ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
      (bhKindHandleWithTracked initTrack smImpl P ki C K) (.inr (.inl (.inr (.startDR sid))))).run σH) =
      match (bhE2EGuard σH.1 sid).map (fun x => x.2.2) with
      | none => pure (none, σH)
      | some (u, j) =>
        (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr (.testSession sid))) :
          OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) >>= fun kr1 =>
        (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr (.revealSpkSk u j))) :
          OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) >>= fun kr2 =>
        bhLiftP (G := SignalPqxdh.keyIndSpec S) ($ᵗ BitVec 256) >>= fun ac =>
        pure (bhE2EFinishStartSpkTracked initTrack C K (some σH.1.b) σH sid kr1 kr2 ac) := by
  dsimp [bhShallowImplOfHandle, bhKindHandleWithTracked, bhTargetQenc, bhTargetRdec]
  cases (bhE2EGuard σH.1 sid).map (fun x => x.2.2) with
  | none => simp only [pure_bind]
  | some uj => rcases uj with ⟨u, j⟩; simp only [bind_assoc, pure_bind, Prod.mk.eta]

private theorem bhKindHandleWithTracked_impl_run_sm (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σH : BHE2EDrvStateTracked τ S ℓ) :
    ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
      (bhKindHandleWithTracked initTrack smImpl P ki C K) (.inr (.inr ⟨i, sq⟩))).run σH) =
      (bhLiftP (G := SignalPqxdh.keyIndSpec S)
        (bhE2EStepLocalSmTracked initTrack smImpl σH i sq) >>=
        fun p => pure (bhUnpackSmResp sq p.1, p.2)) := by
  dsimp [bhShallowImplOfHandle, bhKindHandleWithTracked, bhTargetQenc, bhTargetRdec]
  simp only [bind_assoc, pure_bind]

private theorem simulateQ_bhKindRedWithTracked_impl_step
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σH : BHE2EDrvStateTracked τ S ℓ) :
    (simulateQ (keyIndFullImplWith S ki)
      ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
        (bhKindHandleWithTracked initTrack smImpl P ki C K) q).run
        ({ σH.1 with st := bhKindDummySt S }, σH.2))).run σH.1.st =
    (fun p => ((p.1, ({ p.2.1 with st := bhKindDummySt S }, p.2.2)), p.2.1.st)) <$>
      ((bhE2EDrvImplWithTracked initTrack smImpl P ki C K q).run σH) ∧
    (fun p => (p.1, ({ p.2.1 with b := σH.1.b }, p.2.2))) <$>
      ((bhE2EDrvImplWithTracked initTrack smImpl P ki C K q).run σH) =
      ((bhE2EDrvImplWithTracked initTrack smImpl P ki C K q).run σH) := by
  rcases σH with ⟨σ, logs⟩
  match q with
  | .inl n =>
    refine ⟨?_, ?_⟩
    · change (simulateQ (keyIndFullImplWith S ki)
          (bhFwdU (G := SignalPqxdh.keyIndSpec S) n >>= fun u =>
            pure (u, ({ σ with st := bhKindDummySt S }, logs)))).run σ.st = _
      rw [bhE2EDrvImplWithTracked_run_inl]
      simp only [bhFwdU, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        map_eq_bind_pure_comp, Function.comp_def]
      rfl
    · rw [bhE2EDrvImplWithTracked_run_inl]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  | .inr (.inl (.inl kq)) =>
    refine ⟨?_, ?_⟩
    · rw [bhKindHandleWithTracked_impl_run_ki, bhE2EDrvImplWithTracked_run_ki]
      dsimp only
      cases hOk : bhDrvKiQueryOk P σ.toModelDriverBase kq
      · simp only [Bool.not_false, ↓reduceIte, simulateQ_pure, StateT.run_pure,
          map_eq_bind_pure_comp, Function.comp_def, pure_bind]
      · cases hRef : bhKiNoOpkRefused σ.instMeta kq
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
            simulateQ_keyIndFullImplWith_query_inr, simulateQ_pure, StateT.run_pure,
            map_eq_bind_pure_comp, Function.comp_def, bhE2EMirror_with_st]
          rfl
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_pure,
            map_eq_bind_pure_comp, Function.comp_def, pure_bind]
    · rw [bhE2EDrvImplWithTracked_run_ki]
      dsimp only
      cases hOk : bhDrvKiQueryOk P σ.toModelDriverBase kq
      · simp only [Bool.not_false, ↓reduceIte, map_eq_bind_pure_comp, Function.comp_def, pure_bind]
      · cases hRef : bhKiNoOpkRefused σ.instMeta kq
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
          rfl
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            map_eq_bind_pure_comp, Function.comp_def, pure_bind]
  | .inr (.inl (.inr (.startDR sid))) =>
    refine ⟨?_, ?_⟩
    · rw [bhKindHandleWithTracked_impl_run_startDR, bhE2EDrvImplWithTracked_run_startDR]
      unfold bhE2ELocalStartTracked
      dsimp only
      simp only [bhE2EGuard_with_st]
      cases hG : bhE2EGuard σ sid with
      | none =>
        simp only [Option.map_none, simulateQ_pure, StateT.run_pure,
          map_eq_bind_pure_comp, Function.comp_def, pure_bind]
      | some val =>
        rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
        simp only [Option.map_some, bind_assoc, pure_bind,
          simulateQ_bind, StateT.run_bind, simulateQ_keyIndFullImplWith_query_inr,
          simulateQ_keyIndFullImplWith_bhLiftP_run, simulateQ_pure, StateT.run_pure,
          map_eq_bind_pure_comp, Function.comp_def]
        refine bind_congr fun p1 => bind_congr fun p2 => bind_congr fun ac => congrArg pure ?_
        unfold bhE2EFinishStartSpkTracked
        dsimp only
        have hFin := bhE2EFinishStartSpk_with_st C K (some σ.b)
          { σ with st := p2.2 } (bhKindDummySt S) sid p1.1 p2.1 ac
        have hSt2 := bhE2EFinishStartSpk_st_eq C K (some σ.b)
          { σ with st := p2.2 } sid p1.1 p2.1 ac
        dsimp only at hFin hSt2
        rw [hFin, hSt2]
        cases (bhE2EFinishStartSpk C K (some σ.b) { σ with st := p2.2 } sid p1.1 p2.1 ac).1 <;>
          cases p1.1 <;> rfl
    · rw [bhE2EDrvImplWithTracked_run_startDR]
      unfold bhE2ELocalStartTracked
      dsimp only
      cases hG : bhE2EGuard σ sid with
      | none =>
        simp only [map_eq_bind_pure_comp, Function.comp_def, pure_bind]
      | some val =>
        rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine bind_congr fun p1 => bind_congr fun p2 => bind_congr fun ac => congrArg pure ?_
        have hB := congrArg Prod.snd (bhE2EFinishStartSpk_b_eq C K (some σ.b)
          { σ with st := p2.2 } σ.b rfl sid p1.1 p2.1 ac)
        dsimp only at hB
        exact Prod.ext rfl (Prod.ext hB rfl)
  | .inr (.inr ⟨i, sq⟩) =>
    refine ⟨?_, ?_⟩
    · rw [bhKindHandleWithTracked_impl_run_sm, bhE2EDrvImplWithTracked_run_sm]
      simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
        simulateQ_keyIndFullImplWith_bhLiftP_run, simulateQ_pure, StateT.run_pure]
      have hDummy := bhE2EStepLocalSmTracked_with_st initTrack smImpl (σ, logs) (bhKindDummySt S) i sq
      have hSelf := (bhE2EStepLocalSmTracked_with_st initTrack smImpl (σ, logs) σ.st i sq).symm
      dsimp only at hDummy hSelf ⊢
      rw [hDummy, ← hSelf]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    · rw [bhE2EDrvImplWithTracked_run_sm]
      have hB := bhE2EStepLocalSmTracked_preserves_b initTrack smImpl (σ, logs) i sq
      conv_rhs => rw [← hB]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

private theorem simulateQ_bhKindRedWithTracked_impl_run {α : Type}
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σH : BHE2EDrvStateTracked τ S ℓ) :
    (simulateQ (keyIndFullImplWith S ki)
      ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
        (bhKindHandleWithTracked initTrack smImpl P ki C K)) oa).run
        ({ σH.1 with st := bhKindDummySt S }, σH.2))).run σH.1.st =
    (fun p => ((p.1, ({ p.2.1 with st := bhKindDummySt S }, p.2.2)), p.2.1.st)) <$>
      ((simulateQ (bhE2EDrvImplWithTracked initTrack smImpl P ki C K) oa).run σH) ∧
    (fun p => (p.1, ({ p.2.1 with b := σH.1.b }, p.2.2))) <$>
      ((simulateQ (bhE2EDrvImplWithTracked initTrack smImpl P ki C K) oa).run σH) =
      ((simulateQ (bhE2EDrvImplWithTracked initTrack smImpl P ki C K) oa).run σH) := by
  induction oa using OracleComp.inductionOn generalizing σH with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, pure_bind]
    exact ⟨trivial, trivial⟩
  | query_bind q mx ih =>
    have ⟨hStep, hStepB⟩ := simulateQ_bhKindRedWithTracked_impl_step initTrack smImpl P ki C K q σH
    rw [run_simulateQ_query_bind, simulateQ_bind, StateT.run_bind, run_simulateQ_query_bind]
    refine ⟨?_, ?_⟩
    · rw [hStep]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨r, σH'⟩ => ?_
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using (ih r σH').1
    · conv_lhs => rw [← hStepB]
      conv_rhs => rw [← hStepB]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨r, σH'⟩ => ?_
      have hih := (ih r ({ σH'.1 with b := σH.1.b }, σH'.2)).2
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using hih

end CouplingPrivate

private theorem evalDist_uniformBool_beq_with (b : Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun z => pure (b == z)] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by
  cases b
  · simpa using ProbComp.evalDist_bind_not_uniformBool (fun z => (pure z : ProbComp Bool))
  · simp

@[simp]
private theorem bhE2EDrvWon_with_b_aux {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) (b' b : Bool) :
    bhE2EDrvWon { σ with b := b' } b = bhE2EDrvWon σ b := rfl

theorem evalDist_bhKindRedWithTracked_branch {τ : Type} (initTrack : SampledSessionKey → τ)
    {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (secb : Bool) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[do
      let (w, finalSt) ← (simulateQ (keyIndFullImplWith S ki)
        ((bhKindRedWithTracked initTrack smImpl P ki C K).eval (fun _ => B) ())).run
        (SignalPqxdh.KeyIndState.empty S secb)
      if !allTestedSessionsFresh P finalSt then
        let coin ← $ᵗ Bool
        return coin
      else
        return (w == secb)] =
    𝒟[do
      let z ← bhE2EExpWithKiTracked initTrack smImpl secb P ki C K B
      return (secb == z)] := by
  unfold bhE2EExpWithKiTracked
  dsimp only [BhShallowRed.eval, bhKindRedWithTracked]
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_keyIndFullImplWith_bhLiftP_run, simulateQ_pure, StateT.run_pure]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  let σH0 : BHE2EDrvStateTracked τ S ℓ := ({ b := b, st := SignalPqxdh.KeyIndState.empty S secb }, [])
  have hInit : (({ b := b } : BHE2EDrvState S ℓ), ([] : List τ)) =
      ({ σH0.1 with st := bhKindDummySt S }, σH0.2) := rfl
  have ⟨hRun, hRunB⟩ := simulateQ_bhKindRedWithTracked_impl_run initTrack smImpl P ki C K B σH0
  rw [hInit]
  change 𝒟[(simulateQ (keyIndFullImplWith S ki)
        ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
          (bhKindHandleWithTracked initTrack smImpl P ki C K)) B).run
          ({ σH0.1 with st := bhKindDummySt S }, σH0.2))).run σH0.1.st >>=
      fun x =>
        if !allTestedSessionsFresh P x.2 then $ᵗ Bool >>= fun coin => pure coin
        else pure ((x.1.1 == x.1.2.1.b || bhE2EDrvWon x.1.2.1 x.1.2.1.b) == secb)] =
    𝒟[(simulateQ (bhE2EDrvImplWithTracked initTrack smImpl P ki C K) B).run σH0 >>=
      fun x =>
        (if !allTestedSessionsFresh P x.2.1.st then $ᵗ Bool else pure (x.1 == b || bhE2EDrvWon x.2.1 b)) >>=
          fun z => pure (secb == z)]
  rw [hRun, ← hRunB]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
    bhE2EDrvWon_with_b_aux]
  refine evalDist_bind_congr ((simulateQ (bhE2EDrvImplWithTracked initTrack smImpl P ki C K) B).run σH0) _ _
    fun ⟨b', σH'⟩ => ?_
  have hSt : ({ σH'.1 with b := σH0.1.b } : BHE2EDrvState S ℓ).st = σH'.1.st := rfl
  have hB : ({ σH'.1 with b := σH0.1.b, st := bhKindDummySt S } : BHE2EDrvState S ℓ).b = b := rfl
  have hWon : bhE2EDrvWon ({ σH'.1 with b := σH0.1.b, st := bhKindDummySt S } : BHE2EDrvState S ℓ) b =
      bhE2EDrvWon σH'.1 b := rfl
  dsimp only
  rw [hSt, hB, hWon]
  by_cases hClean : allTestedSessionsFresh P σH'.1.st = true
  · simp [hClean, Bool.beq_comm]
  · have hNotClean : (!allTestedSessionsFresh P σH'.1.st) = true := by
      cases hc : allTestedSessionsFresh P σH'.1.st <;> simp_all
    simp only [hNotClean, ↓reduceIte, bind_pure]
    exact (evalDist_uniformBool_beq_with secb).symm

section AdvantageBounds
variable {τ : Type} (initTrack : SampledSessionKey → τ)
variable {S : SignalPqxdh.Setup} {ℓ : ℕ}
variable (smImpl : BHModelInst S ℓ →
  QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))

theorem evalDist_pqxdhKeyIndExpWith_bhKindRedWithTracked
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[pqxdhKeyIndExpForHandshake S P ki
        ⟨(bhKindRedWithTracked initTrack smImpl P ki C K).eval (fun _ => B) ()⟩] =
    𝒟[do
      let secb ← $ᵗ Bool
      let z ← if secb then bhE2EExpWithKiTracked initTrack smImpl true P ki C K B
               else bhE2EExpWithKiTracked initTrack smImpl false P ki C K B
      return (secb == z)] := by
  unfold pqxdhKeyIndExpForHandshake
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun secb => ?_
  cases secb
  · exact evalDist_bhKindRedWithTracked_branch initTrack smImpl false P ki C K B
  · exact evalDist_bhKindRedWithTracked_branch initTrack smImpl true P ki C K B

theorem keyIndAdvantageWith_bhKindRedWithTracked
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    KeyIndAdvantageForHandshake S P ki
        ⟨(bhKindRedWithTracked initTrack smImpl P ki C K).eval (fun _ => B) ()⟩ =
      𝒟[bhE2EExpWithKiTracked initTrack smImpl true P ki C K B].boolDist
        𝒟[bhE2EExpWithKiTracked initTrack smImpl false P ki C K B] := by
  show 𝒟[pqxdhKeyIndExpForHandshake S P ki
      ⟨(bhKindRedWithTracked initTrack smImpl P ki C K).eval (fun _ => B) ()⟩].boolBias = _
  rw [evalDist_pqxdhKeyIndExpWith_bhKindRedWithTracked, evalDist_boolBias_bind_uniformBool]

/-- For any tracker `(τ, initTrack, smImpl)` and `KeyInd` handler `ki`, the `boolBias` of
`bhE2EExpWithKiTracked` at `secb = true` is at most twice `KeyIndAdvantageForHandshake` on
`bhKindRedWithTracked` plus its `boolBias` at `secb = false`. -/
theorem boolBias_bhE2EExpWithKiTracked_true_le
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhE2EExpWithKiTracked initTrack smImpl true P ki C K B].boolBias ≤
      2 * KeyIndAdvantageForHandshake S P ki
            ⟨(bhKindRedWithTracked initTrack smImpl P ki C K).eval (fun _ => B) ()⟩ +
        𝒟[bhE2EExpWithKiTracked initTrack smImpl false P ki C K B].boolBias := by
  rw [keyIndAdvantageWith_bhKindRedWithTracked, add_comm]
  exact CryptoGames.SM.Construction.boolBias_le_add_two_mul_boolDist
    𝒟[bhE2EExpWithKiTracked initTrack smImpl true P ki C K B]
    𝒟[bhE2EExpWithKiTracked initTrack smImpl false P ki C K B]

/-- Specialization of `boolBias_bhE2EExpWithKiTracked_true_le` to `SignalPqxdh.pqxdhKeyIndImpl1KeyReal`. -/
theorem boolBias_bhE2EExpWithKiTracked_1KeyReal_true_le
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhE2EExpWithKiTracked initTrack smImpl true P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
        C K B].boolBias ≤
      2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P
            ⟨(bhKindRedWithTracked initTrack smImpl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
              C K).eval (fun _ => B) ()⟩ +
        𝒟[bhE2EExpWithKiTracked initTrack smImpl false P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
            C K B].boolBias :=
  boolBias_bhE2EExpWithKiTracked_true_le initTrack smImpl P
    (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K B

end AdvantageBounds

/-- Halted `bhKindRedWithHalted` advantage bound for any `KeyInd` handler `ki`. -/
theorem boolBias_bhE2EExpWithKiHalted_true_le (badLog : List (BitVec 512) → Bool)
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhE2EExpWithKiHalted badLog true S P ki C K ℓ qep decT encT B].boolBias ≤
      2 * KeyIndAdvantageForHandshake S P ki
            ⟨(bhKindRedWithHalted (S := S) (ℓ := ℓ) badLog P ki C K qep decT encT).eval
              (fun _ => B) ()⟩ +
        𝒟[bhE2EExpWithKiHalted badLog false S P ki C K ℓ qep decT encT B].boolBias := by
  rw [bhE2EExpWithKiHalted_eq_tracked, bhE2EExpWithKiHalted_eq_tracked]
  exact boolBias_bhE2EExpWithKiTracked_true_le (fun _ => [])
    (bhHaltedSmImpl badLog C K qep decT encT) P ki C K B

/-- Specialization of `boolBias_bhE2EExpWithKiHalted_true_le` to `SignalPqxdh.pqxdhKeyIndImpl1KeyReal`. -/
theorem boolBias_bhE2EExpWithKiHalted_1KeyReal_true_le (badLog : List (BitVec 512) → Bool)
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhE2EExpWithKiHalted badLog true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
        C K ℓ qep decT encT B].boolBias ≤
      2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P
            ⟨(bhKindRedWithHalted (S := S) (ℓ := ℓ) badLog P
              (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT).eval (fun _ => B) ()⟩ +
        𝒟[bhE2EExpWithKiHalted badLog false S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
            C K ℓ qep decT encT B].boolBias := by
  rw [bhE2EExpWithKiHalted_eq_tracked, bhE2EExpWithKiHalted_eq_tracked]
  exact boolBias_bhE2EExpWithKiTracked_1KeyReal_true_le (fun _ => [])
    (bhHaltedSmImpl badLog C K qep decT encT) P C K B

end Computational.Proofs.LibsignalCli.MainHaltedKeyInd
