/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Game.ModelIface
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.EvalDist.Measure

/-!
# Parametric Per-Session Halt Tracker and Online Coin-Log Coupling

Defines `SessionHaltTracker`, `ValidSessionHaltTracker`, `AgreeInv`, and the coupled
coin-logged and session-tracked R-game and E2E oracles for `MainHaltedOnline`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.MainHaltedCoupling

open scoped ENNReal BigOperators
open OracleComp OracleSpec
open CryptoGames (Party SMSchemeR)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (Adversary ConfigR GameState RecvResult corrR deliverR initState injectR
  samIfNec)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes spqrV1SessionUniformCoins)
open CryptoVerification.E2E (BHModelInst BHE2EDrvState BHE2ESmResp Bytes ModelDriverInstanceMeta
  SMSchemeRM SampledSessionKey allTestedSessionsFresh bhDecodePreKeyMsgE bhDrvKiQueryOk
  bhE2EDrvInstClean bhE2EDrvWon bhE2EFinishStartSpk bhE2EGuard bhE2EInstIkACorr bhE2EMirror
  bhExpectedPreKeyMsg bhHdrOfPreKeyMsg bhInitRegId bhIsBobAcceptSMResp bhIsBobRecvSMQuery
  bhKeySOf bhNoOpkRespPromoted bhPackSmResp bhTargetGameSpec bhUnpackSmResp challRM
  compositionLocalStart configRefuseEarlyBobCorr deliverRM injectRM liftStateT oracleImplRM
  paramsIdsWithSpqr sessionSchemeFixedSpk shortCiphertext smSchemeCoinLogged transmitRM wirePrekey)

/-! ## Monotone bad-log predicates and `SessionHaltTracker` -/

/-- Monotone-sticky (`false`-prefix-closed) boolean log predicate. -/
structure ValidBadLog {α : Type} (badLog : List α → Bool) : Prop where
  nil_false : badLog [] = false
  append_left_false : ∀ (w w' : List α), badLog (w ++ w') = false → badLog w = false

theorem ValidBadLog.snoc_false {α : Type} {badLog : List α → Bool} (h : ValidBadLog badLog)
    (w : List α) (x : α) (hx : badLog (w ++ [x]) = false) : badLog w = false :=
  h.append_left_false w [x] hx

abbrev kemFailBadLog (K : MlKem) (w : List (BitVec 512)) : Bool :=
  K.KemFailBad (w.map coinBytes)

theorem kemFailBad_eq_false_of_subset (K : MlKem) {t₁ t₂ : List Bytes}
    (hsub : ∀ x ∈ t₁, x ∈ t₂) (h₂ : K.KemFailBad t₂ = false) :
    K.KemFailBad t₁ = false := by
  simp only [MlKem.KemFailBad, List.any_eq_false, Bool.not_eq_true] at h₂ ⊢
  exact fun a ha b hb => h₂ a (hsub a ha) b (hsub b hb)

theorem kemFailBadLog_eq_false_of_subset (K : MlKem) {w₁ w₂ : List (BitVec 512)}
    (hsub : ∀ c ∈ w₁, c ∈ w₂) (h₂ : kemFailBadLog K w₂ = false) :
    kemFailBadLog K w₁ = false :=
  kemFailBad_eq_false_of_subset K (fun _ hx => by
    rcases List.mem_map.mp hx with ⟨c, hc, rfl⟩
    exact List.mem_map.mpr ⟨c, hsub c hc, rfl⟩) h₂

theorem validBadLog_kemFailBadLog (K : MlKem) : ValidBadLog (kemFailBadLog K) where
  nil_false := by simp [kemFailBadLog, MlKem.KemFailBad]
  append_left_false w w' h :=
    kemFailBadLog_eq_false_of_subset K (fun c hc => List.mem_append_left w' hc) h

/-- Per-session deterministic R-game halt tracker over state `τ`. -/
structure SessionHaltTracker (St Msg Coins C Key τ : Type) where
  init : Key → τ
  checkSend : GameState St Msg C → Party → Coins → τ → Bool × τ
  commitSend : GameState St Msg C → Party → Coins → C → τ → τ
  onDeliver : GameState St Msg C → Party → C → Option (RecvResult Msg) → τ → τ

/-- Soundness invariant connecting `T : SessionHaltTracker` to global `badGlobal`. -/
structure ValidSessionHaltTracker {St Msg Coins C Key τ : Type}
    (badGlobal : List Coins → Bool) (T : SessionHaltTracker St Msg Coins C Key τ)
    (TrInv : τ → List Coins → Prop) : Prop where
  inv_init : ∀ (k : Key) (gLog : List Coins), TrInv (T.init k) gLog
  inv_mono : ∀ {tr : τ} {gLog : List Coins} (c : Coins), TrInv tr gLog → TrInv tr (gLog ++ [c])
  inv_deliver : ∀ s₀ P c res {tr : τ} {gLog : List Coins},
    TrInv tr gLog → TrInv (T.onDeliver s₀ P c res tr) gLog
  send_good : ∀ s₁ P coins {tr : τ} {gLog : List Coins}, TrInv tr gLog →
    (badGlobal (gLog ++ [coins]) = false → (T.checkSend s₁ P coins tr).1 = false) ∧
    TrInv (T.checkSend s₁ P coins tr).2 (gLog ++ [coins]) ∧
    ∀ ct : C, TrInv (T.commitSend s₁ P coins ct tr) (gLog ++ [coins])

def coinLogSessionTracker {St Msg Coins C Key : Type} (badLog : List Coins → Bool) :
    SessionHaltTracker St Msg Coins C Key (List Coins) where
  init _ := []
  checkSend _ _ coins log := let log' := log ++ [coins]; (badLog log', log')
  commitSend _ _ coins _ log := log ++ [coins]
  onDeliver _ _ _ _ log := log

theorem validSessionHaltTracker_kemFailBadLog {St Msg C Key : Type} (K : MlKem) :
    ValidSessionHaltTracker (kemFailBadLog K)
      (coinLogSessionTracker (St := St) (Msg := Msg) (C := C) (Key := Key) (kemFailBadLog K))
      (fun log gLog => ∀ x ∈ log, x ∈ gLog) where
  inv_init _ _ _ hx := nomatch hx
  inv_mono {_} {_} c hinv x hx := List.mem_append_left [c] (hinv x hx)
  inv_deliver _ _ _ _ {_} {_} hinv := hinv
  send_good _ _ coins {tr} {gLog} hinv := by
    have hsub : ∀ x ∈ tr ++ [coins], x ∈ gLog ++ [coins] := fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left [coins] (hinv x h)
      · exact List.mem_append_right _ h
    exact ⟨kemFailBadLog_eq_false_of_subset K hsub, hsub, fun _ => hsub⟩

def smSchemeTrackState {τ Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) :
    SMSchemeRM (StateT τ ProbComp) Key St Msg Coins RCoins C where
  initA := sm.initA
  initB := sm.initB
  send st m r := pure (sm.send st m r)
  receive st c rc := pure (sm.receive st c rc)

/-- Online-halted `transmit` oracle driven by `T : SessionHaltTracker`. -/
def transmitRSessionTracked {Key St Msg Coins RCoins C τ : Type} [SampleableType Coins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT τ ProbComp)) :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      let tr₀ ← StateT.lift get
      let (isBad, trHalt) := T.checkSend s₁ P coins tr₀
      if isBad then
        StateT.lift (set trHalt)
        return none
      else
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
        StateT.lift (set (T.commitSend s₁ P coins out.2 tr₀))
        return some out.2

/-- Online-halted `chall` oracle driven by `T : SessionHaltTracker`. -/
def challRSessionTracked {Key St Msg Coins RCoins C τ : Type} [SampleableType Coins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT τ ProbComp)) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
      let tr₀ ← StateT.lift get
      let (isBad, trHalt) := T.checkSend s₁ P coins tr₀
      if isBad then
        StateT.lift (set trHalt)
        return none
      else
        let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
        StateT.lift (set (T.commitSend s₁ P coins out.2 tr₀))
        return some out.2

/-- `deliver` oracle driven by `T : SessionHaltTracker`: runs `deliverR` and passively updates `τ`. -/
def deliverRSessionTracked {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
      (StateT (GameState St Msg C) (StateT τ ProbComp)) :=
  fun ⟨P, c⟩ => do
    let s₀ ← get
    let tr₀ ← StateT.lift get
    let res ← liftStateT (deliverR sm cfg (P, c))
    StateT.lift (set (T.onDeliver s₀ P c res tr₀))
    return res

/-- Full R-game oracle handler driven by `T : SessionHaltTracker`. -/
def oracleImplRSessionTracked {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (CryptoGames.SM.spec St Msg Coins C)
      (StateT (GameState St Msg C) (StateT τ ProbComp)) :=
  transmitRSessionTracked T sm Δ qep cfg + challRSessionTracked T sm Δ qep cfg +
    deliverRSessionTracked T sm cfg +
    ((fun q => liftStateT (injectR sm Δ qep cfg q)) :
      QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
        (StateT (GameState St Msg C) (StateT τ ProbComp))) +
    ((fun P => liftStateT (corrR cfg P)) :
      QueryImpl (Party →ₒ Option St)
        (StateT (GameState St Msg C) (StateT τ ProbComp)))

/-- Single-session halted `SM.gameR` driven by `T : SessionHaltTracker`. -/
def gameRSessionTracked {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) : ProbComp (Bool × τ) := do
  let b ← $ᵗ Bool
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT τ ProbComp)) +
    oracleImplRSessionTracked T sm Δ qep cfg
  (StateT.run · (T.init k)) do
    let (b', s) ← (simulateQ impl A).run (initState sm.sendPart k b)
    return (b == b' || s.win)

/-- Promotion step on `BHE2EDrvState S ℓ × List τ` initializing `initTrack kS` on success. -/
def bhE2ELocalStartSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    (σH : BHE2EDrvState S ℓ × List τ) (sid : SignalPqxdh.SessionId S) :
    ProbComp (Option ℕ × (BHE2EDrvState S ℓ × List τ)) := do
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

/-- Pure wire-query unwrapping shared by `bhE2EStepLocalSm` variants. -/
def bhDecodeSmWireQuery {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (im : ModelDriverInstanceMeta S) (d : BHModelInst S ℓ)
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
        if c == wirePrekey ::
            (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes then
          some (.inl (.inl (.inr (.B, m.inner))))
        else none
      | none => none
    else
      match bhDecodePreKeyMsgE c with
      | some m =>
        if bhHdrOfPreKeyMsg m == d.hdr then
          some (.inl (.inl (.inr (.B, m.inner))))
        else none
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

/-- Per-session SM step on `BHE2EDrvState S ℓ × List τ` driven by `T : SessionHaltTracker`. -/
def bhE2EStepLocalSmSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvState S ℓ × List τ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    ProbComp (BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)) := do
  let σ := σH.1
  let tracks := σH.2
  if !bhE2EDrvInstClean σ i then return ((none, none, none), σH)
  else
    match σ.insts[i]?, σ.instMeta[i]? with
    | some d, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d then
        let imCorr := { im with bobAccepted := true, ikACorrAtAccept := true }
        let σ' := { σ with instMeta := σ.instMeta.set i imCorr }
        return ((none, none, none), (σ', tracks))
      else
        match d.gs with
        | none => return ((none, none, none), σH)
        | some gs =>
          let spqr := spqrV1SessionUniformCoins C.F K
          let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
          let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
          let runTr (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
              (σ0 : BHE2EDrvState S ℓ) : ProbComp (BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)) := do
            let tr₀ := (tracks[i]?).getD (T.init default)
            let ((r, gs'), tr') ←
              ((oracleImplRSessionTracked T sch (2 + 1) qep cfg q').run gs).run tr₀
            let accepted := bhIsBobAcceptSMResp q' r
            let im' := if !im.bobAccepted && accepted then
                { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ0 d }
              else im
            let σ1 := { σ0 with insts := σ0.insts.set i { d with gs := some gs' },
                                instMeta := σ0.instMeta.set i im' }
            return (bhPackSmResp q' r, (σ1, tracks.set i tr'))
          match bhDecodeSmWireQuery im d q with
          | none => return ((none, none, none), σH)
          | some q' => runTr q' σ
    | _, _ => return ((none, none, none), σH)

/-- Per-session `SessionHaltTracker`-driven E2E model query implementation. -/
def bhE2EDrvImplWithSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ × List τ) ProbComp) := fun q =>
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
    let (idx?, σH') ← liftM (bhE2ELocalStartSessionTracked T.init ki C K (some σH.1.b) σH sid)
    set σH'
    return idx?
  | .inr (.inr ⟨i, sq⟩) => do
    let σH ← get
    let (sr, σH') ← liftM (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)
    set σH'
    return bhUnpackSmResp sq sr

/-- Per-session `SessionHaltTracker`-driven E2E model experiment. -/
def bhE2EExpWithKiSessionTracked {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (secb : Bool) (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', σH) ← (simulateQ (bhE2EDrvImplWithSessionTracked T P ki C K qep decT encT) B).run
    ({ b := b, st := SignalPqxdh.KeyIndState.empty S secb }, [])
  if !allTestedSessionsFresh P σH.1.st then $ᵗ Bool
  else return (b' == b || bhE2EDrvWon σH.1 b)

/-! ## Global send-coin-logged E2E experiment -/

abbrev CoinLogM : Type → Type := WriterT (List (BitVec 512)) ProbComp

def bhE2EStepLocalSmCoinLogged {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    CoinLogM (BHE2ESmResp ℓ × BHE2EDrvState S ℓ) := do
  if !bhE2EDrvInstClean σ i then return ((none, none, none), σ)
  else
    match σ.insts[i]?, σ.instMeta[i]? with
    | some d, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d then
        let imCorr := { im with bobAccepted := true, ikACorrAtAccept := true }
        let σ' := { σ with instMeta := σ.instMeta.set i imCorr }
        return ((none, none, none), σ')
      else
        match d.gs with
        | none => return ((none, none, none), σ)
        | some gs =>
          let spqr := spqrV1SessionUniformCoins C.F K
          let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
          let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
          let runStd (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
              (σ0 : BHE2EDrvState S ℓ) : CoinLogM (BHE2ESmResp ℓ × BHE2EDrvState S ℓ) := do
            let (r, gs') ← (oracleImplRM (smSchemeCoinLogged sch) (2 + 1) qep cfg q').run gs
            let accepted := bhIsBobAcceptSMResp q' r
            let im' := if !im.bobAccepted && accepted then
                { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ0 d }
              else im
            let σ1 := { σ0 with insts := σ0.insts.set i { d with gs := some gs' },
                                instMeta := σ0.instMeta.set i im' }
            return (bhPackSmResp q' r, σ1)
          match q with
          | .inl (.inl (.inr (.A, c))) =>
            if (bhDecodePreKeyMsgE c).isSome then return ((none, none, none), σ)
            else runStd q σ
          | .inl (.inr (.A, c)) =>
            if (bhDecodePreKeyMsgE c).isSome then return ((none, none, none), σ)
            else runStd q σ
          | .inl (.inl (.inr (.B, c))) =>
            if !im.bobAccepted then
              match bhDecodePreKeyMsgE c with
              | some m =>
                if c == wirePrekey ::
                    (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes then
                  runStd (.inl (.inl (.inr (.B, m.inner)))) σ
                else return ((none, none, none), σ)
              | none => return ((none, none, none), σ)
            else
              match bhDecodePreKeyMsgE c with
              | some m =>
                if bhHdrOfPreKeyMsg m == d.hdr then
                  runStd (.inl (.inl (.inr (.B, m.inner)))) σ
                else return ((none, none, none), σ)
              | none => runStd (.inl (.inl (.inr (.B, c)))) σ
          | .inl (.inr (.B, c)) =>
            if !im.bobAccepted then return ((none, none, none), σ)
            else
              match bhDecodePreKeyMsgE c with
              | some m =>
                if bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
                   decide (m.inner.length + 2048 < 2 ^ 32) then
                  runStd (.inl (.inr (.B, m.inner))) σ
                else return ((none, none, none), σ)
              | none => runStd (.inl (.inr (.B, c))) σ
          | _ => runStd q σ
    | _, _ => return ((none, none, none), σ)

def cliE2EDrvImplWithCoinLogged {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ) CoinLogM) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => do
    let σ ← get
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return .noneResp
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return .noneResp
    else
      let (kr, st') ← StateT.lift (liftM ((ki kq).run σ.st))
      set (bhE2EMirror { σ with st := st' } kq kr)
      return kr
  | .inr (.inl (.inr (.startDR sid))) => do
    let σ ← get
    let (idx?, σ') ← StateT.lift (liftM (compositionLocalStart ki C K (some σ.b) σ sid))
    set σ'
    return idx?
  | .inr (.inr ⟨i, sq⟩) => do
    let σ ← get
    let (sr, σ') ← StateT.lift (bhE2EStepLocalSmCoinLogged C K qep decT encT σ i sq)
    set σ'
    return bhUnpackSmResp sq sr

/-- Send-coin-logged E2E model experiment. -/
def cliE2EExpWithKiCoinLogged (secb : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    ProbComp (Bool × List (BitVec 512)) :=
  WriterT.run do
    let b ← liftM ($ᵗ Bool : ProbComp Bool)
    let (b', σ) ← (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT) B).run
      { b := b, st := SignalPqxdh.KeyIndState.empty S secb }
    if !allTestedSessionsFresh P σ.st then liftM ($ᵗ Bool : ProbComp Bool)
    else return (b' == b || bhE2EDrvWon σ b)

/-! ## State-invariant online agreement (`AgreeInv`) and projections -/

structure PreservesInvBad {σ Coins α : Type}
    (good : List Coins → Prop) (Inv : σ → List Coins → Prop)
    (m : StateT σ (StateT (List Coins) ProbComp) α) : Prop where
  pres_bad : ∀ s gLog, ¬ good gLog → ∀ z ∈ support ((m.run s).run gLog), ¬ good z.2
  pres_inv : ∀ s gLog, Inv s gLog → ∀ z ∈ support ((m.run s).run gLog), Inv z.1.2 z.2

structure AgreeInv {σ Coins α : Type}
    (good : List Coins → Prop) (Inv : σ → List Coins → Prop)
    (m₁ m₂ : StateT σ (StateT (List Coins) ProbComp) α) : Prop where
  pres₁ : PreservesInvBad good Inv m₁
  pres₂ : PreservesInvBad good Inv m₂
  agree : ∀ s gLog, Inv s gLog → good gLog → ∀ p : (α × σ) × List Coins → Prop,
    Pr{let z ← (m₁.run s).run gLog}[p z ∧ good z.2] =
      Pr{let z ← (m₂.run s).run gLog}[p z ∧ good z.2]

private theorem ae_mem_support_evalDist {α : Type} (c : ProbComp α) :
    let _ : MeasurableSpace α := ⊤
    ∀ᵐ x ∂𝒟[c], x ∈ support c := by
  let _ : MeasurableSpace α := ⊤
  rw [MeasureTheory.ae_iff]
  change 𝒟[c] {x | x ∉ support c} = 0
  rw [← prEvent_eq_evalDist_of_discrete]
  exact prEvent_eq_zero_of_forall_mem_support _ _ fun x hx hnot => hnot hx

theorem PreservesInvBad.pure {σ Coins α : Type}
    (good : List Coins → Prop) (Inv : σ → List Coins → Prop) (a : α) :
    PreservesInvBad good Inv (pure a : StateT σ (StateT (List Coins) ProbComp) α) where
  pres_bad s gLog hbad z hz := by
    change z ∈ support (Pure.pure ((a, s), gLog)) at hz
    rw [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hbad
  pres_inv s gLog hinv z hz := by
    change z ∈ support (Pure.pure ((a, s), gLog)) at hz
    rw [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hinv

theorem PreservesInvBad.bind {σ Coins α β : Type}
    {good : List Coins → Prop} {Inv : σ → List Coins → Prop}
    {m : StateT σ (StateT (List Coins) ProbComp) α}
    {k : α → StateT σ (StateT (List Coins) ProbComp) β}
    (hm : PreservesInvBad good Inv m) (hk : ∀ a, PreservesInvBad good Inv (k a)) :
    PreservesInvBad good Inv (m >>= k) where
  pres_bad s gLog hbad z hz := by
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
    rcases hz with ⟨x, hx, hz⟩
    exact (hk x.1.1).pres_bad x.1.2 x.2 (hm.pres_bad s gLog hbad x hx) z hz
  pres_inv s gLog hinv z hz := by
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
    rcases hz with ⟨x, hx, hz⟩
    exact (hk x.1.1).pres_inv x.1.2 x.2 (hm.pres_inv s gLog hinv x hx) z hz

theorem AgreeInv.refl {σ Coins α : Type} {good : List Coins → Prop} {Inv : σ → List Coins → Prop}
    {m : StateT σ (StateT (List Coins) ProbComp) α} (hm : PreservesInvBad good Inv m) :
    AgreeInv good Inv m m := ⟨hm, hm, fun _ _ _ _ _ => rfl⟩

theorem AgreeInv.pure {σ Coins α : Type} (good : List Coins → Prop) (Inv : σ → List Coins → Prop)
    (a : α) : AgreeInv good Inv (pure a : StateT σ (StateT (List Coins) ProbComp) α) (pure a) :=
  AgreeInv.refl (PreservesInvBad.pure good Inv a)

theorem AgreeInv.get {σ Coins : Type} (good : List Coins → Prop) (Inv : σ → List Coins → Prop) :
    AgreeInv good Inv (get : StateT σ (StateT (List Coins) ProbComp) σ) get :=
  AgreeInv.refl
    { pres_bad := fun s gLog hbad z hz => by
        change z ∈ support (Pure.pure ((s, s), gLog)) at hz
        rw [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hbad
      pres_inv := fun s gLog hinv z hz => by
        change z ∈ support (Pure.pure ((s, s), gLog)) at hz
        rw [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hinv }

theorem AgreeInv.bind {σ Coins α β : Type} {good : List Coins → Prop} {Inv : σ → List Coins → Prop}
    {m₁ m₂ : StateT σ (StateT (List Coins) ProbComp) α}
    {k₁ k₂ : α → StateT σ (StateT (List Coins) ProbComp) β}
    (hm : AgreeInv good Inv m₁ m₂) (hk : ∀ a, AgreeInv good Inv (k₁ a) (k₂ a)) :
    AgreeInv good Inv (m₁ >>= k₁) (m₂ >>= k₂) where
  pres₁ := PreservesInvBad.bind hm.pres₁ fun a => (hk a).pres₁
  pres₂ := PreservesInvBad.bind hm.pres₂ fun a => (hk a).pres₂
  agree s gLog hinv hgood p := by
    simp only [StateT.run_bind]
    let : MeasurableSpace ((α × σ) × List Coins) := ⊤
    let G : Set ((α × σ) × List Coins) := {x | Inv x.1.2 x.2 ∧ good x.2}
    let F (k : α → StateT σ (StateT (List Coins) ProbComp) β)
        (x : (α × σ) × List Coins) : ℝ≥0∞ :=
      Pr{let z ← ((k x.1.1).run x.1.2).run x.2}[p z ∧ good z.2]
    have hF_ae {k : α → StateT σ (StateT (List Coins) ProbComp) β}
        (hm_p : PreservesInvBad good Inv m₁ ∨ m₁ = m₂)
        (hm_i : ∀ x ∈ support ((m₁.run s).run gLog), Inv x.1.2 x.2)
        (hk_b : ∀ a, PreservesInvBad good Inv (k a)) (m : StateT σ (StateT (List Coins) ProbComp) α)
        (hm_inv : PreservesInvBad good Inv m) :
        ∀ᵐ x ∂𝒟[(m.run s).run gLog], F k x = G.indicator (F k) x := by
      filter_upwards [ae_mem_support_evalDist ((m.run s).run gLog)] with x hx
      have hxInv : Inv x.1.2 x.2 := hm_inv.pres_inv s gLog hinv x hx
      by_cases hxg : good x.2
      · exact (Set.indicator_of_mem (show x ∈ G from ⟨hxInv, hxg⟩) (F k)).symm
      · rw [Set.indicator_of_notMem fun h => hxg h.2]
        exact prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ⟨_, hg⟩ =>
          (hk_b x.1.1).pres_bad x.1.2 x.2 hxg z hz hg
    have hF_ae₁ := hF_ae (.inl hm.pres₁) (hm.pres₁.pres_inv s gLog hinv) (fun a => (hk a).pres₁) m₁ hm.pres₁
    have hF_ae₂ := hF_ae (.inl hm.pres₁) (hm.pres₁.pres_inv s gLog hinv) (fun a => (hk a).pres₂) m₂ hm.pres₂
    have hF_eq_G (x : (α × σ) × List Coins) : G.indicator (F k₁) x = G.indicator (F k₂) x := by
      by_cases hx : x ∈ G
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        exact (hk x.1.1).agree x.1.2 x.2 hx.1 hx.2 p
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    have hrestrict : 𝒟[(m₁.run s).run gLog].restrict G = 𝒟[(m₂.run s).run gLog].restrict G := by
      refine MeasureTheory.Measure.ext fun A hA => ?_
      rw [MeasureTheory.Measure.restrict_apply hA, MeasureTheory.Measure.restrict_apply hA]
      have hSet : A ∩ G = {z | (z ∈ A ∧ Inv z.1.2 z.2) ∧ good z.2} := by
        ext z; exact ⟨fun ⟨hzA, hi, hg⟩ => ⟨⟨hzA, hi⟩, hg⟩, fun ⟨⟨hzA, hi⟩, hg⟩ => ⟨hzA, hi, hg⟩⟩
      rw [hSet, ← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete]
      exact hm.agree s gLog hinv hgood (fun z => z ∈ A ∧ Inv z.1.2 z.2)
    rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
    change ∫⁻ x, F k₁ x ∂𝒟[(m₁.run s).run gLog] = ∫⁻ x, F k₂ x ∂𝒟[(m₂.run s).run gLog]
    calc ∫⁻ x, F k₁ x ∂𝒟[(m₁.run s).run gLog]
        = ∫⁻ x, G.indicator (F k₁) x ∂𝒟[(m₁.run s).run gLog] :=
            MeasureTheory.lintegral_congr_ae hF_ae₁
      _ = ∫⁻ x, G.indicator (F k₂) x ∂𝒟[(m₁.run s).run gLog] :=
            MeasureTheory.lintegral_congr hF_eq_G
      _ = ∫⁻ x, F k₂ x ∂(𝒟[(m₁.run s).run gLog].restrict G) :=
            MeasureTheory.lintegral_indicator MeasurableSet.of_discrete _
      _ = ∫⁻ x, F k₂ x ∂(𝒟[(m₂.run s).run gLog].restrict G) := by rw [hrestrict]
      _ = ∫⁻ x, G.indicator (F k₂) x ∂𝒟[(m₂.run s).run gLog] :=
            (MeasureTheory.lintegral_indicator MeasurableSet.of_discrete _).symm
      _ = ∫⁻ x, F k₂ x ∂𝒟[(m₂.run s).run gLog] :=
            (MeasureTheory.lintegral_congr_ae hF_ae₂).symm

theorem AgreeInv.simulateQ {σ Coins ι : Type} {ospec : OracleSpec ι}
    {good : List Coins → Prop} {Inv : σ → List Coins → Prop}
    (impl₁ impl₂ : QueryImpl ospec (StateT σ (StateT (List Coins) ProbComp)))
    (himpl : ∀ t, AgreeInv good Inv (impl₁ t) (impl₂ t)) {α : Type} (oa : OracleComp ospec α) :
    AgreeInv good Inv (simulateQ impl₁ oa) (simulateQ impl₂ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact AgreeInv.pure good Inv a
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query]
    exact AgreeInv.bind (himpl t) ih

def ProjectsToLogged {σ τ Coins α : Type}
    (m₁ : StateT (σ × List τ) (StateT (List Coins) ProbComp) α)
    (m₀ : StateT σ (WriterT (List Coins) ProbComp) α) : Prop :=
  ∀ (s : σ) (tracks : List τ) (gLog : List Coins),
    (fun z => ((z.1.1, z.1.2.1), z.2)) <$> ((m₁.run (s, tracks)).run gLog) =
      (fun zw => (zw.1, gLog ++ zw.2)) <$> (m₀.run s).run

theorem ProjectsToLogged.pure {σ τ Coins α : Type} (a : α) :
    ProjectsToLogged (σ := σ) (τ := τ) (Coins := Coins) (pure a) (pure a) := by
  intro s tracks gLog
  change (fun z => ((z.1.1, z.1.2.1), z.2)) <$>
      (Pure.pure ((a, (s, tracks)), gLog) : ProbComp _) =
    (fun zw => (zw.1, gLog ++ zw.2)) <$> (Pure.pure ((a, s), []) : ProbComp _)
  simp

theorem ProjectsToLogged.bind {σ τ Coins α β : Type}
    {m₁ : StateT (σ × List τ) (StateT (List Coins) ProbComp) α}
    {m₀ : StateT σ (WriterT (List Coins) ProbComp) α}
    {k₁ : α → StateT (σ × List τ) (StateT (List Coins) ProbComp) β}
    {k₀ : α → StateT σ (WriterT (List Coins) ProbComp) β}
    (hm : ProjectsToLogged m₁ m₀) (hk : ∀ a, ProjectsToLogged (k₁ a) (k₀ a)) :
    ProjectsToLogged (m₁ >>= k₁) (m₀ >>= k₀) := by
  intro s tracks gLog
  simp only [StateT.run_bind, WriterT.run_bind]
  rw [map_eq_bind_pure_comp, bind_assoc]
  conv_lhs => arg 2; ext z; rw [← map_eq_bind_pure_comp, hk z.1.1 z.1.2.1 z.1.2.2 z.2]
  have hm_eq := hm s tracks gLog
  rw [map_eq_bind_pure_comp] at hm_eq
  calc ((m₁.run (s, tracks)).run gLog >>= fun z =>
          (fun zw => (zw.1, z.2 ++ zw.2)) <$> ((k₀ z.1.1).run z.1.2.1).run)
      = (((m₁.run (s, tracks)).run gLog >>=
            (Pure.pure ∘ fun z => ((z.1.1, z.1.2.1), z.2))) >>= fun y =>
          (fun zw => (zw.1, y.2 ++ zw.2)) <$> ((k₀ y.1.1).run y.1.2).run) := by simp [bind_assoc]
    _ = (((fun zw => (zw.1, gLog ++ zw.2)) <$> (m₀.run s).run) >>= fun y =>
          (fun zw => (zw.1, y.2 ++ zw.2)) <$> ((k₀ y.1.1).run y.1.2).run) := by rw [hm_eq]
    _ = (fun zw => (zw.1, gLog ++ zw.2)) <$> ((m₀.run s).run >>= fun x =>
          (fun y => (y.1, x.2 ++ y.2)) <$> ((k₀ x.1.1).run x.1.2).run) := by
        simp [map_eq_bind_pure_comp, bind_assoc, List.append_assoc]

theorem ProjectsToLogged.simulateQ {σ τ Coins ι : Type} {ospec : OracleSpec ι}
    (impl₁ : QueryImpl ospec (StateT (σ × List τ) (StateT (List Coins) ProbComp)))
    (impl₀ : QueryImpl ospec (StateT σ (WriterT (List Coins) ProbComp)))
    (himpl : ∀ t, ProjectsToLogged (impl₁ t) (impl₀ t)) {α : Type} (oa : OracleComp ospec α) :
    ProjectsToLogged (simulateQ impl₁ oa) (simulateQ impl₀ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact ProjectsToLogged.pure a
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query]
    exact ProjectsToLogged.bind (himpl t) ih

def ProjectsToHalted {σH Coins α : Type}
    (m₂ : StateT σH (StateT (List Coins) ProbComp) α) (mH : StateT σH ProbComp α) : Prop :=
  ∀ (s : σH) (gLog : List Coins), Prod.fst <$> ((m₂.run s).run gLog) = mH.run s

theorem ProjectsToHalted.pure {σH Coins α : Type} (a : α) :
    ProjectsToHalted (σH := σH) (Coins := Coins) (pure a) (pure a) := by
  intro s gLog
  change Prod.fst <$> (Pure.pure ((a, s), gLog) : ProbComp _) = Pure.pure (a, s)
  simp

theorem ProjectsToHalted.bind {σH Coins α β : Type}
    {m₂ : StateT σH (StateT (List Coins) ProbComp) α} {mH : StateT σH ProbComp α}
    {k₂ : α → StateT σH (StateT (List Coins) ProbComp) β} {kH : α → StateT σH ProbComp β}
    (hm : ProjectsToHalted m₂ mH) (hk : ∀ a, ProjectsToHalted (k₂ a) (kH a)) :
    ProjectsToHalted (m₂ >>= k₂) (mH >>= kH) := by
  intro s gLog
  simp only [StateT.run_bind]
  rw [map_eq_bind_pure_comp, bind_assoc]
  conv_lhs => arg 2; ext z; rw [← map_eq_bind_pure_comp, hk z.1.1 z.1.2 z.2]
  have hm_eq := hm s gLog
  rw [map_eq_bind_pure_comp] at hm_eq
  calc ((m₂.run s).run gLog >>= fun z => (kH z.1.1).run z.1.2)
      = (((m₂.run s).run gLog >>= (Pure.pure ∘ Prod.fst)) >>= fun x => (kH x.1).run x.2) := by
        simp [bind_assoc]
    _ = (mH.run s >>= fun x => (kH x.1).run x.2) := by rw [hm_eq]

theorem ProjectsToHalted.simulateQ {σH Coins ι : Type} {ospec : OracleSpec ι}
    (impl₂ : QueryImpl ospec (StateT σH (StateT (List Coins) ProbComp)))
    (implH : QueryImpl ospec (StateT σH ProbComp))
    (himpl : ∀ t, ProjectsToHalted (impl₂ t) (implH t)) {α : Type} (oa : OracleComp ospec α) :
    ProjectsToHalted (simulateQ impl₂ oa) (simulateQ implH oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact ProjectsToHalted.pure a
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query]
    exact ProjectsToHalted.bind (himpl t) ih

/-! ## Coupled session oracles -/

private local instance instLawfulMonadWriterTListCoin {Coins : Type} {M : Type → Type}
    [Monad M] [LawfulMonad M] : LawfulMonad (WriterT (List Coins) M) :=
  LawfulMonad.mk' (id_map := fun {_} _ => by ext; simp)
    (pure_bind := fun {_ _} _ _ => by ext; simp)
    (bind_assoc := fun {_ _ _} _ _ _ => by ext; simp)
    (bind_pure_comp := fun {_ _} _ _ => by ext; simp)

@[simp] private theorem liftStateT_run {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    {σ α : Type} (x : StateT σ ProbComp α) (s : σ) :
    (liftStateT x : StateT σ m α).run s = liftM (x.run s) := rfl

private theorem liftM_prob_run {Coins α : Type} (c : ProbComp α) (log : List Coins) :
    (liftM c : StateT (List Coins) ProbComp α).run log = (fun a => (a, log)) <$> c := by
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift, StateT.run]
  simp [map_eq_bind_pure_comp]

private def embedCoinW {Coins α : Type} (m : WriterT (List Coins) ProbComp α) :
    StateT (List Coins) ProbComp α :=
  fun log => do let (a, w) ← m.run; return (a, log ++ w)

@[simp] private theorem embedCoinW_run {Coins α : Type}
    (m : WriterT (List Coins) ProbComp α) (log : List Coins) :
    (embedCoinW m).run log = (do let (a, w) ← m.run; return (a, log ++ w)) := rfl
@[simp] private theorem embedCoinW_pure {Coins α : Type} (a : α) :
    embedCoinW (pure a : WriterT (List Coins) ProbComp α) = pure a := by ext log; simp
@[simp] private theorem embedCoinW_liftM {Coins α : Type} (c : ProbComp α) :
    embedCoinW (liftM c : WriterT (List Coins) ProbComp α) = liftM c := by
  ext log
  dsimp [embedCoinW, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
    WriterT.liftTell, StateT.lift]
  simp [map_eq_bind_pure_comp, bind_assoc]
@[simp] private theorem embedCoinW_tell {Coins : Type} (w : List Coins) :
    embedCoinW (MonadWriter.tell w) = fun log => pure ((), log ++ w) := by
  ext log; dsimp [StateT.run]; simp
@[simp] private theorem embedCoinW_bind {Coins α β : Type}
    (m : WriterT (List Coins) ProbComp α) (f : α → WriterT (List Coins) ProbComp β) :
    embedCoinW (m >>= f) = embedCoinW m >>= fun a => embedCoinW (f a) := by
  ext log; simp [WriterT.run_bind, StateT.run_bind, List.append_assoc]
@[simp] private theorem embedCoinW_map {Coins α β : Type}
    (f : α → β) (m : WriterT (List Coins) ProbComp α) :
    embedCoinW (f <$> m) = f <$> embedCoinW m := by
  rw [← bind_pure_comp, ← bind_pure_comp, embedCoinW_bind]; simp
private def embedCoinS1 {Coins σ α : Type} (m : StateT σ (WriterT (List Coins) ProbComp) α) :
    StateT σ (StateT (List Coins) ProbComp) α := fun s => embedCoinW (m.run s)
@[simp] private theorem embedCoinS1_run {Coins σ α : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α) (s : σ) :
    (embedCoinS1 m).run s = embedCoinW (m.run s) := rfl
@[simp] private theorem embedCoinS1_pure {Coins σ α : Type} (a : α) :
    embedCoinS1 (pure a : StateT σ (WriterT (List Coins) ProbComp) α) = pure a := by ext s log; simp
@[simp] private theorem embedCoinS1_bind {Coins σ α β : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α)
    (f : α → StateT σ (WriterT (List Coins) ProbComp) β) :
    embedCoinS1 (m >>= f) = embedCoinS1 m >>= fun a => embedCoinS1 (f a) := by
  ext s log; simp [StateT.run_bind]
@[simp] private theorem embedCoinS1_map {Coins σ α β : Type}
    (f : α → β) (m : StateT σ (WriterT (List Coins) ProbComp) α) :
    embedCoinS1 (f <$> m) = f <$> embedCoinS1 m := by
  rw [← bind_pure_comp, ← bind_pure_comp, embedCoinS1_bind]; simp
@[simp] private theorem embedCoinS1_get {Coins σ : Type} :
    embedCoinS1 (get : StateT σ (WriterT (List Coins) ProbComp) σ) = get := by ext s log; simp
@[simp] private theorem embedCoinS1_set {Coins σ : Type} (s' : σ) :
    embedCoinS1 (set s' : StateT σ (WriterT (List Coins) ProbComp) PUnit) = set s' := by
  ext s log; simp
@[simp] private theorem embedCoinS1_lift {Coins σ α : Type}
    (m : WriterT (List Coins) ProbComp α) :
    embedCoinS1 (StateT.lift m : StateT σ (WriterT (List Coins) ProbComp) α) =
      StateT.lift (embedCoinW m) := by ext s log; simp [StateT.run_lift]

private theorem liftM_state_prob_run {σ α : Type} (c : ProbComp α) (s : σ) :
    (liftM c : StateT σ ProbComp α).run s = (fun a => (a, s)) <$> c := by
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift, StateT.run]
  simp [map_eq_bind_pure_comp]

@[simp] private theorem embedCoinS1_liftStateT {Coins σ α : Type} (x : StateT σ ProbComp α) :
    embedCoinS1 (liftStateT x : StateT σ (WriterT (List Coins) ProbComp) α) = liftStateT x := by
  ext s log; have h := congrArg (fun m => m.run log) (embedCoinW_liftM (x.run s)); simp at h ⊢

private def smSchemeCoinState {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) :
    SMSchemeRM (StateT (List Coins) ProbComp) Key St Msg Coins RCoins C where
  initA := sm.initA
  initB := sm.initB
  send st m r := fun log => pure (sm.send st m r, log ++ [r])
  receive st c rc := pure (sm.receive st c rc)

private theorem embedCoinS1_oracleImplRM_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (CryptoGames.SM.spec St Msg Coins C).Domain) :
    embedCoinS1 (oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg q) =
      oracleImplRM (smSchemeCoinState sm) Δ qep cfg q := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change embedCoinS1 (transmitRM (smSchemeCoinLogged sm) Δ qep cfg (P, m, r)) =
      transmitRM (smSchemeCoinState sm) Δ qep cfg (P, m, r)
    unfold transmitRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact embedCoinS1_pure _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_bind,
        embedCoinS1_lift, embedCoinW_liftM, embedCoinS1_pure]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact embedCoinS1_pure _
      | some s₁ =>
        ext s₂ log
        simp [smSchemeCoinLogged, smSchemeCoinState, StateT.run_bind, StateT.run_lift, StateT.run_set]
        dsimp [StateT.run]; simp
  · change embedCoinS1 (challRM (smSchemeCoinLogged sm) Δ qep cfg (P, m₀, m₁, r)) =
      challRM (smSchemeCoinState sm) Δ qep cfg (P, m₀, m₁, r)
    unfold challRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact embedCoinS1_pure _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_bind,
        embedCoinS1_lift, embedCoinW_liftM, embedCoinS1_pure]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact embedCoinS1_pure _
      | some s₁ =>
        dsimp only
        cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
        · ext s₂ log
          simp [smSchemeCoinLogged, smSchemeCoinState, StateT.run_bind, StateT.run_lift, StateT.run_set]
          dsimp [StateT.run]; simp
        · exact embedCoinS1_pure _
  · change embedCoinS1 (deliverRM (smSchemeCoinLogged sm) cfg (P, c)) =
      deliverRM (smSchemeCoinState sm) cfg (P, c)
    unfold deliverRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_pure]
    cases s.inTransit P.other c with
    | none => exact embedCoinS1_pure _
    | some r =>
      dsimp only
      simp only [embedCoinS1_bind, embedCoinS1_lift, embedCoinW_liftM, smSchemeCoinLogged,
        embedCoinW_pure, smSchemeCoinState]
      congr 1; funext rc; congr 1; funext out
      cases out with
      | none => split_ifs <;> simp
      | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · change embedCoinS1 (injectRM (smSchemeCoinLogged sm) Δ qep cfg (P, c)) =
      injectRM (smSchemeCoinState sm) Δ qep cfg (P, c)
    unfold injectRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c)) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_bind, embedCoinS1_lift,
        embedCoinW_liftM, smSchemeCoinLogged, embedCoinW_pure, embedCoinS1_pure, smSchemeCoinState]
    congr 1; funext rc; congr 1; funext out
    cases out with
    | none => exact embedCoinS1_pure _
    | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · exact embedCoinS1_liftStateT _

private theorem deliverRM_smSchemeCoinState_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : ConfigR St Msg C) (q : Party × C) :
    deliverRM (smSchemeCoinState sm) cfg q = liftStateT (deliverR sm cfg q) := by
  rcases q with ⟨P, c⟩; ext s log; rw [liftStateT_run, liftM_prob_run]
  unfold deliverRM deliverR smSchemeCoinState; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · cases s.inTransit P.other c with
    | none => simp
    | some r =>
      dsimp only
      simp only [StateT.run_bind, StateT.run_lift, liftM_state_prob_run,
        map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      congr 1; funext rc
      rcases sm.receive (s.st P) c rc with _ | ⟨st', t', i', m'⟩ <;> dsimp only <;>
        repeat' split_ifs <;> simp [StateT.run_map, StateT.run_set, StateT.run_pure, Function.comp_def]
  · simp

private theorem injectRM_smSchemeCoinState_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : Party × C) :
    injectRM (smSchemeCoinState sm) Δ qep cfg q = liftStateT (injectR sm Δ qep cfg q) := by
  rcases q with ⟨P, c⟩; ext s log; rw [liftStateT_run, liftM_prob_run]
  unfold injectRM injectR smSchemeCoinState; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c))
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
      liftM_state_prob_run, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    congr 1; funext rc
    rcases sm.receive (s.st P) c rc with _ | ⟨st', t', i', m'⟩ <;> dsimp only <;>
      (try repeat' split_ifs) <;>
      simp [StateT.run_map, StateT.run_set, StateT.run_pure, Function.comp_def]
  · simp

def transmitLoggedTracked {Key St Msg Coins RCoins C τ : Type} [SampleableType Coins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp)) :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      let tg ← StateT.lift get
      let out := sm.send (s₁.st P) m coins
      set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
      StateT.lift (set (T.commitSend s₁ P coins out.2 tg.1, tg.2 ++ [coins]))
      return some out.2

def challLoggedTracked {Key St Msg Coins RCoins C τ : Type} [SampleableType Coins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp)) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
      let tg ← StateT.lift get
      let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
      let out := sm.send (s₁.st P) m coins
      set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
      StateT.lift (set (T.commitSend s₁ P coins out.2 tg.1, tg.2 ++ [coins]))
      return some out.2

def transmitHaltedLogged {Key St Msg Coins RCoins C τ : Type} [SampleableType Coins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp)) :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      let tg ← StateT.lift get
      let (isBad, trHalt) := T.checkSend s₁ P coins tg.1
      if isBad then
        StateT.lift (set (trHalt, tg.2 ++ [coins]))
        return none
      else
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
        StateT.lift (set (T.commitSend s₁ P coins out.2 tg.1, tg.2 ++ [coins]))
        return some out.2

def challHaltedLogged {Key St Msg Coins RCoins C τ : Type} [SampleableType Coins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp)) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
      let tg ← StateT.lift get
      let (isBad, trHalt) := T.checkSend s₁ P coins tg.1
      if isBad then
        StateT.lift (set (trHalt, tg.2 ++ [coins]))
        return none
      else
        let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
        StateT.lift (set (T.commitSend s₁ P coins out.2 tg.1, tg.2 ++ [coins]))
        return some out.2

def deliverBothLogged {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
      (StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp)) :=
  fun ⟨P, c⟩ => do
    let s₀ ← get; let tg ← StateT.lift get
    let res ← liftStateT (deliverR sm cfg (P, c))
    StateT.lift (set (T.onDeliver s₀ P c res tg.1, tg.2))
    return res

def oracleLoggedTracked {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (CryptoGames.SM.spec St Msg Coins C)
      (StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp)) :=
  transmitLoggedTracked T sm Δ qep cfg + challLoggedTracked T sm Δ qep cfg +
    deliverBothLogged T sm cfg +
    ((fun q => liftStateT (injectR sm Δ qep cfg q)) :
      QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
        (StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp))) +
    ((fun P => liftStateT (corrR cfg P)) :
      QueryImpl (Party →ₒ Option St)
        (StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp)))

def oracleHaltedLogged {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (CryptoGames.SM.spec St Msg Coins C)
      (StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp)) :=
  transmitHaltedLogged T sm Δ qep cfg + challHaltedLogged T sm Δ qep cfg +
    deliverBothLogged T sm cfg +
    ((fun q => liftStateT (injectR sm Δ qep cfg q)) :
      QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
        (StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp))) +
    ((fun P => liftStateT (corrR cfg P)) :
      QueryImpl (Party →ₒ Option St)
        (StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp)))

private theorem liftStateT_proj_snd {σ τ Coins α : Type} (x : StateT σ ProbComp α)
    (s : σ) (tr₀ : τ) (gLog : List Coins) :
    (fun z : (α × σ) × (τ × List Coins) => (z.1, z.2.2)) <$>
        (((liftStateT x : StateT σ (StateT (τ × List Coins) ProbComp) α).run s).run (tr₀, gLog)) =
      ((liftStateT x : StateT σ (StateT (List Coins) ProbComp) α).run s).run gLog := by
  simp only [liftStateT_run]
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
  simp [map_eq_bind_pure_comp, bind_assoc]

private theorem liftStateT_proj_fst {σ τ Coins α : Type} (x : StateT σ ProbComp α)
    (s : σ) (tr₀ : τ) (gLog : List Coins) :
    (fun z : (α × σ) × (τ × List Coins) => (z.1, z.2.1)) <$>
        (((liftStateT x : StateT σ (StateT (τ × List Coins) ProbComp) α).run s).run (tr₀, gLog)) =
      ((liftStateT x : StateT σ (StateT τ ProbComp) α).run s).run tr₀ := by
  simp only [liftStateT_run]
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
  simp [map_eq_bind_pure_comp, bind_assoc]

theorem oracleLoggedTracked_proj {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (CryptoGames.SM.spec St Msg Coins C).Domain)
    (gs : GameState St Msg C) (tr₀ : τ) (gLog : List Coins) :
    (fun z => (z.1, z.2.2)) <$>
        (((oracleLoggedTracked T sm Δ qep cfg q).run gs).run (tr₀, gLog)) =
      (fun zw => (zw.1, gLog ++ zw.2)) <$>
        ((oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg q).run gs).run := by
  have hrhs : (fun zw => (zw.1, gLog ++ zw.2)) <$>
        ((oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg q).run gs).run =
      ((oracleImplRM (smSchemeCoinState sm) Δ qep cfg q).run gs).run gLog := by
    have h := congrArg (fun m => (m.run gs).run gLog) (embedCoinS1_oracleImplRM_eq sm Δ qep cfg q)
    simpa [embedCoinS1, embedCoinW, map_eq_bind_pure_comp] using h
  rw [hrhs]
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change (fun z => (z.1, z.2.2)) <$>
        (((transmitLoggedTracked T sm Δ qep cfg (P, m, r)).run gs).run (tr₀, gLog)) =
      ((transmitRM (smSchemeCoinState sm) Δ qep cfg (P, m, r)).run gs).run gLog
    unfold transmitLoggedTracked transmitRM
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK gs P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · simp
    · cases gs.win <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp, bind_assoc]
        dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
        simp only [bind_assoc, pure_bind]
        congr 1; funext ⟨coins, bad⟩
        cases gs.epMgmt Δ qep P bad <;> dsimp [smSchemeCoinState, StateT.run] <;> simp
      · simp
  · change (fun z => (z.1, z.2.2)) <$>
        (((challLoggedTracked T sm Δ qep cfg (P, m₀, m₁, r)).run gs).run (tr₀, gLog)) =
      ((challRM (smSchemeCoinState sm) Δ qep cfg (P, m₀, m₁, r)).run gs).run gLog
    unfold challLoggedTracked challRM
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK gs P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · simp
    · cases gs.win <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp, bind_assoc]
        dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
        simp only [bind_assoc, pure_bind]
        congr 1; funext ⟨coins, bad⟩
        cases gs.epMgmt Δ qep P bad with
        | none => simp
        | some s₁ =>
          dsimp only
          cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P))) <;>
            dsimp [smSchemeCoinState, StateT.run] <;> simp
      · simp
  · change (fun z => (z.1, z.2.2)) <$>
        (((deliverBothLogged T sm cfg (P, c)).run gs).run (tr₀, gLog)) =
      ((deliverRM (smSchemeCoinState sm) cfg (P, c)).run gs).run gLog
    rw [deliverRM_smSchemeCoinState_eq]
    unfold deliverBothLogged
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, liftStateT_run, pure_bind]
    dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
    simp [map_eq_bind_pure_comp, bind_assoc]
  · change (fun z => (z.1, z.2.2)) <$>
        (((liftStateT (injectR sm Δ qep cfg (P, c)) :
          StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp) _).run gs).run
          (tr₀, gLog)) =
      ((injectRM (smSchemeCoinState sm) Δ qep cfg (P, c)).run gs).run gLog
    rw [injectRM_smSchemeCoinState_eq]
    exact liftStateT_proj_snd _ gs tr₀ gLog
  · exact liftStateT_proj_snd (corrR cfg P) gs tr₀ gLog

theorem oracleHaltedLogged_proj {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (CryptoGames.SM.spec St Msg Coins C).Domain)
    (gs : GameState St Msg C) (tr₀ : τ) (gLog : List Coins) :
    (fun z => (z.1, z.2.1)) <$>
        (((oracleHaltedLogged T sm Δ qep cfg q).run gs).run (tr₀, gLog)) =
      ((oracleImplRSessionTracked T sm Δ qep cfg q).run gs).run tr₀ := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change (fun z => (z.1, z.2.1)) <$>
        (((transmitHaltedLogged T sm Δ qep cfg (P, m, r)).run gs).run (tr₀, gLog)) =
      ((transmitRSessionTracked T sm Δ qep cfg (P, m, r)).run gs).run tr₀
    unfold transmitHaltedLogged transmitRSessionTracked
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK gs P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · simp
    · cases gs.win <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp, bind_assoc]
        dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
        simp only [bind_assoc, pure_bind]
        congr 1; funext ⟨coins, bad⟩
        cases gs.epMgmt Δ qep P bad with
        | none => simp
        | some s₁ => cases hb : (T.checkSend s₁ P coins tr₀).1 <;> simp [hb]
      · simp
  · change (fun z => (z.1, z.2.1)) <$>
        (((challHaltedLogged T sm Δ qep cfg (P, m₀, m₁, r)).run gs).run (tr₀, gLog)) =
      ((challRSessionTracked T sm Δ qep cfg (P, m₀, m₁, r)).run gs).run tr₀
    unfold challHaltedLogged challRSessionTracked
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK gs P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · simp
    · cases gs.win <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp, bind_assoc]
        dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
        simp only [bind_assoc, pure_bind]
        congr 1; funext ⟨coins, bad⟩
        cases gs.epMgmt Δ qep P bad with
        | none => simp
        | some s₁ =>
          dsimp only
          cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
          · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift]
            cases hb : (T.checkSend s₁ P coins tr₀).1 <;> simp [hb]
          · simp
      · simp
  · change (fun z => (z.1, z.2.1)) <$>
        (((deliverBothLogged T sm cfg (P, c)).run gs).run (tr₀, gLog)) =
      ((deliverRSessionTracked T sm cfg (P, c)).run gs).run tr₀
    unfold deliverBothLogged deliverRSessionTracked
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, liftStateT_run, pure_bind]
    dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
    simp [map_eq_bind_pure_comp, bind_assoc]
  · exact liftStateT_proj_fst (injectR sm Δ qep cfg (P, c)) gs tr₀ gLog
  · exact liftStateT_proj_fst (corrR cfg P) gs tr₀ gLog

end Computational.Proofs.LibsignalCli.MainHaltedCoupling
