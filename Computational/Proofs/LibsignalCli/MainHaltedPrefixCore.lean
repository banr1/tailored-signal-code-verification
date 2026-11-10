/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.Game.ModelIface
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers
public import Computational.Proofs.E2E.ComposedPrefixHelpers
import Computational.Proofs.GameHop.GlobalHybrid
import VCVio.EvalDist.Monad.Basic

/-!
# Parametric Session-Tracked `bhPrefixRedWith` Core

**Checked by Lean.** Defines `SessionHaltTracker`, its soundness invariant
`ValidSessionHaltTracker`, and the session-tracked counterparts of the single-session R-game,
multi-session E2E model experiments, and shallow two-stage reduction `bhPrefixRedWithSessionTracked`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped ENNReal BigOperators
open OracleComp OracleSpec

namespace Computational.Proofs.LibsignalCli.MainHaltedPrefixCore

open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoGames.SM (Adversary ConfigR GameState RecvResult corrR initState samIfNec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (BHDRCtlQuery BHE2EDrvState BHE2ESmResp BHModelInst
  BHPrefixCtx BHTargetQuery BHTargetResp BhShallowTwoStageRed Bytes ModelDriverInstanceMeta
  SMSchemeRM SampledSessionKey allTestedSessionsFresh bhBytesWord
  bhDecodePreKeyMsgE bhDrvKiQueryOk bhE2EDrvInstClean
  bhE2EDrvWon bhE2EFinishStartSpk bhE2EGuard bhE2EInstIkACorr bhE2EMirror bhExpectedPreKeyMsg
  bhHdrOfPreKeyMsg bhIdKeyOf bhInitRegId bhIsBobAcceptSMResp bhIsBobRecvSMQuery
  bhKeySOf bhLiftP bhNoOpkRespPromoted bhPackSmResp
  bhShallowCheckExtSm bhShallowCommitExtSm bhShallowFinishPrefix bhTargetGameSpec bhTargetQenc
  bhTargetRdec bhUnpackSmResp compositionLocalStart configRefuseEarlyBobCorr deliverRM epMgmt_b
  injectRM liftStateT paramsIdsWithSpqr prob_bind_congr_of_support sessionSchemeFixedSpk
  shortCiphertext wirePrekey)

def bhClassifyTargetOnly {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type}
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool) :
    (bhTargetGameSpec S ℓ PQC).Domain → Bool
  | .inl (.inl kq) => pKi kq
  | .inl (.inr cq) => pCtl cq
  | .inr ⟨i, _⟩ => pInst i

abbrev bhClassifyTarget {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type}
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool) :
    (unifSpec + bhTargetGameSpec S ℓ PQC).Domain → Bool :=
  fun x => match x with
    | .inl _ => false
    | .inr t => bhClassifyTargetOnly pKi pCtl pInst t

theorem stateT_run_lift {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

theorem stateT_run_liftM {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

/-! ## Per-session halt tracker and tracked oracles -/

/-- Per-session deterministic halt tracker over state `τ` with `init`, `onSend` (returning
`(halt, trHalt, mkOk)`), and passive `onDeliver` transitions. -/
structure SessionHaltTracker (St Msg Coins C Key τ : Type) where
  init : Key → τ
  onSend : GameState St Msg C → Party → Coins → τ → Bool × τ × (C → τ)
  onDeliver : GameState St Msg C → Party → C → Option (RecvResult Msg) → τ → τ

/-- Soundness invariant relating a per-session `SessionHaltTracker` to `badGlobal` so `onSend` never
halts while `badGlobal` remains `false` on the global send-coin log. -/
structure ValidSessionHaltTracker {St Msg Coins C Key τ : Type}
    (badGlobal : List Coins → Bool)
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (TrInv : τ → List Coins → Prop) : Prop where
  inv_init : ∀ (k : Key) (gLog : List Coins), TrInv (T.init k) gLog
  inv_mono : ∀ {tr : τ} {gLog : List Coins} (c : Coins),
    TrInv tr gLog → TrInv tr (gLog ++ [c])
  inv_deliver : ∀ s₀ P c res {tr : τ} {gLog : List Coins},
    TrInv tr gLog → TrInv (T.onDeliver s₀ P c res tr) gLog
  send_good : ∀ s₁ P coins {tr : τ} {gLog : List Coins}, TrInv tr gLog →
    (badGlobal (gLog ++ [coins]) = false → (T.onSend s₁ P coins tr).1 = false) ∧
    TrInv (T.onSend s₁ P coins tr).2.1 (gLog ++ [coins]) ∧
    (∀ ct, TrInv ((T.onSend s₁ P coins tr).2.2 ct) (gLog ++ [coins]))

/-- Canonical `List Coins` instance of `SessionHaltTracker` recovering coin-list `badLog`. -/
def coinLogSessionTracker {St Msg Coins C Key : Type} (badLog : List Coins → Bool) :
    SessionHaltTracker St Msg Coins C Key (List Coins) where
  init _ := []
  onSend _ _ coins log :=
    let log' := log ++ [coins]
    (badLog log', log', fun _ => log')
  onDeliver _ _ _ _ log := log

/-- Model-state E2E driver state augmented with one `τ` tracker entry per promoted session instance
(`σH.2.length = σH.1.insts.length`). -/
abbrev BHE2EDrvStateSessionTracked (τ : Type) (S : SignalPqxdh.Setup) (ℓ : ℕ) : Type :=
  BHE2EDrvState S ℓ × List τ

def smSchemeTrackState {τ Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) :
    SMSchemeRM (StateT τ ProbComp) Key St Msg Coins RCoins C where
  initA := sm.initA
  initB := sm.initB
  send st m r := pure (sm.send st m r)
  receive st c rc := pure (sm.receive st c rc)

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
      let out := sm.send (s₁.st P) m coins
      let isBad ← StateT.lift (fun tr =>
        let (b, trHalt, mkOk) := T.onSend s₁ P coins tr
        pure (b, if b then trHalt else mkOk out.2))
      if isBad then return none
      else
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
        return some out.2

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
      let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
      let out := sm.send (s₁.st P) m coins
      let isBad ← StateT.lift (fun tr =>
        let (b, trHalt, mkOk) := T.onSend s₁ P coins tr
        pure (b, if b then trHalt else mkOk out.2))
      if isBad then return none
      else
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
        return some out.2

def deliverRSessionTracked {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
      (StateT (GameState St Msg C) (StateT τ ProbComp)) :=
  fun ⟨P, c⟩ => do
    let s₀ ← get
    let res ← deliverRM (smSchemeTrackState sm) cfg ⟨P, c⟩
    let _ ← StateT.lift (fun tr => pure ((), T.onDeliver s₀ P c res tr))
    return res

def oracleImplRSessionTracked {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (CryptoGames.SM.spec St Msg Coins C)
      (StateT (GameState St Msg C) (StateT τ ProbComp)) :=
  transmitRSessionTracked T sm Δ qep cfg + challRSessionTracked T sm Δ qep cfg +
    deliverRSessionTracked T sm cfg + injectRM (smSchemeTrackState (τ := τ) sm) Δ qep cfg +
    ((fun P => liftStateT (corrR cfg P)) :
      QueryImpl (Party →ₒ Option St)
        (StateT (GameState St Msg C) (StateT τ ProbComp)))

def runRSessionTracked {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (b : Bool) (A : Adversary St Msg Coins C) :
    ProbComp ((Bool × GameState St Msg C) × τ) := do
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT τ ProbComp)) +
    oracleImplRSessionTracked T sm Δ qep cfg
  ((simulateQ impl A).run (initState sm.sendPart k b)).run (T.init k)

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
          match q with
          | .inl (.inl (.inr (.A, c))) =>
            if (bhDecodePreKeyMsgE c).isSome then return ((none, none, none), σH)
            else runTr q σ
          | .inl (.inr (.A, c)) =>
            if (bhDecodePreKeyMsgE c).isSome then return ((none, none, none), σH)
            else runTr q σ
          | .inl (.inl (.inr (.B, c))) =>
            if !im.bobAccepted then
              match bhDecodePreKeyMsgE c with
              | some m =>
                if c == wirePrekey ::
                    (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes then
                  runTr (.inl (.inl (.inr (.B, m.inner)))) σ
                else return ((none, none, none), σH)
              | none => return ((none, none, none), σH)
            else
              match bhDecodePreKeyMsgE c with
              | some m =>
                if bhHdrOfPreKeyMsg m == d.hdr then
                  runTr (.inl (.inl (.inr (.B, m.inner)))) σ
                else return ((none, none, none), σH)
              | none => runTr (.inl (.inl (.inr (.B, c)))) σ
          | .inl (.inr (.B, c)) =>
            if !im.bobAccepted then return ((none, none, none), σH)
            else
              match bhDecodePreKeyMsgE c with
              | some m =>
                if bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
                   decide (m.inner.length + 2048 < 2 ^ 32) then
                  runTr (.inl (.inr (.B, m.inner))) σ
                else return ((none, none, none), σH)
              | none => runTr (.inl (.inr (.B, c))) σ
          | _ => runTr q σ
    | _, _ => return ((none, none, none), σH)

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

/-! ## Key-bit generators, prefix experiments, and `bhPrefixRedWithSessionTracked` -/

abbrev ModelDriverKeyBitGen :=
  SignalPqxdh.KeyIndResponse → SignalPqxdh.KeyIndResponse → ProbComp (SampledSessionKey × Bool)

abbrev BHDrvPrefixKeyBitGen :=
  ℕ → ModelDriverKeyBitGen

def bhFinishStartSpkGen {S : SignalPqxdh.Setup} {ℓ : ℕ} (C : Crypto) (K : MlKem)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (kb : SampledSessionKey × Bool) :
    Option ℕ × BHE2EDrvState S ℓ :=
  match bhE2EGuard σ sid, kr1, kr2 with
  | some (hdr, bnd, (u, j)), .drKeyResp dk, .spkSkResp spkSk =>
    if dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
       dk.pqrKey.length == 32 && spkSk.length == 32 then
      let idA := bhIdKeyOf hdr.ikAPk; let idB := bhIdKeyOf bnd.ikB
      let spkCoins := bhBytesWord spkSk
      let spqr := spqrV1SessionUniformCoins C.F K
      let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr idA idB) ℓ spkCoins
      let gs := some (initState sch.sendPart kb.1 kb.2)
      let inst : BHModelInst S ℓ := { sid, hdr, idA, idB, spkCoins, gs }
      let im : ModelDriverInstanceMeta S :=
        { respPrin := some u, respSpkIdx := some j, instOpkId? := hdr.opkId? }
      (some σ.insts.length,
       { σ with insts := σ.insts ++ [inst], instMeta := σ.instMeta ++ [im] })
    else (none, σ)
  | _, _, _ => (none, σ)

def bhMkPrefixExact (k : ℕ) (b_k : Bool) : BHDrvPrefixKeyBitGen :=
  fun len kr1 _ => do
    let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    let dk := match kr1 with | .drKeyResp dk => dk | _ => default
    let b_use := if len == k then b_k else decide (len < k)
    return (bhKeySOf dk ac, b_use)

def bhMkPrefixLazy (k : ℕ) (b_k : Bool) : BHDrvPrefixKeyBitGen :=
  fun len kr1 kr2 => do
    let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    let b_use := if len == k then b_k else decide (len < k)
    match kr1, kr2 with
    | .drKeyResp dk, .spkSkResp spkSk =>
      if dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
         dk.pqrKey.length == 32 && spkSk.length == 32 && len == k then
        let k_fresh ← ($ᵗ SampledSessionKey : ProbComp SampledSessionKey)
        return (k_fresh, b_k)
      else
        return (bhKeySOf dk ac, b_use)
    | .drKeyResp dk, _ =>
      return (bhKeySOf dk ac, b_use)
    | _, _ =>
      return (bhKeySOf default ac, b_use)

def bhComposedPostObs {S : SignalPqxdh.Setup} {ℓ : ℕ} (P : SignalPqxdh.Primitives) :
    Bool × BHE2EDrvState S ℓ → ProbComp Bool :=
  fun ⟨b', σ⟩ =>
    if !allTestedSessionsFresh P σ.st then do
      let coin ← $ᵗ Bool
      return coin
    else
      return (if bhE2EDrvWon σ true then true else if bhE2EDrvWon σ false then false else b')

def bhE2ELocalStartGenWith {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (mkKeyBit : ModelDriverKeyBitGen)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    ProbComp (Option ℕ × BHE2EDrvState S ℓ) := do
  match bhE2EGuard σ sid with
  | none => return (none, σ)
  | some (_, _, (u, j)) =>
    let (kr1, st1) ← (ki (.testSession sid)).run σ.st
    let (kr2, st2) ← (ki (.revealSpkSk u j)).run st1
    let kb ← mkKeyBit kr1 kr2
    return bhFinishStartSpkGen C K { σ with st := st2 } sid kr1 kr2 kb

def bhMkKeyBitConst (b : Bool) : ModelDriverKeyBitGen := fun kr1 _ => do
  let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
  let dk := match kr1 with | .drKeyResp dk => dk | _ => default
  return (bhKeySOf dk ac, b)

def bhMkPrefixHyb (k : ℕ) : BHDrvPrefixKeyBitGen :=
  fun len kr1 _ => do
    let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    let dk := match kr1 with | .drKeyResp dk => dk | _ => default
    return (bhKeySOf dk ac, decide (len < k))

theorem bhMkPrefixExact_true_eq_bhMkPrefixHyb_succ (k : ℕ) :
    bhMkPrefixExact k true = bhMkPrefixHyb (k + 1) := by
  funext len kr1 kr2
  unfold bhMkPrefixExact bhMkPrefixHyb
  have h : (if len == k then true else decide (len < k)) = decide (len < k + 1) := by
    by_cases h1 : len = k <;> (simp [h1]; try omega)
  rw [h]

theorem bhMkPrefixExact_false_eq_bhMkPrefixHyb (k : ℕ) :
    bhMkPrefixExact k false = bhMkPrefixHyb k := by
  funext len kr1 kr2
  unfold bhMkPrefixExact bhMkPrefixHyb
  have h : (if len == k then false else decide (len < k)) = decide (len < k) := by
    by_cases h1 : len = k <;> simp [h1]
  rw [h]

theorem bhFinishStartSpkGen_bhMkKeyBitConst_eq {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem)
    (b : Bool) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) :
    (bhMkKeyBitConst b kr1 kr2 >>= fun kb => pure (bhFinishStartSpkGen C K σ sid kr1 kr2 kb)) =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ac =>
        pure (bhE2EFinishStartSpk C K (some b) σ sid kr1 kr2 ac)) := by
  unfold bhMkKeyBitConst bhFinishStartSpkGen bhE2EFinishStartSpk
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun ac => ?_
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    cases kr1 <;> cases kr2 <;> rfl

def bhE2ELocalStartGenWithSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (mkKeyBit : ModelDriverKeyBitGen)
    (σH : BHE2EDrvState S ℓ × List τ) (sid : SignalPqxdh.SessionId S) :
    ProbComp (Option ℕ × (BHE2EDrvState S ℓ × List τ)) := do
  match bhE2EGuard σH.1 sid with
  | none => return (none, σH)
  | some (_, _, (u, j)) =>
    let (kr1, st1) ← (ki (.testSession sid)).run σH.1.st
    let (kr2, st2) ← (ki (.revealSpkSk u j)).run st1
    let kb ← mkKeyBit kr1 kr2
    let (idx?, σ') := bhFinishStartSpkGen C K { σH.1 with st := st2 } sid kr1 kr2 kb
    let tracks' := if idx?.isSome then σH.2 ++ [initTrack kb.1] else σH.2
    return (idx?, (σ', tracks'))

def bhE2EDrvImplGenWithSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (mkKeyBit : ModelDriverKeyBitGen) :
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
    let (idx?, σH') ← liftM (bhE2ELocalStartGenWithSessionTracked T.init ki C K mkKeyBit σH sid)
    set σH'
    return idx?
  | .inr (.inr ⟨i, sq⟩) => do
    let σH ← get
    let (sr, σH') ← liftM (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)
    set σH'
    return bhUnpackSmResp sq sr

def bhE2EDrvImplPrefixWithSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (mkP : BHDrvPrefixKeyBitGen) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ × List τ) ProbComp) := fun q =>
  StateT.mk fun σH =>
    (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
      (mkP σH.1.insts.length) q).run σH

theorem bhE2EDrvImplPrefixWithSessionTracked_run_eq_gen {τ : Type} {S : SignalPqxdh.Setup}
    {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (mkP : BHDrvPrefixKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) :
    (bhE2EDrvImplPrefixWithSessionTracked T ki P C K qep decT encT mkP q).run σH =
      (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
        (mkP σH.1.insts.length) q).run σH := rfl

def bhComposedPostObsSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) :
    Bool × (BHE2EDrvState S ℓ × List τ) → ProbComp Bool :=
  fun ⟨b', σH⟩ => bhComposedPostObs P (b', σH.1)

def bhModeExpWithSessionTracked {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (b : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool :=
  (simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
      (bhMkKeyBitConst b)) B).run ({}, []) >>=
    bhComposedPostObsSessionTracked P

/-- The `k`-th session-tracked prefix-creation hybrid experiment over `ki`. -/
def bhPrefixHybExpWithSessionTracked {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool :=
  (simulateQ (bhE2EDrvImplPrefixWithSessionTracked T ki P C K qep decT encT
      (bhMkPrefixHyb k)) B).run ({}, []) >>=
    bhComposedPostObsSessionTracked P

def bhPrefixExactFullExpWithSessionTracked {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool :=
  (simulateQ (bhE2EDrvImplPrefixWithSessionTracked T ki P C K qep decT encT
      (bhMkPrefixExact k b_k)) B).run ({}, []) >>=
    bhComposedPostObsSessionTracked P

def bhPrefixLazyFullExpWithSessionTracked {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool :=
  (simulateQ (bhE2EDrvImplPrefixWithSessionTracked T ki P C K qep decT encT
      (bhMkPrefixLazy k b_k)) B).run ({}, []) >>=
    bhComposedPostObsSessionTracked P

def bhShallowStepPreNonCtlSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvState S ℓ × List τ) (q : BHTargetQuery S ℓ (BitVec 512)) :
    ProbComp (BHTargetResp ℓ × (BHE2EDrvState S ℓ × List τ)) := do
  match q with
  | .inl (.inl kq) =>
    let σ := σH.1
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return (.inl (.inl .noneResp), σH)
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return (.inl (.inl .noneResp), σH)
    else
      let (kr, st') ← (ki kq).run σ.st
      return (.inl (.inl kr), (bhE2EMirror { σ with st := st' } kq kr, σH.2))
  | .inl (.inr _) => return (.inl (.inr none), σH)
  | .inr (i, sq) =>
    let (sr, σH') ← bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq
    return (.inr sr, σH')

/-- Stage-1 `startDR` promotion and slot-`k` pause check, appending `initTrack` even at slot `k` so
`σH.2.length = σH.1.insts.length` remains invariant across Stage 1 and Stage 2. -/
def bhShallowStepPreCtlSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem)
    (k : ℕ) (σH : BHE2EDrvState S ℓ × List τ) (sid : SignalPqxdh.SessionId S) :
    ProbComp ((Option ℕ × (BHE2EDrvState S ℓ × List τ)) ⊕
      (BHPrefixCtx × (Option ℕ × (BHE2EDrvState S ℓ × List τ)))) := do
  let (idx?, (σ', tracks')) ← bhE2ELocalStartSessionTracked initTrack ki C K (some true) σH sid
  if k < σ'.insts.length then
    let ctx : BHPrefixCtx := match σ'.insts[k]? with
      | some d => { idA := d.idA, idB := d.idB, spkCoins := d.spkCoins }
      | none => { idA := bhIdKeyOf [], idB := bhIdKeyOf [], spkCoins := 0 }
    let insts' := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d)
    return .inr (ctx, (idx?, ({ σ' with insts := insts', paused := true }, tracks')))
  else return .inl (idx?, (σ', tracks'))

def bhShallowStepPostLocalSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvState S ℓ × List τ) (q : BHTargetQuery S ℓ (BitVec 512)) :
    ProbComp (BHTargetResp ℓ × (BHE2EDrvState S ℓ × List τ)) := do
  match q with
  | .inl (.inl kq) =>
    let σ := σH.1
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return (.inl (.inl .noneResp), σH)
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return (.inl (.inl .noneResp), σH)
    else
      let (kr, st') ← (ki kq).run σ.st
      return (.inl (.inl kr), (bhE2EMirror { σ with st := st' } kq kr, σH.2))
  | .inl (.inr sid) =>
    let (idx?, σH1) ← bhE2ELocalStartSessionTracked T.init ki C K (some false) σH sid
    return (.inl (.inr idx?), σH1)
  | .inr (i, sq) =>
    let (sr, σH') ← bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq
    return (.inr sr, σH')

def bhPrefixHandlePreWithSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ)
    (drv : BHE2EDrvState S ℓ × List τ) (q : BHTargetQuery S ℓ (BitVec 512)) :
    OracleComp (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      ((BHTargetResp ℓ × (BHE2EDrvState S ℓ × List τ)) ⊕
        (BHPrefixCtx × (Option ℕ × (BHE2EDrvState S ℓ × List τ)))) :=
  match q with
  | .inl (.inl kq) => do
    let res ← bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowStepPreNonCtlSessionTracked T P ki C K qep decT encT drv (.inl (.inl kq)))
    return .inl res
  | .inl (.inr sid) => do
    let res ← bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowStepPreCtlSessionTracked T.init ki C K k drv sid)
    match res with
    | .inl ans => return .inl (.inl (.inr ans.1), ans.2)
    | .inr ctxAndDrv => return .inr ctxAndDrv
  | .inr iSq => do
    let res ← bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowStepPreNonCtlSessionTracked T P ki C K qep decT encT drv (.inr iSq))
    return .inl res

def bhPrefixHandlePostWithSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ)
    (drv : BHE2EDrvState S ℓ × List τ) (q : BHTargetQuery S ℓ (BitVec 512)) :
    OracleComp (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (BHTargetResp ℓ × (BHE2EDrvState S ℓ × List τ)) :=
  match q with
  | .inl kiOrCtl =>
    bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowStepPostLocalSessionTracked T P ki C K qep decT encT drv (.inl kiOrCtl))
  | .inr (i, sq) =>
    match bhShallowCheckExtSm k drv.1 i sq with
    | .inl _ =>
      bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (bhShallowStepPostLocalSessionTracked T P ki C K qep decT encT drv (.inr (i, sq)))
    | .inr sq' => do
      let r ← (liftM
        ((unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).query
          (.inr sq')) :
        OracleComp (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) _)
      let (resp, σ1) := bhShallowCommitExtSm k drv.1 sq' (bhPackSmResp sq' r)
      return (resp, (σ1, drv.2))

/-- Shallow two-stage session-tracked prefix reference reduction over `T` and `ki`. -/
def bhPrefixRedWithSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ) :
    BhShallowTwoStageRed (bhTargetGameSpec S ℓ (BitVec 512))
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (BHTargetQuery S ℓ (BitVec 512)) (BHTargetResp ℓ)
      Unit Unit Bool BHPrefixCtx Bool Bool (BHE2EDrvState S ℓ × List τ) (Option ℕ) where
  qenc := bhTargetQenc
  rdec := bhTargetRdec
  init _ := pure ((), ({}, []))
  handlePre := bhPrefixHandlePreWithSessionTracked T P ki C K qep decT encT k
  chDone _ _ := pure { idA := bhIdKeyOf [], idB := bhIdKeyOf [], spkCoins := 0 }
  resume σH p flip := pure (.inl (.inr p), ({ σH.1 with b := flip }, σH.2))
  handlePost := bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k
  finish σH b' flip :=
    bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowFinishPrefix P σH.1 b' flip)

/-! ## Wire-filtering factorization -/

/-- Factor out the 5-way wire-filtering in `bhE2EStepLocalSmSessionTracked` and `bhShallowCheckExtSm`. -/
def bhFilterSmQuery {S : SignalPqxdh.Setup} {ℓ : ℕ}
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

set_option maxHeartbeats 800000 in
theorem bhE2EStepLocalSmSessionTracked_eq_filter {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvState S ℓ × List τ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i q =
      if !bhE2EDrvInstClean σH.1 i then
        pure ((none, none, none), σH)
      else
        match σH.1.insts[i]?, σH.1.instMeta[i]? with
        | some d, some im =>
          if !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σH.1 d then
            let im' := { im with bobAccepted := true, ikACorrAtAccept := true }
            pure ((none, none, none), ({ σH.1 with instMeta := σH.1.instMeta.set i im' }, σH.2))
          else
            match d.gs, bhFilterSmQuery d im q with
            | some gs, some q' => do
              let spqr := spqrV1SessionUniformCoins C.F K
              let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
              let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
              let tr₀ := (σH.2[i]?).getD (T.init default)
              let ((r, gs'), tr') ←
                ((oracleImplRSessionTracked T sch (2 + 1) qep cfg q').run gs).run tr₀
              let accepted := bhIsBobAcceptSMResp q' r
              let im' := if !im.bobAccepted && accepted then
                  { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σH.1 d }
                else im
              let σ1 := { σH.1 with insts := σH.1.insts.set i { d with gs := some gs' },
                                    instMeta := σH.1.instMeta.set i im' }
              return (bhPackSmResp q' r, (σ1, σH.2.set i tr'))
            | _, _ => pure ((none, none, none), σH)
        | _, _ => pure ((none, none, none), σH) := by
  rcases σH with ⟨σ, tracks⟩
  unfold bhE2EStepLocalSmSessionTracked
  dsimp only
  by_cases hClean : (!bhE2EDrvInstClean σ i) = true
  · simp [hClean]
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte]
    cases σ.insts[i]? with
    | none => rfl
    | some d =>
      cases σ.instMeta[i]? with
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
              | A => dsimp only [bhFilterSmQuery]; split_ifs <;> rfl
              | B =>
                dsimp only [bhFilterSmQuery]
                split_ifs
                · cases bhDecodePreKeyMsgE c with
                  | none => rfl
                  | some m => dsimp only; split_ifs <;> rfl
                · cases bhDecodePreKeyMsgE c with
                  | none => rfl
                  | some m => dsimp only; split_ifs <;> rfl
            · cases p with
              | A => dsimp only [bhFilterSmQuery]; split_ifs <;> rfl
              | B =>
                dsimp only [bhFilterSmQuery]
                split_ifs
                · rfl
                · cases bhDecodePreKeyMsgE c with
                  | none => rfl
                  | some m => dsimp only; split_ifs <;> rfl
            · rfl

end Computational.Proofs.LibsignalCli.MainHaltedPrefixCore
