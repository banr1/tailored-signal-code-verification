/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
public import Computational.Proofs.E2E.SignedAdv
public import Computational.Proofs.E2E.SpkLeakRedModel
public import Computational.Proofs.E2E.SpkHop2Red
public import Computational.Specifications.Session.StatementIdsModel
public import Computational.Specifications.Session.StatementSpkModel
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs
public import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.SpqrV1Sync.SendTotalExtras
import Mathlib.Tactic.Ring

/-!
# `KemFailSessionTrack`-halted SPK reductions and combinators

Defines the shallow `KemFailSessionTrack`-halted session reductions, their prefix-averaged
distinguishers, and the support and state-mapping combinators for halted steps.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.HaltedSpkDefs

open scoped BigOperators ENNReal
open MeasureTheory (Measure lintegral_add_left lintegral_add_right lintegral_const lintegral_mono)
open OracleComp OracleSpec
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack
  KemFailTrackState challRTrackHalted deliverRTrackHalted gameRTrackHalted initKemFailTrack
  libsignalSessionPqrOf oracleImplRTrackHalted runRTrackHalted sampledSessionPqrOf
  stepKemFailDeliver stepKemFailSend transmitRTrackHalted)
open CryptoGames (MACScheme Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSM (LibAdv)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey KeyPair LengthsOk Params PublicKey
  RootKey SessionState ShaCompress Spqr currentVersion)
open CryptoGames.MACScheme (evalQuery prfSpec)
open CryptoGames.Ratchet (expandPRG extractPRF)
open CryptoGames.Ratchet.LibsignalInst (libsignalSessionScheme libsignalSessionSchemeFromEpoch0Keys)
open CryptoGames.Ratchet.LibsignalSim (configEpoch0Distinguisher)
open CryptoGames.SM (Adversary ConfigR GameState RecvResult challR corrR deliverR spec transmitR)
open CryptoVerification.E2E (Bytes Hop2Aux Hop2Comp Hop2Hyb Hop2M KeyU SpkLeakRed
  configRefuseEarlyBobCorr deliverSpk epoch0ChainForgeryTerm hop2CreateCollTerm hop2Deliver
  hop2Inject hop2Lift hop2Unif initAOracle injectSpk liftSpkGameM liftStateT paramsIdsWithSpqr
  partyAddressName serializedPartyAddresses sessionSchemeU spkLeakRedU spkSwapCreationPointHitTerm
  spkSwapHybridCount spkSwapHiddenScalarGuessTerm spkSwapSpuriousStepTerm)
open CryptoVerification.E2E.Signed (prfAvg prgAvg)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser addrBytes serviceIdParse utf8)
open CryptoVerification.SpqrV1Sync.SendTotal (spqrV1Send_msg_len_le)

/-! ## Shallow tracker-halted outer reductions -/

section ShallowHaltedDefs

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}

export Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack)

abbrev pqrOfFixedSpk := sampledSessionPqrOf

abbrev pqrOfSessionU (k : KeyU) : BitVec 256 :=
  k.2.2.2

abbrev pqrOfEpoch0Keys := libsignalSessionPqrOf

/-- Online `KemFailSessionTrack`-halted uniform-start PRG distinguisher on `(rk0, ck0)`. -/
def uniformStartDistinguisherTrackHalted (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes) (qep : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    PRGScheme.PRGAdversary (RootKey × BitVec 256) := fun rc => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((b', s), _) ←
    runRTrackHalted pqrOfEpoch0Keys P.C.F K
      (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) 3 qep cfg b A
  return (b == b' || s.win)

/-- Online `KemFailSessionTrack`-halted `eps0Event` in `libsignalSessionScheme`. -/
def eps0EventTrackHalted (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (encPt : Pt → Bytes) (lam : Pt) (onImage : Bytes → Bool) (qep : ℕ)
    (A : LibAdv Bytes (BitVec 512) ℓ) : ProbComp Bool := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((_, s), _) ←
    runRTrackHalted libsignalSessionPqrOf P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configEpoch0Distinguisher onImage) b A
  return (decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))

/-- Online `KemFailSessionTrack`-halted `epoch0Distinguisher` on `(rk0, ck0)`. -/
def epoch0DistinguisherTrackHalted (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (onImage : Bytes → Bool) (qep : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    PRGScheme.PRGAdversary (RootKey × BitVec 256) := fun rc => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((_, s), _) ←
    runRTrackHalted pqrOfEpoch0Keys P.C.F K
      (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) 3 qep
      (configEpoch0Distinguisher onImage) b A
  return (decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))

abbrev SpkTrackHaltedM (F : ShaCompress) (Pt : Type) (ℓ : ℕ) : Type → Type :=
  StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (StateT (KemFailSessionTrack F Bytes) (OracleComp (unifSpec + prfSpec Pt (BitVec 256))))

def liftSpkGameTrackHaltedM {F : ShaCompress} {α : Type}
    (m : StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (StateT (KemFailSessionTrack F Bytes) ProbComp) α) :
    SpkTrackHaltedM F Pt ℓ α :=
  StateT.mk fun s => StateT.mk fun tr =>
    (liftM ((m.run s).run tr) :
      OracleComp (unifSpec + prfSpec Pt (BitVec 256))
        ((α × GameState (GhostState Bytes) (Plain ℓ) Bytes) × KemFailSessionTrack F Bytes))

def liftSpkNoTrackM {F : ShaCompress} {α : Type}
    (m : StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (OracleComp (unifSpec + prfSpec Pt (BitVec 256))) α) :
    SpkTrackHaltedM F Pt ℓ α :=
  StateT.mk fun s => StateT.lift (m.run s)

/-- Pure `KemFailSessionTrack` post-update after a `deliver` query `x = (Q, w)` returning `res`,
using `tr.2.reverse.findIdx?` computed before `deliver`. -/
def updateKemFailOnDeliver {Msg C : Type} [DecidableEq C]
    (F : ShaCompress) (K : MlKem) (tr : KemFailSessionTrack F C) (x : Party × C)
    (res : Option (RecvResult Msg)) : KemFailSessionTrack F C :=
  match res, tr.2.reverse.findIdx? (fun wp => wp.1 == x.2 && wp.2 == x.1.other) with
  | some (.accepted _ _ _), some j => (stepKemFailDeliver F K tr.1 x.1 j, tr.2)
  | _, _ => tr

def deliverSpkTrackHalted (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (x : Party × Bytes) :
    SpkTrackHaltedM P.C.F Pt ℓ (Option (RecvResult (Plain ℓ))) := do
  let (_, honestWires) ← StateT.lift get
  let j? := honestWires.reverse.findIdx? (fun wp => wp.1 == x.2 && wp.2 == x.1.other)
  let res ← liftSpkNoTrackM (deliverSpk P ℓ Dh encT decT s x)
  match res, j? with
  | some (.accepted _ _ _), some j =>
    StateT.lift (modify fun (tr, hw) => (stepKemFailDeliver P.C.F K tr x.1 j, hw))
  | _, _ => pure ()
  return res

def spkOracleImplTrackHalted (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) :
    QueryImpl (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (SpkTrackHaltedM P.C.F Pt ℓ)
  | .inl u =>
    StateT.lift (StateT.lift (OracleSpec.query (spec := unifSpec + prfSpec Pt (BitVec 256)) (.inl u)))
  | .inr (.inl (.inl (.inl (.inl x)))) =>
    liftSpkGameTrackHaltedM
      (transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x)
  | .inr (.inl (.inl (.inl (.inr x)))) =>
    liftSpkGameTrackHaltedM
      (challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x)
  | .inr (.inl (.inl (.inr x))) =>
    deliverSpkTrackHalted P K ℓ Dh encT decT s x
  | .inr (.inl (.inr x)) =>
    liftSpkNoTrackM (injectSpk P ℓ Dh encT decT qep s x)
  | .inr (.inr x) =>
    liftSpkNoTrackM (liftSpkGameM (corrR (configRefuseEarlyBobCorr decT encT) x))

/-- `KemFailSessionTrack`-halted PRF reduction for Hops 1 and 3. -/
def spkLeakRedTrackHalted (K : MlKem) : SpkLeakRed Pt ℓ (BitVec 512) :=
  fun P Dh _encPt encT decT qep s A =>
    show OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool from do
    let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
      OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool)
    let ck0 ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
      OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256))
    let rest ← (liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
      OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256))
    let stA ← initAOracle (Pt := Pt) P Dh ck0 s rest.1 rest.2
    let stB := P.initB ⟨0, ck0, s, rest.1, rest.2⟩
    let initSt : GameState (GhostState Bytes) (Plain ℓ) Bytes :=
      { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
    let tr₀ : KemFailSessionTrack P.C.F Bytes := (initKemFailTrack P.C.F rest.2, [])
    let ((b', finalSt), _finalTr) ←
      ((simulateQ (spkOracleImplTrackHalted P K ℓ Dh encT decT qep s) A).run initSt).run tr₀
    return (b == b' || finalSt.win)

abbrev spkLeakRedHalted (K : MlKem) : SpkLeakRed Pt ℓ (BitVec 512) :=
  spkLeakRedTrackHalted K

abbrev Hop2TrackHaltedM (F : ShaCompress) (Pt : Type) (ℓ : ℕ) : Type → Type :=
  StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)
    (StateT (KemFailSessionTrack F Bytes) (Hop2Comp Pt))

def hop2LiftTrackHalted {F : ShaCompress} {α : Type}
    (m : StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (StateT (KemFailSessionTrack F Bytes) ProbComp) α) :
    Hop2TrackHaltedM F Pt ℓ α :=
  StateT.mk fun st => StateT.mk fun tr => do
    let ((a, gs'), tr') ← (liftM ((m.run st.1).run tr) :
      Hop2Comp Pt ((α × GameState (GhostState Bytes) (Plain ℓ) Bytes) × KemFailSessionTrack F Bytes))
    return ((a, (gs', st.2)), tr')

def liftHop2NoTrackM {F : ShaCompress} {α : Type} (m : Hop2M Pt ℓ α) :
    Hop2TrackHaltedM F Pt ℓ α :=
  StateT.mk fun st => StateT.lift (m.run st)

def hop2DeliverTrackHalted (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (h : Hop2Hyb Pt) (x : Party × Bytes) :
    Hop2TrackHaltedM P.C.F Pt ℓ (Option (RecvResult (Plain ℓ))) := do
  let (_, honestWires) ← StateT.lift get
  let j? := honestWires.reverse.findIdx? (fun wp => wp.1 == x.2 && wp.2 == x.1.other)
  let res ← liftHop2NoTrackM (hop2Deliver P Dh encT decT s h x)
  match res, j? with
  | some (.accepted _ _ _), some j =>
    StateT.lift (modify fun (tr, hw) => (stepKemFailDeliver P.C.F K tr x.1 j, hw))
  | _, _ => pure ()
  return res

def hop2ImplTrackHalted (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (h : Hop2Hyb Pt) :
    QueryImpl (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (Hop2TrackHaltedM P.C.F Pt ℓ)
  | .inl u =>
    StateT.lift (StateT.lift (OracleSpec.query (spec := unifSpec + prfSpec Pt (BitVec 256)) (.inl u)))
  | .inr (.inl (.inl (.inl (.inl y)))) =>
    hop2LiftTrackHalted
      (transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) y)
  | .inr (.inl (.inl (.inl (.inr y)))) =>
    hop2LiftTrackHalted
      (challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) y)
  | .inr (.inl (.inl (.inr y))) => hop2DeliverTrackHalted P K Dh encT decT s h y
  | .inr (.inl (.inr y)) => liftHop2NoTrackM (hop2Inject P Dh encT decT qep s h y)
  | .inr (.inr y) => liftHop2NoTrackM (hop2Lift (corrR (configRefuseEarlyBobCorr decT encT) y))

/-- `KemFailSessionTrack`-halted hybrid game `G(k)` for Hop 2. -/
def hop2GameTrackHalted (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (h : Hop2Hyb Pt)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) : Hop2Comp Pt Bool := do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : Hop2Comp Pt Bool)
  let ck0 ← hop2Unif (Pt := Pt)
  let x ← hop2Unif (Pt := Pt)
  let alice ← hop2Unif (Pt := Pt)
  let pqr ← hop2Unif (Pt := Pt)
  let u1 ← hop2Unif (Pt := Pt)
  let ck1 := if h.k = 0 then h.chall.2 else u1
  let I0 := Dh.dh x (Dh.dh alice Dh.base)
  let spk := (KeyPair.generate P.C x).publicKey
  let sessA := ((SessionState.new currentVersion P.idA P.idB 0
    (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
    (KeyPair.generate P.C alice) ⟨ck1, 0⟩
  let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
  let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
  let initSt : GameState (GhostState Bytes) (Plain ℓ) Bytes :=
    { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
  let aux0 : Hop2Aux Pt :=
    { made := [((0, I0), ck1)]
      idx := fun Q => match Q with | .A => some 1 | .B => some 0
      coins := fun Q => match Q with | .A => alice | .B => x }
  let tr₀ : KemFailSessionTrack P.C.F Bytes := (initKemFailTrack P.C.F pqr, [])
  let ((_, fin), _finalTr) ←
    ((simulateQ (hop2ImplTrackHalted P K Dh encT decT qep s h) A).run (initSt, aux0)).run tr₀
  return fin.2.bad

/-- `KemFailSessionTrack`-halted Hop-2 PRG reduction at hybrid index `k`. -/
def hop2PrgRedKTrackHalted (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    PRGScheme.PRGAdversary (RootKey × BitVec 256) := fun rc =>
  let step : Pt → Hop2Comp Pt (BitVec 256) := fun I =>
    (pure ((extractPRF P.C.F encPt).tag rc.1 I) : Hop2Comp Pt (BitVec 256))
  let prfReal : QueryImpl (prfSpec Pt (BitVec 256)) ProbComp := fun I =>
    (pure ((extractPRF P.C.F encPt).tag rc.1 I) : ProbComp (BitVec 256))
  let impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp :=
    QueryImpl.ofLift unifSpec ProbComp + prfReal
  simulateQ impl (hop2GameTrackHalted P K ℓ Dh encT decT qep s ⟨k, rc, step⟩ A)

/-- `KemFailSessionTrack`-halted Hop-2 PRF reduction at hybrid index `k`. -/
def hop2PrfRedKTrackHalted (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    MACScheme.PRFAdversary Pt (BitVec 256) := (do
  let r ← hop2Unif (Pt := Pt)
  let c ← hop2Unif (Pt := Pt)
  hop2GameTrackHalted P K ℓ Dh encT decT qep s
    ⟨k, (r, c), fun I => evalQuery (Input := Pt) (Tag := BitVec 256) I⟩ A :
    Hop2Comp Pt Bool)

abbrev hop2GameHalted := @hop2GameTrackHalted

abbrev hop2PrgRedKHalted := @hop2PrgRedKTrackHalted

abbrev hop2PrfRedKHalted := @hop2PrfRedKTrackHalted

end ShallowHaltedDefs

/-! ## Prefix-averaged tracker-halted reductions -/

section MixtureDefs

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}

def leakAvgTrackHaltedWithSpqr {α : Type} (C : Crypto) (K : MlKem)
    (spqr : Spqr Bytes (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    MACScheme.PRFAdversary Pt (BitVec 256) :=
  prfAvg oa fun o =>
    spkLeakRedTrackHalted K (paramsIdsWithSpqr C spqr (ida o) (idb o))
      Dh encPt encT decT qep (s o) (A o)

def leakUAvgTrackHaltedWithSpqr {α : Type} (C : Crypto) (K : MlKem)
    (spqr : Spqr Bytes (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    MACScheme.PRFAdversary Pt (BitVec 256) :=
  prfAvg oa fun o =>
    spkLeakRedU (spkLeakRedTrackHalted K)
      (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep (A o)

def hop2PrgAvgTrackHaltedWithSpqr {α : Type} (C : Crypto) (K : MlKem)
    (spqr : Spqr Bytes (BitVec 512)) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256) (k : ℕ)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    PRGScheme.PRGAdversary (RootKey × BitVec 256) :=
  prgAvg oa fun o =>
    hop2PrgRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
      ℓ Dh encPt encT decT qep (s o) k (A o)

def hop2PrfAvgTrackHaltedWithSpqr {α : Type} (C : Crypto) (K : MlKem)
    (spqr : Spqr Bytes (BitVec 512)) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (s : α → BitVec 256) (k : ℕ)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    MACScheme.PRFAdversary Pt (BitVec 256) :=
  prfAvg oa fun o =>
    hop2PrfRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
      ℓ Dh encT decT qep (s o) k (A o)

/-- Tracker-halted counterpart of `Signed.hop2TermAvgWithSpqr`. -/
noncomputable def hop2TermAvgTrackHaltedWithSpqr {α : Type} (C : Crypto) (K : MlKem)
    (spqr : Spqr Bytes (BitVec 512)) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  epoch0ChainForgeryTerm C.F q
    + (∑ k ∈ Finset.range spkSwapHybridCount,
        ((expandPRG C.F).prgAdvantage
            (hop2PrgAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep oa ida idb s k A)
          + (extractPRF C.F encPt).prfAdvantage
            (hop2PrfAvgTrackHaltedWithSpqr C K spqr ℓ Dh encT decT qep oa ida idb s k A)))
    + hop2CreateCollTerm Dh q
    + spkSwapSpuriousStepTerm C.F q
    + spkSwapCreationPointHitTerm Dh q
    + spkSwapHiddenScalarGuessTerm Dh q

noncomputable abbrev hop2TermAvgHaltedWithSpqr := @hop2TermAvgTrackHaltedWithSpqr

end MixtureDefs

/-! ## Halted step combinators and mixture integration -/

section Combinators

private theorem addrsE_length (uuidParse : UuidParser) (s r : Party) (a : List (BitVec 8))
    (h : serializedPartyAddresses uuidParse s r = some a) : a.length = 36 := by
  unfold serializedPartyAddresses at h
  cases hs : serviceIdParse uuidParse (utf8 (partyAddressName s)) <;>
    cases hr : serviceIdParse uuidParse (utf8 (partyAddressName r)) <;> simp_all [addrBytes]
  subst h
  simp

theorem lengthsOk_paramsIdsWithSpqr {PQC : Type} (C : Crypto) (spqr : Spqr Bytes PQC)
    (idA idB : IdentityKey) (ℓ : ℕ) (hℓ : ℓ < 2 ^ 31)
    (hLspqr : ∀ st rq st' salt msg, spqr.send st rq = some (st', salt, msg) →
      msg.length < 2 ^ 29) :
    LengthsOk (paramsIdsWithSpqr C spqr idA idB) ℓ := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro st rq st' salt msg h
    exact hLspqr st rq st' salt msg h
  · intro a h
    rw [addrsE_length _ _ _ a h]; decide
  · intro a h
    rw [addrsE_length _ _ _ a h]; decide

theorem lengthsOk_paramsIdsWithSpqr_spqrV1 (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (ℓ : ℕ) (hℓ : ℓ < 2 ^ 31) :
    LengthsOk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ :=
  lengthsOk_paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB ℓ hℓ
    (fun st r st' salt pm h =>
      Nat.lt_of_le_of_lt (spqrV1Send_msg_len_le C.F K st r st' salt pm h) (by decide))

@[local simp] private theorem stateT_lift_get_run2 {m : Type → Type} [Monad m] [LawfulMonad m]
    {S₁ S₂ : Type} (s₁ : S₁) (s₂ : S₂) :
    (((StateT.lift get : StateT S₁ (StateT S₂ m) S₂).run s₁).run s₂) = pure ((s₂, s₁), s₂) := by
  simp [StateT.run_lift]

@[local simp] private theorem stateT_lift_liftM_run2 {m : Type → Type} [Monad m] [LawfulMonad m]
    {S₁ S₂ α : Type} (c : m α) (s₁ : S₁) (s₂ : S₂) :
    (((StateT.lift (liftM c : StateT S₂ m α) : StateT S₁ (StateT S₂ m) α).run s₁).run s₂) =
      (fun a => ((a, s₁), s₂)) <$> c := by
  simp [StateT.run_lift, StateT.run_monadLift, map_eq_bind_pure_comp]

@[local simp] private theorem liftStateT_run2_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    {S₁ S₂ α : Type} (c : StateT S₁ m α) (s₁ : S₁) (s₂ : S₂) :
    (((liftStateT c : StateT S₁ (StateT S₂ m) α).run s₁).run s₂) =
      (fun rs => (rs, s₂)) <$> c.run s₁ := by
  unfold liftStateT
  change (liftM (c.run s₁) : StateT S₂ m (α × S₁)).run s₂ = _
  simp [StateT.run_monadLift, map_eq_bind_pure_comp]

theorem deliverRTrackHalted_run {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (cfg : ConfigR St Msg C) (x : Party × C)
    (st : GameState St Msg C) (tr : KemFailSessionTrack F C) :
    (((deliverRTrackHalted F K sm cfg x).run st).run tr) =
      (fun rs => (rs, updateKemFailOnDeliver F K tr x rs.1)) <$> (deliverR sm cfg x).run st := by
  rcases x with ⟨Q, w⟩
  rcases tr with ⟨tk, hw⟩
  unfold deliverRTrackHalted updateKemFailOnDeliver
  simp only [StateT.run_bind, stateT_lift_get_run2, liftStateT_run2_eq,
    bind_pure_comp, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  refine bind_congr fun ⟨res, st'⟩ => ?_
  cases res with
  | none => simp
  | some r =>
    cases r <;> cases hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) <;> simp

@[local simp] private theorem bytes_beq_eq_instDecidableEq (a b : Bytes) :
    (a == b) = @BEq.beq Bytes instBEqOfDecidableEq a b := by
  simp

theorem deliverSpkTrackHalted_run {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (x : Party × Bytes)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailSessionTrack P.C.F Bytes) :
    (((deliverSpkTrackHalted P K ℓ Dh encT decT s x).run st).run tr) =
      (fun rs => (rs, updateKemFailOnDeliver P.C.F K tr x rs.1)) <$>
        (deliverSpk P ℓ Dh encT decT s x).run st := by
  rcases x with ⟨Q, w⟩
  rcases tr with ⟨tk, hw⟩
  unfold deliverSpkTrackHalted liftSpkNoTrackM updateKemFailOnDeliver
  simp only [StateT.run_bind, StateT.run_mk, StateT.run_lift, StateT.run_get,
    bind_pure_comp, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
    bytes_beq_eq_instDecidableEq]
  refine bind_congr fun (res : Option (RecvResult (Plain ℓ)) × _) => ?_
  rcases res with ⟨res, st'⟩
  cases res with
  | none => simp
  | some r =>
    cases r with
    | accepted _ _ _ =>
      cases hfind : hw.reverse.findIdx?
        (fun wp => @BEq.beq Bytes instBEqOfDecidableEq wp.1 w && wp.2 == Q.other) <;>
        simp
    | _ => simp

theorem hop2DeliverTrackHalted_run {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (h : Hop2Hyb Pt) (x : Party × Bytes)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)
    (tr : KemFailSessionTrack P.C.F Bytes) :
    (((hop2DeliverTrackHalted P K Dh encT decT s h x).run st).run tr) =
      (fun rs => (rs, updateKemFailOnDeliver P.C.F K tr x rs.1)) <$>
        (hop2Deliver P Dh encT decT s h x).run st := by
  rcases x with ⟨Q, w⟩
  rcases tr with ⟨tk, hw⟩
  unfold hop2DeliverTrackHalted liftHop2NoTrackM updateKemFailOnDeliver
  simp only [StateT.run_bind, StateT.run_mk, StateT.run_lift, StateT.run_get,
    bind_pure_comp, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
    bytes_beq_eq_instDecidableEq]
  refine bind_congr fun (res : Option (RecvResult (Plain ℓ)) × _) => ?_
  rcases res with ⟨res, st'⟩
  cases res with
  | none => simp
  | some r =>
    cases r with
    | accepted _ _ _ =>
      cases hfind : hw.reverse.findIdx?
        (fun wp => @BEq.beq Bytes instBEqOfDecidableEq wp.1 w && wp.2 == Q.other) <;>
        simp
    | _ => simp

/-- Every outcome of `transmitRTrackHalted` either halts returning `(none, s)` or lies in the
support of `transmitR`. -/
theorem transmitRTrackHalted_support {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (x : Party × Msg × Option (BitVec 512))
    (s : GameState St Msg C) (tr : KemFailSessionTrack F C)
    {z : (Option C × GameState St Msg C) × KemFailSessionTrack F C}
    (hz : z ∈ support (((transmitRTrackHalted F K sm Δ qep cfg x).run s).run tr)) :
    z.1 = (none, s) ∨ z.1 ∈ support ((transmitR sm Δ qep cfg x).run s) := by
  rcases x with ⟨P, m, r⟩
  rcases tr with ⟨tk, hw⟩
  unfold transmitRTrackHalted at hz
  unfold transmitR
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz ⊢
  cases hok : cfg.sendOK s P
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; left; rfl
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.transmitImpl,
      StateT.run_bind, StateT.run_get, pure_bind] at hz ⊢
    cases hwin : s.win
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_monadLift, monadLift_self, StateT.run_lift,
        bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz ⊢
      rcases hz with ⟨⟨coins, bad⟩, hsam, hz⟩
      cases hep : s.epMgmt Δ qep P bad with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; left; rfl
      | some s₁ =>
        cases hcand : (stepKemFailSend F K tk P coins).cand.isSome
        · simp [hep, hcand] at hz
          subst hz
          right
          refine ⟨(coins, bad), hsam, ?_⟩
          simp only [hep, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff]
          rfl
        · simp [hep, hcand] at hz
          subst hz; left; rfl
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; left; rfl

/-- Every outcome of `challRTrackHalted` either halts returning `(none, s)` or lies in the
support of `challR`. -/
theorem challRTrackHalted_support {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (x : Party × Msg × Msg × Option (BitVec 512))
    (s : GameState St Msg C) (tr : KemFailSessionTrack F C)
    {z : (Option C × GameState St Msg C) × KemFailSessionTrack F C}
    (hz : z ∈ support (((challRTrackHalted F K sm Δ qep cfg x).run s).run tr)) :
    z.1 = (none, s) ∨ z.1 ∈ support ((challR sm Δ qep cfg x).run s) := by
  rcases x with ⟨P, m₀, m₁, r⟩
  rcases tr with ⟨tk, hw⟩
  unfold challRTrackHalted at hz
  unfold challR
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz ⊢
  cases hok : cfg.sendOK s P
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; left; rfl
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.challImpl,
      StateT.run_bind, StateT.run_get, pure_bind] at hz ⊢
    cases hwin : s.win
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_monadLift, monadLift_self, StateT.run_lift,
        bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz ⊢
      rcases hz with ⟨⟨coins, bad⟩, hsam, hz⟩
      cases hep : s.epMgmt Δ qep P bad with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; left; rfl
      | some s₁ =>
        cases hsafe : (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
        · cases hcand : (stepKemFailSend F K tk P coins).cand.isSome
          · simp [hep, hsafe, hcand] at hz
            subst hz
            right
            refine ⟨(coins, bad), hsam, ?_⟩
            simp only [hep, hsafe, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
              StateT.run_set, pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff]
            rfl
          · simp [hep, hsafe, hcand] at hz
            subst hz; left; rfl
        · simp only [hep, hsafe, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz; left; rfl
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; left; rfl

theorem transmitRTrackHalted_mapSt_eq {Key₁ Key₂ St Msg RCoins₁ RCoins₂ C : Type}
    (F : ShaCompress) (K : MlKem)
    (sm₁ : SMSchemeR Key₁ St Msg (BitVec 512) RCoins₁ C)
    (sm₂ : SMSchemeR Key₂ St Msg (BitVec 512) RCoins₂ C)
    (Δ qep : ℕ) (cfg₁ cfg₂ : ConfigR St Msg C)
    (f : GameState St Msg C → GameState St Msg C)
    (x : Party × Msg × Option (BitVec 512))
    (s : GameState St Msg C) (tr : KemFailSessionTrack F C)
    (hsendOK : cfg₂.sendOK (f s) x.1 = cfg₁.sendOK s x.1)
    (hwin : (f s).win = s.win)
    (hep : ∀ bad, (f s).epMgmt Δ qep x.1 bad = Option.map f (s.epMgmt Δ qep x.1 bad))
    (hsend : cfg₁.sendOK s x.1 = true → ∀ bad s₁ coins, s.epMgmt Δ qep x.1 bad = some s₁ →
      let o₁ := sm₁.send (s₁.st x.1) x.2.1 coins
      let o₂ := sm₂.send ((f s₁).st x.1) x.2.1 coins
      o₂.2 = o₁.2 ∧
        (f s₁).record Δ x.1 o₂.1 ⟨⟨x.1, (f s₁).epoch x.1, (f s₁).idx x.1 + 1⟩, x.2.1, o₂.2⟩ false =
          f (s₁.record Δ x.1 o₁.1 ⟨⟨x.1, s₁.epoch x.1, s₁.idx x.1 + 1⟩, x.2.1, o₁.2⟩ false)) :
    (((transmitRTrackHalted F K sm₂ Δ qep cfg₂ x).run (f s)).run tr) =
      Prod.map (Prod.map id f) id <$>
        (((transmitRTrackHalted F K sm₁ Δ qep cfg₁ x).run s).run tr) := by
  rcases x with ⟨P, m, r⟩
  rcases tr with ⟨tk, hw⟩
  dsimp only at hsendOK hep hsend
  unfold transmitRTrackHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK, hwin]
  cases hok : cfg₁.sendOK s P
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hw_flag : s.win
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_liftM_run2,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine bind_congr fun ⟨coins, bad⟩ => ?_
      rw [hep bad]
      cases hs₁ : s.epMgmt Δ qep P bad with
      | none => simp
      | some s₁ =>
        simp only [Option.map_some]
        cases hcand : (stepKemFailSend F K tk P coins).cand.isSome
        · obtain ⟨hout, hrec⟩ := hsend hok bad s₁ coins hs₁
          simp only [hcand, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
            StateT.run_get, StateT.run_set, StateT.run_pure,
            Function.comp_apply, pure_bind, Prod.map_apply, id_eq]
          rw [hrec, hout]
        · simp [hcand]
    · simp

theorem challRTrackHalted_mapSt_eq {Key₁ Key₂ St Msg RCoins₁ RCoins₂ C : Type}
    (F : ShaCompress) (K : MlKem)
    (sm₁ : SMSchemeR Key₁ St Msg (BitVec 512) RCoins₁ C)
    (sm₂ : SMSchemeR Key₂ St Msg (BitVec 512) RCoins₂ C)
    (Δ qep : ℕ) (cfg₁ cfg₂ : ConfigR St Msg C)
    (f : GameState St Msg C → GameState St Msg C)
    (x : Party × Msg × Msg × Option (BitVec 512))
    (s : GameState St Msg C) (tr : KemFailSessionTrack F C)
    (hsendOK : cfg₂.sendOK (f s) x.1 = cfg₁.sendOK s x.1)
    (hwin : (f s).win = s.win)
    (hb : (f s).b = s.b)
    (hep : ∀ bad, (f s).epMgmt Δ qep x.1 bad = Option.map f (s.epMgmt Δ qep x.1 bad))
    (hsafe : cfg₁.sendOK s x.1 = true → ∀ bad s₁, s.epMgmt Δ qep x.1 bad = some s₁ →
      (f s₁).safeCh Δ x.1 = s₁.safeCh Δ x.1 ∧
        cfg₂.base.challAllowedIn ((f s₁).epoch x.1) = cfg₁.base.challAllowedIn (s₁.epoch x.1) ∧
        cfg₂.base.challMsg ((f s₁).epoch x.1) = cfg₁.base.challMsg (s₁.epoch x.1))
    (hsend : cfg₁.sendOK s x.1 = true → ∀ bad s₁ m coins, s.epMgmt Δ qep x.1 bad = some s₁ →
      let o₁ := sm₁.send (s₁.st x.1) m coins
      let o₂ := sm₂.send ((f s₁).st x.1) m coins
      o₂.2 = o₁.2 ∧
        (f s₁).record Δ x.1 o₂.1 ⟨⟨x.1, (f s₁).epoch x.1, (f s₁).idx x.1 + 1⟩, m, o₂.2⟩ true =
          f (s₁.record Δ x.1 o₁.1 ⟨⟨x.1, s₁.epoch x.1, s₁.idx x.1 + 1⟩, m, o₁.2⟩ true)) :
    (((challRTrackHalted F K sm₂ Δ qep cfg₂ x).run (f s)).run tr) =
      Prod.map (Prod.map id f) id <$>
        (((challRTrackHalted F K sm₁ Δ qep cfg₁ x).run s).run tr) := by
  rcases x with ⟨P, m₀, m₁, r⟩
  rcases tr with ⟨tk, hw⟩
  dsimp only at hsendOK hep hsafe hsend
  unfold challRTrackHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK, hwin]
  cases hok : cfg₁.sendOK s P
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hw_flag : s.win
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_liftM_run2,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine bind_congr fun ⟨coins, bad⟩ => ?_
      rw [hep bad]
      cases hs₁ : s.epMgmt Δ qep P bad with
      | none => simp
      | some s₁ =>
        simp only [Option.map_some]
        obtain ⟨hsf, hall, hmsg⟩ := hsafe hok bad s₁ hs₁
        rw [hsf, hall, hmsg, hb]
        cases hch : (!(s₁.safeCh Δ P) || !(cfg₁.base.challAllowedIn (s₁.epoch P)))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hcand : (stepKemFailSend F K tk P coins).cand.isSome
          · obtain ⟨hout, hrec⟩ := hsend hok bad s₁
              ((cfg₁.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)) coins hs₁
            simp only [hcand, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
              StateT.run_get, StateT.run_set, StateT.run_pure,
              Function.comp_apply, pure_bind, Prod.map_apply, id_eq]
            rw [hrec, hout]
          · simp [hcand]
        · simp
    · simp

theorem simulateQ_run2_stateT {ι₁ ι₂ : Type} {spec₁ : OracleSpec.{0, 0} ι₁}
    {spec₂ : OracleSpec.{0, 0} ι₂} {S₁ S₂ α : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl₂ : QueryImpl spec₂ m)
    (impl₁ : QueryImpl spec₁ (StateT S₁ (StateT S₂ (OracleComp spec₂))))
    (oa : OracleComp spec₁ α) (s₁ : S₁) (s₂ : S₂) :
    simulateQ impl₂ (((simulateQ impl₁ oa).run s₁).run s₂) =
      (((simulateQ (fun q => StateT.mk fun s₁' => StateT.mk fun s₂' =>
          simulateQ impl₂ (((impl₁ q).run s₁').run s₂')) oa).run s₁).run s₂) := by
  induction oa using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    congr 1; funext z
    exact ih z.1.1 z.1.2 z.2

theorem simulateQ_mapSt2_run_eq {ι : Type} {ospec : OracleSpec.{0, 0} ι} {S₁ S₂ S₃ α : Type}
    (impl₁ : QueryImpl ospec (StateT S₁ (StateT S₃ ProbComp)))
    (impl₂ : QueryImpl ospec (StateT S₂ (StateT S₃ ProbComp)))
    (f : S₁ → S₂) (inv : S₁ → Prop)
    (heq : ∀ t s tr, inv s →
      (((impl₂ t).run (f s)).run tr) = Prod.map (Prod.map id f) id <$> (((impl₁ t).run s).run tr))
    (hpres : ∀ t s tr, inv s → ∀ z ∈ support (((impl₁ t).run s).run tr), inv z.1.2)
    (oa : OracleComp ospec α) (s : S₁) (tr : S₃) (hs : inv s) :
    (((simulateQ impl₂ oa).run (f s)).run tr) =
      Prod.map (Prod.map id f) id <$> (((simulateQ impl₁ oa).run s).run tr) := by
  induction oa using OracleComp.inductionOn generalizing s tr with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      StateT.run_bind, heq q s tr hs, map_eq_bind_pure_comp, bind_assoc,
      Function.comp_apply, pure_bind]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun z hz => ?_
    have hih := ih z.1.1 z.1.2 z.2 (hpres q s tr hs z hz)
    rcases z with ⟨⟨a, s'⟩, tr'⟩
    simpa only [Prod.map_apply, id_eq, map_eq_bind_pure_comp] using hih

theorem evalDist_bind_apply_lintegral {α : Type} (oa : ProbComp α) (f : α → ProbComp Bool)
    (v : Bool) :
    letI : MeasurableSpace α := ⊤
    𝒟[oa >>= f] {v} = ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa] := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]

theorem evalDist_bind_apply_le_add {α : Type} (oa : ProbComp α)
    (f g h : α → ProbComp Bool) (c : ℝ≥0∞) (v w : Bool)
    (H : ∀ a, 𝒟[f a] {v} ≤ 𝒟[g a] {v} + (c + 𝒟[h a] {w})) :
    𝒟[oa >>= f] {v} ≤ 𝒟[oa >>= g] {v} + (c + 𝒟[oa >>= h] {w}) := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral,
    evalDist_bind_apply_lintegral]
  calc ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa]
      ≤ ∫⁻ a, (𝒟[g a] {v} + (c + 𝒟[h a] {w})) ∂𝒟[oa] := lintegral_mono H
    _ = ∫⁻ a, 𝒟[g a] {v} ∂𝒟[oa] + (c + ∫⁻ a, 𝒟[h a] {w} ∂𝒟[oa]) := by
      rw [lintegral_add_left Measurable.of_discrete, lintegral_add_left measurable_const,
        lintegral_const, evalDist_apply_univ_eq_one, mul_one]

theorem evalDist_bind_apply_le_add_const {α : Type} (oa : ProbComp α)
    (f g : α → ProbComp Bool) (c : ℝ≥0∞) (v : Bool)
    (H : ∀ a, 𝒟[f a] {v} ≤ 𝒟[g a] {v} + c) :
    𝒟[oa >>= f] {v} ≤ 𝒟[oa >>= g] {v} + c := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral]
  calc ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa]
      ≤ ∫⁻ a, (𝒟[g a] {v} + c) ∂𝒟[oa] := lintegral_mono H
    _ = ∫⁻ a, 𝒟[g a] {v} ∂𝒟[oa] + c := by
      rw [lintegral_add_right _ measurable_const, lintegral_const, evalDist_apply_univ_eq_one,
        mul_one]

theorem evalDist_bind_apply_le_const {α : Type} (oa : ProbComp α)
    (f : α → ProbComp Bool) (c : ℝ≥0∞) (v : Bool) (H : ∀ a, 𝒟[f a] {v} ≤ c) :
    𝒟[oa >>= f] {v} ≤ c := by
  let _ : MeasurableSpace α := ⊤
  rw [evalDist_bind_apply_lintegral]
  calc ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa] ≤ ∫⁻ _a, c ∂𝒟[oa] := lintegral_mono H
    _ = c := by rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

theorem hybrid_chain_le (R T a : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (n : ℕ)
    (h1 : ∀ k, R k ≤ a k + T k) (h2 : ∀ k < n, T k ≤ R (k + 1) + ε) :
    R 0 ≤ (∑ k ∈ Finset.range (n + 1), a k) + (n : ℝ≥0∞) * ε + T n := by
  have hm : ∀ m ≤ n, R 0 ≤ (∑ k ∈ Finset.range m, a k) + (m : ℝ≥0∞) * ε + R m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hmn
      calc R 0 ≤ (∑ k ∈ Finset.range m, a k) + (m : ℝ≥0∞) * ε + R m := ih (by omega)
        _ ≤ (∑ k ∈ Finset.range m, a k) + (m : ℝ≥0∞) * ε + (a m + (R (m + 1) + ε)) := by
          gcongr
          exact (h1 m).trans (add_le_add le_rfl (h2 m (by omega)))
        _ = (∑ k ∈ Finset.range (m + 1), a k) + ((m + 1 : ℕ) : ℝ≥0∞) * ε + R (m + 1) := by
          rw [Finset.sum_range_succ]; push_cast; ring
  calc R 0 ≤ (∑ k ∈ Finset.range n, a k) + (n : ℝ≥0∞) * ε + R n := hm n le_rfl
    _ ≤ (∑ k ∈ Finset.range n, a k) + (n : ℝ≥0∞) * ε + (a n + T n) := by gcongr; exact h1 n
    _ = (∑ k ∈ Finset.range (n + 1), a k) + (n : ℝ≥0∞) * ε + T n := by
      rw [Finset.sum_range_succ]; ring

theorem prgReal_true_le {Seed Out : Type} [SampleableType Seed] [SampleableType Out]
    (G : PRGScheme Seed Out) (B : PRGScheme.PRGAdversary Out) :
    𝒟[G.prgRealExperiment B] {true} ≤
      G.prgAdvantage B + 𝒟[PRGScheme.prgIdealExperiment B] {true} := by
  unfold PRGScheme.prgAdvantage MeasureTheory.Measure.boolDist ENNReal.absDiff
  calc 𝒟[G.prgRealExperiment B] {true}
      ≤ (𝒟[G.prgRealExperiment B] {true} - 𝒟[PRGScheme.prgIdealExperiment B] {true}) +
          𝒟[PRGScheme.prgIdealExperiment B] {true} := le_tsub_add
    _ ≤ ((𝒟[G.prgRealExperiment B] {true} - 𝒟[PRGScheme.prgIdealExperiment B] {true}) +
          (𝒟[PRGScheme.prgIdealExperiment B] {true} - 𝒟[G.prgRealExperiment B] {true})) +
          𝒟[PRGScheme.prgIdealExperiment B] {true} := by
        gcongr
        exact le_self_add

theorem prfBranch_false_true_le {Key Input Tag : Type} [SampleableType Key]
    [DecidableEq Input] [SampleableType Tag]
    (mac : MACScheme Key Input Tag) (A : MACScheme.PRFAdversary Input Tag) :
    𝒟[mac.branch false A] {true} ≤
      mac.prfAdvantage A + 𝒟[mac.branch true A] {true} := by
  rw [MACScheme.prfAdvantage_eq_boolDist]
  unfold MeasureTheory.Measure.boolDist ENNReal.absDiff
  calc 𝒟[mac.branch false A] {true}
      ≤ (𝒟[mac.branch false A] {true} - 𝒟[mac.branch true A] {true}) +
          𝒟[mac.branch true A] {true} := le_tsub_add
    _ ≤ ((𝒟[mac.branch true A] {true} - 𝒟[mac.branch false A] {true}) +
          (𝒟[mac.branch false A] {true} - 𝒟[mac.branch true A] {true})) +
          𝒟[mac.branch true A] {true} := by
        gcongr
        exact le_add_self

end Combinators

end Computational.Proofs.E2E.HaltedSpkDefs
