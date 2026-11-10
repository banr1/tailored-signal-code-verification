/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping -- proof-setup: allow-public-import
public import Computational.Specifications.Game.StatementPqOomFlag
import Computational.Proofs.E2E.Dsl.TablesHonest
import Computational.Proofs.E2E.Dsl.PqxdhSimTypes
import Computational.Proofs.E2E.Dsl.StartAndExtSmAux
import Computational.Proofs.Game.PromotedCostedReds.SimFig8State
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost
import Computational.Proofs.E2E.ComposedPrefixHelpers

/-!
# Tracker-Halted Oracles, State Encoding, and Initializer for `uniformStart`

Defines the `KemFailSessionTrack`-halted R-game oracles (`oracleImplRSessionTrackHalted`,
`uniformStartDistinguisherTrackHalted`) and their `ReductionDsl` state encoding, halted
initializer `initEpoch0GsTrackC`, and reverse wire lookup `findRevHonestWiresIdxE`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Init

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp
  bits atomicSig atomicSessionOps coinOnlyIface
  BV256 BV512 B UniformSamplerTag)
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet (RootKey)
open CryptoGames.Ratchet.LibsignalInst (libsignalSessionSchemeFromEpoch0Keys ratchetKeyAdmissible
  configR1OnCurve)
open CryptoGames.Ratchet.LibsignalSim (kemTrackEnc)
open CryptoGames.SM (RecvResult GameState ConfigR Adversary
  initState inWindow samIfNec transmitImpl challImpl transmitR challR deliverR injectR corrR
  oracleImplR spec noAliceCorrWhileAliceBelowEpoch10 partyEnc boolEq orE otherE pGet
  letE_eval some_eval orE_eval pGet_eval)
open CryptoGames.LibsignalSession (Params Crypto ShaCompress IdentityKey PublicKey GhostState)
open CryptoGames.LibsignalSM.Proofs.Refinement (KemFailTrackState initKemFailTrack
  stepKemFailSend stepKemFailDeliver)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes liftStateT paramsIdsWithSpqr paramsV1 sessionSchemeFixedSpk
  oracleImplR_preserves_b)
open CryptoVerification.E2E.HeadlineU (sample_prod_bindU)
open CryptoVerification.E2E.Costed (e2eSig e2eOps smRT E2EPureOp E2EUnifBase e2eSamplers)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp size_e2ePureOp
  size_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (v eLet eCaseOpt)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmListBounded SmReachBounded smReachBounded_initState
  smReachBounded_oracleImplR)
open Computational.Proofs.E2E.Dsl.StartAndExtSmAux (initFixedSpkAliceE initFixedSpkBobE
  initFixedSpkGsE eval_initFixedSpkGsE cost_initFixedSpkGsE)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (smRCorrE eval_smRCorrE cost_smRCorrE
  e2eGsTy e2eGsEnc e2eGsSt e2eGsWin e2eGsEpoch
  e2eCorrAllowedE eval_e2eCorrAllowedE cost_e2eCorrAllowedE_le
  e2eInWindowE eval_e2eInWindowE cost_e2eInWindowE_le
  e2eAfterCorrAllowedE eval_e2eAfterCorrAllowedE cost_e2eAfterCorrAllowedE_le)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (sessPureOp sessSpqrKemOp
  zeroPqxdhPrims liftTy liftVal coinE2EIface liftCompCoins liftCompCoins_queries_zero
  liftCompCoins_cost liftCompCoins_eval renComp renComp_queries renComp_cost renComp_eval)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (comp_eval_bind
  liftP_unif_eq_self liftCompCoins_size_le renComp_size
  idKeyLitE idKeyPairLitE eval_idKeyPairLitE cost_idKeyPairLitE size_idKeyPairLitE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit (kemTrackT kemTrackAtomicEnc
  initV1BraidStAtomicE initKemTrackAtomicE initKemTrackAtomicE_eval kemTrackEnc_initKemFailTrack)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost (initKemTrackAtomicE_cost)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness (KemTrackDeliverInv
  KemTrackDeliverInv.mono kemTrackDeliverInv_init kemTrackDeliverInv_step
  kemTrackDeliverInv_stepSend)

/-! ## Shallow tracker-halted oracles -/

section Helpers

@[expose] def sub1Ren {S : Sig} {a : Ty S} {Γ : List (Ty S)} : ∀ {u}, Var [a] u → Var (a :: Γ) u
  | _, .zero => .zero

@[expose] def callSub1C {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b : Ty S} (sub : Comp O I [a] b) (arg : Expr O Γ a) :
    Comp O I Γ b :=
  .bind (.ret arg) (renComp sub1Ren sub)

theorem callSub1C_queries {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b : Ty S} (sub : Comp O I [a] b) (arg : Expr O Γ a)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (callSub1C sub arg).queries w ws = sub.queries w ws := by
  simp [callSub1C, Comp.queries, renComp_queries]

theorem callSub1C_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b : Ty S} (sub : Comp O I [a] b) (arg : Expr O Γ a) :
    (callSub1C sub arg).cost = arg.cost + 1 + sub.cost + 1 := by
  simp only [callSub1C, Comp.cost, renComp_cost]

theorem callSub1C_size {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b : Ty S} (sub : Comp O I [a] b) (arg : Expr O Γ a) :
    (callSub1C sub arg).size = arg.size + 1 + sub.size + 1 := by
  simp only [callSub1C, Comp.size, renComp_size]

theorem callSub1C_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b : Ty S} (sub : Comp O I [a] b) (arg : Expr O Γ a) (ρ : Env Γ) :
    (callSub1C sub arg).eval ρ = sub.eval (.cons (arg.eval ρ) .nil) := by
  unfold callSub1C
  simp only [Comp.eval, pure_bind, renComp_eval]
  rfl

end Helpers

section ShallowTrackHalted

/-- Per-session braid tracker paired with the prepend-only list of honest `(wire, sender)` pairs. -/
abbrev KemFailSessionTrack (F : ShaCompress) (C : Type) : Type :=
  KemFailTrackState F × List (C × Party)

@[expose] def initKemFailSessionTrack (F : ShaCompress) (C : Type) (pqrKey : BitVec 256) :
    KemFailSessionTrack F C :=
  (initKemFailTrack F pqrKey, [])

abbrev libsignalSessionPqrOf (k : RootKey × BitVec 256 × BitVec 256 × BitVec 256) : BitVec 256 :=
  k.2.2.2

@[expose] noncomputable def transmitRSessionTrackHalted {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option (BitVec 512)) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (BitVec 512 × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      let (tr, hw) ← StateT.lift get
      let tr' := stepKemFailSend F K tr P coins
      if tr'.cand.isSome then
        StateT.lift (set ({ tr with cand := tr'.cand }, hw))
        return none
      else
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
        StateT.lift (set (tr', (out.2, P) :: hw))
        return some out.2

@[expose] noncomputable def challRSessionTrackHalted {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option (BitVec 512)) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (BitVec 512 × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
      let (tr, hw) ← StateT.lift get
      let tr' := stepKemFailSend F K tr P coins
      if tr'.cand.isSome then
        StateT.lift (set ({ tr with cand := tr'.cand }, hw))
        return none
      else
        let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
        StateT.lift (set (tr', (out.2, P) :: hw))
        return some out.2

@[expose] noncomputable def deliverRSessionTrackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) :=
  fun ⟨Q, w⟩ => do
    let (_, hw) ← StateT.lift get
    let j? := hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other)
    let res ← liftStateT (deliverR sm cfg (Q, w))
    match res, j? with
    | some (.accepted _ _ _), some j =>
      StateT.lift (modify fun (tr, hw') => (stepKemFailDeliver F K tr Q j, hw'))
    | _, _ => pure ()
    return res

@[expose] noncomputable def oracleImplRSessionTrackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (spec St Msg (BitVec 512) C)
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) :=
  transmitRSessionTrackHalted F K sm Δ qep cfg +
    challRSessionTrackHalted F K sm Δ qep cfg +
    deliverRSessionTrackHalted F K sm cfg +
    ((fun q => liftStateT (injectR sm Δ qep cfg q)) :
      QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
        (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp))) +
    ((fun P => liftStateT (corrR cfg P)) :
      QueryImpl (Party →ₒ Option St)
        (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)))

@[expose] noncomputable def runRSessionTrackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (b : Bool) (A : Adversary St Msg (BitVec 512) C) :
    ProbComp ((Bool × GameState St Msg C) × KemFailSessionTrack F C) := do
  let k ← ($ᵗ Key : ProbComp Key)
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) +
    oracleImplRSessionTrackHalted F K sm Δ qep cfg
  ((simulateQ impl A).run (initState sm.sendPart k b)).run
    (initKemFailSessionTrack F C (pqrOf k))

/-- Tracker-halted uniform-start PRG distinguisher on `(rk0, ck0)`. -/
@[expose] noncomputable def uniformStartDistinguisherTrackHalted
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes) (qep : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    PRGScheme.PRGAdversary (RootKey × BitVec 256) := fun rc => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((b', s), _) ←
    runRSessionTrackHalted libsignalSessionPqrOf P.C.F K
      (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) 3 qep cfg b A
  return (b == b' || s.win)

theorem oracleImplRSessionTrackHalted_epoch0Keys_eq_fixedSpk
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ Δ qep : ℕ) (rc : RootKey × BitVec 256) (spk : BitVec 256)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes) :
    oracleImplRSessionTrackHalted C.F K
        (libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2) Δ qep cfg =
      oracleImplRSessionTrackHalted C.F K
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spk) Δ qep cfg :=
  rfl

end ShallowTrackHalted

/-! ## DSL state encoding and halted initializer -/

section InitHalted

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT
local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[expose, reducible] def kemSessionTrackT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (kemTrackT ℓ Pt) (.list (.prod (B (ℓ := ℓ) (Pt := Pt) 32) .bool))

/-- Combined DSL state type pairing `liftTy (Pt := Pt) (e2eGsTy ℓ)` with `kemSessionTrackT ℓ Pt`. -/
@[expose, reducible] def sessionHaltedStTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (kemSessionTrackT ℓ Pt)

@[expose] def kemSessionTrackEnc {F : ShaCompress}
    (ts : KemFailSessionTrack F Bytes) :
    (kemSessionTrackT ℓ Pt).denote :=
  (kemTrackAtomicEnc (kemTrackEnc ts.1), ts.2.map fun wp => (wp.1, partyEnc wp.2))

@[expose] def sessionHaltedEnc {F : ShaCompress}
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack F Bytes) :
    (sessionHaltedStTy ℓ Pt).denote :=
  (liftVal (Pt := Pt) (e2eGsEnc st.1), kemSessionTrackEnc st.2)

@[expose] def initEpoch0GsWithPqrE2EC (idA idB : IdentityKey) :
    Comp EOps (coinE2EIface (coinOnlyIface ℓ Pt))
      [.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256]
      (.prod (e2eGsTy ℓ) CryptoVerification.E2E.Costed.BV256) :=
  .bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) UniformSamplerTag.bool .unit)
    (.bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) (UniformSamplerTag.base .bv256) .unit)
      (.bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) (UniformSamplerTag.base .bv256) .unit)
        (.bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) (UniformSamplerTag.base .bv256) .unit)
          (.bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) (UniformSamplerTag.base .bv256) .unit)
            (.ret (.pair
              (initFixedSpkGsE (idKeyPairLitE idA idB)
                (.pair (.var (.succ (.succ .zero)))
                  (.pair
                    (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
                      (.pair (.var (.succ .zero)) (.var .zero)))
                    (.var (.succ (.succ (.succ (.succ .zero))))))))
              (.var .zero)))))))

/-- Atomic initializer for halted `uniformStart` over `atomicSessionOps`. -/
@[expose] def initEpoch0GsTrackC (idA idB : IdentityKey) :
    Comp AOps (coinOnlyIface ℓ Pt)
      [.prod BV256 BV256]
      (.prod .unit (sessionHaltedStTy ℓ Pt)) :=
  .bind
    (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) rfl
      (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (decT := decT) (encT := encT) idA idB))
    (.ret (.pair .unit
      (.pair (.fst .v0)
        (.pair
          (initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) (.snd .v0))
          .nil))))

theorem initEpoch0GsTrackC_queries_zero (idA idB : IdentityKey) (w : Empty → ℕ) :
    (initEpoch0GsTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).queries
      w (fun _ => 0) = 0 := by
  simp only [initEpoch0GsTrackC, Comp.queries, liftCompCoins_queries_zero, Nat.add_zero]

theorem initEpoch0GsTrackC_cost (idA idB : IdentityKey) :
    (initEpoch0GsTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).cost ≤ 3100000 := by
  have h1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (decT := decT) (encT := encT) idA idB)
  let Γ5 : List (Ty ESig) :=
    [Ty.base E2EUnifBase.bv256.sort,
     Ty.base E2EUnifBase.bv256.sort,
     Ty.base E2EUnifBase.bv256.sort,
     Ty.base E2EUnifBase.bv256.sort,
     .bool,
     .prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256]
  have hids := cost_idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := Γ5) idA idB
  have hgs := cost_initFixedSpkGsE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ5)
    (idKeyPairLitE idA idB)
    (.pair (.var (.succ (.succ .zero)))
      (.pair
        (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
          (.pair (.var (.succ .zero)) (.var .zero)))
        (.var (.succ (.succ (.succ (.succ .zero)))))))
  let ΓA : List (Ty ASig) :=
    [.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) BV256, .prod BV256 BV256]
  have htr := initKemTrackAtomicE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := ΓA) (.snd .v0)
  dsimp only [initEpoch0GsTrackC, initEpoch0GsWithPqrE2EC] at h1 ⊢
  simp only [Comp.cost, Expr.cost, Expr.v0, coinE2EIface, e2eSamplers,
    _root_.ReductionDsl.unifSamplers, E2EUnifBase.cost] at hgs h1 htr ⊢
  omega

theorem initEpoch0GsTrackC_size_le (idA idB : IdentityKey) :
    (initEpoch0GsTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).size ≤ 5200 := by
  have h1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (decT := decT) (encT := encT) idA idB)
  have h2 : (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (decT := decT) (encT := encT) idA idB).size ≤ 550 := by
    simp only [initEpoch0GsWithPqrE2EC, initFixedSpkGsE, initFixedSpkAliceE, initFixedSpkBobE,
      size_idKeyPairLitE, eLet, eCaseOpt, v, size_e2ePureOp, size_e2eCryptoOp, E2EPureOp.opSize,
      Comp.size, Expr.size, show bits 0 = 1 from rfl]
    omega
  have h3 : (initKemTrackAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (Γ := [.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) BV256, .prod BV256 BV256]) (.snd .v0)).size ≤
      130 := by
    have haP : ∀ (o : _root_.ReductionDsl.AtomicPureOp),
        (AOps).opSize (.inl (.inl (.inl (.inl o)))) = o.opSize := fun _ => rfl
    have haS : ∀ (o : _root_.ReductionDsl.AtomicSpqrKemOp),
        (AOps).opSize (.inr o) = 0 := fun _ => rfl
    simp only [initKemTrackAtomicE, initV1BraidStAtomicE,
      Computational.Proofs.Game.PromotedCostedReds.SimFig8State.eLet, sessPureOp, sessSpqrKemOp,
      Expr.size, haP, haS, _root_.ReductionDsl.AtomicPureOp.opSize, List.length_nil,
      Expr.v0, show bits 0 = 1 from rfl]
    omega
  dsimp only [initEpoch0GsTrackC]
  simp only [Comp.size, Expr.size, Expr.v0] at h3 ⊢
  omega

/-- Reverse index search in `honestWires` matching `honestWires.reverse.findIdx?` when
`honestWires.length ≤ q`. -/
@[expose] def findRevHonestWiresIdxE (q : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) : Expr AOps Γ (.opt .nat) :=
  .letE (.pair wiresE (.pair qBE wE))
    (.fst (.foldrB q (.fst .v0) (.pair .none (.nat 0))
      (let qOther := otherE (.fst (.snd .v2))
       let w := Expr.snd (.snd .v2)
       let wEntry := Expr.fst .v0
       let pEntry := Expr.snd .v0
       let eqW := sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
         (decT := decT) (lam := lam) (.bytesEq 32 32) (.pair wEntry w)
       let eqSender := boolEq pEntry qOther
       let matched := Expr.and eqW eqSender
       let prevOpt := Expr.fst .v1
       let cnt := Expr.snd .v1
       let nextOpt := Expr.caseOpt prevOpt (.ite matched (.some cnt) .none) (.some .v0)
       .pair nextOpt (.add cnt (.nat 1)))))

private def stepRevIdx {α : Type} (p : α → Bool) (x : α) (acc : Option ℕ × ℕ) : Option ℕ × ℕ :=
  (match acc.1 with
   | none => if p x then some acc.2 else none
   | some k => some k,
   acc.2 + 1)

private theorem foldl_stepRevIdx_some {α : Type} (p : α → Bool) :
    ∀ (ys : List α) (i k : ℕ),
      (ys.foldl (fun acc x => stepRevIdx p x acc) (some i, k)).1 = some i
  | [], _, _ => rfl
  | _ :: rest, i, k => foldl_stepRevIdx_some p rest i (k + 1)

private theorem foldl_stepRevIdx_none {α : Type} (p : α → Bool) :
    ∀ (ys : List α) (k : ℕ),
      (ys.foldl (fun acc x => stepRevIdx p x acc) (none, k)).1 = (ys.findIdx? p).map (· + k)
  | [], _ => rfl
  | y :: rest, k => by
    rw [List.findIdx?_cons, List.foldl_cons]
    cases hp : p y
    · have h0 : stepRevIdx p y (none, k) = (none, k + 1) := by simp [stepRevIdx, hp]
      rw [h0, foldl_stepRevIdx_none p rest (k + 1)]
      rcases rest.findIdx? p with _ | m
      · simp
      · simp; omega
    · have h0 : stepRevIdx p y (none, k) = (some k, k + 1) := by simp [stepRevIdx, hp]
      rw [h0, foldl_stepRevIdx_some p rest k (k + 1)]
      simp

private theorem foldr_eq_foldl_rev {α β : Type} (f : α → β → β) :
    ∀ (xs : List α) (z : β), xs.foldr f z = xs.reverse.foldl (fun acc x => f x acc) z
  | [], _ => rfl
  | x :: rest, z => by
    rw [List.foldr_cons, foldr_eq_foldl_rev f rest z,
      List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem foldr_stepRevIdx_eq_findIdx {α : Type} (p : α → Bool) (xs : List α) :
    (xs.foldr (stepRevIdx p) (none, 0)).1 = xs.reverse.findIdx? p := by
  rw [foldr_eq_foldl_rev, foldl_stepRevIdx_none]
  rcases xs.reverse.findIdx? p with _ | m <;> simp

theorem findRevHonestWiresIdxE_eval (q : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ)
    (honestWires : List (Bytes × Party)) (Q : Party) (w : Bytes)
    (hLen : honestWires.length ≤ q)
    (hwires : wiresE.eval ρ = honestWires.map fun wp => (wp.1, partyEnc wp.2))
    (hq : qBE.eval ρ = partyEnc Q)
    (hw : wE.eval ρ = w) :
    (findRevHonestWiresIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q wiresE qBE wE).eval ρ =
      honestWires.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) := by
  unfold findRevHonestWiresIdxE
  rw [letE_eval]
  have hp0 : (Expr.pair wiresE (.pair qBE wE)).eval ρ =
      (honestWires.map (fun wp => (wp.1, partyEnc wp.2)), (partyEnc Q, w)) := by
    simp only [Expr.eval, hwires, hq, hw]
  rw [hp0]
  have htake : (honestWires.map fun wp => (wp.1, partyEnc wp.2)).take q =
      honestWires.map fun wp => (wp.1, partyEnc wp.2) := by
    apply List.take_of_length_le
    simpa using hLen
  have hfold :
      (Expr.foldrB q (O := AOps) (.fst .v0) (.pair .none (.nat 0))
        (.pair
          (.caseOpt (.fst .v1)
            (.ite
              (.and
                (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                  (decT := decT) (lam := lam) (.bytesEq 32 32) (.pair (.fst .v0) (.snd (.snd .v2))))
                (boolEq (.snd .v0) (otherE (.fst (.snd .v2)))))
              (.some (.snd .v1)) .none)
            (.some .v0))
          (.add (.snd .v1) (.nat 1)))).eval
        (.cons (honestWires.map (fun wp => (wp.1, partyEnc wp.2)), (partyEnc Q, w)) ρ) =
      honestWires.foldr
        (stepRevIdx (fun wp : Bytes × Party => wp.1 == w && wp.2 == Q.other)) (none, 0) := by
    simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, htake, List.foldr_map]
    congr 1; funext wp acc
    have heqW : (AOps).eval (.inl (.inl (.inl (.inl (.bytesEq 32 32))))) (wp.1, w) =
        (wp.1 == w) := rfl
    simp only [stepRevIdx, otherE, boolEq, Expr.eval, Env.get, heqW]
    rcases wp with ⟨wp1, pEntry⟩
    cases pEntry <;> cases Q <;> rcases acc with ⟨_ | k, cnt⟩ <;>
      simp [partyEnc, Party.other]
  exact (congrArg Prod.fst hfold).trans
    (foldr_stepRevIdx_eq_findIdx
      (fun wp : Bytes × Party => wp.1 == w && wp.2 == Q.other) honestWires)

theorem findRevHonestWiresIdxE_cost (q : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) :
    (findRevHonestWiresIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q wiresE qBE wE).cost ≤
      wiresE.cost + qBE.cost + wE.cost + 100 * q + 20 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hop : (AOps).cost (.inl (.inl (.inl (.inl (.bytesEq 32 32))))) = 64 := rfl
  simp only [findRevHonestWiresIdxE, boolEq, otherE, sessPureOp,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, hb0, hb1, hop]
  have hstep :
      (1 + 1 +
        max
          (1 + 1 + (1 + 1 + 1) + 1 + 64 +
            (1 + 1 + max (1 + 1 + 1 + 1) (1 + 1 + 1 + 1 + 1) + 1) + 1 +
            max (1 + 1 + 1) 1 + 1)
          (1 + 1) + 1 + (1 + 1 + 1 + 1) + 1 + 1) = 92 := by decide
  rw [hstep]
  omega

theorem findRevHonestWiresIdxE_size (q : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) :
    (findRevHonestWiresIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q wiresE qBE wE).size ≤
      wiresE.size + qBE.size + wE.size + bits q + 60 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hop : (AOps).opSize (.inl (.inl (.inl (.inl (.bytesEq 32 32))))) = 0 := rfl
  simp only [findRevHonestWiresIdxE, boolEq, otherE, sessPureOp,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, hb0, hb1, hop]
  omega

@[expose] noncomputable def epoch0TrackInitImpl (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (ℓ : ℕ)
    (rc : RootKey × BitVec 256) :
    ProbComp (Unit × (GameState (GhostState Bytes) (Plain ℓ) Bytes ×
      KemFailSessionTrack C.F Bytes)) := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let k ← ($ᵗ (RootKey × BitVec 256 × BitVec 256 × BitVec 256) : ProbComp _)
  return ((), (initState
    (libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2).sendPart k b,
    initKemFailSessionTrack C.F Bytes k.2.2.2))

theorem initEpoch0GsTrackC_eval (idA idB : IdentityKey) (rc : RootKey × BitVec 256) :
    (initEpoch0GsTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).eval (.cons rc .nil) =
      Prod.map id (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt)) <$>
        epoch0TrackInitImpl C K idA idB ℓ rc := by
  have hev := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (decT := decT) (encT := encT) idA idB)
    (.cons rc .nil)
  change (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
      (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (decT := decT) (encT := encT) idA idB)).eval (.cons rc .nil) =
    liftVal (Pt := Pt) <$>
      (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (decT := decT) (encT := encT) idA idB).eval (.cons rc .nil) at hev
  unfold initEpoch0GsTrackC
  rw [comp_eval_bind, hev]
  have hlift : ∀ {α : Type} (p : ProbComp α),
      (coinE2EIface (coinOnlyIface ℓ Pt)).liftP p = p :=
    fun p => liftP_unif_eq_self _ (fun _ => rfl) p
  unfold initEpoch0GsWithPqrE2EC epoch0TrackInitImpl
  simp only [Comp.eval, hlift, e2eSamplers, _root_.ReductionDsl.unifSamplers,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine congrArg (_ >>= ·) (funext fun b => ?_)
  rw [sample_prod_bindU]
  refine congrArg (_ >>= ·) (funext fun k0 => ?_)
  rw [sample_prod_bindU]
  refine congrArg (_ >>= ·) (funext fun spk => ?_)
  rw [sample_prod_bindU]
  refine congrArg (_ >>= ·) (funext fun ac => ?_)
  refine congrArg (_ >>= ·) (funext fun pqr => ?_)
  let gs0 := initState
    (libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2).sendPart
    (k0, spk, ac, pqr) b
  have hgs :
      (initFixedSpkGsE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
        (decT := decT) (encT := encT)
        (idKeyPairLitE idA idB)
        (.pair (.var (.succ (.succ .zero)))
          (.pair
            (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
              (.pair (.var (.succ .zero)) (.var .zero)))
            (.var (.succ (.succ (.succ (.succ .zero)))))))).eval
        (.cons pqr (.cons ac (.cons spk (.cons k0 (.cons b (.cons rc .nil)))))) =
      e2eGsEnc gs0 := by
    have h := eval_initFixedSpkGsE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT)
      (idKeyPairLitE idA idB)
      (.pair (.var (.succ (.succ .zero)))
        (.pair
          (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
            (.pair (.var (.succ .zero)) (.var .zero)))
          (.var (.succ (.succ (.succ (.succ .zero)))))))
      (.cons pqr (.cons ac (.cons spk (.cons k0 (.cons b (.cons rc .nil))))))
    rw [eval_idKeyPairLitE] at h
    exact h
  exact congrArg pure (Prod.ext rfl (Prod.ext (congrArg (liftVal (Pt := Pt)) hgs) (Prod.ext
    ((initKemTrackAtomicE_eval (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (.snd .v0) _).trans
      (congrArg kemTrackAtomicEnc (kemTrackEnc_initKemFailTrack C.F pqr).symm)) rfl)))

theorem epoch0TrackInitImpl_inv (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ : ℕ) (rc : RootKey × BitVec 256)
    {r : Unit × (GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes)}
    (hr : r ∈ support (epoch0TrackInitImpl C K idA idB ℓ rc)) :
    SmReachBounded C K 0 r.2.1 ∧
      KemTrackDeliverInv C.F K 0 (kemTrackEnc r.2.2.1) ∧
      r.2.2.2.length ≤ 0 := by
  unfold epoch0TrackInitImpl at hr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨b, -, ⟨k0, ⟨spk, ac, pqr⟩⟩, -, rfl⟩ := hr
  exact ⟨smReachBounded_initState C K idA idB ℓ spk ((rc.1, rc.2), (ac, pqr)) b,
    kemTrackDeliverInv_init C.F K 0 pqr,
    Nat.le_refl 0⟩

end InitHalted

section ShallowInvariants

@[local simp] private theorem liftStateT_run_state {σ τ α : Type}
    (x : StateT σ ProbComp α) (s : σ) (t : τ) :
    ((liftStateT x : StateT σ (StateT τ ProbComp) α).run s).run t =
      (x.run s >>= fun a => pure (a, t)) :=
  rfl

theorem oracleImplRSessionTrackHalted_preserves_b
    {Key St Msg RCoins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (sq : (spec St Msg (BitVec 512) C).Domain)
    (st : GameState St Msg C) (ts : KemFailSessionTrack F C)
    {out : ((spec St Msg (BitVec 512) C).Range sq × GameState St Msg C) × KemFailSessionTrack F C}
    (hout : out ∈ support (((oracleImplRSessionTrackHalted F K sm Δ qep cfg sq).run st).run ts)) :
    out.1.2.b = st.b := by
  rcases out with ⟨⟨ans, st'⟩, ⟨tr', hw'⟩⟩
  rcases ts with ⟨tr, hw⟩
  rcases sq with (((⟨P, m, optR⟩ | ⟨P, m0, m1, optR⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | P
  · change ((ans, st'), tr', hw') ∈
        support (((transmitRSessionTrackHalted F K sm Δ qep cfg (P, m, optR)).run st).run (tr, hw)) at hout
    unfold transmitRSessionTrackHalted at hout
    by_cases hok : cfg.sendOK st P
    · by_cases hwin : st.win
      · simp [hok, hwin, StateT.run_bind, StateT.run_get, StateT.run_pure] at hout
        rcases hout with ⟨⟨_, rfl⟩, _, _⟩; rfl
      · simp only [hok, hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_monadLift, monadLift_self,
          pure_bind, bind_assoc, mem_support_bind_iff] at hout
        obtain ⟨⟨coins, bad⟩, hsam, hout⟩ := hout
        cases hep : st.epMgmt Δ qep P bad with
        | none =>
          simp [hep, StateT.run_pure] at hout
          rcases hout with ⟨⟨_, rfl⟩, _, _⟩; rfl
        | some s1 =>
          simp only [hep, StateT.run_bind, StateT.run_lift, StateT.run_get,
            pure_bind, bind_assoc] at hout
          by_cases hc : (stepKemFailSend F K tr P coins).cand.isSome
          · simp [hc, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
              -bind_pure_comp] at hout
            rcases hout with ⟨⟨_, rfl⟩, _, _⟩; rfl
          · simp [hc, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
              -bind_pure_comp] at hout
            rcases hout with ⟨⟨rfl, rfl⟩, rfl, rfl⟩
            have hmem : (some (sm.send (s1.st P) m coins).2,
                s1.record Δ P (sm.send (s1.st P) m coins).1
                  ⟨⟨P, s1.epoch P, s1.idx P + 1⟩, m, (sm.send (s1.st P) m coins).2⟩ false) ∈
                support ((oracleImplR sm Δ qep cfg (.inl (.inl (.inl (.inl (P, m, optR)))))).run st) := by
              change _ ∈ support ((transmitR sm Δ qep cfg (P, m, optR)).run st)
              unfold transmitR transmitImpl
              simp only [StateT.run_bind, StateT.run_get, hok, hwin, Bool.not_true,
                Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
                pure_bind, bind_assoc, mem_support_bind_iff]
              refine ⟨(coins, bad), hsam, ?_⟩
              simp [hep, StateT.run_set]
              exact ⟨rfl, rfl⟩
            exact oracleImplR_preserves_b sm Δ qep cfg (.inl (.inl (.inl (.inl (P, m, optR))))) st hmem
    · simp [hok, StateT.run_bind, StateT.run_get, StateT.run_pure] at hout
      rcases hout with ⟨⟨_, rfl⟩, _, _⟩; rfl
  · change ((ans, st'), tr', hw') ∈
        support (((challRSessionTrackHalted F K sm Δ qep cfg (P, m0, m1, optR)).run st).run (tr, hw)) at hout
    unfold challRSessionTrackHalted at hout
    by_cases hok : cfg.sendOK st P
    · by_cases hwin : st.win
      · simp [hok, hwin, StateT.run_bind, StateT.run_get, StateT.run_pure] at hout
        rcases hout with ⟨⟨_, rfl⟩, _, _⟩; rfl
      · simp only [hok, hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_monadLift, monadLift_self,
          pure_bind, bind_assoc, mem_support_bind_iff] at hout
        obtain ⟨⟨coins, bad⟩, hsam, hout⟩ := hout
        cases hep : st.epMgmt Δ qep P bad with
        | none =>
          simp [hep, StateT.run_pure] at hout
          rcases hout with ⟨⟨_, rfl⟩, _, _⟩; rfl
        | some s1 =>
          by_cases hsc : !(s1.safeCh Δ P) || !(cfg.base.challAllowedIn (s1.epoch P))
          · simp [hep, hsc, StateT.run_pure] at hout
            rcases hout with ⟨⟨_, rfl⟩, _, _⟩; rfl
          · simp only [hep, hsc, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, StateT.run_lift, StateT.run_get,
              pure_bind, bind_assoc] at hout
            by_cases hc : (stepKemFailSend F K tr P coins).cand.isSome
            · simp [hc, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
                -bind_pure_comp] at hout
              rcases hout with ⟨⟨_, rfl⟩, _, _⟩; rfl
            · simp [hc, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
                -bind_pure_comp] at hout
              rcases hout with ⟨⟨rfl, rfl⟩, rfl, rfl⟩
              set mUse := (cfg.base.challMsg (s1.epoch P)).getD (if st.b then m1 else m0)
              have hmem : (some (sm.send (s1.st P) mUse coins).2,
                  s1.record Δ P (sm.send (s1.st P) mUse coins).1
                    ⟨⟨P, s1.epoch P, s1.idx P + 1⟩, mUse, (sm.send (s1.st P) mUse coins).2⟩ true) ∈
                  support ((oracleImplR sm Δ qep cfg
                    (.inl (.inl (.inl (.inr (P, m0, m1, optR)))))).run st) := by
                change _ ∈ support ((challR sm Δ qep cfg (P, m0, m1, optR)).run st)
                unfold challR challImpl
                simp only [StateT.run_bind, StateT.run_get, hok, hwin, Bool.not_true,
                  Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
                  pure_bind, bind_assoc, mem_support_bind_iff]
                refine ⟨(coins, bad), hsam, ?_⟩
                simp [hep, hsc, mUse, StateT.run_set]
                exact ⟨rfl, rfl⟩
              exact oracleImplR_preserves_b sm Δ qep cfg
                (.inl (.inl (.inl (.inr (P, m0, m1, optR))))) st hmem
    · simp [hok, StateT.run_bind, StateT.run_get, StateT.run_pure] at hout
      rcases hout with ⟨⟨_, rfl⟩, _, _⟩; rfl
  · change ((ans, st'), tr', hw') ∈
        support (((deliverRSessionTrackHalted F K sm cfg (Q, w)).run st).run (tr, hw)) at hout
    unfold deliverRSessionTrackHalted at hout
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get,
      liftStateT_run_state, pure_bind, bind_assoc, mem_support_bind_iff] at hout
    obtain ⟨⟨res, s1⟩, hdl, hout⟩ := hout
    have hb1 : s1.b = st.b := oracleImplR_preserves_b sm Δ qep cfg (.inl (.inl (.inr (Q, w)))) st hdl
    generalize hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) = j? at hout
    cases res with
    | none => simp [StateT.run_pure] at hout; rcases hout with ⟨⟨_, rfl⟩, _, _⟩; exact hb1
    | some rr =>
      cases rr with
      | rejected => simp [StateT.run_pure] at hout; rcases hout with ⟨⟨_, rfl⟩, _, _⟩; exact hb1
      | accepted e i m? =>
        cases j? <;>
          simp [StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
            -bind_pure_comp] at hout <;>
          rcases hout with ⟨⟨_, rfl⟩, _, _⟩ <;> exact hb1
  · change ((ans, st'), tr', hw') ∈
        support (((liftStateT (injectR sm Δ qep cfg (Q, w)) :
          StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp) _).run st).run (tr, hw))
      at hout
    simp only [liftStateT_run_state, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨⟨res, s1⟩, hij, h0⟩ := hout
    cases h0
    exact oracleImplR_preserves_b sm Δ qep cfg (.inl (.inr (Q, w))) st hij
  · change ((ans, st'), tr', hw') ∈
        support (((liftStateT (corrR cfg P) :
          StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp) _).run st).run (tr, hw))
      at hout
    simp only [liftStateT_run_state, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨⟨res, s1⟩, hcr, h0⟩ := hout
    cases h0
    exact oracleImplR_preserves_b sm Δ qep cfg (.inr P) st hcr

/-- Joint invariant preservation (`SmReachBounded`, `KemTrackDeliverInv`, and `hw.length`) across
one step of `oracleImplRSessionTrackHalted`. -/
theorem oracleImplRSessionTrackHalted_inv
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (ℓ Δ qep L : ℕ) (spk : BitVec 256)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (sq : (spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailTrackState C.F) (hw : List (Bytes × Party))
    (hReach : SmReachBounded C K L st)
    (hInv : KemTrackDeliverInv C.F K L (kemTrackEnc tr))
    (hHw : hw.length ≤ L)
    {out : ((spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
        GameState (GhostState Bytes) (Plain ℓ) Bytes) × KemFailSessionTrack C.F Bytes}
    (hout : out ∈ support (((oracleImplRSessionTrackHalted C.F K
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spk)
        Δ qep cfg sq).run st).run (tr, hw))) :
    SmReachBounded C K (L + 1) out.1.2 ∧
      KemTrackDeliverInv C.F K (L + 1) (kemTrackEnc out.2.1) ∧
      out.2.2.length ≤ L + 1 := by
  set sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spk
  rcases out with ⟨⟨ans, st'⟩, ⟨tr', hw'⟩⟩
  rcases sq with (((⟨P, m, optR⟩ | ⟨P, m0, m1, optR⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | P
  · change ((ans, st'), tr', hw') ∈
        support (((transmitRSessionTrackHalted C.F K sm Δ qep cfg (P, m, optR)).run st).run (tr, hw)) at hout
    unfold transmitRSessionTrackHalted at hout
    by_cases hok : cfg.sendOK st P
    · by_cases hwin : st.win
      · simp [hok, hwin, StateT.run_bind, StateT.run_get, StateT.run_pure] at hout
        rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
        exact ⟨hReach.mono (Nat.le_succ L), hInv.mono (Nat.le_succ L),
          Nat.le_trans hHw (Nat.le_succ L)⟩
      · simp only [hok, hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_monadLift, monadLift_self,
          pure_bind, bind_assoc, mem_support_bind_iff] at hout
        obtain ⟨⟨coins, bad⟩, hsam, hout⟩ := hout
        cases hep : st.epMgmt Δ qep P bad with
        | none =>
          simp [hep, StateT.run_pure] at hout
          rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
          exact ⟨hReach.mono (Nat.le_succ L), hInv.mono (Nat.le_succ L),
            Nat.le_trans hHw (Nat.le_succ L)⟩
        | some s1 =>
          simp only [hep, StateT.run_bind, StateT.run_lift, StateT.run_get,
            pure_bind, bind_assoc] at hout
          by_cases hc : (stepKemFailSend C.F K tr P coins).cand.isSome
          · simp [hc, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
              -bind_pure_comp] at hout
            rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
            refine ⟨hReach.mono (Nat.le_succ L), ?_, Nat.le_trans hHw (Nat.le_succ L)⟩
            exact (KemTrackDeliverInv.mono
              ⟨hInv.sentB_len, hInv.bOk, hInv.sentB_deser⟩ (Nat.le_succ L))
          · simp [hc, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
              -bind_pure_comp] at hout
            rcases hout with ⟨⟨rfl, rfl⟩, rfl, rfl⟩
            have hmem : (some (sm.send (s1.st P) m coins).2,
                s1.record Δ P (sm.send (s1.st P) m coins).1
                  ⟨⟨P, s1.epoch P, s1.idx P + 1⟩, m, (sm.send (s1.st P) m coins).2⟩ false) ∈
                support ((oracleImplR sm Δ qep cfg (.inl (.inl (.inl (.inl (P, m, optR)))))).run st) := by
              change _ ∈ support ((transmitR sm Δ qep cfg (P, m, optR)).run st)
              unfold transmitR transmitImpl
              simp only [StateT.run_bind, StateT.run_get, hok, hwin, Bool.not_true,
                Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
                pure_bind, bind_assoc, mem_support_bind_iff]
              refine ⟨(coins, bad), hsam, ?_⟩
              simp [hep, StateT.run_set]
              exact ⟨rfl, rfl⟩
            exact ⟨smReachBounded_oracleImplR C K idA idB ℓ Δ qep L spk cfg
              (.inl (.inl (.inl (.inl (P, m, optR))))) hReach hmem,
              kemTrackDeliverInv_stepSend C.F K L tr P coins hInv,
              Nat.succ_le_succ hHw⟩
    · simp [hok, StateT.run_bind, StateT.run_get, StateT.run_pure] at hout
      rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
      exact ⟨hReach.mono (Nat.le_succ L), hInv.mono (Nat.le_succ L),
        Nat.le_trans hHw (Nat.le_succ L)⟩
  · change ((ans, st'), tr', hw') ∈
        support (((challRSessionTrackHalted C.F K sm Δ qep cfg (P, m0, m1, optR)).run st).run (tr, hw)) at hout
    unfold challRSessionTrackHalted at hout
    by_cases hok : cfg.sendOK st P
    · by_cases hwin : st.win
      · simp [hok, hwin, StateT.run_bind, StateT.run_get, StateT.run_pure] at hout
        rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
        exact ⟨hReach.mono (Nat.le_succ L), hInv.mono (Nat.le_succ L),
          Nat.le_trans hHw (Nat.le_succ L)⟩
      · simp only [hok, hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_monadLift, monadLift_self,
          pure_bind, bind_assoc, mem_support_bind_iff] at hout
        obtain ⟨⟨coins, bad⟩, hsam, hout⟩ := hout
        cases hep : st.epMgmt Δ qep P bad with
        | none =>
          simp [hep, StateT.run_pure] at hout
          rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
          exact ⟨hReach.mono (Nat.le_succ L), hInv.mono (Nat.le_succ L),
            Nat.le_trans hHw (Nat.le_succ L)⟩
        | some s1 =>
          by_cases hsc : !(s1.safeCh Δ P) || !(cfg.base.challAllowedIn (s1.epoch P))
          · simp [hep, hsc, StateT.run_pure] at hout
            rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
            exact ⟨hReach.mono (Nat.le_succ L), hInv.mono (Nat.le_succ L),
              Nat.le_trans hHw (Nat.le_succ L)⟩
          · simp only [hep, hsc, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, StateT.run_lift, StateT.run_get,
              pure_bind, bind_assoc] at hout
            by_cases hc : (stepKemFailSend C.F K tr P coins).cand.isSome
            · simp [hc, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
                -bind_pure_comp] at hout
              rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
              refine ⟨hReach.mono (Nat.le_succ L), ?_, Nat.le_trans hHw (Nat.le_succ L)⟩
              exact (KemTrackDeliverInv.mono
                ⟨hInv.sentB_len, hInv.bOk, hInv.sentB_deser⟩ (Nat.le_succ L))
            · simp [hc, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
                -bind_pure_comp] at hout
              rcases hout with ⟨⟨rfl, rfl⟩, rfl, rfl⟩
              set mUse := (cfg.base.challMsg (s1.epoch P)).getD (if st.b then m1 else m0)
              have hmem : (some (sm.send (s1.st P) mUse coins).2,
                  s1.record Δ P (sm.send (s1.st P) mUse coins).1
                    ⟨⟨P, s1.epoch P, s1.idx P + 1⟩, mUse, (sm.send (s1.st P) mUse coins).2⟩ true) ∈
                  support ((oracleImplR sm Δ qep cfg
                    (.inl (.inl (.inl (.inr (P, m0, m1, optR)))))).run st) := by
                change _ ∈ support ((challR sm Δ qep cfg (P, m0, m1, optR)).run st)
                unfold challR challImpl
                simp only [StateT.run_bind, StateT.run_get, hok, hwin, Bool.not_true,
                  Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
                  pure_bind, bind_assoc, mem_support_bind_iff]
                refine ⟨(coins, bad), hsam, ?_⟩
                simp [hep, hsc, mUse, StateT.run_set]
                exact ⟨rfl, rfl⟩
              exact ⟨smReachBounded_oracleImplR C K idA idB ℓ Δ qep L spk cfg
                (.inl (.inl (.inl (.inr (P, m0, m1, optR))))) hReach hmem,
                kemTrackDeliverInv_stepSend C.F K L tr P coins hInv,
                Nat.succ_le_succ hHw⟩
    · simp [hok, StateT.run_bind, StateT.run_get, StateT.run_pure] at hout
      rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
      exact ⟨hReach.mono (Nat.le_succ L), hInv.mono (Nat.le_succ L),
        Nat.le_trans hHw (Nat.le_succ L)⟩
  · change ((ans, st'), tr', hw') ∈
        support (((deliverRSessionTrackHalted C.F K sm cfg (Q, w)).run st).run (tr, hw)) at hout
    unfold deliverRSessionTrackHalted at hout
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get,
      liftStateT_run_state, pure_bind, bind_assoc, mem_support_bind_iff] at hout
    obtain ⟨⟨res, s1⟩, hdl, hout⟩ := hout
    have hReach1 := smReachBounded_oracleImplR C K idA idB ℓ Δ qep L spk cfg
      (.inl (.inl (.inr (Q, w)))) hReach hdl
    cases res with
    | none =>
      simp [StateT.run_pure] at hout
      rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
      exact ⟨hReach1, hInv.mono (Nat.le_succ L), Nat.le_trans hHw (Nat.le_succ L)⟩
    | some rr =>
      cases rr with
      | rejected =>
        simp [StateT.run_pure] at hout
        rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
        exact ⟨hReach1, hInv.mono (Nat.le_succ L), Nat.le_trans hHw (Nat.le_succ L)⟩
      | accepted e i m? =>
        cases hj : List.findIdx? (fun wp =>
            @BEq.beq Bytes (@instBEqOfDecidableEq Bytes inferInstance) wp.1 w &&
              wp.2 == Q.other) hw.reverse with
        | none =>
          rw [hj] at hout
          simp [StateT.run_pure] at hout
          rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
          exact ⟨hReach1, hInv.mono (Nat.le_succ L), Nat.le_trans hHw (Nat.le_succ L)⟩
        | some j =>
          rw [hj] at hout
          simp [StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
            -bind_pure_comp] at hout
          rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
          exact ⟨hReach1,
            (kemTrackDeliverInv_step C.F K L tr Q j hInv).mono (Nat.le_succ L),
            Nat.le_trans hHw (Nat.le_succ L)⟩
  · change ((ans, st'), tr', hw') ∈
        support (((liftStateT (injectR sm Δ qep cfg (Q, w)) :
          StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
            (StateT (KemFailSessionTrack C.F Bytes) ProbComp) _).run st).run (tr, hw)) at hout
    simp only [liftStateT_run_state, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨⟨res, s1⟩, hij, h0⟩ := hout
    cases h0
    exact ⟨smReachBounded_oracleImplR C K idA idB ℓ Δ qep L spk cfg
      (.inl (.inr (Q, w))) hReach hij,
      hInv.mono (Nat.le_succ L),
      Nat.le_trans hHw (Nat.le_succ L)⟩
  · change ((ans, st'), tr', hw') ∈
        support (((liftStateT (corrR cfg P) :
          StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
            (StateT (KemFailSessionTrack C.F Bytes) ProbComp) _).run st).run (tr, hw)) at hout
    simp only [liftStateT_run_state, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨⟨res, s1⟩, hcr, h0⟩ := hout
    cases h0
    exact ⟨smReachBounded_oracleImplR C K idA idB ℓ Δ qep L spk cfg
      (.inr P) hReach hcr,
      hInv.mono (Nat.le_succ L),
      Nat.le_trans hHw (Nat.le_succ L)⟩

end ShallowInvariants

section CrArmE2E

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} {C : Crypto} {K : MlKem}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

private theorem liftP_pure_eq {S0 : Sig} {ι : Type} {T : OracleSpec ι} (I0 : Iface S0 T)
    {α : Type} (a : α) : I0.liftP (pure a) = pure a := by
  simp [Iface.liftP]

@[expose] def noAliceBelow10E {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (pE : Expr EOps Γ .bool) : Expr EOps Γ .bool :=
  .not (.and (.not pE) (.lt (.fst (e2eGsEpoch gsE)) (.nat 10)))

theorem eval_noAliceBelow10E {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (pE : Expr EOps Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party)
    (hgs : gsE.eval ρ = e2eGsEnc st) (hp : pE.eval ρ = partyEnc party) :
    (noAliceBelow10E (C := C) (K := K) (decT := decT) (encT := encT) gsE pE).eval ρ =
      noAliceCorrWhileAliceBelowEpoch10 st party := by
  cases party <;>
    simp [noAliceBelow10E, noAliceCorrWhileAliceBelowEpoch10, e2eGsEpoch, e2eGsEnc, partyEnc,
      hgs, hp, Expr.eval]

theorem cost_noAliceBelow10E_le {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (pE : Expr EOps Γ .bool) :
    (noAliceBelow10E (C := C) (K := K) (decT := decT) (encT := encT) gsE pE).cost ≤
      gsE.cost + pE.cost + 15 := by
  have hb10 : bits 10 = 4 := by decide
  simp only [noAliceBelow10E, e2eGsEpoch, Expr.cost, hb10]
  omega

@[expose] def r1CrArmC {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) :
    Comp EOps I Γ (.prod (smRT CryptoVerification.E2E.Costed.GhostStT) (e2eGsTy ℓ)) :=
  .bind (.ret (.pair gsE crArg))
    (let gs0 : Expr EOps _ (e2eGsTy ℓ) := .fst .v0
     let p0 : Expr EOps _ .bool := .snd .v0
     let refuseCond : Expr EOps _ .bool :=
       orE (e2eGsWin gs0)
         (orE (.not (e2eCorrAllowedE q gs0 p0))
           (orE (e2eInWindowE gs0 p0) (.not (noAliceBelow10E gs0 p0))))
     .ite refuseCond
       (.ret (.pair (smRCorrE .none) gs0))
       (.ret (.pair (smRCorrE (.some (pGet (e2eGsSt gs0) p0)))
         (e2eAfterCorrAllowedE gs0 p0))))

theorem r1CrArmC_queries {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (r1CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := I) q gsE crArg).queries
      w ws = 0 := by
  simp [r1CrArmC, Comp.queries]

theorem r1CrArmC_cost {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) :
    (r1CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := I) q gsE crArg).cost ≤
      gsE.cost + crArg.cost + 75 * q + 550 := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have hallow := cost_e2eCorrAllowedE_le (ℓ := ℓ) (O' := EOps) q
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hwin := cost_e2eInWindowE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hcorrOK := cost_noAliceBelow10E_le (C := C) (K := K) (decT := decT) (encT := encT)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hafter := cost_e2eAfterCorrAllowedE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  simp only [r1CrArmC, orE, pGet, e2eGsSt, e2eGsWin, cost_smRCorrE, Comp.cost, Expr.cost,
    Expr.v0] at hallow hwin hcorrOK hafter ⊢
  omega

theorem r1CrArmC_eval {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party)
    (h : SmListBounded q st)
    (hgs : gsE.eval ρ = e2eGsEnc st) (harg : crArg.eval ρ = partyEnc party) :
    (r1CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := I) q gsE crArg).eval ρ =
      Prod.map (fun st? => (none, (none, st?))) e2eGsEnc <$>
        I.liftP ((corrR (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT))
          party).run st) := by
  set cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)
  have hr1 : cfg.r1 = true := rfl
  unfold r1CrArmC corrR
  simp only [Comp.eval, Expr.eval, hgs, harg, pure_bind]
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) .bool
  set ρ₁ := Env.cons (t := t0) (e2eGsEnc st, partyEnc party) ρ
  have hAllow := eval_e2eCorrAllowedE q (.fst (Expr.v0 (O := EOps))) (.snd .v0)
    ρ₁ st party h rfl rfl
  have hInWin := eval_e2eInWindowE (.fst (Expr.v0 (O := EOps))) (.snd .v0)
    ρ₁ st party rfl rfl
  have hCorrOK :
      (noAliceBelow10E (C := C) (K := K) (decT := decT) (encT := encT)
        (.fst .v0) (.snd .v0)).eval ρ₁ = cfg.corrOK st party :=
    eval_noAliceBelow10E (.fst .v0) (.snd .v0) ρ₁ st party rfl rfl
  have hRefuse :
      (orE (e2eGsWin (.fst (Expr.v0 (O := EOps))))
        (orE (.not (e2eCorrAllowedE q (.fst .v0) (.snd .v0)))
          (orE (e2eInWindowE (.fst .v0) (.snd .v0))
            (.not (noAliceBelow10E (.fst .v0) (.snd .v0)))))).eval ρ₁ =
      (st.win || !st.corrAllowed party || (cfg.r1 && inWindow st party) ||
        !cfg.corrOK st party) := by
    simp only [orE_eval, Expr.eval, hAllow, hInWin, hCorrOK, hr1, Bool.true_and]
    simp [ρ₁, e2eGsWin, e2eGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href :
      st.win || !st.corrAllowed party || (cfg.r1 && inWindow st party) || !cfg.corrOK st party
  · simp only [href, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, liftP_pure_eq, map_pure, Prod.map]
    rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, pure_bind, liftP_pure_eq, map_pure, Prod.map]
    have hallowTrue : st.corrAllowed party = true := by
      cases hc : st.corrAllowed party
      · simp [hc] at href
      · rfl
    have hAfter := eval_e2eAfterCorrAllowedE (.fst (Expr.v0 (O := EOps))) (.snd .v0)
      ρ₁ st party hallowTrue rfl rfl
    have hpGet := pGet_eval (e2eGsSt (.fst (Expr.v0 (O := EOps)))) (.snd .v0)
      ρ₁ st.st party rfl rfl
    simp only [eval_smRCorrE, some_eval, hpGet, hAfter]

end CrArmE2E

end Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Init
