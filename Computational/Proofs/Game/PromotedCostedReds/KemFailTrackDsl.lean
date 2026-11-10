/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux -- proof-setup: allow-public-import
public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
public import LibsignalBinary.Specifications.LibsignalE2E.State
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Msg
import Computational.Proofs.E2E.Dsl.ClampsLossless
import Computational.Proofs.E2E.Dsl.SpqrSimChain

/-!
# Per-Session KEM-Failure Tracker Gadget

Re-exports the polymorphic tracker combinators and cost/size bounds from `KemFailTrackDslBase`
and proves `.eval` characterizations across `KemTrackOpEmbed` (`kemTrackOps`,
`atomicSessionOps`, and `atomicE2EOps`).
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDsl

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp
  partyToBool bytesToWordLE spqrMsgPayloadSuffix
  atomicSig AtomicPureOp AtomicSpqrKemOp B BV256 BV512 U32 U64 fig8CtT fig8CtV
  recvResultT recvResultEnc)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (RecvResult)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.Ratchet.LibsignalSim (SimBraidSt SimKemSeed
  SimKemEncRand SimKemCoins SimKemFailTrack SimFig8C simEncRandOf simEkSideIsA
  simNextKemCoins simInitKemFailTrack simStepKemFailSend simStepKemFailDeliver)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State coinBytes coinBytes_length encode_varint)
open CryptoVerification.SpqrV1Sync.SendTotal (BOkTight)
open CryptoVerification.E2E (Bytes)

open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (trE_e trE_c trE_st trE_sentB trE_sendCtr trE_cand trCandIsSomeE trMk pGet pSet
   boolOrE boolEqE bytes2EqLitE issue1275ScanStepE swapPairsStep64E swapChunk64StepC
   initV1BraidStE encRandBvE isKeysUnsampledV1E isHeaderReceivedV1E
   ekSideIsAE nextKemCoinsE nextKemCandC stepPostKemSendE b64Take48ToB32E)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux
  (coinBytes_bytesToWordLE512 keyToBytes32_bytesToWordLE256
   bytesToWordLE512_coinBytes bytesToWordLE256_keyToBytes32)

export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (kemTrackOps KemTrackOpEmbed baseEmbed sessionEmbed e2eEmbed)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (kemCoinsT kemSentEntryT kemTrackT honestWireEntryT kemSessionTrackT)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (kemCandVecToBv kemCandBvToVec kemCoinsAtomicEnc kemTrackAtomicEnc honestPairEnc)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (SimKemSessionTrack simInitKemSessionTrack kemSessionTrackAtomicEnc)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (issue1275FixEsC honestExchangeFailsC initKemFailTrackE initKemFailSessionTrackE)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (stepKemFailSendPairC stepKemFailSendC prependHonestWireE listNthOptB)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (findRevHonestWireIdxE findRevHonestIdxE stepKemFailDeliverE stepKemFailDeliverC)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (stepKemSessionDeliverOptE kemOnDeliverPostE)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (initKemFailTrackPolyE initKemFailSessionTrackPolyE stepKemFailSendPairPolyC stepKemFailSendPolyC)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (stepKemFailDeliverPolyE stepKemFailDeliverPolyC stepKemSessionDeliverOptPolyE kemOnDeliverPostPolyE)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (findRevHonestWireIdxPolyE findRevHonestIdxPolyE initKemFailTrackE2EE initKemFailSessionTrackE2EE)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (stepKemFailSendE2EC stepKemFailDeliverE2EE stepKemSessionDeliverOptE2EE findRevHonestWireIdxE2EE)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (issue1275FixEsC_queries_zero honestExchangeFailsC_queries_zero honestExchangeFailsC_nq_zero)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (stepKemFailSendPairC_queries_zero stepKemFailSendPairC_nq_zero stepKemFailSendC_queries_zero stepKemFailSendC_nq_zero)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (stepKemFailDeliverC_queries_zero stepKemFailDeliverC_nq_zero issue1275FixEsC_cost_le honestExchangeFailsC_cost_le)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (initKemFailTrackE_cost_le initKemFailSessionTrackE_cost_le stepKemFailSendPairC_cost_le stepKemFailSendC_cost_le)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (prependHonestWireE_cost listNthOptB_cost_le findRevHonestWireIdxE_cost_le findRevHonestIdxE_cost_le)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (stepKemFailDeliverE_cost_le stepKemFailDeliverC_cost_le stepKemSessionDeliverOptE_cost_le kemOnDeliverPostE_cost_le)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (issue1275FixEsC_size_le honestExchangeFailsC_size_le initKemFailTrackE_size_le initKemFailSessionTrackE_size_le)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (stepKemFailSendPairC_size_le stepKemFailSendC_size_le prependHonestWireE_size listNthOptB_size_le)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (findRevHonestWireIdxE_size_le findRevHonestIdxE_size_le stepKemFailDeliverE_size_le stepKemFailDeliverC_size_le)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (stepKemSessionDeliverOptE_size_le kemOnDeliverPostE_size_le)

export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux
  (kemBridgeCoinsToSim kemCandBvToVec_kemCandVecToBv kemCandVecToBv_kemCandBvToVec)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux
  (KemTrackDeliverInv kemTrackDeliverInv_initSim kemTrackDeliverInv_stepDeliverSim kemTrackDeliverInv_stepSendSim)
export Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux
  (issue1275FixEsC_eval honestExchangeFailsC_eval)

section EvalProofs

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} {C : Crypto} {K : MlKem} {O : Ops (atomicSig ℓ Pt)}

local notation "ASig" => atomicSig ℓ Pt

@[simp] private theorem env_get_zero {Γ : List (Ty ASig)} {t : Ty ASig} (v : t.denote) (ρ : Env Γ) :
    (Env.cons v ρ).get .zero = v := rfl

@[simp] private theorem env_get_succ {Γ : List (Ty ASig)} {t u : Ty ASig} (v : t.denote) (ρ : Env Γ)
    (i : Var Γ u) : (Env.cons v ρ).get (.succ i) = ρ.get i := rfl

theorem initV1BraidStE_eval (emb : KemTrackOpEmbed ℓ Pt C K O) (isAlice : Bool)
    {Γ : List (Ty ASig)} (pqrKeyE : Expr O Γ BV256) (ρ : Env Γ) :
    (initV1BraidStE emb isAlice pqrKeyE).eval ρ =
      V1State.encodeRaw
        (((simInitKemFailTrack C.F (pqrKeyE.eval ρ)).st (if isAlice then .A else .B)).into_pb) := by
  have hop : (emb.spqrE .spqrNegotiateInit
      (.pair (emb.pureE (.u8Lit 1#8) .unit)
        (.pair (emb.pureE (.u32Lit (if isAlice then 0#32 else 1#32)) .unit)
          (emb.pureE .bv256ToBytes32 pqrKeyE)))).eval ρ =
    (false, some (some (V1State.encodeRaw
      (((simInitKemFailTrack C.F (pqrKeyE.eval ρ)).st (if isAlice then .A else .B)).into_pb)))) := by
    simp only [emb.eval_spqrE, emb.eval_pureE, Expr.eval, AtomicPureOp.eval, AtomicSpqrKemOp.eval]
    have hEq : _root_.ReductionDsl.spqrNegotiateInitEval (ℓ := ℓ) (Pt := Pt) C.F K 1#8
        (if isAlice then 0#32 else 1#32) (keyToBytes32 (pqrKeyE.eval ρ)) =
      CryptoVerification.E2E.Costed.spqrNegotiateInitEval (ℓ := ℓ) C.F K 1#8
        (if isAlice then 0#32 else 1#32) (keyToBytes32 (pqrKeyE.eval ρ)) := rfl
    rw [hEq, Computational.Proofs.E2E.Dsl.ClampsLossless.spqrNegotiateInitEval_clamp_lossless]
    have hv : CryptoVerification.LibsignalSpqrV1.Version.fromU8? 1#8 = some .v1 := rfl
    cases isAlice
    · have hd : CryptoVerification.LibsignalSpqrV1.Direction.fromI32?
          (if false = true then 0#32 else 1#32) = some .b2a := rfl
      have hdec : CryptoVerification.LibsignalSpqrV1.spqrPolyApi.decoder_new 96 =
          .ok (.ok (CryptoVerification.SpqrV1Sync.InSync.freshDec 96)) := by
        simp only [CryptoVerification.LibsignalSpqrV1.spqrPolyApi,
          CryptoVerification.SpqrV1Sync.InSync.decoderNew_eq 96 (by decide), Except.mapError]
      have hinit : CryptoVerification.LibsignalSpqrV1.initInner
          (CryptoVerification.LibsignalSpqrV1.spqrDeps C.F K) .v1 .b2a
          (keyToBytes32 (pqrKeyE.eval ρ)) =
          .ok (some (((simInitKemFailTrack C.F (pqrKeyE.eval ρ)).st .B).into_pb)) := by
        unfold CryptoVerification.LibsignalSpqrV1.initInner
        dsimp only [CryptoVerification.LibsignalSpqrV1.spqrDeps,
          CryptoVerification.LibsignalSpqrV1.spqrAuthApi,
          CryptoVerification.LibsignalSpqrV1.States.init_b,
          CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.new,
          CryptoVerification.LibsignalSpqrV1.HEADER_SIZE,
          CryptoVerification.LibsignalSpqrV1.AUTHENTICATOR_MACSIZE]
        rw [hdec]; rfl
      unfold Computational.Proofs.E2E.Dsl.ClampsLossless.spqrNegotiateInitRaw
      rw [hv, hd]; dsimp only; rw [hinit]; rfl
    · have hd : CryptoVerification.LibsignalSpqrV1.Direction.fromI32?
          (if true = true then 0#32 else 1#32) = some .a2b := rfl
      have hinit : CryptoVerification.LibsignalSpqrV1.initInner
          (CryptoVerification.LibsignalSpqrV1.spqrDeps C.F K) .v1 .a2b
          (keyToBytes32 (pqrKeyE.eval ρ)) =
          .ok (some (((simInitKemFailTrack C.F (pqrKeyE.eval ρ)).st .A).into_pb)) := rfl
      unfold Computational.Proofs.E2E.Dsl.ClampsLossless.spqrNegotiateInitRaw
      rw [hv, hd]; dsimp only; rw [hinit]; rfl
  dsimp only [initV1BraidStE, Expr.eval]
  rw [hop]; rfl

theorem initKemFailTrackE_eval (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (pqrKeyE : Expr O Γ BV256) (ρ : Env Γ) :
    (initKemFailTrackE emb pqrKeyE).eval ρ =
      kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (simInitKemFailTrack C.F (pqrKeyE.eval ρ)) := by
  dsimp only [initKemFailTrackE, Expr.eval]
  rw [initV1BraidStE_eval, initV1BraidStE_eval]
  simp [emb.eval_pureE, AtomicPureOp.eval, Expr.v0, Expr.eval,
    kemTrackAtomicEnc, kemCoinsAtomicEnc, simInitKemFailTrack]

theorem initKemFailSessionTrackE_eval (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (pqrKeyE : Expr O Γ BV256) (ρ : Env Γ) :
    (initKemFailSessionTrackE emb pqrKeyE).eval ρ =
      kemSessionTrackAtomicEnc (ℓ := ℓ) (Pt := Pt)
        (simInitKemSessionTrack C.F Bytes (pqrKeyE.eval ρ)) := by
  simp [initKemFailSessionTrackE, Expr.eval, initKemFailTrackE_eval,
    kemSessionTrackAtomicEnc, simInitKemSessionTrack]

private theorem isKeysUnsampledV1E_eval (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (v1E : Expr O Γ (B 32)) (ρ : Env Γ) (st : SimBraidSt C.F)
    (hv1 : v1E.eval ρ = V1State.encodeRaw st.into_pb) :
    (isKeysUnsampledV1E emb v1E).eval ρ =
      (match st with | .keysUnsampled _ => true | _ => false) := by
  have hp1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  simp only [isKeysUnsampledV1E, Expr.eval, hv1, emb.eval_pureE, AtomicPureOp.eval, hp1]
  cases st <;>
    (simp [CryptoVerification.LibsignalSpqrV1.States.into_pb, V1State.encodeRaw,
      V1State.InnerState.encode, CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeKey,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux,
      CryptoVerification.LibsignalSpqrV1.Proto.WireType.toU32];
     try (rintro h; injection h with h1; exact absurd h1 (by decide)))

private theorem isHeaderReceivedV1E_eval (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (v1E : Expr O Γ (B 32)) (ρ : Env Γ) (st : SimBraidSt C.F)
    (hv1 : v1E.eval ρ = V1State.encodeRaw st.into_pb) :
    (isHeaderReceivedV1E emb v1E).eval ρ =
      (match st with | .headerReceived _ => true | _ => false) := by
  have hp1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  simp only [isHeaderReceivedV1E, Expr.eval, hv1, emb.eval_pureE, AtomicPureOp.eval, hp1]
  cases st <;>
    (simp [CryptoVerification.LibsignalSpqrV1.States.into_pb, V1State.encodeRaw,
      V1State.InnerState.encode, CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeKey,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux,
      CryptoVerification.LibsignalSpqrV1.Proto.WireType.toU32];
     try (rintro h; injection h with h1; exact absurd h1 (by decide)))

private theorem bytesToWordLE256_eq_bytesToKey32 (bs : Bytes) :
    bytesToWordLE 256 bs = bytesToKey32 bs := by
  induction bs with
  | nil => rfl
  | cons b tl ih =>
    change (bytesToWordLE 256 tl <<< 8) ||| b.zeroExtend 256 =
      (bytesToKey32 tl <<< 8) ||| b.zeroExtend 256
    rw [ih]

private theorem encRandBvE_eval (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (rqE : Expr O Γ BV512) (ρ : Env Γ) (rq : BitVec 512) (hrq : rqE.eval ρ = rq) :
    (encRandBvE emb rqE).eval ρ = bytesToWordLE 256 (simEncRandOf rq).toList := by
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  simp only [encRandBvE, hrq, emb.eval_pureE, AtomicPureOp.eval, hp32, simEncRandOf]
  exact (bytesToWordLE256_eq_bytesToKey32 ((coinBytes rq).take 32)).symm

private theorem keyToBytesVec32_simEncRandOf (rq : BitVec 512) :
    keyToBytesVec32 (bytesToWordLE 256 (simEncRandOf rq).toList) = simEncRandOf rq :=
  Subtype.ext (keyToBytes32_bytesToWordLE256 _ (simEncRandOf rq).2)

private theorem eval_pGet_party {Γ : List (Ty ASig)} {t : Ty ASig}
    (pE : Expr O Γ (.prod t t)) (qE : Expr O Γ .bool) (ρ : Env Γ)
    (f : Party → t.denote) (Q : Party)
    (hp : pE.eval ρ = (f .A, f .B)) (hq : qE.eval ρ = partyToBool Q) :
    (pGet pE qE).eval ρ = f Q := by
  cases Q <;> simp [pGet, Expr.eval, hp, hq, partyToBool]

private theorem eval_pSet_party {Γ : List (Ty ASig)} {t : Ty ASig}
    (pE : Expr O Γ (.prod t t)) (qE : Expr O Γ .bool) (vE : Expr O Γ t) (ρ : Env Γ)
    (f : Party → t.denote) (Q : Party) (v : t.denote)
    (hp : pE.eval ρ = (f .A, f .B)) (hq : qE.eval ρ = partyToBool Q) (hv : vE.eval ρ = v) :
    (pSet pE qE vE).eval ρ = (Function.update f Q v .A, Function.update f Q v .B) := by
  cases Q <;> simp [pSet, Expr.eval, Expr.v0, hp, hq, hv, partyToBool, Function.update]

private theorem nextKemCoinsE_eval (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (cE : Expr O Γ (kemCoinsT ℓ Pt)) (v1QE : Expr O Γ (B 32))
    (rqE : Expr O Γ BV512) (ρ : Env Γ)
    (c : SimKemCoins) (stQ : SimBraidSt C.F) (rq : BitVec 512)
    (hc : cE.eval ρ = kemCoinsAtomicEnc c)
    (hv1 : v1QE.eval ρ = V1State.encodeRaw stQ.into_pb)
    (hrq : rqE.eval ρ = rq) :
    (nextKemCoinsE emb cE v1QE rqE).eval ρ =
      kemCoinsAtomicEnc (simNextKemCoins C.F c stQ (coinBytes rq)) := by
  simp only [nextKemCoinsE, Expr.eval, hc, hv1, hrq]
  rcases c with _ | ⟨s⟩ | ⟨s, r⟩
  · simp only [kemCoinsAtomicEnc, Expr.eval, Expr.v0, Expr.v1, Env.get]
    rw [isKeysUnsampledV1E_eval emb _ _ stQ (by simp [Expr.eval])]
    cases stQ <;>
      simp [simNextKemCoins, coinBytes_length, List.take_of_length_le, bytesToWordLE512_coinBytes]
  · simp only [kemCoinsAtomicEnc, Expr.eval, Expr.v0, Expr.v2, Env.get]
    rw [isHeaderReceivedV1E_eval emb _ _ stQ (by simp [Expr.eval])]
    cases stQ <;> simp [simNextKemCoins, coinBytes_length]
    exact encRandBvE_eval emb _ _ rq (by simp [Expr.eval])
  · simp only [kemCoinsAtomicEnc, Expr.eval, Expr.v0, Env.get]
    cases stQ <;> simp [simNextKemCoins]

private def simNextKemCand (tr : SimKemFailTrack C.F) (Q : Party) (r : BitVec 512) :
    Option (SimKemSeed × SimKemEncRand) :=
  match tr.cand with
  | some p => some p
  | none =>
    if simEkSideIsA tr.e != (Q == .A) then
      match tr.c, tr.st Q with
      | .seed s, .headerReceived _ =>
        if K.honestExchangeFails s (simEncRandOf r) then some (s, simEncRandOf r) else none
      | _, _ => none
    else none

private theorem nextKemCandC_eval (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (rqE : Expr O Γ BV512) (ρ : Env Γ)
    (tr : SimKemFailTrack C.F) (Q : Party) (rq : BitVec 512)
    (htr : trE.eval ρ = kemTrackAtomicEnc tr) (hqB : qBE.eval ρ = partyToBool Q)
    (hrq : rqE.eval ρ = rq) :
    (nextKemCandC emb (I := I) trE qBE rqE).eval ρ =
      pure ((simNextKemCand (C := C) (K := K) tr Q rq).map kemCandVecToBv) := by
  simp only [nextKemCandC, Comp.eval, Expr.eval, htr, hqB, hrq, pure_bind]
  set p0 : (Ty.prod (kemTrackT ℓ Pt) (Ty.prod .bool BV512)).denote :=
    (kemTrackAtomicEnc tr, (partyToBool Q, rq))
  rcases hCand : tr.cand with _ | candVal
  · have hCandE : (trE_cand (O := O) (.fst .v0)).eval (.cons p0 ρ) = none := by
      simp [trE_cand, p0, kemTrackAtomicEnc, hCand, Expr.eval, Expr.v0]
    simp only [hCandE, simNextKemCand, hCand]
    have hv1Q : (pGet (trE_st (O := O) (.fst .v0)) (.fst (.snd .v0))).eval (.cons p0 ρ) =
        V1State.encodeRaw (tr.st Q).into_pb :=
      eval_pGet_party (t := B 32) _ _ _ (fun P => V1State.encodeRaw (tr.st P).into_pb) Q
        (by simp [trE_st, p0, kemTrackAtomicEnc, Expr.eval, Expr.v0])
        (by simp [p0, Expr.eval, Expr.v0])
    have hEkEq : (boolEqE (ekSideIsAE emb (trE_e (.fst .v0))) (.fst (.snd .v0))).eval (.cons p0 ρ) =
        (simEkSideIsA tr.e != (Q == .A)) := by
      simp only [boolEqE, ekSideIsAE, trE_e, p0, kemTrackAtomicEnc, Expr.eval, Expr.v0, Env.get,
        emb.eval_pureE, AtomicPureOp.eval, simEkSideIsA]
      cases Q <;> cases decide (tr.e.toNat % 2 = 1) <;> rfl
    simp only [hEkEq, isHeaderReceivedV1E_eval emb _ _ (tr.st Q) hv1Q]
    cases hSide : (simEkSideIsA tr.e != (Q == .A))
    · simp
    · simp only [Bool.true_and, ↓reduceIte]
      generalize tr.st Q = stQ at hv1Q ⊢
      rcases stQ with _ | _ | _ | _ | _ | _ | _ | hdrSt | _ | _ | _ | _ <;>
        try (rcases tr.c with _ | _ | _ <;> (simp; done))
      rcases hC : tr.c with _ | ⟨s⟩ | ⟨s, r0⟩
      · simp [trE_c, p0, kemTrackAtomicEnc, hC, kemCoinsAtomicEnc, Expr.eval, Expr.v0]
      · set sBv : (BV512 (ℓ := ℓ) (Pt := Pt)).denote := bytesToWordLE 512 s.toList
        set sInl : (Ty.sum (S := ASig) BV512 (.prod BV512 BV256)).denote := Sum.inl sBv
        have hTrC : (trE_c (O := O) (.fst .v0)).eval (.cons p0 ρ) = Sum.inr sInl := by
          simp [trE_c, p0, kemTrackAtomicEnc, hC, kemCoinsAtomicEnc, sInl, sBv, Expr.eval, Expr.v0]
        have hV0Inl : (Expr.v0 : Expr O _ _).eval (.cons sInl (.cons p0 ρ)) = Sum.inl sBv := by
          simp [sInl, Expr.eval, Expr.v0]
        simp only [hTrC, hV0Inl]
        have hHef : (honestExchangeFailsC emb (I := I) .v0
            (encRandBvE emb (.snd (.snd .v2)))).eval (.cons sBv (.cons sInl (.cons p0 ρ))) =
            pure (K.honestExchangeFails s (simEncRandOf rq)) := by
          rw [honestExchangeFailsC_eval emb _ _ _ sBv (bytesToWordLE 256 (simEncRandOf rq).toList)
            (by simp [Expr.eval, Expr.v0])
            (encRandBvE_eval emb _ _ rq (by simp [p0, Expr.eval, Expr.v2]))]
          have hsVec : (⟨coinBytes sBv, coinBytes_length _⟩ : List.Vector (BitVec 8) 64) = s :=
            Subtype.ext (coinBytes_bytesToWordLE512 s.toList s.2)
          rw [hsVec, keyToBytesVec32_simEncRandOf rq]
        rw [hHef, pure_bind]
        have hRand3 (b : Ty.bool.denote) :
            (encRandBvE emb (.snd (.snd .v3))).eval
              (.cons b (.cons sBv (.cons sInl (.cons p0 ρ)))) =
            bytesToWordLE 256 (simEncRandOf rq).toList :=
          encRandBvE_eval emb _ _ rq (by simp [p0, Expr.eval, Expr.v3])
        cases K.honestExchangeFails s (simEncRandOf rq) <;>
          simp [sBv, Expr.eval, Expr.v0, Expr.v1, hRand3, kemCandVecToBv]
      · simp [trE_c, p0, kemTrackAtomicEnc, hC, kemCoinsAtomicEnc, Expr.eval, Expr.v0]
  · simp [trE_cand, p0, kemTrackAtomicEnc, hCand, simNextKemCand, Expr.eval, Expr.v0]

private theorem simStepKemFailSend_eq (tr : SimKemFailTrack C.F) (Q : Party) (r : BitVec 512) :
    simStepKemFailSend C.F K tr Q r =
      let cand' := simNextKemCand (C := C) (K := K) tr Q r
      let tape := coinBytes r
      match (tr.st Q).send K tape with
      | .ok (out, _) =>
        let E := out.msg.epoch.toNat - 1
        let n := tr.sendCtr Q E
        { tr with
          c := simNextKemCoins C.F tr.c (tr.st Q) tape
          st := Function.update tr.st Q out.state
          sentB := tr.sentB ++ [(out.msg, BitVec.ofNat 32 (n + 1))]
          sendCtr := Function.update tr.sendCtr Q (Function.update (tr.sendCtr Q) E (n + 1))
          cand := cand' }
      | .error _ => { tr with cand := cand' } := by
  simp only [simStepKemFailSend, simNextKemCand]
  rcases (tr.st Q).send K (coinBytes r) with _ | ⟨out, _⟩ <;> (
    dsimp only; congr 1
    rcases tr.cand with _ | _
    · by_cases hS : (simEkSideIsA tr.e != (Q == .A)) = true
      · simp only [hS, ↓reduceIte]; rcases tr.c with _ | _ | _ <;> rcases tr.st Q <;> rfl
      · simp [hS]
    · rfl)

theorem stepKemFailSendPairC_eval (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (rqE : Expr O Γ BV512) (ρ : Env Γ)
    (tr : SimKemFailTrack C.F) (Q : Party) (rq : BitVec 512)
    (htr : trE.eval ρ = kemTrackAtomicEnc tr) (hqB : qBE.eval ρ = partyToBool Q)
    (hrq : rqE.eval ρ = rq)
    (hBOk : BOkTight (tr.st Q)) (hSentLen : tr.sentB.length ≤ q) :
    (stepKemFailSendPairC emb q (I := I) trE qBE rqE).eval ρ =
      let tr' := simStepKemFailSend C.F K tr Q rq
      pure (kemTrackAtomicEnc tr', kemTrackAtomicEnc { tr with cand := tr'.cand }) := by
  simp only [stepKemFailSendPairC, Comp.eval, Expr.eval, htr, hqB, hrq, pure_bind]
  set p0 : (Ty.prod (kemTrackT ℓ Pt) (Ty.prod .bool BV512)).denote :=
    (kemTrackAtomicEnc tr, (partyToBool Q, rq))
  rw [nextKemCandC_eval emb _ _ _ (.cons p0 ρ) tr Q rq
    (by simp [p0, Expr.eval, Expr.v0])
    (by simp [p0, Expr.eval, Expr.v0])
    (by simp [p0, Expr.eval, Expr.v0]), pure_bind]
  set cand' := simNextKemCand (C := C) (K := K) tr Q rq
  set candBvD : (Ty.opt (Ty.prod (S := ASig) BV512 BV256)).denote := cand'.map kemCandVecToBv
  set ρ0 := Env.cons candBvD (.cons p0 ρ)
  set pPost : (Ty.prod (kemTrackT ℓ Pt)
      (Ty.prod .bool (Ty.prod BV512 (.opt (.prod BV512 BV256))))).denote :=
    (kemTrackAtomicEnc tr, (partyToBool Q, (rq, candBvD)))
  have hTup1 : ((Expr.v1 : Expr O _ _).eval ρ0).1 = kemTrackAtomicEnc tr := rfl
  have hTup2 : ((Expr.v1 : Expr O _ _).eval ρ0).2.1 = partyToBool Q := rfl
  have hTup3 : ((Expr.v1 : Expr O _ _).eval ρ0).2.2 = rq := rfl
  have hTup4 : (Expr.v0 : Expr O _ _).eval ρ0 = candBvD := rfl
  have hpPost_eq : (kemTrackAtomicEnc tr, (partyToBool Q, (rq, candBvD))) = pPost := rfl
  dsimp only [stepPostKemSendE, Expr.eval]
  rw [hTup1, hTup2, hTup3, hTup4, hpPost_eq]
  have hv1Q : (pGet (trE_st (O := O) (.fst .v0)) (.fst (.snd .v0))).eval (.cons pPost ρ0) =
      V1State.encodeRaw (tr.st Q).into_pb :=
    eval_pGet_party (t := B 32) _ _ _ (fun P => V1State.encodeRaw (tr.st P).into_pb) Q
      (by simp [trE_st, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v0])
      (by simp [pPost, Expr.eval, Expr.v0])
  have hOptEval : ((emb.spqrE .spqrBraidSend
      (.pair (pGet (trE_st (.fst .v0)) (.fst (.snd .v0))) (.fst (.snd (.snd .v0))))).eval
      (.cons pPost ρ0)).2 =
      (_root_.ReductionDsl.spqrBraidSendEval (ℓ := ℓ) (Pt := Pt) C.F K
        (V1State.encodeRaw (tr.st Q).into_pb) rq).2 := by
    simp only [Expr.eval, emb.eval_spqrE, AtomicSpqrKemOp.eval]
    rw [hv1Q]; simp [pPost, Expr.eval, Expr.v0]
  have hSendEq : _root_.ReductionDsl.spqrBraidSendEval (ℓ := ℓ) (Pt := Pt) C.F K
      (V1State.encodeRaw (tr.st Q).into_pb) rq =
      CryptoVerification.E2E.Costed.spqrBraidSendEval (ℓ := ℓ) C.F K
        (V1State.encodeRaw (tr.st Q).into_pb) rq := rfl
  rw [hOptEval, hSendEq,
    Computational.Proofs.E2E.Dsl.SpqrSimChain.spqrBraidSendEval_of_bOkTight C.F K (tr.st Q) hBOk rq,
    simStepKemFailSend_eq (C := C) (K := K) tr Q rq]
  dsimp only
  rcases hSend : (tr.st Q).send K (coinBytes rq) with ⟨err⟩ | ⟨out, tape'⟩
  · cases err <;>
      simp [trMk, trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr, pPost, candBvD, cand',
        kemTrackAtomicEnc, Expr.eval, Expr.v0]
  · dsimp only
    set sOutD : (Ty.prod (B (ℓ := ℓ) (Pt := Pt) 32)
        (Ty.prod U64 (Ty.prod (.opt (.prod U64 BV256)) (B (ℓ := ℓ) (Pt := Pt) 64)))).denote :=
      (V1State.encodeRaw out.state.into_pb, (out.msg.epoch,
        (out.key.map (fun es => (es.epoch, bytesToKey32 es.secret)),
          spqrMsgPayloadSuffix out.msg)))
    set ρS := Env.cons sOutD (.cons pPost ρ0)
    have hsOut_eq : (V1State.encodeRaw out.state.into_pb, (out.msg.epoch,
        (out.key.map (fun es => (es.epoch, bytesToKey32 es.secret)),
          CryptoVerification.E2E.Costed.spqrMsgPayloadSuffix out.msg))) = sOutD := rfl
    have hρS_eq : Env.cons sOutD (Env.cons pPost ρ0) = ρS := rfl
    rw [hsOut_eq, hρS_eq]
    have hv1Q1 : (pGet (trE_st (O := O) (.fst .v1)) (.fst (.snd .v1))).eval ρS =
        V1State.encodeRaw (tr.st Q).into_pb :=
      eval_pGet_party (t := B 32) _ _ _ (fun P => V1State.encodeRaw (tr.st P).into_pb) Q
        (by simp [trE_st, ρS, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v1])
        (by simp [ρS, pPost, Expr.eval, Expr.v1])
    have hCtrQ : (pGet (trE_sendCtr (O := O) (.fst .v1)) (.fst (.snd .v1))).eval ρS =
        tr.sendCtr Q :=
      eval_pGet_party (trE_sendCtr (O := O) (.fst .v1)) _ _ tr.sendCtr Q
        (by simp [trE_sendCtr, ρS, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v1])
        (by simp [ρS, pPost, Expr.eval, Expr.v1])
    have hC' : (nextKemCoinsE emb (trE_c (.fst .v1))
        (pGet (trE_st (.fst .v1)) (.fst (.snd .v1))) (.fst (.snd (.snd .v1)))).eval ρS =
        kemCoinsAtomicEnc (simNextKemCoins C.F tr.c (tr.st Q) (coinBytes rq)) :=
      nextKemCoinsE_eval emb _ _ _ ρS tr.c (tr.st Q) rq
        (by simp [trE_c, ρS, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v1]) hv1Q1
        (by simp [ρS, pPost, Expr.eval, Expr.v1])
    have hSt' : (pSet (trE_st (O := O) (.fst .v1)) (.fst (.snd .v1)) (.fst .v0)).eval ρS =
        (V1State.encodeRaw (Function.update tr.st Q out.state .A).into_pb,
         V1State.encodeRaw (Function.update tr.st Q out.state .B).into_pb) := by
      have hSet0 := eval_pSet_party (O := O) (t := B 32)
        (trE_st (.fst .v1)) (.fst (.snd .v1)) (.fst .v0) ρS
        (fun P => V1State.encodeRaw (tr.st P).into_pb) Q (V1State.encodeRaw out.state.into_pb)
        (by simp [trE_st, ρS, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v1])
        (by simp [ρS, pPost, Expr.eval, Expr.v1])
        (by simp [ρS, sOutD, Expr.eval, Expr.v0])
      rw [hSet0]; cases Q <;> simp [Function.update]
    simp only [trMk, Expr.eval, hC', hSt', hCtrQ, emb.eval_pureE, AtomicPureOp.eval]
    simp only [pSet, Expr.eval, hCtrQ, emb.eval_pureE, AtomicPureOp.eval]
    have hTake : (List.map (fun x => ((x.1.epoch, spqrMsgPayloadSuffix x.1), x.2))
        tr.sentB ++ [((out.msg.epoch, spqrMsgPayloadSuffix out.msg),
          BitVec.ofNat 32 (tr.sendCtr Q (out.msg.epoch.toNat - 1) + 1))]).take (q + 1) =
        List.map (fun x => ((x.1.epoch, spqrMsgPayloadSuffix x.1), x.2))
          (tr.sentB ++ [(out.msg, BitVec.ofNat 32 (tr.sendCtr Q (out.msg.epoch.toNat - 1) + 1))]) := by
      rw [List.take_of_length_le (by simp; omega), List.map_append]; rfl
    cases Q <;> (
      simp [ρS, sOutD, pPost, candBvD, cand', trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr,
        partyToBool, kemTrackAtomicEnc, Expr.eval, Expr.v0, Expr.v1, hTake, Function.update]
      ext j; by_cases hj : j = out.msg.epoch.toNat - 1 <;> simp [hj, Function.update])

theorem stepKemFailSendC_eval (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (rqE : Expr O Γ BV512) (ρ : Env Γ)
    (tr : SimKemFailTrack C.F) (Q : Party) (rq : BitVec 512)
    (htr : trE.eval ρ = kemTrackAtomicEnc tr) (hqB : qBE.eval ρ = partyToBool Q)
    (hrq : rqE.eval ρ = rq)
    (hBOk : BOkTight (tr.st Q)) (hSentLen : tr.sentB.length ≤ q) :
    (stepKemFailSendC emb q (I := I) trE qBE rqE).eval ρ =
      let tr' := simStepKemFailSend C.F K tr Q rq
      pure (tr'.cand.isSome,
        if tr'.cand.isSome then kemTrackAtomicEnc { tr with cand := tr'.cand }
        else kemTrackAtomicEnc tr') := by
  dsimp only [stepKemFailSendC, Comp.eval]
  rw [stepKemFailSendPairC_eval emb q trE qBE rqE ρ tr Q rq htr hqB hrq hBOk hSentLen, pure_bind]
  set tr' := simStepKemFailSend C.F K tr Q rq
  rcases hC : tr'.cand with _ | candVal <;>
    simp [trCandIsSomeE, trE_cand, kemTrackAtomicEnc, hC, Expr.eval, Expr.v0]

theorem prependHonestWireE_eval {Γ : List (Ty ASig)}
    (trOutE : Expr O Γ (kemTrackT ℓ Pt)) (hwE : Expr O Γ (.list (honestWireEntryT ℓ Pt)))
    (wE : Expr O Γ (B 32)) (pBE : Expr O Γ .bool) (ρ : Env Γ)
    (trOut : SimKemFailTrack C.F) (hw : List (Bytes × Party)) (w : Bytes) (P : Party)
    (htr : trOutE.eval ρ = kemTrackAtomicEnc trOut)
    (hhw : hwE.eval ρ = hw.map fun (x, Q) => (x, partyToBool Q))
    (hwv : wE.eval ρ = w) (hp : pBE.eval ρ = partyToBool P) :
    (prependHonestWireE trOutE hwE wE pBE).eval ρ =
      kemSessionTrackAtomicEnc (trOut, (w, P) :: hw) := by
  simp [prependHonestWireE, kemSessionTrackAtomicEnc, Expr.eval, htr, hhw, hwv, hp]

private theorem foldr_len_aux {α : Type} :
    ∀ (ys : List α), ys.foldr (fun _ (acc : ℕ) => 1 + acc) 0 = ys.length
  | [] => rfl
  | _ :: rest => by simp only [List.foldr_cons, foldr_len_aux rest, List.length_cons]; omega

private theorem foldr_nthOpt_aux {α : Type} (idx : ℕ) :
    ∀ (ys : List α) (off : ℕ),
      ys.foldr (fun y (p : ℕ × Option α) =>
        (p.1 - 1, if decide (p.1 - 1 = idx) = true then some y else p.2)) (off + ys.length, none) =
        (off, if off ≤ idx then ys[idx - off]? else none)
  | [], _ => by simp
  | y :: rest, off => by
    have hlen : off + (y :: rest).length = (off + 1) + rest.length := by simp; omega
    simp only [List.foldr_cons, hlen, foldr_nthOpt_aux idx rest (off + 1), Nat.add_sub_cancel]
    by_cases heq : off = idx
    · subst heq; simp
    · by_cases hle : off ≤ idx
      · have hle' : off + 1 ≤ idx := by omega
        have hidx : idx - off = (idx - (off + 1)) + 1 := by omega
        simp [heq, hle, hle', hidx]
      · have hle' : ¬ (off + 1 ≤ idx) := by omega
        simp [heq, hle, hle']

theorem listNthOptB_eval (L : ℕ) {t : Ty ASig} {Γ : List (Ty ASig)}
    (xsE : Expr O Γ (.list t)) (jE : Expr O Γ .nat) (ρ : Env Γ)
    (xs : List t.denote) (j : ℕ) (hxs : xsE.eval ρ = xs) (hj : jE.eval ρ = j)
    (hlen : xs.length ≤ L) :
    (listNthOptB L xsE jE).eval ρ = xs[j]? := by
  have htake : xs.take L = xs := List.take_of_length_le hlen
  have haux := foldr_nthOpt_aux j xs 0
  simp only [Nat.zero_add, Nat.zero_le, ↓reduceIte, Nat.sub_zero] at haux
  simp only [listNthOptB, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get,
    hxs, hj, htake, foldr_len_aux, haux]

private def stepRevIdx {α : Type} (p : α → Bool) (x : α) (acc : Option ℕ × ℕ) : Option ℕ × ℕ :=
  (match acc.1 with | none => if p x then some acc.2 else none | some k => some k, acc.2 + 1)

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
      rcases rest.findIdx? p with _ | m <;> simp; omega
    · have hs : stepRevIdx p y (none, k) = (some k, k + 1) := by simp [stepRevIdx, hp]
      rw [hs, foldl_stepRevIdx_some p rest k (k + 1)]; simp

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

theorem findRevHonestWireIdxE_eval (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)} (hwE : Expr O Γ (.list (honestWireEntryT ℓ Pt)))
    (qBE : Expr O Γ .bool) (wE : Expr O Γ (B 32))
    (ρ : Env Γ) (hw : List (Bytes × Party)) (Q : Party) (w : Bytes)
    (hhw : hwE.eval ρ = hw.map fun (x, P) => (x, partyToBool P))
    (hq : qBE.eval ρ = partyToBool Q) (hwv : wE.eval ρ = w) (hlen : hw.length ≤ L) :
    (findRevHonestWireIdxE emb L hwE qBE wE).eval ρ =
      hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) := by
  let p : Bytes × Party → Bool := fun wp => wp.1 == w && wp.2 == Q.other
  have htake : (hw.map fun (x, P) => (x, partyToBool P)).take L =
      hw.map fun (x, P) => (x, partyToBool P) :=
    List.take_of_length_le (by simpa using hlen)
  simp only [findRevHonestWireIdxE, boolEqE, emb.eval_pureE, AtomicPureOp.eval,
    Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, hhw, hq, hwv, htake, List.foldr_map]
  rw [← foldr_stepRevIdx_eq_findIdx p hw]
  refine congrArg Prod.fst (congrFun (congrFun (congrArg List.foldr ?_) (none, 0)) hw)
  funext wp acc
  unfold stepRevIdx; dsimp only [p]
  have hP : (if partyToBool wp.2 = true then !partyToBool Q else !!partyToBool Q) =
      (wp.2 == Q.other) := by cases wp.2 <;> cases Q <;> rfl
  rw [hP]; cases acc.1 <;> rfl

private theorem sendsIn_other_eq_senderOf_beq (t : ℕ) (Q : Party) :
    (if !partyToBool Q then decide (t % 2 = 0) else decide (t % 2 = 1)) =
      (Party.senderOf t == Q.other) := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;>
    cases Q <;> simp [Party.senderOf, Party.other, partyToBool, h]

theorem findRevHonestIdxE_eval (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)}
    (honestE : Expr O Γ (.list (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
    (qBE : Expr O Γ .bool) (wE : Expr O Γ (B 32))
    (ρ : Env Γ) (honest : List (Bytes × SimFig8C Pt)) (Q : Party) (w : Bytes)
    (hhon : honestE.eval ρ = honest.map honestPairEnc)
    (hq : qBE.eval ρ = partyToBool Q) (hw : wE.eval ρ = w) (hlen : honest.length ≤ L) :
    (findRevHonestIdxE emb L honestE qBE wE).eval ρ =
      honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) := by
  let p : Bytes × SimFig8C Pt → Bool :=
    fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other
  have htake : (honest.map (honestPairEnc (ℓ := ℓ) (Pt := Pt))).take L =
      honest.map honestPairEnc :=
    List.take_of_length_le (by simpa using hlen)
  simp only [findRevHonestIdxE, emb.eval_pureE, AtomicPureOp.eval,
    Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, hhon, hq, hw, htake, List.foldr_map]
  rw [← foldr_stepRevIdx_eq_findIdx p honest]
  refine congrArg Prod.fst (congrFun (congrFun (congrArg List.foldr ?_) (none, 0)) honest)
  funext wc acc
  unfold honestPairEnc fig8CtV stepRevIdx; dsimp only [p]
  rw [sendsIn_other_eq_senderOf_beq wc.2.1.1 Q]; cases acc.1 <;> rfl

private theorem b64Take48ToB32E_eval (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (suf : Expr O Γ (B 64))
    (ρ : Env Γ) (bs : Bytes) (hsuf : suf.eval ρ = bs) (hlen : bs.length ≤ 48) :
    (b64Take48ToB32E emb suf).eval ρ = bs := by
  have hpre : encode_varint ((0#32).zeroExtend 64) (encode_varint 0#64 [1#8]) = [1#8, 0#8, 0#8] :=
    rfl
  have ht64 : bs.take 64 = bs := List.take_of_length_le (by omega)
  have ht96 : ([1#8, 0#8, 0#8] ++ bs).take 96 = [1#8, 0#8, 0#8] ++ bs :=
    List.take_of_length_le (by simp; omega)
  simp only [b64Take48ToB32E, emb.eval_pureE, AtomicPureOp.eval, Expr.eval, hsuf, hpre, ht64, ht96]
  rfl

private theorem eval_caseOpt {Γ : List (Ty ASig)} {a b : Ty ASig}
    (e : Expr O Γ (.opt a)) (n : Expr O Γ b) (s : Expr O (a :: Γ) b) (ρ : Env Γ) :
    (Expr.caseOpt e n s).eval ρ =
      match e.eval ρ with | none => n.eval ρ | some v => s.eval (.cons v ρ) := by
  simp only [Expr.eval]; cases e.eval ρ <;> rfl

theorem stepKemFailDeliverE_eval (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)} (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (jE : Expr O Γ .nat) (ρ : Env Γ) (tr : SimKemFailTrack C.F) (Q : Party) (j : ℕ)
    (htr : trE.eval ρ = kemTrackAtomicEnc tr) (hq : qBE.eval ρ = partyToBool Q)
    (hj : jE.eval ρ = j) (hInv : KemTrackDeliverInv C.F K L tr) :
    (stepKemFailDeliverE emb L trE qBE jE).eval ρ =
      kemTrackAtomicEnc (simStepKemFailDeliver C.F K tr Q j) := by
  dsimp only [stepKemFailDeliverE, Expr.eval]
  rw [htr, hq, hj]
  set t0 : Ty ASig := .prod (kemTrackT ℓ Pt) (.prod .bool .nat)
  set ρ0 : Env (t0 :: Γ) :=
    Env.cons (t := t0) (kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) tr, (partyToBool Q, j)) ρ
  have hnth : (listNthOptB (O := O) L (trE_sentB (.fst .v0)) (.snd (.snd .v0))).eval ρ0 =
      (tr.sentB[j]?).map (fun (m, ctr) => ((m.epoch, spqrMsgPayloadSuffix m), ctr)) := by
    rw [listNthOptB_eval L _ _ ρ0
      (tr.sentB.map (fun (m, ctr) => ((m.epoch, spqrMsgPayloadSuffix m), ctr))) j rfl rfl
      (by simp only [List.length_map]; exact hInv.sentB_len)]
    exact List.getElem?_map
  rw [hnth]
  unfold simStepKemFailDeliver
  cases hj_get : tr.sentB[j]? with
  | none => rfl
  | some mc =>
    rcases mc with ⟨m, ctr⟩; dsimp only [Option.map]
    set ρ1 : Env (kemSentEntryT ℓ Pt :: t0 :: Γ) :=
      Env.cons (t := kemSentEntryT ℓ Pt) ((m.epoch, spqrMsgPayloadSuffix m), ctr) ρ0
    have hm_mem : (m, ctr) ∈ tr.sentB := List.mem_of_getElem? hj_get
    have hdes := hInv.sentB_deser (m, ctr) hm_mem
    have hsfx_len : (spqrMsgPayloadSuffix m).length ≤ 48 := by
      obtain ⟨hlen43, hsfx_eq⟩ :=
        Computational.Proofs.E2E.Dsl.ClampsLossless.spqrMsgPayloadSuffix_lossless m
      have hEq : spqrMsgPayloadSuffix m = CryptoVerification.E2E.Costed.spqrMsgPayloadSuffix m := rfl
      rw [hEq, hsfx_eq]; exact Nat.le_trans hlen43 (by decide)
    have hmSuf1 : (b64Take48ToB32E emb (.snd (.fst .v0))).eval ρ1 = spqrMsgPayloadSuffix m :=
      b64Take48ToB32E_eval emb _ ρ1 (spqrMsgPayloadSuffix m) rfl hsfx_len
    have hrecvOut : ((emb.spqrE .spqrBraidRecv
        (.pair (pGet (trE_st (.fst .v1)) (.fst (.snd .v1)))
          (.pair (.fst (.fst .v0)) (b64Take48ToB32E emb (.snd (.fst .v0)))))).eval ρ1).2.2 =
        (CryptoVerification.E2E.Costed.spqrBraidRecvEval (ℓ := ℓ) C.F K
          (V1State.encodeRaw (tr.st Q).into_pb) m.epoch (spqrMsgPayloadSuffix m)).2.2 := by
      simp only [Expr.eval, emb.eval_spqrE, AtomicSpqrKemOp.eval]
      rw [hmSuf1]
      simp only [pGet, trE_st, Expr.eval, Expr.v0, Expr.v1, ρ1, ρ0, kemTrackAtomicEnc, env_get_zero,
        env_get_succ]
      cases Q <;> rfl
    rw [hrecvOut,
      Computational.Proofs.E2E.Dsl.SpqrSimChain.spqrBraidRecvEval_of_bOkTight
        (ℓ := ℓ) C.F K (tr.st Q) (hInv.bOk Q) m.epoch (spqrMsgPayloadSuffix m), hdes]
    dsimp only
    cases hrecv : (tr.st Q).recv K m with
    | error err => cases err <;> rfl
    | ok out =>
      rcases out with ⟨key, st'⟩; dsimp only
      set t2 : Ty ASig := .prod (.opt (.prod U64 BV256)) (B 32)
      set ρ2 : Env (t2 :: kemSentEntryT ℓ Pt :: t0 :: Γ) := Env.cons (t := t2)
        (key.map (fun es => (es.epoch, bytesToKey32 es.secret)),
          V1State.encodeRaw st'.into_pb) ρ1
      have hmSuf2 : (b64Take48ToB32E emb (.snd (.fst .v1))).eval ρ2 = spqrMsgPayloadSuffix m :=
        b64Take48ToB32E_eval emb _ ρ2 (spqrMsgPayloadSuffix m) rfl hsfx_len
      have hNoneIff :
          ((m.epoch == tr.e + 1#64) && (spqrMsgPayloadSuffix m == [0#8])) =
            decide (m = { epoch := tr.e + 1#64, payload := .none }) := by
        by_cases hm_eq : m = { epoch := tr.e + 1#64, payload := .none }
        · subst hm_eq
          have hsfxNone :
              spqrMsgPayloadSuffix (P := CryptoVerification.LibsignalSpqrV1.spqrPolyApi)
                { epoch := tr.e + 1#64, payload := .none } = [0#8] := rfl
          simp [hsfxNone]
        · cases hep : (m.epoch == tr.e + 1#64)
          · simp [hm_eq]
          · cases hsfx0 : (spqrMsgPayloadSuffix m == [0#8])
            · simp [hm_eq]
            · exfalso
              rw [eq_of_beq hep, eq_of_beq hsfx0] at hdes
              have hdes0 : CryptoVerification.LibsignalSpqrV1.Message.deserialize
                  CryptoVerification.LibsignalSpqrV1.spqrPolyApi (tr.e + 1#64) [0#8] =
                  .ok { epoch := tr.e + 1#64, payload := .none } := by
                simp [CryptoVerification.LibsignalSpqrV1.Message.deserialize,
                  CryptoVerification.LibsignalSpqrV1.MessageType.tryFromU8, bind, Except.bind]
              rw [hdes0] at hdes; cases hdes; exact hm_eq rfl
      simp only [emb.eval_pureE, AtomicPureOp.eval, Expr.eval]
      rw [show (b64Take48ToB32E emb (.snd (.fst .v1))).eval _ = spqrMsgPayloadSuffix m from hmSuf2]
      simp only [pSet, trE_e, trE_c, trE_st, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
        env_get_zero, env_get_succ, ρ2, ρ1, ρ0, kemTrackAtomicEnc, hNoneIff]
      by_cases hm_eq : m = { epoch := tr.e + 1#64, payload := .none }
      · simp only [hm_eq, decide_true, ↓reduceIte, Bool.true_and]
        cases tr.c <;> cases Q <;> rfl
      · simp only [hm_eq, decide_false, ↓reduceIte, Bool.false_and]
        cases tr.c <;> cases Q <;> rfl

theorem stepKemFailDeliverC_eval (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (jE : Expr O Γ .nat) (ρ : Env Γ) (tr : SimKemFailTrack C.F) (Q : Party) (j : ℕ)
    (htr : trE.eval ρ = kemTrackAtomicEnc tr) (hq : qBE.eval ρ = partyToBool Q)
    (hj : jE.eval ρ = j) (hInv : KemTrackDeliverInv C.F K L tr) :
    (stepKemFailDeliverC emb L (I := I) trE qBE jE).eval ρ =
      pure (kemTrackAtomicEnc (simStepKemFailDeliver C.F K tr Q j)) := by
  simp [stepKemFailDeliverC, Comp.eval, stepKemFailDeliverE_eval emb L trE qBE jE ρ tr Q j htr hq hj hInv]

theorem stepKemSessionDeliverOptE_eval (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)} (stE : Expr O Γ (kemSessionTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (jOptE : Expr O Γ (.opt .nat)) (ρ : Env Γ)
    (st : SimKemSessionTrack C.F Bytes) (Q : Party) (j? : Option ℕ)
    (hst : stE.eval ρ = kemSessionTrackAtomicEnc st)
    (hq : qBE.eval ρ = partyToBool Q) (hj : jOptE.eval ρ = j?)
    (hInv : KemTrackDeliverInv C.F K L st.1) :
    (stepKemSessionDeliverOptE emb L stE qBE jOptE).eval ρ =
      kemSessionTrackAtomicEnc
        (match j? with | none => st | some j => (simStepKemFailDeliver C.F K st.1 Q j, st.2)) := by
  dsimp only [stepKemSessionDeliverOptE, Expr.eval]
  rw [hst, hq, hj]
  rcases j? with _ | j
  · rfl
  · dsimp only [Env.get, kemSessionTrackAtomicEnc]
    exact Prod.ext
      (stepKemFailDeliverE_eval emb L (.fst (.fst .v1)) (.fst (.snd .v1)) .v0 _ st.1 Q j rfl rfl rfl hInv) rfl

theorem kemOnDeliverPostE_eval (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)} (qBE : Expr O Γ .bool) (jOptE : Expr O Γ (.opt .nat))
    (rrOptE : Expr O Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (ρ : Env Γ)
    (Q : Party) (j? : Option ℕ) (rr? : Option (RecvResult (Plain ℓ)))
    (tr : SimKemFailTrack C.F)
    (hq : qBE.eval ρ = partyToBool Q) (hj : jOptE.eval ρ = j?)
    (hrr : rrOptE.eval ρ = rr?.map recvResultEnc)
    (htr : trE.eval ρ = kemTrackAtomicEnc tr)
    (hInv : KemTrackDeliverInv C.F K L tr) :
    (kemOnDeliverPostE emb L qBE jOptE rrOptE trE).eval ρ =
      kemTrackAtomicEnc
        (match rr?, j? with
         | some (.accepted _ _ _), some j => simStepKemFailDeliver C.F K tr Q j
         | _, _ => tr) := by
  dsimp only [kemOnDeliverPostE, Expr.eval]
  rw [hq, hj, hrr, htr]
  rcases rr? with _ | rr
  · rfl
  · cases rr with
    | rejected => rfl
    | accepted t i m =>
      rcases j? with _ | j
      · rfl
      · dsimp only [Option.map, recvResultEnc, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get]
        exact stepKemFailDeliverE_eval emb L (.snd (.snd (.snd .v3))) (.fst .v3) .v0 _ tr Q j rfl rfl rfl hInv

end EvalProofs

end Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDsl
