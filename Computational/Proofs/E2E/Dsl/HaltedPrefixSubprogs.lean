/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.HaltedPrefixSubprogsAux -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.M3PqxdhSize
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync

/-!
# Halted Multi-Session Prefix Subprograms

Constructs the atomic `ReductionDsl` subprograms over `atomicE2EOps` and `e2eSessionTargetIface`
for `HaltedPrefixSubprograms` (along with their `b.q_total`-clamped variants) and proves their
query, cost, size, and evaluation lemmas against `MainHaltedPrefixCore`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.HaltedPrefixSubprogs

export Computational.Proofs.E2E.Dsl.HaltedPrefixSubprogsAux (sessHTy sessHEnc)

open Computational.Proofs.E2E.Dsl.HaltedPrefixSubprogsAux
  (kemTrackT kemCoinsBridgeAtomicEnc kemTrackBridgeAtomicEnc liftSamp liftSessionTag
   snocAtomicE snocAtomicE_cost snocAtomicE_size snocAtomicE_eval
   bhE2EFinishStartSpk_some_drKey
   lift1Expr lift1Expr_cost lift1Expr_size lift1Expr_eval
   lift1Comp lift1Comp_cost lift1Comp_size lift1Comp_queries lift1Comp_eval)
open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp UniformSamplerTag bits iterM
  findML anyML mapML consumeFirstML foldML
  partyToBool bytesToWordLE spqrMsgPayloadSuffix atomicSig atomicE2EOps atomicBaseSamplers
  e2eSessionTargetIface AtomicPureOp AtomicCurveCheckOp AtomicSpqrKemOp
  B BV256 BV512 U32 U64 recvResultEnc)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState ShaCompress)
open CryptoGames.Ratchet.LibsignalSim (simInitKemFailTrack)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State)
open CryptoVerification.E2E (Bytes BHE2EDrvState SampledSessionKey bhE2EGuard bhE2EFinishStartSpk
  bhKeySOf bhBytesWord)
open CryptoVerification.E2E.Costed (E2EPureOp E2ECurveCheckOp E2ECryptoOp E2EUnifBase E2ESessionTag
  e2eSig e2eOps e2eSamplers)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (liftSort liftTy liftCtx liftVal liftVal_heq liftVar liftEnv liftEnv_get
   renExpr renComp wk1Ren wk1Expr wk1Expr_cost wk1Expr_eval
   wk1Comp wk1Comp_queries wk1Comp_cost wk1Comp_eval
   readProstVarint_eq splitSpqrPrev_eq)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_succ_le)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (KemFailTrackState KemFailSessionTrack initKemFailTrack initKemFailSessionTrack)

/-! ## Halted prefix subprograms -/

@[expose, reducible] def drvTy (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  liftTy (Pt := Pt) (Computational.Proofs.E2E.Dsl.E2EStateRepr.e2eDrvStateTy S ℓ)

@[expose, reducible] def drvEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (σ : BHE2EDrvState S ℓ) : (drvTy S ℓ Pt).denote :=
  Computational.Proofs.E2E.Dsl.E2EStateRepr.e2eDrvStateEnc σ

@[simp] theorem liftVal_e2eDrvStateEnc_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (σ : BHE2EDrvState S ℓ) :
    liftVal (Pt := Pt) (t := Computational.Proofs.E2E.Dsl.E2EStateRepr.e2eDrvStateTy S ℓ)
      (Computational.Proofs.E2E.Dsl.E2EStateRepr.e2eDrvStateEnc σ) =
      drvEnc (Pt := Pt) σ :=
  eq_of_heq (liftVal_heq _)

section AtomicTrackInit

variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

abbrev e2ePureE (o : AtomicPureOp) {Γ : List (Ty (atomicSig ℓ Pt))}
    (a : Expr (atomicE2EOps ℓ P C K decT encT) Γ (AtomicPureOp.dom (ℓ := ℓ) (Pt := Pt) o)) :
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (AtomicPureOp.cod (ℓ := ℓ) (Pt := Pt) o) :=
  Expr.op (O := atomicE2EOps ℓ P C K decT encT) (.inl (.inl o)) a

abbrev e2eSpqrE (o : AtomicSpqrKemOp) {Γ : List (Ty (atomicSig ℓ Pt))}
    (a : Expr (atomicE2EOps ℓ P C K decT encT) Γ (AtomicSpqrKemOp.dom (ℓ := ℓ) (Pt := Pt) o)) :
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (AtomicSpqrKemOp.cod (ℓ := ℓ) (Pt := Pt) o) :=
  Expr.op (O := atomicE2EOps ℓ P C K decT encT) (.inr (.inr (.inr (.inl o)))) a

@[expose] def initV1BraidStE2EE (isAlice : Bool) {Γ : List (Ty (atomicSig ℓ Pt))}
    (pqrKeyE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (B (ℓ := ℓ) (Pt := Pt) 32) :=
  let ver1 := e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.u8Lit 1#8) .unit
  let dirE := e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (.u32Lit (if isAlice then 0#32 else 1#32)) .unit
  let authKeyE := e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    .bv256ToBytes32 pqrKeyE
  .caseOpt (.snd (e2eSpqrE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      .spqrNegotiateInit (.pair ver1 (.pair dirE authKeyE))))
    (e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.bytesLit 32 []) .unit)
    (.caseOpt (.var .zero)
      (e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.bytesLit 32 []) .unit)
      (.var .zero))

@[expose] def initKemTrackE2EE {Γ : List (Ty (atomicSig ℓ Pt))}
    (pqrKeyE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (kemTrackT ℓ Pt) :=
  .letE pqrKeyE (.pair
    (e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.u64Lit 1#64) .unit)
    (.pair (.inl .unit) (.pair
      (.pair (initV1BraidStE2EE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) true (.var .zero))
             (initV1BraidStE2EE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) false (.var .zero)))
      (.pair .nil (.pair (.pair (.tconst (.nat 0)) (.tconst (.nat 0))) .none)))))

@[expose] def initKemFailSessionTrackE2EE {Γ : List (Ty (atomicSig ℓ Pt))}
    (pqrKeyE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt) :=
  .pair (initKemTrackE2EE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) pqrKeyE) .nil

theorem initKemFailSessionTrackE2EE_cost {Γ : List (Ty (atomicSig ℓ Pt))}
    (pqrKeyE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    (initKemFailSessionTrackE2EE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) pqrKeyE).cost ≤
      pqrKeyE.cost + 3500 := by
  unfold initKemFailSessionTrackE2EE initKemTrackE2EE initV1BraidStE2EE e2ePureE e2eSpqrE
  simp only [Expr.cost, atomicE2EOps, _root_.ReductionDsl.atomicAdapterOps,
    _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicSpqrKemOps,
    Ops.sum, Sum.elim_inl, Sum.elim_inr, AtomicPureOp.cost, AtomicSpqrKemOp.cost,
    List.length_nil, PNat.val_ofNat, show bits 0 = 1 from rfl]; omega

theorem initKemFailSessionTrackE2EE_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (pqrKeyE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    (initKemFailSessionTrackE2EE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) pqrKeyE).size ≤
      pqrKeyE.size + 80 := by
  unfold initKemFailSessionTrackE2EE initKemTrackE2EE initV1BraidStE2EE e2ePureE e2eSpqrE
  simp only [Expr.size, atomicE2EOps, _root_.ReductionDsl.atomicAdapterOps,
    _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicSpqrKemOps,
    Ops.sum, Sum.elim_inl, Sum.elim_inr, AtomicPureOp.opSize, List.length_nil,
    show bits 0 = 1 from rfl]; omega

theorem initV1BraidStE2EE_eval (isAlice : Bool) {Γ : List (Ty (atomicSig ℓ Pt))}
    (pqrKeyE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) :
    (initV1BraidStE2EE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) isAlice pqrKeyE).eval ρ =
      V1State.encodeRaw
        (((simInitKemFailTrack C.F (pqrKeyE.eval ρ)).st (if isAlice then .A else .B)).into_pb) := by
  have hop :
      (e2eSpqrE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) .spqrNegotiateInit
        (.pair (e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.u8Lit 1#8) .unit)
          (.pair (e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
              (.u32Lit (if isAlice then 0#32 else 1#32)) .unit)
            (e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
              .bv256ToBytes32 pqrKeyE)))).eval ρ =
      (false, some (some (V1State.encodeRaw
        (((simInitKemFailTrack C.F (pqrKeyE.eval ρ)).st (if isAlice then .A else .B)).into_pb)))) := by
    dsimp only [e2eSpqrE, e2ePureE, Expr.eval, atomicE2EOps, _root_.ReductionDsl.atomicAdapterOps,
      _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicSpqrKemOps, Ops.sum,
      AtomicPureOp.eval, AtomicSpqrKemOp.eval]
    change CryptoVerification.E2E.Costed.spqrNegotiateInitEval (ℓ := ℓ) C.F K 1#8
      (if isAlice then 0#32 else 1#32) (keyToBytes32 (pqrKeyE.eval ρ)) = _
    rw [Computational.Proofs.E2E.Dsl.ClampsLossless.spqrNegotiateInitEval_clamp_lossless]
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
  dsimp only [e2eSpqrE, e2ePureE, Expr.eval] at hop
  unfold initV1BraidStE2EE; dsimp only [Expr.eval]; rw [hop]; rfl

@[simp] theorem initKemFailSessionTrackE2EE_eval {Γ : List (Ty (atomicSig ℓ Pt))}
    (pqrKeyE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) :
    (initKemFailSessionTrackE2EE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) pqrKeyE).eval ρ =
      sessHEnc (ℓ := ℓ) (Pt := Pt) (initKemFailSessionTrack C.F Bytes (pqrKeyE.eval ρ)) := by
  dsimp only [initKemFailSessionTrackE2EE, initKemTrackE2EE, Expr.eval]
  rw [initV1BraidStE2EE_eval, initV1BraidStE2EE_eval]
  dsimp only [Env.get, e2ePureE, Expr.eval, atomicE2EOps, _root_.ReductionDsl.atomicAdapterOps,
    _root_.ReductionDsl.atomicPureOps, Ops.sum, AtomicPureOp.eval,
    sessHEnc, initKemFailSessionTrack, kemTrackBridgeAtomicEnc, kemCoinsBridgeAtomicEnc]
  simp only [ite_true, Bool.false_eq_true, ite_false, initKemFailTrack, simInitKemFailTrack,
    CryptoVerification.SpqrV1Sync.InSync.freshDec, List.map_nil, Option.map_none]
  rfl

attribute [local irreducible] initKemFailSessionTrackE2EE

end AtomicTrackInit

section PrefixSubprograms

open _root_.ReductionDsl (IdKey prefixCtxT keyIndQT keyIndQenc keyIndRT keyIndRenc
  sidT sidV smQT smQenc smRT GhostStT)
open CryptoVerification.E2E (BHPrefixCtx BHE2ESmResp BHTargetResp e2eTargetGameCodec bhIdKeyOf
  bhShallowStepPreNonCtl bhShallowFinishPrefix
  bhDrvKiQueryOk bhNoOpkRespPromoted bhE2EMirror)
open Computational.Proofs.E2E.Dsl.M3Interfaces
  (e2eDrvStateTy e2eDrvStateEnc DrvMirrorBounded DrvQueryBounded DrvMetaAligned
   KeyIndReachBounded bhPromoteSlotK bhExtSmStep packSmRespEnc mkTestSessionE mkRevealSpkSkE)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval
  (packAtomicSmRespEnc atomicGameRespEnc atomicPrefixCtxEnc)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (bhE2ELocalStartSessionTracked)

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

@[expose] def emptyDrvStateHaltedE {Γ : List (Ty (atomicSig ℓ Pt))}
    (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt) :=
  .pair (.pair .nil (.pair .nil (.pair .nil .nil)))
    (.pair .nil (.pair .nil (.pair .nil (.pair .nil
      (.pair (.pair (.bool false) (.pair .nil (.pair .nil (.pair .nil (.pair .nil
          (.pair .nil (.pair .nil (.pair .nil (.pair .nil (.pair .nil .nil))))))))))
        (.pair bE (.bool false)))))))

theorem emptyDrvStateHaltedE_cost {Γ : List (Ty (atomicSig ℓ Pt))}
    (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    (emptyDrvStateHaltedE (S := S) bE).cost ≤ bE.cost + 40 := by
  simp only [emptyDrvStateHaltedE, Expr.cost]; omega

theorem emptyDrvStateHaltedE_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    (emptyDrvStateHaltedE (S := S) bE).size ≤ bE.size + 40 := by
  simp only [emptyDrvStateHaltedE, Expr.size]; omega

@[simp] theorem emptyDrvStateHaltedE_eval {Γ : List (Ty (atomicSig ℓ Pt))}
    (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) (ρ : Env Γ) :
    (emptyDrvStateHaltedE (S := S) (Pt := Pt) bE).eval ρ = drvEnc { b := bE.eval ρ } := rfl

@[expose] def drvSetBitHaltedE {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt) :=
  lift1Expr (a := .prod (e2eDrvStateTy S ℓ) .bool) (b := e2eDrvStateTy S ℓ) (.pair σE bE)
    (M3Interfaces.drvSetBitE (.fst (.var .zero)) (.snd (.var .zero)))

theorem drvSetBitHaltedE_cost {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    (drvSetBitHaltedE σE bE).cost ≤ σE.cost + bE.cost + 80 := by
  have hb := M3Interfaces.cost_drvSetBitE (S := S) (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT)
    (Γ := [.prod (e2eDrvStateTy S ℓ) .bool]) (.fst (.var .zero)) (.snd (.var .zero))
  simp only [drvSetBitHaltedE, lift1Expr_cost, Expr.cost] at hb ⊢; omega

theorem drvSetBitHaltedE_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    (drvSetBitHaltedE σE bE).size ≤ σE.size + bE.size + 80 := by
  have hb := M3Interfaces.size_drvSetBitE (S := S) (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT)
    (Γ := [.prod (e2eDrvStateTy S ℓ) .bool]) (.fst (.var .zero)) (.snd (.var .zero))
  simp only [drvSetBitHaltedE, lift1Expr_size, Expr.size] at hb ⊢; omega

theorem drvSetBitHaltedE_eval {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (hσ : σE.eval ρ = drvEnc σ) :
    (drvSetBitHaltedE σE bE).eval ρ = drvEnc { σ with b := bE.eval ρ } := by
  have harg : (Expr.pair σE bE).eval ρ =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ) .bool) (e2eDrvStateEnc σ, bE.eval ρ) := by
    dsimp only [Expr.eval]; rw [hσ, ← liftVal_e2eDrvStateEnc_eq]; rfl
  rw [drvSetBitHaltedE, lift1Expr_eval _ _ ρ _ harg,
    M3Interfaces.eval_drvSetBitE _ _ _ rfl]
  dsimp only [Expr.eval, Expr.snd, Expr.var, Var.zero, Env.get]
  exact liftVal_e2eDrvStateEnc_eq _

@[expose] def defaultPrefixCtxHaltedE {Γ : List (Ty (atomicSig ℓ Pt))} :
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (prefixCtxT (ℓ := ℓ) (Pt := Pt)) :=
  let zeroId : Expr (atomicE2EOps ℓ P C K decT encT) Γ (IdKey (ℓ := ℓ) (Pt := Pt)) :=
    e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) .idKeyOfPbytes
      (e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.pbytesLit 32 []) .unit)
  .pair zeroId (.pair zeroId
    (e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.bv256Lit 0#256) .unit))

theorem defaultPrefixCtxHaltedE_cost {Γ : List (Ty (atomicSig ℓ Pt))} :
    (defaultPrefixCtxHaltedE (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ)).cost ≤ 150 := by
  unfold defaultPrefixCtxHaltedE e2ePureE
  simp only [Expr.cost, atomicE2EOps, _root_.ReductionDsl.atomicAdapterOps,
    _root_.ReductionDsl.atomicPureOps, Ops.sum, Sum.elim_inl, AtomicPureOp.cost,
    PNat.val_ofNat, List.length_nil]
  omega

theorem defaultPrefixCtxHaltedE_size {Γ : List (Ty (atomicSig ℓ Pt))} :
    (defaultPrefixCtxHaltedE (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ)).size ≤ 50 := by
  unfold defaultPrefixCtxHaltedE e2ePureE
  simp only [Expr.size, atomicE2EOps, _root_.ReductionDsl.atomicAdapterOps,
    _root_.ReductionDsl.atomicPureOps, Ops.sum, Sum.elim_inl, AtomicPureOp.opSize,
    List.length_nil]
  omega

@[simp] theorem defaultPrefixCtxHaltedE_eval {Γ : List (Ty (atomicSig ℓ Pt))} (ρ : Env Γ) :
    (defaultPrefixCtxHaltedE (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ)).eval ρ = (bhIdKeyOf [], (bhIdKeyOf [], 0)) := rfl

@[expose] def promoteSlotKHaltedEnc
    (res : (Option ℕ × BHE2EDrvState S ℓ) ⊕ (BHPrefixCtx × Option ℕ × BHE2EDrvState S ℓ)) :
    (Ty.sum (.prod (.opt .nat) (drvTy S ℓ Pt))
      (.prod (prefixCtxT (ℓ := ℓ) (Pt := Pt)) (.prod (.opt .nat) (drvTy S ℓ Pt)))).denote :=
  match res with
  | .inl (idx?, σ1) => .inl (idx?, drvEnc σ1)
  | .inr (ctx, (idx?, σ1)) => .inr ((ctx.idA, (ctx.idB, ctx.spkCoins)), (idx?, drvEnc σ1))

@[expose] def promoteSlotKHaltedC (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt)) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ
      (.sum (.prod (.opt .nat) (drvTy S ℓ Pt))
        (.prod (prefixCtxT (ℓ := ℓ) (Pt := Pt)) (.prod (.opt .nat) (drvTy S ℓ Pt)))) :=
  lift1Comp (a := .prod .nat (.prod (.opt .nat) (e2eDrvStateTy S ℓ)))
    (.pair kE (.pair idxOptE σE))
    (StartAndExtSm.promoteSlotKC (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) qStart
      (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0)))

@[expose] def promoteSlotKHaltedCost (qStart : ℕ) : ℕ := StartAndExtSm.promoteSlotKCost qStart + 20
@[expose] def promoteSlotKHaltedSize (qStart : ℕ) : ℕ := 2 * bits qStart + 440

theorem promoteSlotKHaltedC_cost (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt)) :
    (promoteSlotKHaltedC qStart kE idxOptE σE).cost ≤
      kE.cost + idxOptE.cost + σE.cost + promoteSlotKHaltedCost qStart := by
  have hb := StartAndExtSm.promoteSlotKC_cost (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) qStart
    (Γ := [.prod .nat (.prod (.opt .nat) (e2eDrvStateTy S ℓ))])
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
  simp only [promoteSlotKHaltedC, promoteSlotKHaltedCost, lift1Comp_cost, Expr.cost, Expr.v0] at hb ⊢
  omega

theorem promoteSlotKHaltedC_size (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt)) :
    (promoteSlotKHaltedC qStart kE idxOptE σE).size ≤
      kE.size + idxOptE.size + σE.size + promoteSlotKHaltedSize qStart := by
  have hb := M3Subprograms.size_promoteSlotKC (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) qStart
    (Γ := [.prod .nat (.prod (.opt .nat) (e2eDrvStateTy S ℓ))])
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
  simp only [promoteSlotKHaltedC, promoteSlotKHaltedSize, lift1Comp_size, Expr.size, Expr.v0] at hb ⊢
  omega

theorem promoteSlotKHaltedC_queries (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ) :
    (promoteSlotKHaltedC qStart kE idxOptE σE).queries w (fun _ => 0) = 0 := by
  rw [promoteSlotKHaltedC, lift1Comp_queries]
  exact StartAndExtSm.promoteSlotKC_queries (Pt := Pt)
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) qStart _ _ _
    (fun g => w (liftSessionTag g))

private theorem liftVal_promoteSlotKEnc
    (res : (Option ℕ × BHE2EDrvState S ℓ) ⊕ (BHPrefixCtx × Option ℕ × BHE2EDrvState S ℓ)) :
    liftVal (Pt := Pt) (t := .sum (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
      (.prod CryptoVerification.E2E.Costed.prefixCtxT (.prod (.opt .nat) (e2eDrvStateTy S ℓ))))
      (M3Interfaces.promoteSlotKEnc res) =
    promoteSlotKHaltedEnc (Pt := Pt) res := by
  rcases res with ⟨idx?, σ1⟩ | ⟨ctx, idx?, σ1⟩ <;> exact eq_of_heq (liftVal_heq _)

theorem promoteSlotKHaltedC_eval (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (ρ : Env Γ) (σ' : BHE2EDrvState S ℓ) (hσ : σE.eval ρ = drvEnc σ')
    (hlen : σ'.insts.length ≤ qStart) :
    (promoteSlotKHaltedC qStart kE idxOptE σE).eval ρ =
      pure (promoteSlotKHaltedEnc (Pt := Pt)
        (bhPromoteSlotK (kE.eval ρ) (idxOptE.eval ρ) σ')) := by
  have harg : (Expr.pair kE (.pair idxOptE σE)).eval ρ =
      liftVal (Pt := Pt) (t := .prod .nat (.prod (.opt .nat) (e2eDrvStateTy S ℓ)))
        (kE.eval ρ, (idxOptE.eval ρ, e2eDrvStateEnc σ')) := by
    dsimp only [Expr.eval]; rw [hσ, ← liftVal_e2eDrvStateEnc_eq]; cases idxOptE.eval ρ <;> rfl
  rw [promoteSlotKHaltedC, lift1Comp_eval _ _ ρ _ harg,
    StartAndExtSm.promoteSlotKC_eval (Pt := Pt)
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) qStart _ _ _ _ σ' rfl hlen, map_pure]
  exact congrArg pure (liftVal_promoteSlotKEnc (bhPromoteSlotK (kE.eval ρ) (idxOptE.eval ρ) σ'))

@[expose] def finishPrefixHaltedC (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ .bool :=
  lift1Comp (a := .prod (e2eDrvStateTy S ℓ) (.prod .bool .bool)) (b := .bool)
    (.pair σE (.pair bOutE flipE))
    (FreshnessSim.finishPrefixC (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
      qStart b.q_total (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0)))

@[expose] def finishPrefixHaltedCost (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  FreshnessSim.finishPrefixCost S qStart b.q_total + 20

@[expose] def finishPrefixHaltedSize (S : SignalPqxdh.Setup) (qStart : ℕ) : ℕ :=
  2 * bits qStart + 2 * bits S.N_send_tot + 2 * bits S.N_recv_tot +
    3 * bits S.N_id + 2 * bits S.N_spk_tot + 1820

theorem finishPrefixHaltedC_cost (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    (finishPrefixHaltedC b qStart σE bOutE flipE).cost ≤
      σE.cost + bOutE.cost + flipE.cost + finishPrefixHaltedCost S b qStart := by
  have hb := FreshnessSim.cost_finishPrefixC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
    qStart b.q_total (Γ := [.prod (e2eDrvStateTy S ℓ) (.prod .bool .bool)])
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
  simp only [finishPrefixHaltedC, finishPrefixHaltedCost, lift1Comp_cost, Expr.cost, Expr.v0] at hb ⊢
  omega

theorem finishPrefixHaltedC_size (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    (finishPrefixHaltedC b qStart σE bOutE flipE).size ≤
      σE.size + bOutE.size + flipE.size + finishPrefixHaltedSize S qStart := by
  have hb := M3Subprograms.size_finishPrefixC ℓ S P C K decT encT
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) qStart b.q_total
    (Γ := [.prod (e2eDrvStateTy S ℓ) (.prod .bool .bool)])
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
  simp only [finishPrefixHaltedC, finishPrefixHaltedSize, lift1Comp_size, Expr.size, Expr.v0] at hb ⊢
  omega

theorem finishPrefixHaltedC_queries (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool)
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ) :
    (finishPrefixHaltedC b qStart σE bOutE flipE).queries w (fun _ => 0) = 0 := by
  rw [finishPrefixHaltedC, lift1Comp_queries]
  exact FreshnessSim.queries_finishPrefixC
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) qStart b.q_total _ _ _
    (fun g => w (liftSessionTag g))

theorem finishPrefixHaltedC_eval (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ)
    (hσ : σE.eval ρ = drvEnc σ) (hInsts : σ.insts.length ≤ qStart)
    (hReach : KeyIndReachBounded S b.q_total σ.st) :
    (finishPrefixHaltedC b qStart σE bOutE flipE).eval ρ =
      (e2eSessionTargetIface ℓ Pt).liftP
        (bhShallowFinishPrefix P σ (bOutE.eval ρ) (flipE.eval ρ)) := by
  have harg : (Expr.pair σE (.pair bOutE flipE)).eval ρ =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ) (.prod .bool .bool))
        (e2eDrvStateEnc σ, (bOutE.eval ρ, flipE.eval ρ)) := by
    dsimp only [Expr.eval]; rw [hσ, ← liftVal_e2eDrvStateEnc_eq]; rfl
  rw [finishPrefixHaltedC, lift1Comp_eval _ _ ρ _ harg,
    FreshnessSim.eval_finishPrefixC _ qStart b.q_total _ _ _ _ σ
      (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) 0 hP rfl hInsts hReach.setup]
  exact id_map _

private theorem costedLiftP_eq_atomicLiftP {α : Type} (p : ProbComp α) :
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ).liftP p =
      (e2eSessionTargetIface ℓ Pt).liftP p := rfl

private theorem liftVal_sidV_eq (sid : SignalPqxdh.SessionId S) :
    liftVal (Pt := Pt) (t := CryptoVerification.E2E.Costed.sidT S)
      (CryptoVerification.E2E.Costed.sidV sid) = sidV (ℓ := ℓ) (Pt := Pt) sid :=
  (eq_of_heq (liftVal_heq _)).trans (by cases sid <;> rfl)

private theorem liftVal_keyIndQenc_eq (kq : SignalPqxdh.KeyIndQuery S) :
    liftVal (Pt := Pt) (t := CryptoVerification.E2E.Costed.keyIndQT S)
      (CryptoVerification.E2E.Costed.keyIndQenc kq) = keyIndQenc (ℓ := ℓ) (Pt := Pt) kq :=
  (eq_of_heq (liftVal_heq _)).trans (by
    cases kq with
    | testSession sid => cases sid <;> rfl
    | revealSessionKey sid => cases sid <;> rfl
    | _ => rfl)

private theorem liftVal_keyIndRenc_eq (kr : SignalPqxdh.KeyIndResponse) :
    liftVal (Pt := Pt) (t := CryptoVerification.E2E.Costed.keyIndRT)
      (CryptoVerification.E2E.Costed.keyIndRenc kr) = keyIndRenc (ℓ := ℓ) (Pt := Pt) kr :=
  (eq_of_heq (liftVal_heq _)).trans (by cases kr <;> rfl)

private theorem liftVal_smQenc_eq
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    liftVal (Pt := Pt) (t := CryptoVerification.E2E.Costed.smQT)
      (CryptoVerification.E2E.Costed.smQenc sq) = smQenc (ℓ := ℓ) (Pt := Pt) sq :=
  (eq_of_heq (liftVal_heq _)).trans (by
    rcases sq with (((⟨p, _, _⟩ | ⟨p, _, _, _⟩) | ⟨p, _⟩) | ⟨p, _⟩) | p <;> cases p <;> rfl)

private theorem liftVal_packSmRespEnc_eq (br : BHE2ESmResp ℓ) :
    liftVal (Pt := Pt)
      (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
      (packSmRespEnc br) = packAtomicSmRespEnc (ℓ := ℓ) (Pt := Pt) br :=
  (eq_of_heq (liftVal_heq _)).trans (by
    rcases br with ⟨_, rr?, _⟩
    cases rr? with
    | none => rfl
    | some rr => cases rr <;> rfl)

@[expose] def extSmStepHaltedC (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (drvTy S ℓ Pt)) :=
  lift1Comp (a := .prod .nat (.prod (e2eDrvStateTy S ℓ) CryptoVerification.E2E.Costed.smQT))
    (.pair kE (.pair σE sqE))
    (StartAndExtSm.extSmStepC qStart b.q_total b.q_total
      (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0)))

@[expose] def extSmStepHaltedCost (ℓ : ℕ) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  StartAndExtSm.extSmStepCost ℓ qStart b.q_total b.q_total + 20

@[expose] def extSmStepHaltedSize (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  6 * bits qStart + 5 * bits b.q_total + 1820

theorem extSmStepHaltedC_cost (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))) :
    (extSmStepHaltedC b qStart kE σE sqE).cost ≤
      kE.cost + σE.cost + sqE.cost + extSmStepHaltedCost ℓ b qStart := by
  have hb := StartAndExtSm.extSmStepC_cost (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart b.q_total b.q_total
    (Γ := [.prod .nat (.prod (e2eDrvStateTy S ℓ) CryptoVerification.E2E.Costed.smQT)])
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
  simp only [extSmStepHaltedC, extSmStepHaltedCost, lift1Comp_cost, Expr.cost, Expr.v0] at hb ⊢
  omega

theorem extSmStepHaltedC_size (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))) :
    (extSmStepHaltedC b qStart kE σE sqE).size ≤
      kE.size + σE.size + sqE.size + extSmStepHaltedSize b qStart := by
  have hb := M3Subprograms.size_extSmStepC (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart b.q_total b.q_total
    (Γ := [.prod .nat (.prod (e2eDrvStateTy S ℓ) CryptoVerification.E2E.Costed.smQT)])
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
  simp only [extSmStepHaltedC, extSmStepHaltedSize, lift1Comp_size, Expr.size, Expr.v0] at hb ⊢
  omega

theorem extSmStepHaltedC_queries_one (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))) :
    (extSmStepHaltedC b qStart kE σE sqE).queries (fun _ => 1) (fun _ => 0) ≤ 1 := by
  rw [extSmStepHaltedC, lift1Comp_queries]
  exact StartAndExtSm.extSmStepC_queries (Pt := Pt) qStart b.q_total b.q_total
    _ _ _ (fun _ => 1) 1 (fun _ => le_rfl)

theorem extSmStepHaltedC_eval (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (k : ℕ) (σ : BHE2EDrvState S ℓ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hk : kE.eval ρ = k) (hσ : σE.eval ρ = drvEnc σ) (hsq : sqE.eval ρ = smQenc sq)
    (hMir : DrvQueryBounded b.q_total qStart σ) (hMeta : DrvMetaAligned σ) :
    (extSmStepHaltedC b qStart kE σE sqE).eval ρ =
      ((fun out => (packAtomicSmRespEnc out.1, drvEnc out.2)) <$> bhExtSmStep k σ sq) := by
  have harg : (Expr.pair kE (.pair σE sqE)).eval ρ =
      liftVal (Pt := Pt)
        (t := .prod .nat (.prod (e2eDrvStateTy S ℓ) CryptoVerification.E2E.Costed.smQT))
        (k, (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.smQenc sq)) := by
    dsimp only [Expr.eval]; rw [hk, hσ, hsq, ← liftVal_e2eDrvStateEnc_eq, ← liftVal_smQenc_eq]; rfl
  rw [extSmStepHaltedC, lift1Comp_eval _ _ ρ _ harg,
    StartAndExtSm.extSmStepC_eval (Pt := Pt) qStart b.q_total b.q_total _ _ _ _ k σ sq
      rfl rfl rfl hMir.insts_le hMeta hMir.corrPrins_le hMir.revSpks_le hMir.prins_le,
    Functor.map_map]
  congr 1; funext out
  exact Prod.ext (liftVal_packSmRespEnc_eq out.1) (liftVal_e2eDrvStateEnc_eq out.2)

@[expose] def kiStepBodyC (qStart : ℕ) (b : SignalPqxdh.QueryBudget) :
    Comp (e2eOps ℓ P C K decT encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
      [.prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)]
      (.prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ)) :=
  .ite (E2EStateRepr.kiQueryOkE b.q_total qStart (.fst .v0) (.snd .v0))
    (.bind
      ((PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC
        (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total
        (StartAndExtSmAux.drvSt (.fst .v0)) (.snd .v0))
      (.ret (.pair (.fst .v0)
        (E2EStateRepr.bhE2EMirrorE
          (M3Interfaces.drvSetStE (.fst (.var (.succ .zero))) (.snd .v0))
          (.snd (.var (.succ .zero))) (.fst .v0)))))
    (.ret (.pair (.inl .unit) (.fst .v0)))

@[expose] def kiStepHaltedC (qStart : ℕ) (b : SignalPqxdh.QueryBudget)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ
      (.prod (e2eTargetGameCodec S ℓ Pt).R (drvTy S ℓ Pt)) :=
  .bind
    (lift1Comp (a := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S))
      (b := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
      (.pair σE kqE) (kiStepBodyC qStart b))
    (.ret (.pair (.inl (.inl (.fst .v0))) (.snd .v0)))

@[expose] def kiStepHaltedCost (S : SignalPqxdh.Setup) (qStart : ℕ) (b : SignalPqxdh.QueryBudget) : ℕ :=
  168 * b.q_total + 24 * qStart + PqxdhSim.pqxdh1KeyRealStepCost S b.q_total + 1600

@[expose] def kiStepHaltedSize (pqxdhStepSize : ℕ → ℕ) (qStart : ℕ) (b : SignalPqxdh.QueryBudget) : ℕ :=
  3 * bits b.q_total + bits qStart + pqxdhStepSize b.q_total + 1900

theorem kiStepHaltedC_cost (qStart : ℕ) (b : SignalPqxdh.QueryBudget)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    (kiStepHaltedC qStart b σE kqE).cost ≤
      σE.cost + kqE.cost + kiStepHaltedCost S qStart b := by
  let τ0 : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)
  let τr : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.keyIndRT (PqxdhSimTypes.e2eKeyIndStateTy ℓ S)
  have hok := E2EStateRepr.cost_kiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) b.q_total qStart (Γ := [τ0]) (.fst .v0) (.snd .v0)
  have hst := (PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC_cost
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total (Γ := [τ0])
    (StartAndExtSmAux.drvSt (.fst .v0)) (.snd .v0)
  have hset := M3Interfaces.cost_drvSetStE (O := e2eOps ℓ P C K decT encT) (S := S) (ℓ := ℓ)
    (Γ := [τr, τ0]) (.fst (.var (.succ .zero))) (.snd .v0)
  have hmir := E2EStateRepr.cost_bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := [τr, τ0])
    (M3Interfaces.drvSetStE (.fst (.var (.succ .zero))) (.snd .v0))
    (.snd (.var (.succ .zero))) (.fst .v0)
  have hpqCost : (PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepCost b.q_total =
      PqxdhSim.pqxdh1KeyRealStepCost S b.q_total := rfl
  rw [hpqCost] at hst
  dsimp only [τ0, τr] at hok hst hset hmir
  simp only [kiStepHaltedC, kiStepBodyC, kiStepHaltedCost, lift1Comp_cost, StartAndExtSmAux.drvSt,
    Comp.cost, Expr.cost, Expr.v0] at hok hst hset hmir ⊢
  omega

theorem kiStepHaltedC_size {pqxdhStepSize : ℕ → ℕ}
    (hpqSz : ∀ (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
      (stE : Expr (e2eOps ℓ P C K decT encT) Γ (PqxdhSimTypes.e2eKeyIndStateTy ℓ S))
      (qE : Expr (e2eOps ℓ P C K decT encT) Γ (CryptoVerification.E2E.Costed.keyIndQT S)),
      ((PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC
        (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) nAdv stE qE).size ≤
        stE.size + qE.size + pqxdhStepSize nAdv)
    (qStart : ℕ) (b : SignalPqxdh.QueryBudget) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    (kiStepHaltedC qStart b σE kqE).size ≤
      σE.size + kqE.size + kiStepHaltedSize pqxdhStepSize qStart b := by
  let τ0 : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)
  let τr : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.keyIndRT (PqxdhSimTypes.e2eKeyIndStateTy ℓ S)
  have hok := E2EStateRepr.size_kiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) b.q_total qStart (Γ := [τ0]) (.fst .v0) (.snd .v0)
  have hst := hpqSz b.q_total (Γ := [τ0]) (StartAndExtSmAux.drvSt (.fst .v0)) (.snd .v0)
  have hset := M3Interfaces.size_drvSetStE (O := e2eOps ℓ P C K decT encT) (S := S) (ℓ := ℓ)
    (Γ := [τr, τ0]) (.fst (.var (.succ .zero))) (.snd .v0)
  have hmir := E2EStateRepr.size_bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := [τr, τ0])
    (M3Interfaces.drvSetStE (.fst (.var (.succ .zero))) (.snd .v0))
    (.snd (.var (.succ .zero))) (.fst .v0)
  dsimp only [τ0, τr] at hok hst hset hmir
  simp only [kiStepHaltedC, kiStepBodyC, kiStepHaltedSize, lift1Comp_size, StartAndExtSmAux.drvSt,
    Comp.size, Expr.size, Expr.v0] at hok hst hset hmir ⊢
  omega

theorem kiStepHaltedC_queries (qStart : ℕ) (b : SignalPqxdh.QueryBudget)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ) :
    (kiStepHaltedC qStart b σE kqE).queries w (fun _ => 0) = 0 := by
  simp only [kiStepHaltedC, kiStepBodyC, Comp.queries, lift1Comp_queries,
    (PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC_queries
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ),
    Nat.add_zero, Nat.max_self]

private theorem stepALiftP_eq_atomicLiftP (Pt : Type) {α : Type} (p : ProbComp α) :
    (PqxdhSimTypes.stepAIface ℓ
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)).liftP p =
      (e2eSessionTargetIface ℓ Pt).liftP p := rfl

private theorem atomicLiftP_pure {α : Type} (x : α) :
    (e2eSessionTargetIface ℓ Pt).liftP (pure x) = pure x := by
  rw [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP]
  exact CryptoVerification.E2E.bhLiftP_pure x

private theorem atomicLiftP_bind {α β : Type} (p : ProbComp α) (f : α → ProbComp β) :
    (e2eSessionTargetIface ℓ Pt).liftP (p >>= f) =
      ((e2eSessionTargetIface ℓ Pt).liftP p >>=
        fun a => (e2eSessionTargetIface ℓ Pt).liftP (f a)) := by
  rw [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP]
  exact CryptoVerification.E2E.bhLiftP_bind p f

private theorem atomicLiftP_map {α β : Type} (f : α → β) (p : ProbComp α) :
    (e2eSessionTargetIface ℓ Pt).liftP (f <$> p) =
      f <$> (e2eSessionTargetIface ℓ Pt).liftP p := by
  rw [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP]
  exact CryptoVerification.E2E.bhLiftP_map f p

private def kiCorruptPromoted {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S) : Bool :=
  match kq with
  | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u
  | _ => false

private theorem bhShallowStepPreNonCtl_ki
    (qep : ℕ) (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S) :
    bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
      C K qep decT encT σ (.inl (.inl kq)) =
      if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
        pure (.inl (.inl .noneResp), σ)
      else if kiCorruptPromoted σ kq then
        pure (.inl (.inl .noneResp), σ)
      else
        ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run σ.st >>= fun out =>
          pure (.inl (.inl out.1), bhE2EMirror { σ with st := out.2 } kq out.1)) := by
  dsimp only [bhShallowStepPreNonCtl, kiCorruptPromoted]
  cases kq <;> rfl

private theorem liftVal_kiBodyNone (σ1 : BHE2EDrvState S ℓ) :
    liftVal (Pt := Pt) (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
      (.inl (), e2eDrvStateEnc σ1) =
    (.inl (), drvEnc (Pt := Pt) σ1) :=
  eq_of_heq (liftVal_heq _)

private theorem liftVal_kiBodySome (kr : SignalPqxdh.KeyIndResponse) (σ1 : BHE2EDrvState S ℓ) :
    liftVal (Pt := Pt) (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
      (CryptoVerification.E2E.Costed.keyIndRenc kr, e2eDrvStateEnc σ1) =
    (keyIndRenc (ℓ := ℓ) (Pt := Pt) kr, drvEnc (Pt := Pt) σ1) := by
  cases kr <;> exact eq_of_heq (liftVal_heq _)

theorem kiStepHaltedC_eval (qStart qep : ℕ) (b : SignalPqxdh.QueryBudget)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S)
    (hσ : σE.eval ρ = drvEnc σ) (hkq : kqE.eval ρ = keyIndQenc kq)
    (hMir : DrvQueryBounded b.q_total qStart σ)
    (hReach : KeyIndReachBounded S b.q_total σ.st) :
    (kiStepHaltedC qStart b σE kqE).eval ρ =
      (e2eSessionTargetIface ℓ Pt).liftP
        ((fun out => (atomicGameRespEnc out.1, drvEnc out.2)) <$>
          bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
            C K qep decT encT σ (.inl (.inl kq))) := by
  have harg : (Expr.pair σE kqE).eval ρ =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S))
        (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.keyIndQenc kq) := by
    dsimp only [Expr.eval]; rw [hσ, hkq, ← liftVal_e2eDrvStateEnc_eq, ← liftVal_keyIndQenc_eq]; rfl
  have hev : (E2EStateRepr.kiQueryOkE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      b.q_total qStart (.fst .v0) (.snd .v0)).eval
      (.cons (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.keyIndQenc kq) .nil) =
      (bhDrvKiQueryOk P σ.toModelDriverBase kq && !kiCorruptPromoted σ kq) := by
    rw [E2EStateRepr.eval_kiQueryOkE (Pt := Pt) b.q_total qStart hP
      (.fst .v0) (.snd .v0) _ rfl rfl hMir.prins_le hMir.instMeta_le]
    refine congrArg (fun x => bhDrvKiQueryOk P σ.toModelDriverBase kq && !x) ?_
    clear hkq harg; cases kq <;> rfl
  rw [bhShallowStepPreNonCtl_ki]
  dsimp only [kiStepHaltedC, Comp.eval]
  rw [lift1Comp_eval _ _ ρ _ harg]
  dsimp only [kiStepBodyC, Comp.eval]
  rw [hev]
  cases hok : bhDrvKiQueryOk P σ.toModelDriverBase kq
  · simp only [Bool.false_and, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      map_pure, pure_bind, atomicLiftP_pure]
    congr 1
    change (Sum.inl (Sum.inl (liftVal (Pt := Pt)
        (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
        (.inl (), e2eDrvStateEnc σ)).1),
      (liftVal (Pt := Pt)
        (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
        (.inl (), e2eDrvStateEnc σ)).2) = _
    rw [liftVal_kiBodyNone]; rfl
  · cases hpr : kiCorruptPromoted σ kq
    · simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [(PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC_eval
        (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total _ _ _ σ.st kq hP
        (by simp [StartAndExtSmAux.drvSt, Expr.eval, Expr.v0, e2eDrvStateEnc]) rfl
        hReach.setup hReach.advKeys_le, stepALiftP_eq_atomicLiftP Pt]
      simp only [atomicLiftP_bind, atomicLiftP_pure, map_eq_bind_pure_comp,
        Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨kr, st'⟩ => congrArg pure ?_
      have hmir : (E2EStateRepr.bhE2EMirrorE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          (M3Interfaces.drvSetStE (.fst (.var (.succ .zero))) (.snd .v0))
          (.snd (.var (.succ .zero))) (.fst .v0)).eval
          (.cons (CryptoVerification.E2E.Costed.keyIndRenc kr,
            PqxdhSimTypes.e2eKeyIndStateToVal st')
            (.cons (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.keyIndQenc kq) .nil)) =
          e2eDrvStateEnc (bhE2EMirror { σ with st := st' } kq kr) :=
        E2EStateRepr.eval_bhE2EMirrorE_enc (Pt := Pt) _ _ _ _ { σ with st := st' } kq kr
          (M3Interfaces.eval_drvSetStE _ _ _ rfl rfl) rfl rfl
      dsimp only [Expr.v0] at hmir
      dsimp only [Expr.eval, Expr.v0, Env.get, atomicGameRespEnc]
      rw [hmir]
      change (Sum.inl (Sum.inl (liftVal (Pt := Pt)
          (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
          (CryptoVerification.E2E.Costed.keyIndRenc kr,
            e2eDrvStateEnc (bhE2EMirror { σ with st := st' } kq kr))).1),
        (liftVal (Pt := Pt)
          (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
          (CryptoVerification.E2E.Costed.keyIndRenc kr,
            e2eDrvStateEnc (bhE2EMirror { σ with st := st' } kq kr))).2) = _
      rw [liftVal_kiBodySome]; rfl
    · simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        map_pure, pure_bind, atomicLiftP_pure]
      congr 1
      change (Sum.inl (Sum.inl (liftVal (Pt := Pt)
          (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
          (.inl (), e2eDrvStateEnc σ)).1),
        (liftVal (Pt := Pt)
          (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
          (.inl (), e2eDrvStateEnc σ)).2) = _
      rw [liftVal_kiBodyNone]; rfl

private theorem size_extractDrKey32E_aux {Γ : List (Ty (e2eSig ℓ))}
    (krE : Expr (e2eOps ℓ P C K decT encT) Γ CryptoVerification.E2E.Costed.keyIndRT) :
    (StartAndExtSmAux.extractDrKey32E (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      krE).size ≤ krE.size + 90 := by
  unfold StartAndExtSmAux.extractDrKey32E
  dsimp only [PqxdhSimTypes.v, PqxdhSimTypes.Ext.wk]
  simp only [PqxdhSimTypes.eCaseSum, TablesHonest.size_e2ePureOp, E2EPureOp.opSize, Expr.size,
    show bits 32 = 6 from rfl]
  omega

@[expose] def localStartBodyC (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool) :
    Comp (e2eOps ℓ P C K decT encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
      [.prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S)]
      (.prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
        (.opt CryptoVerification.E2E.Costed.BV256)) :=
  .caseOpt
    (E2EStateRepr.prepStartSpkE qStart b.q_total b.q_total b.q_total b.q_total
      (.fst (.var .zero)) (.snd (.var .zero)))
    (.ret (.pair (.pair .none (.fst (.var .zero))) .none))
    (.bind
      ((PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC
        (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total
        (StartAndExtSmAux.drvSt (.fst (.var (.succ .zero))))
        (mkTestSessionE (.snd (.var (.succ .zero)))))
      (.bind
        ((PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC
          (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) (b.q_total + 1)
          (.snd (.var .zero))
          (mkRevealSpkSkE (.var (.succ .zero))))
        (.bind
          (StartAndExtSm.sampleBv256C (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ))
          (.bind
            (StartAndExtSm.finishStartSpkC
              (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
              qStart b.q_total b.q_total b.q_total b.q_total
              (.some (.bool bm))
              (M3Interfaces.drvSetStE
                (.fst (.var (.succ (.succ (.succ (.succ .zero))))))
                (.snd (.var (.succ .zero))))
              (.snd (.var (.succ (.succ (.succ (.succ .zero))))))
              (.fst (.var (.succ (.succ .zero))))
              (.fst (.var (.succ .zero)))
              (.var .zero))
            (.ret (.pair (.var .zero)
              (.caseOpt
                (StartAndExtSmAux.extractDrKey32E (.fst (.var (.succ (.succ (.succ .zero))))))
                .none (.some (.snd (.var .zero))))))))))

/-- Session-promotion subprogram appending `initKemFailSessionTrackE2EE` on successful promotion. -/
@[expose] def localStartHaltedC (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ
      (.prod (.opt .nat) (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt)))) :=
  .bind (.ret (.pair σHE sidE))
    (.bind
      (lift1Comp (a := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S))
        (b := .prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
          (.opt CryptoVerification.E2E.Costed.BV256))
        (.pair (.fst (.fst (.var .zero))) (.snd (.var .zero)))
        (localStartBodyC b qStart bm))
      (.ret
        (.pair (.fst (.fst (.var .zero)))
          (.pair (.snd (.fst (.var .zero)))
            (.caseOpt (.fst (.fst (.var .zero)))
              (.snd (.fst (.var (.succ .zero))))
              (.caseOpt (.snd (.var (.succ .zero)))
                (.snd (.fst (.var (.succ (.succ .zero)))))
                (snocAtomicE qStart
                  (.snd (.fst (.var (.succ (.succ (.succ .zero))))))
                  (initKemFailSessionTrackE2EE (.var .zero)))))))))

@[expose] def localStartHaltedCost (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  600 * qStart + 7600 * b.q_total +
    PqxdhSim.pqxdh1KeyRealStepCost S b.q_total +
    PqxdhSim.pqxdh1KeyRealStepCost S (b.q_total + 1) + 100000

@[expose] def localStartHaltedSize (pqxdhStepSize : ℕ → ℕ)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  7 * bits qStart + 10 * bits b.q_total +
    pqxdhStepSize b.q_total + pqxdhStepSize (b.q_total + 1) + 4200

theorem localStartHaltedC_cost (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    (localStartHaltedC b qStart bm σHE sidE).cost ≤
      σHE.cost + sidE.cost + localStartHaltedCost S b qStart := by
  let τ0 : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S)
  let τuj : Ty (e2eSig ℓ) :=
    .prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv)
  let τr : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.keyIndRT (PqxdhSimTypes.e2eKeyIndStateTy ℓ S)
  let τres : Ty (e2eSig ℓ) := .prod (.opt .nat) (e2eDrvStateTy S ℓ)
  have hp := E2EStateRepr.cost_prepStartSpkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart b.q_total b.q_total b.q_total b.q_total
    (Γ := [τ0]) (.fst (.var .zero)) (.snd (.var .zero))
  have hs1 := (PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC_cost
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total (Γ := [τuj, τ0])
    (StartAndExtSmAux.drvSt (.fst (.var (.succ .zero)))) (mkTestSessionE (.snd (.var (.succ .zero))))
  have hs2 := (PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC_cost
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) (b.q_total + 1) (Γ := [τr, τuj, τ0])
    (.snd (.var .zero)) (mkRevealSpkSkE (.var (.succ .zero)))
  have hfin := StartAndExtSm.finishStartSpkC_cost (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C)
    (K := K) (decT := decT) (encT := encT)
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
    qStart b.q_total b.q_total b.q_total b.q_total
    (Γ := [CryptoVerification.E2E.Costed.BV256, τr, τr, τuj, τ0])
    (.some (.bool bm))
    (M3Interfaces.drvSetStE (.fst (.var (.succ (.succ (.succ (.succ .zero)))))) (.snd (.var (.succ .zero))))
    (.snd (.var (.succ (.succ (.succ (.succ .zero))))))
    (.fst (.var (.succ (.succ .zero)))) (.fst (.var (.succ .zero))) (.var .zero)
  have hset := M3Interfaces.cost_drvSetStE (O := e2eOps ℓ P C K decT encT) (S := S) (ℓ := ℓ)
    (Γ := [CryptoVerification.E2E.Costed.BV256, τr, τr, τuj, τ0])
    (.fst (.var (.succ (.succ (.succ (.succ .zero)))))) (.snd (.var (.succ .zero)))
  have hex := StartAndExtSmAux.cost_extractDrKey32E (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := [τres, CryptoVerification.E2E.Costed.BV256, τr, τr, τuj, τ0])
    (.fst (.var (.succ (.succ (.succ .zero)))))
  let τp0 : Ty (atomicSig ℓ Pt) :=
    .prod (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))) (sidT (ℓ := ℓ) (Pt := Pt) S)
  let τout : Ty (atomicSig ℓ Pt) :=
    liftTy (Pt := Pt) (.prod τres (.opt CryptoVerification.E2E.Costed.BV256))
  have hsn := snocAtomicE_cost (O := atomicE2EOps ℓ P C K decT encT) qStart
    (Γ := BV256 :: .nat :: τout :: τp0 :: Γ)
    (.snd (.fst (.var (.succ (.succ (.succ .zero)))))) (initKemFailSessionTrackE2EE (.var .zero))
  have htr := initKemFailSessionTrackE2EE_cost (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := BV256 :: .nat :: τout :: τp0 :: Γ) (.var .zero)
  have hpq1 : (PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepCost b.q_total =
      PqxdhSim.pqxdh1KeyRealStepCost S b.q_total := rfl
  have hpq2 : (PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepCost (b.q_total + 1) =
      PqxdhSim.pqxdh1KeyRealStepCost S (b.q_total + 1) := rfl
  rw [hpq1] at hs1; rw [hpq2] at hs2
  dsimp only [τ0, τuj, τr, τres, τp0, τout] at hp hs1 hs2 hfin hset hex hsn htr
  simp only [localStartHaltedC, localStartBodyC, localStartHaltedCost, lift1Comp_cost,
    StartAndExtSmAux.drvSt, mkTestSessionE, mkRevealSpkSkE, StartAndExtSm.sampleBv256C_cost,
    StartAndExtSm.finishStartSpkCost, Comp.cost, Expr.cost]
    at hp hs1 hs2 hfin hset hex hsn htr ⊢
  omega

theorem localStartHaltedC_size {pqxdhStepSize : ℕ → ℕ}
    (hpqSz : ∀ (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
      (stE : Expr (e2eOps ℓ P C K decT encT) Γ (PqxdhSimTypes.e2eKeyIndStateTy ℓ S))
      (qE : Expr (e2eOps ℓ P C K decT encT) Γ (CryptoVerification.E2E.Costed.keyIndQT S)),
      ((PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC
        (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) nAdv stE qE).size ≤
        stE.size + qE.size + pqxdhStepSize nAdv)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    (localStartHaltedC b qStart bm σHE sidE).size ≤
      σHE.size + sidE.size + localStartHaltedSize pqxdhStepSize b qStart := by
  let τ0 : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S)
  let τuj : Ty (e2eSig ℓ) :=
    .prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv)
  let τr : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.keyIndRT (PqxdhSimTypes.e2eKeyIndStateTy ℓ S)
  let τres : Ty (e2eSig ℓ) := .prod (.opt .nat) (e2eDrvStateTy S ℓ)
  have hp := E2EStateRepr.size_prepStartSpkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart b.q_total b.q_total b.q_total b.q_total
    (Γ := [τ0]) (.fst (.var .zero)) (.snd (.var .zero))
  have hs1 := hpqSz b.q_total (Γ := [τuj, τ0])
    (StartAndExtSmAux.drvSt (.fst (.var (.succ .zero)))) (mkTestSessionE (.snd (.var (.succ .zero))))
  have hs2 := hpqSz (b.q_total + 1) (Γ := [τr, τuj, τ0])
    (.snd (.var .zero)) (mkRevealSpkSkE (.var (.succ .zero)))
  have hfin := M3Subprograms.size_finishStartSpkC (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C)
    (K := K) (decT := decT) (encT := encT)
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
    qStart b.q_total b.q_total b.q_total b.q_total
    (Γ := [CryptoVerification.E2E.Costed.BV256, τr, τr, τuj, τ0])
    (.some (.bool bm))
    (M3Interfaces.drvSetStE (.fst (.var (.succ (.succ (.succ (.succ .zero)))))) (.snd (.var (.succ .zero))))
    (.snd (.var (.succ (.succ (.succ (.succ .zero))))))
    (.fst (.var (.succ (.succ .zero)))) (.fst (.var (.succ .zero))) (.var .zero)
  have hset := M3Interfaces.size_drvSetStE (O := e2eOps ℓ P C K decT encT) (S := S) (ℓ := ℓ)
    (Γ := [CryptoVerification.E2E.Costed.BV256, τr, τr, τuj, τ0])
    (.fst (.var (.succ (.succ (.succ (.succ .zero)))))) (.snd (.var (.succ .zero)))
  have hex := size_extractDrKey32E_aux (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := [τres, CryptoVerification.E2E.Costed.BV256, τr, τr, τuj, τ0])
    (.fst (.var (.succ (.succ (.succ .zero)))))
  let τp0 : Ty (atomicSig ℓ Pt) :=
    .prod (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))) (sidT (ℓ := ℓ) (Pt := Pt) S)
  let τout : Ty (atomicSig ℓ Pt) :=
    liftTy (Pt := Pt) (.prod τres (.opt CryptoVerification.E2E.Costed.BV256))
  have hsn := snocAtomicE_size (O := atomicE2EOps ℓ P C K decT encT) qStart
    (Γ := BV256 :: .nat :: τout :: τp0 :: Γ)
    (.snd (.fst (.var (.succ (.succ (.succ .zero)))))) (initKemFailSessionTrackE2EE (.var .zero))
  have htr := initKemFailSessionTrackE2EE_size (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := BV256 :: .nat :: τout :: τp0 :: Γ) (.var .zero)
  dsimp only [τ0, τuj, τr, τres, τp0, τout] at hp hs1 hs2 hfin hset hex hsn htr
  simp only [localStartHaltedC, localStartBodyC, localStartHaltedSize, lift1Comp_size,
    StartAndExtSmAux.drvSt, mkTestSessionE, mkRevealSpkSkE, StartAndExtSm.sampleBv256C,
    Comp.size, Expr.size]
    at hp hs1 hs2 hfin hset hex hsn htr ⊢
  omega

private theorem env_get_zero {S₀ : Sig} {Γ : List (Ty S₀)} {t : Ty S₀}
    (x : t.denote) (ρ : Env Γ) : (Env.cons x ρ).get Var.zero = x := rfl

private theorem env_get_succ {S₀ : Sig} {Γ : List (Ty S₀)} {t u : Ty S₀}
    (x : u.denote) (ρ : Env Γ) (v : Var Γ t) : (Env.cons x ρ).get (Var.succ v) = ρ.get v := rfl

private theorem liftVal_localStartOut (idx? : Option ℕ) (σ1 : BHE2EDrvState S ℓ)
    (k? : Option (BitVec 256)) :
    liftVal (Pt := Pt)
      (t := .prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
        (.opt CryptoVerification.E2E.Costed.BV256))
      ((idx?, e2eDrvStateEnc σ1), k?) =
    ((idx?, drvEnc (Pt := Pt) σ1), k?) :=
  eq_of_heq (liftVal_heq _)

theorem localStartHaltedC_queries (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ) :
    (localStartHaltedC b qStart bm σHE sidE).queries w (fun _ => 0) = 0 := by
  simp only [localStartHaltedC, localStartBodyC, Comp.queries, lift1Comp_queries,
    (PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC_queries
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ),
    StartAndExtSm.sampleBv256C_queries
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ),
    StartAndExtSm.finishStartSpkC_queries
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ),
    Nat.add_zero, Nat.max_self]

theorem localStartHaltedC_eval (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes))
    (sid : SignalPqxdh.SessionId S)
    (hσH : σHE.eval ρ = (drvEnc σH.1, σH.2.map sessHEnc))
    (hsid : sidE.eval ρ = sidV sid)
    (hMir : DrvQueryBounded b.q_total qStart σH.1)
    (hReach : KeyIndReachBounded S b.q_total σH.1.st)
    (hTracks : σH.2.length ≤ qStart) :
    (localStartHaltedC b qStart bm σHE sidE).eval ρ =
      (e2eSessionTargetIface ℓ Pt).liftP
        ((fun out => (out.1, (drvEnc out.2.1, out.2.2.map sessHEnc))) <$>
          bhE2ELocalStartSessionTracked
            (fun kS => initKemFailSessionTrack C.F Bytes kS.2.2)
            (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K (some bm) σH sid) := by
  rcases σH with ⟨σ, tracks⟩
  dsimp only [localStartHaltedC, Comp.eval, bhE2ELocalStartSessionTracked]
  rw [pure_bind]
  let ρ1 : Env (.prod (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))) (sidT (ℓ := ℓ) (Pt := Pt) S) :: Γ) :=
    .cons ((Expr.pair σHE sidE).eval ρ) ρ
  have harg : (Expr.pair (O := atomicE2EOps ℓ P C K decT encT)
      (.fst (.fst (.var .zero))) (.snd (.var .zero))).eval ρ1 =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S))
        (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.sidV sid) := by
    dsimp only [ρ1, Expr.eval, Env.get]
    rw [hσH, hsid, ← liftVal_e2eDrvStateEnc_eq, ← liftVal_sidV_eq]; rfl
  have hMir0 : E2EStateRepr.DrvMirrorBounded b.q_total b.q_total b.q_total b.q_total b.q_total qStart σ :=
    ⟨hMir.prins_le, hMir.bundles_le, hMir.opks_le, hMir.sends_le, hMir.corrPrins_le,
     hMir.insts_le, hMir.instMeta_le⟩
  change ((lift1Comp _ (localStartBodyC b qStart bm)).eval ρ1 >>= _) = _
  rw [lift1Comp_eval _ _ ρ1 _ harg]
  dsimp only [localStartBodyC, Comp.eval]
  rw [E2EStateRepr.eval_prepStartSpkE_mirrorBounded (Pt := Pt)
    qStart b.q_total b.q_total b.q_total b.q_total b.q_total _ _ _ σ sid rfl rfl hMir0 le_rfl]
  rcases hg : bhE2EGuard σ sid with _ | ⟨hdr, bnd, ⟨u, j⟩⟩
  · simp only [Option.map, Expr.eval, Env.get, map_pure, pure_bind, atomicLiftP_pure]
    rw [liftVal_localStartOut]
    dsimp only [Expr.eval, Env.get]
    rw [show (σHE.eval ρ).2 = tracks.map sessHEnc from congrArg Prod.snd hσH]
  · simp only [Option.map]
    rw [(PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC_eval
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total _ _ _ σ.st
      (.testSession sid) hP (by simp [StartAndExtSmAux.drvSt, Expr.eval, e2eDrvStateEnc])
      (by simp [M3Interfaces.eval_mkTestSessionE, Expr.eval, TablesHonest.sidOfV_sidV])
      hReach.setup hReach.advKeys_le, stepALiftP_eq_atomicLiftP Pt]
    simp only [atomicLiftP_bind, atomicLiftP_pure, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro ⟨kr1, st1⟩ hout1
    have hout1' : (kr1, st1) ∈ support
        ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.testSession sid)).run σ.st) :=
      PrefixRedHaltedEval.mem_support_of_atomicSessionLiftP _ hout1
    have hReach1 : KeyIndReachBounded S (b.q_total + 1) st1 :=
      hReach.pqxdhStep (.testSession sid) hout1'
    dsimp only [Comp.eval]
    rw [(PqxdhSim.pqxdhSimIface ℓ S P C K decT encT).stepC_eval
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) (b.q_total + 1) _ _ _ st1
      (.revealSpkSk u j) hP rfl (by simp [M3Interfaces.eval_mkRevealSpkSkE, Expr.eval])
      hReach1.setup hReach1.advKeys_le, stepALiftP_eq_atomicLiftP Pt]
    simp only [atomicLiftP_bind, atomicLiftP_pure, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨kr2, st2⟩ => ?_
    dsimp only [Comp.eval]
    rw [StartAndExtSm.sampleBv256C_eval, stepALiftP_eq_atomicLiftP Pt]
    refine bind_congr fun ac => ?_
    have hMir2 : DrvMirrorBounded b.q_total b.q_total b.q_total b.q_total b.q_total qStart
        { σ with st := st2 } :=
      ⟨hMir.prins_le, hMir.bundles_le, hMir.opks_le, hMir.sends_le, hMir.corrPrins_le,
       hMir.insts_le, hMir.instMeta_le, hMir.revSpks_le⟩
    rw [StartAndExtSm.finishStartSpkC_eval (Pt := Pt)
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
      qStart b.q_total b.q_total b.q_total b.q_total b.q_total _ _ _ _ _ _ _
      { σ with st := st2 } sid kr1 kr2
      (M3Interfaces.eval_drvSetStE _ _ _ rfl rfl) rfl rfl rfl hMir2 le_rfl]
    dsimp only [Comp.eval]
    simp only [pure_bind, Expr.eval, env_get_zero, env_get_succ]
    rcases hfin : bhE2EFinishStartSpk C K (some bm) { σ with st := st2 } sid kr1 kr2 ac with
      ⟨_ | idx, σ'⟩
    · dsimp only
      rw [liftVal_localStartOut]
      dsimp only
      rw [show (σHE.eval ρ).2 = tracks.map sessHEnc from congrArg Prod.snd hσH]
    · rcases bhE2EFinishStartSpk_some_drKey C K (some bm) { σ with st := st2 } sid kr1 kr2 ac hfin
        with ⟨dk, rfl, hrk, hck, hpqk⟩
      rw [StartAndExtSmAux.eval_extractDrKey32E]
      simp only [Expr.eval, env_get_zero, env_get_succ,
        TablesHonest.keyIndRdec_keyIndRenc, hrk, hck, hpqk,
        beq_self_eq_true, ↓reduceIte, Bool.and_self]
      rw [liftVal_localStartOut]
      dsimp only
      congr 1
      refine Prod.ext rfl (Prod.ext rfl ?_)
      rw [snocAtomicE_eval qStart _ _ _
          (by simp [Expr.eval, hσH, hTracks]),
        initKemFailSessionTrackE2EE_eval]
      simp [Expr.eval, hσH, List.map_append, bhKeySOf]

/-! ## Clamped halted prefix subprograms -/

@[expose] def finishPrefixHaltedClampedC (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ .bool :=
  lift1Comp (a := .prod (e2eDrvStateTy S ℓ) (.prod .bool .bool)) (b := .bool)
    (.pair σE (.pair bOutE flipE))
    (FreshnessSim.finishPrefixClampedC (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
      qStart b.q_total (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0)))

@[expose] def finishPrefixHaltedClampedCost (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  FreshnessSim.finishPrefixClampedCost S qStart b.q_total + 20

@[expose] def finishPrefixHaltedClampedSize (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  FreshnessSim.finishPrefixClampedSize S qStart b.q_total + 20

theorem finishPrefixHaltedClampedC_cost (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    (finishPrefixHaltedClampedC b qStart σE bOutE flipE).cost ≤
      σE.cost + bOutE.cost + flipE.cost + finishPrefixHaltedClampedCost S b qStart := by
  have hb := FreshnessSim.cost_finishPrefixClampedC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
    qStart b.q_total (Γ := [.prod (e2eDrvStateTy S ℓ) (.prod .bool .bool)])
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
  simp only [finishPrefixHaltedClampedC, finishPrefixHaltedClampedCost, lift1Comp_cost,
    Expr.cost, Expr.v0] at hb ⊢
  omega

theorem finishPrefixHaltedClampedC_size (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    (finishPrefixHaltedClampedC b qStart σE bOutE flipE).size ≤
      σE.size + bOutE.size + flipE.size + finishPrefixHaltedClampedSize S b qStart := by
  have hb := FreshnessSim.size_finishPrefixClampedC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
    qStart b.q_total (Γ := [.prod (e2eDrvStateTy S ℓ) (.prod .bool .bool)])
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
  simp only [finishPrefixHaltedClampedC, finishPrefixHaltedClampedSize, lift1Comp_size,
    Expr.size, Expr.v0] at hb ⊢
  omega

theorem finishPrefixHaltedClampedC_queries (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool)
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ) :
    (finishPrefixHaltedClampedC b qStart σE bOutE flipE).queries w (fun _ => 0) = 0 := by
  rw [finishPrefixHaltedClampedC, lift1Comp_queries]
  exact FreshnessSim.queries_finishPrefixClampedC
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) qStart b.q_total _ _ _
    (fun g => w (liftSessionTag g))

theorem finishPrefixHaltedClampedC_eval (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ)
    (hσ : σE.eval ρ = drvEnc σ)
    (hInsts : σ.insts.length ≤ min qStart (min b.q_total S.N_send_tot))
    (hTested : (σ.st.sessions.filter (·.tested)).length ≤ min qStart (min b.q_total S.N_send_tot))
    (hRespUntested : ∀ r ∈ σ.st.respSessions, r.tested = false)
    (hst : PqxdhSimTypes.stListBounded S b.q_total σ.st) :
    (finishPrefixHaltedClampedC b qStart σE bOutE flipE).eval ρ =
      (e2eSessionTargetIface ℓ Pt).liftP
        (bhShallowFinishPrefix P σ (bOutE.eval ρ) (flipE.eval ρ)) := by
  have harg : (Expr.pair σE (.pair bOutE flipE)).eval ρ =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ) (.prod .bool .bool))
        (e2eDrvStateEnc σ, (bOutE.eval ρ, flipE.eval ρ)) := by
    dsimp only [Expr.eval]; rw [hσ, ← liftVal_e2eDrvStateEnc_eq]; rfl
  rw [finishPrefixHaltedClampedC, lift1Comp_eval _ _ ρ _ harg,
    FreshnessSim.eval_finishPrefixClampedC _ qStart b.q_total _ _ _ _ σ hP rfl hInsts hTested
      (Nat.le_min.mpr ⟨hst.sessions_fuel_le, hst.setup.sessions_le⟩)
      (Nat.le_min.mpr ⟨hst.respSessions_fuel_le, hst.setup.respSessions_le⟩)
      (Nat.le_min.mpr ⟨hst.principals_fuel_le, hst.setup.principals_le⟩)
      (Nat.le_min.mpr ⟨hst.spkBundles_fuel_le, hst.setup.spkBundles_le⟩)
      hRespUntested]
  exact id_map _

@[expose] def kiStepBodyClampedC (qStart : ℕ) (b : SignalPqxdh.QueryBudget) :
    Comp (e2eOps ℓ P C K decT encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
      [.prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)]
      (.prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ)) :=
  let nInst := min qStart (min b.q_total S.N_send_tot)
  .ite (E2EStateRepr.kiQueryOkE b.q_total nInst (.fst .v0) (.snd .v0))
    (.bind
      (PqxdhSim.pqxdh1KeyRealStepClampedC (Pt := Pt) ℓ S P C K decT encT
        (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total
        (StartAndExtSmAux.drvSt (.fst .v0)) (.snd .v0))
      (.ret (.pair (.fst .v0)
        (E2EStateRepr.bhE2EMirrorE
          (M3Interfaces.drvSetStE (.fst (.var (.succ .zero))) (.snd .v0))
          (.snd (.var (.succ .zero))) (.fst .v0)))))
    (.ret (.pair (.inl .unit) (.fst .v0)))

@[expose] def kiStepHaltedClampedC (qStart : ℕ) (b : SignalPqxdh.QueryBudget)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ
      (.prod (e2eTargetGameCodec S ℓ Pt).R (drvTy S ℓ Pt)) :=
  .bind
    (lift1Comp (a := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S))
      (b := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
      (.pair σE kqE) (kiStepBodyClampedC (Pt := Pt) qStart b))
    (.ret (.pair (.inl (.inl (.fst .v0))) (.snd .v0)))

@[expose] def kiStepHaltedClampedCost (S : SignalPqxdh.Setup) (qStart : ℕ)
    (b : SignalPqxdh.QueryBudget) : ℕ :=
  168 * b.q_total + 24 * min qStart (min b.q_total S.N_send_tot) +
    PqxdhSim.pqxdh1KeyRealStepClampedCost S b.q_total + 1600

@[expose] def kiStepHaltedClampedSize (S : SignalPqxdh.Setup) (qStart : ℕ)
    (b : SignalPqxdh.QueryBudget) : ℕ :=
  11 * bits b.q_total + bits (min qStart (min b.q_total S.N_send_tot)) +
    24 * bits (min b.q_total S.N_id) + 12 * bits (min b.q_total S.N_spk_tot) +
    10 * bits (min b.q_total S.N_opk_tot) + 10 * bits (min b.q_total S.N_send_tot) +
    12 * bits (min b.q_total S.N_recv_tot) + 21900

theorem kiStepHaltedClampedC_cost (qStart : ℕ) (b : SignalPqxdh.QueryBudget)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    (kiStepHaltedClampedC qStart b σE kqE).cost ≤
      σE.cost + kqE.cost + kiStepHaltedClampedCost S qStart b := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let τ0 : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)
  let τr : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.keyIndRT (PqxdhSimTypes.e2eKeyIndStateTy ℓ S)
  have hok := E2EStateRepr.cost_kiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) b.q_total nInst (Γ := [τ0]) (.fst .v0) (.snd .v0)
  have hst := PqxdhSim.pqxdh1KeyRealStepClampedC_cost ℓ S (Pt := Pt) P C K decT encT
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total (Γ := [τ0])
    (StartAndExtSmAux.drvSt (.fst .v0)) (.snd .v0)
  have hset := M3Interfaces.cost_drvSetStE (O := e2eOps ℓ P C K decT encT) (S := S) (ℓ := ℓ)
    (Γ := [τr, τ0]) (.fst (.var (.succ .zero))) (.snd .v0)
  have hmir := E2EStateRepr.cost_bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := [τr, τ0])
    (M3Interfaces.drvSetStE (.fst (.var (.succ .zero))) (.snd .v0))
    (.snd (.var (.succ .zero))) (.fst .v0)
  dsimp only [τ0, τr, nInst] at hok hst hset hmir
  simp only [kiStepHaltedClampedC, kiStepBodyClampedC, kiStepHaltedClampedCost, lift1Comp_cost,
    StartAndExtSmAux.drvSt, Comp.cost, Expr.cost, Expr.v0] at hok hst hset hmir ⊢
  omega

theorem kiStepHaltedClampedC_size (qStart : ℕ) (b : SignalPqxdh.QueryBudget)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    (kiStepHaltedClampedC qStart b σE kqE).size ≤
      σE.size + kqE.size + kiStepHaltedClampedSize S qStart b := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let τ0 : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)
  let τr : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.keyIndRT (PqxdhSimTypes.e2eKeyIndStateTy ℓ S)
  have hok := E2EStateRepr.size_kiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) b.q_total nInst (Γ := [τ0]) (.fst .v0) (.snd .v0)
  have hst := M3PqxdhSize.size_pqxdh1KeyRealStepClampedC ℓ S (Pt := Pt) P C K decT encT
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total (Γ := [τ0])
    (StartAndExtSmAux.drvSt (.fst .v0)) (.snd .v0)
  have hset := M3Interfaces.size_drvSetStE (O := e2eOps ℓ P C K decT encT) (S := S) (ℓ := ℓ)
    (Γ := [τr, τ0]) (.fst (.var (.succ .zero))) (.snd .v0)
  have hmir := E2EStateRepr.size_bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := [τr, τ0])
    (M3Interfaces.drvSetStE (.fst (.var (.succ .zero))) (.snd .v0))
    (.snd (.var (.succ .zero))) (.fst .v0)
  dsimp only [τ0, τr, nInst, M3PqxdhSize.pqxdh1KeyRealStepClampedSize] at hok hst hset hmir
  simp only [kiStepHaltedClampedC, kiStepBodyClampedC, kiStepHaltedClampedSize, lift1Comp_size,
    StartAndExtSmAux.drvSt, Comp.size, Expr.size, Expr.v0] at hok hst hset hmir ⊢
  omega

theorem kiStepHaltedClampedC_queries (qStart : ℕ) (b : SignalPqxdh.QueryBudget)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ) :
    (kiStepHaltedClampedC qStart b σE kqE).queries w (fun _ => 0) = 0 := by
  simp only [kiStepHaltedClampedC, kiStepBodyClampedC, Comp.queries, lift1Comp_queries,
    PqxdhSim.pqxdh1KeyRealStepClampedC_queries ℓ S (Pt := Pt) P C K decT encT
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ),
    Nat.add_zero, Nat.max_self]

theorem kiStepHaltedClampedC_eval (qStart qep : ℕ) (b : SignalPqxdh.QueryBudget)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S)
    (hσ : σE.eval ρ = drvEnc σ) (hkq : kqE.eval ρ = keyIndQenc kq)
    (hPrins : σ.prins.length ≤ b.q_total)
    (hInstMeta : σ.instMeta.length ≤ min qStart (min b.q_total S.N_send_tot))
    (hst : PqxdhSimTypes.stListBounded S b.q_total σ.st) :
    (kiStepHaltedClampedC qStart b σE kqE).eval ρ =
      (e2eSessionTargetIface ℓ Pt).liftP
        ((fun out => (atomicGameRespEnc out.1, drvEnc out.2)) <$>
          bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
            C K qep decT encT σ (.inl (.inl kq))) := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  have harg : (Expr.pair σE kqE).eval ρ =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S))
        (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.keyIndQenc kq) := by
    dsimp only [Expr.eval]; rw [hσ, hkq, ← liftVal_e2eDrvStateEnc_eq, ← liftVal_keyIndQenc_eq]; rfl
  have hev : (E2EStateRepr.kiQueryOkE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      b.q_total nInst (.fst .v0) (.snd .v0)).eval
      (.cons (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.keyIndQenc kq) .nil) =
      (bhDrvKiQueryOk P σ.toModelDriverBase kq && !kiCorruptPromoted σ kq) := by
    rw [E2EStateRepr.eval_kiQueryOkE (Pt := Pt) b.q_total nInst hP
      (.fst .v0) (.snd .v0) _ rfl rfl hPrins hInstMeta]
    refine congrArg (fun x => bhDrvKiQueryOk P σ.toModelDriverBase kq && !x) ?_
    clear hkq harg; cases kq <;> rfl
  rw [bhShallowStepPreNonCtl_ki]
  dsimp only [kiStepHaltedClampedC, Comp.eval]
  rw [lift1Comp_eval _ _ ρ _ harg]
  dsimp only [kiStepBodyClampedC, Comp.eval]
  rw [hev]
  cases hok : bhDrvKiQueryOk P σ.toModelDriverBase kq
  · simp only [Bool.false_and, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      map_pure, pure_bind, atomicLiftP_pure]
    congr 1
    change (Sum.inl (Sum.inl (liftVal (Pt := Pt)
        (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
        (.inl (), e2eDrvStateEnc σ)).1),
      (liftVal (Pt := Pt)
        (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
        (.inl (), e2eDrvStateEnc σ)).2) = _
    rw [liftVal_kiBodyNone]; rfl
  · cases hpr : kiCorruptPromoted σ kq
    · simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [PqxdhSim.pqxdh1KeyRealStepClampedC_eval ℓ S (Pt := Pt) P C K decT encT
        (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total _ _ _ σ.st kq hP
        (by simp [StartAndExtSmAux.drvSt, Expr.eval, Expr.v0, e2eDrvStateEnc]) rfl
        hst, stepALiftP_eq_atomicLiftP Pt]
      simp only [atomicLiftP_bind, atomicLiftP_pure, map_eq_bind_pure_comp,
        Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨kr, st'⟩ => congrArg pure ?_
      have hmir : (E2EStateRepr.bhE2EMirrorE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          (M3Interfaces.drvSetStE (.fst (.var (.succ .zero))) (.snd .v0))
          (.snd (.var (.succ .zero))) (.fst .v0)).eval
          (.cons (CryptoVerification.E2E.Costed.keyIndRenc kr,
            PqxdhSimTypes.e2eKeyIndStateToVal st')
            (.cons (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.keyIndQenc kq) .nil)) =
          e2eDrvStateEnc (bhE2EMirror { σ with st := st' } kq kr) :=
        E2EStateRepr.eval_bhE2EMirrorE_enc (Pt := Pt) _ _ _ _ { σ with st := st' } kq kr
          (M3Interfaces.eval_drvSetStE _ _ _ rfl rfl) rfl rfl
      dsimp only [Expr.v0] at hmir
      dsimp only [Expr.eval, Expr.v0, Env.get, atomicGameRespEnc]
      rw [hmir]
      change (Sum.inl (Sum.inl (liftVal (Pt := Pt)
          (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
          (CryptoVerification.E2E.Costed.keyIndRenc kr,
            e2eDrvStateEnc (bhE2EMirror { σ with st := st' } kq kr))).1),
        (liftVal (Pt := Pt)
          (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
          (CryptoVerification.E2E.Costed.keyIndRenc kr,
            e2eDrvStateEnc (bhE2EMirror { σ with st := st' } kq kr))).2) = _
      rw [liftVal_kiBodySome]; rfl
    · simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        map_pure, pure_bind, atomicLiftP_pure]
      congr 1
      change (Sum.inl (Sum.inl (liftVal (Pt := Pt)
          (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
          (.inl (), e2eDrvStateEnc σ)).1),
        (liftVal (Pt := Pt)
          (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
          (.inl (), e2eDrvStateEnc σ)).2) = _
      rw [liftVal_kiBodyNone]; rfl

/-- Clamped `e2eOps` body of `localStartHaltedClampedC`, keeping `nPrins = b.q_total` to scan duplicate `corruptIK` entries losslessly. -/
@[expose] def localStartBodyClampedC (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool) :
    Comp (e2eOps ℓ P C K decT encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
      [.prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S)]
      (.prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
        (.opt CryptoVerification.E2E.Costed.BV256)) :=
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let nSpk := min b.q_total S.N_spk_tot
  .caseOpt
    (E2EStateRepr.prepStartSpkE nInst b.q_total nSpk b.q_total b.q_total
      (.fst (.var .zero)) (.snd (.var .zero)))
    (.ret (.pair (.pair .none (.fst (.var .zero))) .none))
    (.bind
      (PqxdhSim.pqxdhTestStepC (Pt := Pt) ℓ S P C K decT encT
        (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total
        (StartAndExtSmAux.drvSt (.fst (.var (.succ .zero))))
        (.snd (.var (.succ .zero))))
      (.bind
        (PqxdhSim.pqxdhRevealSpkStepC (Pt := Pt) ℓ S P C K decT encT
          (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total
          (.snd (.var .zero))
          (.fst (.var (.succ .zero)))
          (.snd (.var (.succ .zero))))
        (.bind
          (StartAndExtSm.sampleBv256C (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ))
          (.bind
            (StartAndExtSm.finishStartSpkC
              (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
              nInst b.q_total nSpk b.q_total b.q_total
              (.some (.bool bm))
              (M3Interfaces.drvSetStE
                (.fst (.var (.succ (.succ (.succ (.succ .zero))))))
                (.snd (.var (.succ .zero))))
              (.snd (.var (.succ (.succ (.succ (.succ .zero))))))
              (.fst (.var (.succ (.succ .zero))))
              (.fst (.var (.succ .zero)))
              (.var .zero))
            (.ret (.pair (.var .zero)
              (.caseOpt
                (StartAndExtSmAux.extractDrKey32E (.fst (.var (.succ (.succ (.succ .zero))))))
                .none (.some (.snd (.var .zero))))))))))

@[expose] def localStartHaltedClampedC (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ
      (.prod (.opt .nat) (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt)))) :=
  let nInst := min qStart (min b.q_total S.N_send_tot)
  .bind (.ret (.pair σHE sidE))
    (.bind
      (lift1Comp (a := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S))
        (b := .prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
          (.opt CryptoVerification.E2E.Costed.BV256))
        (.pair (.fst (.fst (.var .zero))) (.snd (.var .zero)))
        (localStartBodyClampedC (Pt := Pt) b qStart bm))
      (.ret
        (.pair (.fst (.fst (.var .zero)))
          (.pair (.snd (.fst (.var .zero)))
            (.caseOpt (.fst (.fst (.var .zero)))
              (.snd (.fst (.var (.succ .zero))))
              (.caseOpt (.snd (.var (.succ .zero)))
                (.snd (.fst (.var (.succ (.succ .zero)))))
                (snocAtomicE nInst
                  (.snd (.fst (.var (.succ (.succ (.succ .zero))))))
                  (initKemFailSessionTrackE2EE (.var .zero)))))))))

@[expose] def localStartHaltedClampedCost (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  600 * min qStart (min b.q_total S.N_send_tot) + 920 * b.q_total +
    6600 * min b.q_total S.N_spk_tot +
    PqxdhSim.pqxdhTestStepCost S b.q_total +
    PqxdhSim.pqxdhRevealSpkStepCost S b.q_total + 100000

@[expose] def localStartHaltedClampedSize (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  7 * bits (min qStart (min b.q_total S.N_send_tot)) + 8 * bits b.q_total +
    4 * bits (min b.q_total S.N_spk_tot) +
    3 * bits (min b.q_total S.N_send_tot) +
    3 * bits (min b.q_total S.N_recv_tot) + 8300

theorem localStartHaltedClampedC_cost (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    (localStartHaltedClampedC b qStart bm σHE sidE).cost ≤
      σHE.cost + sidE.cost + localStartHaltedClampedCost S b qStart := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let nSpk := min b.q_total S.N_spk_tot
  let τ0 : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S)
  let τuj : Ty (e2eSig ℓ) :=
    .prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv)
  let τr : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.keyIndRT (PqxdhSimTypes.e2eKeyIndStateTy ℓ S)
  let τres : Ty (e2eSig ℓ) := .prod (.opt .nat) (e2eDrvStateTy S ℓ)
  have hp := E2EStateRepr.cost_prepStartSpkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nInst b.q_total nSpk b.q_total b.q_total
    (Γ := [τ0]) (.fst (.var .zero)) (.snd (.var .zero))
  have hs1 := PqxdhSim.pqxdhTestStepC_cost ℓ S (Pt := Pt) P C K decT encT
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total (Γ := [τuj, τ0])
    (StartAndExtSmAux.drvSt (.fst (.var (.succ .zero)))) (.snd (.var (.succ .zero)))
  have hs2 := PqxdhSim.pqxdhRevealSpkStepC_cost ℓ S (Pt := Pt) P C K decT encT
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total (Γ := [τr, τuj, τ0])
    (.snd (.var .zero)) (.fst (.var (.succ .zero))) (.snd (.var (.succ .zero)))
  have hfin := StartAndExtSm.finishStartSpkC_cost (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C)
    (K := K) (decT := decT) (encT := encT)
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
    nInst b.q_total nSpk b.q_total b.q_total
    (Γ := [CryptoVerification.E2E.Costed.BV256, τr, τr, τuj, τ0])
    (.some (.bool bm))
    (M3Interfaces.drvSetStE (.fst (.var (.succ (.succ (.succ (.succ .zero)))))) (.snd (.var (.succ .zero))))
    (.snd (.var (.succ (.succ (.succ (.succ .zero))))))
    (.fst (.var (.succ (.succ .zero)))) (.fst (.var (.succ .zero))) (.var .zero)
  have hset := M3Interfaces.cost_drvSetStE (O := e2eOps ℓ P C K decT encT) (S := S) (ℓ := ℓ)
    (Γ := [CryptoVerification.E2E.Costed.BV256, τr, τr, τuj, τ0])
    (.fst (.var (.succ (.succ (.succ (.succ .zero)))))) (.snd (.var (.succ .zero)))
  have hex := StartAndExtSmAux.cost_extractDrKey32E (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := [τres, CryptoVerification.E2E.Costed.BV256, τr, τr, τuj, τ0])
    (.fst (.var (.succ (.succ (.succ .zero)))))
  let τp0 : Ty (atomicSig ℓ Pt) :=
    .prod (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))) (sidT (ℓ := ℓ) (Pt := Pt) S)
  let τout : Ty (atomicSig ℓ Pt) :=
    liftTy (Pt := Pt) (.prod τres (.opt CryptoVerification.E2E.Costed.BV256))
  have hsn := snocAtomicE_cost (O := atomicE2EOps ℓ P C K decT encT) nInst
    (Γ := BV256 :: .nat :: τout :: τp0 :: Γ)
    (.snd (.fst (.var (.succ (.succ (.succ .zero)))))) (initKemFailSessionTrackE2EE (.var .zero))
  have htr := initKemFailSessionTrackE2EE_cost (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := BV256 :: .nat :: τout :: τp0 :: Γ) (.var .zero)
  dsimp only [τ0, τuj, τr, τres, τp0, τout, nInst, nSpk] at hp hs1 hs2 hfin hset hex hsn htr
  simp only [localStartHaltedClampedC, localStartBodyClampedC, localStartHaltedClampedCost,
    lift1Comp_cost, StartAndExtSmAux.drvSt, StartAndExtSm.sampleBv256C_cost,
    StartAndExtSm.finishStartSpkCost, Comp.cost, Expr.cost]
    at hp hs1 hs2 hfin hset hex hsn htr ⊢
  omega

theorem localStartHaltedClampedC_size (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    (localStartHaltedClampedC b qStart bm σHE sidE).size ≤
      σHE.size + sidE.size + localStartHaltedClampedSize S b qStart := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let nSpk := min b.q_total S.N_spk_tot
  let τ0 : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S)
  let τuj : Ty (e2eSig ℓ) :=
    .prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv)
  let τr : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.keyIndRT (PqxdhSimTypes.e2eKeyIndStateTy ℓ S)
  let τres : Ty (e2eSig ℓ) := .prod (.opt .nat) (e2eDrvStateTy S ℓ)
  have hp := E2EStateRepr.size_prepStartSpkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nInst b.q_total nSpk b.q_total b.q_total
    (Γ := [τ0]) (.fst (.var .zero)) (.snd (.var .zero))
  have hs1 := M3PqxdhSize.size_pqxdhTestStepC ℓ S (Pt := Pt) P C K decT encT
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total (Γ := [τuj, τ0])
    (StartAndExtSmAux.drvSt (.fst (.var (.succ .zero)))) (.snd (.var (.succ .zero)))
  have hs2 := M3PqxdhSize.size_pqxdhRevealSpkStepC ℓ S (Pt := Pt) P C K decT encT
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total (Γ := [τr, τuj, τ0])
    (.snd (.var .zero)) (.fst (.var (.succ .zero))) (.snd (.var (.succ .zero)))
  have hfin := M3Subprograms.size_finishStartSpkC (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C)
    (K := K) (decT := decT) (encT := encT)
    (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
    nInst b.q_total nSpk b.q_total b.q_total
    (Γ := [CryptoVerification.E2E.Costed.BV256, τr, τr, τuj, τ0])
    (.some (.bool bm))
    (M3Interfaces.drvSetStE (.fst (.var (.succ (.succ (.succ (.succ .zero)))))) (.snd (.var (.succ .zero))))
    (.snd (.var (.succ (.succ (.succ (.succ .zero))))))
    (.fst (.var (.succ (.succ .zero)))) (.fst (.var (.succ .zero))) (.var .zero)
  have hset := M3Interfaces.size_drvSetStE (O := e2eOps ℓ P C K decT encT) (S := S) (ℓ := ℓ)
    (Γ := [CryptoVerification.E2E.Costed.BV256, τr, τr, τuj, τ0])
    (.fst (.var (.succ (.succ (.succ (.succ .zero)))))) (.snd (.var (.succ .zero)))
  have hex := size_extractDrKey32E_aux (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := [τres, CryptoVerification.E2E.Costed.BV256, τr, τr, τuj, τ0])
    (.fst (.var (.succ (.succ (.succ .zero)))))
  let τp0 : Ty (atomicSig ℓ Pt) :=
    .prod (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))) (sidT (ℓ := ℓ) (Pt := Pt) S)
  let τout : Ty (atomicSig ℓ Pt) :=
    liftTy (Pt := Pt) (.prod τres (.opt CryptoVerification.E2E.Costed.BV256))
  have hsn := snocAtomicE_size (O := atomicE2EOps ℓ P C K decT encT) nInst
    (Γ := BV256 :: .nat :: τout :: τp0 :: Γ)
    (.snd (.fst (.var (.succ (.succ (.succ .zero)))))) (initKemFailSessionTrackE2EE (.var .zero))
  have htr := initKemFailSessionTrackE2EE_size (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := BV256 :: .nat :: τout :: τp0 :: Γ) (.var .zero)
  dsimp only [τ0, τuj, τr, τres, τp0, τout, nInst, nSpk,
    M3PqxdhSize.pqxdhTestStepSize, M3PqxdhSize.pqxdhRevealSpkStepSize]
    at hp hs1 hs2 hfin hset hex hsn htr
  simp only [localStartHaltedClampedC, localStartBodyClampedC, localStartHaltedClampedSize,
    lift1Comp_size, StartAndExtSmAux.drvSt, StartAndExtSm.sampleBv256C, Comp.size, Expr.size]
    at hp hs1 hs2 hfin hset hex hsn htr ⊢
  omega

theorem localStartHaltedClampedC_queries (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ) :
    (localStartHaltedClampedC b qStart bm σHE sidE).queries w (fun _ => 0) = 0 := by
  simp only [localStartHaltedClampedC, localStartBodyClampedC, Comp.queries, lift1Comp_queries,
    PqxdhSim.pqxdhTestStepC_queries ℓ S (Pt := Pt) P C K decT encT
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ),
    PqxdhSim.pqxdhRevealSpkStepC_queries ℓ S (Pt := Pt) P C K decT encT
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ),
    StartAndExtSm.sampleBv256C_queries
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ),
    StartAndExtSm.finishStartSpkC_queries
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ),
    Nat.add_zero, Nat.max_self]

theorem localStartHaltedClampedC_eval (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes))
    (sid : SignalPqxdh.SessionId S)
    (hσH : σHE.eval ρ = (drvEnc σH.1, σH.2.map sessHEnc))
    (hsid : sidE.eval ρ = sidV sid)
    (hMir : DrvMirrorBounded b.q_total (min b.q_total S.N_spk_tot) b.q_total b.q_total b.q_total
      (min qStart (min b.q_total S.N_send_tot)) σH.1)
    (hst : PqxdhSimTypes.stListBounded S b.q_total σH.1.st)
    (hTracks : σH.2.length ≤ min qStart (min b.q_total S.N_send_tot)) :
    (localStartHaltedClampedC b qStart bm σHE sidE).eval ρ =
      (e2eSessionTargetIface ℓ Pt).liftP
        ((fun out => (out.1, (drvEnc out.2.1, out.2.2.map sessHEnc))) <$>
          bhE2ELocalStartSessionTracked
            (fun kS => initKemFailSessionTrack C.F Bytes kS.2.2)
            (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K (some bm) σH sid) := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let nSpk := min b.q_total S.N_spk_tot
  rcases σH with ⟨σ, tracks⟩
  dsimp only [localStartHaltedClampedC, Comp.eval, bhE2ELocalStartSessionTracked]
  rw [pure_bind]
  let ρ1 : Env (.prod (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))) (sidT (ℓ := ℓ) (Pt := Pt) S) :: Γ) :=
    .cons ((Expr.pair σHE sidE).eval ρ) ρ
  have harg : (Expr.pair (O := atomicE2EOps ℓ P C K decT encT)
      (.fst (.fst (.var .zero))) (.snd (.var .zero))).eval ρ1 =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S))
        (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.sidV sid) := by
    dsimp only [ρ1, Expr.eval, Env.get]
    rw [hσH, hsid, ← liftVal_e2eDrvStateEnc_eq, ← liftVal_sidV_eq]; rfl
  have hMir0 : E2EStateRepr.DrvMirrorBounded b.q_total nSpk b.q_total b.q_total b.q_total nInst σ :=
    ⟨hMir.prins_le, hMir.bundles_le, hMir.opks_le, hMir.sends_le, hMir.corrPrins_le,
     hMir.insts_le, hMir.instMeta_le⟩
  change ((lift1Comp _ (localStartBodyClampedC (Pt := Pt) b qStart bm)).eval ρ1 >>= _) = _
  rw [lift1Comp_eval _ _ ρ1 _ harg]
  dsimp only [localStartBodyClampedC, Comp.eval]
  rw [E2EStateRepr.eval_prepStartSpkE_mirrorBounded (Pt := Pt)
    nInst b.q_total nSpk b.q_total b.q_total b.q_total _ _ _ σ sid rfl rfl hMir0 le_rfl]
  rcases hg : bhE2EGuard σ sid with _ | ⟨hdr, bnd, ⟨u, j⟩⟩
  · simp only [Option.map, Expr.eval, Env.get, map_pure, pure_bind, atomicLiftP_pure]
    rw [liftVal_localStartOut]
    dsimp only [Expr.eval, Env.get]
    rw [show (σHE.eval ρ).2 = tracks.map sessHEnc from congrArg Prod.snd hσH]
  · simp only [Option.map]
    let τ0 : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S)
    let τuj : Ty (e2eSig ℓ) :=
      .prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv)
    let τr : Ty (e2eSig ℓ) :=
      .prod CryptoVerification.E2E.Costed.keyIndRT (PqxdhSimTypes.e2eKeyIndStateTy ℓ S)
    have hsid_ev : CryptoVerification.E2E.Costed.sidOfV
        ((Expr.snd (O := e2eOps ℓ P C K decT encT) (Γ := [τuj, τ0]) (.var (.succ .zero))).eval
          (.cons (t := τuj) (u, j)
            (.cons (t := τ0) (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.sidV sid) .nil))) =
        sid :=
      TablesHonest.sidOfV_sidV sid
    dsimp only [τ0, τuj] at hsid_ev
    rw [PqxdhSim.pqxdhTestStepC_eval ℓ S (Pt := Pt) P C K decT encT
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total _ _ _ σ.st
      (by simp [StartAndExtSmAux.drvSt, Expr.eval, e2eDrvStateEnc]) hst,
      hsid_ev, stepALiftP_eq_atomicLiftP Pt]
    simp only [atomicLiftP_bind, atomicLiftP_pure, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro ⟨kr1, st1⟩ hout1
    have hout1' : (kr1, st1) ∈ support
        ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.testSession sid)).run σ.st) :=
      PrefixRedHaltedEval.mem_support_of_atomicSessionLiftP _ hout1
    have hst1 : PqxdhSimTypes.stListBounded S b.q_total st1 :=
      PqxdhSim.stListBounded_of_testSession sid hst hout1'
    have hu_ev : (Expr.fst (O := e2eOps ℓ P C K decT encT) (Γ := [τr, τuj, τ0]) (.var (.succ .zero))).eval
        (.cons (t := τr) (CryptoVerification.E2E.Costed.keyIndRenc kr1, PqxdhSimTypes.e2eKeyIndStateToVal st1)
          (.cons (t := τuj) (u, j)
            (.cons (t := τ0) (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.sidV sid) .nil))) = u := rfl
    have hj_ev : (Expr.snd (O := e2eOps ℓ P C K decT encT) (Γ := [τr, τuj, τ0]) (.var (.succ .zero))).eval
        (.cons (t := τr) (CryptoVerification.E2E.Costed.keyIndRenc kr1, PqxdhSimTypes.e2eKeyIndStateToVal st1)
          (.cons (t := τuj) (u, j)
            (.cons (t := τ0) (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.sidV sid) .nil))) = j := rfl
    dsimp only [τ0, τuj, τr] at hu_ev hj_ev
    dsimp only [Comp.eval]
    rw [PqxdhSim.pqxdhRevealSpkStepC_eval ℓ S (Pt := Pt) P C K decT encT
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total _ _ _ _ st1
      rfl hst1, hu_ev, hj_ev, stepALiftP_eq_atomicLiftP Pt]
    simp only [atomicLiftP_bind, atomicLiftP_pure, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨kr2, st2⟩ => ?_
    dsimp only [Comp.eval]
    rw [StartAndExtSm.sampleBv256C_eval, stepALiftP_eq_atomicLiftP Pt]
    refine bind_congr fun ac => ?_
    have hMir2 : DrvMirrorBounded b.q_total nSpk b.q_total b.q_total b.q_total nInst
        { σ with st := st2 } :=
      ⟨hMir.prins_le, hMir.bundles_le, hMir.opks_le, hMir.sends_le, hMir.corrPrins_le,
       hMir.insts_le, hMir.instMeta_le, hMir.revSpks_le⟩
    rw [StartAndExtSm.finishStartSpkC_eval (Pt := Pt)
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
      nInst b.q_total nSpk b.q_total b.q_total b.q_total _ _ _ _ _ _ _
      { σ with st := st2 } sid kr1 kr2
      (M3Interfaces.eval_drvSetStE _ _ _ rfl rfl) rfl rfl rfl hMir2 le_rfl]
    dsimp only [Comp.eval]
    simp only [pure_bind, Expr.eval, env_get_zero, env_get_succ]
    rcases hfin : bhE2EFinishStartSpk C K (some bm) { σ with st := st2 } sid kr1 kr2 ac with
      ⟨_ | idx, σ'⟩
    · dsimp only
      rw [liftVal_localStartOut]
      dsimp only
      rw [show (σHE.eval ρ).2 = tracks.map sessHEnc from congrArg Prod.snd hσH]
    · rcases bhE2EFinishStartSpk_some_drKey C K (some bm) { σ with st := st2 } sid kr1 kr2 ac hfin
        with ⟨dk, rfl, hrk, hck, hpqk⟩
      rw [StartAndExtSmAux.eval_extractDrKey32E]
      simp only [Expr.eval, env_get_zero, env_get_succ,
        TablesHonest.keyIndRdec_keyIndRenc, hrk, hck, hpqk,
        beq_self_eq_true, ↓reduceIte, Bool.and_self]
      rw [liftVal_localStartOut]
      dsimp only
      congr 1
      refine Prod.ext rfl (Prod.ext rfl ?_)
      rw [snocAtomicE_eval nInst _ _ _
          (by dsimp only [nInst]; simp [Expr.eval, hσH, hTracks]),
        initKemFailSessionTrackE2EE_eval]
      simp [Expr.eval, hσH, List.map_append, bhKeySOf]

end PrefixSubprograms

end Computational.Proofs.E2E.Dsl.HaltedPrefixSubprogs
