/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.CostedTables -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.MacroLift -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
public import Computational.Proofs.E2E.Dsl.ClampsLossless -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.M3Interfaces -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.E2EStateRepr -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.FreshnessSim -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.StartAndExtSmAux -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.StartAndExtSm -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.M3Subprograms -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync

/-!
# Halted Handshake-Start and Session-Init Subprograms

Defines the atomic driver and tracker DSL encodings and the handshake-start and pure subprograms
(together with `b₀`-clamped variants) used by `KindRedHalted` over `atomicE2EOps`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.HaltedStartSessionSim

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp UniformSamplerTag bits
  partyToBool bytesToWordLE spqrMsgPayloadSuffix atomicSig atomicE2EOps
  e2eKeyIndTargetIface e2eSessionTargetIface
  AtomicPureOp AtomicCurveCheckOp AtomicSpqrKemOp B BV256 BV512 U32 U64 FinT
  sidT sidV sidOfV keyIndQT keyIndQenc keyIndQdec keyIndRT keyIndRenc keyIndRdec)
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState ShaCompress)
open CryptoGames.Ratchet.LibsignalSim (simInitKemFailTrack)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State)
open CryptoVerification.E2E (Bytes BinState BHE2EDrvState SampledSessionKey bhE2EGuard
  bhE2EFinishStartSpk bhKeySOf bhBytesWord bhDrvKiQueryOk bhNoOpkRespPromoted
  bhE2EMirror bhE2EDrvWon)
open CryptoVerification.E2E.Costed (e2eSig e2eOps e2ePureOps e2eCurveCheckOps
  E2EPureOp E2ECurveCheckOp E2ECryptoOp)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (liftSort liftTy liftCtx liftVal liftVal_heq liftVar liftEnv liftEnv_get)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_succ_le)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (KemFailTrackState KemFailSessionTrack initKemFailTrack initKemFailSessionTrack)
open Computational.Proofs.E2E.Dsl.M3Interfaces
  (e2eDrvStateTy e2eDrvStateEnc DrvMirrorBounded DrvQueryBounded DrvMetaAligned DrvSessionsBounded
   KeyIndReachBounded)

@[expose, reducible] def drvTy (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  liftTy (e2eDrvStateTy S ℓ)

@[expose, reducible] def drvEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (σ : BHE2EDrvState S ℓ) : (drvTy S ℓ Pt).denote := e2eDrvStateEnc σ

@[simp] theorem liftVal_e2eDrvStateEnc_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (σ : BHE2EDrvState S ℓ) : liftVal (Pt := Pt) (e2eDrvStateEnc σ) = drvEnc (Pt := Pt) σ :=
  eq_of_heq (liftVal_heq (e2eDrvStateEnc σ))

@[expose, reducible] def kemCoinsT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .sum .unit (.sum (BV512 (ℓ := ℓ) (Pt := Pt)) (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))))

@[expose, reducible] def kemSentEntryT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.prod (U64 (ℓ := ℓ) (Pt := Pt)) (B (ℓ := ℓ) (Pt := Pt) 64)) (U32 (ℓ := ℓ) (Pt := Pt))

@[expose, reducible] def kemTrackT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (U64 (ℓ := ℓ) (Pt := Pt)) (.prod (kemCoinsT ℓ Pt)
    (.prod (.prod (B (ℓ := ℓ) (Pt := Pt) 32) (B (ℓ := ℓ) (Pt := Pt) 32))
      (.prod (.list (kemSentEntryT ℓ Pt)) (.prod (.prod (.tbl .nat) (.tbl .nat))
        (.opt (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))))))))

@[expose, reducible] def honestWireEntryT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (B (ℓ := ℓ) (Pt := Pt) 32) .bool

@[expose, reducible] def sessHTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (kemTrackT ℓ Pt) (.list (honestWireEntryT ℓ Pt))

@[expose, reducible] def kemCoinsBridgeAtomicEnc {ℓ : ℕ} {Pt : Type} :
    CryptoVerification.SpqrV1Sync.Braid.Coins → (kemCoinsT ℓ Pt).denote
  | .init => .inl ()
  | .seed s => .inr (.inl (bytesToWordLE 512 s.toList))
  | .both s r => .inr (.inr (bytesToWordLE 512 s.toList, bytesToWordLE 256 r.toList))

@[expose, reducible] def kemTrackBridgeAtomicEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (tr : KemFailTrackState F) : (kemTrackT ℓ Pt).denote :=
  (tr.e, (kemCoinsBridgeAtomicEnc tr.c,
    ((V1State.encodeRaw (tr.st .A).into_pb, V1State.encodeRaw (tr.st .B).into_pb),
     (tr.sentB.map (fun (m, ctr) => ((m.epoch, spqrMsgPayloadSuffix m), ctr)),
      ((tr.sendCtr .A, tr.sendCtr .B),
       tr.cand.map fun p => (bytesToWordLE 512 p.1.toList, bytesToWordLE 256 p.2.toList))))))

@[expose, reducible] def sessHEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (st : KemFailSessionTrack F Bytes) : (sessHTy ℓ Pt).denote :=
  (kemTrackBridgeAtomicEnc st.1, st.2.map fun (w, P) => (w, partyToBool P))

theorem sessHEnc_initKemFailSessionTrack_snd {ℓ : ℕ} {Pt : Type} {F : ShaCompress} (k : BitVec 256) :
    (sessHEnc (ℓ := ℓ) (Pt := Pt) (initKemFailSessionTrack F Bytes k)).2 = [] := rfl

/-! ## Bounded list snoc and tracker initialization -/

@[expose] def snocAtomicE {ℓ : ℕ} {Pt : Type} (qStart : ℕ) {O : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))} {τ : Ty (atomicSig ℓ Pt)}
    (xsE : Expr O Γ (.list τ)) (xE : Expr O Γ τ) : Expr O Γ (.list τ) :=
  .appendL (qStart + 1) xsE (.cons xE .nil)

theorem snocAtomicE_cost {ℓ : ℕ} {Pt : Type} (qStart : ℕ) {O : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))} {τ : Ty (atomicSig ℓ Pt)}
    (xsE : Expr O Γ (.list τ)) (xE : Expr O Γ τ) :
    (snocAtomicE qStart xsE xE).cost ≤ xsE.cost + xE.cost + qStart + 4 := by
  unfold snocAtomicE; simp only [Expr.cost]; omega

theorem snocAtomicE_size {ℓ : ℕ} {Pt : Type} (qStart : ℕ) {O : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))} {τ : Ty (atomicSig ℓ Pt)}
    (xsE : Expr O Γ (.list τ)) (xE : Expr O Γ τ) :
    (snocAtomicE qStart xsE xE).size ≤ xsE.size + xE.size + bits qStart + 6 := by
  have hk := bits_succ_le qStart; unfold snocAtomicE; simp only [Expr.size]; omega

@[simp] theorem snocAtomicE_eval {ℓ : ℕ} {Pt : Type} (qStart : ℕ) {O : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))} {τ : Ty (atomicSig ℓ Pt)}
    (xsE : Expr O Γ (.list τ)) (xE : Expr O Γ τ) (ρ : Env Γ) (hlen : (xsE.eval ρ).length ≤ qStart) :
    (snocAtomicE qStart xsE xE).eval ρ = xsE.eval ρ ++ [xE.eval ρ] := by
  have h1 : (xsE.eval ρ ++ [xE.eval ρ]).length ≤ qStart + 1 := by simp; omega
  simp only [snocAtomicE, Expr.eval, List.take_of_length_le h1]

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

private theorem eval_caseOpt_snd_some_some {O : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))} {τ : Ty (atomicSig ℓ Pt)}
    (e : Expr O Γ (.prod .bool (.opt (.opt τ)))) (d1 : Expr O Γ τ) (d2 : Expr O (.opt τ :: Γ) τ)
    (ρ : Env Γ) (b : Bool) (val : τ.denote) (he : e.eval ρ = (b, some (some val))) :
    (Expr.caseOpt (.snd e) d1 (.caseOpt (.var .zero) d2 (.var .zero))).eval ρ = val := by
  dsimp only [Expr.eval]; rw [he]; rfl

@[expose] def initV1BraidStE2EE (isAlice : Bool) {Γ : List (Ty (atomicSig ℓ Pt))}
    (pqrKeyE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (B (ℓ := ℓ) (Pt := Pt) 32) :=
  let ver1 := e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.u8Lit 1#8) .unit
  let dirE := e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (.u32Lit (if isAlice then 0#32 else 1#32)) .unit
  let authKeyE := e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) .bv256ToBytes32 pqrKeyE
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
      pqrKeyE.cost + 3505 := by
  unfold initKemFailSessionTrackE2EE initKemTrackE2EE initV1BraidStE2EE e2ePureE e2eSpqrE
  simp only [Expr.cost, atomicE2EOps, _root_.ReductionDsl.atomicAdapterOps,
    _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicSpqrKemOps,
    Ops.sum, Sum.elim_inl, Sum.elim_inr, AtomicPureOp.cost, AtomicSpqrKemOp.cost, List.length_nil,
    PNat.val_ofNat, show bits 0 = 1 from rfl]
  omega

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
            (e2ePureE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) .bv256ToBytes32 pqrKeyE)))).eval ρ =
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
          (CryptoVerification.LibsignalSpqrV1.spqrDeps C.F K) .v1 .b2a (keyToBytes32 (pqrKeyE.eval ρ)) =
          .ok (some (((simInitKemFailTrack C.F (pqrKeyE.eval ρ)).st .B).into_pb)) := by
        unfold CryptoVerification.LibsignalSpqrV1.initInner
        dsimp only [CryptoVerification.LibsignalSpqrV1.spqrDeps, CryptoVerification.LibsignalSpqrV1.spqrAuthApi,
          CryptoVerification.LibsignalSpqrV1.States.init_b,
          CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.new,
          CryptoVerification.LibsignalSpqrV1.HEADER_SIZE, CryptoVerification.LibsignalSpqrV1.AUTHENTICATOR_MACSIZE]
        rw [hdec]; rfl
      unfold Computational.Proofs.E2E.Dsl.ClampsLossless.spqrNegotiateInitRaw
      rw [hv, hd]; dsimp only; rw [hinit]; rfl
    · have hd : CryptoVerification.LibsignalSpqrV1.Direction.fromI32?
          (if true = true then 0#32 else 1#32) = some .a2b := rfl
      have hinit : CryptoVerification.LibsignalSpqrV1.initInner
          (CryptoVerification.LibsignalSpqrV1.spqrDeps C.F K) .v1 .a2b (keyToBytes32 (pqrKeyE.eval ρ)) =
          .ok (some (((simInitKemFailTrack C.F (pqrKeyE.eval ρ)).st .A).into_pb)) := rfl
      unfold Computational.Proofs.E2E.Dsl.ClampsLossless.spqrNegotiateInitRaw
      rw [hv, hd]; dsimp only; rw [hinit]; rfl
  exact eval_caseOpt_snd_some_some _ _ _ ρ false _ hop

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

theorem bhE2EFinishStartSpk_some_drKey {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (bMode? : Option Bool) (σ : BHE2EDrvState S ℓ)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256)
    {idx : ℕ} {σ' : BHE2EDrvState S ℓ}
    (h : bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac = (some idx, σ')) :
    ∃ dk, kr1 = .drKeyResp dk ∧ dk.rootKey.length = 32 ∧ dk.chainKey.length = 32 ∧ dk.pqrKey.length = 32 := by
  unfold bhE2EFinishStartSpk at h
  rcases hg : bhE2EGuard σ sid with _ | ⟨hdr, bnd, ⟨u, j⟩⟩
  · simp [hg] at h
  · cases kr1 with
    | drKeyResp dk =>
      cases kr2 with
      | spkSkResp spkSk =>
        simp only [hg] at h; split_ifs at h with hlen
        · simp only [Bool.and_eq_true, beq_iff_eq] at hlen
          exact ⟨dk, rfl, hlen.1.1.1, hlen.1.1.2, hlen.1.2⟩
        · cases h
      | _ => simp [hg] at h
    | _ => simp [hg] at h

/-! ## `e2eOps` to `atomicE2EOps` expression lifter -/

section LiftE2EExpr

@[expose] def liftPureOp : E2EPureOp → AtomicPureOp
  | .pbytesLit w v => .pbytesLit w v | .pbytesCat m n => .pbytesCat m n
  | .pbytesCons b w => .pbytesCons b w | .pbytesWiden w d => .pbytesWiden w d
  | .pbytesTakeK w k => .pbytesTakeK w k | .pbytesTake w => .pbytesTake w
  | .pbytesDrop w => .pbytesDrop w | .pbytesLen w => .pbytesLen w | .pbytesEq m n => .pbytesEq m n
  | .bytesLit w v => .bytesLit w v | .bytesCat m n => .bytesCat m n
  | .bytesCons b w => .bytesCons b w | .bytesWiden w d => .bytesWiden w d
  | .bytesTakeK w k => .bytesTakeK w k | .bytesTake w => .bytesTake w
  | .bytesDrop w => .bytesDrop w | .bytesLen w => .bytesLen w | .bytesEq m n => .bytesEq m n
  | .bytesLtOp m n => .bytesLtOp m n | .pbytesToBytes w => .pbytesToBytes w
  | .bytesToPbytes w => .bytesToPbytes w | .pu32Lit k => .pu32Lit k | .pu32OfNat => .pu32OfNat
  | .pu32ToNat => .pu32ToNat | .pu32Eq => .pu32Eq | .pu32ToU32 => .pu32ToU32
  | .u32ToPu32 => .u32ToPu32 | .u8Lit v => .u8Lit v | .u8OfNat => .u8OfNat | .u8ToNat => .u8ToNat
  | .u8Eq => .u8Eq | .u8Lt => .u8Lt | .u32Lit v => .u32Lit v | .u32OfNat => .u32OfNat
  | .u32ToNat => .u32ToNat | .u32Eq => .u32Eq | .u32Lt => .u32Lt | .u32Add => .u32Add
  | .u32Sub => .u32Sub | .u32BeBytes => .u32BeBytes | .u64Lit v => .u64Lit v
  | .u64OfNat => .u64OfNat | .u64ToNat => .u64ToNat | .u64Eq => .u64Eq | .u64Lt => .u64Lt
  | .u64Add => .u64Add | .u64Sub => .u64Sub | .u64Trunc8 => .u64Trunc8 | .finVal n => .finVal n
  | .finEq n => .finEq n | .bv128Eq => .bv128Eq | .bv256Lit v => .bv256Lit v
  | .bv256Eq => .bv256Eq | .bv256ToPbytes32 => .bv256ToPbytes32
  | .pbytesToBv256 => .pbytesToBv256 | .bv256ToBytes32 => .bv256ToBytes32
  | .bytesToBv256 => .bytesToBv256 | .bv512Lit v => .bv512Lit v
  | .bv512ToBytes64 => .bv512ToBytes64 | .idKeyOfPbytes => .idKeyOfPbytes
  | .idKeySerialize => .idKeySerialize | .idKeyEq => .idKeyEq | .pkOfPbytes => .pkOfPbytes
  | .pkDeserialize => .pkDeserialize | .pkSerialize => .pkSerialize | .pkEq => .pkEq
  | .plainDefault => .plainDefault | .plainToBytes => .plainToBytes
  | .bytesToPlain => .bytesToPlain | .plainEq => .plainEq
  | .checkShortCiphertext => .checkShortCiphertext | .parsePreKeyWire => .parsePreKeyWire
  | .partneredInnerBytes => .partneredInnerBytes | .wireInnerBytes => .wireInnerBytes
  | .splitWhisperWire => .splitWhisperWire | .isValidSignalWire => .isValidSignalWire
  | .signalMsgParse => .signalMsgParse | .wrapWhisperWire => .wrapWhisperWire
  | .wrapPreKeyWire => .wrapPreKeyWire | .spqrParsePreamble => .spqrParsePreamble
  | .spqrAssembleMsg => .spqrAssembleMsg | .spqrStateSplit => .spqrStateSplit
  | .spqrStateJoin => .spqrStateJoin | .ghostStateSplit => .ghostStateSplit
  | .ghostStateJoin => .ghostStateJoin | .encodeSessionRecord => .encodeSessionRecord

@[expose] def liftCurveCheckOp : E2ECurveCheckOp → AtomicCurveCheckOp
  | .decEncCheck => .decEncCheck | .checkRatchetKeyOnCurve => .checkRatchetKeyOnCurve

@[expose] def liftE2EOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    (e2eOps ℓ P C K decT encT).Op → (atomicE2EOps ℓ P C K decT encT).Op
  | .inl o => .inl (.inl (liftPureOp o))
  | .inr (.inl cc) => .inl (.inr (liftCurveCheckOp cc))
  | .inr (.inr c) =>
    match c with
    | .x25519 => .inr (.inr (.inr (.inr .x25519))) | .x25519Base => .inr (.inr (.inr (.inr .x25519Base)))
    | .pow8 => .inr (.inr (.inr (.inr .pow8))) | .isCanonical => .inr (.inr (.inr (.inr .isCanonical)))
    | .sigSign => .inr (.inr (.inr (.inr .sigSign))) | .sigVerify => .inr (.inr (.inr (.inr .sigVerify)))
    | .kemKeyGen => .inr (.inr (.inr (.inr .kemKeyGen))) | .kemEncaps => .inr (.inr (.inr (.inr .kemEncaps)))
    | .kemDecaps => .inr (.inr (.inr (.inr .kemDecaps))) | .hkdfDerive96 => .inr (.inr (.inr (.inr .hkdfDerive96)))
    | .sessionKeyPairGen => .inr (.inr (.inl .sessionKeyPairGen))
    | .sessionRootCreateChain => .inr (.inr (.inl .sessionRootCreateChain))
    | .chainStep => .inr (.inr (.inl .chainStep)) | .deriveMsgKeys => .inr (.inr (.inl .deriveMsgKeys))
    | .aes256CbcEnc => .inr (.inr (.inl .aes256CbcEnc)) | .aes256CbcDec => .inr (.inr (.inl .aes256CbcDec))
    | .signalMsgEncode => .inr (.inr (.inl .signalMsgEncode))
    | .signalMsgVerifyMac => .inr (.inr (.inl .signalMsgVerifyMac))
    | .spqrV1InitOp => .inr (.inr (.inr (.inl .spqrV1InitOp)))
    | .spqrNegotiateInit => .inr (.inr (.inr (.inl .spqrNegotiateInit)))
    | .spqrBraidSend => .inr (.inr (.inr (.inl .spqrBraidSend)))
    | .spqrBraidRecv => .inr (.inr (.inr (.inl .spqrBraidRecv)))
    | .spqrChainFromVn => .inr (.inr (.inr (.inl .spqrChainFromVn)))
    | .spqrChainAddEpoch => .inr (.inr (.inr (.inl .spqrChainAddEpoch)))
    | .spqrChainNextKey => .inr (.inr (.inr (.inl .spqrChainNextKey)))

theorem liftE2EOp_dom {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} (o : (e2eOps ℓ P C K decT encT).Op) :
    (atomicE2EOps ℓ P C K decT encT).dom (liftE2EOp (Pt := Pt) o) =
      liftTy (Pt := Pt) ((e2eOps ℓ P C K decT encT).dom o) := by
  rcases o with o | cc | c <;> [cases o; cases cc; cases c] <;> rfl

theorem liftE2EOp_cod {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} (o : (e2eOps ℓ P C K decT encT).Op) :
    (atomicE2EOps ℓ P C K decT encT).cod (liftE2EOp (Pt := Pt) o) =
      liftTy (Pt := Pt) ((e2eOps ℓ P C K decT encT).cod o) := by
  rcases o with o | cc | c <;> [cases o; cases cc; cases c] <;> rfl

private theorem liftE2EOp_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} (o : (e2eOps ℓ P C K decT encT).Op) :
    (atomicE2EOps ℓ P C K decT encT).cost (liftE2EOp (Pt := Pt) o) = (e2eOps ℓ P C K decT encT).cost o := by
  rcases o with o | cc | c <;> [cases o; cases cc; cases c] <;> rfl

private theorem liftE2EOp_opSize {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} (o : (e2eOps ℓ P C K decT encT).Op) :
    (atomicE2EOps ℓ P C K decT encT).opSize (liftE2EOp (Pt := Pt) o) = (e2eOps ℓ P C K decT encT).opSize o := by
  rcases o with o | cc | c <;> [cases o; cases cc; cases c] <;> rfl

@[expose] def castExprTy {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t u : Ty S₀}
    (h : t = u) (e : Expr O Γ t) : Expr O Γ u := h ▸ e

private theorem castExprTy_cost {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t u : Ty S₀}
    (h : t = u) (e : Expr O Γ t) : (castExprTy h e).cost = e.cost := by cases h; rfl

private theorem castExprTy_size {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t u : Ty S₀}
    (h : t = u) (e : Expr O Γ t) : (castExprTy h e).size = e.size := by cases h; rfl

private theorem castExprTy_eval_heq {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t u : Ty S₀}
    (h : t = u) (e : Expr O Γ t) (ρ : Env Γ) : HEq ((castExprTy h e).eval ρ) (e.eval ρ) := by
  cases h; rfl

/-- Lifts an `Expr` from `e2eOps` into `atomicE2EOps` preserving `.cost` and `.size`. -/
@[expose] def liftE2EExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} → Expr (e2eOps ℓ P C K decT encT) Γ t →
    Expr (atomicE2EOps ℓ P C K decT encT) (liftCtx (Pt := Pt) Γ) (liftTy (Pt := Pt) t)
  | _, _, .var v => .var (liftVar v) | _, _, .unit => .unit | _, _, .bool b => .bool b
  | _, _, .nat n => .nat n | _, _, .none => .none | _, _, .some e => .some (liftE2EExpr e)
  | _, _, .pair a b => .pair (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .fst e => .fst (liftE2EExpr e) | _, _, .snd e => .snd (liftE2EExpr e)
  | _, _, .inl e => .inl (liftE2EExpr e) | _, _, .inr e => .inr (liftE2EExpr e)
  | _, _, .nil => .nil | _, _, .cons x xs => .cons (liftE2EExpr x) (liftE2EExpr xs)
  | _, _, .appendL Kb xs ys => .appendL Kb (liftE2EExpr xs) (liftE2EExpr ys)
  | _, _, .take n xs => .take (liftE2EExpr n) (liftE2EExpr xs) | _, _, .len xs => .len (liftE2EExpr xs)
  | _, _, .not e => .not (liftE2EExpr e) | _, _, .and a b => .and (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .eqN a b => .eqN (liftE2EExpr a) (liftE2EExpr b) | _, _, .lt a b => .lt (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .add a b => .add (liftE2EExpr a) (liftE2EExpr b) | _, _, .sub a b => .sub (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .mulK k e => .mulK k (liftE2EExpr e) | _, _, .divK k e => .divK k (liftE2EExpr e)
  | _, _, .modK k e => .modK k (liftE2EExpr e)
  | _, _, .ite c t f => .ite (liftE2EExpr c) (liftE2EExpr t) (liftE2EExpr f)
  | _, _, .letE a b => .letE (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .caseOpt e n s => .caseOpt (liftE2EExpr e) (liftE2EExpr n) (liftE2EExpr s)
  | _, _, .caseSum e l r => .caseSum (liftE2EExpr e) (liftE2EExpr l) (liftE2EExpr r)
  | _, _, .findB Kb xs p => .findB Kb (liftE2EExpr xs) (liftE2EExpr p)
  | _, _, .anyB Kb xs p => .anyB Kb (liftE2EExpr xs) (liftE2EExpr p)
  | _, _, .mapB Kb xs f => .mapB Kb (liftE2EExpr xs) (liftE2EExpr f)
  | _, _, .foldrB Kb xs z f => .foldrB Kb (liftE2EExpr xs) (liftE2EExpr z) (liftE2EExpr f)
  | _, _, .tconst d => .tconst (liftE2EExpr d) | _, _, .tget m i => .tget (liftE2EExpr m) (liftE2EExpr i)
  | _, _, .tset m i v => .tset (liftE2EExpr m) (liftE2EExpr i) (liftE2EExpr v)
  | _, _, .op o e =>
    castExprTy (liftE2EOp_cod (Pt := Pt) o)
      (Expr.op (O := atomicE2EOps ℓ P C K decT encT) (liftE2EOp (Pt := Pt) o)
        (castExprTy (liftE2EOp_dom (Pt := Pt) o).symm (liftE2EExpr e)))

@[simp] theorem liftE2EExpr_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ t) : (liftE2EExpr (Pt := Pt) e).cost = e.cost := by
  induction e <;> simp only [liftE2EExpr, Expr.cost, castExprTy_cost, liftE2EOp_cost, *]

@[simp] theorem liftE2EExpr_size {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ t) : (liftE2EExpr (Pt := Pt) e).size = e.size := by
  induction e <;> simp only [liftE2EExpr, Expr.size, castExprTy_size, liftE2EOp_opSize, *]

private theorem list_find_map {α β : Type} (g : α → β) (q : β → Bool) (p : α → Bool)
    (hpq : ∀ x, q (g x) = p x) : ∀ xs : List α, (xs.map g).find? q = (xs.find? p).map g
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.find?_cons, hpq x]
    cases p x <;> [exact list_find_map g q p hpq xs; rfl]

private theorem list_any_map_eq {α β : Type} (g : α → β) (q : β → Bool) (p : α → Bool)
    (hpq : ∀ x, q (g x) = p x) : ∀ xs : List α, (xs.map g).any q = xs.any p
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, List.any_cons, hpq x, list_any_map_eq g q p hpq xs]

private theorem list_map_map_eq {α β γ δ : Type} (g : α → β) (h : γ → δ)
    (f' : β → δ) (f : α → γ) (hfg : ∀ x, f' (g x) = h (f x)) :
    ∀ xs : List α, (xs.map g).map f' = (xs.map f).map h
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, hfg x, list_map_map_eq g h f' f hfg xs]

private theorem list_foldr_map_eq {α β γ δ : Type} (g : α → β) (h : γ → δ)
    (f' : β → δ → δ) (f : α → γ → γ) (hf : ∀ x acc, f' (g x) (h acc) = h (f x acc)) (z : γ) :
    ∀ xs : List α, (xs.map g).foldr f' (h z) = h (xs.foldr f z)
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, List.foldr_cons, list_foldr_map_eq g h f' f hf z xs, hf x]

private theorem atomic_e2eDecodePreKeyMsg_eq (c : Bytes) :
    _root_.ReductionDsl.e2eDecodePreKeyMsg c =
      CryptoVerification.E2E.Costed.e2eDecodePreKeyMsg c := by
  have hraw : _root_.ReductionDsl.e2eDecodePreKeyRaw c =
      CryptoVerification.E2E.Costed.e2eDecodePreKeyRaw c := by
    unfold _root_.ReductionDsl.e2eDecodePreKeyRaw CryptoVerification.E2E.Costed.e2eDecodePreKeyRaw
      _root_.ReductionDsl.e2eParseOptPreKeyId CryptoVerification.E2E.Costed.e2eParseOptPreKeyId
      _root_.ReductionDsl.e2eParseDjbKeyField CryptoVerification.E2E.Costed.e2eParseDjbKeyField
      _root_.ReductionDsl.e2eParseInnerMsgField CryptoVerification.E2E.Costed.e2eParseInnerMsgField
      _root_.ReductionDsl.e2eParseUint32Field CryptoVerification.E2E.Costed.e2eParseUint32Field
      _root_.ReductionDsl.e2eParseKyberCtField CryptoVerification.E2E.Costed.e2eParseKyberCtField
    rw [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.readProstVarint_eq]; rfl
  unfold _root_.ReductionDsl.e2eDecodePreKeyMsg CryptoVerification.E2E.Costed.e2eDecodePreKeyMsg
  rw [hraw]; rfl

private theorem atomic_spqrChainToV_eq (ℓ : ℕ) (Pt : Type)
    (c : CryptoVerification.LibsignalSpqrV1.ChainPB) :
    _root_.ReductionDsl.spqrChainToV (ℓ := ℓ) (Pt := Pt) c =
      CryptoVerification.E2E.Costed.spqrChainToV (ℓ := ℓ) c := by
  have hdir : _root_.ReductionDsl.spqrDirToV (ℓ := ℓ) (Pt := Pt) =
      CryptoVerification.E2E.Costed.spqrDirToV (ℓ := ℓ) := by
    funext d
    dsimp only [_root_.ReductionDsl.spqrDirToV, CryptoVerification.E2E.Costed.spqrDirToV]
    rw [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.splitSpqrPrev_eq]
  dsimp only [_root_.ReductionDsl.spqrChainToV, CryptoVerification.E2E.Costed.spqrChainToV]
  rw [hdir]
  rfl

private theorem atomic_spqrSplitEval_eq (ℓ : ℕ) (Pt : Type) (x : Bytes) :
    _root_.ReductionDsl.spqrSplitEval (ℓ := ℓ) (Pt := Pt) x =
      CryptoVerification.E2E.Costed.spqrSplitEval (ℓ := ℓ) x := by
  unfold _root_.ReductionDsl.spqrSplitEval CryptoVerification.E2E.Costed.spqrSplitEval
  have hvn : _root_.ReductionDsl.spqrVnToV (ℓ := ℓ) (Pt := Pt) =
      CryptoVerification.E2E.Costed.spqrVnToV (ℓ := ℓ) := by
    funext vn; cases vn.chainParams <;> rfl
  have hch : _root_.ReductionDsl.spqrChainToV (ℓ := ℓ) (Pt := Pt) =
      CryptoVerification.E2E.Costed.spqrChainToV (ℓ := ℓ) :=
    funext (atomic_spqrChainToV_eq ℓ Pt)
  rw [hvn, hch]
  cases CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState x with
  | error _ => rfl
  | ok st =>
    cases st.inner with
    | none => rfl
    | some i => cases i; rfl

private theorem atomic_spqrJoinEval_eq (ℓ : ℕ) (Pt : Type)
    (x : (CryptoVerification.E2E.Costed.spqrStatePartsT (ℓ := ℓ)).denote) :
    _root_.ReductionDsl.spqrJoinEval (ℓ := ℓ) (Pt := Pt) x =
      CryptoVerification.E2E.Costed.spqrJoinEval (ℓ := ℓ) x := by
  rcases x with ⟨v1?, vn?, ch?⟩
  unfold _root_.ReductionDsl.spqrJoinEval CryptoVerification.E2E.Costed.spqrJoinEval
  dsimp only
  apply congrArg (List.take (32 * 11000))
  rcases v1? with _ | _ <;> rcases vn? with _ | _ <;> rcases ch? with _ | _ <;> rfl

private theorem atomic_e2eEncodeSessionRecord_eq (ℓ : ℕ) (Pt : Type)
    (x : ((e2ePureOps ℓ).dom .encodeSessionRecord).denote) :
    _root_.ReductionDsl.e2eEncodeSessionRecord (ℓ := ℓ) (Pt := Pt) x =
      CryptoVerification.E2E.Costed.e2eEncodeSessionRecord (ℓ := ℓ) x := by
  rcases x with ⟨⟨regIdA, regIdB, bobReg, hdr⟩, g⟩
  have hex : _root_.ReductionDsl.e2eRecordExtras = CryptoVerification.E2E.Costed.e2eRecordExtras := by
    funext rA rB bR h p; cases p <;> rfl
  have hbs :
      CryptoVerification.E2E.binStateOfUnderExtras
        (_root_.ReductionDsl.e2eRecordExtras regIdA regIdB bobReg
          (_root_.ReductionDsl.hdrOfV (ℓ := ℓ) (Pt := Pt) hdr)) g =
      CryptoVerification.E2E.binStateOfUnderExtras
        (CryptoVerification.E2E.Costed.e2eRecordExtras regIdA regIdB bobReg
          (CryptoVerification.E2E.Costed.hdrOfV (ℓ := ℓ) hdr)) g := by
    rw [hex]; rfl
  exact congrArg (fun bs : BinState => { bs with bytes := bs.bytes.take (32 * 24000) }) hbs

private theorem liftPureOp_domD (ℓ : ℕ) (Pt : Type) (o : E2EPureOp) :
    ((_root_.ReductionDsl.atomicPureOps ℓ Pt).dom (liftPureOp o)).denote = ((e2ePureOps ℓ).dom o).denote := by
  cases o <;> rfl

private theorem liftPureOp_codD (ℓ : ℕ) (Pt : Type) (o : E2EPureOp) :
    ((_root_.ReductionDsl.atomicPureOps ℓ Pt).cod (liftPureOp o)).denote = ((e2ePureOps ℓ).cod o).denote := by
  cases o <;> rfl

set_option maxHeartbeats 400000 in
private theorem liftPureOp_val_eq (ℓ : ℕ) (Pt : Type) (o : E2EPureOp)
    (x : ((e2ePureOps ℓ).dom o).denote) :
    (_root_.ReductionDsl.atomicPureOps ℓ Pt).eval (liftPureOp o) (cast (liftPureOp_domD ℓ Pt o).symm x) =
      cast (liftPureOp_codD ℓ Pt o).symm ((e2ePureOps ℓ).eval o x) := by
  cases o
  case checkShortCiphertext => rcases x with ⟨c0, _ | i⟩ <;> rfl
  case splitWhisperWire => rcases x with _ | ⟨t, body⟩ <;> rfl
  case parsePreKeyWire =>
    exact congrArg (Option.map fun m => (m.regId, (_root_.ReductionDsl.hdrV (_root_.ReductionDsl.e2eHdrOfPreKeyMsg m),
      m.inner.take x.length))) (atomic_e2eDecodePreKeyMsg_eq x)
  case partneredInnerBytes =>
    rcases x with ⟨bobAcc, regIdA, hdr, c0⟩
    change _root_.ReductionDsl.e2ePartneredInnerBytes bobAcc regIdA (_root_.ReductionDsl.hdrOfV hdr) c0 =
      CryptoVerification.E2E.Costed.e2ePartneredInnerBytes bobAcc regIdA (CryptoVerification.E2E.Costed.hdrOfV hdr) c0
    simp only [_root_.ReductionDsl.e2ePartneredInnerBytes, CryptoVerification.E2E.Costed.e2ePartneredInnerBytes,
      atomic_e2eDecodePreKeyMsg_eq]; rfl
  case wireInnerBytes =>
    change _root_.ReductionDsl.e2eWireInnerBytes x = CryptoVerification.E2E.Costed.e2eWireInnerBytes x
    simp only [_root_.ReductionDsl.e2eWireInnerBytes, CryptoVerification.E2E.Costed.e2eWireInnerBytes,
      atomic_e2eDecodePreKeyMsg_eq]; rfl
  case wrapPreKeyWire =>
    rcases x with ⟨regIdA, hdr, inner⟩
    change (if inner.isEmpty then [] else (CryptoVerification.E2E.wirePrekey ::
      (_root_.ReductionDsl.e2eExpectedPreKeyMsg regIdA (_root_.ReductionDsl.hdrOfV hdr) inner).bytes).take
      (32 * (2 * (ℓ / 32) + 84))) =
      (if inner.isEmpty then [] else (CryptoVerification.E2E.wirePrekey ::
      (CryptoVerification.E2E.Costed.e2eExpectedPreKeyMsg regIdA (CryptoVerification.E2E.Costed.hdrOfV hdr) inner).bytes).take
      (32 * (2 * (ℓ / 32) + 84)))
    have hexp : _root_.ReductionDsl.e2eExpectedPreKeyMsg regIdA (_root_.ReductionDsl.hdrOfV (ℓ := ℓ) (Pt := Pt) hdr) inner =
      CryptoVerification.E2E.Costed.e2eExpectedPreKeyMsg regIdA (CryptoVerification.E2E.Costed.hdrOfV (ℓ := ℓ) hdr) inner := rfl
    rw [hexp]
  case spqrStateSplit => exact atomic_spqrSplitEval_eq ℓ Pt x
  case spqrStateJoin => exact atomic_spqrJoinEval_eq ℓ Pt x
  case ghostStateSplit => cases x.party <;> rfl
  case ghostStateJoin => cases x.1 <;> rfl
  case encodeSessionRecord => exact atomic_e2eEncodeSessionRecord_eq ℓ Pt x
  all_goals rfl

private theorem liftE2EOp_domD {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} (o : (e2eOps ℓ P C K decT encT).Op) :
    ((atomicE2EOps ℓ P C K decT encT).dom (liftE2EOp (Pt := Pt) o)).denote = ((e2eOps ℓ P C K decT encT).dom o).denote := by
  rcases o with o | cc | c
  · exact liftPureOp_domD ℓ Pt o
  · cases cc <;> rfl
  · cases c <;> rfl

private theorem liftE2EOp_codD {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} (o : (e2eOps ℓ P C K decT encT).Op) :
    ((atomicE2EOps ℓ P C K decT encT).cod (liftE2EOp (Pt := Pt) o)).denote = ((e2eOps ℓ P C K decT encT).cod o).denote := by
  rcases o with o | cc | c
  · exact liftPureOp_codD ℓ Pt o
  · cases cc <;> rfl
  · cases c <;> rfl

private theorem liftE2EOp_val_eq {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} (o : (e2eOps ℓ P C K decT encT).Op)
    (x : ((e2eOps ℓ P C K decT encT).dom o).denote) :
    (atomicE2EOps ℓ P C K decT encT).eval (liftE2EOp (Pt := Pt) o) (cast (liftE2EOp_domD (Pt := Pt) o).symm x) =
      cast (liftE2EOp_codD (Pt := Pt) o).symm ((e2eOps ℓ P C K decT encT).eval o x) := by
  rcases o with o | cc | c
  · exact liftPureOp_val_eq ℓ Pt o x
  · cases cc <;> rfl
  · cases c
    case spqrChainFromVn =>
      change _root_.ReductionDsl.spqrChainFromVnEval (ℓ := ℓ) (Pt := Pt) C.F x =
        CryptoVerification.E2E.Costed.spqrChainFromVnEval (ℓ := ℓ) C.F x
      unfold _root_.ReductionDsl.spqrChainFromVnEval CryptoVerification.E2E.Costed.spqrChainFromVnEval
      have hvn : _root_.ReductionDsl.spqrVnOfV (ℓ := ℓ) (Pt := Pt) x =
          CryptoVerification.E2E.Costed.spqrVnOfV (ℓ := ℓ) x := rfl
      rw [hvn]
      cases CryptoVerification.LibsignalSpqrV1.chainFromVersionNegotiation
          (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith C.F) (CryptoVerification.E2E.Costed.spqrVnOfV (ℓ := ℓ) x) with
      | error _ => rfl
      | ok c0 => exact congrArg some (atomic_spqrChainToV_eq ℓ Pt c0.intoPb)
    case spqrChainAddEpoch =>
      rcases x with ⟨ch, ep, sec⟩
      change _root_.ReductionDsl.spqrChainAddEpochEval (ℓ := ℓ) (Pt := Pt) C.F ch ep sec =
        CryptoVerification.E2E.Costed.spqrChainAddEpochEval (ℓ := ℓ) C.F ch ep sec
      unfold _root_.ReductionDsl.spqrChainAddEpochEval CryptoVerification.E2E.Costed.spqrChainAddEpochEval
      have hch : _root_.ReductionDsl.spqrChainOfV (ℓ := ℓ) (Pt := Pt) ch =
          CryptoVerification.E2E.Costed.spqrChainOfV (ℓ := ℓ) ch := rfl
      rw [hch]
      cases CryptoVerification.LibsignalSpqrV1.Chain.fromPb (CryptoVerification.E2E.Costed.spqrChainOfV (ℓ := ℓ) ch) with
      | error _ => rfl
      | ok c0 =>
        dsimp only
        cases c0.addEpoch (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith C.F) ⟨ep, keyToBytes32 sec⟩ with
        | error _ => rfl
        | ok c1 => exact congrArg (fun v => (false, some v)) (atomic_spqrChainToV_eq ℓ Pt c1.intoPb)
    all_goals rfl

private theorem liftE2EOp_eval_eq {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} (o : (e2eOps ℓ P C K decT encT).Op)
    {Γ₂ : List (Ty (atomicSig ℓ Pt))}
    (a₂ : Expr (atomicE2EOps ℓ P C K decT encT) Γ₂ (liftTy (Pt := Pt) ((e2eOps ℓ P C K decT encT).dom o)))
    (ρ₂ : Env Γ₂) (x : ((e2eOps ℓ P C K decT encT).dom o).denote) (ha : a₂.eval ρ₂ = liftVal (Pt := Pt) x) :
    (castExprTy (liftE2EOp_cod (Pt := Pt) o)
      (Expr.op (O := atomicE2EOps ℓ P C K decT encT) (liftE2EOp (Pt := Pt) o)
        (castExprTy (liftE2EOp_dom (Pt := Pt) o).symm a₂))).eval ρ₂ =
      liftVal (Pt := Pt) ((e2eOps ℓ P C K decT encT).eval o x) := by
  apply eq_of_heq; refine (castExprTy_eval_heq _ _ _).trans ?_
  have harg : (castExprTy (liftE2EOp_dom (Pt := Pt) o).symm a₂).eval ρ₂ =
      cast (liftE2EOp_domD (Pt := Pt) o).symm x :=
    eq_of_heq ((castExprTy_eval_heq _ a₂ ρ₂).trans
      ((heq_of_eq ha).trans ((liftVal_heq x).trans (cast_heq (liftE2EOp_domD (Pt := Pt) o).symm x).symm)))
  dsimp only [Expr.eval]; rw [harg, liftE2EOp_val_eq (Pt := Pt) o x]
  exact (cast_heq (liftE2EOp_codD (Pt := Pt) o).symm _).trans (liftVal_heq _).symm

theorem liftE2EExpr_eval {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ t) (ρ : Env Γ) :
    (liftE2EExpr (Pt := Pt) e).eval (liftEnv (Pt := Pt) ρ) = liftVal (Pt := Pt) (e.eval ρ) := by
  induction e with
  | var v => exact liftEnv_get ρ v
  | unit | bool _ | nat _ | none | nil => rfl
  | mulK _ a iha | divK _ a iha | modK _ a iha | not a iha | inl a iha | inr a iha
  | some a iha | tconst a iha => simp only [liftE2EExpr, Expr.eval, iha ρ]; rfl
  | add a b iha ihb | sub a b iha ihb | lt a b iha ihb | eqN a b iha ihb
  | and a b iha ihb | pair a b iha ihb | cons a b iha ihb | tget a b iha ihb =>
    simp only [liftE2EExpr, Expr.eval, iha ρ, ihb ρ]; rfl
  | ite c a b ihc iha ihb =>
    simp only [liftE2EExpr, Expr.eval, ihc ρ]; cases c.eval ρ <;> [exact ihb ρ; exact iha ρ]
  | fst a iha => simp only [liftE2EExpr, Expr.eval, iha ρ]; rcases a.eval ρ with ⟨_, _⟩; rfl
  | snd a iha => simp only [liftE2EExpr, Expr.eval, iha ρ]; rcases a.eval ρ with ⟨_, _⟩; rfl
  | caseOpt e n s ihe ihn ihs =>
    simp only [liftE2EExpr, Expr.eval, ihe ρ]; rcases e.eval ρ with _ | x <;> [exact ihn ρ; exact ihs (.cons x ρ)]
  | caseSum e l r ihe ihl ihr =>
    simp only [liftE2EExpr, Expr.eval, ihe ρ]; rcases e.eval ρ with x | y <;> [exact ihl (.cons x ρ); exact ihr (.cons y ρ)]
  | letE e b ihe ihb => simp only [liftE2EExpr, Expr.eval, ihe ρ]; exact ihb (.cons (e.eval ρ) ρ)
  | op o a iha => exact liftE2EOp_eval_eq o (liftE2EExpr a) (liftEnv ρ) (a.eval ρ) (iha ρ)
  | len l ihl => simp only [liftE2EExpr, Expr.eval, ihl ρ, liftVal, List.length_map]
  | take n l ihn ihl => simp only [liftE2EExpr, Expr.eval, ihn ρ, ihl ρ, liftVal, List.map_take]
  | appendL Kb a b iha ihb =>
    simp only [liftE2EExpr, Expr.eval, iha ρ, ihb ρ, liftVal, ← List.map_append, List.map_take]
  | findB Kb l p ihl ihp =>
    simp only [liftE2EExpr, Expr.eval, ihl ρ, liftVal, ← List.map_take]
    exact list_find_map liftVal (fun y => (liftE2EExpr p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ)) (fun x => ihp (.cons x ρ)) ((l.eval ρ).take Kb)
  | anyB Kb l p ihl ihp =>
    simp only [liftE2EExpr, Expr.eval, ihl ρ, liftVal, ← List.map_take]
    exact list_any_map_eq liftVal (fun y => (liftE2EExpr p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ)) (fun x => ihp (.cons x ρ)) ((l.eval ρ).take Kb)
  | mapB Kb l f ihl ihf =>
    simp only [liftE2EExpr, Expr.eval, ihl ρ, liftVal, ← List.map_take]
    exact list_map_map_eq liftVal liftVal (fun y => (liftE2EExpr f).eval (.cons y (liftEnv ρ)))
      (fun x => f.eval (.cons x ρ)) (fun x => ihf (.cons x ρ)) ((l.eval ρ).take Kb)
  | foldrB Kb l z f ihl ihz ihf =>
    simp only [liftE2EExpr, Expr.eval, ihl ρ, ihz ρ]
    change (((l.eval ρ).map liftVal).take Kb).foldr _ (liftVal (z.eval ρ)) = _
    rw [← List.map_take]
    exact list_foldr_map_eq liftVal liftVal
      (fun y acc => (liftE2EExpr f).eval (.cons y (.cons acc (liftEnv ρ))))
      (fun x acc => f.eval (.cons x (.cons acc ρ))) (fun x acc => ihf (.cons x (.cons acc ρ)))
      (z.eval ρ) ((l.eval ρ).take Kb)
  | tset m i a ihm ihi iha =>
    simp only [liftE2EExpr, Expr.eval, ihm ρ, ihi ρ, iha ρ]
    funext j; by_cases hj : j = i.eval ρ <;> simp [hj, liftVal]

end LiftE2EExpr

/-! ## Atomic handshake and pure subprograms -/

section KindHandshakeSubprograms

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "AExpr" => Expr (atomicE2EOps ℓ P C K decT encT)
local notation "AComp" => Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt)

abbrev wk1E {u t : Ty (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (e : AExpr Γ t) : AExpr (u :: Γ) t := Expr.renameM (fun _ v => v.succ) e

@[expose] def liftLet1E {argTy retTy : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : AExpr Γ (liftTy (Pt := Pt) argTy))
    (bodyE : Expr (e2eOps ℓ P C K decT encT) [argTy] retTy) : AExpr Γ (liftTy (Pt := Pt) retTy) :=
  .letE argE (Expr.wkTop1 (liftE2EExpr (Pt := Pt) bodyE))

private theorem liftLet1E_cost {argTy retTy : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : AExpr Γ (liftTy (Pt := Pt) argTy)) (bodyE : Expr (e2eOps ℓ P C K decT encT) [argTy] retTy) :
    (liftLet1E (P := P) (C := C) (K := K) (decT := decT) (encT := encT) argE bodyE).cost =
      argE.cost + bodyE.cost + 1 := by
  simp only [liftLet1E, Expr.cost, Expr.wkTop1, Expr.renameM_cost, liftE2EExpr_cost]

private theorem liftLet1E_size {argTy retTy : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : AExpr Γ (liftTy (Pt := Pt) argTy)) (bodyE : Expr (e2eOps ℓ P C K decT encT) [argTy] retTy) :
    (liftLet1E (P := P) (C := C) (K := K) (decT := decT) (encT := encT) argE bodyE).size =
      argE.size + bodyE.size + 1 := by
  simp only [liftLet1E, Expr.size, Expr.wkTop1, Expr.renameM_size, liftE2EExpr_size]

private theorem liftLet1E_eval {argTy retTy : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : AExpr Γ (liftTy (Pt := Pt) argTy)) (bodyE : Expr (e2eOps ℓ P C K decT encT) [argTy] retTy)
    (ρ : Env Γ) (x : argTy.denote) (hx : argE.eval ρ = liftVal (Pt := Pt) x) :
    (liftLet1E (P := P) (C := C) (K := K) (decT := decT) (encT := encT) argE bodyE).eval ρ =
      liftVal (Pt := Pt) (bodyE.eval (.cons x .nil)) := by
  simp only [liftLet1E, Expr.eval, hx, Expr.wkTop1_eval]; exact liftE2EExpr_eval bodyE (.cons x .nil)

private theorem atomic_sidV_eq (sid : SignalPqxdh.SessionId S) :
    sidV (ℓ := ℓ) (Pt := Pt) sid = CryptoVerification.E2E.Costed.sidV (ℓ := ℓ) sid := by cases sid <;> rfl

private theorem liftVal_sidV_eq (sid : SignalPqxdh.SessionId S) :
    liftVal (Pt := Pt) (t := CryptoVerification.E2E.Costed.sidT (ℓ := ℓ) S)
      (CryptoVerification.E2E.Costed.sidV (ℓ := ℓ) sid) = sidV (ℓ := ℓ) (Pt := Pt) sid :=
  (eq_of_heq (liftVal_heq _)).trans (atomic_sidV_eq sid).symm

private theorem atomic_keyIndQenc_eq (kq : SignalPqxdh.KeyIndQuery S) :
    keyIndQenc (ℓ := ℓ) (Pt := Pt) kq = CryptoVerification.E2E.Costed.keyIndQenc (ℓ := ℓ) kq := by
  cases kq <;> simp only [keyIndQenc, CryptoVerification.E2E.Costed.keyIndQenc, atomic_sidV_eq] <;> rfl

private theorem liftVal_keyIndQenc_eq (kq : SignalPqxdh.KeyIndQuery S) :
    liftVal (Pt := Pt) (t := CryptoVerification.E2E.Costed.keyIndQT (ℓ := ℓ) S)
      (CryptoVerification.E2E.Costed.keyIndQenc (ℓ := ℓ) kq) = keyIndQenc (ℓ := ℓ) (Pt := Pt) kq :=
  (eq_of_heq (liftVal_heq _)).trans (atomic_keyIndQenc_eq kq).symm

private theorem atomic_keyIndRenc_eq (kr : SignalPqxdh.KeyIndResponse) :
    keyIndRenc (ℓ := ℓ) (Pt := Pt) kr = CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr := by
  cases kr <;> rfl

private theorem liftVal_keyIndRenc_eq (kr : SignalPqxdh.KeyIndResponse) :
    liftVal (Pt := Pt) (t := CryptoVerification.E2E.Costed.keyIndRT (ℓ := ℓ))
      (CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr) = keyIndRenc (ℓ := ℓ) (Pt := Pt) kr :=
  (eq_of_heq (liftVal_heq _)).trans (atomic_keyIndRenc_eq kr).symm

@[expose] def emptyDrvStateAtomicE {O : Ops (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (bE : Expr O Γ .bool) : Expr O Γ (drvTy S ℓ Pt) :=
  .pair (.pair .nil (.pair .nil (.pair .nil .nil)))
    (.pair .nil (.pair .nil (.pair .nil (.pair .nil
      (.pair (.pair (.bool false) (.pair .nil (.pair .nil (.pair .nil (.pair .nil
          (.pair .nil (.pair .nil (.pair .nil (.pair .nil (.pair .nil .nil))))))))))
        (.pair bE (.bool false)))))))

@[expose] def initKindCost : ℕ := 48
@[expose] def initKindSize : ℕ := 48

@[expose] def initKindC {Γ : List (Ty (atomicSig ℓ Pt))} : AComp Γ (drvTy S ℓ Pt) :=
  .bind (.sample (I := e2eKeyIndTargetIface S ℓ Pt) UniformSamplerTag.bool .unit)
    (.ret (emptyDrvStateAtomicE (.var .zero)))

theorem initKindC_cost {Γ : List (Ty (atomicSig ℓ Pt))} :
    (initKindC (S := S) (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (Γ := Γ)).cost ≤ initKindCost := by
  simp only [initKindC, initKindCost, Comp.cost, emptyDrvStateAtomicE, Expr.cost,
    e2eKeyIndTargetIface, _root_.ReductionDsl.atomicBaseSamplers,
    _root_.ReductionDsl.unifSamplers, _root_.ReductionDsl.AtomicBaseUnif.cost]; omega

theorem initKindC_size {Γ : List (Ty (atomicSig ℓ Pt))} :
    (initKindC (S := S) (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (Γ := Γ)).size ≤ initKindSize := by
  simp only [initKindC, initKindSize, Comp.size, emptyDrvStateAtomicE, Expr.size]; omega

theorem initKindC_queries {Γ : List (Ty (atomicSig ℓ Pt))} (w : (e2eKeyIndTargetIface S ℓ Pt).Tag → ℕ) :
    (initKindC (S := S) (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (Γ := Γ)).queries w (fun _ => 0) = 0 := rfl

theorem initKindC_eval {Γ : List (Ty (atomicSig ℓ Pt))} (ρ : Env Γ) :
    (initKindC (S := S) (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)).eval ρ =
      (e2eKeyIndTargetIface S ℓ Pt).liftP
        ((fun b : Bool => drvEnc (Pt := Pt) ({ b := b } : BHE2EDrvState S ℓ)) <$> ($ᵗ Bool : ProbComp Bool)) := by
  have hempty : ∀ b : Bool, (emptyDrvStateAtomicE (S := S) (ℓ := ℓ) (Pt := Pt)
      (O := atomicE2EOps ℓ P C K decT encT) (.var .zero)).eval (.cons b ρ) =
      drvEnc (Pt := Pt) ({ b := b } : BHE2EDrvState S ℓ) := fun _ => rfl
  simp only [initKindC, Comp.eval, hempty, PqxdhSimTypes.liftP_bind, PqxdhSimTypes.liftP_pure,
    map_eq_bind_pure_comp, Function.comp_def]

@[expose] def drvBitCost : ℕ := 7
@[expose] def drvBitSize : ℕ := 7

@[expose] def drvBitE {Γ : List (Ty (atomicSig ℓ Pt))} (σE : AExpr Γ (drvTy S ℓ Pt)) : AExpr Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd σE))))))

theorem drvBitE_cost {Γ : List (Ty (atomicSig ℓ Pt))} (σE : AExpr Γ (drvTy S ℓ Pt)) :
    (drvBitE σE).cost ≤ σE.cost + drvBitCost := by simp only [drvBitE, drvBitCost, Expr.cost]; omega

theorem drvBitE_size {Γ : List (Ty (atomicSig ℓ Pt))} (σE : AExpr Γ (drvTy S ℓ Pt)) :
    (drvBitE σE).size ≤ σE.size + drvBitSize := by simp only [drvBitE, drvBitSize, Expr.size]; omega

theorem drvBitE_eval {Γ : List (Ty (atomicSig ℓ Pt))} (σE : AExpr Γ (drvTy S ℓ Pt))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (hσ : σE.eval ρ = drvEnc σ) :
    (drvBitE σE).eval ρ = σ.b := by simp only [drvBitE, Expr.eval, hσ]; rfl

@[expose] def kiQueryOkCost (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ := 168 * b.q_total + 24 * qStart + 570
@[expose] def kiQueryOkSize (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ := 3 * bits b.q_total + bits qStart + 730

@[expose] def kiQueryOkE (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) : AExpr Γ .bool :=
  liftLet1E (argTy := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)) (retTy := .bool)
    (.pair σE kqE) (E2EStateRepr.kiQueryOkE b.q_total qStart (.fst (.var .zero)) (.snd (.var .zero)))

theorem kiQueryOkE_cost (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    (kiQueryOkE b qStart σE kqE).cost ≤ σE.cost + kqE.cost + kiQueryOkCost b qStart := by
  have hb := E2EStateRepr.cost_kiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    b.q_total qStart (Γ := [.prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)])
    (.fst (.var .zero)) (.snd (.var .zero))
  simp only [kiQueryOkE, kiQueryOkCost, liftLet1E_cost, Expr.cost] at hb ⊢; omega

theorem kiQueryOkE_size (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    (kiQueryOkE b qStart σE kqE).size ≤ σE.size + kqE.size + kiQueryOkSize b qStart := by
  have hb := E2EStateRepr.size_kiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    b.q_total qStart (Γ := [.prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)])
    (.fst (.var .zero)) (.snd (.var .zero))
  simp only [kiQueryOkE, kiQueryOkSize, liftLet1E_size, Expr.size] at hb ⊢; omega

theorem kiQueryOkE_eval (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) {σ : BHE2EDrvState S ℓ} {kq : SignalPqxdh.KeyIndQuery S}
    (hσ : σE.eval ρ = drvEnc σ) (hkq : kqE.eval ρ = keyIndQenc kq) (hbnd : DrvQueryBounded b.q_total qStart σ) :
    (kiQueryOkE b qStart σE kqE).eval ρ =
      (bhDrvKiQueryOk P σ.toModelDriverBase kq &&
        !(match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false)) := by
  have harg : (Expr.pair σE kqE).eval ρ =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S))
        (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.keyIndQenc (ℓ := ℓ) kq) := by
    dsimp only [Expr.eval]; rw [hσ, hkq, ← liftVal_e2eDrvStateEnc_eq, ← liftVal_keyIndQenc_eq]; rfl
  rw [kiQueryOkE, liftLet1E_eval _ _ ρ _ harg,
    E2EStateRepr.eval_kiQueryOkE b.q_total qStart hP _ _ _ (σ := σ) (kq := kq)
      rfl rfl hbnd.prins_le hbnd.instMeta_le]
  cases kq <;> rfl

@[expose] def mirrorCost : ℕ := 820
@[expose] def mirrorSize : ℕ := 1020

@[expose] def mirrorE {Γ : List (Ty (atomicSig ℓ Pt))} (σE : AExpr Γ (drvTy S ℓ Pt))
    (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) (krE : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) :
    AExpr Γ (drvTy S ℓ Pt) :=
  liftLet1E (argTy := .prod (e2eDrvStateTy S ℓ) (.prod (CryptoVerification.E2E.Costed.keyIndQT S)
    CryptoVerification.E2E.Costed.keyIndRT)) (retTy := e2eDrvStateTy S ℓ) (.pair σE (.pair kqE krE))
    (E2EStateRepr.bhE2EMirrorE (.fst (.var .zero)) (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero))))

theorem mirrorE_cost {Γ : List (Ty (atomicSig ℓ Pt))} (σE : AExpr Γ (drvTy S ℓ Pt))
    (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) (krE : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) :
    (mirrorE σE kqE krE).cost ≤ σE.cost + kqE.cost + krE.cost + mirrorCost := by
  have hb := E2EStateRepr.cost_bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [.prod (e2eDrvStateTy S ℓ) (.prod (CryptoVerification.E2E.Costed.keyIndQT S) CryptoVerification.E2E.Costed.keyIndRT)])
    (.fst (.var .zero)) (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [mirrorE, mirrorCost, liftLet1E_cost, Expr.cost] at hb ⊢; omega

theorem mirrorE_size {Γ : List (Ty (atomicSig ℓ Pt))} (σE : AExpr Γ (drvTy S ℓ Pt))
    (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) (krE : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) :
    (mirrorE σE kqE krE).size ≤ σE.size + kqE.size + krE.size + mirrorSize := by
  have hb := E2EStateRepr.size_bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [.prod (e2eDrvStateTy S ℓ) (.prod (CryptoVerification.E2E.Costed.keyIndQT S) CryptoVerification.E2E.Costed.keyIndRT)])
    (.fst (.var .zero)) (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [mirrorE, mirrorSize, liftLet1E_size, Expr.size] at hb ⊢; omega

theorem mirrorE_eval {Γ : List (Ty (atomicSig ℓ Pt))} (σE : AExpr Γ (drvTy S ℓ Pt))
    (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) (krE : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse)
    (hσ : σE.eval ρ = drvEnc σ) (hkq : kqE.eval ρ = keyIndQenc kq) (hkr : krE.eval ρ = keyIndRenc kr) :
    (mirrorE σE kqE krE).eval ρ = drvEnc (bhE2EMirror σ kq kr) := by
  have harg : (Expr.pair σE (.pair kqE krE)).eval ρ =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ)
        (.prod (CryptoVerification.E2E.Costed.keyIndQT S) CryptoVerification.E2E.Costed.keyIndRT))
        (e2eDrvStateEnc σ, (CryptoVerification.E2E.Costed.keyIndQenc (ℓ := ℓ) kq,
          CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr)) := by
    dsimp only [Expr.eval]; rw [hσ, hkq, hkr, ← liftVal_e2eDrvStateEnc_eq, ← liftVal_keyIndQenc_eq, ← liftVal_keyIndRenc_eq]; rfl
  rw [mirrorE, liftLet1E_eval _ _ ρ _ harg, E2EStateRepr.eval_bhE2EMirrorE_enc _ _ _ _ σ kq kr rfl rfl rfl]
  exact eq_of_heq (liftVal_heq (t := e2eDrvStateTy S ℓ) _)

@[expose] def prepStartSpkCost (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ := 361 * qStart + 3872 * b.q_total + 240
@[expose] def prepStartSpkSize (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ := 2 * bits qStart + 5 * bits b.q_total + 2120

@[expose] def prepStartSpkE (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    AExpr Γ (.opt (.prod (FinT (ℓ := ℓ) (Pt := Pt) S.N_id) (FinT (ℓ := ℓ) (Pt := Pt) S.N_recv))) :=
  liftLet1E (argTy := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S))
    (retTy := .opt (.prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv)))
    (.pair σE sidE) (E2EStateRepr.prepStartSpkE qStart b.q_total b.q_total b.q_total b.q_total
      (.fst (.var .zero)) (.snd (.var .zero)))

theorem prepStartSpkE_cost (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    (prepStartSpkE b qStart σE sidE).cost ≤ σE.cost + sidE.cost + prepStartSpkCost b qStart := by
  have hb := E2EStateRepr.cost_prepStartSpkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    qStart b.q_total b.q_total b.q_total b.q_total
    (Γ := [.prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S)]) (.fst (.var .zero)) (.snd (.var .zero))
  simp only [prepStartSpkE, prepStartSpkCost, liftLet1E_cost, Expr.cost] at hb ⊢; omega

theorem prepStartSpkE_size (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    (prepStartSpkE b qStart σE sidE).size ≤ σE.size + sidE.size + prepStartSpkSize b qStart := by
  have hb := E2EStateRepr.size_prepStartSpkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    qStart b.q_total b.q_total b.q_total b.q_total
    (Γ := [.prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S)]) (.fst (.var .zero)) (.snd (.var .zero))
  simp only [prepStartSpkE, prepStartSpkSize, liftLet1E_size, Expr.size] at hb ⊢; omega

theorem prepStartSpkE_eval (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (hσ : σE.eval ρ = drvEnc σ) (hsid : sidE.eval ρ = sidV sid) (hbnd : DrvQueryBounded b.q_total qStart σ) :
    (prepStartSpkE b qStart σE sidE).eval ρ = (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) := by
  have harg : (Expr.pair σE sidE).eval ρ =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S))
        (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.sidV (ℓ := ℓ) sid) := by
    dsimp only [Expr.eval]; rw [hσ, hsid, ← liftVal_e2eDrvStateEnc_eq, ← liftVal_sidV_eq]; rfl
  have hbndE : E2EStateRepr.DrvMirrorBounded b.q_total b.q_total b.q_total b.q_total b.q_total qStart σ :=
    ⟨hbnd.prins_le, hbnd.bundles_le, hbnd.opks_le, hbnd.sends_le, hbnd.corrPrins_le, hbnd.insts_le, hbnd.instMeta_le⟩
  rw [prepStartSpkE, liftLet1E_eval _ _ ρ _ harg,
    E2EStateRepr.eval_prepStartSpkE_mirrorBounded qStart b.q_total b.q_total b.q_total b.q_total b.q_total
      _ _ _ σ sid rfl rfl hbndE (Nat.le_refl _)]
  exact eq_of_heq (liftVal_heq (t := .opt (.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
    (CryptoVerification.E2E.Costed.FinT S.N_recv))) _)

@[expose, reducible] def spkBodyArgTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (.opt .bool) (.prod (e2eDrvStateTy S ℓ) (.prod (CryptoVerification.E2E.Costed.sidT S)
    (.prod CryptoVerification.E2E.Costed.keyIndRT
      (.prod CryptoVerification.E2E.Costed.keyIndRT CryptoVerification.E2E.Costed.BV256))))

@[expose] def finishSpkWithPqrBodyE (b : SignalPqxdh.QueryBudget) (qStart : ℕ) :
    Expr (e2eOps ℓ P C K decT encT) [spkBodyArgTy S ℓ]
      (.prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) (.opt CryptoVerification.E2E.Costed.BV256)) :=
  let v0 : Expr (e2eOps ℓ P C K decT encT) [spkBodyArgTy S ℓ] (spkBodyArgTy S ℓ) := .var .zero
  .pair (StartAndExtSmAux.finishStartSpkGenE qStart b.q_total b.q_total b.q_total b.q_total
      (.fst v0) (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0))) (.pair (.fst (.snd (.snd (.snd v0))))
        (.pair (.fst (.snd (.snd (.snd (.snd v0))))) (.snd (.snd (.snd (.snd (.snd v0)))))))))
    (.caseOpt (StartAndExtSmAux.extractDrKey32E (.fst (.snd (.snd (.snd v0))))) .none (.some (.snd (.var .zero))))

private theorem size_extractDrKey32_v0 :
    (StartAndExtSmAux.extractDrKey32E (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := [spkBodyArgTy S ℓ]) (.fst (.snd (.snd (.snd (.var .zero)))))).size ≤ 95 := by
  simp only [StartAndExtSmAux.extractDrKey32E, PqxdhSimTypes.eCaseSum, PqxdhSimTypes.v,
    PqxdhSimTypes.Ext.wk, TablesHonest.size_e2ePureOp, E2EPureOp.opSize, Expr.size, bits,
    show Nat.log 2 32 = 5 from rfl]; omega

@[expose] def finishStartSpkHaltedCost (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ := 181 * qStart + 3640 * b.q_total + 98700
@[expose] def finishStartSpkHaltedSize (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ := 5 * bits qStart + 5 * bits b.q_total + 1900

@[expose] def finishStartSpkHaltedE (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (bmE : AExpr Γ (.opt .bool)) (σHE : AExpr Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) (acE : AExpr Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    AExpr Γ (.prod (.opt .nat) (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt)))) :=
  .letE σHE (.letE
    (liftLet1E (argTy := spkBodyArgTy S ℓ) (.pair (wk1E bmE) (.pair (.fst (.var .zero))
      (.pair (wk1E sidE) (.pair (wk1E kr1E) (.pair (wk1E kr2E) (wk1E acE)))))) (finishSpkWithPqrBodyE b qStart))
    (.caseOpt (.fst (.fst (.var .zero)))
      (.pair .none (.pair (.snd (.fst (.var .zero))) (.snd (.var (.succ .zero)))))
      (.caseOpt (.snd (.var (.succ .zero)))
        (.pair (.some (.var .zero)) (.pair (.snd (.fst (.var (.succ .zero)))) (.snd (.var (.succ (.succ .zero))))))
        (.pair (.some (.var (.succ .zero))) (.pair (.snd (.fst (.var (.succ (.succ .zero)))))
          (snocAtomicE qStart (.snd (.var (.succ (.succ (.succ .zero))))) (initKemFailSessionTrackE2EE (.var .zero))))))))

@[expose] def finishStartSpkHaltedC (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (bmE : AExpr Γ (.opt .bool)) (σHE : AExpr Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) (acE : AExpr Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    AComp Γ (.prod (.opt .nat) (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt)))) :=
  .ret (finishStartSpkHaltedE b qStart bmE σHE sidE kr1E kr2E acE)

theorem finishStartSpkHaltedC_cost (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (bmE : AExpr Γ (.opt .bool)) (σHE : AExpr Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) (acE : AExpr Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    (finishStartSpkHaltedC b qStart bmE σHE sidE kr1E kr2E acE).cost ≤
      bmE.cost + σHE.cost + sidE.cost + kr1E.cost + kr2E.cost + acE.cost + finishStartSpkHaltedCost b qStart := by
  let v0 : Expr (e2eOps ℓ P C K decT encT) [spkBodyArgTy S ℓ] (spkBodyArgTy S ℓ) := .var .zero
  have hg := StartAndExtSmAux.cost_finishStartSpkGenE qStart b.q_total b.q_total b.q_total b.q_total
    (.fst v0) (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0))) (.pair (.fst (.snd (.snd (.snd v0))))
      (.pair (.fst (.snd (.snd (.snd (.snd v0))))) (.snd (.snd (.snd (.snd (.snd v0))))))))
  have hex := StartAndExtSmAux.cost_extractDrKey32E (.fst (.snd (.snd (.snd v0))))
  let Γ₃ := BV256 (ℓ := ℓ) (Pt := Pt) :: .nat ::
    liftTy (Pt := Pt) (.prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) (.opt CryptoVerification.E2E.Costed.BV256)) ::
    .prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt)) :: Γ
  have hsn := snocAtomicE_cost (ℓ := ℓ) (Pt := Pt) qStart (O := atomicE2EOps ℓ P C K decT encT) (Γ := Γ₃)
    (.snd (.var (.succ (.succ (.succ .zero))))) (initKemFailSessionTrackE2EE (.var .zero))
  have htr := initKemFailSessionTrackE2EE_cost (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ₃) (.var .zero)
  unfold finishStartSpkHaltedC finishStartSpkHaltedE liftLet1E Expr.wkTop1
    finishSpkWithPqrBodyE finishStartSpkHaltedCost wk1E
  simp only [v0, Γ₃, Comp.cost, Expr.cost, Expr.renameM_cost, liftE2EExpr_cost] at hg hex hsn htr ⊢; omega

theorem finishStartSpkHaltedC_size (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (bmE : AExpr Γ (.opt .bool)) (σHE : AExpr Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) (acE : AExpr Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    (finishStartSpkHaltedC b qStart bmE σHE sidE kr1E kr2E acE).size ≤
      bmE.size + σHE.size + sidE.size + kr1E.size + kr2E.size + acE.size + finishStartSpkHaltedSize b qStart := by
  let v0 : Expr (e2eOps ℓ P C K decT encT) [spkBodyArgTy S ℓ] (spkBodyArgTy S ℓ) := .var .zero
  have hg := M3Subprograms.size_finishStartSpkC (PqxdhSimTypes.e2eProbIface ℓ)
    qStart b.q_total b.q_total b.q_total b.q_total (.fst v0) (.fst (.snd v0)) (.fst (.snd (.snd v0)))
    (.fst (.snd (.snd (.snd v0)))) (.fst (.snd (.snd (.snd (.snd v0))))) (.snd (.snd (.snd (.snd (.snd v0)))))
  unfold StartAndExtSm.finishStartSpkC at hg
  have hex : (StartAndExtSmAux.extractDrKey32E (.fst (.snd (.snd (.snd v0))))).size ≤ 95 :=
    size_extractDrKey32_v0 (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
  let Γ₃ := BV256 (ℓ := ℓ) (Pt := Pt) :: .nat ::
    liftTy (Pt := Pt) (.prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) (.opt CryptoVerification.E2E.Costed.BV256)) ::
    .prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt)) :: Γ
  have hsn := snocAtomicE_size (ℓ := ℓ) (Pt := Pt) qStart (O := atomicE2EOps ℓ P C K decT encT) (Γ := Γ₃)
    (.snd (.var (.succ (.succ (.succ .zero))))) (initKemFailSessionTrackE2EE (.var .zero))
  have htr := initKemFailSessionTrackE2EE_size (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ₃) (.var .zero)
  unfold finishStartSpkHaltedC finishStartSpkHaltedE liftLet1E Expr.wkTop1
    finishSpkWithPqrBodyE finishStartSpkHaltedSize wk1E
  simp only [v0, Γ₃, Comp.size, Expr.size, Expr.renameM_size, liftE2EExpr_size] at hg hex hsn htr ⊢; omega

theorem finishStartSpkHaltedC_queries (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (bmE : AExpr Γ (.opt .bool)) (σHE : AExpr Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) (acE : AExpr Γ (BV256 (ℓ := ℓ) (Pt := Pt)))
    (w : (e2eKeyIndTargetIface S ℓ Pt).Tag → ℕ) :
    (finishStartSpkHaltedC b qStart bmE σHE sidE kr1E kr2E acE).queries w (fun _ => 0) = 0 := rfl

@[simp] private theorem env_get_zero {S₀ : Sig} {Γ : List (Ty S₀)} {t : Ty S₀}
    (x : t.denote) (ρ : Env Γ) : (Env.cons x ρ).get .zero = x := rfl

@[simp] private theorem env_get_succ {S₀ : Sig} {Γ : List (Ty S₀)} {t u : Ty S₀}
    (x : u.denote) (ρ : Env Γ) (v : Var Γ t) : (Env.cons x ρ).get (.succ v) = ρ.get v := rfl

private theorem eval_finishSpkWithPqrBodyE (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    (bm : Option Bool) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) (hbnd : DrvQueryBounded b.q_total qStart σ) :
    (finishSpkWithPqrBodyE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) b qStart).eval
      (.cons (bm, (e2eDrvStateEnc σ, (CryptoVerification.E2E.Costed.sidV (ℓ := ℓ) sid,
        (CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr1,
          (CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr2, ac))))) .nil) =
    ((let res := bhE2EFinishStartSpk C K bm σ sid kr1 kr2 ac; (res.1, e2eDrvStateEnc res.2)),
     match kr1 with
     | .drKeyResp dk =>
       if dk.rootKey.length == 32 && dk.chainKey.length == 32 && dk.pqrKey.length == 32 then
         some (bhBytesWord dk.pqrKey) else none
     | _ => none) := by
  have hbnd0 : DrvMirrorBounded b.q_total b.q_total b.q_total b.q_total 0 qStart σ ∨
      (σ.insts.length ≤ qStart ∧ σ.instMeta.length ≤ qStart ∧ σ.prins.length ≤ b.q_total ∧
       σ.bundles.length ≤ b.q_total ∧ σ.opks.length ≤ b.q_total ∧ σ.sends.length ≤ b.q_total ∧ σ.corrPrins.length ≤ b.q_total) :=
    Or.inr ⟨hbnd.insts_le, hbnd.instMeta_le, hbnd.prins_le, hbnd.bundles_le, hbnd.opks_le, hbnd.sends_le, hbnd.corrPrins_le⟩
  unfold finishSpkWithPqrBodyE; dsimp only [Expr.eval]
  rw [StartAndExtSmAux.eval_finishStartSpkGenE qStart b.q_total b.q_total b.q_total b.q_total
    _ _ _ _ rfl hbnd0, StartAndExtSmAux.eval_extractDrKey32E]
  simp only [Expr.eval, env_get_zero, TablesHonest.sidOfV_sidV, TablesHonest.keyIndRdec_keyIndRenc]
  cases kr1 with
  | drKeyResp dk =>
    by_cases h : (dk.rootKey.length == 32 && dk.chainKey.length == 32 && dk.pqrKey.length == 32) = true <;> simp [h]
  | _ => rfl

theorem finishStartSpkHaltedC_eval (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (bmE : AExpr Γ (.opt .bool)) (σHE : AExpr Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) (acE : AExpr Γ (BV256 (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes))
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (hσH : σHE.eval ρ = (drvEnc σH.1, σH.2.map sessHEnc)) (hsid : sidE.eval ρ = sidV sid)
    (hkr1 : kr1E.eval ρ = keyIndRenc kr1) (hkr2 : kr2E.eval ρ = keyIndRenc kr2)
    (hTracks : σH.2.length ≤ qStart) (hbnd : DrvQueryBounded b.q_total qStart σH.1) :
    (finishStartSpkHaltedC b qStart bmE σHE sidE kr1E kr2E acE).eval ρ =
      let res := bhE2EFinishStartSpk C K (bmE.eval ρ) σH.1 sid kr1 kr2 (acE.eval ρ)
      let tracks' := match res.1, kr1 with
        | some _, .drKeyResp dk => σH.2 ++ [initKemFailSessionTrack C.F Bytes (bhKeySOf dk (acE.eval ρ)).2.2]
        | _, _ => σH.2
      pure (res.1, (drvEnc res.2, tracks'.map sessHEnc)) := by
  let ρ1 := Env.cons (σHE.eval ρ) ρ
  have hren : ∀ {t : Ty (atomicSig ℓ Pt)} (e : AExpr Γ t),
      (wk1E (u := .prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))) e).eval ρ1 = e.eval ρ :=
    fun e => Expr.renameM_eval e fun _ _ => rfl
  have harg : (Expr.pair (wk1E bmE) (.pair (.fst (.var .zero))
      (.pair (wk1E sidE) (.pair (wk1E kr1E) (.pair (wk1E kr2E) (wk1E acE)))))).eval ρ1 =
      liftVal (Pt := Pt) (t := spkBodyArgTy S ℓ) (bmE.eval ρ, (e2eDrvStateEnc σH.1,
        (CryptoVerification.E2E.Costed.sidV (ℓ := ℓ) sid,
          (CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr1,
            (CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr2, acE.eval ρ))))) := by
    dsimp only [Expr.eval]; rw [hren, hren, hren, hren, hren]
    simp only [ρ1, env_get_zero, hσH, hsid, hkr1, hkr2]
    rw [← liftVal_e2eDrvStateEnc_eq, ← liftVal_sidV_eq, ← liftVal_keyIndRenc_eq, ← liftVal_keyIndRenc_eq]
    cases bmE.eval ρ <;> rfl
  have hlv : ∀ (a : Option ℕ) (s : BHE2EDrvState S ℓ) (k? : Option (BitVec 256)),
      liftVal (Pt := Pt) (t := .prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) (.opt CryptoVerification.E2E.Costed.BV256))
        ((a, e2eDrvStateEnc s), k?) = ((a, drvEnc (Pt := Pt) s), k?) := by
    intro a s k?; cases a <;> cases k? <;> exact Prod.ext (Prod.ext rfl (liftVal_e2eDrvStateEnc_eq s)) rfl
  have hlet := liftLet1E_eval (argTy := spkBodyArgTy S ℓ)
    (.pair (wk1E bmE) (.pair (.fst (.var .zero)) (.pair (wk1E sidE) (.pair (wk1E kr1E) (.pair (wk1E kr2E) (wk1E acE))))))
    (finishSpkWithPqrBodyE b qStart) ρ1 _ harg
  rw [eval_finishSpkWithPqrBodyE _ _ _ _ _ _ _ _ hbnd, hlv] at hlet
  dsimp only [finishStartSpkHaltedC, Comp.eval]; congr 1; unfold finishStartSpkHaltedE
  change (Expr.caseOpt _ _ _).eval (Env.cons ((liftLet1E (argTy := spkBodyArgTy S ℓ) _ _).eval ρ1) ρ1) = _
  rw [hlet]
  rcases hres : bhE2EFinishStartSpk C K (bmE.eval ρ) σH.1 sid kr1 kr2 (acE.eval ρ) with ⟨_ | idx, σ'⟩
  · simp only [Expr.eval, ρ1, env_get_zero, env_get_succ, hσH]
  · obtain ⟨dk, rfl, h1, h2, h3⟩ := bhE2EFinishStartSpk_some_drKey C K _ _ _ _ _ _ hres
    dsimp only
    simp only [h1, h2, h3, beq_self_eq_true, Bool.and_self, ↓reduceIte, Expr.eval, ρ1, env_get_zero, env_get_succ, hσH]
    have hmapLen : (List.map (sessHEnc (ℓ := ℓ) (Pt := Pt)) σH.2).length ≤ qStart := by simpa using hTracks
    rw [snocAtomicE_eval qStart _ _ _ (by simpa only [Expr.eval, ρ1, env_get_zero, env_get_succ, hσH] using hmapLen),
      initKemFailSessionTrackE2EE_eval]
    simp only [Expr.eval, env_get_zero, env_get_succ, bhKeySOf, List.map_append, List.map_cons, List.map_nil]

@[expose] def finishKindCost (qStart : ℕ) : ℕ := FreshnessSim.finishKindCost qStart + 10
@[expose] def finishKindSize (qStart : ℕ) : ℕ := bits qStart + 90

@[expose] def finishKindE (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (bOutE : AExpr Γ .bool) : AExpr Γ .bool :=
  liftLet1E (argTy := .prod (e2eDrvStateTy S ℓ) .bool) (retTy := .bool) (.pair σE bOutE)
    (FreshnessSim.finishKindE qStart (.fst (.var .zero)) (.snd (.var .zero)))

theorem finishKindE_cost (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (bOutE : AExpr Γ .bool) :
    (finishKindE qStart σE bOutE).cost ≤ σE.cost + bOutE.cost + finishKindCost qStart := by
  have hb := FreshnessSim.cost_finishKindE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    qStart (Γ := [.prod (e2eDrvStateTy S ℓ) .bool]) (.fst (.var .zero)) (.snd (.var .zero))
  simp only [finishKindE, finishKindCost, liftLet1E_cost, Expr.cost] at hb ⊢; omega

theorem finishKindE_size (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (bOutE : AExpr Γ .bool) :
    (finishKindE qStart σE bOutE).size ≤ σE.size + bOutE.size + finishKindSize qStart := by
  have hb := M3Subprograms.size_finishKindE ℓ S P C K decT encT qStart
    (Γ := [.prod (e2eDrvStateTy S ℓ) .bool]) (.fst (.var .zero)) (.snd (.var .zero))
  simp only [finishKindE, finishKindSize, liftLet1E_size, Expr.size] at hb ⊢; omega

theorem finishKindE_eval (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (bOutE : AExpr Γ .bool)
    (ρ : Env Γ) {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = drvEnc σ) (hInsts : σ.insts.length ≤ qStart) :
    (finishKindE qStart σE bOutE).eval ρ = (bOutE.eval ρ == σ.b || bhE2EDrvWon σ σ.b) := by
  have harg : (Expr.pair σE bOutE).eval ρ =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ) .bool) (e2eDrvStateEnc σ, bOutE.eval ρ) := by
    dsimp only [Expr.eval]; rw [hσ, ← liftVal_e2eDrvStateEnc_eq]; rfl
  rw [finishKindE, liftLet1E_eval _ _ ρ _ harg]
  exact FreshnessSim.eval_finishKindE qStart _ _ _ rfl hInsts

/-! ## Clamped handshake and pure subprograms -/

private theorem bits_mono_local {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b := by
  simp only [bits]; exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem bits_le_succ_local (n : ℕ) : bits n ≤ n + 1 := by
  simp only [bits]; exact Nat.add_le_add_right (Nat.log_le_self 2 n) 1

/-- Variant of `bhE2EMirror` capping `bundles` at `nSpk` and `opks` at `nOpk`, agreeing with `bhE2EMirror` below those bounds. -/
@[expose] def bhE2EMirrorClamped {S : SignalPqxdh.Setup} {ℓ : ℕ} (nSpk nOpk : ℕ)
    (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S)
    (kr : SignalPqxdh.KeyIndResponse) : BHE2EDrvState S ℓ :=
  let σ' := bhE2EMirror σ kq kr
  { σ' with
    bundles := if σ.bundles.length < nSpk then σ'.bundles else σ.bundles
    opks := if σ.opks.length < nOpk then σ'.opks else σ.opks }

theorem bhE2EMirrorClamped_eq_of_lt {S : SignalPqxdh.Setup} {ℓ : ℕ} {nSpk nOpk : ℕ}
    (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse)
    (hSpk : (kq matches .genSPK ..) → (kr matches .bundleResp ..) → σ.bundles.length < nSpk)
    (hOpk : (kq matches .genOPK ..) → (kr matches .pkResp ..) → σ.opks.length < nOpk) :
    bhE2EMirrorClamped nSpk nOpk σ kq kr = bhE2EMirror σ kq kr := by
  have h1 : (if σ.bundles.length < nSpk then (bhE2EMirror σ kq kr).bundles else σ.bundles) =
      (bhE2EMirror σ kq kr).bundles := by
    by_cases hlt : σ.bundles.length < nSpk
    · simp [hlt]
    · simp only [hlt, ↓reduceIte]
      dsimp only [bhE2EMirror]
      unfold CryptoVerification.E2E.bhBaseMirror
      split
      · rfl
      · exact absurd (hSpk rfl rfl) hlt
      · rfl
      · rfl
      · rfl
      · rfl
  have h2 : (if σ.opks.length < nOpk then (bhE2EMirror σ kq kr).opks else σ.opks) =
      (bhE2EMirror σ kq kr).opks := by
    by_cases hlt : σ.opks.length < nOpk
    · simp [hlt]
    · simp only [hlt, ↓reduceIte]
      dsimp only [bhE2EMirror]
      unfold CryptoVerification.E2E.bhBaseMirror
      split
      · rfl
      · rfl
      · exact absurd (hOpk rfl rfl) hlt
      · rfl
      · rfl
      · rfl
  dsimp only [bhE2EMirrorClamped]
  rw [h1, h2]

theorem drvMirrorBounded_bhE2EMirrorClamped {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {nP nP' nSpk nOpk nSend nSend' nC nC' nI : ℕ} {σ : BHE2EDrvState S ℓ}
    (h : DrvMirrorBounded nP nSpk nOpk nSend nC nI σ)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse)
    (hP' : (kq matches .initPrin ..) → nP + 1 ≤ nP')
    (hS' : (kq matches .initiateOPK .. || kq matches .initiateNoOPK ..) → nSend + 1 ≤ nSend')
    (hP0 : nP ≤ nP') (hS0 : nSend ≤ nSend') (hC0 : nC + 1 ≤ nC') :
    DrvMirrorBounded nP' nSpk nOpk nSend' nC' nI
      (bhE2EMirrorClamped nSpk nOpk σ kq kr) := by
  have hm := DrvMirrorBounded.mirror h kq kr
  refine ⟨?_, ?_, ?_, ?_, ?_, h.insts_le, h.instMeta_le, ?_⟩
  · dsimp only [bhE2EMirrorClamped, bhE2EMirror]
    unfold CryptoVerification.E2E.bhBaseMirror
    split
    · simp only [List.length_cons]; have := hP' rfl; have := h.prins_le; omega
    · exact Nat.le_trans h.prins_le hP0
    · exact Nat.le_trans h.prins_le hP0
    · exact Nat.le_trans h.prins_le hP0
    · exact Nat.le_trans h.prins_le hP0
    · exact Nat.le_trans h.prins_le hP0
  · dsimp only [bhE2EMirrorClamped]
    by_cases hlt : σ.bundles.length < nSpk
    · simp only [hlt, ↓reduceIte]
      have hb0 := (E2EStateRepr.DrvMirrorBounded.bhE2EMirror
        ⟨h.prins_le, Nat.le_refl _, h.opks_le, h.sends_le, h.corrPrins_le, h.insts_le, h.instMeta_le⟩ kq kr).bundles_le
      omega
    · simp only [hlt, ↓reduceIte]; exact h.bundles_le
  · dsimp only [bhE2EMirrorClamped]
    by_cases hlt : σ.opks.length < nOpk
    · simp only [hlt, ↓reduceIte]
      have ho0 := (E2EStateRepr.DrvMirrorBounded.bhE2EMirror
        ⟨h.prins_le, h.bundles_le, Nat.le_refl _, h.sends_le, h.corrPrins_le, h.insts_le, h.instMeta_le⟩ kq kr).opks_le
      omega
    · simp only [hlt, ↓reduceIte]; exact h.opks_le
  · dsimp only [bhE2EMirrorClamped, bhE2EMirror]
    unfold CryptoVerification.E2E.bhBaseMirror
    split
    · exact Nat.le_trans h.sends_le hS0
    · exact Nat.le_trans h.sends_le hS0
    · exact Nat.le_trans h.sends_le hS0
    · simp only [List.length_cons]; have := hS' (by simp); have := h.sends_le; omega
    · simp only [List.length_cons]; have := hS' (by simp); have := h.sends_le; omega
    · exact Nat.le_trans h.sends_le hS0
  · dsimp only [bhE2EMirrorClamped]; have := hm.corrPrins_le; omega
  · dsimp only [bhE2EMirrorClamped]; have := hm.revSpks_le; omega

@[expose] def mirrorClampedCost (b : SignalPqxdh.QueryBudget) : ℕ := 2 * b.q_total + 880
@[expose] def mirrorClampedSize (b : SignalPqxdh.QueryBudget) : ℕ := 2 * bits b.q_total + 1080

@[expose] def mirrorClampedBodyE (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) :
    Expr (e2eOps ℓ P C K decT encT)
      [.prod (e2eDrvStateTy S ℓ)
        (.prod (CryptoVerification.E2E.Costed.keyIndQT S) CryptoVerification.E2E.Costed.keyIndRT)]
      (e2eDrvStateTy S ℓ) :=
  let nSpk := min b.q_total S.N_spk_tot
  let nOpk := min b.q_total S.N_opk_tot
  let bOld := E2EStateRepr.drvBase (.fst (.var (.succ .zero)))
  let bNew := E2EStateRepr.drvBase (.var .zero)
  .letE (E2EStateRepr.bhE2EMirrorE (.fst (.var .zero)) (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero))))
    (.pair
      (.pair (E2EStateRepr.mbPrins bNew)
        (.pair
          (.ite (.lt (.len (E2EStateRepr.mbBundles bOld)) (.nat nSpk))
            (E2EStateRepr.mbBundles bNew) (E2EStateRepr.mbBundles bOld))
          (.pair
            (.ite (.lt (.len (E2EStateRepr.mbOpks bOld)) (.nat nOpk))
              (E2EStateRepr.mbOpks bNew) (E2EStateRepr.mbOpks bOld))
            (E2EStateRepr.mbSends bNew))))
      (.snd (.var .zero)))

@[expose] def mirrorClampedE (b : SignalPqxdh.QueryBudget) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (krE : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) : AExpr Γ (drvTy S ℓ Pt) :=
  liftLet1E (argTy := .prod (e2eDrvStateTy S ℓ) (.prod (CryptoVerification.E2E.Costed.keyIndQT S)
    CryptoVerification.E2E.Costed.keyIndRT)) (retTy := e2eDrvStateTy S ℓ)
    (.pair σE (.pair kqE krE)) (mirrorClampedBodyE S b)

theorem mirrorClampedE_cost (b : SignalPqxdh.QueryBudget) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (krE : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) :
    (mirrorClampedE b σE kqE krE).cost ≤ σE.cost + kqE.cost + krE.cost + mirrorClampedCost b := by
  let nSpk := min b.q_total S.N_spk_tot
  let nOpk := min b.q_total S.N_opk_tot
  have hb := E2EStateRepr.cost_bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [.prod (e2eDrvStateTy S ℓ) (.prod (CryptoVerification.E2E.Costed.keyIndQT S) CryptoVerification.E2E.Costed.keyIndRT)])
    (.fst (.var .zero)) (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero)))
  have hcSpk : bits nSpk ≤ b.q_total + 1 :=
    Nat.le_trans (bits_le_succ_local nSpk) (Nat.add_le_add_right (Nat.min_le_left _ _) 1)
  have hcOpk : bits nOpk ≤ b.q_total + 1 :=
    Nat.le_trans (bits_le_succ_local nOpk) (Nat.add_le_add_right (Nat.min_le_left _ _) 1)
  simp only [mirrorClampedE, mirrorClampedBodyE, mirrorClampedCost, liftLet1E_cost,
    E2EStateRepr.drvBase, E2EStateRepr.mbPrins, E2EStateRepr.mbBundles, E2EStateRepr.mbOpks, E2EStateRepr.mbSends,
    Expr.cost, nSpk, nOpk] at hb hcSpk hcOpk ⊢
  omega

theorem mirrorClampedE_size (b : SignalPqxdh.QueryBudget) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (krE : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) :
    (mirrorClampedE b σE kqE krE).size ≤ σE.size + kqE.size + krE.size + mirrorClampedSize b := by
  let nSpk := min b.q_total S.N_spk_tot
  let nOpk := min b.q_total S.N_opk_tot
  have hb := E2EStateRepr.size_bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [.prod (e2eDrvStateTy S ℓ) (.prod (CryptoVerification.E2E.Costed.keyIndQT S) CryptoVerification.E2E.Costed.keyIndRT)])
    (.fst (.var .zero)) (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero)))
  have hbSpk : bits nSpk ≤ bits b.q_total := bits_mono_local (Nat.min_le_left _ _)
  have hbOpk : bits nOpk ≤ bits b.q_total := bits_mono_local (Nat.min_le_left _ _)
  simp only [mirrorClampedE, mirrorClampedBodyE, mirrorClampedSize, liftLet1E_size,
    E2EStateRepr.drvBase, E2EStateRepr.mbPrins, E2EStateRepr.mbBundles, E2EStateRepr.mbOpks, E2EStateRepr.mbSends,
    Expr.size, nSpk, nOpk] at hb hbSpk hbOpk ⊢
  omega

theorem mirrorClampedE_eval (b : SignalPqxdh.QueryBudget) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (krE : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse)
    (hσ : σE.eval ρ = drvEnc σ) (hkq : kqE.eval ρ = keyIndQenc kq) (hkr : krE.eval ρ = keyIndRenc kr) :
    (mirrorClampedE b σE kqE krE).eval ρ =
      drvEnc (bhE2EMirrorClamped (min b.q_total S.N_spk_tot) (min b.q_total S.N_opk_tot) σ kq kr) := by
  have harg : (Expr.pair σE (.pair kqE krE)).eval ρ =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ)
        (.prod (CryptoVerification.E2E.Costed.keyIndQT S) CryptoVerification.E2E.Costed.keyIndRT))
        (e2eDrvStateEnc σ, (CryptoVerification.E2E.Costed.keyIndQenc (ℓ := ℓ) kq,
          CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr)) := by
    dsimp only [Expr.eval]
    rw [hσ, hkq, hkr, ← liftVal_e2eDrvStateEnc_eq, ← liftVal_keyIndQenc_eq, ← liftVal_keyIndRenc_eq]
    rfl
  rw [mirrorClampedE, liftLet1E_eval _ _ ρ _ harg]
  have hbody :
      (mirrorClampedBodyE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) S b).eval
        (Env.cons (e2eDrvStateEnc σ, (CryptoVerification.E2E.Costed.keyIndQenc (ℓ := ℓ) kq,
          CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr)) Env.nil) =
      e2eDrvStateEnc (bhE2EMirrorClamped (min b.q_total S.N_spk_tot) (min b.q_total S.N_opk_tot) σ kq kr) := by
    unfold mirrorClampedBodyE
    dsimp only [Expr.eval]
    rw [E2EStateRepr.eval_bhE2EMirrorE_enc _ _ _ _ σ kq kr rfl rfl rfl]
    simp only [E2EStateRepr.drvBase, E2EStateRepr.mbPrins, E2EStateRepr.mbBundles, E2EStateRepr.mbOpks,
      E2EStateRepr.mbSends, Expr.eval, env_get_zero, env_get_succ, e2eDrvStateEnc,
      E2EStateRepr.e2eDrvStateEnc, M3Interfaces.e2eMirrorBaseEnc, bhE2EMirrorClamped, decide_eq_true_eq]
    rfl
  rw [hbody, liftVal_e2eDrvStateEnc_eq]

@[expose] def kiQueryOkClampedCost (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  168 * b.q_total + 24 * min qStart (min b.q_total S.N_send_tot) + 570

@[expose] def kiQueryOkClampedSize (b : SignalPqxdh.QueryBudget) : ℕ :=
  4 * bits b.q_total + 730

@[expose] def kiQueryOkClampedE (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) : AExpr Γ .bool :=
  kiQueryOkE b (min qStart (min b.q_total S.N_send_tot)) σE kqE

theorem kiQueryOkClampedE_cost (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    (kiQueryOkClampedE b qStart σE kqE).cost ≤ σE.cost + kqE.cost + kiQueryOkClampedCost S b qStart := by
  have h := kiQueryOkE_cost (S := S) (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) b (min qStart (min b.q_total S.N_send_tot)) σE kqE
  simp only [kiQueryOkClampedE, kiQueryOkClampedCost, kiQueryOkCost] at h ⊢; omega

theorem kiQueryOkClampedE_size (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    (kiQueryOkClampedE b qStart σE kqE).size ≤ σE.size + kqE.size + kiQueryOkClampedSize b := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  have h : (kiQueryOkClampedE b qStart σE kqE).size ≤ σE.size + kqE.size + kiQueryOkSize b nInst :=
    kiQueryOkE_size b nInst σE kqE
  have hbInst : bits nInst ≤ bits b.q_total :=
    bits_mono_local (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))
  have hsz : kiQueryOkSize b nInst ≤ kiQueryOkClampedSize b := by
    dsimp only [kiQueryOkSize, kiQueryOkClampedSize]; omega
  exact Nat.le_trans h (Nat.add_le_add_left hsz _)

theorem kiQueryOkClampedE_eval (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (kqE : AExpr Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) {σ : BHE2EDrvState S ℓ} {kq : SignalPqxdh.KeyIndQuery S}
    (hσ : σE.eval ρ = drvEnc σ) (hkq : kqE.eval ρ = keyIndQenc kq)
    (hPrins : σ.prins.length ≤ b.q_total)
    (hMeta : σ.instMeta.length ≤ min qStart (min b.q_total S.N_send_tot)) :
    (kiQueryOkClampedE b qStart σE kqE).eval ρ =
      (bhDrvKiQueryOk P σ.toModelDriverBase kq &&
        !(match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false)) := by
  have harg : (Expr.pair σE kqE).eval ρ =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S))
        (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.keyIndQenc (ℓ := ℓ) kq) := by
    dsimp only [Expr.eval]; rw [hσ, hkq, ← liftVal_e2eDrvStateEnc_eq, ← liftVal_keyIndQenc_eq]; rfl
  rw [kiQueryOkClampedE, kiQueryOkE, liftLet1E_eval _ _ ρ _ harg,
    E2EStateRepr.eval_kiQueryOkE b.q_total (min qStart (min b.q_total S.N_send_tot)) hP _ _ _ (σ := σ) (kq := kq)
      rfl rfl hPrins hMeta]
  cases kq <;> rfl

@[expose] def prepStartSpkClampedCost (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  361 * min qStart (min b.q_total S.N_send_tot) + 120 * b.q_total +
    3300 * min b.q_total S.N_spk_tot + 165 * min b.q_total S.N_opk_tot +
    310 * min b.q_total S.N_send_tot + 240

@[expose] def prepStartSpkClampedSize (b : SignalPqxdh.QueryBudget) : ℕ :=
  7 * bits b.q_total + 2120

@[expose] def prepStartSpkClampedE (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    AExpr Γ (.opt (.prod (FinT (ℓ := ℓ) (Pt := Pt) S.N_id) (FinT (ℓ := ℓ) (Pt := Pt) S.N_recv))) :=
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let nSpk := min b.q_total S.N_spk_tot
  let nOpk := min b.q_total S.N_opk_tot
  let nSend := min b.q_total S.N_send_tot
  liftLet1E (argTy := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S))
    (retTy := .opt (.prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv)))
    (.pair σE sidE)
    (E2EStateRepr.prepStartSpkE nInst b.q_total nSpk nOpk nSend (.fst (.var .zero)) (.snd (.var .zero)))

theorem prepStartSpkClampedE_cost (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    (prepStartSpkClampedE b qStart σE sidE).cost ≤
      σE.cost + sidE.cost + prepStartSpkClampedCost S b qStart := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let nSpk := min b.q_total S.N_spk_tot
  let nOpk := min b.q_total S.N_opk_tot
  let nSend := min b.q_total S.N_send_tot
  have hb := E2EStateRepr.cost_prepStartSpkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    nInst b.q_total nSpk nOpk nSend
    (Γ := [.prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S)]) (.fst (.var .zero)) (.snd (.var .zero))
  simp only [prepStartSpkClampedE, prepStartSpkClampedCost, liftLet1E_cost, Expr.cost, nInst, nSpk, nOpk, nSend] at hb ⊢
  omega

theorem prepStartSpkClampedE_size (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    (prepStartSpkClampedE b qStart σE sidE).size ≤
      σE.size + sidE.size + prepStartSpkClampedSize b := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let nSpk := min b.q_total S.N_spk_tot
  let nOpk := min b.q_total S.N_opk_tot
  let nSend := min b.q_total S.N_send_tot
  have hb := E2EStateRepr.size_prepStartSpkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    nInst b.q_total nSpk nOpk nSend
    (Γ := [.prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S)]) (.fst (.var .zero)) (.snd (.var .zero))
  have hbInst : bits nInst ≤ bits b.q_total :=
    bits_mono_local (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))
  have hbSpk : bits nSpk ≤ bits b.q_total := bits_mono_local (Nat.min_le_left _ _)
  have hbOpk : bits nOpk ≤ bits b.q_total := bits_mono_local (Nat.min_le_left _ _)
  have hbSend : bits nSend ≤ bits b.q_total := bits_mono_local (Nat.min_le_left _ _)
  simp only [prepStartSpkClampedE, prepStartSpkClampedSize, liftLet1E_size, Expr.size,
    nInst, nSpk, nOpk, nSend] at hb hbInst hbSpk hbOpk hbSend ⊢
  omega

theorem prepStartSpkClampedE_eval (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (hσ : σE.eval ρ = drvEnc σ) (hsid : sidE.eval ρ = sidV sid)
    (hbnd : DrvMirrorBounded b.q_total (min b.q_total S.N_spk_tot) (min b.q_total S.N_opk_tot)
      (min b.q_total S.N_send_tot) b.q_total (min qStart (min b.q_total S.N_send_tot)) σ) :
    (prepStartSpkClampedE b qStart σE sidE).eval ρ = (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) := by
  have harg : (Expr.pair σE sidE).eval ρ =
      liftVal (Pt := Pt) (t := .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.sidT S))
        (e2eDrvStateEnc σ, CryptoVerification.E2E.Costed.sidV (ℓ := ℓ) sid) := by
    dsimp only [Expr.eval]; rw [hσ, hsid, ← liftVal_e2eDrvStateEnc_eq, ← liftVal_sidV_eq]; rfl
  have hbndE : E2EStateRepr.DrvMirrorBounded b.q_total (min b.q_total S.N_spk_tot)
      (min b.q_total S.N_opk_tot) (min b.q_total S.N_send_tot) b.q_total
      (min qStart (min b.q_total S.N_send_tot)) σ :=
    ⟨hbnd.prins_le, hbnd.bundles_le, hbnd.opks_le, hbnd.sends_le, hbnd.corrPrins_le, hbnd.insts_le, hbnd.instMeta_le⟩
  rw [prepStartSpkClampedE, liftLet1E_eval _ _ ρ _ harg,
    E2EStateRepr.eval_prepStartSpkE_mirrorBounded (min qStart (min b.q_total S.N_send_tot))
      b.q_total (min b.q_total S.N_spk_tot) (min b.q_total S.N_opk_tot) (min b.q_total S.N_send_tot) b.q_total
      _ _ _ σ sid rfl rfl hbndE (Nat.le_refl _)]
  exact eq_of_heq (liftVal_heq (t := .opt (.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
    (CryptoVerification.E2E.Costed.FinT S.N_recv))) _)

@[expose] def finishSpkWithPqrClampedBodyE (b : SignalPqxdh.QueryBudget) (qStart : ℕ) :
    Expr (e2eOps ℓ P C K decT encT) [spkBodyArgTy S ℓ]
      (.prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) (.opt CryptoVerification.E2E.Costed.BV256)) :=
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let nSpk := min b.q_total S.N_spk_tot
  let nOpk := min b.q_total S.N_opk_tot
  let nSend := min b.q_total S.N_send_tot
  let v0 : Expr (e2eOps ℓ P C K decT encT) [spkBodyArgTy S ℓ] (spkBodyArgTy S ℓ) := .var .zero
  .pair (StartAndExtSmAux.finishStartSpkGenE nInst b.q_total nSpk nOpk nSend
      (.fst v0) (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0))) (.pair (.fst (.snd (.snd (.snd v0))))
        (.pair (.fst (.snd (.snd (.snd (.snd v0))))) (.snd (.snd (.snd (.snd (.snd v0)))))))))
    (.caseOpt (StartAndExtSmAux.extractDrKey32E (.fst (.snd (.snd (.snd v0))))) .none (.some (.snd (.var .zero))))

@[expose] def finishStartSpkHaltedClampedCost (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  181 * min qStart (min b.q_total S.N_send_tot) + 110 * b.q_total +
    3300 * min b.q_total S.N_spk_tot + 150 * min b.q_total S.N_opk_tot +
    110 * min b.q_total S.N_send_tot + 98700

@[expose] def finishStartSpkHaltedClampedSize (b : SignalPqxdh.QueryBudget) : ℕ :=
  10 * bits b.q_total + 1900

@[expose] def finishStartSpkHaltedClampedE (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (bmE : AExpr Γ (.opt .bool)) (σHE : AExpr Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) (acE : AExpr Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    AExpr Γ (.prod (.opt .nat) (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt)))) :=
  let nInst := min qStart (min b.q_total S.N_send_tot)
  .letE σHE (.letE
    (liftLet1E (argTy := spkBodyArgTy S ℓ) (.pair (wk1E bmE) (.pair (.fst (.var .zero))
      (.pair (wk1E sidE) (.pair (wk1E kr1E) (.pair (wk1E kr2E) (wk1E acE))))))
      (finishSpkWithPqrClampedBodyE b qStart))
    (.caseOpt (.fst (.fst (.var .zero)))
      (.pair .none (.pair (.snd (.fst (.var .zero))) (.snd (.var (.succ .zero)))))
      (.caseOpt (.snd (.var (.succ .zero)))
        (.pair (.some (.var .zero)) (.pair (.snd (.fst (.var (.succ .zero)))) (.snd (.var (.succ (.succ .zero))))))
        (.pair (.some (.var (.succ .zero))) (.pair (.snd (.fst (.var (.succ (.succ .zero)))))
          (snocAtomicE nInst (.snd (.var (.succ (.succ (.succ .zero))))) (initKemFailSessionTrackE2EE (.var .zero))))))))

@[expose] def finishStartSpkHaltedClampedC (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (bmE : AExpr Γ (.opt .bool)) (σHE : AExpr Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) (acE : AExpr Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    AComp Γ (.prod (.opt .nat) (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt)))) :=
  .ret (finishStartSpkHaltedClampedE b qStart bmE σHE sidE kr1E kr2E acE)

theorem finishStartSpkHaltedClampedC_cost (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (bmE : AExpr Γ (.opt .bool)) (σHE : AExpr Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) (acE : AExpr Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    (finishStartSpkHaltedClampedC b qStart bmE σHE sidE kr1E kr2E acE).cost ≤
      bmE.cost + σHE.cost + sidE.cost + kr1E.cost + kr2E.cost + acE.cost +
        finishStartSpkHaltedClampedCost S b qStart := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let nSpk := min b.q_total S.N_spk_tot
  let nOpk := min b.q_total S.N_opk_tot
  let nSend := min b.q_total S.N_send_tot
  let v0 : Expr (e2eOps ℓ P C K decT encT) [spkBodyArgTy S ℓ] (spkBodyArgTy S ℓ) := .var .zero
  have hg := StartAndExtSmAux.cost_finishStartSpkGenE nInst b.q_total nSpk nOpk nSend
    (.fst v0) (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0))) (.pair (.fst (.snd (.snd (.snd v0))))
      (.pair (.fst (.snd (.snd (.snd (.snd v0))))) (.snd (.snd (.snd (.snd (.snd v0))))))))
  have hex := StartAndExtSmAux.cost_extractDrKey32E (.fst (.snd (.snd (.snd v0))))
  let Γ₃ := BV256 (ℓ := ℓ) (Pt := Pt) :: .nat ::
    liftTy (Pt := Pt) (.prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) (.opt CryptoVerification.E2E.Costed.BV256)) ::
    .prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt)) :: Γ
  have hsn := snocAtomicE_cost (ℓ := ℓ) (Pt := Pt) nInst (O := atomicE2EOps ℓ P C K decT encT) (Γ := Γ₃)
    (.snd (.var (.succ (.succ (.succ .zero))))) (initKemFailSessionTrackE2EE (.var .zero))
  have htr := initKemFailSessionTrackE2EE_cost (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ₃) (.var .zero)
  unfold finishStartSpkHaltedClampedC finishStartSpkHaltedClampedE liftLet1E Expr.wkTop1
    finishSpkWithPqrClampedBodyE finishStartSpkHaltedClampedCost wk1E
  simp only [v0, Γ₃, nInst, nSpk, nOpk, nSend, Comp.cost, Expr.cost, Expr.renameM_cost, liftE2EExpr_cost] at hg hex hsn htr ⊢
  omega

theorem finishStartSpkHaltedClampedC_size (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (bmE : AExpr Γ (.opt .bool)) (σHE : AExpr Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) (acE : AExpr Γ (BV256 (ℓ := ℓ) (Pt := Pt))) :
    (finishStartSpkHaltedClampedC b qStart bmE σHE sidE kr1E kr2E acE).size ≤
      bmE.size + σHE.size + sidE.size + kr1E.size + kr2E.size + acE.size +
        finishStartSpkHaltedClampedSize b := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let nSpk := min b.q_total S.N_spk_tot
  let nOpk := min b.q_total S.N_opk_tot
  let nSend := min b.q_total S.N_send_tot
  let v0 : Expr (e2eOps ℓ P C K decT encT) [spkBodyArgTy S ℓ] (spkBodyArgTy S ℓ) := .var .zero
  have hg := M3Subprograms.size_finishStartSpkC (PqxdhSimTypes.e2eProbIface ℓ)
    nInst b.q_total nSpk nOpk nSend (.fst v0) (.fst (.snd v0)) (.fst (.snd (.snd v0)))
    (.fst (.snd (.snd (.snd v0)))) (.fst (.snd (.snd (.snd (.snd v0))))) (.snd (.snd (.snd (.snd (.snd v0)))))
  unfold StartAndExtSm.finishStartSpkC at hg
  have hex : (StartAndExtSmAux.extractDrKey32E (.fst (.snd (.snd (.snd v0))))).size ≤ 95 :=
    size_extractDrKey32_v0 (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
  let Γ₃ := BV256 (ℓ := ℓ) (Pt := Pt) :: .nat ::
    liftTy (Pt := Pt) (.prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) (.opt CryptoVerification.E2E.Costed.BV256)) ::
    .prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt)) :: Γ
  have hsn := snocAtomicE_size (ℓ := ℓ) (Pt := Pt) nInst (O := atomicE2EOps ℓ P C K decT encT) (Γ := Γ₃)
    (.snd (.var (.succ (.succ (.succ .zero))))) (initKemFailSessionTrackE2EE (.var .zero))
  have htr := initKemFailSessionTrackE2EE_size (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ₃) (.var .zero)
  have hbInst : bits nInst ≤ bits b.q_total :=
    bits_mono_local (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))
  have hbSpk : bits nSpk ≤ bits b.q_total := bits_mono_local (Nat.min_le_left _ _)
  have hbOpk : bits nOpk ≤ bits b.q_total := bits_mono_local (Nat.min_le_left _ _)
  have hbSend : bits nSend ≤ bits b.q_total := bits_mono_local (Nat.min_le_left _ _)
  unfold finishStartSpkHaltedClampedC finishStartSpkHaltedClampedE liftLet1E Expr.wkTop1
    finishSpkWithPqrClampedBodyE finishStartSpkHaltedClampedSize wk1E
  simp only [v0, Γ₃, nInst, nSpk, nOpk, nSend, Comp.size, Expr.size, Expr.renameM_size, liftE2EExpr_size]
    at hg hex hsn htr hbInst hbSpk hbOpk hbSend ⊢
  omega

theorem finishStartSpkHaltedClampedC_queries (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (bmE : AExpr Γ (.opt .bool)) (σHE : AExpr Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) (acE : AExpr Γ (BV256 (ℓ := ℓ) (Pt := Pt)))
    (w : (e2eKeyIndTargetIface S ℓ Pt).Tag → ℕ) :
    (finishStartSpkHaltedClampedC b qStart bmE σHE sidE kr1E kr2E acE).queries w (fun _ => 0) = 0 := rfl

private theorem eval_finishSpkWithPqrClampedBodyE (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    (bm : Option Bool) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256)
    (hbnd : DrvMirrorBounded b.q_total (min b.q_total S.N_spk_tot) (min b.q_total S.N_opk_tot)
      (min b.q_total S.N_send_tot) b.q_total (min qStart (min b.q_total S.N_send_tot)) σ) :
    (finishSpkWithPqrClampedBodyE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) b qStart).eval
      (.cons (bm, (e2eDrvStateEnc σ, (CryptoVerification.E2E.Costed.sidV (ℓ := ℓ) sid,
        (CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr1,
          (CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr2, ac))))) .nil) =
    ((let res := bhE2EFinishStartSpk C K bm σ sid kr1 kr2 ac; (res.1, e2eDrvStateEnc res.2)),
     match kr1 with
     | .drKeyResp dk =>
       if dk.rootKey.length == 32 && dk.chainKey.length == 32 && dk.pqrKey.length == 32 then
         some (bhBytesWord dk.pqrKey) else none
     | _ => none) := by
  unfold finishSpkWithPqrClampedBodyE; dsimp only [Expr.eval]
  rw [StartAndExtSmAux.eval_finishStartSpkGenE (min qStart (min b.q_total S.N_send_tot))
    b.q_total (min b.q_total S.N_spk_tot) (min b.q_total S.N_opk_tot) (min b.q_total S.N_send_tot)
    _ _ _ _ rfl (Or.inr ⟨hbnd.insts_le, hbnd.instMeta_le, hbnd.prins_le,
      hbnd.bundles_le, hbnd.opks_le, hbnd.sends_le, hbnd.corrPrins_le⟩),
    StartAndExtSmAux.eval_extractDrKey32E]
  simp only [Expr.eval, env_get_zero, TablesHonest.sidOfV_sidV, TablesHonest.keyIndRdec_keyIndRenc]
  cases kr1 with
  | drKeyResp dk =>
    by_cases h : (dk.rootKey.length == 32 && dk.chainKey.length == 32 && dk.pqrKey.length == 32) = true <;> simp [h]
  | _ => rfl

theorem finishStartSpkHaltedClampedC_eval (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (bmE : AExpr Γ (.opt .bool)) (σHE : AExpr Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (sidE : AExpr Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : AExpr Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) (acE : AExpr Γ (BV256 (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes))
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (hσH : σHE.eval ρ = (drvEnc σH.1, σH.2.map sessHEnc)) (hsid : sidE.eval ρ = sidV sid)
    (hkr1 : kr1E.eval ρ = keyIndRenc kr1) (hkr2 : kr2E.eval ρ = keyIndRenc kr2)
    (hTracks : σH.2.length ≤ min qStart (min b.q_total S.N_send_tot))
    (hbnd : DrvMirrorBounded b.q_total (min b.q_total S.N_spk_tot) (min b.q_total S.N_opk_tot)
      (min b.q_total S.N_send_tot) b.q_total (min qStart (min b.q_total S.N_send_tot)) σH.1) :
    (finishStartSpkHaltedClampedC b qStart bmE σHE sidE kr1E kr2E acE).eval ρ =
      let res := bhE2EFinishStartSpk C K (bmE.eval ρ) σH.1 sid kr1 kr2 (acE.eval ρ)
      let tracks' := match res.1, kr1 with
        | some _, .drKeyResp dk => σH.2 ++ [initKemFailSessionTrack C.F Bytes (bhKeySOf dk (acE.eval ρ)).2.2]
        | _, _ => σH.2
      pure (res.1, (drvEnc res.2, tracks'.map sessHEnc)) := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let ρ1 := Env.cons (σHE.eval ρ) ρ
  have hren : ∀ {t : Ty (atomicSig ℓ Pt)} (e : AExpr Γ t),
      (wk1E (u := .prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))) e).eval ρ1 = e.eval ρ :=
    fun e => Expr.renameM_eval e fun _ _ => rfl
  have harg : (Expr.pair (wk1E bmE) (.pair (.fst (.var .zero))
      (.pair (wk1E sidE) (.pair (wk1E kr1E) (.pair (wk1E kr2E) (wk1E acE)))))).eval ρ1 =
      liftVal (Pt := Pt) (t := spkBodyArgTy S ℓ) (bmE.eval ρ, (e2eDrvStateEnc σH.1,
        (CryptoVerification.E2E.Costed.sidV (ℓ := ℓ) sid,
          (CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr1,
            (CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) kr2, acE.eval ρ))))) := by
    dsimp only [Expr.eval]; rw [hren, hren, hren, hren, hren]
    simp only [ρ1, env_get_zero, hσH, hsid, hkr1, hkr2]
    rw [← liftVal_e2eDrvStateEnc_eq, ← liftVal_sidV_eq, ← liftVal_keyIndRenc_eq, ← liftVal_keyIndRenc_eq]
    cases bmE.eval ρ <;> rfl
  have hlv : ∀ (a : Option ℕ) (s : BHE2EDrvState S ℓ) (k? : Option (BitVec 256)),
      liftVal (Pt := Pt) (t := .prod (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) (.opt CryptoVerification.E2E.Costed.BV256))
        ((a, e2eDrvStateEnc s), k?) = ((a, drvEnc (Pt := Pt) s), k?) := by
    intro a s k?; cases a <;> cases k? <;> exact Prod.ext (Prod.ext rfl (liftVal_e2eDrvStateEnc_eq s)) rfl
  have hlet := liftLet1E_eval (argTy := spkBodyArgTy S ℓ)
    (.pair (wk1E bmE) (.pair (.fst (.var .zero)) (.pair (wk1E sidE) (.pair (wk1E kr1E) (.pair (wk1E kr2E) (wk1E acE))))))
    (finishSpkWithPqrClampedBodyE b qStart) ρ1 _ harg
  rw [eval_finishSpkWithPqrClampedBodyE _ _ _ _ _ _ _ _ hbnd, hlv] at hlet
  dsimp only [finishStartSpkHaltedClampedC, Comp.eval]; congr 1; unfold finishStartSpkHaltedClampedE
  change (Expr.caseOpt _ _ _).eval (Env.cons ((liftLet1E (argTy := spkBodyArgTy S ℓ) _ _).eval ρ1) ρ1) = _
  rw [hlet]
  rcases hres : bhE2EFinishStartSpk C K (bmE.eval ρ) σH.1 sid kr1 kr2 (acE.eval ρ) with ⟨_ | idx, σ'⟩
  · simp only [Expr.eval, ρ1, env_get_zero, env_get_succ, hσH]
  · obtain ⟨dk, rfl, h1, h2, h3⟩ := bhE2EFinishStartSpk_some_drKey C K _ _ _ _ _ _ hres
    dsimp only [nInst] at hTracks ⊢
    simp only [h1, h2, h3, beq_self_eq_true, Bool.and_self, ↓reduceIte, Expr.eval, ρ1, env_get_zero, env_get_succ, hσH]
    have hmapLen : (List.map (sessHEnc (ℓ := ℓ) (Pt := Pt)) σH.2).length ≤ nInst := by simpa [nInst] using hTracks
    rw [snocAtomicE_eval nInst _ _ _ (by simpa only [Expr.eval, ρ1, env_get_zero, env_get_succ, hσH] using hmapLen),
      initKemFailSessionTrackE2EE_eval]
    simp only [Expr.eval, env_get_zero, env_get_succ, bhKeySOf, List.map_append, List.map_cons, List.map_nil]

@[expose] def finishKindClampedCost (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  FreshnessSim.finishKindCost (min qStart (min b.q_total S.N_send_tot)) + 10

@[expose] def finishKindClampedSize (b : SignalPqxdh.QueryBudget) : ℕ :=
  bits b.q_total + 90

@[expose] def finishKindClampedE (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (bOutE : AExpr Γ .bool) : AExpr Γ .bool :=
  finishKindE (min qStart (min b.q_total S.N_send_tot)) σE bOutE

theorem finishKindClampedE_cost (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (bOutE : AExpr Γ .bool) :
    (finishKindClampedE b qStart σE bOutE).cost ≤ σE.cost + bOutE.cost + finishKindClampedCost S b qStart := by
  rw [finishKindClampedE]
  exact finishKindE_cost (min qStart (min b.q_total S.N_send_tot)) σE bOutE

theorem finishKindClampedE_size (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (bOutE : AExpr Γ .bool) :
    (finishKindClampedE b qStart σE bOutE).size ≤ σE.size + bOutE.size + finishKindClampedSize b := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  have h := finishKindE_size (S := S) (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nInst σE bOutE
  have hbInst : bits nInst ≤ bits b.q_total :=
    bits_mono_local (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))
  rw [finishKindClampedE]
  dsimp only [finishKindClampedSize, finishKindSize, nInst] at h hbInst ⊢
  omega

theorem finishKindClampedE_eval (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : AExpr Γ (drvTy S ℓ Pt)) (bOutE : AExpr Γ .bool)
    (ρ : Env Γ) {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = drvEnc σ)
    (hInsts : σ.insts.length ≤ min qStart (min b.q_total S.N_send_tot)) :
    (finishKindClampedE b qStart σE bOutE).eval ρ = (bOutE.eval ρ == σ.b || bhE2EDrvWon σ σ.b) := by
  rw [finishKindClampedE]
  exact finishKindE_eval (min qStart (min b.q_total S.N_send_tot)) σE bOutE ρ hσ hInsts

end KindHandshakeSubprograms

end Computational.Proofs.E2E.Dsl.HaltedStartSessionSim
