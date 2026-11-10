/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FsAtomicMacrosBase -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.PubRed
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.GameHop.StateSim

/-! # `CoinSimEquiv` soundness for `compilePureTwoStageRed` -/

public section

set_option autoImplicit false

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp GameCodec CostedReduction
  handlerImpl bits iterM findML anyML mapML consumeFirstML foldML atomicSig AtomicPureOp
  AtomicSymOp atomicFsOps atomicBaseSamplers bytesToWordLE fitBytesN toLEBytes fig8PubAdOfV
  fig8PubAdT fig8PubAdV fsRecvStOfV fsRecvStT fsRecvStV fsRrDec fsRrEnc fsSendStOfV fsSendStT
  fsSendStV lctOfV lctT lctV lpubOfV lpubT lpubV salt32OfV salt32V slotAdOfV slotAdT slotAdV
  wireSaltCtOfV wireSaltCtT wireSaltCtV wireSignalHdrOfV wireSignalHdrT wireSignalHdrV)

namespace Computational.Proofs.ReductionDsl.FsAtomicMacros
open CryptoGames (Party WireAEAD MACScheme AEADScheme CipherScheme)
open CryptoGames.HMAC (toBEBytes keyToBytes32 hmacWith hmacSha256Trunc8 bytesToWord64LE hmacScheme)
open CryptoGames.HKDF (bytesToKey32 deriveMessageKeys DerivedMessageKeys)
open CryptoGames.CBC (Plain Block nBlocks cbcPkcs7EncryptOnly blockToBytesLE cbcDecRaw)
open CryptoGames.Ratchet (keyToBytesVec32 padOrTruncatePlain)
open CryptoGames.Ratchet.LibsignalInst (Salt32 LibsignalCiphertextWithSalt32
  LibsignalMsgPublicPart dummyKey lIds lHeader lWire lAeadK lAead lAeadR lPubOf lChainPRG lIdeal
  lSaltPRF32 lSaltRed lWireRed slotSaltRed slotWireRed LibsignalWireOracleSpec)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey IdentityKey MessageKeyGenerator
  ProtoSignalMessage SignalMessage SignalHeader SignalMessageProtoCodec serializeContent computeMac
  macLength aesCbcEncrypt aesCbcDecrypt currentVersion signalWireCodec maxForwardJumps)
open CryptoGames.LibsignalAead (SerializedIdentityKeys wireEncode libsignalReceiveWire
  libsignalWireAead)
open CryptoGames.SM.Construction (Header)
open CryptoGames.FSAEAD (ReceiveResult RatchetSenderState RatchetReceiverState)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarintAux decodeVarint decodeKey
  skipBytes skipScalar skipField skipGroup mergeBytes mergeUint32 mergeField decodeLoop
  emptyProtoSignalMessage decode encodeVarintAux encodeVarint encodeKey encodeBytesField
  encodeUint32Field encode protoSignalCodec)
open CryptoVerification.E2E (Bytes u8Vec toU8 ofU8 vecU8 fitVec)

section PureMacro

open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal)
open _root_.ReductionDsl (TwoStageCostedReduction Mid runFuel)
open CryptoVerification.LibsignalSession (evalTwoStage1)

theorem compilePureTwoStageRed_coinSimEquiv {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .unit .unit .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    (hOp : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.baseTy M.toDen (O₁.dom o) x) .nil) =
        toVal M.baseTy M.toDen (O₁.cod o) (O₁.eval o x))
    (hSamp : ∀ s x,
      CoinSimEquiv I₂.fwdU
        ((M.sampMacro s).eval (.cons (toVal M.baseTy M.toDen (I₁.smp.sDom s) x) .nil))
        (toVal M.baseTy M.toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s x)))
    (hQuery : ∀ g x,
      CoinSimEquiv I₂.fwdU
        ((M.queryMacro g).eval (.cons (toVal M.baseTy M.toDen (I₁.dom g) x) .nil))
        (toVal M.baseTy M.toDen (I₁.cod g) <$>
          (I₁.dec g x <$> (liftM (T.query (I₁.enc g x)) : OracleComp T _))))
    (hQenc : ∀ t : κ, C₂.qenc t = hQ ▸ toVal M.baseTy M.toDen C₁.Q (C₁.qenc t))
    (hRdec : ∀ (t : κ) (r₁ : C₁.R.denote),
      C₂.rdec t (hR ▸ toVal M.baseTy M.toDen C₁.R r₁) = C₁.rdec t r₁)
    (fuel : ℕ) (dflt : Bool)
    (A : Unit → OracleComp (unifSpec + G) Bool) (x : rIn₁.denote) :
    CoinSimEquiv I₂.fwdU
      (evalTwoStage1 (compilePureTwoStageRed C₂ M R hQ hR) fuel dflt A
        (toVal M.baseTy M.toDen rIn₁ x))
      (evalTwoStage1 (S := S₁) R fuel dflt A x) := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, cc₂⟩
  dsimp only at hQ hR; subst hQ; subst hR
  dsimp only at hQenc hRdec
  let C₂' : GameCodec S₂ G := ⟨mapTy M.baseTy C₁.Q, mapTy M.baseTy C₁.R, qenc₂, rdec₂, cc₂⟩
  let R₂' := compilePureTwoStageRed C₂' M R rfl rfl
  have hRun1 : ∀ {α : Type} (d0 : α) (oa : OracleComp (unifSpec + G) α) (f : ℕ)
      (s₁ : R.σ.denote),
      CoinSimEquiv I₂.fwdU
        (R₂'.run1 d0 oa f (toVal M.baseTy M.toDen R.σ s₁))
        (compilePureTwoStageMid C₂' M R rfl rfl <$> R.run1 d0 oa f s₁) := by
    intro α d0 oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro f s₁
      exact CoinSimEquiv.of_eq (by simp [TwoStageCostedReduction.run1, construct_pure,
        compilePureTwoStageMid])
    | query_bind q mx ih =>
      intro f s₁
      rcases q with n | t
      · simp only [TwoStageCostedReduction.run1, construct_query_bind, hFwdU n, map_bind]
        exact (CoinSimEquiv.refl (I₁.fwdU n)).bind fun u => ih u f s₁
      · cases f with
        | zero =>
          exact CoinSimEquiv.of_eq (by simp [TwoStageCostedReduction.run1, construct_query_bind,
            compilePureTwoStageMid])
        | succ f =>
          simp only [TwoStageCostedReduction.run1, construct_query_bind, map_bind]
          dsimp only [R₂', C₂', compilePureTwoStageRed, castHandlePre]
          rw [hQenc t]
          change CoinSimEquiv I₂.fwdU
            ((compilePureComp M R.handlePre).eval
              (mapPureEnv M.baseTy M.toDen (.cons s₁ (.cons (C₁.qenc t) .nil))) >>= _)
            _
          refine ((compilePureComp_coinSimEquiv M hOp hSamp hQuery R.handlePre
            (.cons s₁ (.cons (C₁.qenc t) .nil))).bind fun _ => CoinSimEquiv.refl _).trans ?_
          rw [bind_map_left]
          refine (CoinSimEquiv.refl _).bind fun res => ?_
          rcases res with ⟨v₁, s₁'⟩ | ⟨c₁, p₁, s₁'⟩
          · dsimp [toVal]
            rw [hRdec t v₁]
            exact ih (C₁.rdec t v₁) f s₁'
          · exact CoinSimEquiv.of_eq (by dsimp [toVal]; erw [map_pure]; rfl)
  have hRunFuel : ∀ {α : Type} (d0 : α) (oa : OracleComp (unifSpec + G) α) (f : ℕ)
      (s₁ : R.σ.denote),
      CoinSimEquiv I₂.fwdU
        (runFuel (C := C₂') R₂'.handlePost d0 oa f (toVal M.baseTy M.toDen R.σ s₁))
        (Prod.map id (toVal M.baseTy M.toDen R.σ) <$>
          runFuel (C := C₁) R.handlePost d0 oa f s₁) := by
    intro α d0 oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro f s₁
      exact CoinSimEquiv.of_eq (by simp [runFuel, construct_pure, Prod.map])
    | query_bind q mx ih =>
      intro f s₁
      rcases q with n | t
      · simp only [runFuel, construct_query_bind, hFwdU n, map_bind]
        exact (CoinSimEquiv.refl (I₁.fwdU n)).bind fun u => ih u f s₁
      · cases f with
        | zero =>
          exact CoinSimEquiv.of_eq (by simp [runFuel, construct_query_bind, Prod.map])
        | succ f =>
          simp only [runFuel, construct_query_bind, map_bind]
          dsimp only [R₂', C₂', compilePureTwoStageRed, castHandle]
          rw [hQenc t]
          change CoinSimEquiv I₂.fwdU
            ((compilePureComp M R.handlePost).eval
              (mapPureEnv M.baseTy M.toDen (.cons s₁ (.cons (C₁.qenc t) .nil))) >>= _)
            _
          refine ((compilePureComp_coinSimEquiv M hOp hSamp hQuery R.handlePost
            (.cons s₁ (.cons (C₁.qenc t) .nil))).bind fun _ => CoinSimEquiv.refl _).trans ?_
          rw [bind_map_left]
          refine (CoinSimEquiv.refl _).bind fun ⟨v₁, s₁'⟩ => ?_
          dsimp only [toVal]
          rw [hRdec t v₁]
          exact ih (C₁.rdec t v₁) f s₁'
  have hEval1 :
      CoinSimEquiv I₂.fwdU
        (R₂'.eval1 A (toVal M.baseTy M.toDen rIn₁ x) fuel dflt)
        (Prod.map id (compilePureTwoStageMid C₂' M R rfl rfl) <$> R.eval1 A x fuel dflt) := by
    simp only [TwoStageCostedReduction.eval1, map_bind]
    change CoinSimEquiv I₂.fwdU
      ((compilePureComp M R.init).eval (mapPureEnv M.baseTy M.toDen (.cons x .nil)) >>= _)
      _
    refine ((compilePureComp_coinSimEquiv M hOp hSamp hQuery R.init
      (.cons x .nil)).bind fun _ => CoinSimEquiv.refl _).trans ?_
    erw [bind_map_left]
    refine (CoinSimEquiv.refl _).bind fun ⟨a, s₁⟩ => ?_
    dsimp only [toVal]
    refine ((hRun1 dflt (A a) fuel s₁).bind fun _ => CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left]
    refine (CoinSimEquiv.refl _).bind fun m => ?_
    cases m with
    | done b s₁' =>
      dsimp only [compilePureTwoStageMid]
      simp only [map_bind]
      change CoinSimEquiv I₂.fwdU
        ((compilePureComp M R.chDone).eval
          (mapPureEnv M.baseTy M.toDen (.cons s₁' (.cons b .nil))) >>= _)
        _
      refine ((compilePureComp_coinSimEquiv M hOp hSamp hQuery R.chDone
        (.cons s₁' (.cons b .nil))).bind fun _ => CoinSimEquiv.refl _).trans ?_
      rw [bind_map_left]
      exact (CoinSimEquiv.refl _).bind fun c₁ =>
        CoinSimEquiv.of_eq (by simp [toVal, compilePureTwoStageMid])
    | paused t c₁ p₁ s₁' k =>
      exact CoinSimEquiv.of_eq (by simp [compilePureTwoStageMid])
  have hEval2 : ∀ m : Mid G Bool R.π.denote R.σ.denote Unit,
      CoinSimEquiv I₂.fwdU
        (R₂'.eval2 (compilePureTwoStageMid C₂' M R rfl rfl m) () fuel dflt)
        (R.eval2 m () fuel dflt) := by
    intro m
    cases m with
    | done b s₁ =>
      simp only [TwoStageCostedReduction.eval2, compilePureTwoStageMid, pure_bind]
      change CoinSimEquiv I₂.fwdU
        ((compilePureComp M R.finish).eval
          (mapPureEnv M.baseTy M.toDen (.cons s₁ (.cons b (.cons () .nil)))))
        _
      exact (compilePureComp_coinSimEquiv M hOp hSamp hQuery R.finish
        (.cons s₁ (.cons b (.cons () .nil)))).trans
        (CoinSimEquiv.of_eq (show id <$> _ = _ from id_map _))
    | paused t c₁ p₁ s₁ k =>
      simp only [TwoStageCostedReduction.eval2, compilePureTwoStageMid]
      change CoinSimEquiv I₂.fwdU
        ((compilePureComp M R.resume).eval
          (mapPureEnv M.baseTy M.toDen (.cons s₁ (.cons p₁ (.cons () .nil)))) >>= _)
        _
      refine ((compilePureComp_coinSimEquiv M hOp hSamp hQuery R.resume
        (.cons s₁ (.cons p₁ (.cons () .nil)))).bind fun _ => CoinSimEquiv.refl _).trans ?_
      erw [bind_map_left]
      refine (CoinSimEquiv.refl _).bind fun ⟨v₁, s₁'⟩ => ?_
      dsimp only [toVal]
      have hr : C₂'.rdec t (toVal M.baseTy M.toDen C₁.R v₁) = C₁.rdec t v₁ := hRdec t v₁
      rw [hr]
      refine ((hRunFuel dflt (k (C₁.rdec t v₁)) fuel s₁').bind
        fun _ => CoinSimEquiv.refl _).trans ?_
      rw [bind_map_left]
      refine (CoinSimEquiv.refl _).bind fun ⟨b, s₁''⟩ => ?_
      dsimp only [Prod.map, id]
      change CoinSimEquiv I₂.fwdU
        ((compilePureComp M R.finish).eval
          (mapPureEnv M.baseTy M.toDen (.cons s₁'' (.cons b (.cons () .nil)))))
        _
      exact (compilePureComp_coinSimEquiv M hOp hSamp hQuery R.finish
        (.cons s₁'' (.cons b (.cons () .nil)))).trans
        (CoinSimEquiv.of_eq (show id <$> _ = _ from id_map _))
  change CoinSimEquiv I₂.fwdU (evalTwoStage1 R₂' fuel dflt A (toVal M.baseTy M.toDen rIn₁ x)) _
  simp only [evalTwoStage1]
  refine (hEval1.bind fun _ => CoinSimEquiv.refl _).trans ?_
  rw [bind_map_left]
  exact (CoinSimEquiv.refl _).bind fun ⟨_, m⟩ => hEval2 m


end PureMacro

end Computational.Proofs.ReductionDsl.FsAtomicMacros
