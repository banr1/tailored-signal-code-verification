/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FsAtomicMacrosBase -- proof-setup: allow-public-import
import Mathlib.Tactic.Linarith

/-! # Cost, size, and query bounds for `compilePureTwoStageRed` -/

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
open _root_.ReductionDsl (TwoStageCostedReduction)

theorem compilePureTwoStageRed_totalCost_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .unit .unit .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (opC : O₁.Op → ℕ) (sC : I₁.smp.Samp → ℕ) (qC : I₁.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).cost + 1 ≤ opC o)
    (hSamp : ∀ s, (M.sampMacro s).cost + 2 ≤ sC s)
    (hQuery : ∀ g, (M.queryMacro g).cost + 2 ≤ qC g) (q : ℕ) :
    (compilePureTwoStageRed C₂ M R hQ hR).totalCost q ≤
      compCostBound opC sC qC R.init +
      q * max I₂.uCost
        (max (compCostBound opC sC qC R.handlePre) (compCostBound opC sC qC R.handlePost) +
          C₂.codecCost) +
      max (compCostBound opC sC qC R.chDone) (compCostBound opC sC qC R.resume) +
      compCostBound opC sC qC R.finish := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, cc₂⟩
  dsimp only at hQ hR; subst hQ; subst hR
  have hi := compilePureComp_cost_le M opC sC qC hOp hSamp hQuery R.init
  have hpre := compilePureComp_cost_le M opC sC qC hOp hSamp hQuery R.handlePre
  have hpost := compilePureComp_cost_le M opC sC qC hOp hSamp hQuery R.handlePost
  have hch := compilePureComp_cost_le M opC sC qC hOp hSamp hQuery R.chDone
  have hres := compilePureComp_cost_le M opC sC qC hOp hSamp hQuery R.resume
  have hf := compilePureComp_cost_le M opC sC qC hOp hSamp hQuery R.finish
  have hmaxH : max I₂.uCost
      (max (compilePureComp M R.handlePre).cost (compilePureComp M R.handlePost).cost + cc₂) ≤
      max I₂.uCost
        (max (compCostBound opC sC qC R.handlePre) (compCostBound opC sC qC R.handlePost) + cc₂) :=
    max_le_max le_rfl (Nat.add_le_add_right (max_le_max hpre hpost) cc₂)
  have hmul := Nat.mul_le_mul_left q hmaxH
  have hmaxC := max_le_max hch hres
  dsimp only [TwoStageCostedReduction.totalCost, compilePureTwoStageRed, castHandlePre, castResume,
    castHandle]
  omega

theorem compilePureTwoStageRed_totalCost_le_UB {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .unit .unit .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (opC : O₁.Op → ℕ) (sC : I₁.smp.Samp → ℕ) (qC : I₁.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).cost + 1 ≤ opC o)
    (hSamp : ∀ s, (M.sampMacro s).cost + 2 ≤ sC s)
    (hQuery : ∀ g, (M.queryMacro g).cost + 2 ≤ qC g)
    {cInit cHandlePre cHandlePost cChDone cResume cFin : ℕ}
    (hi : compCostBound opC sC qC R.init ≤ cInit)
    (hpre : compCostBound opC sC qC R.handlePre ≤ cHandlePre)
    (hpost : compCostBound opC sC qC R.handlePost ≤ cHandlePost)
    (hch : compCostBound opC sC qC R.chDone ≤ cChDone)
    (hres : compCostBound opC sC qC R.resume ≤ cResume)
    (hf : compCostBound opC sC qC R.finish ≤ cFin) (q : ℕ) :
    (compilePureTwoStageRed C₂ M R hQ hR).totalCost q ≤
      cInit + q * max I₂.uCost (max cHandlePre cHandlePost + C₂.codecCost) +
        max cChDone cResume + cFin := by
  have h0 := compilePureTwoStageRed_totalCost_le C₂ M R hQ hR opC sC qC hOp hSamp hQuery q
  have hmaxH : max I₂.uCost
      (max (compCostBound opC sC qC R.handlePre) (compCostBound opC sC qC R.handlePost) +
        C₂.codecCost) ≤
      max I₂.uCost (max cHandlePre cHandlePost + C₂.codecCost) :=
    max_le_max le_rfl (Nat.add_le_add_right (max_le_max hpre hpost) C₂.codecCost)
  have hmul := Nat.mul_le_mul_left q hmaxH
  have hmaxC := max_le_max hch hres
  omega

theorem compilePureTwoStageRed_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .unit .unit .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (S_max : ℕ) (hS : 1 ≤ S_max)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ S_max)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ S_max)
    (hQuery : ∀ g, (M.queryMacro g).size + 2 ≤ S_max) :
    (compilePureTwoStageRed C₂ M R hQ hR).size ≤ S_max * R.size := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, cc₂⟩
  dsimp only at hQ hR; subst hQ; subst hR
  have hi := compilePureComp_size_le M S_max hS hOp hSamp hQuery R.init
  have hpre := compilePureComp_size_le M S_max hS hOp hSamp hQuery R.handlePre
  have hch := compilePureComp_size_le M S_max hS hOp hSamp hQuery R.chDone
  have hres := compilePureComp_size_le M S_max hS hOp hSamp hQuery R.resume
  have hpost := compilePureComp_size_le M S_max hS hOp hSamp hQuery R.handlePost
  have hf := compilePureComp_size_le M S_max hS hOp hSamp hQuery R.finish
  dsimp only [TwoStageCostedReduction.size, compilePureTwoStageRed, castHandlePre, castResume,
    castHandle]
  nlinarith


theorem compilePureTwoStageRed_size_le_nodes {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .unit .unit .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (S_max : ℕ)
    (hOp : ∀ o, (M.opMacro o).size ≤ S_max)
    (hSamp : ∀ s, (M.sampMacro s).size + 1 ≤ S_max)
    (hQuery : ∀ g, (M.queryMacro g).size + 1 ≤ S_max) :
    (compilePureTwoStageRed C₂ M R hQ hR).size ≤ R.size + S_max * R.nodes := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, cc₂⟩
  dsimp only at hQ hR; subst hQ; subst hR
  have hi := compilePureComp_size_le_nodes M S_max hOp hSamp hQuery R.init
  have hpre := compilePureComp_size_le_nodes M S_max hOp hSamp hQuery R.handlePre
  have hch := compilePureComp_size_le_nodes M S_max hOp hSamp hQuery R.chDone
  have hres := compilePureComp_size_le_nodes M S_max hOp hSamp hQuery R.resume
  have hpost := compilePureComp_size_le_nodes M S_max hOp hSamp hQuery R.handlePost
  have hf := compilePureComp_size_le_nodes M S_max hOp hSamp hQuery R.finish
  dsimp only [TwoStageCostedReduction.size, TwoStageCostedReduction.nodes, compilePureTwoStageRed,
    castHandlePre, castResume, castHandle]
  nlinarith

theorem compilePureTwoStageRed_totalQueries_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .unit .unit .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hSamp : ∀ s, (M.sampMacro s).queries w₂ ws₂ ≤ ws₁ s)
    (hQuery : ∀ g, (M.queryMacro g).queries w₂ ws₂ ≤ w₁ g) (q : ℕ) :
    (compilePureTwoStageRed C₂ M R hQ hR).totalQueries w₂ ws₂ q ≤
      R.totalQueries w₁ ws₁ q := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, cc₂⟩
  dsimp only at hQ hR; subst hQ; subst hR
  have hi := compilePureComp_queries_le M w₁ ws₁ w₂ ws₂ hSamp hQuery R.init
  have hpre := compilePureComp_queries_le M w₁ ws₁ w₂ ws₂ hSamp hQuery R.handlePre
  have hpost := compilePureComp_queries_le M w₁ ws₁ w₂ ws₂ hSamp hQuery R.handlePost
  have hch := compilePureComp_queries_le M w₁ ws₁ w₂ ws₂ hSamp hQuery R.chDone
  have hres := compilePureComp_queries_le M w₁ ws₁ w₂ ws₂ hSamp hQuery R.resume
  have hf := compilePureComp_queries_le M w₁ ws₁ w₂ ws₂ hSamp hQuery R.finish
  have hmul := Nat.mul_le_mul_left q (max_le_max hpre hpost)
  have hmaxC := max_le_max hch hres
  dsimp only [TwoStageCostedReduction.totalQueries, compilePureTwoStageRed, castHandlePre,
    castResume, castHandle]
  omega


end PureMacro

end Computational.Proofs.ReductionDsl.FsAtomicMacros
