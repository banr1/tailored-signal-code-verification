/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Bytes.AttackerKnowledge
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Honest Wire Representation Upgrade and DH Public-Key Shape Inversion

Defines `recvSeed` and `AuthenticDecryptRep`, proves `g1b_honest_send_branch_core` upgrading a
matched honest-send MAC shape to an `AuthenticDecryptRep` witness, and proves `ShapeId` closure and
`eq_dhPk_randTerm32_of_shape_eq`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace DY.Libsignal.Composed.Refinement

open DY.Libsignal.TripleRatchet in
def recvSeed (st : TRState) (msg : TRSignalMsg) : Option DY.Bytes :=
  if msg.version = messageVersion then
    match recvChainFor st.toDRState msg.ratchetKey with
    | none => none
    | some (c, _) => (consumeMessageKey c msg.counter).map (·.1)
  else none

end DY.Libsignal.Composed.Refinement

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg trMsgKeys trHonestWireMsg)

open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (consumeMessageKey computeMac hmac hkdfBlock1 hkdfBlock2 hkdfBlock3
  lit messageVersion)
open DY.Libsignal.Refinement (ExternCryptoLawsHold aesCbcDecryptSymbol)
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.RecvRep (gamma_concat)
open Symbolic.Swarm.CREF.TR.RecvDecStep (shape_kdfExtract_tr shape_concat_tr)

unseal DY.Bytes in
private instance subKdf0WSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subConcat0WSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeConcat (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSym0WSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSym i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, symFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhPkWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subTrunc0WSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeTrunc (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem kdfExtract_injective {s₁ i₁ s₂ i₂ : DY.Bytes}
    (h : KdfExtract.kdfExtract s₁ i₁ = KdfExtract.kdfExtract s₂ i₂) : s₁ = s₂ ∧ i₁ = i₂ := by
  have h1 := congrArg (fun x => x.view? DY.KdfExtract.KdfExtract.SubF) h
  change Bytes.view? (({ salt := s₁, ikm := i₁ } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack)
      DY.KdfExtract.KdfExtract.SubF =
    Bytes.view? (({ salt := s₂, ikm := i₂ } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack)
      DY.KdfExtract.KdfExtract.SubF at h1
  rw [BytesView.view_pack, BytesView.view_pack, Option.some.injEq] at h1
  cases h1
  exact ⟨rfl, rfl⟩

theorem shape_hmac_inj (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {k₁ m₁ k₂ m₂ : DY.Bytes}
    (h : (gamma' i S g (hmac k₁ m₁)).shape = (gamma' i S g (hmac k₂ m₂)).shape) :
    (gamma' i S g k₁).shape = (gamma' i S g k₂).shape ∧
    (gamma' i S g m₁).shape = (gamma' i S g m₂).shape := by
  unfold hmac at h
  rw [shape_kdfExtract_tr, shape_kdfExtract_tr] at h
  exact kdfExtract_injective h

theorem shape_trMsgKeys_macKey_inj (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {pqSalt₁ seed₁ pqSalt₂ seed₂ : DY.Bytes}
    (h : (gamma' i S g (trMsgKeys pqSalt₁ seed₁).macKey).shape =
         (gamma' i S g (trMsgKeys pqSalt₂ seed₂).macKey).shape) :
    (gamma' i S g pqSalt₁).shape = (gamma' i S g pqSalt₂).shape ∧
    (gamma' i S g seed₁).shape = (gamma' i S g seed₂).shape := by
  dsimp only [trMsgKeys, hkdfBlock2] at h
  exact shape_hmac_inj i S g (shape_hmac_inj i S g h).1

theorem shape_inp_honest_inj (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {pqSalt₁ seed₁ myIk₁ peerIk₁ wire₁ pqSalt₂ seed₂ myIk₂ peerIk₂ wire₂ : DY.Bytes}
    (h : (gamma' i S g (hmac (trMsgKeys pqSalt₁ seed₁).macKey
            (Concat.concat myIk₁ (Concat.concat peerIk₁ wire₁)))).shape =
         (gamma' i S g (hmac (trMsgKeys pqSalt₂ seed₂).macKey
            (Concat.concat myIk₂ (Concat.concat peerIk₂ wire₂)))).shape) :
    (gamma' i S g pqSalt₁).shape = (gamma' i S g pqSalt₂).shape ∧
    (gamma' i S g seed₁).shape = (gamma' i S g seed₂).shape ∧
    (gamma' i S g myIk₁).shape = (gamma' i S g myIk₂).shape ∧
    (gamma' i S g peerIk₁).shape = (gamma' i S g peerIk₂).shape ∧
    (gamma' i S g wire₁).shape = (gamma' i S g wire₂).shape := by
  obtain ⟨hmackey, hcat1⟩ := shape_hmac_inj i S g h
  obtain ⟨hpq, hseed⟩ := shape_trMsgKeys_macKey_inj i S g hmackey
  repeat rw [shape_concat_tr] at hcat1
  obtain ⟨hmy, hcat2⟩ := concat_injective hcat1
  obtain ⟨hpeer, hwire⟩ := concat_injective hcat2
  exact ⟨hpq, hseed, hmy, hpeer, hwire⟩

theorem gamma_kdfExtract_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (s ikm : DY.Bytes) :
    gamma i S g (KdfExtract.kdfExtract s ikm) =
      CryptoGames.HMAC.hmacWith (DY.Libsignal.Refinement.sha256CompressFunction i)
        (gamma i S g s) (gamma i S g ikm) := by
  unfold gamma gamma'
  show ((({ salt := s, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]
  rfl

theorem gamma_hmac_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (k m : DY.Bytes) :
    gamma i S g (hmac k m) =
      CryptoGames.HMAC.hmacWith (DY.Libsignal.Refinement.sha256CompressFunction i)
        (gamma i S g k) (gamma i S g m) :=
  gamma_kdfExtract_tr i S g k m

theorem gamma_hkdfBlock1_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (info : DY.Bytes) {prk₁ prk₂ : DY.Bytes} (hprk : gamma i S g prk₁ = gamma i S g prk₂) :
    gamma i S g (hkdfBlock1 prk₁ info) = gamma i S g (hkdfBlock1 prk₂ info) := by
  dsimp only [hkdfBlock1]
  rw [gamma_hmac_tr, gamma_hmac_tr, hprk]

theorem gamma_hkdfBlock2_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (info : DY.Bytes) {prk₁ prk₂ : DY.Bytes} (hprk : gamma i S g prk₁ = gamma i S g prk₂) :
    gamma i S g (hkdfBlock2 prk₁ info) = gamma i S g (hkdfBlock2 prk₂ info) := by
  dsimp only [hkdfBlock2]
  rw [gamma_hmac_tr, gamma_hmac_tr,
      gamma_concat i S g (hkdfBlock1 prk₁ info),
      gamma_concat i S g (hkdfBlock1 prk₂ info),
      hprk, gamma_hkdfBlock1_eq i S g info hprk]

theorem gamma_hkdfBlock3_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (info : DY.Bytes) {prk₁ prk₂ : DY.Bytes} (hprk : gamma i S g prk₁ = gamma i S g prk₂) :
    gamma i S g (hkdfBlock3 prk₁ info) = gamma i S g (hkdfBlock3 prk₂ info) := by
  dsimp only [hkdfBlock3]
  rw [gamma_hmac_tr, gamma_hmac_tr,
      gamma_concat i S g (hkdfBlock2 prk₁ info),
      gamma_concat i S g (hkdfBlock2 prk₂ info),
      hprk, gamma_hkdfBlock2_eq i S g info hprk]

theorem gamma_trMsgKeys_eq_of_gamma_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {pqSalt₁ seed₁ pqSalt₂ seed₂ : DY.Bytes}
    (hpq : gamma i S g pqSalt₁ = gamma i S g pqSalt₂)
    (hseed : gamma i S g seed₁ = gamma i S g seed₂) :
    gamma i S g (trMsgKeys pqSalt₁ seed₁).cipherKey = gamma i S g (trMsgKeys pqSalt₂ seed₂).cipherKey ∧
    gamma i S g (trMsgKeys pqSalt₁ seed₁).macKey = gamma i S g (trMsgKeys pqSalt₂ seed₂).macKey ∧
    gamma i S g (trMsgKeys pqSalt₁ seed₁).iv = gamma i S g (trMsgKeys pqSalt₂ seed₂).iv := by
  have hprk : gamma i S g (hmac pqSalt₁ seed₁) = gamma i S g (hmac pqSalt₂ seed₂) := by
    rw [gamma_hmac_tr, gamma_hmac_tr, hpq, hseed]
  exact ⟨gamma_hkdfBlock1_eq i S g _ hprk,
         gamma_hkdfBlock2_eq i S g _ hprk,
         gamma_hkdfBlock3_eq i S g _ hprk⟩

theorem gamma_symEnc_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (k iv m : DY.Bytes) :
    gamma i S g (SymEnc.symEnc k iv m) =
      (i DY.Libsignal.Refinement.aesCbcEncryptSymbol
        [gamma i S g m, gamma i S g k, (gamma i S g iv).take 16]).getD [] := by
  unfold gamma gamma'
  show ((({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSym i) (concretizeAll i S g)]
  rfl

theorem gamma_m_eq_ptext_of_decOk
    (i : ExternInterpretation) (hEq : ExternCryptoLawsHold i)
    (S : OpaqueSymbolSemantics) (g : Ghost)
    {pqSalt_s seed_s m_s k_own mkSeed : DY.Bytes} {ctBytes ptext : HwBytes}
    (hpq : gamma i S g pqSalt_s = gamma i S g k_own)
    (hseed : gamma i S g seed_s = gamma i S g mkSeed)
    (hct : gamma i S g (SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey
            (trMsgKeys pqSalt_s seed_s).iv m_s) = ctBytes)
    (hDecOk : i aesCbcDecryptSymbol
      [ctBytes,
       gamma i S g (trMsgKeys k_own mkSeed).cipherKey,
       (gamma i S g (trMsgKeys k_own mkSeed).iv).take 16] = some ptext) :
    gamma i S g m_s = ptext := by
  obtain ⟨hck, _, hiv⟩ := gamma_trMsgKeys_eq_of_gamma_eq i S g hpq hseed
  rw [← hct, gamma_symEnc_tr, hck, hiv,
      hEq.aes_cbc_decrypt_inverts_encrypt (gamma i S g m_s)
        (gamma i S g (trMsgKeys k_own mkSeed).cipherKey)
        ((gamma i S g (trMsgKeys k_own mkSeed).iv).take 16)] at hDecOk
  exact Option.some.inj hDecOk

unseal DY.Bytes in
private instance subLit0WSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem shape_literalToBytes (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (b : ByteArray) :
    (gamma' i S g (Literal.literalToBytes b)).shape = Literal.literalToBytes b := by
  unfold gamma'
  show ((({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll i S g)]
  rfl

theorem version_eq_messageVersion_of_recvSeed {st₀ : TRState} {msg₀ : TRSignalMsg} {mkSeed : DY.Bytes}
    (hseed : recvSeed st₀ msg₀ = some mkSeed) :
    msg₀.version = messageVersion := by
  unfold recvSeed at hseed
  split at hseed
  · assumption
  · contradiction

theorem length_hmac_tr (k m : DY.Bytes) :
    (hmac k m).length = 32 := by
  simp only [hmac, KdfExtract.kdfExtract]
  grind [Symbolic.DYBridge.DY.KdfExtract.KdfExtract.SubF.length_eq_1]

theorem length_computeMac_tr (macKey senderIk receiverIk wire : DY.Bytes) :
    (computeMac macKey senderIk receiverIk wire).length = Trunc.trunc8Length := by
  simp [computeMac, Trunc.length_trunc8, length_hmac_tr, Trunc.trunc8Length]

theorem parseTrSignalMsg_trHonestWireMsg_computeMac
    (rk_s : DY.Bytes) (ns_s pn_s : UInt32) (ct_s pqMsg_s macKey myIk peerIk : DY.Bytes) :
    let wire_s := trHonestWireMsg rk_s ns_s pn_s ct_s pqMsg_s
    let mac_s := computeMac macKey myIk peerIk wire_s
    parseTrSignalMsg (Concat.concat wire_s mac_s) =
      some { wire := wire_s
             mac := mac_s
             version := messageVersion
             ratchetKey := rk_s
             counter := ns_s
             ciphertext := ct_s
             pqRatchet := pqMsg_s } := by
  intro wire_s mac_s
  unfold parseTrSignalMsg
  have hmac_len : mac_s.length = Trunc.trunc8Length :=
    length_computeMac_tr macKey myIk peerIk wire_s
  have hlen : (Concat.concat wire_s mac_s).length - Trunc.trunc8Length = wire_s.length := by
    rw [Concat.length_concat, hmac_len]; omega
  rw [hlen, Concat.split_concat]
  dsimp only [wire_s, trHonestWireMsg]
  simp only [Bind.bind, Pure.pure, Option.bind_some, DY.TrWire.trWireMsgFields?_trWireMsg]
  rfl

theorem parseTrSignalMsg_eq_some_inv {t₀ : DY.Bytes} {msg₀ : TRSignalMsg}
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) :
    ∃ (v₀ : UInt8) (pc₀ : UInt32) (ev₀ : DY.TrWire.EncodingVariation),
      msg₀.wire = DY.TrWire.trWireMsg v₀ msg₀.ratchetKey msg₀.counter pc₀ msg₀.ciphertext msg₀.pqRatchet ev₀ ∧
      msg₀.version = v₀ % 16 := by
  unfold parseTrSignalMsg at hparse₀
  cases hsp : Concat.split t₀ (t₀.length - Trunc.trunc8Length) with
  | none => rw [hsp] at hparse₀; cases hparse₀
  | some wm =>
    rcases wm with ⟨wire, mac⟩
    rw [hsp] at hparse₀
    dsimp only [Bind.bind, Option.bind] at hparse₀
    have hv := DY.Bytes.pack_view? DY.TrWire.TrWireMsg.SubF wire
    cases hwf : DY.TrWire.trWireMsgFields? wire with
    | none => rw [hwf] at hparse₀; cases hparse₀
    | some x =>
      rw [hwf] at hparse₀
      dsimp only [Pure.pure] at hparse₀
      have hview : wire.view? DY.TrWire.TrWireMsg.SubF = some x := hwf
      rw [hview] at hv
      dsimp only at hv
      injection hparse₀ with hmsg
      subst hmsg
      exact ⟨x.version, x.previousCounter, x.encodingVariation, hv.symm, rfl⟩

/-- Authentic decrypt representation `(t', msg', ptTerm, pqSalt)` witnessing MAC verification and
ciphertext decryption under `trMsgKeys pqSalt mkSeed`. -/
def AuthenticDecryptRep
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (b ptext : HwBytes) (msg₀ : TRSignalMsg) (st₀ : TRState)
    (mkSeed k_own : DY.Bytes) : Prop :=
  ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (ptTerm pqSalt : DY.Bytes),
    t' ∈ recvRepresentations interpretation r₀ S g ms b ∧
    t'.AttackerKnows (runTraceMoves r₀ ms) ∧
    pqSalt.AttackerKnows (runTraceMoves r₀ ms) ∧
    gamma interpretation S g pqSalt = gamma interpretation S g k_own ∧
    gamma interpretation S g t' = b ∧
    parseTrSignalMsg t' = some msg' ∧
    msg'.version = msg₀.version ∧
    msg'.ratchetKey = msg₀.ratchetKey ∧
    msg'.counter = msg₀.counter ∧
    gamma interpretation S g msg'.pqRatchet = gamma interpretation S g msg₀.pqRatchet ∧
    msg'.mac = computeMac (trMsgKeys pqSalt mkSeed).macKey st₀.peerIk st₀.myIk msg'.wire ∧
    DY.SymEnc.symDec (trMsgKeys pqSalt mkSeed).cipherKey (trMsgKeys pqSalt mkSeed).iv msg'.ciphertext =
      some ptTerm ∧
    gamma interpretation S g ptTerm = ptext

theorem g1b_honest_send_branch_core
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (b ptext : HwBytes) (parsed : SignalMessage)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (st₀ : TRState)
    (mkSeed : DY.Bytes) (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (k_own : DY.Bytes)
    (hDecOk : interpretation aesCbcDecryptSymbol
      [parsed.ciphertext,
       gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own mkSeed).iv).take 16] = some ptext)
    (salt₁ pqSalt_s seed_s myIk_s peerIk_s a_s m_s pqMsg_s : DY.Bytes) (ns_s pn_s : UInt32)
    (hsalt_gamma : gamma interpretation S g salt₁ = gamma interpretation S g k_own)
    (hmac_eq : msg₀.mac =
      computeMac (trMsgKeys pqSalt_s seed_s).macKey myIk_s peerIk_s
        (trHonestWireMsg (dhPk a_s) ns_s pn_s
          (SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey (trMsgKeys pqSalt_s seed_s).iv m_s)
          pqMsg_s))
    (hsh_inp :
      (gamma' interpretation S g
        (hmac (trMsgKeys pqSalt_s seed_s).macKey
          (Concat.concat myIk_s (Concat.concat peerIk_s
            (trHonestWireMsg (dhPk a_s) ns_s pn_s
              (SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey (trMsgKeys pqSalt_s seed_s).iv m_s)
              pqMsg_s))))).shape =
      (gamma' interpretation S g
        (hmac (trMsgKeys salt₁ mkSeed).macKey
          (Concat.concat st₀.peerIk (Concat.concat st₀.myIk msg₀.wire)))).shape)
    (hpqSalt_kn : pqSalt_s.AttackerKnows (runTraceMoves r₀ ms))
    (ht'_kn :
      (Concat.concat
        (trHonestWireMsg (dhPk a_s) ns_s pn_s
          (SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey (trMsgKeys pqSalt_s seed_s).iv m_s)
          pqMsg_s)
        msg₀.mac).AttackerKnows (runTraceMoves r₀ ms))
    (hrk_eq : dhPk a_s = msg₀.ratchetKey)
    (hseed_eq : seed_s = mkSeed)
    (hmyIk_eq : myIk_s = st₀.peerIk)
    (hpeerIk_eq : peerIk_s = st₀.myIk) :
    AuthenticDecryptRep interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed k_own := by
  let ct_s := SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey (trMsgKeys pqSalt_s seed_s).iv m_s
  let wire_s := trHonestWireMsg (dhPk a_s) ns_s pn_s ct_s pqMsg_s
  let t' := Concat.concat wire_s msg₀.mac
  let msg' : TRSignalMsg :=
    { wire := wire_s
      mac := msg₀.mac
      version := messageVersion
      ratchetKey := dhPk a_s
      counter := ns_s
      ciphertext := ct_s
      pqRatchet := pqMsg_s }
  obtain ⟨hpq_sh, hseed_sh, _, _, hwire_sh⟩ :=
    shape_inp_honest_inj interpretation S g hsh_inp
  have hpq_gamma : gamma interpretation S g pqSalt_s = gamma interpretation S g k_own :=
    (gamma_eq_of_shape_eq interpretation S g pqSalt_s salt₁ hpq_sh).trans hsalt_gamma
  have hseed_gamma : gamma interpretation S g seed_s = gamma interpretation S g mkSeed :=
    gamma_eq_of_shape_eq interpretation S g seed_s mkSeed hseed_sh
  have hwire_gamma_eq : gamma interpretation S g wire_s = gamma interpretation S g msg₀.wire :=
    gamma_eq_of_shape_eq interpretation S g wire_s msg₀.wire hwire_sh
  obtain ⟨v₀, pc₀, ev₀, hwire₀_eq, _⟩ :=
    parseTrSignalMsg_eq_some_inv hparse₀
  have hwire_sh' :
      (gamma' interpretation S g
        (DY.TrWire.trWireMsg messageVersion (dhPk a_s) ns_s pn_s
          ct_s pqMsg_s DY.TrWire.canonicalVariation)).shape =
      (gamma' interpretation S g
        (DY.TrWire.trWireMsg v₀ msg₀.ratchetKey msg₀.counter pc₀ msg₀.ciphertext msg₀.pqRatchet ev₀)).shape := by
    rw [← hwire₀_eq]
    exact hwire_sh
  obtain ⟨_, _, hsh_rk, hctr_eq, _, hsh_ct, hsh_pq, _⟩ :=
    trWire_shape_eq_imp_addr_eq interpretation interpretation S S g g
      messageVersion (dhPk a_s) ns_s pn_s ct_s pqMsg_s DY.TrWire.canonicalVariation
      v₀ msg₀.ratchetKey msg₀.counter pc₀ msg₀.ciphertext msg₀.pqRatchet ev₀
      hwire_sh'
  have hver_eq : messageVersion = msg₀.version :=
    (version_eq_messageVersion_of_recvSeed hseed).symm
  have hct_gamma_eq : gamma interpretation S g ct_s = gamma interpretation S g msg₀.ciphertext :=
    gamma_eq_of_shape_eq interpretation S g ct_s msg₀.ciphertext hsh_ct
  have hpqMsg_gamma_eq : gamma interpretation S g pqMsg_s = gamma interpretation S g msg₀.pqRatchet :=
    gamma_eq_of_shape_eq interpretation S g pqMsg_s msg₀.pqRatchet hsh_pq
  have hrk_gamma_eq : gamma interpretation S g (dhPk a_s) = gamma interpretation S g msg₀.ratchetKey :=
    gamma_eq_of_shape_eq interpretation S g (dhPk a_s) msg₀.ratchetKey hsh_rk
  obtain ⟨_, _, _, hmsg₀_prop⟩ := ht₀
  obtain ⟨hwire₀_take, hmac₀_drop, hmac₀_ns, htry₀⟩ := hmsg₀_prop msg₀ hparse₀
  have hwire_take : gamma interpretation S g wire_s = b.take (b.length - 8) :=
    hwire_gamma_eq.trans hwire₀_take
  have ht'_gamma : gamma interpretation S g t' = b := by
    dsimp only [t']
    rw [gamma_concat, hwire_take, hmac₀_drop, List.take_append_drop]
  have hparse' : parseTrSignalMsg t' = some msg' := by
    dsimp only [t', msg']
    rw [hmac_eq]
    exact parseTrSignalMsg_trHonestWireMsg_computeMac (dhPk a_s) ns_s pn_s ct_s pqMsg_s
      (trMsgKeys pqSalt_s seed_s).macKey myIk_s peerIk_s
  have ht'_mem : t' ∈ recvRepresentations interpretation r₀ S g ms b := by
    refine ⟨ht'_kn, ht'_gamma, by rw [hparse']; rfl, fun msg hmsg => ?_⟩
    rw [hparse'] at hmsg
    injection hmsg with hmsg_eq
    subst hmsg_eq
    refine ⟨hwire_take, hmac₀_drop, hmac₀_ns, fun m hm => ?_⟩
    obtain ⟨hct_m, hrk_m, hpq_m, hctr_m, hver_m⟩ := htry₀ m hm
    refine ⟨hct_gamma_eq.trans hct_m,
            hrk_gamma_eq.trans hrk_m,
            hpqMsg_gamma_eq.trans hpq_m,
            by dsimp only [msg']; rw [hctr_eq, hctr_m],
            by dsimp only [msg']; rw [hver_eq, hver_m]⟩
  obtain ⟨hct₀_parsed, _, _, _, _⟩ := htry₀ parsed hTryFrom
  have hct_parsed : gamma interpretation S g ct_s = parsed.ciphertext :=
    hct_gamma_eq.trans hct₀_parsed
  have hm_ptext : gamma interpretation S g m_s = ptext :=
    gamma_m_eq_ptext_of_decOk interpretation hEq S g hpq_gamma hseed_gamma hct_parsed hDecOk
  refine ⟨t', msg', m_s, pqSalt_s, ht'_mem, ht'_kn, hpqSalt_kn, hpq_gamma, ht'_gamma, hparse',
    hver_eq, hrk_eq, hctr_eq, hpqMsg_gamma_eq, ?_, ?_, hm_ptext⟩
  · dsimp only [msg']
    rw [← hseed_eq, ← hmyIk_eq, ← hpeerIk_eq]
    exact hmac_eq
  · dsimp only [msg', ct_s]
    rw [← hseed_eq]
    exact DY.SymEnc.symDec_symEnc _ _ _

/-! ## Shape-Identity (`ShapeId`) and `dhPk (randTerm t 32)` Shape Inversion -/

unseal DY.Bytes in
private instance subRandomWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDh i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVariant0WSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrInitWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrInit S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrSendStateWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendState S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrSendKeyWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrSendMsgWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendMsg S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrRecvStateWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrRecvState S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrRecvKeyWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrRecvKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrChainKeyWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrChainKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subTrWire0WSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemPkWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemEncapWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemEncap i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemSSWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemSS i S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemRejWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemRej S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVkWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVk S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSignWSI (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSign S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

/-- A term `u` whose `.shape` under `gamma'` is identically `u` (holds for all pure DR terms). -/
def ShapeId (u : DY.Bytes) : Prop :=
  ∀ (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost), (gamma' i S g u).shape = u

theorem eq_of_shape_eq_of_shapeId {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {u₁ u₂ : DY.Bytes} (h₁ : ShapeId u₁) (h₂ : ShapeId u₂)
    (hsh : (gamma' i S g u₁).shape = (gamma' i S g u₂).shape) :
    u₁ = u₂ := by
  rw [h₁ i S g, h₂ i S g] at hsh
  exact hsh

theorem shape_randTerm_of_ne_zero (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (t n : Nat) (hn : n ≠ 0) :
    (gamma' i S g (randTerm t n)).shape = randTerm t n := by
  unfold gamma' randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g)]
  dsimp only [concretizeRandom]
  simp [hn]
  rfl

theorem shape_dhPk_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sk : DY.Bytes) :
    (gamma' i S g (dhPk sk)).shape = dhPk (gamma' i S g sk).shape := by
  unfold gamma'
  show ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape = _
  rw [DY.Bytes.rec_eq (concretizeDhPk i) (concretizeAll i S g)]
  rfl

theorem shapeId_literalToBytes (b : ByteArray) : ShapeId (Literal.literalToBytes b) :=
  fun i S g => shape_literalToBytes i S g b

theorem shapeId_randTerm32 (t : Nat) : ShapeId (randTerm t 32) :=
  fun i S g => shape_randTerm_of_ne_zero i S g t 32 (by decide)

theorem shapeId_concat {l r : DY.Bytes} (hl : ShapeId l) (hr : ShapeId r) :
    ShapeId (Concat.concat l r) := by
  intro i S g
  rw [shape_concat_tr, hl i S g, hr i S g]

theorem shapeId_dhPk {sk : DY.Bytes} (hsk : ShapeId sk) : ShapeId (dhPk sk) := by
  intro i S g
  rw [shape_dhPk_tr, hsk i S g]

private theorem wsi_container_pack_inj_sub
    (f g : Type → Type)
    [DY.ALaCarte.FunctorSizeOf f] [DY.ALaCarte.FunctorSizeOf g]
    [DY.ALaCarte.SubFunctorTC f g] [DY.ALaCarte.Representable g]
    (x : f (DY.ALaCarte.ContainerFor g)) :
    DY.ALaCarte.Container.pack g (DY.ALaCarte.SubFunctorTC.inj (g := g) x) =
      DY.ALaCarte.Container.pack f x := by
  have hv := DY.ALaCarte.Container.pack_view g (DY.ALaCarte.Container.pack f x)
  rw [Symbolic.DYBridge.DY.ALaCarte.Container.view_pack_cross f g x] at hv
  exact hv

private theorem wsi_lift_partialFunDep
    {f g : Type → Type} [DY.ALaCarte.FunctorSizeOf f] [DY.ALaCarte.FunctorSizeOf g]
    [DY.ALaCarte.SubFunctorTC f g] [DY.ALaCarte.Representable g]
    {motive : DY.ALaCarte.ContainerFor g → Prop}
    (h : DY.ALaCarte.Container.PartialFunDep f (g := g) motive)
    (x : f (DY.ALaCarte.ContainerFor g))
    (rec : ∀ y : DY.ALaCarte.ContainerFor g,
      sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf (DY.ALaCarte.SubFunctorTC.inj (g := g) x) → motive y) :
    motive (DY.ALaCarte.Container.pack g (DY.ALaCarte.SubFunctorTC.inj (g := g) x)) := by
  rw [wsi_container_pack_inj_sub f g x]
  exact h x fun y hy => rec y (DY.ALaCarte.SubFunctorTC.sizeOf_inj (g := g) x ▸ hy)

unseal DY.Bytes in
private theorem partialFunDep_not_dhPk
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sh_sk : DY.Bytes)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hg : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      DY.Bytes.view? (gF x rec).shape DY.DiffieHellman.DhPk.SubF = none) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        DY.Bytes.view? (gamma' i S g u).shape DY.DiffieHellman.DhPk.SubF =
          some { sk := sh_sk } →
        ∃ sk : DY.Bytes, u = dhPk sk ∧ (gamma' i S g sk).shape = sh_sk) := by
  intro x _ hview
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview
  change DY.Bytes.view? ((BytesView.pack x).rec (concretizeAll i S g)).shape DY.DiffieHellman.DhPk.SubF = _ at hview
  rw [DY.Bytes.rec_eq gF (concretizeAll i S g) x, hg x _] at hview
  contradiction

unseal DY.Bytes in
private theorem partialFunDep_dhPk
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sh_sk : DY.Bytes) :
    DY.ALaCarte.Container.PartialFunDep DY.DiffieHellman.DhPk.SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        DY.Bytes.view? (gamma' i S g u).shape DY.DiffieHellman.DhPk.SubF =
          some { sk := sh_sk } →
        ∃ sk : DY.Bytes, u = dhPk sk ∧ (gamma' i S g sk).shape = sh_sk) := by
  intro x _ hview
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview ⊢
  change DY.Bytes.view? ((BytesView.pack x).rec (concretizeAll i S g)).shape DY.DiffieHellman.DhPk.SubF = _ at hview
  rw [DY.Bytes.rec_eq (concretizeDhPk i) (concretizeAll i S g) x] at hview
  dsimp only [concretizeDhPk, node] at hview
  rw [DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF)] at hview
  injection hview with h1
  injection h1 with h2
  exact ⟨x.sk, rfl, h2⟩

unseal DY.Bytes in
theorem view?_dhPk_shape_eq_some_inv
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (u : DY.Bytes) (sh_sk : DY.Bytes)
    (h : DY.Bytes.view? (gamma' i S g u).shape DY.DiffieHellman.DhPk.SubF = some { sk := sh_sk }) :
    ∃ sk : DY.Bytes, u = dhPk sk ∧ (gamma' i S g sk).shape = sh_sk := by
  refine DY.ALaCarte.Container.rec (f := DY.BytesF)
    (motive := fun u : DY.Bytes =>
      DY.Bytes.view? (gamma' i S g u).shape DY.DiffieHellman.DhPk.SubF =
        some { sk := sh_sk } →
      ∃ sk : DY.Bytes, u = dhPk sk ∧ (gamma' i S g sk).shape = sh_sk) ?_ u h
  rintro ⟨⟨id, hid⟩, val⟩ rec
  match id with
  | 0 =>
    exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeRandom g)
      (fun _ _ => by dsimp only [concretizeRandom]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) val rec
  | 1 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk concretizeLit (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | 2 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk concretizeConcat (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | 3 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_dhPk i S g sh_sk) v rec
    | 1 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeDh i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 2 => omega
  | 4 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeKdf i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | 5 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeSym i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | 6 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk concretizeTrunc (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | 7 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeVariant i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | 8 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeKemPk S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 1 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeKemEncap i) (fun _ _ => by dsimp only [concretizeKemEncap]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 2 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeKemSS i S) (fun _ _ => by dsimp only [concretizeKemSS]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 3 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeKemRej S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 4 => omega
  | 9 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeVk S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 1 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeSign S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 2 => omega
  | 10 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeSpqrInit S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 1 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeSpqrSendState S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 2 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeSpqrSendKey S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 3 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeSpqrSendMsg S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 4 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeSpqrRecvState S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 5 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeSpqrRecvKey S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 6 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeSpqrChainKey S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 7 => omega
  | 11 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_dhPk i S g sh_sk (concretizeTrWire g) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | n + 12 => omega

unseal DY.Bytes in
private theorem partialFunDep_not_random
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (t : Nat)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hg : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      DY.Bytes.view? (gF x rec).shape DY.Random.Random = none) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        DY.Bytes.view? (gamma' i S g u).shape DY.Random.Random =
          some { timestamp := t, size := 32 } →
        u = randTerm t 32) := by
  intro x _ hview
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview
  change DY.Bytes.view? ((BytesView.pack x).rec (concretizeAll i S g)).shape DY.Random.Random = _ at hview
  rw [DY.Bytes.rec_eq gF (concretizeAll i S g) x, hg x _] at hview
  contradiction

unseal DY.Bytes in
private theorem partialFunDep_random
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (t : Nat) :
    DY.ALaCarte.Container.PartialFunDep DY.Random.Random (g := DY.BytesF)
      (fun u : DY.Bytes =>
        DY.Bytes.view? (gamma' i S g u).shape DY.Random.Random =
          some { timestamp := t, size := 32 } →
        u = randTerm t 32) := by
  intro (x : DY.Random.Random DY.Bytes) _ hview
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview ⊢
  change DY.Bytes.view? ((BytesView.pack x).rec (concretizeAll i S g)).shape DY.Random.Random = _ at hview
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g) x] at hview
  dsimp only [concretizeRandom] at hview
  split at hview
  · dsimp only [litOf, Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes] at hview
    rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random] at hview
    contradiction
  · dsimp only [node] at hview
    rw [DY.BytesView.view_pack (SubF := DY.Random.Random)] at hview
    injection hview with h1
    cases x
    injection h1 with ht hs
    subst ht hs
    rfl

unseal DY.Bytes in
theorem view?_random32_shape_eq_some_inv
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (u : DY.Bytes) (t : Nat)
    (h : DY.Bytes.view? (gamma' i S g u).shape DY.Random.Random = some { timestamp := t, size := 32 }) :
    u = randTerm t 32 := by
  refine DY.ALaCarte.Container.rec (f := DY.BytesF)
    (motive := fun u : DY.Bytes =>
      DY.Bytes.view? (gamma' i S g u).shape DY.Random.Random =
        some { timestamp := t, size := 32 } →
      u = randTerm t 32) ?_ u h
  rintro ⟨⟨id, hid⟩, val⟩ rec
  match id with
  | 0 => exact wsi_lift_partialFunDep (partialFunDep_random i S g t) val rec

  | 1 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t concretizeLit (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | 2 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t concretizeConcat (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | 3 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeDhPk i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 1 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeDh i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 2 => omega
  | 4 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeKdf i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | 5 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeSym i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | 6 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t concretizeTrunc (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | 7 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeVariant i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | 8 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeKemPk S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 1 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeKemEncap i) (fun _ _ => by dsimp only [concretizeKemEncap]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 2 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeKemSS i S) (fun _ _ => by dsimp only [concretizeKemSS]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 3 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeKemRej S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 4 => omega
  | 9 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeVk S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 1 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeSign S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 2 => omega
  | 10 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeSpqrInit S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 1 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeSpqrSendState S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 2 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeSpqrSendKey S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 3 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeSpqrSendMsg S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 4 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeSpqrRecvState S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 5 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeSpqrRecvKey S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | 6 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeSpqrChainKey S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 7 => omega
  | 11 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact wsi_lift_partialFunDep (partialFunDep_not_random i S g t (concretizeTrWire g) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
    | n + 1 => omega
  | n + 12 => omega

/-- For any `u : DY.Bytes`, if `(gamma' i S g (dhPk (randTerm t 32))).shape = (gamma' i S g u).shape`,
then `dhPk (randTerm t 32) = u`. -/
theorem eq_dhPk_randTerm32_of_shape_eq
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (t : Nat) {u : DY.Bytes}
    (hsh : (gamma' i S g (dhPk (randTerm t 32))).shape = (gamma' i S g u).shape) :
    dhPk (randTerm t 32) = u := by
  rw [shape_dhPk_tr, shape_randTerm_of_ne_zero i S g t 32 (by decide)] at hsh
  have hv : DY.Bytes.view? (gamma' i S g u).shape DY.DiffieHellman.DhPk.SubF =
      some { sk := randTerm t 32 } := by
    rw [← hsh]
    exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := randTerm t 32 }
  obtain ⟨sk, rfl, hsk⟩ := view?_dhPk_shape_eq_some_inv i S g u (randTerm t 32) hv
  have hv_sk : DY.Bytes.view? (gamma' i S g sk).shape DY.Random.Random =
      some { timestamp := t, size := 32 } := by
    rw [hsk]
    exact DY.BytesView.view_pack (SubF := DY.Random.Random) { timestamp := t, size := 32 }
  rw [view?_random32_shape_eq_some_inv i S g sk t hv_sk]

end Symbolic.Swarm.CREF.TR.G1
