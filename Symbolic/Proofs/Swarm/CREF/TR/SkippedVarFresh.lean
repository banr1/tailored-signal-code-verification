/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonRep
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.ALaCarte.Basic
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Symbolic.Proofs.Swarm.CREF.TR.G1.CaseSplit
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Stage1Wire
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Skipped-Key Fresh-Chain Same-Base Case

Proves `svk_rk_switch_of_seedKnown` for replacing a wire representation's ratchet key when the
message seed is attacker-known, and `skippedVar_of_fresh_dhPk` ruling out a non-colliding plain
`dhPk` representation with the same normalized X25519 base as an installed variant ratchet key.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet (RecvChain recvChainFor consumeMessageKey computeMac messageVersion)
open DY.Libsignal.Refinement (ExternCryptoLawsHold aesCbcDecryptSymbol WireFields EncodingVariation
  canonicalVariation)
open DY.Libsignal.TripleRatchet
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.RecvRep

local notation "SpqrSem" => OpaqueSymbolSemantics

unseal DY.Bytes in
private instance subDhPkSVF0 (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVariant0SVF0 (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subTrunc0SVF0 (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction concretizeTrunc (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

section Upstream

namespace G1

private theorem termShapeId_iff_termShapeId_x25519Key (pk : DY.Bytes) :
    TermShapeId pk ↔ TermShapeId (DY.X25519.normalizeX25519Key pk) := by
  unfold DY.X25519.normalizeX25519Key
  have hv := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
  cases hview : pk.view? DY.X25519.Variant.SubF with
  | none =>
    exact Iff.rfl
  | some x =>
    rw [hview] at hv
    dsimp only at hv ⊢
    rw [← hv]
    constructor
    · intro h i S g
      have h1 := h i S g
      rw [shape_variant_pack_sid] at h1
      have h2 := congrArg (fun u : DY.Bytes => u.view? DY.X25519.Variant.SubF) h1
      rw [DY.BytesView.view_pack (SubF := DY.X25519.Variant.SubF),
          DY.BytesView.view_pack (SubF := DY.X25519.Variant.SubF)] at h2
      injection h2 with hmk
      exact congrArg DY.X25519.Variant.SubF.key hmk
    · intro h i S g
      rw [shape_variant_pack_sid, h i S g]

end G1

namespace RecvDecStep.SkippedVarKnownCk

unseal DY.Bytes in
private instance subKdf0SVF0 (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem gamma_kdfExtract_svf (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (s ikm : DY.Bytes) :
    gamma i S g (KdfExtract.kdfExtract s ikm) =
      CryptoGames.HMAC.hmacWith (DY.Libsignal.Refinement.sha256CompressFunction i)
        (gamma i S g s) (gamma i S g ikm) := by
  unfold gamma gamma'
  show ((({ salt := s, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]
  rfl

private theorem length_hmac_svf (k m : DY.Bytes) :
    (DY.Libsignal.TripleRatchet.hmac k m).length = 32 := by
  simp only [DY.Libsignal.TripleRatchet.hmac, KdfExtract.kdfExtract]
  grind [Symbolic.DYBridge.DY.KdfExtract.KdfExtract.SubF.length_eq_1]

private theorem length_computeMac_svf (macKey senderIk receiverIk wire : DY.Bytes) :
    (computeMac macKey senderIk receiverIk wire).length = Trunc.trunc8Length := by
  simp [computeMac, Trunc.length_trunc8, length_hmac_svf, Trunc.trunc8Length]

abbrev SkippedVarConcl (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : SpqrSem)
    (g' : Ghost) (ms₁ : List Move) (body ptext : HwBytes) (m : SignalMessage) (st₀_src : TRState)
    (pk seed k_own : DY.Bytes) : Prop :=
  ∃ (t₁ : DY.Bytes) (msg₁ : TRSignalMsg),
    t₁ ∈ recvRepresentations interpretation r₀ S g' ms₁ body ∧
    parseTrSignalMsg t₁ = some msg₁ ∧
    msg₁.version = messageVersion ∧
    msg₁.ratchetKey = pk ∧
    msg₁.counter = UInt32.ofBitVec m.counter ∧
    body.drop (body.length - 8) =
      gamma interpretation S g' (computeMac (trMsgKeys k_own seed).macKey st₀_src.peerIk st₀_src.myIk msg₁.wire) ∧
    (seed.AttackerKnows (runTraceMoves r₀ ms₁) ∨
      Symbolic.Swarm.CREF.TR.G1.AuthenticDecryptRepB3_g1 interpretation r₀ S g' ms₁ body ptext msg₁ st₀_src seed k_own)

private theorem gamma_trunc8_svf (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (x : DY.Bytes) :
    gamma interpretation S g (Trunc.trunc8 x) = (gamma interpretation S g x).take 8 := by
  unfold Trunc.trunc8 gamma gamma'
  show ((({input := x} : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeTrunc (concretizeAll interpretation S g)]; rfl

private theorem gamma_computeMac_congr_wire_svf (interpretation : ExternInterpretation) (S : SpqrSem)
    (g : Ghost) (macKey peerIk myIk wire₁ wire₂ : DY.Bytes)
    (hw : gamma interpretation S g wire₁ = gamma interpretation S g wire₂) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.computeMac macKey peerIk myIk wire₁) =
      gamma interpretation S g (DY.Libsignal.TripleRatchet.computeMac macKey peerIk myIk wire₂) := by
  unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.hmac
  rw [gamma_trunc8_svf, gamma_trunc8_svf, gamma_kdfExtract_svf, gamma_kdfExtract_svf,
      gamma_concat, gamma_concat, gamma_concat, gamma_concat, hw]

private theorem svk_gamma_computeMac_trMsgKeys_congr_salt_tr
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (pqSalt k_own seed peerIk myIk wire : DY.Bytes)
    (hpqSalt_gam : gamma interpretation S g pqSalt = gamma interpretation S g k_own) :
    gamma interpretation S g (computeMac (trMsgKeys pqSalt seed).macKey peerIk myIk wire) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey peerIk myIk wire) := by
  obtain ⟨_, hmk_gam, _⟩ :=
    Symbolic.Swarm.CREF.TR.G1.gamma_trMsgKeys_eq_of_gamma_eq interpretation S g hpqSalt_gam
      (rfl : gamma interpretation S g seed = gamma interpretation S g seed)
  unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.hmac
  rw [gamma_trunc8_svf, gamma_trunc8_svf, gamma_kdfExtract_svf, gamma_kdfExtract_svf, hmk_gam]

private theorem exists_trWire_rep_with_pqTerm_svf
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move) (b : HwBytes)
    (parsed : SignalMessage)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    (rk_term ct_term pq_term : DY.Bytes)
    (hrk_knows : rk_term.AttackerKnows (runTraceMoves r₀ ms))
    (hct_knows : ct_term.AttackerKnows (runTraceMoves r₀ ms))
    (hpq_knows : pq_term.AttackerKnows (runTraceMoves r₀ ms))
    (hrk_gamma : gamma interpretation S g rk_term = parsed.senderRatchetKey.bytes.toList)
    (hct_gamma : gamma interpretation S g ct_term = parsed.ciphertext) :
    ∃ (v : EncodingVariation),
      let wire' := DY.TrWire.trWireMsg (UInt8.ofNat parsed.messageVersion.toNat) rk_term
        (UInt32.ofNat parsed.counter.toNat) (UInt32.ofNat parsed.previousCounter.toNat)
        ct_term pq_term v
      v ≠ canonicalVariation ∧
      wire'.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g wire' = b.take (b.length - 8) ∧
      (b.drop (b.length - 8)).length = Trunc.trunc8Length ∧
      b = gamma interpretation S g wire' ++ b.drop (b.length - 8) ∧
      ∀ (mac_term : DY.Bytes),
        mac_term.AttackerKnows (runTraceMoves r₀ ms) →
        mac_term.length = Trunc.trunc8Length →
        gamma interpretation S g mac_term = b.drop (b.length - 8) →
        spqrHeaded mac_term = false →
        let t' := Concat.concat wire' mac_term
        let msg' : TRSignalMsg :=
          { wire := wire'
            mac := mac_term
            version := UInt8.ofNat parsed.messageVersion.toNat % 16
            ratchetKey := rk_term
            counter := UInt32.ofNat parsed.counter.toNat
            ciphertext := ct_term
            pqRatchet := pq_term }
        t'.AttackerKnows (runTraceMoves r₀ ms) ∧
        gamma interpretation S g t' = b ∧
        parseTrSignalMsg t' = some msg' ∧
        msg'.version.toNat = parsed.messageVersion.toNat ∧
        msg'.ratchetKey = rk_term ∧
        msg'.counter.toNat = parsed.counter.toNat ∧
        msg'.ciphertext = ct_term ∧
        msg'.pqRatchet = pq_term ∧
        (gamma interpretation S g pq_term = parsed.pqRatchet →
          t' ∈ recvRepresentations interpretation r₀ S g ms b) := by
  obtain ⟨v, f, mac, hv_ne, hb, hmac_len, hv3, hv4, _hrk_len, hc_lt, hpc_lt,
          hver_m, hrk_m, hctr_m, hpc_m, hct_m⟩ :=
    DY.Libsignal.TripleRatchet.Refinement.trWireBytes_covered_uniform b parsed hTryFrom
  refine ⟨v, ?_⟩
  intro wire'
  have hwire'_eq : wire' = DY.TrWire.trWireMsg (UInt8.ofNat f.version) rk_term
      (UInt32.ofNat f.counter) (UInt32.ofNat f.previousCounter)
      ct_term pq_term v := by
    dsimp only [wire']
    rw [hver_m, hctr_m, hpc_m]
  have hwire_knows : wire'.AttackerKnows (runTraceMoves r₀ ms) := by
    dsimp only [wire']
    exact DY.TrWire.attacker_knows_trWireMsg _ _ _ _ _ _ _ _
      hrk_knows hct_knows hpq_knows
  have hrk_f : gamma interpretation S g rk_term = f.ratchetKey := hrk_gamma.trans hrk_m
  have hct_f : gamma interpretation S g ct_term = f.ciphertext := hct_gamma.trans hct_m
  have hv_nat : (UInt8.ofNat f.version).toNat = f.version :=
    Nat.mod_eq_of_lt (by omega : f.version < 256)
  have hc_nat : (UInt32.ofNat f.counter).toNat = f.counter :=
    Nat.mod_eq_of_lt hc_lt
  have hpc_nat : (UInt32.ofNat f.previousCounter).toNat = f.previousCounter :=
    Nat.mod_eq_of_lt hpc_lt
  have hwf_eq :
      ({ version := (UInt8.ofNat f.version).toNat
         ratchetKey := gamma interpretation S g rk_term
         counter := (UInt32.ofNat f.counter).toNat
         previousCounter := (UInt32.ofNat f.previousCounter).toNat
         ciphertext := gamma interpretation S g ct_term } : WireFields) = f := by
    cases f
    simp only [hv_nat, hc_nat, hpc_nat, hrk_f, hct_f]
  have hwire_gamma : gamma interpretation S g wire' =
      trWireBytes (g.addr wire') v f (gamma interpretation S g pq_term) := by
    rw [hwire'_eq, DY.Libsignal.Composed.Refinement.gamma_trWireMsg, hwf_eq]
  have hb_inst : b = trWireBytes (g.addr wire') v f (gamma interpretation S g pq_term) ++ mac :=
    hb (g.addr wire') (gamma interpretation S g pq_term)
  have hmacSha256Trunc8 : mac.length = 8 := hmac_len
  have htake : b.take (b.length - 8) =
      trWireBytes (g.addr wire') v f (gamma interpretation S g pq_term) := by
    rw [hb_inst, List.length_append, hmacSha256Trunc8, Nat.add_sub_cancel]
    exact List.take_left' rfl
  have hdrop : b.drop (b.length - 8) = mac := by
    rw [hb_inst, List.length_append, hmacSha256Trunc8, Nat.add_sub_cancel]
    exact List.drop_left' rfl
  have hwire_take : gamma interpretation S g wire' = b.take (b.length - 8) :=
    hwire_gamma.trans htake.symm
  have hdrop_len : (b.drop (b.length - 8)).length = Trunc.trunc8Length := by
    rw [hdrop, hmacSha256Trunc8]; rfl
  have hb_split : b = gamma interpretation S g wire' ++ b.drop (b.length - 8) := by
    rw [hwire_gamma, hdrop, ← hb_inst]
  refine ⟨hv_ne, hwire_knows, hwire_take, hdrop_len, hb_split, ?_⟩
  intro mac_term hmac_knows hmac_sym_len hmac_gamma hmac_ns t' msg'
  have ht'_knows : t'.AttackerKnows (runTraceMoves r₀ ms) :=
    Concat.attacker_knows_concat _ _ _ hwire_knows hmac_knows
  have ht'_gamma : gamma interpretation S g t' = b := by
    dsimp only [t']
    rw [gamma_concat, hmac_gamma, ← hb_split]
  have hparse : parseTrSignalMsg t' = some msg' :=
    parseTrSignalMsg_concat_trWireMsg parsed.messageVersion.toNat rk_term
      parsed.counter.toNat parsed.previousCounter.toNat
      ct_term pq_term v mac_term hmac_sym_len
  have hver_eq : msg'.version.toNat = parsed.messageVersion.toNat := by
    dsimp only [msg']
    exact u8OfNat_mod16_toNat parsed.messageVersion.toNat (by rw [hver_m]; omega)
  have hctr_eq : msg'.counter.toNat = parsed.counter.toNat := by
    dsimp only [msg']
    exact Nat.mod_eq_of_lt parsed.counter.isLt
  refine ⟨ht'_knows, ht'_gamma, hparse, hver_eq, rfl, hctr_eq, rfl, rfl, fun hpq_gamma => ?_⟩
  refine ⟨ht'_knows, ht'_gamma, by rw [hparse]; rfl, fun msg1 hmsg1 => ?_⟩
  have hmsg1 : msg1 = msg' := by rw [hparse] at hmsg1; exact (Option.some.inj hmsg1).symm
  subst hmsg1
  refine ⟨by dsimp only [msg']; exact hwire_take,
          by dsimp only [msg']; exact hmac_gamma,
          by dsimp only [msg']; exact hmac_ns,
          fun m hm_try => ?_⟩
  have hm_eq : m = parsed := by rw [hTryFrom] at hm_try; exact (Except.ok.inj hm_try).symm
  subst hm_eq
  exact ⟨hct_gamma, hrk_gamma, hpq_gamma, hctr_eq, hver_eq⟩

theorem svk_rk_switch_of_seedKnown
    (interpretation : ExternInterpretation) (_hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost)
    (ms : List Move) (b : HwBytes) (parsed : SignalMessage)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    {st : TRState} {t₀ : DY.Bytes} {msg₀ : TRSignalMsg} {pk k_own seed : DY.Bytes}
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hrkK : pk.AttackerKnows (runTraceMoves r₀ ms))
    (hSeedK : seed.AttackerKnows (runTraceMoves r₀ ms))
    (hMacBytes :
      b.drop (b.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st.peerIk st.myIk msg₀.wire))
    (hPeerK : st.peerIk.AttackerKnows (runTraceMoves r₀ ms))
    (hMyK : st.myIk.AttackerKnows (runTraceMoves r₀ ms))
    (hγ_rk : gamma interpretation S g pk = parsed.senderRatchetKey.bytes.toList) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg),
      t' ∈ recvRepresentations interpretation r₀ S g ms b ∧
      parseTrSignalMsg t' = some msg' ∧
      msg'.version = msg₀.version ∧
      msg'.ratchetKey = pk ∧
      msg'.counter = msg₀.counter ∧
      b.drop (b.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st.peerIk st.myIk msg'.wire) := by
  let tr := runTraceMoves r₀ ms
  let pqSalt := litOf (gamma interpretation S g k_own)
  have hsaltK : pqSalt.AttackerKnows tr := Literal.attacker_knows_literalToBytes _ _
  have hprk_kn : (DY.Libsignal.TripleRatchet.hmac pqSalt seed).AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hsaltK hSeedK
  have hinfo_kn : (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys").AttackerKnows tr :=
    Literal.attacker_knows_literalToBytes _ _
  have hck_kn : (trMsgKeys pqSalt seed).cipherKey.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _))
  have hmk_kn : (trMsgKeys pqSalt seed).macKey.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hck_kn
        (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _)))
  have hwire₀_kn : msg₀.wire.AttackerKnows tr := by
    have hsp := Concat.attacker_knows_split t₀ (t₀.length - Trunc.trunc8Length) tr ht₀.1
    unfold parseTrSignalMsg at hparse₀
    rcases hsplit : Concat.split t₀ (t₀.length - Trunc.trunc8Length) with _ | ⟨w₀, m₀⟩
    · rw [hsplit] at hparse₀; cases hparse₀
    · rw [hsplit] at hsp hparse₀; dsimp only [Bind.bind, Option.bind] at hparse₀
      rcases hwf : DY.TrWire.trWireMsgFields? w₀ with _ | x₀
      · rw [hwf] at hparse₀; cases hparse₀
      · rw [hwf] at hparse₀; injection hparse₀ with hmsg; subst hmsg; exact hsp.1
  obtain ⟨v₀, pc₀, ev₀, hwire₀_eq, _⟩ :=
    Symbolic.Swarm.CREF.TR.G1.parseTrSignalMsg_eq_some_inv hparse₀
  have hargs₀ := DY.TrWire.attacker_knows_trWireMsg_args v₀ msg₀.ratchetKey msg₀.counter pc₀
    msg₀.ciphertext msg₀.pqRatchet ev₀ tr (hwire₀_eq ▸ hwire₀_kn)
  obtain ⟨hwire₀_take, _hmac₀_drop, _, htry₀⟩ := ht₀.2.2.2 msg₀ hparse₀
  obtain ⟨hct₀_gam, _hrk₀_gam, hpq₀_gam, hctr₀_nat, hver₀_nat⟩ := htry₀ parsed hTryFrom
  obtain ⟨v, _, hwire'_kn, hwire'_take, _, _, hforged⟩ :=
    exists_trWire_rep_with_pqTerm_svf interpretation r₀ S g ms b parsed hTryFrom
      pk msg₀.ciphertext msg₀.pqRatchet
      hrkK hargs₀.2.1 hargs₀.2.2 hγ_rk hct₀_gam
  let wire' := DY.TrWire.trWireMsg (UInt8.ofNat parsed.messageVersion.toNat) pk
    (UInt32.ofNat parsed.counter.toNat)
    (UInt32.ofNat parsed.previousCounter.toNat)
    msg₀.ciphertext msg₀.pqRatchet v
  let mac' := computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk wire'
  have hmac'_kn : mac'.AttackerKnows tr := by
    dsimp only [mac', DY.Libsignal.TripleRatchet.computeMac, DY.Libsignal.TripleRatchet.hmac]
    exact Trunc.attacker_knows_trunc8 _ tr
      (KdfExtract.attacker_knows_kdfExtract _ _ tr hmk_kn
        (Concat.attacker_knows_concat _ _ tr hPeerK
          (Concat.attacker_knows_concat _ _ tr hMyK hwire'_kn)))
  have hmac'_len : mac'.length = Trunc.trunc8Length := length_computeMac_svf _ _ _ _
  have hmac'_gam : gamma interpretation S g mac' = b.drop (b.length - 8) := by
    dsimp only [mac']
    rw [gamma_computeMac_congr_wire_svf interpretation S g _ _ _ wire' msg₀.wire
      (hwire'_take.trans hwire₀_take.symm),
      svk_gamma_computeMac_trMsgKeys_congr_salt_tr interpretation S g pqSalt k_own seed
        st.peerIk st.myIk msg₀.wire (RecvRep.gamma_litOf _ _ _ _)]
    exact hMacBytes.symm
  have hmac'_nsh : spqrHeaded mac' = false := by
    let inner := hmac (trMsgKeys pqSalt seed).macKey (Concat.concat st.peerIk (Concat.concat st.myIk wire'))
    change spqrHeaded (({ input := inner } : DY.Trunc.Trunc8.SubF DY.Bytes).pack) = false
    unfold spqrHeaded
    rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF,
        Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendState.SubF,
        Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendKey.SubF,
        Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendMsg.SubF,
        Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.RecvState.SubF,
        Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.RecvKey.SubF,
        Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.ChainKey.SubF]
    rfl
  obtain ⟨_ht'_kn, _ht'_gam, hparse', hver', hrk', hctr', _hct', _hpq', hmem_fn⟩ :=
    hforged mac' hmac'_kn hmac'_len hmac'_gam hmac'_nsh
  have ht'_rep := hmem_fn hpq₀_gam
  have hMacBytes' :
      b.drop (b.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st.peerIk st.myIk wire') := by
    rw [gamma_computeMac_congr_wire_svf interpretation S g _ _ _ wire' msg₀.wire
      (hwire'_take.trans hwire₀_take.symm)]
    exact hMacBytes
  exact ⟨Concat.concat wire' mac', _, ht'_rep, hparse',
    UInt8.toNat_inj.mp (hver'.trans hver₀_nat.symm), hrk', UInt32.toNat_inj.mp (hctr'.trans hctr₀_nat.symm), hMacBytes'⟩

end RecvDecStep.SkippedVarKnownCk

end Upstream

namespace RecvDecStep.SkippedVarFresh

open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.CREF.TR.RecvDecStep.SkippedVarKnownCk
  (SkippedVarConcl svk_rk_switch_of_seedKnown)

private theorem gamma_dhPk_ne_nil_svf (i : ExternInterpretation)
    (hEq : ExternCryptoLawsHold i) (S : SpqrSem) (g : Ghost) (a : DY.Bytes) :
    gamma i S g (DY.DiffieHellman.dhPk a) ≠ [] := by
  have hlen : (gamma i S g (DY.DiffieHellman.dhPk a)).length = 32 := by
    unfold gamma gamma'
    rw [show DY.DiffieHellman.dhPk a = ({ sk := a } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
        DY.Bytes.rec_eq (concretizeDhPk i) (concretizeAll i S g)]
    exact hEq.x25519_public_key_length _
  intro hnil; rw [hnil] at hlen; cases hlen

private theorem not_mem_ptAtoms_of_view_random_none_svf
    (r₀ : ProtocolSetup) (ms : List Move) (u : DY.Bytes)
    (h : u.view? DY.Random.Random = none) :
    u ∉ plaintextTerms (runVis r₀ ms) ++ [] := by
  intro hp
  rw [List.append_nil] at hp
  exact not_mem_ptAtoms_of_view_random_isNone r₀ ms [] (fun _ hv => nomatch hv) u
    (Option.isNone_iff_eq_none.mpr h) (by rwa [List.append_nil])

unseal DY.Bytes in
private theorem notSpqrHeaded_dhPk_svf (a : DY.Bytes) :
    notSpqrHeaded (DY.DiffieHellman.dhPk a) := by
  change notSpqrHeaded (({ sk := a } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack)
  unfold notSpqrHeaded
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendState.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendKey.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendMsg.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.RecvState.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.RecvKey.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.ChainKey.SubF]; rfl

unseal DY.Bytes in
private theorem notOpaqueHeaded_dhPk_svf (a : DY.Bytes) :
    notOpaqueHeaded (DY.DiffieHellman.dhPk a) := by
  change notOpaqueHeaded (({ sk := a } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack)
  unfold notOpaqueHeaded
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Pk.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Encap.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.SharedSecret.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Signature.Vk.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Signature.Sign.SubF]; rfl

unseal DY.Bytes in
private theorem dhPk_not_mem_ptAtoms_svf (r₀ : ProtocolSetup) (ms : List Move) (a : DY.Bytes) :
    DY.DiffieHellman.dhPk a ∉ plaintextTerms (runVis r₀ ms) ++ [] :=
  not_mem_ptAtoms_of_view_random_none_svf r₀ ms _
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random ({ sk := a } : DY.DiffieHellman.DhPk.SubF DY.Bytes))

unseal DY.Bytes in
private theorem variant_pack_not_mem_ptAtoms_svf (r₀ : ProtocolSetup) (ms : List Move)
    (x : DY.X25519.Variant.SubF DY.Bytes) :
    x.pack ∉ plaintextTerms (runVis r₀ ms) ++ [] :=
  not_mem_ptAtoms_of_view_random_none_svf r₀ ms _
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)

/-- Rules out a non-colliding wire representation whose ratchet key is a plain `dhPk` sharing the
same normalized X25519 base as an installed variant ratchet key `pk`. -/
theorem skippedVar_of_fresh_dhPk
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (_hwf : ProtocolSetupWF r₀) (S : SpqrSem)
    (g' : Ghost) (ms₁ : List Move) (body ptext : HwBytes) (m : SignalMessage)
    (st₀_src st₁_post : TRState) (c₁ _c₀ _c₀' : RecvChain) (t₀ pk seed k_own : DY.Bytes)
    (msg₀ : TRSignalMsg) (x : DY.X25519.Variant.SubF DY.Bytes)
    (_hRun : ModelRun r₀ ms₁)
    (_hreach : (runTraceMoves r₀ ms₁).Reachable reachability)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g' ms₁ body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (_hver₀ : msg₀.version = messageVersion)
    (_hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter)
    (hNotCol : ¬RecvCollision interpretation r₀ S g' ms₁ t₀)
    (_hst₀_src : st₀_src ∈ availableStates r₀ (runTraceMoves r₀ ms₁))
    (hst₁_post : st₁_post ∈ availableStates r₀ (runTraceMoves r₀ ms₁))
    (hc₁ : c₁ ∈ st₁_post.recv) (hcpk : c₁.ratchetKey = pk)
    (hCaseA' : CaseA' pk)
    (hVar : pk.view? DY.X25519.Variant.SubF = some x)
    (_hJunk : ¬JunkTR pk)
    (hrk_ne : msg₀.ratchetKey ≠ pk)
    (_hrcf : recvChainFor st₀_src.toDRState pk = some (_c₀, true))
    (_hcons : consumeMessageKey _c₀ (UInt32.ofBitVec m.counter) = some (seed, _c₀'))
    (_hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st₀_src msg₀)
    (_hHist : RecvHistInvTR interpretation S g' r₀ ms₁)
    (_hIW : InstallWitnessTR r₀ (runTraceMoves r₀ ms₁))
    (_hrkK : pk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hγ_pk : gamma interpretation S g' pk = m.senderRatchetKey.bytes.toList)
    (_hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g' (computeMac (trMsgKeys k_own seed).macKey st₀_src.peerIk st₀_src.myIk msg₀.wire))
    (_hPeerK : st₀_src.peerIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (_hMyK : st₀_src.myIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (_hDecOk : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g' (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g' (trMsgKeys k_own seed).iv).take 16] = some ptext)
    (hbase : DY.X25519.normalizeX25519Key msg₀.ratchetKey = DY.X25519.normalizeX25519Key pk)
    (hPlain₀ : msg₀.ratchetKey.view? DY.X25519.Variant.SubF = none) :
    SkippedVarConcl interpretation r₀ S g' ms₁ body ptext m st₀_src pk seed k_own := by
  exfalso
  have hxk₀ : DY.X25519.normalizeX25519Key msg₀.ratchetKey = msg₀.ratchetKey := by
    unfold DY.X25519.normalizeX25519Key; rw [hPlain₀]
  obtain ⟨a, ha⟩ := hCaseA'.2
  have hmsg_dhPk : msg₀.ratchetKey = DY.DiffieHellman.dhPk a :=
    hxk₀.symm.trans (hbase.trans ha)
  have hsid_pk : TermShapeId pk :=
    (termShapeId_iff_termShapeId_x25519Key pk).mpr hCaseA'.1.1
  have hsid_c₁ : TermShapeId c₁.ratchetKey := hcpk ▸ hsid_pk
  have hsid_msg₀ : TermShapeId msg₀.ratchetKey :=
    (termShapeId_iff_termShapeId_x25519Key msg₀.ratchetKey).mpr (hbase.symm ▸ hCaseA'.1.1)
  have hns_msg₀ : notSpqrHeaded msg₀.ratchetKey :=
    hmsg_dhPk ▸ notSpqrHeaded_dhPk_svf a
  have hno_msg₀ : notOpaqueHeaded msg₀.ratchetKey :=
    hmsg_dhPk ▸ notOpaqueHeaded_dhPk_svf a
  have hne_nil : gamma interpretation S g' msg₀.ratchetKey ≠ [] := by
    rw [hmsg_dhPk]
    exact gamma_dhPk_ne_nil_svf interpretation hEq S g' a
  have hx₁ : (msg₀.ratchetKey, (gamma' interpretation S g' msg₀.ratchetKey).shape,
      gamma interpretation S g' msg₀.ratchetKey) ∈
      ([t₀] : List DY.Bytes).flatMap
        (fun u => (gamma' interpretation S g' u).memo) := by
    rw [List.mem_flatMap]
    exact ⟨t₀, List.mem_cons_self ..,
      parse_rk_mem_memo_tr interpretation S g' hparse₀ hne_nil hns_msg₀ hno_msg₀⟩
  have hx₂ : (c₁.ratchetKey, c₁.ratchetKey, gamma interpretation S g' c₁.ratchetKey) ∈
      (prefixTerms r₀ (runTraceMoves r₀ ms₁) (runVis r₀ ms₁)).flatMap
        (fun u => (gamma' interpretation S g' u).memo) :=
    rk_mem_prefixTerms_memo_tr interpretation S g' hst₁_post hc₁ hsid_c₁
  have hsh_ne : (gamma' interpretation S g' msg₀.ratchetKey).shape ≠ c₁.ratchetKey := by
    rw [hsid_msg₀ interpretation S g', hcpk]
    exact hrk_ne
  have hinj : assumedInjective msg₀.ratchetKey = true :=
    hmsg_dhPk ▸ assumedInjective_dhPk_tr a
  have hmsg_not_pt : msg₀.ratchetKey ∉ plaintextTerms (runVis r₀ ms₁) ++ [] :=
    hmsg_dhPk ▸ dhPk_not_mem_ptAtoms_svf r₀ ms₁ a
  have hc₁_not_pt : c₁.ratchetKey ∉ plaintextTerms (runVis r₀ ms₁) ++ [] := by
    have hp := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
    rw [hVar] at hp
    dsimp only at hp
    rw [hcpk, ← hp]
    exact variant_pack_not_mem_ptAtoms_svf r₀ ms₁ x
  obtain ⟨_, _, _, htry₀⟩ := ht₀.2.2.2 msg₀ hparse₀
  have hγ_msg₀ : gamma interpretation S g' msg₀.ratchetKey = m.senderRatchetKey.bytes.toList :=
    (htry₀ m htry).2.1
  have hγ_eq : gamma interpretation S g' msg₀.ratchetKey = gamma interpretation S g' c₁.ratchetKey := by
    rw [hγ_msg₀, hcpk, hγ_pk]
  apply hNotCol
  refine Symbolic.Swarm.CREF.Stage1Wire.recvCollision_of_memoCollisionOn_sub (ns := [t₀]) hparse₀ ?_ ?_
  · intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; subst hu
    exact List.mem_cons_self ..
  · exact ⟨_, hx₁, _, List.mem_append_left _ hx₂, hsh_ne, Or.inl hinj,
      fun h1 => False.elim (hmsg_not_pt h1),
      fun h2 => False.elim (hc₁_not_pt h2),
      hγ_eq⟩

end RecvDecStep.SkippedVarFresh

end Symbolic.Swarm.CREF.TR
