/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.SrHonestVer
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.EquationalTheory.KdfExtract
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.Spqr
public import Symbolic.Proofs.Swarm.CREF.TR.SpqrSemDef
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Honest `SendMsg` Extraction and Forged Wire Representation

Constructs non-canonical `trWireMsg` representations parameterized by an arbitrary
symbolic `pq_term` and extracts honest `DY.Spqr.SendMsg` terms under `PqFromHonest`
for forged decrypt steps.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (computeMac messageVersion)
open DY.Libsignal.Refinement (EncodingVariation canonicalVariation)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.LibsignalProtoCodec
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.RecvRep hiding gamma_trWireMsg gamma_litOf
open Symbolic.Swarm.CREF.TR.G1 (gamma_kdfExtract_tr)

namespace RecvDecStep

/-- For any valid wire body `b` and terms `rk_term`, `ct_term`, `pq_term` with matching
`gamma` on `ratchetKey` and `ciphertext`, there exists a non-canonical encoding variation `v`
whose `trWireMsg` evaluates to `b.take (b.length - 8)` independently of `pq_term`. -/
theorem exists_trWire_rep_with_pqTerm
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
  have hv_toNat : (UInt8.ofNat f.version).toNat = f.version :=
    Nat.mod_eq_of_lt (by omega)
  have hc_toNat : (UInt32.ofNat f.counter).toNat = f.counter :=
    Nat.mod_eq_of_lt hc_lt
  have hpc_toNat : (UInt32.ofNat f.previousCounter).toNat = f.previousCounter :=
    Nat.mod_eq_of_lt hpc_lt
  have hwire_gamma : gamma interpretation S g wire' =
      trWireBytes (g.addr wire') v f (gamma interpretation S g pq_term) := by
    rw [hwire'_eq, gamma_trWireMsg, hrk_f, hct_f, hv_toNat, hc_toNat, hpc_toNat]
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
      parsed.counter.toNat parsed.previousCounter.toNat ct_term pq_term v
      mac_term hmac_sym_len
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

unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction concretizeTrunc (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_trunc8_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (x : DY.Bytes) :
    gamma interpretation S g (Trunc.trunc8 x) = (gamma interpretation S g x).take 8 := by
  unfold Trunc.trunc8 gamma gamma'
  show ((({input := x} : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeTrunc (concretizeAll interpretation S g)]; rfl

theorem gamma_computeMac_congr_wire (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (macKey peerIk myIk wire₁ wire₂ : DY.Bytes)
    (hw : gamma interpretation S g wire₁ = gamma interpretation S g wire₂) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.computeMac macKey peerIk myIk wire₁) =
      gamma interpretation S g (DY.Libsignal.TripleRatchet.computeMac macKey peerIk myIk wire₂) := by
  unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.hmac
  rw [gamma_trunc8_tr, gamma_trunc8_tr, gamma_kdfExtract_tr, gamma_kdfExtract_tr,
      gamma_concat, gamma_concat, gamma_concat, gamma_concat, hw]

theorem length_hmac_tr (k m : DY.Bytes) :
    (DY.Libsignal.TripleRatchet.hmac k m).length = 32 := by
  simp only [DY.Libsignal.TripleRatchet.hmac, KdfExtract.kdfExtract]
  grind [Symbolic.DYBridge.DY.KdfExtract.KdfExtract.SubF.length_eq_1]

theorem length_computeMac_tr (macKey senderIk receiverIk wire : DY.Bytes) :
    (DY.Libsignal.TripleRatchet.computeMac macKey senderIk receiverIk wire).length = Trunc.trunc8Length := by
  simp [DY.Libsignal.TripleRatchet.computeMac, Trunc.length_trunc8, length_hmac_tr, Trunc.trunc8Length]

theorem attackerKnows_computeMac_tr (tr : ExecTrace)
    (macKey peerIk myIk wire : DY.Bytes)
    (hmk : macKey.AttackerKnows tr) (hpeer : peerIk.AttackerKnows tr)
    (hmy : myIk.AttackerKnows tr) (hw : wire.AttackerKnows tr) :
    (DY.Libsignal.TripleRatchet.computeMac macKey peerIk myIk wire).AttackerKnows tr :=
  Trunc.attacker_knows_trunc8 _ tr (KdfExtract.attacker_knows_kdfExtract _ _ tr hmk
    (Concat.attacker_knows_concat _ _ tr hpeer (Concat.attacker_knows_concat _ _ tr hmy hw)))

/-- Given attacker-known message keys, identity keys, and an honest `SendMsg` term matching
`parsed.pqRatchet`, constructs a representation `t' ∈ recvRepresentations` whose parsed
`pqRatchet` field satisfies `spqrEmptyMsg msg'.pqRatchet = false`. -/
theorem exists_forged_decrypt_rep_with_sendMsg
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move) (b ptext : HwBytes)
    (parsed : SignalMessage)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    (rk_term pqSalt mkSeed peerIk myIk st_s coins_s : DY.Bytes)
    (hrk_knows : rk_term.AttackerKnows (runTraceMoves r₀ ms))
    (hrk_gamma : gamma interpretation S g rk_term = parsed.senderRatchetKey.bytes.toList)
    (hck_knows : (trMsgKeys pqSalt mkSeed).cipherKey.AttackerKnows (runTraceMoves r₀ ms))
    (hiv_knows : (trMsgKeys pqSalt mkSeed).iv.AttackerKnows (runTraceMoves r₀ ms))
    (hmk_knows : (trMsgKeys pqSalt mkSeed).macKey.AttackerKnows (runTraceMoves r₀ ms))
    (hpeer_knows : peerIk.AttackerKnows (runTraceMoves r₀ ms))
    (hmy_knows : myIk.AttackerKnows (runTraceMoves r₀ ms))
    (hpq_knows : (({ st := st_s, coins := coins_s } : DY.Spqr.SendMsg.SubF DY.Bytes).pack).AttackerKnows
      (runTraceMoves r₀ ms))
    (hpq_gamma : gamma interpretation S g
      (({ st := st_s, coins := coins_s } : DY.Spqr.SendMsg.SubF DY.Bytes).pack) = parsed.pqRatchet)
    (hct_gamma : gamma interpretation S g
      (DY.SymEnc.symEnc (trMsgKeys pqSalt mkSeed).cipherKey (trMsgKeys pqSalt mkSeed).iv (litOf ptext)) =
      parsed.ciphertext)
    (hmac_gamma : ∀ wire' : DY.Bytes,
      gamma interpretation S g wire' = b.take (b.length - 8) →
      gamma interpretation S g (DY.Libsignal.TripleRatchet.computeMac (trMsgKeys pqSalt mkSeed).macKey peerIk myIk wire') =
        b.drop (b.length - 8)) :
    let pq_honest := (({ st := st_s, coins := coins_s } : DY.Spqr.SendMsg.SubF DY.Bytes).pack)
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (ptTerm : DY.Bytes),
      t' ∈ recvRepresentations interpretation r₀ S g ms b ∧
      t'.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g t' = b ∧
      parseTrSignalMsg t' = some msg' ∧
      msg'.version.toNat = parsed.messageVersion.toNat ∧
      msg'.ratchetKey = rk_term ∧
      msg'.counter.toNat = parsed.counter.toNat ∧
      msg'.pqRatchet = pq_honest ∧
      DY.Spqr.spqrEmptyMsg msg'.pqRatchet = false ∧
      msg'.mac = DY.Libsignal.TripleRatchet.computeMac (trMsgKeys pqSalt mkSeed).macKey peerIk myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt mkSeed).cipherKey (trMsgKeys pqSalt mkSeed).iv msg'.ciphertext =
        some ptTerm ∧
      gamma interpretation S g ptTerm = ptext := by
  intro pq_honest
  let ptTerm := litOf ptext
  let ct' := DY.SymEnc.symEnc (trMsgKeys pqSalt mkSeed).cipherKey (trMsgKeys pqSalt mkSeed).iv ptTerm
  have hct'_knows : ct'.AttackerKnows (runTraceMoves r₀ ms) :=
    DY.SymEnc.attacker_knows_symEnc _ _ _ (runTraceMoves r₀ ms) hck_knows hiv_knows (knows_litOf ptext _)
  obtain ⟨v, hv_ne, hwire_knows, hwire_take, _hdrop_len, _hb_split, hforged⟩ :=
    exists_trWire_rep_with_pqTerm interpretation r₀ S g ms b parsed hTryFrom
      rk_term ct' pq_honest hrk_knows hct'_knows hpq_knows hrk_gamma hct_gamma
  let wire' := DY.TrWire.trWireMsg (UInt8.ofNat parsed.messageVersion.toNat) rk_term
    (UInt32.ofNat parsed.counter.toNat) (UInt32.ofNat parsed.previousCounter.toNat)
    ct' pq_honest v
  let mac' := DY.Libsignal.TripleRatchet.computeMac (trMsgKeys pqSalt mkSeed).macKey peerIk myIk wire'
  have hmac'_knows : mac'.AttackerKnows (runTraceMoves r₀ ms) :=
    attackerKnows_computeMac_tr (runTraceMoves r₀ ms) _ _ _ _ hmk_knows hpeer_knows hmy_knows hwire_knows
  have hmac'_len : mac'.length = Trunc.trunc8Length := length_computeMac_tr _ _ _ _
  have hmac'_gamma : gamma interpretation S g mac' = b.drop (b.length - 8) := hmac_gamma wire' hwire_take
  have hmac'_nospqr : spqrHeaded mac' = false := by
    let mac_in := DY.Libsignal.TripleRatchet.hmac (trMsgKeys pqSalt mkSeed).macKey (Concat.concat peerIk (Concat.concat myIk wire'))
    have hmac'_eq : mac' = (({ input := mac_in } : DY.Trunc.Trunc8.SubF DY.Bytes).pack) := rfl
    unfold spqrHeaded
    rw [hmac'_eq,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _]
    rfl
  obtain ⟨ht'_knows, ht'_gamma, hparse', hver', hrk', hctr', hct', hpq', hmem_fn⟩ :=
    hforged mac' hmac'_knows hmac'_len hmac'_gamma hmac'_nospqr
  have hmem : Concat.concat wire' mac' ∈ recvRepresentations interpretation r₀ S g ms b := hmem_fn hpq_gamma
  refine ⟨Concat.concat wire' mac', _, ptTerm, hmem, ht'_knows, ht'_gamma, hparse',
    hver', hrk', hctr', hpq', ?_, rfl, ?_, gamma_litOf interpretation S g ptext⟩
  · rw [hpq']
    have hlit := DY.Literal.literalToBytes_bytesToLiteral pq_honest
    unfold DY.Spqr.spqrEmptyMsg
    rcases hbl : DY.Literal.bytesToLiteral pq_honest with _ | b_lit
    · rfl
    · rw [hbl] at hlit
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hlit)
  · rw [hct']; exact DY.SymEnc.symDec_symEnc _ _ _

theorem exists_honest_sendMsg_of_pqFromHonest
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (b : HwBytes) (parsed : SignalMessage) {who : List Participant}
    (hmp : MatchedPrefix interpretation r₀ S who g ms acc)
    (hfit : SrHonestVer.SendsFit acc)
    (hHon : PqFromHonest (sentBodies acc) b)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed) :
    ∃ (st_s coins_s : DY.Bytes),
      (({ st := st_s, coins := coins_s } : DY.Spqr.SendMsg.SubF DY.Bytes).pack).AttackerKnows
        (runTraceMoves r₀ ms) ∧
      gamma interpretation S g
        (({ st := st_s, coins := coins_s } : DY.Spqr.SendMsg.SubF DY.Bytes).pack) =
        parsed.pqRatchet :=
  SrHonestVer.exists_honest_sendMsg_of_pqFromHonest
    interpretation r₀ S g ms acc b parsed hmp hfit hHon hTryFrom

end RecvDecStep

end Symbolic.Swarm.CREF.CliPure.TR
