/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpine
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTRStrong
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkInvCons
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr

/-!
# Honest-Send Branch of MAC Inversion

Proves `g1b_honest_send_branch_strong`: under `HonestSkelUniq` and `AvailableIkShapeId`, if
`msg₀.mac = Trunc.trunc8 inp₀` is attacker-known and `inp₀` matches the receiver's `hmac` shape
under an honest salt agreeing with `k_own`, then either `inp₀` is attacker-known or `t₀` is an
`AuthenticDecryptRep`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg trMsgKeys trHonestWireMsg)

open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (computeMac hmac kdfCk messageVersion)
open DY.Libsignal.Refinement (ExternCryptoLawsHold aesCbcDecryptSymbol)
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoProofLib.Refinement (ExternInterpretation)

/-- Strengthened `trunc8` inversion on a reachable composed run: an attacker-known `trunc8 inp₀`
either has `inp₀` attacker-known or arises from an honest send by an available state `st_s` with
fresh 32-byte ratchet secret `a` and attacker-known PQ salt and wire message. -/
theorem macKdfSafe_c_trunc8_inv_strong (r₀ : ProtocolSetup) (ms : List Move) (inp₀ : DY.Bytes)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hknows : (Trunc.trunc8 inp₀).AttackerKnows (runTraceMoves r₀ ms)) :
    inp₀.AttackerKnows (runTraceMoves r₀ ms) ∨
    ∃ (pqSalt seed myIk peerIk a : DY.Bytes) (ns pn : UInt32) (m pqMsg : DY.Bytes)
      (t_s : Nat) (st_s : TRState),
      inp₀ = hmac (trMsgKeys pqSalt seed).macKey
        (Concat.concat myIk (Concat.concat peerIk
          (trHonestWireMsg (dhPk a) ns pn
            (SymEnc.symEnc (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv m) pqMsg))) ∧
      pqSalt.AttackerKnows (runTraceMoves r₀ ms) ∧
      (Concat.concat
        (trHonestWireMsg (dhPk a) ns pn
          (SymEnc.symEnc (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv m) pqMsg)
        (Trunc.trunc8 inp₀)).AttackerKnows (runTraceMoves r₀ ms) ∧
      a = randTerm t_s 32 ∧
      st_s ∈ availableStates r₀ (runTraceMoves r₀ ms) ∧
      st_s.myIk = myIk ∧
      st_s.peerIk = peerIk ∧
      (kdfCk st_s.cks).2 = seed :=
  macKdfSafe_tr_trunc8_inv_strong r₀ ms inp₀ hreach hknows

/-- Shape-equal sending and receiving seeds of available states are equal whenever a received
ratchet key opening a fresh chain satisfies `ShapeId`. -/
abbrev HonestSkelUniq (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) : Prop :=
  Spine.HonestSkelUniqRk interpretation r₀ S g ms

/-- Identity keys of all available states satisfy `ShapeId`. -/
def AvailableIkShapeId (r₀ : ProtocolSetup) (ms : List Move) : Prop :=
  ∀ st ∈ availableStates r₀ (runTraceMoves r₀ ms), ShapeId st.myIk ∧ ShapeId st.peerIk

/-- If `msg₀.mac = trunc8 inp₀` with `trunc8 inp₀` attacker-known and `inp₀` shape-matching the
receiver's `hmac` under an honest salt `salt₁` whose key triple on `mkSeed` agrees with `k_own`,
then either `inp₀` is attacker-known or `AuthenticDecryptRep` holds. -/
theorem g1b_honest_send_branch_strong
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (b ptext : HwBytes) (parsed : SignalMessage)
    (hSkel : HonestSkelUniq interpretation r₀ S g ms)
    (hIk : AvailableIkShapeId r₀ ms)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (st₀ : TRState) (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (mkSeed : DY.Bytes) (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (k_own : DY.Bytes)
    (hDecOk : interpretation aesCbcDecryptSymbol
      [parsed.ciphertext,
       gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own mkSeed).iv).take 16] = some ptext)
    (salt₁ inp₀ : DY.Bytes)
    (hsalt_gamma : gamma interpretation S g salt₁ = gamma interpretation S g k_own)
    (hmac_eq : msg₀.mac = Trunc.trunc8 inp₀)
    (htrunc_ak : (Trunc.trunc8 inp₀).AttackerKnows (runTraceMoves r₀ ms))
    (hsh_inp : (gamma' interpretation S g inp₀).shape =
      (gamma' interpretation S g
        (hmac (trMsgKeys salt₁ mkSeed).macKey
          (Concat.concat st₀.peerIk (Concat.concat st₀.myIk msg₀.wire)))).shape) :
    inp₀.AttackerKnows (runTraceMoves r₀ ms) ∨
    AuthenticDecryptRep interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed k_own := by
  rcases macKdfSafe_c_trunc8_inv_strong r₀ ms inp₀ hreach htrunc_ak with
    hinp_ak | ⟨pqSalt', seed', myIk', peerIk', a', ns', pn', m', pqMsg', t_s, st_s,
      hinp_eq, hpq_ak, ht'_ak, ha_eq, hst_s, hmyIk_s, hpeerIk_s, hseed_s⟩
  · exact Or.inl hinp_ak
  · right
    have hmac_eq' : msg₀.mac =
        computeMac (trMsgKeys pqSalt' seed').macKey myIk' peerIk'
          (trHonestWireMsg (dhPk a') ns' pn'
            (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
            pqMsg') := by
      unfold computeMac
      rw [← hinp_eq]
      exact hmac_eq
    have hsh_inp' :
        (gamma' interpretation S g
          (hmac (trMsgKeys pqSalt' seed').macKey
            (Concat.concat myIk' (Concat.concat peerIk'
              (trHonestWireMsg (dhPk a') ns' pn'
                (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
                pqMsg'))))).shape =
        (gamma' interpretation S g
          (hmac (trMsgKeys salt₁ mkSeed).macKey
            (Concat.concat st₀.peerIk (Concat.concat st₀.myIk msg₀.wire)))).shape := by
      rw [← hinp_eq]
      exact hsh_inp
    have ht'_kn' :
        (Concat.concat
          (trHonestWireMsg (dhPk a') ns' pn'
            (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
            pqMsg')
          msg₀.mac).AttackerKnows (runTraceMoves r₀ ms) := by
      rw [hmac_eq]
      exact ht'_ak
    obtain ⟨_, hseed_sh, hmyIk_sh, hpeerIk_sh, hwire_sh⟩ :=
      shape_inp_honest_inj interpretation S g hsh_inp'
    obtain ⟨v₀, pc₀, ev₀, hwire₀_eq, _⟩ :=
      parseTrSignalMsg_eq_some_inv hparse₀
    have hwire_sh' :
        (gamma' interpretation S g
          (DY.TrWire.trWireMsg messageVersion (dhPk a') ns' pn'
            (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
            pqMsg' DY.TrWire.canonicalVariation)).shape =
        (gamma' interpretation S g
          (DY.TrWire.trWireMsg v₀ msg₀.ratchetKey msg₀.counter pc₀ msg₀.ciphertext msg₀.pqRatchet ev₀)).shape := by
      rw [← hwire₀_eq]
      exact hwire_sh
    obtain ⟨_, _, hrk_sh, _, _, _, _, _⟩ :=
      trWire_shape_eq_imp_addr_eq interpretation interpretation S S g g
        messageVersion (dhPk a') ns' pn'
        (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
        pqMsg' DY.TrWire.canonicalVariation
        v₀ msg₀.ratchetKey msg₀.counter pc₀ msg₀.ciphertext msg₀.pqRatchet ev₀
        hwire_sh'
    have hrk_eq : dhPk a' = msg₀.ratchetKey := by
      rw [ha_eq] at hrk_sh ⊢
      exact eq_dhPk_randTerm32_of_shape_eq interpretation S g t_s hrk_sh
    have hrk_sid : ShapeId msg₀.ratchetKey := by
      rw [← hrk_eq, ha_eq]
      exact shapeId_dhPk_randTerm32 t_s
    have hseed_eq : seed' = mkSeed := by
      rw [← hseed_s] at hseed_sh ⊢
      exact hSkel st_s hst_s st₀ hst₀ msg₀ mkSeed (fun _ => hrk_sid) hseed hseed_sh
    have hmyIk_eq : myIk' = st₀.peerIk := by
      rw [← hmyIk_s] at hmyIk_sh ⊢
      exact eq_of_shape_eq_of_shapeId (hIk st_s hst_s).1 (hIk st₀ hst₀).2 hmyIk_sh
    have hpeerIk_eq : peerIk' = st₀.myIk := by
      rw [← hpeerIk_s] at hpeerIk_sh ⊢
      exact eq_of_shape_eq_of_shapeId (hIk st_s hst_s).2 (hIk st₀ hst₀).1 hpeerIk_sh
    exact g1b_honest_send_branch_core interpretation hEq r₀ S g ms b ptext parsed hTryFrom
      t₀ msg₀ ht₀ hparse₀ st₀ mkSeed hseed k_own hDecOk
      salt₁ pqSalt' seed' myIk' peerIk' a' m' pqMsg' ns' pn'
      hsalt_gamma hmac_eq' hsh_inp' hpq_ak ht'_kn' hrk_eq hseed_eq hmyIk_eq hpeerIk_eq

end Symbolic.Swarm.CREF.TR.G1
