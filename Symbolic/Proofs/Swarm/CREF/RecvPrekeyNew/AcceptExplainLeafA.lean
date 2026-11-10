/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Batteries.Data.UInt
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.MacInv
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpqrRkForgedMac
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.Proofs.Swarm.CREF.TR.StoredRk
public import Symbolic.Proofs.Refinement.LemmasPure -- shake: keep
import Symbolic.Proofs.Refinement.EncodeWithCovered -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Forged Pre-Key Wire Representation Construction

Proves canonical X25519 key equivalence under `gamma` and constructs forged attacker-known pre-key
wire representations from an attacker-known receive seed.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg trMsgKeys)
open DY.Libsignal.TripleRatchet (computeMac hmac hkdfBlock1 hkdfBlock3 lit messageVersion)
open DY.Libsignal.PQXDH (errToOption serializedIk)
open Symbolic.Swarm.CREF.MacInv
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.CREF.TR.G1.Spine

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

private theorem leaf_eq_of_uOf_eq_canonical {A B : HwBytes} (hA : A.length = 32)
    (hB : B.length = 32)
    (hAc : DY.X25519.leValue (A.map BitVec.toNat) < DY.X25519.p25519)
    (hBc : DY.X25519.leValue (B.map BitVec.toNat) < DY.X25519.p25519)
    (hu : x25519UCoord A = x25519UCoord B) : A = B := by
  have hp := TR.p25519_lt
  have hAB : DY.X25519.leValue (A.map BitVec.toNat) = DY.X25519.leValue (B.map BitVec.toNat) := by
    unfold x25519UCoord DY.X25519.uCoord at hu
    rwa [Nat.mod_eq_of_lt (by omega : DY.X25519.leValue (A.map BitVec.toNat) < 2 ^ 255),
      Nat.mod_eq_of_lt (by omega : DY.X25519.leValue (B.map BitVec.toNat) < 2 ^ 255),
      Nat.mod_eq_of_lt hAc, Nat.mod_eq_of_lt hBc] at hu
  rw [← TR.RecvRep.leBytes_leValue A, ← TR.RecvRep.leBytes_leValue B, hA, hB, hAB]

private theorem leaf_gamma_variant_pack (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (v : DY.X25519.Variant.SubF DY.Bytes) :
    gamma i S g v.pack =
      variantBytes (DY.Libsignal.Refinement.torsionShift i (gamma i S g v.key) v.torsion)
        v.variation := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeVariant i) (concretizeAll i S g)]
  rfl

private theorem leaf_torsionShift_length (i : ExternInterpretation) (point : HwBytes) (t : Fin 8) :
    (DY.Libsignal.Refinement.torsionShift i point t).length = point.length := by
  unfold DY.Libsignal.Refinement.torsionShift
  split
  · rfl
  · rename_i h
    have hlen : point.length = 32 := by revert h; simp
    split
    · split
      · rename_i q _ hq; omega
      · rfl
    · rfl

/-- `gamma` commutes with `normalizeX25519Key` on an honest X25519 public key whose wire bytes are
canonical and torsion-free. -/
theorem leaf_gamma_x25519Key_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold i)
    (hPubCanon : X25519PubCanonical i)
    (hRej : DY.Libsignal.PQXDH.Refinement.X25519TorsionShiftsRejected i)
    (ek sk : DY.Bytes)
    (hkey : DY.X25519.normalizeX25519Key ek = DY.DiffieHellman.dhPk sk)
    (hek_canon : DY.X25519.leValue ((gamma i S g ek).map BitVec.toNat) < DY.X25519.p25519)
    (hek_tf : DY.Libsignal.PQXDH.Refinement.X25519TorsionFree i (gamma i S g ek)) :
    gamma i S g (DY.X25519.normalizeX25519Key ek) = gamma i S g ek := by
  unfold DY.X25519.normalizeX25519Key at hkey ⊢
  cases hview : ek.view? DY.X25519.Variant.SubF with
  | none => rfl
  | some x =>
    simp only [hview] at hkey ⊢
    have hpack : x.pack = ek := by
      have hp := DY.Bytes.pack_view? DY.X25519.Variant.SubF ek
      simpa [hview] using hp
    have hgamma_ek : gamma i S g ek =
        variantBytes (DY.Libsignal.Refinement.torsionShift i (gamma i S g x.key) x.torsion)
          x.variation := by
      rw [← hpack, leaf_gamma_variant_pack]
    have hl_key : (gamma i S g x.key).length = 32 := by
      rw [hkey, TR.gamma_dhPk]
      exact hEq.x25519_public_key_length (clamp (gamma i S g sk))
    have hk_canon : DY.X25519.leValue ((gamma i S g x.key).map BitVec.toNat) < DY.X25519.p25519 := by
      rw [hkey, TR.gamma_dhPk]
      exact hPubCanon (clamp (gamma i S g sk))
    have hl_ts :
        (DY.Libsignal.Refinement.torsionShift i (gamma i S g x.key) x.torsion).length = 32 := by
      rw [leaf_torsionShift_length, hl_key]
    have hs := TR.variantBytes_spec _ hl_ts x.variation
    have hl_ek : (gamma i S g ek).length = 32 := by
      rw [hgamma_ek]; exact hs.1
    have hu_ek_ts : x25519UCoord (gamma i S g ek) =
        x25519UCoord (DY.Libsignal.Refinement.torsionShift i (gamma i S g x.key) x.torsion) := by
      rw [hgamma_ek]; exact hs.2
    have hu_eq : x25519UCoord (gamma i S g ek) = x25519UCoord (gamma i S g x.key) := by
      by_contra hne
      have hvk : gamma i S g x.key =
          (i DY.Libsignal.Refinement.x25519PublicKeySymbol [clamp (gamma i S g sk)]).getD [] := by
        rw [hkey, TR.gamma_dhPk]
      unfold x25519UCoord at hu_ek_ts hne
      rw [hvk] at hu_ek_ts hne
      exact hRej (clamp (gamma i S g sk)) x.torsion (gamma i S g ek)
        hl_ek hu_ek_ts hne hek_tf
    exact (leaf_eq_of_uOf_eq_canonical hl_ek hl_key hek_canon hk_canon hu_eq).symm

private theorem leaf_parsePreKeyWire_inv {b : HwBytes} {p : PreKeyFields}
    (h : parsePreKeyWire b = some p) :
    CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec p.message = .ok p.inner := by
  unfold parsePreKeyWire at h
  cases b with
  | nil => cases h
  | cons t body =>
    dsimp only at h
    split at h
    · unfold parsePreKey at h
      cases body with
      | nil => cases h
      | cons vb body' =>
        dsimp only at h
        split at h
        · cases h
        · cases hd : decodePreKey body' with
          | none => rw [hd] at h; cases h
          | some m =>
            rw [hd] at h; dsimp only at h
            cases hbk : m.baseKey with
            | none => rw [hbk] at h; cases h
            | some bk =>
              cases hik : m.identityKey with
              | none => rw [hbk, hik] at h; cases h
              | some ik =>
                cases hmsg : m.message with
                | none => rw [hbk, hik, hmsg] at h; cases h
                | some msg =>
                  cases hsid : m.signedPreKeyId with
                  | none => rw [hbk, hik, hmsg, hsid] at h; cases h
                  | some sid =>
                    rw [hbk, hik, hmsg, hsid] at h; dsimp only at h
                    split at h
                    · cases htry : CryptoGames.LibsignalSession.SignalMessage.tryFrom
                          CryptoVerification.LibsignalProtoCodec.protoSignalCodec msg with
                      | error _ => rw [htry] at h; cases h
                      | ok inner =>
                        rw [htry] at h; injection h with hp; subst hp; exact htry
                    · cases h
    · cases h

theorem leaf_isCanonicalKey_litOf (bs : HwBytes)
    (hnotlow : DY.X25519.isLowOrderKey (bs.map BitVec.toNat) = false) :
    PQXDH.isCanonicalKey (litOf bs) = true := by
  unfold PQXDH.isCanonicalKey
  have hv : (litOf bs).view? DY.X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  have hnone : ((litOf bs).view? DY.X25519.Variant.SubF).isNone = true := by
    rw [hv]; rfl
  have hkey : DY.X25519.normalizeX25519Key (litOf bs) = litOf bs := by
    unfold DY.X25519.normalizeX25519Key; rw [hv]
  have hlow : PQXDH.x25519LowOrder (litOf bs) = false := by
    unfold PQXDH.x25519LowOrder
    rw [hkey]
    change (match DY.Literal.bytesToLiteral (DY.Literal.literalToBytes (Bytes := DY.Bytes) ⟨(bs.map UInt8.ofBitVec).toArray⟩) with
      | some b => DY.X25519.isLowOrderKey (b.data.toList.map UInt8.toNat)
      | none => false) = false
    rw [DY.Literal.bytesToLiteral_literalToBytes]
    dsimp only
    have hmap : (⟨(bs.map UInt8.ofBitVec).toArray⟩ : ByteArray).data.toList.map UInt8.toNat =
        bs.map BitVec.toNat := by
      simp [Function.comp_def]
    rw [hmap]
    exact hnotlow
  rw [hnone, hlow]
  rfl

private theorem leaf_runTrace_at?_7 (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move) :
    (runTraceMoves r ms).at? 7 = some (TR.NetE (setupPublic r 2)) := by
  have h2 : setupPublic r 2 = DY.DiffieHellman.dhPk (randTerm 5 32) := by
    rw [(TR.setupPublic_eq r hne).2.1, (TR.setupSecret_eq r hne).2.1]
  rw [h2]
  have hle := setupTrace_le_runTrace r ms
  have h0 : ((setupTrace r).at? 7 : Option DY.Network.ExecEntryT) =
      some (TR.NetE (DY.DiffieHellman.dhPk (randTerm 5 32))) := by
    rw [TR.setupTrace_eq r hne]
    cases r.withOpk <;>
      (simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
       repeat (first
         | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
         | exact TR.at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])))
  by_cases hj : 7 < (setupTrace r).length
  · rw [← h0, at?_of_le hle hj]
  · simp [Trace.at?, hj] at h0

private theorem leaf_setupPublic_2_attackerKnows (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move) :
    (setupPublic r 2).AttackerKnows (runTraceMoves r ms) :=
  TR.attackerKnows_of_at?_network (leaf_runTrace_at?_7 r hne ms)

private theorem leaf_serializedIk_attackerKnows {tr : ExecTrace} {pk : DY.Bytes}
    (h : pk.AttackerKnows tr) :
    (PQXDH.serializedIk pk).AttackerKnows tr :=
  Concat.attacker_knows_concat _ _ _ (Literal.attacker_knows_literalToBytes _ _) h

unseal DY.Bytes in
private instance subTrWire0Leaf (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

private theorem leaf_gamma_trWireMsg (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (v : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes)
    (ev : DY.TrWire.EncodingVariation) :
    gamma i S g (DY.TrWire.trWireMsg v rk c pc ct pq ev) =
      DY.Libsignal.TripleRatchet.Refinement.trWireBytes
        (g.addr (DY.TrWire.trWireMsg v rk c pc ct pq ev))
        ev
        ⟨v.toNat, gamma i S g rk, c.toNat, pc.toNat, gamma i S g ct⟩
        (gamma i S g pq) := by
  unfold DY.TrWire.trWireMsg gamma gamma'
  show (((⟨v, rk, c, pc, ct, pq, ev⟩ : DY.TrWire.TrWireMsg.SubF DY.Bytes).pack).rec
    (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll i S g)]
  rfl

private theorem leaf_parseTrSignalMsg_concat_trWireMsg
    (v : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes)
    (ev : DY.TrWire.EncodingVariation) (mac : DY.Bytes)
    (hmac : mac.length = Trunc.trunc8Length) :
    let wire := DY.TrWire.trWireMsg v rk c pc ct pq ev
    DY.Libsignal.TripleRatchet.parseTrSignalMsg (Concat.concat wire mac) =
      some { wire := wire
             mac := mac
             version := v % 16
             ratchetKey := rk
             counter := c
             ciphertext := ct
             pqRatchet := pq } := by
  intro wire; unfold DY.Libsignal.TripleRatchet.parseTrSignalMsg
  have hlen : (Concat.concat wire mac).length - Trunc.trunc8Length = wire.length := by
    rw [Concat.length_concat, hmac]; omega
  rw [hlen, Concat.split_concat]
  simp [Bind.bind, Pure.pure, wire, DY.TrWire.trWireMsgFields?_trWireMsg]

private theorem leaf_parseTrSignalMsg_eq_some_inv {t₀ : DY.Bytes}
    {msg₀ : DY.Libsignal.TripleRatchet.TRSignalMsg}
    (hparse₀ : DY.Libsignal.TripleRatchet.parseTrSignalMsg t₀ = some msg₀) :
    ∃ (v₀ : UInt8) (pc₀ : UInt32) (ev₀ : DY.TrWire.EncodingVariation),
      msg₀.wire = DY.TrWire.trWireMsg v₀ msg₀.ratchetKey msg₀.counter pc₀
        msg₀.ciphertext msg₀.pqRatchet ev₀ := by
  unfold DY.Libsignal.TripleRatchet.parseTrSignalMsg at hparse₀
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
      rw [hview] at hv; dsimp only at hv
      injection hparse₀ with hmsg; subst hmsg
      exact ⟨x.version, x.previousCounter, x.encodingVariation, hv.symm⟩

open CryptoGames CryptoGames.LibsignalSession CryptoVerification CryptoVerification.LibsignalProtoCodec in
open DY.Libsignal.Refinement (WireFields u32Bytes decodeLittleEndianNat leNat_u32Bytes) in
open DY.TrWire (EncodingVariation canonicalVariation) in
open DY.Libsignal.TripleRatchet in
open Symbolic.Swarm.CREF.TR.RecvRep in
private theorem leaf_exists_trWire_rep_with_pqTerm
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move) (b : HwBytes)
    (parsed : SignalMessage)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    (rk_term ct_term pq_term : DY.Bytes)
    (hrk_knows : rk_term.AttackerKnows (runTraceMoves r₀ ms))
    (hct_knows : ct_term.AttackerKnows (runTraceMoves r₀ ms))
    (hpq_knows : pq_term.AttackerKnows (runTraceMoves r₀ ms))
    (hrk_gamma : gamma interpretation S g rk_term = parsed.senderRatchetKey.bytes.toList)
    (hct_gamma : gamma interpretation S g ct_term = parsed.ciphertext) :
    ∃ (v : EncodingVariation),
      let wire' := DY.TrWire.trWireMsg (UInt8.ofBitVec parsed.messageVersion) rk_term
        (UInt32.ofBitVec parsed.counter) (UInt32.ofBitVec parsed.previousCounter)
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
            version := UInt8.ofBitVec parsed.messageVersion % 16
            ratchetKey := rk_term
            counter := UInt32.ofBitVec parsed.counter
            ciphertext := ct_term
            pqRatchet := pq_term }
        t'.AttackerKnows (runTraceMoves r₀ ms) ∧
        gamma interpretation S g t' = b ∧
        parseTrSignalMsg t' = some msg' ∧
        msg'.version.toNat = parsed.messageVersion.toNat ∧
        msg'.ratchetKey = rk_term ∧
        msg'.counter.toNat = parsed.counter.toNat ∧
        msg'.ciphertext = ct_term ∧
        msg'.pqRatchet = pq_term := by
  obtain ⟨v, f, mac, hv_ne, hb, hmac_len, _hv3, hv4, _hrk_len, _hc_lt, _hpc_lt,
          hver_m, hrk_m, hctr_m, hpc_m, hct_m⟩ :=
    DY.Libsignal.TripleRatchet.Refinement.trWireBytes_covered_uniform b parsed hTryFrom
  refine ⟨v, ?_⟩
  intro wire'
  have hwire_knows : wire'.AttackerKnows (runTraceMoves r₀ ms) := by
    dsimp only [wire']
    exact DY.TrWire.attacker_knows_trWireMsg _ _ _ _ _ _ _ _
      hrk_knows hct_knows hpq_knows
  have hrk_f : gamma interpretation S g rk_term = f.ratchetKey := hrk_gamma.trans hrk_m
  have hct_f : gamma interpretation S g ct_term = f.ciphertext := hct_gamma.trans hct_m
  have hf_eq :
      (⟨(UInt8.ofBitVec parsed.messageVersion).toNat, gamma interpretation S g rk_term,
        (UInt32.ofBitVec parsed.counter).toNat, (UInt32.ofBitVec parsed.previousCounter).toNat,
        gamma interpretation S g ct_term⟩ : WireFields) = f := by
    cases f
    simp only [UInt8.toNat_ofBitVec, UInt32.toNat_ofBitVec]
    dsimp only at hver_m hrk_f hctr_m hpc_m hct_f
    rw [hver_m, hrk_f, hctr_m, hpc_m, hct_f]
  have hwire_gamma : gamma interpretation S g wire' =
      trWireBytes (g.addr wire') v f (gamma interpretation S g pq_term) := by
    dsimp only [wire']
    rw [leaf_gamma_trWireMsg, hf_eq]
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
  intro mac_term hmac_knows hmac_sym_len hmac_gamma _hmac_ns t' msg'
  have ht'_knows : t'.AttackerKnows (runTraceMoves r₀ ms) :=
    Concat.attacker_knows_concat _ _ _ hwire_knows hmac_knows
  have ht'_gamma : gamma interpretation S g t' = b := by
    dsimp only [t']
    rw [TR.gamma_concat, hmac_gamma, ← hb_split]
  have hparse : parseTrSignalMsg t' = some msg' :=
    leaf_parseTrSignalMsg_concat_trWireMsg (UInt8.ofBitVec parsed.messageVersion) rk_term
      (UInt32.ofBitVec parsed.counter) (UInt32.ofBitVec parsed.previousCounter) ct_term pq_term v
      mac_term hmac_sym_len
  have hver_eq : msg'.version.toNat = parsed.messageVersion.toNat := by
    dsimp only [msg']
    rw [UInt8.toNat_mod, UInt8.toNat_ofBitVec]
    change parsed.messageVersion.toNat % 16 = parsed.messageVersion.toNat
    omega
  have hctr_eq : msg'.counter.toNat = parsed.counter.toNat := by
    dsimp only [msg']
    exact UInt32.toNat_ofBitVec
  exact ⟨ht'_knows, ht'_gamma, hparse, hver_eq, rfl, hctr_eq, rfl, rfl⟩

theorem leaf_forged_exactRep_of_ek
    {interpretation : ExternInterpretation} {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    {b ct_wire pt : HwBytes} {p : PreKeyFields} {x' : PreKeyRep} {msg' : TRSignalMsg}
    {salt' seed' : DY.Bytes}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (hmp : MatchedPrefix interpretation r S who g ms acc)
    (hp : parsePreKeyWire b = some p)
    (hnk : ¬ KyberMismatch interpretation r p)
    (hct_wire : p.kyberCiphertext = some (kyberKey ct_wire))
    (hct_len : ct_wire.length = 1568)
    (hopk_ok : p.preKeyId = none ∨ (r.withOpk = true ∧ p.preKeyId = some r.opkId))
    (hx' : x' ∈ preKeyRepresentations interpretation r S g ms b)
    (hparse : parseTrSignalMsg x'.msg = some msg')
    (hbss : TR.bobSaltSeed r p x' = some (salt', seed'))
    (hlow' : TripleRatchet.x25519LowOrder msg'.ratchetKey = false)
    (hctr'_le : msg'.counter.toNat ≤ TripleRatchet.maxForwardJumps)
    (hmac_T_gamma : gamma interpretation S g
      (TripleRatchet.computeMac (TripleRatchet.trMsgKeys salt' seed').macKey
        (PQXDH.serializedIk (setupPublic r 0))
        (PQXDH.serializedIk (setupPublic r 2)) msg'.wire) =
      gamma interpretation S g msg'.mac)
    (hdec_wire : interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
      [gamma interpretation S g msg'.ciphertext,
       gamma interpretation S g (TripleRatchet.trMsgKeys salt' seed').cipherKey,
       (gamma interpretation S g (TripleRatchet.trMsgKeys salt' seed').iv).take 16] = some pt)
    (hpq_ne : gamma interpretation S g msg'.pqRatchet ≠ [])
    {ek_x salt seed : DY.Bytes}
    (hek_x_ak : ek_x.AttackerKnows (runTraceMoves r ms))
    (hek_x_gam : gamma interpretation S g ek_x = gamma interpretation S g x'.ek)
    (hek_x_can : PQXDH.isCanonicalKey ek_x = true)
    (hbss₀ : TR.bobSaltSeed r p { ek := ek_x, ct := x'.ct, msg := x'.msg } = some (salt, seed))
    (hseed_x_ak : seed.AttackerKnows (runTraceMoves r ms)) :
    ∃ (x : PreKeyRep) (msg : TRSignalMsg) (salt seed pqSalt m : DY.Bytes),
      x ∈ preKeyRepresentations interpretation r S g ms b ∧
      PQXDH.isCanonicalKey x.ek = true ∧
      parseTrSignalMsg x.msg = some msg ∧
      TripleRatchet.x25519LowOrder msg.ratchetKey = false ∧
      TR.bobSaltSeed r p x = some (salt, seed) ∧
      pqSalt.AttackerKnows (runTraceMoves r ms) ∧
      msg.mac = TripleRatchet.computeMac (TripleRatchet.trMsgKeys pqSalt seed).macKey
        (PQXDH.serializedIk (setupPublic r 0))
        (PQXDH.serializedIk (setupPublic r 2)) msg.wire ∧
      PQXDH.errToOption (DY.SymEnc.symDec
        (TripleRatchet.trMsgKeys pqSalt seed).cipherKey
        (TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some m ∧
      gamma interpretation S g m = pt := by
  have hne : r.alice ≠ r.bob := hwf.1
  let tr := runTraceMoves r ms
  have hx'_mem := hx'
  obtain ⟨_, hct_ak, hmsg_ak, ⟨p₁, hp₁, hbase₁, hkyb₁, hmsgb₁, hv4₁, hspk₁, hkpk₁, hik₁, hopk₁⟩, p₀, hp₀,
    ⟨msg₀, hparse₀, hw₀, hm₀, hspqr₀, hct₀, hrk₀, hpq₀, hcnt₀, hv₀'⟩⟩ := hx'
  cases hp.symm.trans hp₁
  cases hp.symm.trans hp₀
  rw [hparse] at hparse₀; injection hparse₀ with hmsg₀_eq; subst hmsg₀_eq
  let x₀ : PreKeyRep := { ek := ek_x, ct := x'.ct, msg := x'.msg }
  have hx₀ : x₀ ∈ preKeyRepresentations interpretation r S g ms b :=
    ⟨hek_x_ak, hct_ak, hmsg_ak,
      ⟨p, hp, by dsimp [x₀]; rw [hek_x_gam]; exact hbase₁, hkyb₁, hmsgb₁, hv4₁, hspk₁, hkpk₁, hik₁, hopk₁⟩,
      p, hp, ⟨msg', hparse, hw₀, hm₀, hspqr₀, hct₀, hrk₀, hpq₀, hcnt₀, hv₀'⟩⟩
  have hopk_used : p.preKeyId = none ∨ (r.withOpk = true ∧ false = false ∧ p.preKeyId = some r.opkId) := by
    rcases hopk_ok with h | ⟨h1, h2⟩
    · exact .inl h
    · exact .inr ⟨h1, rfl, h2⟩
  have hctr_p : p.inner.counter.toNat ≤ TripleRatchet.maxForwardJumps := by omega
  have hpq_p : p.inner.pqRatchet ≠ [] := by rw [← hpq₀]; exact hpq_ne
  obtain ⟨hsalt'_gam, hseed'_gam, _⟩ :=
    TR.bobSaltSeed_gamma interpretation hEq r hwf S g hmp.1 false b p hp hnk ct_wire
      hct_wire hct_len hopk_used hctr_p hpq_p ms x' hx'_mem msg' salt' seed' hparse hbss
  obtain ⟨hsalt_gam, hseed_gam, _⟩ :=
    TR.bobSaltSeed_gamma interpretation hEq r hwf S g hmp.1 false b p hp hnk ct_wire
      hct_wire hct_len hopk_used hctr_p hpq_p ms x₀ hx₀ msg' salt seed hparse hbss₀
  let pqSalt := litOf (gamma interpretation S g salt')
  let m := litOf pt
  let ct_term := DY.SymEnc.symEnc (TripleRatchet.trMsgKeys pqSalt seed).cipherKey
    (TripleRatchet.trMsgKeys pqSalt seed).iv m
  have hpqSalt_ak : pqSalt.AttackerKnows tr := TR.RecvRep.knows_litOf _ _
  have hpqSalt_gam : gamma interpretation S g pqSalt = gamma interpretation S g salt' :=
    TR.RecvRep.gamma_litOf interpretation S g _
  have hseed_eq_gam : gamma interpretation S g seed = gamma interpretation S g seed' :=
    hseed_gam.trans hseed'_gam.symm
  obtain ⟨hck_gam, hmk_gam, hiv_gam⟩ :=
    gamma_trMsgKeys_eq_of_gamma_eq interpretation S g hpqSalt_gam hseed_eq_gam
  have hprk_kn : (TripleRatchet.hmac pqSalt seed).AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hpqSalt_ak hseed_x_ak
  have hinfo_kn : (TripleRatchet.lit "WhisperMessageKeys").AttackerKnows tr :=
    Literal.attacker_knows_literalToBytes _ _
  have hck_kn : (TripleRatchet.trMsgKeys pqSalt seed).cipherKey.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _))
  have hmk_kn : (TripleRatchet.trMsgKeys pqSalt seed).macKey.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hck_kn (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _)))
  have hiv_kn : (TripleRatchet.trMsgKeys pqSalt seed).iv.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hmk_kn (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _)))
  have hct_kn : ct_term.AttackerKnows tr :=
    DY.SymEnc.attacker_knows_symEnc _ _ _ tr hck_kn hiv_kn (TR.RecvRep.knows_litOf pt _)
  have hwire'_kn : msg'.wire.AttackerKnows tr :=
    (TR.attackerKnows_ratchetKey_and_wire_of_parseTrSignalMsg hmsg_ak hparse).2
  obtain ⟨v₀, pc₀, ev₀, hwire₀_eq⟩ := leaf_parseTrSignalMsg_eq_some_inv hparse
  have hargs₀ := DY.TrWire.attacker_knows_trWireMsg_args v₀ msg'.ratchetKey msg'.counter pc₀
    msg'.ciphertext msg'.pqRatchet ev₀ tr (hwire₀_eq ▸ hwire'_kn)
  have hck_len : (gamma interpretation S g (TripleRatchet.trMsgKeys salt' seed').cipherKey).length = 32 := by
    unfold TripleRatchet.trMsgKeys hkdfBlock1 hmac
    rw [gamma_kdfExtract_tr]; exact TR.length_hmacWith _ _ _
  have hiv_len32 : (gamma interpretation S g (TripleRatchet.trMsgKeys salt' seed').iv).length = 32 := by
    unfold TripleRatchet.trMsgKeys hkdfBlock3 hmac
    rw [gamma_kdfExtract_tr]; exact TR.length_hmacWith _ _ _
  have hiv_len : ((gamma interpretation S g (TripleRatchet.trMsgKeys salt' seed').iv).take 16).length = 16 := by
    rw [List.length_take, hiv_len32]; decide
  have hct_gam : gamma interpretation S g ct_term = p.inner.ciphertext := by
    rw [← hct₀]
    dsimp only [ct_term, m]
    rw [gamma_symEnc_tr, TR.RecvRep.gamma_litOf, hck_gam, hiv_gam,
        hEq.aes_cbc_encrypt_of_decrypt _ _ _ _ hck_len hiv_len hdec_wire, Option.getD_some]
  have hTryFrom := leaf_parsePreKeyWire_inv hp
  obtain ⟨v, _, hwire_forged_kn, hwire_forged_take, _, _, hforged⟩ :=
    leaf_exists_trWire_rep_with_pqTerm interpretation r S g ms p.message p.inner hTryFrom
      msg'.ratchetKey ct_term msg'.pqRatchet hargs₀.1 hct_kn hargs₀.2.2 hrk₀ hct_gam
  let wire_forged := DY.TrWire.trWireMsg (UInt8.ofBitVec p.inner.messageVersion)
    msg'.ratchetKey (UInt32.ofBitVec p.inner.counter)
    (UInt32.ofBitVec p.inner.previousCounter)
    ct_term msg'.pqRatchet v
  let mac_forged := TripleRatchet.computeMac (TripleRatchet.trMsgKeys pqSalt seed).macKey
    (PQXDH.serializedIk (setupPublic r 0)) (PQXDH.serializedIk (setupPublic r 2)) wire_forged
  have hPeerK : (PQXDH.serializedIk (setupPublic r 0)).AttackerKnows tr :=
    leaf_serializedIk_attackerKnows (setupPublic_0_attackerKnows r hne ms)
  have hMyK : (PQXDH.serializedIk (setupPublic r 2)).AttackerKnows tr :=
    leaf_serializedIk_attackerKnows (leaf_setupPublic_2_attackerKnows r hne ms)
  have hmac_forged_kn : mac_forged.AttackerKnows tr :=
    Trunc.attacker_knows_trunc8 _ _
      (KdfExtract.attacker_knows_kdfExtract _ _ _ hmk_kn
        (Concat.attacker_knows_concat _ _ _ hPeerK
          (Concat.attacker_knows_concat _ _ _ hMyK hwire_forged_kn)))
  have hmac_forged_len : mac_forged.length = Trunc.trunc8Length :=
    length_computeMac_tr _ _ _ _
  have hmac_forged_gam : gamma interpretation S g mac_forged = p.message.drop (p.message.length - 8) := by
    rw [← hm₀, ← hmac_T_gamma]
    dsimp only [mac_forged]
    unfold TripleRatchet.computeMac TripleRatchet.hmac
    rw [TR.gamma_trunc8, TR.gamma_trunc8, gamma_kdfExtract_tr, gamma_kdfExtract_tr,
      TR.gamma_concat, TR.gamma_concat, TR.gamma_concat, TR.gamma_concat,
      hmk_gam, hwire_forged_take.trans hw₀.symm]
  have hmac_forged_spqr : spqrHeaded mac_forged = false := by
    dsimp only [mac_forged, TripleRatchet.computeMac, DY.Trunc.trunc8, DY.Trunc.CanTrunc8.trunc8, spqrHeaded]
    simp only [Symbolic.DYBridge.DY.Bytes.view?_pack_cross]
    rfl
  obtain ⟨ht_forged_kn, ht_forged_gam, hparse_forged, hver_forged, hrk_forged, hctr_forged,
    hct_forged, hpq_forged⟩ :=
    hforged mac_forged hmac_forged_kn hmac_forged_len hmac_forged_gam hmac_forged_spqr
  let t_forged := Concat.concat wire_forged mac_forged
  let msg_forged : TRSignalMsg :=
    { wire := wire_forged
      mac := mac_forged
      version := UInt8.ofBitVec p.inner.messageVersion % 16
      ratchetKey := msg'.ratchetKey
      counter := UInt32.ofBitVec p.inner.counter
      ciphertext := ct_term
      pqRatchet := msg'.pqRatchet }
  have hctr_eq : UInt32.ofBitVec p.inner.counter = msg'.counter :=
    UInt32.ext (hctr_forged.trans hcnt₀.symm)
  let x : PreKeyRep := { ek := ek_x, ct := x'.ct, msg := t_forged }
  have hbss_x : TR.bobSaltSeed r p x = some (salt, seed) := by
    rw [← hbss₀]
    unfold TR.bobSaltSeed
    have hbk : TR.bobKeys r p x = TR.bobKeys r p x₀ := rfl
    rw [hbk, hparse_forged, hparse]
    dsimp only [Bind.bind, Option.bind, TR.bobChain, msg_forged]
    rw [hctr_eq]
  refine ⟨x, msg_forged, salt, seed, pqSalt, m,
    ⟨hek_x_ak, hct_ak, ht_forged_kn,
      ⟨p, hp, by dsimp [x]; rw [hek_x_gam]; exact hbase₁, hkyb₁, ht_forged_gam.symm, hv4₁, hspk₁, hkpk₁, hik₁, hopk₁⟩,
      p, hp, ⟨msg_forged, hparse_forged, hwire_forged_take, hmac_forged_gam, hmac_forged_spqr,
        hct_gam, hrk₀, hpq₀, hctr_forged, hver_forged⟩⟩,
    hek_x_can, hparse_forged, hlow', hbss_x, hpqSalt_ak, rfl, ?_,
    TR.RecvRep.gamma_litOf interpretation S g pt⟩
  dsimp only [msg_forged, ct_term]
  rw [DY.SymEnc.symDec_symEnc]
  rfl

end Symbolic.Swarm.CREF
