/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.CliShape
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
public import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc
public import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
open ByteSpecs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (paddedVarint encodeField PbValue encodeWith canonicalVariation WireFields FieldItem knownValue? sha256CompressFunction)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.Census443Defs
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
private theorem length_hmac_symbolic (k m : DY.Bytes) : (DY.Libsignal.TripleRatchet.hmac k m).length = 32 := length_hmac_symbolic_bridge k m
theorem length_computeMac (mk ikS ikR wire : DY.Bytes) : (DY.Libsignal.TripleRatchet.computeMac mk ikS ikR wire).length = DY.Trunc.trunc8Length := by simp [DY.Libsignal.TripleRatchet.computeMac, DY.Trunc.length_trunc8, length_hmac_symbolic, trunc8Length_eq_8]
theorem length_encMac (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : (encMac tr₂ stA cl pq).length = DY.Trunc.trunc8Length := by unfold encMac; exact length_computeMac _ _ _ _
theorem spqrHeaded_encMac (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : spqrHeaded (encMac tr₂ stA cl pq) = false := spqrHeaded_computeMac_bridge _ _ _ _
def encParsedMsg (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Libsignal.TripleRatchet.TRSignalMsg :=
  let m := randTerm tr₂.length 32; let coins := randTerm (tr₂.length + 1) cl; let (_, _, pqMsg) := DY.Spqr.spqrSend stA.spqr coins; let (_, seed) := DY.Libsignal.TripleRatchet.kdfCk stA.cks; let pqSalt := encSalt tr₂ stA cl pq; let keys := DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed;
  { wire := encWire tr₂ stA cl pq, mac := encMac tr₂ stA cl pq, version := 4, ratchetKey := DY.DiffieHellman.dhPk stA.dhs, counter := stA.ns, ciphertext := DY.SymEnc.symEnc keys.cipherKey keys.iv m, pqRatchet := pqMsg }
theorem parseTrSignalMsg_encOut (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Libsignal.TripleRatchet.parseTrSignalMsg (encOut tr₂ stA cl pq) = some (encParsedMsg tr₂ stA cl pq) := by
  have hl :
      (Concat.concat (encWire tr₂ stA cl pq) (encMac tr₂ stA cl pq)).length - DY.Trunc.trunc8Length =
      (encWire tr₂ stA cl pq).length := by
    rw [DY.Concat.length_concat, length_encMac, Nat.add_sub_cancel]
  simp only [DY.Libsignal.TripleRatchet.parseTrSignalMsg, encOut, hl, DY.Concat.split_concat]; simp only [encWire, DY.Libsignal.TripleRatchet.trHonestWireMsg, bind, Option.bind, DY.TrWire.trWireMsgFields?_trWireMsg]; rfl
theorem paddedVarint_ne_nil (n p : Nat) : paddedVarint n p ≠ [] := by
  rw [paddedVarint.eq_def]
  split <;> simp
theorem paddedVarint_zero_inj : ∀ (s n m : Nat) (r₁ r₂ : HwBytes), n < s → paddedVarint n 0 ++ r₁ = paddedVarint m 0 ++ r₂ → n = m ∧ r₁ = r₂
  | 0, _, _, _, _, hs, _ => absurd hs (Nat.not_lt_zero _)
  | s + 1, n, m, r₁, r₂, hs, h => by
    have hpn := paddedVarint.eq_def n 0; have hpm := paddedVarint.eq_def m 0; rw [hpn, hpm] at h; simp only [and_true] at h
    by_cases hn : n < 128 <;> by_cases hm : m < 128
    · simp only [hn, hm, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h; have hnm : n = m := (by have h1 := congrArg BitVec.toNat h.1; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1; omega); exact ⟨hnm, h.2⟩
    · simp only [hn, hm, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h; have h1 := congrArg BitVec.toNat h.1; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1; omega
    · simp only [hn, hm, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h; have h1 := congrArg BitVec.toNat h.1; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1; omega
    · simp only [hn, hm, ↓reduceIte, List.cons_append, List.cons.injEq] at h; have hmod : n % 128 = m % 128 := (by have h1 := congrArg BitVec.toNat h.1; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1; omega); have ⟨hdiv, hr⟩ := paddedVarint_zero_inj s (n / 128) (m / 128) r₁ r₂ (by omega) h.2; exact ⟨by omega, hr⟩
theorem encodeField_bytes_inj {t : Nat} {b₁ b₂ r₁ r₂ : HwBytes} (h : encodeField t 0 0 (.bytes b₁) ++ r₁ = encodeField t 0 0 (.bytes b₂) ++ r₂) : b₁ = b₂ ∧ r₁ = r₂ := by
  simp only [encodeField, List.append_assoc] at h; have h' := List.append_cancel_left h
  have ⟨hlen, hbr⟩ := paddedVarint_zero_inj (b₁.length + 1) b₁.length b₂.length
    (b₁ ++ r₁) (b₂ ++ r₂) (by omega) h'
  exact List.append_inj hbr hlen
theorem trWireBytes_canonical (addr : HwBytes) (f : WireFields) (pq : HwBytes) : trWireBytes addr canonicalVariation f pq = encodeWith canonicalVariation f ++ (if pq = [] then [] else encodeField 5 0 0 (.bytes pq)) ++ (if addr = [] then [] else encodeField 6 0 0 (.bytes addr)) := by
  unfold trWireBytes trFields honestTrItems encodeWith; simp only [↓reduceIte, List.flatMap_append, List.cons_append, List.append_assoc]; congr 1
  have hfields :
      canonicalVariation.fields.flatMap (trItemEncode addr canonicalVariation f pq) =
        canonicalVariation.fields.flatMap (FieldItem.encode canonicalVariation f) := by
    rw [canonicalVariation_eq]; rfl
  rw [hfields]; congr 1
  by_cases hpq : pq = [] <;> by_cases haddr : addr = [] <;>
    simp [hpq, haddr, trItemEncode]
theorem gamma_hmac_eq (i : ExternInterpretation) (S : Sem) (g : Ghost) (k m : DY.Bytes) : gamma i S g (DY.Libsignal.TripleRatchet.hmac k m) = hmacWith (sha256CompressFunction i) (gamma i S g k) (gamma i S g m) := by
  unfold gamma gamma' DY.Libsignal.TripleRatchet.hmac
  show ((({salt := k, ikm := m} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll i S g)).val = _
  rw [DY.Bytes.rec_eq (gKdf0 i) (gAll i S g)]; rfl
theorem gamma_trunc8 (i : ExternInterpretation) (S : Sem) (g : Ghost) (a : DY.Bytes) : gamma i S g (DY.Trunc.trunc8 a) = (gamma i S g a).take 8 := by
  unfold gamma gamma'
  show ((({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (gAll i S g)).val = _
  rw [DY.Bytes.rec_eq gTrunc0 (gAll i S g)]; rfl
theorem gamma_concat (i : ExternInterpretation) (S : Sem) (g : Ghost) (a b : DY.Bytes) : gamma i S g (DY.Concat.concat a b) = gamma i S g a ++ gamma i S g b := by
  unfold gamma gamma'
  show ((({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack).rec (gAll i S g)).val = _
  rw [DY.Bytes.rec_eq gConcat0 (gAll i S g)]; rfl
theorem gamma_computeMac_length (i : ExternInterpretation) (S : Sem) (g : Ghost) (mk ikS ikR wire : DY.Bytes) : (gamma i S g (DY.Libsignal.TripleRatchet.computeMac mk ikS ikR wire)).length = 8 := by unfold DY.Libsignal.TripleRatchet.computeMac; rw [gamma_trunc8, gamma_hmac_eq, List.length_take, hmacWith_length]; rfl
theorem gamma_encMac_length (i : ExternInterpretation) (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : (gamma i S g (encMac tr₂ stA cl pq)).length = 8 := by unfold encMac; exact gamma_computeMac_length i S g _ _ _ _
theorem gamma_trWire_eq (i : ExternInterpretation) (S : Sem) (g : Ghost) (v : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes) (ev : DY.TrWire.EncodingVariation) : gamma i S g (DY.TrWire.trWireMsg v rk c pc ct pq ev) = trWireBytes (g.addr (DY.TrWire.trWireMsg v rk c pc ct pq ev)) ev ⟨v.toNat, gamma i S g rk, c.toNat, pc.toNat, gamma i S g ct⟩ (gamma i S g pq) := by unfold gamma gamma'; dsimp only [DY.TrWire.trWireMsg, DY.TrWire.CanTrWireMsg.trWireMsg, DY.TrWire.instCanTrWireMsgBytes]; rw [DY.Bytes.rec_eq (gTrWire0 g) (gAll i S g)]; rfl
def innerWirePrefix (p : PreKeyFields) : HwBytes := encodeWith canonicalVariation ⟨4, p.inner.senderRatchetKey.bytes.toList, 0, 0, p.inner.ciphertext⟩ ++ encodeField 5 0 0 (.bytes p.inner.pqRatchet)
def InnerWireCanonical (p : PreKeyFields) : Prop := p.inner.counter = 0 ∧ p.inner.messageVersion = 4 ∧ p.message.take (p.message.length - 8) = innerWirePrefix p ++ (p.message.take (p.message.length - 8)).drop (innerWirePrefix p).length
theorem faithfulInner_of_gamma_encOut_generic (i : ExternInterpretation) (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (p : PreKeyFields) (hns : stA.ns = 0) (hpn : stA.pn = 0) (hγ : gamma i S g (encOut tr₂ stA cl pq) = p.message) (hcan : InnerWireCanonical p) : FaithfulInner i S g (encOut tr₂ stA cl pq) p := by
  obtain ⟨hcnt_p, hver_p, hwire_p⟩ := hcan; refine ⟨encParsedMsg tr₂ stA cl pq, parseTrSignalMsg_encOut tr₂ stA cl pq, ?_⟩; dsimp only [encParsedMsg]; let m := randTerm tr₂.length 32; let coins := randTerm (tr₂.length + 1) cl; let pqMsg := (DY.Spqr.spqrSend stA.spqr coins).2.2; let seed := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2; let pqSalt := encSalt tr₂ stA cl pq; let keys := DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed; let ct := DY.SymEnc.symEnc keys.cipherKey keys.iv m; let w := encWire tr₂ stA cl pq; let mac := encMac tr₂ stA cl pq;
  have hγ_split : gamma i S g w ++ gamma i S g mac = p.message := by rw [← hγ]; exact (gamma_concat i S g w mac).symm
  have hmac_len : (gamma i S g mac).length = 8 := gamma_encMac_length i S g tr₂ stA cl pq
  have hlen_msg : p.message.length - 8 = (gamma i S g w).length := by rw [← hγ_split, List.length_append, hmac_len]; omega
  have hwire_eq : gamma i S g w = p.message.take (p.message.length - 8) := by rw [hlen_msg, ← hγ_split, List.take_left]
  have hmac_eq : gamma i S g mac = p.message.drop (p.message.length - 8) := by rw [hlen_msg, ← hγ_split, List.drop_left]
  have htr :
      trWireBytes (g.addr w) canonicalVariation ⟨4, gamma i S g (DY.DiffieHellman.dhPk stA.dhs), 0, 0, gamma i S g ct⟩ (gamma i S g pqMsg) = innerWirePrefix p ++
        (p.message.take (p.message.length - 8)).drop (innerWirePrefix p).length := by
    have hw := hwire_eq.trans hwire_p
    have hw_unfold : w = DY.TrWire.trWireMsg 4 (DY.DiffieHellman.dhPk stA.dhs) 0 0 ct pqMsg
        canonicalVariation := by
      dsimp only [w, encWire, DY.Libsignal.TripleRatchet.trHonestWireMsg]; rw [hns, hpn]; rfl
    have hγw := gamma_trWire_eq i S g 4 (DY.DiffieHellman.dhPk stA.dhs) 0 0 ct pqMsg canonicalVariation; rw [← hw_unfold] at hγw; exact hγw.symm.trans hw
  rw [trWireBytes_canonical] at htr; simp only [innerWirePrefix, encodeWith, canonicalVariation_eq, List.flatMap_cons, List.flatMap_nil, FieldItem.encode, knownValue?, Option.map_some, Option.getD_some, List.cons_append, List.append_nil, List.append_assoc, List.cons.injEq, true_and] at htr; obtain ⟨hrk0, h2⟩ := encodeField_bytes_inj htr
  have hrk_eq : gamma i S g (DY.DiffieHellman.dhPk stA.dhs) =
      p.inner.senderRatchetKey.bytes.toList := by
    simpa using (List.cons.inj hrk0).2
  have h3 := List.append_cancel_left (List.append_cancel_left h2); obtain ⟨hct_eq, hpq0⟩ := encodeField_bytes_inj h3
  have hpq_ne : gamma i S g pqMsg ≠ [] := by
    intro hpq_nil; rw [hpq_nil] at hpq0; simp only [↓reduceIte, List.nil_append] at hpq0
    by_cases ha : g.addr w = []
    · simp only [ha, ↓reduceIte, encodeField, List.append_assoc] at hpq0; exact paddedVarint_ne_nil (5 * 8 + 2) 0 (List.append_eq_nil_iff.mp hpq0.symm).1
    · simp only [ha, ↓reduceIte] at hpq0
      have h1 : (encodeField 6 0 0 (.bytes (g.addr w))).head? = some 0x32#8 := by rw [encodeField, paddedVarint.eq_def (6 * 8 + 2) 0]; rfl
      have h2f : ∀ r : HwBytes,
          (encodeField 5 0 0 (.bytes p.inner.pqRatchet) ++ r).head? = some 0x2a#8 := by
        intro r; rw [encodeField, paddedVarint.eq_def (5 * 8 + 2) 0]; rfl
      have h3' := h1.symm.trans ((congrArg List.head? hpq0).trans (h2f _)); revert h3'; decide
  simp only [hpq_ne, ↓reduceIte] at hpq0; obtain ⟨hpq_eq, _⟩ := encodeField_bytes_inj hpq0; refine ⟨hwire_eq, hmac_eq, spqrHeaded_encMac tr₂ stA cl pq, hct_eq, hrk_eq, hpq_eq, ?_, ?_⟩
  · simp [hns, hcnt_p]
  · simp [hver_p]
theorem faithfulInner_of_gamma_encOut (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (p : PreKeyFields) (hns : stA.ns = 0) (hpn : stA.pn = 0) (hγ : gamma compI0 S g (encOut tr₂ stA cl pq) = p.message) (hcan : InnerWireCanonical p) : FaithfulInner compI0 S g (encOut tr₂ stA cl pq) p := faithfulInner_of_gamma_encOut_generic compI0 S g tr₂ stA cl pq p hns hpn hγ hcan
end Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
