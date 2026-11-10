/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26WeakStateIdx1
public import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public import Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
public import Symbolic.BugInjection.Proofs.Common443.CompRTag

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1PreKeyRep
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Refinement (paddedVarint encodeField PbValue encodeWith canonicalVariation WireFields FieldItem knownValue? sha256CompressFunction)
open ByteSpecs DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire Symbolic.BugInjection.Proofs.Common443.CompRTag
attribute [local instance 2000] DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasExecBytes DY.Libsignal.Composed.HasExecTrace.toCExecBytes
  DY.Libsignal.Composed.HasExecBytes.toTRExecBytes DY.Libsignal.Composed.HasExecBytes.toPQXDHExecBytes
  DY.Libsignal.Composed.toTripleRatchet DY.Libsignal.Composed.toPQXDHSpqr
  DY.Libsignal.Composed.instBytesFunctor_symbolic DY.Libsignal.Composed.instExecTraceTypes_symbolic
def recvAt (n : Nat) : HwBytes :=
  match ((Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.recv b) => b | _ => []
abbrev wire3Idx1Bytes : HwBytes := recvAt 40
abbrev wire6Idx1Bytes : HwBytes := recvAt 81
def x40Idx1 (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : PreKeyRep :=
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁' := encSt tr₂ (iniAliceStartState tr₁ r.bob o₁) cl₁
  ⟨o₁.ek, o₁.ct, encOut tr₃ stA₁' cl₂ (tr₃.length + 2)⟩
def x81Idx1 (r : Records) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : PreKeyRep :=
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := iniAliceStartState tr₁ r.bob o₁
  let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  ⟨o₂.ek, o₂.ct, encOut tr₂ stA₁ cl₁ (tr₂.length + 2)⟩
theorem sendMatches_append_inv {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {w : HwBytes} {L : List DY.Bytes} {o : DY.Bytes} {q₀ : PreKeyFields} (hsm : SendMatchesMoves i r S g w (L ++ [o])) (hlen : w.length < 2 ^ 63) (hq₀ : parsePreKeyWire w = some q₀) : ∃ ek' ct', L = [ek', ct'] ∧ q₀.baseKey = ecKey (gamma i S g ek') ∧ q₀.kyberCiphertext = some (kyberKey (gamma i S g ct')) ∧ q₀.message = gamma i S g o := by
  obtain ⟨_, hsm⟩ := hsm
  match L, hsm with
  | [ek', ct'], ⟨_, _, _, _, hw⟩ =>
    obtain ⟨_, hkc, hbk, hmsg⟩ := parsePreKeyWire_preKeyWire_inv hw hlen hq₀; exact ⟨ek', ct', rfl, hbk, hkc, hmsg⟩
  | [], hsm | [_], hsm => exact (hsm : False).elim
  | _ :: _ :: _ :: t, hsm => cases t <;> exact (hsm : False).elim
theorem x0_mem_of_parts {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {ek ct msg : DY.Bytes} {q : PreKeyFields} (hkek : ek.AttackerKnows (runTraceMoves r ms)) (hkct : ct.AttackerKnows (runTraceMoves r ms)) (hkmsg : msg.AttackerKnows (runTraceMoves r ms)) (hq : parsePreKeyWire b = some q) (hbk : q.baseKey.take 33 = ecKey (gamma i S g ek)) (hkc : q.kyberCiphertext = some (kyberKey (gamma i S g ct))) (hmsg : q.message = gamma i S g msg) (hout : PreKeyOuterMatches i r b q) (hfi : FaithfulInner i S g msg q) : (⟨ek, ct, msg⟩ : PreKeyRep) ∈ preKeyRepresentations i r S g ms b := ⟨hkek, hkct, hkmsg, ⟨q, hq, hbk, hkc, hmsg, hout⟩, q, hq, hfi⟩
export Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner ( length_computeMac length_encMac spqrHeaded_encMac encParsedMsg parseTrSignalMsg_encOut trWireBytes_canonical gamma_computeMac_length gamma_encMac_length)
def innerWirePrefixAt (cnt : Nat) (p : PreKeyFields) : HwBytes := encodeWith canonicalVariation ⟨4, p.inner.senderRatchetKey.bytes.toList, cnt, 0, p.inner.ciphertext⟩ ++ encodeField 5 0 0 (.bytes p.inner.pqRatchet)
def InnerWireCanonicalAt (cnt : Nat) (p : PreKeyFields) : Prop := p.inner.counter = BitVec.ofNat 32 cnt ∧ p.inner.messageVersion = 4 ∧ p.message.take (p.message.length - 8) = innerWirePrefixAt cnt p ++ (p.message.take (p.message.length - 8)).drop (innerWirePrefixAt cnt p).length
theorem faithfulInner_of_gamma_encOut_at_generic (cnt : UInt32) (i : ExternInterpretation) (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (p : PreKeyFields) (hns : stA.ns = cnt) (hpn : stA.pn = 0) (hγ : gamma i S g (encOut tr₂ stA cl pq) = p.message) (hcan : InnerWireCanonicalAt cnt.toNat p) : FaithfulInner i S g (encOut tr₂ stA cl pq) p ∧ gamma i S g (encWire tr₂ stA cl pq) = p.message.take (p.message.length - 8) ∧ gamma i S g (encMac tr₂ stA cl pq) = p.message.drop (p.message.length - 8) ∧ gamma i S g (DY.DiffieHellman.dhPk stA.dhs) = p.inner.senderRatchetKey.bytes.toList := by
  obtain ⟨hcnt_p, hver_p, hwire_p⟩ := hcan
  let m := randTerm tr₂.length 32; let coins := randTerm (tr₂.length + 1) cl
  let pqMsg := (DY.Spqr.spqrSend stA.spqr coins).2.2
  let keys := DY.Libsignal.TripleRatchet.trMsgKeys (encSalt tr₂ stA cl pq) (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2
  let ct := DY.SymEnc.symEnc keys.cipherKey keys.iv m
  let w := encWire tr₂ stA cl pq; let mac := encMac tr₂ stA cl pq
  have hγ_split : gamma i S g w ++ gamma i S g mac = p.message := hγ ▸ (gamma_concat i S g w mac).symm; have hmac_len : (gamma i S g mac).length = 8 := gamma_encMac_length i S g tr₂ stA cl pq
  have hlen_msg : p.message.length - 8 = (gamma i S g w).length := by rw [← hγ_split, List.length_append, hmac_len]; omega
  have hwire_eq : gamma i S g w = p.message.take (p.message.length - 8) := by rw [hlen_msg, ← hγ_split, List.take_left]
  have hmac_eq : gamma i S g mac = p.message.drop (p.message.length - 8) := by rw [hlen_msg, ← hγ_split, List.drop_left]
  have htr : trWireBytes (g.addr w) canonicalVariation ⟨4, gamma i S g (DY.DiffieHellman.dhPk stA.dhs), cnt.toNat, 0, gamma i S g ct⟩ (gamma i S g pqMsg) = innerWirePrefixAt cnt.toNat p ++ (p.message.take (p.message.length - 8)).drop (innerWirePrefixAt cnt.toNat p).length := by
    have hw_unfold : w = DY.TrWire.trWireMsg 4 (DY.DiffieHellman.dhPk stA.dhs) cnt 0 ct pqMsg canonicalVariation := by dsimp only [w, encWire, DY.Libsignal.TripleRatchet.trHonestWireMsg]; rw [hns, hpn]; rfl
    have hγw := gamma_trWire_eq i S g 4 (DY.DiffieHellman.dhPk stA.dhs) cnt 0 ct pqMsg canonicalVariation; rw [← hw_unfold] at hγw; exact hγw.symm.trans (hwire_eq.trans hwire_p)
  rw [trWireBytes_canonical, innerWirePrefixAt, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.canonicalVariation_eq] at htr
  simp only [encodeWith, List.flatMap_cons, List.flatMap_nil, FieldItem.encode, knownValue?, Option.map_some, Option.getD_some, List.cons_append, List.append_nil, List.append_assoc, List.cons.injEq, true_and] at htr; obtain ⟨hrk0, h2⟩ := encodeField_bytes_inj htr
  have hrk_eq : gamma i S g (DY.DiffieHellman.dhPk stA.dhs) = p.inner.senderRatchetKey.bytes.toList := by
    simpa using (List.cons.inj hrk0).2
  obtain ⟨hct_eq, hpq0⟩ := encodeField_bytes_inj (List.append_cancel_left (List.append_cancel_left h2))
  have hpq_ne : gamma i S g pqMsg ≠ [] := by
    intro hpq_nil; rw [hpq_nil] at hpq0; simp only [↓reduceIte, List.nil_append] at hpq0
    by_cases ha : g.addr w = []
    · simp only [ha, ↓reduceIte, encodeField, List.append_assoc] at hpq0
      exact paddedVarint_ne_nil (5 * 8 + 2) 0 (List.append_eq_nil_iff.mp hpq0.symm).1
    · simp only [ha, ↓reduceIte] at hpq0
      have h1 : (encodeField 6 0 0 (.bytes (g.addr w))).head? = some 0x32#8 := by rw [encodeField, paddedVarint.eq_def (6 * 8 + 2) 0]; rfl
      have h2f : ∀ r : HwBytes, (encodeField 5 0 0 (.bytes p.inner.pqRatchet) ++ r).head? = some 0x2a#8 := by intro r; rw [encodeField, paddedVarint.eq_def (5 * 8 + 2) 0]; rfl
      have h3' := h1.symm.trans ((congrArg List.head? hpq0).trans (h2f _)); revert h3'; decide
  simp only [hpq_ne, ↓reduceIte] at hpq0; obtain ⟨hpq_eq, _⟩ := encodeField_bytes_inj hpq0
  exact ⟨⟨encParsedMsg tr₂ stA cl pq, parseTrSignalMsg_encOut tr₂ stA cl pq, hwire_eq, hmac_eq,
    spqrHeaded_encMac tr₂ stA cl pq, hct_eq, hrk_eq, hpq_eq,
    by dsimp only [encParsedMsg]; rw [hns, hcnt_p]; simp only [BitVec.toNat_ofNat, UInt32.toNat, Nat.mod_eq_of_lt cnt.toBitVec.isLt],
    by dsimp only [encParsedMsg]; rw [hver_p]; rfl⟩, hwire_eq, hmac_eq, hrk_eq⟩
theorem faithfulInner_of_gamma_encOut_generic (i : ExternInterpretation) (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (p : PreKeyFields) (hns : stA.ns = 0) (hpn : stA.pn = 0) (hγ : gamma i S g (encOut tr₂ stA cl pq) = p.message) (hcan : InnerWireCanonicalAt 0 p) : FaithfulInner i S g (encOut tr₂ stA cl pq) p ∧ gamma i S g (encWire tr₂ stA cl pq) = p.message.take (p.message.length - 8) ∧ gamma i S g (encMac tr₂ stA cl pq) = p.message.drop (p.message.length - 8) ∧ gamma i S g (DY.DiffieHellman.dhPk stA.dhs) = p.inner.senderRatchetKey.bytes.toList := faithfulInner_of_gamma_encOut_at_generic 0 i S g tr₂ stA cl pq p hns hpn hγ hcan
theorem faithfulInner_of_gamma_encOut_at1_generic (i : ExternInterpretation) (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (p : PreKeyFields) (hns : stA.ns = 1) (hpn : stA.pn = 0) (hγ : gamma i S g (encOut tr₂ stA cl pq) = p.message) (hcan : InnerWireCanonicalAt 1 p) : FaithfulInner i S g (encOut tr₂ stA cl pq) p ∧ gamma i S g (encWire tr₂ stA cl pq) = p.message.take (p.message.length - 8) ∧ gamma i S g (encMac tr₂ stA cl pq) = p.message.drop (p.message.length - 8) ∧ gamma i S g (DY.DiffieHellman.dhPk stA.dhs) = p.inner.senderRatchetKey.bytes.toList := faithfulInner_of_gamma_encOut_at_generic 1 i S g tr₂ stA cl pq p hns hpn hγ hcan
theorem x40Idx1_mem_preKeyRepresentations
    {r : Records} {S : Sem} {g : Ghost} {ms' : List Move}
    {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {p : PreKeyFields}
    (hkek : (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂).ek.AttackerKnows (runTraceMoves r ms'))
    (hkct : (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂).ct.AttackerKnows (runTraceMoves r ms'))
    (hkmsg : (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂).msg.AttackerKnows (runTraceMoves r ms'))
    (hp : parsePreKeyWire wire3Idx1Bytes = some p)
    (hbk : p.baseKey.take 33 = ecKey (gamma compI0 S g (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂).ek))
    (hkc : p.kyberCiphertext = some (kyberKey (gamma compI0 S g (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂).ct)))
    (hmsg : gamma compI0 S g (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂).msg = p.message)
    (hcan : InnerWireCanonicalAt 1 p)
    (hout : PreKeyOuterMatches compI0 r wire3Idx1Bytes p) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁' := encSt tr₂ (iniAliceStartState tr₁ r.bob o₁) cl₁
    x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂ ∈ preKeyRepresentations compI0 r S g ms' wire3Idx1Bytes ∧
    gamma compI0 S g (encWire tr₃ stA₁' cl₂ (tr₃.length + 2)) = p.message.take (p.message.length - 8) ∧
    gamma compI0 S g (encMac tr₃ stA₁' cl₂ (tr₃.length + 2)) = p.message.drop (p.message.length - 8) ∧
    gamma compI0 S g (DY.DiffieHellman.dhPk stA₁'.dhs) = p.inner.senderRatchetKey.bytes.toList := by
  dsimp only; obtain ⟨hfi, hw, hm, hrk⟩ := faithfulInner_of_gamma_encOut_at1_generic compI0 S g tr₃ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2) p rfl rfl hmsg hcan; exact ⟨x0_mem_of_parts hkek hkct hkmsg hp hbk hkc hmsg.symm hout hfi, hw, hm, hrk⟩
theorem x81Idx1_mem_preKeyRepresentations
    {r : Records} {S : Sem} {g : Ghost} {ms' : List Move}
    {tr₁ tr₂ tr₄ : ExecTrace} {cl₁ : Nat} {p : PreKeyFields}
    (hkek : (x81Idx1 r tr₁ tr₂ tr₄ cl₁).ek.AttackerKnows (runTraceMoves r ms'))
    (hkct : (x81Idx1 r tr₁ tr₂ tr₄ cl₁).ct.AttackerKnows (runTraceMoves r ms'))
    (hkmsg : (x81Idx1 r tr₁ tr₂ tr₄ cl₁).msg.AttackerKnows (runTraceMoves r ms'))
    (hp : parsePreKeyWire wire6Idx1Bytes = some p)
    (hbk : p.baseKey.take 33 = ecKey (gamma compI0 S g (x81Idx1 r tr₁ tr₂ tr₄ cl₁).ek))
    (hkc : p.kyberCiphertext = some (kyberKey (gamma compI0 S g (x81Idx1 r tr₁ tr₂ tr₄ cl₁).ct)))
    (hmsg : gamma compI0 S g (x81Idx1 r tr₁ tr₂ tr₄ cl₁).msg = p.message)
    (hcan : InnerWireCanonicalAt 0 p)
    (hout : PreKeyOuterMatches compI0 r wire6Idx1Bytes p) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    x81Idx1 r tr₁ tr₂ tr₄ cl₁ ∈ preKeyRepresentations compI0 r S g ms' wire6Idx1Bytes ∧
    gamma compI0 S g (encWire tr₂ stA₁ cl₁ (tr₂.length + 2)) = p.message.take (p.message.length - 8) ∧
    gamma compI0 S g (encMac tr₂ stA₁ cl₁ (tr₂.length + 2)) = p.message.drop (p.message.length - 8) ∧
    gamma compI0 S g (DY.DiffieHellman.dhPk stA₁.dhs) = p.inner.senderRatchetKey.bytes.toList := by
  dsimp only; obtain ⟨hfi, hw, hm, hrk⟩ := faithfulInner_of_gamma_encOut_generic compI0 S g tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2) p rfl rfl hmsg hcan; exact ⟨x0_mem_of_parts hkek hkct hkmsg hp hbk hkc hmsg.symm hout hfi, hw, hm, hrk⟩
end Symbolic.BugInjection.Proofs.Common443.WsIdx1PreKeyRep
