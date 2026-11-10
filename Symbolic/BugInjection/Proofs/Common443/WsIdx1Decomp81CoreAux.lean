/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompSwap
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PreKeyRep
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Decomp
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompCore
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Mem
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp40

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Core
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents
open DY.Libsignal (HwBytes) open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443
export Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc (invert_send2_move_opt encrypt_state_of_lastSent_ne_none)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp40 (invert_send2_move seg38_eq decomp40_last)
section Stale
open ByteSpecs Symbolic.BugInjection.Proofs.Common443.WsIdx1PreKeyRep Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open DY.Libsignal.Refinement (paddedVarint encodeField PbValue encodeWith canonicalVariation WireFields FieldItem knownValue?)
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp40 (paddedVarint_zero_inj encodeField_bytes_inj not_gamma_encOut_ns_at not_gamma_encOut_ns0_at1)
theorem not_gamma_encOut_ns1_at0 (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (p : PreKeyFields) (hns : stA.ns = 1) (hpn : stA.pn = 0) (hγ : gamma compI0 S g (encOut tr₂ stA cl pq) = p.message) (hcan : InnerWireCanonicalAt 0 p) : False := by
  refine not_gamma_encOut_ns_at S g tr₂ stA cl pq 1 0 p hns hpn hγ hcan (fun r1 r2 => ?_)
  have h1 : (encodeField 2 0 0 (PbValue.varint (1 + 2 ^ 32 * 0)) ++ r1).take 2 = [0x10#8, 0x01#8] := by rw [encodeField, paddedVarint.eq_def (2 * 8 + 0) 0, paddedVarint.eq_def (1 + 2 ^ 32 * 0) 0]; rfl
  have h2 : (encodeField 2 0 0 (PbValue.varint (0 + 2 ^ 32 * 0)) ++ r2).take 2 = [0x10#8, 0x00#8] := by rw [encodeField, paddedVarint.eq_def (2 * 8 + 0) 0, paddedVarint.eq_def (0 + 2 ^ 32 * 0) 0]; rfl
  change (encodeField 2 0 0 (PbValue.varint (1 + 2 ^ 32 * 0)) ++ r1).take 2 ≠ _; rw [h1, h2]; decide
theorem not_gamma_encOut_ns2_at0 (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (p : PreKeyFields) (hns : stA.ns = 2) (hpn : stA.pn = 0) (hγ : gamma compI0 S g (encOut tr₂ stA cl pq) = p.message) (hcan : InnerWireCanonicalAt 0 p) : False := by
  refine not_gamma_encOut_ns_at S g tr₂ stA cl pq 2 0 p hns hpn hγ hcan (fun r1 r2 => ?_)
  have h1 : (encodeField 2 0 0 (PbValue.varint (2 + 2 ^ 32 * 0)) ++ r1).take 2 = [0x10#8, 0x02#8] := by rw [encodeField, paddedVarint.eq_def (2 * 8 + 0) 0, paddedVarint.eq_def (2 + 2 ^ 32 * 0) 0]; rfl
  have h2 : (encodeField 2 0 0 (PbValue.varint (0 + 2 ^ 32 * 0)) ++ r2).take 2 = [0x10#8, 0x00#8] := by rw [encodeField, paddedVarint.eq_def (2 * 8 + 0) 0, paddedVarint.eq_def (0 + 2 ^ 32 * 0) 0]; rfl
  change (encodeField 2 0 0 (PbValue.varint (2 + 2 ^ 32 * 0)) ++ r1).take 2 ≠ _; rw [h1, h2]; decide
end Stale
section Concrete
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80 (wire80Fast sendAt80_eq_fast)
attribute [local irreducible] Symbolic.BugInjection.hexBytes
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp40 (sendAt ptAt rngAt rs0 take38_shape seg38_shape rs0_length rs0_map_kind rs0_kind sendAt39_eq_wireAt40 wire0Chars send37Chars wire0Str_eq send37Str_eq wire0Fast send37Fast wireAt0_eq_fast sendAt37_eq_fast wire0Fast_byte4 wireAt0_byte4 send37Fast_head? sendAt37_head? send37Fast_len sendAt37_len wire40Fast_len sendAt39_len send37Fast_parses sendAt37_parses send37Fast_hasTag4 sendAt37_hasTag4 send37Fast_baseKey send37Fast_kyberCiphertext wire40Fast_baseKey_full wire40Fast_kyberCiphertext checkCanonAt canon_of_checkCanonAt check_wire40Fast wireAt40_canon sendAt37_baseKey sendAt37_kyberCiphertext wireAt40_baseKey_full wireAt40_kyberCiphertext)
def acceptAt (n : Nat) : HwBytes :=
  match ((Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.accept b) => b | _ => []
def rs4 : List MachineEvent := (((Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.trace).drop 43).take 35).tail
theorem seg40_shape : seg 40 3 = [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)] := rfl
theorem seg43_shape : seg 43 35 = .recv (wireAt 43) :: rs4 := rfl
theorem seg78_shape : seg 78 3 = [.pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80)] := rfl
theorem rs4_length : rs4.length = 34 := rfl
theorem rs4_map_kind : rs4.map eventKind = List.replicate 34 .rng := rfl
theorem rs4_kind : ∀ e ∈ rs4, eventKind e = .rng := fun _ he => List.eq_of_mem_replicate (rs4_map_kind ▸ List.mem_map_of_mem he)
def wire43Chars : List Char := tf_chars_of_hex (wireAt 43)
theorem wireAt43_eq_hex : wireAt 43 = Symbolic.BugInjection.hexBytes (tf_str_of_hex (wireAt 43)) := rfl
set_option maxRecDepth 200000 in theorem wire43Str_eq : (tf_str_of_hex (wireAt 43)) = String.ofList wire43Chars := rfl
def wire43Fast : HwBytes := Symbolic.BugInjection.hexBytes.go hexDigit wire43Chars
theorem wireAt43_eq_fast : wireAt 43 = wire43Fast := by rw [wireAt43_eq_hex, wire43Str_eq, hexBytes_ofList]; rfl
theorem sendAt80_eq_fast' : sendAt 80 = wire80Fast := sendAt80_eq_fast
set_option maxRecDepth 200000 in theorem wire43Fast_byte4 : wire43Fast[4]? ≠ some 1#8 := by decide +kernel
theorem wireAt43_byte4 : (wireAt 43)[4]? ≠ some 1#8 := by rw [wireAt43_eq_fast]; exact wire43Fast_byte4
theorem sendAt80_len : (sendAt 80).length < 2 ^ 63 := Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80.sendAt80_length_lt
theorem sendAt80_head? : (sendAt 80).head? = some 0x03#8 := Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80.sendAt80_head?
theorem sendAt80_parses : ∃ q, parsePreKeyWire (sendAt 80) = some q := Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80.sendAt80_parses
set_option maxRecDepth 200000 in theorem wire80Fast_hasTag4 : CompRBobInit.hasTag4 wire80Fast = false := by decide +kernel
theorem sendAt80_hasTag4 : CompRBobInit.hasTag4 (sendAt 80) = false := by rw [sendAt80_eq_fast']; exact wire80Fast_hasTag4
theorem rs4_eq_cons : rs4 = .rng (rngAt 44) :: rs4.tail := rfl
set_option maxRecDepth 200000 in theorem clamp_rng44_lookup : compLookupPub (clamp (rngAt 44)) = WsIdx1CensusDefs.ek2PubKey := by decide +kernel
set_option maxRecDepth 200000 in theorem rs4_coinHeads_eq : CompRX0Gamma.coinHeads (rs4.tail.take 32) = compKyberE2 := by decide +kernel
set_option maxRecDepth 200000 in theorem compKyberEncaps_e2_take1568 : (compKyberEncaps compKyberE2).take 1568 = compKyberCt2 := by decide +kernel
set_option maxRecDepth 200000 in theorem wire80Fast_baseKey_full : (parsePreKeyWire wire80Fast).map (·.baseKey) = some (ecKey WsIdx1CensusDefs.ek2PubKey) := by decide +kernel
set_option maxRecDepth 200000 in theorem wire80Fast_kyberCiphertext : (parsePreKeyWire wire80Fast).bind (·.kyberCiphertext) = some (kyberKey compKyberCt2) := by decide +kernel
set_option maxRecDepth 200000 in theorem wire81Fast_kyberCiphertext : (parsePreKeyWire wire81Fast).bind (·.kyberCiphertext) = some (kyberKey compKyberCt2) := by decide +kernel
set_option maxRecDepth 200000 in theorem wire81Fast_msg_eq_send37 : (parsePreKeyWire wire81Fast).map (·.message) = (parsePreKeyWire send37Fast).map (·.message) := by decide +kernel
set_option maxRecDepth 200000 in theorem check_wire81Fast : checkCanonAt 0 wire81Fast = true := by decide +kernel
set_option maxRecDepth 200000 in theorem check_send37Fast : checkCanonAt 0 send37Fast = true := by decide +kernel
set_option maxRecDepth 200000 in theorem check_wire80Fast : checkCanonAt 0 wire80Fast = true := by decide +kernel
theorem wireAt81_canon {p : PreKeyFields} (hp : parsePreKeyWire (wireAt 81) = some p) : WsIdx1PreKeyRep.InnerWireCanonicalAt 0 p := by rw [wireAt81_eq_fast] at hp; exact canon_of_checkCanonAt check_wire81Fast p hp
theorem sendAt80_baseKey_full {q : PreKeyFields} (hq : parsePreKeyWire (sendAt 80) = some q) : q.baseKey = ecKey WsIdx1CensusDefs.ek2PubKey := by
  have h1 := wire80Fast_baseKey_full; rw [sendAt80_eq_fast'] at hq; rw [hq] at h1; exact Option.some.inj h1
theorem sendAt80_kyberCiphertext {q : PreKeyFields} (hq : parsePreKeyWire (sendAt 80) = some q) : q.kyberCiphertext = some (kyberKey compKyberCt2) := by
  have h1 := wire80Fast_kyberCiphertext; rw [sendAt80_eq_fast'] at hq; rw [hq] at h1; exact h1
theorem wireAt81_kyberCiphertext {p : PreKeyFields} (hp : parsePreKeyWire (wireAt 81) = some p) : p.kyberCiphertext = some (kyberKey compKyberCt2) := by
  have h1 := wire81Fast_kyberCiphertext; rw [wireAt81_eq_fast] at hp; rw [hp] at h1; exact h1
theorem wireAt81_message_eq_sendAt37 {p q : PreKeyFields} (hp : parsePreKeyWire (wireAt 81) = some p) (hq : parsePreKeyWire (sendAt 37) = some q) : p.message = q.message := by
  have h1 := wire81Fast_msg_eq_send37; rw [wireAt81_eq_fast] at hp; rw [sendAt37_eq_fast] at hq; rw [hp, hq] at h1; exact Option.some.inj h1
theorem sendAt37_canon {p : PreKeyFields} (hp : parsePreKeyWire (sendAt 37) = some p) : WsIdx1PreKeyRep.InnerWireCanonicalAt 0 p := by rw [sendAt37_eq_fast] at hp; exact canon_of_checkCanonAt check_send37Fast p hp
theorem sendAt80_canon {p : PreKeyFields} (hp : parsePreKeyWire (sendAt 80) = some p) : WsIdx1PreKeyRep.InnerWireCanonicalAt 0 p := by rw [sendAt80_eq_fast'] at hp; exact canon_of_checkCanonAt check_wire80Fast p hp
set_option maxRecDepth 200000 in
theorem wire80Fast_srk_ne_rng41 :
    (parsePreKeyWire wire80Fast).map (fun q => q.inner.senderRatchetKey.bytes.toList) ≠
      some (compLookupPub (clamp (rngAt 41))) := by decide +kernel
set_option maxRecDepth 200000 in
theorem wire80Fast_srk_ne_send37 :
    (parsePreKeyWire wire80Fast).map (fun q => q.inner.senderRatchetKey.bytes.toList) ≠
      (parsePreKeyWire send37Fast).map (fun q => q.inner.senderRatchetKey.bytes.toList) := by decide +kernel
theorem sendAt80_srk_ne_rng41 {q : PreKeyFields} (hq : parsePreKeyWire (sendAt 80) = some q) (h : q.inner.senderRatchetKey.bytes.toList = compLookupPub (clamp (rngAt 41))) : False := by apply wire80Fast_srk_ne_rng41; rw [sendAt80_eq_fast'] at hq; rw [hq, Option.map_some, h]
theorem sendAt80_srk_ne_sendAt37 {q₅ q₁ : PreKeyFields} (hq₅ : parsePreKeyWire (sendAt 80) = some q₅) (hq₁ : parsePreKeyWire (sendAt 37) = some q₁) (h : q₅.inner.senderRatchetKey.bytes.toList = q₁.inner.senderRatchetKey.bytes.toList) : False := by apply wire80Fast_srk_ne_send37; rw [sendAt80_eq_fast'] at hq₅; rw [sendAt37_eq_fast] at hq₁; rw [hq₅, hq₁, Option.map_some, Option.map_some, h]
end Concrete
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Core
