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
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Decomp
public import Symbolic.BugInjection.Proofs.Common443.CliCoinSplit
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompCore
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Mem
public import Symbolic.BugInjection.Proofs.Common443.CompRX0SS38
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs
public import Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp40
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents
open DY.Libsignal (HwBytes) open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443
theorem invert_send2_move {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr : ExecTrace} {m : Move} {pt w : HwBytes} (hm : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .send w] (m.vis tr)) (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) : ∃ me sIdx cl pq wr, m = .encrypt me sIdx cl pq (some wr) ∧ lastSent tr (m.next tr) ≠ none ∧ List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .send w] (encVis tr (m.next tr) (some wr) true) := by
  obtain ⟨me, sIdx, cl, pq, wrap, rfl, hls, hwn, hvis⟩ := invert_send2_move_opt hm
  cases wrap with
  | none => exact absurd (hwn rfl) hw
  | some wr => exact ⟨me, sIdx, cl, pq, wr, rfl, hls, hvis⟩
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
theorem seg38_eq : ∃ pt₂ w₂, seg 38 2 = [.pt pt₂, .send w₂] := ⟨_, _, rfl⟩
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
theorem decomp40_last {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {τ₃₈ b2 : List MachineEvent}
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms (τ₃₈ ++ b2)) :
    ∃ (ms₁ pre₂ post : List Move) (m₂ : Move),
      ms = ms₁ ++ pre₂ ++ m₂ :: post ∧
      Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₁ τ₃₈ ∧
      MovesFrom InvisibleNoEffect (runTraceMoves r ms₁) pre₂ ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) b2 (m₂.vis (runTraceMoves r (ms₁ ++ pre₂))) ∧
      MovesFrom InvisibleNoEffect (m₂.next (runTraceMoves r (ms₁ ++ pre₂))) post := by
  obtain ⟨pieces₂, _, _, hb2⟩ := CliCoinSplit.coinSplit_send_exit0_inv hc2
  have hhead : ∀ e ∈ b2.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; simp [hb2] at he; subst he; exact Or.inr rfl
  obtain ⟨ms₁, δ, hms, hmp₁, hfor⟩ := matchedPrefix6_split hmp hhead (matchedPrefix6_prefix_reachable hmp)
  have hB : XplBlock6 compI0 r S g ms₁ δ _ b2 := ⟨hmp₁, hms ▸ hmp.2.1, hfor⟩
  have htail : ∀ e ∈ b2.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; simp only [hb2, List.tail_cons, List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨_, _, rfl⟩ | rfl <;> { dsimp [eventKind]; decide }
  obtain ⟨pre₁, m, post₁, rfl, hpre, ⟨-, -, hm⟩, hpost⟩ := xpl6_oneMove hB hhead (by simp [hb2]) htail
  refine ⟨ms₁, pre₁, post₁, m, by rw [hms]; simp, hmp₁, hpre,
    by rw [CompPrefixInvStruct.runTrace_append]; exact hm,
    by rw [CompPrefixInvStruct.runTrace_append]; exact hpost⟩
section Stale
open ByteSpecs Symbolic.BugInjection.Proofs.Common443.WsIdx1PreKeyRep Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open DY.Libsignal.Refinement (paddedVarint encodeField PbValue encodeWith canonicalVariation WireFields FieldItem knownValue?)
theorem paddedVarint_zero_inj :
    ∀ (s n m : Nat) (r₁ r₂ : HwBytes), n < s → paddedVarint n 0 ++ r₁ = paddedVarint m 0 ++ r₂ → n = m ∧ r₁ = r₂
  | 0, _, _, _, _, hs, _ => absurd hs (Nat.not_lt_zero _)
  | s + 1, n, m, r₁, r₂, hs, h => by
    rw [paddedVarint.eq_def n 0, paddedVarint.eq_def m 0] at h
    simp only [and_true] at h
    by_cases hn : n < 128 <;> by_cases hm : m < 128
    · simp only [hn, hm, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
      have h1 := congrArg BitVec.toNat h.1
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1; exact ⟨by omega, h.2⟩
    · simp only [hn, hm, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
      have h1 := congrArg BitVec.toNat h.1
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1; omega
    · simp only [hn, hm, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
      have h1 := congrArg BitVec.toNat h.1
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1; omega
    · simp only [hn, hm, ↓reduceIte, List.cons_append, List.cons.injEq] at h
      have h1 := congrArg BitVec.toNat h.1
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1
      have ⟨hdiv, hr⟩ := paddedVarint_zero_inj s (n / 128) (m / 128) r₁ r₂ (by omega) h.2
      exact ⟨by omega, hr⟩
theorem encodeField_bytes_inj {t : Nat} {b₁ b₂ r₁ r₂ : HwBytes} (h : encodeField t 0 0 (.bytes b₁) ++ r₁ = encodeField t 0 0 (.bytes b₂) ++ r₂) : b₁ = b₂ ∧ r₁ = r₂ := by
  simp only [encodeField, List.append_assoc] at h
  have ⟨hlen, hbr⟩ := paddedVarint_zero_inj (b₁.length + 1) b₁.length b₂.length
    (b₁ ++ r₁) (b₂ ++ r₂) (by omega) (List.append_cancel_left h)
  exact List.append_inj hbr hlen
theorem not_gamma_encOut_ns_at (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (ns : UInt32) (c : Nat) (p : PreKeyFields) (hns : stA.ns = ns) (hpn : stA.pn = 0) (hγ : gamma compI0 S g (encOut tr₂ stA cl pq) = p.message) (hcan : InnerWireCanonicalAt c p) (hneq : ∀ r1 r2 : HwBytes, (encodeField 2 0 0 (PbValue.varint (ns.toNat + 2 ^ 32 * 0)) ++ r1).take 2 ≠ (encodeField 2 0 0 (PbValue.varint (c + 2 ^ 32 * 0)) ++ r2).take 2) : False := by
  obtain ⟨_hcnt_p, _hver_p, hwire_p⟩ := hcan
  let m := randTerm tr₂.length 32
  let coins := randTerm (tr₂.length + 1) cl
  let pqMsg := (DY.Spqr.spqrSend stA.spqr coins).2.2
  let keys := DY.Libsignal.TripleRatchet.trMsgKeys (encSalt tr₂ stA cl pq) (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2
  let ct := DY.SymEnc.symEnc keys.cipherKey keys.iv m
  let w := encWire tr₂ stA cl pq
  let mac := encMac tr₂ stA cl pq
  have hγ_split : gamma compI0 S g w ++ gamma compI0 S g mac = p.message := hγ ▸ (CompFreshDistinct.gamma_concat_eq compI0 S g w mac).symm; have hmac_len : (gamma compI0 S g mac).length = 8 := gamma_encMac_length compI0 S g tr₂ stA cl pq
  have hlen_msg : p.message.length - 8 = (gamma compI0 S g w).length := by rw [← hγ_split, List.length_append, hmac_len]; omega
  have hwire_eq : gamma compI0 S g w = p.message.take (p.message.length - 8) := by rw [hlen_msg, ← hγ_split, List.take_left]
  have htr : trWireBytes (g.addr w) canonicalVariation ⟨4, gamma compI0 S g (DY.DiffieHellman.dhPk stA.dhs), ns.toNat, 0, gamma compI0 S g ct⟩ (gamma compI0 S g pqMsg) = innerWirePrefixAt c p ++ (p.message.take (p.message.length - 8)).drop (innerWirePrefixAt c p).length := by
    have hw_unfold : w = DY.TrWire.trWireMsg 4 (DY.DiffieHellman.dhPk stA.dhs) ns 0 ct pqMsg canonicalVariation := by dsimp only [w, encWire, DY.Libsignal.TripleRatchet.trHonestWireMsg]; rw [hns, hpn]; rfl
    have hγw := CompFreshDistinct.gamma_trWire_eq compI0 S g 4 (DY.DiffieHellman.dhPk stA.dhs) ns 0 ct pqMsg canonicalVariation; rw [← hw_unfold] at hγw; exact hγw.symm.trans (hwire_eq.trans hwire_p)
  rw [trWireBytes_canonical, innerWirePrefixAt, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.canonicalVariation_eq] at htr; simp only [encodeWith, List.flatMap_cons, List.flatMap_nil, FieldItem.encode, knownValue?, Option.map_some, Option.getD_some, List.cons_append, List.append_nil, List.append_assoc, List.cons.injEq, true_and] at htr; obtain ⟨_, h2⟩ := encodeField_bytes_inj htr
  exact hneq _ _ (congrArg (fun l => l.take 2) h2)
theorem not_gamma_encOut_ns0_at1 (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (p : PreKeyFields) (hns : stA.ns = 0) (hpn : stA.pn = 0) (hγ : gamma compI0 S g (encOut tr₂ stA cl pq) = p.message) (hcan : InnerWireCanonicalAt 1 p) : False := by
  refine not_gamma_encOut_ns_at S g tr₂ stA cl pq 0 1 p hns hpn hγ hcan (fun r1 r2 => ?_)
  have h1 : (encodeField 2 0 0 (PbValue.varint (0 + 2 ^ 32 * 0)) ++ r1).take 2 = [0x10#8, 0x00#8] := by rw [encodeField, paddedVarint.eq_def (2 * 8 + 0) 0, paddedVarint.eq_def (0 + 2 ^ 32 * 0) 0]; rfl
  have h2 : (encodeField 2 0 0 (PbValue.varint (1 + 2 ^ 32 * 0)) ++ r2).take 2 = [0x10#8, 0x01#8] := by rw [encodeField, paddedVarint.eq_def (2 * 8 + 0) 0, paddedVarint.eq_def (1 + 2 ^ 32 * 0) 0]; rfl
  change (encodeField 2 0 0 (PbValue.varint (0 + 2 ^ 32 * 0)) ++ r1).take 2 ≠ _; rw [h1, h2]; decide
end Stale
section Concrete
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
attribute [local irreducible] Symbolic.BugInjection.hexBytes
def sendAt (n : Nat) : HwBytes :=
  match ((Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.send b) => b | _ => []
def ptAt (n : Nat) : HwBytes :=
  match ((Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.pt b) => b | _ => []
def rngAt (n : Nat) : HwBytes :=
  match ((Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.rng b) => b | _ => []
def rs0 : List MachineEvent := ((Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.trace).take 35).tail
theorem take38_shape : (Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.trace).take 38 = (.recv (wireAt 0) :: rs0) ++ [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] := rfl
theorem seg38_shape : seg 38 2 = [.pt (ptAt 38), .send (sendAt 39)] := rfl
theorem rs0_length : rs0.length = 34 := rfl
theorem rs0_map_kind : rs0.map eventKind = List.replicate 34 .rng := rfl
theorem rs0_kind : ∀ e ∈ rs0, eventKind e = .rng := fun _ he => List.eq_of_mem_replicate (rs0_map_kind ▸ List.mem_map_of_mem he)
theorem sendAt39_eq_wireAt40 : sendAt 39 = wireAt 40 := rfl
def wire0Chars : List Char := tf_chars_of_hex (wireAt 0)
def send37Chars : List Char := tf_chars_of_hex (sendAt 37)
theorem wireAt0_eq_hex : wireAt 0 = hexBytes (tf_str_of_hex (wireAt 0)) := rfl
theorem sendAt37_eq_hex : sendAt 37 = hexBytes (tf_str_of_hex (sendAt 37)) := rfl
set_option maxRecDepth 200000 in theorem wire0Str_eq : (tf_str_of_hex (wireAt 0)) = String.ofList wire0Chars := rfl
set_option maxRecDepth 200000 in theorem send37Str_eq : (tf_str_of_hex (sendAt 37)) = String.ofList send37Chars := rfl
def wire0Fast : HwBytes := hexBytes.go hexDigit wire0Chars
def send37Fast : HwBytes := hexBytes.go hexDigit send37Chars
theorem wireAt0_eq_fast : wireAt 0 = wire0Fast := by rw [wireAt0_eq_hex, wire0Str_eq, hexBytes_ofList]; rfl
theorem sendAt37_eq_fast : sendAt 37 = send37Fast := by rw [sendAt37_eq_hex, send37Str_eq, hexBytes_ofList]; rfl
set_option maxRecDepth 200000 in theorem wire0Fast_byte4 : wire0Fast[4]? ≠ some 1#8 := by decide +kernel
theorem wireAt0_byte4 : (wireAt 0)[4]? ≠ some 1#8 := by rw [wireAt0_eq_fast]; exact wire0Fast_byte4
set_option maxRecDepth 200000 in theorem send37Fast_head? : send37Fast.head? = some 0x03#8 := by decide +kernel
theorem sendAt37_head? : (sendAt 37).head? = some 0x03#8 := by rw [sendAt37_eq_fast]; exact send37Fast_head?
set_option maxRecDepth 200000 in theorem send37Fast_len : send37Fast.length < 2 ^ 63 := by decide +kernel
theorem sendAt37_len : (sendAt 37).length < 2 ^ 63 := by rw [sendAt37_eq_fast]; exact send37Fast_len
set_option maxRecDepth 200000 in theorem wire40Fast_len : wire40Fast.length < 2 ^ 63 := by decide +kernel
theorem sendAt39_len : (sendAt 39).length < 2 ^ 63 := by rw [sendAt39_eq_wireAt40, wireAt40_eq_fast]; exact wire40Fast_len
set_option maxRecDepth 200000 in theorem send37Fast_parses : (parsePreKeyWire send37Fast).isSome = true := by decide +kernel
theorem sendAt37_parses : ∃ q, parsePreKeyWire (sendAt 37) = some q := by rw [sendAt37_eq_fast]; exact Option.isSome_iff_exists.mp send37Fast_parses
set_option maxRecDepth 200000 in theorem send37Fast_hasTag4 : CompRBobInit.hasTag4 send37Fast = false := by decide +kernel
theorem sendAt37_hasTag4 : CompRBobInit.hasTag4 (sendAt 37) = false := by rw [sendAt37_eq_fast]; exact send37Fast_hasTag4
theorem rs0_eq_cons : rs0 = .rng (rngAt 1) :: rs0.tail := rfl
set_option maxRecDepth 200000 in theorem clamp_rng1_lookup : compLookupPub (clamp (rngAt 1)) = WsIdx1CensusDefs.ek1PubKey := by decide +kernel
set_option maxRecDepth 200000 in theorem rs0_coinHeads_eq : CompRX0Gamma.coinHeads (rs0.tail.take 32) = compKyberE1 := by decide +kernel
set_option maxRecDepth 200000 in theorem compKyberEncaps_e1_take1568 : (compKyberEncaps compKyberE1).take 1568 = compKyberCt1 := by decide +kernel
set_option maxRecDepth 200000 in
theorem send37Fast_baseKey :
    (parsePreKeyWire send37Fast).map (·.baseKey) = some (ecKey WsIdx1CensusDefs.ek1PubKey) := by decide +kernel
set_option maxRecDepth 200000 in
theorem send37Fast_kyberCiphertext :
    (parsePreKeyWire send37Fast).bind (·.kyberCiphertext) = some (kyberKey compKyberCt1) := by decide +kernel
set_option maxRecDepth 200000 in
theorem wire40Fast_baseKey_full :
    (parsePreKeyWire wire40Fast).map (·.baseKey) = some (ecKey WsIdx1CensusDefs.ek1PubKey) := by decide +kernel
set_option maxRecDepth 200000 in
theorem wire40Fast_kyberCiphertext :
    (parsePreKeyWire wire40Fast).bind (·.kyberCiphertext) = some (kyberKey compKyberCt1) := by decide +kernel
open DY.Libsignal.Refinement (encodeField encodeWith canonicalVariation)
def canonicalVariationFast : DY.Libsignal.Refinement.EncodingVariation := ⟨4, [], 0, 0, [.known 1 0 0, .known 2 0 0, .known 3 0 0, .known 4 0 0]⟩
theorem canonicalVariationFast_eq : canonicalVariationFast = canonicalVariation :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.canonicalVariation_eq.symm
def innerWirePrefixAtFast (c : Nat) (p : PreKeyFields) : HwBytes := encodeWith canonicalVariationFast ⟨4, p.inner.senderRatchetKey.bytes.toList, c, 0, p.inner.ciphertext⟩ ++ encodeField 5 0 0 (.bytes p.inner.pqRatchet)
theorem innerWirePrefixAtFast_eq (c : Nat) (p : PreKeyFields) : innerWirePrefixAtFast c p = WsIdx1PreKeyRep.innerWirePrefixAt c p := by
  unfold innerWirePrefixAtFast WsIdx1PreKeyRep.innerWirePrefixAt; rw [canonicalVariationFast_eq]
def checkCanonAt (c : Nat) (w : HwBytes) : Bool :=
  match parsePreKeyWire w with
  | none => false
  | some p =>
    decide (p.inner.counter = BitVec.ofNat 32 c) &&
    decide (p.inner.messageVersion = 4) &&
    decide (p.message.take (p.message.length - 8) = innerWirePrefixAtFast c p ++ (p.message.take (p.message.length - 8)).drop (innerWirePrefixAtFast c p).length)
theorem canon_of_checkCanonAt {c : Nat} {w : HwBytes} (h : checkCanonAt c w = true) (p : PreKeyFields) (hp : parsePreKeyWire w = some p) : WsIdx1PreKeyRep.InnerWireCanonicalAt c p := by unfold checkCanonAt at h; rw [hp] at h; simp only [Bool.and_eq_true, decide_eq_true_eq, innerWirePrefixAtFast_eq] at h; exact ⟨h.1.1, h.1.2, h.2⟩
set_option maxRecDepth 200000 in theorem check_wire40Fast : checkCanonAt 1 wire40Fast = true := by decide +kernel
theorem wireAt40_canon {p : PreKeyFields} (hp : parsePreKeyWire (wireAt 40) = some p) : WsIdx1PreKeyRep.InnerWireCanonicalAt 1 p := by rw [wireAt40_eq_fast] at hp; exact canon_of_checkCanonAt check_wire40Fast p hp
set_option maxRecDepth 200000 in theorem checkOuter_wire40Fast : CompFitsNames.checkPreKeyOuter Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 wire40Fast = true := by decide +kernel
theorem wireAt40_outer {r : Records} {p : PreKeyFields} (hf : Symbolic.BugInjection.compFits Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 r) (hp : parsePreKeyWire (wireAt 40) = some p) : CompRPreKeyWire.PreKeyOuterMatches compI0 r (wireAt 40) p := by rw [wireAt40_eq_fast] at hp ⊢; exact CompFitsNames.preKeyOuterMatches_of_check hf hp checkOuter_wire40Fast
theorem sendAt37_baseKey {q : PreKeyFields} (hq : parsePreKeyWire (sendAt 37) = some q) : q.baseKey = ecKey WsIdx1CensusDefs.ek1PubKey := by
  have h1 := send37Fast_baseKey; rw [sendAt37_eq_fast] at hq; rw [hq] at h1; exact Option.some.inj h1
theorem sendAt37_kyberCiphertext {q : PreKeyFields} (hq : parsePreKeyWire (sendAt 37) = some q) : q.kyberCiphertext = some (kyberKey compKyberCt1) := by
  have h1 := send37Fast_kyberCiphertext; rw [sendAt37_eq_fast] at hq; rw [hq] at h1; exact h1
theorem wireAt40_baseKey_full {q : PreKeyFields} (hq : parsePreKeyWire (wireAt 40) = some q) : q.baseKey = ecKey WsIdx1CensusDefs.ek1PubKey := by
  have h1 := wire40Fast_baseKey_full; rw [wireAt40_eq_fast] at hq; rw [hq] at h1; exact Option.some.inj h1
theorem wireAt40_kyberCiphertext {q : PreKeyFields} (hq : parsePreKeyWire (wireAt 40) = some q) : q.kyberCiphertext = some (kyberKey compKyberCt1) := by
  have h1 := wire40Fast_kyberCiphertext; rw [wireAt40_eq_fast] at hq; rw [hq] at h1; exact h1
end Concrete
theorem sendMatches_of_encVis2 {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr tr' : ExecTrace} {e c' : Nat} {o : DY.Bytes} {pt w : HwBytes} (hls : lastSent tr tr' = some o) (hm : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .send w] (encVis tr tr' (some (e, c')) true)) : CompRPreKeyWire.SendMatchesMoves i r S g w (received tr [e, c'] ++ [o]) := by
  have hmem : MachineEvent.send w ∈ ([.pt pt, .send w] : List MachineEvent) := by simp
  obtain ⟨v, hv, hev⟩ := xpl_forall₂_mem_left hm (.send w) hmem; have hvk : v.kind = .send := xpl_kind_of_matches hev; unfold encVis at hv; simp only [↓reduceIte, List.mem_append] at hv
  rcases hv with hd | hsnd
  · rcases encDraws_kind _ hd with hk | hk <;> (rw [hvk] at hk; cases hk)
  · unfold encSend at hsnd; rw [hls, List.mem_singleton] at hsnd; subst hsnd; exact hev.2
theorem trStateStoredAt_encNextTr' (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : ((encNextTr tr₂ me sIdx stA cl pq).at? (tr₂.length + 5) : Option TRStEntry) = some (TRStE me (encSt tr₂ stA cl)) :=
  CompRVariantFree38.trStateStoredAt_encNextTr tr₂ me sIdx stA cl pq
theorem at?_trSt_encNextTr' (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq j : Nat) : ((encNextTr tr₂ me sIdx stA cl pq).at? j : Option TRStEntry) = if j = tr₂.length + 5 then some (TRStE me (encSt tr₂ stA cl)) else (tr₂.at? j : Option TRStEntry) :=
  CompRVariantFree38.at?_trSt_encNextTr tr₂ me sIdx stA cl pq j
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
theorem call2_pin {r : Records} {S : Sem} {g : Ghost} {tr₃ : ExecTrace} {m : Move} {b2 : List MachineEvent} {j₀ j₁ pq : Nat} {me₁ : Participant} {st₀ st₁ : DY.Libsignal.TripleRatchet.TRState} (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2) (hat : ∀ j, (tr₃.at? j : Option TRStEntry) = if j = j₁ then some (TRStE me₁ st₁) else if j = j₀ then some (TRStE r.alice st₀) else none) (hns₀ : st₀.ns = 0) (hpn₀ : st₀.pn = 0) (hpq : ∀ me sIdx cl pq' wr, m = .encrypt me sIdx cl pq' wr → pq' = pq) (hpq' : pq = tr₃.length + 2) (hm : List.Forall₂ (EventMatchesEntry compI0 r S g) b2 (m.vis tr₃)) (hw : (wireAt 40).head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) (hlen : (wireAt 40).length < 2 ^ 63) {p : PreKeyFields} (hp : parsePreKeyWire (wireAt 40) = some p) : ∃ cl e c', m = .encrypt me₁ j₁ cl pq (some (e, c')) ∧ m.next tr₃ = encNextTr tr₃ me₁ j₁ st₁ cl pq ∧ st₁.ns ≠ DY.Libsignal.TripleRatchet.u32Max ∧ CompRPreKeyWire.SendMatchesMoves compI0 r S g (wireAt 40) (received tr₃ [e, c'] ++ [encOut tr₃ st₁ cl pq]) := by
  obtain ⟨pieces₂, _, _, hb2⟩ := CliCoinSplit.coinSplit_send_exit0_inv hc2
  have hmem_send : MachineEvent.send (wireAt 40) ∈ b2 := by
    have : WsIdx1CensusDefs.sendAt 39 = wireAt 40 := rfl
    simp [hb2, this]
  obtain ⟨me, sIdx, cl, pq₀, wrap, rfl, hls, hwrap_none, hvis⟩ := CliCoinSplit.invert_send_move_split hmem_send hm
  cases wrap with
  | none => exact absurd (hwrap_none rfl) hw
  | some wr =>
    rcases wr with ⟨e, c'⟩
    have hpq₀ : pq₀ = pq := hpq _ _ _ _ _ rfl; subst hpq₀; obtain ⟨st, hst, hns⟩ := encrypt_state_of_lastSent_ne_none hls; have hst' := hst.symm.trans (hat sIdx)
    by_cases h1 : sIdx = j₁
    · subst h1; simp at hst'; obtain ⟨rfl, rfl⟩ := hst'
      exact ⟨cl, e, c', rfl, encrypt_next_eq_encNextTr_of_ownSalt hst hns hpq', hns, CliCoinSplit.sendMatches_of_encVis_split hc2 (encrypt_lastSent_eq_some_encOut hst hns hpq') hvis⟩
    · by_cases h0 : sIdx = j₀
      · subst h0; simp [h1] at hst'; obtain ⟨rfl, rfl⟩ := hst'; exfalso
        have hsm := CliCoinSplit.sendMatches_of_encVis_split hc2 (encrypt_lastSent_eq_some_encOut hst hns hpq') hvis; obtain ⟨_, _, -, -, -, hmsg⟩ := CompRX0Mem.sendMatches_append_inv hsm hlen hp; exact not_gamma_encOut_ns0_at1 S g tr₃ _ cl _ p hns₀ hpn₀ hmsg.symm (wireAt40_canon hp)
      · simp [h1, h0] at hst'
theorem runMoves_cons_fst₀ (m : Move) (ms : List Move) (tr : ExecTrace) : (runMoves (m :: ms) tr).1 = (runMoves ms (m.next tr)).1 := rfl
set_option maxRecDepth 200000 in
theorem idx1_bobId_secretIdx :
    compSecretIdx (clamp Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup.bobId) = some ⟨4, by decide⟩ := by decide +kernel
set_option maxRecDepth 200000 in
theorem idx1_spk_secretIdx :
    compSecretIdx (clamp Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup.spk) = some ⟨3, by decide⟩ := by decide +kernel
theorem aliceStartState_ns_zero (tr₁ : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : (aliceStartState tr₁ b o).ns = 0 := rfl
theorem aliceStartState_pn_zero (tr₁ : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : (aliceStartState tr₁ b o).pn = 0 := rfl
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
theorem pia_x0_decomp_legacy_split {r : Records} {S : Sem} {g : Ghost}
    {ms : List Move} {bun : HwBytes} {rs : List MachineEvent} {pt c w : HwBytes}
    {blk₂ : List MachineEvent}
    (hNe : r.alice ≠ r.bob)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt pt, .rng c, .send w] blk₂)
    (hmp' : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms ((.recv bun :: rs) ++ blk₂))
    (hrs_len : rs.length = 34) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng)
    (hbun4 : bun[4]? ≠ some 1#8)
    (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) :
    ∃ (pre : List Move) (a : Participant) (idS : Nat) (hb : DY.Libsignal.PQXDH.BundleHandles)
      (shown : Nat) (mid : List Move) (cl e c' : Nat) (post : List Move) (ikA : DY.Bytes)
      (tr₁ tr₂ : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut)
      (stA : DY.Libsignal.TripleRatchet.TRState),
      tr₁ = (runMoves pre (setupTrace r)).1 ∧
      o = aliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none ∧
      stA = aliceStartState tr₁ r.bob o ∧
      tr₂ = (runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁)).1 ∧
      ms = pre ++ .aliceStart a r.bob idS 6 hb shown :: mid ++
          .encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post ∧
      ((idS = 4 ∧ a = r.alice ∧ ikA = setupSecret r 0) ∨
        (idS = 9 ∧ a = r.bob ∧ ikA = setupSecret r 1)) ∧
      NetMsgAt o.ek (tr₁.length + 3) tr₂ ∧ NetMsgAt o.ct (tr₁.length + 4) tr₂ ∧
      o.ek.AttackerKnows (runTraceMoves r ms) ∧ o.ct.AttackerKnows (runTraceMoves r ms) ∧
      (encOut tr₂ stA cl (tr₂.length + 2)).AttackerKnows (runTraceMoves r ms) ∧
      bobDoneBaseKeys (runTraceMoves r ms) = [] ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs)
        (aliceVis tr₁ ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁) hb) ∧
      CompRPreKeyWire.SendMatchesMoves compI0 r S g w (received tr₂ [e, c'] ++ [encOut tr₂ stA cl (tr₂.length + 2)]) ∧
      (Move.aliceStart a r.bob idS 6 hb shown).next tr₁ = aliceStartTrOfOut tr₁ a r.bob o ∧
      MovesFrom InvisibleNoEffect (setupTrace r) pre ∧
      MovesFrom InvisibleNoEffect ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁) mid ∧
      MovesFrom InvisibleNoEffect
        ((Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post := by
  obtain ⟨pre, a, idS, hb, shown, mid, me, sIdx, cl, pq, wr, post, ikA, spkSig, pqpkSig, hms,
    hrest⟩ :=
    CliCoinSplit.matchedPrefix_ini_send_bundle_legacy_split hNe hnb hcs hmp' hrs_len hrs_kind hbun4 hw
  dsimp only at hrest
  obtain ⟨hpre, hmid, hpost, _hshown, _hopk, _hbun0, hdisj, _hspk, _hspkSig, _hpqpk, _hpqpkSig,
    _hcore, hm₀, hls, hvis₀, hvis₁⟩ := hrest
  rcases wr with ⟨e, c'⟩
  have hown : ownSaltsFrom (setupTrace r) ms = true := hmp'.2.1.2.2.2.2.1
  have hntr : NoTRState (runMoves pre (setupTrace r)).1 :=
    noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre
  have hek₁ : NetMsgAt (aliceOut (runMoves pre (setupTrace r)).1 ikA (setupPublic r 2)
      (setupPublic r 4) (setupPublic r 6) none).ek ((runMoves pre (setupTrace r)).1.length + 3)
      ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1) := by
    rw [hm₀]; exact netMsgAt_ek_iniAliceStartTr _ _ _ _
  have hct₁ : NetMsgAt (aliceOut (runMoves pre (setupTrace r)).1 ikA (setupPublic r 2)
      (setupPublic r 4) (setupPublic r 6) none).ct ((runMoves pre (setupTrace r)).1.length + 4)
      ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1) := by
    rw [hm₀]; exact netMsgAt_ct_iniAliceStartTr _ _ _ _
  have hst₁ : ∀ j : Nat,
      (((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1).at? j :
        Option TRStEntry) =
      if j = (runMoves pre (setupTrace r)).1.length + 8 then
        some (TRStE a (aliceStartState (runMoves pre (setupTrace r)).1 r.bob
          (aliceOut (runMoves pre (setupTrace r)).1 ikA (setupPublic r 2) (setupPublic r 4)
            (setupPublic r 6) none)))
      else none := by
    rw [hm₀]; exact at?_trSt_iniAliceStartTr_of_noTRState hntr _ _ _
  obtain ⟨_hE1, hme, hsIdx, hpq, _hns, _hnext, hlastSent, hek₂, hct₂, _hekr, _hctr, _hencr,
    hekK, hctK, hencK, hnil⟩ :=
    CompPrefixInvEnc.pia_enc_inv (stA := aliceStartState (runMoves pre (setupTrace r)).1 r.bob
      (aliceOut (runMoves pre (setupTrace r)).1 ikA (setupPublic r 2) (setupPublic r 4)
        (setupPublic r 6) none)) hms hpre hmid hpost hown hek₁ hct₁ hst₁ hls
  have hsm := CliCoinSplit.sendMatches_of_encVis_split hcs hlastSent hvis₁
  subst hme hsIdx hpq
  exact ⟨pre, me, idS, hb, shown, mid, cl, e, c', post, ikA, (runMoves pre (setupTrace r)).1,
    (runMoves mid ((Move.aliceStart me r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1,
    _, _, rfl, rfl, rfl, rfl, hms, hdisj, hek₂, hct₂, hekK, hctK, hencK, hnil, hvis₀, hsm, hm₀,
    hpre, hmid, hpost⟩

open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
theorem decomp40_full {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b1 b2 : List MachineEvent} (hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 r) (hnb : CompSetupSecrecy.NoBrk r ms) (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] b1) (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2) (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms (((.recv (wireAt 0) :: rs0) ++ b1) ++ b2)) : ∃ (pre mid mid₂ post₂ : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat) (cl₁ e₁ c₁ cl₂ e₂ c₂ : Nat) (tr₁ tr₂ tr₃ : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (stA : DY.Libsignal.TripleRatchet.TRState), tr₁ = (runMoves pre (setupTrace r)).1 ∧ o = aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none ∧ stA = aliceStartState tr₁ r.bob o ∧ tr₂ = (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next tr₁)).1 ∧ tr₃ = (runMoves mid₂ ((Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (e₁, c₁))).next tr₂)).1 ∧ ms = pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (e₁, c₁)) :: mid₂ ++ Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (e₂, c₂)) :: post₂ ∧ (Move.aliceStart r.alice r.bob 4 6 hb shown).next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o ∧ (Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (e₁, c₁))).next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA cl₁ (tr₂.length + 2) ∧ (Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (e₂, c₂))).next tr₃ = encNextTr tr₃ r.alice (tr₂.length + 5) (encSt tr₂ stA cl₁) cl₂ (tr₃.length + 2) ∧ MovesFrom InvisibleNoEffect (setupTrace r) pre ∧ MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next tr₁) mid ∧ MovesFrom InvisibleNoEffect ((Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (e₁, c₁))).next tr₂) mid₂ ∧ MovesFrom InvisibleNoEffect ((Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (e₂, c₂))).next tr₃) post₂ ∧ NetMsgAt o.ek (tr₁.length + 3) tr₂ ∧ NetMsgAt o.ct (tr₁.length + 4) tr₂ ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv (wireAt 0) :: rs0) (aliceVis tr₁ ((Move.aliceStart r.alice r.bob 4 6 hb shown).next tr₁) hb) ∧ CompRPreKeyWire.SendMatchesMoves compI0 r S g (sendAt 37) (received tr₂ [e₁, c₁] ++ [encOut tr₂ stA cl₁ (tr₂.length + 2)]) ∧ CompRPreKeyWire.SendMatchesMoves compI0 r S g (wireAt 40) (received tr₃ [e₂, c₂] ++ [encOut tr₃ (encSt tr₂ stA cl₁) cl₂ (tr₃.length + 2)]) := by
  obtain ⟨ms₁, pre₂, post, m₂, hms, hmp₁, hpre₂, hm₂, hpost⟩ := decomp40_last hc2 hmp
  rcases hfits.1 with ⟨hwf, -, -, -, -, -, -, hsb1, hsb2, -, -, -, -, hEq, -⟩
  have hNe : r.alice ≠ r.bob := hwf.1; have hc : Compat compI0 r S g := hmp.1; have hown : ownSaltsFrom (setupTrace r) ms = true := hmp.2.1.2.2.2.2.1
  have hnb₁ : CompSetupSecrecy.NoBrk r ms₁ := CompRX0Top.noBrk_append_left (ms₂ := pre₂ ++ m₂ :: post) (by rw [← List.append_assoc, ← hms]; exact hnb)
  obtain ⟨pre, a, idS, hb, shown, mid, cl, e, c', post₁, ikA, tr₁, tr₂, o, stA,
    htr₁, ho, hstA, htr₂, hms₁, hdisj, hek, hct, -, -, -, -, hvis₀, hsm, hm₀, hpre, hmid, hpost₁⟩ :=
    pia_x0_decomp_legacy_split hNe hnb₁ hc1 hmp₁ rs0_length rs0_kind wireAt0_byte4 (by rw [sendAt37_head?]; decide)
  rcases hdisj with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  swap
  · exfalso; subst ho hstA
    obtain ⟨q, hq⟩ := sendAt37_parses; obtain ⟨ek', ct', hL, -⟩ := CompRX0Mem.sendMatches_append_inv hsm sendAt37_len hq; rw [hL] at hsm
    exact CompRX0Bytes.not_sendMatches_bobSelf hNe hEq hc
      (by rw [hsb1]; exact idx1_bobId_secretIdx) (by rw [hsb2]; exact idx1_spk_secretIdx)
      (sendAt 37) sendAt37_hasTag4 tr₁ tr₂ r.bob _ _ ek' ct' cl _ hsm
  have hrun₁ : runTraceMoves r ms₁ = (runMoves post₁ ((Move.encrypt r.alice (tr₁.length + 8) cl
      (tr₂.length + 2) (some (e, c'))).next tr₂)).1 := by
    rw [hms₁, xpl_runTrace_eq, List.append_assoc, List.cons_append, runMoves_append_fst, runMoves_cons_fst₀, ← htr₁, runMoves_append_fst, runMoves_cons_fst₀, ← htr₂]
  have hrun₃ : runTraceMoves r (ms₁ ++ pre₂) = (runMoves (post₁ ++ pre₂) ((Move.encrypt r.alice
      (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂)).1 := by
    rw [xpl_runTrace_eq, runMoves_append_fst ms₁ pre₂, ← xpl_runTrace_eq r ms₁, hrun₁, runMoves_append_fst post₁ pre₂]
  obtain ⟨tr₃, htr₃⟩ : ∃ tr₃, tr₃ = (runMoves (post₁ ++ pre₂) ((Move.encrypt r.alice
      (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂)).1 := ⟨_, rfl⟩
  rw [hrun₃, ← htr₃] at hm₂ hpost; rw [hrun₁] at hpre₂
  have hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice (tr₁.length + 8) cl
      (tr₂.length + 2) (some (e, c'))).next tr₂) (post₁ ++ pre₂) := (movesFrom_append _ _ _ _).2 ⟨hpost₁, hpre₂⟩
  have hntr₁ : NoTRState tr₁ := by rw [htr₁]; exact noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre
  have hat₂ : ∀ j, (tr₂.at? j : Option TRStEntry) =
      if j = tr₁.length + 8 then some (TRStE r.alice stA) else none := fun j => by
    rw [htr₂, at?_trSt_of_movesFrom_invisibleNoEffect hmid, hm₀, hstA]
    exact at?_trSt_iniAliceStartTr_of_noTRState hntr₁ r.alice r.bob o j
  have hE₁ : (Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂ =
      encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2) :=
    encrypt_next_eq_encNextTr_of_ownSalt (by rw [hat₂]; simp) (by rw [hstA, aliceStartState_ns_zero]; decide) rfl
  have hat₃ : ∀ j, (tr₃.at? j : Option TRStEntry) =
      if j = tr₂.length + 5 then some (TRStE r.alice (encSt tr₂ stA cl))
      else if j = tr₁.length + 8 then some (TRStE r.alice stA) else none := fun j => by
    rw [htr₃, at?_trSt_of_movesFrom_invisibleNoEffect hmid₂, hE₁, at?_trSt_encNextTr', hat₂]
  have hpq₂ : ∀ me sIdx cl' pq' wr, m₂ = .encrypt me sIdx cl' pq' wr → pq' = tr₃.length + 2 := fun _ _ _ _ _ hm => by
    rw [htr₃, ← hrun₃, xpl_runTrace_eq]
    exact pq_eq_of_ownSaltsFrom_split (post := post) hown (by rw [hms, hm])
  obtain ⟨p40, hp40⟩ := wireAt40_parses
  obtain ⟨cl₂, e₂, c₂, hm₂eq, hE₂, -, hsm₂⟩ := call2_pin hc2 hat₃
    (by rw [hstA]; exact aliceStartState_ns_zero _ _ _) (by rw [hstA]; exact aliceStartState_pn_zero _ _ _)
    hpq₂ rfl hm₂ (by rw [wireAt40_head?]; decide) (by rw [← sendAt39_eq_wireAt40]; exact sendAt39_len) hp40
  subst hm₂eq
  refine ⟨pre, mid, post₁ ++ pre₂, post, hb, shown, cl, e, c', cl₂, e₂, c₂, tr₁, tr₂, tr₃, o, stA, htr₁, ho, hstA, htr₂, htr₃, ?_, hm₀, hE₁, hE₂, hpre, hmid, hmid₂, hpost, hek, hct, hvis₀, hsm, hsm₂⟩
  rw [hms, hms₁]; simp only [List.append_assoc, List.cons_append]
theorem explains_swap2 {i : ExternInterpretation} {r : Records} {S : Sem} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {τ : List MachineEvent} {P₁ mid₂ post : List Move} {me : Participant} {s₁ cl₁ pq₁ e₁ c₁ s₂ cl₂ pq₂ e₂ c₂ e' c' : Nat} {ek ct : DY.Bytes} (hek : NetMsgAt ek e' (runTraceMoves r P₁)) (hct : NetMsgAt ct c' (runTraceMoves r P₁)) (hγ₁ : (received (runTraceMoves r P₁) [e₁, c₁]).map (gamma i S g) = [gamma i S g ek, gamma i S g ct]) (hγ₂ : (received (runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂)) [e₂, c₂]).map (gamma i S g) = [gamma i S g ek, gamma i S g ct]) (hex : ExplainsMoves i r S who ok g (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₂, c₂)) :: post) τ) : ExplainsMoves i r S who ok g (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e', c')) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e', c')) :: post) τ ∧ runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e', c')) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e', c')) :: post) = runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₂, c₂)) :: post) ∧ preKeyRepresentations i r S g (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e', c')) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e', c')) :: post) = preKeyRepresentations i r S g (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₂, c₂)) :: post) := by
  have hA : ∀ (w₁ w₂ : Option (Nat × Nat)) (X : List Move), P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂ :: X = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁ :: (mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂ :: X) := by intros; simp only [List.append_assoc, List.cons_append]
  rw [hA] at hex; obtain ⟨hex₁, htr₁, hrep₁⟩ := WsIdx1DecompSwap.explains_swap_append hek hct hγ₁ hex; rw [← hA] at hex₁ htr₁ hrep₁; rw [← hA (some (e₁, c₁))] at htr₁ hrep₁
  have htrP : runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e', c')) :: mid₂) = runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂) := by rw [WsIdx1DecompSwap.runTrace_append, WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, runMoves_cons_fst₀, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ (some (e', c')) (some (e₁, c₁))]
  have hekP : NetMsgAt ek e' (runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e', c')) :: mid₂)) := by rw [WsIdx1DecompSwap.runTrace_append]; exact netMsgAt_runMoves _ hek
  have hctP : NetMsgAt ct c' (runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e', c')) :: mid₂)) := by rw [WsIdx1DecompSwap.runTrace_append]; exact netMsgAt_runMoves _ hct
  obtain ⟨hex₂, htr₂, hrep₂⟩ := WsIdx1DecompSwap.explains_swap_append hekP hctP (by rw [htrP]; exact hγ₂) hex₁
  exact ⟨hex₂, htr₂.trans htr₁, hrep₂.trans hrep₁⟩
theorem runTrace_snoc (r : Records) (P : List Move) (m : Move) : runTraceMoves r (P ++ [m]) = m.next (runTraceMoves r P) := by rw [xpl_runTrace_eq, xpl_runTrace_eq, runMoves_append_fst]; rfl
theorem decrypt_next_eq_of_invisibleNoEffect {tr : ExecTrace} {m : Move} (hm : InvisibleNoEffect tr m) (hd : m.decryptMsgIdx? ≠ none) : m.next tr = tr := by
  have hv := hm.1
  cases m with
  | decrypt me si mi pq sm w =>
    apply XplSteps.xpl_decrypt_next
    rcases h : tr.getMessageSentAt mi with _ | b
    · rfl
    · exfalso; simp [Move.vis, decVis, h] at hv
  | decryptSkipped me si mi k pq sm w =>
    apply XplSteps.xpl_decryptSkipped_next
    rcases h : tr.getMessageSentAt mi with _ | b
    · rfl
    · exfalso; simp [Move.vis, decVis, h] at hv
  | _ => simp [Move.decryptMsgIdx?] at hd
theorem decryptNoop_snoc {r : Records} {P : List Move} {m : Move} (hP : WsIdx1DecryptNoop.DecryptNoop r P) (hm : m.decryptMsgIdx? ≠ none → m.vis (runTraceMoves r P) = [] ∧ m.next (runTraceMoves r P) = runTraceMoves r P) : WsIdx1DecryptNoop.DecryptNoop r (P ++ [m]) := by
  intro k m' hk hd
  rcases Nat.lt_or_ge k P.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hk; rw [List.take_append_of_le_length hlt.le]; exact hP k m' hk hd
  · rw [List.getElem?_append_right hge] at hk
    obtain rfl : k = P.length := by
      rcases h : k - P.length with _ | n
      · omega
      · rw [h] at hk; simp at hk
    rw [Nat.sub_self] at hk; simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk; rw [List.take_left]; exact hm hd
theorem decryptNoop_append_movesFrom {r : Records} :
    ∀ {P seg : List Move}, WsIdx1DecryptNoop.DecryptNoop r P → MovesFrom InvisibleNoEffect (runTraceMoves r P) seg → WsIdx1DecryptNoop.DecryptNoop r (P ++ seg)
  | P, [], hP, _ => by rw [List.append_nil]; exact hP
  | P, m :: seg, hP, ⟨hm, hseg⟩ => by
    have h1 := decryptNoop_snoc hP (fun hd => ⟨hm.1, decrypt_next_eq_of_invisibleNoEffect hm hd⟩)
    have h2 := decryptNoop_append_movesFrom h1 (by rw [runTrace_snoc]; exact hseg)
    simpa only [List.append_assoc, List.singleton_append] using h2
theorem decryptNoop_split40 {r : Records} {pre mid mid₂ post₂ : List Move} {A E₁ E₂ : Move} (hA : A.decryptMsgIdx? = none) (hE₁ : E₁.decryptMsgIdx? = none) (hE₂ : E₂.decryptMsgIdx? = none) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect (A.next (runTraceMoves r pre)) mid) (hmid₂ : MovesFrom InvisibleNoEffect (E₁.next (runTraceMoves r (pre ++ A :: mid))) mid₂) (hpost : MovesFrom InvisibleNoEffect (E₂.next (runTraceMoves r (pre ++ A :: mid ++ E₁ :: mid₂))) post₂) : WsIdx1DecryptNoop.DecryptNoop r (pre ++ A :: mid ++ E₁ :: mid₂ ++ E₂ :: post₂) := by
  have h0 : WsIdx1DecryptNoop.DecryptNoop r [] := fun k m hk => by simp at hk
  have h1 := decryptNoop_append_movesFrom h0 (by rw [xpl_runTrace_eq]; exact hpre)
  rw [List.nil_append] at h1
  have h2 := decryptNoop_snoc h1 (fun hd => absurd hA hd)
  have h3 := decryptNoop_append_movesFrom h2 (by rw [runTrace_snoc]; exact hmid)
  have h4 := decryptNoop_snoc h3 (fun hd => absurd hE₁ hd)
  have h5 := decryptNoop_append_movesFrom h4 (by
    rw [runTrace_snoc, List.append_assoc, List.singleton_append]; exact hmid₂)
  have h6 := decryptNoop_snoc h5 (fun hd => absurd hE₂ hd)
  have h7 := decryptNoop_append_movesFrom h6 (by
    rw [runTrace_snoc]
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using hpost)
  simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using h7
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol) in
theorem gamma_facts40 {r : Records} {S : Sem} {g : Ghost} {tr₁ : ExecTrace} {hb : DY.Libsignal.PQXDH.BundleHandles} (hvis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv (wireAt 0) :: rs0) (aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb)) : gamma compI0 S g (randTerm (tr₁.length + 1) 32) = compKyberE1 ∧ gamma compI0 S g (DY.DiffieHellman.dhPk (randTerm tr₁.length 32)) = WsIdx1CensusDefs.ek1PubKey ∧ gamma compI0 S g (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ct = compKyberCt1 := by
  rw [rs0_eq_cons] at hvis; obtain ⟨hγek, hγe⟩ := CompRX0Gamma.aliceVis_rng_coins hvis; rw [rs0_coinHeads_eq] at hγe; have hek := CompRX0Gamma.gamma_iniAliceOut_ek_compI0 (S := S) (g := g) (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none hγek; rw [clamp_rng1_lookup] at hek
  have hct := CompRX0Gamma.gamma_iniAliceOut_ct (i := compI0) (S := S) (g := g)
    (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none (by rw [hγe]; decide)
  rw [hγe] at hct
  refine ⟨hγe, hek, ?_⟩; rw [hct]
  have h0 : compI0 kyberEncapsSymbol [gamma compI0 S g (setupPublic r 6), compKyberE1] =
      some (compKyberEncaps compKyberE1) := rfl
  rw [h0, Option.getD_some, compKyberEncaps_e1_take1568]
theorem census_encSt_eq : @Census443Defs.encSt = @CompPrefixInvEnc.encSt := rfl
theorem census_encNextTr_eq : @Census443Defs.encNextTr = @CompPrefixInvEnc.encNextTr := rfl
attribute [local irreducible] setupPublic setupSecret
theorem split3_take_get {α : Type _} (P : List α) (a : α) (M : List α) (b : α) (N : List α) (c : α) (Q : List α) : (P ++ a :: M ++ b :: N ++ c :: Q).take P.length = P ∧ (P ++ a :: M ++ b :: N ++ c :: Q)[P.length]? = some a ∧ (P ++ a :: M ++ b :: N ++ c :: Q).take (P ++ a :: M).length = P ++ a :: M ∧ (P ++ a :: M ++ b :: N ++ c :: Q)[(P ++ a :: M).length]? = some b ∧ (P ++ a :: M ++ b :: N ++ c :: Q).take (P ++ a :: M ++ b :: N).length = P ++ a :: M ++ b :: N ∧ (P ++ a :: M ++ b :: N ++ c :: Q)[(P ++ a :: M ++ b :: N).length]? = some c := by
  have h₁ : P ++ a :: M ++ b :: N ++ c :: Q = P ++ a :: (M ++ b :: N ++ c :: Q) := by simp only [List.append_assoc, List.cons_append]
  have h₂ : P ++ a :: M ++ b :: N ++ c :: Q = (P ++ a :: M) ++ b :: (N ++ c :: Q) := by simp only [List.append_assoc, List.cons_append]
  refine ⟨by rw [h₁]; exact List.take_left, by rw [h₁]; simp,
    by rw [h₂]; exact List.take_left, by rw [h₂]; simp, List.take_left, by simp⟩
theorem split3_lt₁ {α : Type _} (P : List α) {a : α} (M : List α) :
    P.length < (P ++ a :: M).length := by simp only [List.length_append, List.length_cons]; omega
theorem split3_lt₂ {α : Type _} (P : List α) {b : α} (N : List α) :
    P.length < (P ++ b :: N).length := by simp only [List.length_append, List.length_cons]; omega
theorem c_out_eq : @Census443Defs.iniAliceOut = @CompTrace.aliceOut := rfl
theorem c_st_eq : @Census443Defs.iniAliceStartState = @CompPrefixInvBundle.aliceStartState := rfl
theorem c_tr_eq : @Census443Defs.iniAliceStartTr = @CompPrefixInvBundle.aliceStartTrOfOut := rfl
theorem a_out_eq : @CompPrefixInvAlice.iniAliceOut = @CompTrace.aliceOut := rfl
theorem a_tr_eq : @CompPrefixInvAlice.iniAliceStartTr = @CompPrefixInvBundle.aliceStartTrOfOut := rfl
theorem links40Own_of {r : Records} {pre mid mid₂ post₂ : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {sh s₁ s₂ cl₁ cl₂ : Nat} {tr₁ tr₂ tr₃ : ExecTrace} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA : DY.Libsignal.TripleRatchet.TRState} (ho : o = aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hstA : stA = aliceStartState tr₁ r.bob o) (htr₁ : runTraceMoves r pre = tr₁) (htr₂ : runTraceMoves r (pre ++ .aliceStart r.alice r.bob 4 6 hb sh :: mid) = tr₂) (htr₃ : runTraceMoves r (pre ++ .aliceStart r.alice r.bob 4 6 hb sh :: mid ++ .encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂) = tr₃) (hA : (Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o) (hE₁ : (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂ = encNextTr tr₂ r.alice s₁ stA cl₁ (tr₂.length + 2)) (hE₂ : (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃ = encNextTr tr₃ r.alice s₂ (encSt tr₂ stA cl₁) cl₂ (tr₃.length + 2)) : WsIdx1PrefDefs.Links40Own r (pre ++ .aliceStart r.alice r.bob 4 6 hb sh :: mid ++ .encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂ ++ .encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post₂) tr₁ tr₂ tr₃ cl₁ cl₂ := by
  obtain ⟨t₁, g₁, t₂, g₂, t₃, g₃⟩ := split3_take_get pre (.aliceStart r.alice r.bob 4 6 hb sh) mid (.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))) mid₂ (.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))) post₂
  refine ⟨_, _, _, hb, sh, s₁, s₂, split3_lt₁ pre mid, split3_lt₂ (pre ++ _ :: mid) mid₂,
    by rw [t₁, htr₁], g₁, by rw [t₂, htr₂], g₂, by rw [t₃, htr₃], g₃,
    by rw [c_tr_eq, c_out_eq, ← ho]; exact hA,
    by rw [census_encNextTr_eq, c_st_eq, c_out_eq, ← ho, ← hstA]; exact hE₁,
    by rw [census_encNextTr_eq, census_encSt_eq, c_st_eq, c_out_eq, ← ho, ← hstA]; exact hE₂⟩
theorem movesFrom_census {tr : ExecTrace} {δ : List Move} (hnb : CompRX0Top.NoBrkTr (runMoves δ tr).1) (h : MovesFrom InvisibleNoEffect tr δ) : Census443Defs.MovesFrom Census443Defs.InvisibleNoEffect tr δ :=
  CompRX0SS38.movesFrom_to_census443 hnb h
theorem aliceOut_ek_eq (tr : ExecTrace) (ikA ikB spk pqpk : DY.Bytes) : (aliceOut tr ikA ikB spk pqpk none).ek = DY.DiffieHellman.dhPk (randTerm tr.length 32) := rfl
theorem x40_eq (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : WsIdx1CensusDefs.x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂ = ⟨(aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek, (aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ct, encOut tr₃ (encSt tr₂ (aliceStartState tr₁ r.bob (aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2)⟩ := rfl
theorem prk_x40_eq : @WsIdx1PreKeyRep.x40Idx1 = @WsIdx1CensusDefs.x40Idx1 := rfl
theorem prk_recvAt_eq : @WsIdx1PreKeyRep.recvAt = @WsIdx1CensusDefs.recvAt := rfl
theorem census_recvAt_eq : @WsIdx1CensusDefs.recvAt = @wireAt := rfl
theorem prk_wire3_eq : WsIdx1PreKeyRep.wire3Idx1Bytes = WsIdx1CensusDefs.wire3Idx1Bytes := by
  show WsIdx1PreKeyRep.recvAt 40 = WsIdx1CensusDefs.recvAt 40; rw [prk_recvAt_eq]
theorem census_wire3_eq : WsIdx1CensusDefs.wire3Idx1Bytes = wireAt 40 := by
  show WsIdx1CensusDefs.recvAt 40 = wireAt 40; rw [census_recvAt_eq]
theorem rngAt36_ne_nil : rngAt 36 ≠ [] := by decide +kernel
theorem singleton_flatten_prefix {α : Type} (x : List α) : [x].flatten <+: x := ⟨[], by simp⟩
theorem coinSplit_seg35_self :
    DY.Libsignal.Composed.Refinement.Cli.CoinSplit
      (WsIdx1CensusDefs.wsIdx1Trace.drop 35 |>.take 3)
      (WsIdx1CensusDefs.wsIdx1Trace.drop 35 |>.take 3) := by
  show DY.Libsignal.Composed.Refinement.Cli.CoinSplit
    [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)]
    [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)]
  exact .keep (fun _ h => nomatch h)
    (.split (pieces := [rngAt 36])
      (fun d hd => (List.mem_singleton.mp hd) ▸ rngAt36_ne_nil)
      (singleton_flatten_prefix (rngAt 36)) (.keep (fun _ h => nomatch h) .nil))

theorem split40_pre_split {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields}
    {b1 b2 : List MachineEvent}
    (hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (WsIdx1CensusDefs.wsIdx1Trace.drop 35 |>.take 3) b1)
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2)
    (hex : DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S
      Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who
      Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms
      ((WsIdx1CensusDefs.wsIdx1Trace.take 35 ++ b1) ++ b2))
    (hp : parsePreKeyWire WsIdx1CensusDefs.wire3Idx1Bytes = some p) :
    ∃ (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat),
      DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S
        Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who
        Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms'
        ((WsIdx1CensusDefs.wsIdx1Trace.take 35 ++ b1) ++ b2) ∧
      (∃ P₁ mid₂ post me s₁ pq₁ s₂ pq₂ w₁ w₂ w₁' w₂',
        ms = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂ :: post ∧
        ms' = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁' :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂' :: post) ∧
      WsIdx1PrefDefs.WS40Idx1Pre r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ ∧
      WsIdx1CensusDefs.x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂ ∈ preKeyRepresentations compI0 r S g ms' WsIdx1CensusDefs.wire3Idx1Bytes := by
  have hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms
      (((.recv (wireAt 0) :: rs0) ++ b1) ++ b2) :=
    Symbolic.Swarm.CREF.MatchedPrefix.of_composed hex.1
  obtain ⟨pre, mid, mid₂, post₂, hb, shown, cl₁, e₁, c₁, cl₂, e₂, c₂, tr₁, tr₂, tr₃, o, stA, htr₁, ho, hstA, htr₂, htr₃, hms, hA, hE₁, hE₂, hpre, hmid, hmid₂, hpost, hek, hct, hvis,
    hsm₁, hsm₂⟩ := decomp40_full hfits hnb hc1 hc2 hmp
  have hvis' := hvis; rw [hA, ← a_tr_eq, ho, ← a_out_eq] at hvis'; obtain ⟨hent, hek1, hctγ⟩ := gamma_facts40 hvis'; rw [a_out_eq, ← ho] at hctγ
  have hekγ : gamma compI0 S g o.ek = WsIdx1CensusDefs.ek1PubKey := by rw [ho, aliceOut_ek_eq]; exact hek1
  have hrt₁ : runTraceMoves r pre = tr₁ := by rw [xpl_runTrace_eq, htr₁]
  have hrt₂ : runTraceMoves r (pre ++ .aliceStart r.alice r.bob 4 6 hb shown :: mid) = tr₂ := by rw [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₁, htr₂]
  have hrt₃ : runTraceMoves r (pre ++ .aliceStart r.alice r.bob 4 6 hb shown :: mid ++ .encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂) = tr₃ := by rw [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₂, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₁, c₁)), htr₃]
  have hrt₃o : runTraceMoves r (pre ++ .aliceStart r.alice r.bob 4 6 hb shown :: mid ++ .encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (e₁, c₁)) :: mid₂) = tr₃ := by rw [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₂, htr₃]
  obtain ⟨q₁, hq₁⟩ := sendAt37_parses
  have hγ₁ := CompRX0Mem.hγ_of_sendMatches (ek := o.ek) (ct := o.ct) hsm₁ sendAt37_len hq₁
    (by rw [sendAt37_baseKey hq₁, hekγ]) (by rw [sendAt37_kyberCiphertext hq₁, hctγ])
  have hp40 : parsePreKeyWire (wireAt 40) = some p := by rw [← census_wire3_eq]; exact hp
  have hlen₂ : (wireAt 40).length < 2 ^ 63 := by rw [← sendAt39_eq_wireAt40]; exact sendAt39_len
  have hγ₂ := CompRX0Mem.hγ_of_sendMatches (ek := o.ek) (ct := o.ct) hsm₂ hlen₂ hp40
    (by rw [wireAt40_baseKey_full hp40, hekγ]) (by rw [wireAt40_kyberCiphertext hp40, hctγ])
  have hekP : NetMsgAt o.ek (tr₁.length + 3)
      (runTraceMoves r (pre ++ .aliceStart r.alice r.bob 4 6 hb shown :: mid)) := by rw [hrt₂]; exact hek
  have hctP : NetMsgAt o.ct (tr₁.length + 4)
      (runTraceMoves r (pre ++ .aliceStart r.alice r.bob 4 6 hb shown :: mid)) := by rw [hrt₂]; exact hct
  subst hms
  obtain ⟨hex', hrteq, -⟩ := explains_swap2 hekP hctP (by rw [hrt₂]; exact hγ₁)
    (by rw [hrt₃o]; exact hγ₂) hex
  obtain ⟨MS', hMS'⟩ : ∃ MS', MS' = pre ++ .aliceStart r.alice r.bob 4 6 hb shown :: mid ++ .encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂ ++ .encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2)
        (some (tr₁.length + 3, tr₁.length + 4)) :: post₂ := ⟨_, rfl⟩
  obtain ⟨ek₂, ct₂, -, -, -, hmsg₂⟩ := CompRX0Mem.sendMatches_append_inv hsm₂ hlen₂ hp40
  have hle₃ : (Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2)
      (some (tr₁.length + 3, tr₁.length + 4))).next tr₃ ≤ runTraceMoves r MS' := by
    rw [hMS', WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₃]; exact CompPrefixInvEnc.runMoves_le _ _
  have hle₂ : tr₂ ≤ runTraceMoves r MS' := by
    have h1 : tr₂ ≤ (Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2)
        (some (e₁, c₁))).next tr₂ := Move.le_next _ tr₂
    have h2 : (Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2)
        (some (e₁, c₁))).next tr₂ ≤ tr₃ := by rw [htr₃]; exact CompPrefixInvEnc.runMoves_le _ _
    have h3 : tr₃ ≤ (Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2)
        (some (tr₁.length + 3, tr₁.length + 4))).next tr₃ := Move.le_next _ tr₃
    exact Trace.le_trans _ _ _ h1 (Trace.le_trans _ _ _ h2 (Trace.le_trans _ _ _ h3 hle₃))
  have hnbMS : CompRX0Top.NoBrkTr (runTraceMoves r MS') := by
    rw [hMS', hrteq]; exact CompRX0Top.noBrkTr_of_noBrk hnb
  have hnb_tr₁ : CompRX0Top.NoBrkTr tr₁ :=
    CompRX0Top.noBrkTr_of_le (Trace.le_trans _ _ _ (Move.le_next _ _)
      (Trace.le_trans _ _ _ (by rw [htr₂]; exact CompPrefixInvEnc.runMoves_le _ _) hle₂)) hnbMS
  have hnb_tr₂ : CompRX0Top.NoBrkTr tr₂ := CompRX0Top.noBrkTr_of_le hle₂ hnbMS
  have hnb_tr₃ : CompRX0Top.NoBrkTr tr₃ :=
    CompRX0Top.noBrkTr_of_le (Trace.le_trans _ _ _ (Move.le_next _ _) hle₃) hnbMS
  have hnb_post : CompRX0Top.NoBrkTr (runMoves post₂ ((Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (e₂, c₂))).next tr₃)).1 := by
    have hnbMS' := hnbMS
    rw [hMS', WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₃,
      WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₂, c₂))] at hnbMS'
    exact hnbMS'
  have hkmsgN := netMsgAt_encOut_encNextTr tr₃ r.alice (tr₂.length + 5) (encSt tr₂ stA cl₁) cl₂ (tr₃.length + 2); rw [← hE₂, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (tr₁.length + 3, tr₁.length + 4))] at hkmsgN; have hkmsg := (NetMsgAt.mono hle₃ hkmsgN).attackerKnows; have hkek := (NetMsgAt.mono hle₂ hek).attackerKnows; have hkct := (NetMsgAt.mono hle₂ hct).attackerKnows
  have hlen33 : (ecKey WsIdx1CensusDefs.ek1PubKey).take 33 = ecKey WsIdx1CensusDefs.ek1PubKey := by
    apply List.take_of_length_le
    show WsIdx1CensusDefs.ek1PubKey.length + 1 ≤ 33
    have : WsIdx1CensusDefs.ek1PubKey.length = 32 := by decide +kernel
    omega
  have hall := WsIdx1PreKeyRep.x40Idx1_mem_preKeyRepresentations (ms' := MS') (tr₁ := tr₁)
    (tr₂ := tr₂) (tr₃ := tr₃) (cl₁ := cl₁) (cl₂ := cl₂) (p := p)
    (by rw [prk_x40_eq, x40_eq, ← ho, ← hstA]; dsimp only; exact hkek)
    (by rw [prk_x40_eq, x40_eq, ← ho, ← hstA]; dsimp only; exact hkct)
    (by rw [prk_x40_eq, x40_eq, ← ho, ← hstA]; dsimp only; exact hkmsg)
    (by rw [prk_wire3_eq]; exact hp)
    (by rw [prk_x40_eq, x40_eq, ← ho, ← hstA]; dsimp only; rw [hekγ, wireAt40_baseKey_full hp40, hlen33])
    (by rw [prk_x40_eq, x40_eq, ← ho, ← hstA]; dsimp only; rw [hctγ, wireAt40_kyberCiphertext hp40])
    (by rw [prk_x40_eq, x40_eq, ← ho, ← hstA]; dsimp only; rw [hmsg₂])
    (wireAt40_canon hp40)
    (by rw [prk_wire3_eq, census_wire3_eq]; exact wireAt40_outer hfits.1 hp40)
  dsimp only at hall; rw [prk_x40_eq, prk_wire3_eq] at hall; obtain ⟨hmem, hw⟩ := hall; subst hMS'
  refine ⟨_, tr₁, tr₂, tr₃, cl₁, cl₂, hex',
    ⟨pre ++ .aliceStart r.alice r.bob 4 6 hb shown :: mid, mid₂, post₂, r.alice,
      tr₁.length + 8, tr₂.length + 2, tr₂.length + 5, tr₃.length + 2,
      some (e₁, c₁), some (e₂, c₂), some (tr₁.length + 3, tr₁.length + 4), some (tr₁.length + 3, tr₁.length + 4), rfl, rfl⟩,
    { fits := hfits, ex := trivial, mp := WsIdx1CensusDefs.matchedPrefix40_of_split2 hc1 hc2 hex'.1, compat := hex.1.1, hent₁ := hent, hek₁ := hek1
      dn := decryptNoop_split40 (by rfl) (by rfl) (by rfl) hpre (by rw [hrt₁]; exact hmid)
        (by rw [hrt₂]; exact hmid₂)
        (by rw [hrt₃, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₂, c₂))]; exact hpost)
      links := links40Own_of ho hstA hrt₁ hrt₂ hrt₃ hA
        (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₁, c₁))]; exact hE₁)
        (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₂, c₂))]; exact hE₂)
      reach := by rw [hrteq]; exact CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp _ [] (List.append_nil _).symm
      hwire₂ := by dsimp only; intro p' hp'; obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hp); exact hw
      hsalts := ?_ }, hmem⟩
  dsimp only; rw [c_out_eq, c_st_eq, census_encSt_eq, ← ho, ← hstA]; intro s hs
  have h := CompRSchedBSalts.honestSalts_schedB40_mem (r := r) (s₀ := pre) (s₁ := mid)
    (s₂ := mid₂) (s₃ := post₂)
    (A₁ := .aliceStart r.alice r.bob 4 6 hb shown)
    (E₁ := .encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)))
    (E₂ := .encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4)))
    (tr₁ := tr₁) (tr₂ := tr₂) (tr₃ := tr₃) (o₁ := o) (b := r.bob)
    ⟨_, rfl⟩ ⟨_, rfl⟩ (fun _ _ _ _ _ h => by cases h) htr₁ htr₂
    (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₁, c₁))]; exact htr₃)
    (Or.inl (movesFrom_census (by rw [← htr₁]; exact hnb_tr₁) hpre)) (Or.inl (movesFrom_census (by rw [← htr₂]; exact hnb_tr₂) hmid))
    (Or.inl (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₁, c₁))]; exact movesFrom_census (by rw [← htr₃]; exact hnb_tr₃) hmid₂))
    (Or.inl (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₂, c₂))]; exact movesFrom_census hnb_post hpost))
    (by rw [census_encNextTr_eq, c_st_eq, ← hstA, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₁, c₁))]; exact hE₁)
    (by rw [census_encNextTr_eq, census_encSt_eq, c_st_eq, ← hstA, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₂, c₂))]; exact hE₂)
    hs
  rw [census_encSt_eq, c_st_eq, ← hstA] at h; exact h

theorem split40DecompSwapRep_split_of (hpref : WsIdx1PrefDefs.Pref40Hyp)
    {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields} {b1 b2 : List MachineEvent}
    (hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (WsIdx1CensusDefs.wsIdx1Trace.drop 35 |>.take 3) b1)
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2)
    (hex : DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S
      Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who
      Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms
      ((WsIdx1CensusDefs.wsIdx1Trace.take 35 ++ b1) ++ b2))
    (hp : parsePreKeyWire WsIdx1CensusDefs.wire3Idx1Bytes = some p) :
    ∃ (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat),
      DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S
        Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who
        Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms'
        ((WsIdx1CensusDefs.wsIdx1Trace.take 35 ++ b1) ++ b2) ∧
      (∃ P₁ mid₂ post me s₁ pq₁ s₂ pq₂ w₁ w₂ w₁' w₂',
        ms = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂ :: post ∧
        ms' = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁' :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂' :: post) ∧
      WsIdx1DecryptNoop.DecryptNoop r ms' ∧
      WsIdx1CensusDefs.WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ ∧
      WsIdx1PrefDefs.Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ ∧
      WsIdx1CensusDefs.x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂ ∈ preKeyRepresentations compI0 r S g ms' WsIdx1CensusDefs.wire3Idx1Bytes := by
  obtain ⟨ms', tr₁, tr₂, tr₃, cl₁, cl₂, hex', hswap, hP, hmem⟩ := split40_pre_split hfits hnb hc1 hc2 hex hp
  have hF := hpref r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ hP
  obtain ⟨k₁, k₂, k₃, hb, sh, s₁, s₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hP.links
  exact ⟨ms', tr₁, tr₂, tr₃, cl₁, cl₂, hex', hswap, hP.dn,
    { mp := hP.mp
      links := ⟨k₁, k₂, k₃, hb, sh, s₁, s₂, _, _, _, _, h1, h2, h3, h4, h5, h6, h7, h8, h9, rfl, rfl, h10, h11⟩
      compat := hP.compat, reach := hP.reach, hent₁ := hP.hent₁, hek₁ := hP.hek₁
      hdhs₁ := hF.hdhs₁, hm₁ := hF.hm₁, hm₁_len := hF.hm₁_len, hcoins₁ := hF.hcoins₁
      hm₂ := hF.hm₂, hm₂_len := hF.hm₂_len, hcoins₂ := hF.hcoins₂
      hwire₂ := hP.hwire₂, hsalts := hP.hsalts, hpref_safe := hF.hpref_safe }, hP.links, hmem⟩

theorem split40DecompSwapRepOwn_of (hpref : WsIdx1PrefDefs.Pref40Hyp) : ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 r → CompSetupSecrecy.NoBrk r ms → DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms (WsIdx1CensusDefs.wsIdx1Trace.take 40) → parsePreKeyWire WsIdx1CensusDefs.wire3Idx1Bytes = some p → ∃ (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms' (WsIdx1CensusDefs.wsIdx1Trace.take 40) ∧ WsIdx1DecryptNoop.DecryptNoop r ms' ∧ WsIdx1CensusDefs.WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ ∧ WsIdx1PrefDefs.Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ ∧ WsIdx1CensusDefs.x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂ ∈ preKeyRepresentations compI0 r S g ms' WsIdx1CensusDefs.wire3Idx1Bytes := by
  intro r S g ms p hfits hnb hex hp
  obtain ⟨ms', tr₁, tr₂, tr₃, cl₁, cl₂, hex', _, hdn, hinv, hlinks, hmem⟩ :=
    split40DecompSwapRep_split_of hpref hfits hnb coinSplit_seg35_self WsIdx1CensusDefs.coinSplit_seg38_self hex hp
  exact ⟨ms', tr₁, tr₂, tr₃, cl₁, cl₂, hex', hdn, hinv, hlinks, hmem⟩
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp40
