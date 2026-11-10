/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.X25519
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Refinement.LemmasPure
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core
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
# Canonical Symbolic Representations for Parsed Whisper Messages

Proves `decrypt_recvRepresentations_nonempty_of_tryFrom` and its corollary
`recvRepresentations_nonempty_of_tryFrom`: any byte sequence `b` parsed by `SignalMessage.tryFrom`
admits an attacker-known canonical symbolic representation in `recvRepresentations`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR.RecvRep

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalProtoCodec
open DY.DiffieHellman DY.Literal DY.X25519
open DY.Libsignal.Refinement (EncodingVariation)
open DY.Libsignal.TripleRatchet
  (TRSignalMsg parseTrSignalMsg)

/-! ## Little-Endian and `x25519KeyTerm` Helpers -/

theorem length_leBytes : ∀ n w, (leBytes n w).length = n
  | 0, _ => rfl
  | n + 1, w => by simp [leBytes, length_leBytes n]

theorem leValue_leBytes : ∀ n w, leValue ((leBytes n w).map BitVec.toNat) = w % 256 ^ n
  | 0, w => by simp [leBytes, leValue, Nat.mod_one]
  | n + 1, w => by
    have h : w % 256 ^ (n + 1) = w % 256 + 256 * (w / 256 % 256 ^ n) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    rw [h, leBytes, List.map_cons, leValue, leValue_leBytes n, BitVec.toNat_ofNat]

theorem leBytes_leValue : ∀ b : HwBytes, leBytes b.length (leValue (b.map BitVec.toNat)) = b
  | [] => rfl
  | x :: xs => by
    have hx := x.isLt
    simp only [List.length_cons, leBytes, List.map_cons, leValue]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      omega
    · have : (x.toNat + 256 * leValue (xs.map BitVec.toNat)) / 256 = leValue (xs.map BitVec.toNat) := by
        omega
      rw [this, leBytes_leValue xs]

theorem leValue_lt : ∀ b : HwBytes, leValue (b.map BitVec.toNat) < 256 ^ b.length
  | [] => by simp [leValue]
  | x :: xs => by
    have hx := x.isLt
    have ih := leValue_lt xs
    simp only [List.map_cons, leValue, List.length_cons, Nat.pow_succ']
    simp only [BitVec.toNat] at hx
    omega

theorem p25519_lt : p25519 < 2 ^ 255 := by unfold p25519; omega

theorem p25519_pos : 0 < p25519 := by unfold p25519; omega

theorem uOf_lt (b : HwBytes) : x25519UCoord b < p25519 := Nat.mod_lt _ p25519_pos

theorem uOf_leBytes (w : Nat) (hw : w < 2 ^ 256) : x25519UCoord (leBytes 32 w) = w % 2 ^ 255 % p25519 := by
  unfold x25519UCoord uCoord
  rw [leValue_leBytes, Nat.mod_eq_of_lt (a := w) (b := 256 ^ 32) (by omega)]

theorem uOf_canon (b : HwBytes) : x25519UCoord (leBytes 32 (x25519UCoord b)) = x25519UCoord b := by
  have h := uOf_lt b
  have hp := p25519_lt
  have h256 : x25519UCoord b < 2 ^ 256 := by omega
  have h255 : x25519UCoord b < 2 ^ 255 := by omega
  rw [uOf_leBytes (x25519UCoord b) h256, Nat.mod_eq_of_lt h255, Nat.mod_eq_of_lt h]

/-- The little-endian value of a key. -/
def keyValue (b : HwBytes) : Nat := leValue (b.map BitVec.toNat)

/-- The canonical encoding of `b`'s u-coordinate, as a literal. -/
def canonKeyLit (b : HwBytes) : DY.Bytes := litOf (leBytes 32 (x25519UCoord b))

/-- How `b` deviates from the canonical encoding: bit 0 the top bit, bit 1 `+ p`. -/
def keyVariation (b : HwBytes) : Fin 4 :=
  if 2 ^ 255 ≤ keyValue b then (if p25519 ≤ keyValue b % 2 ^ 255 then 3 else 1)
  else (if p25519 ≤ keyValue b % 2 ^ 255 then 2 else 0)

/-- The term for key bytes `b`. -/
def x25519KeyTerm (b : HwBytes) : DY.Bytes := x25519Variant (canonKeyLit b) (keyVariation b)

theorem x25519Key_canonKeyLit (b : HwBytes) : normalizeX25519Key (canonKeyLit b) = canonKeyLit b := by
  unfold normalizeX25519Key canonKeyLit litOf
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _]

/-! ## Composed `gamma` and `AttackerKnows` Helpers -/

unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_litOf (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (b : HwBytes) :
    gamma interpretation S g (litOf b) = b := by
  unfold gamma gamma' litOf
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll interpretation S g)]
  exact DY.Libsignal.Refinement.ofByteArray_toByteArray b

theorem gamma_trWireMsg (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (v : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes) (ev : EncodingVariation) :
    let w : DY.TrWire.TrWireMsg.SubF DY.Bytes :=
      { version := v, senderRatchetKey := rk, counter := c, previousCounter := pc,
        ciphertext := ct, pqRatchet := pq, encodingVariation := ev }
    gamma interpretation S g (DY.TrWire.trWireMsg v rk c pc ct pq ev) =
      trWireBytes (g.addr w.pack) ev
        { version := v.toNat
          ratchetKey := gamma interpretation S g rk
          counter := c.toNat
          previousCounter := pc.toNat
          ciphertext := gamma interpretation S g ct }
        (gamma interpretation S g pq) := by
  intro w
  unfold gamma gamma' DY.TrWire.trWireMsg
  show ((w.pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll interpretation S g)]
  rfl

unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeConcat (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_concat (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (l r : DY.Bytes) :
    gamma interpretation S g (Concat.concat l r) =
      gamma interpretation S g l ++ gamma interpretation S g r := by
  unfold gamma gamma'
  show ((({lhs := l, rhs := r} : DY.Concat.Concat.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll interpretation S g)]; rfl

theorem gamma_x25519Variant_raw (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (k : DY.Bytes) (v : Fin 4) :
    gamma interpretation S g (({key := k, variation := v, torsion := 0} : DY.X25519.Variant.SubF DY.Bytes).pack) =
      variantBytes (gamma interpretation S g k) v := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeVariant interpretation) (concretizeAll interpretation S g)]; rfl

theorem knows_litOf (bs : HwBytes) (tr : ExecTrace) :
    (litOf bs).AttackerKnows tr :=
  Literal.attacker_knows_literalToBytes _ _

theorem length_litOf (bs : HwBytes) : (litOf bs).length = bs.length := by
  change DY.Bytes.length (DY.Literal.literalToBytes ⟨(bs.map UInt8.ofBitVec).toArray⟩) = bs.length
  rw [DY.Literal.length_literalToBytes]
  simp [ByteArray.size]

theorem gamma_canonKeyLit (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (b : HwBytes) :
    gamma interpretation S g (canonKeyLit b) = leBytes 32 (x25519UCoord b) :=
  gamma_litOf interpretation S g (leBytes 32 (x25519UCoord b))

theorem gamma_variant_canon (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (b : HwBytes) (v : Fin 4) (hv : v ≠ 0) :
    gamma interpretation S g (x25519Variant (canonKeyLit b) v) =
      leBytes 32 (if v.val % 2 = 1 then
        (if v.val / 2 = 1 ∧ x25519UCoord b + p25519 < 2 ^ 255 then x25519UCoord b + p25519 else x25519UCoord b) + 2 ^ 255
      else (if v.val / 2 = 1 ∧ x25519UCoord b + p25519 < 2 ^ 255 then x25519UCoord b + p25519 else x25519UCoord b)) := by
  simp only [x25519Variant, x25519Key_canonKeyLit, hv, ↓reduceIte]
  rw [gamma_x25519Variant_raw, gamma_canonKeyLit]
  unfold variantBytes
  simp only [length_leBytes, ↓reduceIte, uOf_canon]

/-- `x25519KeyTerm b` concretizes to `b` for any 32-byte list `b`. -/
theorem gamma_x25519KeyTerm (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (b : HwBytes) (hb : b.length = 32) :
    gamma interpretation S g (x25519KeyTerm b) = b := by
  have hL : keyValue b < 2 ^ 256 := by
    have := leValue_lt b; rw [hb] at this; unfold keyValue; omega
  have hb' : leBytes 32 (keyValue b) = b := by rw [← hb]; exact leBytes_leValue b
  have hu : x25519UCoord b = keyValue b % 2 ^ 255 % p25519 := rfl
  have hp : p25519 = 2 ^ 255 - 19 := rfl
  refine Eq.trans ?_ hb'
  unfold x25519KeyTerm keyVariation
  by_cases h1 : 2 ^ 255 ≤ keyValue b <;> by_cases h2 : p25519 ≤ keyValue b % 2 ^ 255 <;>
    simp only [h1, h2, ↓reduceIte]
  · rw [gamma_variant_canon _ _ _ _ _ (by decide)]
    apply congrArg (leBytes 32)
    rw [show (((3 : Fin 4) : Nat)) = 3 from rfl]
    rw [hp] at hu h2 ⊢
    generalize keyValue b = L at *
    generalize x25519UCoord b = u at *
    by_cases hc : u + (2 ^ 255 - 19) < 2 ^ 255 <;>
      simp (config := {decide := true}) only [hc, Nat.reduceMod, Nat.reduceDiv, true_and, and_true,
        and_false, ↓reduceIte] <;> omega
  · rw [gamma_variant_canon _ _ _ _ _ (by decide)]
    apply congrArg (leBytes 32)
    rw [show (((1 : Fin 4) : Nat)) = 1 from rfl]
    rw [hp] at hu h2 ⊢
    generalize keyValue b = L at *
    generalize x25519UCoord b = u at *
    by_cases hc : u + (2 ^ 255 - 19) < 2 ^ 255 <;>
      simp (config := {decide := true}) only [hc, Nat.reduceMod, Nat.reduceDiv, true_and, and_true,
        and_false, ↓reduceIte] <;> omega
  · rw [gamma_variant_canon _ _ _ _ _ (by decide)]
    apply congrArg (leBytes 32)
    rw [show (((2 : Fin 4) : Nat)) = 2 from rfl]
    rw [hp] at hu h2 ⊢
    generalize keyValue b = L at *
    generalize x25519UCoord b = u at *
    by_cases hc : u + (2 ^ 255 - 19) < 2 ^ 255 <;>
      simp (config := {decide := true}) only [hc, Nat.reduceMod, Nat.reduceDiv, true_and, and_true,
        and_false, ↓reduceIte] <;> omega
  · simp only [x25519Variant, x25519Key_canonKeyLit, ↓reduceIte]
    rw [gamma_canonKeyLit]
    apply congrArg (leBytes 32)
    rw [hp] at hu h2
    generalize keyValue b = L at *
    generalize x25519UCoord b = u at *
    omega

theorem knows_x25519KeyTerm (b : HwBytes) (tr : ExecTrace) :
    (x25519KeyTerm b).AttackerKnows tr := by
  apply DY.Bytes.AttackerKnows.prove X25519.x25519Variant.attackerKnowledge
  exact ⟨canonKeyLit b, keyVariation b, 0, by simp [x25519KeyTerm, x25519Variant, x25519TorsionVariant], Literal.attacker_knows_literalToBytes _ _⟩

/-! ## Symbolic Wire Parsing -/

theorem u8OfNat_mod16_toNat : ∀ v < 16, (UInt8.ofNat v % 16).toNat = v := by decide

theorem parseTrSignalMsg_concat_trWireMsg
    (v : Nat) (rk : DY.Bytes) (c pc : Nat) (ct pq : DY.Bytes)
    (ev : DY.TrWire.EncodingVariation) (mac : DY.Bytes)
    (hmac : mac.length = Trunc.trunc8Length) :
    let wire := DY.TrWire.trWireMsg (UInt8.ofNat v) rk (UInt32.ofNat c)
      (UInt32.ofNat pc) ct pq ev
    parseTrSignalMsg (Concat.concat wire mac) =
      some { wire := wire
             mac := mac
             version := UInt8.ofNat v % 16
             ratchetKey := rk
             counter := UInt32.ofNat c
             ciphertext := ct
             pqRatchet := pq } := by
  intro wire; unfold parseTrSignalMsg
  have hlen : (Concat.concat wire mac).length - Trunc.trunc8Length = wire.length := by
    rw [Concat.length_concat, hmac]; omega
  rw [hlen, Concat.split_concat]
  simp [Bind.bind, Pure.pure, wire, DY.TrWire.trWireMsgFields?_trWireMsg]

/-! ## Non-Emptiness of `recvRepresentations` -/

/-- Whenever `SignalMessage.tryFrom protoSignalCodec b = .ok parsed`, there is a canonical symbolic
representation `t ∈ recvRepresentations interpretation r₀ S g ms b` built from `DY.TrWire.trWireMsg`
and `Concat.concat` with `msg.ratchetKey = x25519KeyTerm parsed.senderRatchetKey.bytes.toList`,
`msg.ciphertext = litOf parsed.ciphertext`, and `msg.pqRatchet = litOf parsed.pqRatchet`. -/
theorem decrypt_recvRepresentations_nonempty_of_tryFrom
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move) (b : HwBytes)
    (parsed : SignalMessage)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed) :
    ∃ (t : DY.Bytes) (msg : TRSignalMsg),
      t ∈ recvRepresentations interpretation r₀ S g ms b ∧
      parseTrSignalMsg t = some msg ∧
      msg.ratchetKey = x25519KeyTerm parsed.senderRatchetKey.bytes.toList ∧
      msg.ciphertext = litOf parsed.ciphertext ∧
      msg.pqRatchet = litOf parsed.pqRatchet := by
  obtain ⟨v, f, mac, _hv, hb, hmac_len, hv3, hv4, hrk_len, hc_lt, hpc_lt,
          hver_m, hrk_m, hctr_m, _hpc_m, hct_m⟩ :=
    DY.Libsignal.TripleRatchet.Refinement.trWireBytes_covered_uniform b parsed hTryFrom
  let rk_term := x25519KeyTerm f.ratchetKey
  let ct_term := litOf f.ciphertext
  let pq_term := litOf parsed.pqRatchet
  let mac_term := litOf mac
  let wire := DY.TrWire.trWireMsg (UInt8.ofNat f.version) rk_term
    (UInt32.ofNat f.counter) (UInt32.ofNat f.previousCounter)
    ct_term pq_term v
  let t := Concat.concat wire mac_term
  let msg : TRSignalMsg :=
    { wire := wire
      mac := mac_term
      version := UInt8.ofNat f.version % 16
      ratchetKey := rk_term
      counter := UInt32.ofNat f.counter
      ciphertext := ct_term
      pqRatchet := pq_term }
  have hrk_gamma : gamma interpretation S g rk_term = f.ratchetKey :=
    gamma_x25519KeyTerm interpretation S g f.ratchetKey hrk_len
  have hct_gamma : gamma interpretation S g ct_term = f.ciphertext :=
    gamma_litOf interpretation S g f.ciphertext
  have hpq_gamma : gamma interpretation S g pq_term = parsed.pqRatchet :=
    gamma_litOf interpretation S g parsed.pqRatchet
  have hmac_gamma : gamma interpretation S g mac_term = mac :=
    gamma_litOf interpretation S g mac
  have hmac_sym_len : mac_term.length = Trunc.trunc8Length := by
    dsimp only [mac_term]
    rw [length_litOf, hmac_len]
    rfl
  have hparse : parseTrSignalMsg t = some msg :=
    parseTrSignalMsg_concat_trWireMsg f.version rk_term f.counter f.previousCounter
      ct_term pq_term v mac_term hmac_sym_len
  have hv_toNat : (UInt8.ofNat f.version).toNat = f.version :=
    Nat.mod_eq_of_lt (by omega)
  have hc_toNat : (UInt32.ofNat f.counter).toNat = f.counter :=
    Nat.mod_eq_of_lt hc_lt
  have hpc_toNat : (UInt32.ofNat f.previousCounter).toNat = f.previousCounter :=
    Nat.mod_eq_of_lt hpc_lt
  have hwire_gamma : gamma interpretation S g wire =
      trWireBytes (g.addr wire) v f parsed.pqRatchet := by
    dsimp only [wire]
    rw [gamma_trWireMsg, hrk_gamma, hct_gamma, hpq_gamma, hv_toNat, hc_toNat, hpc_toNat]
    cases f; rfl
  have hb_inst : b = trWireBytes (g.addr wire) v f parsed.pqRatchet ++ mac :=
    hb (g.addr wire) parsed.pqRatchet
  have ht_gamma : gamma interpretation S g t = b := by
    dsimp only [t]
    rw [gamma_concat, hwire_gamma, hmac_gamma, ← hb_inst]
  have hmacSha256Trunc8 : mac.length = 8 := hmac_len
  have htake : b.take (b.length - 8) = trWireBytes (g.addr wire) v f parsed.pqRatchet := by
    rw [hb_inst, List.length_append, hmacSha256Trunc8, Nat.add_sub_cancel]
    exact List.take_left' rfl
  have hdrop : b.drop (b.length - 8) = mac := by
    rw [hb_inst, List.length_append, hmacSha256Trunc8, Nat.add_sub_cancel]
    exact List.drop_left' rfl
  have hknows : t.AttackerKnows (runTraceMoves r₀ ms) := by
    apply Concat.attacker_knows_concat
    · exact DY.TrWire.attacker_knows_trWireMsg _ _ _ _ _ _ _ _
        (knows_x25519KeyTerm _ _) (knows_litOf _ _) (knows_litOf _ _)
    · exact knows_litOf _ _
  have hMem : t ∈ recvRepresentations interpretation r₀ S g ms b := by
    refine ⟨hknows, ht_gamma, by rw [hparse]; rfl, fun msg' hmsg' => ?_⟩
    have hmsg_eq : msg' = msg := by rw [hparse] at hmsg'; exact (Option.some.inj hmsg').symm
    subst hmsg_eq
    refine ⟨by dsimp only [msg]; rw [hwire_gamma, htake],
            by dsimp only [msg]; rw [hmac_gamma, hdrop],
            by
              dsimp only [msg, mac_term]
              unfold spqrHeaded litOf
              rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF,
                  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendState.SubF,
                  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendKey.SubF,
                  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendMsg.SubF,
                  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.RecvState.SubF,
                  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.RecvKey.SubF,
                  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.ChainKey.SubF]
              rfl,
            fun m hm_try => ?_⟩
    have hm_parsed : m = parsed := by rw [hTryFrom] at hm_try; exact (Except.ok.inj hm_try).symm
    subst hm_parsed
    refine ⟨by dsimp only [msg]; rw [hct_gamma, hct_m],
            by dsimp only [msg]; rw [hrk_gamma, hrk_m],
            by dsimp only [msg]; rw [hpq_gamma],
            ?_, ?_⟩
    · dsimp only [msg]
      rw [hc_toNat, hctr_m]
    · dsimp only [msg]
      rw [u8OfNat_mod16_toNat f.version (by omega), hver_m]
  refine ⟨t, msg, hMem, hparse, ?_, ?_, rfl⟩
  · dsimp only [msg, rk_term]; rw [hrk_m]
  · dsimp only [msg, ct_term]; rw [hct_m]

/-- Any byte sequence `b` parsed by `SignalMessage.tryFrom` has a symbolic representation in
`recvRepresentations`. -/
theorem recvRepresentations_nonempty_of_tryFrom
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move) (b : HwBytes)
    (parsed : SignalMessage)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed) :
    ∃ t, t ∈ recvRepresentations interpretation r₀ S g ms b := by
  obtain ⟨t, _, ht, -⟩ :=
    decrypt_recvRepresentations_nonempty_of_tryFrom interpretation r₀ S g ms b parsed hTryFrom
  exact ⟨t, ht⟩

end Symbolic.Swarm.CREF.TR.RecvRep
