/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTRStrong
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Refinement.EncodeWithCovered
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Honest PQ Ratchet Wire Extraction

Proves protobuf wire-decoding inversion for canonical whisper and pre-key messages and extracts an
attacker-known `Spqr.SendMsg` symbolic term matching `parsed.pqRatchet` whenever `PqFromHonest`
holds on a `MatchedPrefix`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir kdfCk computeMac messageVersion)
open DY.Libsignal.Refinement
  (WireFields EncodingVariation canonicalVariation u32Bytes decodeLittleEndianNat leNat_u32Bytes)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.RecvRep
open Symbolic.Swarm.SHARED.SpqrBytes
open Symbolic.Swarm.SHARED.HookAuth

namespace SrHonestVer

local notation "SpqrSem" => OpaqueSymbolSemantics

/-! ## Canonical Whisper Wire Decoding Inversion -/

unseal DY.Bytes in
private instance subSpqrSendMsg_srhv (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendMsg S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem gamma_trunc8_srhv (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (x : DY.Bytes) :
    gamma interpretation S g (Trunc.trunc8 x) = (gamma interpretation S g x).take 8 := by
  unfold Trunc.trunc8 gamma gamma'
  show ((({input := x} : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeTrunc (concretizeAll interpretation S g)]; rfl

private theorem gamma_kdfExtract_srhv (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (salt ikm : DY.Bytes) :
    gamma interpretation S g (KdfExtract.kdfExtract salt ikm) =
      CryptoGames.HMAC.hmacWith
        (DY.Libsignal.Refinement.sha256CompressFunction interpretation)
        (gamma interpretation S g salt) (gamma interpretation S g ikm) := by
  unfold KdfExtract.kdfExtract gamma gamma'
  show ((({salt := salt, ikm := ikm} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKdf interpretation) (concretizeAll interpretation S g)]; rfl

private theorem length_gamma_computeMac_srhv (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (macKey myIk peerIk wire : DY.Bytes) :
    (gamma interpretation S g (DY.Libsignal.TripleRatchet.computeMac macKey myIk peerIk wire)).length = 8 := by
  unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.hmac
  rw [gamma_trunc8_srhv, gamma_kdfExtract_srhv, List.length_take]
  have hlen : (CryptoGames.HMAC.hmacWith
      (DY.Libsignal.Refinement.sha256CompressFunction interpretation)
      (gamma interpretation S g macKey)
      (gamma interpretation S g (Concat.concat myIk (Concat.concat peerIk wire)))).length = 32 := by
    simp [CryptoGames.HMAC.hmacWith]
  rw [hlen]; decide

private theorem tryFrom_ok_pqRatchet_srhv {b : HwBytes} {m : SignalMessage}
    (h : SignalMessage.tryFrom protoSignalCodec b = .ok m) :
    macLength + 1 ≤ b.length ∧
      ∃ p, protoSignalCodec.decode ((b.take (b.length - macLength)).drop 1) = some p ∧
        m.pqRatchet = p.pqRatchet.getD [] := by
  unfold SignalMessage.tryFrom at h; dsimp only at h; generalize b.headD 0 >>> 4 = ver at h
  by_cases h1 : b.length < macLength + 1
  · simp only [h1, ↓reduceIte] at h; cases h
  by_cases h2 : ver < preKyberVersion
  · simp only [h1, h2, ↓reduceIte] at h; cases h
  by_cases h3 : LibsignalSession.currentVersion < ver
  · simp only [h1, h2, h3, ↓reduceIte] at h; cases h
  simp only [h1, h2, h3, ↓reduceIte] at h
  rcases hd : protoSignalCodec.decode ((b.take (b.length - macLength)).drop 1) with _ | p
  · rw [hd] at h; simp at h
  · rw [hd] at h
    cases hrk : p.ratchetKey with
    | none => simp [hrk] at h
    | some rk =>
      cases hk : PublicKey.deserialize rk with
      | error e => simp [hrk, hk, bind, Except.bind] at h
      | ok k =>
        cases hc : p.counter with
        | none => simp [hrk, hk, hc, bind, Except.bind] at h
        | some c =>
          cases hct : p.ciphertext with
          | none => simp [hrk, hk, hc, hct, bind, Except.bind] at h
          | some ct => simp [hrk, hk, hc, hct] at h; subst h; exact ⟨by omega, p, rfl, rfl⟩

private theorem paddedVarint_zero_append_inj_aux_srhv :
    ∀ (s n m pad : Nat) (r1 r2 : HwBytes), n + m + pad < s →
      DY.Libsignal.Refinement.paddedVarint n 0 ++ r1 =
        DY.Libsignal.Refinement.paddedVarint m pad ++ r2 →
      n = m ∧ pad = 0 ∧ r1 = r2
  | 0, _, _, _, _, _, hs, _ => absurd hs (Nat.not_lt_zero _)
  | s + 1, n, m, pad, r1, r2, hs, heq => by
    by_cases hn : n < 128
    · have hl : DY.Libsignal.Refinement.paddedVarint n 0 = [BitVec.ofNat 8 n] := by
        rw [DY.Libsignal.Refinement.paddedVarint]; simp [hn]
      by_cases hm : m < 128 ∧ pad = 0
      · have hr : DY.Libsignal.Refinement.paddedVarint m pad = [BitVec.ofNat 8 m] := by
          rw [DY.Libsignal.Refinement.paddedVarint]; simp [hm]
        rw [hl, hr, List.singleton_append, List.singleton_append, List.cons.injEq] at heq
        have hnm : n = m := by
          have := congrArg BitVec.toNat heq.1; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
        exact ⟨hnm, hm.2, heq.2⟩
      · have hr : DY.Libsignal.Refinement.paddedVarint m pad =
            BitVec.ofNat 8 (m % 128 + 128) ::
              DY.Libsignal.Refinement.paddedVarint (m / 128) (if m < 128 then pad - 1 else pad) := by
          rw [DY.Libsignal.Refinement.paddedVarint]; simp [hm]
        rw [hl, hr, List.singleton_append, List.cons_append, List.cons.injEq] at heq
        have hbad := congrArg BitVec.toNat heq.1; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hbad; omega
    · have hl : DY.Libsignal.Refinement.paddedVarint n 0 =
          BitVec.ofNat 8 (n % 128 + 128) :: DY.Libsignal.Refinement.paddedVarint (n / 128) 0 := by
        rw [DY.Libsignal.Refinement.paddedVarint]; simp [hn]
      by_cases hm : m < 128 ∧ pad = 0
      · have hr : DY.Libsignal.Refinement.paddedVarint m pad = [BitVec.ofNat 8 m] := by
          rw [DY.Libsignal.Refinement.paddedVarint]; simp [hm]
        rw [hl, hr, List.cons_append, List.singleton_append, List.cons.injEq] at heq
        have hbad := congrArg BitVec.toNat heq.1; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hbad; omega
      · have hr : DY.Libsignal.Refinement.paddedVarint m pad =
            BitVec.ofNat 8 (m % 128 + 128) ::
              DY.Libsignal.Refinement.paddedVarint (m / 128) (if m < 128 then pad - 1 else pad) := by
          rw [DY.Libsignal.Refinement.paddedVarint]; simp [hm]
        rw [hl, hr, List.cons_append, List.cons_append, List.cons.injEq] at heq
        have hmod : n % 128 = m % 128 := by
          have := congrArg BitVec.toNat heq.1; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
        have hs' : n / 128 + m / 128 + (if m < 128 then pad - 1 else pad) < s := by split <;> omega
        obtain ⟨hdiv, hpad, hr_eq⟩ := paddedVarint_zero_append_inj_aux_srhv s (n / 128) (m / 128)
          (if m < 128 then pad - 1 else pad) r1 r2 hs' heq.2
        have hnm : n = m := by omega
        subst hnm; simp only [hn, ↓reduceIte] at hpad; exact ⟨rfl, hpad, hr_eq⟩

private theorem paddedVarint_zero_append_inj_srhv (n m pad : Nat) (r1 r2 : HwBytes)
    (heq : DY.Libsignal.Refinement.paddedVarint n 0 ++ r1 =
      DY.Libsignal.Refinement.paddedVarint m pad ++ r2) : n = m ∧ pad = 0 ∧ r1 = r2 :=
  paddedVarint_zero_append_inj_aux_srhv (n + m + pad + 1) n m pad r1 r2 (by omega) heq

private theorem decodeKey_encodeField_zero_inv_srhv {tag t' : Nat} {wt : LibsignalProtoCodec.WireType}
    {x : DY.Libsignal.Refinement.PbValue} {rest rest0 : HwBytes}
    (hwt : DY.Libsignal.Refinement.WireTypeOk tag x)
    (hkey : decodeKey (DY.Libsignal.Refinement.encodeField tag 0 0 x ++ rest) =
      some ((t', wt), rest0)) : t' = tag ∧ wt = x.wireType ∧ rest0 = x.body 0 ++ rest := by
  obtain ⟨kp, hbs, _, _, _⟩ := DY.Libsignal.Refinement.decodeKey_inv hkey
  rw [DY.Libsignal.Refinement.encodeField_eq, List.append_assoc] at hbs
  obtain ⟨hnum, _, hrest⟩ := paddedVarint_zero_append_inj_srhv _ _ _ _ _ hbs
  have hwn1 : x.wireType.toNat < 8 := by cases x.wireType <;> decide
  have hwn2 : wt.toNat < 8 := by cases wt <;> decide
  rw [← DY.TrWire.PbValue.wireType_toNat hwt] at hnum
  have htag : t' = tag := by omega
  have hwt_nat : wt.toNat = x.wireType.toNat := by omega
  have hwt_eq : wt = x.wireType := by
    have h1 := DY.Libsignal.Refinement.WireType.ofNat?_toNat wt
    have h2 := DY.Libsignal.Refinement.WireType.ofNat?_toNat x.wireType
    rw [hwt_nat, h2] at h1; exact Option.some.inj h1.symm
  exact ⟨htag, hwt_eq, hrest.symm⟩

private theorem mergeBytes_body_zero_inv_srhv {wt : LibsignalProtoCodec.WireType} {b v rest rest' : HwBytes}
    (hm : mergeBytes wt ((DY.TrWire.PbValue.bytes b).body 0 ++ rest) =
      some (v, rest')) : v = b ∧ rest' = rest := by
  obtain ⟨_, vp, hbs, _, _⟩ := DY.Libsignal.Refinement.mergeBytes_inv hm
  simp only [DY.TrWire.PbValue.body, List.append_assoc] at hbs
  obtain ⟨hlen, _, hbr⟩ := paddedVarint_zero_append_inj_srhv _ _ _ _ _ hbs
  obtain ⟨hvb, hrr⟩ := List.append_inj hbr hlen; exact ⟨hvb.symm, hrr.symm⟩

private theorem mergeUint32_body_zero_inv_srhv {wt : LibsignalProtoCodec.WireType} {n : Nat} {v : BitVec 32} {rest rest' : HwBytes}
    (hm : mergeUint32 wt ((DY.TrWire.PbValue.varint n).body 0 ++ rest) =
      some (v, rest')) : v = BitVec.ofNat 32 n ∧ rest' = rest := by
  obtain ⟨_, m, vp, hbs, rfl, _, _⟩ := DY.Libsignal.Refinement.mergeUint32_inv hm
  simp only [DY.TrWire.PbValue.body] at hbs
  obtain ⟨hnm, _, hrr⟩ := paddedVarint_zero_append_inj_srhv _ _ _ _ _ hbs
  subst hnm; exact ⟨rfl, hrr.symm⟩

private theorem mergeField_body_zero_inv_srhv {m m' : ProtoSignalMessage} {tag : Nat}
    {x : DY.Libsignal.Refinement.PbValue} {rest rest' : HwBytes}
    (htag1 : 1 ≤ tag) (htag6 : tag ≤ 6) (hwt : DY.Libsignal.Refinement.WireTypeOk tag x)
    (hm : mergeField m tag x.wireType (x.body 0 ++ rest) = some (m', rest')) :
    m' = DY.Libsignal.Refinement.setField m tag x ∧ rest' = rest := by
  rcases tag with _ | _ | _ | _ | _ | _ | _ | t
  · omega
  · cases x with
    | bytes b =>
      simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨v, r⟩, hmb, rfl, rfl⟩ := hm; obtain ⟨rfl, rfl⟩ := mergeBytes_body_zero_inv_srhv hmb; exact ⟨rfl, rfl⟩
    | varint _ | unknown _ _ => simp [DY.Libsignal.Refinement.WireTypeOk] at hwt
  · cases x with
    | varint n =>
      simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨v, r⟩, hmu, rfl, rfl⟩ := hm; obtain ⟨rfl, rfl⟩ := mergeUint32_body_zero_inv_srhv hmu; exact ⟨rfl, rfl⟩
    | bytes _ | unknown _ _ => simp [DY.Libsignal.Refinement.WireTypeOk] at hwt
  · cases x with
    | varint n =>
      simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨v, r⟩, hmu, rfl, rfl⟩ := hm; obtain ⟨rfl, rfl⟩ := mergeUint32_body_zero_inv_srhv hmu; exact ⟨rfl, rfl⟩
    | bytes _ | unknown _ _ => simp [DY.Libsignal.Refinement.WireTypeOk] at hwt
  · cases x with
    | bytes b =>
      simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨v, r⟩, hmb, rfl, rfl⟩ := hm; obtain ⟨rfl, rfl⟩ := mergeBytes_body_zero_inv_srhv hmb; exact ⟨rfl, rfl⟩
    | varint _ | unknown _ _ => simp [DY.Libsignal.Refinement.WireTypeOk] at hwt
  · cases x with
    | bytes b =>
      simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨v, r⟩, hmb, rfl, rfl⟩ := hm; obtain ⟨rfl, rfl⟩ := mergeBytes_body_zero_inv_srhv hmb; exact ⟨rfl, rfl⟩
    | varint _ | unknown _ _ => simp [DY.Libsignal.Refinement.WireTypeOk] at hwt
  · cases x with
    | bytes b =>
      simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨v, r⟩, hmb, rfl, rfl⟩ := hm; obtain ⟨rfl, rfl⟩ := mergeBytes_body_zero_inv_srhv hmb; exact ⟨rfl, rfl⟩
    | varint _ | unknown _ _ => simp [DY.Libsignal.Refinement.WireTypeOk] at hwt
  · omega

private theorem decodeLoop_encodeField_zero_inv_srhv {fuel : Nat} {m r : ProtoSignalMessage}
    {tag : Nat} {x : DY.Libsignal.Refinement.PbValue} {rest : HwBytes}
    (htag1 : 1 ≤ tag) (htag6 : tag ≤ 6) (hwt : DY.Libsignal.Refinement.WireTypeOk tag x)
    (hd : decodeLoop fuel m (DY.Libsignal.Refinement.encodeField tag 0 0 x ++ rest) = some r) :
    ∃ fuel', fuel = fuel' + 1 ∧
      decodeLoop fuel' (DY.Libsignal.Refinement.setField m tag x) rest = some r := by
  have hne : DY.Libsignal.Refinement.encodeField tag 0 0 x ++ rest ≠ [] := by
    rw [DY.Libsignal.Refinement.encodeField_eq, List.append_assoc]
    exact List.append_ne_nil_of_left_ne_nil (DY.Libsignal.Refinement.paddedVarint_ne_nil _ _) _
  obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hne
  cases fuel with
  | zero => rw [hbs] at hd; simp [decodeLoop] at hd
  | succ fuel' =>
    rw [hbs] at hd; simp only [decodeLoop] at hd; split at hd
    · cases hd
    · next t' wt rest0 hkey =>
      split at hd
      · cases hd
      · next m' rest' hmerge =>
        rw [← hbs] at hkey; obtain ⟨rfl, rfl, rfl⟩ := decodeKey_encodeField_zero_inv_srhv hwt hkey
        obtain ⟨rfl, rfl⟩ := mergeField_body_zero_inv_srhv htag1 htag6 hwt hmerge; exact ⟨fuel', rfl, hd⟩

private theorem trWireBytes_canonical_drop_one_srhv (addr pq : HwBytes) (f : WireFields) :
    (trWireBytes addr canonicalVariation f pq).drop 1 =
      DY.Libsignal.Refinement.encodeField 1 0 0 (.bytes (0x05#8 :: f.ratchetKey)) ++
      (DY.Libsignal.Refinement.encodeField 2 0 0 (.varint f.counter) ++
      (DY.Libsignal.Refinement.encodeField 3 0 0 (.varint f.previousCounter) ++
      (DY.Libsignal.Refinement.encodeField 4 0 0 (.bytes f.ciphertext) ++
      ((if pq = [] then [] else DY.Libsignal.Refinement.encodeField 5 0 0 (.bytes pq)) ++
       (if addr = [] then [] else DY.Libsignal.Refinement.encodeField 6 0 0 (.bytes addr)))))) := by
  rw [DY.Libsignal.TripleRatchet.Refinement.trWireBytes_canonical]
  simp [DY.Libsignal.Refinement.encodeWith, canonicalVariation,
    DY.TrWire.FieldItem.encode,
    DY.Libsignal.Refinement.knownValue?, List.append_assoc]

private theorem decode_trWireBytes_canonical_inv_srhv {addr pq : HwBytes} {f : WireFields} {p : ProtoSignalMessage}
    (hd : protoSignalCodec.decode ((trWireBytes addr canonicalVariation f pq).drop 1) = some p) :
    p.ratchetKey = some (0x05#8 :: f.ratchetKey) ∧ p.counter = some (BitVec.ofNat 32 f.counter) ∧
    p.previousCounter = some (BitVec.ofNat 32 f.previousCounter) ∧ p.ciphertext = some f.ciphertext ∧
    p.pqRatchet.getD [] = pq := by
  change decodeLoop ((trWireBytes addr canonicalVariation f pq).drop 1).length emptyProtoSignalMessage
    ((trWireBytes addr canonicalVariation f pq).drop 1) = some p at hd
  generalize ((trWireBytes addr canonicalVariation f pq).drop 1).length = fuel at hd
  rw [trWireBytes_canonical_drop_one_srhv] at hd
  obtain ⟨fuel1, _, hd1⟩ := decodeLoop_encodeField_zero_inv_srhv (by omega) (by omega)
    (by simp [DY.Libsignal.Refinement.WireTypeOk]) hd
  obtain ⟨fuel2, _, hd2⟩ := decodeLoop_encodeField_zero_inv_srhv (by omega) (by omega)
    (by simp [DY.Libsignal.Refinement.WireTypeOk]) hd1
  obtain ⟨fuel3, _, hd3⟩ := decodeLoop_encodeField_zero_inv_srhv (by omega) (by omega)
    (by simp [DY.Libsignal.Refinement.WireTypeOk]) hd2
  obtain ⟨fuel4, _, hd4⟩ := decodeLoop_encodeField_zero_inv_srhv (by omega) (by omega)
    (by simp [DY.Libsignal.Refinement.WireTypeOk]) hd3
  by_cases hpq : pq = [] <;> by_cases ha : addr = []
  · simp only [hpq, ha, ↓reduceIte, List.append_nil, decodeLoop, Option.some.injEq] at hd4
    subst hd4; exact ⟨rfl, rfl, rfl, rfl, hpq.symm⟩
  · simp only [hpq, ha, ↓reduceIte, List.nil_append] at hd4
    rw [← List.append_nil (DY.Libsignal.Refinement.encodeField 6 0 0 (.bytes addr))] at hd4
    obtain ⟨fuel6, _, hd6⟩ := decodeLoop_encodeField_zero_inv_srhv (by omega) (by omega)
      (by simp [DY.Libsignal.Refinement.WireTypeOk]) hd4
    simp only [decodeLoop, Option.some.injEq] at hd6; subst hd6; exact ⟨rfl, rfl, rfl, rfl, hpq.symm⟩
  · simp only [hpq, ha, ↓reduceIte, List.append_nil] at hd4
    rw [← List.append_nil (DY.Libsignal.Refinement.encodeField 5 0 0 (.bytes pq))] at hd4
    obtain ⟨fuel5, _, hd5⟩ := decodeLoop_encodeField_zero_inv_srhv (by omega) (by omega)
      (by simp [DY.Libsignal.Refinement.WireTypeOk]) hd4
    simp only [decodeLoop, Option.some.injEq] at hd5; subst hd5; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp only [hpq, ha, ↓reduceIte] at hd4
    obtain ⟨fuel5, _, hd5⟩ := decodeLoop_encodeField_zero_inv_srhv (by omega) (by omega)
      (by simp [DY.Libsignal.Refinement.WireTypeOk]) hd4
    rw [← List.append_nil (DY.Libsignal.Refinement.encodeField 6 0 0 (.bytes addr))] at hd5
    obtain ⟨fuel6, _, hd6⟩ := decodeLoop_encodeField_zero_inv_srhv (by omega) (by omega)
      (by simp [DY.Libsignal.Refinement.WireTypeOk]) hd5
    simp only [decodeLoop, Option.some.injEq] at hd6; subst hd6; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem tryFrom_trWireBytes_canonical_pqRatchet_srhv {addr pq mac : HwBytes} {f : WireFields}
    {m : SignalMessage} (hmac : mac.length = 8)
    (htry : SignalMessage.tryFrom protoSignalCodec (trWireBytes addr canonicalVariation f pq ++ mac) = .ok m) :
    m.pqRatchet = pq := by
  have hmac_len : mac.length = macLength := hmac
  obtain ⟨_, p, hdec, hpq⟩ := tryFrom_ok_pqRatchet_srhv htry
  have htake : (trWireBytes addr canonicalVariation f pq ++ mac).take
      ((trWireBytes addr canonicalVariation f pq ++ mac).length - macLength) =
      trWireBytes addr canonicalVariation f pq := by
    rw [List.length_append, hmac_len, Nat.add_sub_cancel, List.take_left' rfl]
  rw [htake] at hdec
  obtain ⟨_, _, _, _, hpq_f⟩ := decode_trWireBytes_canonical_inv_srhv hdec
  exact hpq.trans hpq_f

private theorem gamma_trHonestWireMsg_srhv (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (rk : DY.Bytes) (ns pn : UInt32) (ct pq : DY.Bytes) :
    let wire := trHonestWireMsg rk ns pn ct pq
    gamma interpretation S g wire =
      trWireBytes (g.addr wire) canonicalVariation
        { version := 4, ratchetKey := gamma interpretation S g rk,
          counter := ns.toNat, previousCounter := pn.toNat,
          ciphertext := gamma interpretation S g ct }
        (gamma interpretation S g pq) := by
  intro wire; dsimp only [wire, trHonestWireMsg]
  exact DY.Libsignal.Composed.Refinement.gamma_trWireMsg interpretation S g messageVersion rk ns pn ct pq canonicalVariation

/-! ## Pre-Key Wire Decoding and Inner Message Extraction -/

open DY.Libsignal.PQXDH.Refinement (PreKeyProto versionByte wirePrekeyTag)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.LibsignalProtoCodec (encodeBytesField encodeUint32Field
  decodeKey_encodeKey mergeBytes_encode mergeUint32_encode encodeVarint_ne_nil)

private def pLoopsTo_srhv (m : PreKeyProto) (bs : HwBytes) (r : PreKeyProto) : Prop :=
  ∀ n, bs.length ≤ n → decodePreKeyLoop n m bs = some r

private theorem pLoopsTo_nil_srhv (m : PreKeyProto) : pLoopsTo_srhv m [] m := by
  intro n _; cases n <;> simp [decodePreKeyLoop]

private theorem pLoopsTo_field_srhv (t : Nat) (wt : CryptoVerification.LibsignalProtoCodec.WireType)
    (h1 : 1 ≤ t) (h2 : t < 2 ^ 28) (m m' r : PreKeyProto) (body rest : HwBytes)
    (hmerge : mergePreKeyField m t wt (body ++ rest) = some (m', rest))
    (h : pLoopsTo_srhv m' rest r) :
    pLoopsTo_srhv m (encodeKey t wt ++ (body ++ rest)) r := by
  intro n hn
  have hkey := decodeKey_encodeKey t wt (body ++ rest) h1 h2
  have hpos : 0 < (encodeKey t wt).length := List.length_pos_iff.mpr (encodeVarint_ne_nil _)
  simp only [List.length_append] at hn
  obtain ⟨b, bs, hk⟩ := List.exists_cons_of_ne_nil
    (List.length_pos_iff.mp (by simp only [List.length_append]; omega) :
      encodeKey t wt ++ (body ++ rest) ≠ [])
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [hk] at hkey ⊢; simp only [decodePreKeyLoop, hkey, hmerge]; exact h n' (by omega)

private theorem fieldBytes_split_srhv (t : Nat) (v rest : HwBytes) :
    encodeBytesField t (some v) ++ rest =
      encodeKey t .lengthDelimited ++
        ((CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 v.length) ++ v) ++ rest) := by
  simp [encodeBytesField]

private theorem fieldUint32_split_srhv (t : Nat) (x : BitVec 32) (rest : HwBytes) :
    encodeUint32Field t (some x) ++ rest =
      encodeKey t .varint ++
        (CryptoVerification.LibsignalProtoCodec.encodeVarint (x.zeroExtend 64) ++ rest) := by
  simp [encodeUint32Field]

private theorem pLoopsTo_bytes_srhv (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (o : Option HwBytes) (upd : Option HwBytes → PreKeyProto) (rest : HwBytes) (r : PreKeyProto)
    (hl : ∀ v, o = some v → v.length < 2 ^ 64)
    (hm : ∀ bs, mergePreKeyField (upd none) t .lengthDelimited bs =
      (mergeBytes .lengthDelimited bs).map fun (v, r) => (upd (some v), r))
    (h : pLoopsTo_srhv (upd o) rest r) :
    pLoopsTo_srhv (upd none) (encodeBytesField t o ++ rest) r := by
  cases o with
  | none => simpa [encodeBytesField] using h
  | some v =>
    rw [fieldBytes_split_srhv]; refine pLoopsTo_field_srhv t _ h1 h2 _ _ _ _ _ ?_ h
    rw [hm, List.append_assoc, mergeBytes_encode v rest (hl v rfl)]; rfl

private theorem pLoopsTo_uint32_srhv (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (o : Option (BitVec 32)) (upd : Option (BitVec 32) → PreKeyProto) (rest : HwBytes) (r : PreKeyProto)
    (hm : ∀ bs, mergePreKeyField (upd none) t .varint bs =
      (mergeUint32 .varint bs).map fun (v, r) => (upd (some v), r))
    (h : pLoopsTo_srhv (upd o) rest r) :
    pLoopsTo_srhv (upd none) (encodeUint32Field t o ++ rest) r := by
  cases o with
  | none => simpa [encodeUint32Field] using h
  | some x =>
    rw [fieldUint32_split_srhv]; refine pLoopsTo_field_srhv t _ h1 h2 _ _ _ _ _ ?_ h
    rw [hm, mergeUint32_encode x rest]; rfl

private def preKeyLengthsFit_srhv (p : PreKeyProto) : Prop :=
  ∀ v : HwBytes, p.baseKey = some v ∨ p.identityKey = some v ∨ p.message = some v ∨
    p.kyberCiphertext = some v → v.length < 2 ^ 64

private theorem decodePreKey_encode_srhv (p : PreKeyProto) (h : preKeyLengthsFit_srhv p) :
    decodePreKey (PreKeyProto.encode p) = some p := by
  obtain ⟨reg, pk, spk, kpk, kct, bk, ik, msg⟩ := p
  have hbk : ∀ v, bk = some v → v.length < 2 ^ 64 := fun v hv => h v (Or.inl hv)
  have hik : ∀ v, ik = some v → v.length < 2 ^ 64 := fun v hv => h v (Or.inr (Or.inl hv))
  have hmsg : ∀ v, msg = some v → v.length < 2 ^ 64 := fun v hv => h v (Or.inr (Or.inr (Or.inl hv)))
  have hkct : ∀ v, kct = some v → v.length < 2 ^ 64 := fun v hv => h v (Or.inr (Or.inr (Or.inr hv)))
  have hloop : pLoopsTo_srhv emptyPreKeyMsg
      (encodeUint32Field 1 pk ++ (encodeBytesField 2 bk ++ (encodeBytesField 3 ik ++
        (encodeBytesField 4 msg ++ (encodeUint32Field 5 reg ++ (encodeUint32Field 6 spk ++
          (encodeUint32Field 7 kpk ++ (encodeBytesField 8 kct ++ []))))))))
      ⟨reg, pk, spk, kpk, kct, bk, ik, msg⟩ :=
    pLoopsTo_uint32_srhv 1 (by omega) (by omega) pk (fun o => ⟨none, o, none, none, none, none, none, none⟩) _ _ (fun _ => rfl) <|
    pLoopsTo_bytes_srhv 2 (by omega) (by omega) bk (fun o => ⟨none, pk, none, none, none, o, none, none⟩) _ _ hbk (fun _ => rfl) <|
    pLoopsTo_bytes_srhv 3 (by omega) (by omega) ik (fun o => ⟨none, pk, none, none, none, bk, o, none⟩) _ _ hik (fun _ => rfl) <|
    pLoopsTo_bytes_srhv 4 (by omega) (by omega) msg (fun o => ⟨none, pk, none, none, none, bk, ik, o⟩) _ _ hmsg (fun _ => rfl) <|
    pLoopsTo_uint32_srhv 5 (by omega) (by omega) reg (fun o => ⟨o, pk, none, none, none, bk, ik, msg⟩) _ _ (fun _ => rfl) <|
    pLoopsTo_uint32_srhv 6 (by omega) (by omega) spk (fun o => ⟨reg, pk, o, none, none, bk, ik, msg⟩) _ _ (fun _ => rfl) <|
    pLoopsTo_uint32_srhv 7 (by omega) (by omega) kpk (fun o => ⟨reg, pk, spk, o, none, bk, ik, msg⟩) _ _ (fun _ => rfl) <|
    pLoopsTo_bytes_srhv 8 (by omega) (by omega) kct (fun o => ⟨reg, pk, spk, kpk, o, bk, ik, msg⟩) _ _ hkct (fun _ => rfl) <|
    pLoopsTo_nil_srhv _
  have henc : PreKeyProto.encode ⟨reg, pk, spk, kpk, kct, bk, ik, msg⟩ =
      encodeUint32Field 1 pk ++ (encodeBytesField 2 bk ++ (encodeBytesField 3 ik ++
        (encodeBytesField 4 msg ++ (encodeUint32Field 5 reg ++ (encodeUint32Field 6 spk ++
          (encodeUint32Field 7 kpk ++ (encodeBytesField 8 kct ++ []))))))) := by
    simp only [PreKeyProto.encode, List.append_assoc, List.append_nil]
  rw [decodePreKey, henc]; exact hloop _ (Nat.le_refl _)

private theorem versionByte_four_srhv :
    (DY.Libsignal.PQXDH.Refinement.versionByte 4#8 >>> 4).toNat = 4 := by decide

theorem ecKeyParses_ecKey_of_32 {k : HwBytes} (hk : k.length = 32) :
    ecKeyParses (ecKey k) = true := by simp [ecKeyParses, ecKey, hk]

theorem parsePreKeyWire_preKeyWire (preKeyId : Option (BitVec 32))
    (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes)
    (inner : CryptoGames.LibsignalSession.SignalMessage)
    (hek : 32 ≤ ek.length) (hek' : ek.length + 1 < 2 ^ 64) (hik : ecKeyParses ik = true)
    (hik' : ik.length < 2 ^ 64) (hct : ct.length + 1 < 2 ^ 64) (hmsg : msg.length < 2 ^ 64)
    (hin : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg = .ok inner) :
    parsePreKeyWire (preKeyWire preKeyId spkId kpkId regId ik ek ct msg) =
      some { version := 4, preKeyId, signedPreKeyId := spkId, kyberPreKeyId := some kpkId,
             kyberCiphertext := some (kyberKey ct), baseKey := ecKey ek, identityKey := ik,
             message := msg, inner } := by
  have hfit : preKeyLengthsFit_srhv
      { registrationId := some regId, preKeyId, signedPreKeyId := some spkId,
        kyberPreKeyId := some kpkId, kyberCiphertext := some (kyberKey ct),
        baseKey := some (ecKey ek), identityKey := some ik, message := some msg } := by
    intro v hv; simp only [Option.some.injEq] at hv; rcases hv with rfl | rfl | rfl | rfl
    · simp only [ecKey, List.length_cons]; omega
    · exact hik'
    · exact hmsg
    · simp only [kyberKey, List.length_cons]; omega
  have hbk : ecKeyParses (ecKey ek) = true := by simp [ecKeyParses, ecKey]; omega
  have hcond : (4 < 3 ∨ 4 < 4) ↔ False := by decide
  dsimp only [ecKey, kyberKey] at hfit hbk
  simp only [parsePreKeyWire, preKeyWire, ↓reduceIte, parsePreKey, versionByte_four_srhv, hcond,
    decodePreKey_encode_srhv _ hfit, hbk, hik, Option.isSome_some, Bool.true_or, Bool.and_self]
  rw [hin]; rfl

private theorem sentBody_preKeyWire_eq_map_srhv (preKeyId : Option (BitVec 32))
    (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes) :
    sentBody (preKeyWire preKeyId spkId kpkId regId ik ek ct msg) =
      (parsePreKeyWire (preKeyWire preKeyId spkId kpkId regId ik ek ct msg)).map (·.message) := by
  have hne : wirePrekeyTag ≠ wireWhisperTag := by decide
  unfold sentBody
  cases h : preKeyWire preKeyId spkId kpkId regId ik ek ct msg with
  | nil => simp [preKeyWire] at h
  | cons b rest =>
    have hb : b = wirePrekeyTag := by simp [preKeyWire] at h; exact h.1.symm
    subst hb; simp only [hne, ↓reduceIte]

theorem sentBody_preKeyWire {preKeyId : Option (BitVec 32)} {spkId kpkId regId : BitVec 32}
    {ik ek ct msg : HwBytes} {inner : CryptoGames.LibsignalSession.SignalMessage}
    (hek : 32 ≤ ek.length) (hek' : ek.length + 1 < 2 ^ 64) (hik : ecKeyParses ik = true)
    (hik' : ik.length < 2 ^ 64) (hct : ct.length + 1 < 2 ^ 64) (hmsg : msg.length < 2 ^ 64)
    (hin : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg = .ok inner) :
    sentBody (preKeyWire preKeyId spkId kpkId regId ik ek ct msg) = some msg := by
  rw [sentBody_preKeyWire_eq_map_srhv,
    parsePreKeyWire_preKeyWire preKeyId spkId kpkId regId ik ek ct msg inner hek hek' hik hik' hct hmsg hin]
  rfl

theorem sentBody_preKeyWire_eq_some_inv {preKeyId : Option (BitVec 32)} {spkId kpkId regId : BitVec 32}
    {ik ek ct msg b_sent : HwBytes}
    (hek' : ek.length + 1 < 2 ^ 64) (hik' : ik.length < 2 ^ 64)
    (hct : ct.length + 1 < 2 ^ 64) (hmsg : msg.length < 2 ^ 64)
    (hsb : sentBody (preKeyWire preKeyId spkId kpkId regId ik ek ct msg) = some b_sent) :
    b_sent = msg := by
  have hfit : preKeyLengthsFit_srhv
      { registrationId := some regId, preKeyId, signedPreKeyId := some spkId,
        kyberPreKeyId := some kpkId, kyberCiphertext := some (kyberKey ct),
        baseKey := some (ecKey ek), identityKey := some ik, message := some msg } := by
    intro v hv; simp only [Option.some.injEq] at hv; rcases hv with rfl | rfl | rfl | rfl
    · simp only [ecKey, List.length_cons]; omega
    · exact hik'
    · exact hmsg
    · simp only [kyberKey, List.length_cons]; omega
  have hcond : (4 < 3 ∨ 4 < 4) ↔ False := by decide
  rw [sentBody_preKeyWire_eq_map_srhv] at hsb
  dsimp only [ecKey, kyberKey] at hfit
  simp only [parsePreKeyWire, preKeyWire, ↓reduceIte, parsePreKey, versionByte_four_srhv, hcond,
    decodePreKey_encode_srhv _ hfit] at hsb
  split at hsb
  · split at hsb
    · simp only [Option.map_some, Option.some.injEq] at hsb; exact hsb.symm
    · cases hsb
  · cases hsb

private theorem le_length_encodeBytesField_some_srhv (t : Nat) (v : HwBytes) :
    v.length ≤ (encodeBytesField t (some v)).length := by
  simp only [encodeBytesField, List.length_append]; omega

/-- When `(preKeyWire preKeyId spkId kpkId regId ik ek ct msg).length < 2 ^ 64` and `sentBody`
yields `some b_sent`, `b_sent = msg`. -/
theorem preKeySend_sentBody_strip_srhv
    {preKeyId : Option (BitVec 32)} {spkId kpkId regId : BitVec 32}
    {ik ek ct msg b_sent : HwBytes}
    (hlen : (preKeyWire preKeyId spkId kpkId regId ik ek ct msg).length < 2 ^ 64)
    (hsb : sentBody (preKeyWire preKeyId spkId kpkId regId ik ek ct msg) = some b_sent) :
    b_sent = msg := by
  have h2 := le_length_encodeBytesField_some_srhv 2 (ecKey ek)
  have h3 := le_length_encodeBytesField_some_srhv 3 ik
  have h4 := le_length_encodeBytesField_some_srhv 4 msg
  have h8 := le_length_encodeBytesField_some_srhv 8 (kyberKey ct)
  simp only [ecKey, kyberKey, List.length_cons] at h2 h8
  have hlen' : (encodeBytesField 2 (some (5#8 :: ek))).length +
      (encodeBytesField 3 (some ik)).length + (encodeBytesField 4 (some msg)).length +
      (encodeBytesField 8 (some (8#8 :: ct))).length < 2 ^ 64 := by
    simp only [preKeyWire, PreKeyProto.encode, ecKey, kyberKey, List.length_cons, List.length_append] at hlen; omega
  exact sentBody_preKeyWire_eq_some_inv (by omega) (by omega) (by omega) (by omega) hsb

/-! ## Honest Send Provenance -/

/-- Every `.send m` event in `acc` has wire length `< 2 ^ 64`. -/
def SendsFit (acc : List MachineEvent) : Prop :=
  ∀ m : HwBytes, .send m ∈ acc → m.length < 2 ^ 64

open Symbolic.Swarm.CREF.TR.FreshSigma (StEntry TREntry run_bind_fst run_bind_snd
  at?_eq_some_of_getLocalState_some)
open Symbolic.Swarm.CREF.TR.G1 (TRStateStoredAt le_runMoves_fst
  mem_availableStates_of_trStateStoredAt)

private def RunsSrhv {α : Type} (x : Traceful α) (tr : ExecTrace) (a : α) (tr' : ExecTrace) : Prop :=
  (x.run tr).1 = some a ∧ (x.run tr).2.val = tr'
private def FailsSrhv {α : Type} (x : Traceful α) (tr tr' : ExecTrace) : Prop :=
  (x.run tr).1 = none ∧ (x.run tr).2.val = tr'

private theorem RunsSrhv.bind {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr tr1 tr2 : ExecTrace}
    {a : α} {b : β} (h1 : RunsSrhv x tr a tr1) (h2 : RunsSrhv (f a) tr1 b tr2) : RunsSrhv (x >>= f) tr b tr2 := by
  obtain ⟨h1a, h1b⟩ := h1; obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, ht⟩; rw [hx] at h1a h1b; cases h1a; cases h1b
  rcases hf : (f a).run t with ⟨o', t', ht'⟩; rw [hf] at h2a h2b; cases h2a; cases h2b
  refine ⟨?_, ?_⟩ <;> rw [Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem FailsSrhv.bind_left {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr tr' : ExecTrace} (h : FailsSrhv x tr tr') : FailsSrhv (x >>= f) tr tr' := by
  obtain ⟨h1, h2⟩ := h; rcases hx : x.run tr with ⟨o, t, ht⟩; rw [hx] at h1 h2; cases h1; cases h2
  refine ⟨?_, ?_⟩ <;> rw [Traceful.run_bind, hx]

private theorem FailsSrhv.bind_right {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr tr1 tr2 : ExecTrace} {a : α} (h1 : RunsSrhv x tr a tr1) (h2 : FailsSrhv (f a) tr1 tr2) :
    FailsSrhv (x >>= f) tr tr2 := by
  obtain ⟨h1a, h1b⟩ := h1; obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, ht⟩; rw [hx] at h1a h1b; cases h1a; cases h1b
  rcases hf : (f a).run t with ⟨o', t', ht'⟩; rw [hf] at h2a h2b; cases h2a; cases h2b
  refine ⟨?_, ?_⟩ <;> rw [Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem RunsSrhv.pure {α : Type} (a : α) (tr : ExecTrace) : RunsSrhv (pure a : Traceful α) tr a tr := by
  unfold RunsSrhv; simp only [Traceful.run_pure, and_self]
private theorem RunsSrhv.appendEntry {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    RunsSrhv (DY.appendEntry e) tr tr.length (tr.append e) := by
  unfold RunsSrhv; simp only [Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk, and_self]
private theorem RunsSrhv.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : p) :
    RunsSrhv (_root_.guard p : Traceful Unit) tr () tr := by
  unfold RunsSrhv; simp only [_root_.guard, h, ↓reduceIte, Traceful.run_pure, and_self]
private theorem FailsSrhv.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : ¬ p) :
    FailsSrhv (_root_.guard p : Traceful Unit) tr tr := by
  unfold FailsSrhv; simp only [_root_.guard, h, ↓reduceIte, Traceful.run_failure, and_self]
private theorem RunsSrhv.genRand (tr : ExecTrace) (n : Nat) :
    RunsSrhv (Random.genRand n) tr (randTerm tr.length n) (tr.append (Random.ExecEntryT.mk n)) := by
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1]
  exact RunsSrhv.bind (RunsSrhv.appendEntry tr _) (RunsSrhv.pure _ _)
private theorem RunsSrhv.sendMessage (tr : ExecTrace) (b : DY.Bytes) :
    RunsSrhv (Network.sendMessage b) tr tr.length (tr.append (Network.ExecEntryT.mk b)) := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1]; exact RunsSrhv.appendEntry _ _
private theorem RunsSrhv.logEvent (tr : ExecTrace) (ev : TREvent) :
    RunsSrhv (ProtocolEvent.logEvent ev) tr () (tr.append (⟨ev⟩ : TREntry)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact RunsSrhv.bind (RunsSrhv.appendEntry tr _) (RunsSrhv.pure _ _)
private theorem RunsSrhv.storeLocalState (tr : ExecTrace) (me : Participant) (st : TRState) :
    RunsSrhv (PersistentLocalState.storeLocalState me st) tr tr.length (tr.append (⟨⟨me, st⟩⟩ : StEntry)) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]
  exact RunsSrhv.appendEntry _ _
private theorem RunsSrhv.traceLength (tr : ExecTrace) : RunsSrhv TripleRatchet.traceLength tr tr.length tr := by
  unfold RunsSrhv TripleRatchet.traceLength; simp only [Traceful.run_mk, and_self]

private theorem getLocalState_run_eq_self_srhv (p : Participant) (idx : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState p idx : Traceful TRState).run tr).2.val = tr := by
  (simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]; unfold _root_.guard)
  rw [run_bind_snd, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? idx : Option StEntry) with _ | ⟨⟨q, st⟩⟩
  · rfl
  · dsimp only; rw [Traceful.run_pure]; dsimp only
    change (((if q = p then pure () else failure : Traceful Unit) >>= fun _ => pure st).run tr).2.val = tr
    by_cases hq : q = p
    · rw [ite_eq_left_iff.mpr fun h => absurd hq h]; simp only [Traceful.run_bind, Traceful.run_pure]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hq]; simp only [Traceful.run_bind, Traceful.run_failure]

private theorem RunsSrhv.getLocalState {tr : ExecTrace} {me : Participant} {h : Nat} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState me h : Traceful TRState).run tr).1 = some st) :
    RunsSrhv (PersistentLocalState.getLocalState me h : Traceful TRState) tr st tr :=
  ⟨hst, getLocalState_run_eq_self_srhv me h tr⟩
private theorem FailsSrhv.getLocalState {tr : ExecTrace} {me : Participant} {h : Nat}
    (hst : ((PersistentLocalState.getLocalState me h : Traceful TRState).run tr).1 = none) :
    FailsSrhv (PersistentLocalState.getLocalState me h : Traceful TRState) tr tr :=
  ⟨hst, getLocalState_run_eq_self_srhv me h tr⟩
private theorem RunsSrhv.receiveMessage {tr : ExecTrace} {h : Nat} {b : DY.Bytes}
    (hb : (tr.at? h : Option Network.ExecEntryT) = some ⟨b⟩) : RunsSrhv (Network.receiveMessage h) tr b tr := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  refine RunsSrhv.bind ?_ (RunsSrhv.pure _ _)
  unfold RunsSrhv
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk, hb, and_self]
private theorem RunsSrhv.logMessageKeyAndStore (tr : ExecTrace) (me : Participant)
    (s : TripleRatchet.SessionInfo) (dir : TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes)
    (n : UInt32) (r parentStateIdx : Nat) (st : TRState) :
    RunsSrhv (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r parentStateIdx st)
      tr (tr.length + 1)
      ((tr.append (⟨TREvent.MessageKey s dir seed pqSalt n r parentStateIdx⟩ : TREntry)).append (⟨⟨me, st⟩⟩ : StEntry)) := by
  unfold TripleRatchet.logMessageKeyAndStore
  refine RunsSrhv.bind (RunsSrhv.logEvent _ _) ?_
  convert RunsSrhv.storeLocalState _ me st using 2
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

def encWire_srhv (st : TRState) (coinsLen ts : Nat) : DY.Bytes :=
  let m := randTerm ts 32; let coinsTerm := randTerm (ts + 1) coinsLen
  let (_, key, pqMsg) := Spqr.spqrSend st.spqr coinsTerm; let (_, seed) := TripleRatchet.kdfCk st.cks
  let keys := trMsgKeys key seed
  trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn
    (DY.SymEnc.symEnc keys.cipherKey keys.iv m) pqMsg

def encMac_srhv (st : TRState) (coinsLen ts : Nat) : DY.Bytes :=
  let coinsTerm := randTerm (ts + 1) coinsLen
  let (_, key, _) := Spqr.spqrSend st.spqr coinsTerm; let (_, seed) := TripleRatchet.kdfCk st.cks
  let keys := trMsgKeys key seed
  TripleRatchet.computeMac keys.macKey st.myIk st.peerIk (encWire_srhv st coinsLen ts)

def encMsg_srhv (st : TRState) (coinsLen ts : Nat) : DY.Bytes :=
  DY.Concat.concat (encWire_srhv st coinsLen ts) (encMac_srhv st coinsLen ts)

private def encSt_srhv (st : TRState) (coinsLen ts : Nat) : TRState :=
  { st with cks := (TripleRatchet.kdfCk st.cks).1, ns := st.ns + 1,
            spqr := (Spqr.spqrSend st.spqr (randTerm (ts + 1) coinsLen)).1 }

private def encTr_srhv (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) : ExecTrace :=
  let m := randTerm tr.length 32; let coinsTerm := randTerm (tr.length + 1) coinsLen
  let (_, key, _) := Spqr.spqrSend st.spqr coinsTerm; let (_, seed) := TripleRatchet.kdfCk st.cks
  ((((((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
    (⟨coinsLen⟩ : DY.Random.ExecEntryT)).append
    (⟨key⟩ : Network.ExecEntryT)).append
    (⟨TREvent.Sent me st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns m⟩ : TREntry)).append
    (⟨TREvent.MessageKey (st.sessionInfo me) .sender seed key st.ns
      st.rIdx stateIdx⟩ : TREntry)).append
    (⟨⟨me, encSt_srhv st coinsLen tr.length⟩⟩ : StEntry)).append
    (⟨encMsg_srhv st coinsLen tr.length⟩ : Network.ExecEntryT)

private theorem trStateStoredAt_le_srhv {me : Participant} {st : TRState} {idx : Nat} {tr T : ExecTrace}
    (hle : tr ≤ T) (h : TRStateStoredAt me st idx tr) : TRStateStoredAt me st idx T :=
  Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle h

private theorem encrypt_next_cases_stored_srhv (me : Participant) (stateIdx coinsLen : Nat)
    (wrap : Option (Nat × Nat)) (tr : ExecTrace) :
    (Move.encrypt me stateIdx coinsLen (tr.length + 2) wrap).next tr = tr ∨
    ∃ st : TRState,
      TRStateStoredAt me st stateIdx tr ∧
      (Move.encrypt me stateIdx coinsLen (tr.length + 2) wrap).next tr = encTr_srhv tr me stateIdx coinsLen st := by
  rcases hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with _ | st
  · left
    have h : FailsSrhv (Move.encrypt me stateIdx coinsLen (tr.length + 2) wrap).act tr tr := by
      show FailsSrhv (TripleRatchet.messageEncrypt me stateIdx coinsLen (tr.length + 2) >>= fun _ => pure ()) tr tr
      refine FailsSrhv.bind_left ?_; unfold TripleRatchet.messageEncrypt; exact FailsSrhv.bind_left (FailsSrhv.getLocalState hst)
    exact h.2
  · by_cases hns : st.ns ≠ TripleRatchet.u32Max
    · right; refine ⟨st, at?_eq_some_of_getLocalState_some hst, ?_⟩
      have hkey : ((((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
          (⟨coinsLen⟩ : DY.Random.ExecEntryT)).append
          (⟨(Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1⟩ :
            Network.ExecEntryT)).at? (tr.length + 2) : Option Network.ExecEntryT) =
          some ⟨(Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1⟩ := by
        have hlen2 : tr.length + 2 = ((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
            (⟨coinsLen⟩ : DY.Random.ExecEntryT)).length := by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.add_assoc]
        rw [hlen2]
        exact Trace.at?_append ((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨coinsLen⟩ : DY.Random.ExecEntryT)) _
      have hgen2 : RunsSrhv (Random.genRand coinsLen) (tr.append (⟨32⟩ : DY.Random.ExecEntryT))
          (randTerm (tr.length + 1) coinsLen)
          ((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨coinsLen⟩ : DY.Random.ExecEntryT)) := by
        convert RunsSrhv.genRand (tr.append (⟨32⟩ : DY.Random.ExecEntryT)) coinsLen using 2
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      have hrun : RunsSrhv (TripleRatchet.messageEncrypt me stateIdx coinsLen (tr.length + 2)) tr
          (tr.length + 6) (encTr_srhv tr me stateIdx coinsLen st) := by
        unfold TripleRatchet.messageEncrypt encTr_srhv encSt_srhv encMsg_srhv encMac_srhv encWire_srhv; dsimp only
        refine RunsSrhv.bind (RunsSrhv.getLocalState hst) (RunsSrhv.bind (RunsSrhv.guard _ hns)
          (RunsSrhv.bind (RunsSrhv.genRand _ _) (RunsSrhv.bind hgen2
          (RunsSrhv.bind (RunsSrhv.sendMessage _ _) (RunsSrhv.bind (RunsSrhv.receiveMessage hkey)
          (RunsSrhv.bind (RunsSrhv.logEvent _ _) ?_))))))
        refine RunsSrhv.bind (RunsSrhv.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _) ?_
        convert RunsSrhv.sendMessage _ _ using 2
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.add_assoc]
      exact (RunsSrhv.bind (f := fun _ => pure ()) hrun (RunsSrhv.pure () _)).2
    · left
      have h : FailsSrhv (Move.encrypt me stateIdx coinsLen (tr.length + 2) wrap).act tr tr := by
        show FailsSrhv (TripleRatchet.messageEncrypt me stateIdx coinsLen (tr.length + 2) >>= fun _ => pure ()) tr tr
        refine FailsSrhv.bind_left ?_; unfold TripleRatchet.messageEncrypt
        exact FailsSrhv.bind_right (RunsSrhv.getLocalState hst) (FailsSrhv.bind_left (FailsSrhv.guard _ hns))
      exact h.2

private theorem exposures_not_send_srhv {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') (hk : v.kind = .send) : False := by
  rcases List.mem_append.mp hv with hv | hv <;> {
    obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hv
    try unfold pqExposureAt at hj
    try unfold trExposureAt at hj
    split at hj <;> (try cases hj) <;> cases hk
  }

private theorem aliceVis_not_send_srhv {tr tr' : ExecTrace} {h : PQXDH.BundleHandles}
    {v : VisEntry} (hv : v ∈ aliceVis tr tr' h) (hk : v.kind = .send) : False := by
  unfold aliceVis at hv; rcases List.mem_cons.mp hv with rfl | hv
  · cases hk
  · have hkind := aliceDraws_kind _ _ hv; rw [hkind] at hk; cases hk

private theorem bobVis_not_send_srhv {tr tr' : ExecTrace} {mh : PQXDH.PreKeyMsgHandles}
    {opk : Option DY.Bytes} {v : VisEntry} (hv : v ∈ bobVis tr tr' mh opk) (hk : v.kind = .send) : False := by
  unfold bobVis at hv; rcases List.mem_cons.mp hv with rfl | hv
  · cases hk
  · rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv; cases hk
    · rcases hp : receivedPlaintext tr tr' with _ | m
      · rw [hp] at hv; cases hv
      · rw [hp] at hv; rcases List.mem_singleton.mp hv with rfl; cases hk

private theorem decVis_not_send_srhv {tr tr' : ExecTrace} {stateIdx msgIdx : Nat} {wrapped : Bool}
    {v : VisEntry} (hv : v ∈ decVis tr tr' stateIdx msgIdx wrapped) (hk : v.kind = .send) : False := by
  unfold decVis at hv; rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_append.mp hv with hv | hv
    · rcases hm : tr.getMessageSentAt msgIdx with _ | b
      · rw [hm] at hv; cases hv
      · rw [hm] at hv; rcases List.mem_singleton.mp hv with rfl; cases hk
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv; cases hk
  · rcases hp : receivedPlaintext tr tr' with _ | m
    · rw [hp] at hv; cases hv
    · rw [hp] at hv; rcases List.mem_singleton.mp hv with rfl; cases hk

private theorem encVis_send_inv_srhv {tr tr' : ExecTrace} {wrap : Option (Nat × Nat)}
    {withSend : Bool} {v : VisEntry} (hv : v ∈ encVis tr tr' wrap withSend) (hk : v.kind = .send) :
    withSend = true ∧ v ∈ encSend tr tr' wrap := by
  unfold encVis at hv; rcases List.mem_append.mp hv with hv | hv
  · rcases encDraws_kind _ hv with h | h <;> (rw [h] at hk; cases hk)
  · cases withSend with | false => simp at hv | true => simp only [↓reduceIte] at hv; exact ⟨rfl, hv⟩

private theorem lastSent_encTr_srhv (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    lastSent tr (encTr_srhv tr me stateIdx coinsLen st) = some (encMsg_srhv st coinsLen tr.length) := by
  let tr6 := (((((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨coinsLen⟩ : DY.Random.ExecEntryT)).append
    (⟨(Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1⟩ : Network.ExecEntryT)).append
    (⟨TREvent.Sent me st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns (randTerm tr.length 32)⟩ : TREntry)).append
    (⟨TREvent.MessageKey (st.sessionInfo me) .sender (TripleRatchet.kdfCk st.cks).2
      (Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1 st.ns st.rIdx stateIdx⟩ : TREntry)).append
    (⟨⟨me, encSt_srhv st coinsLen tr.length⟩⟩ : StEntry)
  have hlen : (encTr_srhv tr me stateIdx coinsLen st).length = tr6.length + 1 := by
    simp only [encTr_srhv, tr6, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlt : tr.length < (encTr_srhv tr me stateIdx coinsLen st).length := by
    simp only [encTr_srhv, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, List.length_append, List.length_singleton]; omega
  unfold lastSent; rw [ite_eq_left_iff.mpr fun h => absurd hlt h]
  have hsub : (encTr_srhv tr me stateIdx coinsLen st).length - 1 = tr6.length := by omega
  have heq : encTr_srhv tr me stateIdx coinsLen st =
      tr6.append (⟨encMsg_srhv st coinsLen tr.length⟩ : Network.ExecEntryT) := rfl
  rw [hsub, heq]; simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]; rw [Trace.at?_append]

private theorem move_vis_send_inv_srhv {m : Move} {tr : ExecTrace} {v : VisEntry}
    (hsalts : (match m with | .encrypt _ _ _ pqIdx _ => pqIdx == tr.length + 2 | _ => true) = true)
    (hv : v ∈ m.vis tr) (hk : v.kind = .send) :
    ∃ (me : Participant) (stateIdx : Nat) (st : TRState) (coinsLen : Nat) (wrap : Option (Nat × Nat)),
      TRStateStoredAt me st stateIdx tr ∧
      let w := encMsg_srhv st coinsLen tr.length
      (wrap = none ∧ v = ⟨.send, [w], .whisper, none⟩ ∨
       ∃ e c, wrap = some (e, c) ∧ v = ⟨.send, received tr [e, c] ++ [w], .preKeySend, none⟩) := by
  unfold Move.vis at hv; rcases List.mem_append.mp hv with hv | hv
  · cases m with
    | aliceStart _ _ _ _ h _ => exact False.elim (aliceVis_not_send_srhv (List.mem_of_mem_take hv) hk)
    | bobStart _ _ _ _ mh _ _ _ => exact False.elim (bobVis_not_send_srhv (List.mem_of_mem_take hv) hk)
    | encryptAbort _ _ => obtain ⟨hws, _⟩ := encVis_send_inv_srhv hv hk; cases hws
    | encryptFail _ _ _ => obtain ⟨hws, _⟩ := encVis_send_inv_srhv hv hk; cases hws
    | decrypt _ _ _ _ _ _ => exact False.elim (decVis_not_send_srhv hv hk)
    | decryptSkipped _ _ _ _ _ _ _ => exact False.elim (decVis_not_send_srhv hv hk)
    | reject draws =>
      rcases List.mem_cons.mp hv with rfl | hv
      · cases hk
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv; cases hk
    | setup | compromiseIK | compromiseSPK | compromisePQSPK | compromiseOPK
    | exposeKey | exposeSpqr | exposeSkipped | attackerSend => exact False.elim (List.not_mem_nil hv)
    | brkDH | brkKEM =>
      exact False.elim (List.not_mem_nil hv)
    | encrypt me stateIdx coinsLen pqIdx wrap =>
      simp only [beq_iff_eq] at hsalts; subst hsalts; obtain ⟨_, hencSend⟩ := encVis_send_inv_srhv hv hk
      rcases encrypt_next_cases_stored_srhv me stateIdx coinsLen wrap tr with hnext | ⟨st, hst_at, hnext⟩
      · rw [hnext] at hencSend; unfold encSend lastSent at hencSend; simp at hencSend
      · unfold encSend at hencSend; rw [hnext, lastSent_encTr_srhv] at hencSend
        dsimp only at hencSend; refine ⟨me, stateIdx, st, coinsLen, wrap, hst_at, ?_⟩
        cases wrap with
        | none => rcases List.mem_singleton.mp hencSend with rfl; exact Or.inl ⟨rfl, rfl⟩
        | some ec => rcases ec with ⟨e, c⟩; rcases List.mem_singleton.mp hencSend with rfl; exact Or.inr ⟨e, c, rfl, rfl⟩
  · exact False.elim (exposures_not_send_srhv hv hk)

private theorem runMoves_send_eq_encMsg_stored_srhv :
    ∀ (ms : List Move) (tr : ExecTrace) {v : VisEntry},
      ownSaltsFrom tr ms = true → v ∈ (runMoves ms tr).2 → v.kind = .send →
      ∃ (me : Participant) (stateIdx : Nat) (st : TRState) (coinsLen ts : Nat),
        TRStateStoredAt me st stateIdx (runMoves ms tr).1 ∧
        let w := encMsg_srhv st coinsLen ts
        w ∈ v.terms ∧ (v = ⟨.send, [w], .whisper, none⟩ ∨ ∃ tr1 e c, v = ⟨.send, received tr1 [e, c] ++ [w], .preKeySend, none⟩)
  | [], _, _, _, hv, _ => by cases hv
  | m :: ms, tr, v, hsalts, hv, hk => by
    simp only [ownSaltsFrom, Bool.and_eq_true] at hsalts; rw [runMoves_cons_snd] at hv; rw [runMoves_cons_fst]
    rcases List.mem_append.mp hv with hm | hms
    · obtain ⟨me, stateIdx, st, coinsLen, wrap, hst_at, hshape⟩ := move_vis_send_inv_srhv hsalts.1 hm hk
      have hle : tr ≤ (runMoves ms (m.next tr)).1 :=
        Trace.le_trans tr (m.next tr) (runMoves ms (m.next tr)).1 (m.act.run tr).2.property (le_runMoves_fst ms (m.next tr))
      refine ⟨me, stateIdx, st, coinsLen, tr.length, trStateStoredAt_le_srhv hle hst_at, ?_⟩
      rcases hshape with ⟨_, rfl⟩ | ⟨e, c, _, rfl⟩
      · exact ⟨List.mem_singleton_self _, Or.inl rfl⟩
      · exact ⟨List.mem_append_right _ (List.mem_singleton_self _), Or.inr ⟨tr, e, c, rfl⟩⟩
    · exact runMoves_send_eq_encMsg_stored_srhv ms (m.next tr) hsalts.2 hms hk

private theorem forall₂_eventMatches_send_srhv
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : SpqrSem} {g : Ghost} :
    ∀ {acc : List MachineEvent} {vis : List VisEntry} {b_sent : HwBytes},
      List.Forall₂ (EventMatchesEntry interpretation r₀ S g) acc vis → b_sent ∈ sentBodies acc →
      ∃ (m : HwBytes) (v : VisEntry),
        .send m ∈ acc ∧ v ∈ vis ∧ v.kind = .send ∧ sentBody m = some b_sent ∧
        EventMatchesEntry interpretation r₀ S g (.send m) v
  | [], [], _, _, hb => by simp [sentBodies] at hb
  | ev :: acc, v :: vis, b_sent, List.Forall₂.cons h hd, hb => by
    simp only [sentBodies, List.filterMap_cons] at hb
    cases ev with
    | rng _ | pt _ | recv _ | accept _ | leak _ =>
      obtain ⟨m, v', hm_acc, hv', hvk, hsb, hm⟩ := forall₂_eventMatches_send_srhv hd hb
      exact ⟨m, v', List.mem_cons_of_mem _ hm_acc, List.mem_cons_of_mem _ hv', hvk, hsb, hm⟩
    | send m =>
      dsimp only at hb
      cases hsb : sentBody m with
      | none =>
        rw [hsb] at hb; obtain ⟨m', v', hm_acc, hv', hvk, hsb', hm⟩ := forall₂_eventMatches_send_srhv hd hb
        exact ⟨m', v', List.mem_cons_of_mem _ hm_acc, List.mem_cons_of_mem _ hv', hvk, hsb', hm⟩
      | some b' =>
        rw [hsb, List.mem_cons] at hb; rcases hb with rfl | hb
        · exact ⟨m, v, List.mem_cons_self .., List.mem_cons_self .., h.1.symm, hsb, h⟩
        · obtain ⟨m', v', hm_acc, hv', hvk, hsb', hm⟩ := forall₂_eventMatches_send_srhv hd hb
          exact ⟨m', v', List.mem_cons_of_mem _ hm_acc, List.mem_cons_of_mem _ hv', hvk, hsb', hm⟩

theorem sent_mem_honest
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : SpqrSem}
    {who : List Participant} {g : Ghost}
    {ms : List Move} {acc : List MachineEvent}
    (hmp : MatchedPrefix interpretation r₀ S who g ms acc) (hfit : SendsFit acc)
    (b_sent : HwBytes) (hb_sent : b_sent ∈ sentBodies acc) :
    ∃ (v : VisEntry) (me : Participant) (stateIdx : Nat) (st : TRState) (coinsLen ts : Nat),
      let w := encMsg_srhv st coinsLen ts
      v ∈ runVis r₀ ms ∧ v.kind = .send ∧ w ∈ v.terms ∧
      TRStateStoredAt me st stateIdx (runTraceMoves r₀ ms) ∧ w.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g w = b_sent := by
  obtain ⟨m_wire, v, hm_acc, hv_vis, hvk, hsb, hmatch⟩ := forall₂_eventMatches_send_srhv hmp.2.2.2.2.2 hb_sent
  have hm_len : m_wire.length < 2 ^ 64 := hfit m_wire hm_acc
  have hsalts_all : ownSaltsFrom Trace.nil (r₀.setupMove :: ms) = true := by
    simp only [ownSaltsFrom, ProtocolSetup.setupMove, Bool.true_and]; exact hmp.2.1.2.2.2.2.1
  obtain ⟨me, stateIdx, st, coinsLen, ts, hst_at, hw_mem, hshape⟩ :=
    runMoves_send_eq_encMsg_stored_srhv (r₀.setupMove :: ms) Trace.nil hsalts_all hv_vis hvk
  let w := encMsg_srhv st coinsLen ts
  have hw_knows : w.AttackerKnows (runTraceMoves r₀ ms) := runVis_known hv_vis (Or.inl hvk) w hw_mem
  refine ⟨v, me, stateIdx, st, coinsLen, ts, hv_vis, hvk, hw_mem, hst_at, hw_knows, ?_⟩
  rcases hshape with rfl | ⟨tr1, e, c, rfl⟩
  · have hw_match : ∃ t, ([w] : List DY.Bytes) = [t] ∧
        m_wire = wireWhisperTag :: gamma interpretation S g t := hmatch.2
    obtain ⟨t, ht_eq, hm_eq⟩ := hw_match; have htw : w = t := List.singleton_injective ht_eq
    subst htw; rw [hm_eq] at hsb; simp only [sentBody, ↓reduceIte, Option.some.injEq] at hsb; exact hsb
  · obtain ⟨ids, hsend⟩ : ∃ ids, SendMatches interpretation r₀ S g (some ids) m_wire (received tr1 [e, c] ++ [w]) := hmatch.2
    rcases hterms : received tr1 [e, c] ++ [w] with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, _ | _⟩⟩⟩
    · rw [hterms] at hsend; exact False.elim hsend
    · rw [hterms] at hsend; exact False.elim hsend
    · rw [hterms] at hsend; exact False.elim hsend
    · rw [hterms] at hsend; obtain ⟨preKeyId, spkId, kpkId, _, hm_eq⟩ := hsend
      have hlast : (received tr1 [e, c] ++ [w]).getLast? = ([ek, ct, msg] : List DY.Bytes).getLast? :=
        congrArg List.getLast? hterms
      simp only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil w []),
        List.getLast?_singleton, List.getLast?_cons_cons, Option.some.injEq] at hlast
      subst hlast; rw [hm_eq] at hsb hm_len; exact (preKeySend_sentBody_strip_srhv hm_len hsb).symm
    · rw [hterms] at hsend; exact False.elim hsend

theorem exists_honest_sendMsg_of_pqFromHonest_prov
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (b : HwBytes) (parsed : SignalMessage) {who : List Participant}
    (hmp : MatchedPrefix interpretation r₀ S who g ms acc) (hfit : SendsFit acc)
    (hHon : PqFromHonest (sentBodies acc) b)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed) :
    ∃ (st_s coins_s : DY.Bytes) (st : TRState) (ts coinsLen : Nat),
      (({ st := st_s, coins := coins_s } : DY.Spqr.SendMsg.SubF DY.Bytes).pack).AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g (({ st := st_s, coins := coins_s } : DY.Spqr.SendMsg.SubF DY.Bytes).pack) =
        parsed.pqRatchet ∧
      st ∈ availableStates r₀ (runTraceMoves r₀ ms) ∧ st_s = st.spqr ∧ coins_s = randTerm (ts + 1) coinsLen := by
  obtain ⟨b_sent, hb_sent, m_sent, hm_sent, hpq_eq⟩ := hHon parsed hTryFrom
  obtain ⟨v, _me, _stateIdx, st, coinsLen, ts, _hv_vis, _hvk, _hw_mem, hst_at, hw_knows, hw_gamma⟩ :=
    sent_mem_honest hmp hfit b_sent hb_sent
  have hst_avail : st ∈ availableStates r₀ (runTraceMoves r₀ ms) := mem_availableStates_of_trStateStoredAt r₀ ms hst_at
  let st_s := st.spqr; let coins_s := randTerm (ts + 1) coinsLen
  let pq_honest := (({ st := st_s, coins := coins_s } : DY.Spqr.SendMsg.SubF DY.Bytes).pack)
  let ct_s := DY.SymEnc.symEnc
    (trMsgKeys (Spqr.spqrSend st.spqr coins_s).2.1 (TripleRatchet.kdfCk st.cks).2).cipherKey
    (trMsgKeys (Spqr.spqrSend st.spqr coins_s).2.1 (TripleRatchet.kdfCk st.cks).2).iv (randTerm ts 32)
  let wire_s := trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn ct_s pq_honest
  let mac_s := encMac_srhv st coinsLen ts
  have hw_eq : encMsg_srhv st coinsLen ts = DY.Concat.concat wire_s mac_s := rfl
  rw [hw_eq] at hw_knows hw_gamma
  have hpq_knows : pq_honest.AttackerKnows (runTraceMoves r₀ ms) := by
    have hsp := DY.Concat.attacker_knows_split (DY.Concat.concat wire_s mac_s) wire_s.length (runTraceMoves r₀ ms) hw_knows
    rw [DY.Concat.split_concat] at hsp
    have hargs := DY.TrWire.attacker_knows_trWireMsg_args
      messageVersion (DY.DiffieHellman.dhPk st.dhs)
      st.ns st.pn ct_s pq_honest canonicalVariation (runTraceMoves r₀ ms) hsp.1
    exact hargs.2.2
  have hb_sent_eq : b_sent =
      trWireBytes (g.addr wire_s) canonicalVariation
        { version := 4, ratchetKey := gamma interpretation S g (DY.DiffieHellman.dhPk st.dhs),
          counter := st.ns.toNat, previousCounter := st.pn.toNat, ciphertext := gamma interpretation S g ct_s }
        (gamma interpretation S g pq_honest) ++ gamma interpretation S g mac_s := by
    rw [← hw_gamma, gamma_concat, gamma_trHonestWireMsg_srhv]
  have hmac_len : (gamma interpretation S g mac_s).length = 8 := length_gamma_computeMac_srhv interpretation S g _ _ _ _
  have hm_sent' : SignalMessage.tryFrom protoSignalCodec
      (trWireBytes (g.addr wire_s) canonicalVariation
        { version := 4, ratchetKey := gamma interpretation S g (DY.DiffieHellman.dhPk st.dhs),
          counter := st.ns.toNat, previousCounter := st.pn.toNat, ciphertext := gamma interpretation S g ct_s }
        (gamma interpretation S g pq_honest) ++ gamma interpretation S g mac_s) = .ok m_sent := by rwa [← hb_sent_eq]
  have hpq_m := tryFrom_trWireBytes_canonical_pqRatchet_srhv hmac_len hm_sent'
  exact ⟨st_s, coins_s, st, ts, coinsLen, hpq_knows, hpq_m.symm.trans hpq_eq, hst_avail, rfl, rfl⟩

theorem exists_honest_sendMsg_of_pqFromHonest
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (b : HwBytes) (parsed : SignalMessage) {who : List Participant}
    (hmp : MatchedPrefix interpretation r₀ S who g ms acc) (hfit : SendsFit acc)
    (hHon : PqFromHonest (sentBodies acc) b)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed) :
    ∃ (st_s coins_s : DY.Bytes),
      (({ st := st_s, coins := coins_s } : DY.Spqr.SendMsg.SubF DY.Bytes).pack).AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g (({ st := st_s, coins := coins_s } : DY.Spqr.SendMsg.SubF DY.Bytes).pack) =
        parsed.pqRatchet := by
  obtain ⟨st_s, coins_s, _, _, _, hpq_kn, hpq_gam, _, _, _⟩ :=
    exists_honest_sendMsg_of_pqFromHonest_prov interpretation r₀ S g ms acc b parsed hmp hfit hHon hTryFrom
  exact ⟨st_s, coins_s, hpq_kn, hpq_gam⟩

end SrHonestVer
end Symbolic.Swarm.CREF.TR
