/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.SendWire.PendingPureA
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import DY.Trace.Basic
import DY.Actions.Network
public import Symbolic.Proofs.Swarm.CREF.SendWire.ModelSteps
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.SrHonestVer
import Symbolic.Proofs.Swarm.TRREF.EncodeRecordPqInj
import Symbolic.Proofs.Refinement.LemmasPure -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Pending-PreKey `SendWire` Record Canonicality and `COooAll` Preservation

Defines `PendingWireRecCanon` and proves `recordCanonical_of_sendPending_step`,
`PreKeySignalMessage` protobuf correspondence, `sentBody` agreement, and `COooAll` preservation
(`sndP_ret_cOooAll`) for returning pending-prekey sends.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.SndPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.SendWire
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet (TRState)
open DY.Libsignal.TripleRatchet.Refinement (trWireBytes)
open DY.Libsignal.Refinement (FieldItem EncodingVariation WireFields)
open DY.TrWire (canonicalVariation)
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record (encodeRecord encSession)
open CryptoVerification.LibsignalProtoCodec
open Proofs.libsignal.SR (interpW)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)
open Symbolic.Swarm.COMPOSED
open DY.Libsignal.Refinement (encodeWith paddedVarint FieldWF WireTypeOk HonestWF lastWithTag
  knownValue? tryFrom_encodeWith)

def PendingWireRecCanon (bs : HwBytes) : Prop :=
  ∃ sess : Session (List (BitVec 8)),
    TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q bs sess ∧
    TR.Pure.slots_RecordInScopeP ⟨some sess⟩ ∧
    TR.Pure.slots_RecordScopeP TR.Pure.slots_NonEmptyV1Q ⟨some sess⟩ ∧
    sess.state.remoteIdentity.isSome = true ∧
    bs.length < 2 ^ 62

section PendingPostHelpers

theorem recordCanonical_of_sendPending_step
    {recBytes smState : HwBytes} {sess : Session (List (BitVec 8))} {sc : SenderChain}
    {nextCk : CryptoGames.LibsignalSession.ChainKey} {newPqState : HwBytes}
    (hrc : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes sess)
    (hscope1 : TR.Pure.slots_RecordInScopeP ⟨some sess⟩)
    (_hscope2 : TR.Pure.slots_RecordScopeP TR.Pure.slots_NonEmptyV1Q ⟨some sess⟩)
    (hsc : sess.state.senderChain = some sc)
    (hwc : PendingWireRecCanon smState)
    (hstate_eq : smState = CryptoVerification.E2E.Record.encodeRecord
      ⟨some { sess with state := { sess.state with senderChain := some { sc with chainKey := nextCk }, pqRatchetState := newPqState } }⟩) :
    let sess' : Session (List (BitVec 8)) :=
      { sess with state := { sess.state with senderChain := some { sc with chainKey := nextCk }, pqRatchetState := newPqState } };
    TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q smState sess' ∧
      TR.Pure.slots_RecordInScopeP ⟨some sess'⟩ ∧
      TR.Pure.slots_RecordScopeP TR.Pure.slots_NonEmptyV1Q ⟨some sess'⟩ := by
  intro sess'
  obtain ⟨sess₁, hrc₁, _, hq₁, _, h62₁⟩ := hwc
  have hpq_eq : sess₁.state.pqRatchetState = newPqState :=
    Symbolic.Swarm.TRREF.EncodeRecordPqInj.encodeRecord_pq_inj_of_eq hrc₁.1 hstate_eq h62₁
  have hpq_lt : newPqState.length < 2 ^ 32 := hpq_eq ▸ hq₁ sess₁ rfl
  have henc_le :
      (CryptoVerification.E2E.Record.encSession sess').length ≤
        (CryptoVerification.E2E.Record.encodeRecord ⟨some sess'⟩).length := by
    unfold CryptoVerification.E2E.Record.encodeRecord
      CryptoVerification.E2E.Record.msgField CryptoVerification.E2E.Record.lenField
    simp only [Option.map_some, List.length_append]
    omega
  have henc_lt : (CryptoVerification.E2E.Record.encSession sess').length < 2 ^ 62 :=
    Nat.lt_of_le_of_lt henc_le (hstate_eq ▸ h62₁)
  have hscope1' : TR.Pure.slots_RecordInScopeP ⟨some sess'⟩ := by
    intro s hs; injection hs with hs; subst hs; exact hscope1 sess rfl
  have hscope2' : TR.Pure.slots_RecordScopeP TR.Pure.slots_NonEmptyV1Q ⟨some sess'⟩ := by
    intro s hs; injection hs with hs; subst hs; exact hpq_lt
  have hss' : TR.Pure.slots_SessionScopeP sess' := by
    obtain ⟨s₀, hs₀, hss₀⟩ := hrc.2.1.2; injection hs₀ with hs₀; subst hs₀; exact hss₀
  refine ⟨⟨hstate_eq, ⟨⟨hscope1', hscope2', ?_⟩, ⟨sess', rfl, hss'⟩⟩, ?_⟩, hscope1', hscope2'⟩
  · intro s hs; injection hs with hs; subst hs
    have hrep1 := hrc.2.1.1.2.2 sess rfl
    refine ⟨hrep1.1, ?_, hrep1.2.2.1, hrep1.2.2.2⟩
    intro sc₀ hsc₀; injection hsc₀ with hsc₀; subst hsc₀; exact hrep1.2.1 sc hsc
  · obtain ⟨hwf, hrc_len, hrc_mk, halice, hkyber, _, _⟩ := hrc.2.2
    exact ⟨by dsimp [Session.Wf, sess']; exact hwf,
      hrc_len, hrc_mk, halice, hkyber, hpq_lt, henc_lt⟩

theorem snd_bka_ret_alice {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {records : Participant → Option HwBytes} {accepted : List HwBytes} (retState : HwBytes)
    (hbka : BobRecordBaseKeyInAccepted r records accepted) :
    BobRecordBaseKeyInAccepted r
      (fun q => if q = r.alice then some retState else records q) accepted := by
  intro rr hrr
  simp only [hwf.1.symm, ↓reduceIte] at hrr
  exact hbka rr hrr

private theorem paddedVarint_zero_len_aux_sndP :
    ∀ (k n : Nat), n < 128 ^ (k + 1) → (paddedVarint n 0).length ≤ k + 1
  | 0, n, h => by
    have h' : n < 128 := by simpa using h
    rw [paddedVarint]; simp [h']
  | k + 1, n, h => by
    rw [paddedVarint]
    by_cases h' : n < 128
    · simp [h']
    · have ih := paddedVarint_zero_len_aux_sndP k (n / 128)
        (by rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [Nat.pow_succ] at h; exact h)
      simp only [h', false_and, ↓reduceIte, List.length_cons]
      omega

private theorem paddedVarint_zero_len_le_sndP (n : Nat) (h : n < 2 ^ 64) :
    (paddedVarint n 0).length ≤ 10 :=
  paddedVarint_zero_len_aux_sndP 9 n (lt_of_lt_of_le h (by decide))

private theorem fieldWF_bytes_sndP (t : Nat) (b : HwBytes) (h1 : 1 ≤ t) (h2 : t < 2 ^ 20)
    (ht : t = 1 ∨ t = 4 ∨ t = 5 ∨ t = 6) (hb : b.length < 2 ^ 64) : FieldWF t 0 0 (.bytes b) where
  tag_pos := h1
  tag_lt := lt_of_lt_of_le h2 (by decide)
  key_len := paddedVarint_zero_len_le_sndP _
    (by show t * 8 + 2 < 2 ^ 64; rcases ht with rfl | rfl | rfl | rfl <;> decide)
  head_lt := hb
  head_len := paddedVarint_zero_len_le_sndP _ hb
  wireType := by simp only [WireTypeOk]; omega

private theorem fieldWF_varint_sndP (t n : Nat) (ht : t = 2 ∨ t = 3) (hn : n < 2 ^ 64) :
    FieldWF t 0 0 (.varint n) where
  tag_pos := by omega
  tag_lt := by rcases ht with rfl | rfl <;> decide
  key_len := paddedVarint_zero_len_le_sndP _
    (by show t * 8 + 0 < 2 ^ 64; rcases ht with rfl | rfl <;> decide)
  head_lt := hn
  head_len := paddedVarint_zero_len_le_sndP _ hn
  wireType := by simp only [WireTypeOk]; omega

private def honestExtras_sndP (addr pq : HwBytes) : List FieldItem :=
  (if pq = [] then [] else [.extra 5 (.bytes pq) 0 0]) ++
    (if addr = [] then [] else [.extra 6 (.bytes addr) 0 0])

private def honestVar_sndP (addr pq : HwBytes) : EncodingVariation :=
  ⟨4, [], 0, 0, [.known 1 0 0, .known 2 0 0, .known 3 0 0, .known 4 0 0] ++ honestExtras_sndP addr pq⟩

private theorem trWireBytes_honestVar_sndP (addr pq : HwBytes) (f : WireFields) :
    trWireBytes addr canonicalVariation f pq = encodeWith (honestVar_sndP addr pq) f := by
  rw [DY.Libsignal.TripleRatchet.Refinement.trWireBytes_canonical]
  by_cases hpq : pq = [] <;> by_cases ha : addr = [] <;>
    simp [encodeWith, honestVar_sndP, honestExtras_sndP, canonicalVariation,
      FieldItem.encode, knownValue?, hpq, ha]

private theorem honestWF_honestVar_sndP (addr pq : HwBytes) (f : WireFields) (hv : f.version = 4)
    (hrk : f.ratchetKey.length = 32) (hc : f.counter < 2 ^ 32) (hpc : f.previousCounter < 2 ^ 32)
    (hct : f.ciphertext.length < 2 ^ 64) (hpq : pq.length < 2 ^ 64) (ha : addr.length < 2 ^ 64) :
    HonestWF (honestVar_sndP addr pq) f where
  version := by omega
  ratchetKey := hrk
  counter := hc
  previousCounter := hpc
  items := by
    intro it hit
    have hk : ∀ it ∈ honestExtras_sndP addr pq,
        it = .extra 5 (.bytes pq) 0 0 ∨ it = .extra 6 (.bytes addr) 0 0 := by
      intro it h; unfold honestExtras_sndP at h; split at h <;> split at h <;> simp_all
    simp only [honestVar_sndP, List.cons_append, List.mem_cons, List.nil_append] at hit
    rcases hit with rfl | rfl | rfl | rfl | hit
    · refine ⟨_, rfl, fieldWF_bytes_sndP 1 _ (by omega) (by decide) (by omega) ?_⟩
      simp [honestVar_sndP, hrk]
    · refine ⟨_, rfl, fieldWF_varint_sndP 2 _ (by omega) ?_⟩
      simp only [honestVar_sndP, Nat.reducePow, Nat.mul_zero, Nat.add_zero] at hc ⊢; omega
    · refine ⟨_, rfl, fieldWF_varint_sndP 3 _ (by omega) ?_⟩
      simp only [honestVar_sndP, Nat.reducePow, Nat.mul_zero, Nat.add_zero] at hpc ⊢; omega
    · exact ⟨_, rfl, fieldWF_bytes_sndP 4 _ (by omega) (by decide) (by omega) hct⟩
    · rcases hk it hit with rfl | rfl
      · exact fieldWF_bytes_sndP 5 _ (by omega) (by decide) (by omega) hpq
      · exact fieldWF_bytes_sndP 6 _ (by decide) (by decide) (by omega) ha
  lastRatchetKey := ⟨0, 0, by
    by_cases h1 : pq = [] <;> by_cases h2 : addr = [] <;>
      simp [lastWithTag, honestVar_sndP, honestExtras_sndP, FieldItem.tag, h1, h2]⟩
  lastCounter := ⟨0, 0, by
    by_cases h1 : pq = [] <;> by_cases h2 : addr = [] <;>
      simp [lastWithTag, honestVar_sndP, honestExtras_sndP, FieldItem.tag, h1, h2]⟩
  lastPreviousCounter := .inl ⟨0, 0, by
    by_cases h1 : pq = [] <;> by_cases h2 : addr = [] <;>
      simp [lastWithTag, honestVar_sndP, honestExtras_sndP, FieldItem.tag, h1, h2]⟩
  lastCiphertext := ⟨0, 0, by
    by_cases h1 : pq = [] <;> by_cases h2 : addr = [] <;>
      simp [lastWithTag, honestVar_sndP, honestExtras_sndP, FieldItem.tag, h1, h2]⟩

private theorem varint_low_byte_eq_sndP (b : BitVec 8) :
    BitVec.ofNat 8 (b.toNat % 128 + 128) = (b &&& 127#8) ||| 128#8 := by
  revert b; decide

private theorem prost_varint_eq_encodeVarintAux_sndP :
    ∀ (fuel : Nat) (v : BitVec 64), 0 < fuel → v.toNat < 2 ^ (7 * fuel) →
      CryptoGames.LibsignalSessionApi.Prost.varint v.toNat =
        CryptoVerification.LibsignalProtoCodec.encodeVarintAux fuel v
  | 0, _, hpos, _ => by omega
  | fuel + 1, v, _, h => by
    unfold CryptoGames.LibsignalSessionApi.Prost.varint
      CryptoVerification.LibsignalProtoCodec.encodeVarintAux
    by_cases hlt : v.toNat < 128
    · simp only [hlt, ↓reduceDIte, ↓reduceIte, List.cons.injEq, and_true]
      apply BitVec.eq_of_toNat_eq; simp
    · have hfuel : 0 < fuel := by
        by_contra h0; have h0' : fuel = 0 := by omega
        subst h0'; simp at h; omega
      simp only [hlt, ↓reduceDIte, ↓reduceIte, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · have hmod : v.toNat % 128 = (BitVec.setWidth 8 v).toNat % 128 := by
          rw [BitVec.toNat_setWidth]; omega
        rw [hmod, varint_low_byte_eq_sndP (BitVec.setWidth 8 v)]
        simp [BitVec.setWidth_or, BitVec.setWidth_and]
      · have hdiv : (v >>> 7).toNat = v.toNat / 128 := by
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        rw [← hdiv]; apply prost_varint_eq_encodeVarintAux_sndP fuel (v >>> 7) hfuel; rw [hdiv]
        have hpow : 2 ^ (7 * (fuel + 1)) = 128 * 2 ^ (7 * fuel) := by
          rw [Nat.mul_add, Nat.pow_add]; ring
        omega

private theorem prost_varint_eq_encodeVarint_sndP (n : Nat) (hn : n < 2 ^ 64) :
    CryptoGames.LibsignalSessionApi.Prost.varint n =
      CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 n) := by
  have hto : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have haux := prost_varint_eq_encodeVarintAux_sndP 10 (BitVec.ofNat 64 n) (by decide) (by omega)
  rwa [hto] at haux

private theorem prost_uint32Field_eq_sndP (tag : Nat) (htag : tag ≤ 8) (x : Option (BitVec 32)) :
    CryptoGames.LibsignalSessionApi.Prost.uint32Field tag x =
      CryptoVerification.LibsignalProtoCodec.encodeUint32Field tag x := by
  cases x with
  | none => rfl
  | some v =>
    unfold CryptoGames.LibsignalSessionApi.Prost.uint32Field
      CryptoVerification.LibsignalProtoCodec.encodeUint32Field
      CryptoGames.LibsignalSessionApi.Prost.key CryptoVerification.LibsignalProtoCodec.encodeKey
      CryptoVerification.LibsignalProtoCodec.WireType.toNat
    dsimp only
    have h1 : 8 * tag + 0 < 2 ^ 64 := by omega
    have h2 : v.toNat < 2 ^ 64 := by have := v.isLt; omega
    rw [prost_varint_eq_encodeVarint_sndP _ h1, prost_varint_eq_encodeVarint_sndP _ h2]
    congr 2
    · congr 1; omega
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.mod_eq_of_lt h2]

private theorem prost_bytesField_eq_sndP (tag : Nat) (htag : tag ≤ 8) (x : Option (List (BitVec 8)))
    (hlen : ∀ b, x = some b → b.length < 2 ^ 64) :
    CryptoGames.LibsignalSessionApi.Prost.bytesField tag x =
      CryptoVerification.LibsignalProtoCodec.encodeBytesField tag x := by
  cases x with
  | none => rfl
  | some b =>
    unfold CryptoGames.LibsignalSessionApi.Prost.bytesField
      CryptoVerification.LibsignalProtoCodec.encodeBytesField
      CryptoGames.LibsignalSessionApi.Prost.key CryptoVerification.LibsignalProtoCodec.encodeKey
      CryptoVerification.LibsignalProtoCodec.WireType.toNat
    dsimp only
    have h1 : 8 * tag + 2 < 2 ^ 64 := by omega
    have h2 : b.length < 2 ^ 64 := hlen b rfl
    have hkey : CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (8 * tag + 2)) =
        CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (tag * 8 + 2)) := by
      congr 2; omega
    rw [prost_varint_eq_encodeVarint_sndP _ h1, prost_varint_eq_encodeVarint_sndP _ h2, hkey]

theorem preKeySignalMessage_serialized_eq_preKeyWire
    (regId : BitVec 32) (preKeyId : Option (BitVec 32)) (spkId kpkId : BitVec 32)
    (ek ct : HwBytes) (baseKey : CryptoGames.LibsignalSession.PublicKey)
    (localId : CryptoGames.LibsignalSession.IdentityKey) (ik : HwBytes)
    (msg : CryptoGames.LibsignalSession.SignalMessage)
    (hbk : baseKey.serialize = ecKey ek)
    (hik : localId.serialize = ik)
    (hct_lt : (kyberKey ct).length < 2 ^ 64)
    (hmsg_lt : msg.serialized.length < 2 ^ 64) :
    wirePrekeyTag :: (PreKeySignalMessage.new 4#8 regId preKeyId spkId
      (some ⟨kpkId, kyberKey ct⟩) baseKey localId msg).serialized =
      preKeyWire preKeyId spkId kpkId regId ik ek ct msg.serialized := by
  unfold PreKeySignalMessage.new preKeyWire
  dsimp only [Option.map_some,
    CryptoGames.LibsignalSessionApi.ProtoPreKeySignalMessage.encode]
  rw [hbk, hik]
  have hbk_lt : (ecKey ek).length < 2 ^ 64 := by
    have h1 : baseKey.serialize.length = 33 := by simp [CryptoGames.LibsignalSession.PublicKey.serialize]
    have h2 := congrArg List.length hbk; omega
  have hik_lt : ik.length < 2 ^ 64 := by
    have h1 : localId.serialize.length = 33 := by
      simp [CryptoGames.LibsignalSession.IdentityKey.serialize,
        CryptoGames.LibsignalSession.PublicKey.serialize]
    have h2 := congrArg List.length hik; omega
  congr 2
  rw [prost_uint32Field_eq_sndP 1 (by decide),
      prost_bytesField_eq_sndP 2 (by decide) _ (by rintro _ ⟨rfl⟩; exact hbk_lt),
      prost_bytesField_eq_sndP 3 (by decide) _ (by rintro _ ⟨rfl⟩; exact hik_lt),
      prost_bytesField_eq_sndP 4 (by decide) _ (by rintro _ ⟨rfl⟩; exact hmsg_lt),
      prost_uint32Field_eq_sndP 5 (by decide), prost_uint32Field_eq_sndP 6 (by decide),
      prost_uint32Field_eq_sndP 7 (by decide),
      prost_bytesField_eq_sndP 8 (by decide) _ (by rintro _ ⟨rfl⟩; exact hct_lt)]
  rfl

section SentBodyAndOoo

private theorem list_length_ite {α : Type} (c : Prop) [Decidable c] (a b : List α) :
    (if c then a else b).length = if c then a.length else b.length := by
  split <;> rfl

theorem sentBody_pending_wire (F : ShaCompress) (regId : BitVec 32)
    (preKeyId : Option (BitVec 32)) (spkId kpkId : BitVec 32) (ct : HwBytes)
    (baseKey : PublicKey) (localId remote : IdentityKey) (macKey)
    (rk : PublicKey) (counter prevCounter : BitVec 32) (ctext pqMsgBytes : HwBytes)
    (hw_lt : (wirePrekeyTag :: (PreKeySignalMessage.new 4#8 regId preKeyId spkId
      (some ⟨kpkId, kyberKey ct⟩) baseKey localId
      (SignalMessage.new F protoSignalCodec 4#8 macKey (some pqHarnessAddrBytes)
        rk counter prevCounter ctext localId remote pqMsgBytes)).serialized).length < 2 ^ 64) :
    ∃ body, (sentBody (wirePrekeyTag :: (PreKeySignalMessage.new 4#8 regId preKeyId spkId
      (some ⟨kpkId, kyberKey ct⟩) baseKey localId
      (SignalMessage.new F protoSignalCodec 4#8 macKey (some pqHarnessAddrBytes)
        rk counter prevCounter ctext localId remote pqMsgBytes)).serialized)).toList = [body] := by
  set innerMsg := SignalMessage.new F protoSignalCodec 4#8 macKey (some pqHarnessAddrBytes)
    rk counter prevCounter ctext localId remote pqMsgBytes
  obtain ⟨hct_lt, hinner_lt⟩ := psm_field_lengths_lt_of_wire_lt regId preKeyId spkId kpkId
    (kyberKey ct) baseKey localId innerMsg hw_lt
  obtain ⟨hctext_lt, hpq_lt⟩ := ctext_and_pq_length_lt_of_inner_lt F macKey rk counter prevCounter
    ctext pqMsgBytes localId remote hinner_lt
  have hwire_eq := preKeySignalMessage_serialized_eq_preKeyWire regId preKeyId spkId kpkId
    baseKey.bytes.toList ct baseKey localId (ecKey localId.publicKey.bytes.toList)
    innerMsg rfl rfl hct_lt hinner_lt
  have hcontent_eq : serializeContent protoSignalCodec 4#8 rk counter prevCounter ctext pqMsgBytes
      (some pqHarnessAddrBytes) =
      encodeWith (honestVar_sndP pqHarnessAddrBytes pqMsgBytes)
        ⟨4, rk.bytes.toList, counter.toNat, prevCounter.toNat, ctext⟩ := by
    rw [serializeContent_pending_eq_trWireBytes rk counter prevCounter ctext pqMsgBytes hctext_lt hpq_lt,
        trWireBytes_honestVar_sndP]
  let mac := CryptoGames.LibsignalSession.computeMac F localId remote macKey
    (serializeContent protoSignalCodec 4#8 rk counter prevCounter ctext pqMsgBytes (some pqHarnessAddrBytes))
  have hser_eq : innerMsg.serialized =
      encodeWith (honestVar_sndP pqHarnessAddrBytes pqMsgBytes)
        ⟨4, rk.bytes.toList, counter.toNat, prevCounter.toNat, ctext⟩ ++ mac :=
    congrArg (· ++ mac) hcontent_eq
  have hmac_len : mac.length = macLength := by
    unfold mac CryptoGames.LibsignalSession.computeMac CryptoGames.HMAC.hmacSha256Trunc8 macLength
    simp [CryptoGames.HMAC.hmacWith, list_length_ite]
  obtain ⟨m_in, htry, -⟩ := tryFrom_encodeWith (honestVar_sndP pqHarnessAddrBytes pqMsgBytes)
    ⟨4, rk.bytes.toList, counter.toNat, prevCounter.toNat, ctext⟩ _ hmac_len
    (honestWF_honestVar_sndP pqHarnessAddrBytes pqMsgBytes _ rfl rk.bytes.toList_length
      counter.isLt prevCounter.isLt hctext_lt hpq_lt (by decide))
  rw [← hser_eq] at htry
  have hik_parses : ecKeyParses (ecKey localId.publicKey.bytes.toList) = true :=
    TR.SrHonestVer.ecKeyParses_ecKey_of_32 localId.publicKey.bytes.toList_length
  have hik_len : (ecKey localId.publicKey.bytes.toList).length = 33 := by
    simp [ecKey, localId.publicKey.bytes.toList_length]
  have hbk_len : baseKey.bytes.toList.length = 32 := baseKey.bytes.toList_length
  have hct_len : ct.length + 1 < 2 ^ 64 := by
    simpa [kyberKey] using hct_lt
  have hsb := TR.SrHonestVer.sentBody_preKeyWire (preKeyId := preKeyId) (spkId := spkId)
    (kpkId := kpkId) (regId := regId) (ik := ecKey localId.publicKey.bytes.toList)
    (ek := baseKey.bytes.toList) (ct := ct)
    (by omega) (by omega) hik_parses (by omega) hct_len hinner_lt htry
  exact ⟨innerMsg.serialized, by rw [hwire_eq]; exact congrArg Option.toList hsb⟩

theorem getMessageSentAt_encTr_of_some {tr : ExecTrace} {p : Participant} {stateIdx cLen j : Nat}
    {st : TripleRatchet.TRState} {x : DY.Bytes} (h : tr.getMessageSentAt j = some x) :
    (encTr tr p stateIdx cLen st).getMessageSentAt j = some x := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at h ⊢
  rcases hat : (tr.at? j : Option DY.Network.ExecEntryT) with _ | e
  · rw [hat] at h; cases h
  · have hj_lt : j < tr.length := by
      have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := DY.Network.ExecEntryT) tr j
      rw [hat] at hlt; exact hlt
    rw [at?_encTr_of_lt _ _ _ _ _ hj_lt]; exact h

theorem sndP_ret_cOooAll {interpretation : ExternInterpretation}
    {records : Participant → Option HwBytes} {p : Participant}
    {recBytes retState retMessage : HwBytes}
    {sess : Session HwBytes} {pt coins : HwBytes}
    (hall : COooAll records) (hcanon : PendingRecordCanon recBytes)
    (hrc : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes sess)
    (hwcanon : PendingWireRecCanon retState)
    (hev : TR.SendRetCoinsCliPure.pureEvalSendWire (cryptoOf' interpretation)
      (interpW interpretation) (spqrModelOf interpretation) sess (some pqHarnessAddrBytes)
      pt coins = some (retState, retMessage)) :
    COooAll (fun q => if q = p then some retState else records q) := by
  obtain ⟨_, st', salt, msgPq, hsend, _, henc⟩ :=
    TR.SendRetCoinsCliPure.pureEvalSendWire_some_inv hev
  obtain ⟨hooo, hpqlen⟩ := ooo_of_pendingRecordCanon hcanon hrc
  obtain ⟨sess₁, hrc₁, -, -, -, h62⟩ := hwcanon
  have hpq := Symbolic.Swarm.TRREF.EncodeRecordPqInj.encodeRecord_pq_inj_of_eq hrc₁.1 henc h62
  have hbounded : SpqrOooBounded (pqStateOf retState) := by
    rw [pqStateOf_of_canonical_Q_pend hrc₁, hpq]
    exact (TR.SendRetCoinsCliPure.spqrModelOf_send_growth_pure interpretation
      sess.state.pqRatchetState coins st'.pqRatchetState salt msgPq hooo hpqlen hsend).1
  exact cOOO_step_update hall hbounded

end SentBodyAndOoo

end PendingPostHelpers

end Symbolic.Swarm.CREF.CliPure.SndPure
