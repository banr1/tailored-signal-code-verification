/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqDir
public import Symbolic.Proofs.SpecLemmas.CliPureBytes
public import Symbolic.Specifications.Concrete.MachineEvents
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridgeAux
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Model Unfolding and Wire Length Bounds for `pqSendModel`

Unpacks `pqSendModel W st pt r_coins = some (some (st', wire))` under `PqxdhPartyInSpecDomain W st`,
advances `ReachablePqxdhSession` across `send`, and proves `wire.length < 2 ^ 64` for both whisper
and pending-prekey wire outputs.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoGames.CBC CryptoGames.LibsignalAead
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 (PolyApi sendAfterStates spqrDeps spqrHkdfWith toSpqrModel)
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.SignalSession
open DY.Libsignal (HwBytes)
open Symbolic.Swarm.CREF.Cli

attribute [local simp] mut_exec_pure mut_exec_throw mut_exec_get mut_exec_set
  mut_exec_modify mut_exec_modifyGet mut_exec_liftE mut_exec_bind mut_exec_onRatchet

/-! ## `pqSendModel` Unfolding and Session Reachability -/

theorem pqSendModel_eq_some_some {W : PEParams} {st st' : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes} {pt r_coins wire : HwBytes}
    (hsess : st.session = some (x, g))
    (hmodel : pqSendModel W st pt r_coins = some (some (st', wire))) :
    ∃ (msg : SignalMessage) (s : SessionState HwBytes) (k : IdentityKey),
      SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).sendAddrs g.party) pt r_coins g.session = (.ok msg, s) ∧
      g.session.remoteIdentity = some k ∧
      st.trusts k = true ∧
      ((pqxdhSessionParams W).send g pt r_coins).1 = ghostAfterSend g s ∧
      st' = { st with peerId := some k, session := some (x, { g with session := s }) } ∧
      wire = (if g.session.pendingPreKey
        then wirePrekey :: firstMessageBody x g.session msg
        else wireWhisper :: msg.serialized) := by
  unfold pqSendModel at hmodel
  rw [hsess] at hmodel
  dsimp only at hmodel
  rcases henc : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).sendAddrs g.party) pt r_coins g.session with ⟨err | msg, s⟩
  · cases err <;> simp [henc] at hmodel
  · simp only [henc] at hmodel
    rcases hrem : g.session.remoteIdentity with _ | k
    · simp [hrem] at hmodel
    · simp only [hrem] at hmodel
      cases htr : st.trusts k
      · simp [htr] at hmodel
      · simp only [htr, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq, Prod.mk.injEq] at hmodel
        rcases hmodel with ⟨hst', hwire⟩
        refine ⟨msg, s, k, rfl, rfl, htr, ?_, hst'.symm, hwire.symm⟩
        have hC : (pqxdhSessionParams W).C = W.C := rfl
        have hcod : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
        have hspqr : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
        rw [CryptoVerification.E2E.Record.send_eq_afterSend, hC, hcod, hspqr, henc]

theorem reachPq_afterSend_of_wfPq {W : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    {pt r_coins : HwBytes} {msg : SignalMessage} {s : SessionState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (henc : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).sendAddrs g.party) pt r_coins g.session = (.ok msg, s)) :
    ∃ g₀', ReachablePqxdhSession W st.me x g₀' ∧
      g₀'.party = g.party ∧
      g₀'.session = s := by
  obtain ⟨⟨g₀, hrpq, hp_eq, hs_eq⟩, _, hlen31⟩ := hwf.1 x g hsess
  have hpq_eq : pqSession x g₀ = pqSession x g := by
    unfold pqSession; rw [hs_eq]
  have henc_eq : encodeRecordUnderExtras (fun _ => x) g₀ = encodeRecordUnderExtras (fun _ => x) g := by
    rw [encodeRecordX_eq_encodeRecord_pqSession, encodeRecordX_eq_encodeRecord_pqSession, hpq_eq]
  have hlen31_0 : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
    rw [henc_eq]; exact hlen31
  have hstep := ReachablePqxdhSession.send pt r_coins hrpq hlen31_0
  change ReachablePqxdhSession W st.me x ((pqxdhSessionParams W).send g₀ pt r_coins).1 at hstep
  have hsend0 : ((pqxdhSessionParams W).send g₀ pt r_coins).1 = ghostAfterSend g₀ s := by
    have hC : (pqxdhSessionParams W).C = W.C := rfl
    have hcod : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
    have hspqr : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
    rw [CryptoVerification.E2E.Record.send_eq_afterSend, hp_eq, hs_eq, hC, hcod, hspqr, henc]
  rw [hsend0] at hstep
  exact ⟨ghostAfterSend g₀ s, hstep, hp_eq, rfl⟩

/-! ## Wire Message Byte-Length Bounds -/

private theorem encodeVarintAux_len_le : ∀ (k : Nat) (v : BitVec 64),
    (encodeVarintAux k v).length ≤ k
  | 0, _ => by simp [encodeVarintAux]
  | k + 1, v => by
    unfold encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have ih := encodeVarintAux_len_le k (v >>> 7)
      omega

private theorem encodeUint32Field_len_le (tag : Nat) (ov : Option (BitVec 32)) :
    (encodeUint32Field tag ov).length ≤ 20 := by
  cases ov with
  | none => simp [encodeUint32Field]
  | some v =>
    simp only [encodeUint32Field, List.length_append]
    have h1 := encodeVarintAux_len_le 10 (BitVec.ofNat 64 (tag * 8 + WireType.varint.toNat))
    have h2 := encodeVarintAux_len_le 10 (v.zeroExtend 64)
    unfold encodeKey encodeVarint at *
    omega

private theorem encodeBytesField_len_le (tag : Nat) (obs : Option HwBytes) :
    (encodeBytesField tag obs).length ≤ 20 + (obs.getD []).length := by
  cases obs with
  | none => simp [encodeBytesField]
  | some bs =>
    simp only [encodeBytesField, Option.getD_some, List.length_append]
    have h1 := encodeVarintAux_len_le 10 (BitVec.ofNat 64 (tag * 8 + WireType.lengthDelimited.toNat))
    have h2 := encodeVarintAux_len_le 10 (BitVec.ofNat 64 bs.length)
    unfold encodeKey encodeVarint at *
    omega

private theorem prost_varint_len_aux :
    ∀ (k n : Nat), n < 128 ^ (k + 1) → (Prost.varint n).length ≤ k + 1
  | 0, n, h => by
    have h' : n < 128 := by simpa using h
    unfold Prost.varint; simp [h']
  | k + 1, n, h => by
    unfold Prost.varint
    by_cases h' : n < 128
    · simp [h']
    · have ih := prost_varint_len_aux k (n / 128)
        (by rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [Nat.pow_succ] at h; exact h)
      simp only [h', ↓reduceDIte, List.length_cons]; omega

private theorem prost_varint_len_le (n : Nat) (hn : n < 2 ^ 64) :
    (Prost.varint n).length ≤ 10 :=
  prost_varint_len_aux 9 n (lt_of_lt_of_le hn (by decide))

private theorem prost_uint32Field_len_le (tag : Nat) (htag : tag ≤ 8) (ov : Option (BitVec 32)) :
    (Prost.uint32Field tag ov).length ≤ 20 := by
  cases ov with
  | none => simp [Prost.uint32Field]
  | some v =>
    unfold Prost.uint32Field Prost.key
    dsimp only
    rw [List.length_append]
    have h1 := prost_varint_len_le (8 * tag + 0) (by omega)
    have h2 := prost_varint_len_le v.toNat (by have := v.isLt; omega)
    omega

private theorem prost_bytesField_len_le (tag : Nat) (htag : tag ≤ 8) (obs : Option HwBytes)
    (hlen : (obs.getD []).length < 2 ^ 64) :
    (Prost.bytesField tag obs).length ≤ 20 + (obs.getD []).length := by
  cases obs with
  | none => simp [Prost.bytesField]
  | some bs =>
    unfold Prost.bytesField Prost.key
    dsimp only
    simp only [Option.getD_some, List.length_append] at hlen ⊢
    have h1 := prost_varint_len_le (8 * tag + 2) (by omega)
    have h2 := prost_varint_len_le bs.length hlen
    omega

private theorem addrsE_uuidTryParse_len (s r : Party) (a : HwBytes)
    (h : serializedPartyAddresses uuidTryParse s r = some a) : a.length = 36 := by
  unfold serializedPartyAddresses at h
  cases hs : serviceIdParse uuidTryParse (CryptoVerification.LibsignalTripleRatchetRepr.utf8 (partyAddressName s)) <;>
    cases hr : serviceIdParse uuidTryParse (CryptoVerification.LibsignalTripleRatchetRepr.utf8 (partyAddressName r)) <;> simp_all [addrBytes]
  subst h; simp

private theorem spqr_encodeVarintLoop_len_le :
    ∀ (fuel : Nat) (x : BitVec 64),
      (CryptoVerification.LibsignalSpqrV1.encodeVarintLoop fuel x).length ≤ fuel
  | 0, _ => by simp [CryptoVerification.LibsignalSpqrV1.encodeVarintLoop]
  | f + 1, x => by
    unfold CryptoVerification.LibsignalSpqrV1.encodeVarintLoop
    dsimp only
    split
    · simp
    · simp only [List.length_cons]
      have ih := spqr_encodeVarintLoop_len_le f (x >>> 7)
      omega

private theorem spqr_encode_varint_len_le (v : BitVec 64) (buf : HwBytes) :
    (CryptoVerification.LibsignalSpqrV1.encode_varint v buf).length ≤ buf.length + 10 := by
  unfold CryptoVerification.LibsignalSpqrV1.encode_varint
    CryptoVerification.LibsignalSpqrV1.MAX_VARINT_BYTES_LEN
  rw [List.length_append]
  have := spqr_encodeVarintLoop_len_le 10 v
  omega

private theorem spqr_encode_chunk_len_le {P : PolyApi} (c : P.Chunk) (acc : HwBytes) :
    (CryptoVerification.LibsignalSpqrV1.encode_chunk c acc).length ≤ acc.length + 42 := by
  unfold CryptoVerification.LibsignalSpqrV1.encode_chunk
  have hc := spqr_encode_varint_len_le ((P.chunkIndex c).zeroExtend 64) acc
  have hd : (P.chunkData c).toList.length = 32 := List.Vector.toList_length _
  simp only [List.length_append, hd]; omega

private theorem spqr_message_serialize_len_le {P : PolyApi}
    (m : CryptoVerification.LibsignalSpqrV1.Message P) (idx : BitVec 32) :
    (CryptoVerification.LibsignalSpqrV1.Message.serialize m idx).length ≤ 128 := by
  unfold CryptoVerification.LibsignalSpqrV1.Message.serialize; dsimp only
  have h1 := spqr_encode_varint_len_le m.epoch [1#8]
  rw [List.length_singleton] at h1
  have h2 := spqr_encode_varint_len_le (idx.zeroExtend 64)
    (CryptoVerification.LibsignalSpqrV1.encode_varint m.epoch [1#8])
  rcases m.payload with _ | c | c | c | b | c | c <;> dsimp only
  · repeat rw [List.length_append]
    repeat rw [List.length_singleton]
    omega
  · apply Nat.le_trans (spqr_encode_chunk_len_le _ _)
    repeat rw [List.length_append]; repeat rw [List.length_singleton]; omega
  · apply Nat.le_trans (spqr_encode_chunk_len_le _ _)
    repeat rw [List.length_append]; repeat rw [List.length_singleton]; omega
  · apply Nat.le_trans (spqr_encode_chunk_len_le _ _)
    repeat rw [List.length_append]; repeat rw [List.length_singleton]; omega
  · cases b <;>
    · repeat rw [List.length_append]
      repeat rw [List.length_cons]
      repeat rw [List.length_nil]
      omega
  · apply Nat.le_trans (spqr_encode_chunk_len_le _ _)
    repeat rw [List.length_append]; repeat rw [List.length_singleton]; omega
  · apply Nat.le_trans (spqr_encode_chunk_len_le _ _)
    repeat rw [List.length_append]; repeat rw [List.length_singleton]; omega

private theorem finish_msgSerialize {D : CryptoVerification.LibsignalSpqrV1.SpqrApiDeps}
    {encodeBytes : HwBytes} {msg : D.MessageV1} {idx : BitVec 32}
    {outKey : CryptoVerification.LibsignalSpqrV1.MessageKey}
    {out : CryptoVerification.LibsignalSpqrV1.Send}
    (h : (match D.msgSerialize msg idx with
      | [] => Except.error (CryptoVerification.LibsignalSpqrV1.SpqrApiError.panic
          CryptoVerification.LibsignalSpqrV1.SpqrApiPanic.sendMsgEmpty)
      | b0 :: _ =>
        if (b0 != CryptoVerification.LibsignalSpqrV1.Version.v1.toU8) = true then
          Except.error (CryptoVerification.LibsignalSpqrV1.SpqrApiError.panic
            CryptoVerification.LibsignalSpqrV1.SpqrApiPanic.sendMsgBadVersion)
        else
          Except.ok { state := encodeBytes, msg := D.msgSerialize msg idx, key := outKey }) =
      Except.ok out) :
    ∃ i, out.msg = D.msgSerialize msg i := by
  cases hser : D.msgSerialize msg idx with
  | nil => rw [hser] at h; cases h
  | cons b0 tail =>
    rw [hser] at h; dsimp only at h
    split at h
    · cases h
    · injection h with hout; exact ⟨idx, by rw [← hout, hser]⟩

private theorem sendAfterStates_msg_eq (D : CryptoVerification.LibsignalSpqrV1.SpqrApiDeps)
    (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    (statePb : CryptoVerification.LibsignalSpqrV1.PqRatchetStatePB D.V1StatePB)
    (msg : D.MessageV1) (key : Option CryptoVerification.LibsignalSpqrV1.EpochSecret)
    (state : D.States) (out : CryptoVerification.LibsignalSpqrV1.Send)
    (h : sendAfterStates D hkdf statePb msg key state = .ok out) :
    ∃ idx, out.msg = D.msgSerialize msg idx := by
  unfold sendAfterStates at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  repeat (first | exact finish_msgSerialize h | cases h | split at h)

private theorem spqrPq_send_msg_len_le (W : PEParams) (st r pq' : HwBytes)
    (key : CryptoGames.HKDF.Salt) (pm : HwBytes)
    (h : (pqxdhSpqrSession W).send st r = some (pq', key, pm)) :
    pm.length ≤ 128 := by
  change (toSpqrModel (spqrDeps W.C.F W.Q.K) (spqrHkdfWith W.C.F)).send st r =
    some (pq', key, pm) at h
  unfold toSpqrModel at h; dsimp only at h
  rcases htop : (CryptoVerification.LibsignalSpqrV1.send
      (spqrDeps W.C.F W.Q.K) (spqrHkdfWith W.C.F) st r).1 with err | out
  · rw [htop] at h; cases h
  · rw [htop] at h; dsimp only at h
    rcases hsalt : CryptoVerification.LibsignalSpqrV1.messageKeyToSalt? out.key with _ | salt
    · rw [hsalt] at h; cases h
    · rw [hsalt] at h
      injection h with htuple
      rcases Prod.mk.inj htuple with ⟨_, hrest⟩
      rcases Prod.mk.inj hrest with ⟨_, hpm⟩
      subst hpm
      unfold CryptoVerification.LibsignalSpqrV1.send at htop
      split at htop
      · cases htop
      · split at htop
        · injection htop with hout; rw [← hout]; simp
        · split at htop
          · cases htop
          · split at htop
            split at htop
            · cases htop
            · dsimp only at htop
              obtain ⟨idx, hmsg⟩ := sendAfterStates_msg_eq _ _ _ _ _ _ out htop
              rw [hmsg]
              exact spqr_message_serialize_len_le _ idx

theorem messageEncrypt_pq_serialized_lt {W : PEParams} {g : GhostState HwBytes}
    {pt r_coins : HwBytes} {msg : SignalMessage} {s : SessionState HwBytes}
    (hpt : pt.length < 2 ^ 32)
    (henc : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).sendAddrs g.party) pt r_coins g.session = (.ok msg, s)) :
    msg.serialized.length < 2 ^ 34 := by
  unfold SessionState.messageEncrypt OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at henc
  rcases hsc : g.session.senderChain with _ | sc
  · simp only [hsc, mut_exec_bind, mut_exec_get, mut_exec_throw] at henc; nomatch henc
  · simp only [hsc, mut_exec_bind, mut_exec_get, mut_exec_modifyGet] at henc
    split_ifs at henc
    · simp at henc
    · rcases hrem : g.session.remoteIdentity with _ | remote
      · simp [hrem] at henc
      · simp only [hrem, mut_exec_pure] at henc
        unfold OutgoingTripleRatchet.encrypt at henc
        simp only [mut_exec_bind, mut_exec_get] at henc
        split_ifs at henc
        · simp at henc
        · rcases hspqr : (pqxdhSpqrSession W).send g.session.pqRatchetState r_coins with
            _ | ⟨pq', salt, pm⟩
          · simp [hspqr] at henc
          · have hpm := spqrPq_send_msg_len_le W _ _ _ _ _ hspqr
            simp only [hspqr] at henc
            rcases hnext : sc.chainKey.nextChainKey W.C.F with _ | nextCk
            · simp [hnext] at henc
            · simp only [hnext, mut_exec_bind, mut_exec_liftE, mut_exec_set, mut_exec_pure,
                Prod.mk.injEq, Except.ok.injEq] at henc
              rcases henc with ⟨rfl, _⟩
              have hblk : ∀ l : List (BitVec 128),
                  (l.flatMap CBC.blockToBytesLE).length = 16 * l.length := by
                intro l; induction l with
                | nil => rfl
                | cons b t ih =>
                  have hb : (CBC.blockToBytesLE b).length = 16 := by simp [CBC.blockToBytesLE]
                  simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, hb]; omega
              have hct : ∀ k iv, (aesCbcEncrypt W.C.E k iv pt).length = 16 * (pt.length / 16 + 1) := by
                intro k iv; unfold aesCbcEncrypt; rw [hblk, List.Vector.toList_length]; rfl
              have had6 : (encodeBytesField 6
                  (g.session.encryptAddresses ((pqxdhSessionParams W).sendAddrs g.party))).length ≤ 56 := by
                unfold SessionState.encryptAddresses pqxdhSessionParams Params.sendAddrs
                split_ifs
                · cases g.party <;>
                  · dsimp only
                    cases hs : serializedPartyAddresses uuidTryParse _ _ with
                    | none => simp [encodeBytesField]
                    | some ad =>
                      have h1 := encodeBytesField_len_le 6 (some ad)
                      have h2 := addrsE_uuidTryParse_len _ _ ad hs
                      simp only [Option.getD_some] at h1; omega
                · simp [encodeBytesField]
              dsimp only [SignalMessage.new]
              rw [List.length_append]
              refine Nat.lt_of_le_of_lt
                (Nat.add_le_add_left (by unfold computeMac; exact List.length_take_le 8 _) _) ?_
              dsimp only [serializeContent, protoSignalCodec,
                CryptoVerification.LibsignalProtoCodec.encode]
              have h1 := encodeBytesField_len_le 1 (some sc.ratchetKey.publicKey.serialize)
              have hrk : sc.ratchetKey.publicKey.serialize.length = 33 := by simp [PublicKey.serialize]
              have h2 := encodeUint32Field_len_le 2 (some sc.chainKey.index)
              have h3 := encodeUint32Field_len_le 3 (some g.session.previousCounter)
              have h4 := encodeBytesField_len_le 4 (some (aesCbcEncrypt W.C.E
                ((sc.chainKey.messageKeys W.C.F).generateKeys W.C.F salt).cipherKey
                ((sc.chainKey.messageKeys W.C.F).generateKeys W.C.F salt).iv pt))
              have h4' := hct
                ((sc.chainKey.messageKeys W.C.F).generateKeys W.C.F salt).cipherKey
                ((sc.chainKey.messageKeys W.C.F).generateKeys W.C.F salt).iv
              have h5 : (encodeBytesField 5 (if pm.isEmpty then none else some pm)).length ≤ 20 + pm.length := by
                split_ifs <;> [simp [encodeBytesField]; exact encodeBytesField_len_le 5 (some pm)]
              simp only [Option.getD_some, List.length_append, List.length_cons] at h1 h4 ⊢
              omega

/-- Both whisper and pending-prekey wire outputs of `pqSendModel` have length `< 2 ^ 64` when
`pt.length < 2 ^ 32` and `PqxdhPartyInSpecDomain W st` holds. -/
theorem pqSendModel_wire_lt_2_64 {W : PEParams} {st st' : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes} {pt r_coins wire : HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hpt : pt.length < 2 ^ 32)
    (hmodel : pqSendModel W st pt r_coins = some (some (st', wire))) :
    wire.length < 2 ^ 64 := by
  obtain ⟨msg, _, _, henc, _, _, _, _, hwire⟩ := pqSendModel_eq_some_some hsess hmodel
  have hmsg := messageEncrypt_pq_serialized_lt hpt henc
  subst hwire
  by_cases hpend : g.session.pendingPreKey = true
  · simp only [hpend, ↓reduceIte, List.length_cons]
    obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, hkyb⟩, _, _⟩ := reachPqInvPure_of_wfPq hwf hsess
    unfold firstMessageBody PreKeySignalMessage.new ProtoPreKeySignalMessage.encode
    dsimp only
    have hu5 := prost_uint32Field_len_le 5 (by decide) (some x.localRegistrationId)
    have hu1 := prost_uint32Field_len_le 1 (by decide) x.pending.preKeyId
    have hu6 := prost_uint32Field_len_le 6 (by decide) (some x.pending.signedPreKeyId)
    have hbk : x.pending.baseKey.serialize.length = 33 := by simp [PublicKey.serialize]
    have hb2 := prost_bytesField_len_le 2 (by decide) (some x.pending.baseKey.serialize)
      (by simp [hbk])
    have hik : g.session.localIdentity.serialize.length = 33 := by
      simp [IdentityKey.serialize, PublicKey.serialize]
    have hb3 := prost_bytesField_len_le 3 (by decide) (some g.session.localIdentity.serialize)
      (by simp [hik])
    have hb4 := prost_bytesField_len_le 4 (by decide) (some msg.serialized)
      (by simp only [Option.getD_some]; omega)
    simp only [Option.getD_some] at hb2 hb3 hb4
    cases hk : x.kyber with
    | none =>
      dsimp only [Option.map]
      have h7 : (Prost.uint32Field 7 none).length = 0 := rfl
      have h8 : (Prost.bytesField 8 none).length = 0 := rfl
      repeat rw [List.length_cons]
      repeat rw [List.length_append]
      omega
    | some k =>
      dsimp only [Option.map]
      have hkl := hkyb k hk
      have h7 := prost_uint32Field_len_le 7 (by decide) (some k.preKeyId)
      have h8 := prost_bytesField_len_le 8 (by decide) (some k.ciphertext)
        (by simp only [Option.getD_some]; omega)
      simp only [Option.getD_some] at h8
      repeat rw [List.length_cons]
      repeat rw [List.length_append]
      omega
  · simp only [hpend, Bool.false_eq_true, ↓reduceIte, List.length_cons]
    omega

end Symbolic.Swarm.CREF.Cli.Slots
