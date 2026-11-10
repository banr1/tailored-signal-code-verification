/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SessionPrimsPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.BobKyberNonePure
public import Symbolic.Proofs.SR.ModelW
public import Symbolic.Proofs.Swarm.CREF.Initiate.Is1aRunPure
import Symbolic.Proofs.RngG.R3ModelInv
import Symbolic.Proofs.Swarm.CREF.Grow.PqInit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj
import Symbolic.Proofs.Swarm.TRREF.EncodeRecordPqInj
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.TopPure

/-!
# `SpqrOooBounded` Preservation Across Session Decrypt

Relates `recordBytes ∘ sessionToRecordRecPending` to `encodeRecord` and `pqStateOf` on canonical
records, and proves preservation of `SpqrOooBounded` and PQ ratchet state length bounds across
`tryDecryptWithStateW` and `spqrInitOf`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.RpkCli

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record
  (encodeRecord encSession encSenderChain encReceiverChain encChainKey encPendingPreKey encPendingKyber)
open Symbolic.Swarm.TRREF
open Symbolic.Swarm.TRREF.EncodeRecordPqInj (encodeRecord_pq_inj_of_eq)
open Proofs.libsignal.SR (AesW)
open Swarm.Phase0WholeFunctionBridge
  (senderChainToChainRec receiverChainToChainRec sessionToSessionRec sessionToRecordRec
   u32Field_eq_uint32Field msgField_eq_lenField bytesField_eq_record_bytesField
   lenField_length_le record_bytesField_length_le encChainKey_length_lt
   chainBytes_sender_eq_encSenderChain chainBytes_receiver_eq_encReceiverChain)

/-! ## Record encoding and `pqStateOf` -/

@[scoped simp] theorem sessionToRecordRecPending_pqRatchetState (s : Session HwBytes) :
    (sessionToRecordRecPending s).current.pqRatchetState = s.state.pqRatchetState := rfl

theorem recordBytes_pqRatchetState_inj {r₁ r₂ : RecordRec}
    (h : recordBytes r₁ = recordBytes r₂) :
    r₁.current.pqRatchetState = r₂.current.pqRatchetState := by
  have hn := TR.recordBytes_injective h
  exact congrArg (fun r => r.current.pqRatchetState) hn

@[scoped simp] theorem pqStateOf_recordBytes (r : RecordRec) :
    pqStateOf (recordBytes r) = r.current.pqRatchetState := by
  have hex : ∃ r' : RecordRec, recordBytes r = recordBytes r' := ⟨r, rfl⟩
  simp only [pqStateOf, hex, ↓reduceDIte]
  exact recordBytes_pqRatchetState_inj (Classical.choose_spec hex).symm

private theorem flatten_map_lenField_length_ge {α : Type} (tag : Nat) (f : α → HwBytes)
    (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤ (l.map fun c => CryptoVerification.E2E.Record.lenField tag (f c)).flatten.length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · unfold CryptoVerification.E2E.Record.lenField; simp only [List.length_append]; omega
    · have := ih hmem; omega

private theorem encReceiverChain_length_le_encSession (s : Session HwBytes)
    (rc : ReceiverChain) (hrc : rc ∈ s.state.receiverChains) :
    (encReceiverChain rc).length ≤ (encSession s).length := by
  have h1 := flatten_map_lenField_length_ge 7 encReceiverChain s.state.receiverChains rc hrc
  unfold encSession; simp only [List.length_append]; omega

private theorem encPendingPreKey_length_le_encSession (s : Session HwBytes)
    (p : PendingPreKey) (hp : s.pendingPreKey = some p) :
    (encPendingPreKey p).length ≤ (encSession s).length := by
  unfold encSession; rw [hp]
  dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField,
    CryptoVerification.E2E.Record.lenField]
  simp only [List.length_append]; omega

private theorem encPendingKyber_length_le_encSession (s : Session HwBytes)
    (p : PendingKyberPreKey) (hp : s.pendingKyberPreKey = some p) :
    (encPendingKyber p).length ≤ (encSession s).length := by
  unfold encSession; rw [hp]
  dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField,
    CryptoVerification.E2E.Record.lenField]
  simp only [List.length_append]; omega

theorem recordBytes_sessionToRecordRecPending_eq_encodeRecord
    (s : Session HwBytes)
    (halice : s.aliceBaseKey.length < 2 ^ 64)
    (hpq : s.state.pqRatchetState.length < 2 ^ 64)
    (hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63)
    (hrc_len : ∀ rc ∈ s.state.receiverChains, (encReceiverChain rc).length < 2 ^ 64)
    (hsess_len : (encSession s).length < 2 ^ 64) :
    recordBytes (sessionToRecordRecPending s) = encodeRecord ⟨some s⟩ := by
  unfold recordBytes sessionToRecordRecPending sessionToSessionRec encodeRecord
  dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField]
  rw [List.flatMap_nil, List.append_nil, ← msgField_eq_lenField 1 (encSession s) hsess_len]
  congr 1
  unfold encSession
  have hloc_len : s.state.localIdentity.serialize.length = 33 :=
    TR.Pure.identityKey_serialize_length _
  have hrem_len :
      ((s.state.remoteIdentity.map IdentityKey.serialize).getD []).length < 2 ^ 64 := by
    cases r : s.state.remoteIdentity with
    | none => simp
    | some ik => simp [TR.Pure.identityKey_serialize_length ik]
  have hrk_len : (HMAC.keyToBytes32 s.state.rootKey).length = 32 := by
    simp [HMAC.keyToBytes32]
  have hsc_eq :
      ((Option.map senderChainToChainRec s.state.senderChain).map
        (msgField 6 ∘ chainBytes)).getD [] =
      CryptoVerification.E2E.Record.msgField 6 (s.state.senderChain.map encSenderChain) := by
    cases s.state.senderChain with
    | none => rfl
    | some sc =>
      dsimp only [Option.map_some, Option.getD_some, Function.comp_apply,
        CryptoVerification.E2E.Record.msgField, senderChainToChainRec]
      change DY.Libsignal.TripleRatchet.Refinement.msgField 6
        (DY.Libsignal.TripleRatchet.Refinement.chainBytes (senderChainToChainRec sc)) = _
      unfold senderChainToChainRec
      rw [chainBytes_sender_eq_encSenderChain sc]
      have hsc_len : (encSenderChain sc).length < 2 ^ 64 := by
        unfold encSenderChain
        dsimp [CryptoVerification.E2E.Record.msgField]
        have h1 := record_bytesField_length_le 1 sc.ratchetKey.publicKey.serialize
        have h2 := record_bytesField_length_le 2 sc.ratchetKey.privateKey.bytes.toList
        have h3 := lenField_length_le 3 (encChainKey sc.chainKey)
        have h4 := encChainKey_length_lt sc.chainKey
        have hpub : sc.ratchetKey.publicKey.serialize.length = 33 :=
          TR.Pure.publicKey_serialize_length _
        have hpriv : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
          List.Vector.toList_length _
        simp only [List.length_append]; omega
      exact msgField_eq_lenField 6 _ hsc_len
  have hrc_eq :
      (List.map receiverChainToChainRec s.state.receiverChains).flatMap
        (msgField 7 ∘ chainBytes) =
      (s.state.receiverChains.map fun c =>
        CryptoVerification.E2E.Record.lenField 7 (encReceiverChain c)).flatten := by
    rw [List.flatMap_map, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro rc hrc
    dsimp only [Function.comp_apply]
    change DY.Libsignal.TripleRatchet.Refinement.msgField 7
      (DY.Libsignal.TripleRatchet.Refinement.chainBytes (receiverChainToChainRec rc)) = _
    rw [chainBytes_receiver_eq_encReceiverChain rc (hseeds rc hrc),
        msgField_eq_lenField 7 _ (hrc_len rc hrc)]
  have hppk_eq :
      (((Option.map (fun p => (encPendingPreKey p, ([] : HwBytes))) s.pendingPreKey).map
        fun p => msgField 9 (p.1 ++ p.2)).getD []) =
      CryptoVerification.E2E.Record.msgField 9 (s.pendingPreKey.map encPendingPreKey) := by
    cases hppk : s.pendingPreKey with
    | none => rfl
    | some p =>
      dsimp only [Option.map_some, Option.getD_some,
        CryptoVerification.E2E.Record.msgField]
      rw [List.append_nil]
      have hlen_p : (encPendingPreKey p).length < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (encPendingPreKey_length_le_encSession s p hppk) hsess_len
      exact msgField_eq_lenField 9 _ hlen_p
  have hpkp_eq :
      (((Option.map (fun p => (encPendingKyber p, ([] : HwBytes))) s.pendingKyberPreKey).map
        fun p => msgField 14 (p.1 ++ p.2)).getD []) =
      CryptoVerification.E2E.Record.msgField 14 (s.pendingKyberPreKey.map encPendingKyber) := by
    cases hpkp : s.pendingKyberPreKey with
    | none => rfl
    | some p =>
      dsimp only [Option.map_some, Option.getD_some,
        CryptoVerification.E2E.Record.msgField]
      rw [List.append_nil]
      have hlen_p : (encPendingKyber p).length < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (encPendingKyber_length_le_encSession s p hpkp) hsess_len
      exact msgField_eq_lenField 14 _ hlen_p
  change DY.Libsignal.TripleRatchet.Refinement.u32Field 1 s.state.sessionVersion ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 2 s.state.localIdentity.serialize ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 3
        ((s.state.remoteIdentity.map IdentityKey.serialize).getD []) ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 4 (HMAC.keyToBytes32 s.state.rootKey) ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 5 s.state.previousCounter ++
      ((Option.map senderChainToChainRec s.state.senderChain).map (msgField 6 ∘ chainBytes)).getD [] ++
      (List.map receiverChainToChainRec s.state.receiverChains).flatMap (msgField 7 ∘ chainBytes) ++
      (((Option.map (fun p => (encPendingPreKey p, ([] : HwBytes))) s.pendingPreKey).map
        fun p => msgField 9 (p.1 ++ p.2)).getD []) ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 10 s.remoteRegistrationId ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 11 s.localRegistrationId ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 13 s.aliceBaseKey ++
      (((Option.map (fun p => (encPendingKyber p, ([] : HwBytes))) s.pendingKyberPreKey).map
        fun p => msgField 14 (p.1 ++ p.2)).getD []) ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 15 s.state.pqRatchetState = _
  rw [u32Field_eq_uint32Field 1,
      bytesField_eq_record_bytesField 2 _ (by omega),
      bytesField_eq_record_bytesField 3 _ hrem_len,
      bytesField_eq_record_bytesField 4 _ (by omega),
      u32Field_eq_uint32Field 5,
      hsc_eq, hrc_eq, hppk_eq,
      u32Field_eq_uint32Field 10,
      u32Field_eq_uint32Field 11,
      bytesField_eq_record_bytesField 13 _ halice,
      hpkp_eq,
      bytesField_eq_record_bytesField 15 _ hpq]

theorem recordBytes_sessionToRecordRecPending_of_canonical_Q
    {Q : HwBytes → Prop} {bs : HwBytes} {s : Session HwBytes}
    (hc : TR.Pure.slots_RecordCanonical_Q Q bs s) :
    recordBytes (sessionToRecordRecPending s) = encodeRecord ⟨some s⟩ ∧
      bs = recordBytes (sessionToRecordRecPending s) := by
  obtain ⟨henc_eq, _, ⟨_, _, hchains_sc, halice_lt, _, hpq_lt, hsess_lt⟩⟩ := hc
  have hsess_len : (encSession s).length < 2 ^ 64 := by omega
  have hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63 := by
    intro rc hrc mk hmk; have h32 := (hchains_sc rc hrc).2 mk hmk; omega
  have hrec := recordBytes_sessionToRecordRecPending_eq_encodeRecord s
    (by omega) (by omega) hseeds
    (fun rc hrc' => Nat.lt_of_le_of_lt (encReceiverChain_length_le_encSession s rc hrc') hsess_len)
    hsess_len
  exact ⟨hrec, henc_eq.trans hrec.symm⟩

theorem pqStateOf_of_canonical_Q
    {Q : HwBytes → Prop} {bs : HwBytes} {s : Session HwBytes}
    (hc : TR.Pure.slots_RecordCanonical_Q Q bs s) :
    pqStateOf bs = s.state.pqRatchetState := by
  have ⟨_, hbs⟩ := recordBytes_sessionToRecordRecPending_of_canonical_Q hc
  rw [hbs, pqStateOf_recordBytes, sessionToRecordRecPending_pqRatchetState]

theorem pqStateOf_of_wireRecCanon_and_encodeRecord
    {bs : HwBytes} {s : Session HwBytes}
    (hwc : TR.Pure.WireRecCanon bs) (henc : bs = encodeRecord ⟨some s⟩) :
    pqStateOf bs = s.state.pqRatchetState := by
  obtain ⟨sess₁, hrc, -, -, -, h62, -⟩ := hwc
  have hpq : sess₁.state.pqRatchetState = s.state.pqRatchetState :=
    encodeRecord_pq_inj_of_eq hrc.1 henc h62
  rw [pqStateOf_of_canonical_Q hrc, hpq]

/-! ## `SpqrOooBounded` preservation -/

theorem ooo_of_cref_trRecordCanon_sess {r : ProtocolSetup} {p : Participant} {recBytes : HwBytes}
    {gs : Session HwBytes}
    (hcanon : TR.PureTRRecordCanon r p recBytes)
    (hrc : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes gs) :
    SpqrOooBounded gs.state.pqRatchetState ∧ gs.state.pqRatchetState.length < 2 ^ 32 := by
  obtain ⟨sess₀, hrc₀, -, -, -, h62, -, -, hooo₀⟩ := hcanon
  have hpq : sess₀.state.pqRatchetState = gs.state.pqRatchetState :=
    encodeRecord_pq_inj_of_eq hrc₀.1 hrc.1 h62
  obtain ⟨-, -, -, -, -, -, -, hpqlen, -⟩ := hrc
  exact ⟨hpq ▸ hooo₀, hpqlen⟩

private theorem pureSpqrOf_recv_growth_ooo (i : ExternInterpretation) (pq m pq' : HwBytes)
    (salt : CryptoGames.HKDF.Salt)
    (hb : SpqrOooBounded pq) (hlen : pq.length < 2 ^ 32)
    (h : (pureSpqrOf i).recv pq m = .ok (pq', salt)) :
    SpqrOooBounded pq' ∧ pq'.length ≤ pq.length + 2 ^ 17 := by
  unfold pureSpqrOf pureSpqrFromDeps at h
  dsimp only at h
  cases hr : CryptoVerification.LibsignalSpqrV1.recv
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrDepsWithMac
        (DY.Libsignal.Refinement.sha256CompressFunction i)
        (Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf i)
        (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf i))
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith
        (DY.Libsignal.Refinement.sha256CompressFunction i))
      pq m with
  | error e =>
    rw [hr] at h
    rcases e with e | e <;> cases h
  | ok r =>
    rw [hr] at h
    dsimp only at h
    have hst : r.state = pq' := by
      revert h
      cases CryptoVerification.LibsignalSpqrV1.recvKeyToSalt? r.key with
      | none => intro h; cases h
      | some s => intro h; cases h; rfl
    subst hst
    have hB : Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvB
        (DY.Libsignal.Refinement.sha256CompressFunction i)
        (Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf i)
        (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf i) pq m = some (r.state, r.key) := by
      simp only [Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvB,
        Symbolic.Swarm.TRREF.SpqrSemOf.spqrV1RecvWithMac,
        CryptoVerification.LibsignalSpqrV1.toSpqrRecvModel, hr]
    exact Symbolic.Swarm.TRREF.GrowthRecvPure.spqr_recv_growth _ _ _ pq m r.state r.key hb hlen hB

theorem spqrOooBounded_tryDecryptWithStateW_pureSpqrOf
    (C : Crypto) (W : AesW) (i : ExternInterpretation)
    (expected : Option HwBytes) (msg : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (st st' : SessionState HwBytes) (ptext : HwBytes)
    (hok : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W
      (pureSpqrOf i) expected msg msgType coins) st =
      (.ok ptext, st'))
    (hooo : SpqrOooBounded st.pqRatchetState)
    (hlen : st.pqRatchetState.length < 2 ^ 32) :
    SpqrOooBounded st'.pqRatchetState ∧
      st'.pqRatchetState.length ≤ st.pqRatchetState.length + 2 ^ 17 := by
  obtain ⟨remIk, tr_out, _, hTr, hSt2⟩ := Proofs.libsignal.RngG.R3.tryDecryptWithStateW_ok_inv hok
  obtain ⟨_, _, _, _, newPqrState, pqrKey, _, _, hSpqr, _, _, hTrOut⟩ :=
    Proofs.libsignal.RngG.R3.tripleRatchet_decryptW_ok_inv hTr
  have hpq : st'.pqRatchetState = newPqrState := by
    rw [hSt2, hTrOut]
  rw [hpq]
  exact pureSpqrOf_recv_growth_ooo i
    st.pqRatchetState msg.pqRatchet newPqrState pqrKey hooo hlen hSpqr

theorem spqrOooBounded_spqrInitOf_b2a (i : ExternInterpretation) (k : HwBytes)
    (hk : 1176 + k.length < 2 ^ 32) :
    SpqrOooBounded (Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf i k [1#8]) ∧
      (Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf i k [1#8]).length < 2 ^ 32 := by
  rw [Grow.spqrInitOf_b2a_eq_is1StateRaw]
  exact ⟨Grow.spqrOooBounded_is1StateRaw _ .b2a k (by omega),
    is1StateRaw_encodeRaw_length_lt_2_32 _ .b2a k hk⟩

theorem spqrOooBounded_recvPrekey_promote
    (C : Crypto) (W : AesW) (i : ExternInterpretation)
    (expected : Option HwBytes) (msg : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (sess : Session HwBytes) (st' : SessionState HwBytes) (ptext : HwBytes)
    (hok : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W
      (pureSpqrOf i) expected msg msgType coins) sess.state =
      (.ok ptext, st'))
    (hooo : SpqrOooBounded sess.state.pqRatchetState)
    (hlen : sess.state.pqRatchetState.length < 2 ^ 32) :
    SpqrOooBounded st'.pqRatchetState ∧
      st'.pqRatchetState.length ≤ sess.state.pqRatchetState.length + 2 ^ 17 :=
  spqrOooBounded_tryDecryptWithStateW_pureSpqrOf C W i expected msg msgType coins
    sess.state st' ptext hok hooo hlen

theorem cref_trRecordCanon_of_wireRecCanon_pqInj (r₀ : ProtocolSetup) (p : Participant)
    {bs : HwBytes} {s : Session HwBytes}
    (hwc : TR.Pure.WireRecCanon bs)
    (henc : bs = encodeRecord ⟨some s⟩)
    (hooo : SpqrOooBounded s.state.pqRatchetState)
    (hlen : bs.length < 2 ^ 32 - 2 ^ 20) :
    TR.PureTRRecordCanon r₀ p bs := by
  obtain ⟨sess₁, hrc, hscope, hq, hrid, h62, hppk⟩ := hwc
  have hpq : sess₁.state.pqRatchetState = s.state.pqRatchetState :=
    encodeRecord_pq_inj_of_eq hrc.1 henc h62
  refine ⟨sess₁, hrc, hscope, hq, hrid, h62, hppk, hlen, ?_⟩
  rw [hpq]; exact hooo

end Symbolic.Swarm.CREF.CliPure.RpkCli
