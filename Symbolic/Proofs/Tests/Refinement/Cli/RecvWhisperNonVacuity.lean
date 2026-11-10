/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model
import all Init.Data.String.Defs
import all Init.Data.Repr
import all Init.Data.List.SplitOn.Basic
public import Symbolic.Proofs.Tests.Refinement.Cli.RecvWhisperNonVacuitySteps12
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRecordInj
import Symbolic.Proofs.Swarm.CREF.Cli.TopSlots
import Symbolic.Proofs.Swarm.CREF.TR.PureSessionBounds
import Symbolic.Proofs.Tests.Refinement.Cli.RecvWhisperNonVacuityDecode
import Symbolic.Proofs.Tests.Refinement.Cli.RecvWhisperNonVacuityStep5

/-!
# Concrete SPQR-ON Non-Vacuity Roundtrip

Proves `pqRecvWhisper_nonvacuous_spqr_on`: starting from empty-session `PqParty` states, running
the 5-step CLI model sequence with SPQR V1 active (`pqInitModel`, prekey `pqSendModel`,
`pqRecvPrekeyModel`, whisper `pqSendModel`, and `pqRecvWhisperModel`) succeeds with a non-empty V1
SPQR ratchet state. Also proves `pqModelPost_recvWhisper_nonvacuous_spqr_on`, showing satisfiability
of `PqModelPost` on an accepted SPQR-ON whisper `recv` call inside `PqxdhPartyInSpecDomain`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers

open DY.Libsignal (HwBytes)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession

set_option maxRecDepth 8192

private theorem nvPqA0_len_lt : nvPqA0.length < 20000 := by decide

private theorem nvPqA1_len_lt : nvPqA1.length < 20000 := by
  have hPbEq : nvPbA1 =
      { inner := some nvV1Pb
        versionNegotiation := some nvVnA
        chain := some nvChA1Key.1.intoPb } := rfl
  have hPqRaw : nvPqA1 =
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB.encodeRaw 1#32 (some nvVnA) ++
        CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          CryptoVerification.LibsignalSpqrV1.ChainPB.encodeRaw 2#32 (some nvChA1Key.1.intoPb)) ++
      (26#8 :: (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 nvV1Len) ++
        (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw nvV1Pb ++ []))) := by
    change CryptoVerification.LibsignalSpqrV1.Proto.encodeState
        (CryptoVerification.LibsignalSpqrV1.pbToPqRatchetState nvPbA1) = _
    rw [hPbEq]
    dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeState,
      CryptoVerification.LibsignalSpqrV1.pbToPqRatchetState, Option.map,
      CryptoVerification.LibsignalSpqrV1.PqRatchetState.encode,
      CryptoVerification.LibsignalSpqrV1.PqRatchetState.encodeRaw,
      CryptoVerification.LibsignalSpqrV1.PqRatchetState.Inner.encode,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage]
    have hkey3 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited =
        [26#8] := rfl
    rw [hkey3, nvV1Len_eq]
    simp only [List.append_nil, List.nil_append, List.cons_append, List.append_assoc]
  rw [hPqRaw]
  simp only [List.length_append, List.length_cons, List.length_nil, nvV1Len_eq]
  decide

private theorem encodeRecord_some_length_le_fileCap
    (s : Session HwBytes)
    (hrc_len : s.state.receiverChains.length ≤ 5)
    (hrc_mk : ∀ rc ∈ s.state.receiverChains, rc.messageKeys.length ≤ maxMessageKeys ∧
      ∀ mkg ∈ rc.messageKeys, mkg.seed.length = 32)
    (halice : s.aliceBaseKey.length ≤ 20000)
    (hkyber : match s.pendingKyberPreKey with
      | none => True | some pkp => pkp.ciphertext.length ≤ 20000)
    (hpq : s.state.pqRatchetState.length < 20000) :
    (Record.encodeRecord ⟨some s⟩).length ≤ fileCapBytes := by
  open Symbolic.Swarm.CREF.TR.Pure Symbolic.Swarm.CREF.CliPure.TR.Pure in
  have hrec := encodeRecord_some_length_le s
  have hlen : (Record.encSession s).length =
      (Record.uint32Field 1 s.state.sessionVersion).length +
      (Record.bytesField 2 s.state.localIdentity.serialize).length +
      (Record.bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD [])).length +
      (Record.bytesField 4 (HMAC.keyToBytes32 s.state.rootKey)).length +
      (Record.uint32Field 5 s.state.previousCounter).length +
      (Record.msgField 6 (s.state.senderChain.map Record.encSenderChain)).length +
      ((s.state.receiverChains.map fun c =>
          Record.lenField 7 (Record.encReceiverChain c)).flatten).length +
      (Record.msgField 9 (s.pendingPreKey.map Record.encPendingPreKey)).length +
      (Record.uint32Field 10 s.remoteRegistrationId).length +
      (Record.uint32Field 11 s.localRegistrationId).length +
      (Record.bytesField 13 s.aliceBaseKey).length +
      (Record.msgField 14 (s.pendingKyberPreKey.map Record.encPendingKyber)).length +
      (Record.bytesField 15 s.state.pqRatchetState).length := by
    simp only [Record.encSession, List.length_append]
  have h1 := uint32Field_length_le 1 s.state.sessionVersion
  have h2 := bytesField_length_le 2 s.state.localIdentity.serialize
  rw [identityKey_serialize_length] at h2
  have h3 :
      (Record.bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD [])).length ≤
        53 := by
    rcases s.state.remoteIdentity with _ | ik
    · simp [Record.bytesField]
    · dsimp only [Option.map_some, Option.getD_some]
      have h := bytesField_length_le 3 ik.serialize
      rw [identityKey_serialize_length] at h
      exact h
  have h4 := bytesField_length_le 4 (HMAC.keyToBytes32 s.state.rootKey)
  rw [keyToBytes32_length] at h4
  have h5 := uint32Field_length_le 5 s.state.previousCounter
  have h6 : (Record.msgField 6 (s.state.senderChain.map Record.encSenderChain)).length ≤ 217 := by
    rcases s.state.senderChain with _ | sc
    · simp [Record.msgField]
    · dsimp only [Option.map_some, Record.msgField]
      have h0 := lenField_length_le 6 (Record.encSenderChain sc)
      have heq : (Record.encSenderChain sc).length =
          (Record.bytesField 1 sc.ratchetKey.publicKey.serialize).length +
          (Record.bytesField 2 sc.ratchetKey.privateKey.bytes.toList).length +
          (Record.lenField 3 (Record.encChainKey sc.chainKey)).length := by
        simp only [Record.encSenderChain, Record.msgField, List.length_append]
      have ha := bytesField_length_le 1 sc.ratchetKey.publicKey.serialize
      rw [publicKey_serialize_length] at ha
      have hb := bytesField_length_le 2 sc.ratchetKey.privateKey.bytes.toList
      rw [List.Vector.toList_length] at hb
      have hc := lenField_length_le 3 (Record.encChainKey sc.chainKey)
      have hd := encChainKey_length_le sc.chainKey
      omega
  have h7 := flatten_encReceiverChains_length_le s.state.receiverChains hrc_mk
  have h9 :
      (Record.msgField 9 (s.pendingPreKey.map Record.encPendingPreKey)).length ≤ 133 := by
    rcases s.pendingPreKey with _ | p
    · simp [Record.msgField]
    · dsimp only [Option.map_some, Record.msgField]
      have h0 := lenField_length_le 9 (Record.encPendingPreKey p)
      have heq : (Record.encPendingPreKey p).length =
          (Record.optUint32Field 1 p.preKeyId).length +
          (Record.bytesField 2 p.baseKey.serialize).length +
          (Record.int32Field 3 p.signedPreKeyId).length +
          (Record.uint64Field 4 p.timestamp).length := by
        simp only [Record.encPendingPreKey, List.length_append]
      have ha := optUint32Field_length_le 1 p.preKeyId
      have hb := bytesField_length_le 2 p.baseKey.serialize
      rw [publicKey_serialize_length] at hb
      have hc := int32Field_length_le 3 p.signedPreKeyId
      have hd := uint64Field_length_le 4 p.timestamp
      omega
  have h10 := uint32Field_length_le 10 s.remoteRegistrationId
  have h11 := uint32Field_length_le 11 s.localRegistrationId
  have h13 := bytesField_length_le 13 s.aliceBaseKey
  have h14 :
      (Record.msgField 14 (s.pendingKyberPreKey.map Record.encPendingKyber)).length ≤ 20060 := by
    rcases hp : s.pendingKyberPreKey with _ | pkp
    · simp [Record.msgField]
    · rw [hp] at hkyber
      dsimp only [Option.map_some, Record.msgField]
      have h0 := lenField_length_le 14 (Record.encPendingKyber pkp)
      have heq : (Record.encPendingKyber pkp).length =
          (Record.uint32Field 1 pkp.preKeyId).length +
            (Record.bytesField 2 pkp.ciphertext).length := by
        simp [Record.encPendingKyber]
      have ha := uint32Field_length_le 1 pkp.preKeyId
      have hb := bytesField_length_le 2 pkp.ciphertext
      omega
  have h15 := bytesField_length_le 15 s.state.pqRatchetState
  unfold fileCapBytes
  omega

private theorem nvXA_encodeRecordX_le_fileCap (s : SessionState HwBytes)
    (hrc : s.receiverChains = [⟨⟨nvSpkB.publicKey.bytes⟩, some ⟨nvKey0, 0#32⟩, []⟩])
    (hpq : s.pqRatchetState.length < 20000) :
    (encodeRecordUnderExtras (fun _ => nvXA) ⟨.A, s, 0, [0]⟩).length ≤ fileCapBytes := by
  rw [Symbolic.Swarm.CREF.Cli.encodeRecordX_eq_encodeRecord_pqSession]
  refine encodeRecord_some_length_le_fileCap _ ?_ ?_ ?_ ?_ hpq
  · simp [Symbolic.Swarm.CREF.Cli.pqSession_state, hrc]
  · intro rc hmem
    simp only [Symbolic.Swarm.CREF.Cli.pqSession_state, hrc, List.mem_singleton] at hmem
    subst hmem
    exact ⟨by simp, fun _ hm => nomatch hm⟩
  · rw [Symbolic.Swarm.CREF.Cli.pqSession_aliceBaseKey]
    simp [nvXA, initiatorRecordExtras, PublicKey.serialize, List.Vector.toList_length]
  · rw [Symbolic.Swarm.CREF.Cli.pqSession_pendingKyberPreKey]
    cases s.pendingPreKey
    · trivial
    · simp [nvXA, initiatorRecordExtras, kyberKey, List.Vector.toList_length]

private theorem nvXA_encodeRecordX_lt_31 (s : SessionState HwBytes)
    (hrc : s.receiverChains = [⟨⟨nvSpkB.publicKey.bytes⟩, some ⟨nvKey0, 0#32⟩, []⟩])
    (hpq : s.pqRatchetState.length < 20000) :
    (encodeRecordUnderExtras (fun _ => nvXA) ⟨.A, s, 0, [0]⟩).length < 2 ^ 31 := by
  have h := nvXA_encodeRecordX_le_fileCap s hrc hpq
  unfold fileCapBytes at h
  omega

private theorem nv_encRec_nvSA0_lt_31 :
    (encodeRecordUnderExtras (fun _ => nvXA) ⟨.A, nvSA0, 0, [0]⟩).length < 2 ^ 31 :=
  nvXA_encodeRecordX_lt_31 nvSA0 rfl nvPqA0_len_lt

private theorem nv_encRec_nvSA1_lt_31 :
    (encodeRecordUnderExtras (fun _ => nvXA) ⟨.A, nvSA1, 0, [0]⟩).length < 2 ^ 31 :=
  nvXA_encodeRecordX_lt_31 nvSA1 rfl nvPqA1_len_lt

private theorem nv_encRec_nvSA1_le_fileCap :
    (encodeRecordUnderExtras (fun _ => nvXA) ⟨.A, nvSA1, 0, [0]⟩).length ≤ fileCapBytes :=
  nvXA_encodeRecordX_le_fileCap nvSA1 rfl nvPqA1_len_lt

private theorem mem_encodeDir_signed (W : PEParams) (st : PqParty) {id : BitVec 32}
    {k : PqSignedKey} (hm : (id, k) ∈ st.signed) :
    (signedPreKeyFile id, signedRecordBytes W.C id k) ∈ encodeDir W st := by
  unfold encodeDir
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inl (List.mem_append.mpr (Or.inr ?_)))))))
  exact List.mem_map.mpr ⟨(id, k), hm, rfl⟩

private theorem mem_encodeDir_oneTime (W : PEParams) (st : PqParty) {id : BitVec 32}
    {k : Option (List.Vector (BitVec 8) 32)} (hm : (id, k) ∈ st.oneTime) :
    ∃ v, (oneTimePreKeyFile id, v) ∈ encodeDir W st := by
  rcases k with _ | sk
  · refine ⟨[], List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inr (List.mem_map.mpr ⟨(id, none), hm, rfl⟩))))))⟩
  · refine ⟨oneTimeRecordBytes W.C id sk, List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨(id, some sk), hm, rfl⟩))))))⟩

private theorem mem_encodeDir_kyberOneTime (W : PEParams) (st : PqParty) {id : BitVec 32}
    {k : Option PqKyberKey} (hm : (id, k) ∈ st.kyberOneTime) :
    ∃ v, (oneTimeKyberPreKeyFile id, v) ∈ encodeDir W st := by
  rcases k with _ | sk
  · refine ⟨[], List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨(id, none), hm, rfl⟩))))⟩
  · refine ⟨kyberRecordBytes id sk, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨(id, some sk), hm, rfl⟩))))⟩

private theorem mem_encodeDir_kyberLastResort (W : PEParams) (st : PqParty) {id : BitVec 32}
    {k : PqKyberKey} {seen : List (BitVec 32 × List.Vector (BitVec 8) 32)}
    (hm : (id, k, seen) ∈ st.kyberLastResort) :
    (lastResortKyberPreKeyFile id, kyberRecordBytes id k) ∈ encodeDir W st := by
  unfold encodeDir
  refine List.mem_append.mpr (Or.inr ?_)
  exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨(id, k, seen), hm, rfl⟩,
    List.mem_cons_self ..⟩

private def aliceBaseFiles (W : PEParams) (me : LocalIdentity) (pid : Option IdentityKey) :
    List (String × HwBytes) :=
  [(addressFile, textBytes (partyAddress .A).text),
   (identityKeyPairFile, CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C me.idPriv).publicKey.bytes, me.idPriv.toList⟩),
   (registrationIdFile, le32 me.regId)] ++
  (match pid with
   | some k => [(identityFile (partyAddressName .B), k.serialize)]
   | none => [])

private theorem encodeDir_eq_aliceBase_append (W : PEParams) (st : PqParty)
    (hp : st.party = .A) (hsig : st.signed = []) (hot : st.oneTime = [])
    (hkot : st.kyberOneTime = []) (hklr : st.kyberLastResort = []) :
    encodeDir W st = aliceBaseFiles W st.me st.peerId ++
      (match st.session with
       | some (x, g) => [(sessionFile (partyAddress .B), encodeRecordUnderExtras (fun _ => x) g)]
       | none => []) := by
  unfold encodeDir aliceBaseFiles
  rw [hp, hsig, hot, hkot, hklr]
  simp only [Party.other, List.map_nil, List.flatten_nil, List.append_nil, List.append_assoc]
  rfl

private theorem nv_wfPq_nvStA2 : PqxdhPartyInSpecDomain nvW nvStA2 := by
  have hInit : initiateState nvX nvW .A nvStA0.me nvBundleB nvTapeA =
      some (nvXA, ⟨.A, nvSA0, 0, [0]⟩) := by
    have h1 := nv_step1_init
    unfold pqInitModel at h1
    have htr : nvStA0.trusts ⟨⟨nvBundleB.idPub⟩⟩ = true := rfl
    have hpA : nvStA0.party = .A := rfl
    rw [htr, hpA] at h1
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
    cases hi : initiateState nvX nvW .A nvStA0.me nvBundleB nvTapeA with
    | none => rw [hi] at h1; cases h1
    | some xg =>
      rcases xg with ⟨x0, g0⟩
      rw [hi] at h1
      have hs := congrArg PqParty.session (Prod.mk.inj (Option.some.inj (Option.some.inj h1))).1
      simpa [nvStA1] using hs
  have hR0 : ReachablePqxdhSession nvW nvStA2.me nvXA ⟨.A, nvSA0, 0, [0]⟩ :=
    ReachablePqxdhSession.initiate nvX .A nvStA0.me nvBundleB nvTapeA nvXA ⟨.A, nvSA0, 0, [0]⟩ hInit
  have hR1 : ReachablePqxdhSession nvW nvStA2.me nvXA
      (((pqxdhSessionParams nvW).send ⟨.A, nvSA0, 0, [0]⟩ nvPt1 nvCoins64A).1) :=
    ReachablePqxdhSession.send nvPt1 nvCoins64A hR0 nv_encRec_nvSA0_lt_31
  have hSendEq :
      ((pqxdhSessionParams nvW).send ⟨.A, nvSA0, 0, [0]⟩ nvPt1 nvCoins64A).1.party = .A ∧
      ((pqxdhSessionParams nvW).send ⟨.A, nvSA0, 0, [0]⟩ nvPt1 nvCoins64A).1.session = nvSA1 := by
    have hm := nv_msgEncrypt1
    unfold pqxdhSessionParams at hm
    unfold pqxdhSessionParams Params.send
    dsimp only at hm ⊢
    rw [hm]
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x g hs
    have hs' : some (nvXA, (⟨.A, nvSA1, 0, [0]⟩ : GhostState HwBytes)) = some (x, g) := hs
    cases Option.some.inj hs'
    exact ⟨⟨_, hR1, hSendEq.1, hSendEq.2⟩, rfl, nv_encRec_nvSA1_lt_31⟩
  · intro f hf
    rw [encodeDir_eq_aliceBase_append nvW nvStA2 rfl rfl rfl rfl rfl] at hf
    have hpA2 : nvStA2.peerId = some ⟨nvIdB.publicKey⟩ := rfl
    have hsA2 : nvStA2.session = some (nvXA, ⟨.A, nvSA1, 0, [0]⟩) := rfl
    rw [hpA2, hsA2] at hf
    rcases List.mem_append.mp hf with hbase | hsess
    · dsimp only [aliceBaseFiles, List.cons_append, List.nil_append] at hbase
      rcases List.mem_cons.mp hbase with rfl | hf1
      · refine ⟨by dsimp only; decide +kernel, fun _ => by dsimp only [fileCapBytes]; decide +kernel⟩
      · rcases List.mem_cons.mp hf1 with rfl | hf2
        · refine ⟨?_, fun _ => ?_⟩
          · dsimp only
            simp [CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode,
              CryptoVerification.RecordCodecs.encodeProto3BytesField, encodeBytesField, encodeKey,
              WireType.toNat, encodeVarint, djbKey]
            decide
          · dsimp only [fileCapBytes]
            simp [CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode,
              CryptoVerification.RecordCodecs.encodeProto3BytesField, encodeBytesField, encodeKey,
              WireType.toNat, encodeVarint, djbKey]
            decide
        · rcases List.mem_cons.mp hf2 with rfl | hf3
          · refine ⟨by dsimp only; decide, fun _ => by dsimp only [fileCapBytes]; decide⟩
          · rcases List.mem_cons.mp hf3 with rfl | hf4
            · refine ⟨?_, fun _ => ?_⟩
              · dsimp only
                rw [Symbolic.Swarm.CREF.TR.Pure.identityKey_serialize_length]
                decide
              · dsimp only [fileCapBytes]
                rw [Symbolic.Swarm.CREF.TR.Pure.identityKey_serialize_length]
                decide
            · nomatch hf4
    · rw [List.mem_singleton] at hsess
      subst hsess
      exact ⟨nv_encRec_nvSA1_lt_31, fun _ => nv_encRec_nvSA1_le_fileCap⟩
  · decide
  · decide
  · decide
  · decide

private theorem pendingPreKey_tryDecryptFromRecord_false {PQC : Type}
    (C : Crypto) (S : Spqr HwBytes PQC)
    (expected : Option HwBytes) (m : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (st st' : SessionState HwBytes) (pt : HwBytes)
    (h : SessionState.tryDecryptFromRecord C S expected m msgType coins st = (.ok pt, st')) :
    st'.pendingPreKey = false := by
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C S expected m msgType coins) st with
      ⟨e | ptext, updated⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, rfl⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hd
      rcases hrem : st.remoteIdentity with _ | remote
      · simp only [hrem, Symbolic.Swarm.CREF.Cli.mut_exec_bind,
          Symbolic.Swarm.CREF.Cli.mut_exec_modifyGet, Symbolic.Swarm.CREF.Cli.mut_exec_get,
          Symbolic.Swarm.CREF.Cli.mut_exec_throw] at hd
        nomatch hd
      · simp only [hrem, Symbolic.Swarm.CREF.Cli.mut_exec_bind,
          Symbolic.Swarm.CREF.Cli.mut_exec_modifyGet, Symbolic.Swarm.CREF.Cli.mut_exec_get,
          Symbolic.Swarm.CREF.Cli.mut_exec_pure] at hd
        rcases hdec : Mut.exec (TripleRatchet.decrypt C S expected m msgType coins)
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩ with ⟨e | pt', tr'⟩
        · rw [hdec] at hd
          simp only [Symbolic.Swarm.CREF.Cli.mut_exec_liftE] at hd
          nomatch hd
        · rw [hdec] at hd
          simp only [Symbolic.Swarm.CREF.Cli.mut_exec_liftE,
            Symbolic.Swarm.CREF.Cli.mut_exec_modify, Prod.mk.injEq, Except.ok.injEq] at hd
          rcases hd with ⟨_, rfl⟩
          rfl

private theorem identityKey_serialize_inj {k₁ k₂ : IdentityKey}
    (h : k₁.serialize = k₂.serialize) : k₁ = k₂ := by
  rcases k₁ with ⟨⟨v₁⟩⟩
  rcases k₂ with ⟨⟨v₂⟩⟩
  have hv : v₁ = v₂ := List.Vector.eq v₁ v₂ ((List.cons.inj h).2)
  subst hv
  rfl

private theorem regularFileList_coins (v : HwBytes) :
    Symbolic.Swarm.CREF.Cli.RegularFileList [(coinsFile, v)] :=
  Symbolic.Swarm.CREF.Cli.regularFile_root (by decide) (by decide) (by decide) (by decide)

private theorem filesOf_pqRecvInputs_coins (P : PEParams) (st : PqParty)
    (c : HwBytes) (rc : BitVec 256) :
    filesOf (pqRecvInputs P st c rc).files coinsFile = some (HMAC.keyToBytes32 rc) := by
  open Symbolic.Swarm.CREF.Cli in
  have hcoins := regularFileList_coins (HMAC.keyToBytes32 rc)
  simp only [pqRecvInputs, pqInputs, List.append_nil]
  rw [filesOf_append_of_regular (regularFileList_encodeDir P st) hcoins coinsFile]
  have hc : filesOf [(coinsFile, HMAC.keyToBytes32 rc)] coinsFile =
      some (HMAC.keyToBytes32 rc) := by
    rw [filesOf_eq_optFold hcoins coinsFile]
    simp
  rw [hc]
  rfl

private theorem filesOf_pqRecvInputs_nonCoins (P : PEParams) (st : PqParty)
    (c : HwBytes) (rc : BitVec 256) (p : String)
    (hp : Arm64.normalizePath p ≠ ["coins"]) :
    filesOf (pqRecvInputs P st c rc).files p = filesOf (encodeDir P st) p := by
  open Symbolic.Swarm.CREF.Cli in
  have hcoins := regularFileList_coins (HMAC.keyToBytes32 rc)
  simp only [pqRecvInputs, pqInputs, List.append_nil]
  rw [filesOf_append_of_regular (regularFileList_encodeDir P st) hcoins p]
  have hc : filesOf [(coinsFile, HMAC.keyToBytes32 rc)] p = none := by
    refine filesOf_eq_none_of_forall_ne hcoins fun f hf heq => hp ?_
    rw [List.mem_singleton] at hf
    subst hf
    dsimp only at heq
    exact heq.trans (by decide)
  simp [hc]

private theorem filesOf_encodeDir_alice_ne_session (W : PEParams) (st : PqParty)
    (x : RecordExtras) (g : GhostState HwBytes) (p : String)
    (hp : st.party = .A) (hs : st.session = some (x, g))
    (hsig : st.signed = []) (hot : st.oneTime = [])
    (hkot : st.kyberOneTime = []) (hklr : st.kyberLastResort = [])
    (hsp : Arm64.normalizePath p ≠ Arm64.normalizePath (sessionFile (partyAddress .B))) :
    filesOf (encodeDir W st) p = filesOf (aliceBaseFiles W st.me st.peerId) p := by
  open Symbolic.Swarm.CREF.Cli in
  have heq : encodeDir W st =
      aliceBaseFiles W st.me st.peerId ++ [(sessionFile (partyAddress .B), encodeRecordUnderExtras (fun _ => x) g)] := by
    rw [encodeDir_eq_aliceBase_append W st hp hsig hot hkot hklr, hs]
  have hreg := regularFileList_encodeDir W st
  rw [heq] at hreg ⊢
  have hb : RegularFileList (aliceBaseFiles W st.me st.peerId) :=
    fun f hf => hreg f (List.mem_append_left _ hf)
  have hs_reg : RegularFileList [(sessionFile (partyAddress .B), encodeRecordUnderExtras (fun _ => x) g)] :=
    fun f hf => hreg f (List.mem_append_right _ hf)
  rw [filesOf_append_of_regular hb hs_reg p]
  have hs_none : filesOf [(sessionFile (partyAddress .B), encodeRecordUnderExtras (fun _ => x) g)] p = none := by
    refine filesOf_eq_none_of_forall_ne hs_reg fun f hf hfn => hsp ?_
    rw [List.mem_singleton] at hf
    subst hf
    exact hfn
  simp [hs_none]

private theorem filesOf_encodeDir_alice_none_of_head (W : PEParams) (st₁ : PqParty)
    (pid : IdentityKey) (x₁ : RecordExtras) (g₁ : GhostState HwBytes)
    (hp₁ : st₁.party = .A) (hsig₁ : st₁.signed = []) (hot₁ : st₁.oneTime = [])
    (hkot₁ : st₁.kyberOneTime = []) (hklr₁ : st₁.kyberLastResort = [])
    (hpid₁ : st₁.peerId = some pid) (hsess₁ : st₁.session = some (x₁, g₁))
    {p d : String}
    (hhd : (Arm64.normalizePath p).head? = some d)
    (hnd : d ∉ ["address", "identity-key-pair", "registration-id", "identities", "sessions"]) :
    filesOf (encodeDir W st₁) p = none := by
  open Symbolic.Swarm.CREF.Cli in
  refine filesOf_eq_none_of_forall_ne (regularFileList_encodeDir W st₁) fun f hf heq => ?_
  rw [encodeDir_eq_aliceBase_append W st₁ hp₁ hsig₁ hot₁ hkot₁ hklr₁, hpid₁, hsess₁] at hf
  have hin : d ∈ ["address", "identity-key-pair", "registration-id", "identities", "sessions"] := by
    rcases List.mem_append.mp hf with hbase | hsess
    · dsimp only [aliceBaseFiles, List.cons_append, List.nil_append] at hbase
      rcases List.mem_cons.mp hbase with rfl | hf1
      · rw [heq] at hhd; have hd0 : (Arm64.normalizePath addressFile).head? = some "address" := rfl
        rw [hd0] at hhd; cases hhd; decide
      · rcases List.mem_cons.mp hf1 with rfl | hf2
        · rw [heq] at hhd
          have hd0 : (Arm64.normalizePath identityKeyPairFile).head? = some "identity-key-pair" := rfl
          rw [hd0] at hhd; cases hhd; decide
        · rcases List.mem_cons.mp hf2 with rfl | hf3
          · rw [heq] at hhd
            have hd0 : (Arm64.normalizePath registrationIdFile).head? = some "registration-id" := rfl
            rw [hd0] at hhd; cases hhd; decide
          · rcases List.mem_cons.mp hf3 with rfl | hf4
            · rw [heq] at hhd
              have hd0 : (Arm64.normalizePath (identityFile (partyAddressName .B))).head? = some "identities" :=
                rfl
              rw [hd0] at hhd; cases hhd; decide
            · nomatch hf4
    · rw [List.mem_singleton] at hsess
      subst hsess
      dsimp only at heq
      rw [heq] at hhd
      have hd0 : (Arm64.normalizePath (sessionFile (partyAddress .B))).head? = some "sessions" := rfl
      rw [hd0] at hhd; cases hhd; decide
  exact hnd hin

private theorem pqSession_eq_of_wfPq_encodeRecordX_eq (W₁ W₂ : PEParams) (st₁ st₂ : PqParty)
    (x₁ x₂ : RecordExtras) (g₁ g₂ : GhostState HwBytes)
    (hwf₁ : PqxdhPartyInSpecDomain W₁ st₁) (hs₁ : st₁.session = some (x₁, g₁))
    (hwf₂ : PqxdhPartyInSpecDomain W₂ st₂) (hs₂ : st₂.session = some (x₂, g₂))
    (heq : encodeRecordUnderExtras (fun _ => x₁) g₁ = encodeRecordUnderExtras (fun _ => x₂) g₂) :
    Symbolic.Swarm.CREF.Cli.pqSession x₁ g₁ = Symbolic.Swarm.CREF.Cli.pqSession x₂ g₂ := by
  open Symbolic.Swarm.CREF.Cli in
  have h1 := recordCanonical_Q_of_wfPq hwf₁ hs₁
  have h2 := recordCanonical_Q_of_wfPq hwf₂ hs₂
  rw [← heq] at h2
  exact Slots.recordCanonical_Q_inj h1 h2

private theorem pqRecvWhisperModel_transfer
    (W : PEParams) (st₁ st₂ : PqParty) (x₁ x₂ : RecordExtras) (g₁ g₂ : GhostState HwBytes)
    (s' : SessionState HwBytes) (body pt : HwBytes) (rc : BitVec 256) (pid : IdentityKey)
    (hs₁ : st₁.session = some (x₁, g₁)) (hs₂ : st₂.session = some (x₂, g₂))
    (hp : g₂.party = g₁.party) (hss : g₂.session = g₁.session)
    (htr : ∀ k, st₂.trusts k = st₁.trusts k)
    (h1 : pqRecvWhisperModel W st₁ body rc =
      some (some ({ st₁ with peerId := some pid, session := some (x₁, { g₁ with session := s' }) }, pt))) :
    pqRecvWhisperModel W st₂ body rc =
      some (some ({ st₂ with peerId := some pid, session := some (x₂, { g₂ with session := s' }) }, pt)) ∧
    s'.pendingPreKey = false := by
  unfold pqRecvWhisperModel at h1 ⊢
  rw [hs₁] at h1
  rw [hs₂]
  dsimp only at h1 ⊢
  rcases htf : SignalMessage.tryFrom protoSignalCodec body with _ | msg
  · simp only [htf] at h1; cases h1
  · simp only [htf, pqxdhSessionDecryptModel, hp, hss] at h1 ⊢
    rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).expectedAddrs g₁.party) msg .whisper rc g₁.session with ⟨e | pt', s₂⟩
    · simp only [hdec] at h1; cases e <;> cases h1
    · simp only [hdec] at h1 ⊢
      rcases hrem : s₂.remoteIdentity with _ | k
      · simp only [hrem] at h1; cases h1
      · simp only [hrem, htr k] at h1 ⊢
        cases htk : st₁.trusts k
        · simp [htk] at h1
        · simp only [htk, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq, Prod.mk.injEq] at h1 ⊢
          obtain ⟨hstEq, rfl⟩ := h1
          have hsEq := congrArg PqParty.session hstEq
          have hkEq := congrArg PqParty.peerId hstEq
          simp only [Option.some.injEq, Prod.mk.injEq] at hsEq hkEq
          have hs₂_eq : s₂ = s' := congrArg GhostState.session hsEq.2
          subst hs₂_eq
          subst hkEq
          exact ⟨⟨rfl, rfl⟩, pendingPreKey_tryDecryptFromRecord_false _ _ _ _ _ _ _ _ _ hdec⟩

private theorem pqRecvWhisper_observe_congr_alice (W : PEParams) (st₁ st₂ : PqParty)
    (pid : IdentityKey) (x₁ : RecordExtras) (s₁ s₁' : SessionState HwBytes)
    (body₁ body₂ pt : HwBytes) (rc₁ rc₂ : BitVec 256)
    (hwf₁ : PqxdhPartyInSpecDomain W st₁) (hwf₂ : PqxdhPartyInSpecDomain W st₂)
    (hp₁ : st₁.party = .A) (hsig₁ : st₁.signed = []) (hot₁ : st₁.oneTime = [])
    (hkot₁ : st₁.kyberOneTime = []) (hklr₁ : st₁.kyberLastResort = [])
    (hpid₁ : st₁.peerId = some pid)
    (hsess₁ : st₁.session = some (x₁, ⟨.A, s₁, 0, [0]⟩))
    (hstep : pqRecvWhisperModel W st₁ body₁ rc₁ =
      some (some ({ st₁ with peerId := some pid, session := some (x₁, ⟨.A, s₁', 0, [0]⟩) }, pt)))
    (heq : DY.Libsignal.Composed.Refinement.Cli.InputsEquiv
      (pqRecvInputs W st₁ (wireWhisper :: body₁) rc₁)
      (pqRecvInputs W st₂ (wireWhisper :: body₂) rc₂)) :
    pqxdhExpectedOutcome W (pqRecvInputs W st₁ (wireWhisper :: body₁) rc₁)
        (pqRecvWhisperModel W st₁ body₁ rc₁) =
      pqxdhExpectedOutcome W (pqRecvInputs W st₂ (wireWhisper :: body₂) rc₂)
        (pqRecvWhisperModel W st₂ body₂ rc₂) := by
  open Symbolic.Swarm.CREF.Cli in
  have hbody : body₂ = body₁ := ((List.cons.inj heq.2.2.1).2).symm
  subst body₂
  have hparty : st₂.party = .A := by
    cases hp : st₂.party
    · rfl
    · have harg : (Cmd.recv (partyAddress .B)).argv = (Cmd.recv (partyAddress .A)).argv := by
        have h0 := heq.1
        simpa only [pqRecvInputs, pqInputs, hp₁, hp, Party.other] using h0
      exact absurd harg (by decide)
  have hrc : rc₂ = rc₁ := by
    have hc := heq.2.2.2 coinsFile
    rw [filesOf_pqRecvInputs_coins, filesOf_pqRecvInputs_coins] at hc
    exact (keyToBytes32_inj (Option.some.inj hc)).symm
  subst rc₂
  have hdir : ∀ p, Arm64.normalizePath p ≠ ["coins"] →
      filesOf (encodeDir W st₁) p = filesOf (encodeDir W st₂) p := by
    intro p hp
    have h0 := heq.2.2.2 p
    rwa [filesOf_pqRecvInputs_nonCoins _ _ _ _ p hp,
      filesOf_pqRecvInputs_nonCoins _ _ _ _ p hp] at h0
  have hno_mem : ∀ (p d : String) (g : String × HwBytes),
      (Arm64.normalizePath p).head? = some d →
      d ∉ ["address", "identity-key-pair", "registration-id", "identities", "sessions", "coins"] →
      g ∈ encodeDir W st₂ →
      Arm64.normalizePath p = Arm64.normalizePath g.1 → False := by
    intro p d g hhd hnd hmem hpq
    have hnc : Arm64.normalizePath p ≠ ["coins"] := fun hc => by
      rw [hc] at hhd; cases hhd; exact hnd (by decide)
    have hnone := filesOf_encodeDir_alice_none_of_head W st₁ pid x₁ ⟨.A, s₁, 0, [0]⟩
      hp₁ hsig₁ hot₁ hkot₁ hklr₁ hpid₁ hsess₁ hhd
      (fun hm => hnd (List.mem_append_left ["coins"] hm))
    rw [hdir p hnc] at hnone
    exact filesOf_ne_none_of_mem (regularFileList_encodeDir W st₂) hmem hpq hnone
  have hsig : st₂.signed = [] := by
    cases hs : st₂.signed with
    | nil => rfl
    | cons kv _ =>
      rcases kv with ⟨id, k⟩
      have hhd : (Arm64.normalizePath (signedPreKeyFile id)).head? = some "signed-pre-keys" := by
        simpa [signedPreKeyFile] using head_norm_dir_nat_suf "signed-pre-keys" "" id.toNat
          (by decide) (by decide) (by decide) (by decide)
      have hm : (id, k) ∈ st₂.signed := by rw [hs]; exact List.mem_cons_self ..
      exact False.elim (hno_mem _ _ _ hhd (by decide) (mem_encodeDir_signed W st₂ hm) rfl)
  have hot : st₂.oneTime = [] := by
    cases ho : st₂.oneTime with
    | nil => rfl
    | cons kv _ =>
      rcases kv with ⟨id, k⟩
      have hhd : (Arm64.normalizePath (oneTimePreKeyFile id)).head? = some "one-time-pre-keys" := by
        simpa [oneTimePreKeyFile] using head_norm_dir_nat_suf "one-time-pre-keys" "" id.toNat
          (by decide) (by decide) (by decide) (by decide)
      have hm : (id, k) ∈ st₂.oneTime := by rw [ho]; exact List.mem_cons_self ..
      obtain ⟨_, hmem⟩ := mem_encodeDir_oneTime W st₂ hm
      exact False.elim (hno_mem _ _ _ hhd (by decide) hmem rfl)
  have hkot : st₂.kyberOneTime = [] := by
    cases hk : st₂.kyberOneTime with
    | nil => rfl
    | cons kv _ =>
      rcases kv with ⟨id, k⟩
      have hhd : (Arm64.normalizePath (oneTimeKyberPreKeyFile id)).head? =
          some "one-time-kyber-pre-keys" := by
        simpa [oneTimeKyberPreKeyFile] using head_norm_dir_nat_suf "one-time-kyber-pre-keys" ""
          id.toNat (by decide) (by decide) (by decide) (by decide)
      have hm : (id, k) ∈ st₂.kyberOneTime := by rw [hk]; exact List.mem_cons_self ..
      obtain ⟨_, hmem⟩ := mem_encodeDir_kyberOneTime W st₂ hm
      exact False.elim (hno_mem _ _ _ hhd (by decide) hmem rfl)
  have hklr : st₂.kyberLastResort = [] := by
    cases hl : st₂.kyberLastResort with
    | nil => rfl
    | cons kvs _ =>
      rcases kvs with ⟨id, k, seen⟩
      have hhd : (Arm64.normalizePath (lastResortKyberPreKeyFile id)).head? =
          some "last-resort-kyber-pre-keys" := by
        simpa [lastResortKyberPreKeyFile] using head_norm_dir_nat_suf "last-resort-kyber-pre-keys" ""
          id.toNat (by decide) (by decide) (by decide) (by decide)
      have hm : (id, k, seen) ∈ st₂.kyberLastResort := by rw [hl]; exact List.mem_cons_self ..
      exact False.elim (hno_mem _ _ _ hhd (by decide) (mem_encodeDir_kyberLastResort W st₂ hm) rfl)
  have hnd_st₂ : ((encodeDir W st₂).map fun f => Arm64.normalizePath f.1).Nodup :=
    encodeDir_norm_nodup W st₂ (by simp [hsig]) (by simp [hot]) hkot (by simp [hklr])
  have hnd_st₁ : ((encodeDir W st₁).map fun f => Arm64.normalizePath f.1).Nodup :=
    encodeDir_norm_nodup W st₁ (by simp [hsig₁]) (by simp [hot₁]) hkot₁ (by simp [hklr₁])
  have hpeer : st₂.peerId = some pid := by
    have hp_id := hdir (identityFile (partyAddressName .B)) (by decide)
    have h1_id : filesOf (encodeDir W st₁) (identityFile (partyAddressName .B)) = some pid.serialize :=
      filesOf_eq_some_of_mem_nodup (regularFileList_encodeDir W st₁) hnd_st₁
        (by rw [encodeDir_eq_aliceBase_append W st₁ hp₁ hsig₁ hot₁ hkot₁ hklr₁, hpid₁]
            exact List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))) rfl
    rw [h1_id] at hp_id
    cases hpi : st₂.peerId with
    | none =>
      have hst_none : filesOf (encodeDir W st₂) (identityFile (partyAddressName .B)) = none := by
        refine filesOf_eq_none_of_forall_ne (regularFileList_encodeDir W st₂) fun f hf hfn => ?_
        rw [encodeDir_eq_aliceBase_append W st₂ hparty hsig hot hkot hklr, hpi] at hf
        dsimp only [aliceBaseFiles, List.append_nil] at hf
        rcases List.mem_append.mp hf with hf1 | hfs
        · rcases List.mem_cons.mp hf1 with rfl | hf2
          · dsimp only at hfn; exact absurd hfn (by decide)
          · rcases List.mem_cons.mp hf2 with rfl | hf3
            · dsimp only at hfn; exact absurd hfn (by decide)
            · rcases List.mem_cons.mp hf3 with rfl | hf4
              · dsimp only at hfn; exact absurd hfn (by decide)
              · nomatch hf4
        · cases hs1 : st₂.session with
          | none => rw [hs1] at hfs; nomatch hfs
          | some xg =>
            rcases xg with ⟨x2, g2⟩
            rw [hs1, List.mem_singleton] at hfs
            subst hfs; dsimp only at hfn; exact absurd hfn (by decide)
      rw [hst_none] at hp_id; cases hp_id
    | some k =>
      have hst_id : filesOf (encodeDir W st₂) (identityFile (partyAddressName .B)) = some k.serialize :=
        filesOf_eq_some_of_mem_nodup (regularFileList_encodeDir W st₂) hnd_st₂
          (by rw [encodeDir_eq_aliceBase_append W st₂ hparty hsig hot hkot hklr, hpi]
              exact List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))) rfl
      rw [hst_id] at hp_id
      exact congrArg some (identityKey_serialize_inj (Option.some.inj hp_id)).symm
  have hsess_ex : ∃ x g, st₂.session = some (x, g) ∧
      pqSession x₁ ⟨.A, s₁, 0, [0]⟩ = pqSession x g ∧ g.party = .A := by
    have hp_s := hdir (sessionFile (partyAddress .B)) (by decide)
    have h1_s : filesOf (encodeDir W st₁) (sessionFile (partyAddress .B)) =
        some (encodeRecordUnderExtras (fun _ => x₁) ⟨.A, s₁, 0, [0]⟩) :=
      filesOf_eq_some_of_mem_nodup (regularFileList_encodeDir W st₁) hnd_st₁
        (by rw [encodeDir_eq_aliceBase_append W st₁ hp₁ hsig₁ hot₁ hkot₁ hklr₁, hsess₁]
            exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))) rfl
    rw [h1_s] at hp_s
    cases hs : st₂.session with
    | none =>
      have hst_none : filesOf (encodeDir W st₂) (sessionFile (partyAddress .B)) = none := by
        refine filesOf_eq_none_of_forall_ne (regularFileList_encodeDir W st₂) fun f hf hfn => ?_
        rw [encodeDir_eq_aliceBase_append W st₂ hparty hsig hot hkot hklr, hpeer, hs,
          List.append_nil] at hf
        dsimp only [aliceBaseFiles, List.cons_append, List.nil_append] at hf
        rcases List.mem_cons.mp hf with rfl | hf1
        · dsimp only at hfn; exact absurd hfn (by decide)
        · rcases List.mem_cons.mp hf1 with rfl | hf2
          · dsimp only at hfn; exact absurd hfn (by decide)
          · rcases List.mem_cons.mp hf2 with rfl | hf3
            · dsimp only at hfn; exact absurd hfn (by decide)
            · rcases List.mem_cons.mp hf3 with rfl | hf4
              · dsimp only at hfn; exact absurd hfn (by decide)
              · nomatch hf4
      rw [hst_none] at hp_s; cases hp_s
    | some xg =>
      rcases xg with ⟨x, g⟩
      have hst_s : filesOf (encodeDir W st₂) (sessionFile (partyAddress .B)) =
          some (encodeRecordUnderExtras (fun _ => x) g) :=
        filesOf_eq_some_of_mem_nodup (regularFileList_encodeDir W st₂) hnd_st₂
          (by rw [encodeDir_eq_aliceBase_append W st₂ hparty hsig hot hkot hklr, hs]
              exact List.mem_append_right _ (List.mem_cons_self ..)) rfl
      rw [hst_s] at hp_s
      have hrec_eq :
          encodeRecordUnderExtras (fun _ => x₁) ⟨.A, s₁, 0, [0]⟩ = encodeRecordUnderExtras (fun _ => x) g :=
        Option.some.inj hp_s
      have hpqs := pqSession_eq_of_wfPq_encodeRecordX_eq W W st₁ st₂ x₁ x
        ⟨.A, s₁, 0, [0]⟩ g hwf₁ hsess₁ hwf₂ hs hrec_eq
      exact ⟨x, g, rfl, hpqs, ((hwf₂.1 x g hs).2.1).trans hparty⟩
  obtain ⟨x, g, hsess, hpqs, hg_party⟩ := hsess_ex
  have hg_sess : g.session = s₁ := (congrArg (·.state) hpqs).symm
  have htrusts_eq : ∀ k, st₂.trusts k = st₁.trusts k := fun k => by
    simp only [PqParty.trusts, hpeer, hpid₁]
  have hmodel_st :
      pqRecvWhisperModel W st₂ body₁ rc₁ =
      some (some ({ st₂ with peerId := some pid
                             session := some (x, { g with session := s₁' }) }, pt)) ∧
      s₁'.pendingPreKey = false :=
    pqRecvWhisperModel_transfer W st₁ st₂ x₁ x ⟨.A, s₁, 0, [0]⟩ g s₁' body₁ pt
      rc₁ pid hsess₁ hsess hg_party hg_sess htrusts_eq hstep
  rw [hstep, hmodel_st.1]
  let st₁'' : PqParty :=
    { st₁ with peerId := some pid, session := some (x₁, ⟨.A, s₁', 0, [0]⟩) }
  let st₂' : PqParty :=
    { st₂ with peerId := some pid, session := some (x, { g with session := s₁' }) }
  have hrec_new : encodeRecordUnderExtras (fun _ => x) { g with session := s₁' } =
      encodeRecordUnderExtras (fun _ => x₁) ⟨.A, s₁', 0, [0]⟩ := by
    rw [encodeRecordX_clearPending_eq_storedSession x g s₁' hmodel_st.2,
      ← hpqs,
      ← encodeRecordX_clearPending_eq_storedSession x₁ ⟨.A, s₁, 0, [0]⟩ s₁' hmodel_st.2]
  have hnd_st₁'' : ((encodeDir W st₁'').map fun f => Arm64.normalizePath f.1).Nodup :=
    encodeDir_norm_nodup W st₁'' (by simp [st₁'', hsig₁]) (by simp [st₁'', hot₁]) hkot₁
      (by simp [st₁'', hklr₁])
  have hnd_st₂' : ((encodeDir W st₂').map fun f => Arm64.normalizePath f.1).Nodup :=
    encodeDir_norm_nodup W st₂' (by simp [st₂', hsig]) (by simp [st₂', hot]) hkot
      (by simp [st₂', hklr])
  have hdir_after : ∀ p, filesOf (encodeDir W st₁'') p = filesOf (encodeDir W st₂') p := by
    intro p
    by_cases hsp : Arm64.normalizePath p = Arm64.normalizePath (sessionFile (partyAddress .B))
    · have h1 : filesOf (encodeDir W st₁'') p =
          some (encodeRecordUnderExtras (fun _ => x₁) ⟨.A, s₁', 0, [0]⟩) :=
        filesOf_eq_some_of_mem_nodup (regularFileList_encodeDir W st₁'') hnd_st₁''
          (by rw [encodeDir_eq_aliceBase_append W st₁'' hp₁ hsig₁ hot₁ hkot₁ hklr₁]
              exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))) hsp
      have h2 : filesOf (encodeDir W st₂') p =
          some (encodeRecordUnderExtras (fun _ => x) { g with session := s₁' }) :=
        filesOf_eq_some_of_mem_nodup (regularFileList_encodeDir W st₂') hnd_st₂'
          (by rw [encodeDir_eq_aliceBase_append W st₂' hparty hsig hot hkot hklr]
              exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))) hsp
      rw [h1, h2, hrec_new]
    · by_cases hcp : Arm64.normalizePath p = ["coins"]
      · have hs : IsScrubbedPath p = true :=
          (isScrubbedPath_congr hcp).trans (by decide : IsScrubbedPath coinsFile = true)
        have h1 : filesOf (encodeDir W st₁'') p = none :=
          filesOf_eq_none_of_forall_ne (regularFileList_encodeDir W st₁'') fun f hf hfn => by
            have := (isScrubbedPath_congr hfn).symm.trans hs
            rw [isScrubbedPath_encodeDir W st₁'' f hf] at this
            cases this
        have h2 : filesOf (encodeDir W st₂') p = none :=
          filesOf_eq_none_of_forall_ne (regularFileList_encodeDir W st₂') fun f hf hfn => by
            have := (isScrubbedPath_congr hfn).symm.trans hs
            rw [isScrubbedPath_encodeDir W st₂' f hf] at this
            cases this
        rw [h1, h2]
      · have hA3_eq : filesOf (encodeDir W st₁'') p = filesOf (encodeDir W st₁) p := by
          have h1 := filesOf_encodeDir_alice_ne_session W st₁'' x₁ ⟨.A, s₁', 0, [0]⟩ p
            hp₁ rfl hsig₁ hot₁ hkot₁ hklr₁ hsp
          have h2 := filesOf_encodeDir_alice_ne_session W st₁ x₁ ⟨.A, s₁, 0, [0]⟩ p
            hp₁ hsess₁ hsig₁ hot₁ hkot₁ hklr₁ hsp
          have hme : st₁''.me = st₁.me := rfl; have hpid : st₁''.peerId = st₁.peerId := hpid₁.symm
          rw [h1, h2, hme, hpid]
        have hst'_eq : filesOf (encodeDir W st₂') p = filesOf (encodeDir W st₂) p := by
          have h1 := filesOf_encodeDir_alice_ne_session W st₂' x { g with session := s₁' } p
            hparty rfl hsig hot hkot hklr hsp
          have h2 := filesOf_encodeDir_alice_ne_session W st₂ x g p
            hparty hsess hsig hot hkot hklr hsp
          have hme : st₂'.me = st₂.me := rfl; have hpid : st₂'.peerId = st₂.peerId := hpeer.symm
          rw [h1, h2, hme, hpid]
        rw [hA3_eq, hst'_eq, hdir p hcp]
  unfold pqxdhExpectedOutcome observe; dsimp only [Option.map]; congr 1; funext p
  have hiA : RegularFileList (pqRecvInputs W st₁ (wireWhisper :: body₁) rc₁).files := by
    simp only [pqRecvInputs, pqInputs, List.append_nil]
    exact (regularFileList_encodeDir W st₁).append (regularFileList_coins _)
  have hiS : RegularFileList (pqRecvInputs W st₂ (wireWhisper :: body₁) rc₁).files := by
    simp only [pqRecvInputs, pqInputs, List.append_nil]
    exact (regularFileList_encodeDir W st₂).append (regularFileList_coins _)
  rw [filesOf_append_of_regular hiA (regularFileList_encodeDir W st₁'') p,
    filesOf_append_of_regular hiS (regularFileList_encodeDir W st₂') p,
    hdir_after p, heq.2.2.2 p]

theorem pqModelPost_recvWhisper_nonvacuous_spqr_on_aux
    (interp : CryptoProofLib.Refinement.ExternInterpretation) :
    ∃ (P : PEParams) (st st' : PqParty) (body pt : HwBytes) (rc : BitVec 256)
      (i : Inputs) (o : Outcome),
      PqxdhPartyInSpecDomain P st ∧ body.length < 2 ^ 32 ∧
      i = pqRecvInputs P st (wireWhisper :: body) rc ∧
      pqRecvWhisperModel P st body rc = some (some (st', pt)) ∧
      o = pqxdhExpectedOutcome P i (some (some (st', pt))) ∧
      (∃ out fs, o = .exited 0 out fs) ∧
      (∃ x' g', st'.session = some (x', g') ∧ g'.session.pqRatchetState ≠ []) ∧
      DY.Libsignal.Composed.Refinement.Cli.PqModelPost interp P i o := by
  obtain ⟨sA2, hstep5, hsA2pq⟩ := nv_step5_recvA
  let st' : PqParty :=
    { nvStA2 with peerId := some ⟨nvIdB.publicKey⟩, session := some (nvXA, ⟨.A, sA2, 0, [0]⟩) }
  let i : Inputs := pqRecvInputs nvW nvStA2 (wireWhisper :: nvBody2) 9#256
  let o : Outcome := pqxdhExpectedOutcome nvW i (some (some (st', nvPt2)))
  refine ⟨nvW, nvStA2, st', nvBody2, nvPt2, 9#256, i, o,
    nv_wfPq_nvStA2, by decide, rfl, hstep5, rfl,
    ⟨nvPt2, _, rfl⟩, ⟨nvXA, ⟨.A, sA2, 0, [0]⟩, rfl, hsA2pq ▸ nvPqA2_ne_nil⟩, ?_⟩
  constructor
  · intro _ _ _ _ _ _ heq; exact absurd (List.cons.inj heq.1).1 (by decide)
  · intro _ _ _ _ _ heq; exact absurd (List.cons.inj heq.1).1 (by decide)
  · intro st body rc hwf _ heq
    change pqxdhExpectedOutcome nvW i (some (some (st', nvPt2))) = _; rw [← hstep5]
    exact pqRecvWhisper_observe_congr_alice nvW nvStA2 st ⟨nvIdB.publicKey⟩ nvXA nvSA1 sA2
      nvBody2 body nvPt2 9#256 rc nv_wfPq_nvStA2 hwf rfl rfl rfl rfl rfl rfl rfl hstep5 heq
  · intro _ _ _ _ _ _ _ heq; exact absurd (List.cons.inj heq.2.2.1).1 (by decide)
  · intro _ _ _ _ _ _ _ _ _ _ heq; exact absurd (List.cons.inj heq.2.2.1).1 (by decide)
  · intro _ c _ _ _ hw _ heq
    have hc : wireWhisper :: nvBody2 = c := heq.2.2.1; subst hc; exact absurd rfl hw
  · intro _ _ _ _ _ _ _ _ _ _ heq; exact absurd (List.cons.inj heq.2.2.1).1 (by decide)
  · intro _ _ _ _ _ _ heq; exact absurd (List.cons.inj heq.2.2.1).1 (by decide)
  · intro _ _ _ _ _ _ _ _ _ heq; exact absurd (List.cons.inj heq.2.2.1).1 (by decide)
  · intro _ _ _ _ _ _ _ _ _ _ _ heq; exact absurd (List.cons.inj heq.2.2.1).1 (by decide)
  · intro _ _ _ _ _ _ _ _ _ _ heq; exact absurd (List.cons.inj heq.2.2.1).1 (by decide)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ heq; exact absurd (List.cons.inj heq.2.2.1).1 (by decide)
  · intro _ _ _ _ _ _ _ _ _ heq; exact absurd (List.cons.inj heq.1).1 (by decide)
  · intro _ _ _ _ _ _ _ heq; exact absurd (List.cons.inj heq.1).1 (by decide)

end Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers

namespace Symbolic.Tests.Refinement.Cli

open DY.Libsignal (HwBytes)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession

section NonVacuity

def nvMlKem : CryptoVerification.LibsignalSpqrV1.MlKem where
  keyPair := fun _ => List.Vector.replicate 2400 0#8
  encaps1 := fun _ _ => some (List.Vector.replicate 960 0#8, List.Vector.replicate 2080 0#8,
    List.Vector.replicate 32 1#8)
  encaps2 := fun _ _ => List.Vector.replicate 128 0#8
  decaps := fun _ _ _ => List.Vector.replicate 32 1#8
  validPk := fun _ _ => true

def nvCrypto : Crypto where
  F := fun s _ => s
  E := fun _ b => b
  D := fun _ b => b
  X := fun _ _ => List.Vector.replicate 32 1#8
  pubKey := fun sk => sk

def nvW : PEParams where
  C := nvCrypto
  Q := {
    F512 := fun s _ => s
    scalarMod := fun _ => List.Vector.replicate 32 0#8
    scalarWide := fun _ => List.Vector.replicate 32 0#8
    montToEd := fun _ _ => some (List.Vector.replicate 160 0#8)
    isTorsionFree := fun _ => true
    edNeg := fun _ => List.Vector.replicate 160 0#8
    dsmb := fun _ _ _ => List.Vector.replicate 160 0#8
    compress := fun _ => List.Vector.replicate 32 0#8
    encaps := fun _ _ => (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 1#8)
    decaps := fun _ _ => List.Vector.replicate 32 1#8
    K := nvMlKem
  }

def nvX : UnreachedPqxdhPrimitives where
  sigPkGen := fun _ => List.replicate 32 0
  sigSign := fun _ _ _ => List.replicate 64 0
  scalarMul := fun _ _ => List.replicate 32 0
  scalarAdd := fun _ _ => List.replicate 32 0
  kemKeyGen := fun _ => (List.replicate 1568 0, List.replicate 3168 0)
  pow8 := fun x => x
  isValidDhTriple := fun _ _ _ => true

def nvKeysB : ResponderPreKeySecrets where
  spkId := 1#32
  spkPriv := List.Vector.replicate 32 2#8
  kpkId := 2#32
  kpkPub := List.Vector.replicate 1568 0#8
  kpkSec := List.Vector.replicate 3168 0#8
  opk := none

def nvStA0 : PqParty :=
  { emptyParty with party := .A, me := ⟨List.Vector.replicate 32 3#8, 10#32⟩ }

def nvStB0 : PqParty :=
  { party := .B
    me := ⟨List.Vector.replicate 32 4#8, 20#32⟩
    peerId := none
    session := none
    signed := [(1#32, ⟨List.Vector.replicate 32 2#8, List.Vector.replicate 64 0#8, 0#64⟩)]
    oneTime := []
    kyberOneTime := [(2#32, some ⟨List.Vector.replicate 1568 0#8, List.Vector.replicate 3168 0#8,
      List.Vector.replicate 64 0#8, 0#64⟩)]
    kyberLastResort := [] }

def nvBundleB : PreKeyBundleFields :=
  honestBundle nvW.C nvStB0.me nvKeysB (List.Vector.replicate 64 0#8) (List.Vector.replicate 64 0#8)

private def nvPrekeyMsgFromSend (stA1 : PqParty) (pt1 coins : HwBytes) : Option PreKeyMessageFields :=
  match stA1.session with
  | none => none
  | some (x1, g1) =>
    match SessionState.messageEncrypt nvW.C protoSignalCodec (pqxdhSpqrSession nvW)
        ((pqxdhSessionParams nvW).sendAddrs g1.party) pt1 coins g1.session with
    | (.ok msg1, _) =>
      some {
        regId := x1.localRegistrationId
        opkId := x1.pending.preKeyId
        spkId := x1.pending.signedPreKeyId
        kpkId := 2#32
        kyberCt := List.Vector.replicate 1568 0#8
        baseKey := x1.pending.baseKey.bytes
        idPub := g1.session.localIdentity.publicKey.bytes
        inner := msg1.serialized
      }
    | (.error _, _) => none

private def nvWhisperBodyOf (wire : HwBytes) : Option HwBytes :=
  match wire with
  | t :: body => if t = wireWhisper then some body else none
  | [] => none

private theorem of_nvWhisperBodyOf {wire body : HwBytes}
    (h : nvWhisperBodyOf wire = some body) : wire = wireWhisper :: body := by
  cases wire with
  | nil => cases h
  | cons t b =>
    unfold nvWhisperBodyOf at h
    dsimp only at h
    split at h
    · rename_i ht
      rw [ht, Option.some.inj h]
    · cases h

def nvTapeA : List.Vector (BitVec 8) initiateTapeLen :=
  List.Vector.replicate initiateTapeLen 5#8
def nvCoins64A : HwBytes := List.replicate 64 6#8
def nvCoins64B : HwBytes := List.replicate 64 7#8
def nvPt1 : HwBytes := [0x48#8, 0x69#8]
def nvPt2 : HwBytes := [0x4F#8, 0x4B#8]

/-- Running the 5-step CLI model roundtrip from empty-session `PqParty` states with SPQR V1 active
succeeds and produces a non-empty V1 SPQR ratchet state. -/
theorem pqRecvWhisper_nonvacuous_spqr_on :
    nvStA0.session = none ∧
    nvStB0.session = none ∧
    ∃ (stA1 stA2 stB1 stB2 stA3 : PqParty) (m1 : PreKeyMessageFields) (wire1 wire2 body2 : HwBytes),
      pqInitModel nvX nvW nvStA0 nvBundleB nvTapeA =
        some (some (stA1, [])) ∧
      pqSendModel nvW stA1 nvPt1 nvCoins64A =
        some (some (stA2, wire1)) ∧
      wire1 = wirePrekey :: m1.bytes ∧
      pqRecvPrekeyModel nvX nvW nvStB0 m1 8#256 =
        some (some (stB1, nvPt1)) ∧
      pqSendModel nvW stB1 nvPt2 nvCoins64B =
        some (some (stB2, wire2)) ∧
      wire2 = wireWhisper :: body2 ∧
      pqRecvWhisperModel nvW stA2 body2 9#256 =
        some (some (stA3, nvPt2)) ∧
      ∃ x3 g3, stA3.session = some (x3, g3) ∧ g3.session.pqRatchetState ≠ [] :=
  Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers.mock_nonvacuous_spqr_on

end NonVacuity

/--
info: 'Symbolic.Tests.Refinement.Cli.pqRecvWhisper_nonvacuous_spqr_on' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pqRecvWhisper_nonvacuous_spqr_on

/-- Satisfiability of `PqModelPost` on an accepted SPQR-ON whisper `recv` call inside
`PqxdhPartyInSpecDomain` with a non-empty post-state V1 SPQR ratchet state. -/
theorem pqModelPost_recvWhisper_nonvacuous_spqr_on
    (interp : CryptoProofLib.Refinement.ExternInterpretation) :
    ∃ (P : PEParams) (st st' : PqParty) (body pt : HwBytes) (rc : BitVec 256)
      (i : Inputs) (o : Outcome),
      PqxdhPartyInSpecDomain P st ∧
      body.length < 2 ^ 32 ∧
      i = pqRecvInputs P st (wireWhisper :: body) rc ∧
      pqRecvWhisperModel P st body rc = some (some (st', pt)) ∧
      o = pqxdhExpectedOutcome P i (some (some (st', pt))) ∧
      (∃ out fs, o = .exited 0 out fs) ∧
      (∃ x' g', st'.session = some (x', g') ∧ g'.session.pqRatchetState ≠ []) ∧
      DY.Libsignal.Composed.Refinement.Cli.PqModelPost interp P i o :=
  Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers.pqModelPost_recvWhisper_nonvacuous_spqr_on_aux
    interp

/--
info: 'Symbolic.Tests.Refinement.Cli.pqModelPost_recvWhisper_nonvacuous_spqr_on' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pqModelPost_recvWhisper_nonvacuous_spqr_on

end Symbolic.Tests.Refinement.Cli
