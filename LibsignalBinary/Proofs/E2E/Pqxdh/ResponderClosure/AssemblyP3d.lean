/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3c
public import LibsignalBinary.Proofs.E2E.HooksE.Common
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.ConsumeMessageKey.ModelProofs.AdvanceAndFrame
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.CanonPreservation
import LibsignalBinary.Proofs.E2E.Run.RecvPure
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.Open -- shake: keep

/-!
# Stage P3 Hypothesis Discharges and `tryDecryptFromRecord` Model Bridge

Discharges key-encoding, scalar-clamping, address-distinctness (`UuidNamesDistinct`), and
unconditional no-panic (`receiverChains = []`) side conditions on `initializeRecipientSession`, and
proves equivalence between `pqxdhTryDecryptModel` and `SessionState.tryDecryptFromRecord` together
with `CanonSession` preservation.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

namespace P3P4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
  CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalTripleRatchet.Decrypt.Model
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Run CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore

/-- Initial Bob `SessionState` constructed by `initializeRecipientSession` from `dk`. -/
abbrev recvPrekeyInitSession (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
    (dk : SignalPqxdh.DRKey) : SessionState Bytes :=
  initializeRecipientSession spqrOffB ⟨(keyPairOf W.C me.idPriv).publicKey⟩
    ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv) (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32
    (ofU8 dk.chainKey)) (HKDF.bytesToKey32 (ofU8 dk.pqrKey))

/-! ## 1. Key, Buffer, Clamping, and Address-Distinctness Discharges -/

theorem bytesToBv8_eq_ofU8 (bs : List UInt8) :
    bytesToBv8 bs = ofU8 bs :=
  ResponderCore.bytesToBv8_eq_ofU8 bs

@[simp]
theorem bytesToBv8_vecU8 (v : List.Vector (BitVec 8) 32) :
    bytesToBv8 (vecU8 v) = v.toList :=
  ResponderCore.bytesToBv8_vecU8 v

@[simp]
theorem length_bytesToBv8_vecU8 (v : List.Vector (BitVec 8) 32) :
    (bytesToBv8 (vecU8 v)).length = 32 := by
  rw [bytesToBv8_vecU8]
  exact v.toList_length

theorem bytesToBv8_encodeEC_vecU8 (v : List.Vector (BitVec 8) 32) :
    bytesToBv8 (Model.encodeEC (vecU8 v)) = (⟨v⟩ : PublicKey).serialize := by
  change bytesToBv8 ((5 : UInt8) :: vecU8 v) = 5#8 :: v.toList
  change 5#8 :: bytesToBv8 (vecU8 v) = 5#8 :: v.toList
  rw [bytesToBv8_vecU8]

@[simp]
theorem length_bytesToBv8_encodeEC_vecU8 (v : List.Vector (BitVec 8) 32) :
    (bytesToBv8 (Model.encodeEC (vecU8 v))).length = 33 := by
  rw [bytesToBv8_encodeEC_vecU8]
  simp [PublicKey.serialize]

theorem deserialize_bytesToBv8_encodeEC_vecU8 (v : List.Vector (BitVec 8) 32) :
    PublicKey.deserialize (bytesToBv8 (Model.encodeEC (vecU8 v))) = .ok (⟨v⟩ : PublicKey) := by
  rw [bytesToBv8_encodeEC_vecU8]
  unfold PublicKey.serialize PublicKey.deserialize
  have hlen : v.toList.length = 32 := v.toList_length
  simp [hlen, List.take_of_length_le (Nat.le_of_eq hlen)]

theorem spkPriv_clampScalar_idem (C : Crypto) (spkPriv : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (keyPairOf C spkPriv).privateKey.bytes = (keyPairOf C
      spkPriv).privateKey.bytes := by
  unfold keyPairOf
  dsimp only
  exact Reach.clampScalar_idem spkPriv

theorem acceptKeys_rootKey_chainKey_props {P : Primitives} {inp : AcceptKeysInput} {dk : DRKey}
    (hWF : StructuralPrims P) (hacc : Model.acceptKeys P inp = some dk) : (bytesToBv8
    dk.rootKey).length = 32 ∧ (bytesToBv8 dk.chainKey).length = 32 ∧ keyToBytes32 (HKDF.bytesToKey32
    (ofU8 dk.rootKey)) = bytesToBv8 dk.rootKey ∧ keyToBytes32 (HKDF.bytesToKey32 (ofU8 dk.chainKey))
    = bytesToBv8 dk.chainKey := by
  obtain ⟨hrk_len, _, hck_len⟩ := acceptKeys_some_lengths hWF hacc
  have hrk_bv_len : (bytesToBv8 dk.rootKey).length = 32 := by
    simpa [bytesToBv8] using hrk_len
  have hck_bv_len : (bytesToBv8 dk.chainKey).length = 32 := by
    simpa [bytesToBv8] using hck_len
  have hrk_ofU8_len : (ofU8 dk.rootKey).length = 32 := by
    rwa [← bytesToBv8_eq_ofU8]
  have hck_ofU8_len : (ofU8 dk.chainKey).length = 32 := by
    rwa [← bytesToBv8_eq_ofU8]
  refine ⟨hrk_bv_len, hck_bv_len, ?_, ?_⟩
  · rw [bytesToBv8_eq_ofU8]
    exact Keys.keyToBytes32_bytesToKey32 (ofU8 dk.rootKey) hrk_ofU8_len
  · rw [bytesToBv8_eq_ofU8]
    exact Keys.keyToBytes32_bytesToKey32 (ofU8 dk.chainKey) hck_ofU8_len

theorem acceptKeys_modelPrims_rootKey_chainKey_props
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) {dk :
    SignalPqxdh.DRKey} (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m)
    = some dk) : (bytesToBv8 dk.rootKey).length = 32 ∧ (bytesToBv8 dk.chainKey).length = 32 ∧
    keyToBytes32 (HKDF.bytesToKey32 (ofU8 dk.rootKey)) = bytesToBv8 dk.rootKey ∧ keyToBytes32
    (HKDF.bytesToKey32 (ofU8 dk.chainKey)) = bytesToBv8 dk.chainKey ∧ Model.acceptKeys
    (ofSignalPqxdhPrimitives (modelPrims X W))
      (ofSignalPqxdhAcceptKeysInput (acceptInput W me k m)) = some (ofSignalPqxdhDRKey dk) := by
  have hWF : StructuralPrims (ofSignalPqxdhPrimitives (modelPrims X W)) :=
    Initiator.structuralPrims_initiatorModelPrims X W
  have hacc_rc :
      Model.acceptKeys (ofSignalPqxdhPrimitives (modelPrims X W))
        (ofSignalPqxdhAcceptKeysInput (acceptInput W me k m)) = some (ofSignalPqxdhDRKey dk) := by
    rw [Model.acceptKeys_ofSignalPqxdhPrimitives (modelPrims X W) (acceptInput W me k m), hacc]
    rfl
  obtain ⟨h1, h2, h3, h4⟩ := acceptKeys_rootKey_chainKey_props hWF hacc_rc
  exact ⟨h1, h2, h3, h4, hacc_rc⟩

theorem distinctSid_of_uuidNamesDistinct {parse : UuidParser}
    (hUuid : UuidNamesDistinct parse) (P : Party) (gMe gPeer : AddrGhost) (hgMe : gMe.val =
    (Role.ofParty P).addrVal) (hgPeer : gPeer.val = (Role.ofParty P).peer.addrVal) : DistinctSid
    parse gMe.name.bytes gPeer.name.bytes := by
  unfold DistinctSid
  have hMeName : gMe.name.bytes = (Role.ofParty P).nameBytes := by
    injection hgMe with h1 _
  have hPeerName : gPeer.name.bytes = (Role.ofParty P).peer.nameBytes := by
    injection hgPeer with h1 _
  rw [hMeName, hPeerName]
  exact serviceIdParse_role_ne_peer_of_uuidNamesDistinct hUuid (Role.ofParty P)

theorem not_self_or_distinctSid_of_uuidNamesDistinct {parse : UuidParser} {PQ : Type}
    (hUuid : UuidNamesDistinct parse) (P : Party) (gMe gPeer : AddrGhost) (st : SessionState PQ)
    (hgMe : gMe.val = (Role.ofParty P).addrVal) (hgPeer : gPeer.val = (Role.ofParty P).peer.addrVal)
    : st.remoteIdentity ≠ some st.localIdentity ∨ DistinctSid parse gMe.name.bytes gPeer.name.bytes
    :=
  Or.inr (distinctSid_of_uuidNamesDistinct hUuid P gMe gPeer hgMe hgPeer)

theorem bobSession344WithRegIds_entails_memRegion_344
    (a p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64) (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 :
    BitVec 64) (remoteRegId localRegId : BitVec 32) : (a ↦ₛ bobSession344WithRegIdsBv8 p1 p2 p3 p4
    c5 p5 p6 p7 p8 pad_f4
      c0 c1 c2 c3 c4 d0 d1 d2 remoteRegId localRegId) ⊢ memRegion a 344 := by
  have hlen := bobSession344WithRegIdsBv8_length p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4
    c0 c1 c2 c3 c4 d0 d1 d2 remoteRegId localRegId
  rw [← hlen]
  exact pointsToBytes_entails_memRegion a _

theorem bobSession344WithRegIds_entails_memRegion_104_240
    (a p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64) (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 :
    BitVec 64) (remoteRegId localRegId : BitVec 32) : (a ↦ₛ bobSession344WithRegIdsBv8 p1 p2 p3 p4
    c5 p5 p6 p7 p8 pad_f4
      c0 c1 c2 c3 c4 d0 d1 d2 remoteRegId localRegId) ⊢ memRegion a 104 ∗ memRegion (a + 104#64) 240
      := by
  refine Entails.trans (bobSession344WithRegIds_entails_memRegion_344 a p1 p2 p3 p4 c5 p5 p6 p7 p8
    pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 remoteRegId localRegId) ?_
  rw [memRegion_split a 104 240 (by decide)]
  exact Entails.refl _

theorem bobSession280Mid_append_entails_memRegion_288
    (a p3 p4 c5 p5 p6 p7 p8 : BitVec 64) (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 w : BitVec
    64) : (a ↦ₛ (bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++ unpack64
    w)) ⊢ memRegion a 288 := by
  have hlen : (bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++ unpack64
    w).length = 288 := by
    rw [List.length_append, bobSession280MidBv8_length, unpack64_length]
  rw [← hlen]
  exact pointsToBytes_entails_memRegion a _

theorem bobSession280Mid_append_56_entails_memRegion_344
    (a p3 p4 c5 p5 p6 p7 p8 : BitVec 64) (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 w : BitVec
    64) : (a ↦ₛ (bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++ unpack64
    w)) ∗ memRegion (a + 288#64) 56 ⊢ memRegion a 344 := by
  have h288 := bobSession280Mid_append_entails_memRegion_288 a p3 p4 c5 p5 p6 p7 p8 pad_f4
    c0 c1 c2 c3 c4 d0 d1 d2 w
  rw [memRegion_split a 288 56 (by decide)]
  exact sepConj_mono_left h288

private theorem stackAt_sub_split (sp : BitVec 64) (n m : Nat) (h1 : m ≤ n)
    (h2 : n ≤ 2 ^ 64) :
    stackAt sp n = memRegion (sp - BitVec.ofNat 64 n) (n - m) ∗ stackAt sp m := by
  unfold stackAt
  exact memRegion_split' (b := sp - BitVec.ofNat 64 n) (b' := sp - BitVec.ofNat 64 m)
    (N := n) (n := n - m) (k := m) (by omega)
    (by
      have h : BitVec.ofNat 64 n = BitVec.ofNat 64 (n - m) + BitVec.ofNat 64 m := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel h1]
      rw [h]; bv_lin)
    (by omega)

theorem stackAt_rootStack_split_chainCloneStack (sp : BitVec 64) :
    stackAt sp rootStack = memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack)
      ∗ stackAt sp chainCloneStack :=
  stackAt_sub_split sp rootStack chainCloneStack (by decide) (by decide)

theorem stackAt_recvPrekeyInner_split (sp3 : BitVec 64) (k : Nat)
    (hk : k ≤ 0x100000 - 3280) : memRegion (sp3 - BitVec.ofNat 64 0x100000) (0x100000 - 3280) =
    memRegion (sp3 - BitVec.ofNat 64 0x100000) (0x100000 - 3280 - k) ∗ stackAt (sp3 - 0xcd0#64) k :=
    by
  have haddr : sp3 - BitVec.ofNat 64 0x100000 = (sp3 - 0xcd0#64) - BitVec.ofNat 64 (0x100000 - 3280)
      := by
    change sp3 - 1048576#64 = (sp3 - 0xcd0#64) - 1045296#64
    bv_omega
  have h1 : memRegion (sp3 - BitVec.ofNat 64 0x100000) (0x100000 - 3280) = stackAt (sp3 - 0xcd0#64)
      (0x100000 - 3280) := by
    unfold stackAt
    rw [haddr]
  have h2 := stackAt_sub_split (sp3 - 0xcd0#64) (0x100000 - 3280) k hk (by decide)
  rw [← haddr] at h2
  exact h1.trans h2

theorem stackAt_recvPrekeyInner_rebalance (sp3 : BitVec 64) (k1 k2 : Nat)
    (hk1 : k1 ≤ 0x100000 - 3280) (hk2 : k2 ≤ 0x100000 - 3280) : memRegion (sp3 - BitVec.ofNat 64
    0x100000) (0x100000 - 3280 - k1) ∗ stackAt (sp3 - 0xcd0#64) k1 = memRegion (sp3 - BitVec.ofNat
    64 0x100000) (0x100000 - 3280 - k2) ∗ stackAt (sp3 - 0xcd0#64) k2 := by
  rw [← stackAt_recvPrekeyInner_split sp3 k1 hk1, stackAt_recvPrekeyInner_split sp3 k2 hk2]

/-! ## 2. Unconditional No-Panic on `initializeRecipientSession` -/

private theorem rootCreateChain_ok_index {C : Crypto} {rk newRk : RootKey} {their : PublicKey}
    {our : PrivateKey} {recvCk : ChainKey} (h : rootCreateChain C rk their our = .ok (newRk,
    recvCk)) : recvCk.index = 0#32 := by
  unfold rootCreateChain at h
  split at h
  · cases h
  · injection h with hp
    injection hp with _ hck
    rw [← hck]
    rfl

private theorem storeSkippedKey_singleton_ok (their : PublicKey) (ck : Option ChainKey)
    (mks : List MessageKeyGenerator) (key : MessageKeyGenerator) (r : RatchetState) (hrc :
    r.receiverChains = [⟨their, ck, mks⟩]) : ∃ r1 mks1, Mut.exec (RatchetState.storeSkippedKey their
    key) r = (.ok (), r1) ∧ r1.receiverChains = [⟨their, ck, mks1⟩] ∧ r1.maxForwardJumps =
    r.maxForwardJumps := by
  have hfind : r.findReceiverChainIndex their = some 0 := by
    unfold RatchetState.findReceiverChainIndex
    rw [hrc]
    simp [List.findIdx?, List.findIdx?.go]
  have hget : r.receiverChains[0]? = some ⟨their, ck, mks⟩ := by
    rw [hrc]; rfl
  unfold RatchetState.storeSkippedKey
  rw [exec_bind, exec_get]
  dsimp only
  rw [hfind]
  dsimp only
  rw [hget]
  dsimp only
  refine ⟨_, if maxMessageKeys < (key :: mks).length then (key :: mks).dropLast else key :: mks,
    rfl, ?_, rfl⟩
  dsimp only
  rw [hrc]
  rfl

private theorem setReceiverChainKey_singleton_ok (their : PublicKey) (ck : Option ChainKey)
    (mks : List MessageKeyGenerator) (ck' : ChainKey) (r : RatchetState) (hrc : r.receiverChains =
    [⟨their, ck, mks⟩]) : ∃ r1, Mut.exec (RatchetState.setReceiverChainKey their ck') r = (.ok (),
    r1) := by
  have hfind : r.findReceiverChainIndex their = some 0 := by
    unfold RatchetState.findReceiverChainIndex
    rw [hrc]
    simp [List.findIdx?, List.findIdx?.go]
  have hget : r.receiverChains[0]? = some ⟨their, ck, mks⟩ := by
    rw [hrc]; rfl
  unfold RatchetState.setReceiverChainKey
  rw [exec_bind, exec_get]
  dsimp only
  rw [hfind]
  dsimp only
  rw [hget]
  dsimp only
  exact ⟨_, rfl⟩

private theorem nextChainKey_ok_of_le_25000 (F : ShaCompress) (ck : ChainKey)
    (hle : ck.index.toNat ≤ 25000) : ∃ ck', ck.nextChainKey F = .ok ck' ∧ ck'.index.toNat =
    ck.index.toNat + 1 := by
  have hne : ck.index ≠ BitVec.allOnes 32 := by
    intro h
    rw [h] at hle
    revert hle
    decide
  refine ⟨⟨bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed), ck.index + 1⟩, ?_, ?_⟩
  · simp only [ChainKey.nextChainKey, hne, ↓reduceIte]
  · change (ck.index + 1#32).toNat = ck.index.toNat + 1
    rw [BitVec.toNat_add_of_lt]
    · rfl
    · change ck.index.toNat + 1 < 4294967296
      omega

private theorem advanceChain_singleton_ok (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) (hcnt : counter.toNat ≤ 25000) (ck0 : Option ChainKey) : ∀ (fuel : Nat)
    (ck : ChainKey) (r : RatchetState) (mks : List MessageKeyGenerator), ck.index.toNat ≤
    counter.toNat → r.receiverChains = [⟨their, ck0, mks⟩] → ∃ ck1 r1 mks1, Mut.exec
    (RatchetState.advanceChain F their counter fuel ck) r = (.ok ck1, r1) ∧ ck1.index.toNat ≤ 25000
    ∧ r1.receiverChains = [⟨their, ck0, mks1⟩]
  | 0, ck, r, mks, hle, hrc =>
    ⟨ck, r, mks, rfl, Nat.le_trans hle hcnt, hrc⟩
  | fuel + 1, ck, r, mks, hle, hrc => by
    unfold RatchetState.advanceChain
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte]
      have hlt_nat : ck.index.toNat < counter.toNat := BitVec.lt_def.mp hlt
      obtain ⟨r1, mks1, hst, hrc1, _⟩ := storeSkippedKey_singleton_ok their ck0 mks (ck.messageKeys
        F) r hrc
      obtain ⟨ck', hnck, hidx'⟩ := nextChainKey_ok_of_le_25000 F ck (by omega)
      rw [exec_bind, hst]
      dsimp only
      rw [exec_bind, hnck, exec_liftE_ok]
      dsimp only
      exact advanceChain_singleton_ok F their counter hcnt ck0 fuel ck' r1 mks1 (by omega) hrc1
    · simp only [hlt, ↓reduceIte]
      exact ⟨ck, r, mks, rfl, Nat.le_trans hle hcnt, hrc⟩

/-- When `recvCk.index = 0#32`, `r.maxForwardJumps = 25000`, and
`r.receiverChains = [⟨their, some recvCk, []⟩]`, `consumeMessageKey` never returns `.error .panic`.
    -/
theorem consumeMessageKey_ne_panic_of_index_zero (F : ShaCompress) (their : PublicKey)
    (recvCk : ChainKey) (counter : BitVec 32) (msgType : MessageType) (r : RatchetState) (hidx :
    recvCk.index = 0#32) (hmfj : r.maxForwardJumps = 25000) (hrc : r.receiverChains = [⟨their, some
    recvCk, []⟩]) : (Mut.exec (RatchetState.consumeMessageKey F their recvCk counter msgType) r).1 ≠
    .error .panic := by
  unfold RatchetState.consumeMessageKey
  have hnlt : ¬ (counter < recvCk.index) := by
    rw [hidx]
    intro h
    exact Nat.not_lt_zero _ (BitVec.lt_def.mp h)
  simp only [hnlt, ↓reduceIte, exec_bind, exec_get]
  have hsub : (counter - recvCk.index).toNat = counter.toNat := by
    rw [hidx, BitVec.sub_zero]
  by_cases hgt : (counter - recvCk.index).toNat > r.maxForwardJumps
  · simp only [hgt, ↓reduceIte, exec_bind, exec_throw]
    nofun
  · simp only [hgt, ↓reduceIte]
    have hcnt : counter.toNat ≤ 25000 := by omega
    have hle0 : recvCk.index.toNat ≤ counter.toNat := by rw [hidx]; exact Nat.zero_le _
    obtain ⟨ck1, r1, mks1, hadv, hck1_le, hrc1⟩ := advanceChain_singleton_ok F their counter hcnt
      (some recvCk)
        (counter - recvCk.index).toNat recvCk r [] hle0 hrc
    rw [exec_bind, hadv]
    dsimp only
    obtain ⟨ck2, hnck2, _⟩ := nextChainKey_ok_of_le_25000 F ck1 hck1_le
    rw [exec_bind, hnck2, exec_liftE_ok]
    dsimp only
    obtain ⟨r2, hset⟩ := setReceiverChainKey_singleton_ok their (some recvCk) mks1 ck2 r1 hrc1
    rw [exec_bind, hset]
    dsimp only [exec_pure]; nofun

/-- On `r.receiverChains = []`, `ensureReceiverChain` either fails with `e ≠ .panic` or succeeds
with a fresh chain at `recvCk.index = 0#32` and `r1.receiverChains = [⟨their, some recvCk, []⟩]`. -/
theorem ensureReceiverChain_index_zero_or_err_ne_panic (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r : RatchetState) (hrc : r.receiverChains = []) : (∃ e r1, Mut.exec
    (RatchetState.ensureReceiverChain C their coins) r = (.error e, r1) ∧ e ≠ .panic) ∨ (∃ recvCk
    r1, Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.ok recvCk, r1) ∧
    recvCk.index = 0#32 ∧ r1.maxForwardJumps = r.maxForwardJumps ∧ r1.receiverChains = [⟨their, some
    recvCk, []⟩]) := by
  have hfind : r.findReceiverChainKey their = .ok none := by
    unfold RatchetState.findReceiverChainKey RatchetState.findReceiverChainIndex
    rw [hrc]
    rfl
  rw [ensureReceiverChain_of_find_none hfind]
  cases hsc : r.senderChain with
  | none =>
    left
    refine ⟨_, _, dhRatchetStep_of_senderChain_none hsc, by decide⟩
  | some sc =>
    cases hcc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
    | error e1 =>
      left
      refine ⟨e1, _, dhRatchetStep_of_first_createChain_error hsc hcc1, ?_⟩
      rw [rootCreateChain_error_eq hcc1]; decide
    | ok p1 =>
      rcases p1 with ⟨newRk, recvCk⟩
      cases hcc2 : rootCreateChain C newRk their (KeyPair.generate C coins).privateKey with
      | error e2 =>
        left
        refine ⟨e2, _, dhRatchetStep_of_second_createChain_error hsc hcc1 hcc2, ?_⟩
        rw [rootCreateChain_error_eq hcc2]; decide
      | ok p2 =>
        rcases p2 with ⟨finalRk, sendCk⟩
        right
        refine ⟨recvCk, _, dhRatchetStep_of_both_createChain_ok hsc hcc1 hcc2,
          rootCreateChain_ok_index hcc1, rfl, ?_⟩
        dsimp only
        rw [hrc, List.nil_append]
        rfl

private theorem tryDecryptWithState_unfold {PQC : Type}
    (C : Crypto) (spqr : Spqr (List (BitVec 8)) PQC) (expected : Option (List (BitVec 8))) (msg :
    SignalMessage) (msgType : MessageType) (coins : BitVec 256) (st : SessionState (List (BitVec
    8))) : Mut.exec (SessionState.tryDecryptWithState C spqr expected msg msgType coins) st =
      match Mut.exec TripleRatchet.fromSessionState st with
      | (.error e, st1) => (.error e, st1)
      | (.ok tr, st1) =>
        match Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType coins) tr with
        | (.error e, _) => (.error e, st1)
        | (.ok pt, tr') =>
          (.ok pt, (tr'.applyToSessionState st1).clearUnacknowledgedPreKeyMessage) := by
  unfold SessionState.tryDecryptWithState
  rw [exec_bind]
  cases Mut.exec TripleRatchet.fromSessionState st with
  | mk res st1 =>
    cases res with
    | error e => rfl
    | ok tr =>
      dsimp only
      cases Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType coins) tr with
      | mk r tr' =>
        cases r with
        | error e =>
          rw [exec_bind, exec_liftE_error]
        | ok pt =>
          rw [exec_bind, exec_liftE_ok]
          dsimp only
          rw [exec_bind, exec_modify]
          rfl

/-- For ANY `st` with `st.receiverChains = []` on which `spqr::recv` does not panic,
`SessionState.tryDecryptWithState` never panics. -/
theorem tryDecryptWithState_ne_panic_of_receiverChains_nil { PQC : Type }
    (C : Crypto) (spqr : Spqr (List (BitVec 8)) PQC) (expected : Option (List (BitVec 8))) (msg :
    SignalMessage) (msgType : MessageType) (coins : BitVec 256) (st : SessionState (List (BitVec
    8))) (hrc : st.receiverChains = [])
    (hnp : ¬ spqr.recvPanics st.pqRatchetState msg.pqRatchet) : (Mut.exec
    (SessionState.tryDecryptWithState C spqr expected msg msgType coins) st).1 ≠ .error .panic := by
  rw [tryDecryptWithState_unfold]
  cases htr : Mut.exec TripleRatchet.fromSessionState st with
  | mk res st1 =>
    cases res with
    | error e =>
      have ⟨_, he, _⟩ := fromSessionState_error_inv htr
      subst he; nofun
    | ok tr =>
      dsimp only
      have ⟨_, hrat, hpq, _, _⟩ := fromSessionState_ok_inv htr
      have hrc_tr : tr.ratchet.receiverChains = [] := by rw [hrat, hrc]
      have hmfj_tr : tr.ratchet.maxForwardJumps = 25000 := by rw [hrat]; rfl
      have hnp_tr : spqr.recvPanics tr.pqrState msg.pqRatchet = false := by
        rw [hpq]; simpa using hnp
      have hdec_npan : (Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType coins) tr).1 ≠
        .error .panic := by
        unfold TripleRatchet.decrypt
        rw [exec_bind, onRatchet_eq]
        rcases ensureReceiverChain_index_zero_or_err_ne_panic C msg.senderRatchetKey coins
          tr.ratchet hrc_tr with
          ⟨e, r1, herc, hne⟩ | ⟨ck, r1, herc, hidx, hmfj1, hrc1⟩
        · rw [herc]
          exact fun h => hne (Except.error.inj h)
        · rw [herc]
          dsimp only
          rw [exec_bind, onRatchet_eq]
          dsimp only
          have hcmk_npan := consumeMessageKey_ne_panic_of_index_zero C.F msg.senderRatchetKey ck
            msg.counter msgType r1 hidx (hmfj1.trans hmfj_tr) hrc1
          rcases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck
              msg.counter msgType) r1 with ⟨cmkRes, r2⟩
          rw [hcmk] at hcmk_npan
          dsimp only at hcmk_npan ⊢
          cases cmkRes with
          | error e =>
            dsimp only
            exact fun h => hcmk_npan (congrArg Except.error (Except.error.inj h))
          | ok mkg =>
            dsimp only
            rw [exec_bind, exec_get]
            dsimp only
            simp only [hnp_tr, Bool.false_eq_true, ↓reduceIte]
            cases hspqr : spqr.recv tr.pqrState msg.pqRatchet with
            | error sd =>
              cases sd <;> (dsimp only; rw [exec_bind, exec_throw]; nofun)
            | ok p =>
              rcases p with ⟨newPqrState, pqrKey⟩
              rw [exec_bind, exec_pure]
              dsimp only
              cases hmac : msg.verifyMacWithAddresses C.F expected tr.remoteIdentityKey
                  tr.localIdentityKey (mkg.generateKeys C.F pqrKey).macKey
              · simp only [Bool.not_false, ↓reduceIte, exec_bind, exec_throw]
                nofun
              · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                cases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
                    (mkg.generateKeys C.F pqrKey).iv msg.ciphertext
                · dsimp only
                  rw [exec_throw]; nofun
                · dsimp only
                  rw [exec_bind, exec_modify]; nofun
      cases hdec : Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType coins) tr with
      | mk r tr' =>
        rw [hdec] at hdec_npan
        cases r with
        | error e => exact hdec_npan
        | ok pt => nofun

/-- `pqxdhTryDecryptModel` never panics when `st.receiverChains = []` and `spqr::recv` does not
panic on `st`. -/
theorem pqxdhTryDecryptModel_ne_panic_of_receiverChains_nil (C : Crypto) (S : SpqrModel)
    (parse : UuidParser) (rem loc : AddrGhost) (msg : SignalMessage) (rest : List (BitVec 8)) (st :
    SessionState (List (BitVec 8))) (hrc : st.receiverChains = [])
    (hnp : ¬ S.recvPanics st.pqRatchetState msg.pqRatchet) : (pqxdhTryDecryptModel C S parse
    rem loc msg rest st).1 ≠ .error .panic :=
  tryDecryptWithState_ne_panic_of_receiverChains_nil C S.spqr
    (serializeAddresses (serviceIdParse parse) rem loc) msg .preKey (coinsOf rest) st hrc hnp

/-- `pqxdhTryDecryptModel` never panics on `initializeRecipientSession` (`hnpan1`) when
`spqr::recv` does not panic there (`hnp`; for `HooksE.spqrModelE` use
`spqrModelE_recvPanics_initSession_not`). -/
theorem pqxdhTryDecryptModel_initSession_ne_panic (C : Crypto) (S : SpqrModel)
    (parse : UuidParser) (rem loc : AddrGhost) (msg : SignalMessage) (rest : List (BitVec 8))
    (ourIdentity theirIdentity : IdentityKey) (sendingKeyPair : KeyPair) (rootKey chainKey pqrKey :
    BitVec 256)
    (hnp : ¬ S.recvPanics (initializeRecipientSession spqrOffB ourIdentity theirIdentity
      sendingKeyPair rootKey chainKey pqrKey).pqRatchetState msg.pqRatchet) :
    (pqxdhTryDecryptModel C S parse rem loc msg rest
      (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair
        rootKey chainKey pqrKey)).1 ≠ .error .panic :=
  pqxdhTryDecryptModel_ne_panic_of_receiverChains_nil C S parse rem loc msg rest _ rfl hnp

/-- `HooksE.spqrModelE.recvPanics` is unconditionally `false` (`hnpan2`). -/
theorem spqrModelE_recvPanics_initSession_not
    (ourIdentity theirIdentity : IdentityKey) (sendingKeyPair : KeyPair) (rootKey chainKey pqrKey :
    BitVec 256) (pqMsg : List (BitVec 8)) : ¬ HooksE.spqrModelE.recvPanics
      (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair
        rootKey chainKey pqrKey).pqRatchetState pqMsg :=
  Bool.false_ne_true

/-! ## 3. Model Equivalence (`pqxdhTryDecryptModel` = `tryDecryptFromRecord`) and `CanonSession` -/

/-- Under `gMe.val = (Role.ofParty P).addrVal`, `gPeer.val = (Role.ofParty P).peer.addrVal`, and
`rest = HMAC.keyToBytes32 rc`, `pqxdhTryDecryptModel` equals `Mut.exec
    (SessionState.tryDecryptWithState ...)`. -/
private theorem tryDecryptWithState_spqrModelE_eq_spqrOffB
    (C : Crypto) (expected : Option Bytes) (msg : SignalMessage) (msgType : MessageType) (coins :
    BitVec 256) : SessionState.tryDecryptWithState C HooksE.spqrModelE.spqr expected msg msgType
    coins = SessionState.tryDecryptWithState C spqrOffB expected msg msgType coins :=
  rfl

theorem pqxdhTryDecryptModel_eq_tryDecryptWithState_expectedAddrs
    (W : PEParams) (P : Party) (gMe gPeer : AddrGhost) (msg : SignalMessage) (rc : BitVec 256) (st :
    SessionState Bytes) (hgMe : gMe.val = (Role.ofParty P).addrVal) (hgPeer : gPeer.val =
    (Role.ofParty P).peer.addrVal) : pqxdhTryDecryptModel W.C HooksE.spqrModelE uuidTryParse gPeer
    gMe msg
      (HMAC.keyToBytes32 rc) st = Mut.exec (SessionState.tryDecryptWithState W.C spqrOffB
      ((spqrOffSessionParams W.C).expectedAddrs P) msg .preKey rc) st := by
  unfold pqxdhTryDecryptModel
  have hcoins : coinsOf (HMAC.keyToBytes32 rc) = rc := Run.coinsOf_keyToBytes32 rc
  have haddr : serializeAddresses (serviceIdParse uuidTryParse) gPeer gMe =
      (spqrOffSessionParams W.C).expectedAddrs P := by
    change serializeAddrVal gPeer.val gMe.val = (spqrOffSessionParams W.C).expectedAddrs P
    rw [hgPeer, hgMe]
    cases P <;> rfl
  rw [hcoins, haddr, tryDecryptWithState_spqrModelE_eq_spqrOffB]

/-- For `st0 = initializeRecipientSession ...`, `st0.version = 4#32`. -/
@[simp]
theorem initSession_version_eq (ourIdentity theirIdentity : IdentityKey) (sendingKeyPair : KeyPair)
    (rootKey chainKey pqrKey : BitVec 256) : (initializeRecipientSession spqrOffB ourIdentity
    theirIdentity sendingKeyPair
      rootKey chainKey pqrKey).version = 4#32 :=
  rfl

/-- When `msg.messageVersion.zeroExtend 32 ≠ 4#32`, `SessionState.tryDecryptFromRecord` on
`initializeRecipientSession` returns `(.error (.invalidMessage .preKey .decryptionFailed), st0)`. -/
theorem tryDecryptFromRecord_initSession_of_msgVer_ne_4
    (C : Crypto) (expected : Option Bytes) (msg : SignalMessage) (rc : BitVec 256) (ourIdentity
    theirIdentity : IdentityKey) (sendingKeyPair : KeyPair) (rootKey chainKey pqrKey : BitVec 256)
    (hver : msg.messageVersion.zeroExtend 32 ≠ 4#32) :
    let st0 := initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair
      rootKey chainKey pqrKey
    SessionState.tryDecryptFromRecord C spqrOffB expected msg .preKey rc st0 = (.error
      (.invalidMessage .preKey .decryptionFailed), st0) := by
  intro st0
  have hver_nat : st0.version.toNat ≠ msg.messageVersion.toNat := by
    intro h
    apply hver
    apply BitVec.eq_of_toNat_eq
    have hv : st0.version.toNat = 4 := by
      change (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair
        rootKey chainKey pqrKey).version.toNat = 4
      rw [initSession_version_eq]
      rfl
    have hlt : msg.messageVersion.toNat < 256 := msg.messageVersion.isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  unfold SessionState.tryDecryptFromRecord
  simp [hver_nat]

/-- When `msg.messageVersion.zeroExtend 32 = 4#32`, `SessionState.tryDecryptFromRecord` on
`initializeRecipientSession` dispatches on `Mut.exec (SessionState.tryDecryptWithState ...)`. -/
theorem tryDecryptFromRecord_initSession_of_msgVer_eq_4
    (C : Crypto) (expected : Option Bytes) (msg : SignalMessage) (rc : BitVec 256) (ourIdentity
    theirIdentity : IdentityKey) (sendingKeyPair : KeyPair) (rootKey chainKey pqrKey : BitVec 256)
    (hver : msg.messageVersion.zeroExtend 32 = 4#32) :
    let st0 := initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair
      rootKey chainKey pqrKey
    SessionState.tryDecryptFromRecord C spqrOffB expected msg .preKey rc st0 =
      match Mut.exec (SessionState.tryDecryptWithState C spqrOffB expected msg .preKey rc) st0 with
      | (.ok pt, st') => (.ok pt, st')
      | (.error e, _) => (.error (SessionState.recordError .preKey e), st0) := by
  intro st0
  have hver_nat : st0.version.toNat = msg.messageVersion.toNat := by
    have h := congrArg BitVec.toNat hver
    have hv : st0.version.toNat = 4 := by
      change (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair
        rootKey chainKey pqrKey).version.toNat = 4
      rw [initSession_version_eq]
      rfl
    have hlt : msg.messageVersion.toNat < 256 := msg.messageVersion.isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h
    omega
  unfold SessionState.tryDecryptFromRecord
  simp only [hver_nat, ne_eq, not_true_eq_false, ↓reduceIte]
  cases Mut.exec (SessionState.tryDecryptWithState C spqrOffB expected msg .preKey rc) st0 with
  | mk res st' =>
    cases res <;> rfl

/-- When `e ≠ .panic`, `SessionState.recordError .preKey e ≠ .panic`. -/
theorem recordError_preKey_ne_panic {e : SignalProtocolError} (hne : e ≠ .panic) :
    SessionState.recordError .preKey e ≠ .panic := by
  cases e <;> first | exact absurd rfl hne | nofun

/-- When `(pqxdhTryDecryptModel ...).1 = .ok pt`, the updated `SessionState` has
`pendingPreKey = false`. -/
theorem pqxdhTryDecryptModel_ok_pendingPreKey_false
    (C : Crypto) (S : SpqrModel) (parse : UuidParser) (rem loc : AddrGhost) (msg : SignalMessage)
    (rest : List (BitVec 8)) (st : SessionState Bytes) (pt : Bytes) (hok : (pqxdhTryDecryptModel C S
    parse rem loc msg rest st).1 = .ok pt) : (pqxdhTryDecryptModel C S parse rem loc msg rest
    st).2.pendingPreKey = false := by
  unfold pqxdhTryDecryptModel at hok ⊢
  rw [tryDecryptWithState_unfold] at hok ⊢
  cases htr : Mut.exec TripleRatchet.fromSessionState st with
  | mk res st1 =>
    rw [htr] at hok
    cases res with
    | error e => cases hok
    | ok tr =>
      dsimp only at hok ⊢
      cases hdec : Mut.exec (TripleRatchet.decrypt C S.spqr
          (serializeAddresses (serviceIdParse parse) rem loc) msg .preKey (coinsOf rest)) tr with
      | mk r tr' =>
        rw [hdec] at hok
        cases r with
        | error e => cases hok
        | ok pt' => rfl

private theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  unfold leBytes unpack32 BitVec.extractLsb'
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map, Nat.shiftRight_eq_div_pow]
  rfl

/-- Upgrades `sessionStateAt A p G' st'` from `stageP3_initSession_ok`'s `hOk` branch to
`⌜Record.Serialization.CanonSession G' s⌝ ∗ sessionStateReprAt A p G' s` for
`s = RecordX.sessionOfX (fun _ => responderRecordExtras me m) ⟨P, st', 1, [1]⟩`. -/
theorem sessionStateAt_entails_canonSession_and_sessionAt_recvPrekey
    (A : RustAlloc) (p : BitVec 64) (P : Party) (me : LocalIdentity) (m : PreKeyMessageFields) (newLocIdPtr newRemIdPtr
    newRootKeyPtr newAliceBasePtr : BitVec 64) (locIdBytes remIdBytes : List (BitVec 8)) (sg' :
    SenderChainGhost) (G' : SessionGhost) (st' : SessionState Bytes) (hpend_false :
    st'.pendingPreKey = false) (hdecRel : (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr
    newAliceBasePtr
      locIdBytes remIdBytes (bytesToBv8 (Model.encodeEC (vecU8 m.baseKey))) sg' m.regId
      me.regId).AfterTryDecrypt true G') :
    let s := RecordX.sessionOfX (fun _ => responderRecordExtras me m) ⟨P, st', 1, [1]⟩
    sessionStateAt A p G'
      st' ⊢ ⌜Record.Serialization.CanonSession G' s⌝ ∗ sessionStateReprAt A p G' s := by
  intro s
  rcases hdecRel with ⟨⟨_, _, halice, hreg⟩, hG_pend, hG_kyb⟩
  have hs_pend : s.pendingPreKey = none := by
    simp [s, RecordX.sessionOfX, hpend_false]
  have hs_kyb : s.pendingKyberPreKey = none := by
    simp [s, RecordX.sessionOfX, hpend_false]
  have halice_eq : G'.alice.bytes = s.aliceBaseKey := by
    rw [halice]
    change bytesToBv8 (Model.encodeEC (vecU8 m.baseKey)) = djbKey m.baseKey
    rw [bytesToBv8_encodeEC_vecU8]
    rfl
  have hlen_rem : (unpack32 m.regId).length = 4 := by
    simp [unpack32]
  have hlen_loc : (unpack32 me.regId).length = 4 := by
    simp [unpack32]
  have hreg_rem : G'.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat := by
    rw [hreg]
    change (unpack32 m.regId ++ unpack32 me.regId).take 4 = leBytes 4 m.regId.toNat
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    exact (leBytes_four_eq_unpack32 m.regId).symm
  have hreg_loc : (G'.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat := by
    rw [hreg]
    change ((unpack32 m.regId ++ unpack32 me.regId).drop 4).take 4 = leBytes 4 me.regId.toNat
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), hlen_rem, Nat.sub_self, List.drop_zero,
        List.nil_append, List.take_of_length_le (by omega)]
    exact (leBytes_four_eq_unpack32 me.regId).symm
  have h1 : sessionStateAt A p G' st' ⊢ sessionStateReprAt A p G' s := by
    refine sessionStateAt_entails_sessionAt A p G' s ⟨?_, ?_, halice_eq, hreg_rem, hreg_loc⟩
    · rw [hG_pend, hs_pend]; trivial
    · rw [hG_kyb, hs_kyb]; trivial
  exact Entails.trans h1 (Record.DeserializeGeneral.sessionAt_canon A p G' s)

/-- Any `recordResultAt A outPtr (.error (SessionState.recordError .preKey e))` with `e ≠ .panic`
entails a non-`0xfffffffffffffffe` / non-`0xfffffffffffffffd` error tag at `outPtr`. -/
theorem recordResultAt_recordError_entails_tag (A : RustAlloc) (outPtr : BitVec 64)
    (e : SignalProtocolError) (hne : e ≠ .panic) : recordResultAt A outPtr (.error
    (SessionState.recordError .preKey e)) ⊢ ∃∗ tag : BitVec 64, ⌜tag ≠ 0xfffffffffffffffe#64 ∧ tag ≠
    0xfffffffffffffffd#64⌝ ∗ (outPtr ↦₆₄ tag) ∗ anyHeap := by
  have hrec : (∃ i c, SessionState.recordError .preKey e = .duplicatedMessage i c) ∨
      SessionState.recordError .preKey e = .invalidMessage .preKey .decryptionFailed := by
    cases e with
    | panic => exact absurd rfl hne
    | duplicatedMessage i c => exact Or.inl ⟨i, c, rfl⟩
    | _ => exact Or.inr rfl
  rcases hrec with ⟨i, c, hdup⟩ | hdec
  · rw [hdup]
    dsimp only [recordResultAt, vecResultAt, speAt]
    refine Entails.sepExists_right (speWord 23) ?_
    refine Entails.pure_right (by decide) ?_
    exact sepConj_mono_right (entails_anyHeap _)
  · rw [hdec]
    dsimp only [recordResultAt]
    refine Entails.sepExists_right (speWord 24) ?_
    refine Entails.pure_right (by decide) ?_
    exact sepConj_mono_right (entails_anyHeap _)

end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
