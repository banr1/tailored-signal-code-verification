/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
public import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj
public import Symbolic.Proofs.Refinement.RecordBytesBridge
public import Symbolic.Proofs.Swarm.CREF.TR.PureCanon
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.SendWire.Ghosts -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.Proofs.Swarm.TRREF.B3DefsPure -- shake: keep

/-!
# Send-Wire Coin Roundtrips and Pending-Record Encoding

Proves 32-byte key and 16-byte block roundtrips, re-exports send-wire ghost
helpers, and relates `recordBytes (sessionToRecordRecPending s)` to `encodeRecord`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
open DY.Libsignal.Refinement (PbValue encodeField)
open DY.Libsignal.TripleRatchet
open CryptoVerification
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet

abbrev SpqrSem := OpaqueSymbolSemantics
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Record (encSession encSenderChain encReceiverChain encChainKey
  encPendingPreKey encPendingKyber)
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR

/-! ## Byte and block roundtrips -/

private theorem extractLsb'_zero_shift8_or_c {n : Nat} (hn : 8 ≤ n) (b : BitVec 8) (acc : BitVec n) :
    ((acc <<< 8) ||| b.zeroExtend n).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hin : i < n := by omega
  simp [hi, hin]

private theorem extractLsb'_succ_shift8_or_c {w : Nat} (b : BitVec 8) (acc : BitVec (8 * w))
    (j : Nat) (hj : j + 1 < w) :
    ((acc <<< 8) ||| b.zeroExtend (8 * w)).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 8 * w := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have h4 : 8 * j + i < 8 * w := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [hi, h1, h2, h3, h4, hb]

private theorem extractLsb'_bytesToKey32_c (bs : List (BitVec 8)) (j : Nat)
    (hj : j < bs.length) (h32 : j < 32) :
    (CryptoGames.HKDF.bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero => simpa [CryptoGames.HKDF.bytesToKey32] using extractLsb'_zero_shift8_or_c (by decide) b _
    | succ j =>
      change (((CryptoGames.HKDF.bytesToKey32 rest : BitVec (8 * 32)) <<< 8) ||| b.zeroExtend (8 * 32)).extractLsb' (8 * (j + 1)) 8 = _
      rw [extractLsb'_succ_shift8_or_c b _ j h32, List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem keyToBytes32_bytesToKey32_c (bs : List (BitVec 8)) (h : bs.length = 32) :
    CryptoGames.HMAC.keyToBytes32 (CryptoGames.HKDF.bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [CryptoGames.HMAC.keyToBytes32, h]) fun j _ h2 => ?_
  simp only [CryptoGames.HMAC.keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32_c bs j h2 (by omega)

private theorem extractLsb'_bytesToBlock_c (bs : List (BitVec 8)) (j : Nat)
    (hj : j < bs.length) (h16 : j < 16) :
    (CryptoGames.CBC.bytesToBlock bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero => simpa [CryptoGames.CBC.bytesToBlock] using extractLsb'_zero_shift8_or_c (by decide) b _
    | succ j =>
      change (((CryptoGames.CBC.bytesToBlock rest : BitVec (8 * 16)) <<< 8) ||| b.zeroExtend (8 * 16)).extractLsb' (8 * (j + 1)) 8 = _
      rw [extractLsb'_succ_shift8_or_c b _ j h16, List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem blockToBytesLE_bytesToBlock_c (bs : List (BitVec 8)) (h : bs.length = 16) :
    CryptoGames.CBC.blockToBytesLE (CryptoGames.CBC.bytesToBlock bs) = bs := by
  refine List.ext_getElem (by simp [CryptoGames.CBC.blockToBytesLE, h]) fun j _ h2 => ?_
  simp only [CryptoGames.CBC.blockToBytesLE, List.getElem_ofFn]
  exact extractLsb'_bytesToBlock_c bs j h2 (by omega)

export Symbolic.Swarm.CREF.SendWire
  (encWire encMac encMsg encSt isFreshSendWire updateFreshAt clearSendAddr sendGhost
   isFreshSendWire_encWire sendGhost_addr_encWire gamma_sendGhost_pt gamma_sendGhost_coins)

/-! ## Record byte encoding for `sessionToRecordRecPending` -/

open Swarm.Phase0WholeFunctionBridge

def sessionToRecordRecPending (s : Session (List (BitVec 8))) : RecordRec :=
  { current :=
      { (Swarm.Phase0WholeFunctionBridge.sessionToSessionRec s) with
        pendingPreKey := s.pendingPreKey.map fun p => (CryptoVerification.E2E.Record.encPendingPreKey p, []),
        pendingKyberPreKey := s.pendingKyberPreKey.map fun p => (CryptoVerification.E2E.Record.encPendingKyber p, []) },
    previous := [] }

private def pbFields_c (l : List (Nat × PbValue)) : HwBytes :=
  l.flatMap (fun p => encodeField p.1 0 0 p.2)

private theorem pbFields_append_c (l₁ l₂ : List (Nat × PbValue)) :
    pbFields_c (l₁ ++ l₂) = pbFields_c l₁ ++ pbFields_c l₂ := by
  simp only [pbFields_c, List.flatMap_append]

private def bytesFieldList_c (tag : Nat) (b : HwBytes) : List (Nat × PbValue) :=
  if b = [] then [] else [(tag, .bytes b)]

private def u32FieldList_c (tag : Nat) (v : BitVec 32) : List (Nat × PbValue) :=
  if v = 0 then [] else [(tag, .varint v.toNat)]

private theorem pbFields_bytesFieldList_c (tag : Nat) (b : HwBytes) :
    pbFields_c (bytesFieldList_c tag b) = bytesField tag b := by
  unfold bytesFieldList_c bytesField; split <;> simp [pbFields_c]

private theorem pbFields_u32FieldList_c (tag : Nat) (v : BitVec 32) :
    pbFields_c (u32FieldList_c tag v) = u32Field tag v := by
  unfold u32FieldList_c u32Field; split <;> simp [pbFields_c]

private theorem pbFields_map_msgField7_c (l : List ChainRec) :
    pbFields_c (l.map fun c => (7, PbValue.bytes (chainBytes c))) =
    l.flatMap (msgField 7 ∘ chainBytes) := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, pbFields_c, List.flatMap_cons, msgField, Function.comp_apply]
    congr 1

private def encSessionFields_c (s : Session (List (BitVec 8))) : List (Nat × PbValue) :=
  let st := s.state
  u32FieldList_c 1 st.sessionVersion ++
  bytesFieldList_c 2 st.localIdentity.serialize ++
  bytesFieldList_c 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++
  bytesFieldList_c 4 (HMAC.keyToBytes32 st.rootKey) ++
  u32FieldList_c 5 st.previousCounter ++
  ((st.senderChain.map (fun c => [(6, PbValue.bytes (chainBytes (Swarm.Phase0WholeFunctionBridge.senderChainToChainRec c)))])).getD []) ++
  (st.receiverChains.map Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec).map (fun c => (7, PbValue.bytes (chainBytes c))) ++
  ((s.pendingPreKey.map (fun p => [(9, PbValue.bytes (encPendingPreKey p))])).getD []) ++
  u32FieldList_c 10 s.remoteRegistrationId ++
  u32FieldList_c 11 s.localRegistrationId ++
  bytesFieldList_c 13 s.aliceBaseKey ++
  ((s.pendingKyberPreKey.map (fun p => [(14, PbValue.bytes (encPendingKyber p))])).getD []) ++
  bytesFieldList_c 15 st.pqRatchetState

private theorem encPendingPreKey_length_le_encSession_c (s : Session (List (BitVec 8)))
    (p : PendingPreKey) (hp : s.pendingPreKey = some p) :
    (CryptoVerification.E2E.Record.encPendingPreKey p).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  unfold CryptoVerification.E2E.Record.encSession; rw [hp]
  dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField,
    CryptoVerification.E2E.Record.lenField]; simp only [List.length_append]; omega

private theorem encPendingKyber_length_le_encSession_c (s : Session (List (BitVec 8)))
    (p : PendingKyberPreKey) (hp : s.pendingKyberPreKey = some p) :
    (CryptoVerification.E2E.Record.encPendingKyber p).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  unfold CryptoVerification.E2E.Record.encSession; rw [hp]
  dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField,
    CryptoVerification.E2E.Record.lenField]; simp only [List.length_append]; omega

private theorem pbFields_singleton_bytes_c (tag : Nat) (b : HwBytes) :
    pbFields_c [(tag, PbValue.bytes b)] = msgField tag b := by
  simp [pbFields_c, msgField]

private theorem flatten_map_lenField_length_ge_c (l : List ReceiverChain) (rc : ReceiverChain) (hrc : rc ∈ l) :
    (CryptoVerification.E2E.Record.encReceiverChain rc).length ≤
      ((l.map fun c => CryptoVerification.E2E.Record.lenField 7 (CryptoVerification.E2E.Record.encReceiverChain c)).flatten).length := by
  induction l with
  | nil => cases hrc
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hrc with rfl | hmem
    · unfold CryptoVerification.E2E.Record.lenField; simp only [List.length_append]; omega
    · have := ih hmem; omega

private theorem pbFields_encSessionFields_c (s : Session (List (BitVec 8)))
    (halice : s.aliceBaseKey.length < 2 ^ 64) (hpq : s.state.pqRatchetState.length < 2 ^ 64)
    (hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63)
    (hsess_len : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 64) :
    pbFields_c (encSessionFields_c s) = CryptoVerification.E2E.Record.encSession s := by
  have hcb : ∀ c, chainBytes c = DY.Libsignal.TripleRatchet.Refinement.chainBytes c := fun _ => rfl
  have hloc_len : s.state.localIdentity.serialize.length = 33 := by simp [IdentityKey.serialize, PublicKey.serialize]
  have hrem_len : ((s.state.remoteIdentity.map IdentityKey.serialize).getD []).length < 2 ^ 64 := by
    cases s.state.remoteIdentity <;> simp [IdentityKey.serialize, PublicKey.serialize]
  have hrk_len : (HMAC.keyToBytes32 s.state.rootKey).length = 32 := by simp [HMAC.keyToBytes32]
  have hsc_eq :
      pbFields_c ((s.state.senderChain.map
        (fun c => [(6, PbValue.bytes (chainBytes (Swarm.Phase0WholeFunctionBridge.senderChainToChainRec c)))])).getD []) =
      CryptoVerification.E2E.Record.msgField 6 (s.state.senderChain.map CryptoVerification.E2E.Record.encSenderChain) := by
    cases s.state.senderChain with
    | none => rfl
    | some sc =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField,
        Swarm.Phase0WholeFunctionBridge.senderChainToChainRec]
      rw [pbFields_singleton_bytes_c, hcb, Swarm.Phase0WholeFunctionBridge.chainBytes_sender_eq_encSenderChain sc]
      have hsc_len : (CryptoVerification.E2E.Record.encSenderChain sc).length < 2 ^ 64 := by
        unfold CryptoVerification.E2E.Record.encSenderChain; dsimp [CryptoVerification.E2E.Record.msgField]
        have h1 := Swarm.Phase0WholeFunctionBridge.record_bytesField_length_le 1 sc.ratchetKey.publicKey.serialize
        have h2 := Swarm.Phase0WholeFunctionBridge.record_bytesField_length_le 2 sc.ratchetKey.privateKey.bytes.toList
        have h3 := Swarm.Phase0WholeFunctionBridge.lenField_length_le 3 (CryptoVerification.E2E.Record.encChainKey sc.chainKey)
        have h4 := Swarm.Phase0WholeFunctionBridge.encChainKey_length_lt sc.chainKey
        have hpub : sc.ratchetKey.publicKey.serialize.length = 33 := by simp [PublicKey.serialize]
        have hpriv : sc.ratchetKey.privateKey.bytes.toList.length = 32 := List.Vector.toList_length _
        simp only [List.length_append]; omega
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 6 _ hsc_len
  have hrc_eq :
      pbFields_c ((s.state.receiverChains.map Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec).map
        (fun c => (7, PbValue.bytes (chainBytes c)))) =
      (s.state.receiverChains.map fun c =>
        CryptoVerification.E2E.Record.lenField 7 (CryptoVerification.E2E.Record.encReceiverChain c)).flatten := by
    rw [pbFields_map_msgField7_c, List.flatMap_map, List.flatMap_def]; congr 1
    apply List.map_congr_left; intro rc hrc; dsimp only [Function.comp_apply]
    have hrc_len : (CryptoVerification.E2E.Record.encReceiverChain rc).length < 2 ^ 64 := by
      have h1 := flatten_map_lenField_length_ge_c s.state.receiverChains rc hrc
      unfold CryptoVerification.E2E.Record.encSession at hsess_len
      simp only [List.length_append] at hsess_len; omega
    rw [hcb, Swarm.Phase0WholeFunctionBridge.chainBytes_receiver_eq_encReceiverChain rc (hseeds rc hrc)]
    exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 7 _ hrc_len
  have hppk_eq :
      pbFields_c ((s.pendingPreKey.map
        (fun p => [(9, PbValue.bytes (CryptoVerification.E2E.Record.encPendingPreKey p))])).getD []) =
      CryptoVerification.E2E.Record.msgField 9 (s.pendingPreKey.map CryptoVerification.E2E.Record.encPendingPreKey) := by
    cases hppk : s.pendingPreKey with
    | none => rfl
    | some p =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField]
      rw [pbFields_singleton_bytes_c]
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 9 _
        (lt_of_le_of_lt (encPendingPreKey_length_le_encSession_c s p hppk) hsess_len)
  have hpkp_eq :
      pbFields_c ((s.pendingKyberPreKey.map
        (fun p => [(14, PbValue.bytes (CryptoVerification.E2E.Record.encPendingKyber p))])).getD []) =
      CryptoVerification.E2E.Record.msgField 14 (s.pendingKyberPreKey.map CryptoVerification.E2E.Record.encPendingKyber) := by
    cases hpkp : s.pendingKyberPreKey with
    | none => rfl
    | some p =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField]
      rw [pbFields_singleton_bytes_c]
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 14 _
        (lt_of_le_of_lt (encPendingKyber_length_le_encSession_c s p hpkp) hsess_len)
  unfold encSessionFields_c CryptoVerification.E2E.Record.encSession; dsimp only
  repeat rw [pbFields_append_c]
  rw [hsc_eq, hrc_eq, hppk_eq, hpkp_eq]
  repeat rw [pbFields_u32FieldList_c]
  repeat rw [pbFields_bytesFieldList_c]
  change DY.Libsignal.TripleRatchet.Refinement.u32Field 1 s.state.sessionVersion ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 2 s.state.localIdentity.serialize ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 3 ((Option.map IdentityKey.serialize s.state.remoteIdentity).getD []) ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 4 (HMAC.keyToBytes32 s.state.rootKey) ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 5 s.state.previousCounter ++
      CryptoVerification.E2E.Record.msgField 6 (Option.map encSenderChain s.state.senderChain) ++
      (List.map (fun c => CryptoVerification.E2E.Record.lenField 7 (encReceiverChain c)) s.state.receiverChains).flatten ++
      CryptoVerification.E2E.Record.msgField 9 (Option.map encPendingPreKey s.pendingPreKey) ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 10 s.remoteRegistrationId ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 11 s.localRegistrationId ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 13 s.aliceBaseKey ++
      CryptoVerification.E2E.Record.msgField 14 (Option.map encPendingKyber s.pendingKyberPreKey) ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 15 s.state.pqRatchetState = _
  rw [Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 1,
      Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 2 _ (by omega),
      Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 3 _ hrem_len,
      Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 4 _ (by omega),
      Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 5,
      Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 10,
      Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 11,
      Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 13 _ halice,
      Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 15 _ hpq]

private theorem pbFields_encSessionFields_eq_sessionToRecordRecPending_c (s : Session (List (BitVec 8))) :
    msgField 1 (pbFields_c (encSessionFields_c s)) = recordBytes (sessionToRecordRecPending s) := by
  unfold encSessionFields_c recordBytes sessionToRecordRecPending Swarm.Phase0WholeFunctionBridge.sessionToSessionRec
  dsimp only [List.flatMap_nil, List.append_nil]; repeat rw [pbFields_append_c]
  rw [pbFields_u32FieldList_c, pbFields_bytesFieldList_c, pbFields_bytesFieldList_c,
      pbFields_bytesFieldList_c, pbFields_u32FieldList_c, pbFields_map_msgField7_c,
      pbFields_u32FieldList_c, pbFields_u32FieldList_c, pbFields_bytesFieldList_c, pbFields_bytesFieldList_c]
  cases s.state.senderChain <;> cases s.pendingPreKey <;> cases s.pendingKyberPreKey <;>
    simp [Function.comp_def, pbFields_c, msgField]

theorem recordBytes_sessionToRecordRecPending_eq_encodeRecord_64
    (s : Session (List (BitVec 8))) (halice : s.aliceBaseKey.length < 2 ^ 64)
    (hpq : s.state.pqRatchetState.length < 2 ^ 64)
    (hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63)
    (hsess_len : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 64) :
    recordBytes (sessionToRecordRecPending s) = CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩ := by
  rw [← pbFields_encSessionFields_eq_sessionToRecordRecPending_c, pbFields_encSessionFields_c s halice hpq hseeds hsess_len]
  unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
  dsimp only [Option.map_some]; exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 1 _ hsess_len

theorem encSession_length_le_encodeRecord (s : Session (List (BitVec 8))) :
    (encSession s).length ≤ (CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩).length := by
  unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField CryptoVerification.E2E.Record.lenField
  simp only [Option.map_some, List.length_append]; omega

theorem pqRatchetState_length_le_encSession (s : Session (List (BitVec 8))) :
    s.state.pqRatchetState.length ≤ (encSession s).length := by
  unfold encSession
  have : s.state.pqRatchetState.length ≤ (CryptoVerification.E2E.Record.bytesField 15 s.state.pqRatchetState).length := by
    unfold CryptoVerification.E2E.Record.bytesField CryptoVerification.E2E.Record.lenField; split_ifs with h <;> simp [h]; omega
  simp only [List.length_append]; omega

end Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins
