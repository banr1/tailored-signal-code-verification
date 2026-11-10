/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF14AuxW
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# W-Stack Helpers and `pendingId` Leaf for `SessionStructure::merge_field` on Tag 9

Defines the `SP2Ext` specifications and layout-independent helpers for `SessionStructure::merge_field`
on protobuf tag 9 (`pending_pre_key` at `ss + 0xf8`, `pendingAt9P` / `prostSSGXNoPqAt_x9pW`) at
`mergeFieldStackX = 32768` with slice length `< 2 ^ 62`, and proves the `GenFieldX.pendingId` leaf
(`mergeField9PW_id_ok`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification CryptoVerification.E2E.Record
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.Serialization (allocPanic)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Tag-9 decodes and cursor helpers -/

gen_decodes CryptoVerification.libsignalSessionCode_tree x9pW
  [(ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 60),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 788) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 872),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1800) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1816),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1880) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1952),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 2036) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 2128),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 2204) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 2288),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 2348) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 2356)]

abbrev int32MergeRelOff_x9pW : BitVec 64 :=
  bv% ((2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") -
    (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64)

abbrev bytesMergeRelOff_x9pW : BitVec 64 :=
  bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
    (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64)

theorem encodeVarint_37_57_x9p {n : Nat} (h1 : 37 ≤ n) (h2 : n ≤ 57) :
    encodeVarint (BitVec.ofNat 64 n) = [BitVec.ofNat 8 n] ∧
      BitVec.signExtend 64 (BitVec.ofNat 8 n) = BitVec.ofNat 64 n ∧
      (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have hd : n - 37 ≤ 20 := by omega
  have hn : n = 37 + (n - 37) := by omega
  rw [hn]
  generalize n - 37 = d at hd
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d
  all_goals try decide
  omega

theorem pendingB0_signExtend_1_x9p (v : BitVec 64) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (36 + (encodeVarint v).length)) =
      BitVec.ofNat 64 (36 + (encodeVarint v).length) := by
  have hm := encodeVarint_length_bounds_mf14 v
  exact (encodeVarint_37_57_x9p (by omega) (by omega)).2.1

theorem pendingB0_getLsbD_63_1_x9p (v : BitVec 64) :
    (BitVec.ofNat 64 (36 + (encodeVarint v).length)).getLsbD 63 = false := by
  have hm := encodeVarint_length_bounds_mf14 v
  exact (encodeVarint_37_57_x9p (by omega) (by omega)).2.2

theorem pendingB0_signExtend_2_x9p (v1 v2 : BitVec 64) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (37 + (encodeVarint v1).length + (encodeVarint v2).length)) =
      BitVec.ofNat 64 (37 + (encodeVarint v1).length + (encodeVarint v2).length) := by
  have hm1 := encodeVarint_length_bounds_mf14 v1
  have hm2 := encodeVarint_length_bounds_mf14 v2
  exact (encodeVarint_37_57_x9p (by omega) (by omega)).2.1

theorem pendingB0_getLsbD_63_2_x9p (v1 v2 : BitVec 64) :
    (BitVec.ofNat 64 (37 + (encodeVarint v1).length + (encodeVarint v2).length)).getLsbD 63 = false := by
  have hm1 := encodeVarint_length_bounds_mf14 v1
  have hm2 := encodeVarint_length_bounds_mf14 v2
  exact (encodeVarint_37_57_x9p (by omega) (by omega)).2.2

theorem pendingId_payload_eq_x9p (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33) :
    (GenFieldX.pendingId i k).payload =
      BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length) ::
        8#8 :: (encodeVarint (i.setWidth 64) ++ (18#8 :: 33#8 :: k)) := by
  have hl : lenField 2 k = 18#8 :: 33#8 :: k := by unfold lenField; rw [hk]; rfl
  have hb : pendingIdBody i k =
      8#8 :: (encodeVarint (i.setWidth 64) ++ (18#8 :: 33#8 :: k)) := by
    unfold pendingIdBody; rw [hl]; rfl
  have hblen : (pendingIdBody i k).length = 36 + (encodeVarint (i.setWidth 64)).length := by
    rw [hb]; simp only [List.length_cons, List.length_append, hk]; omega
  have hm := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  have hvar := (encodeVarint_37_57_x9p (n := 36 + (encodeVarint (i.setWidth 64)).length)
    (by omega) (by omega)).1
  dsimp only [GenFieldX.payload]
  rw [hblen, hvar, hb, List.singleton_append]

theorem pendingId_payload_length_x9p (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33) :
    (GenFieldX.pendingId i k).payload.length = 37 + (encodeVarint (i.setWidth 64)).length := by
  rw [pendingId_payload_eq_x9p i hk]
  simp only [List.length_cons, List.length_append, hk]; omega

theorem mergeUint32_encode_64_x9p (v64 : BitVec 64) (rest : List (BitVec 8)) :
    mergeUint32 .varint (encodeVarint v64 ++ rest) = some (v64.setWidth 32, rest) := by
  simp [mergeUint32, decodeVarint_encodeVarint]

theorem setWidth32_setWidth64_x9p (x : BitVec 32) :
    (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem setWidth32_signExtend64_x9p (x : BitVec 32) :
    (x.signExtend 64).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hj, show j < 64 by omega]

theorem mergeBytes_k_x9p {k : List (BitVec 8)} (hk : k.length = 33)
    (rest : List (BitVec 8)) :
    mergeBytes .lengthDelimited (33#8 :: k ++ rest) = some (k, rest) := by
  have h := mergeBytes_encode k rest (by omega)
  rw [hk] at h
  exact h

theorem memRegion_40_split_x9p (ss : BitVec 64) :
    memRegion (ss + 0x100#64) 40 =
      (∃∗ w100 : BitVec 64, (ss + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (ss + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 64, (ss + 0x110#64) ↦₆₄ w110) ∗
      (∃∗ w118 : BitVec 64, (ss + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (ss + 0x120#64) ↦₃₂ w120) ∗
      memRegion (ss + 0x124#64) 4 := by
  rw [memRegion_split' (b := ss + 0x100#64) (b' := ss + 0x108#64) (n := 8) (k := 32) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x108#64) (b' := ss + 0x110#64) (n := 8) (k := 24) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x110#64) (b' := ss + 0x118#64) (n := 8) (k := 16) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x118#64) (b' := ss + 0x120#64) (n := 8) (k := 8) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x120#64) (b' := ss + 0x124#64) (n := 4) (k := 4) rfl (by bv_lin) (by decide),
      ProofLib.memRegion_eight (ss + 0x100#64), ProofLib.memRegion_eight (ss + 0x108#64),
      ProofLib.memRegion_eight (ss + 0x110#64), ProofLib.memRegion_eight (ss + 0x118#64),
      ProofLib.memRegion_four (ss + 0x120#64)]

private theorem pointsTo32_entails_memRegion4_x9p (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ⊢ memRegion a 4 := by
  rw [ProofLib.memRegion_four]
  exact Entails.sepExists_right v (Entails.refl _)

theorem split_272_x9p (ss : BitVec 64) :
    ((ss + 272#64) ↦₆₄ 1#64) = ((ss + 272#64) ↦₃₂ 1#32) ∗ ((ss + 276#64) ↦₃₂ 0#32) := by
  have h := ProofLib.pointsTo64_split32 (ss + 272#64) 1#64
  have h1 : (1#64).extractLsb' 0 32 = 1#32 := rfl
  have h2 : (1#64).extractLsb' 32 32 = 0#32 := rfl
  have h3 : ss + 272#64 + 4#64 = ss + 276#64 := by bv_lin
  rw [h1, h2, h3] at h
  exact h

theorem mask_hi32_truncate32_x9p (w : BitVec 64) :
    (w &&& 18446744069414584320#64 ||| 0#64).truncate 32 = 0#32 := by
  simp

theorem pid_disc_lsb_x9p (w : BitVec 64) :
    ((BitVec.zeroExtend 64 (BitVec.truncate 32 (w &&& 18446744069414584320#64 ||| 0#64))).getLsbD 0
      == true) = false := by
  rw [mask_hi32_truncate32_x9p]; rfl

theorem pid_none_entails_x9p (ss : BitVec 64) (w110 : BitVec 64) :
    ((ss + 272#64) ↦₆₄ (w110 &&& 18446744069414584320#64 ||| 0#64)) ⊢
      ((ss + 0x110#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x114#64) 4 := by
  rw [ProofLib.pointsTo64_split32]
  have hextr (x : BitVec 64) : x.extractLsb' 0 32 = x.truncate 32 := by
    ext i hi; simp
  rw [hextr, mask_hi32_truncate32_x9p]
  have h110 : ss + 272#64 = ss + 0x110#64 := rfl
  have h114 : ss + 272#64 + 4#64 = ss + 0x114#64 := by bv_lin
  rw [h110, h114]
  exact sepConj_mono_right (pointsTo32_entails_memRegion4_x9p _ _)

theorem emptyVec_pending_eq_vecU8At_x9p (A : RustAlloc) (ss : BitVec 64) :
    ((ss + 0xf8#64) ↦₆₄ 0#64) ∗ ((ss + 0x100#64) ↦₆₄ 1#64) ∗ ((ss + 0x108#64) ↦₆₄ 0#64) =
      vecU8At A (ss + 0xf8#64) 0#64 1#64 [] := by
  have h100 : ss + 0xf8#64 + 8#64 = ss + 0x100#64 := by bv_lin
  have h108 : ss + 0xf8#64 + 16#64 = ss + 0x108#64 := by bv_lin
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 :=
    ⟨by decide, by decide, by decide⟩
  dsimp only [vecU8At, vecHeader]
  have hite : (if (0#64 : BitVec 64) = 0 then emp else
      A.live (1#64) (0#64).toNat 1 ∗ 1#64 ↦ₛ [] ∗
        memRegion (1#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length)
          ((0#64 : BitVec 64).toNat - ([] : List (BitVec 8)).length)) = emp := rfl
  rw [h100, h108, eq_true hp, hite, pure_true, emp_sepConj, sepConj_emp, List.length_nil]

theorem sliceCursorAt_int32_gen_fold_x9p (slot p_cur : BitVec 64)
    (v64 : BitVec 64) (rest : List (BitVec 8)) :
    (slot ↦₆₄ p_cur) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 ((encodeVarint v64).length + rest.length)) ∗
      (p_cur ↦ₛ (encodeVarint v64 ++ rest)) =
      Prost.sliceCursorAt slot p_cur (encodeVarint v64 ++ rest) := by
  unfold Prost.sliceCursorAt
  rw [List.length_append]

theorem sliceCursorAfter_int32_gen_unfold_x9p (slot p_cur : BitVec 64)
    (v64 : BitVec 64) (rest : List (BitVec 8)) :
    Prost.sliceCursorAfter slot p_cur (encodeVarint v64 ++ rest) rest =
      (slot ↦₆₄ (p_cur + BitVec.ofNat 64 (encodeVarint v64).length)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
      (p_cur ↦ₛ encodeVarint v64) ∗
      ((p_cur + BitVec.ofNat 64 (encodeVarint v64).length) ↦ₛ rest) := by
  unfold Prost.sliceCursorAfter
  have hsub : (encodeVarint v64 ++ rest).length - rest.length = (encodeVarint v64).length := by
    rw [List.length_append]; omega
  rw [hsub, pointsToBytes_append]

theorem sliceCursorAt_bytes_gen_fold_x9p (slot p_cur : BitVec 64)
    {k : List (BitVec 8)} (hk : k.length = 33) (rest : List (BitVec 8)) :
    (slot ↦₆₄ p_cur) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (34 + rest.length)) ∗
      (p_cur ↦ₛ (33#8 :: k ++ rest)) =
      Prost.sliceCursorAt slot p_cur (33#8 :: k ++ rest) := by
  unfold Prost.sliceCursorAt
  have hlen : (33#8 :: k ++ rest).length = 34 + rest.length := by
    rw [List.length_append, List.length_cons, hk]
  rw [hlen]

theorem sliceCursorAfter_bytes_gen_unfold_x9p (slot p_cur : BitVec 64)
    {k : List (BitVec 8)} (hk : k.length = 33) (rest : List (BitVec 8)) :
    Prost.sliceCursorAfter slot p_cur (33#8 :: k ++ rest) rest =
      (slot ↦₆₄ (p_cur + 34#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
      (p_cur ↦ₛ (33#8 :: k)) ∗
      ((p_cur + 34#64) ↦ₛ rest) := by
  unfold Prost.sliceCursorAfter
  have hsub : (33#8 :: k ++ rest).length - rest.length = 34 := by
    rw [List.length_append, List.length_cons, hk]; omega
  have hlen : (33#8 :: k).length = 34 := by rw [List.length_cons, hk]
  rw [hsub, pointsToBytes_append, hlen]

def pendingPtr2 (ptr : BitVec 64) (i : BitVec 32) : BitVec 64 :=
  ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length

theorem sliceCursorAt_unfold_id_x9p (slot ptr : BitVec 64) (i : BitVec 32) {k : List (BitVec 8)}
    (hk : k.length = 33) (tail : List (BitVec 8)) :
    Prost.sliceCursorAt slot ptr ((GenFieldX.pendingId i k).payload ++ tail) =
      (slot ↦₆₄ ptr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (37 + (encodeVarint (i.setWidth 64)).length +
        tail.length)) ∗
      (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 8#8) ∗
      ((ptr + 2#64) ↦ₛ (encodeVarint (i.setWidth 64) ++ (18#8 :: 33#8 :: k ++ tail))) := by
  unfold Prost.sliceCursorAt
  have hlen : ((GenFieldX.pendingId i k).payload ++ tail).length =
      37 + (encodeVarint (i.setWidth 64)).length + tail.length := by
    rw [List.length_append, pendingId_payload_length_x9p i hk]
  rw [hlen, pendingId_payload_eq_x9p i hk]
  simp only [List.cons_append, List.append_assoc, pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin]

theorem sliceCursorAfter_fold_id_x9p (slot ptr : BitVec 64) (i : BitVec 32) {k : List (BitVec 8)}
    (hk : k.length = 33) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (pendingPtr2 ptr i + 1#64 + 34#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 8#8) ∗
      ((ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (pendingPtr2 ptr i ↦₈ 18#8) ∗
      ((pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k)) ∗
      ((pendingPtr2 ptr i + 1#64 + 34#64) ↦ₛ tail) =
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingId i k).payload ++ tail) tail := by
  unfold Prost.sliceCursorAfter pendingPtr2
  have hsub : ((GenFieldX.pendingId i k).payload ++ tail).length - tail.length =
      37 + (encodeVarint (i.setWidth 64)).length := by
    rw [List.length_append, pendingId_payload_length_x9p i hk]; omega
  have hm := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  have h37 : BitVec.ofNat 64 (37 + (encodeVarint (i.setWidth 64)).length) =
      2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 1#64 + 34#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hptr : ptr + BitVec.ofNat 64 (37 + (encodeVarint (i.setWidth 64)).length) =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 1#64 + 34#64 := by
    rw [h37]; bv_lin
  rw [hsub, hptr, pendingId_payload_eq_x9p i hk]
  simp only [List.cons_append, List.append_assoc, pointsToBytes_cons, pointsToBytes_append, hk,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin,
    show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 1#64 + 1#64 =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 2#64 by bv_lin,
    show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 2#64 + BitVec.ofNat 64 33 =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 1#64 + 34#64 by bv_lin]
  ac_rfl

theorem call_frame_inv_x9p {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P ⊢ T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ hm
      exact not_satisfies_false_sepConj hm) :
    SepWPp prog ret s P Q Qp := by
  intro R' hm hL
  have hTF : s.mem ⊨ (T ∗ F) ∗ R' := Satisfies.mono (sepConj_mono_left hP) hm
  have hpre_in : s.mem ⊨ (spec.inImage img).pre x s ∗ (F ∗ R') := by
    simp only [Spec.inImage, hspec, sepConj_assoc, satisfies_pure_sepConj]
    rw [sepConj_assoc] at hTF
    exact ⟨⟨hfl, hsym⟩, hφ, hTF⟩
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre_in hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanst, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoomst, hpost⟩
  · simp only [Spec.inImage] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hflm : img.FrozenLoaded sm := hfl.of_keepsFrozen hsteps.keepsFrozen
    have hsymm : sm.symtab = img.symtab := hsteps.symtab_eq.trans hsym
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hflm hsymm R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · simp only [Spec.inImage] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanst, _, hpost, hpanic sm hpanst⟩)⟩
  · simp only [Spec.inImage] at hpost
    exact (hexit sm code (F ∗ R') hex hpost).elim
  · simp only [Spec.inImage] at hpost
    exact (hoom sm (F ∗ R') hoomst hpost).elim

theorem allowPanic_frame_trace_x9p {s s0 sf : State} {F R : SepProp}
    (htr : s.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (fun h => by simpa only [allocFailedIn, htr] using h) hm

theorem close_x9p {s0 sf : State} {X R : SepProp}
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hm : sf.mem ⊨ (X ∗ emp) ∗ R) :
    sf.mem ⊨ (⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ X) ∗ R :=
  sat_pure_true_mf14W ⟨htr, hx0⟩ hm

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] pendingB0_signExtend_1_x9p pendingB0_getLsbD_63_1_x9p
  pendingB0_signExtend_2_x9p pendingB0_getLsbD_63_2_x9p

/-! ## Tag-9 field slice (`pendingAt9P`) and `prostSSRestNoPq_x9p` -/

/-- The non-pending fields of `prostSSGXAt` with the `vecU8 A (ss + 0x78#64) []` pin removed. -/
def prostSSRestNoPq_x9p (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGXNoPqAt_eq_pending_sep_rest_x9pW (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGXNoPqAt_x9pW A ss v = pendingAt9P A ss v ∗ prostSSRestNoPq_x9p A ss v := by
  unfold prostSSGXNoPqAt_x9pW prostSSRestNoPq_x9p
  ac_rfl

theorem prostSSRestNoPq_x9p_apply_pending (A : RustAlloc) (ss : BitVec 64) (v : SSGX)
    {fl : GenFieldX}
    (hfl : (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk)) :
    prostSSRestNoPq_x9p A ss (v.apply fl) = prostSSRestNoPq_x9p A ss v := by
  rcases hfl with ⟨i, k, rfl⟩ | ⟨o, k, spk, rfl⟩ <;> rfl

/-! ## W-stack specifications for `merge_field` on tag 9 -/

def mergeField9PPendingSpecAtW (img : Obj.Image) (P : GenFieldX → Prop) : Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧
      (x.v.base.pending = none ∧ x.v.ext.pid = none ∧ x.v.ext.spkId = 0#32) ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      pendingAt9P A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ pendingAt9P A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

def MergeField9PPendingOkAtW (img : Obj.Image) (ext : String → Option (State → State))
    (P : GenFieldX → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeField9PPendingSpecAtW img P)

def mergeField9PPendingSpecAtWA (A : RustAlloc) (img : Obj.Image) (P : GenFieldX → Prop) :
    Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧
      (x.v.base.pending = none ∧ x.v.ext.pid = none ∧ x.v.ext.spkId = 0#32) ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      pendingAt9P A x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ A.pool ∗
      stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ pendingAt9P A x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗ A.pool ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

def MergeField9PPendingOkAtWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (P : GenFieldX → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeField9PPendingSpecAtWA A img P)

def mergeField9PSpecAtW (img : Obj.Image) (P : GenFieldX → Prop) : Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostSSGXNoPqAt_x9pW A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostSSGXNoPqAt_x9pW A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

def MergeField9POkAtW (img : Obj.Image) (ext : String → Option (State → State))
    (P : GenFieldX → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeField9PSpecAtW img P)

theorem mergeField9PPendingSpecAtW_pre_iff (img : Obj.Image) {P : GenFieldX → Prop}
    {x : MergeFieldXGhost} {s : State} {R : SepProp} :
    (s.mem ⊨ (mergeField9PPendingSpecAtW img P).pre x s ∗ R) ↔
      P x.fld ∧ (s.mem ⊨ (mergeField9PPendingSpecAtW img (fun _ => True)).pre x s ∗ R) := by
  simp only [mergeField9PPendingSpecAtW, sepConj_assoc, satisfies_pure_sepConj]
  tauto

theorem mergeField9PPendingOkAtW_of_imp {img : Obj.Image}
    {ext : String → Option (State → State)} {P Q : GenFieldX → Prop}
    (hP : MergeField9PPendingOkAtW img ext P) (hQP : ∀ fl, Q fl → P fl) :
    MergeField9PPendingOkAtW img ext Q := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hq, hpre⟩ := (mergeField9PPendingSpecAtW_pre_iff img).mp hpre
  exact hP.mono_outcome x R s0 hpc hrun
    ((mergeField9PPendingSpecAtW_pre_iff img).mpr ⟨hQP _ hq, hpre⟩) hal fun _ hout => hout

theorem mergeField9PPendingOkAtW_or {img : Obj.Image}
    {ext : String → Option (State → State)} {P Q : GenFieldX → Prop}
    (hP : MergeField9PPendingOkAtW img ext P) (hQ : MergeField9PPendingOkAtW img ext Q) :
    MergeField9PPendingOkAtW img ext (fun fl => P fl ∨ Q fl) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hpq, hpre⟩ := (mergeField9PPendingSpecAtW_pre_iff img).mp hpre
  rcases hpq with hp | hq
  · exact hP.mono_outcome x R s0 hpc hrun
      ((mergeField9PPendingSpecAtW_pre_iff img).mpr ⟨hp, hpre⟩) hal fun _ hout => hout
  · exact hQ.mono_outcome x R s0 hpc hrun
      ((mergeField9PPendingSpecAtW_pre_iff img).mpr ⟨hq, hpre⟩) hal fun _ hout => hout

theorem mergeField9POkAtW_of_pending {img : Obj.Image}
    {ext : String → Option (State → State)} {P : GenFieldX → Prop}
    (hP9 : ∀ fl, P fl → (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk))
    (hP : MergeField9PPendingOkAtW img ext P) :
    MergeField9POkAtW img ext P := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  simp only [mergeField9PSpecAtW, prostSSGXNoPqAt_eq_pending_sep_rest_x9pW,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨h0, h1, h2, h3, h4, hp, hok, hfr, hlen, hfz, hsym⟩, hm⟩ := hpre
  have hfl := hP9 x.fld hp
  have hfr' : x.v.base.pending = none ∧ x.v.ext.pid = none ∧ x.v.ext.spkId = 0#32 := by
    rcases hfl with ⟨i, k, hfl'⟩ | ⟨o, k, spk, hfl'⟩
    · rw [hfl'] at hfr; obtain ⟨hp0, he0⟩ := hfr; rw [he0]; exact ⟨hp0, rfl, rfl⟩
    · rw [hfl'] at hfr; obtain ⟨hp0, he0⟩ := hfr; rw [he0]; exact ⟨hp0, rfl, rfl⟩
  have hpre' : s0.mem ⊨ (mergeField9PPendingSpecAtW img P).pre x s0 ∗
      (prostSSRestNoPq_x9p A0 x.ss x.v ∗ R) := by
    simp only [mergeField9PPendingSpecAtW, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨h0, h1, h2, h3, h4, hp, hok, hfr', hlen, hfz, hsym⟩, ?_⟩
    convert hm using 1; ac_rfl
  refine hP.mono_outcome x (prostSSRestNoPq_x9p A0 x.ss x.v ∗ R) s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [mergeField9PSpecAtW, prostSSGXNoPqAt_eq_pending_sep_rest_x9pW,
      prostSSRestNoPq_x9p_apply_pending A0 x.ss x.v hfl]
    simp only [mergeField9PPendingSpecAtW] at hpost
    convert hpost using 1; ac_rfl
  · right; left
    refine ⟨hpan, ?_⟩
    dsimp only [mergeField9PSpecAtW, mergeField9PPendingSpecAtW] at hpost ⊢
    rw [← sepConj_assoc] at hpost
    exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited hpost).elim

/-! ## Layout, stack, rodata, and arithmetic helpers -/

theorem pendingAt9P_fresh_unfold (A : RustAlloc) (ss : BitVec 64) (v : SSGX)
    (hp : v.base.pending = none) :
    pendingAt9P A ss v =
      ((ss + 0xf8#64) ↦₆₄ noneCap) ∗
      (∃∗ w100 : BitVec 64, (ss + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (ss + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 64, (ss + 0x110#64) ↦₆₄ w110) ∗
      (∃∗ w118 : BitVec 64, (ss + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (ss + 0x120#64) ↦₃₂ w120) ∗
      memRegion (ss + 0x124#64) 4 := by
  unfold pendingAt9P
  rw [hp, memRegion_40_split_x9p ss]

theorem pendingAt9P_post_fold_id (A : RustAlloc) (ss cap' ptr' : BitVec 64) (v : SSGX)
    (hspk0 : v.ext.spkId = 0#32) (i : BitVec 32) (k : List (BitVec 8)) :
    vecU8At A (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 0x110#64) ↦₃₂ 1#32) ∗ ((ss + 0x114#64) ↦₃₂ i) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ 0#32) ∗
      memRegion (ss + 0x124#64) 4 ⊢
      pendingAt9P A ss (v.apply (.pendingId i k)) := by
  have hv : vecU8At A (ss + 0xf8#64) cap' ptr' k ⊢ vecU8 A (ss + 0xf8#64) k :=
    Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
  refine Entails.trans (sepConj_mono_left hv) ?_
  unfold pendingAt9P SSGX.apply pidAt
  dsimp only
  rw [hspk0]
  exact Entails.of_eq (by ac_rfl)

theorem pendingAt9P_post_fold_spk_none (A : RustAlloc) (ss cap' ptr' v24 : BitVec 64) (v : SSGX)
    (k : List (BitVec 8)) (spk : BitVec 32) :
    vecU8At A (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 272#64) ↦₆₄ (v24 &&& 18446744069414584320#64 ||| 0#64)) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spk) ∗
      memRegion (ss + 0x124#64) 4 ⊢
      pendingAt9P A ss (v.apply (.pendingSpk none k spk)) := by
  have hv : vecU8At A (ss + 0xf8#64) cap' ptr' k ⊢ vecU8 A (ss + 0xf8#64) k :=
    Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
  refine Entails.trans (sepConj_mono hv (sepConj_mono_left (pid_none_entails_x9p ss v24))) ?_
  unfold pendingAt9P SSGX.apply pidAt
  dsimp only
  exact Entails.of_eq (by ac_rfl)

theorem pendingAt9P_post_fold_spk_some (A : RustAlloc) (ss cap' ptr' : BitVec 64) (v : SSGX)
    (i : BitVec 32) (k : List (BitVec 8)) (spk : BitVec 32) :
    vecU8At A (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 0x110#64) ↦₃₂ 1#32) ∗ ((ss + 0x114#64) ↦₃₂ i) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spk) ∗
      memRegion (ss + 0x124#64) 4 ⊢
      pendingAt9P A ss (v.apply (.pendingSpk (some i) k spk)) := by
  have hv : vecU8At A (ss + 0xf8#64) cap' ptr' k ⊢ vecU8 A (ss + 0xf8#64) k :=
    Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
  refine Entails.trans (sepConj_mono_left hv) ?_
  unfold pendingAt9P SSGX.apply pidAt
  dsimp only
  exact Entails.of_eq (by ac_rfl)

theorem rodata_jump_tag9_x9pW {img : Obj.Image} {s : State}
    (hLoads : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    s.mem.read8 (img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) = 0xb5#8 ∧
      s.mem.canRead (img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) 1 = true := by
  have hhb := loads_rodata_holdsBytes hLoads hF
    (off := num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) (n := 1) (bs := [0xb5#8])
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel) rfl
    (by rfl_kernel)
  exact ⟨(holdsBytes_cons_iff.mp hhb).1.1, (memSlice_of_holdsBytes_ro hhb).1⟩

private theorem stackAt_mergeFieldX_split_x9pW (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStackX =
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      memRegion (sp0 - 240#64) 160 ∗
      cells (sp0 - 80#64) 10 := by
  have htop := stackAt_split_top_mf14 sp0 mergeFieldSubStackX 240 (by decide)
  change stackAt sp0 mergeFieldStackX =
    stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ memRegion (sp0 - 240#64) 240 at htop
  rw [htop,
      memRegion_split' (b := sp0 - 240#64) (b' := sp0 - 80#64) (n := 160) (k := 80)
        rfl (by bv_lin) (by decide),
      show (80 : Nat) = 8 * 10 by rfl,
      LibsignalTripleRatchet.memRegion_cells (sp0 - 80#64) 10 (by decide)]

theorem stackAt_mergeFieldX_unfold_x9pW (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStackX =
      ∃∗ v80 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v64 : BitVec 64,
      ∃∗ v56 : BitVec 64, ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64,
      ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64,
      ∃∗ v8 : BitVec 64,
        ((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
        ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
        ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
        ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
        ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8) ∗
        memRegion (sp0 - 240#64) 160 ∗
        stackAt (sp0 - 240#64) mergeFieldSubStackX := by
  have h1 : stackAt sp0 mergeFieldStackX =
      cells (sp0 - 80#64) 10 ∗
      (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX) := by
    rw [stackAt_mergeFieldX_split_x9pW sp0]; ac_rfl
  rw [h1]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin, show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin, show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin, show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin, show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin, sepConj_assoc]

theorem bufRef_and_stackAt_mergeFieldX_fold_x9pW
    (bufRef slot sp0 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (SC : SepProp) :
    (bufRef ↦₆₄ slot) ∗ SC ∗
      (((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
       ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
       ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
       ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
       ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8) ∗
       memRegion (sp0 - 240#64) 160 ∗
       stackAt (sp0 - 240#64) mergeFieldSubStackX) ⊢
    (bufRef ↦₆₄ slot) ∗ SC ∗ stackAt sp0 mergeFieldStackX := by
  refine sepConj_mono_right (sepConj_mono_right ?_)
  have h1 : stackAt sp0 mergeFieldStackX =
      (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX) ∗
      cells (sp0 - 80#64) 10 := by
    rw [stackAt_mergeFieldX_split_x9pW sp0]; ac_rfl
  rw [h1]
  simp only [cells, sepConj_emp, ← sepExists_sepConj_left,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin, show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin, show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin, show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin, show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin]
  refine Entails.trans (Q := (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX) ∗
    (((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
     ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
     ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
     ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
     ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8)))
    (by apply Entails.of_eq; ac_rfl) ?_
  refine sepConj_mono_right ?_
  iterate 9 (refine sepConj_mono (Entails.sepExists_intro _) ?_)
  exact Entails.sepExists_intro v8

theorem stackAt_sub_to_int32Merge_x9pW (sp : BitVec 64) :
    stackAt sp mergeFieldSubStackX =
      memRegion (sp - 32528#64) 7792 ∗ stackAt sp Prost.X.int32MergeStackW :=
  ProofLib.stackAt_split_bottom sp Prost.X.int32MergeStackW 7792 (by decide)

theorem stackAt_sub_to_bytesMerge_x9pW (sp : BitVec 64) :
    stackAt sp mergeFieldSubStackX =
      memRegion (sp - 32528#64) 7648 ∗ stackAt sp Prost.X.bytesMergeStackW :=
  ProofLib.stackAt_split_bottom sp Prost.X.bytesMergeStackW 7648 (by decide)

theorem pre_to_int32_gen_x9pWA (A : RustAlloc) (dst bufRef slot curPtr sp0 : BitVec 64)
    (v : BitVec 64) (rest : List (BitVec 8)) (F : SepProp) :
    (dst ↦₃₂ 0#32 ∗ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ curPtr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 ((encodeVarint v).length + rest.length)) ∗
      (curPtr ↦ₛ (encodeVarint v ++ rest)) ∗ A.pool ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ F) ⊢
    (memRegion dst 4 ∗ (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot curPtr (encodeVarint v ++ rest) ∗ A.pool ∗
      stackAt (sp0 - 240#64) Prost.X.int32MergeStackW) ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7792 ∗ F) := by
  rw [stackAt_sub_to_int32Merge_x9pW (sp0 - 240#64)]
  have hsc := sliceCursorAt_int32_gen_fold_x9p slot curPtr v rest
  refine Entails.trans (Q := (dst ↦₃₂ 0#32 ∗ ((bufRef ↦₆₄ slot) ∗ ((slot ↦₆₄ curPtr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 ((encodeVarint v).length + rest.length)) ∗
      (curPtr ↦ₛ (encodeVarint v ++ rest))) ∗ A.pool ∗
      stackAt (sp0 - 240#64) Prost.X.int32MergeStackW)) ∗
    (memRegion (sp0 - 240#64 - 32528#64) 7792 ∗ F)) (by apply Entails.of_eq; ac_rfl) ?_
  rw [hsc]
  exact sepConj_mono_left (sepConj_mono_left (pointsTo32_entails_memRegion4_x9p dst 0#32))

theorem pre_to_int32_gen_x9pW (dst bufRef slot curPtr sp0 : BitVec 64)
    (v : BitVec 64) (rest : List (BitVec 8)) (F : SepProp) :
    (dst ↦₃₂ 0#32 ∗ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ curPtr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 ((encodeVarint v).length + rest.length)) ∗
      (curPtr ↦ₛ (encodeVarint v ++ rest)) ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ F) ⊢
    (memRegion dst 4 ∗ (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot curPtr (encodeVarint v ++ rest) ∗ A0.pool ∗
      stackAt (sp0 - 240#64) Prost.X.int32MergeStackW) ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7792 ∗ F) := by
  have hpool : A0.pool = emp := rfl
  simpa only [hpool, emp_sepConj] using pre_to_int32_gen_x9pWA A0 dst bufRef slot curPtr sp0 v rest F

theorem post_of_int32_gen_x9pWA (A : RustAlloc) (dst bufRef slot curPtr sp0 : BitVec 64)
    (v : BitVec 64) (i : BitVec 32) (hvi : v.setWidth 32 = i)
    (rest : List (BitVec 8)) (F : SepProp) (sm sf : State) (hsp : sm.sp = sp0 - 240#64) :
    (Prost.X.int32MergeSpecW A).post
      ⟨.varint, dst, bufRef, slot, curPtr, encodeVarint v ++ rest⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7792 ∗ F) =
    (⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
      ((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (curPtr + BitVec.ofNat 64 (encodeVarint v).length)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (curPtr ↦ₛ encodeVarint v) ∗
        ((curPtr + BitVec.ofNat 64 (encodeVarint v).length) ↦ₛ rest) ∗ A.pool ∗
        stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ F)) := by
  dsimp only [Prost.X.int32MergeSpecW]
  rw [mergeUint32_encode_64_x9p v rest, hvi]
  dsimp only
  rw [hsp, sliceCursorAfter_int32_gen_unfold_x9p slot curPtr v rest,
      stackAt_sub_to_int32Merge_x9pW (sp0 - 240#64)]
  ac_rfl

theorem post_of_int32_gen_x9pW (dst bufRef slot curPtr sp0 : BitVec 64)
    (v : BitVec 64) (i : BitVec 32) (hvi : v.setWidth 32 = i)
    (rest : List (BitVec 8)) (F : SepProp) (sm sf : State) (hsp : sm.sp = sp0 - 240#64) :
    (Prost.X.int32MergeSpecW A0).post
      ⟨.varint, dst, bufRef, slot, curPtr, encodeVarint v ++ rest⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7792 ∗ F) =
    (⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
      ((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (curPtr + BitVec.ofNat 64 (encodeVarint v).length)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (curPtr ↦ₛ encodeVarint v) ∗
        ((curPtr + BitVec.ofNat 64 (encodeVarint v).length) ↦ₛ rest) ∗
        stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ F)) := by
  have hpool : A0.pool = emp := rfl
  simpa only [hpool, emp_sepConj] using
    post_of_int32_gen_x9pWA A0 dst bufRef slot curPtr sp0 v i hvi rest F sm sf hsp

theorem pre_to_bytesMerge_gen_x9pWA (A : RustAlloc) (ss bufRef slot curPtr sp0 : BitVec 64)
    {k : List (BitVec 8)} (hk : k.length = 33) (rest : List (BitVec 8)) (F : SepProp) :
    (((ss + 0xf8#64) ↦₆₄ 0#64 ∗ (ss + 0x100#64) ↦₆₄ 1#64 ∗ (ss + 0x108#64) ↦₆₄ 0#64) ∗
      bufRef ↦₆₄ slot ∗ ((slot ↦₆₄ curPtr) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (34 + rest.length)) ∗
        (curPtr ↦ₛ (33#8 :: k ++ rest))) ∗ A.pool ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ F) =
    (vecU8At A (ss + 248#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot curPtr (33#8 :: k ++ rest) ∗ A.pool ∗
      stackAt (sp0 - 240#64) Prost.X.bytesMergeStackW) ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7648 ∗ F) := by
  rw [emptyVec_pending_eq_vecU8At_x9p A ss, sliceCursorAt_bytes_gen_fold_x9p slot curPtr hk rest,
      stackAt_sub_to_bytesMerge_x9pW (sp0 - 240#64)]
  ac_rfl

theorem pre_to_bytesMerge_gen_x9pW (ss bufRef slot curPtr sp0 : BitVec 64)
    {k : List (BitVec 8)} (hk : k.length = 33) (rest : List (BitVec 8)) (F : SepProp) :
    (((ss + 0xf8#64) ↦₆₄ 0#64 ∗ (ss + 0x100#64) ↦₆₄ 1#64 ∗ (ss + 0x108#64) ↦₆₄ 0#64) ∗
      bufRef ↦₆₄ slot ∗ ((slot ↦₆₄ curPtr) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (34 + rest.length)) ∗
        (curPtr ↦ₛ (33#8 :: k ++ rest))) ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ F) =
    (vecU8At A0 (ss + 248#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot curPtr (33#8 :: k ++ rest) ∗ A0.pool ∗
      stackAt (sp0 - 240#64) Prost.X.bytesMergeStackW) ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7648 ∗ F) := by
  have hpool : A0.pool = emp := rfl
  simpa only [hpool, emp_sepConj] using pre_to_bytesMerge_gen_x9pWA A0 ss bufRef slot curPtr sp0 hk rest F

theorem post_of_bytesMerge_gen_x9pWA (A : RustAlloc) (ss bufRef slot curPtr sp0 : BitVec 64)
    {k : List (BitVec 8)} (hk : k.length = 33) (rest : List (BitVec 8)) (F : SepProp)
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) :
    (Prost.X.bytesMergeRawSpecW A).post
      ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
        curPtr, 33#8 :: k ++ rest⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7648 ∗ F) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
      (vecU8At A (ss + 248#64) cap' ptr' k ∗ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (curPtr + 34#64)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (curPtr ↦ₛ (33#8 :: k)) ∗
        ((curPtr + 34#64) ↦ₛ rest) ∗ A.pool ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ F)) := by
  dsimp only [Prost.X.bytesMergeRawSpecW]
  rw [mergeBytes_k_x9p hk rest]
  dsimp only
  rw [hsp, sliceCursorAfter_bytes_gen_unfold_x9p slot curPtr hk rest,
      stackAt_sub_to_bytesMerge_x9pW (sp0 - 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

theorem post_of_bytesMerge_gen_x9pW (ss bufRef slot curPtr sp0 : BitVec 64)
    {k : List (BitVec 8)} (hk : k.length = 33) (rest : List (BitVec 8)) (F : SepProp)
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) :
    (Prost.X.bytesMergeRawSpecW A0).post
      ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
        curPtr, 33#8 :: k ++ rest⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7648 ∗ F) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
      (vecU8At A0 (ss + 248#64) cap' ptr' k ∗ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (curPtr + 34#64)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (curPtr ↦ₛ (33#8 :: k)) ∗
        ((curPtr + 34#64) ↦ₛ rest) ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ F)) := by
  have hpool : A0.pool = emp := rfl
  simpa only [hpool, emp_sepConj] using post_of_bytesMerge_gen_x9pWA A0 ss bufRef slot curPtr sp0 hk rest F sm sf hsp

theorem callee_subs_x9pWA {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : DeserializeCalleesAtWA img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName + int32MergeRelOff_x9pW)
      ((Prost.X.int32MergeSpecW A).inImage img) ∧
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName + bytesMergeRelOff_x9pW)
      (Prost.X.bytesMergeSpecW A img) :=
  ⟨int32Merge_ok_sub_mf14WA hC.2.1, bytesMerge_ok_sub_mf14WA hC.2.2.1⟩

theorem callee_subs_x9pW {img : Obj.Image} {ext : String → Option (State → State)}
    (hC : DeserializeCalleesAtW img ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName + int32MergeRelOff_x9pW)
      ((Prost.X.int32MergeSpecW A0).inImage img) ∧
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName + bytesMergeRelOff_x9pW)
      (Prost.X.bytesMergeSpecW A0 img) :=
  callee_subs_x9pWA hC

/-! ## Arithmetic helpers under `< 2 ^ 62` -/

theorem len_ne_zero_x9pW {a n : Nat} (ha : 0 < a) (_hlen : a + n < 2 ^ 62) :
    (BitVec.ofNat 64 (a + n) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at h1; omega

theorem sub1_and_add_neg1_x9pW {a a' n : Nat} (ha : a = a' + 1) (_hlen : a + n < 2 ^ 62) :
    BitVec.ofNat 64 (a + n) - 1#64 = BitVec.ofNat 64 (a' + n) ∧
      BitVec.ofNat 64 (a + n) + (-1#64) = BitVec.ofNat 64 (a' + n) := by
  have h1 : BitVec.ofNat 64 (a + n) - 1#64 = BitVec.ofNat 64 (a' + n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine ⟨h1, ?_⟩
  rw [← BitVec.sub_eq_add_neg]
  exact h1

theorem subs_body_len_x9pW {L n : Nat} (_hlen : L + n < 2 ^ 62) :
    BitVec.ofNat 64 (L + n) - BitVec.ofNat 64 L = BitVec.ofNat 64 n ∧
      BitVec.ult (BitVec.ofNat 64 (L + n)) (BitVec.ofNat 64 L) = false ∧
      BitVec.ule (BitVec.ofNat 64 L) (BitVec.ofNat 64 (L + n)) = true := by
  refine ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  · simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega

theorem cmp_gt_tail_x9pW {a n : Nat} (ha : 0 < a) (_hlen : a + n < 2 ^ 62) :
    BitVec.ult (BitVec.ofNat 64 (a + n)) (BitVec.ofNat 64 n) = false ∧
      BitVec.ule (BitVec.ofNat 64 (a + n)) (BitVec.ofNat 64 n) = false ∧
      BitVec.ult (BitVec.ofNat 64 n) (BitVec.ofNat 64 (a + n)) = true ∧
      BitVec.ofNat 64 (a + n) - BitVec.ofNat 64 n = BitVec.ofNat 64 a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  · simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  · simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-! ## `GenFieldX.pendingId` leaf (`mergeField9PW_id_ok`) -/

open Lean Elab Tactic in
local elab "mf9p_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn := mkIdent `Symbolic.Swarm.TRREF.B3DeserQ.mergeField_fnOff_mf14W
  let mut k := kStart
  while k <= kEnd do
    let dec := mkIdent (.str `Symbolic.Swarm.TRREF.B3DeserQ
      s!"x9pW_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))
    k := k + 4

open Lean Elab Tactic in
local elab "mf9p_fetch_named " nm:ident b:term:max H:term:max kLit:num : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  let k := kLit.getNat
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn := mkIdent `Symbolic.Swarm.TRREF.B3DeserQ.mergeField_fnOff_mf14W
  let dec := mkIdent (.str `Symbolic.Swarm.TRREF.B3DeserQ
    s!"x9pW_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
  evalTactic (← `(tactic|
    have $nm := $fetchAdd (b := $b) (H := $H) (k := $kLit) $hfn (by decide) $dec))

private theorem final_post_entails_id_x9pWA (A : RustAlloc) (ss cap' ptr' : BitVec 64) (v : SSGX)
    (hspk0 : v.ext.spkId = 0#32)
    (bufRef slot ptr : BitVec 64) (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33)
    (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A (ss + 248#64) cap' ptr' k ∗ bufRef ↦₆₄ slot ∗
      slot ↦₆₄ (pendingPtr2 ptr i + 1#64 + 34#64) ∗
      (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
      (pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k) ∗
      (pendingPtr2 ptr i + 1#64 + 34#64) ↦ₛ tail ∗ A.pool ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      ((ss + 276#64) ↦₃₂ i ∗ (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
        pendingPtr2 ptr i ↦₈ 18#8 ∗
        ((ss + 272#64) ↦₃₂ 1#32 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗ (ss + 288#64) ↦₃₂ 0#32 ∗
          memRegion (ss + 292#64) 4 ∗
          ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length) ∗
          (ptr + 1#64) ↦₈ 8#8 ∗ (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗
          (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗ (sp0 - 48#64) ↦₆₄ r24 ∗
          (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
          (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160))) ⊢
    pendingAt9P A ss (v.apply (.pendingId i k)) ∗ bufRef ↦₆₄ slot ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingId i k).payload ++ tail) tail ∗ A.pool ∗
      stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_fold_id_x9p slot ptr i hk tail]
  refine Entails.trans (Entails.trans (Q :=
    (vecU8At A (ss + 0xf8#64) cap' ptr' k ∗ ((ss + 0x110#64) ↦₃₂ 1#32) ∗
      ((ss + 0x114#64) ↦₃₂ i) ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ 0#32) ∗
      memRegion (ss + 0x124#64) 4) ∗ (bufRef ↦₆₄ slot) ∗
    (((slot ↦₆₄ (pendingPtr2 ptr i + 1#64 + 34#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 8#8) ∗ ((ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (pendingPtr2 ptr i ↦₈ 18#8) ∗ ((pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k)) ∗
      ((pendingPtr2 ptr i + 1#64 + 34#64) ↦ₛ tail)) ∗ A.pool) ∗
    ((sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗
      (sp0 - 56#64) ↦₆₄ w118 ∗ (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗
      (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗ (sp0 - 16#64) ↦₆₄ r20 ∗
      (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX))
    (by apply Entails.of_eq; ac_rfl)
    (sepConj_mono (pendingAt9P_post_fold_id A ss cap' ptr' v hspk0 i k)
      (bufRef_and_stackAt_mergeFieldX_fold_x9pW bufRef slot sp0
        r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 _)))
    (by apply Entails.of_eq; ac_rfl)

set_option maxHeartbeats 800000 in
theorem mergeField9PWA_id_ok (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtWA img A ext) :
    MergeField9PPendingOkAtWA img A ext (fun fl => ∃ i k, fl = .pendingId i k) := by
  dsimp only [MergeField9PPendingOkAtWA, OkAtX]
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  refine ⟨(mergeField9PPendingSpecAtWA A img (fun fl => ∃ i k, fl = .pendingId i k)).pre
    ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ s0, R, hpre, ?_⟩
  clear hpre
  dsimp only [mergeField9PPendingSpecAtWA]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, hfld, hOk, hFresh, hlen, hF0, hsym0⟩ => ?_
  obtain ⟨i, k, rfl⟩ := hfld
  have hk : k.length = 33 := hOk
  obtain ⟨hp, _hpid, hspk0⟩ := hFresh
  dsimp only [GenFieldX.tag, GenFieldX.wt, WireType.toNat] at hx1 hx2
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hm := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  rw [List.length_append, pendingId_payload_length_x9p i hk] at hlen
  rw [State.spAligned] at hsp_align
  have hb : img.base &&& 4095#64 = 0#64 := base_aligned_of_loads hLoads
  obtain ⟨hcallI, hcallB⟩ := callee_subs_x9pWA hC
  let H := Rust.withPanics ext
  mf9p_fetches_range img.base H 0 60
  mf9p_fetches_range img.base H 788 872
  mf9p_fetches_range img.base H 1800 1816
  mf9p_fetches_range img.base H 1880 1952
  mf9p_fetches_range img.base H 2036 2128
  mf9p_fetches_range img.base H 2204 2288
  mf9p_fetches_range img.base H 2348 2356
  dsimp only [SP2Ext, contractProg] at hpc hcallB hcallI ⊢
  have hx2_tr : (s0.readReg64 (Reg.gpr 2#5)).truncate 32 &&& 255#32 = 2#32 :=
    wt_and_ff_eq_mf14W (s0.readReg64 .x2) hx2
  have hx2_64 : BitVec.truncate 32 (BitVec.zeroExtend 64
      (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 2#5))) &&& 255#64) = 2#32 :=
    wt_and_ff_64_eq_mf14W (s0.readReg64 .x2) hx2
  have hl_ne0 := len_ne_zero_x9pW (a := 37 + (encodeVarint (i.setWidth 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hl_s1, hl_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 37 + (encodeVarint (i.setWidth 64)).length)
    (a' := 36 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega) hlen
  obtain ⟨hsubL, hultL, huleL⟩ := subs_body_len_x9pW
    (L := 36 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega)
  obtain ⟨hl2_s1, hl2_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 36 + (encodeVarint (i.setWidth 64)).length)
    (a' := 35 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega) (by omega)
  obtain ⟨hult1, hule1, hult1', hsub1⟩ := cmp_gt_tail_x9pW
    (a := 36 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega) (by omega)
  obtain ⟨hl35_s1, hl35_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 35) (a' := 34) (n := tail.length) (by omega) (by omega)
  obtain ⟨hult2, hule2, hult2', hsub2⟩ := cmp_gt_tail_x9pW
    (a := 35) (n := tail.length) (by omega) (by omega)
  have hadrp :
      (((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr mergeFieldName + 40#64) &&&
        bv% (2 ^ 64 - 4096)) +
        bv% (ls_bytes% "0082775f19328d6db5d6cb6d" -
          page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40)) =
        img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d") := by
    rw [Program.fnAddr_rebase, mergeField_fnOff_mf14W]
    exact adrp_rodata_mf14W img.base hb
  mf9p_fetch_named hfetch_ldr8 img.base (Rust.withPanics ext) 52
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr mergeFieldName = entry
  examples_hide_fetches
  conv =>
    arg 4
    rw [pendingAt9P_fresh_unfold A ss v hp, sliceCursorAt_unfold_id_x9p slot ptr i hk tail,
        stackAt_mergeFieldX_unfold_x9pW s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w100 => SepWPp.exists_elim fun w108 =>
    SepWPp.exists_elim fun w110 => SepWPp.exists_elim fun w118 =>
    SepWPp.exists_elim fun w120 => SepWPp.exists_elim fun v80 =>
    SepWPp.exists_elim fun v72 => SepWPp.exists_elim fun v64 =>
    SepWPp.exists_elim fun v56 => SepWPp.exists_elim fun v48 =>
    SepWPp.exists_elim fun v40 => SepWPp.exists_elim fun v32 =>
    SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v16 =>
    SepWPp.exists_elim fun v8 => ?_
  have hlsb := pid_disc_lsb_x9p v24
  let mfStart := entry
  apply of_sepWP_frozen_mf14 hF0 hsym0 (mid := mfStart + 52#64)
  iterate 13 wp_step
  apply SepWP.done (by simp only [mfStart, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hF1 hsym1
  obtain ⟨hread9, hcan9⟩ := rodata_jump_tag9_x9pW hLoads hF1
  apply of_sepWP_frozen_mf14 hF1 hsym1 (mid := entry + int32MergeRelOff_x9pW)
  refine step_ldr8_ro_mf14 (pc := mfStart + 52#64) (pc' := mfStart + 56#64)
    (r := Reg.gpr 11#5) (v64 := 181#64)
    rfl (by simp only [wp_norm, arm64_norm, hrun]) hfetch_ldr8 rfl
    (ea := img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) (wb := none)
    (by simp only [evalAddrMode, wp_norm, arm64_norm])
    hread9 hcan9 (by simp only [applyWriteback, wp_norm, arm64_norm]) ?_
  iterate 30 wp_step
  iterate 32 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hF2 hsym2
  have hlen_i1 : 35 + (encodeVarint (i.setWidth 64)).length + tail.length =
      (encodeVarint (i.setWidth 64)).length + (18#8 :: 33#8 :: k ++ tail).length := by
    simp only [List.length_cons, List.length_append, hk]; omega
  refine call_frame_inv_x9p
    (x := ⟨.varint, ss + 276#64, bufRef, slot, ptr + 2#64,
      encodeVarint (i.setWidth 64) ++ (18#8 :: 33#8 :: k ++ tail)⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7792 ∗
      ((ss + 0xf8#64) ↦₆₄ 0#64 ∗ (ss + 0x100#64) ↦₆₄ 1#64 ∗ (ss + 0x108#64) ↦₆₄ 0#64) ∗
      (ss + 272#64) ↦₃₂ 1#32 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗ (ss + 288#64) ↦₃₂ 0#32 ∗
      memRegion (ss + 292#64) 4 ∗
      ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length) ∗ (ptr + 1#64) ↦₈ 8#8 ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗ (s0.sp - 56#64) ↦₆₄ w118 ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
      memRegion (s0.sp - 240#64) 160)
    hcallI hF2 hsym2
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align) rfl
    (by simp only [Prost.X.int32MergeSpecW, wp_norm, arm64_norm]; rfl)
    (by simp only [List.length_append, List.length_cons, hk]; omega)
    (by
      refine Entails.trans ?_ (pre_to_int32_gen_x9pWA A (ss + 276#64) bufRef slot (ptr + 2#64) s0.sp
          (i.setWidth 64) (18#8 :: 33#8 :: k ++ tail) _)
      rw [split_272_x9p ss, hlen_i1]; exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [Prost.X.int32MergeSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm]) hm) ?_
  intro sf hpcf hrunf hspf hcsf hF3 hsym3
  simp only [wp_norm, arm64_norm] at hpcf
  have hsp_sf : sf.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm] using hspf
  rw [post_of_int32_gen_x9pWA A (ss + 276#64) bufRef slot (ptr + 2#64) s0.sp
      (i.setWidth 64) i (setWidth32_setWidth64_x9p i) (18#8 :: 33#8 :: k ++ tail) _
      _ sf (by simp only [wp_norm, arm64_norm])]
  refine SepWPp.pure_elim fun htr_i => SepWPp.pure_elim fun hx0_i => ?_
  have hlen_i2 : (18#8 :: 33#8 :: k ++ tail).length = 35 + tail.length := by
    simp only [List.cons_append, List.length_cons, List.length_append, hk]; omega
  conv =>
    arg 4
    rw [hlen_i2, show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length =
      pendingPtr2 ptr i from rfl]
    simp only [List.cons_append, pointsToBytes_cons, sepConj_assoc]
  have hx19_i : sf.readReg64 (Reg.gpr 19#5) = ss + 248#64 := by simpa only [wp_norm, arm64_norm] using hcsf.1
  have hx20_i : sf.readReg64 (Reg.gpr 20#5) = 98#64 := by simpa only [wp_norm, arm64_norm] using hcsf.2.1
  have hx21_i : sf.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
  have hx22_i : sf.readReg64 (Reg.gpr 22#5) = 1#64 := by simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.1
  have hx23_i : sf.readReg64 (Reg.gpr 23#5) = ss := by simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.1
  have hx24_i : sf.readReg64 (Reg.gpr 24#5) = bufRef := by simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.1
  have hx25_i : sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := by simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.1
  have hx26_i : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
  have hx27_i : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
  have hx28_i : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
  have hvregs_i : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
  apply of_sepWP_frozen_mf14 hF3 hsym3 (mid := entry + bytesMergeRelOff_x9pW)
  iterate 35 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf])
  intro hF4 hsym4
  refine call_frame_inv_x9p
    (x := ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      pendingPtr2 ptr i + 1#64, 33#8 :: k ++ tail⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7648 ∗
      (ss + 276#64) ↦₃₂ i ∗ (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
      pendingPtr2 ptr i ↦₈ 18#8 ∗
      ((ss + 272#64) ↦₃₂ 1#32 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗ (ss + 288#64) ↦₃₂ 0#32 ∗
        memRegion (ss + 292#64) 4 ∗
        ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length) ∗ (ptr + 1#64) ↦₈ 8#8 ∗
        (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗ (s0.sp - 56#64) ↦₆₄ w118 ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
        memRegion (s0.sp - 240#64) 160))
    hcallB hF4 hsym4
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf])
    (by rw [State.spAligned]; simp only [wp_norm, arm64_norm, hsp_sf]
        simpa only [wp_norm, arm64_norm] using hsp_align) rfl
    (by simp only [Prost.X.bytesMergeRawSpecW, wp_norm, arm64_norm, hsp_sf]; rfl)
    (by rw [List.length_cons, List.length_append, hk]; omega)
    (by
      simp only [← List.cons_append]
      rw [← pre_to_bytesMerge_gen_x9pWA A ss bufRef slot (pendingPtr2 ptr i + 1#64) s0.sp hk tail,
        List.cons_append, pointsToBytes_cons]
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf' _ hm => by
      dsimp only [Prost.X.bytesMergeRawSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm, htr_i]) hm) ?_
  intro sf2 hpcf2 hrunf2 hspf2 hcsf2 _ _
  simp only [wp_norm, arm64_norm] at hpcf2
  rw [post_of_bytesMerge_gen_x9pWA A ss bufRef slot (pendingPtr2 ptr i + 1#64) s0.sp hk tail _
    _ sf2 (by simp only [wp_norm, arm64_norm, hsp_sf])]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun htr_sf => SepWPp.pure_elim fun hx0_sf => ?_
  have htr_sf' : sf2.trace = s0.trace := by simpa only [wp_norm, arm64_norm, htr_i] using htr_sf
  have hx0_sf' : sf2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf
  have hx21_sf : sf2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by simpa only [wp_norm, arm64_norm, hx21_i] using hcsf2.2.2.1
  have hx24_sf : sf2.readReg64 (Reg.gpr 24#5) = bufRef := by simpa only [wp_norm, arm64_norm, hx24_i] using hcsf2.2.2.2.2.2.1
  have hx26_sf : sf2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by simpa only [wp_norm, arm64_norm, hx26_i] using hcsf2.2.2.2.2.2.2.2.1
  have hx27_sf : sf2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by simpa only [wp_norm, arm64_norm, hx27_i] using hcsf2.2.2.2.2.2.2.2.2.1
  have hx28_sf : sf2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by simpa only [wp_norm, arm64_norm, hx28_i] using hcsf2.2.2.2.2.2.2.2.2.2.1
  have hvregs_sf : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sf2 = calleeSavedVRegs sf := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregs_i
  have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm, hsp_sf] using hspf2
  have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = false := by simp [BitVec.ult]
  have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = true := by simp [BitVec.ule]
  apply SepWPp.of_sepWP_ret
  iterate 19 wp_step
  apply SepWP.fold (final_post_entails_id_x9pWA A ss cap' ptr' v hspk0 bufRef slot ptr i hk tail s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) w118
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
    (sepConj_emp _).symm
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf2])
  refine ⟨fun hmf => close_x9p (by simp only [wp_norm, arm64_norm, htr_sf'])
      (by simp only [wp_norm, arm64_norm]) hmf,
    by simp only [wp_norm, arm64_norm],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm, hx26_sf, hx27_sf,
      hx28_sf]; exact hvregs_sf⟩

theorem mergeField9PW_id_ok (img : Obj.Image)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtW img ext) :
    MergeField9PPendingOkAtW img ext (fun fl => ∃ i k, fl = .pendingId i k) := by
  have hpool : A0.pool = emp := rfl
  refine okAtX_of_eq_pre_post_mf14 (mergeField9PWA_id_ok img A0 ext hLoads hC)
    (fun _ _ => by simp only [mergeField9PPendingSpecAtWA, mergeField9PPendingSpecAtW, hpool, emp_sepConj])
    (fun _ _ _ => by simp only [mergeField9PPendingSpecAtWA, mergeField9PPendingSpecAtW, hpool, emp_sepConj])
    rfl rfl rfl

end Symbolic.Swarm.TRREF.B3DeserQ
