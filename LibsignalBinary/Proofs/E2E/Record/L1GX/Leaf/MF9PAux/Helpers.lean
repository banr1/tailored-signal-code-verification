/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF14Aux.Helpers

import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Base
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF9PAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MF9PAux

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.Serialization (OkAt allocPanic)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000


/-! ## Generic `int32::merge` and `bytes::merge` framing lemmas -/

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

theorem pre_to_int32_gen_x9p (dst bufRef slot p_cur sp0 : BitVec 64)
    (v64 : BitVec 64) (rest : List (BitVec 8)) (F : SepProp) :
    (dst ↦₃₂ 0#32 ∗
      bufRef ↦₆₄ slot ∗
      slot ↦₆₄ p_cur ∗
      (slot + 8#64) ↦₆₄ BitVec.ofNat 64 ((encodeVarint v64).length + rest.length) ∗
      p_cur ↦ₛ (encodeVarint v64 ++ rest) ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗
      F) ⊢
    (memRegion dst 4 ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot p_cur (encodeVarint v64 ++ rest) ∗
      A0.pool ∗
      stackAt (sp0 - 240#64) Prost.int32MergeStack) ∗
    (memRegion (sp0 - 240#64 - 16144#64) 7792 ∗ F) := by
  have hpool : A0.pool = emp := rfl
  rw [stackAt_sub_to_int32Merge_mf14 (sp0 - 240#64), hpool, emp_sepConj]
  have hsc := sliceCursorAt_int32_gen_fold_x9p slot p_cur v64 rest
  refine Entails.trans (Q :=
    (dst ↦₃₂ 0#32 ∗
      ((bufRef ↦₆₄ slot) ∗
        ((slot ↦₆₄ p_cur) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 ((encodeVarint v64).length + rest.length)) ∗
          (p_cur ↦ₛ (encodeVarint v64 ++ rest))) ∗
        stackAt (sp0 - 240#64) Prost.int32MergeStack)) ∗
    (memRegion (sp0 - 240#64 - 16144#64) 7792 ∗ F))
    (by apply Entails.of_eq; ac_rfl) ?_
  rw [hsc]
  exact sepConj_mono_left (sepConj_mono_left (Prost.pointsTo32_entails_memRegion4 dst 0#32))

theorem post_of_int32_gen_x9p (dst bufRef slot p_cur sp0 : BitVec 64)
    (v64 : BitVec 64) (id : BitVec 32) (hid : v64.setWidth 32 = id)
    (rest : List (BitVec 8)) (F : SepProp)
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) :
    (Prost.int32MergeSpec A0).post
      ⟨.varint, dst, bufRef, slot, p_cur, encodeVarint v64 ++ rest⟩ sm sf ∗
    (memRegion (sp0 - 240#64 - 16144#64) 7792 ∗ F) =
    (⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
      (dst ↦₃₂ id ∗
        bufRef ↦₆₄ slot ∗
        slot ↦₆₄ (p_cur + BitVec.ofNat 64 (encodeVarint v64).length) ∗
        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length ∗
        p_cur ↦ₛ encodeVarint v64 ∗
        (p_cur + BitVec.ofNat 64 (encodeVarint v64).length) ↦ₛ rest ∗
        stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗
        F)) := by
  have hpool : A0.pool = emp := rfl
  dsimp only [Prost.int32MergeSpec]
  rw [mergeUint32_encode_64_x9p v64 rest, hid]
  dsimp only
  rw [hsp, sliceCursorAfter_int32_gen_unfold_x9p slot p_cur v64 rest,
      stackAt_sub_to_int32Merge_mf14 (sp0 - 240#64), hpool, emp_sepConj]
  ac_rfl

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

theorem pre_to_bytesMerge_gen_x9p (ss bufRef slot p_cur sp0 : BitVec 64)
    {k : List (BitVec 8)} (hk : k.length = 33) (rest : List (BitVec 8)) (F : SepProp) :
    (((ss + 0xf8#64) ↦₆₄ 0#64 ∗
      (ss + 0x100#64) ↦₆₄ 1#64 ∗
      (ss + 0x108#64) ↦₆₄ 0#64) ∗
      bufRef ↦₆₄ slot ∗
      ((slot ↦₆₄ p_cur) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (34 + rest.length)) ∗
        (p_cur ↦ₛ (33#8 :: k ++ rest))) ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗
      F) =
    (vecU8At A0 (ss + 248#64) 0#64 1#64 [] ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot p_cur (33#8 :: k ++ rest) ∗
      A0.pool ∗
      stackAt (sp0 - 240#64) Prost.bytesMergeStack) ∗
    (memRegion (sp0 - 240#64 - 16144#64) 7648 ∗ F) := by
  have hpool : A0.pool = emp := rfl
  rw [emptyVec_pending_eq_vecU8At_x9p A0 ss,
      sliceCursorAt_bytes_gen_fold_x9p slot p_cur hk rest,
      stackAt_sub_to_bytesMerge_mf14 (sp0 - 240#64),
      hpool, emp_sepConj]
  ac_rfl

theorem post_of_bytesMerge_gen_x9p (ss bufRef slot p_cur sp0 : BitVec 64)
    {k : List (BitVec 8)} (hk : k.length = 33) (rest : List (BitVec 8)) (F : SepProp)
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) :
    (Prost.bytesMergeRawSpec A0).post
      ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
        p_cur, 33#8 :: k ++ rest⟩ sm sf ∗
    (memRegion (sp0 - 240#64 - 16144#64) 7648 ∗ F) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
      ⌜Prost.BytesMergeCapOk cap' rest.length⌝ ∗
      (vecU8At A0 (ss + 248#64) cap' ptr' k ∗
        bufRef ↦₆₄ slot ∗
        slot ↦₆₄ (p_cur + 34#64) ∗
        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length ∗
        p_cur ↦ₛ (33#8 :: k) ∗
        (p_cur + 34#64) ↦ₛ rest ∗
        stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗
        F)) := by
  have hpool : A0.pool = emp := rfl
  dsimp only [Prost.bytesMergeRawSpec]
  rw [mergeBytes_k_x9p hk rest]
  dsimp only
  rw [hsp,
      sliceCursorAfter_bytes_gen_unfold_x9p slot p_cur hk rest,
      stackAt_sub_to_bytesMerge_mf14 (sp0 - 240#64),
      hpool, emp_sepConj]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

/-! ## Slice-cursor unfolds and folds -/

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
    have h1 := bv_ofNat_add_eq (a := 37) (b := (encodeVarint (i.setWidth 64)).length) (n :=
      0) (by omega)
    rw [Nat.add_zero] at h1
    rw [h1]
    bv_lin
  have hptr : ptr + BitVec.ofNat 64 (37 + (encodeVarint (i.setWidth 64)).length) =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 1#64 + 34#64 := by
    rw [h37]; bv_lin
  rw [hsub, hptr, pendingId_payload_eq_x9p i hk]
  simp only [List.cons_append, List.append_assoc, pointsToBytes_cons, pointsToBytes_append, hk,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin,
    show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 1#64 + 1#64 =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 2#64 by bv_lin,
    show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 2#64 + BitVec.ofNat 64
    33 =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 1#64 + 34#64 by bv_lin]
  ac_rfl

theorem sliceCursorAt_unfold_spk_none_x9p (slot ptr : BitVec 64) {k : List (BitVec 8)}
    (hk : k.length = 33) {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8)) :
    Prost.sliceCursorAt slot ptr ((GenFieldX.pendingSpk none k spk).payload ++ tail) =
      (slot ↦₆₄ ptr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (37 + (encodeVarint (spk.signExtend 64)).length +
        tail.length)) ∗
      (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 18#8) ∗
      ((ptr + 2#64) ↦ₛ (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))) := by
  unfold Prost.sliceCursorAt
  have hlen : ((GenFieldX.pendingSpk none k spk).payload ++ tail).length =
      37 + (encodeVarint (spk.signExtend 64)).length + tail.length := by
    rw [List.length_append, pendingSpk_none_payload_length_x9p hk hspk]
  rw [hlen, pendingSpk_none_payload_eq_x9p hk hspk]
  simp only [List.cons_append, List.append_assoc, pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin]

theorem sliceCursorAfter_fold_spk_none_x9p (slot ptr : BitVec 64) {k : List (BitVec 8)}
    (hk : k.length = 33) {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 18#8) ∗
      ((ptr + 2#64) ↦ₛ (33#8 :: k)) ∗
      ((ptr + 36#64) ↦₈ 24#8) ∗
      ((ptr + 37#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
      ((ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail) =
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk none k spk).payload ++ tail) tail := by
  unfold Prost.sliceCursorAfter
  have hsub : ((GenFieldX.pendingSpk none k spk).payload ++ tail).length - tail.length =
      37 + (encodeVarint (spk.signExtend 64)).length := by
    rw [List.length_append, pendingSpk_none_payload_length_x9p hk hspk]; omega
  have hm := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  have h37 : BitVec.ofNat 64 (37 + (encodeVarint (spk.signExtend 64)).length) =
      37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length := by
    have := bv_ofNat_add_eq (a := 37) (b := (encodeVarint (spk.signExtend 64)).length) (n :=
      0) (by omega)
    simpa using this
  have hptr : ptr + BitVec.ofNat 64 (37 + (encodeVarint (spk.signExtend 64)).length) =
      ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length := by
    rw [h37]; bv_lin
  rw [hsub, hptr, pendingSpk_none_payload_eq_x9p hk hspk]
  simp only [List.cons_append, List.append_assoc, pointsToBytes_cons, pointsToBytes_append, hk,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin,
    show ptr + 2#64 + 1#64 = ptr + 3#64 by bv_lin,
    show ptr + 3#64 + BitVec.ofNat 64 33 = ptr + 36#64 by bv_lin,
    show ptr + 36#64 + 1#64 = ptr + 37#64 by bv_lin]
  ac_rfl

theorem sliceCursorAt_unfold_spk_some_x9p (slot ptr : BitVec 64) (i : BitVec 32) {k : List (BitVec
    8)}
    (hk : k.length = 33) {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8)) :
    Prost.sliceCursorAt slot ptr ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail) =
      (slot ↦₆₄ ptr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (38 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length + tail.length)) ∗
      (ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 8#8) ∗
      ((ptr + 2#64) ↦ₛ (encodeVarint (i.setWidth 64) ++
        (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))))) := by
  unfold Prost.sliceCursorAt
  have hlen : ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail).length =
      38 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length + tail.length := by
    rw [List.length_append, pendingSpk_some_payload_length_x9p i hk hspk]
  rw [hlen, pendingSpk_some_payload_eq_x9p i hk hspk]
  simp only [List.cons_append, List.append_assoc, pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin]

theorem sliceCursorAfter_fold_spk_some_x9p (slot ptr : BitVec 64) (i : BitVec 32) {k : List (BitVec
    8)}
    (hk : k.length = 33) {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
      BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 8#8) ∗
      ((ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (pendingPtr2 ptr i ↦₈ 18#8) ∗
      ((pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k)) ∗
      ((pendingPtr2 ptr i + 35#64) ↦₈ 24#8) ∗
      ((pendingPtr2 ptr i + 36#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
      ((pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail) =
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail) tail
        := by
  unfold Prost.sliceCursorAfter pendingPtr2
  have hsub : ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail).length - tail.length =
      38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length := by
    rw [List.length_append, pendingSpk_some_payload_length_x9p i hk hspk]; omega
  have hm1 := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  have hm2 := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  have h38 : BitVec.ofNat 64 (38 + (encodeVarint (i.setWidth 64)).length +
      (encodeVarint (spk.signExtend 64)).length) =
      2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length := by
    have h1 := bv_ofNat_add_eq (a := 38 + (encodeVarint (i.setWidth 64)).length)
      (b := (encodeVarint (spk.signExtend 64)).length) (n := 0) (by omega)
    have h2 := bv_ofNat_add_eq (a := 38) (b := (encodeVarint (i.setWidth 64)).length) (n :=
      0) (by omega)
    simp only [Nat.add_zero] at h1 h2
    rw [h1, h2]
    bv_lin
  have hptr : ptr + BitVec.ofNat 64 (38 + (encodeVarint (i.setWidth 64)).length +
      (encodeVarint (spk.signExtend 64)).length) =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length := by
    rw [h38]; bv_lin
  rw [hsub, hptr, pendingSpk_some_payload_eq_x9p i hk hspk]
  simp only [List.cons_append, List.append_assoc, pointsToBytes_cons, pointsToBytes_append, hk,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin,
    show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 1#64 + 1#64 =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 2#64 by bv_lin,
    show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 2#64 + BitVec.ofNat 64
    33 =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 35#64 by bv_lin,
    show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 35#64 + 1#64 =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 36#64 by bv_lin]
  ac_rfl

/-! ## Arithmetic and call helpers -/

theorem wt_and_ff_eq_x9p (r2 : BitVec 64) (hx2 : r2.setWidth 8 = 2#8) :
    r2.truncate 32 &&& 255#32 = 2#32 := by
  apply BitVec.eq_of_toNat_eq
  have h := congrArg BitVec.toNat hx2
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat] at h ⊢
  change (r2.toNat % 4294967296 &&& (2 ^ 8 - 1)) = 2
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem wt_and_ff_64_eq_x9p (r2 : BitVec 64) (hx2 : r2.setWidth 8 = 2#8) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 r2) &&& 255#64) = 2#32 := by
  apply BitVec.eq_of_toNat_eq
  have h := congrArg BitVec.toNat hx2
  simp only [BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat] at h ⊢
  change (((r2.toNat % 4294967296) % 18446744073709551616 &&& (2 ^ 8 - 1)) % 4294967296) = 2
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem len_ne_zero_x9p {a n : Nat} (ha : 0 < a) (hlen : a + n < 2 ^ 32) :
    (BitVec.ofNat 64 (a + n) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at h1; omega

theorem sub1_and_add_neg1_x9p {a a' n : Nat} (ha : a = a' + 1) (hlen : a + n < 2 ^ 32) :
    BitVec.ofNat 64 (a + n) - 1#64 = BitVec.ofNat 64 (a' + n) ∧
      BitVec.ofNat 64 (a + n) + 18446744073709551615#64 = BitVec.ofNat 64 (a' + n) := by
  have h1 : BitVec.ofNat 64 (a + n) - 1#64 = BitVec.ofNat 64 (a' + n) := by
    have hsub := len_sub_mf14 (a := a) (b := 1) (n := n) (by omega) hlen
    have heq : a - 1 + n = a' + n := by omega
    rwa [heq] at hsub
  refine ⟨h1, ?_⟩
  rw [show 18446744073709551615#64 = -1#64 by rfl, ← BitVec.sub_eq_add_neg]
  exact h1

theorem subs_body_len_x9p {L n : Nat} (hlen : L + n < 2 ^ 32) :
    BitVec.ofNat 64 (L + n) - BitVec.ofNat 64 L = BitVec.ofNat 64 n ∧
      BitVec.ult (BitVec.ofNat 64 (L + n)) (BitVec.ofNat 64 L) = false ∧
      BitVec.ule (BitVec.ofNat 64 L) (BitVec.ofNat 64 (L + n)) = true := by
  refine ⟨?_, ?_, ?_⟩
  · have := len_sub_mf14 (a := L) (b := L) (n := n) (by omega) hlen
    simpa using this
  · simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  · simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega

theorem cmp_gt_tail_x9p {a n : Nat} (ha : 0 < a) (hlen : a + n < 2 ^ 32) :
    BitVec.ult (BitVec.ofNat 64 (a + n)) (BitVec.ofNat 64 n) = false ∧
      BitVec.ule (BitVec.ofNat 64 (a + n)) (BitVec.ofNat 64 n) = false ∧
      BitVec.ult (BitVec.ofNat 64 n) (BitVec.ofNat 64 (a + n)) = true ∧
      BitVec.ofNat 64 (a + n) - BitVec.ofNat 64 n = BitVec.ofNat 64 a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  · simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  · simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem int32Merge_ok_sub_x9p {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : Prost.Int32MergeOk sessionImg0.base C A0 ctl abs) :
    subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName +
        18446744073709540264#64)
      ((Prost.int32MergeSpec A0).inImage sessionImg0) := by
  have h1 := int32Merge_ok_sub_mf14 h
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h1.mono_outcome x R s0 hpc hrun hpre.2 hsp fun _ hout => hout

theorem call_frame_inv_x9p {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P ⊢ T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗
      R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.mono_pre_seedChain hP ?_
  refine SepWPp.call_inImage_frame hcall hfl hsym hpc hrun hsp hlr hspec hφ rfl hexit hpanic hnext ?_
  intro sf R' _ hoom_post
  rw [hoom] at hoom_post
  exact (not_satisfies_false_sepConj hoom_post).elim

theorem allowPanic_frame_trace_x9p {s0 sm sf : State} {F R : SepProp}
    (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (fun h' => by unfold allocFailedIn at h' ⊢; rwa [htr] at h') h

theorem close_x9p {m : Memory} {tr0 tr : List Event} {x0 : BitVec 64} {X R : SepProp}
    (htr : tr = tr0) (hx0 : x0 = 0#64) (h : m ⊨ (X ∗ emp) ∗ R) :
    m ⊨ (⌜tr = tr0 ∧ x0 = 0#64⌝ ∗ X) ∗ R := by
  rw [htr, hx0]
  simp only [and_self, pure_true, emp_sepConj]
  rw [sepConj_emp] at h
  exact h

end CryptoVerification.E2E.Record.L1GX.Leaf.MF9PAux
