/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF9PAuxW
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF14AuxW
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `SessionStructure::merge_field` on Tag 9P (`pending_pre_key`)

Verifies `mergeField9PW_spk_none_ok`, `mergeField9PW_spk_some_ok`, `mergeField9PPendingW_ok`
(over `pendingAt9P`), and `mergeField9PW_ok` (over `prostSSGXNoPqAt_x9pW`) on `SP2Ext` at
`mergeFieldStackX = 32768` with slice length `< 2 ^ 62`.
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

/-! ## Payload and cursor helpers for `pendingSpk none` and `pendingSpk (some i)` -/

theorem pendingSpk_none_payload_eq_x9p {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) :
    (GenFieldX.pendingSpk none k spk).payload =
      BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length) ::
        18#8 :: (33#8 :: k ++ (24#8 :: encodeVarint (spk.signExtend 64))) := by
  have hl : lenField 2 k = 18#8 :: 33#8 :: k := by unfold lenField; rw [hk]; rfl
  have hs : int32Field 3 spk = 24#8 :: encodeVarint (spk.signExtend 64) := by
    unfold int32Field; simp [hspk]; rfl
  have hb : pendingSpkBody none k spk =
      18#8 :: (33#8 :: k ++ (24#8 :: encodeVarint (spk.signExtend 64))) := by
    unfold pendingSpkBody optUint32Field; rw [hl, hs]; simp
  have hblen : (pendingSpkBody none k spk).length =
      36 + (encodeVarint (spk.signExtend 64)).length := by
    rw [hb]; simp only [List.length_cons, List.length_append, hk]; omega
  have hm := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  have hvar := (encodeVarint_37_57_x9p (n := 36 + (encodeVarint (spk.signExtend 64)).length)
    (by omega) (by omega)).1
  dsimp only [GenFieldX.payload]
  rw [hblen, hvar, hb, List.singleton_append]

theorem pendingSpk_none_payload_length_x9p {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) :
    (GenFieldX.pendingSpk none k spk).payload.length =
      37 + (encodeVarint (spk.signExtend 64)).length := by
  rw [pendingSpk_none_payload_eq_x9p hk hspk]
  simp only [List.length_cons, List.length_append, hk]; omega

theorem pendingSpk_some_payload_eq_x9p (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) :
    (GenFieldX.pendingSpk (some i) k spk).payload =
      BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
          (encodeVarint (spk.signExtend 64)).length) ::
        8#8 :: (encodeVarint (i.setWidth 64) ++
          (18#8 :: (33#8 :: k ++ (24#8 :: encodeVarint (spk.signExtend 64))))) := by
  have hl : lenField 2 k = 18#8 :: 33#8 :: k := by unfold lenField; rw [hk]; rfl
  have hs : int32Field 3 spk = 24#8 :: encodeVarint (spk.signExtend 64) := by
    unfold int32Field; simp [hspk]; rfl
  have hb : pendingSpkBody (some i) k spk =
      8#8 :: (encodeVarint (i.setWidth 64) ++
        (18#8 :: (33#8 :: k ++ (24#8 :: encodeVarint (spk.signExtend 64))))) := by
    unfold pendingSpkBody optUint32Field
    rw [hl, hs]
    simp [encodeKey, encodeVarint, encodeVarintAux, WireType.toNat]
  have hblen : (pendingSpkBody (some i) k spk).length =
      37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length := by
    rw [hb]; simp only [List.length_cons, List.length_append, hk]; omega
  have hm1 := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  have hm2 := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  have hvar := (encodeVarint_37_57_x9p
    (n := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (by omega) (by omega)).1
  dsimp only [GenFieldX.payload]
  rw [hblen, hvar, hb, List.singleton_append]

theorem pendingSpk_some_payload_length_x9p (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) :
    (GenFieldX.pendingSpk (some i) k spk).payload.length =
      38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length := by
  rw [pendingSpk_some_payload_eq_x9p i hk hspk]
  simp only [List.length_cons, List.length_append, hk]; omega

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
    rw [BitVec.ofNat_add]
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

theorem sliceCursorAt_unfold_spk_some_x9p (slot ptr : BitVec 64) (i : BitVec 32)
    {k : List (BitVec 8)} (hk : k.length = 33) {spk : BitVec 32} (hspk : spk ≠ 0#32)
    (tail : List (BitVec 8)) :
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

theorem sliceCursorAfter_fold_spk_some_x9p (slot ptr : BitVec 64) (i : BitVec 32)
    {k : List (BitVec 8)} (hk : k.length = 33) {spk : BitVec 32} (hspk : spk ≠ 0#32)
    (tail : List (BitVec 8)) :
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
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail) tail := by
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
    rw [BitVec.ofNat_add, BitVec.ofNat_add]; bv_lin
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
    show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 2#64 + BitVec.ofNat 64 33 =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 35#64 by bv_lin,
    show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 35#64 + 1#64 =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 36#64 by bv_lin]
  ac_rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] pendingB0_signExtend_1_x9p pendingB0_getLsbD_63_1_x9p
  pendingB0_signExtend_2_x9p pendingB0_getLsbD_63_2_x9p

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

/-! ## `GenFieldX.pendingSpk none` leaf (`mergeField9PW_spk_none_ok`) -/

private theorem final_post_entails_spk_none_x9pWA (A : RustAlloc) (ss cap' ptr' v24 : BitVec 64)
    (v : SSGX) (bufRef slot ptr : BitVec 64) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    ((ss + 288#64) ↦₃₂ spk ∗ bufRef ↦₆₄ slot ∗
      slot ↦₆₄ (ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ∗
      (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
      (ptr + 37#64) ↦ₛ encodeVarint (spk.signExtend 64) ∗
      (ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail ∗ A.pool ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      (vecU8At A (ss + 248#64) cap' ptr' k ∗ (ptr + 2#64) ↦ₛ (33#8 :: k) ∗ (ptr + 36#64) ↦₈ 24#8 ∗
        ((ss + 272#64) ↦₆₄ (v24 &&& 18446744069414584320#64 ||| 0#64) ∗ (ss + 280#64) ↦₆₄ 0#64 ∗
          memRegion (ss + 292#64) 4 ∗
          ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length) ∗
          (ptr + 1#64) ↦₈ 18#8 ∗ (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗
          (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗ (sp0 - 48#64) ↦₆₄ r24 ∗
          (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
          (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160))) ⊢
    pendingAt9P A ss (v.apply (.pendingSpk none k spk)) ∗ bufRef ↦₆₄ slot ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk none k spk).payload ++ tail) tail ∗
      A.pool ∗ stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_fold_spk_none_x9p slot ptr hk hspk tail]
  refine Entails.trans (Entails.trans (Q :=
    (vecU8At A (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 272#64) ↦₆₄ (v24 &&& 18446744069414584320#64 ||| 0#64)) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spk) ∗ memRegion (ss + 0x124#64) 4) ∗
    (bufRef ↦₆₄ slot) ∗
    (((slot ↦₆₄ (ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 18#8) ∗ ((ptr + 2#64) ↦ₛ (33#8 :: k)) ∗ ((ptr + 36#64) ↦₈ 24#8) ∗
      ((ptr + 37#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
      ((ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail)) ∗ A.pool) ∗
    ((sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗
      (sp0 - 56#64) ↦₆₄ w118 ∗ (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗
      (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗ (sp0 - 16#64) ↦₆₄ r20 ∗
      (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX))
    (by apply Entails.of_eq; ac_rfl)
    (sepConj_mono (pendingAt9P_post_fold_spk_none A ss cap' ptr' v24 v k spk)
      (bufRef_and_stackAt_mergeFieldX_fold_x9pW bufRef slot sp0
        r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 _)))
    (by apply Entails.of_eq; ac_rfl)

set_option maxHeartbeats 800000 in
theorem mergeField9PWA_spk_none_ok (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtWA img A ext) :
    MergeField9PPendingOkAtWA img A ext (fun fl => ∃ k spk, fl = .pendingSpk none k spk) := by
  dsimp only [MergeField9PPendingOkAtWA, OkAtX]
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  refine ⟨(mergeField9PPendingSpecAtWA A img (fun fl => ∃ k spk, fl = .pendingSpk none k spk)).pre
    ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ s0, R, hpre, ?_⟩
  clear hpre
  dsimp only [mergeField9PPendingSpecAtWA]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, hfld, hOk, hFresh, hlen, hF0, hsym0⟩ => ?_
  obtain ⟨k, spk, rfl⟩ := hfld
  obtain ⟨hk, hspk⟩ : k.length = 33 ∧ spk ≠ 0#32 := hOk
  obtain ⟨hp, _hpid, _hspk0⟩ := hFresh
  dsimp only [GenFieldX.tag, GenFieldX.wt, WireType.toNat] at hx1 hx2
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hm := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  rw [List.length_append, pendingSpk_none_payload_length_x9p hk hspk] at hlen
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
  have hl_ne0 := len_ne_zero_x9pW (a := 37 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hl_s1, hl_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 37 + (encodeVarint (spk.signExtend 64)).length)
    (a' := 36 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hsubL, hultL, huleL⟩ := subs_body_len_x9pW
    (L := 36 + (encodeVarint (spk.signExtend 64)).length) (n := tail.length) (by omega)
  obtain ⟨hl2_s1, hl2_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 36 + (encodeVarint (spk.signExtend 64)).length)
    (a' := 35 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult1, hule1, hult1', hsub1⟩ := cmp_gt_tail_x9pW
    (a := 36 + (encodeVarint (spk.signExtend 64)).length) (n := tail.length) (by omega) (by omega)
  obtain ⟨hl3_s1, hl3_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 1 + (encodeVarint (spk.signExtend 64)).length)
    (a' := (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult2, hule2, hult2', hsub2⟩ := cmp_gt_tail_x9pW
    (a := 1 + (encodeVarint (spk.signExtend 64)).length) (n := tail.length) (by omega) (by omega)
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
    rw [pendingAt9P_fresh_unfold A ss v hp,
        sliceCursorAt_unfold_spk_none_x9p slot ptr hk hspk tail,
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
  apply of_sepWP_frozen_mf14 hF1 hsym1 (mid := entry + bytesMergeRelOff_x9pW)
  refine step_ldr8_ro_mf14 (pc := mfStart + 52#64) (pc' := mfStart + 56#64)
    (r := Reg.gpr 11#5) (v64 := 181#64)
    rfl (by simp only [wp_norm, arm64_norm, hrun]) hfetch_ldr8 rfl
    (ea := img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) (wb := none)
    (by simp only [evalAddrMode, wp_norm, arm64_norm])
    hread9 hcan9 (by simp only [applyWriteback, wp_norm, arm64_norm]) ?_
  iterate 30 wp_step
  iterate 31 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hF2 hsym2
  have hlen_b1 : 35 + (encodeVarint (spk.signExtend 64)).length + tail.length =
      34 + (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)).length := by
    simp only [List.length_cons, List.length_append]; omega
  refine call_frame_inv_x9p
    (x := ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      ptr + 2#64, 33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail))⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7648 ∗
      ((ss + 272#64) ↦₆₄ (v24 &&& 18446744069414584320#64 ||| 0#64) ∗
        (ss + 280#64) ↦₆₄ 0#64 ∗
        (ss + 288#64) ↦₃₂ 0#32 ∗
        memRegion (ss + 292#64) 4 ∗
        ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length) ∗
        (ptr + 1#64) ↦₈ 18#8 ∗
        (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
        (s0.sp - 56#64) ↦₆₄ w118 ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
        memRegion (s0.sp - 240#64) 160))
    hcallB hF2 hsym2
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.bytesMergeRawSpecW, wp_norm, arm64_norm]; rfl)
    (by simp only [List.length_cons, List.length_append, hk]; omega)
    (by
      rw [hlen_b1]
      rw [← List.cons_append (a := 33#8)]
      rw [← pre_to_bytesMerge_gen_x9pWA A ss bufRef slot (ptr + 2#64) s0.sp hk
          (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail))]
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [Prost.X.bytesMergeRawSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm]) hm) ?_
  intro sf hpcf hrunf hspf hcsf hF3 hsym3
  simp only [wp_norm, arm64_norm] at hpcf
  have hsp_sf : sf.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm] using hspf
  rw [post_of_bytesMerge_gen_x9pWA A ss bufRef slot (ptr + 2#64) s0.sp hk
      (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)) _ _ sf
      (by simp only [wp_norm, arm64_norm])]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun htr_b => SepWPp.pure_elim fun hx0_b => ?_
  have hlen_b2 : (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)).length =
      1 + (encodeVarint (spk.signExtend 64)).length + tail.length := by
    simp only [List.length_cons, List.length_append]; omega
  conv =>
    arg 4
    rw [hlen_b2, show ptr + 2#64 + 34#64 = ptr + 36#64 by bv_lin]
    rw [pointsToBytes_cons (a := ptr + 36#64), show ptr + 36#64 + 1#64 = ptr + 37#64 by bv_lin]
    simp only [sepConj_assoc]
  have hx19_b : sf.readReg64 (Reg.gpr 19#5) = ss + 248#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.1
  have hx20_b : sf.readReg64 (Reg.gpr 20#5) = 98#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.1
  have hx21_b : sf.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
  have hx22_b : sf.readReg64 (Reg.gpr 22#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.1
  have hx23_b : sf.readReg64 (Reg.gpr 23#5) = ss := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.1
  have hx24_b : sf.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.1
  have hx25_b : sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.1
  have hx26_b : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
  have hx27_b : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
  have hx28_b : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
  have hvregs_b : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
  apply of_sepWP_frozen_mf14 hF3 hsym3 (mid := entry + int32MergeRelOff_x9pW)
  iterate 33 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf])
  intro hF4 hsym4
  refine call_frame_inv_x9p
    (x := ⟨.varint, ss + 288#64, bufRef, slot, ptr + 37#64,
      encodeVarint (spk.signExtend 64) ++ tail⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7792 ∗
      (vecU8At A (ss + 248#64) cap' ptr' k ∗
        (ptr + 2#64) ↦ₛ (33#8 :: k) ∗
        (ptr + 36#64) ↦₈ 24#8 ∗
        ((ss + 272#64) ↦₆₄ (v24 &&& 18446744069414584320#64 ||| 0#64) ∗
          (ss + 280#64) ↦₆₄ 0#64 ∗
          memRegion (ss + 292#64) 4 ∗
          ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length) ∗
          (ptr + 1#64) ↦₈ 18#8 ∗
          (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
          (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
          (s0.sp - 56#64) ↦₆₄ w118 ∗
          (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
          (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
          (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
          (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
          memRegion (s0.sp - 240#64) 160)))
    hcallI hF4 hsym4
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunf])
    (by rw [State.spAligned]; simp only [wp_norm, arm64_norm, hsp_sf]
        simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.int32MergeSpecW, wp_norm, arm64_norm, hsp_sf]; rfl)
    (by rw [List.length_append]; omega)
    (by
      refine Entails.trans ?_
        (pre_to_int32_gen_x9pWA A (ss + 288#64) bufRef slot (ptr + 37#64) s0.sp
          (spk.signExtend 64) tail _)
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf' _ hm => by
      dsimp only [Prost.X.int32MergeSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm, htr_b]) hm) ?_
  intro sf2 hpcf2 hrunf2 hspf2 hcsf2 _ _
  simp only [wp_norm, arm64_norm] at hpcf2
  rw [post_of_int32_gen_x9pWA A (ss + 288#64) bufRef slot (ptr + 37#64) s0.sp
      (spk.signExtend 64) spk (setWidth32_signExtend64_x9p spk) tail _
      _ sf2 (by simp only [wp_norm, arm64_norm, hsp_sf])]
  refine SepWPp.pure_elim fun htr_sf => SepWPp.pure_elim fun hx0_sf => ?_
  have htr_sf' : sf2.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htr_b] using htr_sf
  have hx0_sf' : sf2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf
  have hx21_sf : sf2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm, hx21_b] using hcsf2.2.2.1
  have hx24_sf : sf2.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx24_b] using hcsf2.2.2.2.2.2.1
  have hx26_sf : sf2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26_b] using hcsf2.2.2.2.2.2.2.2.1
  have hx27_sf : sf2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27_b] using hcsf2.2.2.2.2.2.2.2.2.1
  have hx28_sf : sf2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28_b] using hcsf2.2.2.2.2.2.2.2.2.2.1
  have hvregs_sf : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sf2 = calleeSavedVRegs sf := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregs_b
  have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hsp_sf] using hspf2
  have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) =
      false := by
    simp [BitVec.ult]
  have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) =
      true := by
    simp [BitVec.ule]
  apply SepWPp.of_sepWP_ret
  iterate 19 wp_step
  apply SepWP.fold (final_post_entails_spk_none_x9pWA A ss cap' ptr' v24 v bufRef slot ptr hk hspk tail
      s0.sp
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

theorem mergeField9PW_spk_none_ok (img : Obj.Image)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtW img ext) :
    MergeField9PPendingOkAtW img ext (fun fl => ∃ k spk, fl = .pendingSpk none k spk) := by
  have hpool : A0.pool = emp := rfl
  refine okAtX_of_eq_pre_post_mf14 (mergeField9PWA_spk_none_ok img A0 ext hLoads hC)
    (fun _ _ => by simp only [mergeField9PPendingSpecAtWA, mergeField9PPendingSpecAtW, hpool, emp_sepConj])
    (fun _ _ _ => by simp only [mergeField9PPendingSpecAtWA, mergeField9PPendingSpecAtW, hpool, emp_sepConj])
    rfl rfl rfl

/-! ## `GenFieldX.pendingSpk (some i)` leaf (`mergeField9PW_spk_some_ok`) -/

private theorem final_post_entails_spk_some_x9pWA (A : RustAlloc) (ss cap' ptr' : BitVec 64) (v : SSGX)
    (bufRef slot ptr : BitVec 64) (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    ((ss + 288#64) ↦₃₂ spk ∗ bufRef ↦₆₄ slot ∗
      slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ∗
      (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
      (pendingPtr2 ptr i + 36#64) ↦ₛ encodeVarint (spk.signExtend 64) ∗
      (pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail ∗ A.pool ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      (vecU8At A (ss + 248#64) cap' ptr' k ∗ (pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k) ∗
        (pendingPtr2 ptr i + 35#64) ↦₈ 24#8 ∗
        ((ss + 276#64) ↦₃₂ i ∗ (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
          pendingPtr2 ptr i ↦₈ 18#8 ∗
          ((ss + 272#64) ↦₃₂ 1#32 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗ memRegion (ss + 292#64) 4 ∗
            ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
              (encodeVarint (spk.signExtend 64)).length) ∗ (ptr + 1#64) ↦₈ 8#8 ∗
            (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗
            (sp0 - 56#64) ↦₆₄ w118 ∗ (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗
            (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗ (sp0 - 16#64) ↦₆₄ r20 ∗
            (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160)))) ⊢
    pendingAt9P A ss (v.apply (.pendingSpk (some i) k spk)) ∗ bufRef ↦₆₄ slot ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail) tail ∗
      A.pool ∗ stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_fold_spk_some_x9p slot ptr i hk hspk tail]
  refine Entails.trans (Entails.trans (Q :=
    (vecU8At A (ss + 0xf8#64) cap' ptr' k ∗ ((ss + 0x110#64) ↦₃₂ 1#32) ∗
      ((ss + 0x114#64) ↦₃₂ i) ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spk) ∗
      memRegion (ss + 0x124#64) 4) ∗ (bufRef ↦₆₄ slot) ∗
    (((slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
      BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length)) ∗ ((ptr + 1#64) ↦₈ 8#8) ∗
      ((ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗ (pendingPtr2 ptr i ↦₈ 18#8) ∗
      ((pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k)) ∗ ((pendingPtr2 ptr i + 35#64) ↦₈ 24#8) ∗
      ((pendingPtr2 ptr i + 36#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
      ((pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail)) ∗ A.pool) ∗
    ((sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗
      (sp0 - 56#64) ↦₆₄ w118 ∗ (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗
      (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗ (sp0 - 16#64) ↦₆₄ r20 ∗
      (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX))
    (by apply Entails.of_eq; ac_rfl)
    (sepConj_mono (pendingAt9P_post_fold_spk_some A ss cap' ptr' v i k spk)
      (bufRef_and_stackAt_mergeFieldX_fold_x9pW bufRef slot sp0
        r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 _)))
    (by apply Entails.of_eq; ac_rfl)

set_option maxHeartbeats 800000 in
theorem mergeField9PWA_spk_some_ok (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtWA img A ext) :
    MergeField9PPendingOkAtWA img A ext (fun fl => ∃ i k spk, fl = .pendingSpk (some i) k spk) := by
  dsimp only [MergeField9PPendingOkAtWA, OkAtX]
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  refine ⟨(mergeField9PPendingSpecAtWA A img
    (fun fl => ∃ i k spk, fl = .pendingSpk (some i) k spk)).pre
    ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ s0, R, hpre, ?_⟩
  clear hpre
  dsimp only [mergeField9PPendingSpecAtWA]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, hfld, hOk, hFresh, hlen, hF0, hsym0⟩ => ?_
  obtain ⟨i, k, spk, rfl⟩ := hfld
  obtain ⟨hk, hspk⟩ : k.length = 33 ∧ spk ≠ 0#32 := hOk
  obtain ⟨hp, _hpid, _hspk0⟩ := hFresh
  dsimp only [GenFieldX.tag, GenFieldX.wt, WireType.toNat] at hx1 hx2
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hm1 := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  have hm2 := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  rw [List.length_append, pendingSpk_some_payload_length_x9p i hk hspk] at hlen
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
  have hl_ne0 := len_ne_zero_x9pW
    (a := 38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hl_s1, hl_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (a' := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hsubL, hultL, huleL⟩ := subs_body_len_x9pW
    (L := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega)
  obtain ⟨hl2_s1, hl2_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (a' := 36 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult1, hule1, hult1', hsub1⟩ := cmp_gt_tail_x9pW
    (a := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hl3_s1, hl3_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 36 + (encodeVarint (spk.signExtend 64)).length)
    (a' := 35 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult2, hule2, hult2', hsub2⟩ := cmp_gt_tail_x9pW
    (a := 36 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hl4_s1, hl4_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 1 + (encodeVarint (spk.signExtend 64)).length)
    (a' := (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult3, hule3, hult3', hsub3⟩ := cmp_gt_tail_x9pW
    (a := 1 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
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
    rw [pendingAt9P_fresh_unfold A ss v hp,
        sliceCursorAt_unfold_spk_some_x9p slot ptr i hk hspk tail,
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
  have hlen_i1 : 36 + (encodeVarint (i.setWidth 64)).length +
      (encodeVarint (spk.signExtend 64)).length + tail.length =
      (encodeVarint (i.setWidth 64)).length +
        (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))).length := by
    simp only [List.length_cons, List.length_append, hk]; omega
  refine call_frame_inv_x9p
    (x := ⟨.varint, ss + 276#64, bufRef, slot, ptr + 2#64,
      encodeVarint (i.setWidth 64) ++
        (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail))))⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7792 ∗
      ((ss + 0xf8#64) ↦₆₄ 0#64 ∗ (ss + 0x100#64) ↦₆₄ 1#64 ∗ (ss + 0x108#64) ↦₆₄ 0#64) ∗
      (ss + 272#64) ↦₃₂ 1#32 ∗
      (ss + 280#64) ↦₆₄ 0#64 ∗
      (ss + 288#64) ↦₃₂ 0#32 ∗
      memRegion (ss + 292#64) 4 ∗
      ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length) ∗
      (ptr + 1#64) ↦₈ 8#8 ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 56#64) ↦₆₄ w118 ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
      memRegion (s0.sp - 240#64) 160)
    hcallI hF2 hsym2
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.int32MergeSpecW, wp_norm, arm64_norm]; rfl)
    (by simp only [List.length_append, List.length_cons, hk]; omega)
    (by
      refine Entails.trans ?_
        (pre_to_int32_gen_x9pWA A (ss + 276#64) bufRef slot (ptr + 2#64) s0.sp
          (i.setWidth 64)
          (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))) _)
      rw [split_272_x9p ss, hlen_i1]
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [Prost.X.int32MergeSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm]) hm) ?_
  intro sf hpcf hrunf hspf hcsf hF3 hsym3
  simp only [wp_norm, arm64_norm] at hpcf
  have hsp_sf : sf.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm] using hspf
  rw [post_of_int32_gen_x9pWA A (ss + 276#64) bufRef slot (ptr + 2#64) s0.sp
      (i.setWidth 64) i (setWidth32_setWidth64_x9p i)
      (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))) _
      _ sf (by simp only [wp_norm, arm64_norm])]
  refine SepWPp.pure_elim fun htr_i => SepWPp.pure_elim fun hx0_i => ?_
  have hlen_i2 :
      (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))).length =
      36 + (encodeVarint (spk.signExtend 64)).length + tail.length := by
    simp only [List.cons_append, List.length_cons, List.length_append, hk]; omega
  conv =>
    arg 4
    rw [hlen_i2, show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length =
      pendingPtr2 ptr i from rfl,
      pointsToBytes_cons (a := pendingPtr2 ptr i)]
    simp only [sepConj_assoc]
  have hx19_i : sf.readReg64 (Reg.gpr 19#5) = ss + 248#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.1
  have hx20_i : sf.readReg64 (Reg.gpr 20#5) = 98#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.1
  have hx21_i : sf.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
  have hx22_i : sf.readReg64 (Reg.gpr 22#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.1
  have hx23_i : sf.readReg64 (Reg.gpr 23#5) = ss := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.1
  have hx24_i : sf.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.1
  have hx25_i : sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.1
  have hx26_i : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
  have hx27_i : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
  have hx28_i : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
  have hvregs_i : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
  apply of_sepWP_frozen_mf14 hF3 hsym3 (mid := entry + bytesMergeRelOff_x9pW)
  iterate 35 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf])
  intro hF4 hsym4
  have hlen_b1 : 35 + (encodeVarint (spk.signExtend 64)).length + tail.length =
      34 + (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)).length := by
    simp only [List.length_cons, List.length_append]; omega
  refine call_frame_inv_x9p
    (x := ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      pendingPtr2 ptr i + 1#64, 33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail))⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7648 ∗
      (ss + 276#64) ↦₃₂ i ∗
      (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
      pendingPtr2 ptr i ↦₈ 18#8 ∗
      ((ss + 272#64) ↦₃₂ 1#32 ∗
        (ss + 280#64) ↦₆₄ 0#64 ∗
        (ss + 288#64) ↦₃₂ 0#32 ∗
        memRegion (ss + 292#64) 4 ∗
        ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
          (encodeVarint (spk.signExtend 64)).length) ∗
        (ptr + 1#64) ↦₈ 8#8 ∗
        (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
        (s0.sp - 56#64) ↦₆₄ w118 ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
        memRegion (s0.sp - 240#64) 160))
    hcallB hF4 hsym4
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunf])
    (by rw [State.spAligned]; simp only [wp_norm, arm64_norm, hsp_sf]
        simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.bytesMergeRawSpecW, wp_norm, arm64_norm, hsp_sf]; rfl)
    (by simp only [List.length_cons, List.length_append, hk]; omega)
    (by
      rw [hlen_b1, ← List.cons_append (a := 33#8)]
      rw [← pre_to_bytesMerge_gen_x9pWA A ss bufRef slot (pendingPtr2 ptr i + 1#64) s0.sp hk
          (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail))]
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf' _ hm => by
      dsimp only [Prost.X.bytesMergeRawSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm, htr_i]) hm) ?_
  intro sf2 hpcf2 hrunf2 hspf2 hcsf2 hF5 hsym5
  simp only [wp_norm, arm64_norm] at hpcf2
  have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hsp_sf] using hspf2
  rw [post_of_bytesMerge_gen_x9pWA A ss bufRef slot (pendingPtr2 ptr i + 1#64) s0.sp hk
      (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)) _
      _ sf2 (by simp only [wp_norm, arm64_norm, hsp_sf])]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun htr_b => SepWPp.pure_elim fun hx0_b => ?_
  have htr_b' : sf2.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htr_i] using htr_b
  have hlen_b2 : (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)).length =
      1 + (encodeVarint (spk.signExtend 64)).length + tail.length := by
    simp only [List.length_cons, List.length_append]; omega
  conv =>
    arg 4
    rw [hlen_b2, show pendingPtr2 ptr i + 1#64 + 34#64 = pendingPtr2 ptr i + 35#64 by bv_lin,
      pointsToBytes_cons (a := pendingPtr2 ptr i + 35#64),
      show pendingPtr2 ptr i + 35#64 + 1#64 = pendingPtr2 ptr i + 36#64 by bv_lin]
    simp only [sepConj_assoc]
  have hx19_b : sf2.readReg64 (Reg.gpr 19#5) = ss + 248#64 := by
    simpa only [wp_norm, arm64_norm, hx19_i] using hcsf2.1
  have hx20_b : sf2.readReg64 (Reg.gpr 20#5) = 98#64 := by
    simpa only [wp_norm, arm64_norm, hx20_i] using hcsf2.2.1
  have hx21_b : sf2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm, hx21_i] using hcsf2.2.2.1
  have hx22_b : sf2.readReg64 (Reg.gpr 22#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm, hx22_i] using hcsf2.2.2.2.1
  have hx23_b : sf2.readReg64 (Reg.gpr 23#5) = ss := by
    simpa only [wp_norm, arm64_norm, hx23_i] using hcsf2.2.2.2.2.1
  have hx24_b : sf2.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx24_i] using hcsf2.2.2.2.2.2.1
  have hx25_b : sf2.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := by
    simpa only [wp_norm, arm64_norm, hx25_i] using hcsf2.2.2.2.2.2.2.1
  have hx26_b : sf2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26_i] using hcsf2.2.2.2.2.2.2.2.1
  have hx27_b : sf2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27_i] using hcsf2.2.2.2.2.2.2.2.2.1
  have hx28_b : sf2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28_i] using hcsf2.2.2.2.2.2.2.2.2.2.1
  have hvregs_b : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sf2 = calleeSavedVRegs sf := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregs_i
  apply of_sepWP_frozen_mf14 hF5 hsym5 (mid := entry + int32MergeRelOff_x9pW)
  iterate 33 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf2])
  intro hF6 hsym6
  refine call_frame_inv_x9p
    (x := ⟨.varint, ss + 288#64, bufRef, slot, pendingPtr2 ptr i + 36#64,
      encodeVarint (spk.signExtend 64) ++ tail⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7792 ∗
      (vecU8At A (ss + 248#64) cap' ptr' k ∗
        (pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k) ∗
        (pendingPtr2 ptr i + 35#64) ↦₈ 24#8 ∗
        ((ss + 276#64) ↦₃₂ i ∗
          (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
          pendingPtr2 ptr i ↦₈ 18#8 ∗
          ((ss + 272#64) ↦₃₂ 1#32 ∗
            (ss + 280#64) ↦₆₄ 0#64 ∗
            memRegion (ss + 292#64) 4 ∗
            ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
              (encodeVarint (spk.signExtend 64)).length) ∗
            (ptr + 1#64) ↦₈ 8#8 ∗
            (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
            (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
            (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
            (s0.sp - 56#64) ↦₆₄ w118 ∗
            (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
            (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
            (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
            (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
            (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
            (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
            memRegion (s0.sp - 240#64) 160))))
    hcallI hF6 hsym6
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunf2])
    (by rw [State.spAligned]; simp only [wp_norm, arm64_norm, hsp_sf2]
        simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.int32MergeSpecW, wp_norm, arm64_norm, hsp_sf2]; rfl)
    (by rw [List.length_append]; omega)
    (by
      refine Entails.trans ?_
        (pre_to_int32_gen_x9pWA A (ss + 288#64) bufRef slot (pendingPtr2 ptr i + 36#64) s0.sp
          (spk.signExtend 64) tail _)
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf' _ hm => by
      dsimp only [Prost.X.int32MergeSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm, htr_b']) hm) ?_
  intro sf3 hpcf3 hrunf3 hspf3 hcsf3 _ _
  simp only [wp_norm, arm64_norm] at hpcf3
  rw [post_of_int32_gen_x9pWA A (ss + 288#64) bufRef slot (pendingPtr2 ptr i + 36#64) s0.sp
      (spk.signExtend 64) spk (setWidth32_signExtend64_x9p spk) tail _
      _ sf3 (by simp only [wp_norm, arm64_norm, hsp_sf2])]
  refine SepWPp.pure_elim fun htr_sf => SepWPp.pure_elim fun hx0_sf => ?_
  have htr_sf' : sf3.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htr_b'] using htr_sf
  have hx0_sf' : sf3.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf
  have hx21_sf : sf3.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm, hx21_b] using hcsf3.2.2.1
  have hx24_sf : sf3.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx24_b] using hcsf3.2.2.2.2.2.1
  have hx26_sf : sf3.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26_b] using hcsf3.2.2.2.2.2.2.2.1
  have hx27_sf : sf3.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27_b] using hcsf3.2.2.2.2.2.2.2.2.1
  have hx28_sf : sf3.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28_b] using hcsf3.2.2.2.2.2.2.2.2.2.1
  have hvregs_sf : calleeSavedVRegs sf3 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sf3 = calleeSavedVRegs sf2 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf3.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregs_b
  have hsp_sf3 : sf3.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hsp_sf2] using hspf3
  have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) =
      false := by
    simp [BitVec.ult]
  have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) =
      true := by
    simp [BitVec.ule]
  apply SepWPp.of_sepWP_ret
  iterate 19 wp_step
  apply SepWP.fold (final_post_entails_spk_some_x9pWA A ss cap' ptr' v bufRef slot ptr i hk hspk tail
      s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) w118
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
    (sepConj_emp _).symm
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf3])
  refine ⟨fun hmf => close_x9p (by simp only [wp_norm, arm64_norm, htr_sf'])
      (by simp only [wp_norm, arm64_norm]) hmf,
    by simp only [wp_norm, arm64_norm],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm, hx26_sf, hx27_sf,
      hx28_sf]; exact hvregs_sf⟩

theorem mergeField9PW_spk_some_ok (img : Obj.Image)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtW img ext) :
    MergeField9PPendingOkAtW img ext (fun fl => ∃ i k spk, fl = .pendingSpk (some i) k spk) := by
  have hpool : A0.pool = emp := rfl
  refine okAtX_of_eq_pre_post_mf14 (mergeField9PWA_spk_some_ok img A0 ext hLoads hC)
    (fun _ _ => by simp only [mergeField9PPendingSpecAtWA, mergeField9PPendingSpecAtW, hpool, emp_sepConj])
    (fun _ _ _ => by simp only [mergeField9PPendingSpecAtWA, mergeField9PPendingSpecAtW, hpool, emp_sepConj])
    rfl rfl rfl

/-! ## Combined tag-9P leaf contracts -/

def mergeField9PSpecAtWA (A : RustAlloc) (img : Obj.Image) (P : GenFieldX → Prop) :
    Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostSSGXNoPqAt_x9pW A x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ A.pool ∗
      stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostSSGXNoPqAt_x9pW A x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗ A.pool ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

def MergeField9POkAtWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (P : GenFieldX → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeField9PSpecAtWA A img P)

theorem mergeField9PPendingSpecAtWA_pre_iff (A : RustAlloc) (img : Obj.Image)
    {P : GenFieldX → Prop} {x : MergeFieldXGhost} {s : State} {R : SepProp} :
    (s.mem ⊨ (mergeField9PPendingSpecAtWA A img P).pre x s ∗ R) ↔
      P x.fld ∧ (s.mem ⊨ (mergeField9PPendingSpecAtWA A img (fun _ => True)).pre x s ∗ R) := by
  simp only [mergeField9PPendingSpecAtWA, sepConj_assoc, satisfies_pure_sepConj]; tauto

theorem mergeField9PPendingOkAtWA_of_imp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {P Q : GenFieldX → Prop}
    (hP : MergeField9PPendingOkAtWA img A ext P) (hQP : ∀ fl, Q fl → P fl) :
    MergeField9PPendingOkAtWA img A ext Q := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hq, hpre⟩ := (mergeField9PPendingSpecAtWA_pre_iff A img).mp hpre
  exact hP.mono_outcome x R s0 hpc hrun
    ((mergeField9PPendingSpecAtWA_pre_iff A img).mpr ⟨hQP _ hq, hpre⟩) hal fun _ hout => hout

theorem mergeField9PPendingOkAtWA_or {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {P Q : GenFieldX → Prop}
    (hP : MergeField9PPendingOkAtWA img A ext P) (hQ : MergeField9PPendingOkAtWA img A ext Q) :
    MergeField9PPendingOkAtWA img A ext (fun fl => P fl ∨ Q fl) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hpq, hpre⟩ := (mergeField9PPendingSpecAtWA_pre_iff A img).mp hpre
  rcases hpq with hp | hq
  · exact hP.mono_outcome x R s0 hpc hrun
      ((mergeField9PPendingSpecAtWA_pre_iff A img).mpr ⟨hp, hpre⟩) hal fun _ hout => hout
  · exact hQ.mono_outcome x R s0 hpc hrun
      ((mergeField9PPendingSpecAtWA_pre_iff A img).mpr ⟨hq, hpre⟩) hal fun _ hout => hout

theorem mergeField9POkAtWA_of_pending {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {P : GenFieldX → Prop}
    (hP9 : ∀ fl, P fl → (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk))
    (hP : MergeField9PPendingOkAtWA img A ext P) :
    MergeField9POkAtWA img A ext P := by
  refine okAtX_of_imp_frame_mf14 hP (fun _ _ _ _ => rfl) allocPanic_frame_mf14 ?_ (fun _ _ _ => rfl)
  intro x s0 R hpre
  simp only [mergeField9PSpecAtWA, prostSSGXNoPqAt_eq_pending_sep_rest_x9pW A,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨h0, h1, h2, h3, h4, hp, hok, hfr, hlen, hfz, hsym⟩, hm⟩ := hpre
  have hfl := hP9 x.fld hp
  have hfr' : x.v.base.pending = none ∧ x.v.ext.pid = none ∧ x.v.ext.spkId = 0#32 := by
    rcases hfl with ⟨i, k, hfl'⟩ | ⟨o, k, spk, hfl'⟩ <;>
      (rw [hfl'] at hfr; obtain ⟨hp0, he0⟩ := hfr; rw [he0]; exact ⟨hp0, rfl, rfl⟩)
  refine ⟨x, prostSSRestNoPq_x9p A x.ss x.v, ?_, ?_⟩
  · simp only [mergeField9PPendingSpecAtWA, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨h0, h1, h2, h3, h4, hp, hok, hfr', hlen, hfz, hsym⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf hpost
    simp only [mergeField9PSpecAtWA, prostSSGXNoPqAt_eq_pending_sep_rest_x9pW A,
      prostSSRestNoPq_x9p_apply_pending A x.ss x.v hfl]
    simp only [mergeField9PPendingSpecAtWA] at hpost
    convert hpost using 1; ac_rfl

theorem mergeField9PPendingWA_ok (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtWA img A ext) :
    MergeField9PPendingOkAtWA img A ext
      (fun fl => (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk)) := by
  refine mergeField9PPendingOkAtWA_of_imp (mergeField9PPendingOkAtWA_or
    (mergeField9PWA_id_ok img A ext hLoads hC) (mergeField9PPendingOkAtWA_or
      (mergeField9PWA_spk_none_ok img A ext hLoads hC)
      (mergeField9PWA_spk_some_ok img A ext hLoads hC))) ?_
  rintro fl (⟨i, k, rfl⟩ | ⟨o, k, spk, rfl⟩)
  · exact Or.inl ⟨i, k, rfl⟩
  · cases o with
    | none => exact Or.inr (Or.inl ⟨k, spk, rfl⟩)
    | some i => exact Or.inr (Or.inr ⟨i, k, spk, rfl⟩)

theorem mergeField9PWA_ok (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtWA img A ext) :
    MergeField9POkAtWA img A ext
      (fun fl => (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk)) :=
  mergeField9POkAtWA_of_pending (fun _ h => h) (mergeField9PPendingWA_ok img A ext hLoads hC)

theorem mergeField9PPendingW_ok (img : Obj.Image)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtW img ext) :
    MergeField9PPendingOkAtW img ext
      (fun fl => (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk)) := by
  have hpool : A0.pool = emp := rfl
  refine okAtX_of_eq_pre_post_mf14 (mergeField9PPendingWA_ok img A0 ext hLoads hC)
    (fun _ _ => by simp only [mergeField9PPendingSpecAtWA, mergeField9PPendingSpecAtW, hpool, emp_sepConj])
    (fun _ _ _ => by simp only [mergeField9PPendingSpecAtWA, mergeField9PPendingSpecAtW, hpool, emp_sepConj])
    rfl rfl rfl

theorem mergeField9PW_ok (img : Obj.Image)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtW img ext) :
    MergeField9POkAtW img ext
      (fun fl => (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk)) :=
  mergeField9POkAtW_of_pending (fun _ h => h) (mergeField9PPendingW_ok img ext hLoads hC)

/-- Lift `MergeField9POkAtWA` (over `prostSSGXNoPqAt_x9pW`) to `MergeFieldQOkAtWA` by framing
`vecU8 A (x.ss + 0x78#64) x.v.ext.pq` via `prostSSGQAt_eq_x9pW_sep_pq`. -/
theorem mergeFieldQOkAtWA_of_9P (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (h9P : MergeField9POkAtWA img A ext
      (fun fl => (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk))) :
    MergeFieldQOkAtWA img A ext
      (fun fl => (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk)) := by
  refine okAtX_of_imp_frame_mf14 h9P (fun _ _ _ _ => rfl) allocPanic_frame_mf14 ?_ (fun _ _ _ => rfl)
  intro x s0 R hpre
  dsimp only [mergeFieldQSpecAtWA] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hP, hok, hfresh, hlen, hF, hsym⟩, hmem⟩
  have hfx : ∃ fx : GenFieldX,
      ((∃ i k, fx = .pendingId i k) ∨ (∃ o k spk, fx = .pendingSpk o k spk)) ∧
      x.fld = GenFieldX.toGenFieldQ fx := by
    rcases hP with ⟨i, k, hfl⟩ | ⟨o, k, spk, hfl⟩
    · exact ⟨.pendingId i k, Or.inl ⟨i, k, rfl⟩, hfl⟩
    · exact ⟨.pendingSpk o k spk, Or.inr ⟨o, k, spk, rfl⟩, hfl⟩
  rcases hfx with ⟨fx, hfxP, hfl⟩
  rw [hfl] at hx1 hx2 hok hfresh hlen hmem
  rw [toGenFieldQ_tag] at hx1; rw [toGenFieldQ_wt] at hx2; rw [toGenFieldQ_payload] at hlen hmem
  have hnpq : GenFieldX.NoPq fx := by rcases hfxP with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> trivial
  have hok_fx : fx.Ok := (toGenFieldQ_ok fx).mp hok
  have hfresh_fx : fx.Fresh x.v.toSSGX := ((toGenFieldQ_fresh_iff x.v fx).mp hfresh).1
  refine ⟨⟨x.ss, x.v.toSSGX, fx, x.bufRef, x.slot, x.ptr, x.tail⟩,
    vecU8 A (x.ss + 0x78#64) x.v.ext.pq, ?_, ?_⟩
  · dsimp only [mergeField9PSpecAtWA]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hfxP, hok_fx, hfresh_fx, hlen, hF, hsym⟩, ?_⟩
    rw [prostSSGQAt_eq_x9pW_sep_pq A x.ss x.v] at hmem
    convert hmem using 1; ac_rfl
  · intro sf hpost
    dsimp only [mergeField9PSpecAtWA] at hpost
    dsimp only [mergeFieldQSpecAtWA]
    rw [hfl, toGenFieldQ_payload,
      prostSSGQAt_eq_x9pW_sep_pq A x.ss (x.v.apply (GenFieldX.toGenFieldQ fx)),
      apply_toGenFieldQ_toSSGX x.v fx hnpq, apply_toGenFieldQ_pq x.v fx hnpq]
    convert hpost using 1; ac_rfl

end Symbolic.Swarm.TRREF.B3DeserQ
