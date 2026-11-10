/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Record.L1GX.Frame
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF9PAux.Helpers
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF9PAux.PendingId
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF9PAux.PendingSpkNone
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF9PAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# `SessionStructure::merge_field` on tag 9 (`pending_pre_key`)

Re-exports `mergeFieldX9P_ok` for `<SessionStructure as prost::Message>::merge_field` (`0x581c`)
on PQXDH `pending_pre_key` fields (`GenFieldX.pendingId` and `GenFieldX.pendingSpk`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX9P

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.L1GX.Leaf.MF9PAux
open CryptoVerification.E2E.Record.Serialization (OkAt allocPanic)

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] pendingB0_signExtend_1_x9p pendingB0_getLsbD_63_1_x9p
  pendingB0_signExtend_2_x9p pendingB0_getLsbD_63_2_x9p

private theorem final_post_entails_spk_some_x9p (ss cap' ptr' : BitVec 64) (v : SSG)
    (bufRef slot ptr : BitVec 64) (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    ((ss + 288#64) ↦₃₂ spk ∗
      bufRef ↦₆₄ slot ∗
      slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ∗
      (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
      (pendingPtr2 ptr i + 36#64) ↦ₛ encodeVarint (spk.signExtend 64) ∗
      (pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗
      (vecU8At A0 (ss + 248#64) cap' ptr' k ∗
        (pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k) ∗
        (pendingPtr2 ptr i + 35#64) ↦₈ 24#8 ∗
        ((ss + 276#64) ↦₃₂ i ∗
          (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
          pendingPtr2 ptr i ↦₈ 18#8 ∗
          ((ss + 272#64) ↦₃₂ 1#32 ∗
            (ss + 280#64) ↦₆₄ 0#64 ∗
            memRegion (ss + 292#64) 4 ∗
            prostSSRest_x9p A0 ss v ∗
            ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
              (encodeVarint (spk.signExtend 64)).length) ∗
            (ptr + 1#64) ↦₈ 8#8 ∗
            (sp0 - 80#64) ↦₆₄ r29 ∗
            (sp0 - 72#64) ↦₆₄ r30 ∗
            (sp0 - 64#64) ↦₆₄ r25 ∗
            (sp0 - 56#64) ↦₆₄ w118 ∗
            (sp0 - 48#64) ↦₆₄ r24 ∗
            (sp0 - 40#64) ↦₆₄ r23 ∗
            (sp0 - 32#64) ↦₆₄ r22 ∗
            (sp0 - 24#64) ↦₆₄ r21 ∗
            (sp0 - 16#64) ↦₆₄ r20 ∗
            (sp0 - 8#64) ↦₆₄ r19 ∗
            memRegion (sp0 - 240#64) 160)))) ⊢
    prostSSGXAt A0 ss (SSGX.apply ⟨v, ExtraG.empty⟩ (.pendingSpk (some i) k spk)) ∗
      bufRef ↦₆₄ slot ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail) tail ∗
      stackAt sp0 mergeFieldStack := by
  rw [← sliceCursorAfter_fold_spk_some_x9p slot ptr i hk hspk tail]
  refine Entails.trans (Q :=
    (vecU8At A0 (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 0x110#64) ↦₃₂ 1#32) ∗ ((ss + 0x114#64) ↦₃₂ i) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spk) ∗
      memRegion (ss + 0x124#64) 4 ∗ prostSSRest_x9p A0 ss v) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
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
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail)) ∗
    ((sp0 - 80#64) ↦₆₄ r29 ∗
      (sp0 - 72#64) ↦₆₄ r30 ∗
      (sp0 - 64#64) ↦₆₄ r25 ∗
      (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗
      (sp0 - 40#64) ↦₆₄ r23 ∗
      (sp0 - 32#64) ↦₆₄ r22 ∗
      (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗
      (sp0 - 8#64) ↦₆₄ r19 ∗
      memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14))
    (by apply Entails.of_eq; ac_rfl) ?_
  exact sepConj_mono (prostSSGXAt_post_fold_spk_some_x9p A0 ss cap' ptr' v i k spk)
    (sepConj_mono_right (sepConj_mono_right
      (stackAt_mergeField_fold_mf14 sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19)))

theorem mergeFieldX9P_spk_some_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) :
    MergeFieldXOk C ctl (fun fl => ∃ i k spk, fl = .pendingSpk (some i) k spk) abs := by
  dsimp only [MergeFieldXOk, OkAt]
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, ⟨v, e⟩, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  refine ⟨(mergeFieldXSpec (fun fl => ∃ i k spk, fl = .pendingSpk (some i) k spk)).pre
    ⟨ss, ⟨v, e⟩, fld, bufRef, slot, ptr, tail⟩ s0, R, hpre, ?_⟩
  clear hpre
  dsimp only [mergeFieldXSpec]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, hfld, hOk, hFresh, hlen, hF0, hsym0⟩ => ?_
  obtain ⟨i, k, spk, rfl⟩ := hfld
  obtain ⟨hk, hspk⟩ : k.length = 33 ∧ spk ≠ 0#32 := hOk
  obtain ⟨hp, he⟩ := hFresh
  dsimp only at hp he
  subst he
  dsimp only [GenFieldX.tag, GenFieldX.wt, WireType.toNat] at hx1 hx2
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hm1 := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  have hm2 := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  rw [List.length_append, pendingSpk_some_payload_length_x9p i hk hspk] at hlen
  rw [State.spAligned] at hsp_align
  have hb : sessionImg0.base &&& 4095#64 = 0#64 :=
    base_aligned_of_loads E2E.Record.loads_sessionImg0
  have hcallB := bytesMerge_ok_sub_mf14 hC.2.2.1
  have hcallI := int32Merge_ok_sub_x9p hC.2.1
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
    (b := sessionImg0.base) (H := H)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x581c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 4)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5820
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 8)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5824
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 12)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5828
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 16)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x582c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 20)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5830
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 24)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5834
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 28)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5838
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 32)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x583c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 36)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5840
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 40)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5844
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 44)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5848
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 48)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x584c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 52)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5850
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 56)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5854
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 60)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5858
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 788)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b30
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 792)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b34
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 796)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b38
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 800)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b3c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 804)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b40
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 808)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b44
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 812)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b48
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 816)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b4c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 820)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b50
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 824)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b54
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 828)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b58
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 832)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b5c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 836)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b60
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 840)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b64
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 844)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b68
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 848)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b6c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 852)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b70
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 856)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b74
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 860)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b78
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 864)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b7c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 868)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b80
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 872)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5b84
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1800)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f24
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1804)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f28
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1808)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f2c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1812)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f30
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1816)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f34
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1880)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f74
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1884)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f78
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1888)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f7c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1892)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f80
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1896)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f84
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1900)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f88
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1904)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f8c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1908)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f90
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1912)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f94
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1916)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f98
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1920)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5f9c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1924)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5fa0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1928)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5fa4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1932)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5fa8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1936)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5fac
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1940)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5fb0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1944)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5fb4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1948)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5fb8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1952)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x5fbc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2036)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6010
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2040)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6014
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2044)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6018
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2048)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x601c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2052)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6020
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2056)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6024
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2060)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6028
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2064)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x602c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2068)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6030
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2072)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6034
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2076)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6038
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2080)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x603c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2084)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6040
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2088)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6044
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2092)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6048
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2096)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x604c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2100)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6050
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2104)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6054
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2108)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6058
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2112)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x605c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2116)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6060
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2120)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6064
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2124)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6068
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2128)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x606c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2204)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60b8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2208)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60bc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2212)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60c0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2216)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60c4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2220)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60c8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2224)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60cc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2228)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60d0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2232)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60d4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2236)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60d8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2240)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60dc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2244)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60e0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2248)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60e4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2252)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60e8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2256)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60ec
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2260)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60f0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2264)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60f4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2268)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60f8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2272)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x60fc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2276)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6100
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2280)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6104
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2284)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6108
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2288)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x610c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2348)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6148
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2352)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x614c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2356)
    mergeField_fnOff_mf14 (by decide) x9p_decode_0x6150
  dsimp only [tripleRatchetProgAt] at hpc hcallB hcallI ⊢
  have hx2_tr : (s0.readReg64 (Reg.gpr 2#5)).truncate 32 &&& 255#32 = 2#32 :=
    wt_and_ff_eq_x9p (s0.readReg64 .x2) hx2
  have hx2_64 : BitVec.truncate 32 (BitVec.zeroExtend 64
      (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 2#5))) &&& 255#64) = 2#32 :=
    wt_and_ff_64_eq_x9p (s0.readReg64 .x2) hx2
  have hl_ne0 := len_ne_zero_x9p
    (a := 38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hl_s1, hl_a1⟩ := sub1_and_add_neg1_x9p
    (a := 38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (a' := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hsubL, hultL, huleL⟩ := subs_body_len_x9p
    (L := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega)
  obtain ⟨hl2_s1, hl2_a1⟩ := sub1_and_add_neg1_x9p
    (a := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (a' := 36 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult1, hule1, hult1', hsub1⟩ := cmp_gt_tail_x9p
    (a := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hl3_s1, hl3_a1⟩ := sub1_and_add_neg1_x9p
    (a := 36 + (encodeVarint (spk.signExtend 64)).length)
    (a' := 35 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult2, hule2, hult2', hsub2⟩ := cmp_gt_tail_x9p
    (a := 36 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hl4_s1, hl4_a1⟩ := sub1_and_add_neg1_x9p
    (a := 1 + (encodeVarint (spk.signExtend 64)).length)
    (a' := (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult3, hule3, hult3', hsub3⟩ := cmp_gt_tail_x9p
    (a := 1 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  have hadrp :
      (((libsignalSessionCode.rebase sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr mergeFieldName + 40#64) &&&
        18446744073709547520#64) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" - 0x5000) = sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d") := by
    rw [Program.fnAddr_rebase, CryptoVerification.libsignalSessionCode_fnOff_0x581c]
    simp only [hb, arm64_norm]
  have hfetch_0x34 := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := Rust.withPanics (tripleRatchetExterns C ctl abs))
    (k := 52) mergeField_fnOff_mf14 (by decide) x9p_decode_0x5850
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr mergeFieldName = entry
  examples_hide_fetches
  conv =>
    arg 4
    rw [prostSSGXAt_fresh_unfold_x9p A0 ss v hp,
        sliceCursorAt_unfold_spk_some_x9p slot ptr i hk hspk tail,
        stackAt_mergeField_unfold_x9p s0.sp]
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
  apply of_sepWP_frozen_mf14 hF0 hsym0 (mid := entry + 52#64)
  iterate 13 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hF1 hsym1
  obtain ⟨hread9, hcan9⟩ := rodata_jump_tag9_x9p hF1
  apply of_sepWP_frozen_mf14 hF1 hsym1 (mid := entry + 18446744073709540264#64)
  refine step_ldr8_ro_mf14 (pc := entry + 52#64) (pc' := entry + 56#64)
    (r := Reg.gpr 11#5) (v64 := 181#64)
    rfl (by simp only [wp_norm, arm64_norm, hrun]) hfetch_0x34 rfl
    (ea := sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) (wb := none)
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
    (F := memRegion (s0.sp - 240#64 - 16144#64) 7792 ∗
      ((ss + 0xf8#64) ↦₆₄ 0#64 ∗ (ss + 0x100#64) ↦₆₄ 1#64 ∗ (ss + 0x108#64) ↦₆₄ 0#64) ∗
      (ss + 272#64) ↦₃₂ 1#32 ∗
      (ss + 280#64) ↦₆₄ 0#64 ∗
      (ss + 288#64) ↦₃₂ 0#32 ∗
      memRegion (ss + 292#64) 4 ∗
      prostSSRest_x9p A0 ss v ∗
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
    (by simp only [Prost.int32MergeSpec, wp_norm, arm64_norm]; rfl)
    (by simp only [List.length_append, List.length_cons, hk]; omega)
    (by
      refine Entails.trans ?_
        (pre_to_int32_gen_x9p (ss + 276#64) bufRef slot (ptr + 2#64) s0.sp
          (i.setWidth 64)
          (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))) _)
      rw [split_272_x9p ss, hlen_i1]
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [Prost.int32MergeSpec, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm]) hm) ?_
  intro sf hpcf hrunf hspf hcsf hF3 hsym3
  simp only [wp_norm, arm64_norm] at hpcf
  have hsp_sf : sf.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm] using hspf
  rw [post_of_int32_gen_x9p (ss + 276#64) bufRef slot (ptr + 2#64) s0.sp
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
  have hcsv_i : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
  apply of_sepWP_frozen_mf14 hF3 hsym3 (mid := entry + 18446744073709539180#64)
  iterate 35 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf])
  intro hF4 hsym4
  have hlen_b1 : 35 + (encodeVarint (spk.signExtend 64)).length + tail.length =
      34 + (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)).length := by
    simp only [List.length_cons, List.length_append]; omega
  refine call_frame_inv_x9p
    (x := ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      pendingPtr2 ptr i + 1#64, 33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail))⟩)
    (F := memRegion (s0.sp - 240#64 - 16144#64) 7648 ∗
      (ss + 276#64) ↦₃₂ i ∗
      (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
      pendingPtr2 ptr i ↦₈ 18#8 ∗
      ((ss + 272#64) ↦₃₂ 1#32 ∗
        (ss + 280#64) ↦₆₄ 0#64 ∗
        (ss + 288#64) ↦₃₂ 0#32 ∗
        memRegion (ss + 292#64) 4 ∗
        prostSSRest_x9p A0 ss v ∗
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
    (by simp only [Prost.bytesMergeRawSpec, wp_norm, arm64_norm, hsp_sf]; rfl)
    (by refine ⟨?_, Prost.bytesMergeCapOk_zero⟩; simp only [List.length_cons, List.length_append, hk]; omega)
    (by
      rw [hlen_b1, ← List.cons_append (a := 33#8)]
      rw [← pre_to_bytesMerge_gen_x9p ss bufRef slot (pendingPtr2 ptr i + 1#64) s0.sp hk
          (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail))]
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf' _ hm => by
      dsimp only [Prost.bytesMergeRawSpec, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm, htr_i]) hm) ?_
  intro sf2 hpcf2 hrunf2 hspf2 hcsf2 hF5 hsym5
  simp only [wp_norm, arm64_norm] at hpcf2
  have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hsp_sf] using hspf2
  rw [post_of_bytesMerge_gen_x9p ss bufRef slot (pendingPtr2 ptr i + 1#64) s0.sp hk
      (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)) _
      _ sf2 (by simp only [wp_norm, arm64_norm, hsp_sf])]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun htr_b => SepWPp.pure_elim fun hx0_b =>
    SepWPp.pure_elim fun _hcapOk => ?_
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
  have hcsv_b : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
    simpa only [wp_norm, arm64_norm, hcsv_i] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
  apply of_sepWP_frozen_mf14 hF5 hsym5 (mid := entry + 18446744073709540264#64)
  iterate 33 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf2])
  intro hF6 hsym6
  refine call_frame_inv_x9p
    (x := ⟨.varint, ss + 288#64, bufRef, slot, pendingPtr2 ptr i + 36#64,
      encodeVarint (spk.signExtend 64) ++ tail⟩)
    (F := memRegion (s0.sp - 240#64 - 16144#64) 7792 ∗
      (vecU8At A0 (ss + 248#64) cap' ptr' k ∗
        (pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k) ∗
        (pendingPtr2 ptr i + 35#64) ↦₈ 24#8 ∗
        ((ss + 276#64) ↦₃₂ i ∗
          (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
          pendingPtr2 ptr i ↦₈ 18#8 ∗
          ((ss + 272#64) ↦₃₂ 1#32 ∗
            (ss + 280#64) ↦₆₄ 0#64 ∗
            memRegion (ss + 292#64) 4 ∗
            prostSSRest_x9p A0 ss v ∗
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
    (by simp only [Prost.int32MergeSpec, wp_norm, arm64_norm, hsp_sf2]; rfl)
    (by rw [List.length_append]; omega)
    (by
      refine Entails.trans ?_
        (pre_to_int32_gen_x9p (ss + 288#64) bufRef slot (pendingPtr2 ptr i + 36#64) s0.sp
          (spk.signExtend 64) tail _)
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf' _ hm => by
      dsimp only [Prost.int32MergeSpec, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm, htr_b']) hm) ?_
  intro sf3 hpcf3 hrunf3 hspf3 hcsf3 _ _
  simp only [wp_norm, arm64_norm] at hpcf3
  rw [post_of_int32_gen_x9p (ss + 288#64) bufRef slot (pendingPtr2 ptr i + 36#64) s0.sp
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
  have hcsv_sf : calleeSavedVRegs sf3 = calleeSavedVRegs s0 := by
    simpa only [wp_norm, arm64_norm, hcsv_b] using hcsf3.2.2.2.2.2.2.2.2.2.2.2
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
  apply SepWP.fold (final_post_entails_spk_some_x9p ss cap' ptr' v bufRef slot ptr i hk hspk tail
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
    by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hx26_sf, hx27_sf, hx28_sf, hcsv_sf, and_self]⟩

theorem mergeFieldX9P_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) :
    MergeFieldXOk C ctl
      (fun fl => (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk)) abs := by
  have h1 := mergeFieldX9P_id_ok C ctl hC
  have h2 := mergeFieldX9P_spk_none_ok C ctl hC
  have h3 := mergeFieldX9P_spk_some_ok C ctl hC
  refine mergeFieldXOk_of_imp (mergeFieldXOk_or h1 (mergeFieldXOk_or h2 h3)) ?_
  intro fl hfl
  rcases hfl with ⟨i, k, rfl⟩ | ⟨o, k, spk, rfl⟩
  · exact Or.inl ⟨i, k, rfl⟩
  · cases o with
    | none => exact Or.inr (Or.inl ⟨k, spk, rfl⟩)
    | some i => exact Or.inr (Or.inr ⟨i, k, spk, rfl⟩)

end CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX9P
