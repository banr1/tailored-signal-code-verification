/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Frame
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import ProofLib.SepLogic.WPp

/-!
# `OutgoingTripleRatchet::from_session_state` Case 4 (`st.remoteIdentity = some rem`)

Verifies the `Ok` path (`st.senderChain = some sc`, `st.version.toNat < 256`, and
`st.remoteIdentity = some rem`) of `<OutgoingTripleRatchet>::from_session_state`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.Ratchet CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_setWidth32 zeroExtend64_setWidth16 zeroExtend32_setWidth16
  zeroExtend64_setWidth8 zeroExtend32_setWidth8
  localIk_bytes0_7_low32 localIk_bytes0_7_mid16 localIk_bytes0_7_hi8
  shift40_shift16_eq_shift56

/-! ## Case 4 (`st.remoteIdentity = some rem`) helpers and proof -/

theorem remoteIdentityOkAt_some_split_sp152 (sp : BitVec 64)
    (opt : Option IdentityKey) (rem : IdentityKey) (h : opt = some rem) :
    remoteIdentityOkAt (sp - 152#64) opt ⊢
      ((sp - 152#64) ↦₈ 0#8) ∗
      ((sp - 151#64) ↦₈ 1#8) ∗
      ((sp - 150#64) ↦₃₂ pack32 (rem.publicKey.bytes.toList.take 4)) ∗
      ((sp - 146#64) ↦₁₆ pack16 ((rem.publicKey.bytes.toList.drop 4).take 2)) ∗
      ((sp - 144#64) ↦₆₄ pack64 ((rem.publicKey.bytes.toList.drop 6).take 8)) ∗
      ((sp - 136#64) ↦₆₄ pack64 ((rem.publicKey.bytes.toList.drop 14).take 8)) ∗
      ((sp - 128#64) ↦₆₄ pack64 ((rem.publicKey.bytes.toList.drop 22).take 8)) ∗
      ((sp - 120#64) ↦₁₆ pack16 (rem.publicKey.bytes.toList.drop 30)) := by
  subst h
  dsimp only [remoteIdentityOkAt]
  rw [sub_add_eq_sub sp 1#64 152#64 151#64,
      sub_add_eq_sub sp 2#64 152#64 150#64,
      bytes32_eq_4_2_8_8_8_2 (sp - 150#64) rem.publicKey.bytes.toList rem.publicKey.bytes.toList_length,
      sub_add_eq_sub sp 4#64 150#64 146#64,
      sub_add_eq_sub sp 6#64 150#64 144#64,
      sub_add_eq_sub sp 14#64 150#64 136#64,
      sub_add_eq_sub sp 22#64 150#64 128#64,
      sub_add_eq_sub sp 30#64 150#64 120#64]
  exact Entails.refl _

theorem sp352_344_pair32_to_64 (sp : BitVec 64) (v20 v24 v28 v2c : BitVec 32) :
    (((sp - 352#64) ↦₃₂ v20) ∗ ((sp - 348#64) ↦₃₂ v24) ∗
     ((sp - 344#64) ↦₃₂ v28) ∗ ((sp - 340#64) ↦₃₂ v2c)) ⊢
    (((sp - 352#64) ↦₆₄ (v20.zeroExtend 64 ||| (v24.zeroExtend 64 <<< 32))) ∗
     ((sp - 344#64) ↦₆₄ (v28.zeroExtend 64 ||| (v2c.zeroExtend 64 <<< 32)))) := by
  have h1 := pointsTo32_pair_eq_pointsTo64 (sp - 352#64) v20 v24
  have h2 := pointsTo32_pair_eq_pointsTo64 (sp - 344#64) v28 v2c
  rw [sub_add_eq_sub sp 4#64 352#64 348#64] at h1
  rw [sub_add_eq_sub sp 4#64 344#64 340#64] at h2
  rw [← sepConj_assoc, h1, h2]
  exact Entails.refl _

theorem frame128_fold_phaseB_64 (sp : BitVec 64)
    (s00 s08 s10 s18 s20 s28 s30 s38 s40 s48 s50 s68 s70 s78 : BitVec 64)
    (s5c s60 s64 : BitVec 32) :
    (((sp - 384#64) ↦₆₄ s00) ∗ ((sp - 376#64) ↦₆₄ s08) ∗
      ((sp - 368#64) ↦₆₄ s10) ∗ ((sp - 360#64) ↦₆₄ s18) ∗
      ((sp - 352#64) ↦₆₄ s20) ∗ ((sp - 344#64) ↦₆₄ s28) ∗
      ((sp - 336#64) ↦₆₄ s30) ∗ ((sp - 328#64) ↦₆₄ s38) ∗
      ((sp - 320#64) ↦₆₄ s40) ∗ ((sp - 312#64) ↦₆₄ s48) ∗
      ((sp - 304#64) ↦₆₄ s50) ∗ memRegion (sp - 296#64) 4 ∗
      ((sp - 292#64) ↦₃₂ s5c) ∗ ((sp - 288#64) ↦₃₂ s60) ∗
      ((sp - 284#64) ↦₃₂ s64) ∗ ((sp - 280#64) ↦₆₄ s68) ∗
      ((sp - 272#64) ↦₆₄ s70) ∗ ((sp - 264#64) ↦₆₄ s78)) ⊢
    memRegion (sp - 384#64) 128 := by
  rw [mr_cut' sp 384 376 8 120 128 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 376 368 8 112 120 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 368 360 8 104 112 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 360 352 8 96 104 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 352 344 8 88 96 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 344 336 8 80 88 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 336 328 8 72 80 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 328 320 8 64 72 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 320 312 8 56 64 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 312 304 8 48 56 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 304 296 8 40 48 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 296 292 4 36 40 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 292 288 4 32 36 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 288 284 4 28 32 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 284 280 4 24 28 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 280 272 8 16 24 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 272 264 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (pointsTo64_entails_memRegion _ s00) (sepConj_mono (pointsTo64_entails_memRegion _ s08) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion _ s10) (sepConj_mono (pointsTo64_entails_memRegion _ s18) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion _ s20) (sepConj_mono (pointsTo64_entails_memRegion _ s28) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion _ s30) (sepConj_mono (pointsTo64_entails_memRegion _ s38) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion _ s40) (sepConj_mono (pointsTo64_entails_memRegion _ s48) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion _ s50) (sepConj_mono (Entails.refl _) ?_)
  refine sepConj_mono (pointsTo32_entails_memRegion _ s5c) (sepConj_mono (pointsTo32_entails_memRegion _ s60) ?_)
  refine sepConj_mono (pointsTo32_entails_memRegion _ s64) (sepConj_mono (pointsTo64_entails_memRegion _ s68) ?_)
  exact sepConj_mono (pointsTo64_entails_memRegion _ s70) (pointsTo64_entails_memRegion _ s78)

theorem spe_missingRemote_at_sp152 (A : RustAlloc) (sp p w0 w8 w16 w24 : BitVec 64) (w32 : BitVec 16)
    (hw0 : w0 = speWord 20) (hw8 : w8 = p) (hw16 : w16 = 27#64) :
    (((sp - 152#64) ↦₆₄ w0) ∗ ((sp - 144#64) ↦₆₄ w8) ∗
      ((sp - 136#64) ↦₆₄ w16) ∗ (p ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗
      ((sp - 128#64) ↦₆₄ w24) ∗ ((sp - 120#64) ↦₁₆ w32) ∗
      memRegion (sp - 118#64) 6 ∗ memRegion (sp - 112#64) 16) ⊢
    speAt A [] (sp - 152#64) (.invalidSessionStructure .missingRemoteIdentity) ∗
      memRegion (sp - 104#64) 8 := by
  subst w0 w8 w16
  have h16 : memRegion (sp - BitVec.ofNat 64 112) 16 =
      memRegion (sp - 112#64) 8 ∗ memRegion (sp - 104#64) 8 :=
    mr_cut' sp 112 104 8 8 16 rfl rfl (by decide) (by decide) (by decide)
  have hspe := spe_missingRemote_at_sret A (sp - 152#64) p w24 w32
  rw [sub_add_eq_sub sp 8#64 152#64 144#64,
      sub_add_eq_sub sp 16#64 152#64 136#64,
      sub_add_eq_sub sp 24#64 152#64 128#64,
      sub_add_eq_sub sp 32#64 152#64 120#64,
      sub_add_eq_sub sp 34#64 152#64 118#64,
      sub_add_eq_sub sp 40#64 152#64 112#64] at hspe
  rw [h16]
  have hassoc :
      (((sp - 152#64) ↦₆₄ speWord 20) ∗ ((sp - 144#64) ↦₆₄ p) ∗
        ((sp - 136#64) ↦₆₄ 27#64) ∗ (p ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗
        ((sp - 128#64) ↦₆₄ w24) ∗ ((sp - 120#64) ↦₁₆ w32) ∗
        memRegion (sp - 118#64) 6 ∗ (memRegion (sp - 112#64) 8 ∗ memRegion (sp - 104#64) 8)) =
      (((sp - 152#64) ↦₆₄ speWord 20) ∗ ((sp - 144#64) ↦₆₄ p) ∗
        ((sp - 136#64) ↦₆₄ 27#64) ∗ (p ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗
        ((sp - 128#64) ↦₆₄ w24) ∗ ((sp - 120#64) ↦₁₆ w32) ∗
        memRegion (sp - 118#64) 6 ∗ memRegion (sp - 112#64) 8) ∗ memRegion (sp - 104#64) 8 := by
    simp only [sepConj_assoc]
  rw [hassoc]
  exact sepConj_mono_left hspe

theorem sevenBytes_421_to_124_sp232 (sp : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (((sp - 232#64) ↦₃₂ pack32 (bs.take 4)) ∗
     ((sp - 228#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
     ((sp - 226#64) ↦₈ pack8 ((bs.drop 6).take 1))) ⊢
    (((sp - 232#64) ↦₈ pack8 (bs.take 1)) ∗
     ((sp - 231#64) ↦₁₆ pack16 ((bs.drop 1).take 2)) ∗
     ((sp - 229#64) ↦₃₂ pack32 ((bs.drop 3).take 4))) := by
  have h1 := ent_of_eq (sevenBytes_4_2_1_eq_1_2_4 (sp - 232#64) bs h)
  rw [sub_add_eq_sub sp 4#64 232#64 228#64,
      sub_add_eq_sub sp 6#64 232#64 226#64,
      sub_add_eq_sub sp 1#64 232#64 231#64,
      sub_add_eq_sub sp 3#64 232#64 229#64] at h1
  exact h1

theorem ret24_split_srk (ret : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((ret + 24#64) ↦ₛ bs) ⊢
      ((ret + 24#64) ↦₃₂ pack32 (bs.take 4)) ∗
      ((ret + 28#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
      ((ret + 30#64) ↦₈ pack8 ((bs.drop 6).take 1)) ∗
      ((ret + 31#64) ↦₆₄ pack64 ((bs.drop 7).take 8)) ∗
      ((ret + 39#64) ↦₆₄ pack64 ((bs.drop 15).take 8)) ∗
      ((ret + 47#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
      ((ret + 55#64) ↦₈ pack8 (bs.drop 31)) := by
  have h1 := ent_of_eq (bytes32_eq_4_2_1_8_8_8_1 (ret + 24#64) bs h)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  exact h1

theorem sevenBytes_after_store_at_0_ret24 (ret : BitVec 64) (u0 : BitVec 32) (u4 : BitVec 16) (u6 : BitVec 8)
    (bs : List (BitVec 8)) (h : bs.length = 32) (hu0 : u0 = pack32 (bs.take 4)) :
    (((ret + 24#64) ↦₃₂ u0) ∗
     ((ret + 28#64) ↦₁₆ u4) ∗
     ((ret + 30#64) ↦₈ u6)) ⊢
    (((ret + 24#64) ↦₈ pack8 (bs.take 1)) ∗
     ((ret + 25#64) ↦₁₆ pack16 ((bs.drop 1).take 2)) ∗
     ((ret + 27#64) ↦₃₂ pack32 ((bs.drop 3).take 1 ++ unpack16 u4 ++ [u6]))) := by
  subst u0
  have h1 := ent_of_eq (sevenBytes_after_store_at_0 (ret + 24#64) u4 u6 bs h)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  exact h1

theorem ret24_fold_srk (ret : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32)
    (v0 : BitVec 8) (v1 : BitVec 16) (v3 : BitVec 32) (v7 v15 v23 : BitVec 64) (v31 : BitVec 8)
    (hv0 : v0 = pack8 (bs.take 1))
    (hv1 : v1 = pack16 ((bs.drop 1).take 2))
    (hv3 : v3 = pack32 ((bs.drop 3).take 4))
    (hv7 : v7 = pack64 ((bs.drop 7).take 8))
    (hv15 : v15 = pack64 ((bs.drop 15).take 8))
    (hv23 : v23 = pack64 ((bs.drop 23).take 8))
    (hv31 : v31 = pack8 (bs.drop 31)) :
    (((ret + 24#64) ↦₈ v0) ∗
     ((ret + 25#64) ↦₁₆ v1) ∗
     ((ret + 27#64) ↦₃₂ v3) ∗
     ((ret + 31#64) ↦₆₄ v7) ∗
     ((ret + 39#64) ↦₆₄ v15) ∗
     ((ret + 47#64) ↦₆₄ v23) ∗
     ((ret + 55#64) ↦₈ v31)) ⊢
    ((ret + 24#64) ↦ₛ bs) := by
  subst v0 v1 v3 v7 v15 v23 v31
  have h7 := (sevenBytes_4_2_1_eq_1_2_4 (ret + 24#64) bs h).symm
  have h32 := (bytes32_eq_4_2_1_8_8_8_1 (ret + 24#64) bs h).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h7 h32
  have hgrp :
      (((ret + 24#64) ↦₈ pack8 (bs.take 1)) ∗
       ((ret + 25#64) ↦₁₆ pack16 ((bs.drop 1).take 2)) ∗
       ((ret + 27#64) ↦₃₂ pack32 ((bs.drop 3).take 4)) ∗
       ((ret + 31#64) ↦₆₄ pack64 ((bs.drop 7).take 8)) ∗
       ((ret + 39#64) ↦₆₄ pack64 ((bs.drop 15).take 8)) ∗
       ((ret + 47#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
       ((ret + 55#64) ↦₈ pack8 (bs.drop 31))) =
      (((ret + 24#64) ↦₈ pack8 (bs.take 1)) ∗
       ((ret + 25#64) ↦₁₆ pack16 ((bs.drop 1).take 2)) ∗
       ((ret + 27#64) ↦₃₂ pack32 ((bs.drop 3).take 4))) ∗
      (((ret + 31#64) ↦₆₄ pack64 ((bs.drop 7).take 8)) ∗
       ((ret + 39#64) ↦₆₄ pack64 ((bs.drop 15).take 8)) ∗
       ((ret + 47#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
       ((ret + 55#64) ↦₈ pack8 (bs.drop 31))) := by
    ac_rfl
  rw [hgrp, h7]
  simp only [sepConj_assoc]
  rw [h32]
  exact Entails.refl _

theorem ret56_split_priv (ret : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((ret + 56#64) ↦ₛ bs) ⊢
      ((ret + 56#64) ↦₈ pack8 (bs.take 1)) ∗
      ((ret + 57#64) ↦₃₂ pack32 ((bs.drop 1).take 4)) ∗
      ((ret + 61#64) ↦₁₆ pack16 ((bs.drop 5).take 2)) ∗
      ((ret + 63#64) ↦₆₄ pack64 ((bs.drop 7).take 8)) ∗
      ((ret + 71#64) ↦₆₄ pack64 ((bs.drop 15).take 8)) ∗
      ((ret + 79#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
      ((ret + 87#64) ↦₈ pack8 (bs.drop 31)) := by
  have h1 := ent_of_eq (bytes32_eq_1_4_2_8_8_8_1 (ret + 56#64) bs h)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  exact h1

theorem ret56_fold_priv (ret : BitVec 64) (v : List.Vector (BitVec 8) 32)
    (hcl : Ratchet.clampScalar v = v)
    (v0 : BitVec 8) (v1 : BitVec 32) (v5 : BitVec 16) (v7 v15 v23 : BitVec 64) (v31 : BitVec 8)
    (hv0 : v0 = (((pack8 (v.toList.take 1)).zeroExtend 32 &&& 0xfffffff8#32).zeroExtend 64).setWidth 8)
    (hv1 : v1 = pack32 ((v.toList.drop 1).take 4))
    (hv5 : v5 = pack16 ((v.toList.drop 5).take 2))
    (hv7 : v7 = pack64 ((v.toList.drop 7).take 8))
    (hv15 : v15 = pack64 ((v.toList.drop 15).take 8))
    (hv23 : v23 = pack64 ((v.toList.drop 23).take 8))
    (hv31 : v31 = ((BitVec.ofNat 32 64 &&& 4294967232#32 |||
      ((pack8 (v.toList.drop 31)).zeroExtend 32 &&& 63#32)).zeroExtend 64).setWidth 8) :
    (((ret + 56#64) ↦₈ v0) ∗
     ((ret + 57#64) ↦₃₂ v1) ∗
     ((ret + 61#64) ↦₁₆ v5) ∗
     ((ret + 63#64) ↦₆₄ v7) ∗
     ((ret + 71#64) ↦₆₄ v15) ∗
     ((ret + 79#64) ↦₆₄ v23) ∗
     ((ret + 87#64) ↦₈ v31)) ⊢
    ((ret + 56#64) ↦ₛ v.toList) := by
  subst v0 v1 v5 v7 v15 v23 v31
  rw [clampScalar_byte0 hcl, clampScalar_byte31 hcl]
  have h1 := ent_of_eq (bytes32_eq_1_4_2_8_8_8_1 (ret + 56#64) v.toList v.toList_length).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  exact h1

theorem ret88_split_localIk (ret : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((ret + 88#64) ↦ₛ bs) ⊢
      ((ret + 88#64) ↦₃₂ pack32 (bs.take 4)) ∗
      ((ret + 92#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
      ((ret + 94#64) ↦₈ pack8 ((bs.drop 6).take 1)) ∗
      ((ret + 95#64) ↦₆₄ pack64 ((bs.drop 7).take 8)) ∗
      ((ret + 103#64) ↦₆₄ pack64 ((bs.drop 15).take 8)) ∗
      ((ret + 111#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
      ((ret + 119#64) ↦₈ pack8 (bs.drop 31)) := by
  have h1 := ent_of_eq (bytes32_eq_4_2_1_8_8_8_1 (ret + 88#64) bs h)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  exact h1

theorem ret88_fold_localIk (ret : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32)
    (v0 : BitVec 32) (v4 : BitVec 16) (v6 : BitVec 8) (v7 v15 v23 : BitVec 64) (v31 : BitVec 8)
    (hv0 : v0 = pack32 (bs.take 4))
    (hv4 : v4 = pack16 ((bs.drop 4).take 2))
    (hv6 : v6 = pack8 ((bs.drop 6).take 1))
    (hv7 : v7 = (((pack8 ((bs.drop 7).take 1)).zeroExtend 64 |||
      (((pack8 ((bs.drop 8).take 1)).zeroExtend 64) <<< 8)) |||
      ((((pack32 ((bs.drop 9).take 4)).zeroExtend 64) <<< 16) |||
       (((pack16 ((bs.drop 13).take 2)).zeroExtend 64) <<< 48))))
    (hv15 : v15 = pack64 ((bs.drop 15).take 8))
    (hv23 : v23 = pack64 ((bs.drop 23).take 8))
    (hv31 : v31 = pack8 (bs.drop 31)) :
    (((ret + 88#64) ↦₃₂ v0) ∗
     ((ret + 92#64) ↦₁₆ v4) ∗
     ((ret + 94#64) ↦₈ v6) ∗
     ((ret + 95#64) ↦₆₄ v7) ∗
     ((ret + 103#64) ↦₆₄ v15) ∗
     ((ret + 111#64) ↦₆₄ v23) ∗
     ((ret + 119#64) ↦₈ v31)) ⊢
    ((ret + 88#64) ↦ₛ bs) := by
  subst v0 v4 v6 v7 v15 v23 v31
  rw [localIk_bytes7_15_reassemble bs h]
  have h1 := ent_of_eq (bytes32_eq_4_2_1_8_8_8_1 (ret + 88#64) bs h).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  exact h1

theorem ret120_split_remoteIk (ret : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((ret + 120#64) ↦ₛ bs) ⊢
      ((ret + 120#64) ↦₃₂ pack32 (bs.take 4)) ∗
      ((ret + 124#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
      ((ret + 126#64) ↦₆₄ pack64 ((bs.drop 6).take 8)) ∗
      ((ret + 134#64) ↦₆₄ pack64 ((bs.drop 14).take 8)) ∗
      ((ret + 142#64) ↦₆₄ pack64 ((bs.drop 22).take 8)) ∗
      ((ret + 150#64) ↦₁₆ pack16 (bs.drop 30)) := by
  have h1 := ent_of_eq (bytes32_eq_4_2_8_8_8_2 (ret + 120#64) bs h)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  exact h1

theorem ret120_fold_remoteIk (ret : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32)
    (v0 : BitVec 32) (v4 : BitVec 16) (v6 v14 v22 : BitVec 64) (v30 : BitVec 16)
    (hv0 : v0 = pack32 (bs.take 4))
    (hv4 : v4 = pack16 ((bs.drop 4).take 2))
    (hv6 : v6 = pack64 ((bs.drop 6).take 8))
    (hv14 : v14 = pack64 ((bs.drop 14).take 8))
    (hv22 : v22 = pack64 ((bs.drop 22).take 8))
    (hv30 : v30 = pack16 (bs.drop 30)) :
    (((ret + 120#64) ↦₃₂ v0) ∗
     ((ret + 124#64) ↦₁₆ v4) ∗
     ((ret + 126#64) ↦₆₄ v6) ∗
     ((ret + 134#64) ↦₆₄ v14) ∗
     ((ret + 142#64) ↦₆₄ v22) ∗
     ((ret + 150#64) ↦₁₆ v30)) ⊢
    ((ret + 120#64) ↦ₛ bs) := by
  subst v0 v4 v6 v14 v22 v30
  have h1 := ent_of_eq (bytes32_eq_4_2_8_8_8_2 (ret + 120#64) bs h).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  exact h1

theorem ret152_split_ck (ret : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((ret + 152#64) ↦ₛ bs) ⊢
      ((ret + 152#64) ↦₃₂ pack32 (bs.take 4)) ∗
      ((ret + 156#64) ↦₆₄ pack64 ((bs.drop 4).take 8)) ∗
      ((ret + 164#64) ↦₁₆ pack16 ((bs.drop 12).take 2)) ∗
      ((ret + 166#64) ↦₈ pack8 ((bs.drop 14).take 1)) ∗
      ((ret + 167#64) ↦₃₂ (pack64 ((bs.drop 15).take 8)).setWidth 32) ∗
      ((ret + 171#64) ↦₈ (((pack64 ((bs.drop 15).take 8) >>> 32).setWidth 32).zeroExtend 64).setWidth 8) ∗
      ((ret + 172#64) ↦₁₆ (((pack64 ((bs.drop 15).take 8) >>> 40).setWidth 32).zeroExtend 64).setWidth 16) ∗
      ((ret + 174#64) ↦₈ (((pack64 ((bs.drop 15).take 8) >>> 56).setWidth 32).zeroExtend 64).setWidth 8) ∗
      ((ret + 175#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
      ((ret + 183#64) ↦₈ pack8 (bs.drop 31)) := by
  have h1 := ent_of_eq (bytes32_eq_4_8_2_1_8_8_1 (ret + 152#64) bs h)
  have h2 := (pointsTo64_of_4_1_2_1 (ret + 167#64) (pack64 ((bs.drop 15).take 8))).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, zeroExtend64_setWidth32] at h1 h2
  rw [h2] at h1
  simp only [sepConj_assoc] at h1
  exact h1

theorem ret152_fold_ck (ret : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32)
    (v0 : BitVec 32) (v4 : BitVec 64) (v12 : BitVec 16) (v14 : BitVec 8)
    (v15 : BitVec 32) (v19 : BitVec 8) (v20 : BitVec 16) (v22 : BitVec 8)
    (v23 : BitVec 64) (v31 : BitVec 8)
    (hv0 : v0 = pack32 (bs.take 4))
    (hv4 : v4 = pack64 ((bs.drop 4).take 8))
    (hv12 : v12 = (((pack64 ((bs.drop 7).take 8) >>> 40).setWidth 32).zeroExtend 64).setWidth 16)
    (hv14 : v14 = (((pack64 ((bs.drop 7).take 8) >>> 56).setWidth 32).zeroExtend 64).setWidth 8)
    (hv15 : v15 = (pack64 ((bs.drop 15).take 8)).setWidth 32)
    (hv19 : v19 = (((pack64 ((bs.drop 15).take 8) >>> 32).setWidth 32).zeroExtend 64).setWidth 8)
    (hv20 : v20 = (((pack64 ((bs.drop 15).take 8) >>> 40).setWidth 32).zeroExtend 64).setWidth 16)
    (hv22 : v22 = (((pack64 ((bs.drop 15).take 8) >>> 56).setWidth 32).zeroExtend 64).setWidth 8)
    (hv23 : v23 = pack64 ((bs.drop 23).take 8))
    (hv31 : v31 = pack8 (bs.drop 31)) :
    (((ret + 152#64) ↦₃₂ v0) ∗
     ((ret + 156#64) ↦₆₄ v4) ∗
     ((ret + 164#64) ↦₁₆ v12) ∗
     ((ret + 166#64) ↦₈ v14) ∗
     ((ret + 167#64) ↦₃₂ v15) ∗
     ((ret + 171#64) ↦₈ v19) ∗
     ((ret + 172#64) ↦₁₆ v20) ∗
     ((ret + 174#64) ↦₈ v22) ∗
     ((ret + 175#64) ↦₆₄ v23) ∗
     ((ret + 183#64) ↦₈ v31)) ⊢
    ((ret + 152#64) ↦ₛ bs) := by
  subst v0 v4 v12 v14 v15 v19 v20 v22 v23 v31
  rw [pack64_shift40_setWidth16 bs h, pack64_shift56_setWidth8 bs h]
  have h1 := ent_of_eq (bytes32_eq_4_8_2_1_8_8_1 (ret + 152#64) bs h).symm
  have h2 := pointsTo64_of_4_1_2_1 (ret + 167#64) (pack64 ((bs.drop 15).take 8))
  simp only [BitVec.add_assoc, BitVec.reduceAdd, zeroExtend64_setWidth32] at h1 h2
  rw [← h2] at h1
  simp only [sepConj_assoc] at h1
  exact h1

theorem otrResultAt_ok_intro (A : RustAlloc) (ret : BitVec 64) (pq : VecPin)
    (sc : SenderChain) (st : SessionState (List (BitVec 8))) (rem : IdentityKey)
    (w0 w8 w16 : BitVec 64) (v184 v188 : BitVec 32) (v192 : BitVec 8)
    (hw0 : w0 = pq.cap) (hw8 : w8 = pq.ptr)
    (hw16 : w16 = BitVec.ofNat 64 st.pqRatchetState.length)
    (hv184 : v184 = sc.chainKey.index)
    (hv188 : v188 = st.previousCounter)
    (hv192 : v192 = (if (st.sessionVersion == 0#32) = true then 2#32 else st.sessionVersion).setWidth 8) :
    ((ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ w8) ∗
     ((ret + 16#64) ↦₆₄ w16) ∗
     vecU8Buf A pq.cap pq.ptr st.pqRatchetState ∗
     ((ret + 24#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
     ((ret + 56#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
     ((ret + 88#64) ↦ₛ st.localIdentity.publicKey.bytes.toList) ∗
     ((ret + 120#64) ↦ₛ rem.publicKey.bytes.toList) ∗
     ((ret + 152#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗
     ((ret + 184#64) ↦₃₂ v184) ∗
     ((ret + 188#64) ↦₃₂ v188) ∗
     ((ret + 192#64) ↦₈ v192) ∗
     memRegion (ret + 193#64) 7) ⊢
    otrResultAt A ret pq (.ok ⟨sc.ratchetKey, sc.chainKey, st.previousCounter,
      st.pqRatchetState, BitVec.ofNat 8 st.version.toNat, st.localIdentity, rem⟩) := by
  subst w0 w8 w16 v184 v188 v192
  rw [otrResultAt_ok_eq]
  dsimp only
  have hv : (if (st.sessionVersion == 0#32) = true then 2#32 else st.sessionVersion).setWidth 8 =
      BitVec.ofNat 8 st.version.toNat := by
    rw [version_word_eq st]; rfl
  rw [hv]
  exact Entails.refl _

theorem SepWP.seq_callInv {prog : Program} {img : Obj.Image} {mid_pc target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid_pc s P (fun sm P_m =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWP prog target_pc sm P_m post)) :
    SepWP prog target_pc s P post :=
  SepWP.of_sepWP_inv hfrozen hsym h1

def DropSpeExtOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr dropSpeName) ((dropSpeSpecX A).inImage img)

theorem DropSpeExtOkX.of_DropSpeExtOk {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DropSpeExtOk img A ext) :
    DropSpeExtOkX img A ext := by
  refine subroutine_ok_map h ?_
  intro x R s0 hpre
  have hsplit : stackAt s0.sp dropSpeStackX =
      memRegion (s0.sp - 16416#64) 12288 ∗ stackAt s0.sp dropSpeStack := by
    change memRegion (s0.sp - 16416#64) (12288 + 4128) =
      memRegion (s0.sp - 16416#64) 12288 ∗ memRegion (s0.sp - 4128#64) 4128
    rw [memRegion_split (s0.sp - 16416#64) 12288 4128 (by decide)]
    have h2 : s0.sp - 16416#64 + BitVec.ofNat 64 12288 = s0.sp - 4128#64 := by bv_lin
    rw [h2]
  refine ⟨x, memRegion (s0.sp - 16416#64) 12288 ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [Spec.inImage, dropSpeSpec, dropSpeSpecX] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  · dsimp only [Spec.inImage, dropSpeSpec, dropSpeSpecX] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢

theorem dropSpe_ok_at_otrFrom_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DropSpeExtOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrFromName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")))
      ((dropSpeSpecX A).inImage img) := by
  have heq : (tripleRatchetProgAtExt img.base ext).fnAddr otrFromName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")) =
      (tripleRatchetProgAtExt img.base ext).fnAddr dropSpeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"), (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]")]
    bv_lin
  rw [heq]; exact h

theorem stackAt_dropSpeX (sp : BitVec 64) :
    stackAt (sp - 384#64) 65152 =
      stackAt (sp - 16800#64) 48736 ∗ stackAt (sp - 384#64) dropSpeStackX := by
  change memRegion (sp - 384#64 - 65152#64) (48736 + 16416) =
    memRegion (sp - 16800#64 - 48736#64) 48736 ∗ memRegion (sp - 384#64 - 16416#64) 16416
  rw [memRegion_split (sp - 384#64 - 65152#64) 48736 16416 (by decide)]
  have h1 : sp - 384#64 - 65152#64 = sp - 16800#64 - 48736#64 := by bv_lin
  have h2 : sp - 16800#64 - 48736#64 + BitVec.ofNat 64 48736 = sp - 384#64 - 16416#64 := by bv_lin
  rw [h1, h2]

set_option maxHeartbeats 3200000 in
theorem otrFrom_case4_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : DeserializeExtOk img.base ext)
    (hRemIk : RemoteIdentityKeyExtOk img A ext)
    (hDropSpe : DropSpeExtOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrFromName)
      (otrFromCaseSpec A img
        (fun x => ∃ sc rem, x.st.senderChain = some sc ∧
          ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = some rem)) := by
  dsimp only [otrFromCaseSpec, otrFromSpec, Spec.inImage]
  have hbase_align : img.base &&& 0xfff#64 = 0#64 :=
    ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hdeser := deserialize_ok_at_otrFrom_ext hDeser
  have hpkTryFrom := pkTryFromOk_ok_at_ext (ext := ext) himg (name := otrFromName)
    (k := libsignalSessionCode.fnOff pkTryFromName - libsignalSessionCode.fnOff otrFromName)
  have hremIk := remoteIdentityKey_ok_at_otrFrom_ext hRemIk
  have hdropSpe := dropSpe_ok_at_otrFrom_ext_x hDropSpe
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.libsignalSessionBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") (num% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")) 0 1228
  wp_init
  have hadrp3 := fnAddr_adrp_ba80 (b := img.base)
    (H := Rust.withPanics ext) hbase_align
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ss, G, st, ret⟩ := a
  dsimp only at *
  rcases h_1 with ⟨sc, rem, hsc, hver, hrem⟩
  apply SepWP.seq_callInv (mid_pc := entry + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"))) h_2 h_3
  refine SepWP.add_rodata (fun hm => rodata_missingRemoteIdentity_intro himg h_2.roData hm) ?_
  refine SepWP.fold (sessionStateAt_sender_some A ss G st sc hsc) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro sg
  refine SepWP.focus_pure (by sep_focus) fun hGs => ?_
  conv =>
    arg 4
    rw [sessionStateAt_eq_from_some_self A ss G st sg sc hGs hsc,
        sessionStateAt_eq_from_some A ss G st sg sc hGs hsc G.pq st.pqRatchetState,
        stackAt_prologue s0.sp,
        frame288_split_phaseA s0.sp,
        memRegion40_split_deser_sp s0.sp,
        ret200_split_ok ret]
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro r11
  apply SepWP.exists_elim; intro r10
  apply SepWP.exists_elim; intro r9
  apply SepWP.exists_elim; intro r8
  apply SepWP.exists_elim; intro r7
  apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5
  apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  apply SepWP.exists_elim; intro v_deser
  apply SepWP.exists_elim; intro tag0_deser
  apply SepWP.exists_elim; intro ue0
  apply SepWP.exists_elim; intro ud8
  apply SepWP.exists_elim; intro uc8
  apply SepWP.exists_elim; intro uc0
  apply SepWP.exists_elim; intro u9e
  apply SepWP.exists_elim; intro u9c
  apply SepWP.exists_elim; intro u98
  apply SepWP.exists_elim; intro u90
  apply SepWP.exists_elim; intro u88
  apply SepWP.exists_elim; intro u84
  apply SepWP.exists_elim; intro u80
  apply SepWP.exists_elim; intro ver0
  apply SepWP.exists_elim; intro pc0
  apply SepWP.exists_elim; intro idx0
  apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  refine SepWP.focus_pure (by sep_focus) fun hinv1 => ?_
  refine SepWP.focus_pure (by sep_focus) fun hinv2 => ?_
  obtain ⟨hdeser_lik, hrem_inv, hchains_len, hpend_some, hreg_len, _, _⟩ := id hinv1
  have hrem_inv' : PublicKey.deserialize G.remoteIk.bytes = .ok rem.publicKey := by
    rwa [hrem] at hrem_inv
  rcases hinv2 with ⟨hdeser_srk, hpriv_eq, hpriv_clamp, hsrk_len⟩
  refine SepWP.fold (vecU8Buf_bounds A G.localIk.cap G.localIk.ptr G.localIk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hlik_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.srk.cap sg.srk.ptr sg.srk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hsrk_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.priv.cap sg.priv.ptr sg.priv.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpriv_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hck_bds => ?_
  obtain ⟨_, hlik_ge33⟩ :=
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_deserialize_ok_inversion hdeser_lik
  have hlik_cap_ne0 : G.localIk.cap ≠ 0 :=
    vecU8_cap_ne_zero_of_ge hlik_bds.1 (by omega)
  have hlik_len_lt : G.localIk.bytes.length < 2 ^ 63 :=
    Nat.lt_of_le_of_lt hlik_bds.1 hlik_bds.2.1
  have hlik_len_toNat : (BitVec.ofNat 64 G.localIk.bytes.length).toNat = G.localIk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlik_pk_len : st.localIdentity.publicKey.bytes.toList.length = 32 :=
    st.localIdentity.publicKey.bytes.toList_length
  obtain ⟨_, hsrk_ge33⟩ :=
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_deserialize_ok_inversion hdeser_srk
  have hsrk_cap_ne0 : sg.srk.cap ≠ 0 :=
    vecU8_cap_ne_zero_of_ge hsrk_bds.1 (by omega)
  have hsrk_ne_neg1 : (sg.srk.cap + 1#64 == 0#64) = false :=
    addsPState64_neg1_eq_false hsrk_bds.2.1
  have hsrk_len_lt : sg.srk.bytes.length < 2 ^ 63 :=
    Nat.lt_of_le_of_lt hsrk_bds.1 hsrk_bds.2.1
  have hsrk_len_toNat : (BitVec.ofNat 64 sg.srk.bytes.length).toNat = sg.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_len : sg.priv.bytes.length = 32 := by
    rw [hpriv_eq, List.Vector.toList_length]
  have hpriv_cap_ne0 : sg.priv.cap ≠ 0 :=
    vecU8_cap_ne_zero_of_ge hpriv_bds.1 (by omega)
  have hck_cap_ne0 : sg.ck.cap ≠ 0 := by
    have h1 := hck_bds.1
    rw [keyToBytes32_length] at h1
    exact vecU8_cap_ne_zero_of_ge h1 (by decide)
  have hck_ne_neg1 : (sg.ck.cap + 1#64 == 0#64) = false :=
    addsPState64_neg1_eq_false hck_bds.2.1
  have hv_deser_len : v_deser.toList.length = 32 := v_deser.toList_length
  have hsrk_pk_len : sc.ratchetKey.publicKey.bytes.toList.length = 32 :=
    sc.ratchetKey.publicKey.bytes.toList_length
  have hpriv_pk_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
    sc.ratchetKey.privateKey.bytes.toList_length
  have hrem_pk_len : rem.publicKey.bytes.toList.length = 32 :=
    rem.publicKey.bytes.toList_length
  have hck_key_len : (keyToBytes32 sc.chainKey.key).length = 32 :=
    keyToBytes32_length sc.chainKey.key
  have hver_ls :
      ConditionHolds CondCode.LS
        (subsPState32 (if (st.sessionVersion == 0#32) = true then 2#32 else st.sessionVersion) 255#32) =
      true := by
    rw [version_word_eq st, subsPState32_255_ls_iff st.version, decide_eq_true_eq]
    exact hver
  conv =>
    arg 4
    rw [vecU8Buf_eq_bytes_live_of_ne_zero A G.localIk.cap G.localIk.ptr G.localIk.bytes hlik_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.priv.cap sg.priv.ptr sg.priv.bytes hpriv_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0,
        hpriv_eq, hpriv_pk_len,
        bytes32_eq_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len,
        bytes32_eq_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len]
  dsimp only [logOff]
  wp_steps
  wp_call hdeser (sg.srk.ptr, sg.srk.bytes, sc.ratchetKey.publicKey,
    s0.sp - 152#64, tag0_deser, v_deser.toList)
  refine SepWP.fold (bytes32_split_sp151 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_421_to_124_sp151 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_after_store_at_0_sp232 s0.sp u9c u9e sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  -- Stop before the `sturh` at entry+284: the `memRegion` folds below must run first.
  wp_steps 33
  refine SepWP.fold (sevenBytes_124_to_421_sp232 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  refine SepWP.fold (sret_srk_entails_memRegion40 s0.sp _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (memRegion40_split_ck_sp_entails s0.sp) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro c3
  apply SepWP.exists_elim; intro c2
  apply SepWP.exists_elim; intro c0
  wp_steps
  refine SepWP.fold (elevenBytes_218_to_821_sp152 s0.sp (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (frame128_split_phaseB s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro s78
  apply SepWP.exists_elim; intro s70
  apply SepWP.exists_elim; intro s68
  apply SepWP.exists_elim; intro s64
  apply SepWP.exists_elim; intro s60
  apply SepWP.exists_elim; intro s5c
  apply SepWP.exists_elim; intro s50
  apply SepWP.exists_elim; intro s48
  apply SepWP.exists_elim; intro s40
  apply SepWP.exists_elim; intro s38
  apply SepWP.exists_elim; intro s30
  apply SepWP.exists_elim; intro s2c
  apply SepWP.exists_elim; intro s28
  apply SepWP.exists_elim; intro s24
  apply SepWP.exists_elim; intro s20
  apply SepWP.exists_elim; intro s18
  apply SepWP.exists_elim; intro s10
  apply SepWP.exists_elim; intro s08
  apply SepWP.exists_elim; intro s00
  refine SepWP.fold (ent_of_eq (frame33_split s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro ub8
  apply SepWP.exists_elim; intro ub4
  apply SepWP.exists_elim; intro ub0
  apply SepWP.exists_elim; intro ua8
  apply SepWP.exists_elim; intro ua0
  refine SepWP.fold (ent_of_eq (frame15_split s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro ud4
  apply SepWP.exists_elim; intro ud0
  apply SepWP.exists_elim; intro uc9
  wp_steps
  refine SepWP.fold (ck_scratch_entails_memRegion40_sp152 s0.sp _ _ _) (by sep_focus) ?_
  wp_call hpkTryFrom (G.localIk.ptr, G.localIk.bytes, st.localIdentity.publicKey, s0.sp - 152#64)
  refine SepWP.fold (bytes32_split_localIk_sp151 s0.sp st.localIdentity.publicKey.bytes.toList hlik_pk_len) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A G.localIk.cap G.localIk.ptr G.localIk.bytes hlik_cap_ne0) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sret_localIk_entails_memRegion34_6 s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (stackAt_remoteIk s0.sp)) (by sep_focus) ?_
  wp_call hremIk ⟨ss, G.remoteIk, st.remoteIdentity, s0.sp - 152#64⟩
  try rw [hsp_sf_2]
  try rw [hsp_sf_1]
  try rw [hsp_sf]
  refine SepWP.fold (ent_of_eq (stackAt_remoteIk s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (remoteIdentityOkAt_some_split_sp152 s0.sp st.remoteIdentity rem hrem) (by sep_focus) ?_
  refine SepWP.fold (sp184_pair8_to_16 s0.sp _ _) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (pointsTo64_of_1_1_4_2_sp152 s0.sp _ _ _ _) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w152
  wp_steps
  refine SepWP.fold (sp352_344_pair32_to_64 s0.sp _ _ _ _) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (spe_missingRemote_at_sp152 A s0.sp (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) _ _ _ _ _ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; dsimp only [speWord]; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine SepWP.fold (ent_of_eq (stackAt_dropSpeX s0.sp)) (by sep_focus) ?_
  apply SepWP.done
    (by simp only [State.pc_setMem, State.pc_setPC])
    (by simp only [State.status_setMem, State.status_setPC, State.status_writeReg64,
      State.status_setPState, hrun_sf_2])
  intro hfrozen_call hsym_call
  have hsym_call' := hsym_call
  simp only [arm64_norm] at hsym_call'
  wp_call hdropSpe ⟨s0.sp - 152#64, [], .invalidSessionStructure .missingRemoteIdentity⟩
  try rw [hsp_sf_3]
  try rw [hsp_sf_2]
  try rw [hsp_sf_1]
  try rw [hsp_sf]
  refine SepWP.fold (ent_of_eq (stackAt_dropSpeX s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (memRegion48_split_dropSpe s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d8
  apply SepWP.exists_elim; intro d0
  refine SepWP.fold (ret24_split_srk ret v1.toList v1.toList_length) (by sep_focus) ?_
  refine SepWP.fold (ret56_split_priv ret v2.toList v2.toList_length) (by sep_focus) ?_
  refine SepWP.fold (ret88_split_localIk ret v3.toList v3.toList_length) (by sep_focus) ?_
  refine SepWP.fold (ret120_split_remoteIk ret v4.toList v4.toList_length) (by sep_focus) ?_
  refine SepWP.fold (ret152_split_ck ret v5.toList v5.toList_length) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_421_to_124_sp232 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_after_store_at_0_ret24 ret _ _ _ sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  wp_steps
  try rw [hsp_sf_4]
  try rw [hsp_sf_3]
  try rw [hsp_sf_2]
  try rw [hsp_sf_1]
  try rw [hsp_sf]
  have hmod := otrFrom_model_ok ⟨ss, G, st, ret⟩ hsc hver hrem
  have hmod1 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).1 =
      .ok ⟨sc.ratchetKey, sc.chainKey, st.previousCounter, st.pqRatchetState,
        BitVec.ofNat 8 st.version.toNat, st.localIdentity, rem⟩ :=
    congrArg Prod.fst hmod
  have hmod2 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).2 = { st with pqRatchetState := [] } :=
    congrArg Prod.snd hmod
  have hnopanic := otrFrom_model_no_panic ⟨ss, G, st, ret⟩
  rw [hmod1] at hnopanic
  have hagree : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩ } := rfl
  have hagree' : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩, sender := some sg } :=
    agreeExceptPq_of_sender G ⟨0#64, 1#64⟩ sg hGs
  refine FromSessionStateFacts.finish_otrFrom ⟨ss, G, st, ret⟩ { G with pq := ⟨0#64, 1#64⟩ } _ _
    hmod1 hmod2 hnopanic hagree (by wp_done) ?_
  refine FromSessionStateFacts.fold_entails (ret24_fold_srk ret sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine FromSessionStateFacts.fold_entails (ret56_fold_priv ret sc.ratchetKey.privateKey.bytes hpriv_clamp _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · generalize pack8 (List.take 1 sc.ratchetKey.privateKey.bytes.toList) = b; clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · generalize pack8 (List.drop 31 sc.ratchetKey.privateKey.bytes.toList) = b; clear * -; bv_kernel
  refine FromSessionStateFacts.fold_entails (ret88_fold_localIk ret st.localIdentity.publicKey.bytes.toList hlik_pk_len _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · have hhi : ∀ (v4 : BitVec 16) (v6 : BitVec 8),
        (v4.zeroExtend 64 ||| (v6.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32 =
          v4.zeroExtend 32 ||| (v6.zeroExtend 32 <<< 16) := by
      intro v4 v6; clear * -; bv_kernel
    rw [hhi]
    generalize pack32 (List.take 4 st.localIdentity.publicKey.bytes.toList) = v0
    generalize pack16 (List.take 2 (List.drop 4 st.localIdentity.publicKey.bytes.toList)) = v4
    generalize pack8 (List.take 1 (List.drop 6 st.localIdentity.publicKey.bytes.toList)) = v6
    clear * -; bv_kernel
  · have hhi : ∀ (v4 : BitVec 16) (v6 : BitVec 8),
        (v4.zeroExtend 64 ||| (v6.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32 =
          v4.zeroExtend 32 ||| (v6.zeroExtend 32 <<< 16) := by
      intro v4 v6; clear * -; bv_kernel
    rw [hhi]
    generalize pack32 (List.take 4 st.localIdentity.publicKey.bytes.toList) = v0
    generalize pack16 (List.take 2 (List.drop 4 st.localIdentity.publicKey.bytes.toList)) = v4
    generalize pack8 (List.take 1 (List.drop 6 st.localIdentity.publicKey.bytes.toList)) = v6
    clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine FromSessionStateFacts.fold_entails (ret120_fold_remoteIk ret rem.publicKey.bytes.toList hrem_pk_len _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine FromSessionStateFacts.fold_entails (ret152_fold_ck ret (keyToBytes32 sc.chainKey.key) hck_key_len _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine FromSessionStateFacts.fold_entails (otrResultAt_ok_intro A ret G.pq sc st rem _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine FromSessionStateFacts.fold_entails (sevenBytes_124_to_421_sp232 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (memRegion56_fold_ok s0.sp _ _) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (FromSessionStateFacts.frame15_fold_16 s0.sp _ _ _) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (frame33_fold s0.sp _ _ _ _ _) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (frame128_fold_phaseB_64 s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (frame288_fold_phaseA s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (pq_empty_cells_intro A ss) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (sessionStateAt_from_some_pq_empty_fold A ss G st sg sc hGs hsc hinv1 hdeser_srk hpriv_eq hpriv_clamp hsrk_len) (by sep_focus) ?_
  exact ent_of_eq (by ac_rfl)

theorem otrFrom_case4_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : DeserializeExtOk img.base ext)
    (hRemIk : RemoteIdentityKeyExtOk img A ext)
    (hDropSpe : DropSpeExtOk img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrFromName)
      (otrFromCaseSpec A img
        (fun x => ∃ sc rem, x.st.senderChain = some sc ∧
          ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = some rem)) :=
  otrFrom_case4_ok_ext_x himg hDeser hRemIk (DropSpeExtOkX.of_DropSpeExtOk hDropSpe)

theorem otrFrom_case4_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : DeserializeOk img.base C ctl abs)
    (hRemIk : RemoteIdentityKeyOk img C A ctl abs)
    (hDropSpe : DropSpeOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr otrFromName)
      (otrFromCaseSpec A img
        (fun x => ∃ sc rem, x.st.senderChain = some sc ∧
          ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = some rem)) :=
  otrFrom_case4_ok_ext himg hDeser hRemIk hDropSpe

/-! ## Relocatable `[LibsignalPlacement]` Case 4 (`st.remoteIdentity = some rem`) -/

set_option maxHeartbeats 3200000 in
theorem otrFrom_case4_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdeser : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec)
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (hdropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec A))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromCasePlacedSpec A
        (fun x => ∃ sc rem, x.st.senderChain = some sc ∧
          ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = some rem)) := by
  dsimp only [otrFromCasePlacedSpec, otrFromRawPlacedSpec]
  have hpkTryFrom := pkTryFromOk_placed_ok_at (prog := (blkPC_211).rebase (blkPl_211).base H)
  wp_init
  obtain ⟨ss, G, st, ret⟩ := a
  dsimp only at *
  rcases h_1 with ⟨sc, rem, hsc, hver, hrem⟩
  apply sepWP_seq_lscl_ro h_2 h_3 (mid := lsmpl.base 201)
  refine SepWP.add_rodata (fun hm => rodata_missingRemoteIdentity_placed_intro h_3 hm) ?_
  refine SepWP.fold (sessionStateAt_sender_some A ss G st sc hsc) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro sg
  refine SepWP.focus_pure (by sep_focus) fun hGs => ?_
  conv =>
    arg 4
    rw [sessionStateAt_eq_from_some_self A ss G st sg sc hGs hsc,
        sessionStateAt_eq_from_some A ss G st sg sc hGs hsc G.pq st.pqRatchetState,
        stackAt_prologue s0.sp,
        frame288_split_phaseA s0.sp,
        memRegion40_split_deser_sp s0.sp,
        ret200_split_ok ret]
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro r11; apply SepWP.exists_elim; intro r10
  apply SepWP.exists_elim; intro r9; apply SepWP.exists_elim; intro r8
  apply SepWP.exists_elim; intro r7; apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5; apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3; apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1; apply SepWP.exists_elim; intro r0
  apply SepWP.exists_elim; intro v_deser; apply SepWP.exists_elim; intro tag0_deser
  apply SepWP.exists_elim; intro ue0; apply SepWP.exists_elim; intro ud8
  apply SepWP.exists_elim; intro uc8; apply SepWP.exists_elim; intro uc0
  apply SepWP.exists_elim; intro u9e; apply SepWP.exists_elim; intro u9c
  apply SepWP.exists_elim; intro u98; apply SepWP.exists_elim; intro u90
  apply SepWP.exists_elim; intro u88; apply SepWP.exists_elim; intro u84
  apply SepWP.exists_elim; intro u80; apply SepWP.exists_elim; intro ver0
  apply SepWP.exists_elim; intro pc0; apply SepWP.exists_elim; intro idx0
  apply SepWP.exists_elim; intro v5; apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w0
  refine SepWP.focus_pure (by sep_focus) fun hinv1 => ?_
  refine SepWP.focus_pure (by sep_focus) fun hinv2 => ?_
  obtain ⟨hdeser_lik, hrem_inv, hchains_len, hpend_some, hreg_len, _, _⟩ := id hinv1
  have hrem_inv' : PublicKey.deserialize G.remoteIk.bytes = .ok rem.publicKey := by
    rwa [hrem] at hrem_inv
  rcases hinv2 with ⟨hdeser_srk, hpriv_eq, hpriv_clamp, hsrk_len⟩
  refine SepWP.fold (vecU8Buf_bounds A G.localIk.cap G.localIk.ptr G.localIk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hlik_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.srk.cap sg.srk.ptr sg.srk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hsrk_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.priv.cap sg.priv.ptr sg.priv.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpriv_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hck_bds => ?_
  obtain ⟨_, hlik_ge33⟩ :=
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_deserialize_ok_inversion hdeser_lik
  have hlik_cap_ne0 : G.localIk.cap ≠ 0 := vecU8_cap_ne_zero_of_ge hlik_bds.1 (by omega)
  have hlik_len_lt : G.localIk.bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hlik_bds.1 hlik_bds.2.1
  have hlik_len_toNat : (BitVec.ofNat 64 G.localIk.bytes.length).toNat = G.localIk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlik_pk_len : st.localIdentity.publicKey.bytes.toList.length = 32 :=
    st.localIdentity.publicKey.bytes.toList_length
  obtain ⟨_, hsrk_ge33⟩ :=
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_deserialize_ok_inversion hdeser_srk
  have hsrk_cap_ne0 : sg.srk.cap ≠ 0 := vecU8_cap_ne_zero_of_ge hsrk_bds.1 (by omega)
  have hsrk_ne_neg1 : (sg.srk.cap + 1#64 == 0#64) = false := addsPState64_neg1_eq_false hsrk_bds.2.1
  have hsrk_len_lt : sg.srk.bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hsrk_bds.1 hsrk_bds.2.1
  have hsrk_len_toNat : (BitVec.ofNat 64 sg.srk.bytes.length).toNat = sg.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_len : sg.priv.bytes.length = 32 := by rw [hpriv_eq, List.Vector.toList_length]
  have hpriv_cap_ne0 : sg.priv.cap ≠ 0 := vecU8_cap_ne_zero_of_ge hpriv_bds.1 (by omega)
  have hck_cap_ne0 : sg.ck.cap ≠ 0 := by
    have h1 := hck_bds.1; rw [keyToBytes32_length] at h1
    exact vecU8_cap_ne_zero_of_ge h1 (by decide)
  have hck_ne_neg1 : (sg.ck.cap + 1#64 == 0#64) = false := addsPState64_neg1_eq_false hck_bds.2.1
  have hv_deser_len : v_deser.toList.length = 32 := v_deser.toList_length
  have hsrk_pk_len : sc.ratchetKey.publicKey.bytes.toList.length = 32 :=
    sc.ratchetKey.publicKey.bytes.toList_length
  have hpriv_pk_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
    sc.ratchetKey.privateKey.bytes.toList_length
  have hrem_pk_len : rem.publicKey.bytes.toList.length = 32 :=
    rem.publicKey.bytes.toList_length
  have hck_key_len : (keyToBytes32 sc.chainKey.key).length = 32 :=
    keyToBytes32_length sc.chainKey.key
  have hver_ls :
      ConditionHolds CondCode.LS
        (subsPState32 (if (st.sessionVersion == 0#32) = true then 2#32 else st.sessionVersion) 255#32) =
      true := by
    rw [version_word_eq st, subsPState32_255_ls_iff st.version, decide_eq_true_eq]
    exact hver
  conv =>
    arg 4
    rw [vecU8Buf_eq_bytes_live_of_ne_zero A G.localIk.cap G.localIk.ptr G.localIk.bytes hlik_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.priv.cap sg.priv.ptr sg.priv.bytes hpriv_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0,
        hpriv_eq, hpriv_pk_len,
        bytes32_eq_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len,
        bytes32_eq_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len]
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_1 hro_1
  apply sepWP_seq_lscl_ro hcl_1 hro_1 (mid := lsmpl.base 211)
  wp_call (lscall_blk (callerProg := (blkPC_19).rebase (blkPl_19).base H) hdeser hcl_1)
    (sg.srk.ptr, sg.srk.bytes, sc.ratchetKey.publicKey,
    s0.sp - 152#64, tag0_deser, v_deser.toList)
  refine SepWP.fold (bytes32_split_sp151 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_421_to_124_sp151 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_after_store_at_0_sp232 s0.sp u9c u9e sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps 33
  refine SepWP.fold (sevenBytes_124_to_421_sp232 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  refine SepWP.fold (sret_srk_entails_memRegion40 s0.sp _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (memRegion40_split_ck_sp_entails s0.sp) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro c3; apply SepWP.exists_elim; intro c2; apply SepWP.exists_elim; intro c0
  wp_steps
  refine SepWP.fold (elevenBytes_218_to_821_sp152 s0.sp (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (frame128_split_phaseB s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro s78; apply SepWP.exists_elim; intro s70
  apply SepWP.exists_elim; intro s68; apply SepWP.exists_elim; intro s64
  apply SepWP.exists_elim; intro s60; apply SepWP.exists_elim; intro s5c
  apply SepWP.exists_elim; intro s50; apply SepWP.exists_elim; intro s48
  apply SepWP.exists_elim; intro s40; apply SepWP.exists_elim; intro s38
  apply SepWP.exists_elim; intro s30; apply SepWP.exists_elim; intro s2c
  apply SepWP.exists_elim; intro s28; apply SepWP.exists_elim; intro s24
  apply SepWP.exists_elim; intro s20; apply SepWP.exists_elim; intro s18
  apply SepWP.exists_elim; intro s10; apply SepWP.exists_elim; intro s08
  apply SepWP.exists_elim; intro s00
  refine SepWP.fold (ent_of_eq (frame33_split s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro ub8; apply SepWP.exists_elim; intro ub4
  apply SepWP.exists_elim; intro ub0; apply SepWP.exists_elim; intro ua8
  apply SepWP.exists_elim; intro ua0
  refine SepWP.fold (ent_of_eq (frame15_split s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro ud4; apply SepWP.exists_elim; intro ud0; apply SepWP.exists_elim; intro uc9
  wp_steps
  refine SepWP.fold (ck_scratch_entails_memRegion40_sp152 s0.sp _ _ _) (by sep_focus) ?_
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_2 hro_2
  apply sepWP_seq_lscl_ro hcl_2 hro_2 (mid := lsmpl.base 29)
  wp_call (lscall_blk_cl (callerProg := (blkPC_19).rebase (blkPl_19).base H) (spec := pkTryFromOkPlacedSpec) hpkTryFrom hcl_2)
    (G.localIk.ptr, G.localIk.bytes, st.localIdentity.publicKey, s0.sp - 152#64)
  refine SepWP.fold (bytes32_split_localIk_sp151 s0.sp st.localIdentity.publicKey.bytes.toList hlik_pk_len) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A G.localIk.cap G.localIk.ptr G.localIk.bytes hlik_cap_ne0) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sret_localIk_entails_memRegion34_6 s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (stackAt_remoteIk s0.sp)) (by sep_focus) ?_
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_3 hro_3
  apply sepWP_seq_lscl_ro hcl_3 hro_3 (mid := lsmpl.base 5)
  wp_call (lscall_blk_cl (callerProg := (blkPC_19).rebase (blkPl_19).base H) (spec := remoteIdentityKeyPlacedSpec A) hremIk hcl_3)
    ⟨ss, G.remoteIk, st.remoteIdentity, s0.sp - 152#64⟩
  try rw [hsp_sf_2]
  try rw [hsp_sf_1]
  try rw [hsp_sf]
  refine SepWP.fold (ent_of_eq (stackAt_remoteIk s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (remoteIdentityOkAt_some_split_sp152 s0.sp st.remoteIdentity rem hrem) (by sep_focus) ?_
  refine SepWP.fold (sp184_pair8_to_16 s0.sp _ _) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (pointsTo64_of_1_1_4_2_sp152 s0.sp _ _ _ _) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w152
  wp_steps
  refine SepWP.fold (sp352_344_pair32_to_64 s0.sp _ _ _ _) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (spe_missingRemote_at_sp152 A s0.sp (lsρ missingRemoteIdentitySym) _ _ _ _ _ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; dsimp only [speWord]; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine SepWP.fold (ent_of_eq (stackAt_dropSpe s0.sp)) (by sep_focus) ?_
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_4 hro_4
  wp_call (lscall_blk_ro (callerProg := (blkPC_19).rebase (blkPl_19).base H) (spec := dropSpeSpec A) hdropSpe hcl_4 hro_4)
    ⟨s0.sp - 152#64, [], .invalidSessionStructure .missingRemoteIdentity⟩
  try rw [hsp_sf_3]
  try rw [hsp_sf_2]
  try rw [hsp_sf_1]
  try rw [hsp_sf]
  refine SepWP.fold (ent_of_eq (stackAt_dropSpe s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (memRegion48_split_dropSpe s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d8
  apply SepWP.exists_elim; intro d0
  refine SepWP.fold (ret24_split_srk ret v1.toList v1.toList_length) (by sep_focus) ?_
  refine SepWP.fold (ret56_split_priv ret v2.toList v2.toList_length) (by sep_focus) ?_
  refine SepWP.fold (ret88_split_localIk ret v3.toList v3.toList_length) (by sep_focus) ?_
  refine SepWP.fold (ret120_split_remoteIk ret v4.toList v4.toList_length) (by sep_focus) ?_
  refine SepWP.fold (ret152_split_ck ret v5.toList v5.toList_length) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_421_to_124_sp232 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_after_store_at_0_ret24 ret _ _ _ sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  wp_steps
  try rw [hsp_sf_4]
  try rw [hsp_sf_3]
  try rw [hsp_sf_2]
  try rw [hsp_sf_1]
  try rw [hsp_sf]
  have hmod := otrFrom_model_ok ⟨ss, G, st, ret⟩ hsc hver hrem
  have hmod1 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).1 =
      .ok ⟨sc.ratchetKey, sc.chainKey, st.previousCounter, st.pqRatchetState,
        BitVec.ofNat 8 st.version.toNat, st.localIdentity, rem⟩ :=
    congrArg Prod.fst hmod
  have hmod2 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).2 = { st with pqRatchetState := [] } :=
    congrArg Prod.snd hmod
  have hnopanic := otrFrom_model_no_panic ⟨ss, G, st, ret⟩
  rw [hmod1] at hnopanic
  have hagree : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩ } := rfl
  have hagree' : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩, sender := some sg } :=
    agreeExceptPq_of_sender G ⟨0#64, 1#64⟩ sg hGs
  refine FromSessionStateFacts.finish_otrFrom_placed ⟨ss, G, st, ret⟩ { G with pq := ⟨0#64, 1#64⟩ } _ _
    hmod1 hmod2 hnopanic hagree (by wp_done) ?_
  refine FromSessionStateFacts.fold_entails (ret24_fold_srk ret sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine FromSessionStateFacts.fold_entails (ret56_fold_priv ret sc.ratchetKey.privateKey.bytes hpriv_clamp _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · generalize pack8 (List.take 1 sc.ratchetKey.privateKey.bytes.toList) = b; clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · generalize pack8 (List.drop 31 sc.ratchetKey.privateKey.bytes.toList) = b; clear * -; bv_kernel
  refine FromSessionStateFacts.fold_entails (ret88_fold_localIk ret st.localIdentity.publicKey.bytes.toList hlik_pk_len _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · have hhi : ∀ (v4 : BitVec 16) (v6 : BitVec 8),
        (v4.zeroExtend 64 ||| (v6.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32 =
          v4.zeroExtend 32 ||| (v6.zeroExtend 32 <<< 16) := by
      intro v4 v6; clear * -; bv_kernel
    rw [hhi]
    generalize pack32 (List.take 4 st.localIdentity.publicKey.bytes.toList) = v0
    generalize pack16 (List.take 2 (List.drop 4 st.localIdentity.publicKey.bytes.toList)) = v4
    generalize pack8 (List.take 1 (List.drop 6 st.localIdentity.publicKey.bytes.toList)) = v6
    clear * -; bv_kernel
  · have hhi : ∀ (v4 : BitVec 16) (v6 : BitVec 8),
        (v4.zeroExtend 64 ||| (v6.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32 =
          v4.zeroExtend 32 ||| (v6.zeroExtend 32 <<< 16) := by
      intro v4 v6; clear * -; bv_kernel
    rw [hhi]
    generalize pack32 (List.take 4 st.localIdentity.publicKey.bytes.toList) = v0
    generalize pack16 (List.take 2 (List.drop 4 st.localIdentity.publicKey.bytes.toList)) = v4
    generalize pack8 (List.take 1 (List.drop 6 st.localIdentity.publicKey.bytes.toList)) = v6
    clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine FromSessionStateFacts.fold_entails (ret120_fold_remoteIk ret rem.publicKey.bytes.toList hrem_pk_len _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine FromSessionStateFacts.fold_entails (ret152_fold_ck ret (keyToBytes32 sc.chainKey.key) hck_key_len _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine FromSessionStateFacts.fold_entails (otrResultAt_ok_intro A ret G.pq sc st rem _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine FromSessionStateFacts.fold_entails (sevenBytes_124_to_421_sp232 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (memRegion56_fold_ok s0.sp _ _) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (FromSessionStateFacts.frame15_fold_16 s0.sp _ _ _) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (frame33_fold s0.sp _ _ _ _ _) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (frame128_fold_phaseB_64 s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (frame288_fold_phaseA s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (pq_empty_cells_intro A ss) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (sessionStateAt_from_some_pq_empty_fold A ss G st sg sc hGs hsc hinv1 hdeser_srk hpriv_eq hpriv_clamp hsrk_len) (by sep_focus) ?_
  exact ent_of_eq (by ac_rfl)

theorem otrFrom_case4_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (hdropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec A))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromCasePlacedSpec A
        (fun x => ∃ sc rem, x.st.senderChain = some sc ∧
          ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = some rem)) :=
  otrFrom_case4_placed_ok_of_contracts
    (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_placed_ok H)
    hremIk hdropSpe

end CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
