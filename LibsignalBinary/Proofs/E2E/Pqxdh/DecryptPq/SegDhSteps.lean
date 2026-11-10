/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem split_sp_20_for_stepA (sp : BitVec 64) :
    memRegion sp 0x20 =
      (memRegion sp 0x10 ∗
       (∃∗ u10 : BitVec 32, (sp + 0x10#64) ↦₃₂ u10) ∗
       memRegion (sp + 0x14#64) 8 ∗
       (∃∗ u1c : BitVec 32, (sp + 0x1c#64) ↦₃₂ u1c)) := by
  rw [memRegion_split' (b := sp) (b' := sp + 0x10#64) (n := 0x10) (k :=
      0x10) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x10#64) (b' := sp + 0x14#64) (n := 4) (k :=
        12) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x14#64) (b' := sp + 0x1c#64) (n := 8) (k :=
        4) rfl (by bv_arith) (by decide),
      memRegion_four (sp + 0x10#64), memRegion_four (sp + 0x1c#64)]

theorem split_1d8_for_stepA (sp : BitVec 64) :
    memRegion (sp + 0x1d8#64) 0x3a8 =
      (memRegion (sp + 0x1d8#64) 0x1f8 ∗
       (∃∗ u3d0 : BitVec 64, (sp + 0x3d0#64) ↦₆₄ u3d0) ∗
       (∃∗ u3d8 : BitVec 64, (sp + 0x3d8#64) ↦₆₄ u3d8) ∗
       (∃∗ u3e0 : BitVec 32, (sp + 0x3e0#64) ↦₃₂ u3e0) ∗
       (∃∗ u3e4 : BitVec 64, (sp + 0x3e4#64) ↦₆₄ u3e4) ∗
       (∃∗ u3ec : BitVec 64, (sp + 0x3ec#64) ↦₆₄ u3ec) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       (∃∗ u400 : BitVec 64, (sp + 0x400#64) ↦₆₄ u400) ∗
       (∃∗ u408 : BitVec 64, (sp + 0x408#64) ↦₆₄ u408) ∗
       memRegion (sp + 0x410#64) 0x30 ∗
       (∃∗ u440 : BitVec 64, (sp + 0x440#64) ↦₆₄ u440) ∗
       (∃∗ u448 : BitVec 64, (sp + 0x448#64) ↦₆₄ u448) ∗
       memRegion (sp + 0x450#64) 0x50 ∗
       (∃∗ u4a0 : BitVec 32, (sp + 0x4a0#64) ↦₃₂ u4a0) ∗
       (∃∗ u4a4 : BitVec 64, (sp + 0x4a4#64) ↦₆₄ u4a4) ∗
       (∃∗ u4ac : BitVec 64, (sp + 0x4ac#64) ↦₆₄ u4ac) ∗
       (∃∗ u4b4 : BitVec 64, (sp + 0x4b4#64) ↦₆₄ u4b4) ∗
       (∃∗ u4bc : BitVec 32, (sp + 0x4bc#64) ↦₃₂ u4bc) ∗
       (∃∗ u4c0 : BitVec 64, (sp + 0x4c0#64) ↦₆₄ u4c0) ∗
       (∃∗ u4c8 : BitVec 64, (sp + 0x4c8#64) ↦₆₄ u4c8) ∗
       (∃∗ u4d0 : BitVec 64, (sp + 0x4d0#64) ↦₆₄ u4d0) ∗
       (∃∗ u4d8 : BitVec 64, (sp + 0x4d8#64) ↦₆₄ u4d8) ∗
       memRegion (sp + 0x4e0#64) 0x20 ∗
       (∃∗ u500 : BitVec 64, (sp + 0x500#64) ↦₆₄ u500) ∗
       (∃∗ u508 : BitVec 64, (sp + 0x508#64) ↦₆₄ u508) ∗
       (∃∗ u510 : BitVec 32, (sp + 0x510#64) ↦₃₂ u510) ∗
       memRegion (sp + 0x514#64) 0x6c) := by
  rw [memRegion_split' (b := sp + 0x1d8#64) (b' := sp + 0x3d0#64) (n := 0x1f8) (k :=
      0x1b0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3d0#64) (b' := sp + 0x3d8#64) (n := 8) (k :=
        0x1a8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3d8#64) (b' := sp + 0x3e0#64) (n := 8) (k :=
        0x1a0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3e0#64) (b' := sp + 0x3e4#64) (n := 4) (k :=
        0x19c) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3e4#64) (b' := sp + 0x3ec#64) (n := 8) (k :=
        0x194) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3ec#64) (b' := sp + 0x3f4#64) (n := 8) (k :=
        0x18c) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3f4#64) (b' := sp + 0x400#64) (n := 12) (k :=
        0x180) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x400#64) (b' := sp + 0x408#64) (n := 8) (k :=
        0x178) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x408#64) (b' := sp + 0x410#64) (n := 8) (k :=
        0x170) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x410#64) (b' := sp + 0x440#64) (n := 0x30) (k :=
        0x140) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x440#64) (b' := sp + 0x448#64) (n := 8) (k :=
        0x138) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x448#64) (b' := sp + 0x450#64) (n := 8) (k :=
        0x130) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x450#64) (b' := sp + 0x4a0#64) (n := 0x50) (k :=
        0xe0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4a0#64) (b' := sp + 0x4a4#64) (n := 4) (k :=
        0xdc) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4a4#64) (b' := sp + 0x4ac#64) (n := 8) (k :=
        0xd4) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4ac#64) (b' := sp + 0x4b4#64) (n := 8) (k :=
        0xcc) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4b4#64) (b' := sp + 0x4bc#64) (n := 8) (k :=
        0xc4) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4bc#64) (b' := sp + 0x4c0#64) (n := 4) (k :=
        0xc0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4c0#64) (b' := sp + 0x4c8#64) (n := 8) (k :=
        0xb8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4c8#64) (b' := sp + 0x4d0#64) (n := 8) (k :=
        0xb0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4d0#64) (b' := sp + 0x4d8#64) (n := 8) (k :=
        0xa8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4d8#64) (b' := sp + 0x4e0#64) (n := 8) (k :=
        0xa0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4e0#64) (b' := sp + 0x500#64) (n := 0x20) (k :=
        0x80) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x500#64) (b' := sp + 0x508#64) (n := 8) (k :=
        0x78) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x508#64) (b' := sp + 0x510#64) (n := 8) (k :=
        0x70) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x510#64) (b' := sp + 0x514#64) (n := 4) (k :=
        0x6c) rfl (by bv_arith) (by decide),
      memRegion_eight (sp + 0x3d0#64), memRegion_eight (sp + 0x3d8#64),
        memRegion_four (sp + 0x3e0#64),
      memRegion_eight (sp + 0x3e4#64), memRegion_eight (sp + 0x3ec#64),
      memRegion_eight (sp + 0x400#64), memRegion_eight (sp + 0x408#64),
      memRegion_eight (sp + 0x440#64), memRegion_eight (sp + 0x448#64),
      memRegion_four (sp + 0x4a0#64), memRegion_eight (sp + 0x4a4#64),
        memRegion_eight (sp + 0x4ac#64),
      memRegion_eight (sp + 0x4b4#64), memRegion_four (sp + 0x4bc#64),
      memRegion_eight (sp + 0x4c0#64), memRegion_eight (sp + 0x4c8#64),
      memRegion_eight (sp + 0x4d0#64), memRegion_eight (sp + 0x4d8#64),
      memRegion_eight (sp + 0x500#64), memRegion_eight (sp + 0x508#64),
        memRegion_four (sp + 0x510#64)]

theorem fold_after_778 (sp : BitVec 64)
    (r0 r4 c2 : BitVec 32)
    (r1 r2 r3 c0 c1 c3 c4 : BitVec 64) :
    (((sp + 0x190#64) ↦₃₂ 0#32) ∗
     ((sp + 0x194#64) ↦₃₂ r0) ∗ ((sp + 0x198#64) ↦₆₄ r1) ∗
     ((sp + 0x1a0#64) ↦₆₄ r2) ∗ ((sp + 0x1a8#64) ↦₆₄ r3) ∗
     ((sp + 0x1b0#64) ↦₃₂ r4) ∗
     ((sp + 0x1b4#64) ↦₆₄ c0) ∗ ((sp + 0x1bc#64) ↦₆₄ c1) ∗
     ((sp + 0x1c4#64) ↦₃₂ c2) ∗ ((sp + 0x1c8#64) ↦₆₄ c3) ∗
     ((sp + 0x1d0#64) ↦₆₄ c4) ∗
     memRegion (sp + 0x1d8#64) 0x1f8 ∗
     ((sp + 0x400#64) ↦₆₄ c0) ∗ ((sp + 0x408#64) ↦₆₄ c1) ∗
     memRegion (sp + 0x410#64) 0x30 ∗
     ((sp + 0x440#64) ↦₆₄ c3) ∗ ((sp + 0x448#64) ↦₆₄ c4) ∗
     memRegion (sp + 0x450#64) 0x50 ∗
     ((sp + 0x500#64) ↦₆₄ r2) ∗ ((sp + 0x508#64) ↦₆₄ r3) ∗
     ((sp + 0x510#64) ↦₃₂ r4) ∗
     memRegion (sp + 0x514#64) 0x6c) ⊢
    (memRegion (sp + 0x190#64) 0x20 ∗
     memRegion (sp + 0x1b0#64) 0x220 ∗
     memRegion (sp + 0x400#64) 0xa0 ∗
     memRegion (sp + 0x500#64) 0x80) := by
  have h190 : (((sp + 0x190#64) ↦₃₂ 0#32) ∗ ((sp + 0x194#64) ↦₃₂ r0) ∗
      ((sp + 0x198#64) ↦₆₄ r1) ∗ ((sp + 0x1a0#64) ↦₆₄ r2) ∗ ((sp + 0x1a8#64) ↦₆₄ r3)) ⊢
      memRegion (sp + 0x190#64) 0x20 := by
    rw [memRegion_split' (b := sp + 0x190#64) (b' := sp + 0x194#64) (n := 4) (k :=
        28) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x194#64) (b' := sp + 0x198#64) (n := 4) (k :=
          24) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x198#64) (b' := sp + 0x1a0#64) (n := 8) (k :=
          16) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1a0#64) (b' := sp + 0x1a8#64) (n := 8) (k :=
          8) rfl (by bv_arith) (by decide)]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (pointsTo64_entails_memRegion _ _))))
  have h1b0 : (((sp + 0x1b0#64) ↦₃₂ r4) ∗ ((sp + 0x1b4#64) ↦₆₄ c0) ∗
      ((sp + 0x1bc#64) ↦₆₄ c1) ∗ ((sp + 0x1c4#64) ↦₃₂ c2) ∗
      ((sp + 0x1c8#64) ↦₆₄ c3) ∗ ((sp + 0x1d0#64) ↦₆₄ c4) ∗
      memRegion (sp + 0x1d8#64) 0x1f8) ⊢
      memRegion (sp + 0x1b0#64) 0x220 := by
    rw [memRegion_split' (b := sp + 0x1b0#64) (b' := sp + 0x1b4#64) (n := 4) (k :=
        0x21c) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1b4#64) (b' := sp + 0x1bc#64) (n := 8) (k :=
          0x214) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1bc#64) (b' := sp + 0x1c4#64) (n := 8) (k :=
          0x20c) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1c4#64) (b' := sp + 0x1c8#64) (n := 4) (k :=
          0x208) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1c8#64) (b' := sp + 0x1d0#64) (n := 8) (k :=
          0x200) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1d0#64) (b' := sp + 0x1d8#64) (n := 8) (k :=
          0x1f8) rfl (by bv_arith) (by decide)]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))))
  have h400 : (((sp + 0x400#64) ↦₆₄ c0) ∗ ((sp + 0x408#64) ↦₆₄ c1) ∗
      memRegion (sp + 0x410#64) 0x30 ∗
      ((sp + 0x440#64) ↦₆₄ c3) ∗ ((sp + 0x448#64) ↦₆₄ c4) ∗
      memRegion (sp + 0x450#64) 0x50) ⊢
      memRegion (sp + 0x400#64) 0xa0 := by
    rw [memRegion_split' (b := sp + 0x400#64) (b' := sp + 0x408#64) (n := 8) (k :=
        0x98) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x408#64) (b' := sp + 0x410#64) (n := 8) (k :=
          0x90) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x410#64) (b' := sp + 0x440#64) (n := 0x30) (k :=
          0x60) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x440#64) (b' := sp + 0x448#64) (n := 8) (k :=
          0x58) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x448#64) (b' := sp + 0x450#64) (n := 8) (k :=
          0x50) rfl (by bv_arith) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))))
  have h500 : (((sp + 0x500#64) ↦₆₄ r2) ∗ ((sp + 0x508#64) ↦₆₄ r3) ∗
      ((sp + 0x510#64) ↦₃₂ r4) ∗ memRegion (sp + 0x514#64) 0x6c) ⊢
      memRegion (sp + 0x500#64) 0x80 := by
    rw [memRegion_split' (b := sp + 0x500#64) (b' := sp + 0x508#64) (n := 8) (k :=
        0x78) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x508#64) (b' := sp + 0x510#64) (n := 8) (k :=
          0x70) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x510#64) (b' := sp + 0x514#64) (n := 4) (k :=
          0x6c) rfl (by bv_arith) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo32_entails_memRegion _ _)))
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono h190 (sepConj_mono h1b0 (sepConj_mono h400 h500)))

theorem length_chainKeyBytes (ck : ChainKey) : (chainKeyBytes ck).length = 36 := by
  simp [chainKeyBytes, keyToBytes32, leBytes]

theorem split_32_four_64 (a : BitVec 64) :
    memRegion a 32 =
      ((∃∗ u0 : BitVec 64, a ↦₆₄ u0) ∗
       (∃∗ u1 : BitVec 64, (a + 8#64) ↦₆₄ u1) ∗
       (∃∗ u2 : BitVec 64, (a + 16#64) ↦₆₄ u2) ∗
       (∃∗ u3 : BitVec 64, (a + 24#64) ↦₆₄ u3)) := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 24) rfl (by bv_arith) (by decide),
      memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k :=
        16) rfl (by bv_arith) (by decide),
      memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k :=
        8) rfl (by bv_arith) (by decide),
      memRegion_eight a, memRegion_eight (a + 8#64), memRegion_eight (a + 16#64),
        memRegion_eight (a + 24#64)]

theorem fold_32_four_64 (a : BitVec 64) (u0 u1 u2 u3 : BitVec 64) :
    ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3)) ⊢
    memRegion a 32 := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 24) rfl (by bv_arith) (by decide),
      memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k :=
        16) rfl (by bv_arith) (by decide),
      memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k :=
        8) rfl (by bv_arith) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo64_entails_memRegion _ _)))

theorem clamp_byte0 (b0 : BitVec 8) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b0 &&& 1065151889656#64) = b0 &&& 0xf8#8 := by
  bv_slice

theorem clamp_byte31 (b31 : BitVec 8) :
    BitVec.zeroExtend 8 (64#64 ||| BitVec.zeroExtend 64 b31 >>> 0 &&& 63#64) =
      (b31 &&& 0x7f#8) ||| 0x40#8 := by
  bv_slice

theorem split_400_500_for_keygen (sp : BitVec 64) :
    (memRegion (sp + 0x400#64) 0xa0 ∗ memRegion (sp + 0x500#64) 0x80) =
      (memRegion (sp + 0x400#64) 32 ∗
       memRegion (sp + 0x420#64) 32 ∗
       memRegion (sp + 0x440#64) 0x60 ∗
       memRegion (sp + 0x500#64) 32 ∗
       memRegion (sp + 0x520#64) 0x60) := by
  rw [memRegion_split' (b := sp + 0x400#64) (b' := sp + 0x420#64) (n := 32) (k :=
      0x80) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x420#64) (b' := sp + 0x440#64) (n := 32) (k :=
        0x60) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x500#64) (b' := sp + 0x520#64) (n := 32) (k :=
        0x60) rfl (by bv_arith) (by decide)]
  ac_rfl

theorem split_190_4e0_for_cc2 (sp : BitVec 64) :
    (memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 0x220 ∗
     memRegion (sp + 0x4e0#64) 0x20 ∗ memRegion (sp + 0x500#64) 32 ∗
       memRegion (sp + 0x520#64) 0x60) =
      (memRegion (sp + 0x190#64) 72 ∗
       memRegion (sp + 0x1d8#64) 0x1f8 ∗
       memRegion (sp + 0x4e0#64) 0xa0) := by
  have h190 : (memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 0x220) =
      (memRegion (sp + 0x190#64) 72 ∗ memRegion (sp + 0x1d8#64) 0x1f8) := by
    rw [← memRegion_split' (b := sp + 0x190#64) (b' := sp + 0x1b0#64) (n := 32) (k :=
        0x220) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x190#64) (b' := sp + 0x1d8#64) (n := 72) (k :=
          0x1f8) rfl (by bv_arith) (by decide)]
  have h4e0 : (memRegion (sp + 0x4e0#64) 0x20 ∗ memRegion (sp + 0x500#64) 32 ∗
      memRegion (sp + 0x520#64) 0x60) =
      memRegion (sp + 0x4e0#64) 0xa0 := by
    rw [memRegion_split' (b := sp + 0x4e0#64) (b' := sp + 0x500#64) (n := 0x20) (k :=
        0x80) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x500#64) (b' := sp + 0x520#64) (n := 32) (k :=
          0x60) rfl (by bv_arith) (by decide)]
  rw [← sepConj_assoc, h190, sepConj_assoc, h4e0]

theorem fold_after_cc2_ok (sp : BitVec 64) (rk1 : RootKey) :
    (memRegion (sp + 0x1d8#64) 0x1f8 ∗
     memRegion (sp + 0x440#64) 0x60 ∗
     ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1)) ⊢
    (memRegion (sp + 0x1d8#64) 0xd8 ∗
     memRegion (sp + 0x2b0#64) 0x10 ∗
     memRegion (sp + 0x2c0#64) 0x110 ∗
     memRegion (sp + 0x440#64) 0x80) := by
  have h1d8 : memRegion (sp + 0x1d8#64) 0x1f8 =
      (memRegion (sp + 0x1d8#64) 0xd8 ∗ memRegion (sp + 0x2b0#64) 0x10 ∗
        memRegion (sp + 0x2c0#64) 0x110) := by
    rw [memRegion_split' (b := sp + 0x1d8#64) (b' := sp + 0x2b0#64) (n := 0xd8) (k :=
        0x120) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x2b0#64) (b' := sp + 0x2c0#64) (n := 0x10) (k :=
          0x110) rfl (by bv_arith) (by decide)]
  have h440 : (memRegion (sp + 0x440#64) 0x60 ∗ ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1)) ⊢
      memRegion (sp + 0x440#64) 0x80 := by
    have hrk := pointsToBytes_entails_memRegion (sp + 0x4a0#64) (keyToBytes32 rk1)
    rw [length_keyToBytes32] at hrk
    rw [memRegion_split' (b := sp + 0x440#64) (b' := sp + 0x4a0#64) (n := 0x60) (k :=
        32) rfl (by bv_arith) (by decide)]
    exact sepConj_mono_right hrk
  rw [h1d8, sepConj_assoc, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h440))

theorem fold_1d8_after_cc2_err (sp : BitVec 64) (rck : ChainKey)
    (pk bs_sec : List (BitVec 8)) (rk1 : RootKey)
    (hpk : pk.length = 32) (hsec : bs_sec.length = 32) :
    (memRegion (sp + 0x1d8#64) 0x1f8 ∗
     ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
     memRegion (sp + 0x3f4#64) 12 ∗
     ((sp + 0x400#64) ↦ₛ pk) ∗
     ((sp + 0x420#64) ↦ₛ bs_sec) ∗
     memRegion (sp + 0x440#64) 0x60 ∗
     ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
     ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
     ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
     memRegion (sp + 0x4e0#64) 0xa0) ⊢
    memRegion (sp + 0x1d8#64) 0x3a8 := by
  have hrck_len : (chainKeyBytes rck).length = 36 := length_chainKeyBytes rck
  have e3d0 := pointsToBytes_entails_memRegion (sp + 0x3d0#64) (chainKeyBytes rck)
  rw [hrck_len] at e3d0
  have e400 := pointsToBytes_entails_memRegion (sp + 0x400#64) pk
  rw [hpk] at e400
  have e420 := pointsToBytes_entails_memRegion (sp + 0x420#64) bs_sec
  rw [hsec] at e420
  have e4a0 := pointsToBytes_entails_memRegion (sp + 0x4a0#64) (keyToBytes32 rk1)
  rw [length_keyToBytes32] at e4a0
  have e4c0 := pointsToBytes_entails_memRegion (sp + 0x4c0#64) ((chainKeyBytes rck).drop 20)
  have h4c0_len : ((chainKeyBytes rck).drop 20).length = 16 := by simp [hrck_len]
  rw [h4c0_len] at e4c0
  have e4d0 := pointsToBytes_entails_memRegion (sp + 0x4d0#64) ((chainKeyBytes rck).take 16)
  have h4d0_len : ((chainKeyBytes rck).take 16).length = 16 := by simp [hrck_len]
  rw [h4d0_len] at e4d0
  rw [memRegion_split' (b := sp + 0x1d8#64) (b' := sp + 0x3d0#64) (n := 0x1f8) (k :=
      0x1b0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3d0#64) (b' := sp + 0x3f4#64) (n := 36) (k :=
        0x18c) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3f4#64) (b' := sp + 0x400#64) (n := 12) (k :=
        0x180) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x400#64) (b' := sp + 0x420#64) (n := 32) (k :=
        0x160) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x420#64) (b' := sp + 0x440#64) (n := 32) (k :=
        0x140) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x440#64) (b' := sp + 0x4a0#64) (n := 0x60) (k :=
        0xe0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4a0#64) (b' := sp + 0x4c0#64) (n := 32) (k :=
        0xc0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4c0#64) (b' := sp + 0x4d0#64) (n := 16) (k :=
        0xb0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4d0#64) (b' := sp + 0x4e0#64) (n := 16) (k :=
        0xa0) rfl (by bv_arith) (by decide)]
  exact sepConj_mono_right (sepConj_mono e3d0 (sepConj_mono_right
    (sepConj_mono e400 (sepConj_mono e420 (sepConj_mono_right
      (sepConj_mono e4a0 (sepConj_mono e4c0 (sepConj_mono_left e4d0))))))))

theorem fold_sp_20_after_cc2_err (sp : BitVec 64) (rck : ChainKey) (msgW : BitVec 32) :
    (memRegion sp 0x10 ∗
     ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
     memRegion (sp + 0x14#64) 8 ∗
     ((sp + 0x1c#64) ↦₃₂ msgW)) ⊢
    memRegion sp 0x20 := by
  have hrck_len : (chainKeyBytes rck).length = 36 := length_chainKeyBytes rck
  have e10 := pointsToBytes_entails_memRegion (sp + 0x10#64) (((chainKeyBytes rck).drop 16).take 4)
  have h10_len : (((chainKeyBytes rck).drop 16).take 4).length = 4 := by simp [hrck_len]
  rw [h10_len] at e10
  rw [memRegion_split' (b := sp) (b' := sp + 0x10#64) (n := 0x10) (k :=
      0x10) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x10#64) (b' := sp + 0x14#64) (n := 4) (k :=
        12) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x14#64) (b' := sp + 0x1c#64) (n := 8) (k :=
        4) rfl (by bv_arith) (by decide)]
  exact sepConj_mono_right (sepConj_mono e10 (sepConj_mono_right (pointsTo32_entails_memRegion _
      _)))

theorem tryDecryptCommonHeap_split_tape (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (d : Nat) (s0 : State) :
    tryDecryptCommonHeap A ctl img x d s0 =
      (tapeAfter ctl x.cur x.rest d ∗
       (protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        logOff img ∗
        stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool)) := by
  unfold tryDecryptCommonHeap
  ac_rfl


end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB
