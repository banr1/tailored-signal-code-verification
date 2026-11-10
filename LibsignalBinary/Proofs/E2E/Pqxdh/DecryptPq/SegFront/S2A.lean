/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S2Sym
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem exists_words16_of_memRegion_16 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 16 ∗ R) :
    ∃ w0 w1 : BitVec 64, m ⊨ ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗ R := by
  rw [memRegion_eq_exists_bytes a 16 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨w0, w1, hw⟩ := exists_words16_of_length_16 hlen
  exact ⟨w0, w1, by rwa [← hw a]⟩

theorem exists_words20_of_memRegion_20 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 20 ∗ R) :
    ∃ (w0 : BitVec 32) (w1 w2 : BitVec 64),
      m ⊨ ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₆₄ w1) ∗ ((a + 12#64) ↦₆₄ w2)) ∗ R := by
  rw [memRegion_eq_exists_bytes a 20 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨w0, w1, w2, hw⟩ := exists_words20_of_length_20 hlen
  exact ⟨w0, w1, w2, by rwa [← hw a]⟩

theorem exists_words36_of_memRegion_36 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 36 ∗ R) :
    ∃ (w0 : BitVec 32) (w1 w2 w3 w4 : BitVec 64),
      m ⊨ ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₆₄ w1) ∗ ((a + 12#64) ↦₆₄ w2) ∗
            ((a + 20#64) ↦₆₄ w3) ∗ ((a + 28#64) ↦₆₄ w4)) ∗ R := by
  rw [memRegion_split a 20 16 (by decide), sepConj_assoc] at hm
  obtain ⟨w0, w1, w2, hm⟩ := exists_words20_of_memRegion_20 hm
  have hm_re : m ⊨ memRegion (a + 20#64) 16 ∗
      (((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₆₄ w1) ∗ ((a + 12#64) ↦₆₄ w2)) ∗ R) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨w3, w4, hm2⟩ := exists_words16_of_memRegion_16 hm_re
  refine ⟨w0, w1, w2, w3, w4, ?_⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm2
  convert hm2 using 1; sep_ac_rfl

theorem words2_entails_memRegion_16 (a : BitVec 64) (w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ⊢ memRegion a 16 := by
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion a w0) (pointsTo64_entails_memRegion (a + 8#64) w1))
      ?_
  rw [← memRegion_split a 8 8 (by decide)]
  exact Entails.refl _

theorem words20_entails_memRegion_20 (a : BitVec 64) (w0 : BitVec 32) (w1 w2 : BitVec 64) :
    ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₆₄ w1) ∗ ((a + 12#64) ↦₆₄ w2)) ⊢ memRegion a 20 := by
  have h16 := words2_entails_memRegion_16 (a + 4#64) w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h16
  refine Entails.trans (sepConj_mono (pointsTo32_entails_memRegion a w0) h16) ?_
  rw [← memRegion_split a 4 16 (by decide)]
  exact Entails.refl _

theorem words36_entails_memRegion_36 (a : BitVec 64) (w0 : BitVec 32) (w1 w2 w3 w4 : BitVec 64) :
    ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₆₄ w1) ∗ ((a + 12#64) ↦₆₄ w2) ∗
     ((a + 20#64) ↦₆₄ w3) ∗ ((a + 28#64) ↦₆₄ w4)) ⊢ memRegion a 36 := by
  have h20 := words20_entails_memRegion_20 a w0 w1 w2
  have h16 := words2_entails_memRegion_16 (a + 20#64) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h16
  have hre :
      ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₆₄ w1) ∗ ((a + 12#64) ↦₆₄ w2) ∗
       ((a + 20#64) ↦₆₄ w3) ∗ ((a + 28#64) ↦₆₄ w4)) =
      (((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₆₄ w1) ∗ ((a + 12#64) ↦₆₄ w2)) ∗
       (((a + 20#64) ↦₆₄ w3) ∗ ((a + 28#64) ↦₆₄ w4))) := by ac_rfl
  rw [hre]
  refine Entails.trans (sepConj_mono h20 h16) ?_
  rw [← memRegion_split a 20 16 (by decide)]
  exact Entails.refl _

theorem s2_none_stack_recombine (sp : BitVec 64)
    (w0 : BitVec 32) (w1 w2 w3 w4 : BitVec 64) :
    (memRegion (sp + 0x140#64) 0x50 ∗
     ((sp + 0x190#64) ↦₃₂ 0#32) ∗
     (((sp + 0x194#64) ↦₃₂ w0) ∗
      ((sp + 0x198#64) ↦₆₄ w1) ∗
      ((sp + 0x1a0#64) ↦₆₄ w2) ∗
      ((sp + 0x1a8#64) ↦₆₄ w3) ∗
      ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
     memRegion (sp + 0x1b8#64) 0x1c8 ∗
     (((sp + 0x380#64) ↦₆₄ w3) ∗
      ((sp + 0x388#64) ↦₆₄ w4)) ∗
     memRegion (sp + 0x390#64) 0x1f0) ⊢
    memRegion (sp + 0x140#64) 0x440 := by
  have h36 := words36_entails_memRegion_36 (sp + 0x194#64) w0 w1 w2 w3 w4
  have h16 := words2_entails_memRegion_16 (sp + 0x380#64) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36 h16
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x190#64) 0#32)
      (sepConj_mono h36
      (sepConj_mono_right
        (sepConj_mono_left h16))))) ?_
  rw [show sp + 0x390#64 = (sp + 0x380#64) + 16#64 by bv_omega,
      ← memRegion_split (sp + 0x380#64) 16 0x1f0 (by decide),
      show sp + 0x380#64 = (sp + 0x1b8#64) + BitVec.ofNat 64 0x1c8 by bv_omega,
      ← memRegion_split (sp + 0x1b8#64) 0x1c8 0x200 (by decide),
      show sp + 0x1b8#64 = (sp + 0x194#64) + 36#64 by bv_omega,
      ← memRegion_split (sp + 0x194#64) 36 0x3c8 (by decide),
      show sp + 0x194#64 = (sp + 0x190#64) + 4#64 by bv_omega,
      ← memRegion_split (sp + 0x190#64) 4 0x3ec (by decide),
      show sp + 0x190#64 = (sp + 0x140#64) + BitVec.ofNat 64 0x50 by bv_omega,
      ← memRegion_split (sp + 0x140#64) 0x50 0x3f0 (by decide)]
  exact Entails.refl _

theorem s2_some_stack_recombine_left (sp : BitVec 64)
    (w0 : BitVec 32) (w1 w2 w3 w4 : BitVec 64) :
    (memRegion (sp + 0x140#64) 0x50 ∗
     ((sp + 0x190#64) ↦₃₂ 1#32) ∗
     (((sp + 0x194#64) ↦₃₂ w0) ∗
      ((sp + 0x198#64) ↦₆₄ w1) ∗
      ((sp + 0x1a0#64) ↦₆₄ w2) ∗
      ((sp + 0x1a8#64) ↦₆₄ w3) ∗
      ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
     memRegion (sp + 0x1b8#64) 0xf8) ⊢
    memRegion (sp + 0x140#64) 0x170 := by
  have h36 := words36_entails_memRegion_36 (sp + 0x194#64) w0 w1 w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x190#64) 1#32)
      (sepConj_mono_left h36))) ?_
  rw [show sp + 0x1b8#64 = (sp + 0x194#64) + 36#64 by bv_omega,
      ← memRegion_split (sp + 0x194#64) 36 0xf8 (by decide),
      show sp + 0x194#64 = (sp + 0x190#64) + 4#64 by bv_omega,
      ← memRegion_split (sp + 0x190#64) 4 0x11c (by decide),
      show sp + 0x190#64 = (sp + 0x140#64) + BitVec.ofNat 64 0x50 by bv_omega,
      ← memRegion_split (sp + 0x140#64) 0x50 0x120 (by decide)]
  exact Entails.refl _

theorem s2_some_stack_recombine_right (sp : BitVec 64) (w3 w4 : BitVec 64) :
    (memRegion (sp + 0x2d4#64) 0xac ∗
     (((sp + 0x380#64) ↦₆₄ w3) ∗
      ((sp + 0x388#64) ↦₆₄ w4)) ∗
     memRegion (sp + 0x390#64) 0x1f0) ⊢
    memRegion (sp + 0x2d4#64) 0x2ac := by
  have h16 := words2_entails_memRegion_16 (sp + 0x380#64) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h16
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h16)) ?_
  rw [show sp + 0x390#64 = (sp + 0x380#64) + 16#64 by bv_omega,
      ← memRegion_split (sp + 0x380#64) 16 0x1f0 (by decide),
      show sp + 0x380#64 = (sp + 0x2d4#64) + BitVec.ofNat 64 0xac by bv_omega,
      ← memRegion_split (sp + 0x2d4#64) 0xac 0x200 (by decide)]
  exact Entails.refl _

theorem s2_err_stack_recombine_sp38 (sp locA remA : BitVec 64) (ctr : BitVec 32) :
    (memRegion sp 0x20 ∗
     ((sp + 0x20#64) ↦₆₄ locA) ∗
     ((sp + 0x28#64) ↦₃₂ ctr) ∗
     memRegion (sp + 0x2c#64) 4 ∗
     ((sp + 0x30#64) ↦₆₄ remA)) ⊢
    memRegion sp 0x38 := by
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x20#64) locA)
      (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x28#64) ctr)
      (sepConj_mono_right (pointsTo64_entails_memRegion (sp + 0x30#64) remA))))) ?_
  rw [show sp + 0x30#64 = (sp + 0x2c#64) + 4#64 by bv_omega,
      ← memRegion_split (sp + 0x2c#64) 4 8 (by decide),
      show sp + 0x2c#64 = (sp + 0x28#64) + 4#64 by bv_omega,
      ← memRegion_split (sp + 0x28#64) 4 12 (by decide),
      show sp + 0x28#64 = (sp + 0x20#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x20#64) 8 16 (by decide),
      ← memRegion_split sp 0x20 24 (by decide)]
  exact Entails.refl _

theorem s2_err_speBody_entails (A : RustAlloc) (sp p : BitVec 64) (u0 u1 : BitVec 64) (u2 : BitVec
    32) :
    (((sp + 0x168#64) ↦₆₄ p) ∗
     ((sp + 0x170#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length) ∗
     (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗
     ((sp + 0x178#64) ↦₆₄ u0) ∗
     ((sp + 0x180#64) ↦₆₄ u1) ∗
     ((sp + 0x188#64) ↦₃₂ u2) ∗
     ((sp + 0x18c#64) ↦₃₂ 24#32)) ⊢
    speBodyAt A (utf8 "decrypt") (sp + 0x168#64) (.invalidSessionStructure
      .missingReceiverChainKey) := by
  unfold speBodyAt strRefAt
  have hstr :
      (((sp + 0x168#64) ↦₆₄ p) ∗
       ((sp + 0x168#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length) ∗
       (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey)) ⊢
      ∃∗ q : BitVec 64,
        ((sp + 0x168#64) ↦₆₄ q) ∗
        ((sp + 0x168#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length) ∗
        (q ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) :=
    Entails.sepExists_intro
      (P := fun q =>
        ((sp + 0x168#64) ↦₆₄ q) ∗
        ((sp + 0x168#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length) ∗
        (q ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey)) p
  have h24 :
      (((sp + 0x178#64) ↦₆₄ u0) ∗
       ((sp + 0x180#64) ↦₆₄ u1) ∗
       ((sp + 0x188#64) ↦₃₂ u2) ∗
       ((sp + 0x18c#64) ↦₃₂ 24#32)) ⊢
      memRegion (sp + 0x168#64 + 16#64) 24 := by
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x178#64) u0)
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x180#64) u1)
      (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x188#64) u2)
        (pointsTo32_entails_memRegion (sp + 0x18c#64) 24#32)))) ?_
    rw [show sp + 0x18c#64 = (sp + 0x188#64) + 4#64 by bv_omega,
        ← memRegion_split (sp + 0x188#64) 4 4 (by decide),
        show sp + 0x188#64 = (sp + 0x180#64) + 8#64 by bv_omega,
        ← memRegion_split (sp + 0x180#64) 8 8 (by decide),
        show sp + 0x180#64 = (sp + 0x178#64) + 8#64 by bv_omega,
        ← memRegion_split (sp + 0x178#64) 8 16 (by decide),
        show sp + 0x168#64 + 16#64 = sp + 0x178#64 by bv_omega]
    exact Entails.refl _
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hstr h24 ⊢
  have hre :
      (((sp + 0x168#64) ↦₆₄ p) ∗
       ((sp + 0x170#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length) ∗
       (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗
       ((sp + 0x178#64) ↦₆₄ u0) ∗
       ((sp + 0x180#64) ↦₆₄ u1) ∗
       ((sp + 0x188#64) ↦₃₂ u2) ∗
       ((sp + 0x18c#64) ↦₃₂ 24#32)) =
      ((((sp + 0x168#64) ↦₆₄ p) ∗
        ((sp + 0x170#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length) ∗
        (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey)) ∗
       (((sp + 0x178#64) ↦₆₄ u0) ∗
        ((sp + 0x180#64) ↦₆₄ u1) ∗
        ((sp + 0x188#64) ↦₃₂ u2) ∗
        ((sp + 0x18c#64) ↦₃₂ 24#32))) := by ac_rfl
  rw [hre]
  exact sepConj_mono hstr h24

theorem s2_err_stack_recombine_0x190 (sp : BitVec 64)
    (w0 w1 b0 b1 u0 u1 : BitVec 64) (d2d0 u2 : BitVec 32) :
    (((sp + 0x190#64) ↦₃₂ 2#32) ∗
     memRegion (sp + 0x194#64) 4 ∗
     (((sp + 0x198#64) ↦₆₄ w0) ∗ ((sp + 0x1a0#64) ↦₆₄ w1)) ∗
     memRegion (sp + 0x1a8#64) 16 ∗
     memRegion (sp + 0x1b8#64) 0xf8 ∗
     (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1)) ∗
     (((sp + 0x2c0#64) ↦₆₄ w0) ∗ ((sp + 0x2c8#64) ↦₆₄ w1)) ∗
     ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
     memRegion (sp + 0x2d4#64) 0x5c ∗
     (((sp + 0x330#64) ↦₆₄ w0) ∗ ((sp + 0x338#64) ↦₆₄ w1)) ∗
     (((sp + 0x340#64) ↦₆₄ u0) ∗ ((sp + 0x348#64) ↦₆₄ u1)) ∗
     ((sp + 0x350#64) ↦₃₂ u2) ∗
     memRegion (sp + 0x354#64) 0x22c) ⊢
    memRegion (sp + 0x190#64) 0x3f0 := by
  have h198 := words2_entails_memRegion_16 (sp + 0x198#64) w0 w1
  have h2b0 := words2_entails_memRegion_16 (sp + 0x2b0#64) b0 b1
  have h2c0 := words2_entails_memRegion_16 (sp + 0x2c0#64) w0 w1
  have h330 := words2_entails_memRegion_16 (sp + 0x330#64) w0 w1
  have h340 := words2_entails_memRegion_16 (sp + 0x340#64) u0 u1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h198 h2b0 h2c0 h330 h340
  refine Entails.trans
    (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x190#64) 2#32)
    (sepConj_mono_right
      (sepConj_mono h198
      (sepConj_mono_right
      (sepConj_mono_right
      (sepConj_mono h2b0
      (sepConj_mono h2c0
      (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x2d0#64) d2d0)
      (sepConj_mono_right
      (sepConj_mono h330
      (sepConj_mono h340
      (sepConj_mono_left (pointsTo32_entails_memRegion (sp + 0x350#64) u2))))))))))))) ?_
  rw [show sp + 0x354#64 = (sp + 0x350#64) + 4#64 by bv_omega,
      ← memRegion_split (sp + 0x350#64) 4 0x22c (by decide),
      show sp + 0x350#64 = (sp + 0x340#64) + 16#64 by bv_omega,
      ← memRegion_split (sp + 0x340#64) 16 0x230 (by decide),
      show sp + 0x340#64 = (sp + 0x330#64) + 16#64 by bv_omega,
      ← memRegion_split (sp + 0x330#64) 16 0x240 (by decide),
      show sp + 0x330#64 = (sp + 0x2d4#64) + BitVec.ofNat 64 0x5c by bv_omega,
      ← memRegion_split (sp + 0x2d4#64) 0x5c 0x250 (by decide),
      show sp + 0x2d4#64 = (sp + 0x2d0#64) + 4#64 by bv_omega,
      ← memRegion_split (sp + 0x2d0#64) 4 0x2ac (by decide),
      show sp + 0x2d0#64 = (sp + 0x2c0#64) + 16#64 by bv_omega,
      ← memRegion_split (sp + 0x2c0#64) 16 0x2b0 (by decide),
      show sp + 0x2c0#64 = (sp + 0x2b0#64) + 16#64 by bv_omega,
      ← memRegion_split (sp + 0x2b0#64) 16 0x2c0 (by decide),
      show sp + 0x2b0#64 =
        (sp + 0x1b8#64) + BitVec.ofNat 64 0x1c8 - BitVec.ofNat 64 0xd0 by bv_omega]
  rw [show (sp + 0x1b8#64) + BitVec.ofNat 64 0x1c8 - BitVec.ofNat 64 0xd0 =
      (sp + 0x1b8#64) + BitVec.ofNat 64 0xf8 by bv_omega,
      ← memRegion_split (sp + 0x1b8#64) 0xf8 0x2d0 (by decide),
      show sp + 0x1b8#64 = (sp + 0x1a8#64) + 16#64 by bv_omega,
      ← memRegion_split (sp + 0x1a8#64) 16 0x3c8 (by decide),
      show sp + 0x1a8#64 = (sp + 0x198#64) + 16#64 by bv_omega,
      ← memRegion_split (sp + 0x198#64) 16 0x3d8 (by decide),
      show sp + 0x198#64 = (sp + 0x194#64) + 4#64 by bv_omega,
      ← memRegion_split (sp + 0x194#64) 4 0x3e8 (by decide),
      show sp + 0x194#64 = (sp + 0x190#64) + 4#64 by bv_omega,
      ← memRegion_split (sp + 0x190#64) 4 0x3ec (by decide)]
  exact Entails.refl _

theorem findReceiverChainKeyResultAt_error_eq {r : BitVec 64} {e : SignalProtocolError} {R :
    SepProp} {m : Memory}
    (hm : m ⊨ findReceiverChainKeyResultAt r (.error e) ∗ R) :
    e = .invalidSessionStructure .missingReceiverChainKey ∧
    m ⊨ ((r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗
         strRefAt (r + 8#64) (invalidSessionStructureStr .missingReceiverChainKey) ∗ memRegion (r + 24#64) 16) ∗ R := by
  cases e with
  | invalidSessionStructure reason =>
    cases reason with
    | missingReceiverChainKey => exact ⟨rfl, hm⟩
    | _ =>
      change m ⊨ ⌜False⌝ ∗ R at hm
      rw [satisfies_pure_sepConj] at hm
      exact False.elim hm.1
  | _ =>
    change m ⊨ ⌜False⌝ ∗ R at hm
    rw [satisfies_pure_sepConj] at hm
    exact False.elim hm.1



end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
