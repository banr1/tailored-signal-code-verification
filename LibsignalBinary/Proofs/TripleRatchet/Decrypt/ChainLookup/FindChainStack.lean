/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.FindReceiverChainKey
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainSym
import ProofLib.RegChain

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

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
    (sepConj_mono (pointsTo64_entails_memRegion a w0) (pointsTo64_entails_memRegion (a + 8#64) w1)) ?_
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

theorem findChain_none_stack_recombine (sp : BitVec 64)
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

theorem findChain_some_stack_recombine_left (sp : BitVec 64)
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

theorem findChain_some_stack_recombine_right (sp : BitVec 64) (w3 w4 : BitVec 64) :
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

theorem findChain_err_stack_recombine_sp38 (sp locA remA : BitVec 64) (ctr : BitVec 32) :
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

theorem findChain_err_speBody_entails (A : RustAlloc) (sp p : BitVec 64) (u0 u1 : BitVec 64) (u2 : BitVec 32) :
    (((sp + 0x168#64) ↦₆₄ p) ∗
     ((sp + 0x170#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length) ∗
     (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗
     ((sp + 0x178#64) ↦₆₄ u0) ∗
     ((sp + 0x180#64) ↦₆₄ u1) ∗
     ((sp + 0x188#64) ↦₃₂ u2) ∗
     ((sp + 0x18c#64) ↦₃₂ 24#32)) ⊢
    speBodyAt A (utf8 "decrypt") (sp + 0x168#64) (.invalidSessionStructure .missingReceiverChainKey) := by
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

theorem findChain_err_stack_recombine_0x190 (sp : BitVec 64)
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
      show sp + 0x2b0#64 = (sp + 0x1b8#64) + BitVec.ofNat 64 0x1c8 - BitVec.ofNat 64 0xd0 by bv_omega]
  rw [show (sp + 0x1b8#64) + BitVec.ofNat 64 0x1c8 - BitVec.ofNat 64 0xd0 = (sp + 0x1b8#64) + BitVec.ofNat 64 0xf8 by bv_omega,
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

theorem findReceiverChainKeyResultAt_error_eq {r : BitVec 64} {e : SignalProtocolError} {R : SepProp} {m : Memory}
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

theorem reaches_pc_lsro_preserve {prog : Program} {t : BitVec 64} {s : State}
    {pl : Obj.MultiPlacement} {Q : State → Prop}
    (hro : LibsignalRoLoaded pl s.mem) (h : reaches_pc prog t s Q) :
    reaches_pc prog t s (fun sf => Q sf ∧ LibsignalRoLoaded pl sf.mem) := by
  intro hL
  obtain ⟨sf, hst, ⟨hpc, hrun, hQ⟩ | hpan⟩ := h hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, hQ, libsignalRoLoaded_of_keepsFrozen hro hst.keepsFrozen⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

theorem findChain_call_findReceiverChainKey_reaches_placed [LibsignalPlacement]
    {A : RustAlloc} {ctl : BitVec 64} {H : String → Option (State → State)}
    (hfrck : subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedSpec A)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hS2 : FindChainState_placed A ctl x trG tr st1 R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    reaches_pc prog ((blkPl_131).base + 680#64) s
      (fun s_ret =>
        tryDecryptMidMeta_placed s0 s_ret ∧
        s_ret.readReg64 .x19 = x.ret ∧
        s_ret.readReg64 .x20 = sp + 0x140#64 ∧
        s_ret.readReg64 .x21 = x.ss ∧
        s_ret.readReg64 .x22 = x.msgA ∧
        s_ret.readReg64 .x23 = sp + 0x500#64 ∧
        (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s_ret.readReg64 .x25 = sp + 0x190#64 ∧
        s_ret.readReg64 .x27 = sp + 0x38#64 ∧
        s_ret.readReg64 .x28 = sp + 0x2c0#64 ∧
        (s_ret.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 0x38#64) trG tr ∗
          memRegion x.ret 48 ∗ memRegion sp 0x20 ∗
          ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 0x140#64) 0x50 ∗
          findReceiverChainKeyResultAt (sp + 0x190#64) (tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey) ∗
          memRegion (sp + 0x1b8#64) 0x3c8 ∗
          tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hS2 with ⟨hpc, hmeta, hx0, hx1, hx8, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hmem⟩
  dsimp only [segFindChainPC_placed] at hpc
  have hwp_bl := findChain_bl_wp_placed (H := H) hpc (tryDecryptMidMeta_placed.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗ memRegion x.ret 48 ∗ memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x440 ∗
       tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    rw [emp_sepConj]; exact hmem
  have hcl_s : LibsignalCodeLoaded lsmpl s.mem := hmeta.2.2.2.2.2.2.1
  refine reaches_pc_seq_lscl hcl_s (reaches_pc_lsro_preserve hro (sepWP_to_reaches_pc hwp_bl hmem_emp)) ?_
  intro s_call hpc_call _ ⟨⟨P1, hm_call, ⟨hP1, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c, hcs_c⟩⟩, hro_call⟩ hcl_call
  subst hP1
  rw [emp_sepConj] at hm_call
  unfold tryDecryptCommonHeap at hm_call
  rw [trAt_eq_ratchetAt_trRestAt, signalMessageAt_eq_srk_rest, memRegion_0x140_split_findReceiverChainKey,
      logOff_tryDecryptDummyImg,
      stackAt_tryDecryptSubStack_sub s0.sp findReceiverChainKeyStack (by decide)] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  let fg : FindReceiverChainKeyGhost :=
    { self := sp + 0x38#64, G := trG.ratchet, st := tr.ratchet,
      theirA := x.msgA + 0x38#64, their := x.msg.senderRatchetKey, ret := sp + 0x190#64 }
  let F_call : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trRestAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1b8#64) 0x3c8 ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ signalMessageRestAt A x.msgG x.msgA x.msg ∗
    tapeAfter ctl x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64) (tryDecryptSubStack - findReceiverChainKeyStack) ∗
    tryDecryptSavedRegs s0.sp s0 ∗ A.pool ∗ R
  have hfrck_blk := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H) hfrck
  have hpre_call : s_call.mem ⊨ (findReceiverChainKeyPlacedSpec A).pre fg s_call ∗ F_call := by
    dsimp only [findReceiverChainKeyPlacedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hro_call, hx0_c.trans hx0, hx1_c.trans hx1, hx8_c.trans hx8⟩, ?_⟩
    rw [hsp_call]
    dsimp only [fg, F_call, sp] at hm_call ⊢
    convert hm_call using 1; sep_ac_rfl
  refine reaches_pc_call_lscl hfrck_blk fg F_call hpc_call hwpInv_call.1 hlr_call hcl_call hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hcl_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  dsimp only [findReceiverChainKeyPlacedSpec] at hpost_ret
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨htr_ret, hm_ret⟩
  have hsp_ret' : s_ret.sp = s0.sp - 1504#64 := by reg_chain
  have halign_ret : s_ret.spAligned = true := by
    rw [State.spAligned, hsp_ret', ← hwpInv_call.2.1]; exact halign_call
  have hmeta_ret : tryDecryptMidMeta_placed s0 s_ret :=
    ⟨hrun_ret, hsp_ret', hwpInv_call.2.2.1, halign_ret, by reg_chain, by reg_chain,
     hcl_ret, by reg_chain⟩
  refine ⟨hmeta_ret, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
  rw [hsp_call] at hm_ret
  unfold tryDecryptCommonHeap
  rw [trAt_eq_ratchetAt_trRestAt, signalMessageAt_eq_srk_rest, logOff_tryDecryptDummyImg,
      stackAt_tryDecryptSubStack_sub s0.sp findReceiverChainKeyStack (by decide)]
  dsimp only [fg, F_call, sp] at hm_ret ⊢
  convert hm_ret using 1; sep_ac_rfl

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
