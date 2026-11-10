/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
import ProofLib.SepLogic.HeapIntro

/-!
# Hook `RunsToE` Steppers for SPQR KDF

Subroutine `RunsToE` steppers for `compress256`, read-only / read-write `memcpy`, and `memset`
derived from `SpqrKdfHooksExt` at `extHookStack` (`16384` B).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout

namespace SpqrKdfExt

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Arm64.SepProp
  Heap.empty Heap.singleton Heap.singletonRO Heap.Disjoint Heap.union Heap.Matches Heap.complement
  SepProp.Satisfies SepProp.Entails SepProp.emp SepProp.pure SepProp.sepConj SepProp.sepImp
  SepProp.sepExists pointsTo8 pointsToBytes regionHeap regionHeapRO regionBlock memRegion

private theorem satisfies_two_blocks {P1 P2 : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ2 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m)
    (hrw1 : RW m b1 n1) (hrw2 : RW m b2 n2)
    (hd12 : DisjointRegions b1 n1 b2 n2)
    (hn2 : n2 ≤ 2 ^ 64) :
    m ⊨ P1 ∗ P2 := by
  let h1 := regionHeap b1 n1 m
  let h2 := regionHeap b2 n2 m
  have hp1 : P1 h1 := (hb1.iff h1).mpr ⟨m, hΦ1, rfl⟩
  have hp2 : P2 h2 := (hb2.iff h2).mpr ⟨m, hΦ2, rfl⟩
  have hm1 : h1.Matches m := IsBlock.regionHeap_matches b1 n1 m hrw1
  have hm2 : h2.Matches m := IsBlock.regionHeap_matches b2 n2 m hrw2
  have hdisj12 : h1.Disjoint h2 := regionHeap_disjoint m hd12 hn2
  exact Satisfies.sepConj_intro hdisj12 hp1 hp2 (Heap.Matches.union hm1 hm2)

private theorem isBlock_two_none_outside {P1 P2 : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ2 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2)
    {h : Heap} (hp : (P1 ∗ P2) h) {a : BitVec 64}
    (ha1 : OutsideRegion b1 n1 a) (ha2 : OutsideRegion b2 n2 a) :
    h a = none := by
  obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  have hn1 : ¬ InRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mp ha1
  have hn2 : ¬ InRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mp ha2
  simp [Heap.union, regionHeap, hn1, hn2]

private theorem isBlock_two_mapped_false {P1 P2 : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ2 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2)
    {h : Heap} (hp : (P1 ∗ P2) h) (a : BitVec 64) :
    h.mapped a = false := by
  obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  simp [Heap.union, regionHeap]

private theorem isBlock_two_s2frame_aux {P1 P2 : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ2 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2)
    {h : Heap} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hp : (P1 ∗ P2) h) (hm : h.Matches m)
    (hmc : ∀ a c, (fullComplementHeap h m).phys a = some c →
      match c with
      | .rw b => m'.read8 a = b ∧ m'.perm a = some Perm.rw ∧ m'.isLazyFree a = false
      | .ro b => m'.read8 a = b ∧ (m'.perm a).r = true ∧ m'.isLazyFree a = false
      | .protNone b => m'.read8 a = b ∧ m'.perm a = some Perm.protNone ∧ m'.isLazyFree a = false
      | .lazy => m'.perm a = some Perm.rw
      | .protNoneLazy => m'.perm a = some Perm.protNone)
    (hmc_map : ∀ a, (fullComplementHeap h m).mapped a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) :
    (∀ a, (m.perm a).mapped = true ∧ m.isAnon a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) ∧
    (∀ a, m.perm a = some Perm.protNone →
      (∀ r ∈ regs, OutsideRegion r.1 r.2 a) →
      m'.perm a = some Perm.protNone ∧
      (m.isLazyFree a = false → m'.read8 a = m.read8 a ∧ m'.isLazyFree a = false)) := by
  refine ⟨fun a ⟨hm_a, han_a⟩ => ?_, fun a hpn_a _ => ?_⟩
  · have hm0 : h.mapped a = false := isBlock_two_mapped_false hb1 hb2 hp a
    exact hmc_map a (by simp [fullComplementHeap, hm0, hm_a, han_a])
  · have hnone : h a = none := by
      unfold Heap.Matches at hm
      obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := SepProp.holds_sepConj_elim hp
      obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
      obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
      cases ha : (regionHeap b1 n1 m1 |>.union (regionHeap b2 n2 m2)) a with
      | none => rfl
      | some c =>
        have hperm := hm.1 a c ha
        cases c with
        | rw v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | ro v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | protNone v =>
          by_cases h1 : InRegion b1 n1 a <;>
            by_cases h2 : InRegion b2 n2 a <;>
            simp [Heap.union, regionHeap, h1, h2] at ha
        | lazy => rw [hpn_a] at hperm; cases hperm
        | protNoneLazy =>
          by_cases h1 : InRegion b1 n1 a <;>
            by_cases h2 : InRegion b2 n2 a <;>
            simp [Heap.union, regionHeap, h1, h2] at ha
    by_cases hlf : m.isLazyFree a = true
    · have hca : (fullComplementHeap h m).phys a = some .protNoneLazy := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf]; rfl
      exact ⟨hmc a .protNoneLazy hca, fun hlf_f => by rw [hlf] at hlf_f; cases hlf_f⟩
    · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf
      have hca : (fullComplementHeap h m).phys a = some (.protNone (m.read8 a)) := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf_f]; rfl
      obtain ⟨hr, hp', hlf'⟩ := hmc a (.protNone (m.read8 a)) hca
      exact ⟨hp', fun _ => ⟨hr, hlf'⟩⟩

private theorem isBlock_two_s2frame {P1 P1' P2 R1 R2 : SepProp}
    {dst b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ1' Φ2 : Memory → Prop}
    (hb1 : IsBlock P1 dst n1 Φ1) (hb1' : IsBlock P1' dst n1 Φ1')
    (hb2 : IsBlock P2 b2 n2 Φ2)
    {hP : Heap} {m m' : Memory}
    (hpP : (P1 ∗ P2) hP) (hmP : hP.Matches m)
    (hpost_1 : m' ⊨ P1' ∗ R1) (hpost_2 : m' ⊨ P2 ∗ R2)
    (hmc : ∀ a c, (fullComplementHeap hP m).phys a = some c →
      match c with
      | .rw b => m'.read8 a = b ∧ m'.perm a = some Perm.rw ∧ m'.isLazyFree a = false
      | .ro b => m'.read8 a = b ∧ (m'.perm a).r = true ∧ m'.isLazyFree a = false
      | .protNone b => m'.read8 a = b ∧ m'.perm a = some Perm.protNone ∧ m'.isLazyFree a = false
      | .lazy => m'.perm a = some Perm.rw
      | .protNoneLazy => m'.perm a = some Perm.protNone)
    (hmc_map : ∀ a, (fullComplementHeap hP m).mapped a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) :
    S2Frame m m' [(dst, n1), (b2, n2)] := by
  refine ⟨fun a hr_a hlf_a ha => ?_,
    ⟨⟨fun a hnl_a => ?_, fun a hrw_a => ?_⟩,
     isBlock_two_s2frame_aux hb1 hb2 hpP hmP hmc hmc_map⟩,
    fun a hr_a hlf_a => ?_⟩
  · have ha1 : OutsideRegion dst n1 a := ha (dst, n1) (by simp)
    have ha2 : OutsideRegion b2 n2 a := ha (b2, n2) (by simp)
    have hnone : hP a = none := isBlock_two_none_outside hb1 hb2 hpP ha1 ha2
    by_cases hrw_a : m.perm a = some Perm.rw
    · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hlf_a]
      exact (hmc a _ hca).1
    · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
      exact (hmc a _ hca).1
  · by_cases hin1 : InRegion dst n1 a
    · exact hb1'.permNoLazy_rw hpost_1 hin1
    · by_cases hin2 : InRegion b2 n2 a
      · exact hb2.permNoLazy_rw hpost_2 hin2
      · have ha1 : OutsideRegion dst n1 a := (outsideRegion_iff_not_inRegion dst n1 a).mpr hin1
        have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
        have hnone : hP a = none := isBlock_two_none_outside hb1 hb2 hpP ha1 ha2
        obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl_a
        have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_a]
        obtain ⟨-, hp', hlf'⟩ := hmc a _ hca
        exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp', hlf'⟩
  · by_cases hin1 : InRegion dst n1 a
    · exact hb1'.perm_rw hpost_1 hin1
    · by_cases hin2 : InRegion b2 n2 a
      · exact hb2.perm_rw hpost_2 hin2
      · have ha1 : OutsideRegion dst n1 a := (outsideRegion_iff_not_inRegion dst n1 a).mpr hin1
        have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
        have hnone : hP a = none := isBlock_two_none_outside hb1 hb2 hpP ha1 ha2
        by_cases hlf_a : m.isLazyFree a = true
        · have hca : (fullComplementHeap hP m).phys a = some .lazy := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_a]
          exact hmc a .lazy hca
        · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf_a
          have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_f]
          exact (hmc a _ hca).2.1
  · by_cases hin1 : InRegion dst n1 a
    · exact ⟨by rw [hb1'.perm_rw hpost_1 hin1]; rfl, hb1'.isLazyFree_false hpost_1 hin1⟩
    · by_cases hin2 : InRegion b2 n2 a
      · exact ⟨by rw [hb2.perm_rw hpost_2 hin2]; rfl, hb2.isLazyFree_false hpost_2 hin2⟩
      · have ha1 : OutsideRegion dst n1 a := (outsideRegion_iff_not_inRegion dst n1 a).mpr hin1
        have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
        have hnone : hP a = none := isBlock_two_none_outside hb1 hb2 hpP ha1 ha2
        by_cases hrw_a : m.perm a = some Perm.rw
        · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_a]
          obtain ⟨-, hp', hlf'⟩ := hmc a _ hca
          exact ⟨by rw [hp']; rfl, hlf'⟩
        · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
          obtain ⟨-, hp', hlf'⟩ := hmc a _ hca
          exact ⟨hp', hlf'⟩

private theorem regionHeap_disjoint_opt {b₁ b₂ : BitVec 64} {n₁ n₂ : ℕ} (m : Memory)
    (hd : n₁ = 0 ∨ n₂ = 0 ∨ DisjointRegions b₁ n₁ b₂ n₂) (hn₂ : n₂ ≤ 2 ^ 64) :
    (regionHeap b₁ n₁ m).Disjoint (regionHeap b₂ n₂ m) := by
  rcases hd with rfl | rfl | hd
  · apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl); intro a
    exact Or.inl (by simp [regionHeap, InRegion])
  · apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl); intro a
    exact Or.inr (Or.inl (by simp [regionHeap, InRegion]))
  · exact regionHeap_disjoint m hd hn₂

private theorem satisfies_three_blocks_opt {P1 P2 P3 : SepProp} {b1 b2 b3 : BitVec 64}
    {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m) (hΦ3 : Φ3 m)
    (hrw1 : RW m b1 n1) (hrw2 : RW m b2 n2) (hrw3 : RW m b3 n3)
    (hd12 : n1 = 0 ∨ n2 = 0 ∨ DisjointRegions b1 n1 b2 n2)
    (hd13 : n1 = 0 ∨ n3 = 0 ∨ DisjointRegions b1 n1 b3 n3)
    (hd23 : n2 = 0 ∨ n3 = 0 ∨ DisjointRegions b2 n2 b3 n3)
    (hn2 : n2 ≤ 2 ^ 64) (hn3 : n3 ≤ 2 ^ 64) :
    m ⊨ P1 ∗ P2 ∗ P3 := by
  let h1 := regionHeap b1 n1 m
  let h2 := regionHeap b2 n2 m
  let h3 := regionHeap b3 n3 m
  have hp1 : P1 h1 := (hb1.iff h1).mpr ⟨m, hΦ1, rfl⟩
  have hp2 : P2 h2 := (hb2.iff h2).mpr ⟨m, hΦ2, rfl⟩
  have hp3 : P3 h3 := (hb3.iff h3).mpr ⟨m, hΦ3, rfl⟩
  have hm1 : h1.Matches m := IsBlock.regionHeap_matches b1 n1 m hrw1
  have hm2 : h2.Matches m := IsBlock.regionHeap_matches b2 n2 m hrw2
  have hm3 : h3.Matches m := IsBlock.regionHeap_matches b3 n3 m hrw3
  have hdisj23 : h2.Disjoint h3 := regionHeap_disjoint_opt m hd23 hn3
  have hm23 : (h2.union h3).Matches m := Heap.Matches.union hm2 hm3
  have hdisj1_23 : h1.Disjoint (h2.union h3) :=
    (Heap.disjoint_union_right hdisj23).mpr
      ⟨regionHeap_disjoint_opt m hd12 hn2, regionHeap_disjoint_opt m hd13 hn3⟩
  exact Satisfies.sepConj_intro hdisj1_23 hp1 (SepProp.holds_sepConj_intro hdisj23 hp2 hp3)
    (Heap.Matches.union hm1 hm23)

private theorem regionHeap_none_of_outside (b : BitVec 64) (n : ℕ) (m : Memory) (a : BitVec 64)
    (ha : OutsideRegion b n a) : regionHeap b n m a = none := by
  have hni : ¬ InRegion b n a := (outsideRegion_iff_not_inRegion b n a).mp ha
  simp [regionHeap, hni]

private theorem regionHeapRO_none_of_outside (b : BitVec 64) (n : ℕ) (m : Memory) (a : BitVec 64)
    (ha : OutsideRegion b n a) : regionHeapRO b n m a = none := by
  have hni : ¬ InRegion b n a := (outsideRegion_iff_not_inRegion b n a).mp ha
  simp [regionHeapRO, hni]

private theorem matches_regionHeapRO_of_readable {b : BitVec 64} {n : ℕ} {m : Memory}
    (hr : m.Readable b n) : (regionHeapRO b n m).Matches m := by
  apply Heap.Matches.of_phys (ha := rfl) (hf := rfl) (hm := rfl)
  intro a cv hcv
  dsimp [regionHeapRO] at hcv
  split at hcv
  · rename_i ha; cases hcv; exact ⟨rfl, (hr a ha).1, (hr a ha).2⟩
  · contradiction

private theorem disjoint_regionHeap_regionHeapRO {b₁ b₂ : BitVec 64} {n₁ n₂ : ℕ} {m₁ m₂ : Memory}
    (hout : ∀ a, InRegion b₂ n₂ a → OutsideRegion b₁ n₁ a) :
    (regionHeap b₁ n₁ m₁).Disjoint (regionHeapRO b₂ n₂ m₂) := by
  apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl)
  intro a
  by_cases ha₂ : InRegion b₂ n₂ a
  · have hni : ¬ InRegion b₁ n₁ a := (outsideRegion_iff_not_inRegion b₁ n₁ a).mp (hout a ha₂)
    exact Or.inl (by simp [regionHeap, hni])
  · exact Or.inr (Or.inl (by simp [regionHeapRO, ha₂]))

private theorem disjoint_regionHeapRO_regionHeap {b₁ b₂ : BitVec 64} {n₁ n₂ : ℕ} {m₁ m₂ : Memory}
    (hout : ∀ a, InRegion b₁ n₁ a → OutsideRegion b₂ n₂ a) :
    (regionHeapRO b₁ n₁ m₁).Disjoint (regionHeap b₂ n₂ m₂) := by
  apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl)
  intro a
  by_cases ha₁ : InRegion b₁ n₁ a
  · have hni : ¬ InRegion b₂ n₂ a := (outsideRegion_iff_not_inRegion b₂ n₂ a).mp (hout a ha₁)
    exact Or.inr (Or.inl (by simp [regionHeap, hni]))
  · exact Or.inl (by simp [regionHeapRO, ha₁])

private theorem satisfies_two_rw_one_ro {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlockRO P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m) (hΦ3 : Φ3 m)
    (hrw1 : RW m b1 n1) (hread2 : m.Readable b2 n2) (hrw3 : RW m b3 n3)
    (hd13 : n1 = 0 ∨ DisjointRegions b1 n1 b3 n3)
    (hn3 : n3 ≤ 2 ^ 64)
    (hout21 : ∀ a, InRegion b2 n2 a → OutsideRegion b1 n1 a)
    (hout23 : ∀ a, InRegion b2 n2 a → OutsideRegion b3 n3 a) :
    m ⊨ P1 ∗ P2 ∗ P3 := by
  let h1 := regionHeap b1 n1 m
  let h2 := regionHeapRO b2 n2 m
  let h3 := regionHeap b3 n3 m
  have hp1 : P1 h1 := (hb1.iff h1).mpr ⟨m, hΦ1, rfl⟩
  have hp2 : P2 h2 := (hb2.iff h2).mpr ⟨m, hΦ2, rfl⟩
  have hp3 : P3 h3 := (hb3.iff h3).mpr ⟨m, hΦ3, rfl⟩
  have hm1 : h1.Matches m := IsBlock.regionHeap_matches b1 n1 m hrw1
  have hm2 : h2.Matches m := matches_regionHeapRO_of_readable hread2
  have hm3 : h3.Matches m := IsBlock.regionHeap_matches b3 n3 m hrw3
  have hd_23 : h2.Disjoint h3 := disjoint_regionHeapRO_regionHeap hout23
  have hd_12 : h1.Disjoint h2 := disjoint_regionHeap_regionHeapRO hout21
  have hd_13 : h1.Disjoint h3 := regionHeap_disjoint_opt m (hd13.imp id Or.inr) hn3
  have hd_1_23 : h1.Disjoint (h2.union h3) :=
    (Heap.disjoint_union_right hd_23).mpr ⟨hd_12, hd_13⟩
  exact Satisfies.sepConj_intro hd_1_23 hp1 (SepProp.holds_sepConj_intro hd_23 hp2 hp3)
    (Heap.Matches.union hm1 (Heap.Matches.union hm2 hm3))

private theorem isBlock_two_rw_one_ro_none_outside {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop}
    {h : Heap} {a : BitVec 64}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlockRO P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hp : (P1 ∗ P2 ∗ P3) h)
    (ha1 : OutsideRegion b1 n1 a) (ha2 : OutsideRegion b2 n2 a) (ha3 : OutsideRegion b3 n3 a) :
    h a = none := by
  obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  simp [Heap.union, regionHeap_none_of_outside b1 n1 m1 a ha1,
    regionHeapRO_none_of_outside b2 n2 m2 a ha2,
    regionHeap_none_of_outside b3 n3 m3 a ha3]

private theorem isBlock_two_rw_one_ro_mapped_false {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop} {h : Heap}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlockRO P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hp : (P1 ∗ P2 ∗ P3) h) (a : BitVec 64) :
    h.mapped a = false := by
  obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  simp [Heap.union, regionHeap, regionHeapRO]

private theorem isBlock_two_rw_one_ro_s2frame_aux {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop}
    {h : Heap} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlockRO P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hp : (P1 ∗ P2 ∗ P3) h) (hm : h.Matches m)
    (hmc : (fullComplementHeap h m).Matches m') :
    (∀ a, (m.perm a).mapped = true ∧ m.isAnon a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) ∧
    (∀ a, m.perm a = some Perm.protNone →
      (∀ r ∈ regs, OutsideRegion r.1 r.2 a) →
      m'.perm a = some Perm.protNone ∧
      (m.isLazyFree a = false → m'.read8 a = m.read8 a ∧ m'.isLazyFree a = false)) := by
  unfold Heap.Matches at hm hmc
  refine ⟨fun a ⟨hm_a, han_a⟩ => ?_, fun a hpn_a _ => ?_⟩
  · have hm0 : h.mapped a = false := isBlock_two_rw_one_ro_mapped_false hb1 hb2 hb3 hp a
    exact hmc.2.2 a (by simp [fullComplementHeap, hm0, hm_a, han_a])
  · have hnone : h a = none := by
      obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
      obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
      obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
      obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
      obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
      cases ha : (regionHeap b1 n1 m1 |>.union (regionHeapRO b2 n2 m2 |>.union (regionHeap b3 n3 m3))) a with
      | none => rfl
      | some c =>
        have hperm := hm.1 a c ha
        cases c with
        | rw v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | ro v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | protNone v =>
          by_cases h1 : InRegion b1 n1 a <;>
            by_cases h2 : InRegion b2 n2 a <;>
            by_cases h3 : InRegion b3 n3 a <;>
            simp [Heap.union, regionHeap, regionHeapRO, h1, h2, h3] at ha
        | lazy => rw [hpn_a] at hperm; cases hperm
        | protNoneLazy =>
          by_cases h1 : InRegion b1 n1 a <;>
            by_cases h2 : InRegion b2 n2 a <;>
            by_cases h3 : InRegion b3 n3 a <;>
            simp [Heap.union, regionHeap, regionHeapRO, h1, h2, h3] at ha
    by_cases hlf : m.isLazyFree a = true
    · have hca : (fullComplementHeap h m).phys a = some .protNoneLazy := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf]; rfl
      exact ⟨hmc.1 a .protNoneLazy hca, fun hlf_f => by rw [hlf] at hlf_f; cases hlf_f⟩
    · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf
      have hca : (fullComplementHeap h m).phys a = some (.protNone (m.read8 a)) := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf_f]; rfl
      obtain ⟨hr, hp', hlf'⟩ := hmc.1 a (.protNone (m.read8 a)) hca
      exact ⟨hp', fun _ => ⟨hr, hlf'⟩⟩

private theorem shaStateBytes_len (st : ShaState) : (shaStateBytes st).length = 32 := by
  rcases st with ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩
  all_goals (first | rfl | (simp at hl))

theorem compress256_subroutine_runsTo {prog : Program} {img : Obj.Image}
    {F : ShaCompress} {hookStack : Nat}
    (hComp : subroutine_ok prog (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((spqrCompress256ExternSpec F hookStack).inImage img))
    (hstk_le : hookStack ≤ 2 ^ 64 := by decide)
    {s : State} {stPtr blkPtr : BitVec 64} {st : ShaState} {bs : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "sha2::sha256::compress256"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : 64 * (s.readReg64 .x2).toNat = bs.length)
    (hbs_le : bs.length ≤ 2 ^ 64)
    (hst_mem : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hbs_mem : s.mem.readBytes blkPtr bs.length = bs)
    (hrw_st : RW s.mem stPtr 32)
    (hrw_blk : RW s.mem blkPtr bs.length)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 hookStack) hookStack)
    (hd_st_blk : DisjointRegions stPtr 32 blkPtr bs.length)
    (hd_st_stk : DisjointRegions stPtr 32 (s.sp - BitVec.ofNat 64 hookStack) hookStack)
    (hd_blk_stk : DisjointRegions blkPtr bs.length (s.sp - BitVec.ofNat 64 hookStack) hookStack)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE prog s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.readBytes stPtr 32 = shaStateBytes ((HMAC.chunks64 bs).foldl F st) ∧
      s'.mem.readBytes blkPtr bs.length = bs ∧
      S2Frame s.mem s'.mem [(stPtr, 32), (s.sp - BitVec.ofNat 64 hookStack, hookStack)]) := by
  intro hL
  let xg : BitVec 64 × BitVec 64 × ShaState × List (BitVec 8) := (stPtr, blkPtr, st, bs)
  let P1 : SepProp := stPtr ↦ₛ shaStateBytes st
  let P2 : SepProp := blkPtr ↦ₛ bs
  let P3 : SepProp := stackAt s.sp hookStack
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hst_len : (shaStateBytes st).length = 32 := shaStateBytes_len st
  have hb1 : IsBlock P1 stPtr 32
      (fun m => (shaStateBytes st).length ≤ 2 ^ 64 ∧
        m.readBytes stPtr (shaStateBytes st).length = shaStateBytes st) :=
    IsBlock.pointsToBytes_len hst_len
  have hb2 : IsBlock P2 blkPtr bs.length
      (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes blkPtr bs.length = bs) :=
    IsBlock.pointsToBytes blkPtr bs
  have hb3 : IsBlock P3 (s.sp - BitVec.ofNat 64 hookStack) hookStack (fun _ => True) :=
    IsBlock.memRegion (s.sp - BitVec.ofNat 64 hookStack) hookStack
  have hsatP : s.mem ⊨ P :=
    satisfies_three_blocks hb1 hb2 hb3
      ⟨by rw [hst_len]; decide, by rwa [hst_len]⟩ ⟨hbs_le, hbs_mem⟩ trivial
      hrw_st hrw_blk hrw_stk hd_st_blk hd_st_stk hd_blk_stk hbs_le hstk_le
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hpre_sat : s.mem ⊨ ((spqrCompress256ExternSpec F hookStack).inImage img).pre xg s ∗ R := by
    rw [Spec.inImage, spqrCompress256ExternSpec]
    dsimp only [xg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfrz, hsym⟩, ⟨hx0, hx1, hx2⟩, ?_⟩
    dsimp only [P, P1, P2, P3] at hsatPR
    ac_nf at hsatPR ⊢
  have hsp_aligned : s.spAligned = true := by simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full (oom := fun _ => False) hComp xg R hpc hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [Spec.inImage, spqrCompress256ExternSpec] at hp
        rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [Spec.inImage, spqrCompress256ExternSpec] at he
        rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [Spec.inImage, spqrCompress256ExternSpec] at ho
        rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, hoom⟩⟩
  swap; · exact False.elim hoom
  rw [Spec.inImage, spqrCompress256ExternSpec] at hpost_sat
  dsimp only [xg] at hpost_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨htr, hpost_sep⟩
  let st' := (HMAC.chunks64 bs).foldl F st
  let P1' : SepProp := stPtr ↦ₛ shaStateBytes st'
  have hst'_len : (shaStateBytes st').length = 32 := shaStateBytes_len st'
  have hb1' : IsBlock P1' stPtr 32
      (fun m => (shaStateBytes st').length ≤ 2 ^ 64 ∧
        m.readBytes stPtr (shaStateBytes st').length = shaStateBytes st') :=
    IsBlock.pointsToBytes_len hst'_len
  change s'.mem ⊨ (P2 ∗ P1' ∗ P3) ∗ R at hpost_sep
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by ac_nf at hpost_1 ⊢
  have hst_s' : s'.mem.readBytes stPtr 32 = shaStateBytes st' := by
    have h := (hb1'.read hpost_1).2; rwa [hst'_len] at h
  have hbs_s' : s'.mem.readBytes blkPtr bs.length = bs := (hb2.read hpost_2).2
  have hmc : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  unfold Heap.Matches at hmc
  have hframe : S2Frame s.mem s'.mem [(stPtr, 32), (s.sp - BitVec.ofNat 64 hookStack, hookStack)] :=
    isBlock_three_s2frame hb1 hb1' hb2 hb3 hpP hmP
      hpost_1 hpost_2 hpost_3 hbs_le (hbs_s'.trans hbs_mem.symm) hmc.1 hmc.2.2
  exact ⟨s', hsteps, ⟨htr, hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨hpc', hstat', hcc, hst_s', hbs_s', hframe⟩,
    hsteps.codeLoaded hL⟩

private theorem chunks64_single_of_len_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    HMAC.chunks64 bs = [bs] := by simp [HMAC.chunks64, h]

theorem compress256_one_subroutine_runsTo {prog : Program} {img : Obj.Image}
    {F : ShaCompress} {hookStack : Nat}
    (hComp : subroutine_ok prog (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((spqrCompress256ExternSpec F hookStack).inImage img))
    (hstk_le : hookStack ≤ 2 ^ 64 := by decide)
    {s : State} {stPtr blkPtr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "sha2::sha256::compress256"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hst_mem : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk_mem : s.mem.readBytes blkPtr 64 = blk)
    (hrw_st : RW s.mem stPtr 32)
    (hrw_blk : RW s.mem blkPtr 64)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 hookStack) hookStack)
    (hd_st_blk : DisjointRegions stPtr 32 blkPtr 64)
    (hd_st_stk : DisjointRegions stPtr 32 (s.sp - BitVec.ofNat 64 hookStack) hookStack)
    (hd_blk_stk : DisjointRegions blkPtr 64 (s.sp - BitVec.ofNat 64 hookStack) hookStack)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE prog s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.readBytes stPtr 32 = shaStateBytes (F st blk) ∧
      s'.mem.readBytes blkPtr 64 = blk ∧
      S2Frame s.mem s'.mem [(stPtr, 32), (s.sp - BitVec.ofNat 64 hookStack, hookStack)]) := by
  have hblk_len : blk.length = 64 := by rw [← hblk_mem, Memory.readBytes_length]
  have hx2_len : 64 * (s.readReg64 .x2).toNat = blk.length := by rw [hx2, hblk_len]; rfl
  have hrun := compress256_subroutine_runsTo hComp hstk_le hfrz hsym hpc hstat hx0 hx1 hx2_len
    (by rw [hblk_len]; decide) hst_mem (by rwa [hblk_len]) hrw_st (by rwa [hblk_len]) hrw_stk
    (by rwa [hblk_len]) hd_st_stk (by rwa [hblk_len]) hsp_al
  refine hrun.mono fun s' hs' => ?_
  rw [chunks64_single_of_len_64 hblk_len, List.foldl_cons, List.foldl_nil, hblk_len] at hs'
  exact hs'

theorem memcpy_opt_subroutine_runsTo {prog : Program} {img : Obj.Image}
    (hMemcpy : subroutine_ok prog (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    {s : State} {dst src : BitVec 64} {bs : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "memcpy"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hbs_mem : s.mem.readBytes src bs.length = bs)
    (hrw_dst : RW s.mem dst bs.length)
    (hrw_src : RW s.mem src bs.length)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hd_dst_src : bs.length = 0 ∨ DisjointRegions dst bs.length src bs.length)
    (hd_dst_stk : bs.length = 0 ∨
      DisjointRegions dst bs.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hd_src_stk : bs.length = 0 ∨
      DisjointRegions src bs.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE prog s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      s'.mem.readBytes dst bs.length = bs ∧
      s'.mem.readBytes src bs.length = bs ∧
      S2Frame s.mem s'.mem [(dst, bs.length), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)]) := by
  intro hL
  have hbs_le : bs.length ≤ 2 ^ 64 := by
    rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  let xg : BitVec 64 × BitVec 64 × List (BitVec 8) := (dst, src, bs)
  let P1 : SepProp := memRegion dst bs.length
  let P2 : SepProp := src ↦ₛ bs
  let P3 : SepProp := stackAt s.sp extHookStack
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 : IsBlock P1 dst bs.length (fun _ => True) := IsBlock.memRegion dst bs.length
  have hb2 : IsBlock P2 src bs.length
      (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes src bs.length = bs) :=
    IsBlock.pointsToBytes src bs
  have hb3 : IsBlock P3 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack (fun _ => True) :=
    IsBlock.memRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack
  have hsatP : s.mem ⊨ P :=
    satisfies_three_blocks_opt hb1 hb2 hb3 trivial ⟨hbs_le, hbs_mem⟩ trivial
      hrw_dst hrw_src hrw_stk
      (hd_dst_src.imp id Or.inr)
      (hd_dst_stk.imp id Or.inr)
      (hd_src_stk.imp id Or.inr)
      hbs_le (by decide)
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hpre_sat : s.mem ⊨ ((sessionMemcpySpec extHookStack).inImage img).pre xg s ∗ R := by
    dsimp only [Spec.inImage, sessionMemcpySpec, libcMemcpySpec, xg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfrz, hsym⟩, ⟨hx0, hx1, hx2⟩, ?_⟩
    dsimp only [P, P1, P2, P3] at hsatPR
    ac_nf at hsatPR ⊢
  have hsp_aligned : s.spAligned = true := by simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full (oom := fun _ => False) hMemcpy xg R hpc hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [Spec.inImage, sessionMemcpySpec] at hp
        rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [Spec.inImage, sessionMemcpySpec] at he
        rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [Spec.inImage, sessionMemcpySpec] at ho
        rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, hoom⟩⟩
  swap; · exact False.elim hoom
  dsimp only [Spec.inImage, sessionMemcpySpec, xg] at hpost_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨⟨hx0', htr⟩, hpost_sep⟩
  let P1' : SepProp := dst ↦ₛ bs
  have hb1' : IsBlock P1' dst bs.length
      (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes dst bs.length = bs) :=
    IsBlock.pointsToBytes dst bs
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by dsimp only [P1', P2, P3]; ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by ac_nf at hpost_1 ⊢
  have hdst_s' : s'.mem.readBytes dst bs.length = bs := (hb1'.read hpost_1).2
  have hsrc_s' : s'.mem.readBytes src bs.length = bs := (hb2.read hpost_2).2
  have hmc : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  unfold Heap.Matches at hmc
  have hframe : S2Frame s.mem s'.mem
      [(dst, bs.length), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    isBlock_three_s2frame hb1 hb1' hb2 hb3 hpP hmP
      hpost_1 hpost_2 hpost_3 hbs_le (hsrc_s'.trans hbs_mem.symm) hmc.1 hmc.2.2
  exact ⟨s', hsteps, ⟨htr, hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨hpc', hstat', hcc, hx0', hdst_s', hsrc_s', hframe⟩,
    hsteps.codeLoaded hL⟩

theorem memcpy_zero_subroutine_runsTo {prog : Program} {img : Obj.Image}
    (hMemcpy : subroutine_ok prog (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    {s : State} {dst src : BitVec 64}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "memcpy"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = 0)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE prog s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      S2Frame s.mem s'.mem [(dst, 0), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)]) := by
  have hrun := memcpy_opt_subroutine_runsTo hMemcpy (bs := []) hfrz hsym hpc hstat hx0 hx1 hx2
    rfl (by intro a ha; simp [InRegion] at ha) (by intro a ha; simp [InRegion] at ha) hrw_stk
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hsp_al
  exact hrun.mono fun s' ⟨hpc', hstat', hcc, hx0', _, _, hfr⟩ => ⟨hpc', hstat', hcc, hx0', hfr⟩

theorem memcpyRO_subroutine_runsTo {prog : Program} {img : Obj.Image}
    (hRO : subroutine_ok prog (img.base + bv% (ls_off% "memcpy"))
      ((spqrMemcpyROExtSpec extHookStack).inImage img))
    {s : State} {dst src : BitVec 64} {bs : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "memcpy"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hbs_mem : s.mem.readBytes src bs.length = bs)
    (hrw_dst : RW s.mem dst bs.length)
    (hread_src : s.mem.Readable src bs.length)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hd_dst_stk : bs.length = 0 ∨
      DisjointRegions dst bs.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hout_src_dst : ∀ a, InRegion src bs.length a → OutsideRegion dst bs.length a)
    (hout_src_stk : ∀ a, InRegion src bs.length a →
      OutsideRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE prog s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      s'.mem.readBytes dst bs.length = bs ∧
      s'.mem.readBytes src bs.length = bs ∧
      S2FrameRO [(src, bs.length)] s.mem s'.mem
        [(dst, bs.length), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)]) := by
  intro hL
  have hbs_le : bs.length ≤ 2 ^ 64 := by
    rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  let xg : BitVec 64 × BitVec 64 × List (BitVec 8) := (dst, src, bs)
  let P1 : SepProp := memRegion dst bs.length
  let P2 : SepProp := (src ↦ᵣ bs)
  let P3 : SepProp := stackAt s.sp extHookStack
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 : IsBlock P1 dst bs.length (fun _ => True) := IsBlock.memRegion dst bs.length
  have hb2 : IsBlockRO P2 src bs.length (fun m => m.readBytes src bs.length = bs) :=
    IsBlockRO.pointsToBytesRO src bs hbs_le
  have hb3 : IsBlock P3 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack (fun _ => True) :=
    IsBlock.memRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack
  have hsatP : s.mem ⊨ P :=
    satisfies_two_rw_one_ro hb1 hb2 hb3 trivial hbs_mem trivial
      hrw_dst hread_src hrw_stk hd_dst_stk (by decide) hout_src_dst hout_src_stk
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hpre_sat : s.mem ⊨ ((spqrMemcpyROExtSpec extHookStack).inImage img).pre xg s ∗ R := by
    dsimp only [Spec.inImage, spqrMemcpyROExtSpec, xg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfrz, hsym⟩, ⟨hx0, hx1, hx2, hbs_le⟩, ?_⟩
    dsimp only [P, P1, P2, P3] at hsatPR
    ac_nf at hsatPR ⊢
  have hsp_aligned : s.spAligned = true := by simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full (oom := fun _ => False) hRO xg R hpc hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [Spec.inImage, spqrMemcpyROExtSpec] at hp
        rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [Spec.inImage, spqrMemcpyROExtSpec] at he
        rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [Spec.inImage, spqrMemcpyROExtSpec] at ho
        rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, hoom⟩⟩
  swap; · exact False.elim hoom
  dsimp only [Spec.inImage, spqrMemcpyROExtSpec, xg] at hpost_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨⟨hx0', htr⟩, hpost_mem⟩
  let P1' : SepProp := (dst ↦ₛ bs)
  have hb1' : IsBlock P1' dst bs.length
      (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes dst bs.length = bs) :=
    IsBlock.pointsToBytes dst bs
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by dsimp only [P1', P2, P3]; ac_nf at hpost_mem ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by ac_nf at hpost_1 ⊢
  have hdst_s' : s'.mem.readBytes dst bs.length = bs := (hb1'.read hpost_1).2
  have hsrc_s' : s'.mem.readBytes src bs.length = bs := hb2.read hpost_2
  have hmc_full : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  have hmc := hmc_full
  unfold Heap.Matches at hmc
  have hframe : S2FrameRO [(src, bs.length)] s.mem s'.mem
      [(dst, bs.length), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    refine ⟨fun a hr_a hlf_a ha => ?_,
      ⟨⟨fun a ha2 hnl_a => ?_, fun a ha2 hrw_a => ?_⟩,
       isBlock_two_rw_one_ro_s2frame_aux hb1 hb2 hb3 hpP hmP hmc_full⟩,
      fun a hr_a hlf_a => ?_⟩
    · have ha1 : OutsideRegion dst bs.length a := ha (dst, bs.length) (by simp)
      have ha3 : OutsideRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a :=
        ha (s.sp - BitVec.ofNat 64 extHookStack, extHookStack) (by simp)
      by_cases hin2 : InRegion src bs.length a
      · obtain ⟨i, hi, rfl⟩ := (inRegion_iff_exists_offset src bs.length a hbs_le).mp hin2
        exact read8_eq_of_readBytes_eq (hsrc_s'.trans hbs_mem.symm) hi
      · have ha2 : OutsideRegion src bs.length a :=
          (outsideRegion_iff_not_inRegion src bs.length a).mpr hin2
        have hnone : hP a = none := isBlock_two_rw_one_ro_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
        by_cases hrw_a : s.mem.perm a = some Perm.rw
        · have hca : (fullComplementHeap hP s.mem).phys a = some (.rw (s.mem.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_a]
          exact (hmc.1 a _ hca).1
        · have hca : (fullComplementHeap hP s.mem).phys a = some (.ro (s.mem.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
          exact (hmc.1 a _ hca).1
    · by_cases hin1 : InRegion dst bs.length a
      · exact hb1'.permNoLazy_rw hpost_1 hin1
      · by_cases hin3 : InRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a
        · exact hb3.permNoLazy_rw hpost_3 hin3
        · have ha1 : OutsideRegion dst bs.length a :=
            (outsideRegion_iff_not_inRegion dst bs.length a).mpr hin1
          have ha2 : OutsideRegion src bs.length a := ha2 (src, bs.length) (by simp)
          have ha3 : OutsideRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a :=
            (outsideRegion_iff_not_inRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a).mpr hin3
          have hnone : hP a = none := isBlock_two_rw_one_ro_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
          obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl_a
          have hca : (fullComplementHeap hP s.mem).phys a = some (.rw (s.mem.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_a]
          obtain ⟨-, hp', hlf'⟩ := hmc.1 a _ hca
          exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp', hlf'⟩
    · by_cases hin1 : InRegion dst bs.length a
      · exact hb1'.perm_rw hpost_1 hin1
      · by_cases hin3 : InRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a
        · exact hb3.perm_rw hpost_3 hin3
        · have ha1 : OutsideRegion dst bs.length a :=
            (outsideRegion_iff_not_inRegion dst bs.length a).mpr hin1
          have ha2 : OutsideRegion src bs.length a := ha2 (src, bs.length) (by simp)
          have ha3 : OutsideRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a :=
            (outsideRegion_iff_not_inRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a).mpr hin3
          have hnone : hP a = none := isBlock_two_rw_one_ro_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
          by_cases hlf_a : s.mem.isLazyFree a = true
          · have hca : (fullComplementHeap hP s.mem).phys a = some .lazy := by
              simp [fullComplementHeap, hnone, hrw_a, hlf_a]
            exact hmc.1 a .lazy hca
          · have hlf_f : s.mem.isLazyFree a = false := Bool.eq_false_iff.mpr hlf_a
            have hca : (fullComplementHeap hP s.mem).phys a = some (.rw (s.mem.read8 a)) := by
              simp [fullComplementHeap, hnone, hrw_a, hlf_f]
            exact (hmc.1 a _ hca).2.1
    · by_cases hin1 : InRegion dst bs.length a
      · exact ⟨by rw [hb1'.perm_rw hpost_1 hin1]; rfl, hb1'.isLazyFree_false hpost_1 hin1⟩
      · by_cases hin2 : InRegion src bs.length a
        · exact ⟨hb2.perm_r hpost_2 hin2, hb2.isLazyFree_false hpost_2 hin2⟩
        · by_cases hin3 : InRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a
          · exact ⟨by rw [hb3.perm_rw hpost_3 hin3]; rfl, hb3.isLazyFree_false hpost_3 hin3⟩
          · have ha1 : OutsideRegion dst bs.length a :=
              (outsideRegion_iff_not_inRegion dst bs.length a).mpr hin1
            have ha2 : OutsideRegion src bs.length a :=
              (outsideRegion_iff_not_inRegion src bs.length a).mpr hin2
            have ha3 : OutsideRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a :=
              (outsideRegion_iff_not_inRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a).mpr hin3
            have hnone : hP a = none := isBlock_two_rw_one_ro_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
            by_cases hrw_a : s.mem.perm a = some Perm.rw
            · have hca : (fullComplementHeap hP s.mem).phys a = some (.rw (s.mem.read8 a)) := by
                simp [fullComplementHeap, hnone, hrw_a, hlf_a]
              obtain ⟨-, hp', hlf'⟩ := hmc.1 a _ hca
              exact ⟨by rw [hp']; rfl, hlf'⟩
            · have hca : (fullComplementHeap hP s.mem).phys a = some (.ro (s.mem.read8 a)) := by
                simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
              obtain ⟨-, hp', hlf'⟩ := hmc.1 a _ hca
              exact ⟨hp', hlf'⟩
  exact ⟨s', hsteps, ⟨htr, hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨hpc', hstat', hcc, hx0', hdst_s', hsrc_s', hframe⟩,
    hsteps.codeLoaded hL⟩

/-- Unified RO/RW `memcpy` `RunsToE` stepper: dispatches to `memcpy_opt_subroutine_runsTo` when
`ro = false` (`RW s.mem src bs.length`) and to `memcpyRO_subroutine_runsTo` when `ro = true`
(`s.mem.Readable src bs.length` and every `a` in `(src, bs.length)` lies inside some `r ∈ roRegs`). -/
theorem memcpy_any_subroutine_runsTo {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hHooks : SpqrKdfHooksExt img F ext)
    (ro : Bool) (roRegs : List (BitVec 64 × ℕ))
    {s : State} {dst src : BitVec 64} {bs : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "memcpy"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hbs_mem : s.mem.readBytes src bs.length = bs)
    (hrw_dst : RW s.mem dst bs.length)
    (hsrc_perm : if ro then s.mem.Readable src bs.length ∧
        (∀ a, InRegion src bs.length a → ∃ r ∈ roRegs, InRegion r.1 r.2 a)
      else RW s.mem src bs.length)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hd_dst_stk : bs.length = 0 ∨
      DisjointRegions dst bs.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hout_src_dst : ∀ a, InRegion src bs.length a → OutsideRegion dst bs.length a)
    (hout_src_stk : ∀ a, InRegion src bs.length a →
      OutsideRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      s'.mem.readBytes dst bs.length = bs ∧
      s'.mem.readBytes src bs.length = bs ∧
      S2FrameRO roRegs s.mem s'.mem
        [(dst, bs.length), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)]) := by
  cases ro
  · simp only [Bool.false_eq_true, ↓reduceIte] at hsrc_perm
    have hd_dst_src : bs.length = 0 ∨ DisjointRegions dst bs.length src bs.length := by
      by_cases h0 : bs.length = 0
      · exact Or.inl h0
      · exact Or.inr (disjointRegions_of_outside (by omega) (by omega) hout_src_dst).symm
    have hd_src_stk : bs.length = 0 ∨
        DisjointRegions src bs.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
      by_cases h0 : bs.length = 0
      · exact Or.inl h0
      · exact Or.inr (disjointRegions_of_outside (by omega) (by decide) hout_src_stk)
    have hrun := memcpy_opt_subroutine_runsTo hHooks.memcpy hfrz hsym hpc hstat hx0 hx1 hx2
      hbs_mem hrw_dst hsrc_perm hrw_stk hd_dst_src hd_dst_stk hd_src_stk hsp_al
    exact hrun.mono fun s' ⟨hpc', hstat', hcc, hx0', hdst', hsrc', hfr⟩ =>
      ⟨hpc', hstat', hcc, hx0', hdst', hsrc', S2FrameRO.of_s2frame hfr⟩
  · simp only [↓reduceIte] at hsrc_perm
    rcases hsrc_perm with ⟨hread_src, hsub_ro⟩
    have hrun := memcpyRO_subroutine_runsTo hHooks.memcpyRO hfrz hsym hpc hstat hx0 hx1 hx2
      hbs_mem hrw_dst hread_src hrw_stk hd_dst_stk hout_src_dst hout_src_stk hsp_al
    refine hrun.mono fun s' ⟨hpc', hstat', hcc, hx0', hdst', hsrc', hfr⟩ =>
      ⟨hpc', hstat', hcc, hx0', hdst', hsrc', hfr.mono_ro fun a hout ro hro_eq => ?_⟩
    simp only [List.mem_singleton] at hro_eq
    subst hro_eq
    rw [outsideRegion_iff_not_inRegion]
    intro hin
    obtain ⟨r, hr_mem, hin_r⟩ := hsub_ro a hin
    exact (outsideRegion_iff_not_inRegion r.1 r.2 a).mp (hout r hr_mem) hin_r

theorem memset_subroutine_runsTo {prog : Program} {img : Obj.Image}
    (hMemset : subroutine_ok prog (img.base + bv% (ls_off% "memset"))
      ((spqrMemsetExternSpec extHookStack).inImage img))
    {s : State} {dst : BitVec 64} {val : BitVec 8} {n : ℕ}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "memset"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hrw_dst : RW s.mem dst n)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hd_dst_stk : DisjointRegions dst n (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE prog s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      s'.mem.readBytes dst n = List.replicate n val ∧
      S2Frame s.mem s'.mem [(dst, n), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)]) := by
  intro hL
  let xg : BitVec 64 × BitVec 8 × Nat := (dst, val, n)
  let P1 : SepProp := memRegion dst n
  let P2 : SepProp := stackAt s.sp extHookStack
  let P : SepProp := P1 ∗ P2
  have hb1 : IsBlock P1 dst n (fun _ => True) := IsBlock.memRegion dst n
  have hb2 : IsBlock P2 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack (fun _ => True) :=
    IsBlock.memRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack
  have hsatP : s.mem ⊨ P :=
    satisfies_two_blocks hb1 hb2 trivial trivial hrw_dst hrw_stk hd_dst_stk (by decide)
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hpre_sat : s.mem ⊨ ((spqrMemsetExternSpec extHookStack).inImage img).pre xg s ∗ R := by
    dsimp only [Spec.inImage, spqrMemsetExternSpec, xg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfrz, hsym⟩, ⟨hx0, hx1, hx2⟩, ?_⟩
    dsimp only [P, P1, P2] at hsatPR
    ac_nf at hsatPR ⊢
  have hsp_aligned : s.spAligned = true := by simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full (oom := fun _ => False) hMemset xg R hpc hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [Spec.inImage, spqrMemsetExternSpec] at hp
        rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [Spec.inImage, spqrMemsetExternSpec] at he
        rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [Spec.inImage, spqrMemsetExternSpec] at ho
        rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, hoom⟩⟩
  swap; · exact False.elim hoom
  dsimp only [Spec.inImage, spqrMemsetExternSpec, xg] at hpost_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨⟨hx0', htr⟩, hpost_sep⟩
  let P1' : SepProp := dst ↦ₛ List.replicate n val
  have hrep_len : (List.replicate n val).length = n := List.length_replicate
  have hb1' : IsBlock P1' dst n
      (fun m => (List.replicate n val).length ≤ 2 ^ 64 ∧
        m.readBytes dst (List.replicate n val).length = List.replicate n val) :=
    IsBlock.pointsToBytes_len hrep_len
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ R) := by dsimp only [P1', P2]; ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ R) := by ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ P2) := by ac_nf at hpost_1 ⊢
  have hdst_s' : s'.mem.readBytes dst n = List.replicate n val := by
    have h := (hb1'.read hpost_1).2; rwa [hrep_len] at h
  have hmc : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  unfold Heap.Matches at hmc
  have hframe : S2Frame s.mem s'.mem
      [(dst, n), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    isBlock_two_s2frame hb1 hb1' hb2 hpP hmP hpost_1 hpost_2 hmc.1 hmc.2.2
  exact ⟨s', hsteps, ⟨htr, hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨hpc', hstat', hcc, hx0', hdst_s', hframe⟩,
    hsteps.codeLoaded hL⟩

end SpqrKdfExt

end CryptoVerification.SpqrV1.Kdf
