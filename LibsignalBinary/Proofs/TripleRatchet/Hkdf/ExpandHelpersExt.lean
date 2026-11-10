/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import ProofLib.SepLogic.HeapIntro

/-!
# Extended-Stack Frame and State Helpers for `expand_multi_info`

Defines `S2FrameRO`, the read-only `memcpy` step bridge `memcpyRO_subroutine_runsTo`, and
the `extHookStack` state invariants `ExpandFrameX`, `ExpandPreX`, and `ExpandCommonX`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExpandExt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalTripleRatchet.Expand
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Arm64.SepProp
  Heap.empty Heap.singleton Heap.singletonRO Heap.Disjoint Heap.union Heap.Matches Heap.complement
  SepProp.Satisfies SepProp.Entails SepProp.emp SepProp.pure SepProp.sepConj SepProp.sepImp
  SepProp.sepExists pointsTo8 pointsToBytes regionHeap regionHeapRO regionBlock memRegion

abbrev memcpyROLocalSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
      bs.length ≤ 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp hookStack

/-- Stacked read-only `memcpy` contract on `tripleRatchetProgAtExt img.base ext`. -/
abbrev MemcpyROContract (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
    ((memcpyROLocalSpec extHookStack).inImage img)

attribute [scoped simp, local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  sp_sub_496_eq_esp sp_add_neg496_eq_esp esp_add_496_sub_496
  read8_write64_120_127 CryptoVerification.LibsignalTripleRatchet.Expand.truncate8_ofNat64
  bv32_zero_add bv8_zero_add
  t1_length t2_length t3_length

theorem trExt_fnAddr_expandMultiInfo (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr expandMultiInfoName =
      b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info") := by
  unfold tripleRatchetProgAtExt expandMultiInfoName
  rw [Program.fnAddr_rebase,
    (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info")]

/-! ## `S2FrameRO` and Read-Only `memcpy` Bridge -/

/-- Permission-weakening-aware frame relation with a read-only source region `(roBase, roLen)`. -/
def S2FrameRO (roBase : BitVec 64) (roLen : ℕ) (m₁ m₂ : Memory)
    (regs : List (BitVec 64 × ℕ)) : Prop :=
  (∀ a, (m₁.perm a).r = true → m₁.isLazyFree a = false →
    (∀ r ∈ regs, OutsideRegion r.1 r.2 a) → m₂.read8 a = m₁.read8 a) ∧
  (((∀ a, OutsideRegion roBase roLen a → m₁.permNoLazy a = some Perm.rw → m₂.permNoLazy a = some Perm.rw) ∧
    (∀ a, OutsideRegion roBase roLen a → m₁.perm a = some Perm.rw → m₂.perm a = some Perm.rw)) ∧
   ((∀ a, (m₁.perm a).mapped = true ∧ m₁.isAnon a = true →
      (m₂.perm a).mapped = true ∧ m₂.isAnon a = true) ∧
    (∀ a, m₁.perm a = some Perm.protNone →
      (∀ r ∈ regs, OutsideRegion r.1 r.2 a) →
      m₂.perm a = some Perm.protNone ∧
      (m₁.isLazyFree a = false → m₂.read8 a = m₁.read8 a ∧ m₂.isLazyFree a = false)))) ∧
  (∀ a, (m₁.perm a).r = true → m₁.isLazyFree a = false →
    (m₂.perm a).r = true ∧ m₂.isLazyFree a = false)

namespace S2FrameRO

theorem refl (roBase : BitVec 64) (roLen : ℕ) (m : Memory) (regs : List (BitVec 64 × ℕ)) :
    S2FrameRO roBase roLen m m regs :=
  ⟨fun _ _ _ _ => rfl,
   ⟨⟨fun _ _ h => h, fun _ _ h => h⟩, ⟨fun _ h => h, fun _ h _ => ⟨h, fun hlf => ⟨rfl, hlf⟩⟩⟩⟩,
   fun _ hr hlf => ⟨hr, hlf⟩⟩

theorem of_s2frame {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)} (h : S2Frame m₁ m₂ regs) :
    S2FrameRO roBase roLen m₁ m₂ regs :=
  ⟨h.1, ⟨⟨fun a _ hnl => h.2.1.1.1 a hnl, fun a _ hrw => h.2.1.1.2 a hrw⟩, h.2.1.2⟩, h.2.2⟩

theorem of_frame {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)} (h : Frame m₁ m₂ regs) :
    S2FrameRO roBase roLen m₁ m₂ regs :=
  of_s2frame (S2Frame.of_frame h)

theorem trans {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ m₃ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (h12 : S2FrameRO roBase roLen m₁ m₂ regs)
    (h23 : S2FrameRO roBase roLen m₂ m₃ regs) :
    S2FrameRO roBase roLen m₁ m₃ regs :=
  ⟨fun a hr hlf hout =>
     let ⟨hr₂, hlf₂⟩ := h12.2.2 a hr hlf
     (h23.1 a hr₂ hlf₂ hout).trans (h12.1 a hr hlf hout),
   ⟨⟨fun a hro hnl => h23.2.1.1.1 a hro (h12.2.1.1.1 a hro hnl),
     fun a hro hrw => h23.2.1.1.2 a hro (h12.2.1.1.2 a hro hrw)⟩,
    ⟨fun a hm => h23.2.1.2.1 a (h12.2.1.2.1 a hm),
     fun a hpn hout =>
       let ⟨hp₁, hlf₁⟩ := h12.2.1.2.2 a hpn hout
       let ⟨hp₂, hlf₂⟩ := h23.2.1.2.2 a hp₁ hout
       ⟨hp₂, fun hlf =>
         let ⟨hr₁, hlf₁'⟩ := hlf₁ hlf
         let ⟨hr₂, hlf₂'⟩ := hlf₂ hlf₁'
         ⟨hr₂.trans hr₁, hlf₂'⟩⟩⟩⟩,
   fun a hr hlf =>
     let ⟨hr₂, hlf₂⟩ := h12.2.2 a hr hlf
     h23.2.2 a hr₂ hlf₂⟩

theorem mono {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs₁ regs₂ : List (BitVec 64 × ℕ)}
    (h : S2FrameRO roBase roLen m₁ m₂ regs₁)
    (hsub : ∀ a, (∀ r ∈ regs₂, OutsideRegion r.1 r.2 a) → ∀ r ∈ regs₁, OutsideRegion r.1 r.2 a) :
    S2FrameRO roBase roLen m₁ m₂ regs₂ :=
  ⟨fun a hr hlf hout => h.1 a hr hlf (hsub a hout),
   ⟨h.2.1.1,
    ⟨h.2.1.2.1, fun a hpn hout => h.2.1.2.2 a hpn (hsub a hout)⟩⟩,
   h.2.2⟩

theorem readable_of_readable {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (h : S2FrameRO roBase roLen m₁ m₂ regs) (a : BitVec 64) (n : ℕ)
    (hr : m₁.Readable a n) : m₂.Readable a n :=
  fun x hx => h.2.2 x (hr x hx).1 (hr x hx).2

theorem rw_of_rw {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (h : S2FrameRO roBase roLen m₁ m₂ regs) (a : BitVec 64) (n : ℕ)
    (hout : ∀ x, InRegion roBase roLen x → OutsideRegion a n x)
    (hrw : RW m₁ a n) : RW m₂ a n := by
  intro x hx
  have hro : OutsideRegion roBase roLen x := by
    rw [outsideRegion_iff_not_inRegion]
    intro hin
    exact (outsideRegion_iff_not_inRegion a n x).mp (hout x hin) hx
  exact h.2.1.1.1 x hro (hrw x hx)

theorem readBytes_eq_of_readable {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf : S2FrameRO roBase roLen m₁ m₂ regs) {addr : BitVec 64} {len : ℕ}
    (hread : m₁.Readable addr len)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 addr len) (hlen : len ≤ 2 ^ 64 := by decide) :
    m₂.readBytes addr len = m₁.readBytes addr len := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < len := by simpa using h1
  have hin : InRegion addr len (addr + BitVec.ofNat 64 i) :=
    inRegion_base_add addr len i hi hlen
  exact hf.1 _ (hread _ hin).1 (hread _ hin).2 (fun r hr => (hd r hr).outside hin hlen)

theorem read64_eq_of_readable {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf : S2FrameRO roBase roLen m₁ m₂ regs) {addr : BitVec 64}
    (hread : m₁.Readable addr 8)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 addr 8) :
    m₂.read64 addr = m₁.read64 addr := by
  have hbytes := hf.readBytes_eq_of_readable hread hd (by decide)
  rw [Bytes.readBytes_8_eq, Bytes.readBytes_8_eq] at hbytes
  simp only [List.cons.injEq, and_true] at hbytes
  rcases hbytes with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  dsimp only [Memory.read64]
  simp only [BitVec.add_zero, h0, h1, h2, h3, h4, h5, h6, h7]

theorem readBytes_eq {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf : S2FrameRO roBase roLen m₁ m₂ regs) {addr : BitVec 64} {len : ℕ}
    (hrw : RW m₁ addr len)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 addr len) (hlen : len ≤ 2 ^ 64 := by decide) :
    m₂.readBytes addr len = m₁.readBytes addr len :=
  hf.readBytes_eq_of_readable hrw.readable hd hlen

theorem read64_eq {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf : S2FrameRO roBase roLen m₁ m₂ regs) {addr : BitVec 64}
    (hrw : RW m₁ addr 8)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 addr 8) :
    m₂.read64 addr = m₁.read64 addr :=
  hf.read64_eq_of_readable hrw.readable hd

/-- Update two `IsBlock` regions across an `S2FrameRO` while preserving `P_ro ∗ R`
when `hro : IsBlockRO P_ro roBase roLen Φ_ro`. -/
theorem update_two_blocks {P1 P1' P2 P2' P_ro R : SepProp}
    {b1 b2 roBase : BitVec 64} {n1 n2 roLen : ℕ}
    {Φ1 Φ1' Φ2 Φ2' Φ_ro : Memory → Prop}
    {m m' : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb1' : IsBlock P1' b1 n1 Φ1')
    (hb2 : IsBlock P2 b2 n2 Φ2) (hb2' : IsBlock P2' b2 n2 Φ2')
    (hro : IsBlockRO P_ro roBase roLen Φ_ro)
    (h : m ⊨ P1 ∗ (P2 ∗ (P_ro ∗ R)))
    (hf : S2FrameRO roBase roLen m m' [(b1, n1), (b2, n2)])
    (hΦ1' : Φ1' m') (hΦ2' : Φ2' m') :
    m' ⊨ P1' ∗ (P2' ∗ (P_ro ∗ R)) := by
  have hrw1 : RW m b1 n1 := fun a ha => hb1.permNoLazy_rw h ha
  have h_swap : m ⊨ P2 ∗ (P1 ∗ (P_ro ∗ R)) := by rw [sepConj_left_comm]; exact h
  have hrw2 : RW m b2 n2 := fun a ha => hb2.permNoLazy_rw h_swap ha
  obtain ⟨h1, h2R, hd1, hp1, hp2R, hm⟩ := Satisfies.sepConj_elim h
  obtain ⟨h2, hR, hd2, rfl, hp2, hpR⟩ := SepProp.holds_sepConj_elim hp2R
  have hm2R : (h2.union hR).Matches m := Heap.Matches.of_union_right hd1 hm
  have hmR : hR.Matches m := Heap.Matches.of_union_right hd2 hm2R
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨h_ro, h_rest, hd_ro, hR_eq, hp_ro, hp_rest⟩ := SepProp.holds_sepConj_elim hpR
  obtain ⟨m_ro, hΦ_ro, rfl⟩ := (hro.iff h_ro).mp hp_ro
  have hout_ro_1 : ∀ a, InRegion roBase roLen a → OutsideRegion b1 n1 a := by
    intro a ha_ro
    rw [outsideRegion_iff_not_inRegion]
    intro ha1
    unfold Heap.Disjoint at hd1
    have hRa : hR a = some (.ro (m_ro.read8 a)) := by
      rw [hR_eq]; simp [Heap.union, regionHeapRO, ha_ro]
    rcases hd1.1 a with h1n | h2Rn | ⟨_, h1ro, _⟩
    · simp [regionHeap, ha1] at h1n
    · by_cases ha2 : InRegion b2 n2 a
      · simp [Heap.union, regionHeap, ha2] at h2Rn
      · simp [Heap.union, regionHeap, ha2, hRa] at h2Rn
    · simp [regionHeap, ha1] at h1ro
  have hout_ro_2 : ∀ a, InRegion roBase roLen a → OutsideRegion b2 n2 a := by
    intro a ha_ro
    rw [outsideRegion_iff_not_inRegion]
    intro ha2
    unfold Heap.Disjoint at hd2
    have hRa : hR a = some (.ro (m_ro.read8 a)) := by
      rw [hR_eq]; simp [Heap.union, regionHeapRO, ha_ro]
    rcases hd2.1 a with h2n | hRn | ⟨_, h2ro, _⟩
    · simp [regionHeap, ha2] at h2n
    · rw [hRa] at hRn; cases hRn
    · simp [regionHeap, ha2] at h2ro
  have hrw1' : RW m' b1 n1 := hf.rw_of_rw b1 n1 hout_ro_1 hrw1
  have hrw2' : RW m' b2 n2 := hf.rw_of_rw b2 n2 hout_ro_2 hrw2
  let h1' := regionHeap b1 n1 m'
  let h2' := regionHeap b2 n2 m'
  have hp1' : P1' h1' := (hb1'.iff h1').mpr ⟨m', hΦ1', rfl⟩
  have hp2' : P2' h2' := (hb2'.iff h2').mpr ⟨m', hΦ2', rfl⟩
  have hm1' : h1'.Matches m' := IsBlock.regionHeap_matches b1 n1 m' hrw1'
  have hm2' : h2'.Matches m' := IsBlock.regionHeap_matches b2 n2 m' hrw2'
  have hd2' : h2'.Disjoint hR := by
    apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl)
    intro a
    by_cases ha2 : InRegion b2 n2 a
    · rcases hd2.1 a with h2n | hRn | ⟨_, h2ro, _⟩
      · simp [regionHeap, ha2] at h2n
      · exact Or.inr (Or.inl hRn)
      · simp [regionHeap, ha2] at h2ro
    · exact Or.inl (by simp [h2', regionHeap, ha2])
  have hd1' : h1'.Disjoint (h2'.union hR) := by
    apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl)
    intro a
    by_cases ha1 : InRegion b1 n1 a
    · rcases hd1.1 a with h1n | h2Rn | ⟨_, h1ro, _⟩
      · simp [regionHeap, ha1] at h1n
      · refine Or.inr (Or.inl ?_)
        by_cases ha2 : InRegion b2 n2 a
        · simp [Heap.union, regionHeap, ha2] at h2Rn
        · simp [Heap.union, regionHeap, ha2] at h2Rn
          simp [Heap.union, h2', regionHeap, ha2, h2Rn]
      · simp [regionHeap, ha1] at h1ro
    · exact Or.inl (by simp [h1', regionHeap, ha1])
  have hmR' : hR.Matches m' := by
    refine ⟨fun a c hc => ?_, hmR.2.1, fun a hmap => hf.2.1.2.1 a (hmR.2.2 a hmap)⟩
    have hn2 : ¬ InRegion b2 n2 a := by
      intro ha2
      unfold Heap.Disjoint at hd2
      rcases hd2.1 a with h2n | hRn | ⟨_, h2ro, _⟩
      · simp [regionHeap, ha2] at h2n
      · rw [hc] at hRn; cases hRn
      · simp [regionHeap, ha2] at h2ro
    have hn1 : ¬ InRegion b1 n1 a := by
      intro ha1
      unfold Heap.Disjoint at hd1
      rcases hd1.1 a with h1n | h2Rn | ⟨_, h1ro, _⟩
      · simp [regionHeap, ha1] at h1n
      · simp [Heap.union, regionHeap, hn2, hc] at h2Rn
      · simp [regionHeap, ha1] at h1ro
    have ha_out : ∀ r ∈ [(b1, n1), (b2, n2)], OutsideRegion r.1 r.2 a := by
      intro r hr_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
      rcases hr_mem with rfl | rfl
      · exact (outsideRegion_iff_not_inRegion b1 n1 a).mpr hn1
      · exact (outsideRegion_iff_not_inRegion b2 n2 a).mpr hn2
    cases c with
    | rw v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.rw v) hc
      have hr_true : (m.perm a).r = true := by rw [hperm]; rfl
      have hout_ro : OutsideRegion roBase roLen a := by
        rw [outsideRegion_iff_not_inRegion]
        intro hin_ro
        have hRa : hR a = some (.ro (m_ro.read8 a)) := by
          rw [hR_eq]; simp [Heap.union, regionHeapRO, hin_ro]
        rw [hRa] at hc
        cases hc
      have hnl : m.permNoLazy a = some Perm.rw :=
        Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hperm, hlf⟩
      obtain ⟨hperm', hlf'⟩ :=
        Memory.permNoLazy_eq_some_rw_iff.mp (hf.2.1.1.1 a hout_ro hnl)
      exact ⟨(hf.1 a hr_true hlf ha_out).trans hr_eq, hperm', hlf'⟩
    | ro v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.ro v) hc
      obtain ⟨hperm', hlf'⟩ := hf.2.2 a hperm hlf
      exact ⟨(hf.1 a hperm hlf ha_out).trans hr_eq, hperm', hlf'⟩
    | protNone v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.protNone v) hc
      obtain ⟨hperm_m', hlf_fn⟩ := hf.2.1.2.2 a hperm ha_out
      obtain ⟨hr_m', hlf_m'⟩ := hlf_fn hlf
      exact ⟨hr_m'.trans hr_eq, hperm_m', hlf_m'⟩
    | lazy =>
      have hperm := hmR.1 a .lazy hc
      have hout_ro : OutsideRegion roBase roLen a := by
        rw [outsideRegion_iff_not_inRegion]
        intro hin_ro
        have hRa : hR a = some (.ro (m_ro.read8 a)) := by
          rw [hR_eq]; simp [Heap.union, regionHeapRO, hin_ro]
        rw [hRa] at hc
        cases hc
      exact hf.2.1.1.2 a hout_ro hperm
    | protNoneLazy =>
      have hperm := hmR.1 a .protNoneLazy hc
      exact (hf.2.1.2.2 a hperm ha_out).1
  exact Satisfies.sepConj_intro hd1' hp1' (SepProp.holds_sepConj_intro hd2' hp2' hpR)
    (Heap.Matches.union hm1' (Heap.Matches.union hm2' hmR'))

end S2FrameRO

private theorem regionHeap_none_of_outside (b : BitVec 64) (n : ℕ) (m : Memory) (a : BitVec 64)
    (ha : OutsideRegion b n a) :
    regionHeap b n m a = none := by
  have hni : ¬ InRegion b n a := (outsideRegion_iff_not_inRegion b n a).mp ha
  simp [regionHeap, hni]

private theorem regionHeapRO_none_of_outside (b : BitVec 64) (n : ℕ) (m : Memory) (a : BitVec 64)
    (ha : OutsideRegion b n a) :
    regionHeapRO b n m a = none := by
  have hni : ¬ InRegion b n a := (outsideRegion_iff_not_inRegion b n a).mp ha
  simp [regionHeapRO, hni]

private theorem matches_regionHeapRO_of_readable {b : BitVec 64} {n : ℕ} {m : Memory}
    (hr : m.Readable b n) : (regionHeapRO b n m).Matches m := by
  apply Heap.Matches.of_phys (ha := rfl) (hf := rfl) (hm := rfl)
  intro a cv hcv
  dsimp [regionHeapRO] at hcv
  split at hcv
  · rename_i ha
    cases hcv
    exact ⟨rfl, (hr a ha).1, (hr a ha).2⟩
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

/-- Build `m ⊨ P1 ∗ P2 ∗ P3` where `P1`, `P3` are `IsBlock` (RW) and `P2` is `IsBlockRO` (RO). -/
theorem satisfies_two_rw_one_ro {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1)
    (hb2 : IsBlockRO P2 b2 n2 Φ2)
    (hb3 : IsBlock P3 b3 n3 Φ3)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m) (hΦ3 : Φ3 m)
    (hrw1 : RW m b1 n1) (hread2 : m.Readable b2 n2) (hrw3 : RW m b3 n3)
    (hd13 : DisjointRegions b1 n1 b3 n3)
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
  have hd_13 : h1.Disjoint h3 := regionHeap_disjoint m hd13 hn3
  have hd_1_23 : h1.Disjoint (h2.union h3) :=
    (Heap.disjoint_union_right hd_23).mpr ⟨hd_12, hd_13⟩
  exact Satisfies.sepConj_intro hd_1_23 hp1 (SepProp.holds_sepConj_intro hd_23 hp2 hp3)
    (Heap.Matches.union hm1 (Heap.Matches.union hm2 hm3))

theorem isBlock_two_rw_one_ro_none_outside {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop}
    {h : Heap} {a : BitVec 64}
    (hb1 : IsBlock P1 b1 n1 Φ1)
    (hb2 : IsBlockRO P2 b2 n2 Φ2)
    (hb3 : IsBlock P3 b3 n3 Φ3)
    (hp : (P1 ∗ P2 ∗ P3) h)
    (ha1 : OutsideRegion b1 n1 a)
    (ha2 : OutsideRegion b2 n2 a)
    (ha3 : OutsideRegion b3 n3 a) :
    h a = none := by
  obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  have h1n : ¬ InRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mp ha1
  have h2n : ¬ InRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mp ha2
  have h3n : ¬ InRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mp ha3
  simp [Heap.union, regionHeap, regionHeapRO, h1n, h2n, h3n]

theorem isBlock_two_rw_one_ro_mapped_false {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop}
    {h : Heap}
    (hb1 : IsBlock P1 b1 n1 Φ1)
    (hb2 : IsBlockRO P2 b2 n2 Φ2)
    (hb3 : IsBlock P3 b3 n3 Φ3)
    (hp : (P1 ∗ P2 ∗ P3) h) (a : BitVec 64) :
    h.mapped a = false := by
  obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  simp [Heap.union, regionHeap, regionHeapRO]

theorem isBlock_two_rw_one_ro_s2frame_aux {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop}
    {h : Heap} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hb1 : IsBlock P1 b1 n1 Φ1)
    (hb2 : IsBlockRO P2 b2 n2 Φ2)
    (hb3 : IsBlock P3 b3 n3 Φ3)
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

theorem isBlock_two_rw_one_ro_s2frameRO {P1 P1' P2 P3 R1 R2 R3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ1' Φ2 Φ3 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb1' : IsBlock P1' b1 n1 Φ1')
    (hb2 : IsBlockRO P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    {hP : Heap} {m m' : Memory}
    (hpP : (P1 ∗ P2 ∗ P3) hP) (hmP : hP.Matches m)
    (hpost_1 : m' ⊨ P1' ∗ R1) (hpost_2 : m' ⊨ P2 ∗ R2) (hpost_3 : m' ⊨ P3 ∗ R3)
    (hn2 : n2 ≤ 2 ^ 64)
    (hsrc_eq : m'.readBytes b2 n2 = m.readBytes b2 n2)
    (hmc_full : (fullComplementHeap hP m).Matches m') :
    S2FrameRO b2 n2 m m' [(b1, n1), (b3, n3)] := by
  have hmc := hmc_full
  unfold Heap.Matches at hmc
  refine ⟨fun a hr_a hlf_a ha => ?_,
    ⟨⟨fun a ha2 hnl_a => ?_, fun a ha2 hrw_a => ?_⟩,
     isBlock_two_rw_one_ro_s2frame_aux hb1 hb2 hb3 hpP hmP hmc_full⟩,
    fun a hr_a hlf_a => ?_⟩
  · have ha1 : OutsideRegion b1 n1 a := ha (b1, n1) (by simp)
    have ha3 : OutsideRegion b3 n3 a := ha (b3, n3) (by simp)
    by_cases hin2 : InRegion b2 n2 a
    · obtain ⟨i, hi, rfl⟩ := (inRegion_iff_exists_offset b2 n2 a hn2).mp hin2
      exact read8_eq_of_readBytes_eq hsrc_eq hi
    · have ha2 : OutsideRegion b2 n2 a :=
        (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
      have hnone : hP a = none := isBlock_two_rw_one_ro_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
      by_cases hrw_a : m.perm a = some Perm.rw
      · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_a]
        exact (hmc.1 a _ hca).1
      · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
        exact (hmc.1 a _ hca).1
  · by_cases hin1 : InRegion b1 n1 a
    · exact hb1'.permNoLazy_rw hpost_1 hin1
    · by_cases hin3 : InRegion b3 n3 a
      · exact hb3.permNoLazy_rw hpost_3 hin3
      · have ha1 : OutsideRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mpr hin1
        have ha3 : OutsideRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mpr hin3
        have hnone : hP a = none := isBlock_two_rw_one_ro_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
        obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl_a
        have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_a]
        obtain ⟨-, hp', hlf'⟩ := hmc.1 a _ hca
        exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp', hlf'⟩
  · by_cases hin1 : InRegion b1 n1 a
    · exact hb1'.perm_rw hpost_1 hin1
    · by_cases hin3 : InRegion b3 n3 a
      · exact hb3.perm_rw hpost_3 hin3
      · have ha1 : OutsideRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mpr hin1
        have ha3 : OutsideRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mpr hin3
        have hnone : hP a = none := isBlock_two_rw_one_ro_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
        by_cases hlf_a : m.isLazyFree a = true
        · have hca : (fullComplementHeap hP m).phys a = some .lazy := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_a]
          exact hmc.1 a .lazy hca
        · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf_a
          have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_f]
          exact (hmc.1 a _ hca).2.1
  · by_cases hin1 : InRegion b1 n1 a
    · exact ⟨by rw [hb1'.perm_rw hpost_1 hin1]; rfl, hb1'.isLazyFree_false hpost_1 hin1⟩
    · by_cases hin2 : InRegion b2 n2 a
      · exact ⟨hb2.perm_r hpost_2 hin2, hb2.isLazyFree_false hpost_2 hin2⟩
      · by_cases hin3 : InRegion b3 n3 a
        · exact ⟨by rw [hb3.perm_rw hpost_3 hin3]; rfl, hb3.isLazyFree_false hpost_3 hin3⟩
        · have ha1 : OutsideRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mpr hin1
          have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
          have ha3 : OutsideRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mpr hin3
          have hnone : hP a = none := isBlock_two_rw_one_ro_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
          by_cases hrw_a : m.perm a = some Perm.rw
          · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
              simp [fullComplementHeap, hnone, hrw_a, hlf_a]
            obtain ⟨-, hp', hlf'⟩ := hmc.1 a _ hca
            exact ⟨by rw [hp']; rfl, hlf'⟩
          · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
              simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
            obtain ⟨-, hp', hlf'⟩ := hmc.1 a _ hca
            exact ⟨hp', hlf'⟩

/-- Turn `MemcpyROContract img ext` into a `RunsToE` transition on `tripleRatchetProgAtExt`
for a read-only source buffer `(src, bs.length)`. -/
theorem memcpyRO_subroutine_runsTo {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hRO : MemcpyROContract img ext)
    {s : State} {dst src : BitVec 64} {bs : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "memcpy"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hlen_le : bs.length ≤ 64)
    (hbs_mem : s.mem.readBytes src bs.length = bs)
    (hrw_dst : RW s.mem dst bs.length)
    (hread_src : s.mem.Readable src bs.length)
    (hrw_stk : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hd_dst_stk : DisjointRegions dst bs.length (s.sp - BitVec.ofNat 64 extHookStack) extHookStack)
    (hout_src_dst : ∀ a, InRegion src bs.length a → OutsideRegion dst bs.length a)
    (hout_src_stk : ∀ a, InRegion src bs.length a → OutsideRegion (s.sp - BitVec.ofNat 64 extHookStack) extHookStack a)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      s'.mem.readBytes dst bs.length = bs ∧
      s'.mem.readBytes src bs.length = bs ∧
      S2FrameRO src bs.length s.mem s'.mem
        [(dst, bs.length), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)]) := by
  intro hL
  let xg : BitVec 64 × BitVec 64 × List (BitVec 8) := (dst, src, bs)
  let P1 : SepProp := memRegion dst bs.length
  let P2 : SepProp := (src ↦ᵣ bs)
  let P3 : SepProp := stackAt s.sp extHookStack
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 : IsBlock P1 dst bs.length (fun _ => True) := IsBlock.memRegion dst bs.length
  have hb2 : IsBlockRO P2 src bs.length (fun m => m.readBytes src bs.length = bs) :=
    IsBlockRO.pointsToBytesRO src bs (by omega)
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
  have hpre_sat : s.mem ⊨ ((memcpyROLocalSpec extHookStack).inImage img).pre xg s ∗ R := by
    dsimp only [Spec.inImage, memcpyROLocalSpec, xg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfrz, hsym⟩, ⟨hx0, hx1, hx2, by omega⟩, ?_⟩
    dsimp only [P, P1, P2, P3] at hsatPR
    ac_nf at hsatPR ⊢
  have hsp_aligned : s.spAligned = true := by
    simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full (oom := fun _ => False) hRO xg R hpc hstat hpre_sat hsp_aligned
    (by intro _ _ hp
        dsimp only [Spec.inImage, memcpyROLocalSpec] at hp
        rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he
        dsimp only [Spec.inImage, memcpyROLocalSpec] at he
        rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho
        dsimp only [Spec.inImage, memcpyROLocalSpec] at ho
        rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, hoom⟩⟩
  swap; · exact False.elim hoom
  dsimp only [Spec.inImage, memcpyROLocalSpec, xg] at hpost_sat
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
  have hframe : S2FrameRO src bs.length s.mem s'.mem
      [(dst, bs.length), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    isBlock_two_rw_one_ro_s2frameRO hb1 hb1' hb2 hb3 hpP hmP
      hpost_1 hpost_2 hpost_3 (by omega) (hsrc_s'.trans hbs_mem.symm) hmc_full
  exact ⟨s', hsteps, ⟨htr, hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨hpc', hstat', hcc, hx0', hdst_s', hsrc_s', hframe⟩,
    hsteps.codeLoaded hL⟩

/-! ## Extended-Stack Frame and `HmacSt` Helpers -/

/-- Extended stack frame of `expand_multi_info` at `17024` B. -/
abbrev ExpandFrameX (infoPtr : BitVec 64) (infoLen okmLen : ℕ) (s₀ : State) (m : Memory) : Prop :=
  S2FrameRO infoPtr infoLen s₀.mem m [(s₀.readReg64 .x2, okmLen), (s₀.sp - 17024#64, 17024)]

/-- Bundled preconditions of `expandMultiInfoSpecExt` at entry state `s₀`. -/
structure ExpandPreX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (okmLen : ℕ) (s₀ : State) : Prop where
  frozen        : img.FrozenLoaded s₀
  symtab_eq     : s₀.symtab = img.symtab
  pc_eq         : s₀.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info")
  status        : s₀.status = .Running
  x3_eq         : s₀.readReg64 .x3 = BitVec.ofNat 64 okmLen
  prk_le        : prk.length ≤ 64
  info_lt       : info.length < 23
  okm_len       : okmLen = 64 ∨ okmLen = 80
  hmac_st       : HmacSt s₀.mem (s₀.readReg64 .x0) F prk []
  info_ptr      : s₀.mem.read64 (s₀.readReg64 .x1) = infoPtr
  info_len      : s₀.mem.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length
  info_bytes    : s₀.mem.readBytes infoPtr info.length = info
  read_info     : s₀.mem.Readable infoPtr info.length
  read_x0       : s₀.mem.Readable (s₀.readReg64 .x0) 0x90
  read_x1       : s₀.mem.Readable (s₀.readReg64 .x1) 16
  rw_x2         : RW s₀.mem (s₀.readReg64 .x2) okmLen
  rw_stack      : RW s₀.mem (s₀.sp - 17024#64) 17024
  disj_x2_stack : DisjointRegions (s₀.readReg64 .x2) okmLen (s₀.sp - 17024#64) 17024
  disj_x0_stack : DisjointRegions (s₀.readReg64 .x0) 0x90 (s₀.sp - 17024#64) 17024
  disj_x0_x2    : DisjointRegions (s₀.readReg64 .x0) 0x90 (s₀.readReg64 .x2) okmLen
  disj_x1_stack : DisjointRegions (s₀.readReg64 .x1) 16 (s₀.sp - 17024#64) 17024
  disj_x1_x2    : DisjointRegions (s₀.readReg64 .x1) 16 (s₀.readReg64 .x2) okmLen
  out_info_stk  : ∀ a, InRegion infoPtr info.length a → OutsideRegion (s₀.sp - 17024#64) 17024 a
  out_info_x2   : ∀ a, InRegion infoPtr info.length a → OutsideRegion (s₀.readReg64 .x2) okmLen a
  sp_aligned    : (s₀.sp &&& 15#64) = 0#64

theorem ExpandPreX.toExpandPre {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀) :
    ExpandPre img.base F prk info infoPtr okmLen s₀ :=
  have hsub640 : 0 < 640 ∧ ((s₀.sp - 640#64) - (s₀.sp - 17024#64)).toNat + 640 ≤ 17024 := by
    have heq : (s₀.sp - 640#64) - (s₀.sp - 17024#64) = 16384#64 := by bv_lin
    rw [heq]; decide
  { pc_eq         := hpre.pc_eq
    status        := hpre.status
    x3_eq         := hpre.x3_eq
    prk_le        := hpre.prk_le
    info_lt       := hpre.info_lt
    okm_len       := hpre.okm_len
    hmac_st       := hpre.hmac_st
    info_ptr      := hpre.info_ptr
    info_len      := hpre.info_len
    info_bytes    := hpre.info_bytes
    read_x0       := hpre.read_x0
    read_x1       := hpre.read_x1
    rw_x2         := hpre.rw_x2
    rw_stack      := hpre.rw_stack.sub hsub640.2
    disj_x2_stack := hpre.disj_x2_stack.sub_right _ hsub640
    disj_x0_stack := hpre.disj_x0_stack.sub_right _ hsub640
    disj_x0_x2    := hpre.disj_x0_x2
    disj_x1_stack := hpre.disj_x1_stack.sub_right _ hsub640
    disj_x1_x2    := hpre.disj_x1_x2
    out_info_stk  := fun a ha => by
      have hout := hpre.out_info_stk a ha
      simp only [OutsideRegion] at hout ⊢
      bv_omega
    out_info_x2   := hpre.out_info_x2
    sp_aligned    := hpre.sp_aligned }

/-- Common state invariant across cuts of `expand_multi_info` at `17024` B stack. -/
structure ExpandCommonX (infoPtr : BitVec 64) (infoLen okmLen : ℕ) (s₀ s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = esp s₀
  x29_eq : s.readReg64 .x29 = esp s₀ + 400#64
  x27_eq : s.readReg64 .x27 = esp s₀ + 64#64
  x20_eq : s.readReg64 .x20 = s₀.readReg64 .x0
  m8_eq  : s.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1
  m16_eq : s.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64
  saved  : ExpandSaved s₀ s.mem
  frame  : ExpandFrameX infoPtr infoLen okmLen s₀ s.mem

theorem ExpandFrameX.rw_stkX {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameX infoPtr info.length okmLen s₀ m) :
    m.RW (s₀.sp - 17024#64) 17024 :=
  hf.rw_of_rw _ _ hpre.out_info_stk hpre.rw_stack

theorem ExpandFrameX.rw_esp {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameX infoPtr info.length okmLen s₀ m) :
    m.RW (esp s₀) 496 := by
  have hrw := ExpandFrameX.rw_stkX hpre hf
  unfold esp
  exact hrw.sub (by bv_omega)

theorem ExpandFrameX.rw_x2 {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameX infoPtr info.length okmLen s₀ m) :
    m.RW (s₀.readReg64 .x2) okmLen :=
  hf.rw_of_rw _ _ hpre.out_info_x2 hpre.rw_x2

theorem ExpandFrameX.readable_info {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameX infoPtr info.length okmLen s₀ m) :
    m.Readable infoPtr info.length :=
  hf.readable_of_readable _ _ hpre.read_info

theorem ExpandFrameX.readable_x0 {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameX infoPtr info.length okmLen s₀ m) :
    m.Readable (s₀.readReg64 .x0) 0x90 :=
  hf.readable_of_readable _ _ hpre.read_x0

theorem ExpandFrameX.readable_x1 {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameX infoPtr info.length okmLen s₀ m) :
    m.Readable (s₀.readReg64 .x1) 16 :=
  hf.readable_of_readable _ _ hpre.read_x1

theorem readable_sub {m : Memory} {a : BitVec 64} {n : ℕ} (hr : m.Readable a n)
    {b : BitVec 64} {k : ℕ} (hsub : (b - a).toNat + k ≤ n) :
    m.Readable b k := by
  intro x hx
  apply hr x
  simp only [InRegion] at hx ⊢
  bv_omega

theorem ExpandFrameX.hmac_x0 {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameX infoPtr info.length okmLen s₀ m) :
    HmacSt m (s₀.readReg64 .x0) F prk [] := by
  have hd : ∀ r ∈ [(s₀.readReg64 .x2, okmLen), (s₀.sp - 17024#64, 17024)],
      DisjointRegions r.1 r.2 (s₀.readReg64 .x0) 0x90 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hpre.disj_x0_x2.symm
    · exact hpre.disj_x0_stack.symm
  rcases hpre.hmac_st with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
  refine ⟨hlen, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have hrx0 := hpre.read_x0 (s₀.readReg64 .x0 + 0x3f#64) (by unfold InRegion; bv_omega)
    refine (hf.1 _ hrx0.1 hrx0.2 (fun r hr => ?_)).trans hpos
    exact (hd r hr).outside (by unfold InRegion; bv_omega) (by decide)
  · refine (hf.readBytes_eq_of_readable (readable_sub hpre.read_x0 (by bv_omega))
      (fun r hr => ?_) (by decide)).trans hin
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x40#64) ⟨by decide, by bv_omega⟩
  · refine (hf.read64_eq_of_readable (readable_sub hpre.read_x0 (by bv_omega))
      (fun r hr => ?_)).trans hcnt1
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x60#64) ⟨by decide, by bv_omega⟩
  · refine (hf.readBytes_eq_of_readable (readable_sub hpre.read_x0 (by bv_omega))
      (fun r hr => ?_) (by decide)).trans hout
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x68#64) ⟨by decide, by bv_omega⟩
  · refine (hf.read64_eq_of_readable (readable_sub hpre.read_x0 (by bv_omega))
      (fun r hr => ?_)).trans hcnt2
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x88#64) ⟨by decide, by bv_omega⟩

theorem ExpandFrameX.info_ptr_eq {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameX infoPtr info.length okmLen s₀ m) :
    m.read64 (s₀.readReg64 .x1) = infoPtr := by
  rw [hf.read64_eq_of_readable (readable_sub hpre.read_x1 (by bv_omega))]
  · exact hpre.info_ptr
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hpre.disj_x1_x2.symm.sub_right _ ⟨by decide, by bv_omega⟩
    · exact hpre.disj_x1_stack.symm.sub_right _ ⟨by decide, by bv_omega⟩

theorem ExpandFrameX.info_len_eq {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameX infoPtr info.length okmLen s₀ m) :
    m.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length := by
  rw [hf.read64_eq_of_readable (readable_sub hpre.read_x1 (by bv_omega))]
  · exact hpre.info_len
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hpre.disj_x1_x2.symm.sub_right _ ⟨by decide, by bv_omega⟩
    · exact hpre.disj_x1_stack.symm.sub_right _ ⟨by decide, by bv_omega⟩

theorem ExpandFrameX.info_bytes_eq {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameX infoPtr info.length okmLen s₀ m) :
    m.readBytes infoPtr info.length = info := by
  refine (List.ext_getElem (by simp) fun i h1 h2 => ?_).trans hpre.info_bytes
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < info.length := by simpa using h1
  have hin : InRegion infoPtr info.length (infoPtr + BitVec.ofNat 64 i) :=
    inRegion_base_add infoPtr info.length i hi (by have := hpre.info_lt; omega)
  have hrinfo := hpre.read_info _ hin
  refine hf.1 _ hrinfo.1 hrinfo.2 (fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hpre.out_info_x2 _ hin
  · exact hpre.out_info_stk _ hin

theorem ExpandFrameX.of_agreesOutside_esp {infoPtr : BitVec 64} {infoLen okmLen : ℕ}
    {s₀ : State} {m m' : Memory} {off : BitVec 64} {sz : ℕ}
    (hf : ExpandFrameX infoPtr infoLen okmLen s₀ m)
    (hA : AgreesOutside m m' (esp s₀ + off) sz)
    (hoff : off.toNat + sz ≤ 496) :
    ExpandFrameX infoPtr infoLen okmLen s₀ m' := by
  refine hf.trans ((S2FrameRO.of_frame (frame_of_agreesOutside hA)).mono fun a ha => ?_)
  have hstack : OutsideRegion (s₀.sp - 17024#64) 17024 a :=
    ha (s₀.sp - 17024#64, 17024) (by simp)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  unfold esp at *
  simp only [OutsideRegion] at hstack ⊢
  bv_omega

theorem ExpandFrameX.of_agreesOutside_x2 {infoPtr : BitVec 64} {infoLen okmLen : ℕ}
    {s₀ : State} {m m' : Memory} {off : BitVec 64} {sz : ℕ}
    (hf : ExpandFrameX infoPtr infoLen okmLen s₀ m)
    (hA : AgreesOutside m m' (s₀.readReg64 .x2 + off) sz)
    (hoff : off.toNat + sz ≤ okmLen) :
    ExpandFrameX infoPtr infoLen okmLen s₀ m' := by
  refine hf.trans ((S2FrameRO.of_frame (frame_of_agreesOutside hA)).mono fun a ha => ?_)
  have hx2 : OutsideRegion (s₀.readReg64 .x2) okmLen a :=
    ha (s₀.readReg64 .x2, okmLen) (by simp)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [OutsideRegion] at hx2 ⊢
  bv_omega

theorem ExpandCommonX.of_agreesOutside_low32 {infoPtr : BitVec 64} {infoLen okmLen : ℕ}
    {s₀ s s' : State} {off : BitVec 64} {sz : ℕ}
    (hc : ExpandCommonX infoPtr infoLen okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hsp   : s'.sp = esp s₀)
    (hx29  : s'.readReg64 .x29 = esp s₀ + 400#64)
    (hx27  : s'.readReg64 .x27 = esp s₀ + 64#64)
    (hx20  : s'.readReg64 .x20 = s₀.readReg64 .x0)
    (hA    : AgreesOutside s.mem s'.mem (esp s₀ + off) sz)
    (hoff  : decide (32 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 400) = true) :
    ExpandCommonX infoPtr infoLen okmLen s₀ s' := by
  have ⟨h1, h2, h3⟩ : 32 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 400 := of_decide_eq_true hoff
  have hm8 : s'.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1 := by
    rw [hA.read64_eq (by unfold DisjointRegions; bv_omega)]
    exact hc.m8_eq
  have hm16 : s'.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := by
    rw [hA.read64_eq (by unfold DisjointRegions; bv_omega)]
    exact hc.m16_eq
  exact ⟨hstat, hsp, hx29, hx27, hx20, hm8, hm16,
    ExpandSaved.of_agreesOutside_low hc.saved hA ⟨h2, h3⟩,
    ExpandFrameX.of_agreesOutside_esp hc.frame hA (by omega)⟩

theorem fin_side_conditions_x {img : Obj.Image} {C : Crypto}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img C.F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameX infoPtr info.length okmLen s₀ s.mem) :
    RW s.mem (esp s₀ + 208#64) 32 ∧
    RW s.mem (esp s₀ + 240#64) 0x90 ∧
    RW s.mem (esp s₀ - 16528#64) 16528 ∧
    DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ + 240#64) 0x90 ∧
    DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ - 16528#64) 16528 ∧
    DisjointRegions (esp s₀ + 240#64) 0x90 (esp s₀ - 16528#64) 16528 := by
  have hrw_stack : s.mem.RW (s₀.sp - 17024#64) 17024 := ExpandFrameX.rw_stkX hpre hf
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hf
  refine ⟨hrw_esp.sub (by bv_omega), hrw_esp.sub (by bv_omega),
    hrw_stack.sub (by unfold esp; bv_omega),
    by unfold DisjointRegions; bv_omega,
    by unfold DisjointRegions esp at *; bv_omega,
    by unfold DisjointRegions esp at *; bv_omega⟩

theorem ExpandSaved_of_s2frame_disj {s₀ : State} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hs : ExpandSaved s₀ m) (hrw_esp : m.RW (esp s₀) 496)
    (hfr : S2Frame m m' regs)
    (hd_saved : ∀ r ∈ regs, DisjointRegions r.1 r.2 (esp s₀ + 400#64) 96) :
    ExpandSaved s₀ m' := by
  have h_saved_eq : ∀ (off : BitVec 64),
      decide (400 ≤ off.toNat ∧ off.toNat + 8 ≤ 496) = true →
      m'.read64 (esp s₀ + off) = m.read64 (esp s₀ + off) := by
    intro off hoff
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    refine hfr.read64_eq (hrw_esp.sub (by bv_omega)) ?_
    intro r hr
    exact (hd_saved r hr).sub_right (esp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact
    { m400 := (h_saved_eq 400#64 (by decide)).trans h0
      m408 := (h_saved_eq 408#64 (by decide)).trans h1
      m416 := (h_saved_eq 416#64 (by decide)).trans h2
      m424 := (h_saved_eq 424#64 (by decide)).trans h3
      m432 := (h_saved_eq 432#64 (by decide)).trans h4
      m440 := (h_saved_eq 440#64 (by decide)).trans h5
      m448 := (h_saved_eq 448#64 (by decide)).trans h6
      m456 := (h_saved_eq 456#64 (by decide)).trans h7
      m464 := (h_saved_eq 464#64 (by decide)).trans h8
      m472 := (h_saved_eq 472#64 (by decide)).trans h9
      m480 := (h_saved_eq 480#64 (by decide)).trans h10
      m488 := (h_saved_eq 488#64 (by decide)).trans h11 }

theorem ExpandSaved_of_s2frameRO_disj {roBase : BitVec 64} {roLen : ℕ}
    {s₀ : State} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hs : ExpandSaved s₀ m) (hrw_esp : m.RW (esp s₀) 496)
    (hfr : S2FrameRO roBase roLen m m' regs)
    (hd_saved : ∀ r ∈ regs, DisjointRegions r.1 r.2 (esp s₀ + 400#64) 96) :
    ExpandSaved s₀ m' := by
  have h_saved_eq : ∀ (off : BitVec 64),
      decide (400 ≤ off.toNat ∧ off.toNat + 8 ≤ 496) = true →
      m'.read64 (esp s₀ + off) = m.read64 (esp s₀ + off) := by
    intro off hoff
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    refine hfr.read64_eq (hrw_esp.sub (by bv_omega)) ?_
    intro r hr
    exact (hd_saved r hr).sub_right (esp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact
    { m400 := (h_saved_eq 400#64 (by decide)).trans h0
      m408 := (h_saved_eq 408#64 (by decide)).trans h1
      m416 := (h_saved_eq 416#64 (by decide)).trans h2
      m424 := (h_saved_eq 424#64 (by decide)).trans h3
      m432 := (h_saved_eq 432#64 (by decide)).trans h4
      m440 := (h_saved_eq 440#64 (by decide)).trans h5
      m448 := (h_saved_eq 448#64 (by decide)).trans h6
      m456 := (h_saved_eq 456#64 (by decide)).trans h7
      m464 := (h_saved_eq 464#64 (by decide)).trans h8
      m472 := (h_saved_eq 472#64 (by decide)).trans h9
      m480 := (h_saved_eq 480#64 (by decide)).trans h10
      m488 := (h_saved_eq 488#64 (by decide)).trans h11 }

theorem ExpandFrameX.of_fin_frame_x {infoPtr : BitVec 64} {infoLen okmLen : ℕ}
    {s₀ : State} {m m' : Memory}
    (hf : ExpandFrameX infoPtr infoLen okmLen s₀ m)
    (hfr : S2Frame m m' [(esp s₀ + 208#64, 32), (esp s₀ + 240#64, 0x90), (esp s₀ - 16528#64, 16528)]) :
    ExpandFrameX infoPtr infoLen okmLen s₀ m' := by
  refine hf.trans ((S2FrameRO.of_s2frame hfr).mono fun a ha => ?_)
  intro r hr
  have hstack := ha (s₀.sp - 17024#64, 17024) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> (unfold OutsideRegion esp at *; bv_omega)

theorem ExpandCommonX.of_fin_frame_x {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s s' : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hc : ExpandCommonX infoPtr info.length okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hcc : CallingConventionPreserved s s')
    (hfr : S2Frame s.mem s'.mem
      [(esp s₀ + 208#64, 32), (esp s₀ + 240#64, 0x90), (esp s₀ - 16528#64, 16528)]) :
    ExpandCommonX infoPtr info.length okmLen s₀ s' := by
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hc.frame
  have hd_low : ∀ r ∈ [(esp s₀ + 208#64, (32 : ℕ)), (esp s₀ + 240#64, 0x90), (esp s₀ - 16528#64, 16528)],
      DisjointRegions r.1 r.2 (esp s₀) 32 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions esp; bv_omega)
  have hd_saved : ∀ r ∈ [(esp s₀ + 208#64, (32 : ℕ)), (esp s₀ + 240#64, 0x90), (esp s₀ - 16528#64, 16528)],
      DisjointRegions r.1 r.2 (esp s₀ + 400#64) 96 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions esp; bv_omega)
  have hm8 : s'.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1 := by
    rw [hfr.read64_eq (hrw_esp.sub (by bv_omega))
      (fun r hr => (hd_low r hr).sub_right (esp s₀ + 8#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m8_eq
  have hm16 : s'.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := by
    rw [hfr.read64_eq (hrw_esp.sub (by bv_omega))
      (fun r hr => (hd_low r hr).sub_right (esp s₀ + 16#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m16_eq
  exact
    ⟨hstat,
     (Extract.CallingConventionPreserved.sp_eq hcc).trans hc.sp_eq,
     (Extract.CallingConventionPreserved.x29 hcc).trans hc.x29_eq,
     (Extract.CallingConventionPreserved.x27 hcc).trans hc.x27_eq,
     (Extract.CallingConventionPreserved.x20 hcc).trans hc.x20_eq,
     hm8, hm16,
     ExpandSaved_of_s2frame_disj hc.saved hrw_esp hfr hd_saved,
     ExpandFrameX.of_fin_frame_x hc.frame hfr⟩

theorem ExpandFrameX.of_memcpyRO_frame {infoPtr : BitVec 64} {infoLen okmLen : ℕ}
    {s₀ : State} {m m' : Memory} {off : BitVec 64}
    (hf : ExpandFrameX infoPtr infoLen okmLen s₀ m)
    (hoff : off.toNat + infoLen ≤ 496)
    (hfr : S2FrameRO infoPtr infoLen m m'
      [(esp s₀ + off, infoLen), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    ExpandFrameX infoPtr infoLen okmLen s₀ m' := by
  refine hf.trans (hfr.mono fun a ha => ?_)
  intro r hr
  have hstack := ha (s₀.sp - 17024#64, 17024) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · unfold OutsideRegion esp at *; bv_omega
  · change OutsideRegion (esp s₀ - 16384#64) 16384 a
    unfold OutsideRegion esp at *; bv_omega

theorem ExpandCommonX.of_memcpyRO_frame {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s s' : State} {off : BitVec 64}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hc : ExpandCommonX infoPtr info.length okmLen s₀ s)
    (hoff : 32 ≤ off.toNat ∧ off.toNat + info.length ≤ 300)
    (hstat : s'.status = .Running)
    (hcc : CallingConventionPreserved s s')
    (hfr : S2FrameRO infoPtr info.length s.mem s'.mem
      [(esp s₀ + off, info.length), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    ExpandCommonX infoPtr info.length okmLen s₀ s' := by
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hc.frame
  have hd_low : ∀ r ∈ [(esp s₀ + off, info.length), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (esp s₀) 32 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold DisjointRegions; bv_omega
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (esp s₀) 32
      unfold DisjointRegions; bv_omega
  have hd_saved : ∀ r ∈ [(esp s₀ + off, info.length), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (esp s₀ + 400#64) 96 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold DisjointRegions; bv_omega
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (esp s₀ + 400#64) 96
      unfold DisjointRegions; bv_omega
  have hm8 : s'.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1 := by
    rw [hfr.read64_eq (hrw_esp.sub (by bv_omega))
      (fun r hr => (hd_low r hr).sub_right (esp s₀ + 8#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m8_eq
  have hm16 : s'.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := by
    rw [hfr.read64_eq (hrw_esp.sub (by bv_omega))
      (fun r hr => (hd_low r hr).sub_right (esp s₀ + 16#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m16_eq
  exact
    ⟨hstat,
     (Extract.CallingConventionPreserved.sp_eq hcc).trans hc.sp_eq,
     (Extract.CallingConventionPreserved.x29 hcc).trans hc.x29_eq,
     (Extract.CallingConventionPreserved.x27 hcc).trans hc.x27_eq,
     (Extract.CallingConventionPreserved.x20 hcc).trans hc.x20_eq,
     hm8, hm16,
     ExpandSaved_of_s2frameRO_disj hc.saved hrw_esp hfr hd_saved,
     ExpandFrameX.of_memcpyRO_frame hc.frame (by omega) hfr⟩

theorem ExpandFrameX.of_memcpy_x2_frame {infoPtr : BitVec 64} {infoLen okmLen : ℕ}
    {s₀ : State} {m m' : Memory} {off : BitVec 64} {sz : ℕ}
    (hf : ExpandFrameX infoPtr infoLen okmLen s₀ m)
    (hoff : off.toNat + sz ≤ okmLen)
    (hfr : S2Frame m m'
      [(s₀.readReg64 .x2 + off, sz), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    ExpandFrameX infoPtr infoLen okmLen s₀ m' := by
  refine hf.trans ((S2FrameRO.of_s2frame hfr).mono fun a ha => ?_)
  intro r hr
  have hx2 := ha (s₀.readReg64 .x2, okmLen) (by simp)
  have hstack := ha (s₀.sp - 17024#64, 17024) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp only [OutsideRegion] at hx2 ⊢; bv_omega
  · change OutsideRegion (esp s₀ - 16384#64) 16384 a
    unfold OutsideRegion esp at *; bv_omega

theorem ExpandCommonX.of_memcpy_x2_frame {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s s' : State}
    {off : BitVec 64} {sz : ℕ}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hc : ExpandCommonX infoPtr info.length okmLen s₀ s)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ okmLen)
    (hstat : s'.status = .Running)
    (hcc : CallingConventionPreserved s s')
    (hfr : S2Frame s.mem s'.mem
      [(s₀.readReg64 .x2 + off, sz), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    ExpandCommonX infoPtr info.length okmLen s₀ s' := by
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hc.frame
  have hd_x2_esp : DisjointRegions (s₀.readReg64 .x2 + off) sz (esp s₀) 496 := by
    have hd1 := hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + off)
      ⟨hoff.1, by have := hoff.2; have := hpre.okm_len; bv_omega⟩
    unfold esp
    exact hd1.sub_right (s₀.sp - 496#64) ⟨by decide, by bv_omega⟩
  have hd_esp : ∀ r ∈ [(s₀.readReg64 .x2 + off, sz), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (esp s₀) 496 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd_x2_esp
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (esp s₀) 496
      unfold DisjointRegions; bv_omega
  have hd_saved : ∀ r ∈ [(s₀.readReg64 .x2 + off, sz), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (esp s₀ + 400#64) 96 :=
    fun r hr => (hd_esp r hr).sub_right (esp s₀ + 400#64) ⟨by decide, by bv_omega⟩
  have hm8 : s'.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1 := by
    rw [hfr.read64_eq (hrw_esp.sub (by bv_omega))
      (fun r hr => (hd_esp r hr).sub_right (esp s₀ + 8#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m8_eq
  have hm16 : s'.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := by
    rw [hfr.read64_eq (hrw_esp.sub (by bv_omega))
      (fun r hr => (hd_esp r hr).sub_right (esp s₀ + 16#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m16_eq
  exact
    ⟨hstat,
     (Extract.CallingConventionPreserved.sp_eq hcc).trans hc.sp_eq,
     (Extract.CallingConventionPreserved.x29 hcc).trans hc.x29_eq,
     (Extract.CallingConventionPreserved.x27 hcc).trans hc.x27_eq,
     (Extract.CallingConventionPreserved.x20 hcc).trans hc.x20_eq,
     hm8, hm16,
     ExpandSaved_of_s2frame_disj hc.saved hrw_esp hfr hd_saved,
     ExpandFrameX.of_memcpy_x2_frame hc.frame hoff.2 hfr⟩

end CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExpandExt
