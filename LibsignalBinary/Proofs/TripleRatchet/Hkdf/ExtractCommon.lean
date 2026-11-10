/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Common
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import ProofLib.Hoare.SubroutineHook
import ProofLib.SepLogic.HeapIntro

/-!
# Shared Definitions and Cut Predicates for `extract`

Defines `RunsToE`, `S2Frame`, 32-byte `new_from_slice` bridges, and cut-point invariants
`ENfs1`–`EPost` for `GenericHkdf<Hmac<Sha256>>::extract`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)

namespace Extract

attribute [scoped simp, arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  extractLsb'_56_8_read64

@[scoped simp, arm64_norm]
theorem read8_write64_56_63 (m : Memory) (sp0 v : BitVec 64) :
    (m.write64 (sp0 + 56#64) v).read8 (sp0 + 63#64) = v.extractLsb' 56 8 := by
  dsimp only [Memory.write64]
  simp [arm64_norm]

@[scoped simp, arm64_norm]
theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[scoped simp, arm64_norm]
theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

/-! ## `RunsToE` Sequencing -/

/-- Like `RunsTo`, but without `VCalleeSaved` (since `SubroutineOk` / `CallingConventionPreserved`
only preserves `sp` and `x19..x29`). -/
def RunsToE (prog : Program) (s₀ : State) (P : State → Prop) : Prop :=
  prog.CodeLoaded s₀.mem →
    ∃ sf, Steps prog s₀ sf ∧ TraceEq s₀ sf ∧ P sf ∧ prog.CodeLoaded sf.mem

theorem RunsTo.toE {prog : Program} {s₀ : State} {P : State → Prop}
    (h : RunsTo prog s₀ P) : RunsToE prog s₀ P := h

theorem RunsToE.mono {prog : Program} {s : State} {P Q : State → Prop}
    (h : RunsToE prog s P) (hPQ : ∀ s', P s' → Q s') : RunsToE prog s Q := by
  intro hL
  obtain ⟨sf, hst, htr, hP, hLf⟩ := h hL
  exact ⟨sf, hst, htr, hPQ sf hP, hLf⟩

theorem RunsToE.trans {prog : Program} {s : State} {P Q : State → Prop}
    (h1 : RunsToE prog s P) (h2 : ∀ s₁, P s₁ → RunsToE prog s₁ Q) : RunsToE prog s Q := by
  intro hL
  obtain ⟨s₁, hst1, htr1, hP, hL1⟩ := h1 hL
  obtain ⟨s₂, hst2, htr2, hQ, hL2⟩ := h2 s₁ hP hL1
  exact ⟨s₂, hst1.trans hst2, htr2.trans htr1, hQ, hL2⟩

theorem RunsToE.trans_full {prog : Program} {s : State} {P Q : State → Prop}
    (h1 : RunsToE prog s P)
    (h2 : ∀ s₁, P s₁ → s.mem.KeepsFrozen s₁.mem → s₁.symtab = s.symtab → RunsToE prog s₁ Q) :
    RunsToE prog s Q := by
  intro hL
  obtain ⟨s₁, hst1, htr1, hP, hL1⟩ := h1 hL
  obtain ⟨s₂, hst2, htr2, hQ, hL2⟩ := h2 s₁ hP hst1.keepsFrozen hst1.symtab_eq hL1
  exact ⟨s₂, hst1.trans hst2, htr2.trans htr1, hQ, hL2⟩

theorem RunsToE.to_reaches_pc {prog : Program} {target : BitVec 64} {s₀ : State}
    {P : State → Prop} {Q : State → Prop} {oom : State → Prop}
    (h : RunsToE prog s₀ P)
    (hPQ : ∀ sf, P sf → s₀.mem.KeepsFrozen sf.mem → sf.symtab = s₀.symtab → TraceEq s₀ sf →
      sf.pc = target ∧ sf.status = .Running ∧ Q sf) :
    reaches_pc prog target s₀ Q oom := by
  intro hL
  obtain ⟨sf, hsteps, htr, hP, _⟩ := h hL
  exact ⟨sf, hsteps, Or.inl (hPQ sf hP hsteps.keepsFrozen hsteps.symtab_eq htr)⟩

theorem CallingConventionPreserved.sp_eq {s s' : State} (h : CallingConventionPreserved s s') :
    s'.sp = s.sp := h.1
theorem CallingConventionPreserved.x19 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x19 = s.readReg64 .x19 := h.2.1
theorem CallingConventionPreserved.x20 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x20 = s.readReg64 .x20 := h.2.2.1
theorem CallingConventionPreserved.x21 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x21 = s.readReg64 .x21 := h.2.2.2.1
theorem CallingConventionPreserved.x22 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x22 = s.readReg64 .x22 := h.2.2.2.2.1
theorem CallingConventionPreserved.x27 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x27 = s.readReg64 .x27 := h.2.2.2.2.2.2.2.2.2.1
theorem CallingConventionPreserved.x29 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x29 = s.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem CallingConventionPreserved.vregs {s s' : State} (h : CallingConventionPreserved s s') :
    calleeSavedVRegs s' = calleeSavedVRegs s := h.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## Bridge from `NewFromSliceOk` to `RunsToE` -/

theorem read8_eq_of_readBytes_eq {m₁ m₂ : Memory} {a₁ a₂ : BitVec 64} {n : ℕ}
    (h : m₁.readBytes a₁ n = m₂.readBytes a₂ n) {i : ℕ} (hi : i < n) :
    m₁.read8 (a₁ + BitVec.ofNat 64 i) = m₂.read8 (a₂ + BitVec.ofNat 64 i) := by
  have hi1 : i < (m₁.readBytes a₁ n).length := by rw [Memory.readBytes_length]; exact hi
  have hi2 : i < (m₂.readBytes a₂ n).length := by rw [Memory.readBytes_length]; exact hi
  have h1 := Bytes.readBytes_getElem m₁ a₁ n i hi1
  have h2 := Bytes.readBytes_getElem m₂ a₂ n i hi2
  have hq' : (m₁.readBytes a₁ n)[i]? = (m₂.readBytes a₂ n)[i]? := by rw [h]
  rw [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] at hq'
  exact h1.symm.trans ((Option.some.inj hq').trans h2)

theorem regionHeap_disjoint {b₁ b₂ : BitVec 64} {n₁ n₂ : ℕ} (m : Memory)
    (hd : DisjointRegions b₁ n₁ b₂ n₂) (hn₂ : n₂ ≤ 2 ^ 64) :
    (regionHeap b₁ n₁ m).Disjoint (regionHeap b₂ n₂ m) := by
  refine Heap.Disjoint.of_phys_left (ha := by simp [regionHeap]) (hf := by simp [regionHeap])
    (hm := by simp [regionHeap]) fun a => ?_
  by_cases ha₂ : InRegion b₂ n₂ a
  · have hout₁ : OutsideRegion b₁ n₁ a := hd.outside ha₂ hn₂
    have hnot₁ : ¬ InRegion b₁ n₁ a := (outsideRegion_iff_not_inRegion b₁ n₁ a).mp hout₁
    exact Or.inl (by simp [regionHeap, hnot₁])
  · exact Or.inr (Or.inl (by simp [regionHeap, ha₂]))

theorem satisfies_three_blocks {P1 P2 P3 : SepProp} {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ2 Φ3 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m) (hΦ3 : Φ3 m)
    (hrw1 : RW m b1 n1) (hrw2 : RW m b2 n2) (hrw3 : RW m b3 n3)
    (hd12 : DisjointRegions b1 n1 b2 n2)
    (hd13 : DisjointRegions b1 n1 b3 n3)
    (hd23 : DisjointRegions b2 n2 b3 n3)
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
  have hdisj23 : h2.Disjoint h3 := regionHeap_disjoint m hd23 hn3
  have hm23 : (h2.union h3).Matches m := Heap.Matches.union hm2 hm3
  have hdisj1_23 : h1.Disjoint (h2.union h3) :=
    (Heap.disjoint_union_right hdisj23).mpr
      ⟨regionHeap_disjoint m hd12 hn2, regionHeap_disjoint m hd13 hn3⟩
  exact Satisfies.sepConj_intro hdisj1_23 hp1 (SepProp.holds_sepConj_intro hdisj23 hp2 hp3)
    (Heap.Matches.union hm1 hm23)

theorem isBlock_three_none_outside {P1 P2 P3 : SepProp} {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ2 Φ3 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    {h : Heap} (hp : (P1 ∗ P2 ∗ P3) h) {a : BitVec 64}
    (ha1 : OutsideRegion b1 n1 a) (ha2 : OutsideRegion b2 n2 a) (ha3 : OutsideRegion b3 n3 a) :
    h a = none := by
  obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  have hn1 : ¬ InRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mp ha1
  have hn2 : ¬ InRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mp ha2
  have hn3 : ¬ InRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mp ha3
  simp [Heap.union, regionHeap, hn1, hn2, hn3]

theorem isBlock_three_mapped_false {P1 P2 P3 : SepProp} {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ2 Φ3 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    {h : Heap} (hp : (P1 ∗ P2 ∗ P3) h) (a : BitVec 64) :
    h.mapped a = false := by
  obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  simp [Heap.union, regionHeap]

/-- Frame condition preserving all readable bytes outside `regs`, as well as `Perm.rw` and
readability (`(perm a).r = true`) everywhere. -/
def S2Frame (m₁ m₂ : Memory) (regs : List (BitVec 64 × ℕ)) : Prop :=
  (∀ a, (m₁.perm a).r = true → m₁.isLazyFree a = false →
    (∀ r ∈ regs, OutsideRegion r.1 r.2 a) → m₂.read8 a = m₁.read8 a) ∧
  (((∀ a, m₁.permNoLazy a = some Perm.rw → m₂.permNoLazy a = some Perm.rw) ∧
    (∀ a, m₁.perm a = some Perm.rw → m₂.perm a = some Perm.rw)) ∧
   ((∀ a, (m₁.perm a).mapped = true ∧ m₁.isAnon a = true →
      (m₂.perm a).mapped = true ∧ m₂.isAnon a = true) ∧
    (∀ a, m₁.perm a = some Perm.protNone →
      (∀ r ∈ regs, OutsideRegion r.1 r.2 a) →
      m₂.perm a = some Perm.protNone ∧
      (m₁.isLazyFree a = false → m₂.read8 a = m₁.read8 a ∧ m₂.isLazyFree a = false)))) ∧
  (∀ a, (m₁.perm a).r = true → m₁.isLazyFree a = false →
    (m₂.perm a).r = true ∧ m₂.isLazyFree a = false)

namespace S2Frame

theorem refl (m : Memory) (regs : List (BitVec 64 × ℕ)) : S2Frame m m regs :=
  ⟨fun _ _ _ _ => rfl,
   ⟨⟨fun _ h => h, fun _ h => h⟩,
    ⟨fun _ h => h, fun _ h _ => ⟨h, fun hlf => ⟨rfl, hlf⟩⟩⟩⟩,
   fun _ hr hlf => ⟨hr, hlf⟩⟩

theorem of_frame {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ regs) : S2Frame m₁ m₂ regs :=
  ⟨fun a _ _ ha => hf.1 a ha,
   ⟨⟨fun a ha => by
      obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp ha
      exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨(congrFun hf.2.1 a).trans hp, hf.2.2.2.1 a hlf⟩,
     fun a ha => (congrFun hf.2.1 a).trans ha⟩,
    ⟨fun a ⟨hm, han⟩ => ⟨by rw [congrFun hf.2.1 a]; exact hm, hf.2.2.2.2 a han⟩,
     fun a ha hout => ⟨(congrFun hf.2.1 a).trans ha, fun hlf => ⟨hf.1 a hout, hf.2.2.2.1 a hlf⟩⟩⟩⟩,
   fun a hr hlf => ⟨by rw [congrFun hf.2.1 a]; exact hr, hf.2.2.2.1 a hlf⟩⟩

theorem trans {m₁ m₂ m₃ : Memory} {regs : List (BitVec 64 × ℕ)}
    (h₁ : S2Frame m₁ m₂ regs) (h₂ : S2Frame m₂ m₃ regs) : S2Frame m₁ m₃ regs :=
  ⟨fun a hr hlf ha =>
     let ⟨hr₂, hlf₂⟩ := h₁.2.2 a hr hlf
     (h₂.1 a hr₂ hlf₂ ha).trans (h₁.1 a hr hlf ha),
   ⟨⟨fun a hrw => h₂.2.1.1.1 a (h₁.2.1.1.1 a hrw),
     fun a hrw => h₂.2.1.1.2 a (h₁.2.1.1.2 a hrw)⟩,
    ⟨fun a hm => h₂.2.1.2.1 a (h₁.2.1.2.1 a hm),
     fun a hpn ha =>
       let ⟨hp₁, hf₁⟩ := h₁.2.1.2.2 a hpn ha
       let ⟨hp₂, hf₂⟩ := h₂.2.1.2.2 a hp₁ ha
       ⟨hp₂, fun hlf =>
         let ⟨hr₁, hlf₁⟩ := hf₁ hlf
         let ⟨hr₂, hlf₂⟩ := hf₂ hlf₁
         ⟨hr₂.trans hr₁, hlf₂⟩⟩⟩⟩,
   fun a hr hlf =>
     let ⟨hr₂, hlf₂⟩ := h₁.2.2 a hr hlf
     h₂.2.2 a hr₂ hlf₂⟩

theorem mono {m₁ m₂ : Memory} {regs regs' : List (BitVec 64 × ℕ)}
    (h : S2Frame m₁ m₂ regs)
    (hsub : ∀ a, (∀ r ∈ regs', OutsideRegion r.1 r.2 a) → ∀ r ∈ regs, OutsideRegion r.1 r.2 a) :
    S2Frame m₁ m₂ regs' :=
  ⟨fun a hr hlf ha => h.1 a hr hlf (hsub a ha),
   ⟨h.2.1.1,
    ⟨h.2.1.2.1, fun a hpn ha => h.2.1.2.2 a hpn (hsub a ha)⟩⟩,
   h.2.2⟩

theorem rw_of_rw {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (h : S2Frame m₁ m₂ regs) (a : BitVec 64) (n : ℕ) (hrw : RW m₁ a n) : RW m₂ a n :=
  fun x hx => h.2.1.1.1 x (hrw x hx)

theorem read64_eq {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (h : S2Frame m₁ m₂ regs) {a : BitVec 64} (hrw : RW m₁ a 8)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 a 8) :
    m₂.read64 a = m₁.read64 a := by
  refine Memory.read64_congr fun b hb => ?_
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw b hb)
  have hr : (m₁.perm b).r = true := by rw [hp]; rfl
  exact h.1 b hr hlf fun r hr_mem => (hd r hr_mem).outside hb (by decide)

theorem readBytes_eq {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (h : S2Frame m₁ m₂ regs) {a : BitVec 64} {n : ℕ} (hrw : RW m₁ a n)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 a n) (hn : n ≤ 2 ^ 64) :
    m₂.readBytes a n = m₁.readBytes a n := by
  refine Memory.readBytes_congr_region hn fun b hb => ?_
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw b hb)
  have hr : (m₁.perm b).r = true := by rw [hp]; rfl
  exact h.1 b hr hlf fun r hr_mem => (hd r hr_mem).outside hb hn

theorem update_two_blocks {P1 P1' P2 P2' R : SepProp}
    {b1 b2 : BitVec 64} {n1 n2 : ℕ} {Φ1 Φ1' Φ2 Φ2' : Memory → Prop}
    {m m' : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb1' : IsBlock P1' b1 n1 Φ1')
    (hb2 : IsBlock P2 b2 n2 Φ2) (hb2' : IsBlock P2' b2 n2 Φ2')
    (h : m ⊨ P1 ∗ (P2 ∗ R))
    (hf : S2Frame m m' [(b1, n1), (b2, n2)])
    (hΦ1' : Φ1' m') (hΦ2' : Φ2' m') :
    m' ⊨ P1' ∗ (P2' ∗ R) := by
  have hrw1 : RW m b1 n1 := hb1.rw h
  have h_swap : m ⊨ P2 ∗ (P1 ∗ R) := by rw [sepConj_left_comm]; exact h
  have hrw2 : RW m b2 n2 := hb2.rw h_swap
  have hrw1' : RW m' b1 n1 := hf.rw_of_rw b1 n1 hrw1
  have hrw2' : RW m' b2 n2 := hf.rw_of_rw b2 n2 hrw2
  obtain ⟨h1, h2R, hd1, hp1, hp2R, hm⟩ := Satisfies.sepConj_elim h
  obtain ⟨h2, hR, hd2, rfl, hp2, hpR⟩ := SepProp.holds_sepConj_elim hp2R
  have hm2R : (h2.union hR).Matches m := Heap.Matches.of_union_right hd1 hm
  have hmR : hR.Matches m := Heap.Matches.of_union_right hd2 hm2R
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  let h1' := regionHeap b1 n1 m'
  let h2' := regionHeap b2 n2 m'
  have hp1' : P1' h1' := (hb1'.iff h1').mpr ⟨m', hΦ1', rfl⟩
  have hp2' : P2' h2' := (hb2'.iff h2').mpr ⟨m', hΦ2', rfl⟩
  have hm1' : h1'.Matches m' := IsBlock.regionHeap_matches b1 n1 m' hrw1'
  have hm2' : h2'.Matches m' := IsBlock.regionHeap_matches b2 n2 m' hrw2'
  have hd2' : h2'.Disjoint hR := by
    refine Heap.Disjoint.of_phys_left (ha := by simp [h2', regionHeap])
      (hf := by simp [h2', regionHeap]) (hm := by simp [h2', regionHeap]) fun a => ?_
    by_cases ha2 : InRegion b2 n2 a
    · exact Or.inr (Or.inl (Heap.eq_none_of_disjoint_regionHeap hd2 ha2))
    · exact Or.inl (by simp [h2', regionHeap, ha2])
  have hd1' : h1'.Disjoint (h2'.union hR) := by
    refine Heap.Disjoint.of_phys_left (ha := by simp [h1', regionHeap])
      (hf := by simp [h1', regionHeap]) (hm := by simp [h1', regionHeap]) fun a => ?_
    by_cases ha1 : InRegion b1 n1 a
    · have h2Rn := Heap.eq_none_of_disjoint_regionHeap hd1 ha1
      refine Or.inr (Or.inl ?_)
      by_cases ha2 : InRegion b2 n2 a
      · simp [Heap.union, regionHeap, ha2] at h2Rn
      · simp [Heap.union, regionHeap, ha2] at h2Rn
        simp [Heap.union, h2', regionHeap, ha2, h2Rn]
    · exact Or.inl (by simp [h1', regionHeap, ha1])
  have hmR' : hR.Matches m' := by
    unfold Heap.Matches at hmR ⊢
    refine ⟨fun a c hc => ?_, hmR.2.1, fun a hmap => hf.2.1.2.1 a (hmR.2.2 a hmap)⟩
    have hn2 : ¬ InRegion b2 n2 a := by
      intro ha2
      have hRn := Heap.eq_none_of_disjoint_regionHeap hd2 ha2
      rw [hc] at hRn; cases hRn
    have hn1 : ¬ InRegion b1 n1 a := by
      intro ha1
      have h2Rn := Heap.eq_none_of_disjoint_regionHeap hd1 ha1
      simp [Heap.union, regionHeap, hn2, hc] at h2Rn
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
      have hnl : m.permNoLazy a = some Perm.rw := Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hperm, hlf⟩
      obtain ⟨hperm', hlf'⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hf.2.1.1.1 a hnl)
      exact ⟨(hf.1 a hr_true hlf ha_out).trans hr_eq, hperm', hlf'⟩
    | ro v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.ro v) hc
      obtain ⟨hperm', hlf'⟩ := hf.2.2 a hperm hlf
      exact ⟨(hf.1 a hperm hlf ha_out).trans hr_eq, hperm', hlf'⟩
    | protNone v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.protNone v) hc
      obtain ⟨hperm_m', hlf_imp⟩ := hf.2.1.2.2 a hperm ha_out
      obtain ⟨hr_m', hlf_m'⟩ := hlf_imp hlf
      exact ⟨hr_m'.trans hr_eq, hperm_m', hlf_m'⟩
    | lazy =>
      exact hf.2.1.1.2 a (hmR.1 a .lazy hc)
    | protNoneLazy =>
      exact (hf.2.1.2.2 a (hmR.1 a .protNoneLazy hc) ha_out).1
  exact Satisfies.sepConj_intro hd1' hp1' (SepProp.holds_sepConj_intro hd2' hp2' hpR)
    (Heap.Matches.union hm1' (Heap.Matches.union hm2' hmR'))

end S2Frame

/-- Full complement heap capturing `.rw`, `.ro` (readable), and `.protNone` bytes outside `h`. -/
def fullComplementHeap (h : Heap) (m : Memory) : Heap :=
  { phys := fun a =>
      match h.phys a with
      | some _ => none
      | none =>
        if m.perm a = some Perm.rw then
          if m.isLazyFree a then some .lazy else some (.rw (m.read8 a))
        else if (m.perm a).r = true ∧ m.isLazyFree a = false then
          some (.ro (m.read8 a))
        else if m.perm a = some Perm.protNone then
          if m.isLazyFree a then some .protNoneLazy else some (.protNone (m.read8 a))
        else none
    mapped := fun a => !h.mapped a && (m.perm a).mapped && m.isAnon a }

theorem disjoint_fullComplementHeap (h : Heap) (m : Memory) :
    h.Disjoint (fullComplementHeap h m) := by
  unfold Heap.Disjoint
  refine ⟨fun a => ?_, fun _ _ => Or.inr rfl, fun _ _ => Or.inr rfl,
    (fun _ _ _ _ hc => by rcases hc with ⟨_, h2⟩ | ⟨h2, _⟩ <;> cases h2),
    fun a => ?_⟩
  · dsimp only [fullComplementHeap]
    cases h.phys a with
    | none => exact Or.inl rfl
    | some _ => exact Or.inr (Or.inl rfl)
  · dsimp only [fullComplementHeap]
    cases h.mapped a <;> simp

theorem matches_fullComplementHeap (h : Heap) (m : Memory) :
    (fullComplementHeap h m).Matches m := by
  unfold Heap.Matches
  refine ⟨fun a c hc => ?_, ProofLib.Heap.GhostValid.of_phys rfl rfl, fun a hm => ?_⟩
  · dsimp only [fullComplementHeap] at hc
    cases hh : h.phys a with
    | some _ => rw [hh] at hc; cases hc
    | none =>
      rw [hh] at hc
      by_cases hrw : m.perm a = some Perm.rw
      · simp only [hrw, ite_true] at hc
        by_cases hlf : m.isLazyFree a = true
        · simp only [hlf, ite_true] at hc
          injection hc with hc; subst hc; exact hrw
        · simp only [hlf, Bool.not_eq_true, ite_false] at hc
          injection hc with hc; subst hc
          exact ⟨rfl, hrw, Bool.eq_false_iff.mpr hlf⟩
      · simp only [hrw, ite_false] at hc
        by_cases hr : (m.perm a).r = true ∧ m.isLazyFree a = false
        · simp only [hr, and_self, ite_true] at hc
          injection hc with hc; subst hc
          exact ⟨rfl, hr.1, hr.2⟩
        · simp only [hr, ite_false] at hc
          by_cases hpn : m.perm a = some Perm.protNone
          · simp only [hpn, ite_true] at hc
            by_cases hlf : m.isLazyFree a = true
            · simp only [hlf, ite_true] at hc
              injection hc with hc; subst hc; exact hpn
            · simp only [hlf, Bool.not_eq_true, ite_false] at hc
              injection hc with hc; subst hc
              exact ⟨rfl, hpn, Bool.eq_false_iff.mpr hlf⟩
          · simp only [hpn, ite_false] at hc; cases hc
  · dsimp only [fullComplementHeap] at hm
    simp only [Bool.and_eq_true] at hm
    exact ⟨hm.1.2, hm.2⟩

theorem isBlock_three_s2frame_aux {P1 P2 P3 : SepProp} {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ2 Φ3 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    {h : Heap} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hp : (P1 ∗ P2 ∗ P3) h) (hm : h.Matches m)
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
  · have hm0 : h.mapped a = false := isBlock_three_mapped_false hb1 hb2 hb3 hp a
    exact hmc_map a (by simp [fullComplementHeap, hm0, hm_a, han_a])
  · have hnone : h a = none := by
      unfold Heap.Matches at hm
      obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
      obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
      obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
      obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
      obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
      cases ha : (regionHeap b1 n1 m1 |>.union (regionHeap b2 n2 m2 |>.union (regionHeap b3 n3 m3))) a with
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
            simp [Heap.union, regionHeap, h1, h2, h3] at ha
        | lazy => rw [hpn_a] at hperm; cases hperm
        | protNoneLazy =>
          by_cases h1 : InRegion b1 n1 a <;>
            by_cases h2 : InRegion b2 n2 a <;>
            by_cases h3 : InRegion b3 n3 a <;>
            simp [Heap.union, regionHeap, h1, h2, h3] at ha
    by_cases hlf : m.isLazyFree a = true
    · have hca : (fullComplementHeap h m).phys a = some .protNoneLazy := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf]; rfl
      exact ⟨hmc a .protNoneLazy hca, fun hlf_f => by rw [hlf] at hlf_f; cases hlf_f⟩
    · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf
      have hca : (fullComplementHeap h m).phys a = some (.protNone (m.read8 a)) := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf_f]; rfl
      obtain ⟨hr, hp', hlf'⟩ := hmc a (.protNone (m.read8 a)) hca
      exact ⟨hp', fun _ => ⟨hr, hlf'⟩⟩

theorem isBlock_three_s2frame {P1 P1' P2 P3 R1 R2 R3 : SepProp}
    {ret keyA b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ1' Φ2 Φ3 : Memory → Prop}
    (hb1 : IsBlock P1 ret n1 Φ1) (hb1' : IsBlock P1' ret n1 Φ1')
    (hb2 : IsBlock P2 keyA n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    {hP : Heap} {m m' : Memory}
    (hpP : (P1 ∗ P2 ∗ P3) hP) (hmP : hP.Matches m)
    (hpost_1 : m' ⊨ P1' ∗ R1) (hpost_2 : m' ⊨ P2 ∗ R2) (hpost_3 : m' ⊨ P3 ∗ R3)
    (hn2 : n2 ≤ 2 ^ 64)
    (hkey_eq : m'.readBytes keyA n2 = m.readBytes keyA n2)
    (hmc : ∀ a c, (fullComplementHeap hP m).phys a = some c →
      match c with
      | .rw b => m'.read8 a = b ∧ m'.perm a = some Perm.rw ∧ m'.isLazyFree a = false
      | .ro b => m'.read8 a = b ∧ (m'.perm a).r = true ∧ m'.isLazyFree a = false
      | .protNone b => m'.read8 a = b ∧ m'.perm a = some Perm.protNone ∧ m'.isLazyFree a = false
      | .lazy => m'.perm a = some Perm.rw
      | .protNoneLazy => m'.perm a = some Perm.protNone)
    (hmc_map : ∀ a, (fullComplementHeap hP m).mapped a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) :
    S2Frame m m' [(ret, n1), (b3, n3)] := by
  refine ⟨fun a hr_a hlf_a ha => ?_,
    ⟨⟨fun a hnl_a => ?_, fun a hrw_a => ?_⟩,
     isBlock_three_s2frame_aux hb1 hb2 hb3 hpP hmP hmc hmc_map⟩,
    fun a hr_a hlf_a => ?_⟩
  · have ha1 : OutsideRegion ret n1 a := ha (ret, n1) (by simp)
    have ha3 : OutsideRegion b3 n3 a := ha (b3, n3) (by simp)
    by_cases hin2 : InRegion keyA n2 a
    · obtain ⟨i, hi, rfl⟩ := (inRegion_iff_exists_offset keyA n2 a hn2).mp hin2
      exact read8_eq_of_readBytes_eq hkey_eq hi
    · have ha2 : OutsideRegion keyA n2 a :=
        (outsideRegion_iff_not_inRegion keyA n2 a).mpr hin2
      have hnone : hP a = none := isBlock_three_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
      by_cases hrw_a : m.perm a = some Perm.rw
      · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_a]
        exact (hmc a _ hca).1
      · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
        exact (hmc a _ hca).1
  · by_cases hin1 : InRegion ret n1 a
    · exact hb1'.permNoLazy_rw hpost_1 hin1
    · by_cases hin2 : InRegion keyA n2 a
      · exact hb2.permNoLazy_rw hpost_2 hin2
      · by_cases hin3 : InRegion b3 n3 a
        · exact hb3.permNoLazy_rw hpost_3 hin3
        · have ha1 : OutsideRegion ret n1 a := (outsideRegion_iff_not_inRegion ret n1 a).mpr hin1
          have ha2 : OutsideRegion keyA n2 a := (outsideRegion_iff_not_inRegion keyA n2 a).mpr hin2
          have ha3 : OutsideRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mpr hin3
          have hnone : hP a = none := isBlock_three_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
          obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl_a
          have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_a]
          obtain ⟨-, hp', hlf'⟩ := hmc a _ hca
          exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp', hlf'⟩
  · by_cases hin1 : InRegion ret n1 a
    · exact hb1'.perm_rw hpost_1 hin1
    · by_cases hin2 : InRegion keyA n2 a
      · exact hb2.perm_rw hpost_2 hin2
      · by_cases hin3 : InRegion b3 n3 a
        · exact hb3.perm_rw hpost_3 hin3
        · have ha1 : OutsideRegion ret n1 a := (outsideRegion_iff_not_inRegion ret n1 a).mpr hin1
          have ha2 : OutsideRegion keyA n2 a := (outsideRegion_iff_not_inRegion keyA n2 a).mpr hin2
          have ha3 : OutsideRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mpr hin3
          have hnone : hP a = none := isBlock_three_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
          by_cases hlf_a : m.isLazyFree a = true
          · have hca : (fullComplementHeap hP m).phys a = some .lazy := by
              simp [fullComplementHeap, hnone, hrw_a, hlf_a]
            exact hmc a .lazy hca
          · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf_a
            have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
              simp [fullComplementHeap, hnone, hrw_a, hlf_f]
            exact (hmc a _ hca).2.1
  · by_cases hin1 : InRegion ret n1 a
    · exact ⟨by rw [hb1'.perm_rw hpost_1 hin1]; rfl, hb1'.isLazyFree_false hpost_1 hin1⟩
    · by_cases hin2 : InRegion keyA n2 a
      · exact ⟨by rw [hb2.perm_rw hpost_2 hin2]; rfl, hb2.isLazyFree_false hpost_2 hin2⟩
      · by_cases hin3 : InRegion b3 n3 a
        · exact ⟨by rw [hb3.perm_rw hpost_3 hin3]; rfl, hb3.isLazyFree_false hpost_3 hin3⟩
        · have ha1 : OutsideRegion ret n1 a := (outsideRegion_iff_not_inRegion ret n1 a).mpr hin1
          have ha2 : OutsideRegion keyA n2 a := (outsideRegion_iff_not_inRegion keyA n2 a).mpr hin2
          have ha3 : OutsideRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mpr hin3
          have hnone : hP a = none := isBlock_three_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
          by_cases hrw_a : m.perm a = some Perm.rw
          · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
              simp [fullComplementHeap, hnone, hrw_a, hlf_a]
            obtain ⟨-, hp', hlf'⟩ := hmc a _ hca
            exact ⟨by rw [hp']; rfl, hlf'⟩
          · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
              simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
            obtain ⟨-, hr', hlf'⟩ := hmc a _ hca
            exact ⟨hr', hlf'⟩

/-- Turns `NewFromSliceOk` into a `RunsToE` transition on a 32-byte key slice at `keyA`. -/
theorem nfs32_runsTo {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hNfs : NewFromSliceOk img C ctl abs)
    {s : State} {ret keyA : BitVec 64} {key : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hkey_len : key.length = 32)
    (hkey_mem : s.mem.readBytes keyA 32 = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_key : RW s.mem keyA 32)
    (hrw_stk : RW s.mem (s.sp - 544#64) 544)
    (hd_ret_key : DisjointRegions ret 0x98 keyA 32)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 544#64) 544)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 544#64) 544)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE (tripleRatchetProgAt img.base C ctl abs) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)]) := by
  intro hL
  have hfn : (tripleRatchetProgAt img.base C ctl abs).fnAddr newFromSliceName = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]") := by
    unfold tripleRatchetProgAt newFromSliceName
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]")]
  let xg : NewFromSliceGhost := { ret := ret, keyA := keyA, key := key }
  let P1 : SepProp := memRegion ret 0x98
  let P2 : SepProp := (keyA ↦ₛ key)
  let P3 : SepProp := stackAt s.sp newFromSliceStack
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 : IsBlock P1 ret 0x98 (fun _ => True) := IsBlock.memRegion ret 0x98
  have hb2 : IsBlock P2 keyA 32 (fun m => key.length ≤ 2 ^ 64 ∧ m.readBytes keyA key.length = key) :=
    IsBlock.pointsToBytes_len hkey_len
  have hb3 : IsBlock P3 (s.sp - 544#64) 544 (fun _ => True) := IsBlock.memRegion (s.sp - 544#64) 544
  have hkey_le64 : key.length ≤ 64 := by omega
  have hkey_le264 : key.length ≤ 2 ^ 64 := by omega
  have hsatP : s.mem ⊨ P :=
    satisfies_three_blocks hb1 hb2 hb3 trivial ⟨hkey_le264, by rwa [hkey_len]⟩ trivial
      hrw_ret hrw_key hrw_stk hd_ret_key hd_ret_stk hd_key_stk (by decide) (by decide)
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hx2_nat : (s.readReg64 .x2).toNat = key.length := by
    rw [hx2, hkey_len]; rfl
  have hpre_sat : s.mem ⊨ ((newFromSliceSpec C.F).inImage img).pre xg s ∗ R := by
    rw [Spec.inImage, newFromSliceSpec]
    dsimp only [xg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfrz, hsym⟩, ⟨hx0, hx1, hx2_nat, hkey_le64⟩, ?_⟩
    simpa [P, P1, P2, P3, sepConj_assoc] using hsatPR
  have hsp_aligned : s.spAligned = true := by
    simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full hNfs xg R (hpc.trans hfn.symm) hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [Spec.inImage, newFromSliceSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [Spec.inImage, newFromSliceSpec] at he; rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ hoom; dsimp only [Spec.inImage, newFromSliceSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact hoom.1) hL
  obtain ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, hfalse⟩⟩ := hcall
  · rw [Spec.inImage, newFromSliceSpec] at hpost_sat
    dsimp only [xg] at hpost_sat
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
    rcases hpost_sat with ⟨htr, hpost_sep⟩
    let P1' : SepProp := (ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key []
    have hb1_tag : IsBlock (ret ↦₆₄ 0#64) ret 8 (fun m => m.read64 ret = 0#64) :=
      IsBlock.pointsTo64 ret 0#64
    have hb1_hm : IsBlock (hmacCoreAt C.F (ret + 8#64) key []) (ret + 8#64) 0x90
        (fun m => HmacSt m (ret + 8#64) C.F key []) :=
      isBlock_hmacCoreAt C.F (ret + 8#64) key [] (by decide)
    have hb1' : IsBlock P1' ret 0x98
        (fun m => m.read64 ret = 0#64 ∧ HmacSt m (ret + 8#64) C.F key []) :=
      hb1_tag.sepConj hb1_hm rfl (by decide)
    change s'.mem ⊨ ((ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key [] ∗ P2 ∗ P3) ∗ R at hpost_sep
    have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by
      dsimp only [P1']; ac_nf at hpost_sep ⊢
    have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by
      ac_nf at hpost_1 ⊢
    have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by
      ac_nf at hpost_1 ⊢
    have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by
      ac_nf at hpost_1 ⊢
    obtain ⟨hok, hhm⟩ := hb1'.read hpost_1
    have hkey_s' : s'.mem.readBytes keyA 32 = key := by
      have h := (hb2.read hpost_2).2
      rwa [hkey_len] at h
    have hmc : hc.Matches s'.mem := by
      obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
      cases hR_hc'
      exact Heap.Matches.of_union_left hmatch
    unfold Heap.Matches at hmc
    have hmc_map := hmc.2.2
    replace hmc := hmc.1
    have hframe : S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)] :=
      isBlock_three_s2frame hb1 hb1' hb2 hb3 hpP hmP hpost_1 hpost_2 hpost_3
        (by decide) (hkey_s'.trans hkey_mem.symm) hmc hmc_map
    exact ⟨s', hsteps, ⟨htr, CallingConventionPreserved.vregs hcc⟩, ⟨hpc', hstat', hcc, hok, hhm, hframe⟩,
      hsteps.codeLoaded hL⟩
  · exact hfalse.elim

/-! ## Alignment, Sub-Region, and Disjointness Helpers -/

theorem sp0_aligned {sp sp0 : BitVec 64} (hsp0 : sp = sp0 + 432#64)
    (h : (sp &&& 0b1111#64) = 0#64) :
    (sp0 &&& 15#64) = 0#64 := by
  have h1 : sp0 = sp - 432#64 := by subst hsp0; bv_lin
  rw [h1]
  change (sp &&& 15#64) = 0#64 at h
  bv_bits

theorem sp0_aligned_0b1111 {sp0 : BitVec 64} (h : (sp0 &&& 15#64) = 0#64) :
    (sp0 &&& 0b1111#64) = 0#64 := h

theorem disj_sp0_off (sp0 off₁ : BitVec 64) (sz₁ : ℕ) (off₂ : BitVec 64) (sz₂ : ℕ)
    (h : sz₁ ≤ (off₂ - off₁).toNat ∧ sz₂ ≤ (off₁ - off₂).toNat) :
    DisjointRegions (sp0 + off₁) sz₁ (sp0 + off₂) sz₂ := by
  unfold DisjointRegions
  have h1 : (sp0 + off₂) - (sp0 + off₁) = off₂ - off₁ := by bv_lin
  have h2 : (sp0 + off₁) - (sp0 + off₂) = off₁ - off₂ := by bv_lin
  rw [h1, h2]
  exact h

theorem disj_sp0_zero_off (sp0 : BitVec 64) (sz₁ : ℕ) (off₂ : BitVec 64) (sz₂ : ℕ)
    (h : sz₁ ≤ off₂.toNat ∧ sz₂ ≤ (0#64 - off₂).toNat) :
    DisjointRegions sp0 sz₁ (sp0 + off₂) sz₂ := by
  unfold DisjointRegions
  have h1 : (sp0 + off₂) - sp0 = off₂ := by bv_lin
  have h2 : sp0 - (sp0 + off₂) = 0#64 - off₂ := by bv_lin
  rw [h1, h2]
  exact h

theorem disj_sp0_sub_off (sp0 off₁ : BitVec 64) (sz₁ : ℕ) (off₂ : BitVec 64) (sz₂ : ℕ)
    (h : sz₁ ≤ (off₂ + off₁).toNat ∧ sz₂ ≤ (0#64 - (off₂ + off₁)).toNat) :
    DisjointRegions (sp0 - off₁) sz₁ (sp0 + off₂) sz₂ := by
  unfold DisjointRegions
  have h1 : (sp0 + off₂) - (sp0 - off₁) = off₂ + off₁ := by bv_lin
  have h2 : (sp0 - off₁) - (sp0 + off₂) = 0#64 - (off₂ + off₁) := by bv_lin
  rw [h1, h2]
  exact h

theorem rw_stk_sub {m : Memory} {sp0 : BitVec 64} (hrw : RW m (sp0 - 544#64) 976)
    (addr : BitVec 64) (sz : ℕ)
    (hsub : (addr - (sp0 - 544#64)).toNat + sz ≤ 976) :
    RW m addr sz := by
  intro a ha
  apply hrw a
  simp only [InRegion] at ha ⊢
  bv_omega

theorem disj_stk_sub_right {a : BitVec 64} {n : ℕ} {sp0 : BitVec 64}
    (hd : DisjointRegions a n (sp0 - 544#64) 976) (addr : BitVec 64) (sz : ℕ)
    (hsub : 0 < sz ∧ (addr - (sp0 - 544#64)).toNat + sz ≤ 976) :
    DisjointRegions a n addr sz :=
  hd.sub_right addr hsub

/-! ## Frame, Saved Registers, and Common State Invariant -/

def saltPtrOf (sp0 : BitVec 64) (x : ExtractGhost) : BitVec 64 :=
  match x.salt with
  | none => sp0 + 144#64
  | some _ => x.saltA

def saltRegOf (sp0 : BitVec 64) (x : ExtractGhost) : BitVec 64 :=
  if x.saltA = 0#64 then sp0 + 144#64 else x.saltA

def saltSliceOf (x : ExtractGhost) : List (BitVec 8) :=
  match x.salt with
  | none => if x.saltA = 0#64 then List.replicate 32 0#8 else []
  | some s => s.toList

theorem saltSliceOf_length_le (x : ExtractGhost) : (saltSliceOf x).length ≤ 32 := by
  rcases x with ⟨ret, saltA, _ | s, ikmA, ikm⟩
  · dsimp only [saltSliceOf]
    split <;> decide
  · dsimp only [saltSliceOf]
    simp

theorem pointsToBytes_saltRegOf_eq (sp0 : BitVec 64) (x : ExtractGhost)
    (hsalt_some : ∀ sv, x.salt = some sv → x.saltA ≠ 0#64) :
    (saltRegOf sp0 x ↦ₛ saltSliceOf x) = (saltPtrOf sp0 x ↦ₛ saltSliceOf x) := by
  rcases x with ⟨ret, saltA, _ | sv, ikmA, ikm⟩
  · dsimp only [saltRegOf, saltPtrOf, saltSliceOf]
    by_cases h0 : saltA = 0#64
    · simp [h0]
    · simp [h0, pointsToBytes_nil]
  · have hne : saltA ≠ 0#64 := hsalt_some sv rfl
    simp [saltRegOf, saltPtrOf, saltSliceOf, hne]

theorem hmacSt_saltSliceOf (m : Memory) (a : BitVec 64)
    (F : ShaState → List (BitVec 8) → ShaState) (x : ExtractGhost) (msg : List (BitVec 8)) :
    HmacSt m a F (saltSliceOf x) msg = HmacSt m a F (effectiveSalt x.salt) msg := by
  rcases x with ⟨ret, saltA, _ | s, ikmA, ikm⟩
  · dsimp only [saltSliceOf, effectiveSalt, Option.map, Option.getD]
    split <;> rfl
  · rfl

theorem effectiveSalt_length (salt : Salt) : (effectiveSalt salt).length = 32 := by
  cases salt with
  | none => rfl
  | some s => exact s.2

theorem prk_length_le (F : ShaCompress) (x : ExtractGhost) :
    (x.prk F).length ≤ 64 := by
  dsimp [ExtractGhost.prk, hkdfExtract]
  rw [length_hmacWith]
  decide

theorem frame_of_agreesOutside {m₁ m₂ : Memory} {a : BitVec 64} {n : ℕ}
    (h : AgreesOutside m₁ m₂ a n) : Frame m₁ m₂ [(a, n)] :=
  (Frame.refl m₁ [(a, n)]).trans_agreesOutside (by simp) h

abbrev ExtFrame (s0 : State) (sp0 : BitVec 64) (m : Memory) : Prop :=
  S2Frame s0.mem m [(s0.readReg64 .x0, 0xb0), (sp0 - 544#64, 976)]

structure ExtSaved (s0 : State) (sp0 : BitVec 64) (m : Memory) : Prop where
  h29 : m.read64 (sp0 + 336#64) = s0.readReg64 .x29
  hlr : m.read64 (sp0 + 344#64) = s0.readReg64 .lr
  h28 : m.read64 (sp0 + 352#64) = s0.readReg64 .x28
  h26 : m.read64 (sp0 + 368#64) = s0.readReg64 .x26
  h25 : m.read64 (sp0 + 376#64) = s0.readReg64 .x25
  h24 : m.read64 (sp0 + 384#64) = s0.readReg64 .x24
  h23 : m.read64 (sp0 + 392#64) = s0.readReg64 .x23
  h22 : m.read64 (sp0 + 400#64) = s0.readReg64 .x22
  h21 : m.read64 (sp0 + 408#64) = s0.readReg64 .x21
  h20 : m.read64 (sp0 + 416#64) = s0.readReg64 .x20
  h19 : m.read64 (sp0 + 424#64) = s0.readReg64 .x19

theorem agreesOutside_sp0_write64 {m₁ m₂ : Memory} {sp0 off v : BitVec 64} {n : ℕ}
    (h : AgreesOutside m₁ m₂ sp0 n)
    (hoff : decide (off.toNat + 8 ≤ n ∧ n ≤ 432) = true) :
    AgreesOutside m₁ (m₂.write64 (sp0 + off) v) sp0 n := by
  obtain ⟨hk, hn⟩ := of_decide_eq_true hoff
  exact h.write64 (by bv_omega) (by omega)

theorem agreesOutside_sp0_write64_zero {m₁ m₂ : Memory} {sp0 v : BitVec 64} {n : ℕ}
    (h : AgreesOutside m₁ m₂ sp0 n)
    (hoff : decide (8 ≤ n ∧ n ≤ 432) = true) :
    AgreesOutside m₁ (m₂.write64 sp0 v) sp0 n := by
  obtain ⟨hk, hn⟩ := of_decide_eq_true hoff
  exact h.write64 (by bv_omega) (by omega)

theorem agreesOutside_sp0_write8 {m₁ m₂ : Memory} {sp0 off : BitVec 64} {v : BitVec 8} {n : ℕ}
    (h : AgreesOutside m₁ m₂ sp0 n)
    (hoff : decide (off.toNat < n ∧ n ≤ 432) = true) :
    AgreesOutside m₁ (m₂.write8 (sp0 + off) v) sp0 n := by
  obtain ⟨hk, hn⟩ := of_decide_eq_true hoff
  exact h.write8 (by simp only [InRegion]; bv_omega)

theorem agreesOutside_out_write64 {m₁ m₂ : Memory} {out off v : BitVec 64}
    (h : AgreesOutside m₁ m₂ out 0xb0)
    (hoff : decide (off.toNat + 8 ≤ 0xb0) = true) :
    AgreesOutside m₁ (m₂.write64 (out + off) v) out 0xb0 := by
  have hk : off.toNat + 8 ≤ 0xb0 := of_decide_eq_true hoff
  exact h.write64 (by bv_omega) (by decide)

theorem agreesOutside_out_write64_zero {m₁ m₂ : Memory} {out v : BitVec 64}
    (h : AgreesOutside m₁ m₂ out 0xb0) :
    AgreesOutside m₁ (m₂.write64 out v) out 0xb0 :=
  h.write64 (by bv_omega) (by decide)

theorem ExtFrame.of_agreesOutside_sp0 {s0 : State} {sp0 : BitVec 64} {m m' : Memory} {n : ℕ}
    (hf : ExtFrame s0 sp0 m) (hn : n ≤ 432) (hag : AgreesOutside m m' sp0 n) :
    ExtFrame s0 sp0 m' := by
  refine hf.trans ((S2Frame.of_frame (frame_of_agreesOutside hag)).mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 544#64) 976 a :=
    ha (sp0 - 544#64, 976) (by simp)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [OutsideRegion] at hstk ⊢
  bv_omega

theorem ExtFrame.of_agreesOutside_out {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    (hf : ExtFrame s0 sp0 m) (hag : AgreesOutside m m' (s0.readReg64 .x0) 0xb0) :
    ExtFrame s0 sp0 m' := by
  refine hf.trans ((S2Frame.of_frame (frame_of_agreesOutside hag)).mono fun a ha => ?_)
  have hout : OutsideRegion (s0.readReg64 .x0) 0xb0 a :=
    ha (s0.readReg64 .x0, 0xb0) (by simp)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hout

theorem ExtSaved.of_s2frame {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    {rs : List (BitVec 64 × ℕ)} (hs : ExtSaved s0 sp0 m) (hf : S2Frame m m' rs)
    (hrw : RW m (sp0 + 336#64) 96)
    (hd : ∀ r ∈ rs, DisjointRegions r.1 r.2 (sp0 + 336#64) 96) :
    ExtSaved s0 sp0 m' := by
  have hread (off : BitVec 64)
      (hsub : 0 < 8 ∧ ((sp0 + off) - (sp0 + 336#64)).toNat + 8 ≤ 96) :
      m'.read64 (sp0 + off) = m.read64 (sp0 + off) :=
    hf.read64_eq (hrw.sub hsub.2) fun r hr => (hd r hr).sub_right (sp0 + off) hsub
  have hsub_off (off : BitVec 64) (h : (off - 336#64).toNat + 8 ≤ 96) :
      0 < 8 ∧ ((sp0 + off) - (sp0 + 336#64)).toNat + 8 ≤ 96 := by
    have heq : (sp0 + off) - (sp0 + 336#64) = off - 336#64 := by bv_lin
    rw [heq]
    exact ⟨by decide, h⟩
  exact
    { h29 := (hread 336#64 (hsub_off 336#64 (by decide))).trans hs.h29
      hlr := (hread 344#64 (hsub_off 344#64 (by decide))).trans hs.hlr
      h28 := (hread 352#64 (hsub_off 352#64 (by decide))).trans hs.h28
      h26 := (hread 368#64 (hsub_off 368#64 (by decide))).trans hs.h26
      h25 := (hread 376#64 (hsub_off 376#64 (by decide))).trans hs.h25
      h24 := (hread 384#64 (hsub_off 384#64 (by decide))).trans hs.h24
      h23 := (hread 392#64 (hsub_off 392#64 (by decide))).trans hs.h23
      h22 := (hread 400#64 (hsub_off 400#64 (by decide))).trans hs.h22
      h21 := (hread 408#64 (hsub_off 408#64 (by decide))).trans hs.h21
      h20 := (hread 416#64 (hsub_off 416#64 (by decide))).trans hs.h20
      h19 := (hread 424#64 (hsub_off 424#64 (by decide))).trans hs.h19 }

theorem ExtSaved.of_frame {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    {rs : List (BitVec 64 × ℕ)} (hs : ExtSaved s0 sp0 m) (hf : Frame m m' rs)
    (hd : ∀ r ∈ rs, DisjointRegions r.1 r.2 (sp0 + 336#64) 96) :
    ExtSaved s0 sp0 m' := by
  have hread (off : BitVec 64)
      (hsub : 0 < 8 ∧ ((sp0 + off) - (sp0 + 336#64)).toNat + 8 ≤ 96) :
      m'.read64 (sp0 + off) = m.read64 (sp0 + off) :=
    hf.read64_eq fun r hr => (hd r hr).sub_right (sp0 + off) hsub
  have hsub_off (off : BitVec 64) (h : (off - 336#64).toNat + 8 ≤ 96) :
      0 < 8 ∧ ((sp0 + off) - (sp0 + 336#64)).toNat + 8 ≤ 96 := by
    have heq : (sp0 + off) - (sp0 + 336#64) = off - 336#64 := by bv_lin
    rw [heq]
    exact ⟨by decide, h⟩
  exact
    { h29 := (hread 336#64 (hsub_off 336#64 (by decide))).trans hs.h29
      hlr := (hread 344#64 (hsub_off 344#64 (by decide))).trans hs.hlr
      h28 := (hread 352#64 (hsub_off 352#64 (by decide))).trans hs.h28
      h26 := (hread 368#64 (hsub_off 368#64 (by decide))).trans hs.h26
      h25 := (hread 376#64 (hsub_off 376#64 (by decide))).trans hs.h25
      h24 := (hread 384#64 (hsub_off 384#64 (by decide))).trans hs.h24
      h23 := (hread 392#64 (hsub_off 392#64 (by decide))).trans hs.h23
      h22 := (hread 400#64 (hsub_off 400#64 (by decide))).trans hs.h22
      h21 := (hread 408#64 (hsub_off 408#64 (by decide))).trans hs.h21
      h20 := (hread 416#64 (hsub_off 416#64 (by decide))).trans hs.h20
      h19 := (hread 424#64 (hsub_off 424#64 (by decide))).trans hs.h19 }

theorem ExtSaved.of_agreesOutside_328 {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    (hs : ExtSaved s0 sp0 m) (hag : AgreesOutside m m' sp0 328) :
    ExtSaved s0 sp0 m' := by
  refine hs.of_frame (frame_of_agreesOutside hag) ?_
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact disj_sp0_zero_off sp0 328 336#64 96 (by decide)

theorem ExtSaved_and_Frame_of_agreesOutside_328 {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    (hs : ExtSaved s0 sp0 m) (hf : ExtFrame s0 sp0 m) (hag : AgreesOutside m m' sp0 328) :
    ExtSaved s0 sp0 m' ∧ ExtFrame s0 sp0 m' :=
  ⟨hs.of_agreesOutside_328 hag, hf.of_agreesOutside_sp0 (by decide) hag⟩

theorem ExtFrame.trans_pair {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    {a₁ : BitVec 64} {n₁ : ℕ} {a₂ : BitVec 64} {n₂ : ℕ}
    (hf₁ : ExtFrame s0 sp0 m) (hf₂ : S2Frame m m' [(a₁, n₁), (a₂, n₂)])
    (hsub₁ : (a₁ - (sp0 - 544#64)).toNat + n₁ ≤ 976)
    (hsub₂ : (a₂ - (sp0 - 544#64)).toNat + n₂ ≤ 976) :
    ExtFrame s0 sp0 m' := by
  refine hf₁.trans (hf₂.mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 544#64) 976 a :=
    ha (sp0 - 544#64, 976) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  simp only [OutsideRegion] at hstk ⊢
  refine ⟨by bv_omega, by bv_omega⟩

theorem ExtFrame.trans_triple {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    {a₁ : BitVec 64} {n₁ : ℕ} {a₂ : BitVec 64} {n₂ : ℕ} {a₃ : BitVec 64} {n₃ : ℕ}
    (hf₁ : ExtFrame s0 sp0 m) (hf₂ : Frame m m' [(a₁, n₁), (a₂, n₂), (a₃, n₃)])
    (hsub₁ : (a₁ - (sp0 - 544#64)).toNat + n₁ ≤ 976)
    (hsub₂ : (a₂ - (sp0 - 544#64)).toNat + n₂ ≤ 976)
    (hsub₃ : (a₃ - (sp0 - 544#64)).toNat + n₃ ≤ 976) :
    ExtFrame s0 sp0 m' := by
  refine hf₁.trans ((S2Frame.of_frame hf₂).mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 544#64) 976 a :=
    ha (sp0 - 544#64, 976) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  simp only [OutsideRegion] at hstk ⊢
  refine ⟨by bv_omega, by bv_omega, by bv_omega⟩

theorem HmacSt.of_writeBytes_32_write8_pos {m : Memory} {sp0 : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key ikm : List (BitVec 8)}
    (hhm : HmacSt m sp0 F key []) (hlen : ikm.length = 32) :
    HmacSt ((m.writeBytes sp0 ikm).write8 (sp0 + 63#64) 32#8) sp0 F key ikm := by
  let m₁ := m.writeBytes sp0 ikm
  let m₂ := m₁.write8 (sp0 + 63#64) 32#8
  have hag1 : AgreesOutside m m₁ sp0 32 := by
    have h := ProofLib.AgreesOutside.writeBytes_self m sp0 ikm
    rwa [hlen] at h
  have hag2 : AgreesOutside m₁ m₂ (sp0 + 63#64) 1 :=
    (AgreesOutside.rfl' m₁ (sp0 + 63#64) 1).write8 (by simp only [InRegion]; bv_omega)
  have hf64 : Frame m m₂ [(sp0, 64)] :=
    ((Frame.refl m [(sp0, 64)]).trans_agreesOutside_sub (rbase := sp0) (rlen := 64)
      (by simp) (by bv_omega) hag1).trans_agreesOutside_sub (rbase := sp0) (rlen := 64)
      (by simp) (by bv_omega) hag2
  rcases hhm with ⟨_, _, _, hin, hinB, hout, houtB⟩
  change HmacSt m₂ sp0 F key ikm
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hread2 : m₂.readBytes sp0 ikm.length = m₁.readBytes sp0 ikm.length := by
      refine (frame_of_agreesOutside hag2).readBytes_eq ?_ (by omega)
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      rw [hlen]
      exact (disj_sp0_zero_off sp0 32 63#64 1 (by decide)).symm
    rw [hread2]
    exact Bytes.readBytes_writeBytes_same m sp0 ikm (by omega)
  · dsimp [m₂]
    rw [Memory.read8_write8_same, hlen]
  · rw [hf64.readBytes_eq ?_ (by decide), hin]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact disj_sp0_zero_off sp0 64 0x40#64 32 (by decide)
  · rw [hf64.read64_eq ?_, hinB]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact disj_sp0_zero_off sp0 64 0x60#64 8 (by decide)
  · rw [hf64.readBytes_eq ?_ (by decide), hout]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact disj_sp0_zero_off sp0 64 0x68#64 32 (by decide)
  · rw [hf64.read64_eq ?_, houtB]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact disj_sp0_zero_off sp0 64 0x88#64 8 (by decide)

/-! ## Cut Predicates and Read/Write Helpers -/

abbrev ExtCommon (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  s.status = .Running ∧
  s.sp = sp0 ∧
  s.readReg64 .x19 = s0.readReg64 .x0 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x29 = sp0 + 336#64 ∧
  ExtSaved s0 sp0 s.mem ∧
  ExtFrame s0 sp0 s.mem

def ENfs1 (b : BitVec 64) (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommon s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]") ∧
  s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 80) ∧
  s.readReg64 .x0 = sp0 + 176#64 ∧
  s.readReg64 .x1 = saltRegOf sp0 x ∧
  s.readReg64 .x2 = BitVec.ofNat 64 (saltSliceOf x).length ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = 32#64 ∧
  (∀ sv, x.salt = some sv → x.saltA ≠ 0#64) ∧
  s.mem.readBytes (saltPtrOf sp0 x) (saltSliceOf x).length = saltSliceOf x

def ERet1 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommon s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 80) ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = 32#64 ∧
  s.mem.read64 (sp0 + 176#64) = 0#64 ∧
  HmacSt s.mem (sp0 + 184#64) F (effectiveSalt x.salt) []

def EMemcpy (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommon s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "memcpy") ∧
  s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 192) ∧
  s.readReg64 .x0 = sp0 ∧
  s.readReg64 .x1 = x.ikmA ∧
  s.readReg64 .x2 = 32#64 ∧
  s.readReg64 .x21 = 32#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.readReg64 .x25 = 0#64 ∧
  HmacSt s.mem sp0 F (effectiveSalt x.salt) []

def EC88 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommon s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 328) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacSt s.mem sp0 F (effectiveSalt x.salt) x.ikm

def EFin (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommon s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]") ∧
  s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 380) ∧
  s.readReg64 .x0 = sp0 + 144#64 ∧
  s.readReg64 .x1 = sp0 + 176#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacSt s.mem (sp0 + 176#64) F (effectiveSalt x.salt) x.ikm

def ERetFin (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommon s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 380) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.readBytes (sp0 + 144#64) 32 = x.prk F

def ENfs2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommon s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]") ∧
  s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 396) ∧
  s.readReg64 .x0 = sp0 + 176#64 ∧
  s.readReg64 .x1 = sp0 + 144#64 ∧
  s.readReg64 .x2 = 32#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.readBytes (sp0 + 144#64) 32 = x.prk F

def ERet2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommon s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 396) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.read64 (sp0 + 176#64) = 0#64 ∧
  s.mem.readBytes (sp0 + 144#64) 32 = x.prk F ∧
  HmacSt s.mem (sp0 + 184#64) F (x.prk F) []

def EPost (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s' : State) : Prop :=
  s'.pc = s0.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s0 s' ∧
  s'.mem.readBytes (s0.readReg64 .x0) 32 = x.prk F ∧
  HmacSt s'.mem (s0.readReg64 .x0 + 0x20#64) F (x.prk F) [] ∧
  ExtFrame s0 sp0 s'.mem

theorem readBytes_32_zero_of_read64_zero {m : Memory} {a : BitVec 64}
    (h0 : m.read64 a = 0#64)
    (h8 : m.read64 (a + 8#64) = 0#64)
    (h16 : m.read64 (a + 16#64) = 0#64)
    (h24 : m.read64 (a + 24#64) = 0#64) :
    m.readBytes a 32 = List.replicate 32 0#8 := by
  rw [readBytes_32_eq_read64 m a, h0, h8, h16, h24]
  rfl

theorem read64_sp0_write64_out (m : Memory) {sp0 rOff out wOff v : BitVec 64}
    (hd : DisjointRegions out 0xb0 (sp0 - 544#64) 976)
    (hr : decide (rOff.toNat + 8 ≤ 432) = true)
    (hw : decide (wOff.toNat + 8 ≤ 0xb0) = true) :
    (m.write64 (out + wOff) v).read64 (sp0 + rOff) = m.read64 (sp0 + rOff) := by
  have hr' : rOff.toNat + 8 ≤ 432 := of_decide_eq_true hr
  have hw' : wOff.toNat + 8 ≤ 0xb0 := of_decide_eq_true hw
  exact Memory.read64_write64_of_disjoint64_left m (out + wOff) (sp0 + rOff) v
    ((hd.sub_left (out + wOff) ⟨by decide, by bv_omega⟩).sub_right
      (sp0 + rOff) ⟨by decide, by bv_omega⟩)

theorem read64_sp0_write64_out_zero (m : Memory) {sp0 rOff out v : BitVec 64}
    (hd : DisjointRegions out 0xb0 (sp0 - 544#64) 976)
    (hr : decide (rOff.toNat + 8 ≤ 432) = true) :
    (m.write64 out v).read64 (sp0 + rOff) = m.read64 (sp0 + rOff) := by
  have hr' : rOff.toNat + 8 ≤ 432 := of_decide_eq_true hr
  exact Memory.read64_write64_of_disjoint64_left m out (sp0 + rOff) v
    ((hd.sub_left out ⟨by decide, by bv_omega⟩).sub_right
      (sp0 + rOff) ⟨by decide, by bv_omega⟩)

/-! ## Relocatable `[LibsignalPlacement]` Cut Predicates -/

def ENfs1Placed [LibsignalPlacement] (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommon s0 sp0 s ∧
  s.pc = lsmpl.base 114 ∧
  s.readReg64 .lr = (blkPl_54).base + 80#64 ∧
  s.readReg64 .x0 = sp0 + 176#64 ∧
  s.readReg64 .x1 = saltRegOf sp0 x ∧
  s.readReg64 .x2 = BitVec.ofNat 64 (saltSliceOf x).length ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = 32#64 ∧
  (∀ sv, x.salt = some sv → x.saltA ≠ 0#64) ∧
  s.mem.readBytes (saltPtrOf sp0 x) (saltSliceOf x).length = saltSliceOf x

def EMemcpyPlaced [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommon s0 sp0 s ∧
  s.pc = lsρ lsMemcpySym ∧
  s.readReg64 .lr = (blkPl_54).base + 192#64 ∧
  s.readReg64 .x0 = sp0 ∧
  s.readReg64 .x1 = x.ikmA ∧
  s.readReg64 .x2 = 32#64 ∧
  s.readReg64 .x21 = 32#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.readReg64 .x25 = 0#64 ∧
  HmacSt s.mem sp0 F (effectiveSalt x.salt) []

def EFinPlaced [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommon s0 sp0 s ∧
  s.pc = (blkPl_123).base ∧
  s.readReg64 .lr = (blkPl_54).base + 380#64 ∧
  s.readReg64 .x0 = sp0 + 144#64 ∧
  s.readReg64 .x1 = sp0 + 176#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacSt s.mem (sp0 + 176#64) F (effectiveSalt x.salt) x.ikm

def ENfs2Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommon s0 sp0 s ∧
  s.pc = lsmpl.base 114 ∧
  s.readReg64 .lr = (blkPl_54).base + 396#64 ∧
  s.readReg64 .x0 = sp0 + 176#64 ∧
  s.readReg64 .x1 = sp0 + 144#64 ∧
  s.readReg64 .x2 = 32#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.readBytes (sp0 + 144#64) 32 = x.prk F

end Extract

end CryptoVerification.LibsignalTripleRatchet
