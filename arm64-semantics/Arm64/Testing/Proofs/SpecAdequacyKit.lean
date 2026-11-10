/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted
public import ProofLib.SepLogic
public import ProofLib.Hoare.Safety
public import Arm64.Testing.Proofs.SpecAdequacyRustExamples
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model
import Arm64.Trusted.Spec.SepLogicModel

/-!
# Supporting Adequacy Kit

Frame construction (`frameHeap`, `SupportedIn`), byte-heap materialization, and generic operational
adequacy drivers (`subroutine_ok_adequacy`) bridging separation-logic contracts to machine-state
execution in [`Arm64/Testing/Tours/SpecAdequacyTour.lean`](../Tours/SpecAdequacyTour.lean).
-/

public section

namespace Arm64.Testing.SpecAdequacyTour

open Arm64
open ProofLib

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Arm64.SepProp
  SepProp.Satisfies SepProp.Entails SepProp.emp SepProp.pure SepProp.sepConj SepProp.sepExists
  Heap.empty Heap.singleton Heap.Disjoint Heap.union Heap.Matches
  pointsTo8 pointsToBytes pointsTo64 memRegion

/-! ## Rest-of-the-world frame and footprints -/

/-- The "rest of the world" heap for footprint `fp` in memory `m`: every byte outside `fp`
    that is readable in `m` (`m.isLazyFree a = false`), holding its current value. Writable bytes
    become `.rw` cells and other readable bytes (for example code and read-only data) become `.ro`
    cells. Unreadable or `MADV_FREE` (`isLazyFree`) bytes are left out, because `Heap.Matches`
    requires `.rw` and `.ro` cells to be readable (`isLazyFree = false`). -/
@[expose] def frameHeap (fp : BitVec 64 → Prop) [DecidablePred fp] (m : Memory) : Heap :=
  { phys := fun a =>
      if fp a ∨ m.isLazyFree a = true then none
      else if m.perm a = some Perm.rw then some (.rw (m.read8 a))
      else if (m.perm a).r then some (.ro (m.read8 a))
      else none }

def frameOf (fp : BitVec 64 → Prop) [DecidablePred fp] (m : Memory) : SepProp :=
  ⟨fun h => h = frameHeap fp m⟩

private theorem frameOf_holds {fp : BitVec 64 → Prop} [DecidablePred fp] {m : Memory} {h : Heap} :
    frameOf fp m h = (h = frameHeap fp m) := by rfl

/-- `P` only ever owns bytes inside `fp`: every heap satisfying `P` is undefined outside `fp`. -/
@[expose] def SupportedIn (P : SepProp) (fp : BitVec 64 → Prop) : Prop :=
  ∀ h, P h → (∀ a, ¬ fp a → h a = none) ∧ h.auth = (fun _ _ => none) ∧
    h.frag = (fun _ _ => none) ∧ h.mapped = (fun _ => false)

/-- If `P` holds of some heap that matches `m` and lives inside `fp`, then `m` satisfies `P`
    framed by `frameOf fp m`. -/
theorem sat_with_frame {P : SepProp} {fp : BitVec 64 → Prop} [DecidablePred fp] {m : Memory}
    (hP : ∃ h, P h ∧ h.Matches m) (hs : SupportedIn P fp) : m ⊨ P ∗ frameOf fp m := by
  obtain ⟨h, hPh, hm⟩ := hP
  refine SepProp.satisfies_iff.2 ⟨h.union (frameHeap fp m),
    SepProp.holds_sepConj_iff.2 ⟨h, frameHeap fp m, ?_, rfl, hPh, by simp [frameOf_holds]⟩, ?_⟩
  · refine ⟨fun a => ?_, fun _ _ => Or.inr rfl, fun _ _ => Or.inr rfl,
      fun γ k oa v h' => ?_, fun _ => Or.inr rfl⟩
    · by_cases hfa : fp a
      · exact Or.inr (Or.inl (by simp [frameHeap, hfa]))
      · exact Or.inl ((hs h hPh).1 a hfa)
    · rcases h' with ⟨_, hfv⟩ | ⟨ha, _⟩
      · simp [frameHeap] at hfv
      · simp [frameHeap] at ha
  · refine ⟨fun a c hc => ?_, ?_, fun a hma => ?_⟩
    · simp only [Heap.union] at hc
      cases hha : h.phys a with
      | some c' =>
        rw [hha] at hc
        exact hm.1 a c (hha.trans hc)
      | none =>
        rw [hha] at hc
        simp only [frameHeap] at hc
        split at hc
        · cases hc
        · rename_i hnot
          have hlf : m.isLazyFree a = false := by
            cases h0 : m.isLazyFree a <;> simp_all
          split at hc
          · cases hc; exact ⟨rfl, by assumption, hlf⟩
          · split at hc
            · cases hc; exact ⟨rfl, by assumption, hlf⟩
            · cases hc
    · rcases hm.2.1 with ⟨b, hb⟩
      refine ⟨b, fun γ hγ k => ?_⟩
      have ⟨ha, hf⟩ := hb γ hγ k
      exact ⟨by dsimp [Heap.union, frameHeap]; rw [ha], by dsimp [Heap.union, frameHeap]; rw [hf]⟩
    · simp only [Heap.union, frameHeap, Bool.or_false] at hma
      exact hm.2.2 a hma

/-- If the final memory `mf` satisfies `Q` framed by `frameOf fp m`, then every readable
    (`isLazyFree = false`) byte of `m` outside `fp` has the same value in `mf`. -/
theorem frame_preserved {Q : SepProp} {fp : BitVec 64 → Prop} [DecidablePred fp] {m mf : Memory}
    (h : mf ⊨ Q ∗ frameOf fp m) :
    ∀ a, ¬ fp a → (m.perm a).r = true → m.isLazyFree a = false → mf.read8 a = m.read8 a := by
  obtain ⟨_, hqr, hm⟩ := SepProp.satisfies_iff.1 h
  rcases SepProp.holds_sepConj_iff.1 hqr with ⟨hq, hr, hd, rfl, _, hfr⟩
  rw [frameOf_holds] at hfr
  subst hfr
  have hfm := Heap.Matches.of_union_right hd hm
  intro a hfa hra hlf
  by_cases hrw : m.perm a = some Perm.rw
  · exact (hfm.1 a (.rw (m.read8 a)) (by simp [frameHeap, hfa, hlf, hrw])).1
  · exact (hfm.1 a (.ro (m.read8 a)) (by simp [frameHeap, hfa, hlf, hrw, hra])).1

/-! ## Footprints of points-to assertions -/

theorem supp_pointsTo8 (a : BitVec 64) (v : BitVec 8) : SupportedIn (a ↦₈ v) (· = a) := by
  intro h hh; obtain rfl := holds_pointsTo8_iff.1 hh
  exact ⟨fun x hx => by simp [Heap.singleton, hx], rfl, rfl, rfl⟩

theorem supp_emp (fp : BitVec 64 → Prop) : SupportedIn emp fp := by
  intro h hh; obtain rfl := SepProp.holds_emp_iff.1 hh
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem supp_sepConj {P Q : SepProp} {fp fq : BitVec 64 → Prop}
    (hp : SupportedIn P fp) (hq : SupportedIn Q fq) :
    SupportedIn (P ∗ Q) (fun x => fp x ∨ fq x) := by
  intro _ hh; obtain ⟨h₁, h₂, _, rfl, hP, hQ⟩ := SepProp.holds_sepConj_iff.1 hh
  obtain ⟨hp1, ha1, hf1, hm1⟩ := hp h₁ hP
  obtain ⟨hq1, ha2, hf2, hm2⟩ := hq h₂ hQ
  refine ⟨fun x hx => ?_, ?_, ?_, ?_⟩
  · simp only [not_or] at hx
    have h1x : h₁.phys x = none := hp1 x hx.1
    have h2x : h₂.phys x = none := hq1 x hx.2
    simp [Heap.union, h1x, h2x]
  · funext γ k; simp [Heap.union, ha1, ha2]
  · funext γ k; simp [Heap.union, hf1, hf2]
  · funext x; simp [Heap.union, hm1, hm2]

theorem supp_mono {P : SepProp} {fp fq : BitVec 64 → Prop}
    (hp : SupportedIn P fp) (himp : ∀ x, fp x → fq x) : SupportedIn P fq :=
  fun h hP => ⟨fun x hx => (hp h hP).1 x (fun h' => hx (himp x h')), (hp h hP).2⟩

theorem supp_pure_sepConj {φ : Prop} {P : SepProp} {fp : BitVec 64 → Prop}
    (hp : SupportedIn P fp) : SupportedIn (⌜φ⌝ ∗ P) fp := by
  rw [pure_sepConj]
  exact fun h hh => hp h hh.2

theorem supp_pointsToBytes (a : BitVec 64) (bs : List (BitVec 8)) :
    SupportedIn (a ↦ₛ bs) (InRegion a bs.length) := by
  induction bs generalizing a with
  | nil => rw [pointsToBytes_nil_def]; exact supp_emp _
  | cons b bs ih =>
    rw [pointsToBytes_cons_def]
    refine supp_mono (supp_sepConj (supp_pointsTo8 a b) (ih (a + 1#64))) ?_
    rintro x (rfl | hx)
    · simp [InRegion]
    · simp only [InRegion, List.length_cons] at hx ⊢
      bv_omega

/-! ## Building and reading byte heaps -/

theorem Memory.readBytes_length (m : Memory) (a : BitVec 64) (n : Nat) :
    (m.readBytes a n).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [Memory.readBytes, ih]

/-- If `[a, a + n)` is writable and non-`MADV_FREE` (`isLazyFree = false`) in `m`, then
    `a ↦ₛ m.readBytes a n` holds of a heap that matches `m`. (We need `n < 2^64` so the region does
    not wrap onto itself.) -/
theorem bytes_heap (m : Memory) (a : BitVec 64) (n : Nat) (hn : n < 2 ^ 64)
    (hrw : ∀ x, InRegion a n x → m.perm x = some Perm.rw ∧ m.isLazyFree x = false) :
    ∃ h, (a ↦ₛ m.readBytes a n) h ∧ h.Matches m := by
  induction n generalizing a with
  | zero =>
    exact ⟨Heap.empty, by rw [Memory.readBytes, pointsToBytes_nil_def, SepProp.holds_emp_iff],
      Heap.Matches.empty m⟩
  | succ n ih =>
    obtain ⟨h', hP, hm⟩ := ih (a + 1#64) (by omega) (by
      intro x hx; apply hrw; simp only [InRegion] at hx ⊢; bv_omega)
    refine ⟨(Heap.singleton a (m.read8 a)).union h', ?_, ?_⟩
    · rw [Memory.readBytes, pointsToBytes_cons_def]
      refine SepProp.holds_sepConj_iff.2 ⟨_, h', ?_, rfl, holds_pointsTo8_iff.2 rfl, hP⟩
      · refine ⟨fun x => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl,
          fun _ _ _ _ h' => ?_, fun _ => Or.inl rfl⟩
        · by_cases hx : x = a
          · rw [hx]
            refine Or.inr (Or.inl ?_)
            have := (supp_pointsToBytes (a + 1#64) (m.readBytes (a + 1#64) n) h' hP).1 a
            rw [Memory.readBytes_length] at this
            apply this
            simp only [InRegion]; bv_omega
          · exact Or.inl (by simp [Heap.singleton, hx])
        · rcases h' with ⟨h1, _⟩ | ⟨_, h2⟩
          · cases h1
          · cases h2
    · refine Heap.Matches.union ?_ hm
      refine ⟨fun x c hc => ?_, ⟨0, fun _ _ _ => ⟨rfl, rfl⟩⟩, fun _ hma => by cases hma⟩
      simp only [Heap.singleton] at hc
      split at hc
      · rename_i hxa; subst hxa; cases hc
        exact ⟨rfl, (hrw x (by simp [InRegion])).1, (hrw x (by simp [InRegion])).2⟩
      · cases hc

theorem readBytes_of_sat {a : BitVec 64} {bs : List (BitVec 8)} {R : SepProp} {m : Memory}
    (h : m ⊨ (a ↦ₛ bs) ∗ R) : m.readBytes a bs.length = bs := by
  induction bs generalizing a R with
  | nil => rfl
  | cons b bs ih =>
    simp only [pointsToBytes_cons] at h
    rw [sepConj_assoc] at h
    have hb := (satisfies_pointsTo8 (Satisfies.of_sep_left h)).1
    have ht := ih (Satisfies.of_sep_right h)
    simp [hb, ht]

theorem pointsTo64_eq_bytes (a v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦ₛ [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8,
      v.extractLsb' 24 8, v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8,
      v.extractLsb' 56 8]) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, pointsTo64, sepConj_emp, BitVec.add_zero,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem readBytes8_eq (m : Memory) (a : BitVec 64) :
    m.readBytes a 8 = [(m.read64 a).extractLsb' 0 8, (m.read64 a).extractLsb' 8 8,
      (m.read64 a).extractLsb' 16 8, (m.read64 a).extractLsb' 24 8,
      (m.read64 a).extractLsb' 32 8, (m.read64 a).extractLsb' 40 8,
      (m.read64 a).extractLsb' 48 8, (m.read64 a).extractLsb' 56 8] := by
  simp only [Memory.readBytes, Memory.read64, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext i hi
    simp only [BitVec.getElem_extractLsb']
    rw [← BitVec.getLsbD_eq_getElem]
    simp only [BitVec.getLsbD_append]
    repeat' split
    all_goals first | (exfalso; omega) | rfl | (congr 1 <;> omega)

theorem sat_pure_sepConj {φ : Prop} {Q R : SepProp} {m : Memory}
    (h : m ⊨ (⌜φ⌝ ∗ Q) ∗ R) : φ ∧ (m ⊨ Q ∗ R) := by
  rw [sepConj_assoc, pure_sepConj] at h
  obtain ⟨hh, ⟨hφ, hQR⟩, hm⟩ := SepProp.satisfies_iff.1 h
  exact ⟨hφ, SepProp.satisfies_iff.2 ⟨hh, hQR, hm⟩⟩

theorem heap_pure_sepConj {φ : Prop} {P : SepProp} {m : Memory}
    (hφ : φ) (hP : ∃ h, P h ∧ h.Matches m) : ∃ h, (⌜φ⌝ ∗ P) h ∧ h.Matches m := by
  rw [pure_sepConj]
  obtain ⟨h, hh, hm⟩ := hP
  exact ⟨h, ⟨hφ, hh⟩, hm⟩

/-! ## Adequacy driver and example corollaries -/

/-- Instantiates `subroutine_ok` with the rest-of-the-world frame `R := frameOf fp s₀.mem` when
    panic, exit, and `.OutOfMemory` branches are uninhabited (`⌜False⌝`), yielding a normal return
    `s'` with `s'.mem ⊨ spec.post x s₀ s' ∗ R` and intermediate safety prior to `s'`. -/
theorem subroutine_ok_adequacy {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h_ok : subroutine_ok prog entry spec)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl)
    (x : α) (fp : BitVec 64 → Prop) [DecidablePred fp] (s₀ : State)
    (h_pc : s₀.pc = entry) (h_run : s₀.status = .Running) (h_sp : s₀.spAligned = true)
    (h_code : prog.CodeLoaded s₀.mem)
    (h_pre : ∃ h, spec.pre x s₀ h ∧ h.Matches s₀.mem)
    (h_supp : SupportedIn (spec.pre x s₀) fp) :
    ∃ s', Steps prog s₀ s' ∧
      s'.status = .Running ∧ s'.pc = s₀.readReg64 .x30 ∧
      (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
      s'.sp = s₀.sp ∧ CalleeSavedPreserved s₀ s' ∧
      (s'.mem ⊨ spec.post x s₀ s' ∗ frameOf fp s₀.mem) := by
  obtain ⟨s', hsteps, ⟨hpc, hsp, hst⟩, ⟨_, hcs⟩, hpost, hsafe⟩ :=
    subroutine_ok.no_fault_before_return h_ok x (frameOf fp s₀.mem) s₀
      h_pc h_run (sat_with_frame h_pre h_supp) h_sp h_code h_noPanic h_noExit h_noOom
  exact ⟨s', hsteps, hst, hpc, hsafe, hsp, hcs, hpost⟩

/-- The AAPCS64 callee-saved general-purpose registers `X19`-`X28` and the frame pointer `X29`. -/
def calleeSavedRegs : List Reg :=
  [.gpr 19#5, .gpr 20#5, .gpr 21#5, .gpr 22#5, .gpr 23#5, .gpr 24#5, .gpr 25#5, .gpr 26#5,
   .gpr 27#5, .gpr 28#5, .gpr 29#5]

theorem calleeSaved_of {s₀ s' : State} (h : CalleeSavedPreserved s₀ s') :
    ∀ r ∈ calleeSavedRegs, s'.readReg64 r = s₀.readReg64 r := by
  obtain ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, -⟩ := h
  intro r hr
  simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem spAligned_of {s : State} (h : s.readReg64 .sp &&& 0xF#64 = 0#64) : s.spAligned = true := by
  simp only [State.spAligned, State.readReg64] at h ⊢
  simp [h]

/-- Supporting adequacy lemma for a `c_spec` that reads `ctr ↦₆₄ old`, returns `old`, and writes
    `old + n`. -/
theorem pointsTo64_spec_adequacy {prog : Program} {entry : BitVec 64}
    {spec : Spec (BitVec 64 × BitVec 64 × BitVec 64)}
    (h_ok : subroutine_ok prog entry spec)
    (h_pre : ∀ ctr n old s0, spec.pre (ctr, n, old) s0 =
      (⌜s0.readReg64 .x0 = ctr ∧ s0.readReg64 .x1 = n⌝ ∗ ctr ↦₆₄ old) := by intros; rfl)
    (h_post : ∀ ctr n old s0 sf, spec.post (ctr, n, old) s0 sf =
      (⌜sf.readReg64 .x0 = old⌝ ∗ ctr ↦₆₄ (old + n)) := by intros; rfl)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    ∀ (s₀ : State) (ctr n : BitVec 64),
      s₀.status = .Running →
      s₀.pc = entry →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      s₀.readReg64 .x0 = ctr →
      s₀.readReg64 .x1 = n →
      (∀ a : BitVec 64, (a - ctr).toNat < 8 → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      ∃ s' : State,
        Steps prog s₀ s' ∧
        s'.status = .Running ∧
        s'.pc = s₀.readReg64 .x30 ∧
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
        s'.readReg64 .x0 = s₀.mem.read64 ctr ∧
        s'.mem.read64 ctr = s₀.mem.read64 ctr + n ∧
        (∀ a : BitVec 64, 8 ≤ (a - ctr).toNat → (s₀.mem.perm a).r = true → s₀.mem.isLazyFree a = false →
          s'.mem.read8 a = s₀.mem.read8 a) := by
  intro s₀ ctr n h_run h_pc h_sp h_code h_x0 h_x1 h_rw
  let old := s₀.mem.read64 ctr
  have hpre : ∃ h, (ctr ↦₆₄ old) h ∧ h.Matches s₀.mem := by
    rw [pointsTo64_eq_bytes, ← readBytes8_eq]
    exact bytes_heap _ _ 8 (by decide) h_rw
  have hsupp : SupportedIn (ctr ↦₆₄ old) (InRegion ctr 8) := by
    rw [pointsTo64_eq_bytes]; exact supp_pointsToBytes _ _
  have hpre' : ∃ h, spec.pre (ctr, n, old) s₀ h ∧ h.Matches s₀.mem := by
    rw [h_pre]; exact heap_pure_sepConj ⟨h_x0, h_x1⟩ hpre
  have hsupp' : SupportedIn (spec.pre (ctr, n, old) s₀) (InRegion ctr 8) := by
    rw [h_pre]; exact supp_pure_sepConj hsupp
  obtain ⟨s', hsteps, hst, hpc, hsafe, _, _, hpost⟩ :=
    subroutine_ok_adequacy h_ok h_noPanic h_noExit h_noOom (ctr, n, old)
      (InRegion ctr 8) s₀ h_pc h_run (spAligned_of h_sp) h_code hpre' hsupp'
  rw [h_post] at hpost
  obtain ⟨hret, hpost'⟩ := sat_pure_sepConj hpost
  refine ⟨s', hsteps, hst, hpc, hsafe, hret, (IsBlock.pointsTo64 ctr (old + n)).read hpost', ?_⟩
  intro a ha hr hlf
  exact frame_preserved hpost' a (by simp only [InRegion]; omega) hr hlf

/-- Supporting adequacy lemma for a `c_type_spec` that zeroes a mutable byte slice `buf ↦ₛ bs` and
    returns status code `0`. -/
theorem slice8_spec_adequacy {prog : Program} {entry : BitVec 64}
    {spec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8))}
    (h_ok : subroutine_ok prog entry spec)
    (h_pre : ∀ buf len bs s0, spec.pre (buf, len, bs) s0 =
      (⌜s0.readReg64 .x0 = buf ∧ s0.readReg64 .x1 = len ∧
          True ∧ len.toNat = bs.length⌝ ∗ (buf ↦ₛ bs)) := by intros; rfl)
    (h_post : ∀ buf len bs s0 sf, spec.post (buf, len, bs) s0 sf =
      (⌜True ∧ sf.readReg64 .x0 ∈ [0#64]⌝ ∗
        (buf ↦ₛ List.replicate bs.length 0#8)) := by intros; rfl)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    ∀ (s₀ : State) (buf len : BitVec 64),
      s₀.status = .Running →
      s₀.pc = entry →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      s₀.readReg64 .x0 = buf →
      s₀.readReg64 .x1 = len →
      (∀ a : BitVec 64, (a - buf).toNat < len.toNat → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      ∃ s' : State,
        Steps prog s₀ s' ∧
        s'.status = .Running ∧
        s'.pc = s₀.readReg64 .x30 ∧
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
        s'.readReg64 .x0 = 0#64 ∧
        s'.mem.readBytes buf len.toNat = List.replicate len.toNat 0#8 ∧
        (∀ a : BitVec 64, len.toNat ≤ (a - buf).toNat → (s₀.mem.perm a).r = true → s₀.mem.isLazyFree a = false →
          s'.mem.read8 a = s₀.mem.read8 a) := by
  intro s₀ buf len h_run h_pc h_sp h_code h_x0 h_x1 h_rw
  let bs := s₀.mem.readBytes buf len.toNat
  have hlen : bs.length = len.toNat := Memory.readBytes_length _ _ _
  have hpre : ∃ h, (buf ↦ₛ bs) h ∧ h.Matches s₀.mem :=
    bytes_heap _ _ _ len.isLt h_rw
  have hsupp : SupportedIn (buf ↦ₛ bs) (InRegion buf len.toNat) := by
    have := supp_pointsToBytes buf bs; rwa [hlen] at this
  have hpre' : ∃ h, spec.pre (buf, len, bs) s₀ h ∧ h.Matches s₀.mem := by
    rw [h_pre]; exact heap_pure_sepConj ⟨h_x0, h_x1, trivial, hlen.symm⟩ hpre
  have hsupp' : SupportedIn (spec.pre (buf, len, bs) s₀) (InRegion buf len.toNat) := by
    rw [h_pre]; exact supp_pure_sepConj hsupp
  obtain ⟨s', hsteps, hst, hpc, hsafe, _, _, hpost⟩ :=
    subroutine_ok_adequacy h_ok h_noPanic h_noExit h_noOom (buf, len, bs)
      (InRegion buf len.toNat) s₀ h_pc h_run (spAligned_of h_sp) h_code hpre' hsupp'
  rw [h_post] at hpost
  obtain ⟨⟨_, hret⟩, hpost'⟩ := sat_pure_sepConj hpost
  have hbytes := readBytes_of_sat (a := buf) (bs := List.replicate bs.length 0#8) hpost'
  rw [List.length_replicate, hlen] at hbytes
  refine ⟨s', hsteps, hst, hpc, hsafe, by simpa using hret, hbytes, ?_⟩
  intro a ha hr hlf
  exact frame_preserved hpost' a (by simp only [InRegion]; omega) hr hlf

theorem heap_sepConj {P Q : SepProp} {fp fq : BitVec 64 → Prop} {m : Memory}
    (hp : SupportedIn P fp) (hq : SupportedIn Q fq)
    (hdisj : ∀ x, fp x → ¬ fq x)
    (hP : ∃ h, P h ∧ h.Matches m) (hQ : ∃ h, Q h ∧ h.Matches m) :
    ∃ h, (P ∗ Q) h ∧ h.Matches m := by
  obtain ⟨h₁, hPh₁, hm₁⟩ := hP
  obtain ⟨h₂, hQh₂, hm₂⟩ := hQ
  obtain ⟨hp1, ha1, hf1, hm1⟩ := hp h₁ hPh₁
  obtain ⟨hq1, ha2, hf2, _⟩ := hq h₂ hQh₂
  have hd : h₁.Disjoint h₂ := by
    refine ⟨fun x => ?_, fun γ k => ?_, fun γ k => ?_, fun γ k oa v h' => ?_, fun x => ?_⟩
    · by_cases hfx : fp x
      · exact Or.inr (Or.inl (hq1 x (hdisj x hfx)))
      · exact Or.inl (hp1 x hfx)
    · rw [ha1]; exact Or.inl rfl
    · rw [hf1]; exact Or.inl rfl
    · rcases h' with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact nomatch (congrFun (congrFun ha1 γ) k).symm.trans h1
      · exact nomatch (congrFun (congrFun ha2 γ) k).symm.trans h1
    · exact Or.inl (congrFun hm1 x)
  exact ⟨h₁.union h₂, SepProp.holds_sepConj_iff.2 ⟨h₁, h₂, hd, rfl, hPh₁, hQh₂⟩,
    Heap.Matches.union hm₁ hm₂⟩

/-- Supporting adequacy lemma for `rustSliceIndexSpec` (`slice_index(ptr, idx)`): reads
    `(ptr + (idx <<< 3)) ↦₆₄ elem`, preserves it, and returns `elem` in `X0`. -/
theorem sliceIndex_spec_adequacy {prog : Program} {entry : BitVec 64}
    {spec : Spec (BitVec 64 × BitVec 64 × BitVec 64)}
    (h_ok : subroutine_ok prog entry spec)
    (h_pre : ∀ ptr idx elem s0, spec.pre (ptr, idx, elem) s0 =
      (⌜s0.readReg64 .x0 = ptr ∧ s0.readReg64 .x1 = idx⌝ ∗
        (ptr + (idx <<< 3)) ↦₆₄ elem) := by intros; rfl)
    (h_post : ∀ ptr idx elem s0 sf, spec.post (ptr, idx, elem) s0 sf =
      (⌜sf.readReg64 .x0 = elem⌝ ∗ (ptr + (idx <<< 3)) ↦₆₄ elem) := by intros; rfl)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    ∀ (s₀ : State) (ptr idx : BitVec 64),
      s₀.status = .Running →
      s₀.pc = entry →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      s₀.readReg64 .x0 = ptr →
      s₀.readReg64 .x1 = idx →
      (∀ a : BitVec 64, (a - (ptr + (idx <<< 3))).toNat < 8 → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      ∃ s' : State,
        Steps prog s₀ s' ∧
        s'.status = .Running ∧
        s'.pc = s₀.readReg64 .x30 ∧
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
        s'.readReg64 .x0 = s₀.mem.read64 (ptr + (idx <<< 3)) ∧
        s'.mem.read64 (ptr + (idx <<< 3)) = s₀.mem.read64 (ptr + (idx <<< 3)) ∧
        (∀ a : BitVec 64, 8 ≤ (a - (ptr + (idx <<< 3))).toNat → (s₀.mem.perm a).r = true → s₀.mem.isLazyFree a = false →
          s'.mem.read8 a = s₀.mem.read8 a) := by
  intro s₀ ptr idx h_run h_pc h_sp h_code h_x0 h_x1 h_rw
  let addr := ptr + (idx <<< 3)
  let elem := s₀.mem.read64 addr
  have hpre : ∃ h, (addr ↦₆₄ elem) h ∧ h.Matches s₀.mem := by
    rw [pointsTo64_eq_bytes, ← readBytes8_eq]
    exact bytes_heap _ _ 8 (by decide) h_rw
  have hsupp : SupportedIn (addr ↦₆₄ elem) (InRegion addr 8) := by
    rw [pointsTo64_eq_bytes]; exact supp_pointsToBytes _ _
  have hpre' : ∃ h, spec.pre (ptr, idx, elem) s₀ h ∧ h.Matches s₀.mem := by
    rw [h_pre]; exact heap_pure_sepConj ⟨h_x0, h_x1⟩ hpre
  have hsupp' : SupportedIn (spec.pre (ptr, idx, elem) s₀) (InRegion addr 8) := by
    rw [h_pre]; exact supp_pure_sepConj hsupp
  obtain ⟨s', hsteps, hst, hpc, hsafe, _, _, hpost⟩ :=
    subroutine_ok_adequacy h_ok h_noPanic h_noExit h_noOom (ptr, idx, elem)
      (InRegion addr 8) s₀ h_pc h_run (spAligned_of h_sp) h_code hpre' hsupp'
  rw [h_post] at hpost
  obtain ⟨hret, hpost'⟩ := sat_pure_sepConj hpost
  refine ⟨s', hsteps, hst, hpc, hsafe, hret, (IsBlock.pointsTo64 addr elem).read hpost', ?_⟩
  intro a ha hr hlf
  exact frame_preserved hpost' a (by dsimp [addr]; simp only [InRegion]; omega) hr hlf

/-- Supporting adequacy lemma for `rustMemSwapSpec` / `cSwapU64Spec` (`mem_swap(ptrA, ptrB)`):
    requires disjoint 8-byte writable regions `(ptrA ↦₆₄ valA) ∗ (ptrB ↦₆₄ valB)`, swaps their
    64-bit values in memory, and leaves all other readable bytes unchanged. -/
theorem memSwap_spec_adequacy {prog : Program} {entry : BitVec 64}
    {spec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)}
    (h_ok : subroutine_ok prog entry spec)
    (h_pre : ∀ ptrA ptrB valA valB s0, spec.pre (ptrA, ptrB, valA, valB) s0 =
      (⌜s0.readReg64 .x0 = ptrA ∧ s0.readReg64 .x1 = ptrB⌝ ∗
        ((ptrA ↦₆₄ valA) ∗ (ptrB ↦₆₄ valB))) := by intros; rfl)
    (h_post : ∀ ptrA ptrB valA valB s0 sf, spec.post (ptrA, ptrB, valA, valB) s0 sf =
      ((ptrA ↦₆₄ valB) ∗ (ptrB ↦₆₄ valA)) := by intros; rfl)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    ∀ (s₀ : State) (ptrA ptrB : BitVec 64),
      s₀.status = .Running →
      s₀.pc = entry →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      s₀.readReg64 .x0 = ptrA →
      s₀.readReg64 .x1 = ptrB →
      (∀ a : BitVec 64, (a - ptrA).toNat < 8 → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      (∀ a : BitVec 64, (a - ptrB).toNat < 8 → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      (∀ a : BitVec 64, (a - ptrA).toNat < 8 → 8 ≤ (a - ptrB).toNat) →
      ∃ s' : State,
        Steps prog s₀ s' ∧
        s'.status = .Running ∧
        s'.pc = s₀.readReg64 .x30 ∧
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
        s'.mem.read64 ptrA = s₀.mem.read64 ptrB ∧
        s'.mem.read64 ptrB = s₀.mem.read64 ptrA ∧
        (∀ a : BitVec 64, 8 ≤ (a - ptrA).toNat → 8 ≤ (a - ptrB).toNat →
          (s₀.mem.perm a).r = true → s₀.mem.isLazyFree a = false → s'.mem.read8 a = s₀.mem.read8 a) := by
  intro s₀ ptrA ptrB h_run h_pc h_sp h_code h_x0 h_x1 h_rwA h_rwB h_disj
  let valA := s₀.mem.read64 ptrA
  let valB := s₀.mem.read64 ptrB
  have hpreA : ∃ h, (ptrA ↦₆₄ valA) h ∧ h.Matches s₀.mem := by
    rw [pointsTo64_eq_bytes, ← readBytes8_eq]
    exact bytes_heap _ _ 8 (by decide) h_rwA
  have hpreB : ∃ h, (ptrB ↦₆₄ valB) h ∧ h.Matches s₀.mem := by
    rw [pointsTo64_eq_bytes, ← readBytes8_eq]
    exact bytes_heap _ _ 8 (by decide) h_rwB
  have hsuppA : SupportedIn (ptrA ↦₆₄ valA) (InRegion ptrA 8) := by
    rw [pointsTo64_eq_bytes]; exact supp_pointsToBytes _ _
  have hsuppB : SupportedIn (ptrB ↦₆₄ valB) (InRegion ptrB 8) := by
    rw [pointsTo64_eq_bytes]; exact supp_pointsToBytes _ _
  have hdisj' : ∀ x, InRegion ptrA 8 x → ¬ InRegion ptrB 8 x := by
    intro x hxA hxB
    have := h_disj x hxA
    simp only [InRegion] at hxB
    omega
  have hpreAB := heap_sepConj hsuppA hsuppB hdisj' hpreA hpreB
  have hsuppAB := supp_sepConj hsuppA hsuppB
  have hpre' : ∃ h, spec.pre (ptrA, ptrB, valA, valB) s₀ h ∧ h.Matches s₀.mem := by
    rw [h_pre]; exact heap_pure_sepConj ⟨h_x0, h_x1⟩ hpreAB
  have hsupp' : SupportedIn (spec.pre (ptrA, ptrB, valA, valB) s₀)
      (fun x => InRegion ptrA 8 x ∨ InRegion ptrB 8 x) := by
    rw [h_pre]; exact supp_pure_sepConj hsuppAB
  obtain ⟨s', hsteps, hst, hpc, hsafe, _, _, hpost'⟩ :=
    subroutine_ok_adequacy h_ok h_noPanic h_noExit h_noOom (ptrA, ptrB, valA, valB)
      (fun x => InRegion ptrA 8 x ∨ InRegion ptrB 8 x)
      s₀ h_pc h_run (spAligned_of h_sp) h_code hpre' hsupp'
  rw [h_post] at hpost'
  have hpostA : s'.mem ⊨ (ptrA ↦₆₄ valB) ∗ ((ptrB ↦₆₄ valA) ∗
      frameOf (fun x => InRegion ptrA 8 x ∨ InRegion ptrB 8 x) s₀.mem) := by
    rwa [sepConj_assoc] at hpost'
  have hpostB : s'.mem ⊨ (ptrB ↦₆₄ valA) ∗ ((ptrA ↦₆₄ valB) ∗
      frameOf (fun x => InRegion ptrA 8 x ∨ InRegion ptrB 8 x) s₀.mem) := by
    rw [sepConj_comm (ptrA ↦₆₄ valB), sepConj_assoc] at hpost'
    exact hpost'
  refine ⟨s', hsteps, hst, hpc, hsafe,
    (IsBlock.pointsTo64 ptrA valB).read hpostA,
    (IsBlock.pointsTo64 ptrB valA).read hpostB, ?_⟩
  intro a haA haB hr hlf
  exact frame_preserved hpost' a (by simp only [InRegion, not_or]; omega) hr hlf

/-- Supporting adequacy lemma for `memsetSpec` (`memset(dst, c, n)`):
    fills `memRegion dst n.toNat` with `n.toNat` copies of `c.setWidth 8` and returns `dst` in `X0`. -/
theorem memset_spec_adequacy {prog : Program} {entry : BitVec 64}
    {spec : Spec (BitVec 64 × BitVec 32 × BitVec 64)}
    (h_ok : subroutine_ok prog entry spec)
    (h_pre : ∀ dst c n s0, spec.pre (dst, c, n) s0 =
      (⌜s0.readReg64 .x0 = dst ∧ (s0.readReg64 .x1).truncate 32 = c ∧
          s0.readReg64 .x2 = n ∧ True ∧ True⌝ ∗
        memRegion dst n.toNat) := by intros; rfl)
    (h_post : ∀ dst c n s0 sf, spec.post (dst, c, n) s0 sf =
      (⌜True ∧ sf.readReg64 .x0 = dst⌝ ∗
        (dst ↦ₛ List.replicate n.toNat (c.setWidth 8))) := by intros; rfl)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    ∀ (s₀ : State) (dst : BitVec 64) (c : BitVec 32) (n : BitVec 64),
      s₀.status = .Running →
      s₀.pc = entry →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      s₀.readReg64 .x0 = dst →
      (s₀.readReg64 .x1).truncate 32 = c →
      s₀.readReg64 .x2 = n →
      (∀ a : BitVec 64, (a - dst).toNat < n.toNat → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      ∃ s' : State,
        Steps prog s₀ s' ∧
        s'.status = .Running ∧
        s'.pc = s₀.readReg64 .x30 ∧
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
        s'.readReg64 .x0 = dst ∧
        s'.mem.readBytes dst n.toNat = List.replicate n.toNat (c.setWidth 8) ∧
        (∀ a : BitVec 64, n.toNat ≤ (a - dst).toNat → (s₀.mem.perm a).r = true → s₀.mem.isLazyFree a = false →
          s'.mem.read8 a = s₀.mem.read8 a) := by
  intro s₀ dst c n h_run h_pc h_sp h_code h_x0 h_x1 h_x2 h_rw
  have hn64 : n.toNat ≤ 2 ^ 64 := by have := n.isLt; omega
  let bs := s₀.mem.readBytes dst n.toNat
  have hlen : bs.length = n.toNat := Memory.readBytes_length _ _ _
  have hbytes : ∃ h, (dst ↦ₛ bs) h ∧ h.Matches s₀.mem :=
    bytes_heap _ _ _ n.isLt h_rw
  have hpre : ∃ h, (memRegion dst n.toNat) h ∧ h.Matches s₀.mem := by
    rw [memRegion_eq_exists_bytes dst n.toNat hn64]
    obtain ⟨h, hh, hm⟩ := heap_pure_sepConj hlen hbytes
    exact ⟨h, SepProp.holds_sepExists_iff.2 ⟨bs, hh⟩, hm⟩
  have hsupp : SupportedIn (memRegion dst n.toNat) (InRegion dst n.toNat) := by
    rw [memRegion_eq_exists_bytes dst n.toNat hn64]
    intro h hh; obtain ⟨bs', hbs'⟩ := SepProp.holds_sepExists_iff.1 hh
    rw [pure_sepConj] at hbs'
    have hs := supp_pointsToBytes dst bs' h hbs'.2
    rwa [hbs'.1] at hs
  have hpre' : ∃ h, spec.pre (dst, c, n) s₀ h ∧ h.Matches s₀.mem := by
    rw [h_pre]; exact heap_pure_sepConj ⟨h_x0, h_x1, h_x2, trivial, trivial⟩ hpre
  have hsupp' : SupportedIn (spec.pre (dst, c, n) s₀) (InRegion dst n.toNat) := by
    rw [h_pre]; exact supp_pure_sepConj hsupp
  obtain ⟨s', hsteps, hst, hpc, hsafe, _, _, hpost⟩ :=
    subroutine_ok_adequacy h_ok h_noPanic h_noExit h_noOom (dst, c, n)
      (InRegion dst n.toNat) s₀ h_pc h_run (spAligned_of h_sp) h_code hpre' hsupp'
  rw [h_post] at hpost
  obtain ⟨⟨_, hret⟩, hpost'⟩ := sat_pure_sepConj hpost
  have hout := readBytes_of_sat (a := dst) (bs := List.replicate n.toNat (c.setWidth 8)) hpost'
  rw [List.length_replicate] at hout
  refine ⟨s', hsteps, hst, hpc, hsafe, hret, hout, ?_⟩
  intro a ha hr hlf
  exact frame_preserved hpost' a (by simp only [InRegion]; omega) hr hlf

/-- Supporting proof for `subroutineOk_unfold`: unpacks `prog.subroutineOk fnName spec` at symbol
    offset `off` (`prog.findSymbol? fnName = some off`) into raw operational steps, intermediate
    safety (`Steps.running_or_steps_of`), and the four explicit terminal cases of
    `SubroutineOutcome`. -/
theorem subroutineOk_unfold_proof {α : Type} (prog : Program) (fnName : String) (off : Nat)
    (spec : Spec α) :
    prog.subroutineOk fnName spec →
    prog.findSymbol? fnName = some off →
    ∀ (x : α) (R : SepProp) (s₀ : State),
      s₀.pc = prog.base + BitVec.ofNat 64 off →
      s₀.status = .Running →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      (s₀.mem ⊨ spec.pre x s₀ ∗ R) →
      ∃ sf : State,
        Steps prog s₀ sf ∧
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog sf t) ∧
        ((sf.status = .Running ∧
          sf.pc = s₀.readReg64 .x30 ∧
          sf.sp = s₀.sp ∧
          CalleeSavedPreserved s₀ sf ∧
          (sf.mem ⊨ spec.post x s₀ sf ∗ R)) ∨
         (sf.status = .Panicked ∧ (sf.mem ⊨ spec.onPanic x s₀ sf ∗ R)) ∨
         (∃ code, sf.status = .Exited code ∧ (sf.mem ⊨ spec.onExit x code s₀ sf ∗ R)) ∨
         (sf.status = .OutOfMemory ∧ (sf.mem ⊨ spec.onOom x s₀ sf ∗ R))) := by
  intro hok hsym x R s₀ hpc hrun hsp hcode hpre
  have hentry : s₀.pc = prog.fnAddr fnName := by
    simp [Program.fnAddr, Program.fnOff, hsym, hpc]
  obtain ⟨sf, hsteps, hout, hsafe⟩ :=
    subroutine_ok.no_fault_before_outcome hok x R s₀ hentry hrun hpre (spAligned_of hsp) hcode
  refine ⟨sf, hsteps, hsafe, ?_⟩
  rcases hout with ⟨⟨hpc', _, hrun'⟩, ⟨hsp', hcs⟩, hpost⟩ | hpanic | hexit | hoom
  · exact Or.inl ⟨hrun', hpc', hsp', hcs, hpost⟩
  · exact Or.inr (Or.inl hpanic)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

end Arm64.Testing.SpecAdequacyTour
