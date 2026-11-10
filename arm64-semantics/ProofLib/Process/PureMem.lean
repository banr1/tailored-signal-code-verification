/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Process.NonFs
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# Lowering Hook-Based Proofs and Permission Views to `Program.pureMem`

Lowers modular `subroutine_ok` and `Steps` proofs with extern/stub hooks or tightened permission
views to `Program.pureMem`. Provides trace conversion (`Steps.toPureMem_of_running`,
`Steps.toPureMem_of_not_running`, `pureMemStubHook_exec_of_subroutine_ok`, `stubExec_of_split`),
exact address-footprint and permission-monotonicity bridges (`CoversExact`,
`Arm64.SepProp.NoProtNone`, `Arm64.Satisfies.of_perm_mono`, `Arm64.Satisfies.frame_perm_view`), and
the reflective instruction-word loader `pureWordsProg`.
-/

@[expose] public section

namespace Arm64.Process

open ProofLib

/-- Convert a `Steps prog s sf` trace ending in `.Running` to `Steps Program.pureMem s sf`
    whenever every extern hook invoked along the trace is realized by a `Steps Program.pureMem`
    trace from the hook entry state. -/
theorem Steps.toPureMem_of_running {prog : Program} {s0 s sf : State}
    (h_hooks : ∀ (pc : BitVec 64) (f : State → State) (st : State),
      prog.externAt? pc = some f → st.pc = pc → st.status = .Running →
      s0.mem.KeepsFrozen st.mem → Steps Program.pureMem st (f st))
    (h_kf : s0.mem.KeepsFrozen s.mem)
    (h_steps : Steps prog s sf)
    (h_run : sf.status = .Running)
    (h_svc : prog.svc = Syscall.standard := by rfl) :
    Steps Program.pureMem s sf := by
  induction h_steps with
  | refl s => exact Steps.refl s
  | @step s1 s2 s3 h1 h2 ih =>
    have h_kf2 : s0.mem.KeepsFrozen s2.mem := h_kf.trans h1.keepsFrozen
    cases h1 with
    | @exec inst hr hf =>
      have hf' : Program.pureMem.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem at hf ⊢
        split at hf
        · contradiction
        · exact hf
      have hev : prog.evalInst inst s1 = Program.pureMem.evalInst inst s1 := by
        simp only [Program.evalInst, Program.pureMem, Program.pureWithSvc, Program.ofSvc, h_svc]
      have ih2 := ih h_kf2 h_run
      rw [hev] at ih2
      exact Steps.step (Step.exec hr hf') ih2
    | halt_unmapped _ _ _ =>
      have heq := Steps.from_not_running h2 (by simp)
      subst heq
      simp at h_run
    | extern hr he _ _ =>
      exact (h_hooks s1.pc _ s1 he rfl hr h_kf).trans (ih h_kf2 h_run)
    | extern_fault _ _ _ =>
      have heq := Steps.from_not_running h2 (by simp)
      subst heq
      simp at h_run

/-- Any `Steps prog s sf` trace ending in `.Running` for a program without extern/override hooks
    (such as `Program.ofWords base words`) is a `Steps Program.pureMem s sf` trace. -/
theorem Steps.toPureMem_of_no_extern {prog : Program} {s sf : State}
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (h_steps : Steps prog s sf)
    (h_run : sf.status = .Running)
    (h_svc : prog.svc = Syscall.standard := by rfl) :
    Steps Program.pureMem s sf :=
  Steps.toPureMem_of_running
    (fun pc _ _ he => by rw [h_no_ext pc] at he; contradiction)
    (Memory.KeepsFrozen.refl s.mem) h_steps h_run h_svc

/-- Lower `subroutine_ok prog entry spec` (for a non-panicking, non-exiting, non-OOM spec)
    to a `Steps Program.pureMem s0 sf` execution when `prog.CodeLoaded s0.mem` holds and
    every extern hook of `prog` is realized by `Steps Program.pureMem`. -/
theorem subroutine_ok_toPureMem {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h_sub : subroutine_ok prog entry spec)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl)
    {x : α} {R : SepProp} {s0 : State}
    (hpc : s0.pc = entry)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (hsp : s0.spAligned = true)
    (hcode : prog.CodeLoaded s0.mem)
    (h_hooks : ∀ (pc : BitVec 64) (f : State → State) (st : State),
      prog.externAt? pc = some f → st.pc = pc → st.status = .Running →
      s0.mem.KeepsFrozen st.mem → Steps Program.pureMem st (f st))
    (h_svc : prog.svc = Syscall.standard := by rfl) :
    ∃ sf : State,
      Steps Program.pureMem s0 sf ∧
      Returned s0 sf ∧
      CallingConventionPreserved s0 sf ∧
      (sf.mem ⊨ spec.post x s0 sf ∗ R) := by
  simp only [subroutine_ok_iff, reaches_outcome_iff] at h_sub
  obtain ⟨sf, h_steps, hout⟩ := h_sub x R s0 hpc hrun hpre hsp hcode
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, he⟩ | ⟨_, ho⟩
  · exact ⟨sf, Steps.toPureMem_of_running h_hooks (Memory.KeepsFrozen.refl _) h_steps hret.2.2 h_svc,
      hret, hcc, hpost⟩
  · rw [h_noPanic] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · rw [h_noExit] at he; exact False.elim (not_satisfies_false_sepConj he)
  · rw [h_noOom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

/-- Extern stub hook that executes `Program.pureMem` from `s0.setPC targetAddr` when a valid
    `SubroutineOutcome` state `sf` is reachable, and falls back to `fallback s0` otherwise. -/
noncomputable def pureMemStubHook {α : Type} (targetAddr : BitVec 64)
    (spec : Spec α) (fallback : State → State) (s0 : State) : State :=
  open Classical in
  let s1 := s0.setPC targetAddr
  if h : ∃ sf, Steps Program.pureMem s1 sf ∧ s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
      (∀ (x : α) (R : SepProp),
        s0.status = .Running → s0.spAligned = true → (s0.mem ⊨ spec.pre x s0 ∗ R) →
        SubroutineOutcome spec x R s0 sf) then
    Classical.choose h
  else
    fallback s0

/-- `pureMemStubHook targetAddr spec fallback` satisfies `HookOk` whenever `fallback` does. -/
theorem pureMemStubHook_ok {α : Type} (targetAddr : BitVec 64)
    (spec : Spec α) {fallback : State → State}
    (h_fb : HookOk fallback spec) :
    HookOk (pureMemStubHook targetAddr spec fallback) spec := by
  intro x R s0 hrun hpre hsp
  dsimp only [pureMemStubHook]
  split
  · rename_i h
    obtain ⟨_, hkf, hsym, hout⟩ := Classical.choose_spec h
    exact ⟨hkf, hsym, hout x R hrun hsp hpre⟩
  · exact h_fb x R s0 hrun hpre hsp

/-- `pureMemStubHook targetAddr spec fallback s0` is reachable from `s0` via `Steps Program.pureMem`
    whenever `s0` steps to `s0.setPC targetAddr` and the target execution witness exists. -/
theorem steps_pureMemStubHook {α : Type} {targetAddr : BitVec 64}
    {spec : Spec α} {fallback : State → State} {s0 : State}
    (h_branch : Steps Program.pureMem s0 (s0.setPC targetAddr))
    (h_exec : ∃ sf, Steps Program.pureMem (s0.setPC targetAddr) sf ∧
      s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
      (∀ (x : α) (R : SepProp),
        s0.status = .Running → s0.spAligned = true → (s0.mem ⊨ spec.pre x s0 ∗ R) →
        SubroutineOutcome spec x R s0 sf)) :
    Steps Program.pureMem s0 (pureMemStubHook targetAddr spec fallback s0) := by
  dsimp only [pureMemStubHook]
  split
  · rename_i h
    exact h_branch.trans (Classical.choose_spec h).1
  · rename_i h_not
    exact False.elim (h_not h_exec)

/-- Canonical rest-of-the-world heap outside footprint `fp` in memory `m`. -/
def frameHeap (fp : BitVec 64 → Prop) [DecidablePred fp] (m : Memory) : Heap :=
  { phys := fun a =>
      if fp a then none
      else if m.perm a = some Perm.rw then
        if m.isLazyFree a then some .lazy else some (.rw (m.read8 a))
      else if m.perm a = some Perm.protNone then
        if m.isLazyFree a then some .protNoneLazy else some (.protNone (m.read8 a))
      else if (m.perm a).r && !m.isLazyFree a then some (.ro (m.read8 a))
      else none
    mapped := fun a => (m.perm a).mapped && m.isAnon a }

/-- Canonical frame assertion `R := frameOf fp m` holding only on `frameHeap fp m`. -/
def frameOf (fp : BitVec 64 → Prop) [DecidablePred fp] (m : Memory) : SepProp :=
  ⟨fun h => h = frameHeap fp m⟩

/-- `P` owns the exact writable physical footprint `fp` with no ghost camera state or mapping tokens. -/
def CoversExact (P : SepProp) (fp : BitVec 64 → Prop) : Prop :=
  ∀ h : Heap, P.holds h →
    (∀ a, fp a → ∃ b, h.phys a = some (.rw b)) ∧
    (∀ a, ¬ fp a → h.phys a = none) ∧
    h.auth = (fun _ _ => none) ∧
    h.frag = (fun _ _ => none) ∧
    h.mapped = (fun _ => false)

namespace CoversExact

theorem iff {P : SepProp} {fp fq : BitVec 64 → Prop}
    (hP : CoversExact P fp) (heq : ∀ a, fp a ↔ fq a) :
    CoversExact P fq := by
  intro h hh
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP h hh
  exact ⟨fun a ha => h1 a ((heq a).mpr ha), fun a ha => h2 a (fun hfa => ha ((heq a).mp hfa)), h3, h4, h5⟩

theorem emp : CoversExact SepProp.emp (fun _ => False) := by
  intro h hh; rw [SepProp.holds_emp_iff] at hh; subst hh
  exact ⟨fun _ hf => False.elim hf, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem pointsTo8 (a : BitVec 64) (v : BitVec 8) :
    CoversExact (a ↦₈ v) (· = a) := by
  intro h hh; rw [holds_pointsTo8_iff] at hh; subst hh
  refine ⟨fun x hx => ?_, fun x hx => by simp [Heap.singleton, hx], rfl, rfl, rfl⟩
  subst hx
  exact ⟨v, by simp [Heap.singleton]⟩

theorem pure_sepConj {φ : Prop} {P : SepProp} {fp : BitVec 64 → Prop}
    (hP : CoversExact P fp) :
    CoversExact (⌜φ⌝ ∗ P) fp := by
  intro h hh
  obtain ⟨h₁, h₂, _, rfl, hp, hh₂⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨rfl, _⟩ := SepProp.holds_pure_iff.mp hp
  rw [empty_union_eq]
  exact hP h₂ hh₂

theorem sepConj {P Q : SepProp} {fp fq : BitVec 64 → Prop}
    (hP : CoversExact P fp) (hQ : CoversExact Q fq) :
    CoversExact (P ∗ Q) (fun a => fp a ∨ fq a) := by
  intro h hh
  obtain ⟨h₁, h₂, _, rfl, hh₁, hh₂⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hP h₁ hh₁
  obtain ⟨hq1, hq2, hq3, hq4, hq5⟩ := hQ h₂ hh₂
  refine ⟨fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
  · rcases ha with hfa | hqa
    · obtain ⟨b, hb⟩ := hp1 a hfa
      exact ⟨b, by simp [Heap.union, hb]⟩
    · by_cases hfa : fp a
      · obtain ⟨b, hb⟩ := hp1 a hfa
        exact ⟨b, by simp [Heap.union, hb]⟩
      · obtain ⟨b, hb⟩ := hq1 a hqa
        have hn1 := hp2 a hfa
        exact ⟨b, by simp [Heap.union, hn1, hb]⟩
  · have hn1 := hp2 a (fun h => ha (Or.inl h))
    have hn2 := hq2 a (fun h => ha (Or.inr h))
    simp [Heap.union, hn1, hn2]
  · funext γ k; simp [Heap.union, hp3, hq3]
  · funext γ k; simp [Heap.union, hp4, hq4]
  · funext a; simp [Heap.union, hp5, hq5]

theorem pointsToBytes (a : BitVec 64) (bs : List (BitVec 8)) (hlen : bs.length ≤ 2 ^ 64) :
    CoversExact (a ↦ₛ bs) (InRegion a bs.length) := by
  induction bs generalizing a with
  | nil =>
    rw [pointsToBytes_nil_def]
    refine (CoversExact.emp).iff fun x => ?_
    simp [InRegion]
  | cons b bs ih =>
    have hlen' : bs.length ≤ 2 ^ 64 := by simp at hlen; omega
    rw [pointsToBytes_cons_def]
    refine (CoversExact.sepConj (CoversExact.pointsTo8 a b) (ih (a + 1#64) hlen')).iff fun x => ?_
    simp only [InRegion, List.length_cons] at hlen ⊢
    constructor
    · rintro (rfl | hx)
      · simp
      · bv_omega
    · intro hx
      by_cases hxa : x = a
      · exact Or.inl hxa
      · right; bv_omega

theorem pointsToBytes_len {a : BitVec 64} {bs : List (BitVec 8)} {n : Nat}
    (h : bs.length = n) (hn : n ≤ 2 ^ 64) :
    CoversExact (a ↦ₛ bs) (InRegion a n) := by
  subst h
  exact pointsToBytes a bs hn

theorem exists_pointsToBytes (a : BitVec 64) (n : Nat) (hn : n ≤ 2 ^ 64) :
    CoversExact (∃∗ bs : List (BitVec 8), ⌜bs.length = n⌝ ∗ (a ↦ₛ bs)) (InRegion a n) := by
  intro h hh
  obtain ⟨bs, hb⟩ := SepProp.holds_sepExists_iff.mp hh
  obtain ⟨h₁, h₂, _, rfl, hp, hh₂⟩ := SepProp.holds_sepConj_iff.mp hb
  obtain ⟨rfl, hlen⟩ := SepProp.holds_pure_iff.mp hp
  rw [empty_union_eq]
  exact pointsToBytes_len hlen hn h₂ hh₂

end CoversExact

/-- If `m ⊨ P ∗ R₀` and `CoversExact P fp`, then `m ⊨ P ∗ frameOf fp m`. -/
theorem sat_with_frameOf {P R₀ : SepProp} {fp : BitVec 64 → Prop} [DecidablePred fp] {m : Memory}
    (hcov : CoversExact P fp)
    (hsat : m ⊨ P ∗ R₀) :
    m ⊨ P ∗ frameOf fp m := by
  obtain ⟨_, hh, hm, _, _⟩ := SepProp.satisfies_iff.mp hsat
  obtain ⟨h₁, h₂, hd, rfl, hP, _⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨_, hp2, hp3, hp4, hp5⟩ := hcov h₁ hP
  refine SepProp.satisfies_iff.mpr ⟨h₁.union (frameHeap fp m),
    SepProp.holds_sepConj_iff.mpr ⟨h₁, frameHeap fp m, ?_, rfl, hP, rfl⟩, ?_,
    ⟨0, fun _ _ _ => ⟨by simp [Heap.union, hp3, frameHeap], by simp [Heap.union, hp4, frameHeap]⟩⟩,
    ?_⟩
  · refine ⟨fun a => ?_, fun _ _ => Or.inr rfl, fun _ _ => Or.inr rfl, fun _ _ _ _ h => ?_,
      fun _ => Or.inl (by simp [hp5])⟩
    · by_cases hfa : fp a
      · exact Or.inr (Or.inl (by simp [frameHeap, hfa]))
      · exact Or.inl (hp2 a hfa)
    · rcases h with ⟨_, hf⟩ | ⟨ha, _⟩
      · simp [frameHeap] at hf
      · simp [frameHeap] at ha
  · intro a c hc
    simp only [Heap.union] at hc
    cases hh1 : h₁.phys a with
    | some c1 =>
      rw [hh1] at hc
      have hu : (h₁.union h₂).phys a = some c := by simp [Heap.union, hh1, hc]
      exact hm a c hu
    | none =>
      rw [hh1] at hc
      simp only [frameHeap] at hc
      split at hc
      · contradiction
      · split at hc
        · rename_i _ hrw
          split at hc
          · injection hc with hc; subst hc; exact hrw
          · rename_i hlf
            injection hc with hc; subst hc
            exact ⟨rfl, hrw, Bool.eq_false_iff.mpr hlf⟩
        · split at hc
          · rename_i _ _ hpn
            split at hc
            · injection hc with hc; subst hc; exact hpn
            · rename_i hlf
              injection hc with hc; subst hc
              exact ⟨rfl, hpn, Bool.eq_false_iff.mpr hlf⟩
          · split at hc
            · rename_i _ _ _ hro
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hro
              injection hc with hc; subst hc
              exact ⟨rfl, hro.1, hro.2⟩
            · contradiction
  · intro a ha
    simp only [Heap.union, hp5, frameHeap, Bool.false_or, Bool.and_eq_true] at ha
    exact ha

/-- Transfer `sf.mem ⊨ Q ∗ frameOf fp s0.mem` to any caller frame `R` satisfying `s0.mem ⊨ P ∗ R`
    when `P` and `Q` both have exact writable footprint `fp`. -/
theorem frameOf_transfer {P Q R : SepProp} {fp : BitVec 64 → Prop} [DecidablePred fp]
    {s0_mem sf_mem : Memory}
    (hcovP : CoversExact P fp)
    (hcovQ : CoversExact Q fp)
    (hpre : s0_mem ⊨ P ∗ R)
    (hpost : sf_mem ⊨ Q ∗ frameOf fp s0_mem) :
    sf_mem ⊨ Q ∗ R := by
  obtain ⟨_, hh0, hm0, hgv0, hmap0⟩ := SepProp.satisfies_iff.mp hpre
  obtain ⟨hP, hR, hdPR, rfl, hhP, hhR⟩ := SepProp.holds_sepConj_iff.mp hh0
  obtain ⟨_, hhf, hmf, _, hmapf⟩ := SepProp.satisfies_iff.mp hpost
  obtain ⟨hQ, hF, hdQF, rfl, hhQ, hhF⟩ := SepProp.holds_sepConj_iff.mp hhf
  change hF = frameHeap fp s0_mem at hhF
  subst hhF
  obtain ⟨hp1, _, hp3, hp4, hp5⟩ := hcovP hP hhP
  obtain ⟨_, hq2, hq3, hq4, hq5⟩ := hcovQ hQ hhQ
  have hR_out : ∀ a, fp a → hR.phys a = none := by
    intro a hfa
    obtain ⟨b, hb⟩ := hp1 a hfa
    rcases hdPR.1 a with h1 | h2 | ⟨_, h1, _⟩
    · rw [hb] at h1; contradiction
    · exact h2
    · rw [hb] at h1; cases h1
  have hdQR : hQ.Disjoint hR := by
    refine ⟨fun a => ?_, fun _ _ => Or.inl (by simp [hq3]), fun _ _ => Or.inl (by simp [hq4]),
      fun _ _ _ _ h => ?_, fun _ => Or.inl (by simp [hq5])⟩
    · by_cases hfa : fp a
      · exact Or.inr (Or.inl (hR_out a hfa))
      · exact Or.inl (hq2 a hfa)
    · rcases h with ⟨ha, _⟩ | ⟨_, hf⟩
      · simp [hq3] at ha
      · simp [hq4] at hf
  refine SepProp.satisfies_iff.mpr ⟨hQ.union hR, SepProp.holds_sepConj_iff.mpr ⟨hQ, hR, hdQR, rfl, hhQ, hhR⟩, ?_, ?_, ?_⟩
  · intro a c hc
    simp only [Heap.union] at hc
    cases hhQ_a : hQ.phys a with
    | some cQ =>
      rw [hhQ_a] at hc
      have hu : (hQ.union (frameHeap fp s0_mem)).phys a = some c := by
        simp [Heap.union, hhQ_a, hc]
      exact hmf a c hu
    | none =>
      rw [hhQ_a] at hc
      have h_not_fp : ¬ fp a := fun hfa => by
        rw [hR_out a hfa] at hc; contradiction
      have hu0 : (hP.union hR).phys a = some c := by
        have hP_none := (hcovP hP hhP).2.1 a h_not_fp
        simp [Heap.union, hP_none, hc]
      have hm0_a := hm0 a c hu0
      cases c with
      | rw b =>
        have hF_a : (frameHeap fp s0_mem).phys a = some (.rw (s0_mem.read8 a)) := by
          simp [frameHeap, h_not_fp, hm0_a.2.1, hm0_a.2.2]
        have huF : (hQ.union (frameHeap fp s0_mem)).phys a = some (.rw (s0_mem.read8 a)) := by
          simp [Heap.union, hhQ_a, hF_a]
        have hmf_a := hmf a (.rw (s0_mem.read8 a)) huF
        exact ⟨hmf_a.1.trans hm0_a.1, hmf_a.2⟩
      | protNone b =>
        have hF_a : (frameHeap fp s0_mem).phys a = some (.protNone (s0_mem.read8 a)) := by
          simp [frameHeap, h_not_fp, hm0_a.2.1, hm0_a.2.2]; decide
        have huF : (hQ.union (frameHeap fp s0_mem)).phys a = some (.protNone (s0_mem.read8 a)) := by
          simp [Heap.union, hhQ_a, hF_a]
        have hmf_a := hmf a (.protNone (s0_mem.read8 a)) huF
        exact ⟨hmf_a.1.trans hm0_a.1, hmf_a.2⟩
      | lazy =>
        by_cases hlf : s0_mem.isLazyFree a = true
        · have hF_a : (frameHeap fp s0_mem).phys a = some .lazy := by
            simp [frameHeap, h_not_fp, hm0_a, hlf]
          have huF : (hQ.union (frameHeap fp s0_mem)).phys a = some .lazy := by
            simp [Heap.union, hhQ_a, hF_a]
          exact hmf a .lazy huF
        · have hlf_f : s0_mem.isLazyFree a = false := Bool.eq_false_iff.mpr hlf
          have hF_a : (frameHeap fp s0_mem).phys a = some (.rw (s0_mem.read8 a)) := by
            simp [frameHeap, h_not_fp, hm0_a, hlf_f]
          have huF : (hQ.union (frameHeap fp s0_mem)).phys a = some (.rw (s0_mem.read8 a)) := by
            simp [Heap.union, hhQ_a, hF_a]
          exact (hmf a (.rw (s0_mem.read8 a)) huF).2.1
      | protNoneLazy =>
        by_cases hlf : s0_mem.isLazyFree a = true
        · have hF_a : (frameHeap fp s0_mem).phys a = some .protNoneLazy := by
            simp [frameHeap, h_not_fp, hm0_a, hlf]; decide
          have huF : (hQ.union (frameHeap fp s0_mem)).phys a = some .protNoneLazy := by
            simp [Heap.union, hhQ_a, hF_a]
          exact hmf a .protNoneLazy huF
        · have hlf_f : s0_mem.isLazyFree a = false := Bool.eq_false_iff.mpr hlf
          have hF_a : (frameHeap fp s0_mem).phys a = some (.protNone (s0_mem.read8 a)) := by
            simp [frameHeap, h_not_fp, hm0_a, hlf_f]; decide
          have huF : (hQ.union (frameHeap fp s0_mem)).phys a = some (.protNone (s0_mem.read8 a)) := by
            simp [Heap.union, hhQ_a, hF_a]
          exact (hmf a (.protNone (s0_mem.read8 a)) huF).2.1
      | ro b =>
        have h_not_pn : s0_mem.perm a ≠ some Perm.protNone := by
          intro hpn
          have hr := hm0_a.2.1
          rw [hpn] at hr
          revert hr; decide
        by_cases hrw : s0_mem.perm a = some Perm.rw
        · have hF_a : (frameHeap fp s0_mem).phys a = some (.rw (s0_mem.read8 a)) := by
            simp [frameHeap, h_not_fp, hrw, hm0_a.2.2]
          have huF : (hQ.union (frameHeap fp s0_mem)).phys a = some (.rw (s0_mem.read8 a)) := by
            simp [Heap.union, hhQ_a, hF_a]
          have hmf_a := hmf a (.rw (s0_mem.read8 a)) huF
          refine ⟨hmf_a.1.trans hm0_a.1, ?_, hmf_a.2.2⟩
          rw [hmf_a.2.1]; rfl
        · have hF_a : (frameHeap fp s0_mem).phys a = some (.ro (s0_mem.read8 a)) := by
            simp [frameHeap, h_not_fp, hrw, h_not_pn, hm0_a.2.1, hm0_a.2.2]
          have huF : (hQ.union (frameHeap fp s0_mem)).phys a = some (.ro (s0_mem.read8 a)) := by
            simp [Heap.union, hhQ_a, hF_a]
          have hmf_a := hmf a (.ro (s0_mem.read8 a)) huF
          exact ⟨hmf_a.1.trans hm0_a.1, hmf_a.2⟩
  · rcases hgv0 with ⟨b, hb⟩
    refine ⟨b, fun γ hγ k => ?_⟩
    have ⟨ha, hf⟩ := hb γ hγ k
    simp only [Heap.union, hp3, hp4] at ha hf
    simp [Heap.union, hq3, hq4, ha, hf]
  · intro a ha
    have hRa : hR.mapped a = true := by simpa [Heap.union, hq5] using ha
    have h0a : (s0_mem.perm a).mapped = true ∧ s0_mem.isAnon a = true :=
      hmap0 a (by simp [Heap.union, hRa])
    exact hmapf a (by simp [Heap.union, frameHeap, h0a.1, h0a.2])

end Arm64.Process

/-- A `SepProp` assertion contains no `PROT_NONE` (`.protNone` or `.protNoneLazy`) heap cells. -/
def Arm64.SepProp.NoProtNone (P : SepProp) : Prop :=
  ∀ h a, P.holds h → (∀ b, h.phys a ≠ some (.protNone b)) ∧ h.phys a ≠ some .protNoneLazy

section NoProtNoneLemmas

open Arm64

namespace Arm64.SepProp.NoProtNone

@[simp]
theorem emp : SepProp.NoProtNone SepProp.emp := by
  intro h a hp; rw [SepProp.holds_emp_iff] at hp; subst hp; simp [Heap.empty]

@[simp]
theorem pure (φ : Prop) : SepProp.NoProtNone ⌜φ⌝ := by
  intro h a hp; obtain ⟨rfl, _⟩ := SepProp.holds_pure_iff.mp hp; simp [Heap.empty]

@[simp]
theorem sepConj {P Q : SepProp} (hP : SepProp.NoProtNone P) (hQ : SepProp.NoProtNone Q) :
    SepProp.NoProtNone (P ∗ Q) := by
  intro h a hp
  obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := SepProp.holds_sepConj_iff.mp hp
  simp only [Heap.union]
  cases h1a : h1.phys a with
  | none => exact hQ h2 a hp2
  | some c =>
    refine ⟨fun b heq => ?_, fun heq => ?_⟩
    · injection heq with hc; subst hc; exact (hP h1 a hp1).1 b h1a
    · injection heq with hc; subst hc; exact (hP h1 a hp1).2 h1a

theorem sepExists {α : Sort _} {P : α → SepProp} (hP : ∀ x, SepProp.NoProtNone (P x)) :
    SepProp.NoProtNone (∃∗ x, P x) := by
  intro h a hp; obtain ⟨x, hx⟩ := SepProp.holds_sepExists_iff.mp hp; exact hP x h a hx

@[simp]
theorem sepExists_iff {α : Sort _} {P : α → SepProp} :
    SepProp.NoProtNone (∃∗ x, P x) ↔ ∀ x, SepProp.NoProtNone (P x) :=
  ⟨fun h x h_heap a hp => h h_heap a (SepProp.holds_sepExists_iff.mpr ⟨x, hp⟩), sepExists⟩

@[simp]
theorem ite {c : Prop} [Decidable c] {P Q : SepProp}
    (hP : SepProp.NoProtNone P) (hQ : SepProp.NoProtNone Q) :
    SepProp.NoProtNone (if c then P else Q) := by
  split <;> assumption

@[simp]
theorem dite {c : Prop} [Decidable c] {P : c → SepProp} {Q : ¬ c → SepProp}
    (hP : ∀ hc, SepProp.NoProtNone (P hc)) (hQ : ∀ hc, SepProp.NoProtNone (Q hc)) :
    SepProp.NoProtNone (if hc : c then P hc else Q hc) := by
  split
  · rename_i hc; exact hP hc
  · rename_i hc; exact hQ hc

@[simp]
theorem pointsTo8 (x : BitVec 64) (v : BitVec 8) : SepProp.NoProtNone (x ↦₈ v) := by
  intro h a hp; rw [holds_pointsTo8_iff] at hp; subst hp; simp [Heap.singleton]

@[simp]
theorem pointsTo8RO (x : BitVec 64) (v : BitVec 8) : SepProp.NoProtNone (x ↦₈ᵣ v) := by
  intro h a hp; rw [holds_pointsTo8RO_iff] at hp; subst hp; simp [Heap.singletonRO]

@[simp]
theorem pointsTo8Lazy (x : BitVec 64) : SepProp.NoProtNone (x ↦₈ₗ) := by
  intro h a hp; rw [holds_pointsTo8Lazy_iff] at hp; subst hp; simp [Heap.singletonLazy]

@[simp]
theorem not_pointsTo8ProtNone (x : BitVec 64) (v : BitVec 8) : ¬ SepProp.NoProtNone (x ↦₈ₙ v) := by
  intro hnp
  exact (hnp (Heap.singletonProtNone x v) x (holds_pointsTo8ProtNone_iff.mpr rfl)).1 v (by simp [Heap.singletonProtNone])

@[simp]
theorem pointsTo16 (x : BitVec 64) (v : BitVec 16) : SepProp.NoProtNone (x ↦₁₆ v) := by
  unfold Arm64.pointsTo16; exact sepConj (pointsTo8 _ _) (pointsTo8 _ _)

@[simp]
theorem pointsTo32 (x : BitVec 64) (v : BitVec 32) : SepProp.NoProtNone (x ↦₃₂ v) := by
  unfold Arm64.pointsTo32
  exact sepConj (pointsTo8 _ _) (sepConj (pointsTo8 _ _) (sepConj (pointsTo8 _ _) (pointsTo8 _ _)))

@[simp]
theorem pointsTo64 (x : BitVec 64) (v : BitVec 64) : SepProp.NoProtNone (x ↦₆₄ v) := by
  unfold Arm64.pointsTo64
  exact sepConj (pointsTo8 _ _) (sepConj (pointsTo8 _ _) (sepConj (pointsTo8 _ _)
    (sepConj (pointsTo8 _ _) (sepConj (pointsTo8 _ _) (sepConj (pointsTo8 _ _)
      (sepConj (pointsTo8 _ _) (pointsTo8 _ _)))))))

@[simp]
theorem pointsTo128 (x : BitVec 64) (v : BitVec 128) : SepProp.NoProtNone (x ↦₁₂₈ v) := by
  unfold Arm64.pointsTo128; exact sepConj (pointsTo64 _ _) (pointsTo64 _ _)

@[simp]
theorem pointsToBytes (x : BitVec 64) (bs : List (BitVec 8)) : SepProp.NoProtNone (x ↦ₛ bs) := by
  induction bs generalizing x with
  | nil => rw [pointsToBytes_nil_def]; exact emp
  | cons b bs ih => rw [pointsToBytes_cons_def]; exact sepConj (pointsTo8 _ _) (ih _)

@[simp]
theorem pointsToWords64 (x : BitVec 64) (ws : List (BitVec 64)) : SepProp.NoProtNone (x ↦₆₄* ws) := by
  induction ws generalizing x with
  | nil => exact emp
  | cons w ws ih => exact sepConj (pointsTo64 _ _) (ih _)

@[simp]
theorem pointsTo16RO (x : BitVec 64) (v : BitVec 16) : SepProp.NoProtNone (x ↦₁₆ᵣ v) := by
  unfold Arm64.pointsTo16RO; exact sepConj (pointsTo8RO _ _) (pointsTo8RO _ _)

@[simp]
theorem pointsTo32RO (x : BitVec 64) (v : BitVec 32) : SepProp.NoProtNone (x ↦₃₂ᵣ v) := by
  unfold Arm64.pointsTo32RO
  exact sepConj (pointsTo8RO _ _) (sepConj (pointsTo8RO _ _) (sepConj (pointsTo8RO _ _) (pointsTo8RO _ _)))

@[simp]
theorem pointsTo64RO (x : BitVec 64) (v : BitVec 64) : SepProp.NoProtNone (x ↦₆₄ᵣ v) := by
  unfold Arm64.pointsTo64RO
  exact sepConj (pointsTo8RO _ _) (sepConj (pointsTo8RO _ _) (sepConj (pointsTo8RO _ _)
    (sepConj (pointsTo8RO _ _) (sepConj (pointsTo8RO _ _) (sepConj (pointsTo8RO _ _)
      (sepConj (pointsTo8RO _ _) (pointsTo8RO _ _)))))))

@[simp]
theorem pointsTo128RO (x : BitVec 64) (v : BitVec 128) : SepProp.NoProtNone (x ↦₁₂₈ᵣ v) := by
  unfold Arm64.pointsTo128RO; exact sepConj (pointsTo64RO _ _) (pointsTo64RO _ _)

@[simp]
theorem pointsToBytesRO (x : BitVec 64) (bs : List (BitVec 8)) : SepProp.NoProtNone (x ↦ᵣ bs) := by
  induction bs generalizing x with
  | nil => rw [pointsToBytesRO_nil_def]; exact emp
  | cons b bs ih => rw [pointsToBytesRO_cons_def]; exact sepConj (pointsTo8RO _ _) (ih _)

@[simp]
theorem pointsTo16Lazy (x : BitVec 64) : SepProp.NoProtNone (x ↦₁₆ₗ) := by
  unfold Arm64.pointsTo16Lazy; exact sepConj (pointsTo8Lazy _) (pointsTo8Lazy _)

@[simp]
theorem pointsTo32Lazy (x : BitVec 64) : SepProp.NoProtNone (x ↦₃₂ₗ) := by
  unfold Arm64.pointsTo32Lazy
  exact sepConj (pointsTo8Lazy _) (sepConj (pointsTo8Lazy _) (sepConj (pointsTo8Lazy _) (pointsTo8Lazy _)))

@[simp]
theorem pointsTo64Lazy (x : BitVec 64) : SepProp.NoProtNone (x ↦₆₄ₗ) := by
  unfold Arm64.pointsTo64Lazy
  exact sepConj (pointsTo8Lazy _) (sepConj (pointsTo8Lazy _) (sepConj (pointsTo8Lazy _)
    (sepConj (pointsTo8Lazy _) (sepConj (pointsTo8Lazy _) (sepConj (pointsTo8Lazy _)
      (sepConj (pointsTo8Lazy _) (pointsTo8Lazy _)))))))

@[simp]
theorem pointsTo128Lazy (x : BitVec 64) : SepProp.NoProtNone (x ↦₁₂₈ₗ) := by
  unfold Arm64.pointsTo128Lazy; exact sepConj (pointsTo64Lazy _) (pointsTo64Lazy _)

@[simp]
theorem regionBlock (base : BitVec 64) (len : Nat) (m : Memory) :
    SepProp.NoProtNone (Arm64.regionBlock base len m) := by
  intro h a hp; rw [holds_regionBlock_iff] at hp; subst hp; simp [Arm64.regionHeap]

@[simp]
theorem regionBlockRO (base : BitVec 64) (len : Nat) (m : Memory) :
    SepProp.NoProtNone (Arm64.regionBlockRO base len m) := by
  intro h a hp; rw [holds_regionBlockRO_iff] at hp; subst hp; simp [Arm64.regionHeapRO]

@[simp]
theorem memRegion (base : BitVec 64) (len : Nat) : SepProp.NoProtNone (Arm64.memRegion base len) := by
  intro h a hp; obtain ⟨m, hm⟩ := holds_memRegion_iff.mp hp
  exact regionBlock base len m h a (holds_regionBlock_iff.mpr hm)

@[simp]
theorem memRegionLazy (base : BitVec 64) (len : Nat) : SepProp.NoProtNone (Arm64.memRegionLazy base len) := by
  intro h a hp; rw [holds_memRegionLazy_iff] at hp; subst hp; simp [Arm64.regionHeapLazy]

@[simp]
theorem memMapped (base : BitVec 64) (len : Nat) : SepProp.NoProtNone (Arm64.memMapped base len) := by
  intro h a hp; rw [holds_memMapped_iff] at hp; subst hp; refine ⟨fun _ => nofun, nofun⟩

end Arm64.SepProp.NoProtNone

/-- Forward permission monotonicity for `SepProp.Satisfies`: if `m'` has the same byte values as `m`
    and preserves `some Perm.rw`, `some Perm.protNone`, `.r = true`, `.mapped = true`,
    `isLazyFree = false`, and `isAnon = true` forward, then every `SepProp` satisfied by `m` is also
    satisfied by `m'`. -/
theorem Arm64.Satisfies.of_perm_mono {m m' : Memory} {P : SepProp}
    (hread : ∀ a, m'.read8 a = m.read8 a)
    (hrw : ∀ a, m.perm a = some Perm.rw → m'.perm a = some Perm.rw)
    (hpn : ∀ a, m.perm a = some Perm.protNone → m'.perm a = some Perm.protNone)
    (hr : ∀ a, (m.perm a).r = true → (m'.perm a).r = true)
    (hmap : ∀ a, (m.perm a).mapped = true → (m'.perm a).mapped = true)
    (hlf : ∀ a, m.isLazyFree a = false → m'.isLazyFree a = false)
    (hanon : ∀ a, m.isAnon a = true → m'.isAnon a = true)
    (hsat : m ⊨ P) :
    m' ⊨ P := by
  obtain ⟨h, hP, hm, hgv, hmmap⟩ := SepProp.satisfies_iff.mp hsat
  refine SepProp.satisfies_iff.mpr ⟨h, hP, ?_, hgv, fun a ha => ⟨hmap a (hmmap a ha).1, hanon a (hmmap a ha).2⟩⟩
  intro a c hc
  cases c with
  | rw b =>
    obtain ⟨hval, hperm, hnlf⟩ := hm a (.rw b) hc
    exact ⟨(hread a).trans hval, hrw a hperm, hlf a hnlf⟩
  | ro b =>
    obtain ⟨hval, hperm, hnlf⟩ := hm a (.ro b) hc
    exact ⟨(hread a).trans hval, hr a hperm, hlf a hnlf⟩
  | protNone b =>
    obtain ⟨hval, hperm, hnlf⟩ := hm a (.protNone b) hc
    exact ⟨(hread a).trans hval, hpn a hperm, hlf a hnlf⟩
  | lazy =>
    exact hrw a (hm a .lazy hc)
  | protNoneLazy =>
    exact hpn a (hm a .protNoneLazy hc)

/-- Exact-heap frame witness for transporting a separation-logic postcondition back from a
    modified memory view `mf'` (such as an execute-stripped view) to the underlying memory `mf`
    across a permission-preserving execution (`∀ a, mf.perm a = m0.perm a`), when the callee
    postcondition `Q` satisfies `SepProp.NoProtNone Q` and the caller frame `R` is unrestricted
    (and may own `PROT_NONE` cells, lazy-free cells, ghost state, or mapped tokens). -/
theorem Arm64.Satisfies.frame_perm_view {m0 : Memory} {P R : SepProp}
    (hpre : m0 ⊨ P ∗ R) :
    ∃ R_view : SepProp,
      (m0 ⊨ P ∗ R_view) ∧
      ∀ {Q : SepProp} {mf mf' : Memory},
        SepProp.NoProtNone Q →
        (∀ a, mf.perm a = m0.perm a) →
        (∀ a, mf'.read8 a = mf.read8 a) →
        (∀ a, mf'.perm a = some Perm.rw → mf.perm a = some Perm.rw) →
        (∀ a, (mf'.perm a).r = true → (mf.perm a).r = true) →
        (∀ a, (mf'.perm a).mapped = true → (mf.perm a).mapped = true) →
        (∀ a, mf'.isLazyFree a = false → mf.isLazyFree a = false) →
        (∀ a, mf'.isAnon a = true → mf.isAnon a = true) →
        (mf' ⊨ Q ∗ R_view) →
        (mf ⊨ Q ∗ R) := by
  obtain ⟨_, hh0, hm0, hgv0, hmap0⟩ := SepProp.satisfies_iff.mp hpre
  obtain ⟨hP, hR, hdPR, rfl, hhP, hhR⟩ := SepProp.holds_sepConj_iff.mp hh0
  refine ⟨⟨fun h => h = hR⟩, SepProp.satisfies_iff.mpr ⟨hP.union hR, SepProp.holds_sepConj_iff.mpr ⟨hP, hR, hdPR, rfl, hhP, rfl⟩, hm0, hgv0, hmap0⟩, ?_⟩
  intro Q mf mf' hnpQ hperm0 hread hrw hr hmap hlf hanon hpost'
  obtain ⟨_, hhq, hmf', hgvf', hmapf'⟩ := SepProp.satisfies_iff.mp hpost'
  obtain ⟨hQ, hR', hdQR, rfl, hhQ, hhR'⟩ := SepProp.holds_sepConj_iff.mp hhq
  change hR' = hR at hhR'
  subst hR'
  refine SepProp.satisfies_iff.mpr ⟨hQ.union hR, SepProp.holds_sepConj_iff.mpr ⟨hQ, hR, hdQR, rfl, hhQ, hhR⟩, ?_, hgvf',
    fun a ha => ⟨hmap a (hmapf' a ha).1, hanon a (hmapf' a ha).2⟩⟩
  intro a c hc
  cases c with
  | rw b =>
    obtain ⟨hval', hperm', hnlf'⟩ := hmf' a (.rw b) hc
    exact ⟨(hread a).symm.trans hval', hrw a hperm', hlf a hnlf'⟩
  | ro b =>
    obtain ⟨hval', hperm', hnlf'⟩ := hmf' a (.ro b) hc
    exact ⟨(hread a).symm.trans hval', hr a hperm', hlf a hnlf'⟩
  | lazy =>
    exact hrw a (hmf' a .lazy hc)
  | protNone b =>
    obtain ⟨hval', _, hnlf'⟩ := hmf' a (.protNone b) hc
    refine ⟨(hread a).symm.trans hval', ?_, hlf a hnlf'⟩
    simp only [Heap.union] at hc
    cases hhQa : hQ.phys a with
    | some cQ =>
      simp only [hhQa] at hc
      injection hc with hcQ
      subst hcQ
      exact False.elim ((hnpQ hQ a hhQ).1 b hhQa)
    | none =>
      simp only [hhQa] at hc
      have hhPa : hP.phys a = none := by
        rcases hdPR.1 a with h1 | h2 | ⟨_, _, h2⟩
        · exact h1
        · rw [hc] at h2; contradiction
        · rw [hc] at h2; cases h2
      have hu0 : (hP.union hR).phys a = some (.protNone b) := by
        simp [Heap.union, hhPa, hc]
      exact (hperm0 a).trans (hm0 a (.protNone b) hu0).2.1
  | protNoneLazy =>
    simp only [Heap.union] at hc
    cases hhQa : hQ.phys a with
    | some cQ =>
      simp only [hhQa] at hc
      injection hc with hcQ
      subst hcQ
      exact False.elim ((hnpQ hQ a hhQ).2 hhQa)
    | none =>
      simp only [hhQa] at hc
      have hhPa : hP.phys a = none := by
        rcases hdPR.1 a with h1 | h2 | ⟨_, _, h2⟩
        · exact h1
        · rw [hc] at h2; contradiction
        · rw [hc] at h2; cases h2
      have hu0 : (hP.union hR).phys a = some .protNoneLazy := by
        simp [Heap.union, hhPa, hc]
      exact (hperm0 a).trans (hm0 a .protNoneLazy hu0)

end NoProtNoneLemmas

namespace Arm64.Process

/-- Construct the execution witness required by `steps_pureMemStubHook` from
    `subroutine_ok (Program.ofWords targetAddr words) targetAddr spec` when the spec input `x`
    is uniquely determined by `s0` (`xOf s0`) and `spec.pre` / `spec.post` have exact footprint `fp s0`. -/
theorem pureMemStubHook_exec_of_subroutine_ok {α : Type}
    {targetAddr : BitVec 64} {words : List (BitVec 32)} {spec : Spec α}
    (xOf : State → α) (fp : State → BitVec 64 → Prop) [∀ s, DecidablePred (fp s)]
    (h_sub : subroutine_ok (Program.ofWords targetAddr words) targetAddr spec)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_x_unique : ∀ s0 x R, (s0.mem ⊨ spec.pre x s0 ∗ R) → x = xOf s0)
    (h_pre_pc : ∀ s0, spec.pre (xOf s0) (s0.setPC targetAddr) = spec.pre (xOf s0) s0)
    (h_post_pc : ∀ s0 sf, spec.post (xOf s0) (s0.setPC targetAddr) sf = spec.post (xOf s0) s0 sf)
    (h_cov_pre : ∀ s0, CoversExact (spec.pre (xOf s0) s0) (fp s0))
    (h_cov_post : ∀ s0 sf, CoversExact (spec.post (xOf s0) s0 sf) (fp s0))
    {s0 : State}
    (h_code : (Program.ofWords targetAddr words).CodeLoaded s0.mem) :
    ∃ sf, Steps Program.pureMem (s0.setPC targetAddr) sf ∧
      s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
      (∀ (x : α) (R : SepProp),
        s0.status = .Running → s0.spAligned = true → (s0.mem ⊨ spec.pre x s0 ∗ R) →
        SubroutineOutcome spec x R s0 sf) := by
  let s1 := s0.setPC targetAddr
  by_cases hex : ∃ R₀ : SepProp, s0.status = .Running ∧ s0.spAligned = true ∧
      (s0.mem ⊨ spec.pre (xOf s0) s0 ∗ R₀)
  · obtain ⟨R₀, hrun, hsp, hpre₀⟩ := hex
    have hpre_frame : s1.mem ⊨ spec.pre (xOf s0) s1 ∗ frameOf (fp s0) s0.mem := by
      change s0.mem ⊨ spec.pre (xOf s0) s1 ∗ frameOf (fp s0) s0.mem
      rw [h_pre_pc s0]
      exact sat_with_frameOf (h_cov_pre s0) hpre₀
    have h_no_ext : ∀ pc, (Program.ofWords targetAddr words).externAt? pc = none := by
      intro _; rfl
    obtain ⟨sf, h_steps, hret, hcc, hpost_frame⟩ :=
      @subroutine_ok_toPureMem _ _ _ _ h_sub h_noPanic h_noExit h_noOom
        (xOf s0) (frameOf (fp s0) s0.mem) s1 rfl hrun hpre_frame hsp h_code
        (fun pc _ _ he => by rw [h_no_ext pc] at he; contradiction) rfl
    rw [h_post_pc s0 sf] at hpost_frame
    refine ⟨sf, h_steps, h_steps.keepsFrozen, h_steps.symtab_eq, ?_⟩
    intro x R _ _ hpre_xR
    have hx : x = xOf s0 := h_x_unique s0 x R hpre_xR
    subst hx
    have hpost_R : sf.mem ⊨ spec.post (xOf s0) s0 sf ∗ R :=
      frameOf_transfer (h_cov_pre s0) (h_cov_post s0 sf) hpre_xR hpost_frame
    exact Or.inl ⟨hret, hcc, hpost_R⟩
  · refine ⟨s1, Steps.refl s1, Memory.KeepsFrozen.refl s0.mem, rfl, ?_⟩
    intro x R hrun hsp hpre_xR
    have hx : x = xOf s0 := h_x_unique s0 x R hpre_xR
    subst hx
    exact False.elim (hex ⟨R, hrun, hsp, hpre_xR⟩)

/-- `stubExec_of_subroutine_ok` without ghost uniqueness: every ghost precondition splits into the
    canonical one plus a frame `Rex`, and the canonical postcondition rejoins with it. -/
theorem stubExec_of_split {α : Type} {prog : Program} {targetAddr : BitVec 64}
    {spec : Spec α} (xOf : State → α) (fp : State → BitVec 64 → Prop) [∀ s, DecidablePred (fp s)]
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (h_sub : subroutine_ok prog targetAddr spec)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝)
    (h_split : ∀ s0 x R, (s0.mem ⊨ spec.pre x s0 ∗ R) → ∃ Rex : SepProp,
      (s0.mem ⊨ spec.pre (xOf s0) s0 ∗ (Rex ∗ R)) ∧
      ∀ sf (m : Memory), (m ⊨ spec.post (xOf s0) s0 sf ∗ (Rex ∗ R)) → m ⊨ spec.post x s0 sf ∗ R)
    (h_pre_pc : ∀ s0, spec.pre (xOf s0) (s0.setPC targetAddr) = spec.pre (xOf s0) s0)
    (h_post_pc : ∀ s0 sf, spec.post (xOf s0) (s0.setPC targetAddr) sf = spec.post (xOf s0) s0 sf)
    (h_cov_pre : ∀ s0 (R : SepProp), (s0.mem ⊨ spec.pre (xOf s0) s0 ∗ R) →
      CoversExact (spec.pre (xOf s0) s0) (fp s0))
    (h_cov_post : ∀ s0 sf (R : SepProp), (s0.mem ⊨ spec.pre (xOf s0) s0 ∗ R) →
      CoversExact (spec.post (xOf s0) s0 sf) (fp s0))
    {s0 : State} (h_code : prog.CodeLoaded s0.mem)
    (h_svc : prog.svc = Syscall.standard := by rfl) :
    ∃ sf, Steps Program.pureMem (s0.setPC targetAddr) sf ∧
      s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
      (∀ (x : α) (R : SepProp),
        s0.status = .Running → s0.spAligned = true → (s0.mem ⊨ spec.pre x s0 ∗ R) →
        SubroutineOutcome spec x R s0 sf) := by
  by_cases hex : ∃ R₀ : SepProp, s0.status = .Running ∧ s0.spAligned = true ∧
      (s0.mem ⊨ spec.pre (xOf s0) s0 ∗ R₀)
  · obtain ⟨R₀, hrun, hsp, hpre₀⟩ := hex
    have hcov := h_cov_pre s0 R₀ hpre₀
    have hpre_frame : (s0.setPC targetAddr).mem ⊨
        spec.pre (xOf s0) (s0.setPC targetAddr) ∗ frameOf (fp s0) s0.mem := by
      rw [h_pre_pc s0]; exact sat_with_frameOf hcov hpre₀
    obtain ⟨sf, h_steps, hret, hcc, hpost⟩ :=
      @subroutine_ok_toPureMem _ _ _ _ h_sub h_noPanic h_noExit h_noOom
        (xOf s0) (frameOf (fp s0) s0.mem) (s0.setPC targetAddr) rfl hrun hpre_frame hsp h_code
        (fun pc _ _ he => by rw [h_no_ext pc] at he; contradiction) h_svc
    rw [h_post_pc s0 sf] at hpost
    refine ⟨sf, h_steps, h_steps.keepsFrozen, h_steps.symtab_eq, fun x R _ _ hxR => ?_⟩
    obtain ⟨Rex, hsplit, hjoin⟩ := h_split s0 x R hxR
    exact Or.inl ⟨hret, hcc,
      hjoin sf _ (frameOf_transfer hcov (h_cov_post s0 sf R₀ hpre₀) hsplit hpost)⟩
  · refine ⟨_, Steps.refl _, Memory.KeepsFrozen.refl s0.mem, rfl, fun x R hrun hsp hxR => ?_⟩
    obtain ⟨Rex, hsplit, _⟩ := h_split s0 x R hxR
    exact False.elim (hex ⟨_, hrun, hsp, hsplit⟩)

/-- Construct a pure instruction-slice `Program` (`extern := fun _ => none`) at `base` from `words`
    for lowering `SepWP` / `reaches_pc` steps to `Program.pureMem`. -/
def pureWordsProg (base : BitVec 64) (words : List (BitVec 32)) : Program :=
  Program.ofWords base words

theorem pureWordsProg_hasWords {base : BitVec 64} {words : List (BitVec 32)}
    (hlen : 4 * words.length ≤ 2 ^ 64)
    (hread : ((List.range words.length).all fun i =>
      (pureWordsProg base words).readWordOff (4 * i) == words[i]?) = true) :
    (pureWordsProg base words).hasWords base words := by
  unfold Program.hasWords Program.hasWordsOff
  have hsub : (base - (pureWordsProg base words).base).toNat = 0 := by
    change (base - base).toNat = 0
    simp
  rw [hsub, Nat.zero_add]
  refine ⟨hlen, fun i hi => ?_, ⟨rfl, rfl⟩⟩
  have hmem : i ∈ List.range words.length := List.mem_range.mpr hi
  have hall := beq_iff_eq.mp (List.all_eq_true.mp hread i hmem)
  rw [Nat.zero_add, hall, List.getElem?_eq_getElem hi]


end Arm64.Process
