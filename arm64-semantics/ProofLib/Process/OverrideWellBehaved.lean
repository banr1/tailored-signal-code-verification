/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.OverrideWellBehaved
public import ProofLib.Process.Overrides
public import ProofLib.Hoare.Hooks
public import ProofLib.SepLogic

/-!
# Hook Contracts for Well-Behaved Overrides

Derives `HookOk` and `subroutine_ok` contracts (`Override.regionSpec`, `WellBehaved.hookOk`,
`WellBehaved.subroutine_ok`) for `WellBehaved` overrides whose memory footprint lies in an owned
`memRegion`, together with a register-only constructor (`WellBehaved.of_regs`) and a decidable
single-state refutation witness (`Override.probe`, `WellBehaved.not_of_probe`).
-/

@[expose] public section

namespace Arm64.Override

open ProofLib Process

theorem not_frozen_of_canWrite {m : Memory} {a : BitVec 64} (h : m.canWrite a 1 = true) :
    ¬ m.Frozen a := by
  simp only [Memory.canWrite, Memory.allPerm, Bool.and_true] at h
  simp only [Memory.Frozen]
  cases hp : m.perm a with
  | none => simp
  | some p => simp_all [Perm.frozen]

section
variable {pre : State → Prop} {fp : State → BitVec 64 → Prop} {f : State → State} {s : State}

theorem WellBehaved.keepsFrozen (h : WellBehaved pre fp f) (hrun : s.status = .Running)
    (hpre : pre s) : s.mem.KeepsFrozen (f s).mem := by
  obtain ⟨-, -, hperm, hanon, -, hwr⟩ := h s hrun hpre
  intro a hfz
  refine ⟨Classical.byContradiction fun hne => ?_, by rw [hperm],
    Classical.byContradiction fun hne => ?_, by rw [hanon]⟩
  · exact not_frozen_of_canWrite (hwr a (Or.inl hne)).2 hfz
  · exact not_frozen_of_canWrite (hwr a (Or.inr hne)).2 hfz

theorem WellBehaved.symtab (h : WellBehaved pre fp f) (hrun : s.status = .Running)
    (hpre : pre s) : (f s).symtab = s.symtab := by
  obtain ⟨⟨_, _, _, _, _, he⟩, -⟩ := h s hrun hpre
  rw [he]

theorem WellBehaved.status (h : WellBehaved pre fp f) (hrun : s.status = .Running)
    (hpre : pre s) : (f s).status = .Running := by
  obtain ⟨⟨_, _, _, _, _, he⟩, -⟩ := h s hrun hpre
  rw [he]; exact hrun

theorem WellBehaved.returned (h : WellBehaved pre fp f) (hrun : s.status = .Running)
    (hpre : pre s) : Returned s (f s) ∧ CallingConventionPreserved s (f s) := by
  obtain ⟨⟨_, _, _, _, _, he⟩, hcc, -⟩ := h s hrun hpre
  refine ⟨⟨by rw [he], hcc.1, WellBehaved.status h hrun hpre⟩, hcc⟩

/-- A footprint inside `[base, base + len)` gives the separation-logic frame condition. -/
theorem WellBehaved.agreesOutside (h : WellBehaved pre fp f) (hrun : s.status = .Running)
    (hpre : pre s) {base : BitVec 64} {len : Nat} (hfp : ∀ a, fp s a → InRegion base len a) :
    AgreesOutside s.mem (f s).mem base len := by
  obtain ⟨-, -, hperm, hanon, hlf_mono, hwr⟩ := h s hrun hpre
  refine ⟨fun a hout => Classical.byContradiction fun hne => ?_, hperm,
    fun a hout => Classical.byContradiction fun hne => ?_, hlf_mono,
    fun a ha => by rw [hanon]; exact ha⟩
  · have := hfp a (hwr a (Or.inl hne)).1
    simp only [InRegion, OutsideRegion] at this hout
    omega
  · have := hfp a (hwr a (Or.inr hne)).1
    simp only [InRegion, OutsideRegion] at this hout
    omega

end

/-- The hook contract of a `WellBehaved` override whose footprint lies in `memRegion base len`:
    the caller passes ownership of the region and `φ s0`; it gets the region back and `ψ s0 sf`. -/
def regionSpec (base : BitVec 64) (len : Nat) (φ : State → Prop) (ψ : State → State → Prop) :
    Spec Unit where
  pre _ s0 := ⌜φ s0⌝ ∗ memRegion base len
  post _ s0 sf := ⌜ψ s0 sf⌝ ∗ memRegion base len

/-- A `WellBehaved` override meets `regionSpec base len φ ψ` when
    - (`hpre`) `φ` and ownership of the region establish the `WellBehaved` precondition,
    - (`hfp`) under `φ` the footprint lies inside the region, and
    - (`hpost`) the functional postcondition holds on `f s0`.
    All register, return-address, `sp`, permission, frozen-byte and frame obligations of
    `HookOk` come from `WellBehaved`. -/
theorem WellBehaved.hookOk {pre : State → Prop} {fp : State → BitVec 64 → Prop}
    {f : State → State} {base : BitVec 64} {len : Nat} {φ : State → Prop}
    {ψ : State → State → Prop} (h : WellBehaved pre fp f)
    (hpre : ∀ s0 R, φ s0 → (s0.mem ⊨ memRegion base len ∗ R) → pre s0)
    (hfp : ∀ s0, φ s0 → ∀ a, fp s0 a → InRegion base len a)
    (hpost : ∀ s0, s0.status = .Running → φ s0 → pre s0 → ψ s0 (f s0)) :
    HookOk f (regionSpec base len φ ψ) := by
  intro x R s0 hrun hsat _
  simp only [regionSpec, sepConj_assoc, satisfies_pure_sepConj] at hsat
  obtain ⟨hφ, hmem⟩ := hsat
  have hp := hpre s0 R hφ hmem
  obtain ⟨hret, hcc⟩ := h.returned hrun hp
  refine ⟨h.keepsFrozen hrun hp, h.symtab hrun hp, Or.inl ⟨hret, hcc, ?_⟩⟩
  simp only [regionSpec, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpost s0 hrun hφ hp, (IsBlock.memRegion base len).update (IsBlock.memRegion base len)
    (Nat.le_refl _) hmem (h.agreesOutside hrun hp (hfp s0 hφ)) trivial⟩

/-- After a successful `resolveAddrs`, the override program has hook `g` at `pc` for every site
    `(n, pc.toNat, g)` of `zipSites os addrs` (name `n`, resolved address, model). -/
theorem overrideProgram_externAt_of_mem {bytes : List (BitVec 8)} {img : ElfImage}
    {svc : State → State} {os : List (String × (State → State))} {addrs : List Nat}
    (h : resolveAddrs bytes img (os.map (·.1)) = .ok addrs) {n : String} {pc : BitVec 64}
    {g : State → State} (hm : (n, pc.toNat, g) ∈ zipSites os addrs) :
    (overrideProgram svc os addrs).externAt? pc = some g := by
  obtain ⟨syms, shdrs, hp, hR, -, -⟩ := resolveAddrs_ok h
  obtain ⟨-, -, h3, -⟩ := zipSites_spec hR
  obtain ⟨hmem, hr⟩ := h3 _ hm
  exact (overrideProgram_externAt_iff h pc g).mpr ⟨syms, shdrs, hp, n, hmem, hr⟩

/-- `WellBehaved.hookOk` as a `subroutine_ok` contract at the resolved `.symtab` address `pc` of
    an override `f` in `overrideProgram svc os addrs`, the program run by
    `ElfRunsToWithOverrides svc os`. -/
theorem WellBehaved.subroutine_ok {bytes : List (BitVec 8)} {img : ElfImage}
    {svc : State → State} {os : List (String × (State → State))} {addrs : List Nat}
    (hres : resolveAddrs bytes img (os.map (·.1)) = .ok addrs) {name : String} {pc : BitVec 64}
    {pre : State → Prop} {fp : State → BitVec 64 → Prop} {f : State → State}
    (hm : (name, pc.toNat, f) ∈ zipSites os addrs) {base : BitVec 64} {len : Nat}
    {φ : State → Prop} {ψ : State → State → Prop} (h : WellBehaved pre fp f)
    (hpre : ∀ s0 R, φ s0 → (s0.mem ⊨ memRegion base len ∗ R) → pre s0)
    (hfp : ∀ s0, φ s0 → ∀ a, fp s0 a → InRegion base len a)
    (hpost : ∀ s0, s0.status = .Running → φ s0 → pre s0 → ψ s0 (f s0)) :
    Arm64.subroutine_ok (overrideProgram svc os addrs) pc (regionSpec base len φ ψ) :=
  subroutine_ok_of_hookOk (overrideProgram_externAt_of_mem hres hm) (h.hookOk hpre hfp hpost)

/-- An override that only writes registers and returns, `fun s => (g s).setPC (s.readReg64 .lr)`
    with `g s = { s with regs := ..., vregs := ..., pstate := ..., fpsr := ... }`, is `WellBehaved`
    with an empty footprint as soon as `g` preserves the callee-saved registers and `sp`. -/
theorem WellBehaved.of_regs {pre : State → Prop} (g : State → State)
    (hg : ∀ s, s.status = .Running → pre s →
      ∃ regs vregs pstate fpsr, g s = { s with regs, vregs, pstate, fpsr })
    (hcc : ∀ s, s.status = .Running → pre s → CallingConventionPreserved s (g s)) :
    WellBehaved pre (fun _ _ => False) (fun s => (g s).setPC (s.readReg64 .lr)) := by
  intro s hrun hp
  obtain ⟨regs, vregs, pstate, fpsr, he⟩ := hg s hrun hp
  have hcc := hcc s hrun hp
  dsimp only
  rw [he] at hcc ⊢
  exact ⟨⟨regs, vregs, pstate, fpsr, s.mem, rfl⟩, hcc, rfl, rfl, fun _ h => h,
    fun _ hne => False.elim (hne.elim (fun h => h rfl) (fun h => h rfl))⟩

/-- Decidable observation of one transition `s ↦ f s` that every `WellBehaved` override passes
    (`WellBehaved.probe`): `pc` is the entry `x30`, and `sp`, `x19..x29`, `status = .Running`,
    `brk` and `tpidrEl0` are kept. -/
def probe (f : State → State) (s : State) : Bool :=
  (f s).pc == s.readReg64 .lr && (f s).sp == s.sp &&
  [19#5, 20#5, 21#5, 22#5, 23#5, 24#5, 25#5, 26#5, 27#5, 28#5].all
    (fun i => (f s).readReg64 (.gpr i) == s.readReg64 (.gpr i)) &&
  (f s).readReg64 .fp == s.readReg64 .fp &&
  (f s).status == .Running && (f s).brk == s.brk && (f s).tpidrEl0 == s.tpidrEl0

theorem WellBehaved.probe {pre : State → Prop} {fp : State → BitVec 64 → Prop}
    {f : State → State} (h : WellBehaved pre fp f) {s : State} (hrun : s.status = .Running)
    (hpre : pre s) : Override.probe f s = true := by
  obtain ⟨⟨_, _, _, _, _, he⟩, ⟨hsp, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, -⟩, -⟩ :=
    h s hrun hpre
  have hpc : (f s).pc = s.readReg64 .lr := by rw [he]
  have hst : (f s).status = .Running := by rw [he]; exact hrun
  have hbrk : (f s).brk = s.brk := by rw [he]
  have htp : (f s).tpidrEl0 = s.tpidrEl0 := by rw [he]
  simp [Override.probe, hpc, hsp, hst, hbrk, htp, h19, h20, h21, h22, h23, h24, h25, h26, h27,
    h28, h29] <;> rfl

/-- Refute `WellBehaved` with one running state satisfying `pre` on which `probe` fails
    (`by decide` on a concrete state). -/
theorem WellBehaved.not_of_probe {pre : State → Prop} {fp : State → BitVec 64 → Prop}
    {f : State → State} (s : State) (hrun : s.status = .Running) (hpre : pre s)
    (hbad : Override.probe f s = false) : ¬ WellBehaved pre fp f := fun h => by
  rw [h.probe hrun hpre] at hbad; contradiction

end Arm64.Override
