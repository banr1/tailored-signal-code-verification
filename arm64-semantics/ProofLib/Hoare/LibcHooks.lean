/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.Hoare.Hooks
public import ProofLib.LibcHooks
public import ProofLib.SepLogic.Bytes
public import ProofLib.CType
import Arm64.Trusted.Spec.SepLogic

/-!
# Libc and Allocator `HookOk` Witnesses

Provides `HookOk` witnesses for leaf and field-query external hooks (`retHook`, `hookNoop`,
`hookReturnZero`, `fieldHook`, `fieldHook64`), stack-frame splitting combinators, standard memory
operations (`memset`, `memcpy`, `memmove`), and single-slot or bump-pointer pool allocators
(`witnessAlloc`, `bumpAllocator`, `bumpAllocReg`).
-/

@[expose] public section

namespace ProofLib

open Arm64

/-! ## Leaf and field-query hooks -/

/-- Wrap a state transformer `f` as a leaf subroutine hook that returns to `LR` (`X30`). -/
def retHook (f : State → State) (s : State) : State :=
  (f s).setPC (s.readReg64 .lr)

/-- No-op extern hook: returns immediately to `LR` (`X30`) leaving all registers and memory unchanged. -/
def hookNoop : State → State :=
  retHook id

/-- Null-returning extern hook (e.g. `malloc`/`calloc`/`realloc` returning `NULL`):
    sets `X0 = 0` and returns to `LR` (`X30`). -/
def hookReturnZero : State → State :=
  retHook fun s => s.writeReg64 .x0 0#64

abbrev hookAllocNull := hookReturnZero

/-- Soundness rule for `retHook f`: reduces `HookOk (retHook f) spec` to showing that `f`
    preserves frozen memory, `symtab`, `.Running` status, and AAPCS64 callee-saved registers/SP,
    and establishes `spec.post x s0 (f s0) ∗ R` when `(f s0).setPC lr = retHook f s0`. -/
theorem retHook_ok {α : Type} {f : State → State} {spec : Spec α}
    (h : ∀ x R s0, s0.status = .Running → (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      Memory.KeepsFrozen s0.mem (f s0).mem ∧
      (f s0).symtab = s0.symtab ∧
      (f s0).status = .Running ∧
      CallingConventionPreserved s0 (f s0) ∧
      ((f s0).mem ⊨ spec.post x s0 (retHook f s0) ∗ R)) :
    HookOk (retHook f) spec := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hst, ⟨hsp_eq, hcs⟩, hpost⟩ := h x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, Or.inl ⟨⟨rfl, hsp_eq, hst⟩, ⟨hsp_eq, hcs⟩, hpost⟩⟩

/-- Soundness of `hookNoop` for any `spec` whose postcondition holds on `hookNoop s0` with unchanged memory. -/
theorem hookNoop_ok {α : Type} {spec : Spec α}
    (h : ∀ x R s0, (s0.mem ⊨ spec.pre x s0 ∗ R) →
      (s0.mem ⊨ spec.post x s0 (hookNoop s0) ∗ R)) :
    HookOk hookNoop spec := by
  refine retHook_ok fun x R s0 _ hpre _ => ?_
  exact ⟨Memory.KeepsFrozen.refl _, rfl, ‹_›,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, h x R s0 hpre⟩

/-- Soundness of `hookReturnZero` for any `spec` whose postcondition holds when `X0 = 0` and memory is unchanged. -/
theorem hookReturnZero_ok {α : Type} {spec : Spec α}
    (h : ∀ x R s0, (s0.mem ⊨ spec.pre x s0 ∗ R) →
      (s0.mem ⊨ spec.post x s0 (hookReturnZero s0) ∗ R)) :
    HookOk hookReturnZero spec := by
  refine retHook_ok fun x R s0 _ hpre _ => ?_
  exact ⟨Memory.KeepsFrozen.refl _, rfl, ‹_›,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, h x R s0 hpre⟩

@[simp]
theorem retHook_writeReg64_x0 (s0 : State) (f : State → BitVec 64) :
    (retHook (fun s => s.writeReg64 .x0 (f s)) s0).readReg64 .x0 = f s0 := rfl

@[simp]
theorem retHook_writeReg32_x0 (s0 : State) (f : State → BitVec 32) :
    (retHook (fun s => s.writeReg32 .x0 (f s)) s0).readReg32 .x0 = f s0 := by
  simp [retHook, State.setPC, State.writeReg32, State.readReg32,
    State.writeReg64, State.readReg64, RegFile.write, RegFile.read]

/-- Soundness of `retHook g` for a register-only state transformer `g` (leaving memory, `symtab`,
    status, and AAPCS64 callee-saved registers/SP unchanged). -/
theorem regHook_ok {α : Type} {spec : Spec α} (g : State → State)
    (h : ∀ x R s0, (s0.mem ⊨ spec.pre x s0 ∗ R) →
      (s0.mem ⊨ spec.post x s0 (retHook g s0) ∗ R))
    (hmem : ∀ s, (g s).mem = s.mem := by intro _; rfl)
    (hsym : ∀ s, (g s).symtab = s.symtab := by intro _; rfl)
    (hst : ∀ s, (g s).status = s.status := by intro _; rfl)
    (hcc : ∀ s, CallingConventionPreserved s (g s) := by
      intro _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) :
    HookOk (retHook g) spec := by
  refine retHook_ok fun x R s0 hrun hpre _ => ?_
  refine ⟨?_, hsym s0, (hst s0).trans hrun, hcc s0, ?_⟩
  · rw [hmem]; exact Memory.KeepsFrozen.refl _
  · rw [hmem]; exact h x R s0 hpre

/-- Leaf hook returning `g w` in `W0`, where `w` is the 32-bit word at `X0 + off`. -/
def fieldHook (off : BitVec 64) (g : BitVec 32 → BitVec 32) : State → State :=
  retHook fun s => s.writeReg32 .x0 (g (s.mem.read32 (s.readReg64 .x0 + off)))

/-- Leaf hook returning `g w` in `X0`, where `w` is the 64-bit word at `X0 + off`. -/
def fieldHook64 (off : BitVec 64) (g : BitVec 64 → BitVec 64) : State → State :=
  retHook fun s => s.writeReg64 .x0 (g (s.mem.read64 (s.readReg64 .x0 + off)))

@[simp]
theorem fieldHook_readReg32_x0 (off : BitVec 64) (g : BitVec 32 → BitVec 32) (s0 : State) :
    (fieldHook off g s0).readReg32 .x0 = g (s0.mem.read32 (s0.readReg64 .x0 + off)) :=
  retHook_writeReg32_x0 s0 _

@[simp]
theorem fieldHook64_readReg64_x0 (off : BitVec 64) (g : BitVec 64 → BitVec 64) (s0 : State) :
    (fieldHook64 off g s0).readReg64 .x0 = g (s0.mem.read64 (s0.readReg64 .x0 + off)) := rfl

/-- Auto-parameter helper that unfolds concrete `Spec.pre` / `Spec.post` projections so
    `simp [ctype_simp]` reduces lowered `c_spec` / `c_type_spec` handle query contracts. -/
elab "close_field_hook_entails" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| intros))
  let goal ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← goal.getType)
  let ty' ← Lean.Core.transform ty (pre := fun e => do
    if e.isAppOfArity ``Spec.pre 4 || e.isAppOfArity ``Spec.post 5 then
      let specExpr := (e.getAppArgs)[1]!
      if let some specUnf ← Lean.Meta.unfoldDefinition? specExpr then
        let args := e.getAppArgs.set! 1 specUnf
        return .visit (← Lean.Meta.whnf (Lean.mkAppN e.getAppFn args))
    return .continue)
  let goal' ← goal.replaceTargetDefEq ty'
  Lean.Elab.Tactic.replaceMainGoal [goal']
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    (try dsimp only;
     try simp only [ctype_simp, true_and, and_true, pure_true_sepConj, sepConj_pure_true,
       sepConj_emp, emp_sepConj];
     try rw [show _ = _ by ac_rfl];
     exact Entails.refl _)))

/-- Soundness of `fieldHook off g` for any read-only 32-bit query contract over a handle `(p, m)`
    with representation `rep p m` returning `f m` in `W0`. -/
theorem fieldHook_ok {M : Type} {rep : BitVec 64 → M → SepProp}
    {spec : Spec (BitVec 64 × M)}
    (off : BitVec 64) (g : BitVec 32 → BitVec 32) (f : M → BitVec 32)
    (hf : ∀ {mem : Memory} {p : BitVec 64} {m : M} {R : SepProp},
      (mem ⊨ rep p m ∗ R) → g (mem.read32 (p + off)) = f m)
    (hpre_ent : ∀ p m s0,
      spec.pre (p, m) s0 ⊢ ⌜s0.readReg64 .x0 = p⌝ ∗ rep p m := by close_field_hook_entails)
    (hpost_ent : ∀ p m s0 sf,
      ⌜sf.readReg32 .x0 = f m⌝ ∗ rep p m ⊢ spec.post (p, m) s0 sf := by close_field_hook_entails) :
    HookOk (fieldHook off g) spec := by
  refine regHook_ok (fun s => s.writeReg32 .x0 (g (s.mem.read32 (s.readReg64 .x0 + off))))
    fun ⟨p, m⟩ R s0 hpre => ?_
  have hpre' := Satisfies.mono (sepConj_mono_left (hpre_ent p m s0)) hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  refine Satisfies.mono (sepConj_mono_left (hpost_ent p m s0 _)) ?_
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨?_, hpre'.2⟩
  change (fieldHook off g s0).readReg32 .x0 = f m
  rw [fieldHook_readReg32_x0, hpre'.1]
  exact hf hpre'.2

/-- Soundness of `fieldHook64 off g` for any read-only 64-bit query contract over a handle `(p, m)`
    with representation `rep p m` returning `f m` in `X0`. -/
theorem fieldHook64_ok {M : Type} {rep : BitVec 64 → M → SepProp}
    {spec : Spec (BitVec 64 × M)}
    (off : BitVec 64) (g : BitVec 64 → BitVec 64) (f : M → BitVec 64)
    (hf : ∀ {mem : Memory} {p : BitVec 64} {m : M} {R : SepProp},
      (mem ⊨ rep p m ∗ R) → g (mem.read64 (p + off)) = f m)
    (hpre_ent : ∀ p m s0,
      spec.pre (p, m) s0 ⊢ ⌜s0.readReg64 .x0 = p⌝ ∗ rep p m := by close_field_hook_entails)
    (hpost_ent : ∀ p m s0 sf,
      ⌜sf.readReg64 .x0 = f m⌝ ∗ rep p m ⊢ spec.post (p, m) s0 sf := by close_field_hook_entails) :
    HookOk (fieldHook64 off g) spec := by
  refine regHook_ok (fun s => s.writeReg64 .x0 (g (s.mem.read64 (s.readReg64 .x0 + off))))
    fun ⟨p, m⟩ R s0 hpre => ?_
  have hpre' := Satisfies.mono (sepConj_mono_left (hpre_ent p m s0)) hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  refine Satisfies.mono (sepConj_mono_left (hpost_ent p m s0 _)) ?_
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨?_, hpre'.2⟩
  change (fieldHook64 off g s0).readReg64 .x0 = f m
  rw [fieldHook64_readReg64_x0, hpre'.1]
  exact hf hpre'.2

/-! ## Stack-frame splitting -/

/-- Split the unused bottom `d` bytes off `stackAt sp m` (`n + d = m ≤ 2 ^ 64`) leaving
    `stackAt sp n` at the top for a callee or hook. -/
theorem stackAt_split_bottom_of_eq (sp : BitVec 64) (m n d : Nat)
    (hnd : n + d = m := by decide) (hm : m ≤ 2 ^ 64 := by decide) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) d ∗ stackAt sp n := by
  subst hnd
  exact stackAt_split_bottom sp n d hm

/-- Split a `d + hookBytes` stack into its unused bottom `d` bytes and a callback's `hookBytes`
    region (defaulting `hookBytes` to `4096`). -/
theorem stackAt_split_hook (sp : BitVec 64) (d : Nat) (hookBytes : Nat := 4096)
    (h : d + hookBytes ≤ 2 ^ 64 := by decide) :
    stackAt sp (d + hookBytes) =
      memRegion (sp - BitVec.ofNat 64 (d + hookBytes)) d ∗ stackAt sp hookBytes := by
  rw [show d + hookBytes = hookBytes + d by omega]
  exact stackAt_split_bottom sp hookBytes d (by omega)

/-- Refold an unused bottom `memRegion a d` (`a = sp - BitVec.ofNat 64 m`) and `stackAt sp n`
    (`n + d = m ≤ 2 ^ 64`) back into the caller's `stackAt sp m`. -/
theorem stackAt_refold_bottom (sp a : BitVec 64) (n d m : Nat)
    (hn : n + d = m := by decide) (hm : m ≤ 2 ^ 64 := by decide)
    (ha : a = sp - BitVec.ofNat 64 m := by rfl) :
    (memRegion a d ∗ stackAt sp n) ⊢ stackAt sp m := by
  subst ha hn
  rw [stackAt_split_bottom sp n d hm]
  exact Entails.refl _

/-! ## Memory-operation hooks -/

/-- Any `memRegion ptr len` separated from a non-empty stack region `memRegion (sp - frameSize) frameSize`
    has `len < 2^64` (since the two regions are disjoint in the 64-bit address space). -/
theorem len_lt_of_memRegion_hookFrame {m : Memory} {ptr sp : BitVec 64} {len frameSize : Nat}
    {R : SepProp}
    (h : m ⊨ memRegion ptr len ∗ (memRegion (sp - BitVec.ofNat 64 frameSize) frameSize ∗ R))
    (hframe : 0 < frameSize := by decide) :
    len < 2 ^ 64 := by
  by_cases h0 : len = 0
  · omega
  · have hpos : 0 < len := Nat.pos_of_ne_zero h0
    have hd := (IsBlock.memRegion ptr len).disjoint
      (IsBlock.memRegion (sp - BitVec.ofNat 64 frameSize) frameSize) hpos hframe h
    have hlt := (sp - BitVec.ofNat 64 frameSize - ptr).isLt
    exact Nat.lt_of_le_of_lt hd.1 hlt

/-- Functional hook for `void *memset(void *ptr, int c, size_t n)`:
    writes `n` copies of `(W1).truncate 8` at `X0` and returns `X0` at `LR`. -/
def hookMemset : State → State :=
  retHook fun s =>
    let ptr := s.readReg64 .x0
    let c : BitVec 8 := (s.readReg32 .x1).truncate 8
    let n := (s.readReg64 .x2).toNat
    s.setMem (s.mem.writeBytes ptr (List.replicate n c))

/-- Functional hook for `void *memcpy(void *dst, const void *src, size_t n)` /
    `void *memmove(void *dst, const void *src, size_t n)`:
    reads `n` bytes from `X1`, writes them to `X0`, and returns `X0` at `LR`. -/
def hookMemcpy : State → State :=
  retHook fun s =>
    let dst := s.readReg64 .x0
    let src := s.readReg64 .x1
    let n := (s.readReg64 .x2).toNat
    s.setMem (s.mem.writeBytes dst (s.mem.readBytes src n))

abbrev hookMemmove : State → State := hookMemcpy

/-- Standard separation-logic specification for `memset(ptr, c, len)` with a `hookStack`-byte stack frame. -/
def libcMemsetSpec (hookStack : Nat := 4096) : Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := fun (ptr, c, len) s0 =>
    ⌜s0.readReg64 .x0 = ptr ∧
     (s0.readReg32 .x1).truncate 8 = c ∧
     (s0.readReg64 .x2).toNat = len⌝ ∗
    memRegion ptr len ∗
    stackAt s0.sp hookStack
  post := fun (ptr, c, len) s0 sf =>
    ⌜sf.readReg64 .x0 = ptr⌝ ∗
    (ptr ↦ₛ List.replicate len c) ∗
    stackAt s0.sp hookStack

/-- Soundness of `hookMemset` for `libcMemsetSpec hookStack` (`0 < hookStack`). -/
theorem hookMemset_ok (hookStack : Nat := 4096) (hstack : 0 < hookStack := by decide) :
    HookOk hookMemset (libcMemsetSpec hookStack) := by
  refine retHook_ok fun ⟨ptr, c, len⟩ R s0 _ hpre _ => ?_
  simp only [libcMemsetSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hlen : (List.replicate len c).length ≤ 2 ^ 64 := by
    rw [List.length_replicate]
    exact Nat.le_of_lt (len_lt_of_memRegion_hookFrame hmem hstack)
  have hmem_rep : s0.mem ⊨ memRegion ptr (List.replicate len c).length ∗ (stackAt s0.sp hookStack ∗ R) := by
    rwa [List.length_replicate]
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only
    rw [hx0, hx1, hx2]
    exact keepsFrozen_writeBytes_of_memRegion (List.replicate len c) hlen hmem_rep
  · simp only [libcMemsetSpec, retHook, State.readReg64_setPC, State.readReg64_setMem,
      hx0, hx1, hx2, sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact satisfies_writeBytes (List.replicate len c) hlen hmem_rep

/-- Standard separation-logic specification for `memset(ptr, 0, len)` without a stack-frame conjunct
    (requiring `len ≤ 2^64`). -/
def memsetRegionSpec : Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := fun (ptr, c, len) s0 =>
    ⌜s0.readReg64 .x0 = ptr ∧
     (s0.readReg32 .x1).truncate 8 = c ∧
     (s0.readReg64 .x2).toNat = len ∧
     len ≤ 2 ^ 64⌝ ∗
    memRegion ptr len
  post := fun (ptr, c, len) _ sf =>
    ⌜sf.readReg64 .x0 = ptr⌝ ∗
    (ptr ↦ₛ List.replicate len c)

/-- Soundness of `hookMemset` for `memsetRegionSpec`. -/
theorem hookMemset_region_ok : HookOk hookMemset memsetRegionSpec := by
  refine retHook_ok fun ⟨ptr, c, len⟩ R s0 _ hpre _ => ?_
  simp only [memsetRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hlen' : (List.replicate len c).length ≤ 2 ^ 64 := by simpa using hlen
  have hmem_rep : s0.mem ⊨ memRegion ptr (List.replicate len c).length ∗ R := by
    rwa [List.length_replicate]
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only
    rw [hx0, hx1, hx2]
    exact keepsFrozen_writeBytes_of_memRegion (List.replicate len c) hlen' hmem_rep
  · simp only [memsetRegionSpec, retHook, State.readReg64_setPC, State.readReg64_setMem,
      hx0, hx1, hx2, sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact satisfies_writeBytes (List.replicate len c) hlen' hmem_rep

/-- Standard separation-logic specification for non-overlapping `memcpy(dst, src, bs.length)`. -/
def libcMemcpySpec (hookStack : Nat := 4096) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ₛ bs) ∗
    stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst⌝ ∗
    (dst ↦ₛ bs) ∗
    (src ↦ₛ bs) ∗
    stackAt s0.sp hookStack

/-- Soundness of `hookMemcpy` for `libcMemcpySpec hookStack`. -/
theorem hookMemcpy_ok (hookStack : Nat := 4096) :
    HookOk hookMemcpy (libcMemcpySpec hookStack) := by
  refine retHook_ok fun ⟨dst, src, bs⟩ R s0 _ hpre _ => ?_
  simp only [libcMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hsrc_front : s0.mem ⊨ (src ↦ₛ bs) ∗ (memRegion dst bs.length ∗ (stackAt s0.sp hookStack ∗ R)) := by
    rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
  obtain ⟨hlen, hread⟩ := (IsBlock.pointsToBytes src bs).read hsrc_front
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only
    rw [hx0, hx1, hx2, hread]
    exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  · simp only [libcMemcpySpec, retHook, State.readReg64_setPC, State.readReg64_setMem,
      hx0, hx1, hx2, hread, sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact satisfies_writeBytes bs hlen hmem

/-- Standard separation-logic specification for `memcpy(dst, src, bs.length)` without a stack-frame conjunct. -/
def memcpyRegionSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ₛ bs)
  post := fun (dst, src, bs) _ sf =>
    ⌜sf.readReg64 .x0 = dst⌝ ∗
    (dst ↦ₛ bs) ∗
    (src ↦ₛ bs)

/-- Soundness of `hookMemcpy` for `memcpyRegionSpec`. -/
theorem hookMemcpy_region_ok : HookOk hookMemcpy memcpyRegionSpec := by
  refine retHook_ok fun ⟨dst, src, bs⟩ R s0 _ hpre _ => ?_
  simp only [memcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hsrc_front : s0.mem ⊨ (src ↦ₛ bs) ∗ (memRegion dst bs.length ∗ R) := by
    rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
  obtain ⟨hlen, hread⟩ := (IsBlock.pointsToBytes src bs).read hsrc_front
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only
    rw [hx0, hx1, hx2, hread]
    exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  · simp only [memcpyRegionSpec, retHook, State.readReg64_setPC, State.readReg64_setMem,
      hx0, hx1, hx2, hread, sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact satisfies_writeBytes bs hlen hmem

/-- Standard separation-logic specification for in-buffer `memmove(base + dst, base + src, len)`
    operating on a single owned buffer `base ↦ₛ buf` (allowing overlapping `dst` and `src` slices). -/
def libcMemmoveSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) where
  pre := fun (base, buf, dst, src, len) s0 =>
    ⌜s0.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧
     s0.readReg64 .x1 = base + BitVec.ofNat 64 src ∧
     (s0.readReg64 .x2).toNat = len ∧
     dst + len ≤ buf.length ∧
     src + len ≤ buf.length⌝ ∗
    (base ↦ₛ buf) ∗
    stackAt s0.sp hookStack
  post := fun (base, buf, dst, src, len) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 dst⌝ ∗
    (base ↦ₛ listMove buf dst src len) ∗
    stackAt s0.sp hookStack

/-- Soundness of `hookMemmove` (`hookMemcpy`) for in-buffer potentially-overlapping `libcMemmoveSpec`. -/
theorem hookMemmove_ok (hookStack : Nat := 4096) :
    HookOk hookMemmove (libcMemmoveSpec hookStack) := by
  refine retHook_ok fun ⟨base, buf, dst, src, len⟩ R s0 _ hpre _ => ?_
  simp only [libcMemmoveSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hdst, hsrc⟩, hmem⟩
  have hbuf_len : (buf.length ≤ 2 ^ 64) := ((IsBlock.pointsToBytes base buf).read hmem).1
  have hsrc_split : s0.mem ⊨
      ((base + BitVec.ofNat 64 src) ↦ₛ (buf.drop src).take len) ∗
      (((base ↦ₛ buf.take src) ∗
        ((base + BitVec.ofNat 64 (src + len)) ↦ₛ buf.drop (src + len))) ∗
       (stackAt s0.sp hookStack ∗ R)) := by
    rw [pointsToBytes_split3 base buf src len hsrc, sepConj_assoc] at hmem
    exact hmem
  obtain ⟨hlen_le, hread_src⟩ :=
    (IsBlock.pointsToBytes (base + BitVec.ofNat 64 src) ((buf.drop src).take len)).read hsrc_split
  have hslice_len : ((buf.drop src).take len).length = len := by
    rw [List.length_take, List.length_drop]; omega
  rw [hslice_len] at hread_src hlen_le
  have hdst_split : s0.mem ⊨
      ((base + BitVec.ofNat 64 dst) ↦ₛ (buf.drop dst).take len) ∗
      (((base ↦ₛ buf.take dst) ∗
        ((base + BitVec.ofNat 64 (dst + len)) ↦ₛ buf.drop (dst + len))) ∗
       (stackAt s0.sp hookStack ∗ R)) := by
    rw [pointsToBytes_split3 base buf dst len hdst, sepConj_assoc] at hmem
    exact hmem
  have hdst_len : ((buf.drop dst).take len).length = len := by
    rw [List.length_take, List.length_drop]; omega
  have hdst_reg : s0.mem ⊨
      memRegion (base + BitVec.ofNat 64 dst) ((buf.drop src).take len).length ∗
      (((base ↦ₛ buf.take dst) ∗
        ((base + BitVec.ofNat 64 (dst + len)) ↦ₛ buf.drop (dst + len))) ∗
       (stackAt s0.sp hookStack ∗ R)) := by
    have hent := pointsToBytes_entails_memRegion (base + BitVec.ofNat 64 dst) ((buf.drop dst).take len)
    rw [show ((buf.drop dst).take len).length = ((buf.drop src).take len).length by omega] at hent
    exact Satisfies.mono (sepConj_mono_left hent) hdst_split
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only
    rw [hx0, hx1, hx2, hread_src]
    exact keepsFrozen_writeBytes_of_memRegion ((buf.drop src).take len) (by omega) hdst_reg
  · simp only [libcMemmoveSpec, retHook, State.readReg64_setPC,
      State.readReg64_setMem, hx0, hx1, hx2, hread_src, sepConj_assoc, satisfies_pure_sepConj,
      true_and]
    have hw := satisfies_writeBytes_step hdst_split (bs := (buf.drop src).take len) (by omega)
    rwa [← sepConj_assoc, pointsToBytes_listMove base buf dst src len hdst hsrc] at hw

/-! ## Pool and bump-pointer allocator witnesses -/

/-- Single-slot constant-address allocator hook: returns `slotAddr` in `X0` and jumps to `LR`. -/
def witnessAlloc (slotAddr : BitVec 64) : State → State :=
  retHook fun s => s.writeReg64 .x0 slotAddr

abbrev mallocPoolHook := witnessAlloc
abbrev freePoolHook := hookNoop

/-- Soundness of `witnessAlloc slotAddr` for any `spec` whose postcondition holds when `X0 = slotAddr`
    and memory is unchanged. -/
theorem witnessAlloc_ok (slotAddr : BitVec 64) {α : Type} {spec : Spec α}
    (h : ∀ x R s0, (s0.mem ⊨ spec.pre x s0 ∗ R) →
      (s0.mem ⊨ spec.post x s0 (witnessAlloc slotAddr s0) ∗ R)) :
    HookOk (witnessAlloc slotAddr) spec := by
  refine retHook_ok fun x R s0 _ hpre _ => ?_
  exact ⟨Memory.KeepsFrozen.refl _, rfl, ‹_›,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, h x R s0 hpre⟩

/-- Bump-pointer allocator invariant over `[poolBase, poolBase + poolCap)` with a 64-bit bump
    offset counter at `counterAddr`. -/
def bumpAllocator (poolBase : BitVec 64) (poolCap : Nat) (counterAddr : BitVec 64) : SepProp :=
  ∃∗ cur : BitVec 64,
    (counterAddr ↦₆₄ cur) ∗
    if cur.toNat ≤ poolCap then
      memRegion (poolBase + cur) (poolCap - cur.toNat)
    else
      emp

/-- Initialize `bumpAllocator` from `counterAddr ↦₆₄ 0#64` and `memRegion poolBase poolCap`. -/
theorem satisfies_bumpAllocator_init {m : Memory} {poolBase : BitVec 64} {poolCap : Nat}
    {counterAddr : BitVec 64} {R : SepProp}
    (h : m ⊨ (counterAddr ↦₆₄ 0#64) ∗ (memRegion poolBase poolCap ∗ R)) :
    m ⊨ bumpAllocator poolBase poolCap counterAddr ∗ R := by
  unfold bumpAllocator
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨0#64, ?_⟩
  simpa [sepConj_assoc] using h

/-- Bump-pointer allocator hook reading its byte-count request via `reqFn s` (supporting size
    arguments in `X0`, `X1`, `X2`, or `X1 * X2`). -/
def bumpAllocReg (poolBase : BitVec 64) (poolCap : Nat) (counterAddr : BitVec 64)
    (reqFn : State → BitVec 64) (s : State) : State :=
  let req := reqFn s
  let cur := s.mem.read64 counterAddr
  if cur.toNat + req.toNat ≤ poolCap then
    let s1 := s.setMem (s.mem.write64 counterAddr (cur + req))
    (s1.writeReg64 .x0 (poolBase + cur)).setPC (s.readReg64 .lr)
  else
    (s.writeReg64 .x0 0#64).setPC (s.readReg64 .lr)

/-- Step rule for `bumpAllocReg` over `bumpAllocator`: splits off `Allocator.optRegion` when the
    request fits and returns `0#64` when the pool is exhausted. -/
theorem bumpAllocReg_step {poolBase : BitVec 64} {poolCap : Nat} {counterAddr : BitVec 64}
    (reqFn : State → BitVec 64) {s0 : State} {sz : Nat} {F : SepProp}
    (hbase_pos : 0 < poolBase.toNat)
    (hcap_bound : poolBase.toNat + poolCap < 2 ^ 64)
    (hrun : s0.status = .Running)
    (hreq : reqFn s0 = BitVec.ofNat 64 sz)
    (hsz : sz < 2 ^ 64)
    (hmem : s0.mem ⊨ bumpAllocator poolBase poolCap counterAddr ∗ F) :
    let sf := bumpAllocReg poolBase poolCap counterAddr reqFn s0
    s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
    Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    sf.mem ⊨
      (bumpAllocator poolBase poolCap counterAddr ∗
       Allocator.optRegion (sf.readReg64 .x0) sz) ∗ F := by
  have hreq_toNat : (BitVec.ofNat 64 sz).toNat = sz := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hsz
  unfold bumpAllocator at hmem
  rw [sepExists_sepConj_left, satisfies_sepExists] at hmem
  rcases hmem with ⟨cur, hmem⟩
  rw [sepConj_assoc] at hmem
  have hcur_read : s0.mem.read64 counterAddr = cur :=
    (IsBlock.pointsTo64 counterAddr cur).read hmem
  have hcur_cw : s0.mem.canWrite counterAddr 8 = true :=
    (IsBlock.pointsTo64 counterAddr cur).canWrite (by decide) hmem
  dsimp only
  unfold bumpAllocReg
  dsimp only
  rw [hreq, hcur_read]
  split
  · rename_i hfit
    rw [hreq_toNat] at hfit
    have hcur_le : cur.toNat ≤ poolCap := by omega
    simp only [hcur_le, ↓reduceIte] at hmem
    let req := BitVec.ofNat 64 sz
    have hkf : Memory.KeepsFrozen s0.mem (s0.mem.write64 counterAddr (cur + req)) :=
      Memory.keepsFrozen_write64 hcur_cw (cur + req)
    refine ⟨hkf, rfl, ⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    have hupd : s0.mem.write64 counterAddr (cur + req) ⊨
        (counterAddr ↦₆₄ (cur + req)) ∗
        (memRegion (poolBase + cur) (poolCap - cur.toNat) ∗ F) :=
      (IsBlock.pointsTo64 counterAddr cur).write64 hmem (cur + req)
    have hadd_toNat : (cur + req).toNat = cur.toNat + sz := by
      change (cur + BitVec.ofNat 64 sz).toNat = cur.toNat + sz
      rw [BitVec.toNat_add, hreq_toNat, Nat.mod_eq_of_lt (by omega)]
    have hsplit_eq : poolCap - cur.toNat = sz + (poolCap - (cur + req).toNat) := by omega
    have haddr_eq : poolBase + cur + BitVec.ofNat 64 sz = poolBase + (cur + req) := by
      rw [BitVec.add_assoc]
    have hcur'_le : (cur + req).toNat ≤ poolCap := by omega
    have hptr_ne : poolBase + cur ≠ 0#64 := by
      intro heq
      have ht : (poolBase + cur).toNat = 0 := by rw [heq]; rfl
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)] at ht
      omega
    rw [hsplit_eq, memRegion_split (poolBase + cur) sz (poolCap - (cur + req).toNat) (by omega),
        haddr_eq] at hupd
    change s0.mem.write64 counterAddr (cur + req) ⊨
      (bumpAllocator poolBase poolCap counterAddr ∗
       Allocator.optRegion (poolBase + cur) sz) ∗ F
    unfold Allocator.optRegion bumpAllocator
    simp only [hptr_ne, ↓reduceIte]
    rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨cur + req, ?_⟩
    simp only [hcur'_le, ↓reduceIte, sepConj_assoc]
    have hperm :
        ((counterAddr ↦₆₄ (cur + req)) ∗
          (memRegion (poolBase + (cur + req)) (poolCap - (cur + req).toNat) ∗
           (memRegion (poolBase + cur) sz ∗ F))) =
        ((counterAddr ↦₆₄ (cur + req)) ∗
          ((memRegion (poolBase + cur) sz ∗
            memRegion (poolBase + (cur + req)) (poolCap - (cur + req).toNat)) ∗ F)) := by
      ac_rfl
    rw [hperm]
    exact hupd
  · rename_i _hnofit
    refine ⟨Memory.KeepsFrozen.refl _, rfl, ⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    change s0.mem ⊨
      (bumpAllocator poolBase poolCap counterAddr ∗
       Allocator.optRegion 0#64 sz) ∗ F
    unfold Allocator.optRegion bumpAllocator
    simp only [↓reduceIte, sepConj_emp]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨cur, by rwa [← sepConj_assoc] at hmem⟩

/-- Any allocation returned by `bumpAllocReg` (or `0#64` on pool exhaustion) fits in the 64-bit
    address space without wrapping (`(sf.readReg64 .x0).toNat + sz ≤ 2 ^ 64`). -/
theorem bumpAllocReg_noWrap {poolBase : BitVec 64} {poolCap : Nat} {counterAddr : BitVec 64}
    (reqFn : State → BitVec 64) {s0 : State} {sz : Nat}
    (hcap_bound : poolBase.toNat + poolCap < 2 ^ 64)
    (hreq : reqFn s0 = BitVec.ofNat 64 sz)
    (hsz : sz < 2 ^ 64) :
    ((bumpAllocReg poolBase poolCap counterAddr reqFn s0).readReg64 .x0).toNat + sz ≤ 2 ^ 64 := by
  have hreq_toNat : (BitVec.ofNat 64 sz).toNat = sz := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hsz
  unfold bumpAllocReg
  dsimp only
  rw [hreq]
  split
  · rename_i hfit
    rw [hreq_toNat] at hfit
    change (poolBase + s0.mem.read64 counterAddr).toNat + sz ≤ 2 ^ 64
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    omega
  · change 0 + sz ≤ 2 ^ 64
    omega

/-! ## Read-only `memcpy` and call-site `Allocator` combinators -/

/-- Separation-logic specification for `memcpy(dst, src, bs.length)` from a read-only source buffer
    `src ↦ᵣ bs`. -/
def libcMemcpyROSpec (hookStack : Nat := 4096) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ᵣ bs) ∗
    stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst⌝ ∗
    (dst ↦ₛ bs) ∗
    (src ↦ᵣ bs) ∗
    stackAt s0.sp hookStack

namespace Allocator

@[simp]
theorem optRegion_zero (len : Nat) : optRegion 0#64 len = emp := rfl

theorem optRegion_of_ne_zero {ptr : BitVec 64} (len : Nat) (h : ptr ≠ 0#64) :
    optRegion ptr len = memRegion ptr len := by
  simp [optRegion, h]

@[simp]
theorem optZeroBytes_zero (len : Nat) : optZeroBytes 0#64 len = emp := rfl


@[simp]
theorem allocSeq_nil (alloc : ProofLib.Allocator) (idx : Nat) :
    alloc.allocSeq idx [] = emp := rfl

@[simp]
theorem allocSeq_cons (alloc : ProofLib.Allocator) (idx : Nat) (req : BitVec 64) (len : Nat)
    (rest : List (BitVec 64 × Nat)) :
    alloc.allocSeq idx ((req, len) :: rest) =
      alloc.allocAt idx req len ∗ alloc.allocSeq (idx + 1) rest := rfl

/-- Two successful positive-length allocations in `allocSeq` at consecutive call sites `idx` and
    `idx + 1` never alias, even when both request the exact same byte size `req`. -/
theorem allocSeq_pair_ne {m : Memory} {alloc : ProofLib.Allocator} {idx : Nat}
    {req1 req2 : BitVec 64} {len1 len2 : Nat}
    {rest : List (BitVec 64 × Nat)} {R : SepProp}
    (h : m ⊨ alloc.allocSeq idx ((req1, len1) :: (req2, len2) :: rest) ∗ R)
    (hp1 : alloc.ptr idx req1 ≠ 0#64) (hp2 : alloc.ptr (idx + 1) req2 ≠ 0#64)
    (hlen1 : 0 < len1) (hlen2 : 0 < len2) :
    alloc.ptr idx req1 ≠ alloc.ptr (idx + 1) req2 := by
  simp only [allocSeq_cons, allocAt, optRegion_of_ne_zero _ hp1, optRegion_of_ne_zero _ hp2,
    sepConj_assoc] at h
  intro heq
  rw [heq] at h
  have hd := (IsBlock.memRegion (alloc.ptr (idx + 1) req2) len1).disjoint
    (IsBlock.memRegion (alloc.ptr (idx + 1) req2) len2) hlen1 hlen2 h
  simp only [DisjointRegions, BitVec.sub_self, BitVec.toNat_ofNat, Nat.zero_mod] at hd
  omega

end Allocator

/-- Soundness of `freePoolHook` (`hookNoop`) for `libcFreeSpec hookStack`. -/
theorem hookFree_ok (hookStack : Nat := 4096) :
    HookOk freePoolHook (libcFreeSpec hookStack) := by
  refine hookNoop_ok fun ⟨ptr, len⟩ R s0 hpre => ?_
  simp only [libcFreeSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact Satisfies.of_sep_right hpre.2


end ProofLib
