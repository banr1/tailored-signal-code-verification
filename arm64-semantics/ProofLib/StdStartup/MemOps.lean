/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import Arm64.Trusted.Spec.Hoare
public import ProofLib.Hoare.SubroutineOk
public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.Region
public import ProofLib.SepLogic.WP.Structural
public import ProofLib.SepLogic.FrameInfer
public import ProofLib.ProgramReflection
public import ProofLib.BV.Bits

/-!
# Memory and Atomic Operations for Runtime Startup

Defines process-state preservation (`StdStatePreserved`), total-correctness subroutine contracts and
framed `SepWP` call lemmas for `memset`, `memcpy`, and AArch64 outline atomics, and `WordTree`
instruction/word matchers.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib.StdStartup

open Arm64 ProofLib

/-! ## Process-Level State Preservation -/

/-- Non-memory-content process state preserved across pure memory routines (`memset`, `memcpy`,
    `strlen`): file-system state (`fs`), observable trace (`trace`), thread pointer (`tpidrEl0`),
    signal dispositions (`sigActions`), program break (`brk`, `brkStart`), and page permissions. -/
def StdStatePreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
  sf.trace = s0.trace ∧
  sf.tpidrEl0 = s0.tpidrEl0 ∧
  sf.sigActions = s0.sigActions ∧
  sf.brk = s0.brk ∧
  sf.brkStart = s0.brkStart ∧
  sf.physMemAvail = s0.physMemAvail ∧
  (∀ a, sf.mem.perm a = s0.mem.perm a)

theorem StdStatePreserved.rfl (s : State) : StdStatePreserved s s :=
  ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, fun _ => Eq.refl _⟩

theorem StdStatePreserved.trans {s0 s1 s2 : State}
    (h01 : StdStatePreserved s0 s1) (h12 : StdStatePreserved s1 s2) :
    StdStatePreserved s0 s2 :=
  ⟨h12.1.trans h01.1,
   h12.2.1.trans h01.2.1,
   h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1,
   h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   fun a => (h12.2.2.2.2.2.2.2 a).trans (h01.2.2.2.2.2.2.2 a)⟩

/-! ## Memory Subroutine Specifications -/

/-- Total-correctness contract for `void *memset(void *dst, int c, size_t len)` preserving
    `StdStatePreserved`. -/
def stdMemsetSpec : Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := fun (dst, byteVal, len) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      (s0.readReg32 .x1).truncate 8 = byteVal ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 len ∧
      len < 2 ^ 64⌝ ∗
    memRegion dst len
  post := fun (dst, byteVal, len) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ StdStatePreserved s0 sf⌝ ∗
    (dst ↦ₛ List.replicate len byteVal)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Total-correctness contract for `void *memcpy(void *dst, const void *src, size_t n)` over a
    read-write source buffer `src ↦ₛ bs`, preserving `StdStatePreserved`. -/
def stdMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
    (memRegion dst bs.length ∗ (src ↦ₛ bs))
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ StdStatePreserved s0 sf⌝ ∗
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Read-only source variant of `stdMemcpySpec` (`src ↦ᵣ bs`), preserving `StdStatePreserved`. -/
def stdMemcpyROSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
    (memRegion dst bs.length ∗ (src ↦ᵣ bs))
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ StdStatePreserved s0 sf⌝ ∗
    ((dst ↦ₛ bs) ∗ (src ↦ᵣ bs))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-! ## Memory-Operations Bundle and Framed Call Helpers -/

/-- Verified `memset` and `memcpy` contracts for a program `P` at link addresses `memcpyAddr` and
    `memsetAddr`. -/
structure StdMemOps (P : Program) (memcpyAddr memsetAddr : BitVec 64) : Prop where
  memset_ok    : subroutine_ok P memsetAddr stdMemsetSpec
  memcpy_ok    : subroutine_ok P memcpyAddr stdMemcpySpec
  memcpy_ro_ok : subroutine_ok P memcpyAddr stdMemcpyROSpec

/-- Step a call to `memsetAddr` inside `SepWP`: pass `(F := ?F) (by sep_frame)` to split
    `memRegion dst len` from `Pre` and continue at `ret_pc` with
    `(dst ↦ₛ List.replicate len byteVal) ∗ F` and `StdStatePreserved s sf`. -/
theorem StdMemOps.call_memset {P : Program} {memcpyAddr memsetAddr target_pc ret_pc : BitVec 64}
    (ops : StdMemOps P memcpyAddr memsetAddr)
    {dst : BitVec 64} {byteVal : BitVec 8} {len : Nat}
    {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ memRegion dst len ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = dst → StdStatePreserved s sf →
      SepWP P target_pc sf ((dst ↦ₛ List.replicate len byteVal) ∗ F) post oom)
    (hpc : s.pc = memsetAddr := by
      simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by
      simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg64 .x0 = dst := by
      simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx1 : (s.readReg32 .x1).truncate 8 = byteVal := by
      simp (config := { decide := true }) only [
        State.readReg32, BitVec.truncate_truncate, Nat.reduceMin, arm64_norm, *]
      try bv_bits)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 len := by
      simp (config := { decide := true }) only [arm64_norm, *]; try bv_arith)
    (hlen : len < 2 ^ 64 := by omega)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ stdMemsetSpec.onOom (dst, byteVal, len) s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame ops.memset_ok (x := (dst, byteVal, len)) (F := F)
    hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ h_oom
  · intro R hm
    dsimp only [stdMemsetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen⟩, hpre R hm⟩
  · intro R' sf _ hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    exact not_satisfies_false_sepConj he
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only [stdMemsetSpec]
    rw [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hx0_f, hstd_f⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hstd_f

/-- Step a call to `memcpyAddr` with read-write source `src ↦ₛ bs` inside `SepWP`: pass
    `(F := ?F) (by sep_frame)` to split `memRegion dst bs.length ∗ (src ↦ₛ bs)` from `Pre`. -/
theorem StdMemOps.call_memcpy {P : Program} {memcpyAddr memsetAddr target_pc ret_pc : BitVec 64}
    (ops : StdMemOps P memcpyAddr memsetAddr)
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = dst → StdStatePreserved s sf →
      SepWP P target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F) post oom)
    (hpc : s.pc = memcpyAddr := by
      simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by
      simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg64 .x0 = dst := by
      simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx1 : s.readReg64 .x1 = src := by
      simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
      simp (config := { decide := true }) only [arm64_norm, *]; try bv_arith)
    (hlen : bs.length < 2 ^ 64 := by omega)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ stdMemcpySpec.onOom (dst, src, bs) s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame ops.memcpy_ok (x := (dst, src, bs)) (F := F)
    hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ h_oom
  · intro R hm
    dsimp only [stdMemcpySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen⟩, hpre R hm⟩
  · intro R' sf _ hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    exact not_satisfies_false_sepConj he
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only [stdMemcpySpec]
    rw [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hx0_f, hstd_f⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hstd_f

/-- Step a call to `memcpyAddr` with read-only source `src ↦ᵣ bs` inside `SepWP`: pass
    `(F := ?F) (by sep_frame)` to split `memRegion dst bs.length ∗ (src ↦ᵣ bs)` from `Pre`. -/
theorem StdMemOps.call_memcpy_ro {P : Program} {memcpyAddr memsetAddr target_pc ret_pc : BitVec 64}
    (ops : StdMemOps P memcpyAddr memsetAddr)
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (memRegion dst bs.length ∗ (src ↦ᵣ bs)) ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = dst → StdStatePreserved s sf →
      SepWP P target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ᵣ bs)) ∗ F) post oom)
    (hpc : s.pc = memcpyAddr := by
      simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by
      simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg64 .x0 = dst := by
      simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx1 : s.readReg64 .x1 = src := by
      simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
      simp (config := { decide := true }) only [arm64_norm, *]; try bv_arith)
    (hlen : bs.length < 2 ^ 64 := by omega)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ stdMemcpyROSpec.onOom (dst, src, bs) s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame ops.memcpy_ro_ok (x := (dst, src, bs)) (F := F)
    hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ h_oom
  · intro R hm
    dsimp only [stdMemcpyROSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen⟩, hpre R hm⟩
  · intro R' sf _ hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    exact not_satisfies_false_sepConj he
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only [stdMemcpyROSpec]
    rw [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hx0_f, hstd_f⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hstd_f

/-! ## PC-Relative Helpers and `WordTree` Matchers -/

open ProofLib.ProgramReflection

/-- Page-delta immediate `(target & ~0xfff) - (pc & ~0xfff)` carried by `Instr.adr true rd offset`. -/
@[inline] def adrpOff (pc target : BitVec 64) : BitVec 64 :=
  (target &&& 0xfffffffffffff000#64) - (pc &&& 0xfffffffffffff000#64)

/-- Low 12-bit page offset `target & 0xfff` carried by `AddrMode.Offset` after `adrp`. -/
@[inline] def pageLo12 (target : BitVec 64) : BitVec 64 :=
  target &&& 0xfff#64

@[simp, arm64_norm] theorem adrp_page_eq (pc target : BitVec 64) :
    (pc &&& 0xfffffffffffff000#64) + adrpOff pc target = target &&& 0xfffffffffffff000#64 := by
  unfold adrpOff; bv_bits

@[simp, arm64_norm] theorem page_add_lo12_eq (target : BitVec 64) :
    (target &&& 0xfffffffffffff000#64) + pageLo12 target = target := by
  unfold pageLo12; bv_bits

@[simp, arm64_norm] theorem page_add_trunc12_eq (target : BitVec 64) :
    (target &&& 0xfffffffffffff000#64) + BitVec.zeroExtend 64 (target.truncate 12) = target := by
  bv_bits

/-- Asserts that `P.fetch` decodes `instrs[i]` at `base + 4 * i` for every `i < instrs.length`. -/
def hasInstrs (P : Program) (base : BitVec 64) (instrs : List Instr) : Prop :=
  ∀ (i : Nat) (hi : i < instrs.length),
    P.fetch (base + BitVec.ofNat 64 (4 * i)) = some (instrs[i]'hi)

theorem hasInstrs.fetch_off {P : Program} {base : BitVec 64} {instrs : List Instr}
    (h : hasInstrs P base instrs) (i : Nat) (off : BitVec 64) {inst : Instr}
    (hi : i < instrs.length := by decide)
    (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl)
    (hinst : instrs[i]'hi = inst := by rfl) :
    P.fetch (base + off) = some inst := by
  rw [← hoff, ← hinst]; exact h i hi

/-- Decidable `O(k log N)` check that `t` decodes to `instrs` starting at byte offset `baseOff`. -/
def checkInstrsAt (t : WordTree) (baseOff : Nat) (instrs : List Instr) : Bool :=
  (List.range instrs.length).all fun i =>
    t.fetchDecodeAt (baseOff + 4 * i) == instrs[i]?

theorem hasInstrs_of_wordTree {P : Program} {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    {base : BitVec 64} {baseOff : Nat} {instrs : List Instr}
    (hbase : P.base + BitVec.ofNat 64 baseOff = base)
    (hbnd : baseOff + 4 * instrs.length < 2 ^ 64)
    (h_ext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (h_ovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkInstrsAt t baseOff instrs = true) :
    hasInstrs P base instrs := by
  intro i hi
  have hmem : i ∈ List.range instrs.length := List.mem_range.mpr hi
  have hall := beq_iff_eq.mp (List.all_eq_true.mp hok i hmem)
  rw [List.getElem?_eq_getElem hi] at hall
  have hf := fetch_of_wordTree n hcode hwf hall (by omega)
    (hookAtOff?_eq_none_of_isNone h_ext h_ovr _)
  have hadd : P.base + BitVec.ofNat 64 (baseOff + 4 * i) = base + BitVec.ofNat 64 (4 * i) := by
    rw [← hbase, BitVec.add_assoc, BitVec.ofNat_add]
  rwa [hadd] at hf

private theorem drop_all_toBytesAux_local :
    ∀ (t : WordTree) {n : Nat} (acc : List (BitVec 8)),
      t.checkSize? = some n → (t.toBytesAux acc).drop (4 * n) = acc
  | .empty, _, acc, h => by simp only [WordTree.checkSize?, Option.some.injEq] at h; subst h; rfl
  | .leaf _ _ _ _, _, acc, h => by simp only [WordTree.checkSize?, Option.some.injEq] at h; subst h; rfl
  | .node lw l r, _, acc, h => by
    simp only [WordTree.checkSize?] at h
    split at h <;> try contradiction
    rename_i nl nr hl hr
    split at h <;> try contradiction
    simp only [Option.some.injEq] at h; subst h
    rw [WordTree.toBytesAux, Nat.mul_add 4 nl nr, ← List.drop_drop,
        drop_all_toBytesAux_local l _ hl, drop_all_toBytesAux_local r _ hr]

private theorem getQuad?_drop_toBytesAux_local {b0 b1 b2 b3 : BitVec 8} :
    ∀ (t : WordTree) {n : Nat} (acc : List (BitVec 8)) (j : Nat),
      t.checkSize? = some n → t.getQuad? j = some (b0, b1, b2, b3) →
      ∃ rest, (t.toBytesAux acc).drop (4 * j) = b0 :: b1 :: b2 :: b3 :: rest
  | .empty, _, _, _, _, hget => by simp [WordTree.getQuad?] at hget
  | .leaf _ _ _ _, _, acc, 0, _, hget => by
    simp only [WordTree.getQuad?, Option.some.injEq, Prod.mk.injEq] at hget
    rcases hget with ⟨rfl, rfl, ⟨rfl, rfl⟩⟩; exact ⟨acc, rfl⟩
  | .leaf _ _ _ _, _, _, _ + 1, _, hget => by simp [WordTree.getQuad?] at hget
  | .node lw l r, _, acc, j, hsz, hget => by
    simp only [WordTree.checkSize?] at hsz
    split at hsz <;> try contradiction
    rename_i nl nr hl hr
    split at hsz <;> try contradiction
    rename_i hlw; have hlw_eq : lw = nl := beq_iff_eq.mp hlw; subst hlw_eq
    simp only [WordTree.getQuad?] at hget; split at hget
    · exact getQuad?_drop_toBytesAux_local l _ j hl hget
    · rw [WordTree.toBytesAux, show 4 * j = 4 * lw + 4 * (j - lw) by omega, ← List.drop_drop,
          drop_all_toBytesAux_local l _ hl]
      exact getQuad?_drop_toBytesAux_local r acc (j - lw) hr hget

/-- Decidable `O(k log N)` check that `t` contains raw 32-bit `words` starting at `baseOff`. -/
def checkWordsAt (t : WordTree) (baseOff : Nat) (words : List (BitVec 32)) : Bool :=
  baseOff % 4 == 0 &&
  (List.range words.length).all fun i =>
    match t.getQuad? (baseOff / 4 + i), words[i]? with
    | some (b0, b1, b2, b3), some w => (b3 ++ b2 ++ b1 ++ b0) == w
    | _, _ => false

theorem hasWords_of_wordTree {P : Program} {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    {addr : BitVec 64} {baseOff : Nat} {words : List (BitVec 32)}
    (hoff : (addr - P.base).toNat = baseOff)
    (hbnd : baseOff + 4 * words.length ≤ 2 ^ 64)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hok : checkWordsAt t baseOff words = true) :
    P.hasWords addr words := by
  unfold Program.hasWords Program.hasWordsOff; rw [hoff]
  unfold checkWordsAt at hok; simp only [Bool.and_eq_true, beq_iff_eq] at hok
  rcases hok with ⟨hal, hall⟩
  refine ⟨hbnd, fun i hi => ?_, by simp [Program.hookFree, hstubs, hsyms]⟩
  have hm := List.all_eq_true.mp hall i (List.mem_range.mpr hi)
  rw [List.getElem?_eq_getElem hi] at hm
  split at hm <;> try contradiction
  rename_i b0 b1 b2 b3 w hget hweq
  cases Option.some.inj hweq
  have hw := beq_iff_eq.mp hm
  rcases getQuad?_drop_toBytesAux_local t [] (baseOff / 4 + i) hwf hget with ⟨rest, hdrop⟩
  unfold Program.readWordOff
  have hmul : baseOff + 4 * i = 4 * (baseOff / 4 + i) := by omega
  have hmod : ¬(4 * (baseOff / 4 + i) % 4 ≠ 0) := by omega
  simp only [hmul, hmod, ↓reduceIte, hcode, WordTree.toBytes, hdrop, hw]

/-! ## Outline-Atomics Specifications and Framed Call Helpers -/

/-- Contract for `__rust_enable_lse()`: writes `1#8` to `haveLseAddr` and preserves
    `StdStatePreserved`. -/
def stdRustEnableLseSpec (haveLseAddr : BitVec 64) : Spec (BitVec 8) where
  pre := fun oldVal _ => haveLseAddr ↦₈ oldVal
  post := fun _ s0 sf => ⌜StdStatePreserved s0 sf⌝ ∗ (haveLseAddr ↦₈ 1#8)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Contract for 64-bit outline CAS (`__aarch64_cas8_relax` / `__aarch64_cas8_acq`) reading
    `haveLseAddr ↦₈ᵣ haveLse` under arbitrary `exclFails` (`x0 = exp`, `x1 = new`, `x2 = ptr`). -/
def stdCas8Spec (haveLseAddr : BitVec 64) : Spec (BitVec 8 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (haveLse, ptr, v0, exp, new) s0 =>
    ⌜s0.readReg64 .x0 = exp ∧ s0.readReg64 .x1 = new ∧ s0.readReg64 .x2 = ptr ∧
      MemWidth.isAligned .X64 ptr = true⌝ ∗
    ((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₆₄ v0))
  post := fun (haveLse, ptr, v0, exp, new) s0 sf =>
    ⌜sf.readReg64 .x0 = v0 ∧ StdStatePreserved s0 sf⌝ ∗
    ((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₆₄ (if v0 == exp then new else v0)))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Contract for 32-bit outline CAS (`__aarch64_cas4_acq`) reading `haveLseAddr ↦₈ᵣ haveLse`
    under arbitrary `exclFails` (`w0 = exp`, `w1 = new`, `x2 = ptr`). -/
def stdCas4Spec (haveLseAddr : BitVec 64) : Spec (BitVec 8 × BitVec 64 × BitVec 32 × BitVec 32 × BitVec 32) where
  pre := fun (haveLse, ptr, v0, exp, new) s0 =>
    ⌜s0.readReg32 .x0 = exp ∧ s0.readReg32 .x1 = new ∧ s0.readReg64 .x2 = ptr ∧
      MemWidth.isAligned .W32 ptr = true⌝ ∗
    ((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₃₂ v0))
  post := fun (haveLse, ptr, v0, exp, new) s0 sf =>
    ⌜sf.readReg64 .x0 = v0.zeroExtend 64 ∧ StdStatePreserved s0 sf⌝ ∗
    ((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₃₂ (if v0 == exp then new else v0)))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Contract for 32-bit outline atomic swap (`__aarch64_swp4_rel`) reading
    `haveLseAddr ↦₈ᵣ haveLse` under arbitrary `exclFails` (`w0 = new`, `x1 = ptr`). -/
def stdSwp4Spec (haveLseAddr : BitVec 64) : Spec (BitVec 8 × BitVec 64 × BitVec 32 × BitVec 32) where
  pre := fun (haveLse, ptr, v0, new) s0 =>
    ⌜s0.readReg32 .x0 = new ∧ s0.readReg64 .x1 = ptr ∧ MemWidth.isAligned .W32 ptr = true⌝ ∗
    ((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₃₂ v0))
  post := fun (haveLse, ptr, v0, new) s0 sf =>
    ⌜sf.readReg64 .x0 = v0.zeroExtend 64 ∧ StdStatePreserved s0 sf⌝ ∗
    ((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₃₂ new))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Bundle of verified AArch64 outline-atomics subroutine contracts for `P`. -/
structure StdOutlineAtomics (P : Program)
    (haveLseAddr cas8RelaxAddr cas4AcqAddr cas8AcqAddr swp4RelAddr : BitVec 64) : Prop where
  cas8Relax_ok : subroutine_ok P cas8RelaxAddr (stdCas8Spec haveLseAddr)
  cas4Acq_ok   : subroutine_ok P cas4AcqAddr (stdCas4Spec haveLseAddr)
  cas8Acq_ok   : subroutine_ok P cas8AcqAddr (stdCas8Spec haveLseAddr)
  swp4Rel_ok   : subroutine_ok P swp4RelAddr (stdSwp4Spec haveLseAddr)

theorem call_stdCas8 {P : Program} {fnAddr haveLseAddr target_pc ret_pc : BitVec 64}
    (hok : subroutine_ok P fnAddr (stdCas8Spec haveLseAddr))
    {haveLse : BitVec 8} {ptr v0 exp new : BitVec 64}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₆₄ v0)) ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → sf.readReg64 .x0 = v0 → StdStatePreserved s sf →
      SepWP P target_pc sf (((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₆₄ (if v0 == exp then new else v0))) ∗ F) post oom)
    (hpc : s.pc = fnAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg64 .x0 = exp := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx1 : s.readReg64 .x1 = new := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx2 : s.readReg64 .x2 = ptr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (halign : MemWidth.isAligned .X64 ptr = true)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (stdCas8Spec haveLseAddr).onOom (haveLse, ptr, v0, exp, new) s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame hok (x := (haveLse, ptr, v0, exp, new)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm; dsimp only [stdCas8Spec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, halign⟩, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [stdCas8Spec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_f, hstd_f⟩; exact hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hstd_f

theorem call_stdCas4 {P : Program} {fnAddr haveLseAddr target_pc ret_pc : BitVec 64}
    (hok : subroutine_ok P fnAddr (stdCas4Spec haveLseAddr))
    {haveLse : BitVec 8} {ptr : BitVec 64} {v0 exp new : BitVec 32}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₃₂ v0)) ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = v0.zeroExtend 64 → StdStatePreserved s sf →
      SepWP P target_pc sf (((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₃₂ (if v0 == exp then new else v0))) ∗ F) post oom)
    (hpc : s.pc = fnAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg32 .x0 = exp := by simp (config := { decide := true }) only [State.readReg32, arm64_norm, *]; try bv_bits)
    (hx1 : s.readReg32 .x1 = new := by simp (config := { decide := true }) only [State.readReg32, arm64_norm, *]; try bv_bits)
    (hx2 : s.readReg64 .x2 = ptr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (halign : MemWidth.isAligned .W32 ptr = true)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (stdCas4Spec haveLseAddr).onOom (haveLse, ptr, v0, exp, new) s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame hok (x := (haveLse, ptr, v0, exp, new)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm; dsimp only [stdCas4Spec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, halign⟩, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [stdCas4Spec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_f, hstd_f⟩; exact hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hstd_f

theorem call_stdSwp4 {P : Program} {fnAddr haveLseAddr target_pc ret_pc : BitVec 64}
    (hok : subroutine_ok P fnAddr (stdSwp4Spec haveLseAddr))
    {haveLse : BitVec 8} {ptr : BitVec 64} {v0 new : BitVec 32}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₃₂ v0)) ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = v0.zeroExtend 64 → StdStatePreserved s sf →
      SepWP P target_pc sf (((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₃₂ new)) ∗ F) post oom)
    (hpc : s.pc = fnAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg32 .x0 = new := by simp (config := { decide := true }) only [State.readReg32, arm64_norm, *]; try bv_bits)
    (hx1 : s.readReg64 .x1 = ptr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (halign : MemWidth.isAligned .W32 ptr = true)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (stdSwp4Spec haveLseAddr).onOom (haveLse, ptr, v0, new) s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame hok (x := (haveLse, ptr, v0, new)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm; dsimp only [stdSwp4Spec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, halign⟩, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [stdSwp4Spec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_f, hstd_f⟩; exact hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hstd_f

end ProofLib.StdStartup
