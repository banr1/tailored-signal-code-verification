/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.CoreLemmas
public import ProofLib.Invariant
public import ProofLib.BV.Arith

/-!
# Sanitized `mmap`, `mremap`, `ppoll`, and Signal Syscall Lemmas

Soundness and completeness lemmas for `findMappedByte`, `findUnmappedArea`, and `sanitizeMmapAddr`,
together with symbolic step equations for `execMmap`, `execMremap`, `execPpoll`,
`execSigaltstack`, and `execRtSigaction`.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib

open Arm64

/-! ## `pageAlignUp` Arithmetic Helpers -/

theorem pageAlignUp_pos_of_ne_zero {n : Nat} (h : n ≠ 0) : 0 < pageAlignUp n := by
  unfold pageAlignUp PAGE_SIZE
  omega

theorem pageAlignUp_mod_pageSize (n : Nat) : pageAlignUp n % PAGE_SIZE = 0 := by
  unfold pageAlignUp PAGE_SIZE
  omega

/-! ## `findMappedByte`, `findUnmappedArea`, and `sanitizeMmapAddr` -/

/-- `findMappedByte m base curOff rem = none` iff every byte in
    `[base + curOff, base + curOff + rem)` is unmapped. -/
theorem findMappedByte_none_iff (m : Memory) (base : BitVec 64) (curOff rem : Nat) :
    findMappedByte m base curOff rem = none ↔
      ∀ k < rem, (m.perm (base + BitVec.ofNat 64 (curOff + k))).mapped = false := by
  induction rem generalizing curOff with
  | zero =>
    simp [findMappedByte]
  | succ rem ih =>
    unfold findMappedByte
    cases hm : (m.perm (base + BitVec.ofNat 64 curOff)).mapped
    · simp only [Bool.false_eq_true, ↓reduceIte, ih (curOff + 1)]
      constructor
      · intro h k hk
        cases k with
        | zero => simpa using hm
        | succ k' =>
          have hk' := h k' (by omega)
          have hadd : curOff + 1 + k' = curOff + (k' + 1) := by omega
          simpa [hadd] using hk'
      · intro h k hk
        have hk' := h (k + 1) (by omega)
        have hadd : curOff + (k + 1) = curOff + 1 + k := by omega
        simpa [hadd] using hk'
    · simp only [↓reduceIte, reduceCtorEq, false_iff]
      intro h
      have h0 := h 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [hm] at h0
      exact Bool.noConfusion h0

/-- If `findMappedByte m base 0 size = none`, then `m.canMap base size = true`. -/
theorem canMap_of_findMappedByte_none {m : Memory} {base : BitVec 64} {size : Nat}
    (h : findMappedByte m base 0 size = none) :
    m.canMap base size = true := by
  unfold Memory.canMap
  rw [Memory.allPerm_iff]
  intro i hi
  have hi' := (findMappedByte_none_iff m base 0 size).1 h i hi
  simpa using hi'

/-- If `findMappedByte m base curOff rem = some off`, then `off ∈ [curOff, curOff + rem)` and byte
    `base + off` is mapped in `m`. -/
theorem findMappedByte_some {m : Memory} {base : BitVec 64} {curOff rem off : Nat}
    (h : findMappedByte m base curOff rem = some off) :
    curOff ≤ off ∧ off < curOff + rem ∧ (m.perm (base + BitVec.ofNat 64 off)).mapped = true := by
  induction rem generalizing curOff with
  | zero =>
    simp [findMappedByte] at h
  | succ rem ih =>
    unfold findMappedByte at h
    cases hm : (m.perm (base + BitVec.ofNat 64 curOff)).mapped
    · rw [hm] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hlo, hhi, hmap⟩ := ih h
      exact ⟨by omega, by omega, hmap⟩
    · rw [hm] at h
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨by omega, by omega, hm⟩

private theorem findUnmappedAreaLoop_spec {m : Memory} {size fuel addr : Nat} {base : BitVec 64}
    (hmin : MMAP_MIN_ADDR ≤ addr)
    (hal : addr % PAGE_SIZE = 0)
    (h : findUnmappedAreaLoop m size fuel addr = some base) :
    MMAP_MIN_ADDR ≤ base.toNat ∧
    base ≠ 0#64 ∧
    base.toNat % PAGE_SIZE = 0 ∧
    base.toNat + size ≤ USER_VA_LIMIT ∧
    m.canMap base size = true := by
  induction fuel generalizing addr with
  | zero =>
    simp [findUnmappedAreaLoop] at h
  | succ fuel ih =>
    unfold findUnmappedAreaLoop at h
    split at h
    · simp at h
    · rename_i hfit_neg
      have hfit : addr + size ≤ USER_VA_LIMIT := by simpa using hfit_neg
      have hlt64 : addr < 2 ^ 64 := by
        unfold USER_VA_LIMIT at hfit; omega
      have htoNat : (BitVec.ofNat 64 addr).toNat = addr := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
      dsimp (config := { zetaHave := true }) only at h
      cases hfb : findMappedByte m (BitVec.ofNat 64 addr) 0 size
      · rw [hfb] at h
        simp only [Option.some.injEq] at h
        subst h
        have hne : BitVec.ofNat 64 addr ≠ 0#64 := by
          intro hz
          have hz' := congrArg BitVec.toNat hz
          rw [htoNat] at hz'
          unfold MMAP_MIN_ADDR at hmin
          simp at hz'
          omega
        exact ⟨by rw [htoNat]; exact hmin, hne, by rw [htoNat]; exact hal,
          by rw [htoNat]; exact hfit, canMap_of_findMappedByte_none hfb⟩
      · rename_i off
        rw [hfb] at h
        dsimp (config := { zetaHave := true }) only at h
        apply ih _ _ h
        · unfold PAGE_SIZE; omega
        · unfold PAGE_SIZE; omega

/-- Every address returned by `findUnmappedArea m size = some base` lies at or above
    `MMAP_MIN_ADDR`, is non-null and page-aligned, fits in `[0, USER_VA_LIMIT]`, and is completely
    unmapped across `[base, base + size)`. -/
theorem findUnmappedArea_spec {m : Memory} {size : Nat} {base : BitVec 64}
    (h : findUnmappedArea m size = some base) :
    MMAP_MIN_ADDR ≤ base.toNat ∧
    base ≠ 0#64 ∧
    base.toNat % PAGE_SIZE = 0 ∧
    base.toNat + size ≤ USER_VA_LIMIT ∧
    m.canMap base size = true := by
  unfold findUnmappedArea at h
  split at h
  · simp at h
  · exact findUnmappedAreaLoop_spec (Nat.le_refl _) (by decide) h

/-- For every oracle candidate `cand`, `sanitizeMmapAddr m cand size = some base` implies
    `MMAP_MIN_ADDR ≤ base.toNat`. -/
theorem sanitizeMmapAddr_min {m : Memory} {cand : BitVec 64} {size : Nat} {base : BitVec 64}
    (h : sanitizeMmapAddr m cand size = some base) :
    MMAP_MIN_ADDR ≤ base.toNat := by
  unfold sanitizeMmapAddr at h
  split at h
  · simp at h
  · split at h
    · rename_i hcand
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcand
      exact hcand.1.1.1
    · exact (findUnmappedArea_spec h).1

/-- For every oracle candidate `cand`, `sanitizeMmapAddr m cand size = some base` implies that
    `base` is non-null, page-aligned, fits within `USER_VA_LIMIT`, and satisfies
    `m.canMap base size = true`. -/
theorem sanitizeMmapAddr_spec {m : Memory} {cand : BitVec 64} {size : Nat} {base : BitVec 64}
    (h : sanitizeMmapAddr m cand size = some base) :
    base ≠ 0#64 ∧
    base.toNat % PAGE_SIZE = 0 ∧
    base.toNat + size ≤ USER_VA_LIMIT ∧
    m.canMap base size = true := by
  unfold sanitizeMmapAddr at h
  split at h
  · simp at h
  · split at h
    · rename_i hcand
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcand
      have hne : cand ≠ 0#64 := by
        intro h0; subst h0; have := hcand.1.1.1; unfold MMAP_MIN_ADDR at this; contradiction
      exact ⟨hne, hcand.1.1.2, hcand.1.2, hcand.2⟩
    · obtain ⟨_, hne, hal, hfit, hmap⟩ := findUnmappedArea_spec h
      exact ⟨hne, hal, hfit, hmap⟩

/-- When `cand` already satisfies all placement invariants for a positive page-aligned `size`,
    `sanitizeMmapAddr m cand size` accepts `cand` directly. -/
theorem sanitizeMmapAddr_eq_some_of_valid {m : Memory} {cand : BitVec 64} {size : Nat}
    (hsz0 : size ≠ 0)
    (hszAl : size % PAGE_SIZE = 0)
    (hmin : MMAP_MIN_ADDR ≤ cand.toNat)
    (hal : cand.toNat % PAGE_SIZE = 0)
    (hfit : cand.toNat + size ≤ USER_VA_LIMIT)
    (hmap : m.canMap cand size = true) :
    sanitizeMmapAddr m cand size = some cand := by
  unfold sanitizeMmapAddr
  simp [hsz0, hszAl, hmin, hal, hfit, hmap]

private theorem findUnmappedAreaLoop_isSome_of_gap {m : Memory} {size fuel curAddr : Nat}
    {gap : BitVec 64}
    (hcurLe : curAddr ≤ gap.toNat)
    (hcurAl : curAddr % PAGE_SIZE = 0)
    (hgapAl : gap.toNat % PAGE_SIZE = 0)
    (hfit : gap.toNat + size ≤ USER_VA_LIMIT)
    (hmap : m.canMap gap size = true)
    (hfuel : (gap.toNat - curAddr) / PAGE_SIZE < fuel) :
    (findUnmappedAreaLoop m size fuel curAddr).isSome = true := by
  induction fuel generalizing curAddr with
  | zero => exact absurd hfuel (Nat.not_lt_zero _)
  | succ fuel ih =>
    unfold findUnmappedAreaLoop
    have hcurDec : decide (curAddr + size ≤ USER_VA_LIMIT) = true :=
      decide_eq_true (by omega)
    simp (config := { zetaHave := true }) only [hcurDec, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hfb : findMappedByte m (BitVec.ofNat 64 curAddr) 0 size with
    | none => rfl
    | some off =>
      dsimp (config := { zetaHave := true }) only
      obtain ⟨_, hoffLt, hoffMap⟩ := findMappedByte_some hfb
      have hoffBeforeGap : curAddr + off < gap.toNat := by
        by_cases hlt : curAddr + off < gap.toNat
        · exact hlt
        · exfalso
          have hge : gap.toNat ≤ curAddr + off := by omega
          let j := curAddr + off - gap.toNat
          have hjLt : j < size := by omega
          have hlt64_cur : curAddr < 2 ^ 64 := by unfold USER_VA_LIMIT at hfit; omega
          have hlt64_off : off < 2 ^ 64 := by unfold USER_VA_LIMIT at hfit; omega
          have hlt64_j : j < 2 ^ 64 := by unfold USER_VA_LIMIT at hfit; omega
          have hlt64_sum : curAddr + off < 2 ^ 64 := by unfold USER_VA_LIMIT at hfit; omega
          have haddrEq : BitVec.ofNat 64 curAddr + BitVec.ofNat 64 off = gap + BitVec.ofNat 64 j := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hlt64_cur, Nat.mod_eq_of_lt hlt64_off, Nat.mod_eq_of_lt hlt64_j]
            have hgj : gap.toNat + j = curAddr + off := by omega
            rw [hgj, Nat.mod_eq_of_lt hlt64_sum]
          unfold Memory.canMap at hmap
          rw [Memory.allPerm_iff] at hmap
          have hunmap := hmap j hjLt
          rw [haddrEq] at hoffMap
          rw [hoffMap] at hunmap
          exact Bool.noConfusion hunmap
      apply ih
      · unfold PAGE_SIZE at *; omega
      · unfold PAGE_SIZE; omega
      · unfold PAGE_SIZE at *; omega

/-- Completeness of `findUnmappedArea`: whenever `[MMAP_MIN_ADDR, USER_VA_LIMIT)` contains at least
    one page-aligned unmapped region `gap` of positive page-aligned length `size`,
    `findUnmappedArea m size` succeeds (`isSome = true`). -/
theorem findUnmappedArea_isSome_of_gap {m : Memory} {size : Nat} {gap : BitVec 64}
    (hpos : 0 < size)
    (hal : size % PAGE_SIZE = 0)
    (hmin : MMAP_MIN_ADDR ≤ gap.toNat)
    (hgapAl : gap.toNat % PAGE_SIZE = 0)
    (hfit : gap.toNat + size ≤ USER_VA_LIMIT)
    (hmap : m.canMap gap size = true) :
    (findUnmappedArea m size).isSome = true := by
  unfold findUnmappedArea
  have hguard : (size == 0 || size % PAGE_SIZE != 0) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]
    exact ⟨by omega, hal⟩
  rw [hguard]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply findUnmappedAreaLoop_isSome_of_gap hmin (by decide) hgapAl hfit hmap
  unfold PAGE_SIZE MMAP_MIN_ADDR USER_VA_LIMIT at *
  omega

/-- Completeness of `sanitizeMmapAddr`: for every oracle hint `cand`, if a valid unmapped gap
    exists in `[MMAP_MIN_ADDR, USER_VA_LIMIT)`, `sanitizeMmapAddr m cand size` succeeds. -/
theorem sanitizeMmapAddr_isSome_of_gap {m : Memory} (cand : BitVec 64) {size : Nat}
    {gap : BitVec 64}
    (hpos : 0 < size)
    (hal : size % PAGE_SIZE = 0)
    (hmin : MMAP_MIN_ADDR ≤ gap.toNat)
    (hgapAl : gap.toNat % PAGE_SIZE = 0)
    (hfit : gap.toNat + size ≤ USER_VA_LIMIT)
    (hmap : m.canMap gap size = true) :
    (sanitizeMmapAddr m cand size).isSome = true := by
  unfold sanitizeMmapAddr
  have hguard : (size == 0 || size % PAGE_SIZE != 0) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]
    exact ⟨by omega, hal⟩
  rw [hguard]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  · exact findUnmappedArea_isSome_of_gap hpos hal hmin hgapAl hfit hmap

/-- Existential form of `sanitizeMmapAddr_isSome_of_gap`: for every oracle hint `cand`, a free
    page-aligned gap in `[MMAP_MIN_ADDR, USER_VA_LIMIT)` yields `∃ base, sanitizeMmapAddr m cand size = some base`. -/
theorem sanitizeMmapAddr_exists_of_gap {m : Memory} (cand : BitVec 64) {size : Nat}
    {gap : BitVec 64}
    (hpos : 0 < size)
    (hal : size % PAGE_SIZE = 0)
    (hmin : MMAP_MIN_ADDR ≤ gap.toNat)
    (hgapAl : gap.toNat % PAGE_SIZE = 0)
    (hfit : gap.toNat + size ≤ USER_VA_LIMIT)
    (hmap : m.canMap gap size = true) :
    ∃ base, sanitizeMmapAddr m cand size = some base :=
  Option.isSome_iff_exists.mp (sanitizeMmapAddr_isSome_of_gap cand hpos hal hmin hgapAl hfit hmap)

/-! ## Sanitized `execMmap`, `execMremap`, `execPpoll`, and `execRtSigaction` -/

/-- Anonymous `PROT_READ | PROT_WRITE` `mmap` (`flags ∈ {0x22, 0x20022}`) when `sanitizeMmapAddr`
    resolves to `some base` and `pageAlignUp len ≤ s.physMemAvail`: maps
    `[base, base + pageAlignUp len)` zero-filled as `Perm.rw`, deducts `pageAlignUp len` from
    `s.physMemAvail`, advances the oracle and `PC`, writes `base` to `X0`, and preserves `s.status`
    (never transitioning to `.OutOfMemory`). -/
theorem execMmap_anon_sanitized_ok (s : State) {base : BitVec 64}
    (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64 ∨ s.readReg64 .x3 = 0x20022#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : s.readReg64 .x1 ≠ 0#64)
    (hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) = some base)
    (hphys : pageAlignUp (s.readReg64 .x1).toNat ≤ s.physMemAvail) :
    execMmap s =
      ((((s.setMem (s.mem.mapZero base
          (pageAlignUp (s.readReg64 .x1).toNat))).setPhysMemAvail
          (s.physMemAvail - pageAlignUp (s.readReg64 .x1).toNat)).nextOracle).writeReg64
        .x0 base).advancePC := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  dsimp (config := { zetaHave := true }) only [execMmap]
  rcases hflags with hf | hf <;>
    simp [MMAP_PROT_RW, MMAP_PROT_NONE, MMAP_FLAGS_PRIVATE_ANON, MMAP_FLAGS_PRIVATE_ANON_STACK,
      MMAP_FLAGS_PRIVATE_ANON_FIXED, hprot, hf, hoff, hlen', hsan, hphys]

/-- Anonymous `PROT_READ | PROT_WRITE` `mmap` when `sanitizeMmapAddr` resolves to `some base`
    and `pageAlignUp len ≤ s.physMemAvail`: maps `[base, base + pageAlignUp len)` zero-filled as
    `Perm.rw`, deducts `pageAlignUp len` from `s.physMemAvail`, advances the oracle and `PC`,
    writes `base` to `X0`, and preserves `s.status` (never transitioning to `.OutOfMemory`). -/
theorem execMmap_sanitized_ok (s : State) {base : BitVec 64}
    (hprot : s.readReg64 .x2 = 3#64) (hflags : s.readReg64 .x3 = 0x22#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : s.readReg64 .x1 ≠ 0#64)
    (hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) = some base)
    (hphys : pageAlignUp (s.readReg64 .x1).toNat ≤ s.physMemAvail) :
    execMmap s =
      ((((s.setMem (s.mem.mapZero base
          (pageAlignUp (s.readReg64 .x1).toNat))).setPhysMemAvail
          (s.physMemAvail - pageAlignUp (s.readReg64 .x1).toNat)).nextOracle).writeReg64
        .x0 base).advancePC :=
  execMmap_anon_sanitized_ok s hprot (Or.inl hflags) hoff hlen hsan hphys

/-- Anonymous `PROT_READ | PROT_WRITE` `mmap` (`flags ∈ {0x22, 0x20022}`) when `sanitizeMmapAddr`
    resolves to `some base` but `s.physMemAvail < pageAlignUp len`: transitions to
    `ExecStatus.OutOfMemory`. -/
theorem execMmap_anon_sanitized_oom (s : State) {base : BitVec 64}
    (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64 ∨ s.readReg64 .x3 = 0x20022#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : s.readReg64 .x1 ≠ 0#64)
    (hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) = some base)
    (hphys : ¬ pageAlignUp (s.readReg64 .x1).toNat ≤ s.physMemAvail) :
    execMmap s = s.setStatus .OutOfMemory := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  dsimp (config := { zetaHave := true }) only [execMmap]
  rcases hflags with hf | hf <;>
    simp [MMAP_PROT_RW, MMAP_PROT_NONE, MMAP_FLAGS_PRIVATE_ANON, MMAP_FLAGS_PRIVATE_ANON_STACK,
      MMAP_FLAGS_PRIVATE_ANON_FIXED, hprot, hf, hoff, hlen', hsan, hphys]

/-- Anonymous `PROT_READ | PROT_WRITE` `mmap` when `sanitizeMmapAddr` resolves to `some base`
    but `s.physMemAvail < pageAlignUp len`: transitions to `ExecStatus.OutOfMemory`. -/
theorem execMmap_sanitized_oom (s : State) {base : BitVec 64}
    (hprot : s.readReg64 .x2 = 3#64) (hflags : s.readReg64 .x3 = 0x22#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : s.readReg64 .x1 ≠ 0#64)
    (hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) = some base)
    (hphys : ¬ pageAlignUp (s.readReg64 .x1).toNat ≤ s.physMemAvail) :
    execMmap s = s.setStatus .OutOfMemory :=
  execMmap_anon_sanitized_oom s hprot (Or.inl hflags) hoff hlen hsan hphys

/-- Anonymous non-`MAP_FIXED` `PROT_NONE` `mmap` (`flags ∈ {0x22, 0x20022}`) when
    `sanitizeMmapAddr` resolves to `some base`: maps `[base, base + pageAlignUp len)` zero-filled
    with `Perm.protNone`, advances the oracle and `PC`, and writes `base` to `X0`. -/
theorem execMmap_anon_protNone_sanitized_ok (s : State) {base : BitVec 64}
    (hprot : s.readReg64 .x2 = 0#64)
    (hflags : s.readReg64 .x3 = 0x22#64 ∨ s.readReg64 .x3 = 0x20022#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : s.readReg64 .x1 ≠ 0#64)
    (hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) = some base) :
    execMmap s =
      (((s.setMem ((s.mem.mapZero base
          (pageAlignUp (s.readReg64 .x1).toNat)).setPermNonFrozen base
          (pageAlignUp (s.readReg64 .x1).toNat) Perm.protNone)).nextOracle).writeReg64
        .x0 base).advancePC := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  dsimp (config := { zetaHave := true }) only [execMmap]
  rcases hflags with hf | hf <;>
    simp [MMAP_PROT_RW, MMAP_PROT_NONE, MMAP_FLAGS_PRIVATE_ANON, MMAP_FLAGS_PRIVATE_ANON_STACK,
      MMAP_FLAGS_PRIVATE_ANON_FIXED, hprot, hf, hoff, hlen', hsan]

/-- Anonymous non-`MAP_FIXED` `PROT_NONE` `mmap` when `sanitizeMmapAddr` resolves to `some base`:
    maps `[base, base + pageAlignUp len)` zero-filled with `Perm.protNone`, advances the oracle
    and `PC`, and writes `base` to `X0`. -/
theorem execMmap_protNone_sanitized_ok (s : State) {base : BitVec 64}
    (hprot : s.readReg64 .x2 = 0#64) (hflags : s.readReg64 .x3 = 0x22#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : s.readReg64 .x1 ≠ 0#64)
    (hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) = some base) :
    execMmap s =
      (((s.setMem ((s.mem.mapZero base
          (pageAlignUp (s.readReg64 .x1).toNat)).setPermNonFrozen base
          (pageAlignUp (s.readReg64 .x1).toNat) Perm.protNone)).nextOracle).writeReg64
        .x0 base).advancePC :=
  execMmap_anon_protNone_sanitized_ok s hprot (Or.inl hflags) hoff hlen hsan

private theorem allPerm_not_frozen_of_allPerm_rw {m : Memory} {base : BitVec 64} {size : Nat}
    (h : m.allPerm (fun p => p == some Perm.rw) base size = true) :
    m.allPerm (fun p => !p.frozen) base size = true := by
  rw [Memory.allPerm_iff] at h ⊢
  intro i hi
  have hi' := eq_of_beq (h i hi)
  rw [hi']
  rfl

private theorem canMap_eq_false_of_allPerm_rw_pos {m : Memory} {base : BitVec 64} {size : Nat}
    (hpos : 0 < size)
    (h : m.allPerm (fun p => p == some Perm.rw) base size = true) :
    m.canMap base size = false := by
  unfold Memory.canMap
  rw [Bool.eq_false_iff]
  intro hcm
  rw [Memory.allPerm_iff] at h hcm
  have h0 := eq_of_beq (h 0 hpos)
  have hm0 := hcm 0 hpos
  rw [h0] at hm0
  exact Bool.noConfusion hm0

/-- Successful `mremap(oldAddr, oldLen, newLen, MREMAP_MAYMOVE)` when `mremapFail = false`,
    `sanitizeMmapAddr` on the unmapped source memory returns `some newBase`, and
    `pageAlignUp newLen ≤ s.physMemAvail + pageAlignUp oldLen`. -/
theorem execMremap_ok (s : State) {newBase : BitVec 64}
    (hflags : s.readReg64 .x3 = MREMAP_MAYMOVE)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (holdLen : s.readReg64 .x1 ≠ 0#64)
    (hnewLen : s.readReg64 .x2 ≠ 0#64)
    (hnewMax : (s.readReg64 .x2).toNat ≤ 2 ^ 64 - PAGE_SIZE)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ USER_VA_LIMIT)
    (hperm : s.mem.allPerm (fun p => p == some Perm.rw) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hanon : s.mem.allAnon (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hnoFail : s.oracle.mremapFail s.oracleIdx = false)
    (hsan : sanitizeMmapAddr
      (s.mem.unmapNonFrozen (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat))
      (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x2).toNat) = some newBase)
    (hphys : pageAlignUp (s.readReg64 .x2).toNat ≤
      s.physMemAvail + pageAlignUp (s.readReg64 .x1).toNat) :
    execMremap s =
      ((((s.setMem (s.mem.remapRw (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat)
          newBase (pageAlignUp (s.readReg64 .x2).toNat))).setPhysMemAvail
          (s.physMemAvail + pageAlignUp (s.readReg64 .x1).toNat -
            pageAlignUp (s.readReg64 .x2).toNat)).nextOracle).writeReg64
        .x0 newBase).advancePC := by
  have holdLen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact holdLen (BitVec.eq_of_toNat_eq (by simpa using h))
  have hnewLen' : (s.readReg64 .x2).toNat ≠ 0 := by
    intro h; exact hnewLen (BitVec.eq_of_toNat_eq (by simpa using h))
  have hnewNotGt : ¬((s.readReg64 .x2).toNat > 2 ^ 64 - PAGE_SIZE) := by omega
  have hfitNotGt : ¬((s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat > USER_VA_LIMIT) := by
    omega
  have hfrz := allPerm_not_frozen_of_allPerm_rw hperm
  have hcm := canMap_eq_false_of_allPerm_rw_pos (pageAlignUp_pos_of_ne_zero holdLen') hperm
  dsimp (config := { zetaHave := true }) only [execMremap]
  simp [hflags, hal, holdLen', hnewLen', hnewNotGt, hfitNotGt, hfrz, hcm, hanon, hperm, hnoFail, hsan, hphys]

/-- `mremap(oldAddr, oldLen, newLen, MREMAP_MAYMOVE)` when `mremapFail = false`,
    `sanitizeMmapAddr` returns `some newBase`, and
    `¬ pageAlignUp newLen ≤ s.physMemAvail + pageAlignUp oldLen` transitions to
    `ExecStatus.OutOfMemory`. -/
theorem execMremap_oom (s : State) {newBase : BitVec 64}
    (hflags : s.readReg64 .x3 = MREMAP_MAYMOVE)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (holdLen : s.readReg64 .x1 ≠ 0#64)
    (hnewLen : s.readReg64 .x2 ≠ 0#64)
    (hnewMax : (s.readReg64 .x2).toNat ≤ 2 ^ 64 - PAGE_SIZE)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ USER_VA_LIMIT)
    (hperm : s.mem.allPerm (fun p => p == some Perm.rw) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hanon : s.mem.allAnon (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hnoFail : s.oracle.mremapFail s.oracleIdx = false)
    (hsan : sanitizeMmapAddr
      (s.mem.unmapNonFrozen (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat))
      (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x2).toNat) = some newBase)
    (hphys : ¬ pageAlignUp (s.readReg64 .x2).toNat ≤
      s.physMemAvail + pageAlignUp (s.readReg64 .x1).toNat) :
    execMremap s = s.setStatus .OutOfMemory := by
  have holdLen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact holdLen (BitVec.eq_of_toNat_eq (by simpa using h))
  have hnewLen' : (s.readReg64 .x2).toNat ≠ 0 := by
    intro h; exact hnewLen (BitVec.eq_of_toNat_eq (by simpa using h))
  have hnewNotGt : ¬((s.readReg64 .x2).toNat > 2 ^ 64 - PAGE_SIZE) := by omega
  have hfitNotGt : ¬((s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat > USER_VA_LIMIT) := by
    omega
  have hfrz := allPerm_not_frozen_of_allPerm_rw hperm
  have hcm := canMap_eq_false_of_allPerm_rw_pos (pageAlignUp_pos_of_ne_zero holdLen') hperm
  dsimp (config := { zetaHave := true }) only [execMremap]
  simp [hflags, hal, holdLen', hnewLen', hnewNotGt, hfitNotGt, hfrz, hcm, hanon, hperm, hnoFail, hsan, hphys]

/-- `mremap` returns `-ENOMEM` (preserving `s.status`, advancing the oracle and `PC`) whenever a
    valid `MREMAP_MAYMOVE` request hits `oracle.mremapFail = true` or no unmapped destination fits. -/
theorem execMremap_enomem_of_fail (s : State)
    (hflags : s.readReg64 .x3 = MREMAP_MAYMOVE)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (holdLen : s.readReg64 .x1 ≠ 0#64)
    (hnewLen : s.readReg64 .x2 ≠ 0#64)
    (hnewMax : (s.readReg64 .x2).toNat ≤ 2 ^ 64 - PAGE_SIZE)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ USER_VA_LIMIT)
    (hperm : s.mem.allPerm (fun p => p == some Perm.rw) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hanon : s.mem.allAnon (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hfail : s.oracle.mremapFail s.oracleIdx = true ∨
      sanitizeMmapAddr
        (s.mem.unmapNonFrozen (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat))
        (s.oracle.mmap s.oracleIdx)
        (pageAlignUp (s.readReg64 .x2).toNat) = none) :
    execMremap s = ((s.nextOracle).writeReg64 .x0 (-ENOMEM)).advancePC := by
  have holdLen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact holdLen (BitVec.eq_of_toNat_eq (by simpa using h))
  have hnewLen' : (s.readReg64 .x2).toNat ≠ 0 := by
    intro h; exact hnewLen (BitVec.eq_of_toNat_eq (by simpa using h))
  have hnewNotGt : ¬((s.readReg64 .x2).toNat > 2 ^ 64 - PAGE_SIZE) := by omega
  have hfitNotGt : ¬((s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat > USER_VA_LIMIT) := by
    omega
  have hfrz := allPerm_not_frozen_of_allPerm_rw hperm
  have hcm := canMap_eq_false_of_allPerm_rw_pos (pageAlignUp_pos_of_ne_zero holdLen') hperm
  dsimp (config := { zetaHave := true }) only [execMremap]
  rcases hfail with hmf | hnone
  · simp [hflags, hal, holdLen', hnewLen', hnewNotGt, hfitNotGt, hfrz, hcm, hanon, hperm, hmf]
  · cases hmf : s.oracle.mremapFail s.oracleIdx <;>
      simp [hflags, hal, holdLen', hnewLen', hnewNotGt, hfitNotGt, hfrz, hcm, hanon, hperm, hnone]

@[simp]
theorem _root_.Arm64.Memory.allPerm_r_of_canRead {m : Memory} {addr : BitVec 64} {n : Nat}
    (h : m.canRead addr n = true) : m.allPerm (·.r) addr n = true :=
  ((Bool.and_eq_true _ _).mp h).1

@[simp]
theorem _root_.Arm64.Memory.allNoLazyFree_of_canRead {m : Memory} {addr : BitVec 64} {n : Nat}
    (h : m.canRead addr n = true) : m.allNoLazyFree addr n = true :=
  ((Bool.and_eq_true _ _).mp h).2

/-- Non-blocking `ppoll(ufds, nfds, tsp, 0)` with zero timeout `{0, 0}`: updates each `revents`
    halfword via `evalPpollEntries` and returns the ready count in `X0`. -/
theorem execPpoll_ok (s : State) {m' : Memory} {count : Nat}
    (hsigmask : s.readReg64 .x3 = 0#64)
    (htspNe : s.readReg64 .x2 ≠ 0#64)
    (htspFit : (s.readReg64 .x2).toNat + 16 ≤ 2 ^ 64)
    (htspRead : s.mem.canRead (s.readReg64 .x2) 16 = true)
    (htvSec : s.mem.read64 (s.readReg64 .x2) = 0#64)
    (htvNsec : s.mem.read64 (s.readReg64 .x2 + 8#64) = 0#64)
    (hnfdsMax : (s.readReg32 .x1).toNat ≤ FsState.maxOpenFds)
    (hufdsFit : (s.readReg64 .x0).toNat + (s.readReg32 .x1).toNat * 8 ≤ 2 ^ 64)
    (hufdsRead : s.mem.canRead (s.readReg64 .x0) ((s.readReg32 .x1).toNat * 8) = true)
    (hufdsWrite : s.mem.canWrite (s.readReg64 .x0) ((s.readReg32 .x1).toNat * 8) = true)
    (heval : evalPpollEntries s.fs s.mem (s.readReg64 .x0) (s.readReg32 .x1).toNat 0 0 =
      some (m', count)) :
    execPpoll s = ((s.setMem m').writeReg64 .x0 (BitVec.ofNat 64 count)).advancePC := by
  have htspDec : decide ((s.readReg64 .x2).toNat + 16 ≤ 2 ^ 64) = true :=
    decide_eq_true htspFit
  have hufdsDec : decide ((s.readReg64 .x0).toNat + (s.readReg32 .x1).toNat * 8 ≤ 2 ^ 64) = true :=
    decide_eq_true hufdsFit
  have hnfdsNotGt : ¬((s.readReg32 .x1).toNat > FsState.maxOpenFds) := by omega
  dsimp (config := { zetaHave := true }) only [execPpoll]
  rw [htspDec, hufdsDec]
  by_cases hnfds0 : (s.readReg32 .x1).toNat = 0
  · rw [hnfds0] at heval
    simp only [evalPpollEntries, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hsetSelf : s.setMem s.mem = s := by cases s; rfl
    simp [hsigmask, htspNe, htspRead, htvSec, htvNsec, hnfds0, hsetSelf]
  · simp [hsigmask, htspNe, htspRead, htvSec, htvNsec, hnfdsNotGt, hnfds0,
      hufdsRead, hufdsWrite, heval]

theorem SigAltStack.onSigStack_of_size_zero {sas : SigAltStack} (h : sas.size = 0#64)
    (sp : BitVec 64) : sas.onSigStack sp = false := by
  unfold SigAltStack.onSigStack
  rw [h, Bool.eq_false_iff]
  intro htrue
  simp only [Bool.and_eq_true, BitVec.ult, BitVec.ule, decide_eq_true_eq] at htrue
  bv_omega

@[simp, arm64_norm, wp_norm]
theorem SigAltStack.onSigStack_default (sp : BitVec 64) :
    ({} : SigAltStack).onSigStack sp = false :=
  SigAltStack.onSigStack_of_size_zero rfl sp

theorem SigAltStack.flags_of_size_zero {sas : SigAltStack} (h : sas.size = 0#64)
    (sp : BitVec 64) :
    sas.flags sp = if sas.autodisarm then SS_DISABLE ||| SS_AUTODISARM else SS_DISABLE := by
  simp [SigAltStack.flags, h]

@[simp, arm64_norm, wp_norm]
theorem SigAltStack.flags_default (sp : BitVec 64) :
    ({} : SigAltStack).flags sp = SS_DISABLE := rfl

@[simp, arm64_norm, wp_norm]
theorem SigAltStack.toBytes_length (sas : SigAltStack) (sp : BitVec 64) :
    (sas.toBytes sp).length = 24 := rfl

/-- Valid `sigaltstack(uss, uoss)` for null `uss` (query), `SS_DISABLE` teardown (regardless of
    `ss_size`), or valid active installation (`ssMode ∈ {0, SS_ONSTACK}` with
    `MINSIGSTKSZ ≤ ssSize.toNat` and `!onSigStack`), and null or writable 24-byte `uoss`. -/
theorem execSigaltstack_ok (s : State)
    (huss : s.readReg64 .x0 = 0#64 ∨
      ((s.readReg64 .x0).toNat + 24 ≤ 2 ^ 64 ∧
       s.mem.canRead (s.readReg64 .x0) 24 = true ∧
       s.sigAltStack.onSigStack s.sp = false ∧
       ((s.mem.read32 (s.readReg64 .x0 + 8#64) &&& ~~~SS_AUTODISARM) = SS_DISABLE ∨
        (((s.mem.read32 (s.readReg64 .x0 + 8#64) &&& ~~~SS_AUTODISARM) = 0#32 ∨
          (s.mem.read32 (s.readReg64 .x0 + 8#64) &&& ~~~SS_AUTODISARM) = SS_ONSTACK) ∧
         MINSIGSTKSZ ≤ (s.mem.read64 (s.readReg64 .x0 + 16#64)).toNat))))
    (huoss : s.readReg64 .x1 = 0#64 ∨
      ((s.readReg64 .x1).toNat + 24 ≤ 2 ^ 64 ∧ s.mem.canWrite (s.readReg64 .x1) 24 = true)) :
    execSigaltstack s =
      let uss := s.readReg64 .x0
      let uoss := s.readReg64 .x1
      let ssSp := s.mem.read64 uss
      let ssFlags := s.mem.read32 (uss + 8#64)
      let ssSize := s.mem.read64 (uss + 16#64)
      let ssMode := ssFlags &&& ~~~SS_AUTODISARM
      let oldBytes := s.sigAltStack.toBytes s.sp
      let s' :=
        if uss == 0#64 then s
        else if ssMode == SS_DISABLE then
          s.setSigAltStack { sp := 0#64, size := 0#64, ssFlags }
        else
          s.setSigAltStack { sp := ssSp, size := ssSize, ssFlags }
      if uoss == 0#64 then
        (s'.writeReg64 .x0 0#64).advancePC
      else
        ((s'.setMem (s'.mem.writeBytes uoss oldBytes)).writeReg64
          .x0 0#64).advancePC := by
  dsimp (config := { zetaHave := true }) only [execSigaltstack]
  by_cases huss0 : s.readReg64 .x0 = 0#64
  · by_cases huoss0 : s.readReg64 .x1 = 0#64
    · simp [huss0, huoss0]
    · obtain ⟨huossFit, hcw⟩ := huoss.resolve_left huoss0
      have huossDec : decide ((s.readReg64 .x1).toNat + 24 ≤ 2 ^ 64) = true :=
        decide_eq_true huossFit
      rw [huossDec]
      simp [huss0, huoss0, hcw]
  · obtain ⟨hussFit, hcr, hon, hmode⟩ := huss.resolve_left huss0
    have hall : s.mem.allPerm (·.r) (s.readReg64 .x0) 24 = true :=
      Memory.allPerm_r_of_canRead hcr
    have hussDec : decide ((s.readReg64 .x0).toNat + 24 ≤ 2 ^ 64) = true :=
      decide_eq_true hussFit
    rw [hussDec]
    by_cases huoss0 : s.readReg64 .x1 = 0#64
    · rcases hmode with hdis | ⟨hm01, hsz⟩
      · simp [huss0, hall, hcr, hon, hdis, huoss0]
      · have hnotLt : ¬(s.mem.read64 (s.readReg64 .x0 + 16#64)).toNat < MINSIGSTKSZ := by omega
        rcases hm01 with hm0 | hmon
        · simp [huss0, hall, hcr, hon, hm0, hnotLt, huoss0, SS_DISABLE, SS_ONSTACK]
        · simp [huss0, hall, hcr, hon, hmon, hnotLt, huoss0, SS_DISABLE, SS_ONSTACK]
    · obtain ⟨huossFit, hcw⟩ := huoss.resolve_left huoss0
      have huossDec : decide ((s.readReg64 .x1).toNat + 24 ≤ 2 ^ 64) = true :=
        decide_eq_true huossFit
      rw [huossDec]
      rcases hmode with hdis | ⟨hm01, hsz⟩
      · simp [huss0, hall, hcr, hon, hdis, huoss0, hcw]
      · have hnotLt : ¬(s.mem.read64 (s.readReg64 .x0 + 16#64)).toNat < MINSIGSTKSZ := by omega
        rcases hm01 with hm0 | hmon
        · simp [huss0, hall, hcr, hon, hm0, hnotLt, huoss0, hcw, SS_DISABLE, SS_ONSTACK]
        · simp [huss0, hall, hcr, hon, hmon, hnotLt, huoss0, hcw, SS_DISABLE, SS_ONSTACK]

/-- Valid `rt_sigaction(signum, act, oldact, 8)` for `1 ≤ signum ≤ 64`, supporting `SIG_DFL`/`SIG_IGN`
    on any catchable signal and custom user-space handlers on `LINUX_SIGSEGV`/`LINUX_SIGBUS`, plus
    null or writable `oldact`. -/
theorem execRtSigaction_any_ok (s : State)
    (hsigset : s.readReg64 .x3 = 8#64)
    (hlo : 1 ≤ (s.readReg32 .x0).toNat)
    (hhi : (s.readReg32 .x0).toNat ≤ 64)
    (hact : s.readReg64 .x1 = 0#64 ∨
      (s.readReg32 .x0 ≠ LINUX_SIGKILL ∧
       s.readReg32 .x0 ≠ LINUX_SIGSTOP ∧
       (s.readReg64 .x1).toNat + 32 ≤ 2 ^ 64 ∧
       s.mem.canRead (s.readReg64 .x1) 32 = true ∧
       (s.mem.read64 (s.readReg64 .x1) = SIG_DFL ∨
        s.mem.read64 (s.readReg64 .x1) = SIG_IGN ∨
        s.readReg32 .x0 = LINUX_SIGSEGV ∨
        s.readReg32 .x0 = LINUX_SIGBUS)))
    (hold : s.readReg64 .x2 = 0#64 ∨
      ((s.readReg64 .x2).toNat + 32 ≤ 2 ^ 64 ∧ s.mem.canWrite (s.readReg64 .x2) 32 = true)) :
    execRtSigaction s =
      let signum := s.readReg32 .x0
      let act := s.readReg64 .x1
      let oldact := s.readReg64 .x2
      let oldAction := s.getSigAction signum
      let s' :=
        if act == 0#64 then s
        else
          s.setSigAction signum
            { handler := s.mem.read64 act
              flags := s.mem.read64 (act + 8#64) &&& UAPI_SA_FLAGS
              restorer := s.mem.read64 (act + 16#64)
              mask := s.mem.read64 (act + 24#64) &&& ~~~SIG_UNBLOCKABLE_MASK }
      if oldact == 0#64 then
        (s'.writeReg64 .x0 0#64).advancePC
      else
        ((s'.setMem (s'.mem.writeBytes oldact oldAction.toBytes)).writeReg64
          .x0 0#64).advancePC := by
  have hsle : (s.readReg32 .x0).sle 0#32 = false := by
    unfold BitVec.sle
    rw [decide_eq_false_iff_not, BitVec.toInt_eq_toNat_cond]
    have hlt2 : 2 * (s.readReg32 .x0).toNat < 2 ^ 32 := by omega
    simp only [hlt2, ↓reduceIte, BitVec.toInt_zero]
    omega
  have hgt64 : ¬((s.readReg32 .x0).toNat > 64) := by omega
  dsimp (config := { zetaHave := true }) only [execRtSigaction]
  by_cases hact0 : s.readReg64 .x1 = 0#64
  · by_cases hold0 : s.readReg64 .x2 = 0#64
    · simp [hsigset, hsle, hgt64, hact0, hold0]
    · obtain ⟨holdFit, hcw⟩ := hold.resolve_left hold0
      have holdDec : decide ((s.readReg64 .x2).toNat + 32 ≤ 2 ^ 64) = true :=
        decide_eq_true holdFit
      rw [holdDec]
      simp [hsigset, hsle, hgt64, hact0, hold0, hcw]
  · obtain ⟨hkill, hstop, hactFit, hcr, hdisp⟩ := hact.resolve_left hact0
    have hactDec : decide ((s.readReg64 .x1).toNat + 32 ≤ 2 ^ 64) = true :=
      decide_eq_true hactFit
    rw [hactDec]
    by_cases hold0 : s.readReg64 .x2 = 0#64
    · rcases hdisp with hdfl | hign | hsegv | hbus
      · simp [hsigset, hsle, hgt64, hact0, hkill, hstop, hcr, hdfl, hold0]
      · simp [hsigset, hsle, hgt64, hact0, hkill, hstop, hcr, hign, hold0]
      · simp [hsigset, hact0, hcr, hsegv, hold0, LINUX_SIGSEGV, LINUX_SIGKILL, LINUX_SIGSTOP]
      · simp [hsigset, hact0, hcr, hbus, hold0, LINUX_SIGBUS, LINUX_SIGKILL, LINUX_SIGSTOP]
    · obtain ⟨holdFit, hcw⟩ := hold.resolve_left hold0
      have holdDec : decide ((s.readReg64 .x2).toNat + 32 ≤ 2 ^ 64) = true :=
        decide_eq_true holdFit
      rw [holdDec]
      rcases hdisp with hdfl | hign | hsegv | hbus
      · simp [hsigset, hsle, hgt64, hact0, hkill, hstop, hcr, hdfl, hold0, hcw]
      · simp [hsigset, hsle, hgt64, hact0, hkill, hstop, hcr, hign, hold0, hcw]
      · simp [hsigset, hact0, hcr, hsegv, hold0, hcw, LINUX_SIGSEGV, LINUX_SIGKILL, LINUX_SIGSTOP]
      · simp [hsigset, hact0, hcr, hbus, hold0, hcw, LINUX_SIGBUS, LINUX_SIGKILL, LINUX_SIGSTOP]

/-- Valid `rt_sigaction(signum, act, oldact, 8)` for `1 ≤ signum ≤ 64`, `SIG_DFL`/`SIG_IGN` (or
    null `act`), and null or writable `oldact`. -/
theorem execRtSigaction_ok (s : State)
    (hsigset : s.readReg64 .x3 = 8#64)
    (hlo : 1 ≤ (s.readReg32 .x0).toNat)
    (hhi : (s.readReg32 .x0).toNat ≤ 64)
    (hact : s.readReg64 .x1 = 0#64 ∨
      (s.readReg32 .x0 ≠ LINUX_SIGKILL ∧
       s.readReg32 .x0 ≠ LINUX_SIGSTOP ∧
       (s.readReg64 .x1).toNat + 32 ≤ 2 ^ 64 ∧
       s.mem.canRead (s.readReg64 .x1) 32 = true ∧
       (s.mem.read64 (s.readReg64 .x1) = SIG_DFL ∨ s.mem.read64 (s.readReg64 .x1) = SIG_IGN)))
    (hold : s.readReg64 .x2 = 0#64 ∨
      ((s.readReg64 .x2).toNat + 32 ≤ 2 ^ 64 ∧ s.mem.canWrite (s.readReg64 .x2) 32 = true)) :
    execRtSigaction s =
      let signum := s.readReg32 .x0
      let act := s.readReg64 .x1
      let oldact := s.readReg64 .x2
      let oldAction := s.getSigAction signum
      let s' :=
        if act == 0#64 then s
        else
          s.setSigAction signum
            { handler := s.mem.read64 act
              flags := s.mem.read64 (act + 8#64) &&& UAPI_SA_FLAGS
              restorer := s.mem.read64 (act + 16#64)
              mask := s.mem.read64 (act + 24#64) &&& ~~~SIG_UNBLOCKABLE_MASK }
      if oldact == 0#64 then
        (s'.writeReg64 .x0 0#64).advancePC
      else
        ((s'.setMem (s'.mem.writeBytes oldact oldAction.toBytes)).writeReg64
          .x0 0#64).advancePC :=
  execRtSigaction_any_ok s hsigset hlo hhi
    (hact.imp id fun ⟨hk, hs, hf, hc, hd⟩ => ⟨hk, hs, hf, hc, hd.imp id Or.inl⟩) hold

end ProofLib
