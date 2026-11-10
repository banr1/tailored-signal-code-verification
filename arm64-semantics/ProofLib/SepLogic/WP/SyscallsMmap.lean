/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.CoreLemmas
public import ProofLib.Lemmas
public import ProofLib.SyscallModels
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.Region
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SepLogic.WP.StepsCore
public import ProofLib.SepLogic.WP.Structural
public import ProofLib.Hoare.SubroutineHook
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.Defs

/-!
# `SepWP` Rules for Anonymous `mmap`

Provides `SepWP` step rules for Linux AArch64 `SVC #0` `execMmap` covering non-fixed anonymous
`PROT_NONE` reserve (`step_svc_mmap_anon_reserve`), non-fixed anonymous `PROT_READ | PROT_WRITE`
mapping (`step_svc_mmap_anon_rw`), `MAP_FIXED` commit (`step_svc_mmap_fixed_commit`), and
`MAP_FIXED` decommit (`step_svc_mmap_fixed_decommit`), exposing the exact post-`svc` memory `m'`
and conditional out-of-memory premise. Not re-exported by `ProofLib` or `ProofLib.SepLogic.WP`;
import `ProofLib.SepLogic.WP.SyscallsMmap` directly.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib

open Arm64

private theorem inRegion_add_ofNat {base : BitVec 64} {len i : Nat} (hi : i < len) :
    InRegion base len (base + BitVec.ofNat 64 i) := by
  simp only [InRegion]
  have hsub : base + BitVec.ofNat 64 i - base = BitVec.ofNat 64 i := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  rw [hsub, BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hi

/-- An owned `PROT_NONE` range holds no writable bytes: `countRw base len = 0`. -/
theorem Satisfies.countRw_eq_zero_of_memRegionProtNone {m : Memory} {base : BitVec 64}
    {len : Nat} {R : SepProp} (h : m ⊨ memRegionProtNone base len ∗ R) :
    m.countRw base len = 0 := by
  unfold Memory.countRw
  refine Memory.countPerm_eq_zero_of_allPerm_not m (· == some Perm.rw) base len ?_
  rw [Memory.allPerm_iff]; intro i hi
  rw [(IsBlockProtNone.memRegionProtNone base len).perm_protNone h (inRegion_add_ofNat hi)]
  rfl

/-- Every byte of an owned writable range is writable: `countRw base len = len`. -/
theorem Satisfies.countRw_eq_of_memRegion {m : Memory} {base : BitVec 64}
    {len : Nat} {R : SepProp} (h : m ⊨ memRegion base len ∗ R) :
    m.countRw base len = len := by
  apply Memory.countRw_eq_of_allPerm_rw
  rw [Memory.allPerm_iff]; intro i hi
  rw [(IsBlock.memRegion base len).perm_rw h (inRegion_add_ofNat hi)]
  rfl

/-- After `unmapNonFrozen` over an owned `PROT_NONE` range, the range can be mapped again. -/
theorem Satisfies.canMap_unmapNonFrozen_of_memRegionProtNone {m : Memory} {base : BitVec 64}
    {len : Nat} {R : SepProp} (h : m ⊨ memRegionProtNone base len ∗ R) :
    (m.unmapNonFrozen base len).canMap base len = true := by
  rw [Memory.canMap, Memory.allPerm_iff]; intro i hi
  have hin := inRegion_add_ofNat (base := base) hi
  have hp := (IsBlockProtNone.memRegionProtNone base len).perm_protNone h hin
  rw [Memory.perm_unmapNonFrozen]; simp only [InRegion] at hin; simp only [hin, hp]; decide

/-- An anonymous non-fixed `PROT_NONE` `mmap` (`flags` `0x22` or `0x20022`) for which
    `sanitizeMmapAddr` finds no free gap transitions to `ExecStatus.OutOfMemory`. -/
theorem execMmap_anon_protNone_oom (s : State)
    (hprot : s.readReg64 .x2 = 0#64)
    (hflags : s.readReg64 .x3 = 0x22#64 ∨ s.readReg64 .x3 = 0x20022#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : s.readReg64 .x1 ≠ 0#64)
    (hfail : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) = none) :
    execMmap s = s.setStatus .OutOfMemory := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  dsimp (config := { zetaHave := true }) only [execMmap]
  rcases hflags with hf | hf <;>
    simp [MMAP_PROT_RW, MMAP_PROT_NONE, MMAP_FLAGS_PRIVATE_ANON, MMAP_FLAGS_PRIVATE_ANON_STACK,
      MMAP_FLAGS_PRIVATE_ANON_FIXED, hprot, hf, hoff, hlen', hfail]

private theorem readReg64_x1_ne_zero_of_pageAlignUp {s : State} {len : Nat}
    (hlen_eq : pageAlignUp (s.readReg64 .x1).toNat = len) (hlen0 : 0 < len) :
    s.readReg64 .x1 ≠ 0#64 := by
  intro h; rw [h] at hlen_eq; subst hlen_eq; exact absurd hlen0 (by decide)

/-- Step rule for a non-fixed anonymous `PROT_NONE` `SYS_mmap` (`svc #0` with `X8 = 222`,
    `X2 = 0`, `X3` equal to `0x22` or `0x20022`, `X5 = 0`) of page-rounded length
    `len = pageAlignUp X1 > 0`: reserves `(mb ↦ₙ List.replicate len 0#8) ∗ memMapped mb len`
    in `m' = (s.mem.mapZero mb len).setPermNonFrozen mb len Perm.protNone` without charging
    `physMemAvail`, or transitions to `.OutOfMemory` when `sanitizeMmapAddr` returns `none`. For
    page-aligned `X1`, discharge `hlen_eq` with `pageAlignUp_of_dvd`. -/
theorem SepWP.step_svc_mmap_anon_reserve {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {len : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64)
    (hprot : s.readReg64 .x2 = 0#64)
    (hflags : s.readReg64 .x3 = 0x22#64 ∨ s.readReg64 .x3 = 0x20022#64)
    (hoff : s.readReg64 .x5 = 0#64)
    (hlen_eq : pageAlignUp (s.readReg64 .x1).toNat = len) (hlen0 : 0 < len)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      MMAP_MIN_ADDR ≤ mb.toNat → mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + len ≤ 2 ^ 48 →
      m' = (s.mem.mapZero mb len).setPermNonFrozen mb len Perm.protNone →
      SepWP prog target_pc
        (((s.nextOracle.writeReg64 .x0 mb).setPC (pc + 4#64)).setMem m')
        ((mb ↦ₙ List.replicate len 0#8) ∗ memMapped mb len ∗ P) post oom)
    (hoom : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx) len = none →
      ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R) := by
      intro _ _ hm; (try simp only [wp_unfold, Spec.allowOom] at hm ⊢)
      first | exact satisfies_true_sepConj hm | exact satisfies_true_sepConj_frame hm)
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  let _ := hx8
  refine SepWP.of_reaches_pc fun R hm => ?_
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  rw [hsvc]
  have hlen_ne := readReg64_x1_ne_zero_of_pageAlignUp hlen_eq hlen0
  cases hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) with
  | some mb =>
    have hmin := sanitizeMmapAddr_min hsan
    obtain ⟨hne, hal, hfit, hmap⟩ := sanitizeMmapAddr_spec hsan
    unfold USER_VA_LIMIT at hfit
    rw [execMmap_anon_protNone_sanitized_ok s hprot hflags hoff hlen_ne hsan, hlen_eq]
    rw [hlen_eq] at hfit hmap
    have hdvd : 4096 ∣ mb.toNat := by
      unfold PAGE_SIZE at hal; exact Nat.dvd_of_mod_eq_zero hal
    have hm' := Satisfies.mapZeroProtNone_mapped hm hmap (by omega)
    have hm'' : ((s.mem.mapZero mb len).setPermNonFrozen mb len Perm.protNone) ⊨
        ((mb ↦ₙ List.replicate len 0#8) ∗ memMapped mb len ∗ P) ∗ R := by
      simpa only [sepConj_assoc] using hm'
    have hst :
        (((s.setMem ((s.mem.mapZero mb len).setPermNonFrozen mb len Perm.protNone)).nextOracle
          ).writeReg64 .x0 mb).advancePC =
        (((s.nextOracle.writeReg64 .x0 mb).setPC (pc + 4#64)).setMem
          ((s.mem.mapZero mb len).setPermNonFrozen mb len Perm.protNone)) := by
      cases s; simp [State.setMem, State.nextOracle, State.writeReg64, State.advancePC,
        State.setPC] at hpc ⊢
      exact hpc
    rw [hst]
    exact SepWP.to_reaches_pc (hok mb _ hmin hne hdvd hfit rfl) hm''
  | none =>
    rw [execMmap_anon_protNone_oom s hprot hflags hoff hlen_ne hsan]
    rw [hlen_eq] at hsan
    exact reaches_pc_oom rfl (by simpa [State.setStatus] using hoom hsan R hm)

/-- Step rule for a non-fixed anonymous `PROT_READ | PROT_WRITE` `SYS_mmap` (`svc #0` with
    `X8 = 222`, `X2 = 3`, `X3` equal to `0x22` or `0x20022`, `X5 = 0`) of page-rounded length
    `len = pageAlignUp X1 > 0`: maps `(mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len` in
    `m' = s.mem.mapZero mb len` charging `len` from `physMemAvail`, or transitions to
    `.OutOfMemory` when `sanitizeMmapAddr` returns `none` or `physMemAvail < len`. For page-aligned
    `X1`, discharge `hlen_eq` with `pageAlignUp_of_dvd`. -/
theorem SepWP.step_svc_mmap_anon_rw {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {len : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64)
    (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64 ∨ s.readReg64 .x3 = 0x20022#64)
    (hoff : s.readReg64 .x5 = 0#64)
    (hlen_eq : pageAlignUp (s.readReg64 .x1).toNat = len) (hlen0 : 0 < len)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      MMAP_MIN_ADDR ≤ mb.toNat → mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + len ≤ 2 ^ 48 →
      len ≤ s.physMemAvail → m' = s.mem.mapZero mb len →
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail - len)).nextOracle.writeReg64 .x0 mb).setPC
          (pc + 4#64)).setMem m')
        ((mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗ P) post oom)
    (hoom : (sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx) len = none ∨
        s.physMemAvail < len) →
      ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R) := by
      intro _ _ hm; (try simp only [wp_unfold, Spec.allowOom] at hm ⊢)
      first | exact satisfies_true_sepConj hm | exact satisfies_true_sepConj_frame hm)
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  let _ := hx8
  refine SepWP.of_reaches_pc fun R hm => ?_
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  rw [hsvc]
  have hlen_ne := readReg64_x1_ne_zero_of_pageAlignUp hlen_eq hlen0
  cases hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) with
  | some mb =>
    by_cases hphys : pageAlignUp (s.readReg64 .x1).toNat ≤ s.physMemAvail
    · have hmin := sanitizeMmapAddr_min hsan
      obtain ⟨hne, hal, hfit, hmap⟩ := sanitizeMmapAddr_spec hsan
      unfold USER_VA_LIMIT at hfit
      rw [execMmap_anon_sanitized_ok s hprot hflags hoff hlen_ne hsan hphys, hlen_eq]
      rw [hlen_eq] at hfit hmap hphys
      have hdvd : 4096 ∣ mb.toNat := by
        unfold PAGE_SIZE at hal; exact Nat.dvd_of_mod_eq_zero hal
      have hm'' : s.mem.mapZero mb len ⊨
          ((mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗ P) ∗ R := by
        simpa only [sepConj_assoc] using Satisfies.mapZero_bytes_mapped hm hmap (by omega)
      have hst :
          ((((s.setMem (s.mem.mapZero mb len)).setPhysMemAvail (s.physMemAvail - len)).nextOracle
            ).writeReg64 .x0 mb).advancePC =
          ((((s.setPhysMemAvail (s.physMemAvail - len)).nextOracle.writeReg64 .x0 mb).setPC
            (pc + 4#64)).setMem (s.mem.mapZero mb len)) := by
        cases s; simp [State.setMem, State.setPhysMemAvail, State.nextOracle, State.writeReg64,
          State.advancePC, State.setPC] at hpc ⊢
        exact hpc
      rw [hst]
      exact SepWP.to_reaches_pc (hok mb _ hmin hne hdvd hfit hphys rfl) hm''
    · rw [execMmap_anon_sanitized_oom s hprot hflags hoff hlen_ne hsan hphys]
      rw [hlen_eq] at hphys
      exact reaches_pc_oom rfl
        (by simpa [State.setStatus] using hoom (Or.inr (Nat.lt_of_not_le hphys)) R hm)
  | none =>
    rw [execMmap_anon_oom s hprot hflags hoff hlen_ne hsan]
    rw [hlen_eq] at hsan
    exact reaches_pc_oom rfl (by simpa [State.setStatus] using hoom (Or.inl hsan) R hm)

/-- Step rule for `SYS_mmap` with `MAP_FIXED` and `PROT_READ | PROT_WRITE` (`X8 = 222`, `X2 = 3`,
    `X3 = 0x32`, `X5 = 0`) committing an owned `PROT_NONE` range `[addr, addr + len)`: when
    `len <= physMemAvail`, produces zero-filled writable bytes in
    `m' = (s.mem.unmapNonFrozen addr len).mapZero addr len` and charges `len` to `physMemAvail`;
    otherwise transitions to `.OutOfMemory`. -/
theorem SepWP.step_svc_mmap_fixed_commit {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc addr : BitVec 64} {len : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (haddr : s.readReg64 .x0 = addr)
    (hprot : s.readReg64 .x2 = 3#64) (hflags : s.readReg64 .x3 = 0x32#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen_eq : (s.readReg64 .x1).toNat = len)
    (hlen0 : 0 < len) (hlen4096 : 4096 ∣ len)
    (hal : 4096 ∣ addr.toNat) (hmin : Arm64.MMAP_MIN_ADDR ≤ addr.toNat)
    (hfit : addr.toNat + len ≤ 2 ^ 48)
    (hok : ∀ m' : Memory, len ≤ s.physMemAvail →
      m' = (s.mem.unmapNonFrozen addr len).mapZero addr len →
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail - len)).writeReg64 .x0 addr).setPC
          (pc + 4#64)).setMem m')
        ((addr ↦ₛ List.replicate len 0#8) ∗ memMapped addr len ∗ P) post oom)
    (hoom : ∀ R, ¬ len ≤ s.physMemAvail →
      (s.mem ⊨ (memRegionProtNone addr len ∗ memMapped addr len ∗ P) ∗ R) →
      (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R) := by
      intro _ _ hm; (try simp only [wp_unfold, Spec.allowOom] at hm ⊢)
      first | exact satisfies_true_sepConj hm | exact satisfies_true_sepConj_frame hm)
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegionProtNone addr len ∗ memMapped addr len ∗ P) post oom := by
  let _ := hx8; subst hlen_eq haddr
  refine SepWP.of_reaches_pc fun R hm => ?_
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); rw [hsvc]
  have hlen_ne : s.readReg64 .x1 ≠ 0#64 := by intro h; rw [h] at hlen0; contradiction
  have hlen_nat_ne : (s.readReg64 .x1).toNat ≠ 0 := by omega
  have halign : pageAlignUp (s.readReg64 .x1).toNat = (s.readReg64 .x1).toNat :=
    pageAlignUp_of_dvd hlen4096
  have hm' : s.mem ⊨ memRegionProtNone (s.readReg64 .x0) (s.readReg64 .x1).toNat ∗
      memMapped (s.readReg64 .x0) (s.readReg64 .x1).toNat ∗ (P ∗ R) := by
    simpa only [sepConj_assoc] using hm
  have hfrz := Satisfies.allPerm_not_frozen_of_memRegionProtNone hm'
  have hcnt := Satisfies.countRw_eq_zero_of_memRegionProtNone hm'
  have hmin' : ¬ (s.readReg64 .x0).toNat < MMAP_MIN_ADDR := by omega
  have hal' : (s.readReg64 .x0).toNat % 4096 = 0 := Nat.mod_eq_zero_of_dvd hal
  by_cases hphys : (s.readReg64 .x1).toNat ≤ s.physMemAvail
  · have hexec : execMmap s =
        (((s.setMem ((s.mem.unmapNonFrozen (s.readReg64 .x0) (s.readReg64 .x1).toNat).mapZero
            (s.readReg64 .x0) (s.readReg64 .x1).toNat)).setPhysMemAvail
            (s.physMemAvail - (s.readReg64 .x1).toNat)).writeReg64
          .x0 (s.readReg64 .x0)).advancePC := by
      simp [execMmap, MMAP_PROT_RW, MMAP_PROT_NONE, MMAP_FLAGS_PRIVATE_ANON,
        MMAP_FLAGS_PRIVATE_ANON_STACK, MMAP_FLAGS_PRIVATE_ANON_FIXED, hprot, hflags, hoff,
        hlen_nat_ne, halign, show PAGE_SIZE = 4096 from rfl, hal', hmin', hfit, hfrz,
        hcnt, hphys]
    rw [hexec]
    have hst :
        (((s.setMem ((s.mem.unmapNonFrozen (s.readReg64 .x0) (s.readReg64 .x1).toNat).mapZero
            (s.readReg64 .x0) (s.readReg64 .x1).toNat)).setPhysMemAvail
            (s.physMemAvail - (s.readReg64 .x1).toNat)).writeReg64
          .x0 (s.readReg64 .x0)).advancePC =
        ((((s.setPhysMemAvail (s.physMemAvail - (s.readReg64 .x1).toNat)).writeReg64
          .x0 (s.readReg64 .x0)).setPC (pc + 4#64)).setMem
          ((s.mem.unmapNonFrozen (s.readReg64 .x0) (s.readReg64 .x1).toNat).mapZero
            (s.readReg64 .x0) (s.readReg64 .x1).toNat)) := by
      cases s; simp [State.setMem, State.setPhysMemAvail, State.writeReg64, State.advancePC,
        State.setPC] at hpc ⊢; exact hpc
    rw [hst]
    have hlen64 : (s.readReg64 .x1).toNat ≤ 2 ^ 64 := Nat.le_of_lt (s.readReg64 .x1).isLt
    have hm_final : (s.mem.unmapNonFrozen (s.readReg64 .x0) (s.readReg64 .x1).toNat).mapZero
        (s.readReg64 .x0) (s.readReg64 .x1).toNat ⊨
        ((s.readReg64 .x0 ↦ₛ List.replicate (s.readReg64 .x1).toNat 0#8) ∗
          memMapped (s.readReg64 .x0) (s.readReg64 .x1).toNat ∗ P) ∗ R := by
      simpa only [sepConj_assoc] using
        Satisfies.mapZero_bytes_mapped (Satisfies.unmapNonFrozen_protNone hm')
          (Satisfies.canMap_unmapNonFrozen_of_memRegionProtNone hm') hlen64
    exact SepWP.to_reaches_pc (hok _ hphys rfl) hm_final
  · have hexec : execMmap s = s.setStatus .OutOfMemory := by
      simp [execMmap, MMAP_PROT_RW, MMAP_PROT_NONE, MMAP_FLAGS_PRIVATE_ANON,
        MMAP_FLAGS_PRIVATE_ANON_STACK, MMAP_FLAGS_PRIVATE_ANON_FIXED, hprot, hflags, hoff,
        hlen_nat_ne, halign, show PAGE_SIZE = 4096 from rfl, hal', hmin', hfit, hfrz,
        hcnt, hphys]
    rw [hexec]
    exact reaches_pc_oom rfl (by simpa [State.setStatus] using hoom R hphys hm)

/-- Step rule for `SYS_mmap` with `MAP_FIXED` and `PROT_NONE` (`X8 = 222`, `X2 = 0`,
    `X3 = 0x32`, `X5 = 0`) decommitting an owned writable range `[addr, addr + len)`: produces
    zero-filled `PROT_NONE` bytes in
    `m' = ((s.mem.unmapNonFrozen addr len).mapZero addr len).setPermNonFrozen addr len Perm.protNone`
    and refunds `len` to `physMemAvail`. -/
theorem SepWP.step_svc_mmap_fixed_decommit {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc addr : BitVec 64} {len : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (haddr : s.readReg64 .x0 = addr)
    (hprot : s.readReg64 .x2 = 0#64) (hflags : s.readReg64 .x3 = 0x32#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen_eq : (s.readReg64 .x1).toNat = len)
    (hlen0 : 0 < len) (hlen4096 : 4096 ∣ len)
    (hal : 4096 ∣ addr.toNat) (hmin : Arm64.MMAP_MIN_ADDR ≤ addr.toNat)
    (hfit : addr.toNat + len ≤ 2 ^ 48)
    (hok : ∀ m' : Memory,
      m' = ((s.mem.unmapNonFrozen addr len).mapZero addr len).setPermNonFrozen addr len
        Perm.protNone →
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail + len)).writeReg64 .x0 addr).setPC
          (pc + 4#64)).setMem m')
        ((addr ↦ₙ List.replicate len 0#8) ∗ P) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegion addr len ∗ P) post oom := by
  let _ := hx8
  subst hlen_eq haddr
  refine SepWP.of_reaches_pc fun R hm => ?_
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  rw [hsvc]
  have hlen_ne : s.readReg64 .x1 ≠ 0#64 := by
    intro h; rw [h] at hlen0; contradiction
  have halign : pageAlignUp (s.readReg64 .x1).toNat = (s.readReg64 .x1).toNat :=
    pageAlignUp_of_dvd hlen4096
  have hm' : s.mem ⊨ memRegion (s.readReg64 .x0) (s.readReg64 .x1).toNat ∗ (P ∗ R) := by
    rw [← sepConj_assoc]; exact hm
  have hrw : s.mem.RW (s.readReg64 .x0) (s.readReg64 .x1).toNat :=
    (IsBlock.memRegion _ _).rw hm'
  have hfrz := hrw.allPerm_not_frozen (by omega)
  have hcnt := Satisfies.countRw_eq_of_memRegion hm'
  rw [execMmap_fixed_protNone_ok s hprot hflags hoff hlen_ne
    (by unfold PAGE_SIZE; exact Nat.mod_eq_zero_of_dvd hal)
    hmin (by rw [halign]; exact hfit) (by rw [halign]; exact hfrz), halign, hcnt]
  have hlen64 : (s.readReg64 .x1).toNat ≤ 2 ^ 64 := Nat.le_of_lt (s.readReg64 .x1).isLt
  have hst :
      (((s.setMem (((s.mem.unmapNonFrozen (s.readReg64 .x0) (s.readReg64 .x1).toNat).mapZero
          (s.readReg64 .x0) (s.readReg64 .x1).toNat).setPermNonFrozen (s.readReg64 .x0)
          (s.readReg64 .x1).toNat Perm.protNone)).setPhysMemAvail
          (s.physMemAvail + (s.readReg64 .x1).toNat)).writeReg64 .x0 (s.readReg64 .x0)).advancePC =
      ((((s.setPhysMemAvail (s.physMemAvail + (s.readReg64 .x1).toNat)).writeReg64
          .x0 (s.readReg64 .x0)).setPC (pc + 4#64)).setMem
        (((s.mem.unmapNonFrozen (s.readReg64 .x0) (s.readReg64 .x1).toNat).mapZero
          (s.readReg64 .x0) (s.readReg64 .x1).toNat).setPermNonFrozen (s.readReg64 .x0)
          (s.readReg64 .x1).toNat Perm.protNone)) := by
    cases s; simp [State.setMem, State.setPhysMemAvail, State.writeReg64, State.advancePC,
      State.setPC] at hpc ⊢
    exact hpc
  rw [hst]
  have hm_final := Satisfies.mmapFixedProtNone_owned hm' hlen64
  exact SepWP.to_reaches_pc (hok _ rfl) (by simpa only [sepConj_assoc, State.setMem] using hm_final)

end ProofLib
