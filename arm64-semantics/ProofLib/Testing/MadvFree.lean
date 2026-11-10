/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public meta import Arm64
public import ProofLib
public import ProofLib.Hoare.SubroutineHook
public import ProofLib.Process

/-!
# `MADV_FREE` Separation-Logic and `SepWP` Tests

Tests `HeapCell.lazy`, lazy-free points-to assertions, `memRegionLazy`, `SepStoreW.here_lazy`,
`SepWP.step_svc_madvise_free`, `SepWP.step_svc_madvise_dontneed_lazy`, and `#guard_msgs`
rejections of loads or unstored upgrades on lazy-free cells.
-/

@[expose] public section

set_option autoImplicit false

namespace Examples.Testing.MadvFreeTest

open Arm64 ProofLib

set_option maxHeartbeats 400000
arm64_proof_prelude

/-! ## Store and load on lazy-free cells -/

@[simp, arm64_norm] def store_load_lazy_addr : BitVec 64 := 0x70000#64

def storeLoadLazyCode : FnCode :=
  .atAddr "store_load_lazy" store_load_lazy_addr
    ("f9000001 " ++ -- 0x70000: str x1, [x0]
     "f9400002 " ++ -- 0x70004: ldr x2, [x0]
     "d65f03c0")    -- 0x70008: ret

theorem store_load_lazy64_wp_steps (prog : Program) (s0 : State) (ptr val : BitVec 64) (R : SepProp)
    (hc : storeLoadLazyCode.holds prog)
    (hpc : s0.pc = store_load_lazy_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr) (hx1 : s0.readReg64 .x1 = val) :
    SepWP prog (s0.readReg64 .lr) s0
      ((ptr ↦₆₄ₗ) ∗ R)
      (sepPost (fun sf => sf.readReg64 .x2 = val) ((ptr ↦₆₄ val) ∗ R)) := by
  wp_steps
  wp_done

theorem store_load_lazy64_wp_sym_steps (prog : Program) (s0 : State) (ptr val : BitVec 64) (R : SepProp)
    (hc : storeLoadLazyCode.holds prog)
    (hpc : s0.pc = store_load_lazy_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr) (hx1 : s0.readReg64 .x1 = val) :
    SepWP prog (s0.readReg64 .lr) s0
      ((ptr ↦₆₄ₗ) ∗ R)
      (sepPost (fun sf => sf.readReg64 .x2 = val) ((ptr ↦₆₄ val) ∗ R)) := by
  wp_sym_steps
  wp_done

/-! ## `MADV_FREE` followed by store and load -/

@[simp, arm64_norm] def madv_free_seq_addr : BitVec 64 := 0x71000#64

/-- Subroutine calling `madvise(addr, 4096, MADV_FREE)` followed by `STR` and `LDR`. -/
def madvFreeSeqCode : FnCode :=
  .atAddr "madv_free_seq" madv_free_seq_addr
    ("d4000001 " ++ -- 0x71000: svc #0
     "f9000064 " ++ -- 0x71004: str x4, [x3]
     "f9400065 " ++ -- 0x71008: ldr x5, [x3]
     "d65f03c0")    -- 0x7100c: ret

private theorem evalInst_svc_madvise {prog : Program} {s : State}
    (hsvc : prog.svc = Syscall.standard) (hx8 : s.readReg64 .x8 = 233#64) :
    prog.evalInst (.system false 0#16) s = execMadvise s := by
  rw [_root_.Arm64.Program.evalInst_svc0, hsvc, evalSvc_standard]
  simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable,
    Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, SYS_BRK, SYS_MUNMAP,
    SYS_MREMAP, SYS_MMAP, SYS_MPROTECT, SYS_MADVISE, hx8]

theorem madv_free_then_store_load_ok (prog : Program) (s0 : State)
    (addr val : BitVec 64) (F : SepProp)
    (hc : madvFreeSeqCode.holds prog)
    (hsvc : prog.svc = Syscall.standard)
    (hpc : s0.pc = madv_free_seq_addr) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = 233#64)
    (hx0 : s0.readReg64 .x0 = addr)
    (hx1 : s0.readReg64 .x1 = 4096#64)
    (hx2 : s0.readReg64 .x2 = 8#64)
    (hx3 : s0.readReg64 .x3 = addr)
    (hx4 : s0.readReg64 .x4 = val)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hfit : addr.toNat + 4096 ≤ 2 ^ 48) :
    SepWP prog (s0.readReg64 .lr) s0
      (memRegion addr 4096 ∗ (memMapped addr 4096 ∗ F))
      (sepPost (fun sf => sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x5 = val)
        ((addr ↦₆₄ val) ∗ memRegionLazy (addr + 8#64) 4088 ∗ memMapped addr 4096 ∗ F)) := by
  have hfetch0 : prog.fetch madv_free_seq_addr = some (.system false 0#16) := by wp_fetch
  apply SepWP.step_svc_madvise_free hpc hrun hfetch0 hx8 hx0 hx1 hx2 hal
    (by decide) (by decide) hfit (hsvc := evalInst_svc_madvise hsvc hx8)
  intro m'
  rw [memRegionLazy_split addr 8 4088 (by decide), ← pointsTo64Lazy_eq_memRegionLazy addr,
    sepConj_assoc]
  wp_steps
  wp_done

/-! ## `MADV_DONTNEED`, `munmap`, and `mprotect` on lazy-free regions -/

@[simp, arm64_norm] def madv_dontneed_lazy_addr : BitVec 64 := 0x72000#64

/-- Subroutine calling `madvise(addr, 4096, MADV_DONTNEED)` followed by `LDR`. -/
def madvDontneedLazyCode : FnCode :=
  .atAddr "madv_dontneed_lazy" madv_dontneed_lazy_addr
    ("d4000001 " ++ -- 0x72000: svc #0
     "f9400065 " ++ -- 0x72004: ldr x5, [x3]
     "d65f03c0")    -- 0x72008: ret

theorem madv_dontneed_lazy_region_ok (prog : Program) (s0 : State)
    (addr : BitVec 64) (F : SepProp)
    (hfetch0 : prog.fetch madv_dontneed_lazy_addr = some (.system false 0#16))
    (hsvc : prog.svc = Syscall.standard)
    (hpc : s0.pc = madv_dontneed_lazy_addr) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = 233#64)
    (hx0 : s0.readReg64 .x0 = addr)
    (hx1 : s0.readReg64 .x1 = 4096#64)
    (hx2 : s0.readReg64 .x2 = 4#64)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hfit : addr.toNat + 4096 ≤ 2 ^ 48) :
    SepWP prog (madv_dontneed_lazy_addr + 4#64) s0
      (memRegionLazy addr 4096 ∗ (memMapped addr 4096 ∗ F))
      (sepPost (fun sf => sf.readReg64 .x0 = 0#64)
        (memRegion addr 4096 ∗ (memMapped addr 4096 ∗ F))) := by
  apply SepWP.step_svc_madvise_dontneed_lazy hpc hrun hfetch0 hx8 hx0 hx1 hx2 hal
    (by decide) (by decide) hfit (hsvc := evalInst_svc_madvise hsvc hx8)
  intro m'
  wp_done

theorem madv_dontneed_lazy_reads_zero_ok (prog : Program) (s0 : State)
    (addr : BitVec 64) (F : SepProp)
    (hc : madvDontneedLazyCode.holds prog)
    (hsvc : prog.svc = Syscall.standard)
    (hpc : s0.pc = madv_dontneed_lazy_addr) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = 233#64)
    (hx0 : s0.readReg64 .x0 = addr)
    (hx1 : s0.readReg64 .x1 = 4096#64)
    (hx2 : s0.readReg64 .x2 = 4#64)
    (hx3 : s0.readReg64 .x3 = addr)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hfit : addr.toNat + 4096 ≤ 2 ^ 48) :
    SepWP prog (s0.readReg64 .lr) s0
      (memRegionLazy addr 4096 ∗ (memMapped addr 4096 ∗ F))
      (sepPost (fun sf => sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x5 = 0#64)
        ((addr ↦ₛ List.replicate 4096 0#8) ∗ (memMapped addr 4096 ∗ F))) := by
  have hfetch0 : prog.fetch madv_dontneed_lazy_addr = some (.system false 0#16) := by wp_fetch
  apply SepWP.step_svc_madvise_dontneed_lazy_bytes hpc hrun hfetch0 hx8 hx0 hx1 hx2 hal
    (by decide) (by decide) hfit (hsvc := evalInst_svc_madvise hsvc hx8)
  intro m'
  rw [show (4096 : Nat) = 8 + 4088 from rfl, pointsToBytes_replicate_split addr 8 4088 0#8,
    pointsToBytes_replicate8_zero addr, sepConj_assoc]
  wp_steps
  rw [← sepConj_assoc, ← pointsToBytes_replicate8_zero addr,
    ← pointsToBytes_replicate_split addr 8 4088 0#8]
  wp_done

private theorem evalInst_svc_munmap {prog : Program} {s : State}
    (hsvc : prog.svc = Syscall.standard) (hx8 : s.readReg64 .x8 = 215#64) :
    prog.evalInst (.system false 0#16) s = execMunmap s := by
  rw [_root_.Arm64.Program.evalInst_svc0, hsvc, evalSvc_standard]
  simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable,
    Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, SYS_BRK, SYS_MUNMAP,
    SYS_MREMAP, SYS_MMAP, SYS_MPROTECT, SYS_MADVISE, hx8]

private theorem evalInst_svc_mprotect {prog : Program} {s : State}
    (hsvc : prog.svc = Syscall.standard) (hx8 : s.readReg64 .x8 = 226#64) :
    prog.evalInst (.system false 0#16) s = execMprotect s := by
  rw [_root_.Arm64.Program.evalInst_svc0, hsvc, evalSvc_standard]
  simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable,
    Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, SYS_BRK, SYS_MUNMAP,
    SYS_MREMAP, SYS_MMAP, SYS_MPROTECT, SYS_MADVISE, hx8]

theorem madv_dontneed_region_ok (prog : Program) (s0 : State)
    (addr : BitVec 64) (F : SepProp)
    (hfetch0 : prog.fetch madv_dontneed_lazy_addr = some (.system false 0#16))
    (hsvc : prog.svc = Syscall.standard)
    (hpc : s0.pc = madv_dontneed_lazy_addr) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = 233#64)
    (hx0 : s0.readReg64 .x0 = addr)
    (hx1 : s0.readReg64 .x1 = 4096#64)
    (hx2 : s0.readReg64 .x2 = 4#64)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hfit : addr.toNat + 4096 ≤ 2 ^ 48) :
    SepWP prog (madv_dontneed_lazy_addr + 4#64) s0
      (memRegion addr 4096 ∗ (memMapped addr 4096 ∗ F))
      (sepPost (fun sf => sf.readReg64 .x0 = 0#64)
        (memRegion addr 4096 ∗ (memMapped addr 4096 ∗ F))) := by
  apply SepWP.step_svc_madvise_dontneed hpc hrun hfetch0 hx8 hx0 hx1 hx2 hal
    (by decide) (by decide) hfit (hsvc := evalInst_svc_madvise hsvc hx8)
  intro m'
  wp_done

theorem madv_noop_hugepage_ok (prog : Program) (s0 : State)
    (addr : BitVec 64) (F : SepProp)
    (hfetch0 : prog.fetch madv_dontneed_lazy_addr = some (.system false 0#16))
    (hsvc : prog.svc = Syscall.standard)
    (hpc : s0.pc = madv_dontneed_lazy_addr) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = 233#64)
    (hx0 : s0.readReg64 .x0 = addr)
    (hx1 : s0.readReg64 .x1 = 4096#64)
    (hx2 : s0.readReg64 .x2 = 14#64)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hfit : addr.toNat + 4096 ≤ 2 ^ 48) :
    SepWP prog (madv_dontneed_lazy_addr + 4#64) s0
      (memRegion addr 4096 ∗ F)
      (sepPost (fun sf => sf.readReg64 .x0 = 0#64 ∧ sf.mem = s0.mem)
        (memRegion addr 4096 ∗ F)) := by
  apply SepWP.step_svc_madvise_noop hpc hrun hfetch0 hx8 hx0 hx1
    (by simp [hx2, MADV_HUGEPAGE]) hal (by decide) (by decide) hfit
    (hsvc := evalInst_svc_madvise hsvc hx8)
  wp_done

theorem munmap_region_ok (prog : Program) (s0 : State)
    (addr : BitVec 64) (F : SepProp)
    (hfetch0 : prog.fetch madv_dontneed_lazy_addr = some (.system false 0#16))
    (hsvc : prog.svc = Syscall.standard)
    (hpc : s0.pc = madv_dontneed_lazy_addr) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = 215#64)
    (hx0 : s0.readReg64 .x0 = addr)
    (hx1 : s0.readReg64 .x1 = 4096#64)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hfit : addr.toNat + 4096 ≤ 2 ^ 48) :
    SepWP prog (madv_dontneed_lazy_addr + 4#64) s0
      (memRegion addr 4096 ∗ (memMapped addr 4096 ∗ F))
      (sepPost (fun sf => sf.readReg64 .x0 = 0#64) F) := by
  apply SepWP.step_svc_munmap hpc hrun hfetch0 hx8 hx0 hx1 hal
    (by decide) (by decide) hfit (hsvc := evalInst_svc_munmap hsvc hx8)
  intro m' phys'
  wp_done

theorem mprotect_protNone_then_rw_ok (prog : Program) (s0 : State)
    (addr : BitVec 64) (F : SepProp)
    (hfetch0 : prog.fetch madv_dontneed_lazy_addr = some (.system false 0#16))
    (hsvc : prog.svc = Syscall.standard)
    (hpc : s0.pc = madv_dontneed_lazy_addr) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = 226#64)
    (hx0 : s0.readReg64 .x0 = addr)
    (hx1 : s0.readReg64 .x1 = 4096#64)
    (hx2 : s0.readReg64 .x2 = 0#64)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hfit : addr.toNat + 4096 ≤ 2 ^ 48) :
    SepWP prog (madv_dontneed_lazy_addr + 4#64) s0
      (memRegion addr 4096 ∗ F)
      (sepPost (fun sf => sf.readReg64 .x0 = 0#64)
        (memRegionProtNone addr 4096 ∗ F)) := by
  apply SepWP.step_svc_mprotect_protNone hpc hrun hfetch0 hx8 hx0 hx1 hx2 hal
    (by decide) (by decide) hfit (hsvc := evalInst_svc_mprotect hsvc hx8)
  intro m'
  wp_done

/-! ## Structural and entailment checks -/

example (a b c : BitVec 64) (n : Nat) :
    SepProp.NoRO ((a ↦₈ₗ) ∗ (b ↦₆₄ₗ) ∗ memRegionLazy c n) := by
  simp

example (a b c : BitVec 64) (n : Nat) :
    SepProp.NoProtNone ((a ↦₈ₗ) ∗ (b ↦₆₄ₗ) ∗ memRegionLazy c n) := by
  simp

example (a : BitVec 64) (v : BitVec 64) : (a ↦₆₄ v) ⊢ |==> (a ↦₆₄ₗ) :=
  pointsTo64_bupd_lazy a v

example {m : Memory} {P : SepProp} {base : BitVec 64} {len : Nat}
    (h : m ⊨ memRegionLazy base len ∗ memMapped base len ∗ P) :
    m.unmapNonFrozen base len ⊨ P :=
  Satisfies.unmapNonFrozen_lazy h

example {m : Memory} {a b : BitVec 64} {w : BitVec 8} {R : SepProp}
    (h : m ⊨ (a ↦₆₄ₗ) ∗ (R ∗ (b ↦₈ w))) :
    m ⊨ (b ↦₈ w) ∗ ((a ↦₆₄ₗ) ∗ R) := by
  sep_entail

/-! ## Rejected loads and unstored upgrades -/

/-- error: wp_sep_access -/
#guard_msgs (error, substring := true) in
example {a : BitVec 64} {v : BitVec 8} {R : SepProp} :
    SepLoad8 a ((a ↦₈ₗ) ∗ R) v := by
  wp_sep_access

/-- error: wp_sep_access -/
#guard_msgs (error, substring := true) in
example {a : BitVec 64} {v : BitVec 64} {R : SepProp} :
    SepLoad64 a ((a ↦₆₄ₗ) ∗ R) v := by
  wp_sep_access

/-- error: frame_split: no match -/
#guard_msgs (error, substring := true) in
example {m : Memory} {a : BitVec 64} {v : BitVec 8} {R : SepProp}
    (h : m ⊨ (a ↦₈ₗ) ∗ R) :
    m ⊨ (a ↦₈ v) ∗ R := by
  sep_entail

/-- error: frame_split: no match -/
#guard_msgs (error, substring := true) in
example {m : Memory} {a : BitVec 64} {v : BitVec 64} {R : SepProp}
    (h : m ⊨ (a ↦₆₄ₗ) ∗ R) :
    m ⊨ (a ↦₆₄ v) ∗ R := by
  sep_entail

end Examples.Testing.MadvFreeTest
