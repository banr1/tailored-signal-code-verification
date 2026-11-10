/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.Lookup
public import CaseStudies.Hashbrown.Proofs.WithCapacity

/-!
# Pure Invariants and Frame Helpers for `reserve_rehash`

Defines the compositional interface `HbRehashInPlaceProp`, prologue and epilogue stack-frame
helpers, and pure SwissTable copy invariants (`NewTablePartialInv`, `OldScanInv`) for
`resize_inner`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.ResizeInternal

open Arm64 Arm64.Obj Arm64.Rust ProofLib ProofLib.StdStartup CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

/-! ## Interface with `RehashInPlace` and Prologue / Epilogue Helpers -/

def HbRehashInPlaceProp (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State)) : Prop :=
  HbExterns ((hbProg P).rebase P.pl.base X) P.pl A →
  ∀ {s1 : State} {mapPtr bm : BitVec 64} {m : Map64} {w : HbHeapMapWitness}
    {oom : State → SepProp},
    s1.pc = P.pl.base + 120#64 → s1.status = .Running →
    s1.spAligned = true → A.CodeInv s1.mem →
    s1.readReg64 .x0 = mapPtr →
    s1.readReg64 .x8 = (bm + 1#64) >>> 3 →
    s1.readReg64 .x20 = bucketMaskToCapacityBV bm →
    s1.readReg64 .x22 = w.items →
    s1.readReg64 .x23 = bm →
    s1.readReg64 .x24 = bm + 1#64 →
    mapPtr.toNat % 8 = 0 → mapPtr.toNat + 32 ≤ 2 ^ 64 →
    SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m →
    w.allocPtr ≠ 0#64 → w.allocPtr.toNat % 8 = 0 →
    w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 →
    w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) →
    m.length + 1 ≤ bucketMaskToCapacity bm / 2 →
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1080#64) s1
      (hbRodata P.pl ∗
       U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
       A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
       slotsDownFrom w.ctrlPtr w.slots ∗
       (w.ctrlPtr ↦ₛ w.ctrl))
      (fun s2 P2 =>
        s2.sp = s1.sp ∧
        s2.spAligned = true ∧
        s2.readReg64 .x0 = 0xffffffffffffffff#64 ∧
        s2.readReg64 (.gpr 28#5) = s1.readReg64 (.gpr 28#5) ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s1 ∧
        StdStatePreserved s1 s2 ∧
        s1.mem.KeepsFrozen s2.mem ∧
        (P2 ⊢ U64MapRepReady P.pl A mapPtr m bm))
      oom

theorem step_str8_perm {prog : Program} {target_pc pc ea : BitVec 64} {val : BitVec 8}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have htrunc : (s.readReg64 rt).truncate 8 = val := by rw [← bitvec_truncate8_truncate32]; exact hval
  let m' := s.mem.write8 ea val
  have hm' := hstore.store hm; have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]; exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write8 s.mem ea val)) hm'

theorem step_str64_perm {prog : Program} {target_pc pc ea val : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm; let m' := s.mem.write64 ea val
  have hm' := hstore.store hm; have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write64 s.mem ea val)) hm'

theorem step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm; have hm2 := hstore2.store hm1
  have hcan1 := hstore1.writable hm; have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))) hm2

theorem step_strSimd128_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.strSimd .Q128 vt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : (s.readVReg128 vt).extractLsb' 0 64 = v1) (hv2 : (s.readVReg128 vt).extractLsb' 64 64 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm; have hm2 := hstore2.store hm1
  have hcan1 := hstore1.writable hm; have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  have hcan16 : s.mem.canWrite ea 16 = true := Memory.canWrite_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.strSimd .Q128 vt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, Memory.write128,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan16, SimdMemSize.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))) hm2

def hbReserveFrame (s0 : State) (vPad : BitVec 64) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((s0.sp - 72#64) ↦₆₄ vPad) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

def HbTopSaved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧ calleeSavedVRegs s = calleeSavedVRegs s0

theorem HbTopSaved.trans_cs {s0 s1 s2 : State}
    (h01 : HbTopSaved s0 s1) (h12 : CalleeSavedPreserved s1 s2) : HbTopSaved s0 s2 :=
  ⟨h12.readReg64_x28.trans h01.1, h12.vregs.trans h01.2⟩

local macro "hb_top " h:ident : tactic => `(tactic|
  exact ⟨by simpa using ($h).1, by simpa [calleeSavedVRegs] using ($h).2⟩)

theorem hbReserve_prologue (P : HbPlaced) (X : String → Option (State → State))
    {target : BitVec 64} {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = P.pl.base) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcont : ∀ (s1 : State) (vPad : BitVec 64),
      s1.pc = P.pl.base + 28#64 → s1.status = .Running → s1.sp = s0.sp - 96#64 →
      s1.spAligned = true → s1.readReg64 .x0 = s0.readReg64 .x0 →
      s1.readReg64 .x1 = s0.readReg64 .x1 → s1.readReg32 .x3 = s0.readReg32 .x3 →
      HbTopSaved s0 s1 → StdStatePreserved s0 s1 →
      SepWP ((hbProg P).rebase P.pl.base X) target s1 (hbReserveFrame s0 vPad ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) target s0 (memRegion (s0.sp - 96#64) 96 ∗ F) post oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  have hsp96 : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := State.spAligned_sub s0 96 hsp
  open_cells (s0.sp - 96#64) 96 12; rename_i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
  rw [show s0.sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 = s0.sp - 8#64 by bv_omega]
  refine step_stp64_perm (rt1 := .x29) (rt2 := .x30) (addr := .PreIndex .sp (-96#64))
    (ea := s0.sp - 96#64) (ea2 := s0.sp - 88#64) (wb := some (.sp, s0.sp - 96#64))
    hpc hrun (by simp) hsp
    (by show (s0.sp + -96#64, some (Reg.sp, s0.sp + -96#64)) = _; rw [show s0.sp + -96#64 = s0.sp - 96#64 by bv_omega])
    (by bv_omega) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  refine step_str64_perm (pc := P.pl.base + 4#64) (rt := .x27) (addr := .Offset .sp 16#64)
    (ea := s0.sp - 80#64) (wb := none) (val := s0.readReg64 .x27) (by simp) (by simp [hrun]) (by simp)
    (by dsimp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, applyWriteback]; simpa [State.writeReg64_sp] using hsp96)
    (by show (s0.sp - 96#64 + 16#64, none) = _; rw [show s0.sp - 96#64 + 16#64 = s0.sp - 80#64 by bv_omega])
    (by simp) (by wp_sep_access) fun m2 hm2 => ?_
  refine step_stp64_perm (pc := P.pl.base + 8#64) (rt1 := .x26) (rt2 := .x25) (addr := .Offset .sp 32#64)
    (ea := s0.sp - 64#64) (ea2 := s0.sp - 56#64) (wb := none) (v1 := s0.readReg64 .x26) (v2 := s0.readReg64 .x25)
    (by simp) (by simp [hrun]) (by simp)
    (by dsimp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, applyWriteback]; simpa [State.writeReg64_sp] using hsp96)
    (by show (s0.sp - 96#64 + 32#64, none) = _; rw [show s0.sp - 96#64 + 32#64 = s0.sp - 64#64 by bv_omega])
    (by bv_omega) (by simp) (by simp) (by wp_sep_access) (by wp_sep_access) fun m3 hm3 => ?_
  refine step_stp64_perm (pc := P.pl.base + 12#64) (rt1 := .x24) (rt2 := .x23) (addr := .Offset .sp 48#64)
    (ea := s0.sp - 48#64) (ea2 := s0.sp - 40#64) (wb := none) (v1 := s0.readReg64 .x24) (v2 := s0.readReg64 .x23)
    (by simp) (by simp [hrun]) (by simp)
    (by dsimp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, applyWriteback]; simpa [State.writeReg64_sp] using hsp96)
    (by show (s0.sp - 96#64 + 48#64, none) = _; rw [show s0.sp - 96#64 + 48#64 = s0.sp - 48#64 by bv_omega])
    (by bv_omega) (by simp) (by simp) (by wp_sep_access) (by wp_sep_access) fun m4 hm4 => ?_
  refine step_stp64_perm (pc := P.pl.base + 16#64) (rt1 := .x22) (rt2 := .x21) (addr := .Offset .sp 64#64)
    (ea := s0.sp - 32#64) (ea2 := s0.sp - 24#64) (wb := none) (v1 := s0.readReg64 .x22) (v2 := s0.readReg64 .x21)
    (by simp) (by simp [hrun]) (by simp)
    (by dsimp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, applyWriteback]; simpa [State.writeReg64_sp] using hsp96)
    (by show (s0.sp - 96#64 + 64#64, none) = _; rw [show s0.sp - 96#64 + 64#64 = s0.sp - 32#64 by bv_omega])
    (by bv_omega) (by simp) (by simp) (by wp_sep_access) (by wp_sep_access) fun m5 hm5 => ?_
  refine step_stp64_perm (pc := P.pl.base + 20#64) (rt1 := .x20) (rt2 := .x19) (addr := .Offset .sp 80#64)
    (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (wb := none) (v1 := s0.readReg64 .x20) (v2 := s0.readReg64 .x19)
    (by simp) (by simp [hrun]) (by simp)
    (by dsimp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, applyWriteback]; simpa [State.writeReg64_sp] using hsp96)
    (by show (s0.sp - 96#64 + 80#64, none) = _; rw [show s0.sp - 96#64 + 80#64 = s0.sp - 16#64 by bv_omega])
    (by bv_omega) (by simp) (by simp) (by wp_sep_access) (by wp_sep_access) fun m6 hm6 => ?_
  dsimp only [applyWriteback]
  refine SepWP.weaken_pre (P' := hbReserveFrame s0 c3 ∗ F)
    (Entails.of_eq (by unfold hbReserveFrame; ac_rfl)) ?_
  rw [show P.pl.base + 20#64 + 4#64 = P.pl.base + 24#64 by simp]; wp_step
  exact hcont _ c3 (by simp) (by simp [hrun]) (by simp) (by simpa [State.spAligned] using hsp96)
    (by simp) (by simp) (by simp [State.readReg32])
    ⟨by simp, by simp [calleeSavedVRegs]⟩
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
     fun a => by simpa using congrFun (hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1))))) a⟩

theorem hbReserve_epilogue (P : HbPlaced) (X : String → Option (State → State))
    {s0 s : State} {vPad : BitVec 64} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = P.pl.base + 1080#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hsp0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = 0xffffffffffffffff#64) (htop : HbTopSaved s0 s)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 Reg.lr → sf.status = .Running → sf.sp = s0.sp →
      sf.readReg64 .x0 = 0xffffffffffffffff#64 →
      CalleeSavedPreserved s0 sf → StdStatePreserved s sf → sf.mem = s.mem →
      post sf (memRegion (s0.sp - 96#64) 96 ∗ F)) :
    SepWP ((hbProg P).rebase P.pl.base X) (s0.readReg64 Reg.lr) s
      (hbReserveFrame s0 vPad ∗ F) post oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  unfold hbReserveFrame
  wp_sym_steps
  refine SepWP.weaken_pre (P' := memRegion (s0.sp - 96#64) 96 ∗ F) ?_ ?_
  · refine sepConj_mono_left ?_
    rw [show memRegion (s0.sp - 96#64) 96 = cells (s0.sp - 96#64) 12 from memRegion_cells (s0.sp - 96#64) 12 (by decide)]
    refine cells_sub_succ_entails 96 12 (cells_sub_succ_entails 88 11 (cells_sub_succ_entails 80 10
      (cells_sub_succ_entails 72 9 (cells_sub_succ_entails 64 8 (cells_sub_succ_entails 56 7
        (cells_sub_succ_entails 48 6 (cells_sub_succ_entails 40 5 (cells_sub_succ_entails 32 4
          (cells_sub_succ_entails 24 3 (cells_sub_succ_entails 16 2 ?_))))))))))
    rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide), Nat.sub_self, cells_zero]
    exact Entails.sepExists_right _ (by rw [sepConj_emp]; exact Entails.refl _)
  · refine SepWP.done (by simp [Reg.lr]) (by simp [hrun])
      (hcont _ (by simp [Reg.lr]) (by simp [hrun]) (by simp) (by simpa [Reg.x0] using hx0) ?_ ?_ rfl)
    · exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simpa using htop.1, by simp [Reg.fp], by simpa [calleeSavedVRegs] using htop.2⟩
    · exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩

/-! ## Pure Invariants for `resize_inner` Fresh-Table Copy -/

theorem sepStore8_pointsToBytes_set {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {v : BitVec 8} {P F : SepProp} (h : P = (base ↦ₛ bs) ∗ F) (hoff : off < bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepStore8 a v P ((base ↦ₛ bs.set off v) ∗ F) := by
  subst ha
  refine SepStore8.of_eq (v := bs.getD off 0#8)
    (F := (base ↦ₛ bs.take off) ∗ (((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1)) ∗ F))
    ?_ ?_
  · rw [h, pointsToBytes_focus8 base bs off hoff]; simp only [sepConj_assoc]
  · have hoff' : off < (bs.set off v).length := by simp [hoff]
    rw [pointsToBytes_focus8 base (bs.set off v) off hoff']
    have hget : (bs.set off v).getD off 0#8 = v := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hoff]; rfl
    rw [hget, List.take_set_of_le (Nat.le_refl off), List.drop_set_of_lt (by omega)]
    simp only [sepConj_assoc]

def setCtrl (bm : BitVec 64) (ctrl : List (BitVec 8)) (idx : Nat) (tag : BitVec 8) :
    List (BitVec 8) :=
  (ctrl.set idx tag).set (setCtrlMirrorIdx bm idx) tag

theorem setCtrlMirrorIdx_eq_of_ge8 {bm : BitVec 64} {idx : Nat}
    (hbm : ValidBucketMask bm) (hge8 : 8 ≤ bm.toNat + 1) (hidx : idx < bm.toNat + 1) :
    setCtrlMirrorIdx bm idx = (if idx < 8 then (bm.toNat + 1) + idx else idx) ∧
    ((BitVec.ofNat 64 idx - 8#64) &&& bm) + 8#64 = BitVec.ofNat 64 (setCtrlMirrorIdx bm idx) ∧
    setCtrlMirrorIdx bm idx < bm.toNat + 1 + 8 := by
  rcases hbm.buckets_bounds_dvd with ⟨_, hb58, q, hq⟩; have h58 : 2 ^ 58 + 16 < 2 ^ 64 := by decide
  have hand_eq : (((BitVec.ofNat 64 idx - 8#64) &&& bm)).toNat =
      if idx < 8 then (bm.toNat + 1) + idx - 8 else idx - 8 := by
    rw [hbm.and_toNat_eq_mod]; by_cases hlt8 : idx < 8
    · simp only [hlt8, ↓reduceIte]
      have h1 : (BitVec.ofNat 64 idx).toNat = idx := Nat.mod_eq_of_lt (by omega)
      have hsub : (BitVec.ofNat 64 idx - 8#64).toNat = 2 ^ 64 - (8 - idx) := by
        rw [BitVec.toNat_sub, h1, show (8#64 : BitVec 64).toNat = 8 from rfl]; omega
      have hq_pos : 1 ≤ q := (Nat.eq_zero_or_pos q).resolve_left fun h0 => by subst h0; simp at hq
      have hmul : (bm.toNat + 1) * q = (bm.toNat + 1) + (bm.toNat + 1) * (q - 1) := by
        conv => lhs; rw [show q = 1 + (q - 1) by omega, Nat.left_distrib, Nat.mul_one]
      rw [hsub, show 2 ^ 64 - (8 - idx) = ((bm.toNat + 1) + idx - 8) + (bm.toNat + 1) * (q - 1) by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    · simp only [hlt8, ↓reduceIte]
      have h1 : (BitVec.ofNat 64 idx).toNat = idx := Nat.mod_eq_of_lt (by omega)
      have hle : 8#64 ≤ BitVec.ofNat 64 idx := by rw [BitVec.le_def, h1]; exact Nat.le_of_not_lt hlt8
      rw [BitVec.toNat_sub_of_le hle, h1, show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hmir_eq : setCtrlMirrorIdx bm idx = if idx < 8 then (bm.toNat + 1) + idx else idx := by
    unfold setCtrlMirrorIdx; rw [BitVec.toNat_add, hand_eq]
    by_cases hlt8 : idx < 8 <;> simp only [hlt8, ↓reduceIte, BitVec.toNat_ofNat] <;> omega
  exact ⟨hmir_eq, by unfold setCtrlMirrorIdx; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [hmir_eq]; split <;> omega⟩

theorem setCtrl_props_of_ge8 {bm : BitVec 64} {ctrl : List (BitVec 8)} {idx : Nat}
    {tag : BitVec 8} (hbm : ValidBucketMask bm) (hge8 : 8 ≤ bm.toNat + 1)
    (hmir : CtrlMirrorInv (bm.toNat + 1) ctrl) (hidx : idx < bm.toNat + 1) (htag : ValidTag tag) :
    (setCtrl bm ctrl idx tag).length = ctrl.length ∧
    CtrlMirrorInv (bm.toNat + 1) (setCtrl bm ctrl idx tag) ∧
    (∀ (j : Nat) (hj : j < bm.toNat + 1),
      (setCtrl bm ctrl idx tag)[j]'(by simp [setCtrl, hmir.1]; omega) =
        if j = idx then tag else ctrl[j]'(by have := hmir.1; omega)) ∧
    (setCtrl bm ctrl idx tag).take (bm.toNat + 1) = (ctrl.take (bm.toNat + 1)).set idx tag ∧
    (∀ c ∈ setCtrl bm ctrl idx tag, c = tag ∨ c ∈ ctrl) := by
  obtain ⟨hmir_idx, _, _⟩ := setCtrlMirrorIdx_eq_of_ge8 hbm hge8 hidx; have hlen := hmir.1
  have hget_lt : ∀ (j : Nat) (hj : j < bm.toNat + 1),
      (setCtrl bm ctrl idx tag)[j]'(by simp [setCtrl, hlen]; omega) =
        if j = idx then tag else ctrl[j]'(by omega) := by
    intro j hj; simp only [setCtrl, List.getElem_set]
    have hne_m : setCtrlMirrorIdx bm idx = j → j = idx := by rw [hmir_idx]; split <;> omega
    by_cases hji : j = idx
    · subst hji; split <;> simp
    · simp [show ¬ (setCtrlMirrorIdx bm idx = j) from fun h => hji (hne_m h), Ne.symm hji, hji]
  have hmem_sub : ∀ c ∈ setCtrl bm ctrl idx tag, c = tag ∨ c ∈ ctrl := fun c hc =>
    (List.mem_or_eq_of_mem_set hc).elim
      (fun h1 => (List.mem_or_eq_of_mem_set h1).elim Or.inr Or.inl) Or.inl
  refine ⟨by simp [setCtrl], ⟨by simp [setCtrl, hlen],
    fun c hc => (hmem_sub c hc).elim (· ▸ htag) (hmir.2.1 c), fun h4 => by omega, ?_⟩,
    hget_lt, ?_, hmem_sub⟩
  · intro _ j hj
    rw [List.getElem?_eq_getElem (by simp [setCtrl, hlen]; omega),
        List.getElem?_eq_getElem (by simp [setCtrl, hlen]; omega)]; congr 1
    rw [hget_lt j (by omega)]; simp only [setCtrl, List.getElem_set, hmir_idx]
    by_cases hji : j = idx
    · subst hji; simp [hj]
    · have hm0 := hmir.2.2.2 hge8 j hj
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hm0
      by_cases hlt8 : idx < 8
      · simp only [hlt8, ↓reduceIte, hji, show ¬ (bm.toNat + 1 + idx = bm.toNat + 1 + j) by omega,
          show ¬ (idx = bm.toNat + 1 + j) by omega]; exact Option.some.inj hm0
      · simp only [hlt8, ↓reduceIte, hji, show ¬ (idx = bm.toNat + 1 + j) by omega]
        exact Option.some.inj hm0
  · apply List.ext_getElem (by simp [setCtrl, hlen]); intro j hj1 _
    rw [List.getElem_take, hget_lt j (by simp [setCtrl, hlen] at hj1; omega), List.getElem_set]
    by_cases hji : idx = j
    · subst hji; simp
    · simp [hji, Ne.symm hji]

theorem nextResizeMask_capacity_gt {bm : BitVec 64}
    (hbm : ValidBucketMask bm) (hcap : bucketMaskToCapacity bm < MaxHashbrownCapacity) :
    bucketMaskToCapacity bm < bucketMaskToCapacity (nextResizeMask bm) := by
  have hne := hbm.ne_zero
  obtain ⟨hv_next, hmul2⟩ := ValidBucketMask.nextResizeMask_valid hbm hcap
  rcases hbm with ⟨exp, hlo, hhi, hbm_eq⟩
  have hexp_lt58 : exp < 58 := by
    by_cases h58 : exp = 58
    · subst h58
      rw [hbm_eq, show bucketMaskToCapacity (BitVec.ofNat 64 (2 ^ 58 - 1)) = MaxHashbrownCapacity by decide] at hcap
      omega
    · omega
  have hbkt := ValidBucketMask.buckets_eq hlo hhi hbm_eq
  have hcap_eq := ValidBucketMask.capacity_eq hlo hhi hbm_eq
  have hnext_eq : nextResizeMask bm = BitVec.ofNat 64 (2 ^ (exp + 1) - 1) := by
    simp only [nextResizeMask, hne, ↓reduceIte, hbkt]
    congr 1; rw [Nat.pow_succ, Nat.mul_comm]
  have hcap_next := ValidBucketMask.capacity_eq (exp := exp + 1) (by omega) (by omega) hnext_eq
  by_cases he2 : exp = 2
  · subst he2; simp only [↓reduceIte] at hcap_eq; simp only [show ¬ (2 + 1 = 2) by decide, ↓reduceIte] at hcap_next
    omega
  · simp only [he2, ↓reduceIte] at hcap_eq
    simp only [show ¬ (exp + 1 = 2) by omega, ↓reduceIte] at hcap_next
    have hpow2 : 2 ^ (exp + 1 - 3) = 2 * 2 ^ (exp - 3) := by
      rw [show exp + 1 - 3 = (exp - 3) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hpos : 1 ≤ 2 ^ (exp - 3) := Nat.one_le_pow _ _ (by decide)
    omega

theorem cntTrue_pos_of_true {p : Nat → Bool} {x : Nat} :
    ∀ n, x < n → p x = true → 1 ≤ cntTrue p n
  | 0, hx, _ => by omega
  | n + 1, hx, hpx => by
    simp only [cntTrue]
    by_cases hxn : x = n
    · subst hxn; simp [hpx]
    · have := cntTrue_pos_of_true n (by omega) hpx; split <;> omega

theorem countP_set_false_to_true {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (idx : Nat) (hidx : idx < xs.length) (y : α),
      p xs[idx] = false → p y = true → (xs.set idx y).countP p = xs.countP p + 1
  | [], _, hidx, _, _, _ => by simp at hidx
  | x :: _, 0, _, _, hfalse, htrue => by
    dsimp only [List.getElem_cons_zero] at hfalse; simp [hfalse, htrue]
  | _ :: rest, idx + 1, hidx, y, hfalse, htrue => by
    simp only [List.set, List.countP_cons]
    rw [countP_set_false_to_true p rest idx (by simp at hidx; omega) y (by simpa using hfalse) htrue]
    omega

def oldFullAt (oldCtrl : List (BitVec 8)) (B i : Nat) : Bool :=
  if h : i < B ∧ i < oldCtrl.length then isFullTag (oldCtrl[i]'h.2) else false

theorem oldFullAt_eq_of_lt {oldCtrl : List (BitVec 8)} {B i : Nat}
    (hi : i < B) (hlen : B ≤ oldCtrl.length) :
    oldFullAt oldCtrl B i = isFullTag (oldCtrl[i]'(by omega)) := by
  unfold oldFullAt; have h : i < B ∧ i < oldCtrl.length := ⟨hi, by omega⟩; simp [h]

theorem cntTrue_le_take_countP {oldCtrl : List (BitVec 8)} {p : Nat → Bool} :
    ∀ n, (hn : n ≤ oldCtrl.length) →
      (∀ (r : Nat) (hr : r < n), p r = true → isFullTag (oldCtrl[r]'(by omega)) = true) →
      cntTrue p n ≤ (oldCtrl.take n).countP isFullTag
  | 0, _, _ => by simp [cntTrue]
  | n + 1, hn, hp => by
    have ih := cntTrue_le_take_countP n (by omega) (fun r hr => hp r (by omega))
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        List.countP_append, List.countP_singleton]
    simp only [cntTrue]
    cases hpn : p n with
    | false => simp; omega
    | true => simp [hp n (by omega) hpn]; omega

theorem cntTrue_eq_take_countP {oldCtrl : List (BitVec 8)} {p : Nat → Bool} :
    ∀ n, (hn : n ≤ oldCtrl.length) →
      (∀ (r : Nat) (hr : r < n), p r = isFullTag (oldCtrl[r]'(by omega))) →
      cntTrue p n = (oldCtrl.take n).countP isFullTag
  | 0, _, _ => by simp [cntTrue]
  | n + 1, hn, hp => by
    have ih := cntTrue_eq_take_countP n (by omega) (fun r hr => hp r (by omega))
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        List.countP_append, List.countP_singleton]
    simp only [cntTrue, ih, hp n (by omega)]

structure NewTablePartialInv {bm oldGl oldItems : BitVec 64}
    {oldCtrl : List (BitVec 8)} {oldSlots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (oldInv : SwissTableInv bm oldGl oldItems oldCtrl oldSlots m)
    (bm' : BitVec 64) (copied : Nat → Bool)
    (newCtrl : List (BitVec 8)) (newSlots : List (BitVec 64 × BitVec 64)) : Prop where
  validMask : ValidBucketMask bm'
  ge8 : 8 ≤ bm'.toNat + 1
  cap_gt : m.length < bucketMaskToCapacity bm'
  slots_len : newSlots.length = bm'.toNat + 1
  mirror : CtrlMirrorInv (bm'.toNat + 1) newCtrl
  no_deleted : ∀ c ∈ newCtrl, c ≠ tagDeleted
  copied_only_full : ∀ (r : Nat) (_ : r < bm.toNat + 1), copied r = true →
    isFullTag (oldCtrl[r]'(by have := oldInv.mirror.1; omega)) = true
  countFull_eq : (newCtrl.take (bm'.toNat + 1)).countP isFullTag = cntTrue copied (bm.toNat + 1)
  full_bwd : ∀ (j : Nat) (hj : j < bm'.toNat + 1),
    isFullTag (newCtrl[j]'(by have := mirror.1; omega)) = true →
      newCtrl[j]'(by have := mirror.1; omega) = h2Tag (newSlots[j]'(by omega)).1 ∧
      ProbeReachable bm' newCtrl (newSlots[j]'(by omega)).1 j ∧
      ∃ (r : Nat) (hr : r < bm.toNat + 1), copied r = true ∧
        newSlots[j]'(by omega) = oldSlots[r]'(by have := oldInv.slots_len; omega)
  copied_fwd : ∀ (r : Nat) (hr : r < bm.toNat + 1), copied r = true →
    ∃ (j : Nat) (hj : j < bm'.toNat + 1),
      isFullTag (newCtrl[j]'(by have := mirror.1; omega)) = true ∧
      newSlots[j]'(by omega) = oldSlots[r]'(by have := oldInv.slots_len; omega)
  full_inj : ∀ (i j : Nat) (hi : i < bm'.toNat + 1) (hj : j < bm'.toNat + 1),
    isFullTag (newCtrl[i]'(by have := mirror.1; omega)) = true →
    isFullTag (newCtrl[j]'(by have := mirror.1; omega)) = true →
    (newSlots[i]'(by omega)).1 = (newSlots[j]'(by omega)).1 → i = j

section
variable {bm oldGl oldItems : BitVec 64} {oldCtrl : List (BitVec 8)}
  {oldSlots : List (BitVec 64 × BitVec 64)} {m : Map64}
  {oldInv : SwissTableInv bm oldGl oldItems oldCtrl oldSlots m} {bm' : BitVec 64}
  {copied : Nat → Bool} {newCtrl : List (BitVec 8)} {newSlots : List (BitVec 64 × BitVec 64)}

theorem NewTablePartialInv.init
    (oldInv : SwissTableInv bm oldGl oldItems oldCtrl oldSlots m)
    (hbm' : ValidBucketMask bm') (hge8 : 8 ≤ bm'.toNat + 1)
    (hcap_gt : m.length < bucketMaskToCapacity bm') (hsl : newSlots.length = bm'.toNat + 1)
    (hcop : ∀ r < bm.toNat + 1, copied r = false) :
    NewTablePartialInv oldInv bm' copied (List.replicate (bm'.toNat + 1 + 8) tagEmpty) newSlots := by
  have hcnt0 : cntTrue copied (bm.toNat + 1) = 0 := by
    rw [cntTrue_congr (q := fun _ => false) (bm.toNat + 1) hcop]
    clear hcop; induction (bm.toNat + 1) with | zero => rfl | succ n ih => simp [cntTrue, ih]
  refine ⟨hbm', hge8, hcap_gt, hsl, CtrlMirrorInv_init (bm'.toNat + 1) (Or.inr hge8),
    fun c hc => by rw [(List.mem_replicate.mp hc).2]; decide,
    fun r hr hc => (by rw [hcop r hr] at hc; cases hc), ?_,
    fun _ _ hf => (by simp [List.getElem_replicate] at hf),
    fun r hr hc => (by rw [hcop r hr] at hc; cases hc),
    fun _ _ _ _ hf _ _ => (by simp [List.getElem_replicate] at hf)⟩
  rw [hcnt0, List.take_replicate, Nat.min_eq_left (by omega), List.countP_eq_zero]
  intro c hc; rw [(List.mem_replicate.mp hc).2]; decide

theorem NewTablePartialInv.special_eq_empty
    (h : NewTablePartialInv oldInv bm' copied newCtrl newSlots) {c : BitVec 8} (hmem : c ∈ newCtrl) :
    isSpecialTag c = true ↔ c = tagEmpty :=
  ⟨fun hs => (ValidTag.special_cases (h.mirror.2.1 c hmem) hs).resolve_right (h.no_deleted c hmem),
   fun he => he ▸ by decide⟩

theorem NewTablePartialInv.exists_empty_probe_group
    (h : NewTablePartialInv oldInv bm' copied newCtrl newSlots) (k : BitVec 64) :
    ∃ step < numGroups bm', tagEmpty ∈ ctrlGroupAt newCtrl (probePos bm' k step) := by
  apply exists_empty_probe_group_of_empty_slot h.validMask h.mirror ?_ k
  have hcnt_le : cntTrue copied (bm.toNat + 1) ≤ m.length := by
    rw [← oldInv.countFull_eq]
    exact cntTrue_le_take_countP (bm.toNat + 1) (by have := oldInv.mirror.1; omega) h.copied_only_full
  have := h.validMask.capacity_bounds.2; have := h.cap_gt
  have hfull_lt : (newCtrl.take (bm'.toNat + 1)).countP isFullTag < bm'.toNat + 1 := by
    rw [h.countFull_eq]; omega
  apply Classical.byContradiction; intro hno
  have hpfx_len : (newCtrl.take (bm'.toNat + 1)).length = bm'.toNat + 1 := by simp [h.mirror.1]
  have hall_full : (newCtrl.take (bm'.toNat + 1)).countP (fun a => decide ¬isFullTag a = true) = 0 := by
    rw [List.countP_eq_zero]; intro c hc hf
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    have hi_b : i < bm'.toNat + 1 := by simp [h.mirror.1] at hi; exact hi
    simp only [List.getElem_take, decide_eq_true_eq] at hf
    have hmem : newCtrl[i]'(by have := h.mirror.1; omega) ∈ newCtrl := List.getElem_mem _
    exact (h.mirror.2.1 _ hmem).elim (fun e => hno ⟨i, hi_b, e⟩)
      (fun hor => hor.elim (h.no_deleted _ hmem) (fun hlt => hf ((isFullTag_iff_lt_0x80 _).mpr hlt)))
  rw [List.length_eq_countP_add_countP isFullTag, hall_full] at hpfx_len; omega

theorem NewTablePartialInv.insert_step
    (h : NewTablePartialInv oldInv bm' copied newCtrl newSlots)
    {oldIdx : Nat} (holdIdx : oldIdx < bm.toNat + 1)
    (holdFull : isFullTag (oldCtrl[oldIdx]'(by have := oldInv.mirror.1; omega)) = true)
    (hnot_copied : copied oldIdx = false)
    {step lane : Nat} (hstep : step < numGroups bm') (hlane : lane < 8)
    (hprev : ∀ s' < step, tagEmpty ∉ ctrlGroupAt newCtrl
      (probePos bm' (oldSlots[oldIdx]'(by have := oldInv.slots_len; omega)).1 s'))
    (hemp : newCtrl[(probePos bm' (oldSlots[oldIdx]'(by have := oldInv.slots_len; omega)).1 step + lane) %
      (bm'.toNat + 1)]'(by
        have := h.mirror.1; have := Nat.mod_lt
          (probePos bm' (oldSlots[oldIdx]'(by have := oldInv.slots_len; omega)).1 step + lane)
          (by omega : 0 < bm'.toNat + 1); omega) = tagEmpty)
    {copied' : Nat → Bool}
    (hcopied' : ∀ r < bm.toNat + 1, copied' r = (copied r || (oldIdx == r))) :
    let kv := oldSlots[oldIdx]'(by have := oldInv.slots_len; omega)
    let newIdx := (probePos bm' kv.1 step + lane) % (bm'.toNat + 1)
    NewTablePartialInv oldInv bm' copied'
      (setCtrl bm' newCtrl newIdx (h2Tag kv.1)) (newSlots.set newIdx kv) := by
  intro kv newIdx; have hnewIdx : newIdx < bm'.toNat + 1 := Nat.mod_lt _ (by omega)
  obtain ⟨_, hmir', hget', htake', hmem_sub⟩ :=
    setCtrl_props_of_ge8 h.validMask h.ge8 h.mirror hnewIdx (Or.inr (Or.inr (h2Tag_lt_0x80 kv.1)))
  let newCtrl' := setCtrl bm' newCtrl newIdx (h2Tag kv.1)
  have hlane_eq : ∀ (p l : Nat) (hp : p < bm'.toNat + 1) (hl : l < 8),
      (ctrlGroupAt newCtrl' p)[l]? =
        if (p + l) % (bm'.toNat + 1) = newIdx then some (h2Tag kv.1) else (ctrlGroupAt newCtrl p)[l]? := by
    intro p l hp hl
    rw [ctrlGroupAt_getElem? (by rw [hmir'.1]; omega) hl, ctrlGroupAt_getElem? (by rw [h.mirror.1]; omega) hl,
        CtrlMirrorInv.lane_eq_mod_of_ge8 hmir' h.ge8 hp hl, CtrlMirrorInv.lane_eq_mod_of_ge8 h.mirror h.ge8 hp hl,
        hget' _ (Nat.mod_lt _ (by omega))]; split <;> rfl
  have hno_new_empty : ∀ (p : Nat) (hp : p < bm'.toNat + 1),
      tagEmpty ∉ ctrlGroupAt newCtrl p → tagEmpty ∉ ctrlGroupAt newCtrl' p := by
    intro p hp hne hmem'; rw [mem_ctrlGroupAt_iff (by rw [hmir'.1]; omega)] at hmem'
    obtain ⟨l, hl, heq'⟩ := hmem'
    rw [CtrlMirrorInv.lane_eq_mod_of_ge8 hmir' h.ge8 hp hl, hget' _ (Nat.mod_lt _ (by omega))] at heq'
    by_cases hmod : (p + l) % (bm'.toNat + 1) = newIdx
    · simp only [hmod, ↓reduceIte] at heq'; exact h2Tag_ne_empty kv.1 heq'
    · simp only [hmod, ↓reduceIte] at heq'
      exact hne ((mem_ctrlGroupAt_iff (by rw [h.mirror.1]; omega) _).mpr
        ⟨l, hl, by rwa [CtrlMirrorInv.lane_eq_mod_of_ge8 h.mirror h.ge8 hp hl]⟩)
  have hreach_pres : ∀ (k0 : BitVec 64) (j : Nat),
      ProbeReachable bm' newCtrl k0 j → ProbeReachable bm' newCtrl' k0 j := by
    rintro k0 j ⟨s0, l0, hs0, hl0, htag0, hidx0, hprev0⟩
    refine ⟨s0, l0, hs0, hl0, ?_, hidx0, fun s' hs' =>
      hno_new_empty _ (probePos_lt_buckets h.validMask k0 s') (hprev0 s' hs')⟩
    have hp0 := probePos_lt_buckets h.validMask k0 s0; rw [hlane_eq _ l0 hp0 hl0]
    by_cases hmod : (probePos bm' k0 s0 + l0) % (bm'.toNat + 1) = newIdx
    · rw [ctrlGroupAt_getElem? (by rw [h.mirror.1]; omega) hl0, Option.some.injEq,
          CtrlMirrorInv.lane_eq_mod_of_ge8 h.mirror h.ge8 hp0 hl0] at htag0
      have hemp0 : newCtrl[(probePos bm' k0 s0 + l0) % (bm'.toNat + 1)]'(by
          have := h.mirror.1; have := Nat.mod_lt (probePos bm' k0 s0 + l0) (by omega : 0 < bm'.toNat + 1); omega) =
          tagEmpty := by simp only [hmod]; exact hemp
      exact False.elim (h2Tag_ne_empty k0 (htag0.symm.trans hemp0))
    · simp [hmod, htag0]
  have hreach_new : ProbeReachable bm' newCtrl' kv.1 newIdx :=
    ⟨step, lane, hstep, hlane, by rw [hlane_eq _ lane (probePos_lt_buckets h.validMask kv.1 step) hlane]; simp [newIdx],
     rfl, fun s' hs' => hno_new_empty _ (probePos_lt_buckets h.validMask kv.1 s') (hprev s' hs')⟩
  have hkey_fresh : ∀ (j : Nat) (hj : j < bm'.toNat + 1),
      isFullTag (newCtrl[j]'(by have := h.mirror.1; omega)) = true →
      (newSlots[j]'(by have := h.slots_len; omega)).1 ≠ kv.1 := fun j hj hfj hkeq => by
    obtain ⟨_, _, r, hr, hcr, hsr⟩ := h.full_bwd j hj hfj
    have hrold := oldInv.full_inj r oldIdx hr holdIdx (h.copied_only_full r hr hcr) holdFull (by rw [← hsr]; exact hkeq)
    subst hrold; rw [hcr] at hnot_copied; cases hnot_copied
  refine ⟨h.validMask, h.ge8, h.cap_gt, by simp [h.slots_len], hmir',
    fun c hc => (hmem_sub c hc).elim (fun e => e ▸ h2Tag_ne_deleted kv.1) (h.no_deleted c),
    fun r hr hcr => ?_, ?_, fun j hj hfj => ?_, fun r hr hcr => ?_, fun i j hi hj hfi hfj hkeq => ?_⟩
  · rw [hcopied' r hr, Bool.or_eq_true] at hcr
    exact hcr.elim (h.copied_only_full r hr) (fun heq => by rw [beq_iff_eq] at heq; subst heq; exact holdFull)
  · change (newCtrl'.take (bm'.toNat + 1)).countP isFullTag = cntTrue copied' (bm.toNat + 1)
    have hpfx_len : (newCtrl.take (bm'.toNat + 1)).length = bm'.toNat + 1 := by simp [h.mirror.1]
    rw [htake', countP_set_false_to_true isFullTag (newCtrl.take (bm'.toNat + 1)) newIdx (by omega)
        (h2Tag kv.1) (by rw [List.getElem_take, hemp]; rfl) (isFullTag_h2Tag kv.1), h.countFull_eq,
      cntTrue_congr (p := copied') (q := fun r => copied r || (oldIdx == r)) (bm.toNat + 1) hcopied',
      cntTrue_set copied oldIdx (bm.toNat + 1) holdIdx hnot_copied]
  · change isFullTag (newCtrl'[j]'(by rw [hmir'.1]; omega)) = true at hfj; rw [hget' j hj] at hfj
    by_cases hji : j = newIdx
    · subst hji; have hsget : (newSlots.set newIdx kv)[newIdx]'(by simp [h.slots_len]; omega) = kv := by simp
      exact ⟨by rw [hget' newIdx hnewIdx, hsget]; simp, by rw [hsget]; exact hreach_new,
        oldIdx, holdIdx, by rw [hcopied' oldIdx holdIdx]; simp, hsget⟩
    · simp only [hji, ↓reduceIte] at hfj
      have hsget : (newSlots.set newIdx kv)[j]'(by simp [h.slots_len]; omega) =
          newSlots[j]'(by rw [h.slots_len]; omega) := by simp [Ne.symm hji]
      obtain ⟨htag_j, hreach_j, r, hr, hcr, hsr⟩ := h.full_bwd j hj hfj
      exact ⟨by rw [hget' j hj, hsget]; simp [hji, htag_j], by rw [hsget]; exact hreach_pres _ j hreach_j,
        r, hr, by rw [hcopied' r hr, hcr]; rfl, hsget.trans hsr⟩
  · rw [hcopied' r hr, Bool.or_eq_true] at hcr; rcases hcr with hcr0 | heq
    · obtain ⟨j, hj, hfj, hsj⟩ := h.copied_fwd r hr hcr0
      have hne_j : j ≠ newIdx := fun e => by subst e; rw [hemp] at hfj; cases hfj
      exact ⟨j, hj, by rw [hget' j hj]; simp [hne_j, hfj], by simp [Ne.symm hne_j, hsj]⟩
    · rw [beq_iff_eq] at heq; subst heq
      exact ⟨newIdx, hnewIdx, by rw [hget' newIdx hnewIdx]; simp, by simp [kv]⟩
  · rw [hget' i hi] at hfi; rw [hget' j hj] at hfj
    by_cases hi_eq : i = newIdx <;> by_cases hj_eq : j = newIdx
    · exact hi_eq.trans hj_eq.symm
    · subst hi_eq; simp only [hj_eq, ↓reduceIte] at hfj
      rw [show (newSlots.set newIdx kv)[newIdx]'(by simp [h.slots_len]; omega) = kv by simp,
          show (newSlots.set newIdx kv)[j]'(by simp [h.slots_len]; omega) =
            newSlots[j]'(by rw [h.slots_len]; omega) by simp [Ne.symm hj_eq]] at hkeq
      exact False.elim (hkey_fresh j hj hfj hkeq.symm)
    · subst hj_eq; simp only [hi_eq, ↓reduceIte] at hfi
      rw [show (newSlots.set newIdx kv)[i]'(by simp [h.slots_len]; omega) =
            newSlots[i]'(by rw [h.slots_len]; omega) by simp [Ne.symm hi_eq],
          show (newSlots.set newIdx kv)[newIdx]'(by simp [h.slots_len]; omega) = kv by simp] at hkeq
      exact False.elim (hkey_fresh i hi hfi hkeq)
    · simp only [hi_eq, hj_eq, ↓reduceIte] at hfi hfj
      rw [show (newSlots.set newIdx kv)[i]'(by simp [h.slots_len]; omega) =
            newSlots[i]'(by rw [h.slots_len]; omega) by simp [Ne.symm hi_eq],
          show (newSlots.set newIdx kv)[j]'(by simp [h.slots_len]; omega) =
            newSlots[j]'(by rw [h.slots_len]; omega) by simp [Ne.symm hj_eq]] at hkeq
      exact h.full_inj i j hi hj hfi hfj hkeq

theorem NewTablePartialInv.to_swissTableInv
    (h : NewTablePartialInv oldInv bm' copied newCtrl newSlots)
    (hall : ∀ (r : Nat) (hr : r < bm.toNat + 1),
      isFullTag (oldCtrl[r]'(by have := oldInv.mirror.1; omega)) = true → copied r = true) :
    SwissTableInv bm' (bucketMaskToCapacityBV bm' - oldItems) oldItems newCtrl newSlots m ∧
    0 < (bucketMaskToCapacityBV bm' - oldItems).toNat := by
  have hcnt_eq : cntTrue copied (bm.toNat + 1) = m.length := by
    rw [← oldInv.countFull_eq]
    refine cntTrue_eq_take_countP (bm.toNat + 1) (by have := oldInv.mirror.1; omega) fun r hr => ?_
    cases hc : copied r with
    | true => exact (h.copied_only_full r hr hc).symm
    | false =>
      cases hf : isFullTag (oldCtrl[r]'(by have := oldInv.mirror.1; omega)) with
      | false => rfl
      | true => rw [hall r hr hf] at hc; cases hc
  have hcap64 : bucketMaskToCapacity bm' < 2 ^ 64 := by
    have := h.validMask.capacity_bounds.2; obtain ⟨_, hb58, _⟩ := h.validMask.buckets_bounds_dvd
    have : 2 ^ 58 < 2 ^ 64 := (by decide); omega
  have hitems_nat : oldItems.toNat = m.length := by
    rw [oldInv.items_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.cap_gt; omega)]
  have hgl_nat : (bucketMaskToCapacityBV bm' - oldItems).toNat = bucketMaskToCapacity bm' - m.length := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hitems_nat]; exact Nat.le_of_lt h.cap_gt), hitems_nat]; rfl
  have hdel0 : (newCtrl.take (bm'.toNat + 1)).countP (· == tagDeleted) = 0 :=
    List.countP_eq_zero.mpr fun c hc => by simp [h.no_deleted c (List.mem_of_mem_take hc)]
  refine ⟨⟨h.validMask, oldInv.wf, h.slots_len, h.mirror, oldInv.items_eq,
      by rw [hgl_nat]; omega, by rw [hdel0, hgl_nat]; have := h.cap_gt; omega,
      h.countFull_eq.trans hcnt_eq, fun j hj hfj => ?_, h.full_inj, fun k v hlook => ?_⟩,
    by rw [hgl_nat]; have := h.cap_gt; omega⟩
  · obtain ⟨htag, hreach, r, hr, hcr, hsr⟩ := h.full_bwd j hj hfj
    exact ⟨htag, by rw [hsr]; exact (oldInv.full_sound r hr (h.copied_only_full r hr hcr)).2.1, hreach⟩
  · obtain ⟨r, hr, hfr, hsr⟩ := oldInv.complete k v hlook
    obtain ⟨j, hj, hfj, hsj⟩ := h.copied_fwd r hr (hall r hr hfr); exact ⟨j, hj, hfj, hsj.trans hsr⟩

end

def copiedAt (oldCtrl : List (BitVec 8)) (B grpBase : Nat) (b : BitVec 8) (i : Nat) : Bool :=
  oldFullAt oldCtrl B i &&
    (decide (i < grpBase) || (decide (grpBase ≤ i ∧ i < grpBase + 8) && !b.getLsbD (i - grpBase)))

def uncopiedAt (oldCtrl : List (BitVec 8)) (B grpBase : Nat) (b : BitVec 8) (i : Nat) : Bool :=
  oldFullAt oldCtrl B i &&
    (decide (grpBase + 8 ≤ i) || (decide (grpBase ≤ i ∧ i < grpBase + 8) && b.getLsbD (i - grpBase)))

theorem copiedAt_uncopiedAt_pointwise (oldCtrl : List (BitVec 8)) (B grpBase : Nat)
    (b : BitVec 8) (i : Nat) :
    (if copiedAt oldCtrl B grpBase b i then 1 else 0) +
      (if uncopiedAt oldCtrl B grpBase b i then 1 else 0) =
      (if oldFullAt oldCtrl B i then 1 else 0) := by
  unfold copiedAt uncopiedAt
  cases hf : oldFullAt oldCtrl B i <;> simp only [Bool.false_and, Bool.true_and, ↓reduceIte]
  · rfl
  · by_cases h1 : i < grpBase
    · have h2 : ¬ (grpBase ≤ i ∧ i < grpBase + 8) := by omega
      have h3 : ¬ (grpBase + 8 ≤ i) := by omega
      simp [h1, h2, h3]
    · by_cases h2 : grpBase ≤ i ∧ i < grpBase + 8
      · have h3 : ¬ (grpBase + 8 ≤ i) := by omega
        simp only [h1, h2.1, h2.2, h3, and_self, decide_false, decide_true, Bool.false_or, Bool.true_and]
        cases b.getLsbD (i - grpBase) <;> rfl
      · have h3 : grpBase + 8 ≤ i := by omega
        simp [h1, h2, h3]

theorem copiedAt_uncopiedAt_sum (oldCtrl : List (BitVec 8)) (B grpBase : Nat)
    (b : BitVec 8) (hlen : B ≤ oldCtrl.length) :
    cntTrue (copiedAt oldCtrl B grpBase b) B + cntTrue (uncopiedAt oldCtrl B grpBase b) B =
      (oldCtrl.take B).countP isFullTag := by
  have hsum : ∀ n,
      cntTrue (copiedAt oldCtrl B grpBase b) n + cntTrue (uncopiedAt oldCtrl B grpBase b) n =
        cntTrue (oldFullAt oldCtrl B) n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [cntTrue]; have := copiedAt_uncopiedAt_pointwise oldCtrl B grpBase b n; omega
  rw [hsum B]
  exact cntTrue_eq_take_countP B hlen (fun r hr => oldFullAt_eq_of_lt hr hlen)

structure OldScanInv (bm : BitVec 64) (oldCtrl : List (BitVec 8))
    (grpBase : Nat) (b : BitVec 8) : Prop where
  validMask : ValidBucketMask bm
  mirror : CtrlMirrorInv (bm.toNat + 1) oldCtrl
  bound : (bm.toNat + 1 = 4 ∧ grpBase = 0) ∨ (8 ≤ bm.toNat + 1 ∧ grpBase % 8 = 0 ∧ grpBase + 8 ≤ bm.toNat + 1)
  bits_full : ∀ (j : Nat) (_ : j < 8), b.getLsbD j = true →
    grpBase + j < bm.toNat + 1 ∧ isFullTag (oldCtrl[grpBase + j]'(by have := mirror.1; omega)) = true

theorem OldScanInv.init {bm : BitVec 64} {oldCtrl : List (BitVec 8)}
    (hbm : ValidBucketMask bm) (hmir : CtrlMirrorInv (bm.toNat + 1) oldCtrl) :
    let b0 := fullBits8 (ctrlGroupWord oldCtrl 0)
    OldScanInv bm oldCtrl 0 b0 ∧ (∀ r < bm.toNat + 1, copiedAt oldCtrl (bm.toNat + 1) 0 b0 r = false) ∧
    cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) 0 b0) (bm.toNat + 1) =
      (oldCtrl.take (bm.toNat + 1)).countP isFullTag := by
  intro b0; have hb_cases := hbm.buckets_cases
  have hbits : ∀ (j : Nat) (hj : j < 8), b0.getLsbD j = true →
      0 + j < bm.toNat + 1 ∧ isFullTag (oldCtrl[0 + j]'(by have := hmir.1; omega)) = true := by
    intro j hj hbit
    have hfull : isFullTag (oldCtrl[0 + j]'(by have := hmir.1; omega)) = true := by
      have h1 := (getLsbD_fullBits8 (ctrlGroupWord oldCtrl 0) hj).symm.trans hbit
      rwa [getLane8_ctrlGroupWord_eq_getElem (by have := hmir.1; omega) hj] at h1
    rcases hb_cases with h4 | ⟨h8, _⟩
    · by_cases hj4 : j < 4
      · exact ⟨by omega, hfull⟩
      · have hemp := (hmir.2.2.1 h4).1 (j - 4) (by omega)
        rw [show 4 + (j - 4) = 0 + j by omega, List.getElem?_eq_getElem (by have := hmir.1; omega)] at hemp
        rw [Option.some.inj hemp] at hfull; cases hfull
    · exact ⟨by omega, hfull⟩
  have hcop0 : ∀ r < bm.toNat + 1, copiedAt oldCtrl (bm.toNat + 1) 0 b0 r = false := by
    intro r hr; unfold copiedAt; have hm1 : ¬ (r < 0) := by omega
    by_cases hr8 : r < 8
    · rw [oldFullAt_eq_of_lt hr (by have := hmir.1; omega)]
      have hbit : b0.getLsbD r = isFullTag (oldCtrl[r]'(by have := hmir.1; omega)) := by
        rw [getLsbD_fullBits8 _ hr8, getLane8_ctrlGroupWord oldCtrl 0 hr8, Nat.zero_add,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by have := hmir.1; omega)]; rfl
      simp only [hm1, Nat.zero_le, Nat.zero_add, hr8, Nat.sub_zero, and_self,
        decide_false, decide_true, Bool.false_or, Bool.true_and, hbit]
      cases isFullTag (oldCtrl[r]'(by have := hmir.1; omega)) <;> rfl
    · simp [hm1, hr8]
  have hcnt0 : cntTrue (copiedAt oldCtrl (bm.toNat + 1) 0 b0) (bm.toNat + 1) = 0 := by
    rw [cntTrue_congr (q := fun _ => false) (bm.toNat + 1) hcop0]
    induction (bm.toNat + 1) with | zero => rfl | succ n ih => simp [cntTrue, ih]
  have hsum := copiedAt_uncopiedAt_sum oldCtrl (bm.toNat + 1) 0 b0 (by have := hmir.1; omega)
  exact ⟨⟨hbm, hmir, hb_cases.imp (fun h4 => ⟨h4, rfl⟩) (fun ⟨h8, _⟩ => ⟨h8, rfl, by omega⟩), hbits⟩, hcop0, by omega⟩

theorem OldScanInv.advance_zero {bm : BitVec 64} {oldCtrl : List (BitVec 8)}
    {grpBase : Nat} (h : OldScanInv bm oldCtrl grpBase 0#8)
    (hrem : 0 < cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase 0#8) (bm.toNat + 1)) :
    let b' := fullBits8 (ctrlGroupWord oldCtrl (grpBase + 8))
    8 ≤ bm.toNat + 1 ∧ grpBase + 16 ≤ bm.toNat + 1 ∧ OldScanInv bm oldCtrl (grpBase + 8) b' ∧
    (∀ r < bm.toNat + 1,
      copiedAt oldCtrl (bm.toNat + 1) (grpBase + 8) b' r = copiedAt oldCtrl (bm.toNat + 1) grpBase 0#8 r) ∧
    cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) (grpBase + 8) b') (bm.toNat + 1) =
      cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase 0#8) (bm.toNat + 1) := by
  intro b'
  have hlt_B : grpBase + 8 < bm.toNat + 1 := Classical.byContradiction fun hge => by
    have hall0 : ∀ r < bm.toNat + 1, uncopiedAt oldCtrl (bm.toNat + 1) grpBase 0#8 r = false :=
      fun r hr => by unfold uncopiedAt; simp [show ¬ (grpBase + 8 ≤ r) by omega]
    have hcnt0 : cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase 0#8) (bm.toNat + 1) = 0 := by
      rw [cntTrue_congr (q := fun _ => false) (bm.toNat + 1) hall0]
      induction (bm.toNat + 1) with | zero => rfl | succ n ih => simp [cntTrue, ih]
    omega
  rcases h.bound with ⟨h4, rfl⟩ | ⟨h8, hmod8, _⟩
  · omega
  · rcases h.validMask.buckets_cases with h4 | ⟨_, hmodB⟩
    · omega
    · have h16 : grpBase + 16 ≤ bm.toNat + 1 := by omega
      have hbits' : ∀ (j : Nat) (hj : j < 8), b'.getLsbD j = true →
          (grpBase + 8) + j < bm.toNat + 1 ∧
          isFullTag (oldCtrl[(grpBase + 8) + j]'(by have := h.mirror.1; omega)) = true := fun j hj hbit => by
        have h1 := (getLsbD_fullBits8 (ctrlGroupWord oldCtrl (grpBase + 8)) hj).symm.trans hbit
        rw [getLane8_ctrlGroupWord_eq_getElem (by have := h.mirror.1; omega) hj] at h1; exact ⟨by omega, h1⟩
      have hcop_eq : ∀ r < bm.toNat + 1,
          copiedAt oldCtrl (bm.toNat + 1) (grpBase + 8) b' r = copiedAt oldCtrl (bm.toNat + 1) grpBase 0#8 r := by
        intro r hr; unfold copiedAt
        by_cases hr1 : r < grpBase + 8
        · simp only [hr1, show ¬ (grpBase + 8 ≤ r ∧ r < grpBase + 8 + 8) by omega, decide_true, Bool.true_or, Bool.and_true]
          by_cases hr0 : r < grpBase <;> simp [hr0, show ¬ r < grpBase → grpBase ≤ r ∧ r < grpBase + 8 by omega]
        · simp only [hr1, show ¬ (r < grpBase) by omega, and_false, decide_false, Bool.false_or]
          by_cases hr2 : r < grpBase + 16
          · rw [oldFullAt_eq_of_lt hr (by have := h.mirror.1; omega)]
            have hj8 : r - (grpBase + 8) < 8 := by omega
            have hbit : b'.getLsbD (r - (grpBase + 8)) = isFullTag (oldCtrl[r]'(by have := h.mirror.1; omega)) := by
              rw [getLsbD_fullBits8 _ hj8, getLane8_ctrlGroupWord oldCtrl (grpBase + 8) hj8,
                  show grpBase + 8 + (r - (grpBase + 8)) = r by omega,
                  List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by have := h.mirror.1; omega)]; rfl
            simp only [show grpBase + 8 ≤ r by omega, hr2, and_self, decide_true, Bool.true_and, hbit]
            cases isFullTag (oldCtrl[r]'(by have := h.mirror.1; omega)) <;> rfl
          · simp [hr2]
      have hsum1 := copiedAt_uncopiedAt_sum oldCtrl (bm.toNat + 1) (grpBase + 8) b' (by have := h.mirror.1; omega)
      have hsum2 := copiedAt_uncopiedAt_sum oldCtrl (bm.toNat + 1) grpBase 0#8 (by have := h.mirror.1; omega)
      have := cntTrue_congr (bm.toNat + 1) hcop_eq
      exact ⟨h8, h16, ⟨h.validMask, h.mirror, Or.inr ⟨h8, by omega, h16⟩, hbits'⟩, hcop_eq, by omega⟩

theorem OldScanInv.clear_lowest {bm : BitVec 64} {oldCtrl : List (BitVec 8)}
    {grpBase : Nat} {b : BitVec 8} (h : OldScanInv bm oldCtrl grpBase b) (hb : b ≠ 0#8) :
    let oldIdx := grpBase + b.ctz.toNat; let b' := (b - 1#8) &&& b
    oldIdx < bm.toNat + 1 ∧
    isFullTag (oldCtrl[oldIdx]'(by
      rcases bv8_ctz_spec hb with ⟨hj8, hbt, _⟩; have := (h.bits_full _ hj8 hbt).1; have := h.mirror.1; omega)) = true ∧
    copiedAt oldCtrl (bm.toNat + 1) grpBase b oldIdx = false ∧
    1 ≤ cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase b) (bm.toNat + 1) ∧
    OldScanInv bm oldCtrl grpBase b' ∧
    (∀ r < bm.toNat + 1,
      copiedAt oldCtrl (bm.toNat + 1) grpBase b' r = (copiedAt oldCtrl (bm.toNat + 1) grpBase b r || (oldIdx == r))) ∧
    cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase b') (bm.toNat + 1) =
      cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase b) (bm.toNat + 1) - 1 := by
  dsimp only; rcases bv8_ctz_spec hb with ⟨hj8, hbt, _⟩; obtain ⟨hold_lt, hold_full⟩ := h.bits_full _ hj8 hbt
  have hm_lt : ¬ (grpBase + b.ctz.toNat < grpBase) := by omega
  have hm_mid : grpBase ≤ grpBase + b.ctz.toNat ∧ grpBase + b.ctz.toNat < grpBase + 8 := by omega
  have hm_ge : ¬ (grpBase + 8 ≤ grpBase + b.ctz.toNat) := by omega
  have hcop_false : copiedAt oldCtrl (bm.toNat + 1) grpBase b (grpBase + b.ctz.toNat) = false := by
    unfold copiedAt; simp [hm_lt, hm_mid, hbt]
  have huncop_true : uncopiedAt oldCtrl (bm.toNat + 1) grpBase b (grpBase + b.ctz.toNat) = true := by
    unfold uncopiedAt; rw [oldFullAt_eq_of_lt hold_lt (by have := h.mirror.1; omega)]
    simp [hm_ge, hm_mid, hbt, hold_full]
  have hbits' : ∀ (j : Nat) (hj : j < 8), ((b - 1#8) &&& b).getLsbD j = true →
      grpBase + j < bm.toNat + 1 ∧ isFullTag (oldCtrl[grpBase + j]'(by have := h.mirror.1; omega)) = true :=
    fun j hj hbit' => h.bits_full j hj ((Bool.and_eq_true _ _).mp (bv8_getLsbD_clear_lowest b hj ▸ hbit')).1
  have hcop_step : ∀ r < bm.toNat + 1,
      copiedAt oldCtrl (bm.toNat + 1) grpBase ((b - 1#8) &&& b) r =
        (copiedAt oldCtrl (bm.toNat + 1) grpBase b r || ((grpBase + b.ctz.toNat) == r)) := by
    intro r _; by_cases hro : grpBase + b.ctz.toNat = r
    · subst hro; rw [hcop_false]; unfold copiedAt
      rw [oldFullAt_eq_of_lt hold_lt (by have := h.mirror.1; omega)]
      simp [hm_lt, hm_mid, bv8_getLsbD_clear_lowest b hj8, hold_full]
    · simp only [beq_eq_false_iff_ne.mpr hro, Bool.or_false]; unfold copiedAt
      by_cases hmid : grpBase ≤ r ∧ r < grpBase + 8
      · simp [hmid, bv8_getLsbD_clear_lowest b (by omega : r - grpBase < 8), show r - grpBase ≠ b.ctz.toNat by omega]
      · simp [hmid]
  have hcnt_step :
      cntTrue (copiedAt oldCtrl (bm.toNat + 1) grpBase ((b - 1#8) &&& b)) (bm.toNat + 1) =
        cntTrue (copiedAt oldCtrl (bm.toNat + 1) grpBase b) (bm.toNat + 1) + 1 := by
    rw [cntTrue_congr (bm.toNat + 1) hcop_step, cntTrue_set _ _ _ hold_lt hcop_false]
  have hsum1 := copiedAt_uncopiedAt_sum oldCtrl (bm.toNat + 1) grpBase ((b - 1#8) &&& b) (by have := h.mirror.1; omega)
  have hsum2 := copiedAt_uncopiedAt_sum oldCtrl (bm.toNat + 1) grpBase b (by have := h.mirror.1; omega)
  exact ⟨hold_lt, hold_full, hcop_false, cntTrue_pos_of_true _ hold_lt huncop_true,
    ⟨h.validMask, h.mirror, h.bound, hbits'⟩, hcop_step, by omega⟩

theorem copiedAt_done {oldCtrl : List (BitVec 8)} {B grpBase : Nat} {b : BitVec 8}
    (hlen : B ≤ oldCtrl.length) (hzero : cntTrue (uncopiedAt oldCtrl B grpBase b) B = 0) :
    ∀ (r : Nat) (hr : r < B), isFullTag (oldCtrl[r]'(by omega)) = true → copiedAt oldCtrl B grpBase b r = true := by
  intro r hr hfull
  have hun : uncopiedAt oldCtrl B grpBase b r = false := by
    cases hu : uncopiedAt oldCtrl B grpBase b r with
    | false => rfl
    | true => have := cntTrue_pos_of_true B hr hu; omega
  have hp := copiedAt_uncopiedAt_pointwise oldCtrl B grpBase b r
  rw [oldFullAt_eq_of_lt hr hlen, hfull, hun] at hp; cases hc : copiedAt oldCtrl B grpBase b r <;> simp_all

/-! ## Machine-Code Proofs for `resize_inner` -/

theorem sepWP_pure_elim {prog : Program} {target : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWP prog target s P post oom) : SepWP prog target s (⌜φ⌝ ∗ P) post oom := by
  apply SepWP.of_reaches_pc; intro R hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact SepWP.to_reaches_pc (h hm.1) hm.2

theorem stdStatePreserved_congr_left {s1 s1' s2 : State}
    (h1 : s1'.fs = s1.fs) (h2 : s1'.trace = s1.trace) (h3 : s1'.tpidrEl0 = s1.tpidrEl0)
    (h4 : s1'.sigActions = s1.sigActions) (h5 : s1'.brk = s1.brk) (h6 : s1'.brkStart = s1.brkStart)
    (h7 : s1'.physMemAvail = s1.physMemAvail) (h8 : s1'.mem = s1.mem)
    (h : StdStatePreserved s1' s2) : StdStatePreserved s1 s2 :=
  ⟨h.1.trans h1, h.2.1.trans h2, h.2.2.1.trans h3, h.2.2.2.1.trans h4, h.2.2.2.2.1.trans h5,
   h.2.2.2.2.2.1.trans h6, h.2.2.2.2.2.2.1.trans h7, fun a => (h.2.2.2.2.2.2.2 a).trans (congrArg (fun m => m.perm a) h8)⟩

theorem sepWP_seq_frozen {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {Φ : Memory → Prop}
    (hst : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m') (hΦ : Φ s.mem)
    (h : SepWP prog mid s P (fun sm Pm => Φ sm.mem → SepWP prog target sm Pm post oom) oom) :
    SepWP prog target s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm hL
  rcases SepWP.to_reaches_pc h hm hL with ⟨sm, hst1, ⟨_, _, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hst2, hout⟩ := SepWP.to_reaches_pc (hcont (hst _ _ hΦ hst1.keepsFrozen)) hmm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr hoom⟩

theorem satisfies_pure_frame_of_sepConj {φ : Prop} {P R : SepProp} {m : Memory}
    (hφ : φ) (hm : m ⊨ P ∗ R) : m ⊨ ⌜φ⌝ ∗ R :=
  (satisfies_pure_sepConj φ R m).mpr ⟨hφ, ((satisfies_pure_sepConj True R m).mp (satisfies_true_sepConj hm)).2⟩

theorem sepWPp_call_coldPanic {prog : Program} {ret entry ret_pc spBase : BitVec 64}
    {s : State} {F R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    {φ : Prop} {stkTotal : Nat} (hcall : subroutine_ok prog entry (hbColdPanicSpec φ))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hsp : s.sp = spBase) (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg32 .x0 = 1#32)
    (hφ : φ) (hge16 : 16 ≤ stkTotal) (hnw_stk : spBase.toNat < 2 ^ 64 ∧ stkTotal ≤ 2 ^ 64) :
    SepWPp prog ret s (stackAt spBase stkTotal ∗ F) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜φ⌝ ∗ R)) oom := by
  have hsh := stackAt_shrink spBase stkTotal 16 hge16 hnw_stk.2
  refine SepWPp.call (x := ()) hcall hpc hrun hsp_al hlr
    (F := memRegion (spBase - BitVec.ofNat 64 stkTotal) (stkTotal - 16) ∗ F)
    (fun R' hm => by
      dsimp only [hbColdPanicSpec]; rw [sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨⟨hx0, hφ⟩, ?_⟩
      rw [hsh] at hm; rw [hsp]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ hmf => satisfies_pure_frame_of_sepConj hφ hmf)
    (fun _ _ _ _ _ => SepWPp.pure_left False.elim) (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)

theorem hbResize_cap_after_csinc {bm : BitVec 64} {mLen : Nat}
    (hbm : bm = 0#64 ∨ ValidBucketMask bm) (hm_le : mLen ≤ bucketMaskToCapacity bm) :
    bucketMaskToCapacity bm ≤ MaxHashbrownCapacity ∧
    (if (bucketMaskToCapacityBV bm + 1#64).ule (BitVec.ofNat 64 (mLen + 1)) = true
     then BitVec.ofNat 64 (mLen + 1) else bucketMaskToCapacityBV bm + 1#64) =
      BitVec.ofNat 64 (bucketMaskToCapacity bm + 1) := by
  have hcap_le : bucketMaskToCapacity bm ≤ MaxHashbrownCapacity := by
    rcases hbm with rfl | ⟨e, hlo, hhi, heq⟩
    · decide
    · rw [ValidBucketMask.capacity_eq hlo hhi heq]; by_cases he2 : e = 2
      · subst he2; decide
      · simp only [he2, ↓reduceIte]; exact Nat.mul_le_mul_left 7 (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨hcap_le, ?_⟩
  have hmax : MaxHashbrownCapacity = 7 * 2 ^ 55 := rfl
  have hadd1_eq : bucketMaskToCapacityBV bm + 1#64 = BitVec.ofNat 64 (bucketMaskToCapacity bm + 1) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]
    change (bucketMaskToCapacity bm + 1) % 2 ^ 64 = _; simp only [BitVec.toNat_ofNat]
  simp only [hadd1_eq, BitVec.ule_iff_le, BitVec.le_def, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : bucketMaskToCapacity bm + 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : mLen + 1 < 2 ^ 64)]
  split
  · congr 1; omega
  · rfl

end CaseStudies.Hashbrown.Proofs.ResizeInternal

namespace CaseStudies.Hashbrown.Proofs
export ResizeInternal (HbRehashInPlaceProp)
end CaseStudies.Hashbrown.Proofs
