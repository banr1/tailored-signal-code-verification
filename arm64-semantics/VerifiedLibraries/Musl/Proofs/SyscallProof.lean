/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Spec.Top
public import VerifiedLibraries.Musl.Proofs.SyscallSym
public import ProofLib.MallocngIface
public import ProofLib

/-!
# Placement-Generic `musl` Syscall Wrapper Contracts

Placement-generic `subroutine_ok` contracts over `muslSysPlacedLib` for `___errno_location`,
`__errno_location`, `__syscall_ret`, `close`, `read`, `write`, and `open`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.Musl

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup

/-- Valid NUL-free Latin-1/ASCII C-string path bounded by `PATH_MAX`. -/
def ValidCPath (path : String) : Prop :=
  path.toList.length < PATH_MAX ∧
  ∀ c ∈ path.toList, c.toNat < 256 ∧ c.toNat ≠ 0

/-- Valid relative C-string path without leading `/` or `..` segments. -/
def ValidRelCPath (path : String) : Prop :=
  ValidCPath path ∧
  hasLeadingSlash path = false ∧
  hasDotDot path = false

theorem ValidCPath.bytesOfString_spec {path : String} (h : ValidCPath path) :
    (bytesOfString path).length < PATH_MAX ∧ ∀ b ∈ bytesOfString path, b ≠ 0#8 := by
  obtain ⟨hlen, hcs⟩ := h
  refine ⟨by simpa [bytesOfString] using hlen, fun b hb => ?_⟩
  simp only [bytesOfString, List.mem_map] at hb
  rcases hb with ⟨c, hc, rfl⟩
  obtain ⟨hlt, hne⟩ := hcs c hc
  intro h0
  have := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt (by omega : c.toNat < 2 ^ 8)] at this
  exact hne this

theorem placed_program_rebase_self (lib : Obj.PlacedLib) (pl : Obj.Placement) :
    (lib.program pl).rebase pl.base (fun _ => none) = lib.program pl := rfl

theorem FsState.setFd_self {fs : FsState} {fd : BitVec 64} {d : Option FdEntry}
    (h : fs.fds fd = d) :
    fs.setFd fd d = fs := by
  cases fs with
  | mk entries stdin fds =>
    dsimp only at h
    simp only [FsState.setFd, FsState.mk.injEq, true_and]
    funext k
    by_cases hk : (k == fd) = true
    · rw [eq_of_beq hk]; simp [h]
    · simp [hk]

/-! ## `___errno_location` and `__syscall_ret` -/

/-- Contract for `int *__errno_location(void)` (`blk00`): returns `muslErrnoAddr s0` in `x0`. -/
def muslErrnoLocationSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = muslErrnoAddr s0 ∧ sf.mem = s0.mem ∧ StdStatePreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslErrnoLocation_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 0)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "___errno_location")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslErrnoLocationSpec) := by
  rw [show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 0 =
    muslSysPC00.rebase muslSysPl00.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib00 muslSysPl00).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "___errno_location" = muslSysPl00.base := by
    have hl : Obj.lookupBlockSym "___errno_location" muslSysPlacedLib.blocks = some (0, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl00, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry; wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp [wp_norm, arm64_norm, muslErrnoAddr], rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩

theorem muslErrnoLocation2_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 0)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "__errno_location")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslErrnoLocationSpec) :=
  muslErrnoLocation_block_ok

theorem muslErrnoLocation_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "___errno_location")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslErrnoLocationSpec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 0) (by decide) muslErrnoLocation_block_ok hext hsvc

private def muslAioCloseSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = s0.readReg64 .x0 ∧ sf.mem = s0.mem ∧ StdStatePreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslAioClose_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC04.rebase muslSysPl04.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__aio_close")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslAioCloseSpec) := by
  have hentry : muslSysPlacedLib.resolve MuslSysPlacement.mpl "__aio_close" = muslSysPl04.base := by
    have hl : Obj.lookupBlockSym "__aio_close" muslSysPlacedLib.blocks = some (4, 0) := by decide
    simp [Obj.MultiPlacedLib.resolve, hl, muslSysPl04, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry; wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
    by simpa using hmem⟩

private theorem condHI_adds_4096_false {a : BitVec 64} (ha : a.toNat ≤ 2 ^ 64 - 4096) :
    ConditionHolds .HI (addsPState64 a 4096#64) = false := by
  rw [conditionHolds_hi_addsPState64]
  have hpow : 4096 < 2 ^ 64 := by decide
  by_cases heq : a = -4096#64
  · subst heq; decide
  · have hlt_strict : a.toNat < 2 ^ 64 - 4096 := by
      refine Nat.lt_of_le_of_ne ha fun h => heq (BitVec.eq_of_toNat_eq ?_)
      have : (-4096#64 : BitVec 64).toNat = 2 ^ 64 - 4096 := by decide
      omega
    have hadd : (a + 4096#64).toNat = a.toNat + 4096 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : 4096 % 2 ^ 64 = 4096 := by decide
      rw [this, Nat.mod_eq_of_lt (by omega)]
    have hult : BitVec.ult (a + 4096#64) a = false := by
      simp only [BitVec.ult, hadd, decide_eq_false_iff_not]; omega
    rw [hult, Bool.false_and]

private theorem condHI_adds_4096_true {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ConditionHolds .HI (addsPState64 (-BitVec.ofNat 64 err) 4096#64) = true := by
  rw [conditionHolds_hi_addsPState64]
  have herr_mod : err % 2 ^ 64 = err := Nat.mod_eq_of_lt (by omega)
  have h4096_mod : 4096 % 2 ^ 64 = 4096 := by decide
  have hneg : (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
    rw [BitVec.toNat_neg, BitVec.toNat_ofNat, herr_mod, Nat.mod_eq_of_lt (by omega)]
  have hsum : (-BitVec.ofNat 64 err + 4096#64).toNat = 4096 - err := by
    rw [BitVec.toNat_add, hneg, BitVec.toNat_ofNat, h4096_mod]
    have : 2 ^ 64 - err + 4096 = 2 ^ 64 + (4096 - err) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hult : BitVec.ult (-BitVec.ofNat 64 err + 4096#64) (-BitVec.ofNat 64 err) = true := by
    simp only [BitVec.ult, hneg, hsum, decide_eq_true_eq]; omega
  have hne : (-BitVec.ofNat 64 err + 4096#64 != 0#64) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro heq
    have := congrArg BitVec.toNat heq
    simp only [hsum, BitVec.toNat_ofNat] at this
    omega
  rw [hult, hne]; rfl

theorem step_str64_perm_c {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .X64 rt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write64 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 8 = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .X64 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write64 s.mem ea val)) hm'

theorem step_stp64_perm {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W64 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  have hperm : m2.perm = s.mem.perm :=
    (Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1)
  exact SepWP.to_reaches_pc (hnext m2 hperm) hm2

theorem step_str32_perm {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .W32 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg32 rt = val)
    (hstore : SepStore32 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .W32 rt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write32 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 4 = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .W32 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    have hval' : (s.readReg64 rt).truncate 32 = val := hval
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hval', hcan, MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write32 s.mem ea val)) hm'

theorem step_stp32_64_perm {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {new64 : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W32 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (((s.readReg32 rt2).zeroExtend 64) <<< 32) ||| ((s.readReg32 rt1).zeroExtend 64) = new64)
    (hstore : SepStore64 ea new64 P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W32 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let v1 := (s.readReg64 rt1).truncate 32
  let v2 := (s.readReg64 rt2).truncate 32
  let m' := (s.mem.write32 ea v1).write32 (ea + 4#64) v2
  have hm64 : s.mem.write64 ea new64 ⊨ P' ∗ R := hstore.store hm
  have hm' : m' ⊨ P' ∗ R := by
    refine Satisfies.congr_mem (fun a => ?_) ?_ ?_ (by simp [m']) hm64
    · exact Memory.read8_write32_pair_eq_read8_write64 s.mem ea a v1 v2 new64 hval
    · rw [Memory.perm_write32, Memory.perm_write32, Memory.perm_write64]
    · funext a
      have ha0 : ea + 4#64 + 0#64 = ea + 4#64 := by bv_bits
      have ha1 : ea + 4#64 + 1#64 = ea + 5#64 := by bv_bits
      have ha2 : ea + 4#64 + 2#64 = ea + 6#64 := by bv_bits
      have ha3 : ea + 4#64 + 3#64 = ea + 7#64 := by bv_bits
      simp only [m', Memory.write32, Memory.write64, Memory.isLazyFree_write8, ha0, ha1, ha2, ha3]
  have hcan1 : s.mem.canWrite ea 4 = true := Memory.canWrite_4_of_8 (hstore.writable hm)
  have hcan2 : s.mem.canWrite (ea + 4#64) 4 = true := Memory.canWrite_hi4_of_8 (hstore.writable hm)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W32 rt1 rt2 addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hcan1, hcan2, MemWidth.bytes, hpc, m', v1, v2]
  rw [hstep]
  have hperm : m'.perm = s.mem.perm :=
    (Memory.perm_write32 _ _ _).trans (Memory.perm_write32 _ _ _)
  exact SepWP.to_reaches_pc (hnext m' hperm) hm'

macro "wp_stp64_perm " hm:ident : tactic =>
  `(tactic| (
    apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
    (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
    (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
    intro _ $hm; try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
      State.mem_advancePC, State.mem_setPC, State.mem_setMem] at $hm:ident))

macro "wp_str64_perm " hm:ident : tactic =>
  `(tactic| (
    apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
    (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
    intro _ $hm; try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
      State.mem_advancePC, State.mem_setPC, State.mem_setMem] at $hm:ident))

macro "wp_str32_perm " hm:ident : tactic =>
  `(tactic| (
    apply step_str32_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
    (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
    intro _ $hm; try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
      State.mem_advancePC, State.mem_setPC, State.mem_setMem] at $hm:ident))

macro "wp_stp32_64_perm " hm:ident : tactic =>
  `(tactic| (
    apply step_stp32_64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
    (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
    intro _ $hm; try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
      State.mem_advancePC, State.mem_setPC, State.mem_setMem] at $hm:ident))

/-- Non-error contract for `long __syscall_ret(unsigned long r)` (`blk01`, `r <= 2^64 - 4096`). -/
def muslSyscallRetOkSpec : Spec (BitVec 64) where
  pre := fun retVal s0 =>
    ⌜s0.readReg64 .x0 = retVal ∧ retVal.toNat ≤ 2 ^ 64 - 4096⌝ ∗ stackAt s0.sp 32
  post := fun retVal s0 sf =>
    ⌜sf.readReg64 .x0 = retVal ∧ StdStatePreserved s0 sf⌝ ∗ stackAt s0.sp 32
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslSyscallRetOk_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 1)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "__syscall_ret")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSyscallRetOkSpec) := by
  rw [show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 1 =
    muslSysPC01.rebase muslSysPl01.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib01 muslSysPl01).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "__syscall_ret" = muslSysPl01.base := by
    have hl : Obj.lookupBlockSym "__syscall_ret" muslSysPlacedLib.blocks = some (1, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl01, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre => rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
  cells_unfold; simp only [sepConj_assoc]; repeat (apply SepWP.exists_left; intro)
  wp_stp64_perm hm1; wp_sym_steps 2; wp_str64_perm hm2; wp_sym_steps
  have hcond : ConditionHolds .HI (addsPState64 _ 4096#64) = false := condHI_adds_4096_false ‹_›
  simp only [hcond, Bool.false_eq_true, ↓reduceIte]; wp_sym_steps; wp_clear_temps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp_all [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp [wp_norm, arm64_norm, hm2, hm1]⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
    cells_unfold; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [wp_norm, arm64_norm]

/-- Error contract for `long __syscall_ret(unsigned long r)` (`blk01`, `r = -err` for `1 <= err <= 4095`). -/
def muslSyscallRetErrSpec : Spec (Nat × BitVec 32) where
  pre := fun (err, e0) s0 =>
    ⌜s0.readReg64 .x0 = -BitVec.ofNat 64 err ∧ 1 ≤ err ∧ err ≤ 4095⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (err, _) s0 sf =>
    ⌜sf.readReg64 .x0 = -1#64 ∧ StdStatePreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ BitVec.ofNat 32 err))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem neg_truncate32_neg_ofNat (err : Nat) :
    0#32 - (-BitVec.ofNat 64 err).truncate 32 = BitVec.ofNat 32 err := by bv_omega

theorem muslSyscallRetErr_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 1)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "__syscall_ret")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSyscallRetErrSpec) := by
  rw [show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 1 =
    muslSysPC01.rebase muslSysPl01.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib01 muslSysPl01).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "__syscall_ret" = muslSysPl01.base := by
    have hl : Obj.lookupBlockSym "__syscall_ret" muslSysPlacedLib.blocks = some (1, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl01, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre => rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps 2; wp_str64_perm hm2; wp_sym_steps
  have hcond : ConditionHolds .HI (addsPState64 _ 4096#64) = true := condHI_adds_4096_true ‹_› ‹_›
  simp only [hcond, ↓reduceIte]; wp_sym_steps
  wp_call_block muslErrnoLocation_block_ok ()
  rcases ‹StdStatePreserved _ sf› with ⟨hbrk_sf, hfs_sf, htpidr_sf, htr_sf, hoidx_sf, horacle_sf, hphys_sf, _⟩
  simp only [wp_norm, arm64_norm] at hbrk_sf hfs_sf htpidr_sf htr_sf hoidx_sf horacle_sf hphys_sf
  simp only [muslErrnoAddr] at *; wp_sym_steps 3; wp_str32_perm hm3; wp_sym_steps; wp_clear_temps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, ‹sf.status = .Running›])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, hbrk_sf.symm],
      by simp [wp_norm, arm64_norm, hfs_sf.symm], by simp [wp_norm, arm64_norm, htpidr_sf.symm],
      by simp [wp_norm, arm64_norm, htr_sf.symm], by simp [wp_norm, arm64_norm, hoidx_sf.symm],
      by simp [wp_norm, arm64_norm, horacle_sf.symm], by simp [wp_norm, arm64_norm, hphys_sf.symm],
      fun _ => by simp [wp_norm, arm64_norm, hm3, ‹sf.mem = _›, hm2, hm1]⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm, htpidr_sf.symm, neg_truncate32_neg_ofNat]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

/-! ## `__syscall_cp` and `sccp` -/

private theorem muslSyscallCp_step [MuslSysPlacement] {s0 : State} {target_pc : BitVec 64}
    {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s0.pc = muslSysPl03.base) (hrun : s0.status = .Running)
    (hcl : muslSysPlacedLib.CodeLoaded MuslSysPlacement.mpl s0.mem)
    (hnext : SepWP (muslSysPC02.rebase muslSysPl02.base (fun _ => none)) target_pc
      ((((((((s0.writeReg64 .x8 (s0.readReg64 .x0)).writeReg64 .x0 (s0.readReg64 .x1)).writeReg64
        .x1 (s0.readReg64 .x2)).writeReg64 .x2 (s0.readReg64 .x3)).writeReg64
        .x3 (s0.readReg64 .x4)).writeReg64 .x4 (s0.readReg64 .x5)).writeReg64
        .x5 (s0.readReg64 .x6)).setPC (muslSysPl02.base + 28#64)) P post) :
    SepWP (muslSysPC03.rebase muslSysPl03.base (fun _ => none)) target_pc s0 P post := by
  wp_sym_steps
  have hsccp : muslSysPl03.base + (muslSysPl03.ρ "sccp" - muslSysPl03.base) = muslSysPl02.base := by
    have hadd : muslSysPl03.base + (muslSysPl03.ρ "sccp" - muslSysPl03.base) = muslSysPl03.ρ "sccp" := by bv_omega
    have hl : Obj.lookupBlockSym "sccp" muslSysPlacedLib.blocks = some (2, 0) := by decide
    rw [hadd]
    simp [muslSysPl03, muslSysPl02, Obj.MultiPlacedLib.blockPlacement, Obj.MultiPlacedLib.resolve, hl]
  rw [hsccp]
  refine SepWP.of_sameHooks (P := muslSysPC03.rebase muslSysPl03.base (fun _ => none))
    (Q := muslSysPC02.rebase muslSysPl02.base (fun _ => none))
    (by intro pc
        change ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 2).rebase muslSysPl02.base (fun _ => none)).externAt? pc =
          ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 3).rebase muslSysPl03.base (fun _ => none)).externAt? pc
        simp)
    rfl ((hcl 2 (by decide)).of_base_code rfl rfl) ?_
  wp_sym_steps
  simpa [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8] using hnext

private theorem resolve_syscall_cp [MuslSysPlacement] :
    muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp" = muslSysPl03.base := by
  have hl : Obj.lookupBlockSym "__syscall_cp" muslSysPlacedLib.blocks = some (3, 0) := by decide
  simp [Obj.MultiPlacedLib.resolve, hl, muslSysPl03, Obj.MultiPlacedLib.blockPlacement]

theorem ofNat64_toNat_of_lt63 {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]

private theorem ofNat64_ne_zero {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro h0
  have := congrArg BitVec.toNat h0
  rw [ofNat64_toNat_of_lt63 hlt] at this
  simp at this; omega

@[wp_norm, simp] theorem muslSysPC02_svc [MuslSysPlacement] : muslSysPC02.svc = Syscall.standard := rfl
@[wp_norm, simp] theorem muslSysPC08_svc [MuslSysPlacement] : muslSysPC08.svc = Syscall.standard := rfl
@[wp_norm, simp] theorem muslSysPC10_svc [MuslSysPlacement] : muslSysPC10.svc = Syscall.standard := rfl

private def muslSccpCloseSpec : Spec (BitVec 64 × FdEntry) where
  pre := fun (fd, desc) s0 =>
    ⌜s0.readReg64 .x0 = 57#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.fs.fds fd = some desc ∧
      desc.kind = .localFile⌝
  post := fun (fd, _) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.fs = s0.fs.setFd fd none ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslSccpClose_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC03.rebase muslSysPl03.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSccpCloseSpec) := by
  rw [resolve_syscall_cp]; wp_entry
  refine muslSyscallCp_step hpc hrun h ?_
  refine SepWP.step_svc_close_fd (fd := a_1) (desc := a_rest) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4 h_5 h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  dsimp only; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private def muslSccpReadClampedSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, oldBuf) s0 =>
    ⌜s0.readReg64 .x0 = 63#64 ∧ (s0.readReg32 .x1).zeroExtend 64 = fd ∧ fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x2 = buf ∧ s0.readReg64 .x3 = count ∧
      buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE ∧ oldBuf.length = count.toNat ∧
      s0.fs.fds fd = some desc ∧ desc.kind = .localFile ∧ desc.accMode.canRead = true⌝ ∗
    (buf ↦ₛ oldBuf)
  post := fun (fd, buf, count, desc, oldBuf) s0 sf =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take (min count.toNat Arm64.MAX_RW_COUNT)
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧
      sf.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
      sf.trace = s0.trace ∧ SyscallPreserved s0 sf⌝ ∗
    (buf ↦ₛ (chunk ++ oldBuf.drop chunk.length))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslSccpReadClamped_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC03.rebase muslSysPl03.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSccpReadClampedSpec) := by
  rw [resolve_syscall_cp]; wp_entry
  refine muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine SepWP.step_svc_read_clamped (fd := a_1) (buf := a) (count := a_2) (desc := a_3) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4
    (by simp [wp_norm, arm64_norm, h_5]) (by simp [wp_norm, arm64_norm, h_6]) h_9
    h_10 (by rw [h_11]; rfl) h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, execRead, h_2])
    h_7 (fun _ => h_8)
  dsimp only; rw [sepConj_emp]
  (conv => arg 3; simp only [wp_norm, arm64_norm])
  (conv => arg 4; simp only [wp_norm, arm64_norm, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8])
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm],
      by cases a_3; simp_all [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp [wp_norm, arm64_norm]⟩, by simpa [Arm64.MAX_RW_COUNT] using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private def muslSccpReadSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, oldBuf) s0 =>
    ⌜s0.readReg64 .x0 = 63#64 ∧ (s0.readReg32 .x1).zeroExtend 64 = fd ∧ fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x2 = buf ∧ s0.readReg64 .x3 = count ∧
      count.toNat ≤ Arm64.MAX_RW_COUNT ∧ buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE ∧ oldBuf.length = count.toNat ∧
      s0.fs.fds fd = some desc ∧ desc.kind = .localFile ∧ desc.accMode.canRead = true⌝ ∗
    (buf ↦ₛ oldBuf)
  post := fun (fd, buf, count, desc, oldBuf) s0 sf =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take count.toNat
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧
      sf.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
      sf.trace = s0.trace ∧ SyscallPreserved s0 sf⌝ ∗
    (buf ↦ₛ (chunk ++ oldBuf.drop chunk.length))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslSccpRead_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC03.rebase muslSysPl03.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSccpReadSpec) := by
  rw [resolve_syscall_cp]; wp_entry
  refine muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine SepWP.step_svc_read (fd := a_1) (buf := a) (count := a_2) (desc := a_3) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4
    (by simp [wp_norm, arm64_norm, h_5]) (by simp [wp_norm, arm64_norm, h_6]) h_10
    h_11 (by rw [h_12]; rfl) h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, execRead, h_2])
    h_7 h_8 (fun _ => h_9)
  dsimp only; rw [sepConj_emp]
  (conv => arg 3; simp only [wp_norm, arm64_norm])
  (conv => arg 4; simp only [wp_norm, arm64_norm, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8])
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm],
      by cases a_3; simp_all [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp [wp_norm, arm64_norm]⟩, by simpa [Arm64.MAX_RW_COUNT] using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private def muslSccpWriteStderrSpec : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (buf, bs) s0 =>
    ⌜s0.readReg64 .x0 = 64#64 ∧ s0.readReg32 .x1 = 2#32 ∧ s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = BitVec.ofNat 64 bs.length ∧
      bs.length ≤ Arm64.MAX_RW_COUNT ∧ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT⌝ ∗
    (buf ↦ᵣ bs)
  post := fun (buf, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 bs.length ∧ sf.fs = s0.fs ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stderr bs ∧ SyscallPreserved s0 sf⌝ ∗
    (buf ↦ᵣ bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslSccpWriteStderr_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC03.rebase muslSysPl03.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSccpWriteStderrSpec) := by
  rw [resolve_syscall_cp]; wp_entry
  have hlt63 : a_rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt h_6 (by decide)
  have hlen_nat : (BitVec.ofNat 64 a_rest.length).toNat = a_rest.length :=
    ofNat64_toNat_of_lt63 hlt63
  refine muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ᵣ _)]
  refine step_svc_write_stdio_ro false (buf := a_1) (count := BitVec.ofNat 64 a_rest.length) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2])
    (by simpa [wp_norm, arm64_norm] using congrArg (BitVec.zeroExtend 64) h_3)
    (by simp [wp_norm, arm64_norm, h_4]) (by simp [wp_norm, arm64_norm, h_5]) hlen_nat.symm ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
    (by rw [hlen_nat]; exact h_6) (by rw [hlen_nat]; exact h_1)
  rw [sepConj_emp]; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm, State.appendTrace], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
      by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [wp_norm, arm64_norm, State.appendTrace, calleeSavedVRegs]

private def muslSccpWriteFileClampedSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, bs) s0 =>
    ⌜s0.readReg64 .x0 = 64#64 ∧ (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      3 ≤ fd.toNat ∧ fd.toNat < 2 ^ 31 ∧ s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = count ∧ count ≠ 0#64 ∧
      bs.length = min count.toNat Arm64.MAX_RW_COUNT ∧
      buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE ∧
      s0.fs.fds fd = some desc ∧ desc.kind = .localFile ∧
      desc.accMode.canWrite = true ∧ desc.append = false ∧
      desc.offset + bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE⌝ ∗
    (buf ↦ₛ bs)
  post := fun (fd, buf, _, desc, bs) s0 sf =>
    let oldBytes := match s0.fs.files desc.path with | some (.file b) => b | _ => []
    let newBytes := writeFileBytes oldBytes desc.offset bs
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 bs.length ∧
      sf.fs = (s0.fs.setFile desc.path (some (.file newBytes))).setFd fd
        (some { desc with offset := desc.offset + bs.length }) ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes (OutputStream.ofFd fd) bs ∧
      SyscallPreserved s0 sf⌝ ∗
    (buf ↦ₛ bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslSccpWriteFileClamped_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC03.rebase muslSysPl03.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSccpWriteFileClampedSpec) := by
  rw [resolve_syscall_cp]; wp_entry
  refine muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine step_svc_write_file_clamped (fd := a_1) (buf := a)
    (count := a_2) (desc := a_3) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4 h_5
    (by simp [wp_norm, arm64_norm, h_6]) (by simp [wp_norm, arm64_norm, h_7])
    h_8 h_9 h_12 h_13 h_14 h_15 h_11 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
    h_10 (by simpa [Arm64.MAX_RW_COUNT, ← h_9] using h_1)
  dsimp only; rw [sepConj_emp]; (conv => arg 3; simp only [wp_norm, arm64_norm, Arm64.MAX_RW_COUNT, ← h_9]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm, ← h_9],
      by cases a_3; cases hfl : s0.fs.files _ <;> (try cases ‹FsEntry›) <;>
           simp_all [wp_norm, arm64_norm, State.appendTrace],
      by simp [wp_norm, arm64_norm, State.appendTrace], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
      by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [wp_norm, arm64_norm, State.appendTrace, calleeSavedVRegs]

private def muslSccpWriteFileSpec : Spec (BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, desc, bs) s0 =>
    ⌜s0.readReg64 .x0 = 64#64 ∧ (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      3 ≤ fd.toNat ∧ fd.toNat < 2 ^ 31 ∧ s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = BitVec.ofNat 64 bs.length ∧ 0 < bs.length ∧
      bs.length ≤ Arm64.MAX_RW_COUNT ∧ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT ∧
      s0.fs.fds fd = some desc ∧ desc.kind = .localFile ∧
      desc.accMode.canWrite = true ∧ desc.append = false ∧
      desc.offset + bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE⌝ ∗
    (buf ↦ₛ bs)
  post := fun (fd, buf, desc, bs) s0 sf =>
    let oldBytes := match s0.fs.files desc.path with | some (.file b) => b | _ => []
    let newBytes := writeFileBytes oldBytes desc.offset bs
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 bs.length ∧
      sf.fs = (s0.fs.setFile desc.path (some (.file newBytes))).setFd fd
        (some { desc with offset := desc.offset + bs.length }) ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes (OutputStream.ofFd fd) bs ∧
      SyscallPreserved s0 sf⌝ ∗
    (buf ↦ₛ bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslSccpWriteFile_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC03.rebase muslSysPl03.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSccpWriteFileSpec) := by
  rw [resolve_syscall_cp]; wp_entry
  have hlt63 : a_rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt h_9 (by decide)
  have hlen_nat : (BitVec.ofNat 64 a_rest.length).toNat = a_rest.length :=
    ofNat64_toNat_of_lt63 hlt63
  have hcnt_nz : BitVec.ofNat 64 a_rest.length ≠ 0#64 :=
    ofNat64_ne_zero h_8 hlt63
  have hlfs : a_2.offset + (BitVec.ofNat 64 a_rest.length).toNat ≤ Arm64.MAX_LFS_FILESIZE := by
    rw [hlen_nat]; exact Nat.le_trans h_1 (by decide)
  refine muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine step_svc_write_file (fd := a_1) (buf := a)
    (count := BitVec.ofNat 64 a_rest.length) (desc := a_2) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4 h_5
    (by simp [wp_norm, arm64_norm, h_6]) (by simp [wp_norm, arm64_norm, h_7])
    hcnt_nz hlen_nat.symm h_11 h_12 h_13 h_14 hlfs ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
    (by rw [hlen_nat]; exact h_9) (by rw [hlen_nat]; exact h_10) (by rw [hlen_nat]; exact h_1)
  dsimp only; rw [sepConj_emp, hlen_nat]; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm],
      by cases a_2; cases hfl : s0.fs.files _ <;> (try cases ‹FsEntry›) <;>
           simp_all [wp_norm, arm64_norm, State.appendTrace],
      by simp [wp_norm, arm64_norm, State.appendTrace], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
      by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [wp_norm, arm64_norm, State.appendTrace, calleeSavedVRegs]

/-! ## `close`, `read`, and `write` -/

@[simp, arm64_norm] theorem sxtw64_truncate32 (v : BitVec 64) :
    (v >>> 0 &&& 4294967295#64 |||
      (if v.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64).truncate 32 = v.truncate 32 := by
  have hlo : (4294967295#64 : BitVec 64) = (BitVec.allOnes 32).zeroExtend 64 := by decide
  have hhi : (0xffffffff00000000#64 : BitVec 64) = 0xffffffff#64 <<< 32 := by decide
  have hall : ∀ (i : Nat) (hi : i < 32), (4294967295#32)[i]'hi = true := by decide
  ext i hi; rw [hlo, hhi]
  by_cases hb : v.getLsbD 31 = true <;> simp [hb, hall]

theorem ofNat64_le_maxSyscallOk {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).toNat ≤ 2 ^ 64 - 4096 := by
  rw [ofNat64_toNat_of_lt63 h]; omega

def CodeLoadedAt (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (m : Memory) : Prop :=
  lib.CodeLoaded mpl m

theorem seq_codeLoaded_lr {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    (hcl : lib.CodeLoaded mpl s.mem)
    (h : SepWP prog (s.readReg64 .lr) s P (fun sm Pm =>
      CodeLoadedAt lib mpl sm.mem → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  Obj.MultiPlacedLib.seq_codeLoaded hcl h

syntax "wp_call_block_keep" ppSpace colGt term:max (ppSpace colGt wppCallOpt)* : tactic
macro_rules
  | `(tactic| wp_call_block_keep $hcall:term $[$opts:wppCallOpt]*) =>
    `(tactic| (
      try (
        apply SepWP.done
        · first | wp_norm_lhs | wp_norm_goal | rfl
        · wp_norm_lhs
        intro)
      apply seq_codeLoaded_lr ‹_›
      wp_call_block $hcall $[$opts]*
      apply SepWP.done
      · simp [wp_norm, arm64_norm, *]
      · assumption
      intro; dsimp only [CodeLoadedAt] at *))

/-- Contract for `int close(int fd)` (`blk05`, `48`-byte stack frame) on an open `.localFile`
    descriptor `fd >= 3`. -/
def muslClose48Spec : Spec (BitVec 64 × FdEntry) where
  pre := fun (fd, desc) s0 =>
    ⌜(s0.readReg32 .x0).zeroExtend 64 = fd ∧ 3 ≤ fd.toNat ∧ fd.toNat < 2 ^ 31 ∧
      s0.fs.fds fd = some desc ∧ desc.kind = .localFile⌝ ∗
    stackAt s0.sp 48
  post := fun (fd, _) s0 sf =>
    ⌜sf.readReg32 .x0 = 0#32 ∧ sf.fs = s0.fs.setFd fd none ∧ sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝ ∗
    stackAt s0.sp 48
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslClose48_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 5)
      (muslSysPlacedLib.fnAddr muslSysMpl "close")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslClose48Spec) := by
  rw [show muslSysPlacedLib.blockProgram muslSysMpl 5 =
    muslSysPC05.rebase muslSysPl05.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib05 muslSysPl05).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "close" = muslSysPl05.base := by
    have hl : Obj.lookupBlockSym "close" muslSysPlacedLib.blocks = some (5, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl05, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 32 2 (by decide)]
  cells_unfold; simp only [sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep muslAioClose_blk_ok ()
  rcases ‹StdStatePreserved _ _› with ⟨hfs1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at hfs1 htr1 htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block_keep muslSccpClose_blk_ok (a_1, a_rest)
  rcases ‹SyscallPreserved _ _› with ⟨htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at htp2 hsig2 hb2 hbs2 hp2 hmp2
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block muslSyscallRetOk_block_ok 0#64
  rcases ‹StdStatePreserved _ _› with ⟨hfs3, htr3, htp3, hsig3, hb3, hbs3, hp3, hmp3⟩
  simp only [wp_norm, arm64_norm, htp2, hsig2, hb2, hbs2, hp2, hmp2] at hfs3 htr3 htp3 hsig3 hb3 hbs3 hp3 hmp3
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
      by simp [wp_norm, arm64_norm, *], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
        stackAt_split_cells s0.sp 32 2 (by decide)]
      cells_unfold; simp only [wp_norm, arm64_norm, *]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

theorem muslClose48_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "close")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslClose48Spec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 5) (by decide) muslClose48_block_ok hext hsvc

/-- Contract for `ssize_t read(int fd, void *buf, size_t count)` (`blk06`, `32`-byte stack frame)
    on an open readable `.localFile` descriptor (`count <= MAX_RW_COUNT`). -/
def muslRead32Spec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, oldBuf) s0 =>
    ⌜(s0.readReg32 .x0).zeroExtend 64 = fd ∧ 3 ≤ fd.toNat ∧ fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x1 = buf ∧ s0.readReg64 .x2 = count ∧
      count.toNat ≤ Arm64.MAX_RW_COUNT ∧ buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE ∧
      oldBuf.length = count.toNat ∧ s0.fs.fds fd = some desc ∧
      desc.kind = .localFile ∧ desc.accMode.canRead = true⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ₛ oldBuf))
  post := fun (fd, buf, count, desc, oldBuf) s0 sf =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take count.toNat
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧
      sf.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
      sf.trace = s0.trace ∧ SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ₛ (chunk ++ oldBuf.drop chunk.length)))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslRead32_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 6)
      (muslSysPlacedLib.fnAddr muslSysMpl "read")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslRead32Spec) := by
  rw [show muslSysPlacedLib.blockProgram muslSysMpl 6 =
    muslSysPC06.rebase muslSysPl06.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib06 muslSysPl06).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "read" = muslSysPl06.base := by
    have hl : Obj.lookupBlockSym "read" muslSysPlacedLib.blocks = some (6, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl06, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep muslSccpRead_blk_ok (a_1, a, a_2, a_3, a_rest_1)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗
    (a ↦ₛ (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat ++
      a_rest_1.drop (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length)))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hchunk_lt : (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length < 2 ^ 63 := by
    simp only [List.length_take]
    have hmax := ‹a_2.toNat ≤ Arm64.MAX_RW_COUNT›
    simp only [Arm64.MAX_RW_COUNT] at hmax; omega
  have hchunk_ok := ofNat64_le_maxSyscallOk hchunk_lt
  wp_call_block muslSyscallRetOk_block_ok
    (BitVec.ofNat 64 (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], ?_, by simp [wp_norm, arm64_norm, *], ?_⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    · simp_all [wp_norm, arm64_norm]
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm] at *; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

theorem muslRead32_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "read")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslRead32Spec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 6) (by decide) muslRead32_block_ok hext hsvc

/-- Contract for `ssize_t read(int fd, void *buf, size_t count)` (`blk06`, `32`-byte stack frame)
    on an open readable `.localFile` descriptor, clamping the transfer length to
    `min count.toNat MAX_RW_COUNT`. -/
def muslRead32ClampedSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, oldBuf) s0 =>
    ⌜(s0.readReg32 .x0).zeroExtend 64 = fd ∧ 3 ≤ fd.toNat ∧ fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x1 = buf ∧ s0.readReg64 .x2 = count ∧
      buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE ∧
      oldBuf.length = count.toNat ∧ s0.fs.fds fd = some desc ∧
      desc.kind = .localFile ∧ desc.accMode.canRead = true⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ₛ oldBuf))
  post := fun (fd, buf, count, desc, oldBuf) s0 sf =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take (min count.toNat Arm64.MAX_RW_COUNT)
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧
      sf.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
      sf.trace = s0.trace ∧ SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ₛ (chunk ++ oldBuf.drop chunk.length)))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslRead32Clamped_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 6)
      (muslSysPlacedLib.fnAddr muslSysMpl "read")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslRead32ClampedSpec) := by
  rw [show muslSysPlacedLib.blockProgram muslSysMpl 6 =
    muslSysPC06.rebase muslSysPl06.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib06 muslSysPl06).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "read" = muslSysPl06.base := by
    have hl : Obj.lookupBlockSym "read" muslSysPlacedLib.blocks = some (6, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl06, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep muslSccpReadClamped_blk_ok (a_1, a, a_2, a_3, a_rest_1)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗
    (a ↦ₛ (((s0.fs.fdBytes a_3).drop a_3.offset).take (min a_2.toNat Arm64.MAX_RW_COUNT) ++
      a_rest_1.drop (((s0.fs.fdBytes a_3).drop a_3.offset).take (min a_2.toNat Arm64.MAX_RW_COUNT)).length)))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hchunk_lt : (((s0.fs.fdBytes a_3).drop a_3.offset).take (min a_2.toNat Arm64.MAX_RW_COUNT)).length < 2 ^ 63 := by
    have hle : (((s0.fs.fdBytes a_3).drop a_3.offset).take (min a_2.toNat Arm64.MAX_RW_COUNT)).length ≤ Arm64.MAX_RW_COUNT :=
      Nat.le_trans (List.length_take_le _ _) (Nat.min_le_right _ _)
    exact Nat.lt_of_le_of_lt hle (by decide)
  have hchunk_ok := ofNat64_le_maxSyscallOk hchunk_lt
  wp_call_block muslSyscallRetOk_block_ok
    (BitVec.ofNat 64 (((s0.fs.fdBytes a_3).drop a_3.offset).take (min a_2.toNat Arm64.MAX_RW_COUNT)).length)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], ?_, by simp [wp_norm, arm64_norm, *], ?_⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    · simp_all [wp_norm, arm64_norm]
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm] at *; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

theorem muslRead32Clamped_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "read")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslRead32ClampedSpec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 6) (by decide) muslRead32Clamped_block_ok hext hsvc

/-- Contract for `ssize_t write(2, const void *buf, size_t count)` (`blk07`, `32`-byte stack frame)
    writing a read-only message `bs` (`0 < bs.length <= MAX_RW_COUNT`) to `stderr` (`fd = 2`). -/
def muslWriteStderr32Spec : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (buf, bs) s0 =>
    ⌜s0.readReg32 .x0 = 2#32 ∧ s0.readReg64 .x1 = buf ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ 0 < bs.length ∧
      bs.length ≤ Arm64.MAX_RW_COUNT ∧ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ᵣ bs))
  post := fun (buf, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 bs.length ∧ sf.fs = s0.fs ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stderr bs ∧ SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ᵣ bs))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslWriteStderr32_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 7)
      (muslSysPlacedLib.fnAddr muslSysMpl "write")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslWriteStderr32Spec) := by
  rw [show muslSysPlacedLib.blockProgram muslSysMpl 7 =
    muslSysPC07.rebase muslSysPl07.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib07 muslSysPl07).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "write" = muslSysPl07.base := by
    have hl : Obj.lookupBlockSym "write" muslSysPlacedLib.blocks = some (7, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl07, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep muslSccpWriteStderr_blk_ok (a_1, a_rest)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗ (a_1 ↦ᵣ a_rest))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hlt63 : a_rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt ‹a_rest.length ≤ Arm64.MAX_RW_COUNT› (by decide)
  have hlen_ok := ofNat64_le_maxSyscallOk hlt63
  wp_call_block muslSyscallRetOk_block_ok (BitVec.ofNat 64 a_rest.length)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

theorem muslWriteStderr32_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "write")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslWriteStderr32Spec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 7) (by decide) muslWriteStderr32_block_ok hext hsvc

/-- Contract for `ssize_t write(fd, const void *buf, size_t count)` (`blk07`, `32`-byte stack frame)
    writing an owned non-empty slice `bs` (`0 < bs.length <= MAX_RW_COUNT`) to an open writable
    `.localFile` `fd >= 3`. -/
def muslWriteFile32Spec : Spec (BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, desc, bs) s0 =>
    ⌜(s0.readReg32 .x0).zeroExtend 64 = fd ∧ 3 ≤ fd.toNat ∧ fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x1 = buf ∧ s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
      0 < bs.length ∧ bs.length ≤ Arm64.MAX_RW_COUNT ∧ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT ∧
      s0.fs.fds fd = some desc ∧
      desc.kind = .localFile ∧ desc.accMode.canWrite = true ∧ desc.append = false ∧
      desc.offset + bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ₛ bs))
  post := fun (fd, buf, desc, bs) s0 sf =>
    let oldBytes := match s0.fs.files desc.path with | some (.file b) => b | _ => []
    let newBytes := writeFileBytes oldBytes desc.offset bs
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 bs.length ∧
      sf.fs = (s0.fs.setFile desc.path (some (.file newBytes))).setFd fd
        (some { desc with offset := desc.offset + bs.length }) ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes (OutputStream.ofFd fd) bs ∧
      SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ₛ bs))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslWriteFile32_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 7)
      (muslSysPlacedLib.fnAddr muslSysMpl "write")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslWriteFile32Spec) := by
  rw [show muslSysPlacedLib.blockProgram muslSysMpl 7 =
    muslSysPC07.rebase muslSysPl07.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib07 muslSysPl07).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "write" = muslSysPl07.base := by
    have hl : Obj.lookupBlockSym "write" muslSysPlacedLib.blocks = some (7, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl07, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep muslSccpWriteFile_blk_ok (a_1, a, a_2, a_rest)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗ (a ↦ₛ a_rest))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hlt63 : a_rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt ‹a_rest.length ≤ Arm64.MAX_RW_COUNT› (by decide)
  have hlen_ok := ofNat64_le_maxSyscallOk hlt63
  wp_call_block muslSyscallRetOk_block_ok (BitVec.ofNat 64 a_rest.length)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], ?_,
      by simp_all [wp_norm, arm64_norm, TraceEvent.ofBytes, OutputStream.ofFd], ?_⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    · cases a_2; cases hfl : s0.fs.files _ <;> (try cases ‹FsEntry›) <;> simp_all [wp_norm, arm64_norm]
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

theorem muslWriteFile32_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "write")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslWriteFile32Spec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 7) (by decide) muslWriteFile32_block_ok hext hsvc

/-- Contract for `ssize_t write(fd, const void *buf, size_t count)` (`blk07`, `32`-byte stack frame)
    writing an owned non-empty clamped slice `bs` (`bs.length = min count.toNat MAX_RW_COUNT`,
    `count != 0`) to an open writable `.localFile` `fd >= 3`. -/
def muslWriteFile32ClampedSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, bs) s0 =>
    ⌜(s0.readReg32 .x0).zeroExtend 64 = fd ∧ 3 ≤ fd.toNat ∧ fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x1 = buf ∧ s0.readReg64 .x2 = count ∧ count ≠ 0#64 ∧
      bs.length = min count.toNat Arm64.MAX_RW_COUNT ∧
      buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE ∧
      s0.fs.fds fd = some desc ∧
      desc.kind = .localFile ∧ desc.accMode.canWrite = true ∧ desc.append = false ∧
      desc.offset + bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ₛ bs))
  post := fun (fd, buf, _, desc, bs) s0 sf =>
    let oldBytes := match s0.fs.files desc.path with | some (.file b) => b | _ => []
    let newBytes := writeFileBytes oldBytes desc.offset bs
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 bs.length ∧
      sf.fs = (s0.fs.setFile desc.path (some (.file newBytes))).setFd fd
        (some { desc with offset := desc.offset + bs.length }) ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes (OutputStream.ofFd fd) bs ∧
      SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ₛ bs))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslWriteFile32Clamped_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 7)
      (muslSysPlacedLib.fnAddr muslSysMpl "write")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslWriteFile32ClampedSpec) := by
  rw [show muslSysPlacedLib.blockProgram muslSysMpl 7 =
    muslSysPC07.rebase muslSysPl07.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib07 muslSysPl07).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "write" = muslSysPl07.base := by
    have hl : Obj.lookupBlockSym "write" muslSysPlacedLib.blocks = some (7, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl07, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep muslSccpWriteFileClamped_blk_ok (a_1, a, a_2, a_3, a_rest_1)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗ (a ↦ₛ a_rest_1))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hlt63 : a_rest_1.length < 2 ^ 63 := by
    have hle : a_rest_1.length ≤ Arm64.MAX_RW_COUNT := by
      rw [‹a_rest_1.length = min a_2.toNat Arm64.MAX_RW_COUNT›]
      exact Nat.min_le_right _ _
    exact Nat.lt_of_le_of_lt hle (by decide)
  have hlen_ok := ofNat64_le_maxSyscallOk hlt63
  wp_call_block muslSyscallRetOk_block_ok (BitVec.ofNat 64 a_rest_1.length)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], ?_,
      by simp_all [wp_norm, arm64_norm, TraceEvent.ofBytes, OutputStream.ofFd], ?_⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    · cases a_3; cases hfl : s0.fs.files _ <;> (try cases ‹FsEntry›) <;> simp_all [wp_norm, arm64_norm]
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

theorem muslWriteFile32Clamped_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "write")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslWriteFile32ClampedSpec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 7) (by decide) muslWriteFile32Clamped_block_ok hext hsvc

/-! ## `open` -/

/-- Outcome characterization of `execOpenat` for `musl`'s `open(path, flags, mode)` (`O_CLOEXEC` set). -/
inductive OpenatOutcome where
  | ok (fd : BitVec 64) (desc : FdEntry) (fs' : FsState) (traceExtra : List TraceEvent)
  | err (errPred : Nat → Prop)

/-- Hypothesis asserting that `execOpenat` on `(AT_FDCWD, path, flags ||| O_LARGEFILE_W32, mode)`
    from any state with filesystem `fs0` and trace `tr0` behaves according to `out`. -/
def OpenatExecSpec (fs0 : FsState) (tr0 : List TraceEvent) (path : String)
    (flags mode : BitVec 32) (out : OpenatOutcome) : Prop :=
  ∀ {s : State},
    readCString s.mem (s.readReg64 .x1) = .ok path →
    s.fs = fs0 →
    s.trace = tr0 →
    s.readReg32 .x0 = AT_FDCWD_W32 →
    s.readReg32 .x2 = flags ||| O_LARGEFILE_W32 →
    s.readReg32 .x3 = mode →
    match out with
    | .ok fd desc fs' traceExtra =>
      fd.toNat < 2 ^ 31 ∧
      fs'.fds fd = some desc ∧
      desc.kind = .localFile ∧
      desc.cloexec = true ∧
      execOpenat s =
        (((s.setFs fs').appendTrace traceExtra).writeReg64 .x0 fd).advancePC
    | .err errPred =>
      ∃ errno : Nat,
        1 ≤ errno ∧ errno ≤ 4095 ∧ errPred errno ∧
        execOpenat s = (s.writeReg64 .x0 (-BitVec.ofNat 64 errno)).advancePC

private def muslSccpOpenatExecSpec :
    Spec (BitVec 64 × String × BitVec 32 × BitVec 32 × FsState × List TraceEvent × OpenatOutcome) where
  pre := fun (cstr, path, flags, mode, fs0, tr0, out) s0 =>
    ⌜s0.readReg64 .x0 = 56#64 ∧
      s0.readReg32 .x1 = AT_FDCWD_W32 ∧
      s0.readReg64 .x2 = cstr ∧
      s0.readReg32 .x3 = flags ||| O_LARGEFILE_W32 ∧
      s0.readReg32 .x4 = mode ∧
      s0.fs = fs0 ∧
      s0.trace = tr0 ∧
      ValidCPath path ∧
      OpenatExecSpec fs0 tr0 path flags mode out⌝ ∗
    (cstr ↦ₛ cstrBytes path)
  post := fun (cstr, path, _, _, fs0, tr0, out) s0 sf =>
    match out with
    | .ok fd desc fs' traceExtra =>
      ⌜sf.readReg64 .x0 = fd ∧
        fd.toNat < 2 ^ 31 ∧
        fs'.fds fd = some desc ∧
        desc.kind = .localFile ∧
        desc.cloexec = true ∧
        sf.fs = fs' ∧
        sf.mem = s0.mem ∧
        sf.trace = tr0 ++ traceExtra ∧
        SyscallPreserved s0 sf⌝ ∗
      (cstr ↦ₛ cstrBytes path)
    | .err errPred =>
      ∃∗ errno : Nat,
        ⌜sf.readReg64 .x0 = -BitVec.ofNat 64 errno ∧
          1 ≤ errno ∧ errno ≤ 4095 ∧ errPred errno ∧
          sf.fs = fs0 ∧
          sf.mem = s0.mem ∧
          sf.trace = tr0 ∧
          SyscallPreserved s0 sf⌝ ∗
        (cstr ↦ₛ cstrBytes path)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslSccpOpenatExec_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC03.rebase muslSysPl03.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSccpOpenatExecSpec) := by
  rw [resolve_syscall_cp]; wp_entry
  obtain ⟨hlen_p, hval_p⟩ := h_9
  refine muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine step_svc_openat_rw (path := a) (fname := a_1) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simp [wp_norm, arm64_norm, h_4])
    hlen_p hval_p (fun hcs => ?_)
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  rw [sepConj_emp]
  have hexec := h_1 hcs (by simp [wp_norm, arm64_norm, h_7]) (by simp [wp_norm, arm64_norm, h_8])
    (by simpa [wp_norm, arm64_norm] using h_3) (by simpa [wp_norm, arm64_norm] using h_5)
    (by simpa [wp_norm, arm64_norm] using h_6)
  cases a_rest_1 with
  | ok fd desc fs' traceExtra =>
    dsimp only [OpenatExecSpec] at hexec
    rcases hexec with ⟨hfd_lt, hfds, hkind, hclo, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [muslSccpOpenatExecSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], hfd_lt, hfds, hkind, hclo,
        by simp [wp_norm, arm64_norm, State.appendTrace], rfl,
        by simp [wp_norm, arm64_norm, State.appendTrace, h_8], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [wp_norm, arm64_norm, State.appendTrace, calleeSavedVRegs]
  | err errPred =>
    dsimp only [OpenatExecSpec] at hexec
    rcases hexec with ⟨errno, h1, h2, hpred, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [muslSccpOpenatExecSpec]
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], h1, h2, hpred,
        by simp [wp_norm, arm64_norm, h_7], rfl,
        by simp [wp_norm, arm64_norm, h_8], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem truncate32_and64 (x y : BitVec 64) :
    (x &&& y).truncate 32 = x.truncate 32 &&& y.truncate 32 := by ext i hi; simp

@[simp, arm64_norm] private theorem muslErrnoAddr_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    muslErrnoAddr (s.writeReg64 r v) = muslErrnoAddr s := rfl
@[simp, arm64_norm] private theorem muslErrnoAddr_setPC (s : State) (pc : BitVec 64) :
    muslErrnoAddr (s.setPC pc) = muslErrnoAddr s := rfl
@[simp, arm64_norm] private theorem muslErrnoAddr_setMem (s : State) (m : Memory) :
    muslErrnoAddr (s.setMem m) = muslErrnoAddr s := rfl

private theorem getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    fd.getLsbD 31 = false := by
  rw [BitVec.getLsbD]
  exact Nat.testBit_lt_two_pow hfd

private theorem truncate32_getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd.truncate 32).getLsbD 31 = false := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, getLsbD_31_false_of_lt hfd]; decide

private theorem mask32_or_zero_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 ||| 0#64) = fd := by
  simp only [BitVec.ushiftRight_zero, BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem setWidth64_setWidth32_and_mask_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.setWidth 32 fd) &&& 4294967295#64 = fd := by
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
  rw [h1]
  simpa [BitVec.ushiftRight_zero, BitVec.or_zero] using mask32_or_zero_of_lt31 hfd

private theorem sxtw64_eq_self_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 |||
      (if fd.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = fd := by
  rw [getLsbD_31_false_of_lt hfd]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_and, BitVec.or_zero, BitVec.ushiftRight_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem neg_ofNat_toNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
  rw [BitVec.toNat_neg, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).getLsbD 31 = true := by
  rw [BitVec.getLsbD, neg_ofNat_toNat h1 h2, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hdiv : (2 ^ 64 - err) / 2 ^ 31 = 2 ^ 33 - 1 := by omega
  rw [hdiv]; decide

private theorem truncate32_getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err).truncate 32).getLsbD 31 = true := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, getLsbD_31_neg_ofNat h1 h2]; decide

private theorem sxtw_neg_of_hi_ones {v : BitVec 64} (h : v >>> 32 = 0xffffffff#64) :
    (v >>> 0 &&& 4294967295#64 ||| 0xffffffffffffffff#64 &&& 0xffffffff00000000#64) = v := by
  bv_robdd

private theorem sxtw64_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err) >>> 0 &&& 4294967295#64 |||
      (if (-BitVec.ofNat 64 err).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = -BitVec.ofNat 64 err := by
  rw [getLsbD_31_neg_ofNat h1 h2]
  simp only [↓reduceIte]
  refine sxtw_neg_of_hi_ones (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_ushiftRight, neg_ofNat_toNat h1 h2, Nat.shiftRight_eq_div_pow]
  have hmax : (4294967295#64 : BitVec 64).toNat = 2 ^ 32 - 1 := by decide
  rw [hmax]; omega

private theorem zeroExtend64_getLsbD_6 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 6 = flags.getLsbD 6 := by simp

private theorem zeroExtend64_getLsbD_19 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 19 = flags.getLsbD 19 := by simp

private theorem tmpfile_mask_eq_zero {flags : BitVec 32} (h : flags &&& 0x404000#32 = 0#32) :
    (flags &&& 0x007fc000#32) &&& 0xffc07fff#32 = 0#32 := by
  have heq : (flags &&& 0x007fc000#32) &&& 0xffc07fff#32 = flags &&& 0x404000#32 := by bv_bits
  rw [heq, h]

private theorem or_largefile_sxtw_truncate32 (flags : BitVec 32) :
    (((flags.zeroExtend 64 ||| 131072#64) >>> 0 &&& 4294967295#64 |||
      (if (flags.zeroExtend 64 ||| 131072#64).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64).truncate 32) = flags ||| O_LARGEFILE_W32 := by
  rw [sxtw64_truncate32]
  change (flags.zeroExtend 64 ||| 0x20000#64).truncate 32 = flags ||| 0x20000#32
  bv_bits

/-- Generic `execOpenat`-parameterized contract for `open(path, flags, mode)` (`blk08`, `112`-byte
    stack frame) on the non-`O_CREAT` path (`O_CREAT = 0`, not `O_TMPFILE`, `O_CLOEXEC = 1`). -/
def muslOpenNoCreatCloexecExecSpec : Spec (BitVec 64 × String × BitVec 32 × BitVec 32 × OpenatOutcome) where
  pre := fun (cstr, path, flags, e0, out) s0 =>
    ⌜s0.readReg64 .x0 = cstr ∧
      s0.readReg32 .x1 = flags ∧
      flags.getLsbD 6 = false ∧
      flags &&& 0x404000#32 = 0#32 ∧
      flags.getLsbD 19 = true ∧
      ValidCPath path ∧
      OpenatExecSpec s0.fs s0.trace path flags 0#32 out⌝ ∗
    (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (cstr, path, _, e0, out) s0 sf =>
    match out with
    | .ok fd _ fs' traceExtra =>
      ⌜sf.readReg32 .x0 = fd.truncate 32 ∧
        sf.fs = fs' ∧
        sf.trace = s0.trace ++ traceExtra ∧
        SyscallPreserved s0 sf⌝ ∗
      (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr sf ↦₃₂ e0))
    | .err errPred =>
      ∃∗ errno : Nat,
        ⌜1 ≤ errno ∧ errno ≤ 4095 ∧ errPred errno ∧
          sf.readReg32 .x0 = 0xffffffff#32 ∧
          sf.fs = s0.fs ∧
          sf.trace = s0.trace ∧
          SyscallPreserved s0 sf⌝ ∗
        (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr sf ↦₃₂ BitVec.ofNat 32 errno))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Generic `execOpenat`-parameterized contract for `open(path, flags, mode)` (`blk08`, `112`-byte
    stack frame) on the `O_CREAT` path (`O_CREAT = 1`, `O_CLOEXEC = 1`). -/
def muslOpenCreatCloexecExecSpec : Spec (BitVec 64 × String × BitVec 32 × BitVec 32 × OpenatOutcome) where
  pre := fun (cstr, path, flags, e0, out) s0 =>
    ⌜s0.readReg64 .x0 = cstr ∧
      s0.readReg32 .x1 = flags ∧
      flags.getLsbD 6 = true ∧
      flags.getLsbD 19 = true ∧
      ValidCPath path ∧
      OpenatExecSpec s0.fs s0.trace path flags (s0.readReg32 .x2) out⌝ ∗
    (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := muslOpenNoCreatCloexecExecSpec.post
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

local macro "musl_open_finish_after_sccp " s0:ident sf:ident h_clo:ident e0:ident out:ident : tactic =>
  `(tactic| (
    cases $out:ident with
    | ok fd desc fs' traceExtra =>
      wp_conv_pre => try dsimp only [muslSccpOpenatExecSpec]; simp only [sepConj_assoc]
      apply SepWP.pure_elim
      rintro ⟨hx0, hfd_lt, hfds, hkind, hclo, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
      try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
      have hsvc08 : muslSysPC08.svc = Syscall.standard := rfl
      have hsxtw : (fd >>> 0 &&& 4294967295#64 |||
          (if fd.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
            0xffffffff00000000#64) = fd := sxtw64_eq_self_of_lt31 hfd_lt
      have hmask0 : (fd >>> 0 &&& 4294967295#64 ||| 0#64) = fd := mask32_or_zero_of_lt31 hfd_lt
      have hfd_ze_mask : BitVec.setWidth 64 (BitVec.setWidth 32 fd) &&& 4294967295#64 = fd :=
        setWidth64_setWidth32_and_mask_of_lt31 hfd_lt
      have hfd_ze : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
      have htbnz : fd.getLsbD 31 = false := getLsbD_31_false_of_lt hfd_lt
      have htbnz32 : (fd.truncate 32).getLsbD 31 = false := truncate32_getLsbD_31_false_of_lt hfd_lt
      wp_sym_steps 1
      (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, hmask0, htbnz, htbnz32])
      wp_sym_steps 1
      simp only [wp_norm, arm64_norm, hx0, hsxtw, hmask0, htbnz, htbnz32, Bool.false_eq_true, ↓reduceIte]
      wp_sym_steps 1
      simp only [wp_norm, arm64_norm, ‹State.readReg64 $sf (Reg.gpr 19#5) = _›,
        zeroExtend64_getLsbD_19, $h_clo:ident, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hdesc_eq : ({ desc with cloexec := true } : FdEntry) = desc := by
        cases desc; simp at hclo; subst hclo; rfl
      have hsetfd_eq : fs'.setFd fd (some { desc with cloexec := true }) = fs' := by
        rw [hdesc_eq]; exact FsState.setFd_self hfds
      have h1_clo : (1#64 &&& 1#64 != 0#64) = true := by decide
      wp_sym_steps
      refine step_svc_fcntl_setfd (fd := fd) (arg := 1#64) rfl
        (by simp [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hsxtw, hmask0, hfd_ze_mask, hfd_ze]) hfd_lt
        (by simp [wp_norm, arm64_norm, F_SETFD_W32]) (by simp [wp_norm, arm64_norm])
        (by simpa [wp_norm, arm64_norm, hfs1] using hfds) hkind ?_
        (by simp [wp_norm, arm64_norm, hsvc08, Reg.x8, *])
      dsimp only
      (conv => arg 3; simp only [wp_norm, arm64_norm, hfs1, h1_clo, hsetfd_eq])
      wp_sym_steps
      have hfd_ok : fd.toNat ≤ 2 ^ 64 - 4096 := by omega
      wp_cut_codeLoaded
      wp_call_block muslSyscallRetOk_block_ok fd
      rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
      try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1]
        at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
      wp_sym_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
      refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
      · try dsimp only [muslOpenNoCreatCloexecExecSpec, muslOpenCreatCloexecExecSpec]
        try rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp_all [wp_norm, arm64_norm],
          by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
        · rw [show stackAt (State.sp $s0) 112 =
              stackAt (State.sp $s0 - 80#64) 32 ∗ cells (State.sp $s0 - 80#64) 10 from
            stackAt_split_cells (State.sp $s0) 32 10 (by decide)]
          cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
      · unfold CalleeSavedPreserved
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    | err errPred =>
      wp_conv_pre => try dsimp only [muslSccpOpenatExecSpec]; simp only [sepExists_sepConj_left, sepConj_assoc]
      apply SepWP.exists_left; intro errno
      apply SepWP.pure_elim
      rintro ⟨hx0, h1, h2, hpred, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
      try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
      have hsxtw : ((-BitVec.ofNat 64 errno) >>> 0 &&& 4294967295#64 |||
          (if (-BitVec.ofNat 64 errno).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
            0xffffffff00000000#64) = -BitVec.ofNat 64 errno := sxtw64_neg_ofNat h1 h2
      have htbnz : (-BitVec.ofNat 64 errno).getLsbD 31 = true := getLsbD_31_neg_ofNat h1 h2
      have htbnz32 : ((-BitVec.ofNat 64 errno).truncate 32).getLsbD 31 = true :=
        truncate32_getLsbD_31_neg_ofNat h1 h2
      have htp_e : muslErrnoAddr $s0 = muslErrnoAddr $sf := by unfold muslErrnoAddr; rw [htp1]
      wp_conv_pre => rw [htp_e]
      wp_cut_codeLoaded; wp_sym_steps 1
      (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, htbnz, htbnz32])
      wp_sym_steps 1
      simp only [wp_norm, arm64_norm, hx0, htbnz, htbnz32, ↓reduceIte]
      wp_sym_steps
      wp_call_block muslSyscallRetErr_block_ok (errno, $e0)
      rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
      try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1]
        at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
      wp_sym_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
      refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
      · try dsimp only [muslOpenNoCreatCloexecExecSpec, muslOpenCreatCloexecExecSpec]
        try rw [sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨errno, ?_⟩
        try rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨h1, h2, hpred, by simp [wp_norm, arm64_norm, *],
          by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *], ?_⟩,
          ProofLib.Satisfies.of_entails hmem ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
        · rw [show stackAt (State.sp $s0) 112 =
              stackAt (State.sp $s0 - 80#64) 32 ∗ cells (State.sp $s0 - 80#64) 10 from
            stackAt_split_cells (State.sp $s0) 32 10 (by decide)]
          cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
      · unfold CalleeSavedPreserved
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]))

theorem muslOpenNoCreatCloexecExec_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 8)
      (muslSysPlacedLib.fnAddr muslSysMpl "open")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslOpenNoCreatCloexecExecSpec) := by
  rw [show muslSysPlacedLib.blockProgram muslSysMpl 8 =
    muslSysPC08.rebase muslSysPl08.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib08 muslSysPl08).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "open" = muslSysPl08.base := by
    have hl : Obj.lookupBlockSym "open" muslSysPlacedLib.blocks = some (8, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl08, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 112 = stackAt (s0.sp - 80#64) 32 ∗ cells (s0.sp - 80#64) 10 from
      stackAt_split_cells s0.sp 32 10 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  wp_stp64_perm hm1; wp_sym_steps 1; wp_str64_perm hm2; wp_sym_steps 1; wp_str64_perm hm3
  (conv => arg 3; simp only [wp_norm, arm64_norm, h_3, zeroExtend64_getLsbD_6, h_4])
  wp_sym_steps 3
  have htmp := tmpfile_mask_eq_zero h_5
  (conv => arg 3; simp only [wp_norm, arm64_norm, truncate32_and64, h_3, htmp])
  wp_sym_steps
  have hcwd : (-100#32 : BitVec 32) = AT_FDCWD_W32 := by decide
  have hflg := or_largefile_sxtw_truncate32 a_2
  have ⟨_, _⟩ := ‹ValidCPath a›
  wp_call_block_keep muslSccpOpenatExec_blk_ok (a_1, a, a_2, 0#32, s0.fs, s0.trace, a_rest_1)
  musl_open_finish_after_sccp s0 sf h_6 a_3 a_rest_1

theorem muslOpenCreatCloexecExec_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 8)
      (muslSysPlacedLib.fnAddr muslSysMpl "open")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslOpenCreatCloexecExecSpec) := by
  rw [show muslSysPlacedLib.blockProgram muslSysMpl 8 =
    muslSysPC08.rebase muslSysPl08.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib08 muslSysPl08).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "open" = muslSysPl08.base := by
    have hl : Obj.lookupBlockSym "open" muslSysPlacedLib.blocks = some (8, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl08, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 112 = stackAt (s0.sp - 80#64) 32 ∗ cells (s0.sp - 80#64) 10 from
      stackAt_split_cells s0.sp 32 10 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  wp_stp64_perm hm1; wp_sym_steps 1; wp_str64_perm hm2; wp_sym_steps 1; wp_str64_perm hm3
  (conv => arg 3; simp only [wp_norm, arm64_norm, h_3, zeroExtend64_getLsbD_6, h_4])
  wp_sym_steps 2
  wp_conv_pre => rw [pointsTo64_split32_sub s0.sp 8#64 4#64]
  wp_sym_steps 4
  wp_conv_pre => rw [← pointsTo64_split32_sub s0.sp 8#64 4#64]
  wp_stp64_perm hm4; wp_str64_perm hm5; wp_stp32_64_perm hm6
  wp_sym_steps
  have hcwd : (-100#32 : BitVec 32) = AT_FDCWD_W32 := by decide
  have hflg := or_largefile_sxtw_truncate32 a_2
  have ⟨_, _⟩ := ‹ValidCPath a›
  wp_call_block_keep muslSccpOpenatExec_blk_ok (a_1, a, a_2, s0.readReg32 .x2, s0.fs, s0.trace, a_rest_1)
  musl_open_finish_after_sccp s0 sf h_5 a_3 a_rest_1

/-- Contract for `int open(const char *path, O_CLOEXEC, mode)` (`blk08`, `112`-byte stack frame)
    opening a relative path read-only (`s0.fs.allocFd = some fd`, `fd < 2 ^ 31`). -/
def muslOpenRdonlySpec (fd : BitVec 64 := 3#64) : Spec (BitVec 64 × String × BitVec 32) where
  pre := fun (cstr, path, e0) s0 =>
    ⌜s0.readReg64 .x0 = cstr ∧
      s0.readReg32 .x1 = O_CLOEXEC_W32 ∧
      ValidRelCPath path ∧
      (ancestorWalkErrno? s0.fs path = none → s0.fs.files path ≠ some .dir) ∧
      s0.fs.allocFd = some fd ∧
      fd.toNat < 2 ^ 31⌝ ∗
    (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (cstr, path, e0) s0 sf =>
    match fsReadFile? s0.fs path with
    | some fileBytes =>
      ⌜sf.readReg32 .x0 = fd.truncate 32 ∧
        s0.fs.files path = some (.file fileBytes) ∧
        sf.fs = s0.fs.setFd fd
          (some { path := path, accMode := .rdonly, append := false, cloexec := true, offset := 0 }) ∧
        sf.trace = s0.trace ∧
        SyscallPreserved s0 sf⌝ ∗
      (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr sf ↦₃₂ e0))
    | none =>
      ∃∗ err : BitVec 32,
        ⌜sf.readReg32 .x0 = 0xffffffff#32 ∧
          (err = 2#32 ∨ err = 20#32 ∨ err = 36#32) ∧
          sf.fs = s0.fs ∧
          sf.trace = s0.trace ∧
          SyscallPreserved s0 sf⌝ ∗
        (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr sf ↦₃₂ err))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem setFs_appendTrace_nil (s : State) (fs' : FsState) :
    (s.setFs fs').appendTrace [] = s.setFs fs' := by
  cases s; simp [State.setFs, State.appendTrace]

theorem muslOpenRdonly_block_ok [MuslSysPlacement] (fd : BitVec 64 := 3#64) :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 8)
      (muslSysPlacedLib.fnAddr muslSysMpl "open")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl (muslOpenRdonlySpec fd)) := by
  refine subroutine_ok_refine_entails muslOpenNoCreatCloexecExec_block_ok ?_
  rintro ⟨cstr, path, e0⟩ R s0 hpre
  simp only [MultiPlacedLib.withCodeLoaded, muslOpenRdonlySpec, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, ⟨hcp, hlead, hdot⟩, hnotdir, halloc, hfd_lt⟩, hm⟩
  have hb6 : O_CLOEXEC_W32.getLsbD 6 = false := by decide
  have htmp : O_CLOEXEC_W32 &&& 0x404000#32 = 0#32 := by decide
  have hb19 : O_CLOEXEC_W32.getLsbD 19 = true := by decide
  have hfl_eq : O_CLOEXEC_W32 ||| O_LARGEFILE_W32 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32 := by decide
  cases hread : fsReadFile? s0.fs path with
  | some fileBytes =>
    let desc : FdEntry :=
      { path := path, accMode := .rdonly, append := false, cloexec := true, offset := 0 }
    let fs' : FsState := s0.fs.setFd fd (some desc)
    have hfile_s0 : s0.fs.files path = some (.file fileBytes) := by
      unfold fsReadFile? FsState.files at hread
      split at hread
      · cases hread
      · cases hg : s0.fs.getEntry (normalizePath path) with
        | none => simp [hg] at hread
        | some e =>
          cases e with
          | dir => simp [hg] at hread
          | file b => simp [hg] at hread; subst hread; exact hg
    refine ⟨(cstr, path, O_CLOEXEC_W32, e0, .ok fd desc fs' []), ?_, fun sf => ?_⟩
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecExecSpec, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2 _
      have hexec := execOpenat_rdonly_cloexec hs_x0 (hfl_eq ▸ hs_x2) hcs hlead hdot
        (hs_fs.symm ▸ hnotdir) (hs_fs.symm ▸ halloc)
      rw [hs_fs, hread] at hexec
      refine ⟨hfd_lt, by simp [fs', FsState.setFd], rfl, rfl, ?_⟩
      rw [setFs_appendTrace_nil]
      exact hexec.2
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecExecSpec,
        muslOpenRdonlySpec, hread, List.append_nil]
      exact sepConj_mono_left (Entails.pure_mono fun ⟨hr0, hfs, htr, hsp⟩ =>
        ⟨hr0, hfile_s0, hfs, htr, hsp⟩)
  | none =>
    refine ⟨(cstr, path, O_CLOEXEC_W32, e0, .err (fun n => n = 2 ∨ n = 20 ∨ n = 36)), ?_, fun sf => ?_⟩
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecExecSpec, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2 _
      have hexec := execOpenat_rdonly_cloexec hs_x0 (hfl_eq ▸ hs_x2) hcs hlead hdot
        (hs_fs.symm ▸ hnotdir) (hs_fs.symm ▸ halloc)
      rw [hs_fs, hread] at hexec
      rcases hexec with ⟨err, herr, hexec_eq⟩
      rcases herr with rfl | rfl | rfl
      · exact ⟨2, by decide, by decide, Or.inl rfl, hexec_eq⟩
      · exact ⟨20, by decide, by decide, Or.inr (Or.inl rfl), hexec_eq⟩
      · exact ⟨36, by decide, by decide, Or.inr (Or.inr rfl), hexec_eq⟩
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecExecSpec,
        muslOpenRdonlySpec, hread]
      refine Entails.sepExists_elim fun errno => Entails.sepExists_right (BitVec.ofNat 32 errno) ?_
      exact sepConj_mono_left (Entails.pure_mono fun ⟨_, _, hpred, hr0, hfs, htr, hsp⟩ =>
        ⟨hr0, by rcases hpred with rfl | rfl | rfl <;> decide, hfs, htr, hsp⟩)

theorem muslOpenRdonly_ok [MuslSysPlacement] {P : Program} (fd : BitVec 64 := 3#64)
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "open")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl (muslOpenRdonlySpec fd)) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 8) (by decide) (muslOpenRdonly_block_ok fd) hext hsvc

/-- Contract for `int open(const char *path, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, mode)`
    (`blk08`, `112`-byte stack frame) creating/truncating a relative path (`allocFd = some fd`,
    owner read-write `mode`). -/
def muslOpenCreateTruncSpec (fd : BitVec 64 := 3#64) : Spec (BitVec 64 × String × BitVec 32) where
  pre := fun (cstr, path, e0) s0 =>
    ⌜s0.readReg64 .x0 = cstr ∧
      s0.readReg32 .x1 = 1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_CLOEXEC_W32 ∧
      s0.readReg32 .x2 &&& O_CREAT_OWNER_RW_MASK = O_CREAT_OWNER_RW_MASK ∧
      ValidRelCPath path ∧
      s0.fs.allocFd = some fd ∧
      fd.toNat < 2 ^ 31⌝ ∗
    (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (cstr, path, e0) s0 sf =>
    if fsCanWriteFile s0.fs path then
      ⌜sf.readReg32 .x0 = fd.truncate 32 ∧
        sf.fs = (s0.fs.setFile path (some (.file []))).setFd fd
          (some { path := path, accMode := .wronly, append := false, cloexec := true, offset := 0 }) ∧
        sf.trace = s0.trace ++ [.fileChanged (normalizePath path).toPathString] ∧
        SyscallPreserved s0 sf⌝ ∗
      (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr sf ↦₃₂ e0))
    else
      ∃∗ err : BitVec 32,
        ⌜sf.readReg32 .x0 = 0xffffffff#32 ∧
          (err = 2#32 ∨ err = 20#32 ∨ err = 21#32 ∨ err = 36#32) ∧
          sf.fs = s0.fs ∧
          sf.trace = s0.trace ∧
          SyscallPreserved s0 sf⌝ ∗
        (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr sf ↦₃₂ err))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslOpenCreateTrunc_block_ok [MuslSysPlacement] (fd : BitVec 64 := 3#64) :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 8)
      (muslSysPlacedLib.fnAddr muslSysMpl "open")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl (muslOpenCreateTruncSpec fd)) := by
  refine subroutine_ok_refine_entails muslOpenCreatCloexecExec_block_ok ?_
  rintro ⟨cstr, path, e0⟩ R s0 hpre
  simp only [MultiPlacedLib.withCodeLoaded, muslOpenCreateTruncSpec, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hmode, ⟨hcp, hlead, hdot⟩, halloc, hfd_lt⟩, hm⟩
  let flags32 : BitVec 32 := 1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_CLOEXEC_W32
  have hb6 : flags32.getLsbD 6 = true := by decide
  have hb19 : flags32.getLsbD 19 = true := by decide
  have hfl_eq : flags32 ||| O_LARGEFILE_W32 =
      1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32 := by decide
  by_cases hcan : fsCanWriteFile s0.fs path = true
  · let desc : FdEntry :=
      { path := path, accMode := .wronly, append := false, cloexec := true, offset := 0 }
    let fs' : FsState := (s0.fs.setFile path (some (.file []))).setFd fd (some desc)
    let trExtra : List TraceEvent := [.fileChanged (normalizePath path).toPathString]
    refine ⟨(cstr, path, flags32, e0, .ok fd desc fs' trExtra), ?_, fun sf => ?_⟩
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenCreatCloexecExecSpec, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2 hs_x3
      have hexec := execOpenat_wronly_creat_trunc_cloexec hs_x0 (hfl_eq ▸ hs_x2)
        (hs_x3.symm ▸ hmode) hcs hlead hdot (hs_fs.symm ▸ halloc)
      rw [hs_fs, hcan] at hexec; simp only [↓reduceIte] at hexec
      refine ⟨hfd_lt, by simp [fs', FsState.setFd], rfl, rfl, ?_⟩
      simpa [fs', desc, trExtra] using hexec
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenCreatCloexecExecSpec,
        muslOpenNoCreatCloexecExecSpec, muslOpenCreateTruncSpec, hcan, ↓reduceIte]
      exact Entails.refl _
  · simp only [Bool.not_eq_true] at hcan
    refine ⟨(cstr, path, flags32, e0, .err (fun n => n = 2 ∨ n = 20 ∨ n = 21 ∨ n = 36)), ?_, fun sf => ?_⟩
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenCreatCloexecExecSpec, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2 hs_x3
      have hexec := execOpenat_wronly_creat_trunc_cloexec hs_x0 (hfl_eq ▸ hs_x2)
        (hs_x3.symm ▸ hmode) hcs hlead hdot (hs_fs.symm ▸ halloc)
      rw [hs_fs, hcan] at hexec; simp only [Bool.false_eq_true, ↓reduceIte] at hexec
      rcases hexec with ⟨err, herr, hexec_eq⟩
      rcases herr with rfl | rfl | rfl | rfl
      · exact ⟨2, by decide, by decide, Or.inl rfl, hexec_eq⟩
      · exact ⟨20, by decide, by decide, Or.inr (Or.inl rfl), hexec_eq⟩
      · exact ⟨21, by decide, by decide, Or.inr (Or.inr (Or.inl rfl)), hexec_eq⟩
      · exact ⟨36, by decide, by decide, Or.inr (Or.inr (Or.inr rfl)), hexec_eq⟩
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenCreatCloexecExecSpec,
        muslOpenNoCreatCloexecExecSpec, muslOpenCreateTruncSpec, hcan, Bool.false_eq_true, ↓reduceIte]
      refine Entails.sepExists_elim fun errno => Entails.sepExists_right (BitVec.ofNat 32 errno) ?_
      exact sepConj_mono_left (Entails.pure_mono fun ⟨_, _, hpred, hr0, hfs, htr, hsp⟩ =>
        ⟨hr0, by
          rcases hpred with rfl | rfl | rfl | rfl <;> decide, hfs, htr, hsp⟩)

theorem muslOpenCreateTrunc_ok [MuslSysPlacement] {P : Program} (fd : BitVec 64 := 3#64)
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "open")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl (muslOpenCreateTruncSpec fd)) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 8) (by decide) (muslOpenCreateTrunc_block_ok fd) hext hsvc

end VerifiedLibraries.Musl
