/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.SliceArray
public import ProofLib.StdStartup.StackInit
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
public meta import ProofLib.LiteralFetchLint
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics

/-!
# musl Stage-1 Startup and `envp`/`auxv` Scan Contracts

Symbolic `SepWP` contracts for `_start`, `_start_c`, `__libc_start_main`, `dummy1`, and the
`__init_libc` `envp`, `auxv`, and `__progname` scan loops.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib.StdStartup

open Arm64 Arm64.Process ProofLib

/-! ## Parametric Instruction Lists for Stage-1 Startup -/

/-- `dummy1` weak stub (`ret`, 1 instruction). -/
def dummy1Words : List (BitVec 32) := [0xd65f03c0#32]

/-- `_start` entrypoint (`7` instructions at `L.startAddr`). -/
def startInstrs (L : StdBinaryLayout) : List Instr :=
  [ .moveWide .W64 .MOVZ .x29 0#16 0, .moveWide .W64 .MOVZ .lr 0#16 0,
    .addSubImm .W64 .ADD .x0 .sp 0#12 false, .adr true .x1 (adrpOff (L.startAddr + 0x0c#64) 0#64),
    .addSubImm .W64 .ADD .x1 .x1 0#12 false, .logicalImm .W64 .AND .sp .x0 0xfffffffffffffff0#64,
    .b (L.startCAddr - (L.startAddr + 0x18#64)) ]

/-- `_start_c` (`10` instructions at `L.startCAddr`). -/
def startCInstrs (L : StdBinaryLayout) : List Instr :=
  [ .logicalShift .W64 .ORR .x2 .xzr .x0 .LSL 0, .adr true .x4 (adrpOff (L.startCAddr + 0x04#64) (L.gotAddr + 0x08#64)),
    .adr true .x3 (adrpOff (L.startCAddr + 0x08#64) (L.gotAddr + 0x10#64)), .adr true .x0 (adrpOff (L.startCAddr + 0x0c#64) (L.gotAddr + 0x18#64)),
    .ldr .W64 .X64 false .x4 (.Offset .x4 (pageLo12 (L.gotAddr + 0x08#64))), .moveWide .W64 .MOVZ .x5 0#16 0,
    .ldr .W64 .X64 false .x3 (.Offset .x3 (pageLo12 (L.gotAddr + 0x10#64))), .ldr .W64 .X64 false .x0 (.Offset .x0 (pageLo12 (L.gotAddr + 0x18#64))),
    .ldr .W64 .X64 false .x1 (.PostIndex .x2 8#64), .b (L.libcStartMainAddr - (L.startCAddr + 0x24#64)) ]

/-- `__libc_start_main` (`21` instructions at `L.libcStartMainAddr`). -/
def libcStartMainInstrs (L : StdBinaryLayout) : List Instr :=
  [ .stp .W64 .x29 .lr (.PreIndex .sp (-0x30#64)), .addSubImm .W64 .ADD .x29 .sp 0#12 false,
    .stp .W64 .x19 .x20 (.Offset .sp 0x10#64), .logicalShift .W64 .ORR .x19 .xzr .x2 .LSL 0,
    .logicalShift .W32 .ORR .x20 .xzr .x1 .LSL 0, .str .X64 .x21 (.Offset .sp 0x20#64),
    .addSubExt .W64 .ADD .x2 .x2 .x1 .SXTW 3, .logicalShift .W64 .ORR .x21 .xzr .x0 .LSL 0,
    .addSubImm .W64 .ADD .x0 .x2 8#12 false, .ldr .W64 .X64 false .x1 (.Offset .x19 0#64),
    .bl (L.initLibcAddr - (L.libcStartMainAddr + 0x28#64)), .logicalShift .W64 .ORR .x2 .xzr .x19 .LSL 0,
    .logicalShift .W32 .ORR .x1 .xzr .x20 .LSL 0, .logicalShift .W64 .ORR .x0 .xzr .x21 .LSL 0,
    .adr true .x3 (adrpOff (L.libcStartMainAddr + 0x38#64) L.libcStartMainStage2Addr), .addSubImm .W64 .ADD .x3 .x3 (L.libcStartMainStage2Addr.truncate 12) false,
    .ldp .W64 false .x19 .x20 (.Offset .sp 0x10#64), .logicalShift .W64 .ORR .x16 .xzr .x3 .LSL 0,
    .ldr .W64 .X64 false .x21 (.Offset .sp 0x20#64), .ldp .W64 false .x29 .lr (.PostIndex .sp 0x30#64), .br .x16 ]

/-- `__init_libc` (`118` instructions at `L.initLibcAddr`). -/
def initLibcInstrs (L : StdBinaryLayout) : List Instr :=
  [ .stp .W64 .x29 .lr (.PreIndex .sp (-0x190#64)), .moveWide .W64 .MOVZ .x2 0x130#16 0,
    .addSubImm .W64 .ADD .x4 .sp 0x60#12 false, .addSubImm .W64 .ADD .x29 .sp 0#12 false,
    .stp .W64 .x19 .x20 (.Offset .sp 0x10#64), .logicalShift .W64 .ORR .x19 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x20 .xzr .x1 .LSL 0, .logicalShift .W64 .ORR .x0 .xzr .x4 .LSL 0,
    .moveWide .W32 .MOVZ .x1 0#16 0, .str .X64 .x21 (.Offset .sp 0x20#64),
    .bl (L.memsetAddr - (L.initLibcAddr + 0x28#64)), .logicalShift .W64 .ORR .x4 .xzr .x0 .LSL 0,
    .adr true .x0 (adrpOff (L.initLibcAddr + 0x30#64) (L.gotAddr + 0x38#64)), .moveWide .W64 .MOVZ .x2 0#16 0,
    .ldr .W64 .X64 false .x0 (.Offset .x0 (pageLo12 (L.gotAddr + 0x38#64))), .str .X64 .x19 (.Offset .x0 0#64),
    .ldr .W64 .X64 false .x3 (.RegOffset .x19 .x2 .UXTX 3), .addSubImm .W64 .ADD .x2 .x2 1#12 false,
    .cbz .W64 true .x3 (-0x08#64), .adr true .x21 (adrpOff (L.initLibcAddr + 0x4c#64) L.libcAddr),
    .addSubImm .W64 .ADD .x1 .x21 (L.libcAddr.truncate 12) false, .addSubShift .W64 .ADD .x2 .x19 .x2 .LSL 3,
    .logicalShift .W64 .ORR .x0 .xzr .x2 .LSL 0, .str .X64 .x2 (.Offset .x1 8#64),
    .b 8#64, .addSubImm .W64 .ADD .x0 .x0 0x10#12 false,
    .ldr .W64 .X64 false .x19 (.Offset .x0 0#64), .cbz .W64 false .x19 0x18#64,
    .addSubImm .W64 .SUBS .xzr .x19 0x25#12 false, .bCond .HI (-0x10#64),
    .ldr .W64 .X64 false .x1 (.Offset .x0 8#64), .str .X64 .x1 (.RegOffset .x4 .x19 .UXTX 3),
    .b (-0x1c#64), .adr true .x1 (adrpOff (L.initLibcAddr + 0x84#64) L.hwcapAddr),
    .ldr .W64 .X64 false .x0 (.Offset .sp 0x160#64), .ldr .W64 .X64 false .x2 (.Offset .sp 0xe0#64),
    .str .X64 .x2 (.Offset .x1 (pageLo12 L.hwcapAddr)), .cbz .W64 false .x0 0x0c#64,
    .adr true .x1 (adrpOff (L.initLibcAddr + 0x98#64) L.sysinfoAddr), .str .X64 .x0 (.Offset .x1 (pageLo12 L.sysinfoAddr)),
    .addSubImm .W64 .ADD .x0 .x21 (L.libcAddr.truncate 12) false, .ldr .W64 .X64 false .x1 (.Offset .sp 0x90#64),
    .str .X64 .x1 (.Offset .x0 0x30#64), .cbz .W64 false .x20 0x28#64,
    .adr true .x2 (adrpOff (L.initLibcAddr + 0xb0#64) (L.gotAddr + 0x40#64)), .adr true .x1 (adrpOff (L.initLibcAddr + 0xb4#64) (L.gotAddr + 0x48#64)),
    .addSubImm .W64 .ADD .x0 .x20 1#12 false, .ldr .W64 .X64 false .x2 (.Offset .x2 (pageLo12 (L.gotAddr + 0x40#64))),
    .ldr .W64 .X64 false .x1 (.Offset .x1 (pageLo12 (L.gotAddr + 0x48#64))), .str .X64 .x20 (.Offset .x2 0#64),
    .logicalShift .W64 .ORR .x2 .xzr .x1 .LSL 0, .str .X64 .x20 (.Offset .x1 0#64),
    .b 0x1c#64, .ldr .W64 .X64 false .x20 (.Offset .sp 0x158#64),
    .cbz .W64 true .x20 (-0x28#64), .adr true .x20 (adrpOff (L.initLibcAddr + 0xdc#64) L.emptyCStrAddr),
    .addSubImm .W64 .ADD .x20 .x20 (L.emptyCStrAddr.truncate 12) false, .b (-0x34#64),
    .addSubImm .W64 .ADD .x0 .x0 1#12 false, .ldr .W32 .B8 false .x1 (.UnscaledOffset .x0 (-1#64)),
    .cbz .W32 false .x1 0x14#64, .addSubImm .W32 .SUBS .xzr .x1 0x2f#12 false,
    .bCond .NE (-0x10#64), .str .X64 .x0 (.Offset .x2 0#64),
    .b (-0x18#64), .logicalShift .W64 .ORR .x0 .xzr .x4 .LSL 0,
    .bl (L.staticInitTlsAddr - (L.initLibcAddr + 0x108#64)), .ldr .W64 .X64 false .x0 (.Offset .sp 0x128#64),
    .bl (L.dummy1Addr - (L.initLibcAddr + 0x110#64)), .ldp .W64 false .x1 .x0 (.Offset .sp 0xb8#64),
    .addSubShift .W64 .SUBS .xzr .x1 .x0 .LSL 0, .bCond .EQ 0x50#64,
    .addSubImm .W64 .ADD .x5 .sp 0x48#12 false, .stp .W64 .xzr .xzr (.Offset .sp 0x48#64),
    .moveWide .W32 .MOVZ .x7 1#16 0, .str .X64 .xzr (.Offset .sp 0x58#64),
    .moveWide .W32 .MOVZ .x6 2#16 0, .logicalShift .W64 .ORR .x0 .xzr .x5 .LSL 0,
    .addSubImm .W64 .ADD .x2 .sp 0x38#12 false, .moveWide .W64 .MOVZ .x8 0x49#16 0,
    .moveWide .W64 .MOVZ .x1 3#16 0, .moveWide .W64 .MOVZ .x3 0#16 0,
    .moveWide .W64 .MOVZ .x4 8#16 0, .stp .W64 .xzr .xzr (.Offset .sp 0x38#64),
    .str .W32 .x7 (.Offset .sp 0x50#64), .str .W32 .x6 (.Offset .sp 0x58#64),
    .system false 0#16, .adr true .x1 (adrpOff (L.initLibcAddr + 0x15c#64) L.devNullLibcAddr),
    .addSubImm .W64 .ADD .x1 .x1 (L.devNullLibcAddr.truncate 12) false, .tbz .W32 false .x0 31 0x2c#64,
    .b 0x48#64, .ldp .W64 false .x1 .x0 (.Offset .sp 0xc8#64),
    .addSubShift .W64 .SUBS .xzr .x1 .x0 .LSL 0, .bCond .NE (-0x54#64),
    .ldr .W64 .X64 false .x0 (.Offset .sp 0x118#64), .cbz .W64 true .x0 (-0x5c#64),
    .b 0x48#64, .addSubImm .W64 .ADD .x19 .x19 8#12 false,
    .addSubImm .W64 .SUBS .xzr .x19 0x18#12 false, .bCond .EQ 0x30#64,
    .addSubShift .W64 .ADD .x0 .x5 .x19 .LSL 0, .ldr .W32 .H16 false .x0 (.Offset .x0 6#64),
    .tbz .W32 false .x0 5 (-0x14#64), .moveWide .W64 .MOVZ .x8 0x38#16 0,
    .moveWide .W64 .MOVN .x0 0x63#16 0, .logicalImm .W32 .ORR .x2 .xzr 0x0002000200020002#64,
    .system false 0#16, .tbz .W64 false .x0 63 (-0x28#64),
    .moveWide .W64 .MOVZ .x0 0#16 0, .str .B8 .xzr (.Offset .x0 0#64),
    .system true 0x3e8#16, .addSubImm .W64 .ADD .x21 .x21 (L.libcAddr.truncate 12) false,
    .moveWide .W32 .MOVZ .x0 1#16 0, .str .B8 .x0 (.Offset .x21 2#64),
    .ldp .W64 false .x19 .x20 (.Offset .sp 0x10#64), .ldr .W64 .X64 false .x21 (.Offset .sp 0x20#64),
    .ldp .W64 false .x29 .lr (.PostIndex .sp 0x190#64), .ret .lr ]

/-- Pure pointer scan matching musl's `__progname` `'/'` search over `argv[0]`. -/
def scanSlashPtr (cur best : BitVec 64) : List (BitVec 8) → BitVec 64
  | [] => best
  | b :: rest => scanSlashPtr (cur + 1#64) (if b == 0x2f#8 then cur + 1#64 else best) rest

/-- Mutable globals owned and initialized by `musl` stage-1 (`__init_libc`). -/
def Stage1GlobalsPre (L : StdBinaryLayout) : SepProp :=
  ((L.libcAddr + 0x08#64) ↦₆₄ 0#64) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 0#64) ∗
  (L.sysinfoAddr ↦₆₄ 0#64) ∗ (L.hwcapAddr ↦₆₄ 0#64) ∗
  (L.environAddr ↦₆₄ 0#64) ∗ (L.prognameFullAddr ↦₆₄ 0#64) ∗ (L.prognameAddr ↦₆₄ 0#64)

/-- Post-stage-1 state of the mutable globals initialized by `__init_libc`. -/
def Stage1GlobalsPost (L : StdBinaryLayout) (inputs : ProcessInputs) (sl : StackLayout) : SepProp :=
  let argv0Addr := sl.argvAddrs.getD 0 0#64
  let argv0Bytes := inputs.argv.getD 0 []
  ((L.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
  (L.sysinfoAddr ↦₆₄ (auxvScan38 sl.auxvEntries).getD 32 0#64) ∗
  (L.hwcapAddr ↦₆₄ inputs.init.auxv.hwcap) ∗ (L.environAddr ↦₆₄ sl.envpTableAddr) ∗
  (L.prognameFullAddr ↦₆₄ argv0Addr) ∗
  (L.prognameAddr ↦₆₄ scanSlashPtr argv0Addr argv0Addr argv0Bytes)

/-! ## Arithmetic, Fetch, and Memory-Slice Helpers -/

set_option linter.literalFetch false in
theorem fetch_dummy1 {P : Program} {addr : BitVec 64} (h : P.hasWords addr dummy1Words) :
    P.fetch addr = some (.ret .lr) := by
  rcases h with ⟨_, hrd, hhf⟩
  have h0 := hrd 0 (by decide)
  have hext : P.externAt? addr = none :=
    P.hookAtOff?_eq_none_of_hookFree hhf (Nat.le_refl _) (Nat.lt_add_of_pos_right (by decide))
  simp only [Program.fetch, hext, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rw [Nat.add_zero] at h0; rw [h0]; rfl

namespace Stage1Internal

theorem pc_ne_of_fetch_ne {P : Program} {p1 p2 : BitVec 64} {i1 i2 : Instr}
    (h1 : P.fetch p1 = some i1) (h2 : P.fetch p2 = some i2)
    (hne : i1 ≠ i2 := by first | nofun | decide) :
    p1 ≠ p2 := by
  intro heq; subst heq; rw [h1] at h2; exact hne (Option.some.inj h2)

theorem add_sub_pc (a b : BitVec 64) : a + (b - a) = b := by bv_lin

theorem align16_and_15 {x : BitVec 64} (h : x.toNat % 16 = 0) :
    x &&& 15#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have : 15 = 2 ^ 4 - 1 := rfl
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [this, Nat.and_two_pow_sub_one_eq_mod, h]

theorem fetch_at {P : Program} {base : BitVec 64} {ls : List Instr} {inst : Instr}
    (i : Nat) (off : BitVec 64) (h : hasInstrs P base ls)
    (hi : ls[i]? = some inst := by rfl)
    (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) :
    P.fetch (base + off) = some inst := by
  have hlt : i < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have hf := h.fetch_off i off hlt hoff
  rw [List.getElem?_eq_getElem hlt] at hi; cases hi; exact hf

theorem fetch_at0 {P : Program} {base : BitVec 64} {ls : List Instr} {inst : Instr}
    (h : hasInstrs P base ls) (hi : ls[0]? = some inst := by rfl) :
    P.fetch base = some inst := by
  simpa using fetch_at 0 0#64 h hi rfl

def projSB (s : State) := (s.sigActions, s.brk, s.brkStart, s.physMemAvail)
theorem projSB_pc (s : State) (p : BitVec 64) : projSB (s.setPC p) = projSB s := by cases s; rfl
theorem projSB_mem (s : State) (m : Memory) : projSB (s.setMem m) = projSB s := by cases s; rfl
theorem projSB_ps (s : State) (p : PState) : projSB (s.setPState p) = projSB s := by cases s; rfl
theorem projSB_w64 (s : State) (r : Reg) (v : BitVec 64) : projSB (s.writeReg64 r v) = projSB s := by
  cases s; cases r <;> rfl
theorem projSB_w32 (s : State) (r : Reg) (v : BitVec 32) : projSB (s.writeReg32 r v) = projSB s :=
  projSB_w64 s r _
theorem mk_stdPres {s0 sf : State}
    (hfs : sf.fs = s0.fs) (htr : sf.trace = s0.trace) (htp : sf.tpidrEl0 = s0.tpidrEl0)
    (hsb : projSB sf = projSB s0) (hp : ∀ a, sf.mem.perm a = s0.mem.perm a) :
    StdStatePreserved s0 sf :=
  ⟨hfs, htr, htp, (Prod.mk.inj hsb).1, (Prod.mk.inj (Prod.mk.inj hsb).2).1,
   (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hsb).2).2).1,
   (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hsb).2).2).2, hp⟩

theorem step_str64_perm {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 64}
    (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
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
  have hcan : s.mem.canWrite ea _ = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .X64 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write64 s.mem ea val)) hm'

end Stage1Internal

open Stage1Internal

theorem align16_and15 {x : BitVec 64} (h : x.toNat % 16 = 0) :
    x &&& 15#64 = 0#64 :=
  align16_and_15 h

theorem align16_and_mask {x : BitVec 64} (h : x.toNat % 16 = 0) :
    x &&& 0xfffffffffffffff0#64 = x := by
  have hb := align16_and_15 h; bv_bits

private theorem spAligned_sub16 {x off : BitVec 64} (h : x.toNat % 16 = 0)
    (hoff : off &&& 15#64 = 0#64 := by rfl) :
    ((x - off) &&& 15#64 == 0#64) = true := by
  have hb := align16_and_15 h
  rw [beq_iff_eq]; bv_bits

theorem sxtw3_argc_eq {n : Nat} (hn : n < 2 ^ 31) :
    ((BitVec.ofNat 64 n).truncate 32).signExtend 64 <<< 3 = BitVec.ofNat 64 (8 * n) := by
  have htrunc : (BitVec.ofNat 64 n).truncate 32 = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
  have hmsb : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]; omega
  rw [htrunc, BitVec.signExtend_eq_setWidth_of_msb_false hmsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 8 * n < 2 ^ 64), Nat.shiftLeft_eq]
  omega

theorem ze32_argc_eq {n : Nat} (hn : n < 2 ^ 31) :
    ((BitVec.ofNat 64 n).truncate 32).zeroExtend 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]

theorem envpTableAddr_calc (sp0 : BitVec 64) (argc : Nat) :
    sp0 + 8#64 + BitVec.ofNat 64 (8 * argc) + 8#64 =
      sp0 + BitVec.ofNat 64 (8 * (argc + 2)) := by
  have : BitVec.ofNat 64 (8 * (argc + 2)) = 8#64 + BitVec.ofNat 64 (8 * argc) + 8#64 := by
    rw [show 8 * (argc + 2) = 8 + 8 * argc + 8 by omega, BitVec.ofNat_add, BitVec.ofNat_add]
  rw [this]; bv_lin

theorem auxvTableAddr_calc (sp0 : BitVec 64) (argc envc : Nat) :
    sp0 + BitVec.ofNat 64 (8 * (argc + 2)) + BitVec.ofNat 64 (8 * (envc + 1)) =
      sp0 + BitVec.ofNat 64 (8 * (argc + envc + 3)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

private theorem step_stp64_perm {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
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
  exact SepWP.to_reaches_pc (hnext m2 (funext fun a => by rw [Memory.perm_write64, Memory.perm_write64])) hm2

local macro "wp_str64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm $hf
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_sep_access
  · wp_focus_close wp_norm_lhs
  intro $m $hm
  try wp_norm_state))

local macro "wp_stp64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stp64_perm $hf
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_sep_access
  · wp_focus_close wp_sep_access
  · wp_focus_close wp_norm_lhs
  intro $m $hm
  try wp_norm_state))

/-- Stack slots saved by `__libc_start_main` at `[sp0 - 0x30, sp0)`. -/
def LsmSavedFrame (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 0x30#64) ↦₆₄ 0#64) ∗ ((sp0 - 0x28#64) ↦₆₄ 0#64) ∗
  ((sp0 - 0x20#64) ↦₆₄ s0.readReg64 .x19) ∗ ((sp0 - 0x18#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 0x10#64) ↦₆₄ s0.readReg64 .x21) ∗ memRegion (sp0 - 0x08#64) 8

/-! ## `_start` to `bl __init_libc` -/

theorem start_to_initLibc_call {P : Program} {L : StdBinaryLayout}
    {inputs : ProcessInputs} {sl : StackLayout} {s0 : State} {F : SepProp}
    (hc_start : hasInstrs P L.startAddr (startInstrs L))
    (hc_startC : hasInstrs P L.startCAddr (startCInstrs L))
    (hc_lsm : hasInstrs P L.libcStartMainAddr (libcStartMainInstrs L))
    (hc_init : hasInstrs P L.initLibcAddr (initLibcInstrs L))
    (hsp0 : s0.sp = sl.sp0) (hpc0 : s0.pc = L.startAddr) (hrun0 : s0.status = .Running)
    (hal16 : sl.sp0.toNat % 16 = 0)
    (hargc_lo : 1 ≤ inputs.argv.length) (hargc_hi : inputs.argv.length < 2 ^ 31)
    (hargv_len : sl.argvAddrs.length = inputs.argv.length)
    (henvp_eq : sl.envpTableAddr = sl.sp0 + BitVec.ofNat 64 (8 * (inputs.argv.length + 2)))
    (hargv_eq : sl.argvTableAddr = sl.sp0 + 8#64) :
    SepWP P L.initLibcAddr s0
      (((sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
        (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
        StdGotGlobals L ∗ memRegion (sl.sp0 - 0x30#64) 0x30) ∗ F)
      (fun s1 Q =>
        s1.pc = L.initLibcAddr ∧ s1.status = .Running ∧
        s1.sp = sl.sp0 - 0x30#64 ∧
        s1.readReg64 .lr = L.libcStartMainAddr + 0x2c#64 ∧
        s1.readReg64 .x0 = sl.envpTableAddr ∧
        s1.readReg64 .x1 = sl.argvAddrs.getD 0 0#64 ∧
        s1.readReg64 .x19 = sl.argvTableAddr ∧
        s1.readReg32 .x20 = BitVec.ofNat 32 inputs.argv.length ∧
        s1.readReg64 .x21 = L.cMainAddr ∧
        s1.readReg64 .x29 = sl.sp0 - 0x30#64 ∧
        StdStatePreserved s0 s1 ∧
        Q = (((sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
              (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
              StdGotGlobals L ∗ LsmSavedFrame sl.sp0 s0) ∗ F)) := by
  have hs0 := fetch_at0 hc_start; have hs1 := fetch_at 1 0x04#64 hc_start; have hs2 := fetch_at 2 0x08#64 hc_start
  have hs3 := fetch_at 3 0x0c#64 hc_start; have hs4 := fetch_at 4 0x10#64 hc_start; have hs5 := fetch_at 5 0x14#64 hc_start
  have hs6 := fetch_at 6 0x18#64 hc_start; have hc0 := fetch_at0 hc_startC; have hc1 := fetch_at 1 0x04#64 hc_startC
  have hc2 := fetch_at 2 0x08#64 hc_startC; have hc3 := fetch_at 3 0x0c#64 hc_startC; have hc4 := fetch_at 4 0x10#64 hc_startC
  have hc5 := fetch_at 5 0x14#64 hc_startC; have hc6 := fetch_at 6 0x18#64 hc_startC; have hc7 := fetch_at 7 0x1c#64 hc_startC
  have hc8 := fetch_at 8 0x20#64 hc_startC; have hc9 := fetch_at 9 0x24#64 hc_startC; have hl0 := fetch_at0 hc_lsm
  have hl1 := fetch_at 1 0x04#64 hc_lsm; have hl2 := fetch_at 2 0x08#64 hc_lsm; have hl3 := fetch_at 3 0x0c#64 hc_lsm
  have hl4 := fetch_at 4 0x10#64 hc_lsm; have hl5 := fetch_at 5 0x14#64 hc_lsm; have hl6 := fetch_at 6 0x18#64 hc_lsm
  have hl7 := fetch_at 7 0x1c#64 hc_lsm; have hl8 := fetch_at 8 0x20#64 hc_lsm; have hl9 := fetch_at 9 0x24#64 hc_lsm
  have hl10 := fetch_at 10 0x28#64 hc_lsm
  have hsp_al0 : s0.spAligned = true := by simp only [State.spAligned, hsp0, beq_iff_eq]; exact align16_and_15 hal16
  have hsp_al_lsm : ((sl.sp0 - 0x30#64) &&& 15#64 == 0#64) = true := spAligned_sub16 hal16
  apply SepWP.cut (mid := L.startAddr + 0x18#64)
  wp_steps 6
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun0]) ?_
  apply SepWP.cut (mid := L.startCAddr)
  have hne_s_c : L.startAddr + 0x18#64 ≠ L.startCAddr := pc_ne_of_fetch_ne hs6 hc0
  wp_step; rw [add_sub_pc]
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun0]) ?_
  apply SepWP.cut (mid := L.startCAddr + 0x24#64)
  conv => arg 4; dsimp only [StdGotGlobals, StdBinaryLayout.gotAtoms, rwAtomListSep, RwAtom.toSepProp]
  have hmask : sl.sp0 &&& 0xfffffffffffffff0#64 = sl.sp0 := align16_and_mask hal16
  wp_steps 9
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun0]) ?_
  change SepWP P L.initLibcAddr _ (((sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
    (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗ StdGotGlobals L ∗ memRegion (sl.sp0 - 0x30#64) 0x30) ∗ F) _ _
  apply SepWP.cut (mid := L.libcStartMainAddr)
  have hne_c_l : L.startCAddr + 0x24#64 ≠ L.libcStartMainAddr := pc_ne_of_fetch_ne hc9 hl0
  wp_step; rw [add_sub_pc]
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun0]) ?_
  obtain ⟨argv0, argvRest, ha_cons⟩ : ∃ a as, sl.argvAddrs = a :: as := by
    cases h : sl.argvAddrs with | nil => simp [h] at hargv_len; omega | cons a as => exact ⟨a, as, rfl⟩
  rw [memRegion_uncons (sl.sp0 - 0x30#64) (by decide) (by decide), show (0x30 - 8 : Nat) = 40 from rfl, show sl.sp0 - 0x30#64 + 8#64 = sl.sp0 - 0x28#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x28#64) (by decide) (by decide), show (40 - 8 : Nat) = 32 from rfl, show sl.sp0 - 0x28#64 + 8#64 = sl.sp0 - 0x20#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x20#64) (by decide) (by decide), show (32 - 8 : Nat) = 24 from rfl, show sl.sp0 - 0x20#64 + 8#64 = sl.sp0 - 0x18#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x18#64) (by decide) (by decide), show (24 - 8 : Nat) = 16 from rfl, show sl.sp0 - 0x18#64 + 8#64 = sl.sp0 - 0x10#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x10#64) (by decide) (by decide), show (16 - 8 : Nat) = 8 from rfl, show sl.sp0 - 0x10#64 + 8#64 = sl.sp0 - 0x08#64 by bv_lin]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro w0; apply SepWP.exists_left; intro w1; apply SepWP.exists_left; intro w2
  apply SepWP.exists_left; intro w3; apply SepWP.exists_left; intro w4
  rw [ha_cons, List.cons_append, pointsToWords64RO_cons, hargv_eq]
  apply SepWP.cut (mid := L.libcStartMainAddr + 0x28#64)
  wp_stp64 hl0 m1 hm1; wp_step; wp_stp64 hl2 m2 hm2; wp_steps 2; wp_str64 hl5 m3 hm3; wp_steps 4
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun0]) ?_
  have hne_l_i : L.libcStartMainAddr + 0x28#64 ≠ L.initLibcAddr := pc_ne_of_fetch_ne hl10 (fetch_at0 hc_init)
  wp_step; rw [add_sub_pc]
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun0]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun0],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm, sxtw3_argc_eq hargc_hi, henvp_eq, envpTableAddr_calc],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm]; rfl,
    by simp (config := { decide := true }) only [wp_norm, arm64_norm],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm]; apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt (by omega : inputs.argv.length < 2 ^ 32)],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm],
    mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_mem, projSB_w64])
      (fun a => by simp only [wp_norm, arm64_norm, hm3, hm2, hm1]),
    by dsimp only [LsmSavedFrame]⟩

/-! ## `__init_libc` Prologue, `memset`, and `envp` Scan (`+0x00..+0x60`) -/

private theorem ofNat_shl3 {k : Nat} (hk : 8 * k < 2 ^ 64) :
    (BitVec.ofNat 64 k) <<< 3 = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt hk]; omega

private theorem replicate_zero_eq_unpackL : ∀ n : Nat,
    List.replicate (8 * n) 0#8 = unpackL (List.replicate n 0#64)
  | 0 => rfl
  | n + 1 => by
    rw [Nat.mul_succ, Nat.add_comm, List.replicate_add, replicate_zero_eq_unpackL n]; rfl

/-- Callee-saved slots + 56-byte local scratch at `[sp0 - 0x1c0, sp0 - 0x160)` in `__init_libc`. -/
def InitSavedFrame (sp0 : BitVec 64) (s1 : State) : SepProp :=
  ((sp0 - 0x1c0#64) ↦₆₄ s1.readReg64 .x29) ∗ ((sp0 - 0x1b8#64) ↦₆₄ s1.readReg64 .lr) ∗
  ((sp0 - 0x1b0#64) ↦₆₄ s1.readReg64 .x19) ∗ ((sp0 - 0x1a8#64) ↦₆₄ s1.readReg64 .x20) ∗
  ((sp0 - 0x1a0#64) ↦₆₄ s1.readReg64 .x21) ∗ memRegion (sp0 - 0x198#64) 0x38

private theorem envp_scan_loop {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.initLibcAddr (initLibcInstrs L))
    (rem : List (BitVec 64)) (base : BitVec 64) (k : Nat) {s : State} (F : SepProp)
    (hno0 : ∀ p ∈ rem, p ≠ 0#64) (hbnd : 8 * (k + rem.length + 1) < 2 ^ 64)
    (hpc : s.pc = L.initLibcAddr + 0x40#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = base) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 k) :
    SepWP P (L.initLibcAddr + 0x4c#64) s
      (((base + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ* (rem ++ [0#64])) ∗ F)
      (fun sf Q =>
        sf.pc = L.initLibcAddr + 0x4c#64 ∧ sf.status = .Running ∧
        sf.sp = s.sp ∧ sf.mem = s.mem ∧
        sf.readReg64 .x2 = BitVec.ofNat 64 (k + rem.length + 1) ∧
        sf.readReg64 .x4 = s.readReg64 .x4 ∧
        sf.readReg64 .x19 = base ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .lr = s.readReg64 .lr ∧
        StdStatePreserved s sf ∧
        Q = (((base + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ* (rem ++ [0#64])) ∗ F)) := by
  have hi16 := fetch_at 16 0x40#64 hc; have hi17 := fetch_at 17 0x44#64 hc
  have hi18 := fetch_at 18 0x48#64 hc
  induction rem generalizing k s F with
  | nil =>
    have hsh := ofNat_shl3 (k := k) (by simp at hbnd; omega)
    rw [List.nil_append, pointsToWords64RO_cons, pointsToWords64RO_nil]
    wp_steps 3
    refine SepWP.done (by simp (config := { decide := true }) only [arm64_norm])
      (by simp only [arm64_norm, hrun]) ?_
    have hk1 : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 0 + 1) := by
      rw [Nat.add_zero, BitVec.ofNat_add]
    refine ⟨by simp (config := { decide := true }) only [arm64_norm],
      by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [List.length_nil, arm64_norm, hk1], by simp only [arm64_norm],
      by simp only [arm64_norm, hx19], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm],
      mk_stdPres (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [projSB_pc, projSB_w64]) (fun _ => rfl), ?_⟩
    rw [← pointsToWords64RO_nil (base + BitVec.ofNat 64 (8 * k) + 8#64), ← pointsToWords64RO_cons]
  | cons p ps ih =>
    have hsh := ofNat_shl3 (k := k) (by simp at hbnd; omega)
    have hp0 : (p == 0#64) = false := beq_eq_false_iff_ne.mpr (hno0 p (List.mem_cons_self ..))
    have hnext_addr : base + BitVec.ofNat 64 (8 * k) + 8#64 = base + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * k + 8 = 8 * (k + 1) by omega]
    rw [List.cons_append, pointsToWords64RO_cons, hnext_addr, sepConj_assoc]
    apply SepWP.cut (mid := L.initLibcAddr + 0x48#64)
    wp_steps 2
    refine SepWP.done (by simp (config := { decide := true }) only [arm64_norm])
      (by simp only [arm64_norm, hrun]) ?_
    wp_step
    rw [← sepConj_assoc, sepConj_comm ((base + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ p), sepConj_assoc]
    have hk1 : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by rw [BitVec.ofNat_add]
    apply SepWP.mono
    case h =>
      refine ih (k + 1) _ (fun q hq => hno0 q (List.mem_cons_of_mem _ hq)) ?_ ?_ ?_ ?_ ?_
      · simp at hbnd ⊢; omega
      · simp only [arm64_norm]
      · simp only [arm64_norm, hrun]
      · simp only [arm64_norm, hx19]
      · simp only [arm64_norm, hk1]
    case hoom => exact fun _ _ _ ho => ho
    case himp =>
      rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hmem_f, hx2_f, hx4_f, hx19_f, hx20_f, hx29_f, hlr_f, hstd_f, rfl⟩
      have hpres : StdStatePreserved s sf := by
        refine StdStatePreserved.trans ?_ hstd_f
        exact mk_stdPres (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [projSB_pc, projSB_w64]) (fun _ => rfl)
      refine ⟨hpc_f, hrun_f, by simpa [arm64_norm] using hsp_f, by simpa [arm64_norm] using hmem_f,
        by simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hx2_f,
        by simpa [arm64_norm] using hx4_f, hx19_f, by simpa [arm64_norm] using hx20_f,
        by simpa [arm64_norm] using hx29_f, by simpa [arm64_norm] using hlr_f, hpres, ?_⟩
      ac_rfl

private theorem envp_scan0 {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.initLibcAddr (initLibcInstrs L))
    (rem : List (BitVec 64)) (base : BitVec 64) {s : State} (F : SepProp)
    (hno0 : ∀ p ∈ rem, p ≠ 0#64) (hbnd : 8 * (rem.length + 1) < 2 ^ 64)
    (hpc : s.pc = L.initLibcAddr + 0x40#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = base) (hx2 : s.readReg64 .x2 = 0#64) :
    SepWP P (L.initLibcAddr + 0x4c#64) s ((base ↦₆₄ᵣ* (rem ++ [0#64])) ∗ F)
      (fun sf Q => sf.pc = L.initLibcAddr + 0x4c#64 ∧ sf.status = .Running ∧
        sf.sp = s.sp ∧ sf.mem = s.mem ∧ sf.readReg64 .x2 = BitVec.ofNat 64 (rem.length + 1) ∧
        sf.readReg64 .x4 = s.readReg64 .x4 ∧ sf.readReg64 .x19 = base ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .lr = s.readReg64 .lr ∧ StdStatePreserved s sf ∧
        Q = ((base ↦₆₄ᵣ* (rem ++ [0#64])) ∗ F)) := by
  simpa using envp_scan_loop hc rem base 0 F hno0 (by simpa using hbnd) hpc hrun hx19 hx2

theorem initLibc_prologue_envp {P : Program} {L : StdBinaryLayout}
    {inputs : ProcessInputs} {sl : StackLayout} {s1 : State} {F : SepProp}
    (hc : hasInstrs P L.initLibcAddr (initLibcInstrs L))
    (ops : StdMemOps P L.memcpyAddr L.memsetAddr)
    (hpc1 : s1.pc = L.initLibcAddr) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = sl.sp0 - 0x30#64)
    (hx0 : s1.readReg64 .x0 = sl.envpTableAddr)
    (hx1 : s1.readReg64 .x1 = sl.argvAddrs.getD 0 0#64)
    (hal16 : sl.sp0.toNat % 16 = 0)
    (henvp_len : sl.envpAddrs.length = inputs.envp.length)
    (henvp_hi : inputs.envp.length < 2 ^ 31)
    (henvp_no0 : ∀ p ∈ sl.envpAddrs, p ≠ 0#64)
    (hauxv_eq : sl.auxvTableAddr = sl.envpTableAddr + BitVec.ofNat 64 (8 * (inputs.envp.length + 1)))
    (_hne_memset : L.initLibcAddr + 0x28#64 ≠ L.memsetAddr) :
    SepWP P (L.initLibcAddr + 0x68#64) s1
      ((memRegion (sl.sp0 - 0x1c0#64) 0x190 ∗ StdGotGlobals L ∗
        (L.environAddr ↦₆₄ 0#64) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ 0#64) ∗
        (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64]))) ∗ F)
      (fun s2 Q =>
        s2.pc = L.initLibcAddr + 0x68#64 ∧ s2.status = .Running ∧
        s2.sp = sl.sp0 - 0x1c0#64 ∧
        s2.readReg64 .x0 = sl.auxvTableAddr ∧
        s2.readReg64 .x4 = sl.sp0 - 0x160#64 ∧
        s2.readReg64 .x20 = sl.argvAddrs.getD 0 0#64 ∧
        s2.readReg64 .x21 = L.libcAddr &&& 0xfffffffffffff000#64 ∧
        s2.readReg64 .x29 = sl.sp0 - 0x1c0#64 ∧
        StdStatePreserved s1 s2 ∧
        Q = ((InitSavedFrame sl.sp0 s1 ∗ ((sl.sp0 - 0x160#64) ↦₆₄* List.replicate 38 0#64) ∗
              StdGotGlobals L ∗ (L.environAddr ↦₆₄ sl.envpTableAddr) ∗
              ((L.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
              (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64]))) ∗ F)) := by
  have hi0 := fetch_at0 hc; have hi1 := fetch_at 1 0x04#64 hc; have hi2 := fetch_at 2 0x08#64 hc
  have hi3 := fetch_at 3 0x0c#64 hc; have hi4 := fetch_at 4 0x10#64 hc; have hi5 := fetch_at 5 0x14#64 hc
  have hi6 := fetch_at 6 0x18#64 hc; have hi7 := fetch_at 7 0x1c#64 hc; have hi8 := fetch_at 8 0x20#64 hc
  have hi9 := fetch_at 9 0x24#64 hc; have hi10 := fetch_at 10 0x28#64 hc; have hi11 := fetch_at 11 0x2c#64 hc
  have hi12 := fetch_at 12 0x30#64 hc; have hi13 := fetch_at 13 0x34#64 hc; have hi14 := fetch_at 14 0x38#64 hc
  have hi15 := fetch_at 15 0x3c#64 hc; have hi19 := fetch_at 19 0x4c#64 hc; have hi20 := fetch_at 20 0x50#64 hc
  have hi21 := fetch_at 21 0x54#64 hc; have hi22 := fetch_at 22 0x58#64 hc; have hi23 := fetch_at 23 0x5c#64 hc
  have hi24 := fetch_at 24 0x60#64 hc
  have hsp0_al : (sl.sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr (align16_and_15 hal16)
  have hsp_sub : sl.sp0 - 0x30#64 + (-0x190#64 : BitVec 64) = sl.sp0 - 0x1c0#64 := by bv_lin
  rw [memRegion_split_le (sl.sp0 - 0x1c0#64) 0x60 0x190 (by decide) (by decide),
      show (0x190 - 0x60 : Nat) = 304 from rfl,
      show sl.sp0 - 0x1c0#64 + BitVec.ofNat 64 0x60 = sl.sp0 - 0x160#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x1c0#64) (by decide) (by decide), show (0x60 - 8 : Nat) = 88 from rfl, show sl.sp0 - 0x1c0#64 + 8#64 = sl.sp0 - 0x1b8#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x1b8#64) (by decide) (by decide), show (88 - 8 : Nat) = 80 from rfl, show sl.sp0 - 0x1b8#64 + 8#64 = sl.sp0 - 0x1b0#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x1b0#64) (by decide) (by decide), show (80 - 8 : Nat) = 72 from rfl, show sl.sp0 - 0x1b0#64 + 8#64 = sl.sp0 - 0x1a8#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x1a8#64) (by decide) (by decide), show (72 - 8 : Nat) = 64 from rfl, show sl.sp0 - 0x1a8#64 + 8#64 = sl.sp0 - 0x1a0#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x1a0#64) (by decide) (by decide), show (64 - 8 : Nat) = 0x38 from rfl, show sl.sp0 - 0x1a0#64 + 8#64 = sl.sp0 - 0x198#64 by bv_lin]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro u0; apply SepWP.exists_left; intro u1; apply SepWP.exists_left; intro u2
  apply SepWP.exists_left; intro u3; apply SepWP.exists_left; intro u4
  apply SepWP.cut (mid := L.initLibcAddr + 0x28#64)
  wp_stp64 hi0 m1 hm1; wp_steps 3; wp_stp64 hi4 m2 hm2; wp_steps 4; wp_str64 hi9 m3 hm3
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1]) ?_
  apply SepWP.cut (mid := L.memsetAddr)
  wp_step; rw [add_sub_pc]
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1]) ?_
  refine ops.call_memset (dst := sl.sp0 - 0x160#64) (byteVal := 0#8) (len := 304)
    (ret_pc := L.initLibcAddr + 0x2c#64) (F := ?F_ms) (by sep_frame) ?_
    (hsp_align := by simp only [State.spAligned, wp_norm, arm64_norm, hsp0_al])
    (hx1 := by simp only [wp_norm, arm64_norm])
  intro sm hpc_m hrun_m hsp_m hcs_m hx0_m hstd_m
  have hpres_m : StdStatePreserved s1 sm := by
    refine StdStatePreserved.trans ?_ hstd_m
    exact mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_mem, projSB_w64])
      (fun a => by simp only [wp_norm, arm64_norm, hm3, hm2, hm1])
  have hsp_m' : sm.sp = sl.sp0 - 0x1c0#64 := by simpa [wp_norm, arm64_norm, hsp_sub] using hsp_m
  have hx19_m : sm.readReg64 .x19 = sl.envpTableAddr := by
    have h := hcs_m.readReg64_x19; simpa [wp_norm, arm64_norm, hx0] using h
  have hx20_m : sm.readReg64 .x20 = sl.argvAddrs.getD 0 0#64 := by
    have h := hcs_m.readReg64_x20; simpa [wp_norm, arm64_norm, hx1] using h
  have hx29_m : sm.readReg64 .x29 = sl.sp0 - 0x1c0#64 := by
    have h := hcs_m.readReg64_x29; simpa [wp_norm, arm64_norm, hsp_sub] using h
  rw [show (304 : Nat) = 8 * 38 from rfl, replicate_zero_eq_unpackL 38, ← pointsToWords64_eq_pointsToBytes]
  apply SepWP.cut (mid := L.initLibcAddr + 0x40#64)
  conv => arg 4; dsimp only [StdGotGlobals, StdBinaryLayout.gotAtoms, rwAtomListSep, RwAtom.toSepProp]
  wp_steps 4; wp_str64 hi15 m4 hm4
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun_m]) ?_
  apply SepWP.cut (mid := L.initLibcAddr + 0x4c#64)
  refine SepWP.weaken_pre (P' := (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗ ?F_ev) (by sep_frame) ?_
  apply SepWP.mono
  case h =>
    refine envp_scan0 hc sl.envpAddrs sl.envpTableAddr ?F_ev henvp_no0 ?_ ?_ ?_ ?_ ?_
    · rw [henvp_len]; omega
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hrun_m]
    · simp only [wp_norm, arm64_norm, hx19_m]
    · simp only [wp_norm, arm64_norm]
  case hoom => exact fun _ _ _ ho => ho
  case himp =>
  rintro se Q hpc_e hrun_e ⟨_, _, hsp_e, hmem_e, hx2_e, hx4_e, hx19_e, hx20_e, hx29_e, _, hstd_e, rfl⟩
  have hpres_e : StdStatePreserved s1 se := by
    refine hpres_m.trans (StdStatePreserved.trans ?_ hstd_e)
    exact mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_mem, projSB_w64])
      (fun a => by simp only [wp_norm, arm64_norm, hm4])
  have hsh_ev := ofNat_shl3 (k := inputs.envp.length + 1) (by omega)
  have hx2_ev : se.readReg64 .x2 = BitVec.ofNat 64 (inputs.envp.length + 1) := by
    simpa [henvp_len] using hx2_e
  have hlibc_pg : (L.libcAddr &&& 0xfffffffffffff000#64) + (L.libcAddr.truncate 12).zeroExtend 64 = L.libcAddr :=
    page_add_trunc12_eq L.libcAddr
  apply SepWP.cut (mid := L.initLibcAddr + 0x60#64)
  wp_steps 4; wp_str64 hi23 m5 hm5
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun_e]) ?_
  wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun_e]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun_e],
    by simpa [wp_norm, arm64_norm, hsp_m'] using hsp_e,
    by simp (config := { decide := true }) only [wp_norm, arm64_norm, hauxv_eq],
    by simpa [wp_norm, arm64_norm, hx0_m] using hx4_e,
    by simpa [wp_norm, arm64_norm, hx20_m] using hx20_e,
    by simp (config := { decide := true }) only [wp_norm, arm64_norm],
    by simpa [wp_norm, arm64_norm, hx29_m] using hx29_e,
    hpres_e.trans (mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_mem, projSB_w64])
      (fun a => by simp only [wp_norm, arm64_norm, hm5])), ?_⟩
  rw [← hauxv_eq]
  dsimp only [InitSavedFrame, StdGotGlobals, StdBinaryLayout.gotAtoms, rwAtomListSep, RwAtom.toSepProp]
  ac_rfl

/-! ## Post-Index `envp`, `auxv`, and `__progname` Scan Loops (`zig cc` / `aarch64-linux-musl`) -/

/-- `zig cc` `musl` `envp` scan loop (`pc`: `ldr x8, [x20], #8`; `pc+4`: `cbnz x8, pc`):
    advances `x20` past a NUL-terminated pointer table `cur ↦₆₄ᵣ* (rem ++ [0#64])` to
    `cur + 8 * (rem.length + 1)`. -/
theorem zig_envp_scan_loop {prog : Program} {pc : BitVec 64}
    (hf0 : prog.fetch pc = some (.ldr .W64 .X64 false .x8 (.PostIndex .x20 8#64)))
    (hf1 : prog.fetch (pc + 4#64) = some (.cbz .W64 true .x8 (-4#64)))
    (rem : List (BitVec 64)) (cur : BitVec 64) {s : State} (F : SepProp)
    (hne : ∀ v ∈ rem, v ≠ 0#64)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = cur) :
    SepWP prog (pc + 8#64) s
      ((cur ↦₆₄ᵣ* (rem ++ [0#64])) ∗ F)
      (fun sf Q =>
        sf.pc = pc + 8#64 ∧ sf.status = .Running ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = cur + BitVec.ofNat 64 (8 * (rem.length + 1)) ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .lr = s.readReg64 .lr ∧
        Q = ((cur ↦₆₄ᵣ* (rem ++ [0#64])) ∗ F)) := by
  induction rem generalizing cur s F with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_add, Nat.mul_one]
    rw [pointsToWords64RO_cons, pointsToWords64RO_nil]
    wp_steps 2
    refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      rfl⟩
  | cons v vs ih =>
    have hv0 : (v == 0#64) = false := beq_eq_false_iff_ne.mpr (hne v (List.mem_cons_self ..))
    have hback : pc + 4#64 + (-4#64) = pc := by bv_omega
    conv => arg 4; simp only [List.cons_append]
    rw [pointsToWords64RO_cons]
    apply SepWP.cut (mid := pc)
    wp_steps 2
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine SepWP.weaken_pre (P' := ((cur + 8#64) ↦₆₄ᵣ* (vs ++ [0#64])) ∗ ((cur ↦₆₄ᵣ v) ∗ F))
      (by sep_frame) ?_
    apply SepWP.mono
    case h =>
      refine ih (cur + 8#64) ((cur ↦₆₄ᵣ v) ∗ F)
        (fun w hw => hne w (List.mem_cons_of_mem _ hw)) ?_ ?_ ?_
      · simp only [wp_norm, arm64_norm]
      · simp only [wp_norm, arm64_norm, hrun]
      · simp only [wp_norm, arm64_norm]
    case hoom => exact fun _ _ _ ho => ho
    case himp =>
      rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx19_f, hx20_f, hx21_f, hx29_f, hlr_f, rfl⟩
      have haddr : cur + 8#64 + BitVec.ofNat 64 (8 * (vs.length + 1)) =
          cur + BitVec.ofNat 64 (8 * ((v :: vs).length + 1)) := by
        simp only [List.length_cons]
        rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
          ← BitVec.ofNat_add]
        congr 2; omega
      refine ⟨hpc_f, hrun_f,
        by simpa [wp_norm, arm64_norm] using hsp_f,
        by simpa [wp_norm, arm64_norm] using hx19_f,
        hx20_f.trans haddr,
        by simpa [wp_norm, arm64_norm] using hx21_f,
        by simpa [wp_norm, arm64_norm] using hx29_f,
        by simpa [wp_norm, arm64_norm] using hlr_f,
        ?_⟩
      simp only [List.cons_append]
      rw [pointsToWords64RO_cons]; ac_rfl

/-- Inner loop of `zig cc` `musl` `auxv` scan starting at `pcL = pc₀ + 0x0c` (`cmp x8, #0x25;
    b.hi pcL+0x10; ldur x10, [x20, #-8]; str x10, [x9, x8, lsl #3]; ldr x8, [x20], #0x10;
    cbnz x8, pcL`). -/
theorem zig_auxv_scan_inner {prog : Program} {pcL : BitVec 64}
    (hf0 : prog.fetch pcL = some (.addSubImm .W64 .SUBS .xzr .x8 0x25#12 false))
    (hf1 : prog.fetch (pcL + 4#64) = some (.bCond .HI 0x0c#64))
    (hf2 : prog.fetch (pcL + 8#64) = some (.ldr .W64 .X64 false .x10 (.UnscaledOffset .x20 (-8#64))))
    (hf3 : prog.fetch (pcL + 0x0c#64) = some (.str .X64 .x10 (.RegOffset .x9 .x8 .UXTX 3)))
    (hf4 : prog.fetch (pcL + 0x10#64) = some (.ldr .W64 .X64 false .x8 (.PostIndex .x20 16#64)))
    (hf5 : prog.fetch (pcL + 0x14#64) = some (.cbz .W64 true .x8 (-0x14#64)))
    (t₀ v₀ : BitVec 64) (rest : List (BitVec 64 × BitVec 64))
    (cur auxPtr : BitVec 64) (acc : List (BitVec 64)) {s : State} (F : SepProp)
    (ht0 : t₀ ≠ 0#64) (hno0 : ∀ p ∈ rest, p.1 ≠ 0#64) (hlen : acc.length = 38)
    (hpc : s.pc = pcL) (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = t₀) (hx20 : s.readReg64 .x20 = cur + 16#64)
    (hx9 : s.readReg64 .x9 = auxPtr) :
    SepWP prog (pcL + 0x18#64) s
      ((((cur + 8#64) ↦₆₄ v₀) ∗
        ((cur + 16#64) ↦₆₄* ((rest ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
        (auxPtr ↦₆₄* acc)) ∗ F)
      (fun sf Q =>
        sf.pc = pcL + 0x18#64 ∧ sf.status = .Running ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .lr = s.readReg64 .lr ∧
        Q = ((((cur + 8#64) ↦₆₄ v₀) ∗
              ((cur + 16#64) ↦₆₄* ((rest ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
              (auxPtr ↦₆₄*
                ((t₀, v₀) :: rest).foldl
                  (fun a (t, v) => if t.toNat < 38 then a.set t.toNat v else a) acc)) ∗ F)) := by
  induction rest generalizing t₀ v₀ cur acc s F with
  | nil =>
    simp only [List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.foldl_cons, List.foldl_nil]
    rw [pointsToWords64_cons, pointsToWords64_cons, pointsToWords64_nil]
    have hcur_m8 : cur + 16#64 + (-8#64) = cur + 8#64 := by bv_omega
    have hjmp_hi : pcL + 4#64 + 0x0c#64 = pcL + 0x10#64 := by bv_omega
    by_cases hlt : t₀.toNat < 38
    · have hult : (37#64).ult t₀ = false := by simp [BitVec.ult]; omega
      rw [pointsToWords64_focus_idx auxPtr acc t₀ (by omega) (by omega)]
      have hupd :
          ((auxPtr + (t₀ <<< 3)) ↦₆₄ v₀) ∗
            (pointsToArray 8 (· ↦₆₄ ·) auxPtr (acc.take t₀.toNat) ∗
             pointsToArray 8 (· ↦₆₄ ·) (auxPtr + BitVec.ofNat 64 (8 * (t₀.toNat + 1)))
               (acc.drop (t₀.toNat + 1))) =
          (auxPtr ↦₆₄* acc.set t₀.toNat v₀) := by
        rw [pointsToArray_update_shift 3 (· ↦₆₄ ·) auxPtr acc t₀ v₀ (by omega) (by omega),
          ← pointsToWords64_eq_pointsToArray]
      wp_steps 6
      refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
      refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun],
        by simp only [wp_norm, arm64_norm],
        by simp only [wp_norm, arm64_norm],
        by simp only [wp_norm, arm64_norm],
        by simp only [wp_norm, arm64_norm],
        by simp only [wp_norm, arm64_norm],
        ?_⟩
      simp only [hlt, ↓reduceIte]
      rw [← hupd]
    · have hult : (37#64).ult t₀ = true := by simp [BitVec.ult]; omega
      wp_steps 4
      refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
      refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun],
        by simp only [wp_norm, arm64_norm],
        by simp only [wp_norm, arm64_norm],
        by simp only [wp_norm, arm64_norm],
        by simp only [wp_norm, arm64_norm],
        by simp only [wp_norm, arm64_norm],
        ?_⟩
      simp only [hlt, ↓reduceIte]
  | cons p ps ih =>
    rcases p with ⟨t₁, v₁⟩
    have ht1_ne : t₁ ≠ 0#64 := hno0 (t₁, v₁) (List.mem_cons_self ..)
    have ht1_beq : (t₁ == 0#64) = false := beq_eq_false_iff_ne.mpr ht1_ne
    have hcur_m8 : cur + 16#64 + (-8#64) = cur + 8#64 := by bv_omega
    have hcur32 : cur + 16#64 + 8#64 + 8#64 = cur + 16#64 + 16#64 := by bv_omega
    have hjmp_hi : pcL + 4#64 + 0x0c#64 = pcL + 0x10#64 := by bv_omega
    have hback : pcL + 0x14#64 + (-0x14#64) = pcL := by bv_omega
    conv => arg 4; simp only [List.cons_append, List.flatMap_cons, List.nil_append]
    rw [pointsToWords64_cons, pointsToWords64_cons, hcur32]
    by_cases hlt : t₀.toNat < 38
    · have hult : (37#64).ult t₀ = false := by simp [BitVec.ult]; omega
      rw [pointsToWords64_focus_idx auxPtr acc t₀ (by omega) (by omega)]
      have hupd :
          ((auxPtr + (t₀ <<< 3)) ↦₆₄ v₀) ∗
            (pointsToArray 8 (· ↦₆₄ ·) auxPtr (acc.take t₀.toNat) ∗
             pointsToArray 8 (· ↦₆₄ ·) (auxPtr + BitVec.ofNat 64 (8 * (t₀.toNat + 1)))
               (acc.drop (t₀.toNat + 1))) =
          (auxPtr ↦₆₄* acc.set t₀.toNat v₀) := by
        rw [pointsToArray_update_shift 3 (· ↦₆₄ ·) auxPtr acc t₀ v₀ (by omega) (by omega),
          ← pointsToWords64_eq_pointsToArray]
      apply SepWP.cut (mid := pcL)
      wp_steps 6
      refine SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun]) ?_
      refine SepWP.weaken_pre
        (P' := ((((cur + 16#64 + 8#64) ↦₆₄ v₁) ∗
          ((cur + 16#64 + 16#64) ↦₆₄* ((ps ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
          (auxPtr ↦₆₄* acc.set t₀.toNat v₀)) ∗
          (((cur + 8#64) ↦₆₄ v₀) ∗ ((cur + 16#64) ↦₆₄ t₁) ∗ F)))
        (by rw [← hupd]; sep_frame) ?_
      apply SepWP.mono
      case h =>
        refine ih t₁ v₁ (cur + 16#64) (acc.set t₀.toNat v₀)
          (((cur + 8#64) ↦₆₄ v₀) ∗ ((cur + 16#64) ↦₆₄ t₁) ∗ F)
          ht1_ne (fun q hq => hno0 q (List.mem_cons_of_mem _ hq)) (by simp [hlen])
          ?_ ?_ ?_ ?_ ?_
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hrun]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx9]
      case hoom => exact fun _ _ _ ho => ho
      case himp =>
        rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx19_f, hx21_f, hx29_f, hlr_f, rfl⟩
        refine ⟨hpc_f, hrun_f,
          by simpa [wp_norm, arm64_norm] using hsp_f,
          by simpa [wp_norm, arm64_norm] using hx19_f,
          by simpa [wp_norm, arm64_norm] using hx21_f,
          by simpa [wp_norm, arm64_norm] using hx29_f,
          by simpa [wp_norm, arm64_norm] using hlr_f,
          ?_⟩
        simp only [List.cons_append, List.flatMap_cons, List.nil_append, List.foldl_cons,
          hlt, ↓reduceIte]
        rw [pointsToWords64_cons, pointsToWords64_cons, hcur32]; ac_rfl
    · have hult : (37#64).ult t₀ = true := by simp [BitVec.ult]; omega
      apply SepWP.cut (mid := pcL)
      wp_steps 4
      refine SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun]) ?_
      refine SepWP.weaken_pre
        (P' := ((((cur + 16#64 + 8#64) ↦₆₄ v₁) ∗
          ((cur + 16#64 + 16#64) ↦₆₄* ((ps ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
          (auxPtr ↦₆₄* acc)) ∗
          (((cur + 8#64) ↦₆₄ v₀) ∗ ((cur + 16#64) ↦₆₄ t₁) ∗ F)))
        (by sep_frame) ?_
      apply SepWP.mono
      case h =>
        refine ih t₁ v₁ (cur + 16#64) acc
          (((cur + 8#64) ↦₆₄ v₀) ∗ ((cur + 16#64) ↦₆₄ t₁) ∗ F)
          ht1_ne (fun q hq => hno0 q (List.mem_cons_of_mem _ hq)) hlen
          ?_ ?_ ?_ ?_ ?_
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hrun]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx9]
      case hoom => exact fun _ _ _ ho => ho
      case himp =>
        rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx19_f, hx21_f, hx29_f, hlr_f, rfl⟩
        refine ⟨hpc_f, hrun_f,
          by simpa [wp_norm, arm64_norm] using hsp_f,
          by simpa [wp_norm, arm64_norm] using hx19_f,
          by simpa [wp_norm, arm64_norm] using hx21_f,
          by simpa [wp_norm, arm64_norm] using hx29_f,
          by simpa [wp_norm, arm64_norm] using hlr_f,
          ?_⟩
        simp only [List.cons_append, List.flatMap_cons, List.nil_append, List.foldl_cons,
          hlt, ↓reduceIte]
        rw [pointsToWords64_cons, pointsToWords64_cons, hcur32]; ac_rfl

private theorem replicate_zero_eq_flatMap {f : BitVec 64 → List (BitVec 8)}
    (hf : f 0#64 = List.replicate 8 0#8) :
    ∀ n : Nat, List.replicate (8 * n) 0#8 = (List.replicate n 0#64).flatMap f
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.flatMap_cons, ← replicate_zero_eq_flatMap hf n, hf,
      ← List.replicate_add, show 8 + 8 * n = 8 * (n + 1) by omega]

/-- Full `zig cc` `musl` `auxv` scan (`pc₀..pc₀+0x24`), starting from raw `encodeAuxvBytes entries`
    at `x20 = auxvTableAddr` and zeroed `(sp + 0x30) ↦ₛ List.replicate 304 0#8`, producing
    `((sp + 0x30) ↦₆₄* auxvScan38 entries)`. -/
theorem zig_auxv_scan_loop {prog : Program} {pc₀ : BitVec 64}
    (hf0 : prog.fetch pc₀ = some (.ldr .W64 .X64 false .x8 (.PostIndex .x20 16#64)))
    (hf1 : prog.fetch (pc₀ + 4#64) = some (.cbz .W64 false .x8 0x40#64))
    (hf2 : prog.fetch (pc₀ + 8#64) = some (.addSubImm .W64 .ADD .x9 .sp 0x30#12 false))
    (hf3 : prog.fetch (pc₀ + 0x0c#64) = some (.addSubImm .W64 .SUBS .xzr .x8 0x25#12 false))
    (hf4 : prog.fetch (pc₀ + 0x10#64) = some (.bCond .HI 0x0c#64))
    (hf5 : prog.fetch (pc₀ + 0x14#64) = some (.ldr .W64 .X64 false .x10 (.UnscaledOffset .x20 (-8#64))))
    (hf6 : prog.fetch (pc₀ + 0x18#64) = some (.str .X64 .x10 (.RegOffset .x9 .x8 .UXTX 3)))
    (hf7 : prog.fetch (pc₀ + 0x1c#64) = some (.ldr .W64 .X64 false .x8 (.PostIndex .x20 16#64)))
    (hf8 : prog.fetch (pc₀ + 0x20#64) = some (.cbz .W64 true .x8 (-0x14#64)))
    (entries : List (BitVec 64 × BitVec 64)) (auxvAddr : BitVec 64) {s : State} (F : SepProp)
    (hne_nil : entries ≠ []) (hno0 : ∀ p ∈ entries, p.1 ≠ 0#64)
    (hpc : s.pc = pc₀) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = auxvAddr) :
    SepWP prog (pc₀ + 0x24#64) s
      (((auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
        ((s.sp + 0x30#64) ↦ₛ List.replicate 304 0#8)) ∗ F)
      (fun sf Q =>
        sf.pc = pc₀ + 0x24#64 ∧ sf.status = .Running ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .lr = s.readReg64 .lr ∧
        Q = (((auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
              ((s.sp + 0x30#64) ↦₆₄* auxvScan38 entries)) ∗ F)) := by
  cases entries with
  | nil => exact False.elim (hne_nil rfl)
  | cons p₀ rest =>
    rcases p₀ with ⟨t₀, v₀⟩
    have ht0_ne : t₀ ≠ 0#64 := hno0 (t₀, v₀) (List.mem_cons_self ..)
    have ht0_beq : (t₀ == 0#64) = false := beq_eq_false_iff_ne.mpr ht0_ne
    have hzero38 : ((s.sp + 0x30#64) ↦ₛ List.replicate 304 0#8) =
        ((s.sp + 0x30#64) ↦₆₄* List.replicate 38 0#64) := by
      rw [pointsToWords64_eq_pointsToBytesLE]
      exact congrArg ((s.sp + 0x30#64) ↦ₛ ·) (replicate_zero_eq_flatMap rfl 38)
    have haux_words : (auxvAddr ↦ₛ encodeAuxvBytes ((t₀, v₀) :: rest)) =
        ((auxvAddr ↦₆₄ t₀) ∗ ((auxvAddr + 8#64) ↦₆₄ v₀) ∗
         ((auxvAddr + 16#64) ↦₆₄* ((rest ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v]))) := by
      rw [encodeAuxvBytes_eq_flatMap_bytesLE, ← pointsToWords64_eq_pointsToBytesLE]
      simp only [List.cons_append, List.flatMap_cons, List.nil_append, AuxvTag.null]
      rw [pointsToWords64_cons, pointsToWords64_cons]
      have ha16 : auxvAddr + 8#64 + 8#64 = auxvAddr + 16#64 := by bv_omega
      rw [ha16]
    rw [hzero38, haux_words]
    apply SepWP.cut (mid := pc₀ + 0x0c#64)
    wp_steps 3
    refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    have hp4 : pc₀ + 0x0c#64 + 4#64 = pc₀ + 0x10#64 := by bv_omega
    have hp8 : pc₀ + 0x0c#64 + 8#64 = pc₀ + 0x14#64 := by bv_omega
    have hp12 : pc₀ + 0x0c#64 + 0x0c#64 = pc₀ + 0x18#64 := by bv_omega
    have hp16 : pc₀ + 0x0c#64 + 0x10#64 = pc₀ + 0x1c#64 := by bv_omega
    have hp20 : pc₀ + 0x0c#64 + 0x14#64 = pc₀ + 0x20#64 := by bv_omega
    have hp24 : pc₀ + 0x0c#64 + 0x18#64 = pc₀ + 0x24#64 := by bv_omega
    rw [← hp24]
    refine SepWP.weaken_pre
      (P' := ((((auxvAddr + 8#64) ↦₆₄ v₀) ∗
        ((auxvAddr + 16#64) ↦₆₄* ((rest ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
        ((s.sp + 0x30#64) ↦₆₄* List.replicate 38 0#64)) ∗
        ((auxvAddr ↦₆₄ t₀) ∗ F)))
      (by sep_frame) ?_
    apply SepWP.mono
    case h =>
      refine zig_auxv_scan_inner hf3 (hp4.symm ▸ hf4) (hp8.symm ▸ hf5) (hp12.symm ▸ hf6)
        (hp16.symm ▸ hf7) (hp20.symm ▸ hf8) t₀ v₀ rest auxvAddr (s.sp + 0x30#64)
        (List.replicate 38 0#64) ((auxvAddr ↦₆₄ t₀) ∗ F)
        ht0_ne (fun q hq => hno0 q (List.mem_cons_of_mem _ hq)) (by simp)
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
    case hoom => exact fun _ _ _ ho => ho
    case himp =>
      rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx19_f, hx21_f, hx29_f, hlr_f, rfl⟩
      refine ⟨hp24 ▸ hpc_f, hrun_f,
        by simpa [wp_norm, arm64_norm] using hsp_f,
        by simpa [wp_norm, arm64_norm] using hx19_f,
        by simpa [wp_norm, arm64_norm] using hx21_f,
        by simpa [wp_norm, arm64_norm] using hx29_f,
        by simpa [wp_norm, arm64_norm] using hlr_f,
        ?_⟩
      unfold auxvScan38; ac_rfl

/-- Inner loop of `zig cc` `musl` `__progname` `'/'` scan (`pcP + 4`: `add x9, x9, #1;
    ldurb w10, [x9, #-1]; cmp w10, #0x2f; b.eq pcP; cbnz w10, pcP + 4`). -/
theorem zig_progname_scan_inner {prog : Program} {pcP : BitVec 64} {imm : BitVec 64}
    (hf0 : prog.fetch pcP = some (.str .X64 .x9 (.Offset .x8 imm)))
    (hf1 : prog.fetch (pcP + 4#64) = some (.addSubImm .W64 .ADD .x9 .x9 1#12 false))
    (hf2 : prog.fetch (pcP + 8#64) = some (.ldr .W32 .B8 false .x10 (.UnscaledOffset .x9 (-1#64))))
    (hf3 : prog.fetch (pcP + 0x0c#64) = some (.addSubImm .W32 .SUBS .xzr .x10 0x2f#12 false))
    (hf4 : prog.fetch (pcP + 0x10#64) = some (.bCond .EQ (-0x10#64)))
    (hf5 : prog.fetch (pcP + 0x14#64) = some (.cbz .W32 true .x10 (-0x10#64)))
    (bs : List (BitVec 8)) (cur slotAddr best : BitVec 64) {s : State} (F : SepProp)
    (hnul : 0#8 ∉ bs)
    (hpc : s.pc = pcP + 4#64) (hrun : s.status = .Running)
    (hx9 : s.readReg64 .x9 = cur) (hx8 : s.readReg64 .x8 + imm = slotAddr) :
    SepWP prog (pcP + 0x18#64) s
      (((cur ↦ᵣ (bs ++ [0#8])) ∗ (slotAddr ↦₆₄ best)) ∗ F)
      (fun sf Q =>
        sf.pc = pcP + 0x18#64 ∧ sf.status = .Running ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .lr = s.readReg64 .lr ∧
        ∃ best' : BitVec 64,
          Q = (((cur ↦ᵣ (bs ++ [0#8])) ∗ (slotAddr ↦₆₄ best')) ∗ F)) := by
  induction bs generalizing cur best s F with
  | nil =>
    simp only [List.nil_append]
    rw [pointsToBytesRO_singleton]
    have hm1 : cur + 1#64 + (-1#64) = cur := by bv_omega
    wp_steps 5
    refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      best, rfl⟩
  | cons c rest ih =>
    have hc0 : c ≠ 0#8 := fun h => hnul (h ▸ List.mem_cons_self ..)
    have hrest_nul : 0#8 ∉ rest := fun h => hnul (List.mem_cons_of_mem _ h)
    have hc_ze64 : (c.zeroExtend 64 == 0#64) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro h; apply hc0; apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans c.isLt (by decide : 256 < 2 ^ 64))]
        using this
    have hm1 : cur + 1#64 + (-1#64) = cur := by bv_omega
    have hback_eq : pcP + 0x10#64 + (-0x10#64) = pcP := by bv_omega
    have hback_ne : pcP + 0x14#64 + (-0x10#64) = pcP + 4#64 := by bv_omega
    simp only [List.cons_append]
    rw [pointsToBytesRO_cons]
    by_cases hslash : c = 0x2f#8
    · subst hslash
      apply SepWP.cut (mid := pcP + 4#64)
      wp_steps 5
      refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
      refine SepWP.weaken_pre
        (P' := (((cur + 1#64) ↦ᵣ (rest ++ [0#8])) ∗ (slotAddr ↦₆₄ (cur + 1#64))) ∗
          ((cur ↦₈ᵣ 0x2f#8) ∗ F))
        (by sep_frame) ?_
      apply SepWP.mono
      case h =>
        refine ih (cur + 1#64) (cur + 1#64) ((cur ↦₈ᵣ 0x2f#8) ∗ F) hrest_nul
          (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hx8])
      case hoom => exact fun _ _ _ ho => ho
      case himp =>
        rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx19_f, hx20_f, hx21_f, hx29_f, hlr_f, best', rfl⟩
        refine ⟨hpc_f, hrun_f,
          by simpa [wp_norm, arm64_norm] using hsp_f,
          by simpa [wp_norm, arm64_norm] using hx19_f,
          by simpa [wp_norm, arm64_norm] using hx20_f,
          by simpa [wp_norm, arm64_norm] using hx21_f,
          by simpa [wp_norm, arm64_norm] using hx29_f,
          by simpa [wp_norm, arm64_norm] using hlr_f,
          best', ?_⟩
        ac_rfl
    · have hslash_ze : (c.zeroExtend 32 == 0x2f#32) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro h; apply hslash; apply BitVec.eq_of_toNat_eq
        have := congrArg BitVec.toNat h
        simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans c.isLt (by decide : 256 < 2 ^ 32))]
          using this
      apply SepWP.cut (mid := pcP + 4#64)
      wp_steps 5
      refine SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun]) ?_
      refine SepWP.weaken_pre
        (P' := (((cur + 1#64) ↦ᵣ (rest ++ [0#8])) ∗ (slotAddr ↦₆₄ best)) ∗
          ((cur ↦₈ᵣ c) ∗ F))
        (by sep_frame) ?_
      apply SepWP.mono
      case h =>
        refine ih (cur + 1#64) best ((cur ↦₈ᵣ c) ∗ F) hrest_nul
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrun])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hx8])
      case hoom => exact fun _ _ _ ho => ho
      case himp =>
        rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx19_f, hx20_f, hx21_f, hx29_f, hlr_f, best', rfl⟩
        refine ⟨hpc_f, hrun_f,
          by simpa [wp_norm, arm64_norm] using hsp_f,
          by simpa [wp_norm, arm64_norm] using hx19_f,
          by simpa [wp_norm, arm64_norm] using hx20_f,
          by simpa [wp_norm, arm64_norm] using hx21_f,
          by simpa [wp_norm, arm64_norm] using hx29_f,
          by simpa [wp_norm, arm64_norm] using hlr_f,
          best', ?_⟩
        ac_rfl

/-- Full `zig cc` `musl` `__progname` `'/'` scan (`pcP..pcP + 0x18`), including the initial
    `str x9, [x8, #imm]` at `pcP`. -/
theorem zig_progname_scan_loop {prog : Program} {pcP : BitVec 64} {imm : BitVec 64}
    (hf0 : prog.fetch pcP = some (.str .X64 .x9 (.Offset .x8 imm)))
    (hf1 : prog.fetch (pcP + 4#64) = some (.addSubImm .W64 .ADD .x9 .x9 1#12 false))
    (hf2 : prog.fetch (pcP + 8#64) = some (.ldr .W32 .B8 false .x10 (.UnscaledOffset .x9 (-1#64))))
    (hf3 : prog.fetch (pcP + 0x0c#64) = some (.addSubImm .W32 .SUBS .xzr .x10 0x2f#12 false))
    (hf4 : prog.fetch (pcP + 0x10#64) = some (.bCond .EQ (-0x10#64)))
    (hf5 : prog.fetch (pcP + 0x14#64) = some (.cbz .W32 true .x10 (-0x10#64)))
    (bs : List (BitVec 8)) (cur slotAddr oldVal : BitVec 64) {s : State} (F : SepProp)
    (hnul : 0#8 ∉ bs)
    (hpc : s.pc = pcP) (hrun : s.status = .Running)
    (hx9 : s.readReg64 .x9 = cur) (hx8 : s.readReg64 .x8 + imm = slotAddr) :
    SepWP prog (pcP + 0x18#64) s
      (((cur ↦ᵣ (bs ++ [0#8])) ∗ (slotAddr ↦₆₄ oldVal)) ∗ F)
      (fun sf Q =>
        sf.pc = pcP + 0x18#64 ∧ sf.status = .Running ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .lr = s.readReg64 .lr ∧
        ∃ best' : BitVec 64,
          Q = (((cur ↦ᵣ (bs ++ [0#8])) ∗ (slotAddr ↦₆₄ best')) ∗ F)) := by
  apply SepWP.cut (mid := pcP + 4#64)
  wp_steps 1
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine SepWP.weaken_pre
    (P' := (((cur ↦ᵣ (bs ++ [0#8])) ∗ (slotAddr ↦₆₄ cur)) ∗ F))
    (by sep_frame) ?_
  apply SepWP.mono
  case h =>
    exact zig_progname_scan_inner hf0 hf1 hf2 hf3 hf4 hf5 bs cur slotAddr cur F hnul
      (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm, hx9])
      (by simp only [wp_norm, arm64_norm, hx8])
  case hoom => exact fun _ _ _ ho => ho
  case himp =>
    rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx19_f, hx20_f, hx21_f, hx29_f, hlr_f, best', rfl⟩
    exact ⟨hpc_f, hrun_f,
      by simpa [wp_norm, arm64_norm] using hsp_f,
      by simpa [wp_norm, arm64_norm] using hx19_f,
      by simpa [wp_norm, arm64_norm] using hx20_f,
      by simpa [wp_norm, arm64_norm] using hx21_f,
      by simpa [wp_norm, arm64_norm] using hx29_f,
      by simpa [wp_norm, arm64_norm] using hlr_f,
      best', rfl⟩

end ProofLib.StdStartup
