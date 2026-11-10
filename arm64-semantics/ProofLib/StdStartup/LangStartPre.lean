/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.StdStartup.StackInit
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.NonVmSteps

/-!
# Pre-Main Rust Runtime Startup Contracts

Symbolic `SepWP` contracts for `ThreadId` initialization, `sanitize_standard_fds` (`poll`/`ppoll`),
`reset_sigpipe` (`signal`/`rt_sigaction`), `sysconf(30)`, `args::init`, and
`__rust_begin_short_backtrace` entry to `L.userMainAddr`.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib.StdStartup

open Arm64 Arm64.Process ProofLib

def sccpWords : List (BitVec 32) := [0xaa0003e8#32, 0xaa0103e0#32, 0xaa0203e1#32, 0xaa0303e2#32, 0xaa0403e3#32, 0xaa0503e4#32, 0xaa0603e5#32, 0xd4000001#32, 0xd65f03c0#32]
def syscallRetNonnegWords : List (BitVec 32) := [0xa9be7bfd#32, 0xb140041f#32, 0x910003fd#32, 0xf9000bf3#32, 0xaa0003f3#32, 0x54000088#32, 0xf9400bf3#32, 0xa8c27bfd#32, 0xd65f03c0#32]
def signalWords : List (BitVec 32) := [0xa9ac7bfd#32, 0xaa0103e4#32, 0x52a20003#32, 0x910003fd#32, 0xa9137fff#32, 0x910043e2#32, 0x9102a3e1#32, 0xf90057e4#32, 0xa90b7fff#32, 0xa90c7fff#32, 0xa90d7fff#32, 0xa90e7fff#32, 0xa90f7fff#32, 0xa9107fff#32, 0xa9117fff#32, 0xa9127fff#32, 0xb90133e3#32, 0x94000070#32, 0xf9400be1#32, 0x7100001f#32, 0xa8d47bfd#32, 0xda9fa020#32, 0xd65f03c0#32]
def libcSigactionHeadWords : List (BitVec 32) := [0xa9b97bfd#32, 0xaa0103e4#32, 0xd2800001#32, 0x910003fd#32, 0xa90153f3#32, 0xaa0203f4#32, 0xf90013f5#32, 0x93407c15#32, 0xb4000904#32, 0xf9400086#32, 0xf10004df#32, 0x54000689#32]
def sysconfEpilogueWords : List (BitVec 32) := [0xa8d97bfd#32, 0xd65f03c0#32]
def beginShortBacktraceWords : List (BitVec 32) := [0xa9bf7bfd#32, 0x910003fd#32, 0xd63f0000#32, 0xa8c17bfd#32, 0xd65f03c0#32]
def syscallCpInstrs (L : StdBinaryLayout) : List Instr := [.b (L.sccpAddr - L.syscallCpAddr)]
def pollInstrs (L : StdBinaryLayout) : List Instr := [.stp .W64 .x29 .lr (.PreIndex .sp 0xffffffffffffffe0#64), .logicalShift .W32 .ORR .x6 .xzr .x2 .LSL 0, .moveWide .W64 .MOVZ .x3 0#16 0, .addSubImm .W64 .ADD .x29 .sp 0#12 false, .logicalShift .W64 .ORR .x2 .xzr .x1 .LSL 0, .tbz .W32 true .x6 31 0x3c#64, .moveWide .W32 .MOVZ .x5 0x4dd3#16 0, .moveWide .W32 .MOVZ .x7 0x03e8#16 0, .moveWide .W32 .MOVK .x5 0x1062#16 16, .moveWide .W32 .MOVZ .x1 0x4240#16 0, .moveWide .W32 .MOVK .x1 0x000f#16 16, .addSubImm .W64 .ADD .x3 .sp 0x010#12 false, .dataProc3 .W64 .SMADDL .x5 .x6 .x5 .xzr, .bitfield .W64 .SBFM .x5 .x5 38 63, .addSubShift .W32 .SUB .x4 .x5 .x6 .ASR 31, .bitfield .W64 .SBFM .x5 .x4 0 31, .dataProc3 .W32 .MSUB .x4 .x4 .x7 .x6, .dataProc3 .W32 .MADD .x4 .x4 .x1 .xzr, .bitfield .W64 .SBFM .x4 .x4 0 31, .stp .W64 .x5 .x4 (.Offset .sp 0x10#64), .logicalShift .W64 .ORR .x1 .xzr .x0 .LSL 0, .moveWide .W64 .MOVZ .x6 0#16 0, .moveWide .W64 .MOVZ .x5 8#16 0, .moveWide .W64 .MOVZ .x4 0#16 0, .moveWide .W64 .MOVZ .x0 0x49#16 0, .bl (L.syscallCpAddr - (L.pollAddr + 0x64#64)), .bl (L.syscallRetAddr - (L.pollAddr + 0x68#64)), .ldp .W64 false .x29 .lr (.PostIndex .sp 0x20#64), .ret .lr]
def sigactionFastInstrs (L : StdBinaryLayout) : List Instr := [.stp .W64 .x29 .lr (.PreIndex .sp 0xffffffffffffffb0#64), .addSubImm .W32 .SUB .x4 .x0 0x001#12 false, .addSubImm .W32 .SUB .x3 .x0 0x020#12 false, .addSubImm .W64 .ADD .x29 .sp 0#12 false, .stp .W64 .x19 .x20 (.Offset .sp 0x10#64), .addSubImm .W32 .SUBS .xzr .x4 0x03f#12 false, .condCompareImm .W32 true .x3 0x02#5 0#4 .LS, .bCond .LS 0x28#64, .logicalShift .W32 .ORR .x19 .xzr .x0 .LSL 0, .addSubImm .W32 .SUBS .xzr .x0 0x006#12 false, .bCond .EQ 0x30#64, .bl (L.libcSigactionAddr - (L.sigactionAddr + 0x2c#64)), .logicalShift .W32 .ORR .x19 .xzr .x0 .LSL 0, .logicalShift .W32 .ORR .x0 .xzr .x19 .LSL 0, .ldp .W64 false .x19 .x20 (.Offset .sp 0x10#64), .ldp .W64 false .x29 .lr (.PostIndex .sp 0x50#64), .ret .lr]
def libcSigactionIgnTailInstrs (L : StdBinaryLayout) : List Instr := let b := L.libcSigactionAddr + 0xfc#64; [.ldr .W32 .W32 false .x0 (.Offset .x4 0x88#64), .logicalImm .W64 .ANDS .xzr .x0 4#64, .logicalImm .W32 .ORR .x0 .x0 0x0400000004000000#64, .adr true .x5 (adrpOff (b + 0x0c#64) L.restoreRtAddr), .adr true .x2 (adrpOff (b + 0x10#64) L.restoreRtAddr), .addSubImm .W64 .ADD .x5 .x5 (L.restoreRtAddr.truncate 12) false, .addSubImm .W64 .ADD .x2 .x2 (L.restoreRtAddr.truncate 12) false, .bitfield .W64 .SBFM .x3 .x0 0 31, .addSubImm .W64 .ADD .x1 .x4 0x008#12 false, .condSelect .W64 .CSEL .x4 .x2 .x5 .NE, .addSubImm .W64 .ADD .x19 .sp 0x030#12 false, .addSubImm .W64 .ADD .x0 .sp 0x048#12 false, .moveWide .W64 .MOVZ .x2 8#16 0, .stp .W64 .x6 .x3 (.Offset .sp 0x30#64), .str .X64 .x4 (.Offset .sp 0x40#64), .bl (L.memcpyAddr - (b + 0x3c#64)), .logicalShift .W64 .ORR .x1 .xzr .x19 .LSL 0, .addSubImm .W64 .SUBS .xzr .x20 0#12 false, .addSubImm .W64 .ADD .x4 .sp 0x050#12 false, .logicalShift .W64 .ORR .x0 .xzr .x21 .LSL 0, .condSelect .W64 .CSEL .x2 .x4 .xzr .NE, .moveWide .W64 .MOVZ .x8 0x86#16 0, .moveWide .W64 .MOVZ .x3 8#16 0, .system false 0#16, .addSubImm .W64 .SUBS .xzr .x20 0#12 false, .logicalShift .W64 .ORR .x19 .xzr .x0 .LSL 0, .condCompareImm .W32 true .x0 0#5 0#4 .NE, .bCond .EQ 0x1c#64, .bitfield .W64 .SBFM .x0 .x19 0 31, .bl (L.syscallRetAddr - (b + 0x74#64)), .ldp .W64 false .x19 .x20 (.Offset .sp 0x10#64), .ldr .W64 .X64 false .x21 (.Offset .sp 0x20#64), .ldp .W64 false .x29 .lr (.PostIndex .sp 0x70#64), .ret .lr, .ldr .W64 .X64 false .x0 (.Offset .sp 0x50#64), .str .X64 .x0 (.Offset .x20 0#64), .ldr .W64 .X64 false .x0 (.Offset .sp 0x58#64), .str .W32 .x0 (.Offset .x20 0x88#64), .logicalShift .W64 .ORR .x2 .xzr .x3 .LSL 0, .addSubImm .W64 .ADD .x1 .x4 0x018#12 false, .addSubShift .W64 .ADD .x0 .x20 .x3 .LSL 0, .bl (L.memcpyAddr - (b + 0xa4#64)), .b 0xffffffffffffffc8#64]
def sysconfPagesizeInstrs (L : StdBinaryLayout) : List Instr := [.stp .W64 .x29 .lr (.PreIndex .sp 0xfffffffffffffe70#64), .addSubImm .W32 .SUBS .xzr .x0 0x0fa#12 false, .addSubImm .W64 .ADD .x29 .sp 0#12 false, .bCond .HI 0x6c#64, .stp .W64 .x19 .x20 (.Offset .sp 0x10#64), .logicalShift .W32 .ORR .x19 .xzr .x0 .LSL 0, .adr true .x0 (adrpOff (L.sysconfAddr + 0x18#64) L.sysconfValuesAddr), .addSubImm .W64 .ADD .x0 .x0 (L.sysconfValuesAddr.truncate 12) false, .ldr .W32 .H16 true .x20 (.RegOffset .x0 .x19 .SXTW 1), .cbz .W32 false .x20 0x50#64, .addSubImm .W32 .ADDS .xzr .x20 0x001#12 false, .bCond .GE 0x110#64, .addSubImm .W32 .ADDS .xzr .x20 0x100#12 false, .bCond .LT 0x5c#64, .logicalImm .W32 .AND .x1 .x20 0x000000ff000000ff#64, .addSubImm .W32 .SUBS .xzr .x1 0x007#12 false, .bCond .HI 0xa0#64, .addSubImm .W32 .SUBS .xzr .x1 0x005#12 false, .bCond .HI 0x100#64, .addSubImm .W32 .SUBS .xzr .x1 0x003#12 false, .bCond .EQ 0x1cc#64, .bCond .LS 0x6c#64, .adr true .x2 (adrpOff (L.sysconfAddr + 0x58#64) (L.libcAddr + 0x30#64)), .addSubImm .W32 .SUBS .xzr .x1 0x004#12 false, .logicalImm .W64 .ORR .x0 .xzr 0x7fffffff#64, .ldr .W64 .X64 false .x1 (.Offset .x2 (pageLo12 (L.libcAddr + 0x30#64))), .ldp .W64 false .x19 .x20 (.Offset .sp 0x10#64), .condSelect .W64 .CSEL .x0 .x0 .x1 .NE, .b 0x68#64]
@[inline] def cMainEcShiftNoArgc (L : StdBinaryLayout) : BitVec 64 := if L.userMainReturnsExitCode then 0x08#64 else 0x00#64
@[inline] def cMainEcShiftWithArgc (L : StdBinaryLayout) : BitVec 64 := if L.userMainReturnsExitCode then 0x00#64 else 0xfffffffffffffff8#64
def cMainPreNoArgcInstrs (L : StdBinaryLayout) : List Instr := let b := L.cMainAddr; let ec := cMainEcShiftNoArgc L; [.addSubImm .W64 .SUB .sp .sp 0x060#12 false, .stp .W64 .x29 .lr (.Offset .sp 0x20#64), .addSubImm .W64 .ADD .x29 .sp 0x020#12 false, .str .X64 .x23 (.Offset .sp 0x30#64), .stp .W64 .x22 .x21 (.Offset .sp 0x40#64), .stp .W64 .x20 .x19 (.Offset .sp 0x50#64), .sysReg true 0x5e82#15 .x8, .logicalShift .W64 .ORR .x19 .xzr .x1 .LSL 0, .addSubImm .W64 .ADD .x8 .x8 0#12 true, .addSubImm .W64 .ADD .x22 .x8 0x010#12 false, .ldr .W64 .X64 false .x8 (.Offset .x22 0#64), .cbz .W64 true .x8 0x40#64, .adr true .x8 (adrpOff (b + 0x30#64) L.threadIdCounterAddr), .adr true .x20 (adrpOff (b + 0x34#64) L.threadIdCounterAddr), .addSubImm .W64 .ADD .x20 .x20 (L.threadIdCounterAddr.truncate 12) false, .ldr .W64 .X64 false .x21 (.Offset .x8 (pageLo12 L.threadIdCounterAddr)), .addSubImm .W64 .ADDS .xzr .x21 0x001#12 false, .bCond .EQ (0x270#64 + ec), .addSubImm .W64 .ADD .x1 .x21 0x001#12 false, .logicalShift .W64 .ORR .x0 .xzr .x21 .LSL 0, .logicalShift .W64 .ORR .x2 .xzr .x20 .LSL 0, .addSubImm .W64 .ADD .x23 .x21 0x001#12 false, .bl (L.cas8RelaxAddr - (b + 0x58#64)), .addSubShift .W64 .SUBS .xzr .x0 .x21 .LSL 0, .logicalShift .W64 .ORR .x21 .xzr .x0 .LSL 0, .bCond .NE 0xffffffffffffffdc#64, .str .X64 .x23 (.Offset .x22 0#64), .moveWide .W32 .MOVZ .x8 1#16 0, .moveWide .W32 .MOVZ .x9 2#16 0, .stp .W64 .xzr .x8 (.Offset .sp 0x08#64), .str .X64 .x9 (.Offset .sp 0x18#64), .addSubImm .W64 .ADD .x0 .sp 0x008#12 false, .moveWide .W32 .MOVZ .x1 3#16 0, .logicalShift .W32 .ORR .x2 .xzr .xzr .LSL 0, .bl (L.pollAddr - (b + 0x88#64)), .addSubImm .W32 .ADDS .xzr .x0 0x001#12 false, .bCond .NE (0x1c0#64 + ec)]
def cMainPollLoopNoArgcInstrs (L : StdBinaryLayout) : List Instr := let ec := cMainEcShiftNoArgc L; let b := L.cMainAddr + (0x250#64 + ec); [.logicalShift .W64 .ORR .x22 .xzr .xzr .LSL 0, .moveWide .W32 .MOVN .x21 0#16 0, .addSubImm .W64 .ADD .x23 .sp 0x008#12 false, .adr true .x20 (adrpOff (b + 0x0c#64) L.devNullStdAddr), .addSubImm .W64 .ADD .x20 .x20 (L.devNullStdAddr.truncate 12) false, .addSubImm .W64 .SUBS .xzr .x22 0x018#12 false, .bCond .EQ (0xffffffffffffff50#64 - ec), .addSubShift .W64 .ADD .x8 .x23 .x22 .LSL 0, .addSubImm .W64 .ADD .x22 .x22 0x008#12 false, .ldr .W32 .H16 false .x8 (.Offset .x8 0x06#64), .tbz .W32 false .x8 5 0xffffffffffffffec#64]
def cMainMidNoArgcInstrs (L : StdBinaryLayout) : List Instr := let b := L.cMainAddr + 0x1b8#64; let ec := cMainEcShiftNoArgc L; [.moveWide .W32 .MOVZ .x0 0x0d#16 0, .moveWide .W32 .MOVZ .x1 1#16 0, .bl (L.signalAddr - (b + 0x08#64)), .addSubImm .W64 .ADDS .xzr .x0 0x001#12 false, .bCond .EQ (0xf0#64 + ec), .moveWide .W32 .MOVZ .x0 0x1e#16 0, .bl (L.sysconfAddr - (b + 0x18#64)), .adr true .x8 (adrpOff (b + 0x1c#64) L.pageSizeGlobalAddr), .str .X64 .x0 (.Offset .x8 (pageLo12 L.pageSizeGlobalAddr)), .adr true .x0 (adrpOff (b + 0x24#64) L.userMainAddr), .addSubImm .W64 .ADD .x0 .x0 (L.userMainAddr.truncate 12) false, .ldr .W64 .X64 false .xzr (.Offset .x8 (pageLo12 L.pageSizeGlobalAddr)), .adr true .x8 (adrpOff (b + 0x30#64) L.argvGlobalAddr), .str .X64 .x19 (.Offset .x8 (pageLo12 L.argvGlobalAddr)), .bl (L.beginShortBacktraceAddr - (b + 0x38#64))]
def cMainPreWithArgcInstrs (L : StdBinaryLayout) : List Instr := let b := L.cMainAddr; let ec := cMainEcShiftWithArgc L; [.addSubImm .W64 .SUB .sp .sp 0x060#12 false, .stp .W64 .x29 .lr (.Offset .sp 0x20#64), .addSubImm .W64 .ADD .x29 .sp 0x020#12 false, .stp .W64 .x24 .x23 (.Offset .sp 0x30#64), .stp .W64 .x22 .x21 (.Offset .sp 0x40#64), .stp .W64 .x20 .x19 (.Offset .sp 0x50#64), .sysReg true 0x5e82#15 .x8, .logicalShift .W64 .ORR .x19 .xzr .x1 .LSL 0, .addSubImm .W64 .ADD .x8 .x8 0#12 true, .addSubImm .W64 .ADD .x22 .x8 0x010#12 false, .ldr .W64 .X64 false .x8 (.Offset .x22 0#64), .cbz .W64 true .x8 0x48#64, .adr true .x8 (adrpOff (b + 0x30#64) L.threadIdCounterAddr), .logicalShift .W64 .ORR .x23 .xzr .x0 .LSL 0, .adr true .x20 (adrpOff (b + 0x38#64) L.threadIdCounterAddr), .addSubImm .W64 .ADD .x20 .x20 (L.threadIdCounterAddr.truncate 12) false, .ldr .W64 .X64 false .x21 (.Offset .x8 (pageLo12 L.threadIdCounterAddr)), .addSubImm .W64 .ADDS .xzr .x21 0x001#12 false, .bCond .EQ (0x288#64 + ec), .addSubImm .W64 .ADD .x1 .x21 0x001#12 false, .logicalShift .W64 .ORR .x0 .xzr .x21 .LSL 0, .logicalShift .W64 .ORR .x2 .xzr .x20 .LSL 0, .addSubImm .W64 .ADD .x24 .x21 0x001#12 false, .bl (L.cas8RelaxAddr - (b + 0x5c#64)), .addSubShift .W64 .SUBS .xzr .x0 .x21 .LSL 0, .logicalShift .W64 .ORR .x21 .xzr .x0 .LSL 0, .bCond .NE 0xffffffffffffffdc#64, .logicalShift .W64 .ORR .x0 .xzr .x23 .LSL 0, .str .X64 .x24 (.Offset .x22 0#64), .bitfield .W64 .SBFM .x22 .x0 0 31, .moveWide .W32 .MOVZ .x8 1#16 0, .moveWide .W32 .MOVZ .x9 2#16 0, .stp .W64 .xzr .x8 (.Offset .sp 0#64), .str .X64 .x9 (.Offset .sp 0x10#64), .addSubImm .W64 .ADD .x0 .sp 0#12 false, .moveWide .W32 .MOVZ .x1 3#16 0, .logicalShift .W32 .ORR .x2 .xzr .xzr .LSL 0, .bl (L.pollAddr - (b + 0x94#64)), .addSubImm .W32 .ADDS .xzr .x0 0x001#12 false, .bCond .NE (0x1d0#64 + ec)]
def cMainPollLoopWithArgcInstrs (L : StdBinaryLayout) : List Instr := let ec := cMainEcShiftWithArgc L; let b := L.cMainAddr + (0x26c#64 + ec); [.logicalShift .W64 .ORR .x23 .xzr .xzr .LSL 0, .moveWide .W32 .MOVN .x21 0#16 0, .addSubImm .W64 .ADD .x24 .sp 0#12 false, .adr true .x20 (adrpOff (b + 0x0c#64) L.devNullStdAddr), .addSubImm .W64 .ADD .x20 .x20 (L.devNullStdAddr.truncate 12) false, .addSubImm .W64 .SUBS .xzr .x23 0x018#12 false, .bCond .EQ (0xffffffffffffff40#64 - ec), .addSubShift .W64 .ADD .x8 .x24 .x23 .LSL 0, .addSubImm .W64 .ADD .x23 .x23 0x008#12 false, .ldr .W32 .H16 false .x8 (.Offset .x8 0x06#64), .tbz .W32 false .x8 5 0xffffffffffffffec#64]
def cMainMidWithArgcInstrs (L : StdBinaryLayout) : List Instr := let b := L.cMainAddr + 0x1c4#64; let ec := cMainEcShiftWithArgc L; [.moveWide .W32 .MOVZ .x0 0x0d#16 0, .moveWide .W32 .MOVZ .x1 1#16 0, .bl (L.signalAddr - (b + 0x08#64)), .addSubImm .W64 .ADDS .xzr .x0 0x001#12 false, .bCond .EQ (0x100#64 + ec), .moveWide .W32 .MOVZ .x0 0x1e#16 0, .bl (L.sysconfAddr - (b + 0x18#64)), .adr true .x8 (adrpOff (b + 0x1c#64) L.pageSizeGlobalAddr), .adr true .x9 (adrpOff (b + 0x20#64) L.argcGlobalAddr), .str .X64 .x0 (.Offset .x8 (pageLo12 L.pageSizeGlobalAddr)), .adr true .x0 (adrpOff (b + 0x28#64) L.userMainAddr), .addSubImm .W64 .ADD .x0 .x0 (L.userMainAddr.truncate 12) false, .ldr .W64 .X64 false .xzr (.Offset .x8 (pageLo12 L.pageSizeGlobalAddr)), .adr true .x8 (adrpOff (b + 0x34#64) L.argvGlobalAddr), .str .X64 .x22 (.Offset .x9 (pageLo12 L.argcGlobalAddr)), .str .X64 .x19 (.Offset .x8 (pageLo12 L.argvGlobalAddr)), .bl (L.beginShortBacktraceAddr - (b + 0x40#64))]

/-- Code hypotheses required across `c_main` pre-user-`main` initialization and its callees. -/
structure LangStartPreCode (P : Program) (L : StdBinaryLayout) : Prop where
  svc_ok : P.svc = Syscall.standard ∨ P.svc = nonVmSvc
  signal_sigaction_off : L.signalAddr + 0x204#64 = L.sigactionAddr
  sccp_code : P.hasCode L.sccpAddr sccpWords
  syscallRet_code : P.hasCode L.syscallRetAddr syscallRetNonnegWords
  signal_code : P.hasCode L.signalAddr signalWords
  libcSigactionHead_code : P.hasCode L.libcSigactionAddr libcSigactionHeadWords
  sysconfEpilogue_code : P.hasCode (L.sysconfAddr + 0xd8#64) sysconfEpilogueWords
  beginShortBacktrace_code : P.hasCode L.beginShortBacktraceAddr beginShortBacktraceWords
  syscallCp_instrs : hasInstrs P L.syscallCpAddr (syscallCpInstrs L)
  poll_instrs : hasInstrs P L.pollAddr (pollInstrs L)
  sigaction_instrs : hasInstrs P L.sigactionAddr (sigactionFastInstrs L)
  libcSigactionTail_instrs : hasInstrs P (L.libcSigactionAddr + 0xfc#64) (libcSigactionIgnTailInstrs L)
  sysconf_instrs : hasInstrs P L.sysconfAddr (sysconfPagesizeInstrs L)
  cMain_instrs :
    if L.hasArgcGlobal then hasInstrs P L.cMainAddr (cMainPreWithArgcInstrs L) ∧ hasInstrs P (L.cMainAddr + (0x26c#64 + cMainEcShiftWithArgc L)) (cMainPollLoopWithArgcInstrs L) ∧ hasInstrs P (L.cMainAddr + 0x1c4#64) (cMainMidWithArgcInstrs L)
    else hasInstrs P L.cMainAddr (cMainPreNoArgcInstrs L) ∧ hasInstrs P (L.cMainAddr + (0x250#64 + cMainEcShiftNoArgc L)) (cMainPollLoopNoArgcInstrs L) ∧ hasInstrs P (L.cMainAddr + 0x1b8#64) (cMainMidNoArgcInstrs L)
section WordTreeCheck
open ProofLib.ProgramReflection
def checkLangStartWordsAt (base : BitVec 64) (t : WordTree) (addr : BitVec 64) (ws : List (BitVec 32)) : Bool := decide ((addr - base).toNat + 4 * ws.length ≤ 2 ^ 64) && checkWordsAt t (addr - base).toNat ws
def checkLangStartInstrsAt (base : BitVec 64) (t : WordTree) (addr : BitVec 64) (is : List Instr) : Bool := (base + BitVec.ofNat 64 (addr - base).toNat == addr) && decide ((addr - base).toNat + 4 * is.length < 2 ^ 64) && checkInstrsAt t (addr - base).toNat is
/-- $O(k \log N)$ boolean validator discharging `LangStartPreCode P L` from a `WordTree`. -/
def checkLangStartPreCode (L : StdBinaryLayout) (base : BitVec 64) (t : WordTree) : Bool :=
  (L.signalAddr + 0x204#64 == L.sigactionAddr) && checkLangStartWordsAt base t L.sccpAddr sccpWords && checkLangStartWordsAt base t L.syscallRetAddr syscallRetNonnegWords &&
  checkLangStartWordsAt base t L.signalAddr signalWords && checkLangStartWordsAt base t L.libcSigactionAddr libcSigactionHeadWords && checkLangStartWordsAt base t (L.sysconfAddr + 0xd8#64) sysconfEpilogueWords &&
  checkLangStartWordsAt base t L.beginShortBacktraceAddr beginShortBacktraceWords && checkLangStartInstrsAt base t L.syscallCpAddr (syscallCpInstrs L) && checkLangStartInstrsAt base t L.pollAddr (pollInstrs L) &&
  checkLangStartInstrsAt base t L.sigactionAddr (sigactionFastInstrs L) && checkLangStartInstrsAt base t (L.libcSigactionAddr + 0xfc#64) (libcSigactionIgnTailInstrs L) && checkLangStartInstrsAt base t L.sysconfAddr (sysconfPagesizeInstrs L) &&
  (if L.hasArgcGlobal then checkLangStartInstrsAt base t L.cMainAddr (cMainPreWithArgcInstrs L) && checkLangStartInstrsAt base t (L.cMainAddr + (0x26c#64 + cMainEcShiftWithArgc L)) (cMainPollLoopWithArgcInstrs L) && checkLangStartInstrsAt base t (L.cMainAddr + 0x1c4#64) (cMainMidWithArgcInstrs L)
   else checkLangStartInstrsAt base t L.cMainAddr (cMainPreNoArgcInstrs L) && checkLangStartInstrsAt base t (L.cMainAddr + (0x250#64 + cMainEcShiftNoArgc L)) (cMainPollLoopNoArgcInstrs L) && checkLangStartInstrsAt base t (L.cMainAddr + 0x1b8#64) (cMainMidNoArgcInstrs L))
theorem langStartPreCode_of_wordTree {P : Program} {L : StdBinaryLayout} {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n) (hsvc : P.svc = Syscall.standard := by rfl) (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl) (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl) (hok : checkLangStartPreCode L P.base t = true) : LangStartPreCode P L := by
  have hw : ∀ a ws, checkLangStartWordsAt P.base t a ws = true → P.hasCode a ws := fun a ws h => by simp only [checkLangStartWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h; exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
  have hi : ∀ a is, checkLangStartInstrsAt P.base t a is = true → hasInstrs P a is := fun a is h => by simp only [checkLangStartInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h; exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  unfold checkLangStartPreCode at hok; simp only [Bool.and_eq_true] at hok; rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsig, w1⟩, w2⟩, w3⟩, w4⟩, w5⟩, w6⟩, i1⟩, i2⟩, i3⟩, i4⟩, i5⟩, icm⟩
  refine ⟨Or.inl hsvc, beq_iff_eq.mp hsig, hw _ _ w1, hw _ _ w2, hw _ _ w3, hw _ _ w4, hw _ _ w5, hw _ _ w6, hi _ _ i1, hi _ _ i2, hi _ _ i3, hi _ _ i4, hi _ _ i5, ?_⟩
  by_cases h_argc : L.hasArgcGlobal <;> simp only [h_argc, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at icm ⊢ <;> exact ⟨hi _ _ icm.1.1, hi _ _ icm.1.2, hi _ _ icm.2⟩
end WordTreeCheck

theorem LangStartPreCode.withSvc_nonVm {P : Program} {L : StdBinaryLayout} (h : LangStartPreCode P L) :
    LangStartPreCode (P.withSvc nonVmSvc) L :=
  { h with svc_ok := Or.inr rfl }
theorem peel_instr0 {P : Program} {base : BitVec 64} {x : Instr} {xs : List Instr} {G : Prop}
    (hk : P.fetch base = some x → (∀ (k : Nat) (h : k < xs.length), P.fetch (base + (4#64 + BitVec.ofNat 64 (4 * k))) = some (xs[k]'h)) → G) (h : hasInstrs P base (x :: xs)) : G :=
  hk (by simpa using h 0 (Nat.zero_lt_succ _)) fun k h' => by have heq : base + (4#64 + BitVec.ofNat 64 (4 * k)) = base + BitVec.ofNat 64 (4 * (k + 1)) := (by bv_omega); simpa [heq] using h (k + 1) (Nat.succ_lt_succ h')
theorem peel_instrS {P : Program} {base off off' : BitVec 64} {x : Instr} {xs : List Instr} {G : Prop} (hoff : off + 4#64 = off')
    (hk : P.fetch (base + off) = some x → (∀ (k : Nat) (h : k < xs.length), P.fetch (base + (off' + BitVec.ofNat 64 (4 * k))) = some (xs[k]'h)) → G)
    (h : ∀ (k : Nat) (h : k < (x :: xs).length), P.fetch (base + (off + BitVec.ofNat 64 (4 * k))) = some ((x :: xs)[k]'h)) : G :=
  hk (by simpa using h 0 (Nat.zero_lt_succ _)) fun k h' => by have heq : base + (off' + BitVec.ofNat 64 (4 * k)) = base + (off + BitVec.ofNat 64 (4 * (k + 1))) := (by rw [← hoff]; bv_omega); simpa [heq] using h (k + 1) (Nat.succ_lt_succ h')
macro "unfold_stack_cells " k:num : tactic => `(tactic| (
  wp_conv_pre => simp only [Nat.reduceMul]; simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]; simp only [BitVec.ofNat_eq_ofNat]
  iterate $k (refine SepWP.exists_elim fun _ => ?_)))
macro "fold_stack_cells" : tactic => `(tactic| (simp (disch := decide) only [Nat.reduceMul, ProofLib.cells_sub_succ, Nat.reduceSub, BitVec.ofNat_eq_ofNat, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left]; sep_entail))

/-! ## Shared `musl` and `std` subroutine step contracts -/
/-- Non-memory process fields preserved across pre-`main` pure/poll subroutines (`fs`, `trace`, `tpidrEl0`, `sigActions`, `brk`, `brkStart`). -/
def PreMainFieldsPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.sigActions = s0.sigActions ∧ sf.brk = s0.brk ∧ sf.brkStart = s0.brkStart
theorem PreMainFieldsPreserved.rfl (s : State) : PreMainFieldsPreserved s s := ⟨_root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl⟩
theorem PreMainFieldsPreserved.trans {s0 s1 s2 : State} (h01 : PreMainFieldsPreserved s0 s1) (h12 : PreMainFieldsPreserved s1 s2) : PreMainFieldsPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1, h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1, h12.2.2.2.2.2.trans h01.2.2.2.2.2⟩
theorem StdStatePreserved.toPreMain {s0 sf : State} (h : StdStatePreserved s0 sf) : PreMainFieldsPreserved s0 sf := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
@[local simp] private theorem preMain_w64_r (a b : State) (r : Reg) (v : BitVec 64) : PreMainFieldsPreserved a (b.writeReg64 r v) ↔ PreMainFieldsPreserved a b := by cases r <;> rfl
@[local simp] private theorem preMain_w64_l (a b : State) (r : Reg) (v : BitVec 64) : PreMainFieldsPreserved (a.writeReg64 r v) b ↔ PreMainFieldsPreserved a b := by cases r <;> rfl
@[local simp] private theorem preMain_w32_r (a b : State) (r : Reg) (v : BitVec 32) : PreMainFieldsPreserved a (b.writeReg32 r v) ↔ PreMainFieldsPreserved a b := by simp [State.writeReg32]
@[local simp] private theorem preMain_w32_l (a b : State) (r : Reg) (v : BitVec 32) : PreMainFieldsPreserved (a.writeReg32 r v) b ↔ PreMainFieldsPreserved a b := by simp [State.writeReg32]
@[local simp] private theorem preMain_pc_r (a b : State) (p : BitVec 64) : PreMainFieldsPreserved a (b.setPC p) ↔ PreMainFieldsPreserved a b := Iff.rfl
@[local simp] private theorem preMain_pc_l (a b : State) (p : BitVec 64) : PreMainFieldsPreserved (a.setPC p) b ↔ PreMainFieldsPreserved a b := Iff.rfl
@[local simp] private theorem preMain_mem_r (a b : State) (m : Memory) : PreMainFieldsPreserved a (b.setMem m) ↔ PreMainFieldsPreserved a b := Iff.rfl
@[local simp] private theorem preMain_mem_l (a b : State) (m : Memory) : PreMainFieldsPreserved (a.setMem m) b ↔ PreMainFieldsPreserved a b := Iff.rfl
@[local simp] private theorem preMain_ps_r (a b : State) (p : PState) : PreMainFieldsPreserved a (b.setPState p) ↔ PreMainFieldsPreserved a b := Iff.rfl
@[local simp] private theorem preMain_ps_l (a b : State) (p : PState) : PreMainFieldsPreserved (a.setPState p) b ↔ PreMainFieldsPreserved a b := Iff.rfl
@[local simp] private theorem preMain_adv_r (a b : State) : PreMainFieldsPreserved a b.advancePC ↔ PreMainFieldsPreserved a b := Iff.rfl
@[local simp] private theorem preMain_adv_l (a b : State) : PreMainFieldsPreserved a.advancePC b ↔ PreMainFieldsPreserved a b := Iff.rfl
local macro "peelS " k:num : tactic => `(tactic| iterate $k (refine peel_instrS (by simp only [wp_norm]; rfl) fun _ => ?_))
local macro "peel1 " h:ident : tactic => `(tactic| refine peel_instrS (by simp only [wp_norm]; rfl) fun $h => ?_)
local macro "wn" : tactic => `(tactic| simp [wp_norm, arm64_norm, bv_lin_norm])
local macro "wnh " h:term : tactic => `(tactic| simp [wp_norm, arm64_norm, bv_lin_norm, $h:term])
local macro "sp_al " h:term : tactic => `(tactic| (simp [State.spAligned, wp_norm, arm64_norm, bv_lin_norm]; simpa [State.spAligned, beq_iff_eq] using $h))
local macro "pm_rfl " s:term : tactic => `(tactic| (simp only [preMain_w64_r, preMain_w32_r, preMain_pc_r, preMain_mem_r, preMain_ps_r, preMain_adv_r]; exact PreMainFieldsPreserved.rfl $s))
private theorem step_frame {P : Program} {t : BitVec 64} {s : State} {Pre A F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hw : SepWP P t s (A ∗ F) post oom) (h : ∀ R, s.mem ⊨ Pre ∗ R → s.mem ⊨ A ∗ (F ∗ R) := by intro R hm; sep_frame) : SepWP P t s Pre post oom :=
  SepWP.weaken_pre_frame (fun R hm => by rw [sepConj_assoc]; exact h R hm) hw
private theorem step_cut {P : Program} {t : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} (k : ∀ s', s' = s → SepWP P t s' Pre post oom) : SepWP P t s Pre post oom := k s rfl
private theorem step_entail {P : Program} {t : BitVec 64} {s : State} {Pre Q : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} (hw : SepWP P t s Q post oom) (h : ∀ R, s.mem ⊨ Pre ∗ R → s.mem ⊨ Q ∗ R) : SepWP P t s Pre post oom := SepWP.weaken_pre_frame h hw

/-- Packed 24-byte `struct pollfd[3]` array (`fd = 0, 1, 2`, `events = 0`, `revents = 0`). -/
def stdioPollfdBytes : List (BitVec 8) := unpack64 0#64 ++ unpack64 1#64 ++ unpack64 2#64
theorem evalPpollBytes_stdio3 {fs : FsState}
    (h0 : ∃ d, fs.fds 0#64 = some d ∧ (d.kind == .stdio || d.kind == .localFile) = true)
    (h1 : ∃ d, fs.fds 1#64 = some d ∧ (d.kind == .stdio || d.kind == .localFile) = true)
    (h2 : ∃ d, fs.fds 2#64 = some d ∧ (d.kind == .stdio || d.kind == .localFile) = true) :
    evalPpollBytes fs stdioPollfdBytes 0 = some (stdioPollfdBytes, 0) := by
  rcases h0 with ⟨d0, hd0, hk0⟩; rcases h1 with ⟨d1, hd1, hk1⟩; rcases h2 with ⟨d2, hd2, hk2⟩
  change evalPpollBytes fs [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 1#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 2#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] 0 = _; dsimp only [evalPpollBytes]
  change (match fs.fds 0#64 with | none => _ | some desc => _) = _; rw [hd0]; simp only [hk0, ↓reduceIte]
  change Option.map _ (match fs.fds 1#64 with | none => _ | some desc => _) = _; rw [hd1]; simp only [hk1, ↓reduceIte]
  change Option.map _ (Option.map _ (match fs.fds 2#64 with | none => _ | some desc => _)) = _; rw [hd2]; simp only [hk2, ↓reduceIte]; rfl
theorem evalPpollBytes_initFsState (inputs : ProcessInputs) : evalPpollBytes (initFsState inputs) stdioPollfdBytes 0 = some (stdioPollfdBytes, 0) :=
  evalPpollBytes_stdio3 ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩

/-- Step through `__syscall_ret` (`9` insns) when `x0 = 0#64`, leaving `x0 = 0#64`, `sp`, callee-saved registers `x19..x29`, `stackAt s.sp 0x20`, and `PreMainFieldsPreserved` unchanged. -/
theorem step_syscallRet_zero {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hcode : P.hasCode L.syscallRetAddr syscallRetNonnegWords) {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ stackAt s.sp 0x20 ∗ (F ∗ R))
    (hpc : s.pc = L.syscallRetAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → PreMainFieldsPreserved s sf →
      SepWP P target_pc sf (stackAt s.sp 0x20 ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine step_frame ?_ hpre
  have hsp_sub_align : ((s.sp + 0xffffffffffffffe0#64) &&& 0xf#64 == 0#64) = true := (by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align)
  have hhi : ConditionHolds CondCode.HI (addsPState64 0#64 4096#64) = false := (by dsimp [addsPState64, AddWithCarry64, ConditionHolds]; decide)
  rw [stackAt_eq_cells s.sp 4]; unfold_stack_cells 4; wp_steps
  exact step_entail (hnext _ rfl hrun rfl hsp_align (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by simp [arm64_norm, hx0]) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) fun R hm => by rw [stackAt_eq_cells s.sp 4]; fold_stack_cells

theorem stdioPollfds_eq_bytes (ufds : BitVec 64) : ((ufds ↦₆₄ 0#64) ∗ ((ufds + 8#64) ↦₆₄ 1#64) ∗ ((ufds + 16#64) ↦₆₄ 2#64)) = (ufds ↦ₛ stdioPollfdBytes) := by
  unfold stdioPollfdBytes; rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append]; simp only [unpack64_length, ← pointsTo64_eq_pointsToBytes]
  have h16 : ufds + 8#64 + 8#64 = ufds + 16#64 := (by bv_omega); rw [h16]
private theorem evalInst_svc_ppoll {P : Program} {s : State} (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc) (hx8 : s.readReg64 .x8 = 73#64) : P.evalInst (.system false 0#16) s = execPpoll s := by
  rcases hsvc with h | h
  · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_standard]; simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, hx8]
  · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_nonVmSvc]; simp [nonVmSvc, nonVmSyscallTable, Syscall.dispatch, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, hx8]
private theorem evalInst_svc_rt_sigaction {P : Program} {s : State} (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc) (hx8 : s.readReg64 .x8 = 134#64) : P.evalInst (.system false 0#16) s = execRtSigaction s := by
  rcases hsvc with h | h
  · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_standard]; simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, hx8]
  · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_nonVmSvc]; simp [nonVmSvc, nonVmSyscallTable, Syscall.dispatch, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.signalsTable, hx8]
private theorem step_b_to {P : Program} {target_pc pc dst : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.b (dst - pc))) (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) : SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.b (dst - pc)) _ rfl]; simp [wp_norm, arm64_norm]; rw [show pc + (dst - pc) = dst by bv_omega]) rfl hnext
private theorem step_bl_to {P : Program} {target_pc pc dst : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.bl (dst - pc))) (hnext : SepWP P target_pc ((s.writeReg64 .lr (pc + 4#64)).setPC dst) Pre post oom) : SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := (s.writeReg64 .lr (pc + 4#64)).setPC dst) hpc hrun hfetch (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bl (dst - pc)) _ rfl]; simp [wp_norm, arm64_norm]; rw [show pc + (dst - pc) = dst by bv_omega]) rfl hnext

/-- Step `__syscall_cp` (`1` insn) + `sccp` (`9` insns) for `ppoll(ufds, 3, tsp, 0)` (`x0 = 73`). -/
theorem step_syscallCp_sccp_ppoll {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc) (hcp : hasInstrs P L.syscallCpAddr (syscallCpInstrs L)) (hsccp : P.hasCode L.sccpAddr sccpWords)
    {s : State} {ufds tsp : BitVec 64} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ ((ufds ↦ₛ stdioPollfdBytes) ∗ ((tsp ↦₆₄ 0#64) ∗ ((tsp + 8#64) ↦₆₄ 0#64))) ∗ (F ∗ R))
    (hpc : s.pc = L.syscallCpAddr) (hrun : s.status = .Running) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = 73#64) (hx1 : s.readReg64 .x1 = ufds) (hx2 : s.readReg64 .x2 = 3#64) (hx3 : s.readReg64 .x3 = tsp) (hx4 : s.readReg64 .x4 = 0#64)
    (htsp_ne : tsp ≠ 0#64) (htsp_fit : tsp.toNat + 16 ≤ 2 ^ 64) (hufds_fit : ufds.toNat + 24 ≤ 2 ^ 64) (heval : evalPpollBytes s.fs stdioPollfdBytes 0 = some (stdioPollfdBytes, 0))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → PreMainFieldsPreserved s sf →
      SepWP P target_pc sf (((ufds ↦ₛ stdioPollfdBytes) ∗ ((tsp ↦₆₄ 0#64) ∗ ((tsp + 8#64) ↦₆₄ 0#64))) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := (ufds ↦ₛ stdioPollfdBytes) ∗ (((tsp ↦₆₄ 0#64) ∗ ((tsp + 8#64) ↦₆₄ 0#64)) ∗ F)) (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  refine step_b_to hpc hrun (by simpa [syscallCpInstrs] using hcp 0 (Nat.zero_lt_succ 0)) ?_; wp_steps 7
  refine SepWP.step_svc_ppoll (pc := L.sccpAddr + 28#64) (ufds := ufds) (tsp := tsp) (nfds := 3) (count := 0) (bs₀ := stdioPollfdBytes) (bs' := stdioPollfdBytes)
    (by wn) (by wnh hrun) (Program.fetch_of_hasCode_decodeAt 7 hsccp rfl (by decide)) (by wn) (by wn) (by wn) (by wn) (by wn) htsp_ne htsp_fit (by decide) hufds_fit (by decide) heval (fun m' => ?_) (evalInst_svc_ppoll hsvc (by wn))
  wp_steps 1; exact step_entail (hnext _ (by wn) (by wnh hrun) (by wn) (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by wn) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) fun R hm => by ac_nf at hm ⊢

/-- Step `poll(ufds, 3, 0)` (`29` insns) when stdio fds `0, 1, 2` are open, returning `x0 = 0#64`. -/
theorem step_poll_stdio3 {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hcode : LangStartPreCode P L) {s : State} {ufds : BitVec 64} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ (((ufds ↦₆₄ 0#64) ∗ ((ufds + 8#64) ↦₆₄ 1#64) ∗ ((ufds + 16#64) ↦₆₄ 2#64)) ∗ stackAt s.sp 0x40) ∗ (F ∗ R))
    (hpc : s.pc = L.pollAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0x40 ≤ s.sp.toNat) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ufds) (hx1 : s.readReg64 .x1 = 3#64) (hx2 : s.readReg32 .x2 = 0#32)
    (hufds_fit : ufds.toNat + 24 ≤ 2 ^ 64) (heval : evalPpollBytes s.fs stdioPollfdBytes 0 = some (stdioPollfdBytes, 0))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 → PreMainFieldsPreserved s sf →
      SepWP P target_pc sf ((((ufds ↦₆₄ 0#64) ∗ ((ufds + 8#64) ↦₆₄ 1#64) ∗ ((ufds + 16#64) ↦₆₄ 2#64)) ∗ stackAt s.sp 0x40) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine step_frame ?_ hpre; have hp := hcode.poll_instrs; dsimp only [pollInstrs] at hp; revert hp; refine peel_instr0 fun _ => ?_; peelS 24; peel1 hf25; peel1 hf26; peelS 2; intro _
  have hsp_sub_align : ((s.sp + 0xffffffffffffffe0#64) &&& 0xf#64 == 0#64) = true := (by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align); rw [State.readReg32, Reg.x2] at hx2
  rw [sepConj_assoc, stdioPollfds_eq_bytes ufds, stackAt_split_cells s.sp 0x20 4 (by decide)]; unfold_stack_cells 4; wp_steps 25
  refine step_bl_to (pc := L.pollAddr + 100#64) (dst := L.syscallCpAddr) (by wn) (by wnh hrun) hf25 ?_; have htsp8 : (s.sp - 8#64) = (s.sp - 16#64) + 8#64 := (by simp only [bv_lin_norm])
  wp_conv_pre => rw [htsp8]
  refine step_cut fun s0 hs0 => ?_; have hcs0 : CalleeSavedPreserved ((s.writeReg64 .sp (s.sp + 0xffffffffffffffe0#64)).writeReg64 (.gpr 29#5) (s.sp + 0xffffffffffffffe0#64)) s0 := (by subst hs0; simp (config := { decide := true }) only [arm64_norm])
  have hpr0 : PreMainFieldsPreserved s s0 := (by subst hs0; pm_rfl s); have hsp0 : s0.sp = s.sp - 32#64 := (by subst hs0; wn); have hrun0 : s0.status = .Running := (by subst hs0; wnh hrun)
  refine step_syscallCp_sccp_ppoll hcode.svc_ok hcode.syscallCp_instrs hcode.sccp_code (ufds := ufds) (tsp := s.sp - 16#64) (F := ?_) (fun R hm => by sep_frame) (by subst hs0; wn) hrun0 (by subst hs0; wn) (by subst hs0; wn) (by subst hs0; wn) (by subst hs0; wn) (by subst hs0; wn) (by subst hs0; wn) (by bv_omega) (by bv_omega) hufds_fit (by rw [hpr0.1]; exact heval) (ret_pc := L.pollAddr + 104#64) ?_
  intro s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hpr1; clear hs0; refine step_bl_to (pc := L.pollAddr + 104#64) (dst := L.syscallRetAddr) hpc1 hrun1 hf26 ?_
  have hsp1_eq : ((s1.writeReg64 .lr (L.pollAddr + 104#64 + 4#64)).setPC L.syscallRetAddr).sp = s.sp - 32#64 := (by simp [wp_norm, arm64_norm, hsp1, hsp0])
  refine step_syscallRet_zero hcode.syscallRet_code (F := ?_) (fun R hm => by rw [hsp1_eq]; sep_frame) rfl (by wnh hrun1) (by rw [State.spAligned, hsp1_eq]; exact s.spAligned_sub 0x20#64 hsp_align) (by wn) (by wnh hx0_1) (ret_pc := L.pollAddr + 108#64) ?_
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hx0_2 hpr2; have hsp2_eq : s2.sp = s.sp - 32#64 := hsp2.trans hsp1_eq; have h32 : s.sp - 32#64 = s2.sp := hsp2_eq.symm
  have h24 : s.sp - 24#64 = s2.sp + 8#64 := (by rw [hsp2_eq]; simp only [bv_lin_norm]); have hsp_end : s2.sp + 32#64 = s.sp := (by rw [hsp2_eq]; simp only [bv_lin_norm]); clear hsp2 hsp2_eq
  rw [State.spAligned] at hsp_al2; wp_conv_pre => rw [← htsp8, h32, h24]
  wp_steps 2; refine step_entail (hnext _ (by wn) (by wnh hrun2) (by wn) (by sp_al hsp_align) ?_ (by wnh hx0_2) (by simp only [preMain_w64_l, preMain_pc_l, preMain_w64_r, preMain_pc_r] at hpr2 ⊢; exact hpr0.trans (hpr1.trans hpr2))) (fun R hm => by rw [hsp1_eq, ← h24, ← h32] at hm; rw [stdioPollfds_eq_bytes ufds, stackAt_split_cells s.sp 0x20 4 (by decide)]; fold_stack_cells)
  simp (config := { decide := true }) only [arm64_norm] at hcs2 ⊢; exact CalleeSavedPreserved.restore (s0 := s) (s2 := s2.writeReg64 .sp s.sp) (hcs0.trans (hcs1.trans hcs2))

/-- Step the 3-instruction entry of `__rust_begin_short_backtrace` up to `L.userMainAddr`. -/
theorem step_beginShortBacktrace_enter {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hcode : P.hasCode L.beginShortBacktraceAddr beginShortBacktraceWords) {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ stackAt s.sp 0x10 ∗ (F ∗ R))
    (hpc : s.pc = L.beginShortBacktraceAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = L.userMainAddr)
    (hnext : ∀ sf : State, sf.pc = L.userMainAddr → sf.status = .Running → sf.sp = s.sp - 16#64 → sf.spAligned = true →
      sf.readReg64 .x29 = s.sp - 16#64 → sf.readReg64 .lr = L.beginShortBacktraceAddr + 12#64 →
      CalleeSavedPreserved (s.writeReg64 (.gpr 29#5) (s.sp - 16#64)) sf → PreMainFieldsPreserved s sf →
      SepWP P target_pc sf ((((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 8#64) ↦₆₄ ret_pc)) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine step_frame ?_ hpre; have hsp_sub_align : ((s.sp + 0xfffffffffffffff0#64) &&& 0xf#64 == 0#64) = true := (by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x10#64 hsp_align); wp_conv_pre => rw [stackAt_eq_cells s.sp 2]
  unfold_stack_cells 2; wp_steps 3
  exact hnext _ (by wn) (by wnh hrun) (by wn) (by sp_al hsp_align) (by wn) (by wn) (by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm]; exact CalleeSavedPreserved.rfl _) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Step `sysconf(30)` (`_SC_PAGESIZE`, `31` insns) reading `(L.libcAddr + 0x30#64) ↦₆₄ 4096#64`. -/
theorem step_sysconf_pagesize {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hsys : hasInstrs P L.sysconfAddr (sysconfPagesizeInstrs L)) (hepi : P.hasCode (L.sysconfAddr + 0xd8#64) sysconfEpilogueWords)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ (((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s.sp 0x190) ∗ (F ∗ R))
    (hpc : s.pc = L.sysconfAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 30#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf → sf.readReg64 .x0 = 4096#64 → PreMainFieldsPreserved s sf →
      SepWP P target_pc sf ((((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s.sp 0x190) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine step_frame ?_ hpre; have hp := hsys; dsimp only [sysconfPagesizeInstrs] at hp; revert hp; refine peel_instr0 fun _ => ?_; peelS 28; intro _
  have hsp_sub_align : ((s.sp + 0xfffffffffffffe70#64) &&& 0xf#64 == 0#64) = true := (by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x190#64 hsp_align)
  have hge : ConditionHolds CondCode.GE (addsPState32 0xffffff04#32 1#32) = false := (by unfold addsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide)
  have hlt : ConditionHolds CondCode.LT (addsPState32 0xffffff04#32 256#32) = false := (by unfold addsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide)
  have he0 : P.fetch (L.sysconfAddr + 216#64) = some (.ldp .W64 false .x29 .lr (.PostIndex .sp 400#64)) := Program.fetch_of_hasCode_decodeAt 0 hepi (by simp only [wp_norm]) (by decide)
  have he1 : P.fetch (L.sysconfAddr + 220#64) = some (.ret .lr) := Program.fetch_of_hasCode_decodeAt 1 hepi (by simp only [wp_norm]) (by decide)
  clear hepi; wp_conv_pre => rw [stackAt_split_bottom s.sp 0x170 32 (by decide), memRegion_cells (s.sp - 0x190#64) 4 (by decide)]
  unfold_stack_cells 4; wp_steps 31
  refine step_entail (hnext _ (by wn) (by wnh hrun) (by wn) (by sp_al hsp_align) (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by wn) (by pm_rfl s)) (fun R hm => by rw [stackAt_split_bottom s.sp 0x170 32 (by decide), memRegion_cells (s.sp - 0x190#64) 4 (by decide)]; fold_stack_cells)

/-- Signal disposition installed for `SIGPIPE` (`13`) by `reset_sigpipe` (`signal(13, SIG_IGN)`). -/
def sigpipeIgnAction (L : StdBinaryLayout) : SigAction := { handler := 1#64, flags := 0x14000000#64, restorer := L.restoreRtAddr, mask := 0#64 }
private theorem fourCells_eq_bytes (a v0 v1 v2 v3 : BitVec 64) : ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3)) = (a ↦ₛ (unpack64 v0 ++ unpack64 v1 ++ unpack64 v2 ++ unpack64 v3)) := by
  rw [List.append_assoc, List.append_assoc, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]; simp only [unpack64_length, ← pointsTo64_eq_pointsToBytes]
  rw [show a + 8#64 + 8#64 = a + 16#64 by simp only [bv_lin_norm], show a + 16#64 + 8#64 = a + 24#64 by simp only [bv_lin_norm]]
@[local simp] private theorem calleeSavedVRegs_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) : calleeSavedVRegs (s.setSigAction sig act) = calleeSavedVRegs s := rfl

/-- Step `__libc_sigaction(13, act, oact)` (`SIG_IGN`, `SA_RESTART`), installing `sigpipeIgnAction L` and returning `0#64`. -/
theorem step_libcSigaction_ign {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hcode : LangStartPreCode P L) (ops : StdMemOps P L.memcpyAddr L.memsetAddr)
    {s : State} {act oact v0 v1 v17 : BitVec 64} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ (((act ↦₆₄ 1#64) ∗ ((act + 8#64) ↦₆₄ 0#64) ∗ ((act + 0x88#64) ↦₆₄ 0x10000000#64)) ∗ ((oact ↦₆₄ v0) ∗ ((oact + 8#64) ↦₆₄ v1) ∗ ((oact + 0x88#64) ↦₆₄ v17)) ∗ stackAt s.sp 0x90) ∗ (F ∗ R))
    (hpc : s.pc = L.libcSigactionAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0x90 ≤ s.sp.toNat)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 13#64) (hx1 : s.readReg64 .x1 = act) (hx2 : s.readReg64 .x2 = oact)
    (hact_ne : act ≠ 0#64) (hoact_ne : oact ≠ 0#64) (hsig0 : s.getSigAction 13#32 = {})
    (hnext : ∀ (sf : State) (v17' : BitVec 64), sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → PreMainFieldsPreserved (s.setSigAction 13#32 (sigpipeIgnAction L)) sf →
      SepWP P target_pc sf ((((act ↦₆₄ 1#64) ∗ ((act + 8#64) ↦₆₄ 0#64) ∗ ((act + 0x88#64) ↦₆₄ 0x10000000#64)) ∗ ((oact ↦₆₄ 0#64) ∗ ((oact + 8#64) ↦₆₄ 0#64) ∗ ((oact + 0x88#64) ↦₆₄ v17')) ∗ stackAt s.sp 0x90) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := (((act ↦₆₄ 1#64) ∗ ((act + 8#64) ↦₆₄ 0#64) ∗ ((act + 0x88#64) ↦₆₄ 0x10000000#64)) ∗ ((oact ↦₆₄ v0) ∗ memRegion (oact + 8#64) 8 ∗ ((oact + 0x88#64) ↦₆₄ v17)) ∗ stackAt s.sp 0x90) ∗ F) (fun R hm => by replace hm := hpre R hm; rw [memRegion_eight]; sep_entail) ?_
  have hhead := hcode.libcSigactionHead_code; have hp := hcode.libcSigactionTail_instrs; dsimp only [libcSigactionIgnTailInstrs] at hp; generalize hb : L.libcSigactionAddr + 0xfc#64 = b at hp; revert hp
  refine peel_instr0 fun _ => ?_; peelS 14; peel1 hf15; peelS 7; peel1 hf23; peelS 5; peel1 hf29; peelS 11; peel1 hf41; peelS 1; intro _
  have hsp_sub_al : ((s.sp + 0xffffffffffffff90#64) &&& 0xf#64 == 0#64) = true := (by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align); have hact_f : (act == 0#64) = false := beq_false_of_ne hact_ne
  wp_conv_pre => rw [stackAt_split_cells s.sp 0x20 14 (by decide), cells_split_sub s.sp 112 40 9 5, cells_split_sub s.sp 40 32 1 4, ← memRegion_cells (s.sp - BitVec.ofNat 64 40) 1 (by decide)]; simp only [Nat.reduceMul]; simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun w10 => SepWP.exists_elim fun w11 => SepWP.exists_elim fun w12 => SepWP.exists_elim fun w13 => ?_; iterate 9 (refine SepWP.exists_elim fun _ => ?_)
  wp_steps 12; clear hhead; wp_steps 15; refine step_bl_to (pc := b + 60#64) (dst := L.memcpyAddr) (by wn) (by wnh hrun) hf15 ?_; refine step_cut fun s0 hs0 => ?_
  have ⟨hpc0, hrun0, hsp0, hsp_al0, hlr0, hx0_0, hx1_0, hx2_0, hx19_0, hx20_0, hx21_0⟩ : s0.pc = L.memcpyAddr ∧ s0.status = .Running ∧ s0.sp = s.sp - 112#64 ∧ s0.spAligned = true ∧ s0.readReg64 .lr = L.libcSigactionAddr + 316#64 ∧ s0.readReg64 .x0 = s.sp - 40#64 ∧ s0.readReg64 .x1 = act + 8#64 ∧ s0.readReg64 .x2 = 8#64 ∧ s0.readReg64 .x19 = s.sp - 64#64 ∧ s0.readReg64 .x20 = oact ∧ s0.readReg64 .x21 = 13#64 :=
    (by rw [hs0]; refine ⟨by wn, by wnh hrun, by wn, by sp_al hsp_align, by rw [← hb]; wn, by wn, by wn, by wn, by wn, by wnh hx2, by wnh hx0⟩)
  have hcs0 : CalleeSavedPreserved (((((s.writeReg64 .sp (s.sp - 112#64)).writeReg64 (.gpr 29#5) (s.sp - 112#64)).writeReg64 (.gpr 19#5) (s.sp - 64#64)).writeReg64 (.gpr 20#5) oact).writeReg64 (.gpr 21#5) 13#64) s0 :=
    (by rw [hs0]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, bv_lin_norm])
  have hpre0 : PreMainFieldsPreserved s s0 := (by rw [hs0]; pm_rfl s); clear hs0 hf15 hpc hlr hx0 hx1 hx2 hsp_sub_al hact_f; wp_conv_pre => rw [pointsTo64_eq_pointsToBytes (act + 8#64) 0#64]
  refine ops.call_memcpy (ret_pc := L.libcSigactionAddr + 316#64) (dst := s.sp - 40#64) (src := act + 8#64) (bs := unpack64 0#64) (F := ?_) (fun R hm => by dsimp only [unpack64_length] at *; revert hm; sep_frame) (fun s1 hpc1 hrun1 hsp1 hcs1 _ hstd1 => ?_) hpc0 hrun0 hsp_al0 hlr0 hx0_0 hx1_0 (by simp [unpack64_length, hx2_0]) (by simp [unpack64_length])
  wp_conv_pre => simp only [← pointsTo64_eq_pointsToBytes]
  have hsp1_eq : s1.sp = s.sp - 112#64 := hsp1.trans hsp0; have hpre01 : PreMainFieldsPreserved s s1 := hpre0.trans hstd1.toPreMain; have hsig1 : s1.getSigAction 13#32 = {} := (by rw [State.getSigAction, hpre01.2.2.2.1, ← State.getSigAction, hsig0])
  have hx19_1 : s1.readReg64 .x19 = s.sp - 64#64 := hcs1.1.trans hx19_0; have hx20_1 : s1.readReg64 .x20 = oact := hcs1.2.1.trans hx20_0; have hx21_1 : s1.readReg64 .x21 = 13#64 := hcs1.2.2.1.trans hx21_0
  have hpc1_b : s1.pc = b + 64#64 := (by rw [hpc1, ← hb]; simp only [bv_lin_norm]); have hsp_al1 : s1.spAligned = true := (by rw [State.spAligned, hsp1]; simpa [State.spAligned] using hsp_al0); clear hpc1; rw [State.spAligned] at hsp_al1
  have ho_bne : (oact != 0#64) = true := bne_iff_ne.mpr hoact_ne; have hk_f : ((s.sp - 64#64) == 0#64) = false := beq_false_of_ne (by bv_omega); have ho_f : ((s1.sp + 80#64) == 0#64) = false := beq_false_of_ne (by rw [hsp1_eq]; bv_omega)
  have ka1 : (s.sp - 64#64) + 8#64 = s.sp - 56#64 := (by simp only [bv_lin_norm]); have ka2 : (s.sp - 64#64) + 16#64 = s.sp - 48#64 := (by simp only [bv_lin_norm]); have ka3 : (s.sp - 64#64) + 24#64 = s.sp - 40#64 := (by simp only [bv_lin_norm])
  have ko0 : s1.sp + 80#64 = s.sp - 32#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm]); have ko1 : s1.sp + 80#64 + 8#64 = s.sp - 24#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm]); have ko2 : s1.sp + 80#64 + 16#64 = s.sp - 16#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm]); have ko3 : s1.sp + 80#64 + 24#64 = s.sp - 8#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm])
  have oa1 : s1.sp + 80#64 + 8#64 = s1.sp + 88#64 := (by simp only [bv_lin_norm]); have oa2 : s1.sp + 80#64 + 16#64 = s1.sp + 96#64 := (by simp only [bv_lin_norm]); have oa3 : s1.sp + 80#64 + 24#64 = s1.sp + 104#64 := (by simp only [bv_lin_norm])
  wp_steps 7; refine step_frame (A := kSigActionAt (s.sp - 64#64) 1#64 0x14000000#64 L.restoreRtAddr 0#64 ∗ optOldSigActionAt (s1.sp + 80#64) (unpack64 w10 ++ unpack64 w11 ++ unpack64 w12 ++ unpack64 w13)) (F := ?_) ?_
    (fun R hm => by dsimp only [kSigActionAt, optOldSigActionAt]; rw [hk_f, ho_f]; simp only [Bool.false_eq_true, ↓reduceIte, ← fourCells_eq_bytes]; rw [ka1, ka2, ka3, ko1, ko2, ko3, ko0]; revert hm; sep_frame)
  rw [sepConj_assoc]; refine SepWP.step_svc_rt_sigaction (pc := b + 92#64) (signum := 13#32) (act := s.sp - 64#64) (handler := 1#64) (flags := 0x14000000#64) (restorer := L.restoreRtAddr) (mask := 0#64) (oldact := s1.sp + 80#64) (oldBs₀ := unpack64 w10 ++ unpack64 w11 ++ unpack64 w12 ++ unpack64 w13) (by wn) (by wnh hrun1) hf23 (by wn) (by wn) (by wn) (by wnh hsp1_eq) (by wn) (by decide) (by decide) (Or.inr ⟨by decide, by decide, by bv_omega, Or.inr rfl⟩) (Or.inr ⟨by rw [hsp1_eq]; bv_omega, by simp [unpack64_length]⟩) (fun m' => ?_) (evalInst_svc_rt_sigaction hcode.svc_ok (by wn))
  dsimp only []; have hsig_m : ((((((((s1.writeReg64 (.gpr 1#5) (s.sp - 64#64)).writeReg64 (.gpr 4#5) (s.sp - 32#64)).writeReg64 (.gpr 0#5) 13#64).writeReg64 (.gpr 2#5) (s.sp - 32#64)).writeReg64 (.gpr 8#5) 134#64).writeReg64 (.gpr 3#5) 8#64).setPState (subsPState64 oact 0#64)).setPC (b + 92#64)).getSigAction 13#32 = {} := hsig1
  wp_conv_pre => dsimp only [kSigActionAt, optOldSigActionAt]; rw [hsig_m, hk_f, ho_f]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [show ({} : SigAction).toBytes = unpack64 0#64 ++ unpack64 0#64 ++ unpack64 0#64 ++ unpack64 0#64 from rfl, ← fourCells_eq_bytes, ka1, ka2, ka3, oa1, oa2, oa3]
  conv => arg 3; rw [hk_f]; simp only [Bool.false_eq_true, ↓reduceIte, show (0#64 &&& ~~~SIG_UNBLOCKABLE_MASK) = 0#64 from rfl]
  wp_steps 11; refine step_bl_to (pc := b + 164#64) (dst := L.memcpyAddr) (by wn) (by wnh hrun1) hf41 ?_; refine step_cut fun s2 hs2 => ?_
  have ⟨hpc2, hrun2, hsp2, hsp_al2, hlr2, hx0_2, hx1_2, hx2_2, hx19_2⟩ : s2.pc = L.memcpyAddr ∧ s2.status = .Running ∧ s2.sp = s1.sp ∧ s2.spAligned = true ∧ s2.readReg64 .lr = L.libcSigactionAddr + 420#64 ∧ s2.readReg64 .x0 = oact + 8#64 ∧ s2.readReg64 .x1 = s1.sp + 104#64 ∧ s2.readReg64 .x2 = 8#64 ∧ s2.readReg64 .x19 = 0#64 :=
    (by rw [hs2]; refine ⟨by wn, by wnh hrun1, by wn, by simp [State.spAligned, wp_norm, arm64_norm, hsp_al1], by rw [← hb]; wn, by wn, by wnh hsp1_eq, by wn, by wn⟩)
  have hcs2 : CalleeSavedPreserved (s1.writeReg64 (.gpr 19#5) 0#64) s2 := (by rw [hs2]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
  have hpre2 : PreMainFieldsPreserved (s1.setSigAction 13#32 (sigpipeIgnAction L)) s2 := (by rw [hs2]; simp only [preMain_w64_r, preMain_pc_r, preMain_mem_r, preMain_ps_r]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  clear hs2 hf23 hf41; wp_conv_pre => rw [pointsTo64_eq_pointsToBytes (s1.sp + 104#64) 0#64]
  refine ops.call_memcpy (ret_pc := L.libcSigactionAddr + 420#64) (dst := oact + 8#64) (src := s1.sp + 104#64) (bs := unpack64 0#64) (F := ?_) (fun R hm => by dsimp only [unpack64_length] at *; revert hm; sep_frame) (fun s3 hpc3 hrun3 hsp3 hcs3 _ hstd3 => ?_) hpc2 hrun2 hsp_al2 hlr2 hx0_2 hx1_2 (by simp [unpack64_length, hx2_2]) (by simp [unpack64_length])
  wp_conv_pre => simp only [← pointsTo64_eq_pointsToBytes]
  have hsp3_eq : s3.sp = s.sp - 112#64 := hsp3.trans (hsp2.trans hsp1_eq); have hx19_3 : s3.readReg64 .x19 = 0#64 := hcs3.1.trans hx19_2; have hpc3_b : s3.pc = b + 168#64 := (by rw [hpc3, ← hb]; simp only [bv_lin_norm]); clear hpc3
  wp_steps 2; refine step_bl_to (pc := b + 116#64) (dst := L.syscallRetAddr) (by wn) (by wnh hrun3) hf29 ?_; refine step_cut fun s3' hs3' => ?_; have hsp3' : s3'.sp = s.sp - 112#64 := (by rw [hs3']; wnh hsp3_eq)
  refine step_syscallRet_zero hcode.syscallRet_code (ret_pc := b + 120#64) (F := ?_) (fun R hm => by rw [hsp3']; revert hm; sep_frame) (by rw [hs3']; wn) (by rw [hs3']; wnh hrun3) (by rw [State.spAligned, hsp3']; exact s.spAligned_sub 0x70#64 hsp_align) (by rw [hs3']; wn) (by rw [hs3']; wn) fun s4 hpc4 hrun4 hsp4 hsp_al4 hcs4_raw hx0_4 hpre4_raw => ?_
  have hcs4 : CalleeSavedPreserved s3 s4 := (by rw [hs3'] at hcs4_raw; simpa [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] using hcs4_raw); have hpre4 : PreMainFieldsPreserved s3 s4 := (by rw [hs3'] at hpre4_raw; simpa [preMain_w64_l, preMain_pc_l] using hpre4_raw)
  have hsp4_eq : s4.sp = s.sp - 112#64 := hsp4.trans hsp3'; clear hs3' hsp4 hf29 hcode ops; rw [State.spAligned] at hsp_al4; have hsp_add_al : ((s4.sp + 112#64) &&& 15#64 == 0#64) = true := (by simp only [beq_iff_eq] at hsp_al4 ⊢; bv_bits)
  have e0 : s.sp - 112#64 = s4.sp := hsp4_eq.symm; have e1 : s.sp - 104#64 = s4.sp + 8#64 := (by rw [hsp4_eq]; simp only [bv_lin_norm]); have e2 : s.sp - 96#64 = s4.sp + 16#64 := (by rw [hsp4_eq]; simp only [bv_lin_norm])
  have e3 : s.sp - 88#64 = s4.sp + 24#64 := (by rw [hsp4_eq]; simp only [bv_lin_norm]); have e4 : s.sp - 80#64 = s4.sp + 32#64 := (by rw [hsp4_eq]; simp only [bv_lin_norm]); have hsp_end : s4.sp + 112#64 = s.sp := (by rw [hsp4_eq]; simp only [bv_lin_norm])
  clear hsp4_eq; wp_conv_pre => rw [e0, e1, e2, e3, e4]
  wp_steps 4; have hpre_sig : PreMainFieldsPreserved (s.setSigAction 13#32 (sigpipeIgnAction L)) (s1.setSigAction 13#32 (sigpipeIgnAction L)) := ⟨hpre01.1, hpre01.2.1, hpre01.2.2.1, by dsimp only [State.setSigAction]; rw [hpre01.2.2.2.1], hpre01.2.2.2.2.1, hpre01.2.2.2.2.2⟩
  refine step_entail (hnext _ _ (by wn) (by wnh hrun4) (by wn) (by sp_al hsp_align) (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] at hcs0 hcs1 hcs2 hcs3 hcs4 ⊢; simp [hcs0, hcs1, hcs2, hcs3, hcs4]) (by wnh hx0_4) (hpre_sig.trans (hpre2.trans (hstd3.toPreMain.trans (hpre4.trans (by pm_rfl s4))))))
    (fun R hm => by rw [← e4, ← e3, ← e2, ← e1, ← e0, ← oa1, ← oa2, ← oa3, ko1, ko2, ko3, ko0, hsp3'] at hm; rw [stackAt_split_cells s.sp 0x20 14 (by decide)]; fold_stack_cells)
/-- Step through `sigaction(13, act, oact)` fast path (`17` insns + `__libc_sigaction`), returning `x0 = 0#64`. -/
theorem step_sigaction_fast13 {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hcode : LangStartPreCode P L) (ops : StdMemOps P L.memcpyAddr L.memsetAddr)
    {s : State} {act oact v0 v1 v17 : BitVec 64} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ (((act ↦₆₄ 1#64) ∗ ((act + 8#64) ↦₆₄ 0#64) ∗ ((act + 0x88#64) ↦₆₄ 0x10000000#64)) ∗ ((oact ↦₆₄ v0) ∗ ((oact + 8#64) ↦₆₄ v1) ∗ ((oact + 0x88#64) ↦₆₄ v17)) ∗ stackAt s.sp 0xe0) ∗ (F ∗ R))
    (hpc : s.pc = L.sigactionAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0xe0 ≤ s.sp.toNat)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 13#64) (hx1 : s.readReg64 .x1 = act) (hx2 : s.readReg64 .x2 = oact)
    (hact_ne : act ≠ 0#64) (hoact_ne : oact ≠ 0#64) (hsig0 : s.getSigAction 13#32 = {})
    (hnext : ∀ (sf : State) (v17' : BitVec 64), sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → PreMainFieldsPreserved (s.setSigAction 13#32 (sigpipeIgnAction L)) sf →
      SepWP P target_pc sf ((((act ↦₆₄ 1#64) ∗ ((act + 8#64) ↦₆₄ 0#64) ∗ ((act + 0x88#64) ↦₆₄ 0x10000000#64)) ∗ ((oact ↦₆₄ 0#64) ∗ ((oact + 8#64) ↦₆₄ 0#64) ∗ ((oact + 0x88#64) ↦₆₄ v17')) ∗ stackAt s.sp 0xe0) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine step_frame ?_ hpre; have hp := hcode.sigaction_instrs; dsimp only [sigactionFastInstrs] at hp; revert hp; refine peel_instr0 fun _ => ?_; peelS 10; peel1 hf11; peelS 5; intro _
  have hsp_sub_al : ((s.sp + 0xffffffffffffffb0#64) &&& 0xf#64 == 0#64) = true := (by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x50#64 hsp_align)
  have hls1 : ConditionHolds .LS (subsPState32 12#32 63#32) = true := (by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide)
  have hls2 : ConditionHolds .LS (subsPState32 0xffffffed#32 2#32) = false := (by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide)
  wp_conv_pre => rw [stackAt_split_cells s.sp 0x90 10 (by decide), cells_split_sub s.sp 80 48 4 6, ← memRegion_cells (s.sp - BitVec.ofNat 64 48) 6 (by decide)]
  unfold_stack_cells 4; wp_steps 11; refine step_bl_to (pc := L.sigactionAddr + 44#64) (dst := L.libcSigactionAddr) (by wn) (by wnh hrun) hf11 ?_; refine step_cut fun s0 hs0 => ?_
  have ⟨hpc0, hrun0, hsp0, hsp_al0, hlr0, hx0_0, hx1_0, hx2_0⟩ : s0.pc = L.libcSigactionAddr ∧ s0.status = .Running ∧ s0.sp = s.sp - 80#64 ∧ s0.spAligned = true ∧ s0.readReg64 .lr = L.sigactionAddr + 48#64 ∧ s0.readReg64 .x0 = 13#64 ∧ s0.readReg64 .x1 = act ∧ s0.readReg64 .x2 = oact :=
    (by rw [hs0]; refine ⟨by wn, by wnh hrun, by wn, by sp_al hsp_align, by wn, by wnh hx0, by wnh hx1, by wnh hx2⟩)
  have hcs0 : CalleeSavedPreserved (((s.writeReg64 .sp (s.sp - 80#64)).writeReg64 (.gpr 29#5) (s.sp - 80#64)).writeReg64 (.gpr 19#5) 13#64) s0 := (by rw [hs0]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, bv_lin_norm])
  have hpre0 : PreMainFieldsPreserved s s0 := (by rw [hs0]; pm_rfl s); clear hs0 hf11 hpc hlr hx0 hx1 hx2 hsp_sub_al hls1 hls2; have hsig_s0 : s0.getSigAction 13#32 = {} := (by rw [State.getSigAction, hpre0.2.2.2.1, ← State.getSigAction, hsig0])
  refine step_libcSigaction_ign hcode ops (ret_pc := L.sigactionAddr + 48#64) (F := ?_) (fun R hm => by rw [hsp0]; revert hm; sep_frame) hpc0 hrun0 hsp_al0 (by rw [hsp0]; bv_omega) hlr0 hx0_0 hx1_0 hx2_0 hact_ne hoact_ne hsig_s0 fun s1 v17' hpc1 hrun1 hsp1 hsp_al1 hcs1 hx0_1 hpre1 => ?_
  clear hcode; have hsp1_eq : s1.sp = s.sp - 80#64 := hsp1.trans hsp0; have hc0 : s.sp - 80#64 = s1.sp := hsp1_eq.symm
  have hc1 : s.sp - 72#64 = s1.sp + 8#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm]); have hc2 : s.sp - 64#64 = s1.sp + 16#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm])
  have hc3 : s.sp - 56#64 = s1.sp + 24#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm]); have hsp_end : s1.sp + 80#64 = s.sp := (by rw [hsp1_eq]; simp only [bv_lin_norm]); clear hsp1 hsp1_eq; rw [State.spAligned] at hsp_al1
  have hsp_add_al : ((s1.sp + 80#64) &&& 15#64 == 0#64) = true := (by simp only [beq_iff_eq] at hsp_al1 ⊢; bv_bits); wp_conv_pre => rw [hc0, hc1, hc2, hc3]
  wp_steps 5; have hpre_sig : PreMainFieldsPreserved (s.setSigAction 13#32 (sigpipeIgnAction L)) (s0.setSigAction 13#32 (sigpipeIgnAction L)) := ⟨hpre0.1, hpre0.2.1, hpre0.2.2.1, by dsimp only [State.setSigAction]; rw [hpre0.2.2.2.1], hpre0.2.2.2.2.1, hpre0.2.2.2.2.2⟩
  refine step_entail (hnext _ v17' (by wn) (by wnh hrun1) (by wn) (by sp_al hsp_align) (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] at hcs0 hcs1 ⊢; simp [hcs0, hcs1]) (by wn) (hpre_sig.trans (hpre1.trans (by pm_rfl s1))))
    (fun R hm => by rw [← hc3, ← hc2, ← hc1, ← hc0, hsp0] at hm; rw [stackAt_split_cells s.sp 0x90 10 (by decide), cells_split_sub s.sp 80 48 4 6, ← memRegion_cells (s.sp - BitVec.ofNat 64 48) 6 (by decide)]; fold_stack_cells)
/-- Step through `signal(13, SIG_IGN)` (`23` insns + `sigaction` + `__libc_sigaction`), returning `0#64` in `x0`. -/
theorem step_signal_sigpipe_ign {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hcode : LangStartPreCode P L) (ops : StdMemOps P L.memcpyAddr L.memsetAddr)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ stackAt s.sp 0x220 ∗ (F ∗ R))
    (hpc : s.pc = L.signalAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0x220 ≤ s.sp.toNat)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 13#64) (hx1 : s.readReg64 .x1 = 1#64) (hsig0 : s.getSigAction 13#32 = {})
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → PreMainFieldsPreserved (s.setSigAction 13#32 (sigpipeIgnAction L)) sf → SepWP P target_pc sf (stackAt s.sp 0x220 ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine step_frame ?_ hpre; have hsig_code := hcode.signal_code; have hoff := hcode.signal_sigaction_off
  have hsp_sub_al : ((s.sp + 0xfffffffffffffec0#64) &&& 0xf#64 == 0#64) = true := (by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x140#64 hsp_align)
  have hf17 : P.fetch (L.signalAddr + 68#64) = some (.bl 448#64) := Program.fetch_of_hasCode_decodeAt 17 hsig_code (by simp only [wp_norm]) (by decide)
  wp_conv_pre => rw [stackAt_split_cells s.sp 0xe0 40 (by decide), cells_split_sub s.sp 320 288 4 36, cells_split_sub s.sp 288 168 15 21, cells_split_sub s.sp 168 160 1 20, cells_split_sub s.sp 160 152 1 19, ← memRegion_cells (s.sp - BitVec.ofNat 64 288) 15 (by decide), ← memRegion_cells (s.sp - BitVec.ofNat 64 160) 1 (by decide)]
  unfold_stack_cells 24; wp_steps 17; refine step_bl_to (pc := L.signalAddr + 68#64) (dst := L.sigactionAddr) (by wn) (by wnh hrun) (by rw [show L.sigactionAddr - (L.signalAddr + 68#64) = 448#64 by rw [← hoff]; simp only [bv_lin_norm]]; exact hf17) ?_; refine step_cut fun s0 hs0 => ?_
  have ⟨hpc0, hrun0, hsp0, hsp_al0, hlr0, hx0_0, hx1_0, hx2_0⟩ : s0.pc = L.sigactionAddr ∧ s0.status = .Running ∧ s0.sp = s.sp - 320#64 ∧ s0.spAligned = true ∧ s0.readReg64 .lr = L.signalAddr + 72#64 ∧ s0.readReg64 .x0 = 13#64 ∧ s0.readReg64 .x1 = s.sp - 152#64 ∧ s0.readReg64 .x2 = s.sp - 304#64 :=
    (by rw [hs0]; refine ⟨by wn, by wnh hrun, by wn, by sp_al hsp_align, by wn, by wnh hx0, by wn, by wn⟩)
  have hcs0 : CalleeSavedPreserved ((s.writeReg64 .sp (s.sp - 320#64)).writeReg64 (.gpr 29#5) (s.sp - 320#64)) s0 := (by rw [hs0]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
  have hpre0 : PreMainFieldsPreserved s s0 := (by rw [hs0]; pm_rfl s); clear hs0 hf17 hoff hpc hlr hx0 hx1 hsp_sub_al; have hsig_s0 : s0.getSigAction 13#32 = {} := (by rw [State.getSigAction, hpre0.2.2.2.1, ← State.getSigAction, hsig0])
  have ha1 : (s.sp - 152#64) + 8#64 = s.sp - 144#64 := (by simp only [bv_lin_norm]); have ha2 : (s.sp - 152#64) + 0x88#64 = s.sp - 16#64 := (by simp only [bv_lin_norm])
  have ho1 : (s.sp - 304#64) + 8#64 = s.sp - 296#64 := (by simp only [bv_lin_norm]); have ho2 : (s.sp - 304#64) + 0x88#64 = s.sp - 168#64 := (by simp only [bv_lin_norm])
  refine step_sigaction_fast13 hcode ops (ret_pc := L.signalAddr + 72#64) (act := s.sp - 152#64) (oact := s.sp - 304#64) (F := ?_) (fun R hm => by rw [ha1, ha2, ho1, ho2, hsp0]; revert hm; sep_frame) hpc0 hrun0 hsp_al0 (by rw [hsp0]; bv_omega) hlr0 hx0_0 hx1_0 hx2_0 (by bv_omega) (by bv_omega) hsig_s0 fun s1 v17' hpc1 hrun1 hsp1 hsp_al1 hcs1 hx0_1 hpre1 => ?_
  clear hcode; have hsp1_eq : s1.sp = s.sp - 320#64 := hsp1.trans hsp0; have hc0 : s.sp - 320#64 = s1.sp := hsp1_eq.symm
  have hc1 : s.sp - 312#64 = s1.sp + 8#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm]); have hc2 : s.sp - 304#64 = s1.sp + 16#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm])
  have hsp_end : s1.sp + 320#64 = s.sp := (by rw [hsp1_eq]; simp only [bv_lin_norm]); clear hsp1 hsp1_eq; rw [State.spAligned] at hsp_al1
  have hsp_add_al : ((s1.sp + 320#64) &&& 15#64 == 0#64) = true := (by simp only [beq_iff_eq] at hsp_al1 ⊢; bv_bits); have hge0 : ConditionHolds .GE (subsPState32 0#32 0#32) = true := (by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide)
  wp_conv_pre => rw [ha1, ha2, ho1, ho2, hc0, hc1, hc2]
  wp_steps 5; have hpre_sig : PreMainFieldsPreserved (s.setSigAction 13#32 (sigpipeIgnAction L)) (s0.setSigAction 13#32 (sigpipeIgnAction L)) := ⟨hpre0.1, hpre0.2.1, hpre0.2.2.1, by dsimp only [State.setSigAction]; rw [hpre0.2.2.2.1], hpre0.2.2.2.2.1, hpre0.2.2.2.2.2⟩
  refine step_entail (hnext _ (by wn) (by wnh hrun1) (by wn) (by sp_al hsp_align) (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] at hcs0 hcs1 ⊢; simp [hcs0, hcs1]) (by wn) (hpre_sig.trans (hpre1.trans (by pm_rfl s1))))
    (fun R hm => by rw [← hc2, ← hc1, ← hc0, hsp0] at hm; rw [stackAt_split_cells s.sp 0xe0 40 (by decide), cells_split_sub s.sp 320 288 4 36, cells_split_sub s.sp 288 168 15 21, cells_split_sub s.sp 168 160 1 20, cells_split_sub s.sp 160 152 1 19, ← memRegion_cells (s.sp - BitVec.ofNat 64 288) 15 (by decide), ← memRegion_cells (s.sp - BitVec.ofNat 64 160) 1 (by decide)]; fold_stack_cells)
/-! ## `c_main` pre-user-`main` wrapper -/
@[local simp] private theorem sigActions_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).sigActions = s.sigActions := rfl
@[local simp] private theorem sigActions_setPC (s : State) (p : BitVec 64) : (s.setPC p).sigActions = s.sigActions := rfl
private theorem step_bCond_taken {P : Program} {target_pc pc off dst : BitVec 64} {c : CondCode} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.bCond c off)) (hcond : ConditionHolds c s.pstate = true) (hdst : pc + off = dst) (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) : SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bCond c off) _ rfl]; simp [wp_norm, arm64_norm, hcond, hdst]) rfl hnext
@[local simp] private theorem cond_cmn1 : ConditionHolds .EQ (addsPState64 0#64 1#64) = false := by unfold addsPState64 ConditionHolds; dsimp [AddWithCarry64]
@[local simp] private theorem cond_cas0 : ConditionHolds .NE (subsPState64 0#64 0#64) = false := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]; decide
@[local simp] private theorem cond_poll0 : ConditionHolds .NE (addsPState32 0#32 1#32) = true := by unfold addsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide
@[local simp] private theorem cond_loop0 : ConditionHolds .EQ (subsPState64 0#64 0x18#64) = false := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]
@[local simp] private theorem cond_loop1 : ConditionHolds .EQ (subsPState64 8#64 0x18#64) = false := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]
@[local simp] private theorem cond_loop2 : ConditionHolds .EQ (subsPState64 16#64 0x18#64) = false := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]
@[local simp] private theorem cond_loop3 : ConditionHolds .EQ (subsPState64 24#64 0x18#64) = true := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]
def cMainSavedFrame (L : StdBinaryLayout) (s : State) (stage2Ret w0 w1 w2 w3 wPad : BitVec 64) : SepProp :=
  (((s.sp - 0x70#64) ↦₆₄ (s.sp - 0x40#64)) ∗ ((s.sp - 0x68#64) ↦₆₄ (if L.hasArgcGlobal then L.cMainAddr + 0x208#64 else L.cMainAddr + 0x1f4#64))) ∗
  (((s.sp - 0x60#64) ↦₆₄ w0) ∗ ((s.sp - 0x58#64) ↦₆₄ w1) ∗ ((s.sp - 0x50#64) ↦₆₄ w2) ∗ ((s.sp - 0x48#64) ↦₆₄ w3) ∗ ((s.sp - 0x40#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 0x38#64) ↦₆₄ stage2Ret) ∗
    ((s.sp - 0x30#64) ↦₆₄ (if L.hasArgcGlobal then s.readReg64 (.gpr 24#5) else s.readReg64 (.gpr 23#5))) ∗ ((s.sp - 0x28#64) ↦₆₄ (if L.hasArgcGlobal then s.readReg64 (.gpr 23#5) else wPad)) ∗
    ((s.sp - 0x20#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((s.sp - 0x18#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5)))
def cMainUnsavedCalleeRegs (hasArgcGlobal : Bool) (s0 sf : State) : Prop :=
  (if hasArgcGlobal then True else sf.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5)) ∧ sf.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  sf.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧ sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧ sf.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧ calleeSavedVRegs sf = calleeSavedVRegs s0
private theorem cMainUnsaved_of_cs {b : Bool} {s0 s1 s2 : State} (h01 : cMainUnsavedCalleeRegs b s0 s1) (h12 : CalleeSavedPreserved s1 s2) : cMainUnsavedCalleeRegs b s0 s2 := by
  simp (config := { decide := true }) [Arm64.CalleeSavedPreserved] at h12; rcases h01 with ⟨h24, h25, h26, h27, h28, hv⟩
  refine ⟨by cases b <;> simp at h24 ⊢; simp [h12, h24], by simp [h12, h25], by simp [h12, h26], by simp [h12, h27], by simp [h12, h28], by simp [h12, hv]⟩
private theorem cMainUnsaved_congr {b : Bool} {s0 s1 s2 : State} (h : cMainUnsavedCalleeRegs b s0 s1)
    (h24 : b = false → s2.readReg64 (.gpr 24#5) = s1.readReg64 (.gpr 24#5) := by intro hb; first | exact Bool.noConfusion hb | simp [wp_norm, arm64_norm])
    (h25 : s2.readReg64 (.gpr 25#5) = s1.readReg64 (.gpr 25#5) := by simp [wp_norm, arm64_norm]) (h26 : s2.readReg64 (.gpr 26#5) = s1.readReg64 (.gpr 26#5) := by simp [wp_norm, arm64_norm])
    (h27 : s2.readReg64 (.gpr 27#5) = s1.readReg64 (.gpr 27#5) := by simp [wp_norm, arm64_norm]) (h28 : s2.readReg64 (.gpr 28#5) = s1.readReg64 (.gpr 28#5) := by simp [wp_norm, arm64_norm])
    (hv : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp [wp_norm, arm64_norm]) : cMainUnsavedCalleeRegs b s0 s2 := by
  rcases h with ⟨u24, u25, u26, u27, u28, uv⟩; refine ⟨by cases b <;> simp at u24 ⊢; exact (h24 rfl).trans u24, h25.trans u25, h26.trans u26, h27.trans u27, h28.trans u28, hv.trans uv⟩
private theorem preMain_setSigAction {k : BitVec 32} {act : SigAction} {s0 s1 : State} (h : PreMainFieldsPreserved s0 s1) : PreMainFieldsPreserved (s0.setSigAction k act) (s1.setSigAction k act) :=
  ⟨h.1, h.2.1, h.2.2.1, by dsimp only [State.setSigAction]; rw [h.2.2.2.1], h.2.2.2.2.1, h.2.2.2.2.2⟩
private theorem stackAt_split40 (sp : BitVec 64) : stackAt (sp - 96#64) 0x220 = memRegion (sp - 0x280#64) 0x1e0 ∗ stackAt (sp - 96#64) 0x40 := by rw [stackAt_split_bottom (sp - 96#64) 0x40 0x1e0 (by decide)]; simp only [BitVec.ofNat_eq_ofNat, bv_lin_norm]
private theorem stackAt_split190 (sp : BitVec 64) : stackAt (sp - 96#64) 0x220 = memRegion (sp - 0x280#64) 0x90 ∗ stackAt (sp - 96#64) 0x190 := by rw [stackAt_split_bottom (sp - 96#64) 0x190 0x90 (by decide)]; simp only [BitVec.ofNat_eq_ofNat, bv_lin_norm]
private theorem stackAt_190_split10 (sp : BitVec 64) : stackAt (sp - 96#64) 0x190 = stackAt (sp - 0x70#64) 0x180 ∗ stackAt (sp - 96#64) 0x10 := by rw [stackAt_split_cells (sp - 96#64) 0x180 2 (by decide), ← stackAt_eq_cells (sp - 96#64) 2 (by decide)]; simp only [BitVec.ofNat_eq_ofNat, bv_lin_norm]
private theorem stackAt_210_split (sp : BitVec 64) : stackAt (sp - 0x70#64) 0x210 = memRegion (sp - 0x280#64) 0x90 ∗ stackAt (sp - 0x70#64) 0x180 := by rw [stackAt_split_bottom (sp - 0x70#64) 0x180 0x90 (by decide)]; simp only [BitVec.ofNat_eq_ofNat, bv_lin_norm]
private theorem step_cMain_head_noArgc {P : Program} {L : StdBinaryLayout} {target_pc stage2Ret tp argvPtr : BitVec 64} {haveLse : BitVec 8}
    (hcode : LangStartPreCode P L) (hpre_code : hasInstrs P L.cMainAddr (cMainPreNoArgcInstrs L))
    (atomics : StdOutlineAtomics P L.haveLseAtomicsAddr L.cas8RelaxAddr L.cas4AcqAddr L.cas8AcqAddr L.swp4RelAddr)
    (htid_align : MemWidth.isAligned .X64 L.threadIdCounterAddr = true) {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = L.cMainAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0x280 ≤ s.sp.toNat) (hlr : s.readReg64 .lr = stage2Ret)
    (hx1 : s.readReg64 .x1 = argvPtr) (htp : s.tpidrEl0 = tp) (hpoll_ok : evalPpollBytes s.fs stdioPollfdBytes 0 = some (stdioPollfdBytes, 0))
    (hpre : ∀ R, s.mem ⊨ Pre ∗ R → s.mem ⊨ ((((L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (L.threadIdCounterAddr ↦₆₄ 0#64) ∗ ((tp + 16#64) ↦₆₄ 0#64)) ∗ stackAt s.sp 0x280) ∗ (F ∗ R)))
    (hnext : ∀ (s2 : State) (w0 wPad : BitVec 64), s2.pc = L.cMainAddr + (0x250#64 + cMainEcShiftNoArgc L) → s2.status = .Running → s2.sp = s.sp - 96#64 → s2.spAligned = true → s2.readReg64 .x19 = argvPtr → s2.readReg64 .x29 = s.sp - 64#64 → cMainUnsavedCalleeRegs false s s2 → PreMainFieldsPreserved s s2 →
      SepWP P target_pc s2 ((((L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (L.threadIdCounterAddr ↦₆₄ 1#64) ∗ ((tp + 16#64) ↦₆₄ 1#64)) ∗ (((s.sp - 96#64) ↦₆₄ w0) ∗ ((s.sp - 88#64) ↦₆₄ 0#64) ∗ ((s.sp - 80#64) ↦₆₄ 1#64) ∗ ((s.sp - 72#64) ↦₆₄ 2#64) ∗ ((s.sp - 64#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 56#64) ↦₆₄ stage2Ret) ∗ ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗ ((s.sp - 40#64) ↦₆₄ wPad) ∗ ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((s.sp - 24#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5))) ∗ stackAt (s.sp - 96#64) 0x220) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine step_frame ?_ hpre; have hp := hpre_code; clear hpre_code; dsimp only [cMainPreNoArgcInstrs] at hp; revert hp
  refine peel_instr0 fun _ => ?_; peelS 5; peel1 hf6; peelS 15; peel1 hf22; peelS 11; peel1 hf34; peelS 1; peel1 hf36; intro _; rw [stackAt_split_cells s.sp 0x220 12 (by decide)]; unfold_stack_cells 12
  wp_steps 6; refine SepWP.step_mrs_tpidr_el0 (pc := L.cMainAddr + 24#64) (by wn) (by wnh hrun) hf6 rfl ?_; wp_steps 15; refine step_bl_to (pc := L.cMainAddr + 88#64) (dst := L.cas8RelaxAddr) (by wn) (by wnh hrun) hf22 ?_; refine step_cut fun s0 hs0 => ?_
  have ⟨hsp0, hx19_0, hx21_0, hx22_0, hx23_0, hx29_0⟩ : s0.sp = s.sp - 96#64 ∧ s0.readReg64 .x19 = argvPtr ∧ s0.readReg64 .x21 = 0#64 ∧ s0.readReg64 .x22 = tp + 16#64 ∧ s0.readReg64 .x23 = 1#64 ∧ s0.readReg64 .x29 = s.sp - 64#64 :=
    (by rw [hs0]; refine ⟨by wn, by wn, by wn, by wn, by wn, by wn⟩)
  have huns0 : cMainUnsavedCalleeRegs false s s0 := (by rw [hs0]; simp [cMainUnsavedCalleeRegs, wp_norm, arm64_norm]); have hpre0 : PreMainFieldsPreserved s s0 := (by rw [hs0]; pm_rfl s)
  refine call_stdCas8 atomics.cas8Relax_ok (ret_pc := L.cMainAddr + 92#64) (haveLse := haveLse) (ptr := L.threadIdCounterAddr) (v0 := 0#64) (exp := 0#64) (new := 1#64) (F := ?_) (fun R hm => by revert hm; sep_frame) (fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hstd1 => ?_) (by rw [hs0]; wn) (by rw [hs0]; wnh hrun) (by rw [State.spAligned, hsp0]; exact s.spAligned_sub 0x60#64 hsp_align) (by rw [hs0]; wn) (by rw [hs0]; wn) (by rw [hs0]; wn) (by rw [hs0]; wn) htid_align
  clear hs0 hf6 hf22 hpc hlr hx1 htp; have hsp1_eq : s1.sp = s.sp - 96#64 := hsp1.trans hsp0; have hsp_al1 : s1.spAligned = true := (by rw [State.spAligned, hsp1_eq]; exact s.spAligned_sub 0x60#64 hsp_align)
  have hx19_1 : s1.readReg64 .x19 = argvPtr := hcs1.1.trans hx19_0; have hx21_1 : s1.readReg64 .x21 = 0#64 := hcs1.2.2.1.trans hx21_0; have hx22_1 : s1.readReg64 .x22 = tp + 16#64 := hcs1.2.2.2.1.trans hx22_0
  have hx23_1 : s1.readReg64 .x23 = 1#64 := hcs1.2.2.2.2.1.trans hx23_0; have hx29_1 : s1.readReg64 .x29 = s.sp - 64#64 := (CalleeSavedPreserved.readReg64_x29 hcs1).trans hx29_0
  have hc1 : s.sp - 88#64 = s1.sp + 8#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm]); have hc2 : s.sp - 80#64 = s1.sp + 16#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm]); have hc3 : s.sp - 72#64 = s1.sp + 24#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm]); clear hsp1 hsp1_eq
  wp_conv_pre => rw [show (if (0#64 : BitVec 64) == 0#64 then (1#64 : BitVec 64) else 0#64) = 1#64 from rfl, hc1, hc2, hc3]
  wp_steps 11; refine step_bl_to (pc := L.cMainAddr + 136#64) (dst := L.pollAddr) (by wn) (by wnh hrun1) hf34 ?_; have hsp_s1 : s1.sp = s.sp - 96#64 := (by have := congrArg (· - 8#64) hc1; simpa [bv_lin_norm] using this.symm)
  have hu1 : (s1.sp + 8#64) + 8#64 = s1.sp + 16#64 := (by simp only [bv_lin_norm]); have hu2 : (s1.sp + 8#64) + 16#64 = s1.sp + 24#64 := (by simp only [bv_lin_norm]); have hfs1 : s1.fs = s.fs := hstd1.toPreMain.1.trans hpre0.1
  refine step_poll_stdio3 hcode (ret_pc := L.cMainAddr + 140#64) (ufds := s1.sp + 8#64) (F := ?_) (fun R hm => by rw [hu1, hu2]; simp only [wp_norm, arm64_norm, hsp_s1, stackAt_split40] at hm ⊢; revert hm; sep_frame) (by wn) (by wnh hrun1) (by sp_al hsp_al1) (by simp [wp_norm, arm64_norm]; rw [hsp_s1]; bv_omega) (by wn) (by wn) (by wn) (by wn) (by rw [hsp_s1]; bv_omega) (by simpa [wp_norm, arm64_norm, hfs1] using hpoll_ok) fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hx0_2 hpre2 => ?_
  wp_steps 1; refine step_bCond_taken (pc := L.cMainAddr + 144#64) (dst := L.cMainAddr + (0x250#64 + cMainEcShiftNoArgc L)) (by wn) (by wnh hrun2) hf36 (by wn) (by simp only [bv_lin_norm]) ?_
  have hx19_2 : s2.readReg64 .x19 = argvPtr := hcs2.1.trans (by wnh hx19_1); have hx29_2 : s2.readReg64 .x29 = s.sp - 64#64 := (CalleeSavedPreserved.readReg64_x29 hcs2).trans (by wnh hx29_1)
  have huns2 := cMainUnsaved_of_cs (cMainUnsaved_congr (cMainUnsaved_of_cs huns0 hcs1)) hcs2; have hpre2_s1 : PreMainFieldsPreserved s1 s2 := (by simp only [preMain_w64_l, preMain_pc_l, preMain_mem_l, preMain_ps_l] at hpre2; exact hpre2)
  refine step_entail (hnext _ _ _ (by wn) (by wnh hrun2) (by simp [wp_norm, arm64_norm] at hsp2 ⊢; exact hsp2.trans hsp_s1) (by sp_al hsp_al2) (by wnh hx19_2) (by wnh hx29_2) (cMainUnsaved_congr huns2) (hpre0.trans (hstd1.toPreMain.trans (hpre2_s1.trans (by pm_rfl s2)))))
    (fun R hm => by rw [hu1, hu2, ← hc3, ← hc2, ← hc1] at hm; simp only [wp_norm, arm64_norm, hsp_s1, stackAt_split40] at hm ⊢; sep_entail)

private theorem step_cMain_tail_noArgc {P : Program} {L : StdBinaryLayout} {target_pc argvPtr vPage vArgv : BitVec 64}
    (hcode : LangStartPreCode P L) (ops : StdMemOps P L.memcpyAddr L.memsetAddr)
    (hloop : hasInstrs P (L.cMainAddr + (0x250#64 + cMainEcShiftNoArgc L)) (cMainPollLoopNoArgcInstrs L)) (hmid : hasInstrs P (L.cMainAddr + 0x1b8#64) (cMainMidNoArgcInstrs L))
    {s s2 : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc2 : s2.pc = L.cMainAddr + (0x250#64 + cMainEcShiftNoArgc L)) (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s.sp - 96#64)
    (hsp_al2 : s2.spAligned = true) (hsp_lo : 0x280 ≤ s.sp.toNat) (hx19_2 : s2.readReg64 .x19 = argvPtr) (hx29_2 : s2.readReg64 .x29 = s.sp - 64#64)
    (huns2 : cMainUnsavedCalleeRegs false s s2) (hpre2 : PreMainFieldsPreserved s s2) (hsig0 : s.getSigAction 13#32 = {})
    (hpre : ∀ R, s2.mem ⊨ Pre ∗ R → s2.mem ⊨ (((((s.sp - 88#64) ↦₆₄ 0#64) ∗ ((s.sp - 80#64) ↦₆₄ 1#64) ∗ ((s.sp - 72#64) ↦₆₄ 2#64)) ∗ ((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ (L.pageSizeGlobalAddr ↦₆₄ vPage) ∗ (L.argvGlobalAddr ↦₆₄ vArgv) ∗ stackAt (s.sp - 96#64) 0x220) ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = L.userMainAddr → sf.status = .Running → sf.sp = s.sp - 0x70#64 → sf.spAligned = true → sf.readReg64 .x29 = s.sp - 0x70#64 → sf.readReg64 .lr = L.beginShortBacktraceAddr + 12#64 → cMainUnsavedCalleeRegs false s sf → PreMainFieldsPreserved (s.setSigAction 13#32 (sigpipeIgnAction L)) sf →
      SepWP P target_pc sf (((((s.sp - 0x70#64) ↦₆₄ (s.sp - 0x40#64)) ∗ ((s.sp - 0x68#64) ↦₆₄ (L.cMainAddr + 0x1f4#64))) ∗ (((s.sp - 88#64) ↦₆₄ 0#64) ∗ ((s.sp - 80#64) ↦₆₄ 1#64) ∗ ((s.sp - 72#64) ↦₆₄ 2#64)) ∗ ((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ (L.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ (L.argvGlobalAddr ↦₆₄ argvPtr) ∗ stackAt (s.sp - 0x70#64) 0x210) ∗ F) post oom) :
    SepWP P target_pc s2 Pre post oom := by
  refine step_frame ?_ hpre; have hc1 : s.sp - 88#64 = s2.sp + 8#64 := (by rw [hsp2]; simp only [bv_lin_norm]); have hc2 : s.sp - 80#64 = (s2.sp + 8#64) + 8#64 := (by rw [hsp2]; simp only [bv_lin_norm]); have hc3 : s.sp - 72#64 = (s2.sp + 8#64) + 16#64 := (by rw [hsp2]; simp only [bv_lin_norm]); clear hsp2; have hpl := hloop; clear hloop; dsimp only [cMainPollLoopNoArgcInstrs] at hpl
  generalize hb0 : L.cMainAddr + (0x250#64 + cMainEcShiftNoArgc L) = b0 at hpl hpc2; revert hpl; refine peel_instr0 fun _ => ?_; peelS 5; peel1 hf6l; peelS 4; intro _; wp_conv_pre => rw [hc1, hc2, hc3, stdioPollfds_eq_bytes (s2.sp + 8#64)]
  wp_steps 24; refine step_bCond_taken (pc := b0 + 24#64) (dst := L.cMainAddr + 0x1b8#64) (by wn) (by wnh hrun2) hf6l (by wn) (by rw [← hb0]; simp only [bv_lin_norm]) ?_; wp_conv_pre => rw [← stdioPollfds_eq_bytes (s2.sp + 8#64), ← hc3, ← hc2, ← hc1]
  have hsp2 : s2.sp = s.sp - 96#64 := (by have := congrArg (· - 8#64) hc1; simpa [bv_lin_norm] using this.symm); refine step_cut fun s3 hs3 => ?_
  have ⟨hpc3, hrun3, hsp3, hsp_al3, hx19_3, hx29_3, huns3⟩ : s3.pc = L.cMainAddr + 0x1b8#64 ∧ s3.status = .Running ∧ s3.sp = s.sp - 96#64 ∧ s3.spAligned = true ∧ s3.readReg64 .x19 = argvPtr ∧ s3.readReg64 .x29 = s.sp - 64#64 ∧ cMainUnsavedCalleeRegs false s s3 := (by rw [hs3]; refine ⟨by wn, by wnh hrun2, by wnh hsp2, by sp_al hsp_al2, by wnh hx19_2, by wnh hx29_2, cMainUnsaved_congr huns2⟩); have hpre3 : PreMainFieldsPreserved s s3 := hpre2.trans (by rw [hs3]; pm_rfl s2); clear hs3 hc1 hc2 hc3 hb0 hf6l hpc2 hrun2 hsp2 hsp_al2 hx19_2 hx29_2 huns2 hpre2
  have hp := hmid; clear hmid; dsimp only [cMainMidNoArgcInstrs] at hp; generalize hb : L.cMainAddr + 0x1b8#64 = b at hp hpc3; revert hp; refine peel_instr0 fun _ => ?_; peelS 1; peel1 hf2; peelS 3; peel1 hf6; peelS 7; peel1 hf14; intro _
  wp_steps 2; refine step_bl_to (pc := b + 8#64) (dst := L.signalAddr) (by wn) (by wnh hrun3) hf2 ?_; have hsig_s3 : s3.getSigAction 13#32 = {} := (by rw [State.getSigAction, hpre3.2.2.2.1, ← State.getSigAction, hsig0])
  refine step_signal_sigpipe_ign hcode ops (ret_pc := b + 12#64) (F := ?_) (fun R hm => by simp only [wp_norm, arm64_norm, hsp3] at hm ⊢; revert hm; sep_frame) (by wn) (by wnh hrun3) (by sp_al hsp_al3) (by simp [wp_norm, arm64_norm, hsp3]; bv_omega) (by wn) (by wn) (by wn) (by simpa [State.getSigAction] using hsig_s3) fun s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hx0_4 hpre4 => ?_
  have hsp4_eq : s4.sp = s.sp - 96#64 := (by simpa [wp_norm, arm64_norm] using hsp4 : s4.sp = s3.sp).trans hsp3; have hx19_4 : s4.readReg64 .x19 = argvPtr := hcs4.1.trans (by wnh hx19_3); have hx29_4 : s4.readReg64 .x29 = s.sp - 64#64 := (CalleeSavedPreserved.readReg64_x29 hcs4).trans (by wnh hx29_3); have huns4 := cMainUnsaved_of_cs (cMainUnsaved_congr huns3) hcs4; have hpre4_sig := (preMain_setSigAction (hpre3.trans (by pm_rfl s3))).trans hpre4; wp_steps 3; refine step_bl_to (pc := b + 24#64) (dst := L.sysconfAddr) (by wn) (by wnh hrun4) hf6 ?_
  refine step_sysconf_pagesize hcode.sysconf_instrs hcode.sysconfEpilogue_code (ret_pc := b + 28#64) (F := ?_) (fun R hm => by simp only [wp_norm, arm64_norm, hsp3, hsp4_eq, stackAt_split190] at hm ⊢; revert hm; sep_frame) (by wn) (by wnh hrun4) (by sp_al hsp_al4) (by wn) (by wn) fun s5 hpc5 hrun5 hsp5 hsp_al5 hcs5 hx0_5 hpre5 => ?_
  have hsp5_eq : s5.sp = s.sp - 96#64 := (by simpa [wp_norm, arm64_norm] using hsp5 : s5.sp = s4.sp).trans hsp4_eq; have hx19_5 : s5.readReg64 .x19 = argvPtr := hcs5.1.trans (by wnh hx19_4); have hx29_5 : s5.readReg64 .x29 = s.sp - 64#64 := (CalleeSavedPreserved.readReg64_x29 hcs5).trans (by wnh hx29_4); have huns5 := cMainUnsaved_of_cs (cMainUnsaved_congr huns4) hcs5; have hpre5_sig := hpre4_sig.trans (by simp only [preMain_w64_l, preMain_pc_l, preMain_ps_l] at hpre5; exact hpre5); wp_steps 7; refine step_bl_to (pc := b + 56#64) (dst := L.beginShortBacktraceAddr) (by wn) (by wnh hrun5) hf14 ?_
  refine step_beginShortBacktrace_enter hcode.beginShortBacktrace_code (ret_pc := L.cMainAddr + 0x1f4#64) (F := ?_) (fun R hm => by simp only [wp_norm, arm64_norm, hsp4_eq, hsp5_eq, stackAt_190_split10] at hm ⊢; revert hm; sep_frame) (by wn) (by wnh hrun5) (by sp_al hsp_al5) (by rw [← hb]; wn) (by wn) fun sf hpcf hrunf hspf hsp_alf hx29f hlrf hcsf hpref => ?_
  refine SepWP.weaken_pre_frame (fun R hm => by have hx29_raw : s5.readReg64 (.gpr 29#5) = s.sp - 0x40#64 := hx29_5; rw [stackAt_210_split]; simp only [wp_norm, arm64_norm, hsp5_eq, hx29_raw, bv_lin_norm] at hm ⊢; ac_nf at hm ⊢) (hnext sf hpcf hrunf (by simpa [wp_norm, arm64_norm, hsp5_eq, bv_lin_norm] using hspf) hsp_alf (by simpa [wp_norm, arm64_norm, hsp5_eq, bv_lin_norm] using hx29f) hlrf (cMainUnsaved_of_cs (cMainUnsaved_congr huns5) hcsf) (hpre5_sig.trans (by simp only [preMain_w64_l, preMain_pc_l, preMain_mem_l] at hpref; exact hpref)))
private theorem sxtw_ofNat_norm {argc : Nat} (h : argc < 2 ^ 31) : (BitVec.ofNat 64 argc >>> 0 &&& 0xffffffff#64 ||| (if (BitVec.ofNat 64 argc).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&& 0xffffffff00000000#64) = BitVec.ofNat 64 argc := by
  have h31 : (BitVec.ofNat 64 argc).getLsbD 31 = false := (by dsimp [BitVec.getLsbD]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.testBit_lt_two_pow h); rw [h31, BitVec.ushiftRight_zero]; simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_and, BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (0xffffffff#64 : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
private theorem step_cMain_head_withArgc {P : Program} {L : StdBinaryLayout} {target_pc stage2Ret tp argvPtr : BitVec 64} {argc : Nat} {haveLse : BitVec 8}
    (hcode : LangStartPreCode P L) (hpre_code : hasInstrs P L.cMainAddr (cMainPreWithArgcInstrs L)) (atomics : StdOutlineAtomics P L.haveLseAtomicsAddr L.cas8RelaxAddr L.cas4AcqAddr L.cas8AcqAddr L.swp4RelAddr)
    (htid_align : MemWidth.isAligned .X64 L.threadIdCounterAddr = true) (hargc : argc < 2 ^ 31) {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = L.cMainAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0x280 ≤ s.sp.toNat) (hlr : s.readReg64 .lr = stage2Ret) (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 argc) (hx1 : s.readReg64 .x1 = argvPtr) (htp : s.tpidrEl0 = tp) (hpoll_ok : evalPpollBytes s.fs stdioPollfdBytes 0 = some (stdioPollfdBytes, 0))
    (hpre : ∀ R, s.mem ⊨ Pre ∗ R → s.mem ⊨ ((((L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (L.threadIdCounterAddr ↦₆₄ 0#64) ∗ ((tp + 16#64) ↦₆₄ 0#64)) ∗ stackAt s.sp 0x280) ∗ (F ∗ R)))
    (hnext : ∀ (s2 : State) (w3 : BitVec 64), s2.pc = L.cMainAddr + (0x26c#64 + cMainEcShiftWithArgc L) → s2.status = .Running → s2.sp = s.sp - 96#64 → s2.spAligned = true → s2.readReg64 .x19 = argvPtr → s2.readReg64 .x22 = BitVec.ofNat 64 argc → s2.readReg64 .x29 = s.sp - 64#64 → cMainUnsavedCalleeRegs true s s2 → PreMainFieldsPreserved s s2 →
      SepWP P target_pc s2 ((((L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (L.threadIdCounterAddr ↦₆₄ 1#64) ∗ ((tp + 16#64) ↦₆₄ 1#64)) ∗ (((s.sp - 96#64) ↦₆₄ 0#64) ∗ ((s.sp - 88#64) ↦₆₄ 1#64) ∗ ((s.sp - 80#64) ↦₆₄ 2#64) ∗ ((s.sp - 72#64) ↦₆₄ w3) ∗ ((s.sp - 64#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 56#64) ↦₆₄ stage2Ret) ∗ ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((s.sp - 40#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗ ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((s.sp - 24#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5))) ∗ stackAt (s.sp - 96#64) 0x220) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine step_frame ?_ hpre; have hp := hpre_code; clear hpre_code; dsimp only [cMainPreWithArgcInstrs] at hp; revert hp; refine peel_instr0 fun _ => ?_; peelS 5; peel1 hf6; peelS 16; peel1 hf23; peelS 13; peel1 hf37; peelS 1; peel1 hf39; intro _; rw [stackAt_split_cells s.sp 0x220 12 (by decide)]; unfold_stack_cells 12
  wp_steps 6; refine SepWP.step_mrs_tpidr_el0 (pc := L.cMainAddr + 24#64) (by wn) (by wnh hrun) hf6 rfl ?_; wp_steps 16; refine step_bl_to (pc := L.cMainAddr + 92#64) (dst := L.cas8RelaxAddr) (by wn) (by wnh hrun) hf23 ?_; refine step_cut fun s0 hs0 => ?_
  have ⟨hsp0, hx19_0, hx21_0, hx22_0, hx23_0, hx24_0, hx29_0⟩ : s0.sp = s.sp - 96#64 ∧ s0.readReg64 .x19 = argvPtr ∧ s0.readReg64 .x21 = 0#64 ∧ s0.readReg64 .x22 = tp + 16#64 ∧ s0.readReg64 .x23 = BitVec.ofNat 64 argc ∧ s0.readReg64 .x24 = 1#64 ∧ s0.readReg64 .x29 = s.sp - 64#64 := (by rw [hs0]; refine ⟨by wn, by wn, by wn, by wn, by wn, by wn, by wn⟩); have huns0 : cMainUnsavedCalleeRegs true s s0 := (by rw [hs0]; simp [cMainUnsavedCalleeRegs, wp_norm, arm64_norm]); have hpre0 : PreMainFieldsPreserved s s0 := (by rw [hs0]; pm_rfl s)
  refine call_stdCas8 atomics.cas8Relax_ok (ret_pc := L.cMainAddr + 96#64) (haveLse := haveLse) (ptr := L.threadIdCounterAddr) (v0 := 0#64) (exp := 0#64) (new := 1#64) (F := ?_) (fun R hm => by revert hm; sep_frame) (fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hstd1 => ?_) (by rw [hs0]; wn) (by rw [hs0]; wnh hrun) (by rw [State.spAligned, hsp0]; exact s.spAligned_sub 0x60#64 hsp_align) (by rw [hs0]; wn) (by rw [hs0]; wn) (by rw [hs0]; wn) (by rw [hs0]; wn) htid_align
  clear hs0 hf6 hf23 hpc hlr hx0 hx1 htp; have hsp1_eq : s1.sp = s.sp - 96#64 := hsp1.trans hsp0; have hsp_al1 : s1.spAligned = true := (by rw [State.spAligned, hsp1_eq]; exact s.spAligned_sub 0x60#64 hsp_align); have hx19_1 : s1.readReg64 .x19 = argvPtr := hcs1.1.trans hx19_0; have hx21_1 : s1.readReg64 .x21 = 0#64 := hcs1.2.2.1.trans hx21_0; have hx22_1 : s1.readReg64 .x22 = tp + 16#64 := hcs1.2.2.2.1.trans hx22_0
  have hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 argc := hcs1.2.2.2.2.1.trans hx23_0; have hx24_1 : s1.readReg64 .x24 = 1#64 := hcs1.2.2.2.2.2.1.trans hx24_0; have hx29_1 : s1.readReg64 .x29 = s.sp - 64#64 := (CalleeSavedPreserved.readReg64_x29 hcs1).trans hx29_0; have hc0 : s.sp - 96#64 = s1.sp := hsp1_eq.symm; have hc1 : s.sp - 88#64 = s1.sp + 8#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm]); have hc2 : s.sp - 80#64 = s1.sp + 16#64 := (by rw [hsp1_eq]; simp only [bv_lin_norm]); clear hsp1 hsp1_eq
  wp_conv_pre => rw [show (if (0#64 : BitVec 64) == 0#64 then (1#64 : BitVec 64) else 0#64) = 1#64 from rfl, hc0, hc1, hc2]
  wp_steps 13; refine step_bl_to (pc := L.cMainAddr + 148#64) (dst := L.pollAddr) (by wn) (by wnh hrun1) hf37 ?_; have hsp_s1 : s1.sp = s.sp - 96#64 := hc0.symm; have hfs1 : s1.fs = s.fs := hstd1.toPreMain.1.trans hpre0.1
  refine step_poll_stdio3 hcode (ret_pc := L.cMainAddr + 152#64) (ufds := s1.sp) (F := ?_) (fun R hm => by simp only [wp_norm, arm64_norm, hsp_s1, stackAt_split40] at hm ⊢; revert hm; sep_frame) (by wn) (by wnh hrun1) (by sp_al hsp_al1) (by simp [wp_norm, arm64_norm]; rw [hsp_s1]; bv_omega) (by wn) (by wn) (by wn) (by wn) (by rw [hsp_s1]; bv_omega) (by simpa [wp_norm, arm64_norm, hfs1] using hpoll_ok) fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hx0_2 hpre2 => ?_
  wp_steps 1; refine step_bCond_taken (pc := L.cMainAddr + 156#64) (dst := L.cMainAddr + (0x26c#64 + cMainEcShiftWithArgc L)) (by wn) (by wnh hrun2) hf39 (by wn) (by simp only [bv_lin_norm]) ?_
  have hx19_2 : s2.readReg64 .x19 = argvPtr := hcs2.1.trans (by wnh hx19_1); have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 argc := hcs2.2.2.2.1.trans (by rw [sxtw_ofNat_norm hargc]; wn); have hx29_2 : s2.readReg64 .x29 = s.sp - 64#64 := (CalleeSavedPreserved.readReg64_x29 hcs2).trans (by wnh hx29_1); have huns2 := cMainUnsaved_of_cs (cMainUnsaved_congr (cMainUnsaved_of_cs huns0 hcs1)) hcs2; have hpre2_s1 : PreMainFieldsPreserved s1 s2 := (by simp only [preMain_w64_l, preMain_pc_l, preMain_mem_l, preMain_ps_l] at hpre2; exact hpre2)
  refine step_entail (hnext _ _ (by wn) (by wnh hrun2) (by simp [wp_norm, arm64_norm] at hsp2 ⊢; exact hsp2.trans hsp_s1) (by sp_al hsp_al2) (by wnh hx19_2) (by wnh hx22_2) (by wnh hx29_2) (cMainUnsaved_congr huns2) (hpre0.trans (hstd1.toPreMain.trans (hpre2_s1.trans (by pm_rfl s2))))) (fun R hm => by rw [← hc2, ← hc1, ← hc0] at hm; simp only [wp_norm, arm64_norm, hsp_s1, stackAt_split40] at hm ⊢; sep_entail)
private theorem step_cMain_tail_withArgc {P : Program} {L : StdBinaryLayout} {target_pc argvPtr vPage vArgc vArgv : BitVec 64} {argc : Nat}
    (hcode : LangStartPreCode P L) (ops : StdMemOps P L.memcpyAddr L.memsetAddr) (hloop : hasInstrs P (L.cMainAddr + (0x26c#64 + cMainEcShiftWithArgc L)) (cMainPollLoopWithArgcInstrs L)) (hmid : hasInstrs P (L.cMainAddr + 0x1c4#64) (cMainMidWithArgcInstrs L))
    {s s2 : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc2 : s2.pc = L.cMainAddr + (0x26c#64 + cMainEcShiftWithArgc L)) (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s.sp - 96#64) (hsp_al2 : s2.spAligned = true) (hsp_lo : 0x280 ≤ s.sp.toNat)
    (hx19_2 : s2.readReg64 .x19 = argvPtr) (hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 argc) (hx29_2 : s2.readReg64 .x29 = s.sp - 64#64) (huns2 : cMainUnsavedCalleeRegs true s s2) (hpre2 : PreMainFieldsPreserved s s2) (hsig0 : s.getSigAction 13#32 = {})
    (hpre : ∀ R, s2.mem ⊨ Pre ∗ R → s2.mem ⊨ (((((s.sp - 96#64) ↦₆₄ 0#64) ∗ ((s.sp - 88#64) ↦₆₄ 1#64) ∗ ((s.sp - 80#64) ↦₆₄ 2#64)) ∗ ((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ (L.pageSizeGlobalAddr ↦₆₄ vPage) ∗ (L.argcGlobalAddr ↦₆₄ vArgc) ∗ (L.argvGlobalAddr ↦₆₄ vArgv) ∗ stackAt (s.sp - 96#64) 0x220) ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = L.userMainAddr → sf.status = .Running → sf.sp = s.sp - 0x70#64 → sf.spAligned = true → sf.readReg64 .x29 = s.sp - 0x70#64 → sf.readReg64 .lr = L.beginShortBacktraceAddr + 12#64 → cMainUnsavedCalleeRegs true s sf → PreMainFieldsPreserved (s.setSigAction 13#32 (sigpipeIgnAction L)) sf →
      SepWP P target_pc sf (((((s.sp - 0x70#64) ↦₆₄ (s.sp - 0x40#64)) ∗ ((s.sp - 0x68#64) ↦₆₄ (L.cMainAddr + 0x208#64))) ∗ (((s.sp - 96#64) ↦₆₄ 0#64) ∗ ((s.sp - 88#64) ↦₆₄ 1#64) ∗ ((s.sp - 80#64) ↦₆₄ 2#64)) ∗ ((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ (L.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ (L.argcGlobalAddr ↦₆₄ BitVec.ofNat 64 argc) ∗ (L.argvGlobalAddr ↦₆₄ argvPtr) ∗ stackAt (s.sp - 0x70#64) 0x210) ∗ F) post oom) :
    SepWP P target_pc s2 Pre post oom := by
  refine step_frame ?_ hpre; have hc0 : s.sp - 96#64 = s2.sp := hsp2.symm; have hc1 : s.sp - 88#64 = s2.sp + 8#64 := (by rw [hsp2]; simp only [bv_lin_norm]); have hc2 : s.sp - 80#64 = s2.sp + 16#64 := (by rw [hsp2]; simp only [bv_lin_norm]); clear hsp2; have hpl := hloop; clear hloop; dsimp only [cMainPollLoopWithArgcInstrs] at hpl
  generalize hb0 : L.cMainAddr + (0x26c#64 + cMainEcShiftWithArgc L) = b0 at hpl hpc2; revert hpl; refine peel_instr0 fun _ => ?_; peelS 5; peel1 hf6l; peelS 4; intro _; wp_conv_pre => rw [hc0, hc1, hc2, stdioPollfds_eq_bytes s2.sp]
  wp_steps 24; refine step_bCond_taken (pc := b0 + 24#64) (dst := L.cMainAddr + 0x1c4#64) (by wn) (by wnh hrun2) hf6l (by wn) (by rw [← hb0]; simp only [bv_lin_norm]) ?_; wp_conv_pre => rw [← stdioPollfds_eq_bytes s2.sp, ← hc2, ← hc1, ← hc0]
  have hsp2 : s2.sp = s.sp - 96#64 := hc0.symm; refine step_cut fun s3 hs3 => ?_
  have ⟨hpc3, hrun3, hsp3, hsp_al3, hx19_3, hx22_3, hx29_3, huns3⟩ : s3.pc = L.cMainAddr + 0x1c4#64 ∧ s3.status = .Running ∧ s3.sp = s.sp - 96#64 ∧ s3.spAligned = true ∧ s3.readReg64 .x19 = argvPtr ∧ s3.readReg64 .x22 = BitVec.ofNat 64 argc ∧ s3.readReg64 .x29 = s.sp - 64#64 ∧ cMainUnsavedCalleeRegs true s s3 := (by rw [hs3]; refine ⟨by wn, by wnh hrun2, by wnh hsp2, by sp_al hsp_al2, by wnh hx19_2, by wnh hx22_2, by wnh hx29_2, cMainUnsaved_congr huns2⟩); have hpre3 : PreMainFieldsPreserved s s3 := hpre2.trans (by rw [hs3]; pm_rfl s2); clear hs3 hc0 hc1 hc2 hb0 hf6l hpc2 hrun2 hsp2 hsp_al2 hx19_2 hx22_2 hx29_2 huns2 hpre2
  have hp := hmid; clear hmid; dsimp only [cMainMidWithArgcInstrs] at hp; generalize hb : L.cMainAddr + 0x1c4#64 = b at hp hpc3; revert hp; refine peel_instr0 fun _ => ?_; peelS 1; peel1 hf2; peelS 3; peel1 hf6; peelS 9; peel1 hf16; intro _
  wp_steps 2; refine step_bl_to (pc := b + 8#64) (dst := L.signalAddr) (by wn) (by wnh hrun3) hf2 ?_; have hsig_s3 : s3.getSigAction 13#32 = {} := (by rw [State.getSigAction, hpre3.2.2.2.1, ← State.getSigAction, hsig0])
  refine step_signal_sigpipe_ign hcode ops (ret_pc := b + 12#64) (F := ?_) (fun R hm => by simp only [wp_norm, arm64_norm, hsp3] at hm ⊢; revert hm; sep_frame) (by wn) (by wnh hrun3) (by sp_al hsp_al3) (by simp [wp_norm, arm64_norm, hsp3]; bv_omega) (by wn) (by wn) (by wn) (by simpa [State.getSigAction] using hsig_s3) fun s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hx0_4 hpre4 => ?_
  have hsp4_eq : s4.sp = s.sp - 96#64 := (by simpa [wp_norm, arm64_norm] using hsp4 : s4.sp = s3.sp).trans hsp3; have hx19_4 : s4.readReg64 .x19 = argvPtr := hcs4.1.trans (by wnh hx19_3); have hx22_4 : s4.readReg64 .x22 = BitVec.ofNat 64 argc := hcs4.2.2.2.1.trans (by wnh hx22_3); have hx29_4 : s4.readReg64 .x29 = s.sp - 64#64 := (CalleeSavedPreserved.readReg64_x29 hcs4).trans (by wnh hx29_3); have huns4 := cMainUnsaved_of_cs (cMainUnsaved_congr huns3) hcs4; have hpre4_sig := (preMain_setSigAction (hpre3.trans (by pm_rfl s3))).trans hpre4; wp_steps 3; refine step_bl_to (pc := b + 24#64) (dst := L.sysconfAddr) (by wn) (by wnh hrun4) hf6 ?_
  refine step_sysconf_pagesize hcode.sysconf_instrs hcode.sysconfEpilogue_code (ret_pc := b + 28#64) (F := ?_) (fun R hm => by simp only [wp_norm, arm64_norm, hsp3, hsp4_eq, stackAt_split190] at hm ⊢; revert hm; sep_frame) (by wn) (by wnh hrun4) (by sp_al hsp_al4) (by wn) (by wn) fun s5 hpc5 hrun5 hsp5 hsp_al5 hcs5 hx0_5 hpre5 => ?_
  have hsp5_eq : s5.sp = s.sp - 96#64 := (by simpa [wp_norm, arm64_norm] using hsp5 : s5.sp = s4.sp).trans hsp4_eq; have hx19_5 : s5.readReg64 .x19 = argvPtr := hcs5.1.trans (by wnh hx19_4); have hx22_5 : s5.readReg64 .x22 = BitVec.ofNat 64 argc := hcs5.2.2.2.1.trans (by wnh hx22_4); have hx29_5 : s5.readReg64 .x29 = s.sp - 64#64 := (CalleeSavedPreserved.readReg64_x29 hcs5).trans (by wnh hx29_4); have huns5 := cMainUnsaved_of_cs (cMainUnsaved_congr huns4) hcs5; have hpre5_sig := hpre4_sig.trans (by simp only [preMain_w64_l, preMain_pc_l, preMain_ps_l] at hpre5; exact hpre5); wp_steps 9; refine step_bl_to (pc := b + 64#64) (dst := L.beginShortBacktraceAddr) (by wn) (by wnh hrun5) hf16 ?_
  refine step_beginShortBacktrace_enter hcode.beginShortBacktrace_code (ret_pc := L.cMainAddr + 0x208#64) (F := ?_) (fun R hm => by simp only [wp_norm, arm64_norm, hsp4_eq, hsp5_eq, stackAt_190_split10] at hm ⊢; revert hm; sep_frame) (by wn) (by wnh hrun5) (by sp_al hsp_al5) (by rw [← hb]; wn) (by wn) fun sf hpcf hrunf hspf hsp_alf hx29f hlrf hcsf hpref => ?_
  refine SepWP.weaken_pre_frame (fun R hm => by have hx29_raw : s5.readReg64 (.gpr 29#5) = s.sp - 0x40#64 := hx29_5; rw [stackAt_210_split]; simp only [wp_norm, arm64_norm, hsp5_eq, hx29_raw, bv_lin_norm] at hm ⊢; ac_nf at hm ⊢) (hnext sf hpcf hrunf (by simpa [wp_norm, arm64_norm, hsp5_eq, bv_lin_norm] using hspf) hsp_alf (by simpa [wp_norm, arm64_norm, hsp5_eq, bv_lin_norm] using hx29f) hlrf (cMainUnsaved_of_cs (cMainUnsaved_congr huns5) hcsf) (hpre5_sig.trans (by simp only [preMain_w64_l, preMain_pc_l, preMain_mem_l] at hpref; exact hpref)))

/-- Step Rust `std`'s `c_main` wrapper from `L.cMainAddr` up to `L.userMainAddr` (`hasArgcGlobal = false/true`). -/
theorem step_cMain_preUserMain {P : Program} {L : StdBinaryLayout} {target_pc stage2Ret tp argvPtr vPage vArgv vArgc : BitVec 64} {argc : Nat} {haveLse : BitVec 8}
    (hcode : LangStartPreCode P L) (ops : StdMemOps P L.memcpyAddr L.memsetAddr) (atomics : StdOutlineAtomics P L.haveLseAtomicsAddr L.cas8RelaxAddr L.cas4AcqAddr L.cas8AcqAddr L.swp4RelAddr)
    (htid_align : MemWidth.isAligned .X64 L.threadIdCounterAddr = true := by decide) {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ (((L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (L.threadIdCounterAddr ↦₆₄ 0#64) ∗ ((tp + 16#64) ↦₆₄ 0#64) ∗ ((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ (L.pageSizeGlobalAddr ↦₆₄ vPage) ∗ (L.argvGlobalAddr ↦₆₄ vArgv) ∗ (if L.hasArgcGlobal then L.argcGlobalAddr ↦₆₄ vArgc else emp) ∗ stackAt s.sp 0x280) ∗ (F ∗ R)))
    (hpc : s.pc = L.cMainAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0x280 ≤ s.sp.toNat) (hlr : s.readReg64 .lr = stage2Ret)
    (hargc_in : if L.hasArgcGlobal then argc < 2 ^ 31 ∧ s.readReg64 .x0 = BitVec.ofNat 64 argc else True) (hx1 : s.readReg64 .x1 = argvPtr) (htp : s.tpidrEl0 = tp) (hsig0 : s.getSigAction 13#32 = {}) (hpoll_ok : evalPpollBytes s.fs stdioPollfdBytes 0 = some (stdioPollfdBytes, 0))
    (hnext : ∀ (sf : State) (w0 w1 w2 w3 wPad : BitVec 64), sf.pc = L.userMainAddr → sf.status = .Running → sf.sp = s.sp - 0x70#64 → sf.spAligned = true → sf.readReg64 .x29 = s.sp - 0x70#64 → sf.readReg64 .lr = L.beginShortBacktraceAddr + 12#64 → cMainUnsavedCalleeRegs L.hasArgcGlobal s sf → PreMainFieldsPreserved (s.setSigAction 13#32 (sigpipeIgnAction L)) sf →
      SepWP P target_pc sf (((L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (L.threadIdCounterAddr ↦₆₄ 1#64) ∗ ((tp + 16#64) ↦₆₄ 1#64) ∗ ((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ (L.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ (L.argvGlobalAddr ↦₆₄ argvPtr) ∗ (if L.hasArgcGlobal then L.argcGlobalAddr ↦₆₄ BitVec.ofNat 64 argc else emp) ∗ stackAt (s.sp - 0x70#64) 0x210 ∗ cMainSavedFrame L s stage2Ret w0 w1 w2 w3 wPad) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  have hcm := hcode.cMain_instrs; cases h_argc : L.hasArgcGlobal
  · simp only [h_argc, Bool.false_eq_true, ↓reduceIte] at hcm; rcases hcm with ⟨hpre_c, hloop_c, hmid_c⟩
    refine step_cMain_head_noArgc (haveLse := haveLse) (F := ?_) hcode hpre_c atomics htid_align hpc hrun hsp_align hsp_lo hlr hx1 htp hpoll_ok (fun R hm => by have h := hpre R hm; simp only [h_argc, Bool.false_eq_true, ↓reduceIte, emp_sepConj] at h; revert h; sep_frame) fun s2 w0 wPad hpc2 hrun2 hsp2 hsp_al2 hx19_2 hx29_2 huns2 hpre2 =>
      step_cMain_tail_noArgc (vPage := vPage) (vArgv := vArgv) (F := ?_) hcode ops hloop_c hmid_c hpc2 hrun2 hsp2 hsp_al2 hsp_lo hx19_2 hx29_2 huns2 hpre2 hsig0 (by intro R hm; sep_frame) fun sf hpcf hrunf hspf hsp_alf hx29f hlrf hunsf hpref =>
      SepWP.weaken_pre_frame (fun R hm => by dsimp only [cMainSavedFrame]; simp only [h_argc, Bool.false_eq_true, ↓reduceIte]; revert hm; sep_entail) (hnext sf w0 0#64 1#64 2#64 wPad hpcf hrunf hspf hsp_alf hx29f hlrf (by simpa [h_argc] using hunsf) hpref)
  · simp only [h_argc, ↓reduceIte] at hcm hargc_in; rcases hcm with ⟨hpre_c, hloop_c, hmid_c⟩; rcases hargc_in with ⟨hargc_lt, hx0⟩
    refine step_cMain_head_withArgc (haveLse := haveLse) (F := ?_) hcode hpre_c atomics htid_align hargc_lt hpc hrun hsp_align hsp_lo hlr hx0 hx1 htp hpoll_ok (fun R hm => by have h := hpre R hm; simp only [h_argc, ↓reduceIte] at h; revert h; sep_frame) fun s2 w3 hpc2 hrun2 hsp2 hsp_al2 hx19_2 hx22_2 hx29_2 huns2 hpre2 =>
      step_cMain_tail_withArgc (vPage := vPage) (vArgc := vArgc) (vArgv := vArgv) (F := ?_) hcode ops hloop_c hmid_c hpc2 hrun2 hsp2 hsp_al2 hsp_lo hx19_2 hx22_2 hx29_2 huns2 hpre2 hsig0 (by intro R hm; sep_frame) fun sf hpcf hrunf hspf hsp_alf hx29f hlrf hunsf hpref =>
      SepWP.weaken_pre_frame (fun R hm => by dsimp only [cMainSavedFrame]; simp only [h_argc, ↓reduceIte]; revert hm; sep_entail) (hnext sf 0#64 1#64 2#64 w3 0#64 hpcf hrunf hspf hsp_alf hx29f hlrf (by simpa [h_argc] using hunsf) hpref)
end ProofLib.StdStartup
