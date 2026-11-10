/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Write-Error Entry & Basic-Block Helpers for M5 Drop (Block `617`)

Basic-block step combinators and stack-frame carving helpers taking `M5ErrEntryPlaced`
(`M+0xbcc` / `0xbdc` / `0xbf4`) to `M+0xbf4` on Block `617` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.CodeLayout
open M5DropPlacedHelpers

macro "m5_drop_fetch_placed" : term =>
  `(by dsimp only [mProgPlaced]; simp only [arm64_norm]; try rfl)

/-! ## 1. Abstract `Program` Basic-Block Helpers with `BitVec 64` Branch Offsets -/

theorem step_bcc_zero_placed {prog : Program} {fnBase v38 v1b8 : BitVec 64}
    {s : State} {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3020#64) (hrun : s.status = .Running) (hal : s.spAligned)
    (hx23 : s.readReg64 (.gpr 23#5) = 0#64)
    (f0 : prog.fetch (fnBase + 3020#64) =
      some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 8#5) (AddrMode.Offset Reg.sp 56#64)))
    (f1 : prog.fetch (fnBase + 3024#64) =
      some (Instr.str MemWidth.X64 (Reg.gpr 8#5) (AddrMode.Offset Reg.sp 440#64)))
    (f2 : prog.fetch (fnBase + 3028#64) =
      some (Instr.cbz RegWidth.W64 true (Reg.gpr 23#5) 16#64))
    (f3 : prog.fetch (fnBase + 3032#64) =
      some (Instr.b 28#64))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3060#64 → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.symtab = s.symtab → s'.vregs = s.vregs → s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      Q s' (((s.sp + 56#64) ↦₆₄ v38) ∗ ((s.sp + 440#64) ↦₆₄ v38) ∗ R)) :
    SepWP prog (fnBase + 3060#64) s
      (((s.sp + 56#64) ↦₆₄ v38) ∗ ((s.sp + 440#64) ↦₆₄ v1b8) ∗ R) Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])

theorem step_bcc_dealloc_placed {prog : Program} {fnBase v38 v1b8 pathPtr pathCap bl : BitVec 64}
    {s : State} {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3020#64) (hrun : s.status = .Running) (hal : s.spAligned)
    (hx22 : s.readReg64 (.gpr 22#5) = pathPtr) (hx23 : s.readReg64 (.gpr 23#5) = pathCap)
    (hnez : pathCap ≠ 0#64)
    (f0 : prog.fetch (fnBase + 3020#64) =
      some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 8#5) (AddrMode.Offset Reg.sp 56#64)))
    (f1 : prog.fetch (fnBase + 3024#64) =
      some (Instr.str MemWidth.X64 (Reg.gpr 8#5) (AddrMode.Offset Reg.sp 440#64)))
    (f2 : prog.fetch (fnBase + 3028#64) =
      some (Instr.cbz RegWidth.W64 true (Reg.gpr 23#5) 16#64))
    (f4 : prog.fetch (fnBase + 3044#64) =
      some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 0#5) Reg.xzr (Reg.gpr 22#5) ShiftType.LSL 0))
    (f5 : prog.fetch (fnBase + 3048#64) =
      some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 1#5) Reg.xzr (Reg.gpr 23#5) ShiftType.LSL 0))
    (f6 : prog.fetch (fnBase + 3052#64) =
      some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 2#5) (1#16) 0))
    (f7 : prog.fetch (fnBase + 3056#64) =
      some (Instr.bl bl))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3056#64 + bl → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.symtab = s.symtab → s'.vregs = s.vregs → s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 .lr = fnBase + 3060#64 →
      s'.readReg64 (.gpr 0#5) = pathPtr → s'.readReg64 (.gpr 1#5) = pathCap →
      s'.readReg64 (.gpr 2#5) = 1#64 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      Q s' (((s.sp + 56#64) ↦₆₄ v38) ∗ ((s.sp + 440#64) ↦₆₄ v38) ∗ R)) :
    SepWP prog (fnBase + 3056#64 + bl) s
      (((s.sp + 56#64) ↦₆₄ v38) ∗ ((s.sp + 440#64) ↦₆₄ v1b8) ∗ R) Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])

theorem step_bdc_dealloc_placed {prog : Program} {fnBase v38 v1b8 pathPtr pathCap bl : BitVec 64}
    {s : State} {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3036#64) (hrun : s.status = .Running) (hal : s.spAligned)
    (hx22 : s.readReg64 (.gpr 22#5) = pathPtr) (hx23 : s.readReg64 (.gpr 23#5) = pathCap)
    (f0 : prog.fetch (fnBase + 3036#64) =
      some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 8#5) (AddrMode.Offset Reg.sp 56#64)))
    (f1 : prog.fetch (fnBase + 3040#64) =
      some (Instr.str MemWidth.X64 (Reg.gpr 8#5) (AddrMode.Offset Reg.sp 440#64)))
    (f4 : prog.fetch (fnBase + 3044#64) =
      some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 0#5) Reg.xzr (Reg.gpr 22#5) ShiftType.LSL 0))
    (f5 : prog.fetch (fnBase + 3048#64) =
      some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 1#5) Reg.xzr (Reg.gpr 23#5) ShiftType.LSL 0))
    (f6 : prog.fetch (fnBase + 3052#64) =
      some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 2#5) (1#16) 0))
    (f7 : prog.fetch (fnBase + 3056#64) =
      some (Instr.bl bl))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3056#64 + bl → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.symtab = s.symtab → s'.vregs = s.vregs → s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 .lr = fnBase + 3060#64 →
      s'.readReg64 (.gpr 0#5) = pathPtr → s'.readReg64 (.gpr 1#5) = pathCap →
      s'.readReg64 (.gpr 2#5) = 1#64 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      Q s' (((s.sp + 56#64) ↦₆₄ v38) ∗ ((s.sp + 440#64) ↦₆₄ v38) ∗ R)) :
    SepWP prog (fnBase + 3056#64 + bl) s
      (((s.sp + 56#64) ↦₆₄ v38) ∗ ((s.sp + 440#64) ↦₆₄ v1b8) ∗ R) Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])

theorem step_bf4_pre_placed {prog : Program} {fnBase curCap curPtr v30 : BitVec 64}
    {s : State} {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3060#64) (hrun : s.status = .Running) (hal : s.spAligned)
    (f0 : prog.fetch (fnBase + 3060#64) =
      some (Instr.ldp RegWidth.W64 false (Reg.gpr 22#5) (Reg.gpr 25#5) (AddrMode.Offset Reg.sp 40#64)))
    (f1 : prog.fetch (fnBase + 3064#64) =
      some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 23#5) (AddrMode.Offset Reg.sp 32#64)))
    (f2 : prog.fetch (fnBase + 3068#64) =
      some (Instr.addSubImm RegWidth.W64 AddSubOp.ADD (Reg.gpr 21#5) (Reg.gpr 22#5) (32#12) false))
    (f3 : prog.fetch (fnBase + 3072#64) =
      some (Instr.b 16#64))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3088#64 → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.mem = s.mem → s'.symtab = s.symtab → s'.vregs = s.vregs →
      s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 21#5) = curPtr + 32#64 →
      s'.readReg64 (.gpr 22#5) = curPtr →
      s'.readReg64 (.gpr 23#5) = curCap →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      s'.readReg64 (.gpr 25#5) = v30 →
      Q s' (((s.sp + 32#64) ↦₆₄ curCap) ∗ ((s.sp + 40#64) ↦₆₄ curPtr) ∗
        ((s.sp + 48#64) ↦₆₄ v30) ∗ R)) :
    SepWP prog (fnBase + 3088#64) s
      (((s.sp + 32#64) ↦₆₄ curCap) ∗ ((s.sp + 40#64) ↦₆₄ curPtr) ∗
        ((s.sp + 48#64) ↦₆₄ v30) ∗ R) Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])

theorem step_c3c_dealloc_placed {prog : Program} {fnBase curPtr curCap bl : BitVec 64}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3132#64) (hrun : s.status = .Running)
    (hx22 : s.readReg64 (.gpr 22#5) = curPtr) (hx23 : s.readReg64 (.gpr 23#5) = curCap)
    (hnez : curCap ≠ 0#64)
    (c0 : prog.fetch (fnBase + 3132#64) =
      some (Instr.cbz RegWidth.W64 false (Reg.gpr 23#5) 24#64))
    (c1 : prog.fetch (fnBase + 3136#64) =
      some (Instr.addSubShift RegWidth.W64 AddSubOp.ADD (Reg.gpr 8#5) (Reg.gpr 23#5) (Reg.gpr 23#5) ShiftType.LSL 1))
    (c2 : prog.fetch (fnBase + 3140#64) =
      some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 0#5) Reg.xzr (Reg.gpr 22#5) ShiftType.LSL 0))
    (c3 : prog.fetch (fnBase + 3144#64) =
      some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 2#5) (8#16) 0))
    (c4 : prog.fetch (fnBase + 3148#64) =
      some (Instr.bitfield RegWidth.W64 BitfieldOp.UBFM (Reg.gpr 1#5) (Reg.gpr 8#5) 60 59))
    (c5 : prog.fetch (fnBase + 3152#64) =
      some (Instr.bl bl))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3152#64 + bl → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.mem = s.mem → s'.symtab = s.symtab → s'.vregs = s.vregs →
      s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 .lr = fnBase + 3156#64 →
      s'.readReg64 (.gpr 0#5) = curPtr → s'.readReg64 (.gpr 1#5) = curCap * 48#64 →
      s'.readReg64 (.gpr 2#5) = 8#64 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      s'.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) →
      Q s' P) :
    SepWP prog (fnBase + 3152#64 + bl) s P Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]; bv_bits) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])

theorem step_c54_post_placed {prog : Program} {fnBase v38 : BitVec 64}
    {s : State} {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3156#64) (hrun : s.status = .Running) (hal : s.spAligned)
    (m0 : prog.fetch (fnBase + 3156#64) =
      some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 23#5) (AddrMode.Offset Reg.sp 56#64)))
    (m1 : prog.fetch (fnBase + 3160#64) =
      some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 22#5) (1#16) 0))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3164#64 → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.mem = s.mem → s'.symtab = s.symtab → s'.vregs = s.vregs →
      s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 22#5) = 1#64 →
      s'.readReg64 (.gpr 23#5) = v38 →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      s'.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) →
      Q s' (((s.sp + 56#64) ↦₆₄ v38) ∗ R)) :
    SepWP prog (fnBase + 3164#64) s (((s.sp + 56#64) ↦₆₄ v38) ∗ R) Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])

theorem step_c5c_eq8_placed {prog : Program} {fnBase : BitVec 64}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3164#64) (hrun : s.status = .Running)
    (hx23 : s.readReg64 (.gpr 23#5) = 8#64)
    (d0 : prog.fetch (fnBase + 3164#64) =
      some (Instr.addSubImm RegWidth.W64 AddSubOp.SUBS Reg.xzr (Reg.gpr 23#5) (8#12) false))
    (d1 : prog.fetch (fnBase + 3168#64) =
      some (Instr.bCond CondCode.EQ 784#64))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3952#64 → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.mem = s.mem → s'.symtab = s.symtab → s'.vregs = s.vregs →
      s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      Q s' P) :
    SepWP prog (fnBase + 3952#64) s P Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])

theorem step_c5c_ne8_placed {prog : Program} {fnBase v23 v25 : BitVec 64}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3164#64) (hrun : s.status = .Running)
    (hx23 : s.readReg64 (.gpr 23#5) = v23) (hx25 : s.readReg64 (.gpr 25#5) = v25)
    (hne8 : v23 ≠ 8#64)
    (d0 : prog.fetch (fnBase + 3164#64) =
      some (Instr.addSubImm RegWidth.W64 AddSubOp.SUBS Reg.xzr (Reg.gpr 23#5) (8#12) false))
    (d1 : prog.fetch (fnBase + 3168#64) =
      some (Instr.bCond CondCode.EQ 784#64))
    (d2 : prog.fetch (fnBase + 3172#64) =
      some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 8#5) (40#16) 0))
    (d3 : prog.fetch (fnBase + 3176#64) =
      some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 26#5) Reg.xzr (Reg.gpr 23#5) ShiftType.LSL 0))
    (d4 : prog.fetch (fnBase + 3180#64) =
      some (Instr.dataProc3 RegWidth.W64 DataProc3Op.MADD (Reg.gpr 23#5) (Reg.gpr 23#5) (Reg.gpr 8#5) (Reg.gpr 25#5)))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3184#64 → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.mem = s.mem → s'.symtab = s.symtab → s'.vregs = s.vregs →
      s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      s'.readReg64 (.gpr 23#5) = v25 + v23 * 40#64 →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      s'.readReg64 (.gpr 26#5) = v23 →
      Q s' P) :
    SepWP prog (fnBase + 3184#64) s P Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl])

/-! ## 2. Stack Frame Helpers & Step A: `M5ErrEntryPlaced` (`0xbcc` / `0xbdc` / `0xbf4`) → `0xbf4` -/

private theorem localsCtx_pull (fsp : BitVec 64) (off : Nat)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat)
    (m₁ : List (Nat × Nat × SepProp)) (o₂ n₂ : Nat) (tail : List (Nat × Nat × SepProp)) :
    ∃ Ctx : SepProp, ∀ P : SepProp,
      localsCtx fsp off cs₁ o n (m₁ ++ (o₂, n₂, P) :: tail) = P ∗ Ctx := by
  induction cs₁ generalizing off with
  | nil =>
    refine ⟨localsCtx fsp (o + n) m₁ o₂ n₂ tail ∗ memRegion (fsp + BitVec.ofNat 64 off) (o - off),
      fun P => ?_⟩
    simp only [localsCtx, localsFrom_focus]
    ac_rfl
  | cons c cs₁ ih =>
    rcases c with ⟨o₁, n₁, P₁⟩
    obtain ⟨Ctx', hCtx'⟩ := ih (o₁ + n₁)
    refine ⟨memRegion (fsp + BitVec.ofNat 64 off) (o₁ - off) ∗ P₁ ∗ Ctx', fun P => ?_⟩
    simp only [localsCtx, hCtx' P]
    ac_rfl

private theorem m5ErrCellsPlaced_open_38_1b8 (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64)
    (g : StoresGhost) {k : Nat} (hk : k < 8) :
    ∃ Ctx : SepProp,
      (locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) =
        ∃∗ v : BitVec 64,
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ ((fsp + 440#64) ↦₆₄ v) ∗ Ctx) ∧
      (∀ w : BitVec 64,
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ ((fsp + 440#64) ↦₆₄ w) ∗ Ctx ⊢
          locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k)) := by
  let pre38 : List (Nat × Nat × SepProp) :=
    [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap, cell fsp 0x18 outPtr,
     cell fsp 0x20 curCap, cell fsp 0x28 curPtr, cell fsp 0x30 (fsp + 0x1c8#64)]
  let mid : List (Nat × Nat × SepProp) :=
    [cell fsp 0x50 inPtr]
  let tail : List (Nat × Nat × SepProp) :=
    [(0x1c8 + 0x28 * (k + 1), 0x28 * (8 - (k + 1)),
      dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)))]
  let cs1 : List (Nat × Nat × SepProp) :=
    pre38 ++ (cell fsp 0x38 (BitVec.ofNat 64 (k + 1)) :: mid)
  have heq_cells :
      m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k = cs1 ++ tail := rfl
  have hcarve := locals_carve_cell fsp cs1 0x1b8 tail
    (by simp [cs1, pre38, mid, localsEnd])
    (by simp [tail, localsBound]; omega)
    (by simp [tail, localsBound]; omega)
  have hfoc_both :
      ∀ w : BitVec 64,
        locals fsp (cs1 ++ cell fsp 0x1b8 w :: tail) =
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
            localsCtx fsp 0 pre38 0x38 8 (mid ++ cell fsp 0x1b8 w :: tail) :=
    fun w => locals_focus fsp pre38 0x38 8 ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1))
      (mid ++ cell fsp 0x1b8 w :: tail)
  obtain ⟨ctx, hctx_split⟩ := localsCtx_pull fsp 0 pre38 0x38 8 mid 0x1b8 8 tail
  refine ⟨ctx, ?_, ?_⟩
  · rw [heq_cells, hcarve]
    congr 1; funext v
    rw [hfoc_both v, hctx_split ((fsp + 440#64) ↦₆₄ v)]
  · intro w
    rw [← hctx_split ((fsp + 440#64) ↦₆₄ w), ← hfoc_both w, heq_cells]
    exact locals_forget_cell fsp cs1 0x1b8 w tail
      (by simp [cs1, pre38, mid, localsEnd])
      (by simp [tail, localsBound]; omega)
      (by simp [tail, localsBound]; omega)

private theorem m5ErrCellsPlaced_open_frame (A : RustAlloc)
    {fsp sp outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64}
    (hsp : sp = fsp) (g : StoresGhost) {k : Nat} (hk : k < 8)
    (Pre Post : SepProp) (stk : Nat) :
    ∃ Ctx : SepProp,
      (Pre ∗ (locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
          (A.pool ∗ (stackAt fsp (stk - mainFrameSize) ∗ Post))) =
        Pre ∗ ((∃∗ v : BitVec 64,
          ((sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ ((sp + 440#64) ↦₆₄ v) ∗ Ctx) ∗
          (A.pool ∗ (stackAt sp (stk - mainFrameSize) ∗ Post)))) ∧
      (∀ w : BitVec 64,
        ((sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ ((sp + 440#64) ↦₆₄ w) ∗ Ctx ⊢
          locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k)) := by
  subst hsp
  obtain ⟨Ctx, hopen, hclose⟩ :=
    m5ErrCellsPlaced_open_38_1b8 A sp outCap outPtr outLen inCap inPtr curCap curPtr g hk
  exact ⟨Ctx, by rw [hopen], hclose⟩

theorem m5ErrCellsPlaced_open_spills (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64)
    (g : StoresGhost) (k : Nat) :
    ∃ Ctx : SepProp,
      locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) =
        ((fsp + 32#64) ↦₆₄ curCap) ∗
        ((fsp + 40#64) ↦₆₄ curPtr) ∗
        ((fsp + 48#64) ↦₆₄ (fsp + 0x1c8#64)) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ Ctx := by
  let head9 : List (Nat × Nat × SepProp) :=
    [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap, cell fsp 0x18 outPtr,
     cell fsp 0x20 curCap, cell fsp 0x28 curPtr, cell fsp 0x30 (fsp + 0x1c8#64),
     cell fsp 0x38 (BitVec.ofNat 64 (k + 1)), cell fsp 0x50 inPtr]
  let tail : List (Nat × Nat × SepProp) :=
    [(0x1c8 + 0x28 * (k + 1), 0x28 * (8 - (k + 1)),
      dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)))]
  have heq9 :
      m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k = head9 ++ tail := rfl
  refine ⟨memRegion (fsp + BitVec.ofNat 64 0) 0 ∗
    ((fsp + 0#64) ↦₆₄ outLen) ∗ memRegion (fsp + 8#64) 0 ∗
    ((fsp + 8#64) ↦₆₄ outCap) ∗ memRegion (fsp + 16#64) 0 ∗
    ((fsp + 16#64) ↦₆₄ inCap) ∗ memRegion (fsp + 24#64) 0 ∗
    ((fsp + 24#64) ↦₆₄ outPtr) ∗ memRegion (fsp + 32#64) 0 ∗
    memRegion (fsp + 40#64) 0 ∗ memRegion (fsp + 48#64) 0 ∗
    memRegion (fsp + 56#64) 0 ∗ memRegion (fsp + 64#64) 16 ∗
    ((fsp + 80#64) ↦₆₄ inPtr) ∗ localsFrom fsp 88 tail, ?_⟩
  rw [heq9]
  change localsFrom fsp 0 (head9 ++ tail) = _
  dsimp only [head9, cell, localsFrom, List.cons_append, List.nil_append, Nat.reduceAdd, Nat.reduceSub]
  ac_rfl

theorem m5ErrCellsPlaced_focus_tail (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64)
    (g : StoresGhost) (k : Nat) :
    let pre9 : List (Nat × Nat × SepProp) :=
      [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap,
       cell fsp 0x18 outPtr, cell fsp 0x20 curCap, cell fsp 0x28 curPtr,
       cell fsp 0x30 (fsp + 0x1c8#64), cell fsp 0x38 (BitVec.ofNat 64 (k + 1)), cell fsp 0x50 inPtr]
    locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) =
      dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)) ∗
        localsCtx fsp 0 pre9 (0x1c8 + 0x28 * (k + 1)) (0x28 * (8 - (k + 1))) [] :=
  locals_focus fsp
    [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap,
     cell fsp 0x18 outPtr, cell fsp 0x20 curCap, cell fsp 0x28 curPtr,
     cell fsp 0x30 (fsp + 0x1c8#64), cell fsp 0x38 (BitVec.ofNat 64 (k + 1)), cell fsp 0x50 inPtr]
    (0x1c8 + 0x28 * (k + 1)) (0x28 * (8 - (k + 1)))
    (dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)))
    []

theorem m5_err_to_bf4_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks}
    {ret : BitVec 64} {s0 s : State} {stk k : Nat}
    {outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64}
    {g : StoresGhost} {e : M5ErrEntryPlaced}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hk : k < 8)
    (hs : InMainPlaced CodeOk s0 s e.pcOff)
    (herr : e.regs s)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm 0xbf4 →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5ErrCellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize)
            outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
          A.pool ∗ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (e.heap A ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5ErrCellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize)
            outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
        A.pool ∗ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
      Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hsp : s.sp = fsp := hs.sp
  cases e with
  | bf4 =>
    dsimp only [M5ErrEntryPlaced.heap, M5ErrEntryPlaced.pcOff] at hs ⊢
    refine SepWPp.weaken_pre (Entails.of_eq (emp_sepConj _)) ?_
    exact hnext s hs rfl rfl rfl rfl rfl
  | bcc pathCap pathPtr pathBs =>
    dsimp only [M5ErrEntryPlaced.heap, M5ErrEntryPlaced.pcOff, M5ErrEntryPlaced.regs] at hs herr ⊢
    rcases herr with ⟨hx22, hx23⟩
    unfold ownedBytes
    simp only [sepConj_assoc]
    apply SepWPp.pure_elim
    rintro ⟨_, hlen, hcap_lt, _⟩
    obtain ⟨Ctx, hopen, hclose⟩ := m5ErrCellsPlaced_open_frame A hs.sp g hk _ F stk
    refine SepWPp.weaken_pre (Entails.of_eq hopen) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro v1b8
    by_cases hcap0 : pathCap = 0#64
    · subst hcap0
      have hz0 : (0#64 : BitVec 64) = 0 := rfl
      simp only [hz0, ite_true, emp_sepConj, sepConj_assoc]
      apply seq_frozen_codeOk (mid := mPcPlaced 0xbf4) hs.inv
      refine step_bcc_zero_placed (fnBase := (blkPl_617).base) hs.pc hs.run hs.spAligned_state hx23
        m5_drop_fetch_placed m5_drop_fetch_placed
        m5_drop_fetch_placed m5_drop_fetch_placed ?_
      intro s1 hpcm hrunm hsp1 hfp1 hsym1 hv1 hfs1 htr1 hx19_1 hx20_1 hx24_1 _ _ hfz
      refine SepWPp.weaken_pre (P' :=
        locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
          A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗ F) ?_ ?_
      · refine Entails.trans (Entails.of_eq (show
          ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
            ((s.sp + 440#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
            (Ctx ∗ (A.pool ∗ (stackAt s.sp (stk - mainFrameSize) ∗ F))) =
          (((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
            ((s.sp + 440#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ Ctx) ∗
            (A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗ F) by rw [hsp]; ac_rfl)) ?_
        exact sepConj_mono_left (hclose (BitVec.ofNat 64 (k + 1)))
      · exact hnext s1
          (InMainPlaced.step_store hs hpcm hrunm hfz hsp1 hfp1
            (by simp only [calleeSavedVRegs, hv1]))
          hx19_1 hx20_1 hx24_1 hfs1 htr1
    · have hcap0' : pathCap ≠ 0 := hcap0
      simp only [hcap0', ite_false, sepConj_assoc]
      have hlay := layoutOk_u8_of_cap_ne_zero hcap0 hcap_lt
      have hmerge :
          (pathPtr ↦ₛ pathBs) ∗
            memRegion (pathPtr + BitVec.ofNat 64 pathBs.length) (pathCap.toNat - pathBs.length) ⊢
          memRegion pathPtr pathCap.toNat :=
        ProofLib.pointsToBytes_memRegion_entails pathPtr pathBs pathCap.toNat hlen (by omega)
      let bl : BitVec 64 := (lsρ lsRustDeallocSymCli - (blkPl_617).base) - 3056#64
      have hbl : (blkPl_617).base + 3056#64 + bl = lsρ lsRustDeallocSymCli :=
        mPcPlaced_bl_dealloc 3056
      refine SepWPp.weaken_pre (Entails.of_eq (show
        A.live pathPtr pathCap.toNat 1 ∗ (pathPtr ↦ₛ pathBs) ∗
          memRegion (pathPtr + BitVec.ofNat 64 pathBs.length) (pathCap.toNat - pathBs.length) ∗
          ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          ((s.sp + 440#64) ↦₆₄ v1b8) ∗ Ctx ∗
          A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F =
        ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          ((s.sp + 440#64) ↦₆₄ v1b8) ∗
          (A.live pathPtr pathCap.toNat 1 ∗
            ((pathPtr ↦ₛ pathBs) ∗
              memRegion (pathPtr + BitVec.ofNat 64 pathBs.length)
                (pathCap.toNat - pathBs.length)) ∗
            Ctx ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by ac_rfl)) ?_
      apply seq_frozen_codeOk (mid := (blkPl_617).base + 3056#64 + bl) hs.inv
      refine step_bcc_dealloc_placed (fnBase := (blkPl_617).base) (bl := bl)
        hs.pc hs.run hs.spAligned_state hx22 hx23 hcap0
        m5_drop_fetch_placed m5_drop_fetch_placed
        m5_drop_fetch_placed m5_drop_fetch_placed
        m5_drop_fetch_placed m5_drop_fetch_placed
        m5_drop_fetch_placed ?_
      intro s1 hpcm hrunm hsp1 hfp1 hsym1 hv1 hfs1 htr1 hlr1 hx0_1 hx1_1 hx2_1
        hx19_1 hx20_1 hx24_1 _ _ hfz
      refine step_dealloc_placed (sub := stk - mainFrameSize)
        (F := locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗ F)
        hA (by omega) (by omega)
        hfz
        (hpcm.trans hbl) hrunm
        (by simpa only [State.spAligned, hsp1] using hs.spAligned_state)
        hlr1 hx0_1
        (congrArg BitVec.toNat hx1_1)
        (by rw [hx2_1]; decide)
        hlay
        ?_ ?_
      · refine Entails.trans (Entails.of_eq (show
          ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
            ((s.sp + 440#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
            (A.live pathPtr pathCap.toNat 1 ∗
              ((pathPtr ↦ₛ pathBs) ∗
                memRegion (pathPtr + BitVec.ofNat 64 pathBs.length)
                  (pathCap.toNat - pathBs.length)) ∗
              Ctx ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) =
          (A.live pathPtr pathCap.toNat 1 ∗
            ((pathPtr ↦ₛ pathBs) ∗
              memRegion (pathPtr + BitVec.ofNat 64 pathBs.length)
                (pathCap.toNat - pathBs.length))) ∗
            ((((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
              ((s.sp + 440#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ Ctx) ∗
              A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono (sepConj_mono_right hmerge) (sepConj_mono_left (hclose (BitVec.ofNat 64 (k + 1))))) ?_
        exact Entails.of_eq (by rw [hsp1]; ac_rfl)
      · intro sm hpcm' hrunm' hspm' hcsm hinv' hfsm htrm
        refine SepWPp.weaken_pre (P' :=
          locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
            A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗ F)
          (Entails.of_eq (by rw [hsp1, hsp]; ac_rfl)) ?_
        exact hnext sm
          (hs.mk_step hpcm' hrunm' (hspm'.trans hsp1)
            (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp1) hinv'
            (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, hv1])))
          (hcsm.1.trans hx19_1) (hcsm.2.1.trans hx20_1)
          (hcsm.2.2.2.2.2.1.trans hx24_1) (hfsm.trans hfs1) (htrm.trans htr1)
  | bdc pathCap pathPtr pathBs =>
    dsimp only [M5ErrEntryPlaced.heap, M5ErrEntryPlaced.pcOff, M5ErrEntryPlaced.regs] at hs herr ⊢
    rcases herr with ⟨hx22, hx23, hcap0⟩
    have hcap0' : pathCap ≠ 0 := hcap0
    unfold ownedBytes
    simp only [hcap0', ite_false, sepConj_assoc]
    apply SepWPp.pure_elim
    rintro ⟨_, hlen, hcap_lt, _⟩
    have hlay := layoutOk_u8_of_cap_ne_zero hcap0 hcap_lt
    have hmerge :
        (pathPtr ↦ₛ pathBs) ∗
          memRegion (pathPtr + BitVec.ofNat 64 pathBs.length) (pathCap.toNat - pathBs.length) ⊢
        memRegion pathPtr pathCap.toNat :=
      ProofLib.pointsToBytes_memRegion_entails pathPtr pathBs pathCap.toNat hlen (by omega)
    obtain ⟨Ctx, hopen, hclose⟩ :=
      m5ErrCellsPlaced_open_38_1b8 A s.sp outCap outPtr outLen inCap inPtr curCap curPtr g hk
    refine SepWPp.weaken_pre (P' :=
      A.live pathPtr pathCap.toNat 1 ∗ (pathPtr ↦ₛ pathBs) ∗
        memRegion (pathPtr + BitVec.ofNat 64 pathBs.length) (pathCap.toNat - pathBs.length) ∗
        (∃∗ v : BitVec 64,
          ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ ((s.sp + 440#64) ↦₆₄ v) ∗ Ctx) ∗
        A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F)
      (Entails.of_eq (by rw [← hs.sp, hopen])) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v1b8
    let bl : BitVec 64 := (lsρ lsRustDeallocSymCli - (blkPl_617).base) - 3056#64
    have hbl : (blkPl_617).base + 3056#64 + bl = lsρ lsRustDeallocSymCli :=
      mPcPlaced_bl_dealloc 3056
    refine SepWPp.weaken_pre (Entails.of_eq (show
      A.live pathPtr pathCap.toNat 1 ∗ (pathPtr ↦ₛ pathBs) ∗
        memRegion (pathPtr + BitVec.ofNat 64 pathBs.length) (pathCap.toNat - pathBs.length) ∗
        ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
        ((s.sp + 440#64) ↦₆₄ v1b8) ∗ Ctx ∗
        A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F =
      ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
        ((s.sp + 440#64) ↦₆₄ v1b8) ∗
        (A.live pathPtr pathCap.toNat 1 ∗
          ((pathPtr ↦ₛ pathBs) ∗
            memRegion (pathPtr + BitVec.ofNat 64 pathBs.length)
              (pathCap.toNat - pathBs.length)) ∗
          Ctx ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by ac_rfl)) ?_
    apply seq_frozen_codeOk (mid := (blkPl_617).base + 3056#64 + bl) hs.inv
    refine step_bdc_dealloc_placed (fnBase := (blkPl_617).base) (bl := bl)
      hs.pc hs.run hs.spAligned_state hx22 hx23
      m5_drop_fetch_placed m5_drop_fetch_placed
      m5_drop_fetch_placed m5_drop_fetch_placed
      m5_drop_fetch_placed m5_drop_fetch_placed ?_
    intro s1 hpcm hrunm hsp1 hfp1 hsym1 hv1 hfs1 htr1 hlr1 hx0_1 hx1_1 hx2_1
      hx19_1 hx20_1 hx24_1 _ _ hfz
    refine step_dealloc_placed (sub := stk - mainFrameSize)
      (F := locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗ F)
      hA (by omega) (by omega)
      hfz
      (hpcm.trans hbl) hrunm
      (by simpa only [State.spAligned, hsp1] using hs.spAligned_state)
      hlr1 hx0_1
      (congrArg BitVec.toNat hx1_1)
      (by rw [hx2_1]; decide)
      hlay
      ?_ ?_
    · refine Entails.trans (Entails.of_eq (show
        ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          ((s.sp + 440#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          (A.live pathPtr pathCap.toNat 1 ∗
            ((pathPtr ↦ₛ pathBs) ∗
              memRegion (pathPtr + BitVec.ofNat 64 pathBs.length)
                (pathCap.toNat - pathBs.length)) ∗
            Ctx ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) =
        (A.live pathPtr pathCap.toNat 1 ∗
          ((pathPtr ↦ₛ pathBs) ∗
            memRegion (pathPtr + BitVec.ofNat 64 pathBs.length)
              (pathCap.toNat - pathBs.length))) ∗
          ((((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
            ((s.sp + 440#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ Ctx) ∗
            A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by ac_rfl)) ?_
      refine Entails.trans
        (sepConj_mono (sepConj_mono_right hmerge) (sepConj_mono_left (hclose (BitVec.ofNat 64 (k + 1))))) ?_
      exact Entails.of_eq (by rw [hsp1, hsp]; ac_rfl)
    · intro sm hpcm' hrunm' hspm' hcsm hinv' hfsm htrm
      refine SepWPp.weaken_pre (P' :=
        locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
          A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗ F)
        (Entails.of_eq (by rw [hsp1, hsp]; ac_rfl)) ?_
      exact hnext sm
        (hs.mk_step hpcm' hrunm' (hspm'.trans hsp1)
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp1) hinv'
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, hv1])))
        (hcsm.1.trans hx19_1) (hcsm.2.1.trans hx20_1)
        (hcsm.2.2.2.2.2.1.trans hx24_1) (hfsm.trans hfs1) (htrm.trans htr1)

end CryptoVerification.SignalSession.Cli.MainHops
