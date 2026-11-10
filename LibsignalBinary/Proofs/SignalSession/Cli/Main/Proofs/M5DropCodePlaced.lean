/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5IfacePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Code Typeclasses for M5 Drop Loops (Block `617`)

Defines register encodings (`DropLoopRegsPlaced`) and `[LibsignalPlacement]` instruction-fetch
typeclasses (`DropLoopCodePlaced`, `DropDirCodePlaced`, `DropDirCmpCodePlaced`) for the `(String, Vec<u8>)`
and unrolled `Dir` drop blocks on Block `617`.
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

/-- Pure `State`-field projection simp set for `[LibsignalPlacement]` M5 drop proofs. -/
register_simp_attr m5_st_pl

/-- Register pair `(counter, pointer)` used by the nine `(String, Vec<u8>)` drop loops in `main`. -/
inductive DropLoopRegsPlaced where
  | r20_21
  | r20_25
  deriving DecidableEq

/-- Counter GPR index (`20`). -/
def DropLoopRegsPlaced.rc : DropLoopRegsPlaced → BitVec 5
  | .r20_21 => 20#5
  | .r20_25 => 20#5

/-- Pointer GPR index (`21` or `25`). -/
def DropLoopRegsPlaced.rp : DropLoopRegsPlaced → BitVec 5
  | .r20_21 => 21#5
  | .r20_25 => 25#5

/-- `Reg` encoding of the counter register (`x20`). -/
def DropLoopRegsPlaced.rcZr : DropLoopRegsPlaced → Reg
  | .r20_21 => .gpr 20#5
  | .r20_25 => .gpr 20#5

/-- `Reg` encoding of the counter register (`x20`). -/
def DropLoopRegsPlaced.rcSp : DropLoopRegsPlaced → Reg
  | .r20_21 => .gpr 20#5
  | .r20_25 => .gpr 20#5

/-- `Reg` encoding of the pointer register (`x21` or `x25`). -/
def DropLoopRegsPlaced.rpSp : DropLoopRegsPlaced → Reg
  | .r20_21 => .gpr 21#5
  | .r20_25 => .gpr 25#5

/-- Every callee-saved GPR `x19 .. x29` other than `rc` and `rp` keeps its value from `s` to `sm`. -/
def DropLoopRegsPlaced.keeps (regs : DropLoopRegsPlaced) (s sm : State) : Prop :=
  ∀ r : BitVec 5,
    19 ≤ r.toNat → r.toNat ≤ 29 →
    r ≠ regs.rc → r ≠ regs.rp →
    sm.readReg64 (.gpr r) = s.readReg64 (.gpr r)

theorem mPcPlaced_eq_blkPl_drop [LibsignalPlacement] (off : Nat) :
    mPcPlaced off = (blkPl_617).base + BitVec.ofNat 64 off := rfl

macro "m5_drop_placed_field" : tactic =>
  `(tactic| (intros; dsimp only [mProgPlaced, DropLoopRegsPlaced.rcZr, DropLoopRegsPlaced.rcSp, DropLoopRegsPlaced.rpSp]; rw [mPcPlaced_eq_blkPl_drop]; simp only [Nat.reduceAdd, Nat.reduceSub, arm64_norm]))

/-! ## 1. Generic 14-Instruction `(String, Vec<u8>)` Drop Loop Code Typeclass -/

/-- Relocatable `[LibsignalPlacement]` instruction-fetch bundle for a 14-instruction
`(String, Vec<u8>)` entry drop loop on Block `617` (`mProgPlaced H`) with header at offset `h`,
exit branch target `exit`, and loop registers `regs`. -/
class DropLoopCodePlaced [LibsignalPlacement] (h exit : Nat) (regs : DropLoopRegsPlaced) : Prop where
  hexit : h + 8 ≤ exit ∧ exit ≤ 4096
  f0 : ∀ H, (mProgPlaced H).fetch (mPcPlaced h) =
    some (Instr.addSubImm RegWidth.W64 AddSubOp.SUBS regs.rcZr regs.rcSp (1#12) false)
  f4 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 4)) =
    some (Instr.addSubImm RegWidth.W64 AddSubOp.ADD regs.rpSp regs.rpSp (48#12) false)
  f8 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 8)) =
    some (Instr.bCond CondCode.EQ (BitVec.ofNat 64 (exit - (h + 8))))
  f12 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 12)) =
    some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 1#5)
      (AddrMode.UnscaledOffset regs.rpSp (-32#64)))
  f16 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 16)) =
    some (Instr.cbz RegWidth.W64 false (Reg.gpr 1#5) 16#64)
  f20 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 20)) =
    some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 0#5)
      (AddrMode.UnscaledOffset regs.rpSp (-24#64)))
  f24 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 24)) =
    some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 2#5) (1#16) 0)
  f28 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 28)) =
    some (Instr.bl ((lsρ lsRustDeallocSymCli - (blkPl_617).base) - BitVec.ofNat 64 (h + 28)))
  f32 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 32)) =
    some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 1#5)
      (AddrMode.UnscaledOffset regs.rpSp (-8#64)))
  f36 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 36)) =
    some (Instr.cbz RegWidth.W64 false (Reg.gpr 1#5) (-36#64))
  f40 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 40)) =
    some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 0#5)
      (AddrMode.Offset regs.rpSp 0#64))
  f44 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 44)) =
    some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 2#5) (1#16) 0)
  f48 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 48)) =
    some (Instr.bl ((lsρ lsRustDeallocSymCli - (blkPl_617).base) - BitVec.ofNat 64 (h + 48)))
  f52 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (h + 52)) =
    some (Instr.b (-52#64))

macro "mk_drop_loop_placed " h:num exit:num regs:term : term =>
  `({ hexit := by decide
      f0 := by m5_drop_placed_field
      f4 := by m5_drop_placed_field
      f8 := by m5_drop_placed_field
      f12 := by m5_drop_placed_field
      f16 := by m5_drop_placed_field
      f20 := by m5_drop_placed_field
      f24 := by m5_drop_placed_field
      f28 := by m5_drop_placed_field
      f32 := by m5_drop_placed_field
      f36 := by m5_drop_placed_field
      f40 := by m5_drop_placed_field
      f44 := by m5_drop_placed_field
      f48 := by m5_drop_placed_field
      f52 := by m5_drop_placed_field : DropLoopCodePlaced $h $exit $regs })

instance instDropLoopPlaced_0xa84 [LibsignalPlacement] :
    DropLoopCodePlaced 0xa84 0xabc .r20_21 :=
  mk_drop_loop_placed 2692 2748 .r20_21

instance instDropLoopPlaced_0xc04 [LibsignalPlacement] :
    DropLoopCodePlaced 0xc04 0xc3c .r20_21 :=
  mk_drop_loop_placed 3076 3132 .r20_21

instance instDropLoopPlaced_0xc80 [LibsignalPlacement] :
    DropLoopCodePlaced 0xc80 0xcb8 .r20_25 :=
  mk_drop_loop_placed 3200 3256 .r20_25

instance instDropLoopPlaced_0xcec [LibsignalPlacement] :
    DropLoopCodePlaced 0xcec 0xd24 .r20_25 :=
  mk_drop_loop_placed 3308 3364 .r20_25

instance instDropLoopPlaced_0xd58 [LibsignalPlacement] :
    DropLoopCodePlaced 0xd58 0xd90 .r20_25 :=
  mk_drop_loop_placed 3416 3472 .r20_25

instance instDropLoopPlaced_0xdc4 [LibsignalPlacement] :
    DropLoopCodePlaced 0xdc4 0xdfc .r20_25 :=
  mk_drop_loop_placed 3524 3580 .r20_25

instance instDropLoopPlaced_0xe30 [LibsignalPlacement] :
    DropLoopCodePlaced 0xe30 0xe68 .r20_25 :=
  mk_drop_loop_placed 3632 3688 .r20_25

instance instDropLoopPlaced_0xe9c [LibsignalPlacement] :
    DropLoopCodePlaced 0xe9c 0xed4 .r20_25 :=
  mk_drop_loop_placed 3740 3796 .r20_25

instance instDropLoopPlaced_0xf08 [LibsignalPlacement] :
    DropLoopCodePlaced 0xf08 0xf54 .r20_25 :=
  mk_drop_loop_placed 3848 3924 .r20_25

/-! ## 2. Generic Unrolled `Dir` Drop Block Code Typeclasses -/

/-- Relocatable `[LibsignalPlacement]` instruction-fetch bundle for one unrolled `Dir` drop block
starting at `sOff`, with buffer-free sub-block at `freeOff` and stack offset `dirOff` relative to `x23`. -/
class DropDirCodePlaced [LibsignalPlacement] (sOff freeOff : Nat) (dirOff : outParam Nat) : Prop where
  loop : DropLoopCodePlaced (sOff + 16) freeOff .r20_25
  hfree : sOff + 28 ≤ freeOff ∧ freeOff ≤ 4096
  s0 : ∀ H, (mProgPlaced H).fetch (mPcPlaced sOff) =
    some (Instr.ldp RegWidth.W64 false (Reg.gpr 21#5) (Reg.gpr 20#5)
      (AddrMode.Offset (Reg.gpr 23#5) (BitVec.ofNat 64 (dirOff + 8))))
  s4 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (sOff + 4)) =
    some (Instr.cbz RegWidth.W64 false (Reg.gpr 20#5) (BitVec.ofNat 64 (freeOff - (sOff + 4))))
  s8 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (sOff + 8)) =
    some (Instr.addSubImm RegWidth.W64 AddSubOp.ADD (Reg.gpr 25#5) (Reg.gpr 21#5) (32#12) false)
  s12 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (sOff + 12)) =
    some (Instr.b 16#64)
  b0 : ∀ H, (mProgPlaced H).fetch (mPcPlaced freeOff) =
    some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 8#5)
      (AddrMode.Offset (Reg.gpr 23#5) (BitVec.ofNat 64 dirOff)))
  b4 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (freeOff + 4)) =
    some (Instr.cbz RegWidth.W64 false (Reg.gpr 8#5) 24#64)
  b8 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (freeOff + 8)) =
    some (Instr.addSubShift RegWidth.W64 AddSubOp.ADD (Reg.gpr 8#5) (Reg.gpr 8#5) (Reg.gpr 8#5) ShiftType.LSL 1)
  b12 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (freeOff + 12)) =
    some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 0#5) Reg.xzr (Reg.gpr 21#5) ShiftType.LSL 0)
  b16 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (freeOff + 16)) =
    some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 2#5) (8#16) 0)
  b20 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (freeOff + 20)) =
    some (Instr.bitfield RegWidth.W64 BitfieldOp.UBFM (Reg.gpr 1#5) (Reg.gpr 8#5) 60 59)
  b24 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (freeOff + 24)) =
    some (Instr.bl ((lsρ lsRustDeallocSymCli - (blkPl_617).base) - BitVec.ofNat 64 (freeOff + 24)))

attribute [instance] DropDirCodePlaced.loop

macro "mk_drop_dir_placed " sOff:num freeOff:num dirOff:num loopInst:ident : term =>
  `({ loop := $loopInst
      hfree := by decide
      s0 := by m5_drop_placed_field
      s4 := by m5_drop_placed_field
      s8 := by m5_drop_placed_field
      s12 := by m5_drop_placed_field
      b0 := by m5_drop_placed_field
      b4 := by m5_drop_placed_field
      b8 := by m5_drop_placed_field
      b12 := by m5_drop_placed_field
      b16 := by m5_drop_placed_field
      b20 := by m5_drop_placed_field
      b24 := by m5_drop_placed_field : DropDirCodePlaced $sOff $freeOff $dirOff })

instance instDropDirPlaced_0 [LibsignalPlacement] : DropDirCodePlaced 0xc70 0xcb8 0x0 :=
  mk_drop_dir_placed 3184 3256 0 instDropLoopPlaced_0xc80
instance instDropDirPlaced_1 [LibsignalPlacement] : DropDirCodePlaced 0xcdc 0xd24 0x28 :=
  mk_drop_dir_placed 3292 3364 40 instDropLoopPlaced_0xcec
instance instDropDirPlaced_2 [LibsignalPlacement] : DropDirCodePlaced 0xd48 0xd90 0x50 :=
  mk_drop_dir_placed 3400 3472 80 instDropLoopPlaced_0xd58
instance instDropDirPlaced_3 [LibsignalPlacement] : DropDirCodePlaced 0xdb4 0xdfc 0x78 :=
  mk_drop_dir_placed 3508 3580 120 instDropLoopPlaced_0xdc4
instance instDropDirPlaced_4 [LibsignalPlacement] : DropDirCodePlaced 0xe20 0xe68 0xa0 :=
  mk_drop_dir_placed 3616 3688 160 instDropLoopPlaced_0xe30
instance instDropDirPlaced_5 [LibsignalPlacement] : DropDirCodePlaced 0xe8c 0xed4 0xc8 :=
  mk_drop_dir_placed 3724 3796 200 instDropLoopPlaced_0xe9c
instance instDropDirPlaced_6 [LibsignalPlacement] : DropDirCodePlaced 0xef8 0xf54 0xf0 :=
  mk_drop_dir_placed 3832 3924 240 instDropLoopPlaced_0xf08

/-- Relocatable `[LibsignalPlacement]` instruction-fetch bundle for the 2-instruction loop-bound
comparison (`cmp x26, #(7 - j); b.eq 0xf70`) at `freeOff + 28 .. freeOff + 32` for stages `j = 0 .. 5`. -/
class DropDirCmpCodePlaced [LibsignalPlacement] (freeOff j : Nat) : Prop where
  hcmp : freeOff + 32 ≤ 0xf70
  c0 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (freeOff + 28)) =
    some (Instr.addSubImm RegWidth.W64 AddSubOp.SUBS Reg.xzr (Reg.gpr 26#5) (BitVec.ofNat 12 (7 - j)) false)
  c4 : ∀ H, (mProgPlaced H).fetch (mPcPlaced (freeOff + 32)) =
    some (Instr.bCond CondCode.EQ (BitVec.ofNat 64 (0xf70 - (freeOff + 32))))

macro "mk_drop_cmp_placed " freeOff:num j:num : term =>
  `({ hcmp := by decide
      c0 := by m5_drop_placed_field
      c4 := by m5_drop_placed_field : DropDirCmpCodePlaced $freeOff $j })

instance instDropDirCmpPlaced_0 [LibsignalPlacement] : DropDirCmpCodePlaced 0xcb8 0 := mk_drop_cmp_placed 3256 0
instance instDropDirCmpPlaced_1 [LibsignalPlacement] : DropDirCmpCodePlaced 0xd24 1 := mk_drop_cmp_placed 3364 1
instance instDropDirCmpPlaced_2 [LibsignalPlacement] : DropDirCmpCodePlaced 0xd90 2 := mk_drop_cmp_placed 3472 2
instance instDropDirCmpPlaced_3 [LibsignalPlacement] : DropDirCmpCodePlaced 0xdfc 3 := mk_drop_cmp_placed 3580 3
instance instDropDirCmpPlaced_4 [LibsignalPlacement] : DropDirCmpCodePlaced 0xe68 4 := mk_drop_cmp_placed 3688 4
instance instDropDirCmpPlaced_5 [LibsignalPlacement] : DropDirCmpCodePlaced 0xed4 5 := mk_drop_cmp_placed 3796 5

end CryptoVerification.SignalSession.Cli.MainHops
