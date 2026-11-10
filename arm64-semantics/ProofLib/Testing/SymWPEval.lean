/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
import all Init.Data.Range.Basic
public import Arm64
public meta import Arm64
public import ProofLib
public meta import ProofLib.Invariant
public meta import ProofLib.Exec
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.SymWP.InsnSteps
public import ProofLib.SepLogic.SymWP

/-!
# Differential and Conformance Tests for `SymWP` and `VCGen`

Tests `ProofLib.SepLogic.SymWP` and `ProofLib.VCGen` against concrete `Arm64.execInst`
execution: literal evaluation (`evalNatLit?`, `evalBitVecLit?`), instruction-rule dispatch
(`classifyInsnStepRule`), `MetaM` differential execution of `symSimpExpr` versus `execInst`,
and end-to-end `wp_sym_steps` and `wp_steps` subroutine proofs.
-/

@[expose] public section

namespace Testing.SymWPEval

open Arm64 ProofLib

/-! ## `MetaM` Differential Harness -/

public meta section MetaDiffHarness
set_option compiler.relaxedMetaCheck true
open Lean Meta

/-- Decode a 32-bit instruction word `w` in `MetaM` to its `instExpr : Expr` by reducing `Arm64.decode w`. -/
def decodeWordExpr (w : BitVec 32) : MetaM Expr := do
  let app := mkApp (mkConst ``Arm64.decode) (toExpr w)
  let r ← withTransparency .all (reduce app)
  if r.isAppOfArity ``Option.some 2 then
    return r.getArg! 1
  throwError "decodeWordExpr: failed to decode {w}"

/-- Convert a `PState` to its Lean `Expr` (`PState.mk n z c v`). -/
def pstateToExpr (ps : PState) : Expr :=
  mkApp4 (mkConst ``PState.mk) (toExpr ps.n) (toExpr ps.z) (toExpr ps.c) (toExpr ps.v)

/-- Monitored general-purpose registers for differential comparison. -/
def monitoredGprs : List Reg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x29, .lr]

/-- Convert a `Reg` to its canonical `Expr`. -/
def regToCanonExpr : Reg → Expr
  | .gpr idx => mkApp (mkConst ``Reg.gpr) (toExpr idx)
  | .sp      => mkConst ``Reg.sp
  | .xzr     => mkConst ``Reg.xzr

/-- Construct both a concrete `Arm64.State` and a symbolic `State` spine expression rooted at `sBase`
    with identical initial register values, `SP`, `PC`, and `PState`. -/
def mkInitialStates (sBase : Expr) (pc0 : BitVec 64) (sp0 : BitVec 64) (ps0 : PState)
    (regVals : List (Reg × BitVec 64)) : Arm64.State × Expr := Id.run do
  let mut sConc : Arm64.State := { pc := pc0, sp := sp0, pstate := ps0, status := .Running }
  let mut sExpr : Expr := sBase
  -- Seed all monitored GPRs with 0#64 first so every read resolves on the symbolic spine
  for r in monitoredGprs do
    sConc := sConc.writeReg64 r 0#64
    sExpr := mkApp3 (mkConst ``Arm64.State.writeReg64) sExpr (regToCanonExpr r) (toExpr 0#64)
  for (r, v) in regVals do
    sConc := sConc.writeReg64 r v
    sExpr := mkApp3 (mkConst ``Arm64.State.writeReg64) sExpr (regToCanonExpr r) (toExpr v)
  sExpr := mkApp3 (mkConst ``Arm64.State.writeReg64) sExpr (mkConst ``Reg.sp) (toExpr sp0)
  sExpr := mkApp2 (mkConst ``Arm64.State.setPState) sExpr (pstateToExpr ps0)
  sExpr := mkApp2 (mkConst ``Arm64.State.setPC) sExpr (toExpr pc0)
  return (sConc, sExpr)

/-- Differentially execute a sequence of 32-bit instruction words through both `Arm64.execInst`
    and `ProofLib.symSimpExpr`, verifying kernel proof validity and bit-for-bit equality of all
    monitored registers, `SP`, `PC`, and `NZCV` flags after every step. -/
def diffExecWordsInSymM (suiteName : String) (words : List (BitVec 32))
    (pc0 : BitVec 64 := 0x10000#64) (sp0 : BitVec 64 := 0x80000#64)
    (ps0 : PState := { n := false, z := false, c := false, v := false })
    (initRegs : List (Reg × BitVec 64) := []) : MetaM Unit := do
  let baseThms ← getOrBuildSymWPTheorems
  let methods := mkSymWPMethods baseThms {}
  let config : Sym.Simp.Config := { maxSteps := 100000 }
  withLocalDeclD `sBase (mkConst ``Arm64.State) fun sBase => do
    let mut bs ← mkInitialWpSymBlockState
    let (sConc0, sSym0) := mkInitialStates sBase pc0 sp0 ps0 initRegs
    let mut sConc := sConc0
    let mut sSym := sSym0
    let mut stepIdx : Nat := 0
    for w in words do
      let some inst := Arm64.decode w
        | throwError "[{suiteName}] step {stepIdx}: Arm64.decode failed on {w}"
      let instExpr ← decodeWordExpr w
      sConc := Arm64.execInst inst sConc
      let execLhs := mkApp2 (mkConst ``Arm64.execInst) instExpr sSym
      let ((sSymNext, hexec), bsNext) ← symSimpExpr execLhs methods config bs
      Meta.check hexec
      let prfTy ← inferType hexec
      let expectedEq ← mkEq execLhs sSymNext
      unless ← isDefEq prfTy expectedEq do
        throwError "[{suiteName}] step {stepIdx} ({w}): proof type mismatch:\n  got: {prfTy}\n  expected: {expectedEq}"
      sSym := sSymNext
      bs := bsNext
      let pcLhs := mkApp (mkConst ``Arm64.State.pc) sSym
      let ((pcSymExpr, hpc), bs1) ← symSimpExpr pcLhs methods config bs
      Meta.check hpc
      bs := bs1
      let some (64, pcSymVal) ← evalBitVecLit? pcSymExpr
        | throwError "[{suiteName}] step {stepIdx} ({w}): symbolic PC did not simplify to literal: {pcSymExpr}"
      if BitVec.ofNat 64 pcSymVal != sConc.pc then
        throwError "[{suiteName}] step {stepIdx} ({w}): PC mismatch: sym={BitVec.ofNat 64 pcSymVal}, conc={sConc.pc}"
      let spLhs := mkApp (mkConst ``Arm64.State.sp) sSym
      let ((spSymExpr, hsp), bs2) ← symSimpExpr spLhs methods config bs
      Meta.check hsp
      bs := bs2
      let some (64, spSymVal) ← evalBitVecLit? spSymExpr
        | throwError "[{suiteName}] step {stepIdx} ({w}): symbolic SP did not simplify to literal: {spSymExpr}"
      if BitVec.ofNat 64 spSymVal != sConc.sp then
        throwError "[{suiteName}] step {stepIdx} ({w}): SP mismatch: sym={BitVec.ofNat 64 spSymVal}, conc={sConc.sp}"
      for r in monitoredGprs do
        let rLhs := mkApp2 (mkConst ``Arm64.State.readReg64) sSym (regToCanonExpr r)
        let ((rSymExpr, hr), bsR) ← symSimpExpr rLhs methods config bs
        Meta.check hr
        bs := bsR
        let some (64, rSymVal) ← evalBitVecLit? rSymExpr
          | throwError "[{suiteName}] step {stepIdx} ({w}) reg {repr r}: did not simplify to literal: {rSymExpr}"
        let concVal := sConc.readReg64 r
        if BitVec.ofNat 64 rSymVal != concVal then
          throwError "[{suiteName}] step {stepIdx} ({w}) reg {repr r} mismatch: sym={BitVec.ofNat 64 rSymVal}, conc={concVal}"
      let psLhs := mkApp (mkConst ``PState.toBits4) (mkApp (mkConst ``Arm64.State.pstate) sSym)
      let ((psSymExpr, hps), bsPs) ← symSimpExpr psLhs methods config bs
      Meta.check hps
      bs := bsPs
      let some (4, psSymVal) ← evalBitVecLit? psSymExpr
        | throwError "[{suiteName}] step {stepIdx} ({w}): symbolic PState.toBits4 did not simplify to literal: {psSymExpr}"
      let concBits := sConc.pstate.toBits4
      if BitVec.ofNat 4 psSymVal != concBits then
        throwError "[{suiteName}] step {stepIdx} ({w}): NZCV mismatch: sym={BitVec.ofNat 4 psSymVal}, conc={concBits}"
      stepIdx := stepIdx + 1

/-- Test `VCGen` `evalNatLit?` and `evalBitVecLit?` across ground arithmetic, shifts, extensions,
    negations, `Int64` round-trips, and open terms. -/
def testVCGenLiteralEvaluators : MetaM Unit := do
  let natCases : List (Expr × Nat) := [
    (toExpr (0 : Nat), 0),
    (toExpr (42 : Nat), 42),
    (← mkAppM ``HAdd.hAdd #[toExpr (17 : Nat), toExpr (25 : Nat)], 42),
    (← mkAppM ``HSub.hSub #[toExpr (100 : Nat), toExpr (37 : Nat)], 63),
    (← mkAppM ``HMul.hMul #[toExpr (12 : Nat), toExpr (11 : Nat)], 132),
    (← mkAppM ``HDiv.hDiv #[toExpr (144 : Nat), toExpr (12 : Nat)], 12),
    (← mkAppM ``HMod.hMod #[toExpr (149 : Nat), toExpr (12 : Nat)], 5),
    (← mkAppM ``HShiftLeft.hShiftLeft #[toExpr (3 : Nat), toExpr (5 : Nat)], 96),
    (← mkAppM ``HShiftRight.hShiftRight #[toExpr (96 : Nat), toExpr (4 : Nat)], 6),
    (← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (10 : Nat)], 1024)
  ]
  for (e, expected) in natCases do
    let some actual ← evalNatLit? e
      | throwError "evalNatLit? returned none on {e}"
    unless actual == expected do
      throwError "evalNatLit? mismatch on {e}: got {actual}, expected {expected}"
  let bvCases : List (Expr × Nat × Nat) := [
    (toExpr 0x123456789abcdef0#64, 64, 0x123456789abcdef0),
    (toExpr 0xdeadbeef#32, 32, 0xdeadbeef),
    (← mkAppM ``HAdd.hAdd #[toExpr 0x10000#64, toExpr 0x24#64], 64, 0x10024),
    (← mkAppM ``Neg.neg #[toExpr 16#64], 64, (1 <<< 64) - 16),
    (mkApp (mkConst ``Int64.toBitVec) (mkApp (mkConst ``Int64.ofBitVec) (toExpr 0x400#64)), 64, 0x400),
    (mkApp3 (mkConst ``BitVec.zeroExtend) (toExpr 32) (toExpr 64) (toExpr 0xffffffff#32), 64, 0xffffffff),
    (mkApp3 (mkConst ``BitVec.truncate) (toExpr 64) (toExpr 32) (toExpr 0x123456789abcdef0#64), 32, 0x9abcdef0),
    (← mkAppM ``HShiftLeft.hShiftLeft #[toExpr 0xf#64, toExpr (8 : Nat)], 64, 0xf00),
    (← mkAppM ``HShiftRight.hShiftRight #[toExpr 0xf00#64, toExpr (4 : Nat)], 64, 0xf0)
  ]
  for (e, expW, expV) in bvCases do
    let some (w, v) ← evalBitVecLit? e
      | throwError "evalBitVecLit? returned none on {e}"
    unless w == expW && v == expV do
      throwError "evalBitVecLit? mismatch on {e}: got ({w}, {v}), expected ({expW}, {expV})"
  withLocalDeclD `x (mkApp (mkConst ``BitVec) (toExpr 64)) fun x => do
    let openAdd ← mkAppM ``HAdd.hAdd #[x, toExpr 4#64]
    if (← evalBitVecLit? openAdd).isSome then
      throwError "evalBitVecLit? unexpectedly succeeded on open term {openAdd}"

/-- Test `classifyInsnStepRule` across all `SymInsnStepRule` and `WpStepOutcome` categories. -/
def testClassifyInsnStepRule : MetaM Unit := do
  let checkRule (label : String) (w : BitVec 32)
      (pred : SymInsnStepRule → Bool) (expOutcome : WpStepOutcome) : MetaM Unit := do
    let instExpr ← decodeWordExpr w
    let (rule, outcome) := classifyInsnStepRule instExpr
    unless pred rule do
      throwError "classifyInsnStepRule [{label}] ({w}): unexpected rule (theorems: {rule.theoremNames})"
    unless outcome == expOutcome do
      throwError "classifyInsnStepRule [{label}] ({w}): got outcome {repr outcome}, expected {repr expOutcome}"
  checkRule "ADD X0, X1, #42"      0x9100a820#32 (· == .pureStep) .steppedNormal
  checkRule "SUBS XZR, X0, X1"     0xeb01001f#32 (· == .pureStep) .steppedNormal
  checkRule "B #16"                0x14000004#32 (· == .pureStep) .steppedBranch
  checkRule "BL #64"               0x94000010#32 (· == .pureStep) .steppedCall
  checkRule "BLR X8"               0xd63f0100#32 (· == .pureStep) .steppedCall
  checkRule "RET"                  0xd65f03c0#32 (· == .pureStep) .steppedRet
  checkRule "B.EQ #8"              0x54000040#32 (· == .pureStep) .steppedNormal
  checkRule "CBZ X0, #8"           0xb4000040#32 (· == .pureStep) .steppedNormal
  checkRule "LDR X0, [SP, #8]"     0xf94007e0#32 (fun | .ldr64 _ _ => true | _ => false) .steppedNormal
  checkRule "STR X0, [SP, #8]"     0xf90007e0#32 (fun | .str64 _ _ => true | _ => false) .steppedNormal
  checkRule "LDUR X0, [X1, #-8]"   0xf85f8020#32 (fun | .ldr64 _ _ => true | _ => false) .steppedNormal
  checkRule "STUR X0, [X1, #-8]"   0xf81f8020#32 (fun | .str64 _ _ => true | _ => false) .steppedNormal
  checkRule "LDP X29, X30, [SP], #16" 0xa8c17bfd#32 (· == .ldp64) .steppedNormal
  checkRule "STP X29, X30, [SP, #-16]!" 0xa9bf7bfd#32 (· == .stp64) .steppedNormal
  checkRule "LDR W0, [X1, #4]"     0xb9400420#32 (· == .ldr32) .steppedNormal
  checkRule "STR W0, [X1, #4]"     0xb9000420#32 (· == .str32) .steppedNormal
  checkRule "LDUR W0, [X1, #-4]"   0xb85fc020#32 (· == .ldr32) .steppedNormal
  checkRule "STUR W0, [X1, #-4]"   0xb81fc020#32 (· == .str32) .steppedNormal
  checkRule "LDRSW X0, [X1, #4]"   0xb9800420#32 (· == .ldrsw32) .steppedNormal
  checkRule "LDP W0, W1, [X2]"     0x29400440#32 (· == .ldp32) .steppedNormal
  checkRule "STP W0, W1, [X2]"     0x29000440#32 (· == .stp32) .steppedNormal
  checkRule "LDAR W0, [X1]"        0x88dffc20#32 (· == .ldar32) .steppedNormal
  checkRule "LDXR X8, [X10]"       0xc85f7d48#32 (· == .otherMemOrSpecial) .steppedNormal
  checkRule "STXR W12, X11, [X10]" 0xc80c7d4b#32 (· == .otherMemOrSpecial) .steppedNormal
  checkRule "LDRH W0, [X1, #2]"    0x79400420#32 (· == .ldr16) .steppedNormal
  checkRule "STRH W0, [X1, #2]"    0x79000420#32 (· == .str16) .steppedNormal
  checkRule "LDRSH X0, [X1, #2]"   0x79800420#32 (· == .ldrsh16) .steppedNormal
  checkRule "LDRB W0, [X1, #1]"    0x39400420#32 (· == .ldr8) .steppedNormal
  checkRule "STRB W0, [X1, #1]"    0x39000420#32 (· == .str8) .steppedNormal
  checkRule "LDRSB X0, [X1, #1]"   0x39800420#32 (· == .ldrsb) .steppedNormal
  checkRule "LDR Q0, [X1]"         0x3dc00020#32 (· == .ldrSimd128) .steppedNormal
  checkRule "STR Q0, [X1]"         0x3d800020#32 (· == .strSimd128) .steppedNormal
  checkRule "LDP Q0, Q1, [X3, #0x40]!" 0xadc20460#32 (· == .ldpSimd128) .steppedNormal
  checkRule "STP Q0, Q1, [X3, #0x40]!" 0xad820460#32 (· == .stpSimd128) .steppedNormal
  checkRule "DC ZVA, X0"           0xd50b7420#32 (· == .dcZva) .steppedNormal
  checkRule "MRS X5, DCZID_EL0"    0xd53b00e5#32 (· == .pureStep) .steppedNormal

/-- Run all `MetaM` differential suites comparing `SymWP` (`symSimpExpr`) against `Arm64.execInst`
    across every pure AArch64 instruction family. -/
def runAllSymWPMetaDiffSuites : MetaM Unit := do
  testVCGenLiteralEvaluators
  testClassifyInsnStepRule

  -- Suite 1: Arithmetic, shifted/extended add/sub, carry/borrow (ADC/ADCS/SBC/SBCS), and NZCV flags
  diffExecWordsInSymM "arith_and_flags"
    [ 0x9100a820#32, -- add  x0, x1, #42
      0x1100a822#32, -- add  w2, w1, #42 (32-bit zero-extension check)
      0xb1000403#32, -- adds x3, x0, #1
      0x9a010004#32, -- adc  x4, x0, x1
      0xba010005#32, -- adcs x5, x0, x1
      0xda010006#32, -- sbc  x6, x0, x1
      0xfa010007#32, -- sbcs x7, x0, x1
      0x8b010c00#32, -- add  x0, x0, x1, lsl #3
      0xcb411002#32, -- sub  x2, x0, x1, lsr #4
      0x8b21c403#32, -- add  x3, x0, w1, sxtw #1
      0xcb214804#32, -- sub  x4, x0, w1, uxth #2
      0x6b02003f#32  -- cmp  w1, w2
    ]
    (initRegs := [(.x0, 0x7fffffff_ffffffff#64), (.x1, 0xffffffff_80000001#64), (.x2, 0x12345678_9abcdef0#64)])

  -- Suite 2: Logical immediate, logical shifted, and move wide (MOVZ/MOVN/MOVK)
  diffExecWordsInSymM "logical_and_mov_wide"
    [ 0x92401c20#32, -- and  x0, x1, #0xff
      0xb2401c22#32, -- orr  x2, x1, #0xff
      0xd2401c23#32, -- eor  x3, x1, #0xff
      0xf2401c24#32, -- ands x4, x1, #0xff
      0x8a220825#32, -- bic  x5, x1, x2, lsl #2
      0xaa220826#32, -- orn  x6, x1, x2, lsl #2
      0xca220827#32, -- eon  x7, x1, x2, lsl #2
      0xea220828#32, -- bics x8, x1, x2, lsl #2
      0xd2824680#32, -- movz x0, #0x1234
      0xf2ab5fe0#32, -- movk x0, #0x5aff, lsl #16
      0x12800002#32, -- movn w2, #0 (sets x2 = 0xffffffff)
      0x92800023#32  -- movn x3, #1
    ]
    (initRegs := [(.x1, 0xfedcba98_76543210#64), (.x2, 0x01234567_89abcdef#64)])

  -- Suite 3: Bitfield (UBFM, SBFM, BFM wrap-around & non-wrap) and EXTR (32-bit & 64-bit)
  diffExecWordsInSymM "bitfield_and_extr"
    [ 0xd348fc20#32, -- lsr  x0, x1, #8         (ubfm x0, x1, #8, #63)
      0xd378dc22#32, -- lsl  x2, x1, #8         (ubfm x2, x1, #56, #55, wrap-around)
      0x93407c23#32, -- sxtw x3, w1             (sbfm x3, x1, #0, #31)
      0x93401c24#32, -- sxtb x4, w1             (sbfm x4, x1, #0, #7)
      0x9378dc25#32, -- sbfiz x5, x1, #8, #56   (sbfm wrap-around)
      0xb3483c20#32, -- bfxil x0, x1, #8, #8    (bfm non-wrap)
      0xb3781c20#32, -- bfi   x0, x1, #8, #8    (bfm wrap-around)
      0x53087c26#32, -- lsr  w6, w1, #8         (32-bit ubfm)
      0x13001c27#32, -- sxtb w7, w1             (32-bit sbfm)
      0x93c23028#32, -- extr x8, x1, x2, #12    (64-bit extr)
      0x13823020#32  -- extr w0, w1, w2, #12    (32-bit extr)
    ]
    (initRegs := [(.x0, 0x11112222_33334444#64), (.x1, 0x89abcdef_fedcba98#64), (.x2, 0x01234567_89abcdef#64)])

  -- Suite 4: Conditional select (CSEL, CSINC, CSINV, CSNEG) & conditional compare (CCMP, CCMN)
  diffExecWordsInSymM "cond_select_and_ccmp"
    [ 0xeb02003f#32, -- cmp   x1, x2
      0x9a820020#32, -- csel  x0, x1, x2, eq
      0x9a821423#32, -- csinc x3, x1, x2, ne
      0xda822024#32, -- csinv x4, x1, x2, cs
      0xda82b425#32, -- csneg x5, x1, x2, lt
      0xfa421025#32, -- ccmp  x1, x2, #5, ne
      0x9a820026#32, -- csel  x6, x1, x2, eq
      0xfa42002a#32, -- ccmp  x1, x2, #0xa, eq
      0x9a82b027#32, -- csel  x7, x1, x2, lt
      0x1a821428#32  -- csinc w8, w1, w2, ne
    ]
    (initRegs := [(.x1, 10#64), (.x2, 25#64)])

  -- Suite 5: Data processing 1-source, 2-source, and 3-source (including SMADDL/UMADDL/SMULH/UMULH)
  diffExecWordsInSymM "dataproc_1_2_3_src"
    [ 0xdac00020#32, -- rbit   x0, x1
      0xdac00422#32, -- rev16  x2, x1
      0xdac00823#32, -- rev32  x3, x1
      0xdac00c24#32, -- rev    x4, x1
      0x5ac00825#32, -- rev    w5, w1
      0xdac01026#32, -- clz    x6, x1
      0xdac01427#32, -- cls    x7, x1
      0x9ac20820#32, -- udiv   x0, x1, x2
      0x9ac20c22#32, -- sdiv   x2, x1, x2
      0x9ac22023#32, -- lslv   x3, x1, x2
      0x9ac22424#32, -- lsrv   x4, x1, x2
      0x9ac22825#32, -- asrv   x5, x1, x2
      0x9ac22c26#32, -- rorv   x6, x1, x2
      0x9b020c20#32, -- madd   x0, x1, x2, x3
      0x9b028c24#32, -- msub   x4, x1, x2, x3
      0x9b220c25#32, -- smaddl x5, w1, w2, x3
      0x9b228c26#32, -- smsubl x6, w1, w2, x3
      0x9b427c27#32, -- smulh  x7, x1, x2
      0x9ba20c28#32, -- umaddl x8, w1, w2, x3
      0x9bc27c20#32  -- umulh  x0, x1, x2
    ]
    (initRegs := [(.x1, 0xffff_fffe_8000_0005#64), (.x2, 7#64), (.x3, 1000#64)])

  -- Suite 6: PC-relative addressing (ADR, ADRP) and branches (B, BL, BR, BLR, RET, B.cond, CBZ, CBNZ, TBZ, TBNZ)
  diffExecWordsInSymM "branches_and_pc_rel"
    [ 0x10000080#32, -- adr  x0, #16
      0x90000021#32, -- adrp x1, #4096
      0x14000004#32, -- b    #16
      0x94000008#32, -- bl   #32
      0xb4000042#32, -- cbz  x2, #8 (taken since x2 = 0)
      0xb5000043#32, -- cbnz x3, #8 (taken since x3 != 0)
      0x37180043#32, -- tbnz w3, #3, #8 (taken since bit 3 of x3 is 1)
      0x36180042#32, -- tbz  w2, #3, #8 (taken since bit 3 of x2 is 0)
      0xd65f03c0#32  -- ret
    ]
    (initRegs := [(.x2, 0#64), (.x3, 8#64), (.lr, 0xdead0000#64)])

set_option maxRecDepth 4096 in
run_meta do
  runAllSymWPMetaDiffSuites

/-- `symSimpExpr` reaches a fixpoint on register reads over an opaque state within a small step
    budget (exceeding `maxSteps` throws), and resolves reads through `State.writeReg64` whose
    register is a `Reg.x<n>` abbreviation. -/
def testSymSimpRegReadFixpoint : MetaM Unit := do
  let abbrevCases : List (Name × Option Reg) := [
    (``Reg.x15, some (.gpr 15#5)), (``Reg.x3, some (.gpr 3#5)),
    (``Reg.xzr, some .xzr),
    (``Reg.x30, some (.gpr 30#5)), (``Reg.lr, some (.gpr 30#5)), (``Reg.sp, some .sp),
    (`Arm64.Reg.x31, none),
    (`Arm64.Other.X1, none)]
  for (nm, expected) in abbrevCases do
    let got := evalRegKindPure? (mkConst nm)
    unless got == expected do
      throwError "evalRegKindPure? {nm}: got {repr got}, expected {repr expected}"
  let baseThms ← getOrBuildSymWPTheorems
  let methods := mkSymWPMethods baseThms {}
  let config : Sym.Simp.Config := { maxSteps := 200 }
  withLocalDeclD `s (mkConst ``Arm64.State) fun s => do
  withLocalDeclD `v (mkApp (mkConst ``BitVec) (toExpr 64)) fun v => do
    let simpChecked (lhs : Expr) : MetaM Expr := do
      let ((rhs, prf), _) ← symSimpExpr lhs methods config (← mkInitialWpSymBlockState)
      Meta.check prf
      unless ← isDefEq (← inferType prf) (← mkEq lhs rhs) do
        throwError "symSimpExpr proof type mismatch on {lhs}"
      return rhs
    let isReadOf (e : Expr) (idx : Nat) : Bool :=
      e.isAppOfArity ``State.readReg64 2 && e.getArg! 0 == s &&
        evalRegKindPure? (e.getArg! 1) == some (.gpr (BitVec.ofNat 5 idx))
    for idx in [0, 12, 30] do
      for r in [canonRegExpr (.gpr (BitVec.ofNat 5 idx)), regToCanonExpr (.gpr (BitVec.ofNat 5 idx))] do
        let rhs ← simpChecked (mkApp2 (mkConst ``State.readReg64) s r)
        unless isReadOf rhs idx do
          throwError "read x{idx} of opaque state: unexpected {rhs}"
    let w15 := mkConst ``Reg.x15
    let s1 := mkApp3 (mkConst ``State.writeReg64) s w15 v
    let rhs13 ← simpChecked (mkApp2 (mkConst ``State.readReg64) s1 (canonRegExpr (.gpr 13#5)))
    unless isReadOf rhs13 13 do
      throwError "read x13 past write to Reg.x15: unexpected {rhs13}"
    let rhs15 ← simpChecked (mkApp2 (mkConst ``State.readReg64) s1 (canonRegExpr (.gpr 15#5)))
    unless rhs15 == v do
      throwError "read x15 after write to Reg.x15: unexpected {rhs15}"

run_meta testSymSimpRegReadFixpoint

/-- error: `simp` failed: maximum number of steps exceeded -/
#guard_msgs (error, substring := true) in
run_meta do
  -- Negative control: a budget too small for one `execInst` step throws an error.
  let baseThms ← getOrBuildSymWPTheorems
  let methods := mkSymWPMethods baseThms {}
  withLocalDeclD `s (mkConst ``Arm64.State) fun s => do
    let instExpr ← decodeWordExpr 0x9100a820#32 -- add x0, x1, #42
    let lhs := mkApp2 (mkConst ``Arm64.execInst) instExpr s
    discard <| symSimpExpr lhs methods { maxSteps := 2 } (← mkInitialWpSymBlockState)

end MetaDiffHarness

/-! ## End-to-End `wp_sym_steps` and `wp_steps` Subroutine Proofs -/

section EndToEndSymWPSubroutines

set_option maxHeartbeats 200000
arm64_proof_prelude

@[simp, arm64_norm] def symwp_test_addr : BitVec 64 := 0x30000#64

/-- Multi-instruction subroutine exercising:
    - `stp x29, x30, [x4]` (64-bit store pair)
    - `add x0, x0, x1` (64-bit arithmetic)
    - `eor x0, x0, #0xff` (64-bit logical immediate)
    - `lsl x2, x1, #4` (`ubfm x2, x1, #60, #59` wrap-around bitfield shift)
    - `add x0, x0, x2` (64-bit arithmetic)
    - `str x0, [x4, #16]` / `ldr x0, [x4, #16]` (64-bit store & load)
    - `ldp x29, x30, [x4]` (64-bit load pair)
    - `ret` -/
def symwpAluMemCode : FnCode :=
  .atAddr "symwp_alu_mem" symwp_test_addr
    ("a900789d " ++ -- 0x30000: stp x29, x30, [x4]
     "8b010000 " ++ -- 0x30004: add x0, x0, x1
     "d2401c00 " ++ -- 0x30008: eor x0, x0, #0xff
     "d37cec22 " ++ -- 0x3000c: lsl x2, x1, #4
     "8b020000 " ++ -- 0x30010: add x0, x0, x2
     "f9000880 " ++ -- 0x30014: str x0, [x4, #16]
     "f9400880 " ++ -- 0x30018: ldr x0, [x4, #16]
     "a940789d " ++ -- 0x3001c: ldp x29, x30, [x4]
     "d65f03c0")    -- 0x30020: ret

abbrev SymwpAluMemCodeAt (prog : Program) : Prop :=
  symwpAluMemCode.holds prog

/-- Expected symbolic result of `symwpAluMemCode` for inputs `(a, b)`. -/
@[simp, arm64_norm]
def symwpAluMemExpected (a b : BitVec 64) : BitVec 64 :=
  ((a + b) ^^^ 0xff#64) + (b <<< 4)

structure SymwpAluMemGhost where
  p  : BitVec 64
  a  : BitVec 64
  b  : BitVec 64
  v0 : BitVec 64
  v1 : BitVec 64
  v2 : BitVec 64

abbrev symwpAluMemSpec : Spec SymwpAluMemGhost where
  pre := fun g s0 =>
    ⌜s0.readReg64 .x0 = g.a ∧
     s0.readReg64 .x1 = g.b ∧
     s0.readReg64 .x4 = g.p⌝ ∗
    (g.p ↦₆₄ g.v0) ∗ ((g.p + 8#64) ↦₆₄ g.v1) ∗ ((g.p + 16#64) ↦₆₄ g.v2)
  post := fun g s0 sf =>
    ⌜sf.readReg64 .x0 = symwpAluMemExpected g.a g.b ∧
     sf.readReg64 .x29 = s0.readReg64 .x29 ∧
     sf.readReg64 .x30 = s0.readReg64 .x30⌝ ∗
    (g.p ↦₆₄ s0.readReg64 .x29) ∗
    ((g.p + 8#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((g.p + 16#64) ↦₆₄ symwpAluMemExpected g.a g.b)

/-- Verify `symwpAluMemCode` using `wp_sym_steps` (`SymM` engine). -/
theorem symwp_alu_mem_sym_ok (prog : Program) (h_code : SymwpAluMemCodeAt prog) :
    prog.subroutineOk "symwp_alu_mem" symwpAluMemSpec := by
  wp_init g s0
  wp_sym_steps
  wp_done

/-- Verify the same specification with `wp_steps` to check agreement with `wp_sym_steps`. -/
theorem symwp_alu_mem_wp_ok (prog : Program) (h_code : SymwpAluMemCodeAt prog) :
    prog.subroutineOk "symwp_alu_mem" symwpAluMemSpec := by
  wp_init g s0
  wp_steps
  wp_done

/-- Runtime conformance check verifying that concrete execution of `symwpAluMemCode` via
    `Arm64.execUntilPC` matches `symwpAluMemExpected` across multiple input pairs. -/
def symWPEvalRuntimeCheck : Bool :=
  let prog := Program.ofWords symwp_test_addr symwpAluMemCode.hex
  let frameBase : BitVec 64 := 0x90000#64
  let pairs : List (BitVec 64 × BitVec 64) := [
    (0#64, 0#64),
    (42#64, 7#64),
    (0x123456789abcdef0#64, 0x0fedcba987654321#64),
    (0xffffffffffffffff#64, 1#64)
  ]
  pairs.all fun (a, b) =>
    let s0 : State :=
      ({} : State).setMem (prog.loadCode ({} : State).mem).mapRestRw
        |>.writeReg64 .x0 a
        |>.writeReg64 .x1 b
        |>.writeReg64 .x4 frameBase
        |>.writeReg64 .x29 0x1111222233334444#64
        |>.writeReg64 .lr 0xdead0000#64
        |>.setPC symwp_test_addr
    let sf := execUntilPC 50 prog 0xdead0000#64 s0
    let exp := symwpAluMemExpected a b
    sf.status == .Running &&
    sf.pc == 0xdead0000#64 &&
    sf.readReg64 .x0 == exp &&
    sf.readReg64 .x29 == 0x1111222233334444#64 &&
    sf.readReg64 .lr == 0xdead0000#64 &&
    sf.mem.read64 frameBase == 0x1111222233334444#64 &&
    sf.mem.read64 (frameBase + 8#64) == 0xdead0000#64 &&
    sf.mem.read64 (frameBase + 16#64) == exp

#guard symWPEvalRuntimeCheck

/-- Straight-line (retry-less) exclusive load/modify/store sequence:
    - `ldxr x8, [x0]` / `add x8, x8, #1` / `stxr w9, x8, [x0]` (64-bit)
    - `ldaxr w10, [x1]` / `add w10, w10, #2` / `stlxr w11, w10, [x1]` (32-bit acquire/release)
    - `ret`
    Without `cbnz` retry loops, this sequence only guarantees an increment when `s0.exclFails = []`
    (tested negatively below when `s0.exclFails = [true]`). -/
def symwpExclCode : FnCode :=
  .atAddr "symwp_excl" 0x31000#64
    ("c85f7c08 " ++ -- ldxr  x8, [x0]
     "91000508 " ++ -- add   x8, x8, #1
     "c8097c08 " ++ -- stxr  w9, x8, [x0]
     "885ffc2a " ++ -- ldaxr w10, [x1]
     "1100094a " ++ -- add   w10, w10, #2
     "880bfc2a " ++ -- stlxr w11, w10, [x1]
     "d65f03c0")    -- ret

abbrev SymwpExclCodeAt (prog : Program) : Prop :=
  symwpExclCode.holds prog

structure SymwpExclGhost where
  p : BitVec 64
  q : BitVec 64
  a : BitVec 64
  b : BitVec 32

/-- Specification with no constraint on `s0.exclFails` (universally quantified over all finite
    spurious-failure oracle schedules). -/
abbrev symwpExclSpec : Spec SymwpExclGhost where
  pre := fun g s0 =>
    ⌜s0.readReg64 .x0 = g.p ∧ s0.readReg64 .x1 = g.q ∧
     MemWidth.isAligned .X64 g.p = true ∧ MemWidth.isAligned .W32 g.q = true⌝ ∗
    (g.p ↦₆₄ g.a) ∗ (g.q ↦₃₂ g.b)
  post := fun g _ sf =>
    ⌜sf.readReg64 .x9 = 0#64 ∧ sf.readReg64 .x11 = 0#64⌝ ∗
    (g.p ↦₆₄ (g.a + 1#64)) ∗ (g.q ↦₃₂ (g.b + 2#32))

/-- Restricted specification pinning `s0.exclFails = []`, under which even a retry-less `stxr`
    sequence succeeds on the first attempt. -/
abbrev symwpExclNoFailSpec : Spec SymwpExclGhost where
  pre := fun g s0 =>
    ⌜s0.readReg64 .x0 = g.p ∧ s0.readReg64 .x1 = g.q ∧
     MemWidth.isAligned .X64 g.p = true ∧ MemWidth.isAligned .W32 g.q = true ∧
     s0.exclFails = []⌝ ∗
    (g.p ↦₆₄ g.a) ∗ (g.q ↦₃₂ g.b)
  post := fun g _ sf =>
    ⌜sf.readReg64 .x9 = 0#64 ∧ sf.readReg64 .x11 = 0#64⌝ ∗
    (g.p ↦₆₄ (g.a + 1#64)) ∗ (g.q ↦₃₂ (g.b + 2#32))

/-- Negative regression test (operational): on `s0.exclFails = [true]`, executing the retry-less
    `ldxr x8, [x0]; add x8, x8, #1; stxr w9, x8, [x0]` sequence produces `w9 = 1` and leaves memory
    at `x0` unchanged (`s3.mem.read64 p = a`), so a retry-less `stxr` cannot verify a guaranteed increment. -/
theorem symwp_excl_retryless_fails_on_spurious (s0 : State) (p a : BitVec 64)
    (hp : s0.readReg64 .x0 = p) (hal : MemWidth.isAligned .X64 p = true)
    (hr : s0.mem.canRead p 8 = true) (hw : s0.mem.canWrite p 8 = true)
    (hmem : s0.mem.read64 p = a) (horacle : s0.exclFails = [true]) :
    let s1 := execInst (.ldxr .X64 false .x0 .x8) s0
    let s2 := execInst (.addSubImm .W64 .ADD .x8 .x8 1#12 false) s1
    let s3 := execInst (.stxr .X64 false .x9 .x0 .x8) s2
    s3.readReg64 .x9 = 1#64 ∧ s3.mem.read64 p = a ∧ s3.exclFails = [] := by
  intro s1 s2 s3
  have hsp1 : checkRegSPAligned s0 .x0 = true := rfl
  have hsp3 : checkRegSPAligned s2 .x0 = true := rfl
  have hp2 : s2.readReg64 .x0 = p := by
    simp [s2, s1, execInstWithSvc, execAddSubImm, hsp1, hp, hal, hr]
  have hw2 : s2.mem.canWrite p 8 = true := by
    simp [s2, s1, execInstWithSvc, execAddSubImm, hsp1, hp, hal, hr, hw]
  have hexcl2 : s2.exclFails = [true] := by
    simp [s2, s1, execInstWithSvc, execAddSubImm, hsp1, hp, hal, hr, horacle]
  have hs3 : s3 = ((s2.stepExclOracle).writeReg .W32 .x9 1#64).advancePC := by
    simp [s3, hsp3, hp2, hal, hw2, hexcl2]
  refine ⟨?_, ?_, ?_⟩
  · simp [hs3]
  · simp [hs3, s2, s1, execInstWithSvc, execAddSubImm, hsp1, hp, hal, hr, hmem]
  · simp [hs3, hexcl2]

-- Negative regression test (`wp_steps`): without a retry loop or `s0.exclFails = []`, `wp_steps`
-- stops at `stxr` (`200712#64`) because `s.exclWillFail = false` does not hold for arbitrary `s0 : State`.
/--
error: wp_done: current PC `200712#64` does not match target PC
-/
#guard_msgs (error, substring := true) in
example (prog : Program) (h_code : SymwpExclCodeAt prog) :
    prog.subroutineOk "symwp_excl" symwpExclSpec := by
  wp_init g s0
  wp_steps
  wp_done

/-- Single-step `LDXR`/`STXR`/`LDAXR`/`STLXR` succeeds when `s0.exclFails = []`. -/
theorem symwp_excl_wp_ok (prog : Program) (h_code : SymwpExclCodeAt prog) :
    prog.subroutineOk "symwp_excl" symwpExclNoFailSpec := by
  wp_init g s0
  wp_steps
  wp_done

/--
[proofLib.symStep.fallback] no SymM fast path for this instruction class: stepping with wpStepCoreWithOutcome at PC 200712#64
    instruction: Instr.stxr MemWidth.X64 false (Reg.gpr 9#5) (Reg.gpr 0#5) (Reg.gpr 8#5)
    goal head: @SepWP
-/
#guard_msgs (trace, substring := true) in
set_option trace.proofLib.symStep.fallback true in
/-- `wp_sym_steps` steps the exclusive load/store with the `wpStepCoreWithOutcome` fallback;
    `trace.proofLib.symStep.fallback` reports each such step. -/
theorem symwp_excl_sym_ok (prog : Program) (h_code : SymwpExclCodeAt prog) :
    prog.subroutineOk "symwp_excl" symwpExclNoFailSpec := by
  wp_init g s0
  wp_sym_steps
  wp_done

-- The fallback trace is off by default.
#guard_msgs in
example (prog : Program) (h_code : SymwpExclCodeAt prog) :
    prog.subroutineOk "symwp_excl" symwpExclNoFailSpec := by
  wp_init g s0
  wp_sym_steps
  wp_done

/-- Exclusive load/modify/store with `cbnz` retry loops (64-bit `ldxr`/`add`/`stxr`/`cbnz -12` and
    32-bit `ldaxr`/`add`/`stlxr`/`cbnz -12`), provable for arbitrary `s0.exclFails : List Bool`. -/
def symwpExclRetryCode : FnCode :=
  .atAddr "symwp_excl_retry" 0x31100#64
    ("c85f7c08 " ++ -- 0x31100: ldxr  x8, [x0]
     "91000508 " ++ -- 0x31104: add   x8, x8, #1
     "c8097c08 " ++ -- 0x31108: stxr  w9, x8, [x0]
     "35ffffa9 " ++ -- 0x3110c: cbnz  w9, 0x31100 (-12)
     "885ffc2a " ++ -- 0x31110: ldaxr w10, [x1]
     "1100094a " ++ -- 0x31114: add   w10, w10, #2
     "880bfc2a " ++ -- 0x31118: stlxr w11, w10, [x1]
     "35ffffab " ++ -- 0x3111c: cbnz  w11, 0x31110 (-12)
     "d65f03c0")    -- 0x31120: ret

abbrev SymwpExclRetryCodeAt (prog : Program) : Prop :=
  symwpExclRetryCode.holds prog

/-- Positive regression test: `wp_steps` verifies the 64-bit and 32-bit LL/SC retry loops in
    `symwpExclRetryCode` against `symwpExclSpec` (arbitrary `s0.exclFails : List Bool`). -/
theorem symwp_excl_retry_wp_ok (prog : Program) (h_code : SymwpExclRetryCodeAt prog) :
    prog.subroutineOk "symwp_excl_retry" symwpExclSpec := by
  wp_init g s0
  wp_steps
  wp_done

end EndToEndSymWPSubroutines

/-! ## `SepWP.weaken_pre_frame` (frame-wise precondition weakening) Regression Tests -/

section WeakenPreFrame

/-- Positive: weaken an exact cell precondition to a `memRegion` using only a state-local,
    frame-wise entailment (without unsealing `SepWP`). -/
example {prog : Program} {target_pc a v : BitVec 64} {s : State}
    {post : State → SepProp → Prop}
    (hent : ∀ R : SepProp, s.mem ⊨ (a ↦₆₄ v) ∗ R → s.mem ⊨ (a ↦₆₄ v) ∗ R)
    (h : SepWP prog target_pc s (a ↦₆₄ v) post) :
    SepWP prog target_pc s (a ↦₆₄ v) post :=
  SepWP.weaken_pre_frame hent h

-- Negative: the rule does not let the precondition be weakened without an entailment.
/--
error: Type mismatch
  h
has type
  SepWP prog target_pc s P' post
but is expected to have type
  SepWP prog target_pc s P post
-/
#guard_msgs in
example {prog : Program} {target_pc : BitVec 64} {s : State} {P P' : SepProp}
    {post : State → SepProp → Prop} (h : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post := h

end WeakenPreFrame

/-! ## `tryProveIteCondStep?` (step-level branch-condition closer) Regression Tests -/

section TryProveIteCondStep
open Lean Elab Tactic Meta

/-- On a goal `c → _`, decide `c` with `tryProveIteCondStep?` (on `c`, then on `¬c`, as
    `resolveIteCondStep?` does) and report the outcome. `c` is not in the local context. -/
elab "test_try_prove_ite_step" : tactic => withMainContext do
  let c ← instantiateMVars (← whnfR (← getMainTarget)).bindingDomain!
  let (_, hypIds) ← getLightweightSimpHyps
  if (← tryProveIteCondStep? hypIds c).isSome then logInfo "decided: true"
  else if (← tryProveIteCondStep? hypIds (mkNot c)).isSome then logInfo "decided: false"
  else logInfo "undecided"

/-- info: decided: true -/
#guard_msgs in
-- Positive: a narrowed mask compare that `simp` and the cheap closers leave open is decided by
-- the pruned `bv_kernel` closer, despite irrelevant `Nat`-subtraction hypotheses.
set_option linter.unusedVariables false in
set_option maxHeartbeats 5000 in
example (x : BitVec 64) (h : x &&& 0xff#64 = 0x41#64)
    (p0 p1 p2 p3 p4 p5 p6 p7 : BitVec 64) (n : Nat)
    (hp0 : p1 = p0 + 8#64) (hp1 : p2 = p1 + 8#64) (hp2 : p3 = p2 + 8#64) (hp3 : p4 = p3 + 8#64)
    (hp4 : p5 = p4 + 8#64) (hp5 : p6 = p5 + 8#64) (hp6 : p7 = p6 + 8#64)
    (hb0 : n - p0.toNat ≥ 8) (hb1 : n - p1.toNat ≥ 8) (hb2 : n - p2.toNat ≥ 8)
    (hb3 : n - p3.toNat ≥ 8) (hb4 : n - p4.toNat ≥ 8) (hb5 : n - p5.toNat ≥ 8)
    (hb6 : n - p6.toNat ≥ 8) :
    (BitVec.setWidth 32 x &&& 0xff#32 == 0x41#32) = true → True := by
  test_try_prove_ite_step
  exact fun _ => trivial

/-- info: undecided -/
#guard_msgs in
-- Negative: an undecidable compare (only the low byte of `x` and `y` agree) with many
-- `Nat`-subtraction hypotheses over atoms linked to `x` and `y` is reported undecided within a
-- small heartbeat budget: no closer hands the whole context to `bv_omega` (whose failing
-- `omega` run ignores the heartbeat cap and would exhaust the budget of the `exact` below).
set_option linter.unusedVariables false in
set_option maxHeartbeats 5000 in
example (x y : BitVec 64) (h : x &&& 0xff#64 = y &&& 0xff#64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : BitVec 64) (n : Nat)
    (hp0 : p1 = p0 + 8#64) (hp1 : p2 = p1 + 8#64) (hp2 : p3 = p2 + 8#64) (hp3 : p4 = p3 + 8#64)
    (hp4 : p5 = p4 + 8#64) (hp5 : p6 = p5 + 8#64) (hp6 : p7 = p6 + 8#64) (hp7 : p8 = p7 + 8#64)
    (hp8 : p9 = p8 + 8#64) (hp9 : p10 = p9 + 8#64)
    (hb0 : n - p0.toNat ≥ 8) (hb1 : n - p1.toNat ≥ 8) (hb2 : n - p2.toNat ≥ 8)
    (hb3 : n - p3.toNat ≥ 8) (hb4 : n - p4.toNat ≥ 8) (hb5 : n - p5.toNat ≥ 8)
    (hb6 : n - p6.toNat ≥ 8) (hb7 : n - p7.toNat ≥ 8) (hb8 : n - p8.toNat ≥ 8)
    (hb9 : n - p9.toNat ≥ 8) (hx : x = p3 + y) (hy : y.toNat ≤ n - p7.toNat) :
    (BitVec.setWidth 32 x &&& 0xffff#32 == BitVec.setWidth 32 y &&& 0xffff#32) = true → True := by
  test_try_prove_ite_step
  exact fun _ => trivial

end TryProveIteCondStep

/-! ## `State.orFpsr` / `State.setFpsr` Spine Normalization Regression Tests -/

section OrFpsrStateNorm

-- Positive: `State.orFpsr` commutes past `writeReg64`, `writeVReg128`, `setPC`, `setMem`, and
-- `setPState`, consecutive `orFpsr` updates merge via `State.orFpsr_orFpsr`, and GPR/VReg reads
-- simplify through them.
#guard_msgs in
example (s : State) (f1 f2 : BitVec 32) (v : BitVec 64) (q : BitVec 128) :
    ((((s.writeReg64 .x0 v).orFpsr f1).writeVReg128 1#5 q).orFpsr f2).readReg64 .x0 = v := by
  simp

-- Negative: `State.fpsr` after `State.orFpsr f` is `s.fpsr ||| f`, not `s.fpsr`, so `rfl`
-- fails to equate them for arbitrary `f`.
/--
error: Type mismatch
  rfl
has type
  ?m.5 = ?m.5
but is expected to have type
  (s.orFpsr f).fpsr = s.fpsr

Note: The following definitions were not unfolded because their definition is not exposed:
  Nat.lor ↦ 4
-/
#guard_msgs in
example (s : State) (f : BitVec 32) : (s.orFpsr f).fpsr = s.fpsr := rfl

end OrFpsrStateNorm

end Testing.SymWPEval
