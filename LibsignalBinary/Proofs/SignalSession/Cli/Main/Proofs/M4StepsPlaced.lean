/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4LitsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FramePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Symbolic Execution of `main_m4` Setup (`M+0x678 → signal_session::run`)

Executes the 75 straight-line instructions on Block `617` from `M+0x678` through `bl run` at
`M+0x7a0` (`lsmpl.base 579`, `lr = mPcPlaced 0x7a4`) in three parts under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.MainHops.M4Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- Machine invariant at `M+0x678` (`1656`) after the `M+0x5dc .. M+0x60c` coins-statics stores and
`¬ IsSendOverCap` guard. -/
structure AtM4SetupPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (s0 s : State) (w : CallW) (n : Nat)
    (buf inCap : BitVec 64) (inLen : Nat) : Prop where
  base : InMainPlaced CodeOk s0 s 0x678
  x19 : s.readReg64 (.gpr 19#5) = buf
  x21 : s.readReg64 (.gpr 21#5) = w.w5
  x22 : s.readReg64 (.gpr 22#5) = w.w2
  x23 : s.readReg64 (.gpr 23#5) = inCap
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x25 : s.readReg64 (.gpr 25#5) = w.w0
  x26 : s.readReg64 (.gpr 26#5) = w.w6
  x27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 inLen

/-- Intermediate machine invariant at `M+0x6fc` (`1788`) after `m4_step_part1_placed`. -/
structure AtM4P1EndPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (s0 s : State) (w : CallW) (n : Nat)
    (buf inCap inPtr : BitVec 64) (inLen : Nat) : Prop where
  base : InMainPlaced CodeOk s0 s 0x6fc
  x0 : s.readReg64 .x0 = s.sp + 0x1b8#64
  x1 : s.readReg64 .x1 = s.sp + 0x78#64
  x2 : s.readReg64 .x2 = s.sp + 0x310#64
  x3 : s.readReg64 .x3 = inPtr
  x4 : s.readReg64 .x4 = BitVec.ofNat 64 inLen
  x8 : s.readReg64 (.gpr 8#5) = w.w4
  x10 : s.readReg64 (.gpr 10#5) = 17#64
  x19 : s.readReg64 (.gpr 19#5) = buf
  x21 : s.readReg64 (.gpr 21#5) = w.w5
  x22 : s.readReg64 (.gpr 22#5) = s.sp + 0x78#64
  x23 : s.readReg64 (.gpr 23#5) = inCap
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 inLen

/-- Intermediate machine invariant at `M+0x748` (`1864`) after `m4_step_part2_placed`. -/
structure AtM4P2EndPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (s0 s : State) (n : Nat)
    (buf inCap inPtr : BitVec 64) (inLen : Nat) : Prop where
  base : InMainPlaced CodeOk s0 s 0x748
  x0 : s.readReg64 .x0 = s.sp + 0x1b8#64
  x1 : s.readReg64 .x1 = s.sp + 0x78#64
  x2 : s.readReg64 .x2 = s.sp + 0x310#64
  x3 : s.readReg64 .x3 = inPtr
  x4 : s.readReg64 .x4 = BitVec.ofNat 64 inLen
  x9 : s.readReg64 (.gpr 9#5) = 6#64
  x10 : s.readReg64 (.gpr 10#5) = 17#64
  x19 : s.readReg64 (.gpr 19#5) = buf
  x21 : s.readReg64 (.gpr 21#5) = s.sp + 0x310#64
  x22 : s.readReg64 (.gpr 22#5) = s.sp + 0x78#64
  x23 : s.readReg64 (.gpr 23#5) = inCap
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 inLen

/-- Machine invariant right at the `signal_session::run` entry (`lsmpl.base 579`) after `bl` at `M+0x7a0`. -/
structure AtM4RunCallPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (s0 s : State) (n : Nat)
    (buf inCap inPtr : BitVec 64) (inLen : Nat) : Prop where
  pc : s.pc = lsmpl.base 579
  lr : s.readReg64 .lr = mPcPlaced 0x7a4
  run : s.status = .Running
  sp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize
  fp : s.readReg64 .fp = s0.sp - 0x60#64
  inv : CodeOk s.mem
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  spAligned : s.spAligned = true
  x0 : s.readReg64 .x0 = s.sp + 0x1b8#64
  x1 : s.readReg64 .x1 = s.sp + 0x78#64
  x2 : s.readReg64 .x2 = s.sp + 0x310#64
  x3 : s.readReg64 .x3 = inPtr
  x4 : s.readReg64 .x4 = BitVec.ofNat 64 inLen
  x19 : s.readReg64 (.gpr 19#5) = buf
  x21 : s.readReg64 (.gpr 21#5) = s.sp + 0x310#64
  x22 : s.readReg64 (.gpr 22#5) = s.sp + 0x78#64
  x23 : s.readReg64 (.gpr 23#5) = inCap
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 inLen

/-- Steps `M+0x678 → M+0x6fc` (33 instructions): loads `inPtr, w.w1, w.w3, w.w4`, sets `x0..x4`
and `x22 = sp + 0x78`, copies `w0, w1, w2, w3, w6` to `[sp+0x78..0x90, 0xa8]`, and writes the first
9 words of `Stores`. -/
theorem m4_step_part1_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {s0 s : State} {ret : BitVec 64} {w : CallW} {n : Nat}
    {buf inCap inPtr : BitVec 64} {inLen : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hs : AtM4SetupPlaced CodeOk s0 s w n buf inCap inLen)
    (hk : ∀ s1 : State,
      AtM4P1EndPlaced CodeOk s0 s1 w n buf inCap inPtr inLen →
      s1.trace = s.trace →
      s1.fs = s.fs →
      SepWPp (mProgPlaced H) ret s1
        (((s.sp + 0x40#64) ↦₆₄ w.w3) ∗
          ((s.sp + 0x48#64) ↦₆₄ w.w4) ∗
          ((s.sp + 0x50#64) ↦₆₄ inPtr) ∗
          ((s.sp + 0x58#64) ↦₆₄ w.w1) ∗
          m4WrittenP1Placed s.sp w ∗ F)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (((s.sp + 0x40#64) ↦₆₄ w.w3) ∗
        ((s.sp + 0x48#64) ↦₆₄ w.w4) ∗
        ((s.sp + 0x50#64) ↦₆₄ inPtr) ∗
        ((s.sp + 0x58#64) ↦₆₄ w.w1) ∗
        m4UninitP1 s.sp ∗ F)
      Q Qp oom := by
  have hpc : s.pc = (blkPl_617).base + 1656#64 := hs.base.pc
  have hrun : s.status = .Running := hs.base.run
  have hsp_al : s.spAligned = true := hs.base.spAligned_state
  have hx19 := hs.x19
  have hx21 := hs.x21
  have hx22 := hs.x22
  have hx23 := hs.x23
  have hx24 := hs.x24
  have hx25 := hs.x25
  have hx26 := hs.x26
  have hx27 := hs.x27
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1788#64) hs.base.inv
  dsimp only [m4UninitP1, m4Slot]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro v78
  apply SepWP.exists_left; intro v80
  apply SepWP.exists_left; intro v88
  apply SepWP.exists_left; intro v90
  apply SepWP.exists_left; intro va8
  apply SepWP.exists_left; intro v328
  apply SepWP.exists_left; intro v350
  apply SepWP.exists_left; intro v358
  apply SepWP.exists_left; intro v378
  apply SepWP.exists_left; intro v380
  apply SepWP.exists_left; intro v3a0
  apply SepWP.exists_left; intro v3a8
  apply SepWP.exists_left; intro v3c8
  apply SepWP.exists_left; intro v3d0
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv1
  refine sepWPp_weaken_pre ?_ (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm]))
  · dsimp only [m4WrittenP1Placed, dirLit0Sym, dirLit1Sym, dirLit2Sym, dirLit3Sym]
    exact Entails.of_eq (by ac_rfl)
  · exact
      { base := InMainPlaced.mk_step hs.base
          (by simp only [mPcPlaced_eq, arm64_norm])
          (by simp only [arm64_norm, hrun])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          hinv1
          (by simp only [calleeSavedVRegs, arm64_norm])
        x0 := by simp only [arm64_norm]
        x1 := by simp only [arm64_norm]
        x2 := by simp only [arm64_norm]
        x3 := by simp only [arm64_norm]
        x4 := by simp only [arm64_norm]
        x8 := by simp only [arm64_norm]
        x10 := by simp only [arm64_norm]
        x19 := by simp only [arm64_norm, hx19]
        x21 := by simp only [arm64_norm, hx21]
        x22 := by simp only [arm64_norm]
        x23 := by simp only [arm64_norm, hx23]
        x24 := by simp only [arm64_norm, hx24]
        x27 := by simp only [arm64_norm, hx27] }

/-- Steps `M+0x6fc → M+0x748` (19 instructions): copies `w4, w5` to `[sp+0x98..0xa0]`, sets
`x21 = sp + 0x310`, and writes the next 11 words of `Stores`. -/
theorem m4_step_part2_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {s0 s : State} {ret : BitVec 64} {w : CallW} {n : Nat}
    {buf inCap inPtr : BitVec 64} {inLen : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hs : AtM4P1EndPlaced CodeOk s0 s w n buf inCap inPtr inLen)
    (hk : ∀ s2 : State,
      AtM4P2EndPlaced CodeOk s0 s2 n buf inCap inPtr inLen →
      s2.trace = s.trace →
      s2.fs = s.fs →
      SepWPp (mProgPlaced H) ret s2
        (m4WrittenP2Placed s.sp w ∗ F)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (m4UninitP2 s.sp ∗ F)
      Q Qp oom := by
  have hpc : s.pc = (blkPl_617).base + 1788#64 := hs.base.pc
  have hrun : s.status = .Running := hs.base.run
  have hsp_al : s.spAligned = true := hs.base.spAligned_state
  have hx0 := hs.x0
  have hx1 := hs.x1
  have hx2 := hs.x2
  have hx3 := hs.x3
  have hx4 := hs.x4
  have hx8 := hs.x8
  have hx10 := hs.x10
  have hx19 := hs.x19
  have hx21 := hs.x21
  have hx22 := hs.x22
  have hx23 := hs.x23
  have hx24 := hs.x24
  have hx27 := hs.x27
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1864#64) hs.base.inv
  dsimp only [m4UninitP2, m4Slot]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro v98
  apply SepWP.exists_left; intro va0
  apply SepWP.exists_left; intro v318
  apply SepWP.exists_left; intro v340
  apply SepWP.exists_left; intro v368
  apply SepWP.exists_left; intro v390
  apply SepWP.exists_left; intro v3b8
  apply SepWP.exists_left; intro v3e0
  apply SepWP.exists_left; intro v3f0
  apply SepWP.exists_left; intro v408
  apply SepWP.exists_left; intro v418
  apply SepWP.exists_left; intro v420
  apply SepWP.exists_left; intro v430
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv2
  refine sepWPp_weaken_pre ?_ (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm]))
  · dsimp only [m4WrittenP2Placed, dirLit4Sym, dirLit5Sym]
    exact Entails.of_eq (by ac_rfl)
  · exact
      { base := InMainPlaced.mk_step hs.base
          (by simp only [mPcPlaced_eq, arm64_norm])
          (by simp only [arm64_norm, hrun])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          hinv2
          (by simp only [calleeSavedVRegs, arm64_norm])
        x0 := by simp only [arm64_norm, hx0]
        x1 := by simp only [arm64_norm, hx1]
        x2 := by simp only [arm64_norm, hx2]
        x3 := by simp only [arm64_norm, hx3]
        x4 := by simp only [arm64_norm, hx4]
        x9 := by simp only [arm64_norm]
        x10 := by simp only [arm64_norm, hx10]
        x19 := by simp only [arm64_norm, hx19]
        x21 := by simp only [arm64_norm]
        x22 := by simp only [arm64_norm, hx22]
        x23 := by simp only [arm64_norm, hx23]
        x24 := by simp only [arm64_norm, hx24]
        x27 := by simp only [arm64_norm, hx27] }

/-- Steps `M+0x748 → signal_session::run` (23 instructions): finishes the remaining 20 words of
`Stores` and executes `bl signal_session::run` at `M+0x7a0` (`lr = M+0x7a4`). -/
theorem m4_step_part3_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {s0 s : State} {ret : BitVec 64} {n : Nat}
    {buf inCap inPtr : BitVec 64} {inLen : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hs : AtM4P2EndPlaced CodeOk s0 s n buf inCap inPtr inLen)
    (hk : ∀ s3 : State,
      AtM4RunCallPlaced CodeOk s0 s3 n buf inCap inPtr inLen →
      s3.sp = s.sp →
      s3.trace = s.trace →
      s3.fs = s.fs →
      SepWPp (mProgPlaced H) ret s3
        (m4WrittenP3Placed s.sp ∗ F)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (m4UninitP3 s.sp ∗ F)
      Q Qp oom := by
  have hpc : s.pc = (blkPl_617).base + 1864#64 := hs.base.pc
  have hrun : s.status = .Running := hs.base.run
  have hsp_al : s.spAligned = true := hs.base.spAligned_state
  have hx0 := hs.x0
  have hx1 := hs.x1
  have hx2 := hs.x2
  have hx3 := hs.x3
  have hx4 := hs.x4
  have hx9 := hs.x9
  have hx10 := hs.x10
  have hx19 := hs.x19
  have hx21 := hs.x21
  have hx22 := hs.x22
  have hx23 := hs.x23
  have hx24 := hs.x24
  have hx27 := hs.x27
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsmpl.base 579) hs.base.inv
  dsimp only [m4UninitP3, m4Slot]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro v310
  apply SepWP.exists_left; intro v320
  apply SepWP.exists_left; intro v330
  apply SepWP.exists_left; intro v338
  apply SepWP.exists_left; intro v348
  apply SepWP.exists_left; intro v360
  apply SepWP.exists_left; intro v370
  apply SepWP.exists_left; intro v388
  apply SepWP.exists_left; intro v398
  apply SepWP.exists_left; intro v3b0
  apply SepWP.exists_left; intro v3c0
  apply SepWP.exists_left; intro v3d8
  apply SepWP.exists_left; intro v3e8
  apply SepWP.exists_left; intro v3f8
  apply SepWP.exists_left; intro v400
  apply SepWP.exists_left; intro v410
  apply SepWP.exists_left; intro v428
  apply SepWP.exists_left; intro v438
  apply SepWP.exists_left; intro v440
  apply SepWP.exists_left; intro v448
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv3
  refine sepWPp_weaken_pre ?_
    (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]))
  · dsimp only [m4WrittenP3Placed, dirLit6Sym]
    exact Entails.of_eq (by ac_rfl)
  · exact
      { pc := by simp only [arm64_norm, *]
        lr := by simp only [mPcPlaced_eq, arm64_norm]
        run := by simp only [arm64_norm, hrun]
        sp := (by simp only [arm64_norm] : _ = s.sp).trans hs.base.sp
        fp := (by simp only [arm64_norm] : _ = s.readReg64 .fp).trans hs.base.fp
        inv := hinv3
        vregs := by
          simp only [calleeSavedVRegs, arm64_norm]
          exact hs.base.vregs
        spAligned := by simpa only [State.spAligned, arm64_norm] using hsp_al
        x0 := by simp only [arm64_norm, hx0]
        x1 := by simp only [arm64_norm, hx1]
        x2 := by simp only [arm64_norm, hx2]
        x3 := by simp only [arm64_norm, hx3]
        x4 := by simp only [arm64_norm, hx4]
        x19 := by simp only [arm64_norm, hx19]
        x21 := by simp only [arm64_norm, hx21]
        x22 := by simp only [arm64_norm, hx22]
        x23 := by simp only [arm64_norm, hx23]
        x24 := by simp only [arm64_norm, hx24]
        x27 := by simp only [arm64_norm, hx27] }

end CryptoVerification.SignalSession.Cli.MainHops
