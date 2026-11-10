/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5MovesLayoutPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable M5 Payload Moves & Iterator Setup (`M+0x7b0 → M+0x8b8`, Block `617`)

Verifies `m5_moves_placed` (`M+0x7b0 → M+0x8b8`) on Block `617` under `[LibsignalPlacement]`,
moving `run`'s `Ok (Stores, Vec<u8>)` payload into loop slots and establishing `AtM5LoopPlaced … 0`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout

namespace M5MovesSteps

open M5MovesHelpers

/-! ## 1. Six Modular Straight-Line Sub-Lemmas (`M+0x7b0 .. M+0x8b8`) -/

/-- `M+0x7b0 .. M+0x7cc` (8 instructions, ending at `bl memcpy`): spill `inCap` to `[fsp+0x10]`,
initialize `x20`, `x23`, `x25`, and call `memcpy(fsp + 0x78, fsp + 0x1b8, 0x140)`. -/
theorem step_pre_mc1_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {fsp fpVal buf inCap u10 : BitVec 64} {n : Nat}
    (hpc : s.pc = mPcPlaced 0x7b0)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfp : s.readReg64 .fp = fpVal)
    (hal : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx21 : s.readReg64 (.gpr 21#5) = fsp + 0x310#64)
    (hx22 : s.readReg64 (.gpr 22#5) = fsp + 0x78#64)
    (hx23 : s.readReg64 (.gpr 23#5) = inCap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n) :
    SepWP ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName) s
      ((fsp + 0x10#64) ↦₆₄ u10)
      (fun s1 P1 =>
        (s1.sp = fsp ∧
          s1.readReg64 .fp = fpVal ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
          s1.readReg64 .lr = mPcPlaced 0x7d0 ∧
          s1.readReg64 .x0 = fsp + 0x78#64 ∧
          s1.readReg64 .x1 = fsp + 0x1b8#64 ∧
          s1.readReg64 .x2 = 0x140#64 ∧
          s1.readReg64 (.gpr 19#5) = buf ∧
          s1.readReg64 (.gpr 20#5) = fsp + 0x1b8#64 ∧
          s1.readReg64 (.gpr 21#5) = fsp + 0x310#64 ∧
          s1.readReg64 (.gpr 22#5) = fsp + 0x78#64 ∧
          s1.readReg64 (.gpr 23#5) = fsp + 0x78#64 ∧
          s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n ∧
          s1.readReg64 (.gpr 25#5) = fsp + 0x310#64 ∧
          s1.fs = s.fs ∧
          s1.trace = s.trace) ∧
        P1 = ((fsp + 0x10#64) ↦₆₄ inCap))
      (fun _ => ⌜False⌝) := by
  subst hsp
  simp only [mPcPlaced_eq] at hpc ⊢
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  exact ⟨⟨by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *]⟩, rfl⟩

/-- `M+0x7d0 .. M+0x804` (14 instructions, landing at `M+0x808`): copy `d1` completely (`w0..w4`),
copy `d2.w0..w3`, load `x1 = fsp + 0x310`, `x2 = 0x140`, `x8 = d2.w4`, `x9 = d0.w4`,
`x10 = d3.w4`, `x11 = d7.w4`. -/
theorem step_chunk_a_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {fsp fpVal buf : BitVec 64} {n : Nat}
    {ws dstWs : StoresWords}
    (hpc : s.pc = mPcPlaced 0x7d0)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfp : s.readReg64 .fp = fpVal)
    (hal : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx20 : s.readReg64 (.gpr 20#5) = fsp + 0x1b8#64)
    (hx21 : s.readReg64 (.gpr 21#5) = fsp + 0x310#64)
    (hx22 : s.readReg64 (.gpr 22#5) = fsp + 0x78#64)
    (hx23 : s.readReg64 (.gpr 23#5) = fsp + 0x78#64)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : s.readReg64 (.gpr 25#5) = fsp + 0x310#64) :
    SepWP ((blkPC_617).rebase (blkPl_617).base H) (mPcPlaced 0x808) s
      (dirStackAt (fsp + 0x78#64) ws.d0 ∗
        dirStackAt (fsp + 0xa0#64) ws.d1 ∗
        dirStackAt (fsp + 0xc8#64) ws.d2 ∗
        dirStackAt (fsp + 0xf0#64) ws.d3 ∗
        dirStackAt (fsp + 0x190#64) ws.d7 ∗
        dirStackAt (fsp + 0x338#64) dstWs.d1 ∗
        dirStackAt (fsp + 0x360#64) dstWs.d2)
      (fun s1 P1 =>
        (s1.sp = fsp ∧
          s1.readReg64 .fp = fpVal ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
          s1.readReg64 .x1 = fsp + 0x310#64 ∧
          s1.readReg64 .x2 = 0x140#64 ∧
          s1.readReg64 (.gpr 8#5) = ws.d2.w4 ∧
          s1.readReg64 (.gpr 9#5) = ws.d0.w4 ∧
          s1.readReg64 (.gpr 10#5) = ws.d3.w4 ∧
          s1.readReg64 (.gpr 11#5) = ws.d7.w4 ∧
          s1.readReg64 (.gpr 19#5) = buf ∧
          s1.readReg64 (.gpr 20#5) = fsp + 0x1b8#64 ∧
          s1.readReg64 (.gpr 21#5) = fsp + 0x310#64 ∧
          s1.readReg64 (.gpr 22#5) = fsp + 0x78#64 ∧
          s1.readReg64 (.gpr 23#5) = fsp + 0x78#64 ∧
          s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n ∧
          s1.readReg64 (.gpr 25#5) = fsp + 0x310#64 ∧
          s1.fs = s.fs ∧
          s1.trace = s.trace) ∧
        P1 =
          (dirStackAt (fsp + 0x78#64) ws.d0 ∗
            dirStackAt (fsp + 0xa0#64) ws.d1 ∗
            dirStackAt (fsp + 0xc8#64) ws.d2 ∗
            dirStackAt (fsp + 0xf0#64) ws.d3 ∗
            dirStackAt (fsp + 0x190#64) ws.d7 ∗
            dirStackAt (fsp + 0x338#64) ws.d1 ∗
            dirStackAt (fsp + 0x360#64) ⟨ws.d2.w0, ws.d2.w1, ws.d2.w2, ws.d2.w3, dstWs.d2.w4⟩))
      (fun _ => ⌜False⌝) := by
  subst hsp
  simp only [mPcPlaced_eq] at hpc ⊢
  wp_simp_pre [dirStackAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  refine ⟨⟨by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *]⟩, ?_⟩
  simp only [dirStackAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- `M+0x808 .. M+0x83c` (14 instructions, landing at `M+0x840`): finish `d2.w4`, copy `d3`
completely (`w0..w4`), copy `d4.w0..w3` and `d5.w0..w3`, leaving `x8 = d4.w4` and `x10 = d5.w4`. -/
theorem step_chunk_b_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {fsp fpVal buf : BitVec 64} {n : Nat}
    {ws dstWs : StoresWords}
    (hpc : s.pc = mPcPlaced 0x808)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfp : s.readReg64 .fp = fpVal)
    (hal : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx1 : s.readReg64 .x1 = fsp + 0x310#64)
    (hx2 : s.readReg64 .x2 = 0x140#64)
    (hx8 : s.readReg64 (.gpr 8#5) = ws.d2.w4)
    (hx9 : s.readReg64 (.gpr 9#5) = ws.d0.w4)
    (hx10 : s.readReg64 (.gpr 10#5) = ws.d3.w4)
    (hx11 : s.readReg64 (.gpr 11#5) = ws.d7.w4)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx20 : s.readReg64 (.gpr 20#5) = fsp + 0x1b8#64)
    (hx21 : s.readReg64 (.gpr 21#5) = fsp + 0x310#64)
    (hx22 : s.readReg64 (.gpr 22#5) = fsp + 0x78#64)
    (hx23 : s.readReg64 (.gpr 23#5) = fsp + 0x78#64)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : s.readReg64 (.gpr 25#5) = fsp + 0x310#64) :
    SepWP ((blkPC_617).rebase (blkPl_617).base H) (mPcPlaced 0x840) s
      (dirStackAt (fsp + 0xf0#64) ws.d3 ∗
        dirStackAt (fsp + 0x118#64) ws.d4 ∗
        dirStackAt (fsp + 0x140#64) ws.d5 ∗
        dirStackAt (fsp + 0x360#64) ⟨ws.d2.w0, ws.d2.w1, ws.d2.w2, ws.d2.w3, dstWs.d2.w4⟩ ∗
        dirStackAt (fsp + 0x388#64) dstWs.d3 ∗
        dirStackAt (fsp + 0x3b0#64) dstWs.d4 ∗
        dirStackAt (fsp + 0x3d8#64) dstWs.d5)
      (fun s1 P1 =>
        (s1.sp = fsp ∧
          s1.readReg64 .fp = fpVal ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
          s1.readReg64 .x1 = fsp + 0x310#64 ∧
          s1.readReg64 .x2 = 0x140#64 ∧
          s1.readReg64 (.gpr 8#5) = ws.d4.w4 ∧
          s1.readReg64 (.gpr 9#5) = ws.d0.w4 ∧
          s1.readReg64 (.gpr 10#5) = ws.d5.w4 ∧
          s1.readReg64 (.gpr 11#5) = ws.d7.w4 ∧
          s1.readReg64 (.gpr 19#5) = buf ∧
          s1.readReg64 (.gpr 20#5) = fsp + 0x1b8#64 ∧
          s1.readReg64 (.gpr 21#5) = fsp + 0x310#64 ∧
          s1.readReg64 (.gpr 22#5) = fsp + 0x78#64 ∧
          s1.readReg64 (.gpr 23#5) = fsp + 0x78#64 ∧
          s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n ∧
          s1.readReg64 (.gpr 25#5) = fsp + 0x310#64 ∧
          s1.fs = s.fs ∧
          s1.trace = s.trace) ∧
        P1 =
          (dirStackAt (fsp + 0xf0#64) ws.d3 ∗
            dirStackAt (fsp + 0x118#64) ws.d4 ∗
            dirStackAt (fsp + 0x140#64) ws.d5 ∗
            dirStackAt (fsp + 0x360#64) ws.d2 ∗
            dirStackAt (fsp + 0x388#64) ws.d3 ∗
            dirStackAt (fsp + 0x3b0#64) ⟨ws.d4.w0, ws.d4.w1, ws.d4.w2, ws.d4.w3, dstWs.d4.w4⟩ ∗
            dirStackAt (fsp + 0x3d8#64) ⟨ws.d5.w0, ws.d5.w1, ws.d5.w2, ws.d5.w3, dstWs.d5.w4⟩))
      (fun _ => ⌜False⌝) := by
  subst hsp
  simp only [mPcPlaced_eq] at hpc ⊢
  wp_simp_pre [dirStackAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  refine ⟨⟨by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *]⟩, ?_⟩
  simp only [dirStackAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- `M+0x840 .. M+0x864` (10 instructions, landing at `M+0x868`): finish `d4` and `d5`, copy
`d6.w0..w3`, load `x10 = d6.w4`, set `x25 = x0 = fsp + 0x1c8`, and load `d7.w0..w3` into `(q1, q0)`. -/
theorem step_chunk_c_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {fsp fpVal buf : BitVec 64} {n : Nat}
    {ws dstWs : StoresWords}
    (hpc : s.pc = mPcPlaced 0x840)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfp : s.readReg64 .fp = fpVal)
    (hal : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx1 : s.readReg64 .x1 = fsp + 0x310#64)
    (hx2 : s.readReg64 .x2 = 0x140#64)
    (hx8 : s.readReg64 (.gpr 8#5) = ws.d4.w4)
    (hx9 : s.readReg64 (.gpr 9#5) = ws.d0.w4)
    (hx10 : s.readReg64 (.gpr 10#5) = ws.d5.w4)
    (hx11 : s.readReg64 (.gpr 11#5) = ws.d7.w4)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx20 : s.readReg64 (.gpr 20#5) = fsp + 0x1b8#64)
    (hx21 : s.readReg64 (.gpr 21#5) = fsp + 0x310#64)
    (hx22 : s.readReg64 (.gpr 22#5) = fsp + 0x78#64)
    (hx23 : s.readReg64 (.gpr 23#5) = fsp + 0x78#64)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n) :
    SepWP ((blkPC_617).rebase (blkPl_617).base H) (mPcPlaced 0x868) s
      (dirStackAt (fsp + 0x168#64) ws.d6 ∗
        dirStackAt (fsp + 0x190#64) ws.d7 ∗
        dirStackAt (fsp + 0x3b0#64) ⟨ws.d4.w0, ws.d4.w1, ws.d4.w2, ws.d4.w3, dstWs.d4.w4⟩ ∗
        dirStackAt (fsp + 0x3d8#64) ⟨ws.d5.w0, ws.d5.w1, ws.d5.w2, ws.d5.w3, dstWs.d5.w4⟩ ∗
        dirStackAt (fsp + 0x400#64) dstWs.d6)
      (fun s1 P1 =>
        (s1.sp = fsp ∧
          s1.readReg64 .fp = fpVal ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
          s1.readReg64 .x0 = fsp + 0x1c8#64 ∧
          s1.readReg64 .x1 = fsp + 0x310#64 ∧
          s1.readReg64 .x2 = 0x140#64 ∧
          s1.readReg64 (.gpr 9#5) = ws.d0.w4 ∧
          s1.readReg64 (.gpr 10#5) = ws.d6.w4 ∧
          s1.readReg64 (.gpr 11#5) = ws.d7.w4 ∧
          s1.readReg64 (.gpr 19#5) = buf ∧
          s1.readReg64 (.gpr 21#5) = fsp + 0x310#64 ∧
          s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n ∧
          s1.readReg64 (.gpr 25#5) = fsp + 0x1c8#64 ∧
          s1.readVReg128 0#5 = (ws.d7.w3 ++ ws.d7.w2) ∧
          s1.readVReg128 1#5 = (ws.d7.w1 ++ ws.d7.w0) ∧
          s1.fs = s.fs ∧
          s1.trace = s.trace) ∧
        P1 =
          (dirStackAt (fsp + 0x168#64) ws.d6 ∗
            dirStackAt (fsp + 0x190#64) ws.d7 ∗
            dirStackAt (fsp + 0x3b0#64) ws.d4 ∗
            dirStackAt (fsp + 0x3d8#64) ws.d5 ∗
            dirStackAt (fsp + 0x400#64) ⟨ws.d6.w0, ws.d6.w1, ws.d6.w2, ws.d6.w3, dstWs.d6.w4⟩))
      (fun _ => ⌜False⌝) := by
  subst hsp
  simp only [mPcPlaced_eq] at hpc ⊢
  wp_simp_pre [dirStackAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  refine ⟨⟨by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *]⟩, ?_⟩
  simp only [dirStackAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- `M+0x868 .. M+0x8a4` (16 instructions, ending at `bl memcpy`): finish `d6`, copy `d0` and `d7`
completely, move `out`'s `Vec` header (`outLen` @0x0, `outCap` @0x8, `outPtr` @0x18), store `8` at
`[fsp+0x1c0]`, and issue `bl memcpy(fsp + 0x1c8, fsp + 0x310, 0x140)`. -/
theorem step_chunk_d_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {fsp fpVal buf outCap outPtr outLen u00 u08 u18 u1c0 : BitVec 64} {n : Nat}
    {ws dstWs : StoresWords}
    (hpc : s.pc = mPcPlaced 0x868)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfp : s.readReg64 .fp = fpVal)
    (hal : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = fsp + 0x1c8#64)
    (hx1 : s.readReg64 .x1 = fsp + 0x310#64)
    (hx2 : s.readReg64 .x2 = 0x140#64)
    (hx9 : s.readReg64 (.gpr 9#5) = ws.d0.w4)
    (hx10 : s.readReg64 (.gpr 10#5) = ws.d6.w4)
    (hx11 : s.readReg64 (.gpr 11#5) = ws.d7.w4)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx21 : s.readReg64 (.gpr 21#5) = fsp + 0x310#64)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : s.readReg64 (.gpr 25#5) = fsp + 0x1c8#64)
    (hq0 : s.readVReg128 0#5 = (ws.d7.w3 ++ ws.d7.w2))
    (hq1 : s.readVReg128 1#5 = (ws.d7.w1 ++ ws.d7.w0)) :
    SepWP ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName) s
      ((fsp ↦₆₄ u00) ∗
        ((fsp + 0x08#64) ↦₆₄ u08) ∗
        ((fsp + 0x18#64) ↦₆₄ u18) ∗
        ((fsp + 0x1c0#64) ↦₆₄ u1c0) ∗
        ((fsp + 0x2f8#64) ↦₆₄ outCap) ∗
        ((fsp + 0x300#64) ↦₆₄ outPtr) ∗
        ((fsp + 0x308#64) ↦₆₄ outLen) ∗
        dirStackAt (fsp + 0x78#64) ws.d0 ∗
        dirStackAt (fsp + 0x310#64) dstWs.d0 ∗
        dirStackAt (fsp + 0x400#64) ⟨ws.d6.w0, ws.d6.w1, ws.d6.w2, ws.d6.w3, dstWs.d6.w4⟩ ∗
        dirStackAt (fsp + 0x428#64) dstWs.d7)
      (fun s1 P1 =>
        (s1.sp = fsp ∧
          s1.readReg64 .fp = fpVal ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
          s1.readReg64 .lr = mPcPlaced 0x8a8 ∧
          s1.readReg64 .x0 = fsp + 0x1c8#64 ∧
          s1.readReg64 .x1 = fsp + 0x310#64 ∧
          s1.readReg64 .x2 = 0x140#64 ∧
          s1.readReg64 (.gpr 19#5) = buf ∧
          s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n ∧
          s1.readReg64 (.gpr 25#5) = fsp + 0x1c8#64 ∧
          s1.fs = s.fs ∧
          s1.trace = s.trace) ∧
        P1 =
          ((fsp ↦₆₄ outLen) ∗
            ((fsp + 0x08#64) ↦₆₄ outCap) ∗
            ((fsp + 0x18#64) ↦₆₄ outPtr) ∗
            ((fsp + 0x1c0#64) ↦₆₄ 8#64) ∗
            ((fsp + 0x2f8#64) ↦₆₄ outCap) ∗
            ((fsp + 0x300#64) ↦₆₄ outPtr) ∗
            ((fsp + 0x308#64) ↦₆₄ outLen) ∗
            dirStackAt (fsp + 0x78#64) ws.d0 ∗
            dirStackAt (fsp + 0x310#64) ws.d0 ∗
            dirStackAt (fsp + 0x400#64) ws.d6 ∗
            dirStackAt (fsp + 0x428#64) ws.d7))
      (fun _ => ⌜False⌝) := by
  subst hsp
  simp only [mPcPlaced_eq] at hpc ⊢
  wp_simp_pre [dirStackAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  refine ⟨⟨by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *]⟩, ?_⟩
  simp only [dirStackAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- `M+0x8a8 .. M+0x8b4` (4 instructions, landing at `M+0x8b8`): initialize loop index and constants
(`x23 = 0`, `x26 = 0x28`, `[fsp+0x58] = 1`). -/
theorem step_post_mc2_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {fsp fpVal buf u58 : BitVec 64} {n : Nat}
    (hpc : s.pc = mPcPlaced 0x8a8)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfp : s.readReg64 .fp = fpVal)
    (hal : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : s.readReg64 (.gpr 25#5) = fsp + 0x1c8#64) :
    SepWP ((blkPC_617).rebase (blkPl_617).base H) (mPcPlaced 0x8b8) s
      ((fsp + 0x58#64) ↦₆₄ u58)
      (fun s1 P1 =>
        (s1.sp = fsp ∧
          s1.readReg64 .fp = fpVal ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
          s1.readReg64 (.gpr 19#5) = buf ∧
          s1.readReg64 (.gpr 23#5) = 0#64 ∧
          s1.readReg64 (.gpr 25#5) = fsp + 0x1c8#64 ∧
          s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n ∧
          s1.readReg64 (.gpr 26#5) = 0x28#64 ∧
          s1.fs = s.fs ∧
          s1.trace = s.trace) ∧
        P1 = ((fsp + 0x58#64) ↦₆₄ 1#64))
      (fun _ => ⌜False⌝) := by
  subst hsp
  simp only [mPcPlaced_eq] at hpc ⊢
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  exact ⟨⟨by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *],
    by simp only [arm64_norm, *]⟩, rfl⟩

end M5MovesSteps

/-! ## 2. Top-Level `m5_moves_placed` Composition (`M+0x7b0 → M+0x8b8`) -/

/-- Moves `run`'s `Ok (Stores, Vec<u8>)` payload (`M+0x7b0 → M+0x8b8`) from `fsp + 0x1b8` into
`[fsp + 0x00 .. 0x20]` + `[fsp + 0x1c8 .. 0x308]`, initializes the commit loop registers, and
establishes `AtM5LoopPlaced … 0` and `m5LoopMemPlaced … 0` with `s'.fs = s.fs` and
`s'.trace = s.trace`. -/
theorem m5_moves_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks}
    {io : IoModel} {i : Inputs} {c : CallV} {g : StoresGhost}
    {out inp : List (BitVec 8)} {s0 s : State} {stk n : Nat}
    {buf inCap inPtr : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hs : AtM4EndPlaced CodeOk i s0 s c n buf inCap)
    (hnext : ∀ (s' : State) (outCap outPtr : BitVec 64),
      s'.fs = s.fs →
      s'.trace = s.trace →
      AtM5LoopPlaced CodeOk io s.fs.files s.trace g s0 s' n buf 0 →
      ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s'
        (m5LoopMemPlaced A s0 stk n outCap outPtr inCap inPtr buf out inp ps g 0)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5CellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ anyHeap)
      Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp := rfl
  have hfsp4e0 : s0.sp - 0x4e0#64 = fsp := rfl
  have hmc := M5MovesHelpers.main_sessionMemcpyRegionFs_placed_ok hA
  refine sepWPp_with_stk_le_two_pow_64 (s0 := s0) (stk := stk)
    (by simp [mainFrameSize] at hstk ⊢; omega)
    (F := ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      locals fsp (m5CellsPlaced A fsp inPtr g out) ∗ A.pool ∗ anyHeap)
    (Entails.of_eq (by ac_rfl)) fun hstk64 => ?_
  have hext_le : extHookStack ≤ stk - mainFrameSize := by
    simp [mainFrameSize, extHookStack] at hstk ⊢; omega
  have hsub_le64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  let outerFrame : M5MovesHelpers.M5OpenVarsPlaced → SepProp := fun v =>
    ownedBytes A v.outCap v.outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      mainSaved s0 ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
        (stk - mainFrameSize - extHookStack) ∗
      A.pool ∗ anyHeap
  have hopen :
      ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗
        locals fsp (m5CellsPlaced A fsp inPtr g out) ∗
        stackAt fsp (stk - mainFrameSize) ∗
        A.pool ∗ anyHeap ⊢
      (∃∗ v : M5MovesHelpers.M5OpenVarsPlaced,
        (fsp ↦₆₄ v.u00) ∗
          ((fsp + 0x08#64) ↦₆₄ v.u08) ∗
          ((fsp + 0x10#64) ↦₆₄ v.u10) ∗
          ((fsp + 0x18#64) ↦₆₄ v.u18) ∗
          ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ((fsp + 0x58#64) ↦₆₄ v.u58) ∗
          memRegion (fsp + 0x78#64) 0x140 ∗
          ((fsp + 0x1b8#64) ↦ₛ M5MovesHelpers.storesBytes v.ws) ∗
          ((fsp + 0x2f8#64) ↦₆₄ v.outCap) ∗
          ((fsp + 0x300#64) ↦₆₄ v.outPtr) ∗
          ((fsp + 0x308#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          M5MovesHelpers.storesStackAt (fsp + 0x310#64) v.dstWs ∗
          M5MovesHelpers.m5LocalsRestPlaced fsp ∗
          M5MovesHelpers.storesHeap A v.ws g ∗
          stackAt fsp extHookStack ∗
          outerFrame v) ∗ emp := by
    rw [stackAt_split_ge fsp hext_le hsub_le64, sepConj_emp]
    refine Entails.trans
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono_left (M5MovesHelpers.m5_locals_open_placed A fsp inPtr g out))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v
    refine Entails.sepExists_right v ?_
    dsimp only [outerFrame]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hopen (M5MovesHelpers.sepWPp_exists_left fun v => ?_)
  set outLen := BitVec.ofNat 64 out.length
  refine M5MovesHelpers.sepWP_seq_placed_frame hs.base.inv
    (F := (fsp ↦₆₄ v.u00) ∗
      ((fsp + 0x08#64) ↦₆₄ v.u08) ∗
      ((fsp + 0x18#64) ↦₆₄ v.u18) ∗
      ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ((fsp + 0x58#64) ↦₆₄ v.u58) ∗
      memRegion (fsp + 0x78#64) 0x140 ∗
      ((fsp + 0x1b8#64) ↦ₛ M5MovesHelpers.storesBytes v.ws) ∗
      ((fsp + 0x2f8#64) ↦₆₄ v.outCap) ∗
      ((fsp + 0x300#64) ↦₆₄ v.outPtr) ∗
      ((fsp + 0x308#64) ↦₆₄ outLen) ∗
      M5MovesHelpers.storesStackAt (fsp + 0x310#64) v.dstWs ∗
      M5MovesHelpers.m5LocalsRestPlaced fsp ∗
      M5MovesHelpers.storesHeap A v.ws g ∗
      stackAt fsp extHookStack ∗
      outerFrame v)
    (Entails.of_eq (by ac_rfl))
    (M5MovesSteps.step_pre_mc1_placed (fsp := fsp) (u10 := v.u10)
      hs.base.pc hs.base.run hs.base.sp hs.base.fp
      hs.base.spAligned_state hs.base.vregs hs.x19 hs.x21 hs.x22 hs.x23 hs.x24)
    fun s1 hinv1 hpc1 hrun1 hpost1 => ?_
  rcases hpost1 with ⟨hsp1, hfp1, hvregs1, hlr1, hx0_1, hx1_1, hx2_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hfs1, htr1⟩
  refine M5MovesHelpers.step_memcpy_region_fs_placed (bs := M5MovesHelpers.storesBytes v.ws)
    hmc hinv1 hpc1 hrun1 hsp1
    (M5MovesHelpers.spAligned_of_s0 hs.base.spAligned (hsp1.trans hfsp4e0.symm))
    hlr1 hx0_1 hx1_1
    (by simp [hx2_1])
    hfs1 htr1
    (F := (fsp ↦₆₄ v.u00) ∗
      ((fsp + 0x08#64) ↦₆₄ v.u08) ∗
      ((fsp + 0x10#64) ↦₆₄ inCap) ∗
      ((fsp + 0x18#64) ↦₆₄ v.u18) ∗
      ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ((fsp + 0x58#64) ↦₆₄ v.u58) ∗
      ((fsp + 0x2f8#64) ↦₆₄ v.outCap) ∗
      ((fsp + 0x300#64) ↦₆₄ v.outPtr) ∗
      ((fsp + 0x308#64) ↦₆₄ outLen) ∗
      M5MovesHelpers.storesStackAt (fsp + 0x310#64) v.dstWs ∗
      M5MovesHelpers.m5LocalsRestPlaced fsp ∗
      M5MovesHelpers.storesHeap A v.ws g ∗
      outerFrame v)
    (by rw [M5MovesHelpers.storesBytes_length]; exact Entails.of_eq (by ac_rfl))
    fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2,
    _, _, _, hfp2, hvregs2⟩
  refine SepWPp.weaken_pre
    (sepConj_mono_left (M5MovesHelpers.m5_post_first_memcpy fsp v.ws))
    (M5MovesHelpers.sepWPp_exists_left fun u1c0 => ?_)
  dsimp only [M5MovesHelpers.storesStackAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine M5MovesHelpers.sepWP_seq_placed_frame hinv2
    (F := (M5MovesHelpers.dirStackAt (fsp + 0x118#64) v.ws.d4 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x140#64) v.ws.d5 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x168#64) v.ws.d6) ∗
      (M5MovesHelpers.dirStackAt (fsp + 0x310#64) v.dstWs.d0 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x388#64) v.dstWs.d3 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x3b0#64) v.dstWs.d4 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x3d8#64) v.dstWs.d5 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x400#64) v.dstWs.d6 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x428#64) v.dstWs.d7) ∗
      (fsp ↦₆₄ v.u00) ∗
      ((fsp + 0x08#64) ↦₆₄ v.u08) ∗
      ((fsp + 0x10#64) ↦₆₄ inCap) ∗
      ((fsp + 0x18#64) ↦₆₄ v.u18) ∗
      ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ((fsp + 0x58#64) ↦₆₄ v.u58) ∗
      ((fsp + 0x1c0#64) ↦₆₄ u1c0) ∗
      memRegion (fsp + 0x1b8#64) 0x08 ∗
      memRegion (fsp + 0x1c8#64) 0x130 ∗
      ((fsp + 0x2f8#64) ↦₆₄ v.outCap) ∗
      ((fsp + 0x300#64) ↦₆₄ v.outPtr) ∗
      ((fsp + 0x308#64) ↦₆₄ outLen) ∗
      M5MovesHelpers.m5LocalsRestPlaced fsp ∗
      M5MovesHelpers.storesHeap A v.ws g ∗
      stackAt fsp extHookStack ∗
      outerFrame v)
    (Entails.of_eq (by ac_rfl))
    (M5MovesSteps.step_chunk_a_placed (fsp := fsp) (ws := v.ws) (dstWs := v.dstWs)
      hpc2 hrun2 hsp2 (hfp2.trans hfp1)
      (M5MovesHelpers.spAligned_of_s0 hs.base.spAligned (hsp2.trans hfsp4e0.symm))
      (hvregs2.trans hvregs1)
      (hx19_2.trans hx19_1) (hx20_2.trans hx20_1) (hx21_2.trans hx21_1)
      (hx22_2.trans hx22_1) (hx23_2.trans hx23_1) (hx24_2.trans hx24_1)
      (hx25_2.trans hx25_1))
    fun s3 hinv3 hpc3 hrun3 hpost3 => ?_
  rcases hpost3 with ⟨hsp3, hfp3, hvregs3, hx1_3, hx2_3, hx8_3, hx9_3, hx10_3, hx11_3,
    hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hfs3, htr3⟩
  refine M5MovesHelpers.sepWP_seq_placed_frame hinv3
    (F := (M5MovesHelpers.dirStackAt (fsp + 0x78#64) v.ws.d0 ∗
        M5MovesHelpers.dirStackAt (fsp + 0xa0#64) v.ws.d1 ∗
        M5MovesHelpers.dirStackAt (fsp + 0xc8#64) v.ws.d2 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x168#64) v.ws.d6 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x190#64) v.ws.d7) ∗
      (M5MovesHelpers.dirStackAt (fsp + 0x310#64) v.dstWs.d0 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x338#64) v.ws.d1 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x400#64) v.dstWs.d6 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x428#64) v.dstWs.d7) ∗
      (fsp ↦₆₄ v.u00) ∗
      ((fsp + 0x08#64) ↦₆₄ v.u08) ∗
      ((fsp + 0x10#64) ↦₆₄ inCap) ∗
      ((fsp + 0x18#64) ↦₆₄ v.u18) ∗
      ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ((fsp + 0x58#64) ↦₆₄ v.u58) ∗
      ((fsp + 0x1c0#64) ↦₆₄ u1c0) ∗
      memRegion (fsp + 0x1b8#64) 0x08 ∗
      memRegion (fsp + 0x1c8#64) 0x130 ∗
      ((fsp + 0x2f8#64) ↦₆₄ v.outCap) ∗
      ((fsp + 0x300#64) ↦₆₄ v.outPtr) ∗
      ((fsp + 0x308#64) ↦₆₄ outLen) ∗
      M5MovesHelpers.m5LocalsRestPlaced fsp ∗
      M5MovesHelpers.storesHeap A v.ws g ∗
      stackAt fsp extHookStack ∗
      outerFrame v)
    (Entails.of_eq (by ac_rfl))
    (M5MovesSteps.step_chunk_b_placed (fsp := fsp) (ws := v.ws) (dstWs := v.dstWs)
      hpc3 hrun3 hsp3 hfp3
      (M5MovesHelpers.spAligned_of_s0 hs.base.spAligned (hsp3.trans hfsp4e0.symm))
      hvregs3 hx1_3 hx2_3 hx8_3 hx9_3 hx10_3 hx11_3
      hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3)
    fun s4 hinv4 hpc4 hrun4 hpost4 => ?_
  rcases hpost4 with ⟨hsp4, hfp4, hvregs4, hx1_4, hx2_4, hx8_4, hx9_4, hx10_4, hx11_4,
    hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hfs4, htr4⟩
  refine M5MovesHelpers.sepWP_seq_placed_frame hinv4
    (F := (M5MovesHelpers.dirStackAt (fsp + 0x78#64) v.ws.d0 ∗
        M5MovesHelpers.dirStackAt (fsp + 0xa0#64) v.ws.d1 ∗
        M5MovesHelpers.dirStackAt (fsp + 0xc8#64) v.ws.d2 ∗
        M5MovesHelpers.dirStackAt (fsp + 0xf0#64) v.ws.d3 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x118#64) v.ws.d4 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x140#64) v.ws.d5) ∗
      (M5MovesHelpers.dirStackAt (fsp + 0x310#64) v.dstWs.d0 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x338#64) v.ws.d1 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x360#64) v.ws.d2 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x388#64) v.ws.d3 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x428#64) v.dstWs.d7) ∗
      (fsp ↦₆₄ v.u00) ∗
      ((fsp + 0x08#64) ↦₆₄ v.u08) ∗
      ((fsp + 0x10#64) ↦₆₄ inCap) ∗
      ((fsp + 0x18#64) ↦₆₄ v.u18) ∗
      ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ((fsp + 0x58#64) ↦₆₄ v.u58) ∗
      ((fsp + 0x1c0#64) ↦₆₄ u1c0) ∗
      memRegion (fsp + 0x1b8#64) 0x08 ∗
      memRegion (fsp + 0x1c8#64) 0x130 ∗
      ((fsp + 0x2f8#64) ↦₆₄ v.outCap) ∗
      ((fsp + 0x300#64) ↦₆₄ v.outPtr) ∗
      ((fsp + 0x308#64) ↦₆₄ outLen) ∗
      M5MovesHelpers.m5LocalsRestPlaced fsp ∗
      M5MovesHelpers.storesHeap A v.ws g ∗
      stackAt fsp extHookStack ∗
      outerFrame v)
    (Entails.of_eq (by ac_rfl))
    (M5MovesSteps.step_chunk_c_placed (fsp := fsp) (ws := v.ws) (dstWs := v.dstWs)
      hpc4 hrun4 hsp4 hfp4
      (M5MovesHelpers.spAligned_of_s0 hs.base.spAligned (hsp4.trans hfsp4e0.symm))
      hvregs4 hx1_4 hx2_4 hx8_4 hx9_4 hx10_4 hx11_4
      hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4)
    fun s5 hinv5 hpc5 hrun5 hpost5 => ?_
  rcases hpost5 with ⟨hsp5, hfp5, hvregs5, hx0_5, hx1_5, hx2_5, hx9_5, hx10_5, hx11_5,
    hx19_5, hx21_5, hx24_5, hx25_5, hq0_5, hq1_5, hfs5, htr5⟩
  refine M5MovesHelpers.sepWP_seq_placed_frame hinv5
    (F := (M5MovesHelpers.dirStackAt (fsp + 0xa0#64) v.ws.d1 ∗
        M5MovesHelpers.dirStackAt (fsp + 0xc8#64) v.ws.d2 ∗
        M5MovesHelpers.dirStackAt (fsp + 0xf0#64) v.ws.d3 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x118#64) v.ws.d4 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x140#64) v.ws.d5 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x168#64) v.ws.d6 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x190#64) v.ws.d7) ∗
      (M5MovesHelpers.dirStackAt (fsp + 0x338#64) v.ws.d1 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x360#64) v.ws.d2 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x388#64) v.ws.d3 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x3b0#64) v.ws.d4 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x3d8#64) v.ws.d5) ∗
      ((fsp + 0x10#64) ↦₆₄ inCap) ∗
      ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ((fsp + 0x58#64) ↦₆₄ v.u58) ∗
      memRegion (fsp + 0x1b8#64) 0x08 ∗
      memRegion (fsp + 0x1c8#64) 0x130 ∗
      M5MovesHelpers.m5LocalsRestPlaced fsp ∗
      M5MovesHelpers.storesHeap A v.ws g ∗
      stackAt fsp extHookStack ∗
      outerFrame v)
    (Entails.of_eq (by ac_rfl))
    (M5MovesSteps.step_chunk_d_placed (fsp := fsp) (ws := v.ws) (dstWs := v.dstWs)
      (outCap := v.outCap) (outPtr := v.outPtr) (outLen := outLen)
      (u00 := v.u00) (u08 := v.u08) (u18 := v.u18) (u1c0 := u1c0)
      hpc5 hrun5 hsp5 hfp5
      (M5MovesHelpers.spAligned_of_s0 hs.base.spAligned (hsp5.trans hfsp4e0.symm))
      hvregs5 hx0_5 hx1_5 hx2_5 hx9_5 hx10_5 hx11_5
      hx19_5 hx21_5 hx24_5 hx25_5 hq0_5 hq1_5)
    fun s6 hinv6 hpc6 hrun6 hpost6 => ?_
  rcases hpost6 with ⟨hsp6, hfp6, hvregs6, hlr6, hx0_6, hx1_6, hx2_6,
    hx19_6, hx24_6, hx25_6, hfs6, htr6⟩
  have hpre_mc2 :
      ((fsp ↦₆₄ outLen) ∗
        ((fsp + 0x08#64) ↦₆₄ v.outCap) ∗
        ((fsp + 0x18#64) ↦₆₄ v.outPtr) ∗
        ((fsp + 0x1c0#64) ↦₆₄ 8#64) ∗
        ((fsp + 0x2f8#64) ↦₆₄ v.outCap) ∗
        ((fsp + 0x300#64) ↦₆₄ v.outPtr) ∗
        ((fsp + 0x308#64) ↦₆₄ outLen) ∗
        M5MovesHelpers.dirStackAt (fsp + 0x78#64) v.ws.d0 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x310#64) v.ws.d0 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x400#64) v.ws.d6 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x428#64) v.ws.d7) ∗
      ((M5MovesHelpers.dirStackAt (fsp + 0xa0#64) v.ws.d1 ∗
        M5MovesHelpers.dirStackAt (fsp + 0xc8#64) v.ws.d2 ∗
        M5MovesHelpers.dirStackAt (fsp + 0xf0#64) v.ws.d3 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x118#64) v.ws.d4 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x140#64) v.ws.d5 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x168#64) v.ws.d6 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x190#64) v.ws.d7) ∗
      (M5MovesHelpers.dirStackAt (fsp + 0x338#64) v.ws.d1 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x360#64) v.ws.d2 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x388#64) v.ws.d3 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x3b0#64) v.ws.d4 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x3d8#64) v.ws.d5) ∗
      ((fsp + 0x10#64) ↦₆₄ inCap) ∗
      ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ((fsp + 0x58#64) ↦₆₄ v.u58) ∗
      memRegion (fsp + 0x1b8#64) 0x08 ∗
      memRegion (fsp + 0x1c8#64) 0x130 ∗
      M5MovesHelpers.m5LocalsRestPlaced fsp ∗
      M5MovesHelpers.storesHeap A v.ws g ∗
      stackAt fsp extHookStack ∗
      outerFrame v) ⊢
      memRegion (fsp + 0x1c8#64) (M5MovesHelpers.storesBytes v.ws).length ∗
        ((fsp + 0x310#64) ↦ₛ M5MovesHelpers.storesBytes v.ws) ∗
        stackAt fsp extHookStack ∗
        ((fsp ↦₆₄ outLen) ∗
          ((fsp + 0x08#64) ↦₆₄ v.outCap) ∗
          ((fsp + 0x10#64) ↦₆₄ inCap) ∗
          ((fsp + 0x18#64) ↦₆₄ v.outPtr) ∗
          ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ((fsp + 0x58#64) ↦₆₄ v.u58) ∗
          M5MovesHelpers.storesHeap A v.ws g ∗
          outerFrame v ∗
          M5MovesHelpers.m5PreMemcpy2RestPlaced fsp) := by
    rw [M5MovesHelpers.storesBytes_length]
    have hmid := M5MovesHelpers.m5_pre_second_memcpy_placed fsp v.outCap v.outPtr outLen v.ws
    dsimp only [M5MovesHelpers.storesStackAt] at hmid
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmid
    refine Entails.trans (Entails.of_eq (show _ =
      ((M5MovesHelpers.dirStackAt (fsp + 0x78#64) v.ws.d0 ∗
        M5MovesHelpers.dirStackAt (fsp + 0xa0#64) v.ws.d1 ∗
        M5MovesHelpers.dirStackAt (fsp + 0xc8#64) v.ws.d2 ∗
        M5MovesHelpers.dirStackAt (fsp + 0xf0#64) v.ws.d3 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x118#64) v.ws.d4 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x140#64) v.ws.d5 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x168#64) v.ws.d6 ∗
        M5MovesHelpers.dirStackAt (fsp + 0x190#64) v.ws.d7) ∗
        memRegion (fsp + 0x1b8#64) 0x08 ∗
        ((fsp + 0x1c0#64) ↦₆₄ 8#64) ∗
        memRegion (fsp + 0x1c8#64) 0x130 ∗
        ((fsp + 0x2f8#64) ↦₆₄ v.outCap) ∗
        ((fsp + 0x300#64) ↦₆₄ v.outPtr) ∗
        ((fsp + 0x308#64) ↦₆₄ outLen) ∗
        (M5MovesHelpers.dirStackAt (fsp + 0x310#64) v.ws.d0 ∗
          M5MovesHelpers.dirStackAt (fsp + 0x338#64) v.ws.d1 ∗
          M5MovesHelpers.dirStackAt (fsp + 0x360#64) v.ws.d2 ∗
          M5MovesHelpers.dirStackAt (fsp + 0x388#64) v.ws.d3 ∗
          M5MovesHelpers.dirStackAt (fsp + 0x3b0#64) v.ws.d4 ∗
          M5MovesHelpers.dirStackAt (fsp + 0x3d8#64) v.ws.d5 ∗
          M5MovesHelpers.dirStackAt (fsp + 0x400#64) v.ws.d6 ∗
          M5MovesHelpers.dirStackAt (fsp + 0x428#64) v.ws.d7) ∗
        M5MovesHelpers.m5LocalsRestPlaced fsp) ∗
      (stackAt fsp extHookStack ∗
        (fsp ↦₆₄ outLen) ∗
        ((fsp + 0x08#64) ↦₆₄ v.outCap) ∗
        ((fsp + 0x10#64) ↦₆₄ inCap) ∗
        ((fsp + 0x18#64) ↦₆₄ v.outPtr) ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        ((fsp + 0x58#64) ↦₆₄ v.u58) ∗
        M5MovesHelpers.storesHeap A v.ws g ∗
        outerFrame v) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hmid) ?_
    exact Entails.of_eq (by ac_rfl)
  refine M5MovesHelpers.step_memcpy_region_fs_placed (bs := M5MovesHelpers.storesBytes v.ws)
    hmc hinv6 hpc6 hrun6 hsp6
    (M5MovesHelpers.spAligned_of_s0 hs.base.spAligned (hsp6.trans hfsp4e0.symm))
    hlr6 hx0_6 hx1_6
    (by simp [hx2_6])
    (hfs6.trans (hfs5.trans (hfs4.trans (hfs3.trans hfs2))))
    (htr6.trans (htr5.trans (htr4.trans (htr3.trans htr2))))
    hpre_mc2
    fun s7 hinv7 hpc7 hrun7 hsp7 hcs7 hfs7 htr7 => ?_
  rcases hcs7 with ⟨hx19_7, _, _, _, _, hx24_7, hx25_7, _, _, _, hfp7, hvregs7⟩
  refine M5MovesHelpers.sepWP_seq_placed_frame hinv7
    (F := (((fsp + 0x1c8#64) ↦ₛ M5MovesHelpers.storesBytes v.ws) ∗
        ((fsp + 0x310#64) ↦ₛ M5MovesHelpers.storesBytes v.ws)) ∗
      stackAt fsp extHookStack ∗
      (fsp ↦₆₄ outLen) ∗
      ((fsp + 0x08#64) ↦₆₄ v.outCap) ∗
      ((fsp + 0x10#64) ↦₆₄ inCap) ∗
      ((fsp + 0x18#64) ↦₆₄ v.outPtr) ∗
      ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      M5MovesHelpers.storesHeap A v.ws g ∗
      outerFrame v ∗
      M5MovesHelpers.m5PreMemcpy2RestPlaced fsp)
    (Entails.of_eq (by ac_rfl))
    (M5MovesSteps.step_post_mc2_placed (fsp := fsp) (u58 := v.u58)
      hpc7 hrun7 hsp7 (hfp7.trans hfp6)
      (M5MovesHelpers.spAligned_of_s0 hs.base.spAligned (hsp7.trans hfsp4e0.symm))
      (hvregs7.trans hvregs6)
      (hx19_7.trans hx19_6) (hx24_7.trans hx24_6) (hx25_7.trans hx25_6))
    fun s8 hinv8 hpc8 hrun8 hpost8 => ?_
  rcases hpost8 with ⟨hsp8, hfp8, hvregs8, hx19_8, hx23_8, hx25_8, hx24_8, hx26_8, hfs8, htr8⟩
  have hfs_final : s8.fs = s.fs := hfs8.trans hfs7
  have htr_final : s8.trace = s.trace := htr8.trans htr7
  have hbase8 : InMainPlaced CodeOk s0 s8 0x8b8 :=
    { pc := hpc8
      run := hrun8
      sp := hsp8
      fp := hfp8
      inv := hinv8
      vregs := hvregs8
      spAligned := hs.base.spAligned }
  have hloop0 : AtM5LoopPlaced CodeOk io s.fs.files s.trace g s0 s8 n buf 0 :=
    AtM5LoopPlaced.of_zero hbase8 hx19_8 hx23_8 hx25_8 hx24_8 hx26_8
      (congrArg FsState.files hfs_final) htr_final
  have hclose :
      ((fsp + 0x58#64) ↦₆₄ 1#64) ∗
        ((((fsp + 0x1c8#64) ↦ₛ M5MovesHelpers.storesBytes v.ws) ∗
          ((fsp + 0x310#64) ↦ₛ M5MovesHelpers.storesBytes v.ws)) ∗
        stackAt fsp extHookStack ∗
        (fsp ↦₆₄ outLen) ∗
        ((fsp + 0x08#64) ↦₆₄ v.outCap) ∗
        ((fsp + 0x10#64) ↦₆₄ inCap) ∗
        ((fsp + 0x18#64) ↦₆₄ v.outPtr) ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        M5MovesHelpers.storesHeap A v.ws g ∗
        outerFrame v ∗
        M5MovesHelpers.m5PreMemcpy2RestPlaced fsp) ⊢
      m5LoopMemPlaced A s0 stk n v.outCap v.outPtr inCap inPtr buf out inp ps g 0 := by
    dsimp only [outerFrame, m5LoopMemPlaced]
    change _ ⊢
      ownedBytes A v.outCap v.outPtr outLen out ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗
        locals fsp (m5LoopCellsPlaced A fsp v.outCap v.outPtr outLen inCap inPtr g 0) ∗
        stackAt fsp (stk - mainFrameSize) ∗
        A.pool ∗ anyHeap
    refine Entails.trans (Entails.of_eq (show _ =
      ((fsp ↦₆₄ outLen) ∗
        ((fsp + 0x08#64) ↦₆₄ v.outCap) ∗
        ((fsp + 0x10#64) ↦₆₄ inCap) ∗
        ((fsp + 0x18#64) ↦₆₄ v.outPtr) ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        ((fsp + 0x58#64) ↦₆₄ 1#64) ∗
        ((fsp + 0x1c8#64) ↦ₛ M5MovesHelpers.storesBytes v.ws) ∗
        ((fsp + 0x310#64) ↦ₛ M5MovesHelpers.storesBytes v.ws) ∗
        M5MovesHelpers.m5PreMemcpy2RestPlaced fsp ∗
        M5MovesHelpers.storesHeap A v.ws g) ∗
      (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - extHookStack) ∗
        stackAt fsp extHookStack) ∗
      (ownedBytes A v.outCap v.outPtr outLen out ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗ A.pool ∗ anyHeap) by ac_rfl)) ?_
    rw [← stackAt_split_ge fsp hext_le hsub_le64]
    refine Entails.trans
      (sepConj_mono_left (M5MovesHelpers.m5_locals_close_placed A fsp v.outCap v.outPtr outLen inCap inPtr 1#64 v.ws g)) ?_
    exact Entails.of_eq (by ac_rfl)
  exact SepWPp.weaken_pre hclose (hnext s8 v.outCap v.outPtr hfs_final htr_final hloop0)

end CryptoVerification.SignalSession.Cli.MainHops
