/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledSteps
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ekReceivedCt1Sampled` Arm Steps (Relocatable)

Relocatable `[LibsignalPlacement]` jump-table dispatch (`+36 -> +3392`) and instruction stepping
lemmas for `.ekReceivedCt1Sampled` (`lsmpl.base 332 + 3392#64`, tag `10#64`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Relocatable Dispatch (`+36 -> +3392`, Block `332`) -/

theorem states_recv_dispatch_ekReceivedCt1Sampled_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (fsp st_ptr : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = lsmpl.base 332 + 36#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 3392#64) s1
      ((st_ptr ↦₆₄ 10#64) ∗ statesRecvRoPlacedAt ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ (st_ptr ↦₆₄ 10#64) ∗ statesRecvRoPlacedAt ∗ Rest) ∧
        s2.sp = fsp ∧ s2.readReg64 .x0 = s1.readReg64 .x0 ∧ s2.readReg64 .x1 = st_ptr ∧
        s2.readReg64 .x2 = s1.readReg64 .x2 ∧ s2.readReg64 .x3 = s1.readReg64 .x3 ∧
        s2.readReg64 .x8 = 8#64 ∧ s2.readReg64 .x12 = 10#64 ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧ s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧ s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧ TraceCalleeSaved s2 s1) := by
  exact states_recv_dispatch_placed (ext := ext) s1 fsp st_ptr 10#64 Rest
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1

/-! ## 2. Relocatable Stepping Lemmas for `.ekReceivedCt1Sampled` (`+3392`, Block `332`) -/

set_option maxHeartbeats 800000 in
theorem ek_step_3392_3560_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out st_ptr msg_ptr msg_ep : BitVec 64)
    (w : Words66) (sp : SendEkSpills) (qac0 qf10 : BitVec 128) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 3392#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = st_ptr) (hx19 : s.readReg64 .x19 = out) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 3560#64) s
      (words10At (st_ptr + 8#64) w.b0 ∗ words10At (st_ptr + 88#64) w.b1 ∗
       words10At (st_ptr + 168#64) w.b2 ∗ words10At (st_ptr + 248#64) w.b3 ∗
       words10At (st_ptr + 328#64) w.b4 ∗
       ((st_ptr + 488#64) ↦₁₂₈ w.q60) ∗ ((st_ptr + 512#64) ↦₁₂₈ w.q63) ∗ ((st_ptr + 528#64) ↦₆₄ w.w65) ∗
       (msg_ptr ↦₆₄ msg_ep) ∗
       words10At (fsp + 88#64) sp.b1 ∗ words10At (fsp + 168#64) sp.b2 ∗
       words10At (fsp + 248#64) sp.b3 ∗ words10At (fsp + 328#64) sp.b4 ∗ words10At (fsp + 408#64) sp.b5 ∗
       ((fsp + 496#64) ↦₆₄ sp.w61) ∗ ((fsp + 504#64) ↦₆₄ sp.w62) ∗
       ((fsp + 2752#64) ↦₁₂₈ qac0) ∗ ((fsp + 3856#64) ↦₁₂₈ qf10) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words10At (st_ptr + 8#64) w.b0 ∗ words10At (st_ptr + 88#64) w.b1 ∗
          words10At (st_ptr + 168#64) w.b2 ∗ words10At (st_ptr + 248#64) w.b3 ∗
          words10At (st_ptr + 328#64) w.b4 ∗
          ((st_ptr + 488#64) ↦₁₂₈ w.q60) ∗ ((st_ptr + 512#64) ↦₁₂₈ w.q63) ∗ ((st_ptr + 528#64) ↦₆₄ w.w65) ∗
          (msg_ptr ↦₆₄ msg_ep) ∗
          words10At (fsp + 88#64) (ekLoadSpillsA sp w).b1 ∗ words10At (fsp + 168#64) (ekLoadSpillsA sp w).b2 ∗
          words10At (fsp + 248#64) (ekLoadSpillsA sp w).b3 ∗ words10At (fsp + 328#64) (ekLoadSpillsA sp w).b4 ∗
          words10At (fsp + 408#64) (ekLoadSpillsA sp w).b5 ∗
          ((fsp + 496#64) ↦₆₄ (ekLoadSpillsA sp w).w61) ∗ ((fsp + 504#64) ↦₆₄ (ekLoadSpillsA sp w).w62) ∗
          ((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = st_ptr + 8#64 ∧ sm.readReg64 .x1 = st_ptr ∧
        sm.readReg64 .x3 = w.b0.w3 ∧ sm.readReg64 .x4 = w.b1.w5 ∧
        sm.readReg64 .x5 = w.b4.w4 ∧ sm.readReg64 .x6 = w.b4.w0 ∧
        sm.readReg64 .x7 = w.b3.w1 ∧ sm.readReg64 .x9 = w.b3.w2 ∧
        sm.readReg64 .x10 = w.b2.w5 ∧ sm.readReg64 .x11 = w.b2.w9 ∧
        sm.readReg64 .x12 = w.b1.w8 ∧ sm.readReg64 .x13 = w.b4.w3 ∧
        sm.readReg64 .x14 = w.b3.w9 ∧ sm.readReg64 .x17 = w.b1.w3 ∧
        sm.readReg64 .x18 = w.b2.w7 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w.b1.w6 ∧ sm.readReg64 .x21 = w.b0.w7 ∧
        sm.readReg64 .x22 = w.b0.w4 ∧ sm.readReg64 .x24 = msg_ptr ∧
        sm.readReg64 .x25 = msg_ep ∧ sm.readReg64 .x26 = w.b1.w0 ∧
        sm.readReg64 .x27 = w.b1.w2 ∧ sm.readReg64 .x28 = w.w65 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.readReg64 .x30 = w.b2.w3 ∧
        sm.pstate = subsPState64 msg_ep w.w65 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx1 hx19 hx24
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_simp_pre [words10At, ekLoadSpillsA, pointsTo128, bv_add_lit_add_lit_ek, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words10At, ekLoadSpillsA, pointsTo128, bv_add_lit_add_lit_ek, Nat.reduceAdd, sepConj_assoc]
  wp_done

set_option maxHeartbeats 800000 in
theorem ek_step_3560_3732_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp st_ptr : BitVec 64)
    (w : Words66) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 3560#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = st_ptr + 8#64)
    (hx9 : s.readReg64 .x9 = w.b3.w2) (hx11 : s.readReg64 .x11 = w.b2.w9) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 3732#64) s
      (words10At (st_ptr + 248#64) w.b3 ∗ words10At (st_ptr + 328#64) w.b4 ∗
       words10At (st_ptr + 408#64) w.b5 ∗ ((st_ptr + 504#64) ↦₆₄ w.w62) ∗
       words10At (fsp + 8#64) sp.b0 ∗ words10At (fsp + 88#64) (ekLoadSpillsA sp w).b1 ∗
       words10At (fsp + 168#64) (ekLoadSpillsA sp w).b2 ∗ words10At (fsp + 248#64) (ekLoadSpillsA sp w).b3 ∗
       words10At (fsp + 408#64) (ekLoadSpillsA sp w).b5 ∗ ((fsp + 488#64) ↦₆₄ sp.w60) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words10At (st_ptr + 248#64) w.b3 ∗ words10At (st_ptr + 328#64) w.b4 ∗
          words10At (st_ptr + 408#64) w.b5 ∗ ((st_ptr + 504#64) ↦₆₄ w.w62) ∗
          words10At (fsp + 8#64) (ekLoadSpills sp w).b0 ∗ words10At (fsp + 88#64) (ekLoadSpills sp w).b1 ∗
          words10At (fsp + 168#64) (ekLoadSpills sp w).b2 ∗ words10At (fsp + 248#64) (ekLoadSpills sp w).b3 ∗
          words10At (fsp + 408#64) (ekLoadSpills sp w).b5 ∗ ((fsp + 488#64) ↦₆₄ (ekLoadSpills sp w).w60) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = st_ptr + 8#64 ∧ sm.readReg64 .x1 = s.readReg64 .x1 ∧
        sm.readReg64 .x3 = s.readReg64 .x3 ∧ sm.readReg64 .x4 = s.readReg64 .x4 ∧
        sm.readReg64 .x5 = s.readReg64 .x5 ∧ sm.readReg64 .x6 = s.readReg64 .x6 ∧
        sm.readReg64 .x7 = s.readReg64 .x7 ∧ sm.readReg64 .x10 = s.readReg64 .x10 ∧
        sm.readReg64 .x11 = w.b4.w1 ∧ sm.readReg64 .x12 = s.readReg64 .x12 ∧
        sm.readReg64 .x13 = s.readReg64 .x13 ∧ sm.readReg64 .x14 = s.readReg64 .x14 ∧
        sm.readReg64 .x15 = w.b3.w5 ∧ sm.readReg64 .x17 = s.readReg64 .x17 ∧
        sm.readReg64 .x18 = s.readReg64 .x18 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧ sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧ sm.readReg64 .x23 = w.b5.w2 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧ sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧ sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = s.readReg64 .x30 ∧
        sm.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 s.pstate) ∧
        sm.pstate.z = (ekCmpW8 s.pstate == 0#32) ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_simp_pre [words10At, ekLoadSpillsA, ekLoadSpills, bv_add_lit_add_lit_ek, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words10At, ekLoadSpillsA, ekLoadSpills, ekCmpW8, bv_add_lit_add_lit_ek, Nat.reduceAdd, sepConj_assoc]
  wp_done

set_option maxHeartbeats 800000 in
theorem ek_step_10136_10276_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp st_ptr w592_old : BitVec 64) (q576_old : BitVec 128)
    (w : Words66) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 10136#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx1 : s.readReg64 .x1 = st_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 10276#64) s
      (((st_ptr + 488#64) ↦₁₂₈ w.q60) ∗ ((st_ptr + 512#64) ↦₁₂₈ w.q63) ∗ ((st_ptr + 528#64) ↦₆₄ w.w65) ∗
       words10At (fsp + 8#64) sp.b0 ∗ words10At (fsp + 88#64) sp.b1 ∗ words10At (fsp + 168#64) sp.b2 ∗
       words10At (fsp + 248#64) sp.b3 ∗ words10At (fsp + 328#64) sp.b4 ∗ words10At (fsp + 408#64) sp.b5 ∗
       ((fsp + 488#64) ↦₆₄ sp.w60) ∗ ((fsp + 576#64) ↦₁₂₈ q576_old) ∗ ((fsp + 592#64) ↦₆₄ w592_old) ∗
       ((fsp + 960#64) ↦₁₂₈ sp.q3c0) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((st_ptr + 488#64) ↦₁₂₈ w.q60) ∗ ((st_ptr + 512#64) ↦₁₂₈ w.q63) ∗ ((st_ptr + 528#64) ↦₆₄ w.w65) ∗
          words10At (fsp + 8#64) (ekSpills10136 s sp w.q60).b0 ∗
          words10At (fsp + 88#64) (ekSpills10136 s sp w.q60).b1 ∗
          words10At (fsp + 168#64) (ekSpills10136 s sp w.q60).b2 ∗
          words10At (fsp + 248#64) (ekSpills10136 s sp w.q60).b3 ∗
          words10At (fsp + 328#64) (ekSpills10136 s sp w.q60).b4 ∗
          words10At (fsp + 408#64) (ekSpills10136 s sp w.q60).b5 ∗
          ((fsp + 488#64) ↦₆₄ (ekSpills10136 s sp w.q60).w60) ∗
          ((fsp + 576#64) ↦₁₂₈ w.q63) ∗ ((fsp + 592#64) ↦₆₄ w.w65) ∗
          ((fsp + 960#64) ↦₁₂₈ (ekSpills10136 s sp w.q60).q3c0) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = s.readReg64 .x14 ∧ sm.readReg64 .x1 = sp.b0.w7 ∧
        sm.readReg64 .x2 = sp.b5.w8 ∧ sm.readReg64 .x3 = sp.b1.w1 ∧
        sm.readReg64 .x4 = sp.b2.w2 ∧ sm.readReg64 .x6 = s.readReg64 .x6 ∧
        sm.readReg64 .x7 = sp.b0.w7 ∧ sm.readReg64 .x9 = sp.b5.w4 ∧
        sm.readReg64 .x10 = s.readReg64 .x15 ∧ sm.readReg64 .x12 = sp.b0.w9 ∧
        sm.readReg64 .x13 = sp.w60 ∧ sm.readReg64 .x16 = s.readReg64 .x11 ∧
        sm.readReg64 .x17 = sp.b1.w4 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp.b5.w9 ∧ sm.readReg64 .x23 = s.readReg64 .x23 ∧
        sm.readReg64 .x25 = sp.b0.w4 ∧ sm.readReg64 .x26 = sp.b2.w0 ∧
        sm.readReg64 .x27 = sp.b1.w0 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = sp.b0.w8 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx1
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_simp_pre [words10At, ekSpills10136, pointsTo128, bv_add_lit_add_lit_ek, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words10At, ekSpills10136, pointsTo128, bv_add_lit_add_lit_ek, Nat.reduceAdd, sepConj_assoc]
  wp_done

set_option maxHeartbeats 800000 in
theorem ek_step_10276_18996_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 10276#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 18996#64) s
      (words10At (fsp + 8#64) sp.b0 ∗ words10At (fsp + 88#64) sp.b1 ∗
       words10At (fsp + 168#64) sp.b2 ∗ words10At (fsp + 408#64) sp.b5 ∗
       ((fsp + 488#64) ↦₆₄ sp.w60) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words10At (fsp + 8#64) (ekSpills10276 s sp).b0 ∗
          words10At (fsp + 88#64) (ekSpills10276 s sp).b1 ∗
          words10At (fsp + 168#64) (ekSpills10276 s sp).b2 ∗
          words10At (fsp + 408#64) (ekSpills10276 s sp).b5 ∗
          ((fsp + 488#64) ↦₆₄ (ekSpills10276 s sp).w60) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = s.readReg64 .x0 ∧ sm.readReg64 .x1 = sp.b1.w6 ∧
        sm.readReg64 .x2 = s.readReg64 .x27 ∧ sm.readReg64 .x3 = sp.b0.w3 ∧
        sm.readReg64 .x4 = s.readReg64 .x4 ∧ sm.readReg64 .x5 = sp.b2.w6 ∧
        sm.readReg64 .x6 = s.readReg64 .x6 ∧ sm.readReg64 .x7 = s.readReg64 .x7 ∧
        sm.readReg64 .x8 = sp.b2.w5 ∧ sm.readReg64 .x9 = sp.b2.w3 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧ sm.readReg64 .x11 = s.readReg64 .x30 ∧
        sm.readReg64 .x12 = s.readReg64 .x12 ∧ sm.readReg64 .x13 = s.readReg64 .x23 ∧
        sm.readReg64 .x14 = s.readReg64 .x17 ∧ sm.readReg64 .x15 = sp.b1.w3 ∧
        sm.readReg64 .x16 = s.readReg64 .x3 ∧ sm.readReg64 .x17 = sp.b2.w4 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = sp.b1.w7 ∧
        sm.readReg64 .x21 = sp.b2.w9 ∧ sm.readReg64 .x22 = sp.b2.w1 ∧
        sm.readReg64 .x23 = sp.b1.w8 ∧ sm.readReg64 .x24 = sp.b0.w2 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = sp.b1.w9 ∧ sm.readReg64 .x28 = sp.b1.w5 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.readReg64 .x30 = s.readReg64 .x16 ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_simp_pre [words10At, ekSpills10276, noneCap, bv_add_lit_add_lit_ek, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words10At, ekSpills10276, noneCap, bv_add_lit_add_lit_ek, Nat.reduceAdd, sepConj_assoc]
  wp_done

theorem ek_step_3732_lt_10136_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 3732#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hz : s.pstate.z = false) (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 255#32) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 10136#64) s
      Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x1 = s.readReg64 .x1 ∧ sm.readReg64 .x3 = s.readReg64 .x3 ∧
        sm.readReg64 .x4 = s.readReg64 .x4 ∧ sm.readReg64 .x5 = s.readReg64 .x5 ∧
        sm.readReg64 .x6 = s.readReg64 .x6 ∧ sm.readReg64 .x7 = s.readReg64 .x7 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧ sm.readReg64 .x11 = s.readReg64 .x11 ∧
        sm.readReg64 .x12 = s.readReg64 .x12 ∧ sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x14 = s.readReg64 .x14 ∧ sm.readReg64 .x15 = s.readReg64 .x15 ∧
        sm.readReg64 .x17 = s.readReg64 .x17 ∧ sm.readReg64 .x18 = s.readReg64 .x18 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = s.readReg64 .x30 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  have hcond : ConditionHolds CondCode.EQ s.pstate = false := hz
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps; wp_done

theorem ek_step_3732_eq_9064_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 3732#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hz : s.pstate.z = true) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 9064#64) s
      Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x1 = s.readReg64 .x1 ∧ sm.readReg64 .x3 = s.readReg64 .x3 ∧
        sm.readReg64 .x4 = s.readReg64 .x4 ∧ sm.readReg64 .x5 = s.readReg64 .x5 ∧
        sm.readReg64 .x6 = s.readReg64 .x6 ∧ sm.readReg64 .x7 = s.readReg64 .x7 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧ sm.readReg64 .x11 = s.readReg64 .x11 ∧
        sm.readReg64 .x12 = s.readReg64 .x12 ∧ sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x14 = s.readReg64 .x14 ∧ sm.readReg64 .x15 = s.readReg64 .x15 ∧
        sm.readReg64 .x17 = s.readReg64 .x17 ∧ sm.readReg64 .x18 = s.readReg64 .x18 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧ sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.readReg64 .x30 = s.readReg64 .x30 ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  have hcond : ConditionHolds CondCode.EQ s.pstate = true := hz
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps; wp_done

theorem ek_step_3732_gt_19324_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s : State) (fsp out st_ptr msg_ep u0 u16 : BitVec 64) (u8 : BitVec 8)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 3732#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hz : s.pstate.z = false) (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 1#32)
    (hx0 : s.readReg64 .x0 = st_ptr + 8#64) (hx19 : s.readReg64 .x19 = out) (hx25 : s.readReg64 .x25 = msg_ep) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 19324#64) s
      ((out ↦₆₄ u0) ∗ ((out + 8#64) ↦₈ u8) ∗ ((out + 16#64) ↦₆₄ u16) ∗
       chunkedEkReceivedCt1SampledAt A (st_ptr + 8#64) st ∗ A.pool ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 4#8) ∗ ((out + 16#64) ↦₆₄ msg_ep) ∗
          memRegion (st_ptr + 8#64) 528 ∗ A.pool ∗ stackAt fsp dropStack32 ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  subst hsp hx19 hx25
  have hcond : ConditionHolds CondCode.EQ s.pstate = false := hz
  have hdrop_cl : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 275)
      (withLsCodeLoaded lsmpl (dropChunkedEkReceivedCt1SampledSpec A F)) :=
    drop_chunked_ek_received_ct1_sampled_cl_on hdealloc
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, dropChunkedEkReceivedCt1SampledSpec, chunkedEkReceivedCt1SampledSize,
    noneCap, BitVec.ofNat_eq_ofNat] at hpc hdrop_cl ⊢
  refine CryptoVerification.sepWP_seq_lscl hcl (mid := lsmpl.base 275) ?_
  wp_steps
  refine SepWP.done rfl hrun (fun hcl1 => ?_)
  have hdrop_raw := subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop_cl hcl1
  dsimp only [withMemEq] at hdrop_raw
  wp_call hdrop_raw ⟨st_ptr + 8#64, st⟩
  wp_steps; wp_done

open CryptoVerification.SpqrV1.Top.MessageSerialize in
theorem ek_step_9064_no_ack_10136_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp msg_ptr : BitVec 64) (p : MessagePayload spqrPolyApi) (Frame : SepProp)
    (hno : (match p with
      | .ct1Ack true => true
      | .ekCt1Ack _ => true
      | _ => false) = false)
    (hpc : s.pc = lsmpl.base 332 + 9064#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 10136#64) s
      (messagePayloadAt spqrPolyApi msg_ptr p ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ messagePayloadAt spqrPolyApi msg_ptr p ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x1 = s.readReg64 .x1 ∧ sm.readReg64 .x3 = s.readReg64 .x3 ∧
        sm.readReg64 .x4 = s.readReg64 .x4 ∧ sm.readReg64 .x5 = s.readReg64 .x5 ∧
        sm.readReg64 .x6 = s.readReg64 .x6 ∧ sm.readReg64 .x7 = s.readReg64 .x7 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧ sm.readReg64 .x11 = s.readReg64 .x11 ∧
        sm.readReg64 .x12 = s.readReg64 .x12 ∧ sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x14 = s.readReg64 .x14 ∧ sm.readReg64 .x15 = s.readReg64 .x15 ∧
        sm.readReg64 .x17 = s.readReg64 .x17 ∧ sm.readReg64 .x18 = s.readReg64 .x18 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = s.readReg64 .x30 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx24
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  cases p with
  | ekCt1Ack _ => simp at hno
  | ct1Ack b_ack =>
    cases b_ack with
    | true => simp at hno
    | false =>
      dsimp only [messagePayloadAt, BitVec.ofNat_eq_ofNat]
      wp_simp_pre [sepConj_assoc]; wp_steps; wp_done
  | none | hdr _ | ek _ | ct1 _ | ct2 _ =>
    dsimp only [messagePayloadAt, BitVec.ofNat_eq_ofNat]
    wp_simp_pre [sepConj_assoc]; wp_steps; wp_done

open CryptoVerification.SpqrV1.Top.MessageSerialize in
theorem ek_step_9064_ack_9344_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp msg_ptr : BitVec 64) (p : MessagePayload spqrPolyApi) (Frame : SepProp)
    (hack : (match p with
      | .ct1Ack true => true
      | .ekCt1Ack _ => true
      | _ => false) = true)
    (hpc : s.pc = lsmpl.base 332 + 9064#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 9344#64) s
      (messagePayloadAt spqrPolyApi msg_ptr p ∗ unchunkedSendCt2PlacedRoAt ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ messagePayloadAt spqrPolyApi msg_ptr p ∗ unchunkedSendCt2PlacedRoAt ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x1 = s.readReg64 .x1 ∧ sm.readReg64 .x3 = s.readReg64 .x3 ∧
        sm.readReg64 .x4 = s.readReg64 .x4 ∧ sm.readReg64 .x5 = s.readReg64 .x5 ∧
        sm.readReg64 .x6 = s.readReg64 .x6 ∧ sm.readReg64 .x7 = s.readReg64 .x7 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧ sm.readReg64 .x11 = s.readReg64 .x11 ∧
        sm.readReg64 .x12 = s.readReg64 .x12 ∧ sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x14 = s.readReg64 .x14 ∧ sm.readReg64 .x15 = s.readReg64 .x15 ∧
        sm.readReg64 .x17 = s.readReg64 .x17 ∧ sm.readReg64 .x18 = s.readReg64 .x18 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧ sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = s.readReg64 .x30 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx24
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, unchunkedSendCt2PlacedRoAt, lsLogFilterAddr, lsρ, BitVec.ofNat_eq_ofNat] at hpc ⊢
  cases p with
  | ekCt1Ack _ =>
    dsimp only [messagePayloadAt, BitVec.ofNat_eq_ofNat]
    wp_simp_pre [sepConj_assoc]; wp_steps; wp_done
  | ct1Ack b_ack =>
    cases b_ack with
    | false => simp at hack
    | true =>
      dsimp only [messagePayloadAt, BitVec.ofNat_eq_ofNat]
      wp_simp_pre [sepConj_assoc]; wp_steps; wp_done
  | none | hdr _ | ek _ | ct1 _ | ct2 _ => simp at hack

set_option maxHeartbeats 1600000 in
theorem ek_step_9344_9784_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp msg_ep : BitVec 64) (w u740 : Words66) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 9344#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx3 : s.readReg64 .x3 = w.b0.w3) (hx4 : s.readReg64 .x4 = w.b1.w5)
    (hx5 : s.readReg64 .x5 = w.b4.w4) (hx6 : s.readReg64 .x6 = w.b4.w0)
    (hx7 : s.readReg64 .x7 = w.b3.w1) (hx10 : s.readReg64 .x10 = w.b2.w5)
    (hx11 : s.readReg64 .x11 = w.b4.w1) (hx12 : s.readReg64 .x12 = w.b1.w8)
    (hx13 : s.readReg64 .x13 = w.b4.w3) (hx14 : s.readReg64 .x14 = w.b3.w9)
    (hx15 : s.readReg64 .x15 = w.b3.w5) (hx17 : s.readReg64 .x17 = w.b1.w3)
    (hx18 : s.readReg64 .x18 = w.b2.w7) (hx20 : s.readReg64 .x20 = w.b1.w6)
    (hx21 : s.readReg64 .x21 = w.b0.w7) (hx22 : s.readReg64 .x22 = w.b0.w4)
    (hx23 : s.readReg64 .x23 = w.b5.w2) (hx25 : s.readReg64 .x25 = msg_ep)
    (hx26 : s.readReg64 .x26 = w.b1.w0) (hx27 : s.readReg64 .x27 = w.b1.w2)
    (hx28 : s.readReg64 .x28 = w.w65) (hx30 : s.readReg64 .x30 = w.b2.w3) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 9784#64) s
      (sendEkSpillsAt fsp (ekLoadSpills sp w) ∗
       ((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗
       words66At (fsp + 1856#64) u740 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          sendEkSpillsAt fsp (ekLoadSpills sp w) ∗
          ((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗
          words66At (fsp + 1856#64) w ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 976#64 ∧
        sm.readReg64 .x1 = fsp + 1856#64 ∧ sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx25
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_simp_pre [sendEkSpillsAt, ekLoadSpills, words66At, words10At, pointsTo128, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [sendEkSpillsAt, ekLoadSpills, words66At, words10At, pointsTo128, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc,
    hx3, hx4, hx5, hx6, hx7, hx10, hx11, hx12, hx13, hx14, hx15, hx17, hx18, hx20, hx21, hx22, hx23, hx26, hx27, hx28, hx30]
  wp_done

set_option maxHeartbeats 1600000 in
theorem ek_step_9788_10276_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (w : Words57) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 9788#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 10276#64) s
      (words57At (fsp + 976#64) w ∗ sendEkSpillsAt fsp sp ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words57At (fsp + 976#64) w ∗ sendEkSpillsAt fsp (ekSpills9788 sp w) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = w.b3.w9 ∧ sm.readReg64 .x2 = w.b4.w6 ∧
        sm.readReg64 .x3 = w.w55 ∧ sm.readReg64 .x4 = w.b4.w9 ∧
        sm.readReg64 .x6 = w.b4.w0 ∧ sm.readReg64 .x7 = w.b3.w8 ∧
        sm.readReg64 .x9 = w.b1.w7 ∧ sm.readReg64 .x10 = w.b3.w5 ∧
        sm.readReg64 .x12 = w.b3.w3 ∧ sm.readReg64 .x13 = w.w56 ∧
        sm.readReg64 .x16 = w.b4.w1 ∧ sm.readReg64 .x17 = w.w53 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = w.w54 ∧
        sm.readReg64 .x23 = w.w52 ∧ sm.readReg64 .x25 = w.b3.w2 ∧
        sm.readReg64 .x26 = w.b4.w7 ∧ sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.readReg64 .x30 = w.b3.w4 ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_simp_pre [words57At, sendEkSpillsAt, ekSpills9788, words10At, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words57At, sendEkSpillsAt, ekSpills9788, words10At, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  states_recv_dispatch_ekReceivedCt1Sampled_placed
  ek_step_3392_3560_placed
  ek_step_3560_3732_placed
  ek_step_10136_10276_placed
  ek_step_10276_18996_placed
  ek_step_3732_lt_10136_placed
  ek_step_3732_eq_9064_placed
  ek_step_3732_gt_19324_placed
  ek_step_9064_no_ack_10136_placed
  ek_step_9064_ack_9344_placed
  ek_step_9344_9784_placed
  ek_step_9788_10276_placed
)

end CryptoVerification.SpqrV1.States.Recv
