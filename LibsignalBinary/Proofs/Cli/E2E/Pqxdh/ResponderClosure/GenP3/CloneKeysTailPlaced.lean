/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTail
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Placed Segment 4: `alice_base_key` & `pq_ratchet_state`

Proves `cloneKeysTail_vregs_placed_ok` (`+0x1b20 → +0x1bac`, `genP3J3Placed → genP3J4Placed`)
on `lsProg_518 ext`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Tail Step Helpers (`+0x1b20 .. +0x1bac`) -/

set_option maxHeartbeats 400000 in
private theorem seg5a_nil_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr v23 v26 u_38 u_40 : BitVec 64)
    (f248 f24c u_30 u_34 : BitVec 32)
    (hpc : s.pc = (blkPl_518).base + 0x1b20#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = v23)
    (hx26 : s.readReg64 .x26 = v26) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1b68#64) s
      (((coroPtr + 0x168#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
       ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x30#64) ↦₃₂ u_30) ∗
       ((s.sp + 0x34#64) ↦₃₂ u_34) ∗
       ((s.sp + 0x38#64) ↦₆₄ u_38) ∗
       ((s.sp + 0x40#64) ↦₆₄ u_40))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x168#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
          ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x30#64) ↦₃₂ f248) ∗
          ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x38#64) ↦₆₄ v26) ∗
          ((s.sp + 0x40#64) ↦₆₄ v23)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x24 = 0#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v23 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v26 := hx26
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem seg5a1_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec)
    (s : State) (coroPtr aliceBasePtr aliceBaseLen v23 v26 u_38 u_40 : BitVec 64)
    (f248 f24c u_30 u_34 : BitVec 32)
    (hlen_nz : aliceBaseLen ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x1b20#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = v23)
    (hx26 : s.readReg64 .x26 = v26) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1b48#64) s
      (((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗
       ((coroPtr + 0x168#64) ↦₆₄ aliceBaseLen) ∗
       ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
       ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x30#64) ↦₃₂ u_30) ∗
       ((s.sp + 0x34#64) ↦₃₂ u_34) ∗
       ((s.sp + 0x38#64) ↦₆₄ u_38) ∗
       ((s.sp + 0x40#64) ↦₆₄ u_40))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗
          ((coroPtr + 0x168#64) ↦₆₄ aliceBaseLen) ∗
          ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
          ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x30#64) ↦₃₂ f248) ∗
          ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x38#64) ↦₆₄ v26) ∗
          ((s.sp + 0x40#64) ↦₆₄ v23)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = aliceBaseLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = aliceBasePtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = aliceBaseLen ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim' := closure_shim_placed_ok ext hshim
  have hlen_beq : (aliceBaseLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v23 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v26 := hx26
  wp_steps
  wp_call hshim' ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem seg5a2_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (s : State) (coroPtr aliceBasePtr newAliceBasePtr : BitVec 64)
    (aliceBaseBytes : List (BitVec 8))
    (hnew_nz : newAliceBasePtr ≠ 0#64)
    (hlen_lt : aliceBaseBytes.length < 2 ^ 64)
    (hpc : s.pc = (blkPl_518).base + 0x1b4c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newAliceBasePtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = aliceBasePtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 aliceBaseBytes.length) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1b68#64) s
      ((aliceBasePtr ↦ₛ aliceBaseBytes) ∗
       memRegion newAliceBasePtr aliceBaseBytes.length ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
          (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = newAliceBasePtr ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 aliceBaseBytes.length ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy' := closure_memcpy_4k_placed_ok ext hmemcpy
  have hnew_beq : (newAliceBasePtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  dsimp only [withStack] at hmemcpy' ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newAliceBasePtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = aliceBasePtr := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 aliceBaseBytes.length := hx24
  wp_steps
  wp_call hmemcpy' (newAliceBasePtr, aliceBasePtr, aliceBaseBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem seg5b_nil_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x1b68#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1bac#64) s
      ((coroPtr + 0x180#64) ↦₆₄ 0#64)
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0x180#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = 1#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = 0#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem seg5b1_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec)
    (s : State) (coroPtr bobKyberPtr bobKyberLen : BitVec 64)
    (hlen_nz : bobKyberLen ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x1b68#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1b84#64) s
      (((coroPtr + 0x178#64) ↦₆₄ bobKyberPtr) ∗
       ((coroPtr + 0x180#64) ↦₆₄ bobKyberLen))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x178#64) ↦₆₄ bobKyberPtr) ∗
          ((coroPtr + 0x180#64) ↦₆₄ bobKyberLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = bobKyberLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = bobKyberLen ∧
        s1.readReg64 .x27 = bobKyberPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim' := closure_shim_placed_ok ext hshim
  have hlen_beq : (bobKyberLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hshim' ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem seg5b2_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (s : State) (coroPtr bobKyberPtr newBobKyberPtr rootKeyLen : BitVec 64)
    (bobKyberBytes : List (BitVec 8))
    (hnew_nz : newBobKyberPtr ≠ 0#64)
    (hlen_lt : bobKyberBytes.length < 2 ^ 64)
    (hpc : s.pc = (blkPl_518).base + 0x1b88#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newBobKyberPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 bobKyberBytes.length)
    (hx27 : s.readReg64 .x27 = bobKyberPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1bac#64) s
      (((s.sp + 0x98#64) ↦₆₄ rootKeyLen) ∗
       (bobKyberPtr ↦ₛ bobKyberBytes) ∗
       memRegion newBobKyberPtr bobKyberBytes.length ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ rootKeyLen) ∗
          (bobKyberPtr ↦ₛ bobKyberBytes) ∗
          (newBobKyberPtr ↦ₛ bobKyberBytes) ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = newBobKyberPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 bobKyberBytes.length ∧
        s1.readReg64 .x27 = s.readReg64 .x28 ∧
        s1.readReg64 .x28 = rootKeyLen ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy' := closure_memcpy_4k_placed_ok ext hmemcpy
  have hnew_beq : (newBobKyberPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  dsimp only [withStack] at hmemcpy' ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newBobKyberPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 bobKyberBytes.length := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = bobKyberPtr := hx27
  wp_steps
  wp_call hmemcpy' (newBobKyberPtr, bobKyberPtr, bobKyberBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-! ## 2. Modular Substage Composition for Tail (`+0x1b20 → +0x1bac`) -/

set_option maxHeartbeats 400000 in
private theorem seg_alice_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (s0 s : State) (coroPtr v23 v26 u_38 u_40 : BitVec 64)
    (f248 f24c u_30 u_34 : BitVec 32) (alice : VecGhost)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1b20#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = v23)
    (hx26 : s.readReg64 .x26 = v26) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1b68#64) s
      (A.pool ∗ stackAt s.sp allocHookStack ∗
        vecGhostAt A alice (coroPtr + 0x158#64) ∗
        ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
        ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
        ((s.sp + 0x30#64) ↦₃₂ u_30) ∗
        ((s.sp + 0x34#64) ↦₃₂ u_34) ∗
        ((s.sp + 0x38#64) ↦₆₄ u_38) ∗
        ((s.sp + 0x40#64) ↦₆₄ u_40))
      (fun s1 P_f =>
        ∃ newAlicePtr : BitVec 64,
          (P_f ⊢
            A.pool ∗ stackAt s.sp allocHookStack ∗
            vecGhostAt A alice (coroPtr + 0x158#64) ∗
            vecU8Buf A (BitVec.ofNat 64 alice.bytes.length) newAlicePtr alice.bytes ∗
            ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
            ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
            ((s.sp + 0x30#64) ↦₃₂ f248) ∗
            ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
            ((s.sp + 0x38#64) ↦₆₄ v26) ∗
            ((s.sp + 0x40#64) ↦₆₄ v23)) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x23 = newAlicePtr ∧
          s1.readReg64 .x24 = BitVec.ofNat 64 alice.bytes.length ∧
          s1.readReg64 .x25 = s.readReg64 .x25 ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = s.readReg64 .x28 ∧
          s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have h160 : coroPtr + 0x158#64 + 8#64 = coroPtr + 0x160#64 := by bv_arith
  have h168 : coroPtr + 0x158#64 + 16#64 = coroPtr + 0x168#64 := by bv_arith
  rcases eq_nil_or_length_pos alice.bytes with hnil | hpos
  · rw [vecGhostAt_eq_of_nil A alice (coroPtr + 0x158#64) hnil, h160, h168]
    simp only [sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hcap_lt, hptr⟩ => ?_
    refine ret_sepWP_lscro_frame_placed hcro
      (seg5a_nil_placed_wp ext s coroPtr v23 v26 u_38 u_40 f248 f24c u_30 u_34
        hpc hrun hsp_align hx19 hx23 hx26)
      (by sep_focus)
      fun s1 _ _ hcro1
        ⟨hsp1, htr1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1,
          hvregs1⟩ => ?_
    refine ⟨1#64, ?_, hsp1, htr1.trans htr, hcro1,
      hx19_1, hx22_1, hx23_1, by simpa [hnil] using hx24_1, hx25_1, hx27_1, hx28_1, hx29_1,
      hvregs1⟩
    simp only [hnil, List.length_nil, BitVec.ofNat_eq_ofNat, vecU8Buf_nil_eq A,
      sepConj_emp, emp_sepConj, sepConj_assoc]
    exact entails_pure_3rd ⟨hcap_lt, hptr⟩ (Entails.of_eq (by ac_rfl))
  · rw [vecGhostAt_eq_of_pos A alice (coroPtr + 0x158#64) hpos, h160, h168]
    simp only [sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hlen_lt63 : alice.bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hlen_le hcap_lt
    have hlen_lt64 : alice.bytes.length < 2 ^ 64 := by omega
    have hlen_nz : BitVec.ofNat 64 alice.bytes.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpos hlen_lt64
    refine bind_sepWP_lscro_frame_placed hcro
      (seg5a1_placed_wp ext hshim s coroPtr alice.ptr (BitVec.ofNat 64 alice.bytes.length)
        v23 v26 u_38 u_40 f248 f24c u_30 u_34 hlen_nz hpc hrun hsp_align hx19 hx23 hx26)
      (by sep_focus)
      fun s1 hpc1 hrun1 hcro1
        ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, _, hx21_1, hx22_1, hx24_1, hx25_1,
          hx27_1, hx28_1, hx29_1, hvregs1⟩ => ?_
    have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    refine P3P4.SepWPp.bind_sepWPp_frame_dep
      (alloc_1b48_placed_ok ext halloc hpanic s0 s1 alice.bytes.length emp hpos hlen_lt63
        hcro1 hpc1 hrun1 hsp1_al (htr1.trans htr) hx0_1 hx1_1)
      (by rw [hsp1]; sep_focus)
      fun s2 hpc2 hrun2 ⟨hnew_nz, hsp2, htr2, hcs2, hcro2⟩ => ?_
    set newAlicePtr := s2.readReg64 .x0
    have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
    have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
    have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
    have hx21_2 : s2.readReg64 .x21 = alice.ptr := hcs2.2.2.1.trans hx21_1
    have hx22_2 : s2.readReg64 .x22 = s.readReg64 .x22 := hcs2.2.2.2.1.trans hx22_1
    have hx24_2 : s2.readReg64 .x24 = BitVec.ofNat 64 alice.bytes.length :=
      hcs2.2.2.2.2.2.1.trans hx24_1
    have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hcs2.2.2.2.2.2.2.1.trans hx25_1
    have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
    have hx28_2 : s2.readReg64 .x28 = s.readReg64 .x28 := hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
    have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s :=
      hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    refine ret_sepWP_lscro_frame_placed hcro2
      (seg5a2_placed_wp ext hmemcpy s2 coroPtr alice.ptr newAlicePtr alice.bytes
        hnew_nz hlen_lt64 hpc2 hrun2 hsp2_al rfl hx19_2 hx21_2 hx24_2)
      (by simp only [hsp1, hsp2']; sep_focus)
      fun s3 _ _ hcro3
        ⟨hsp3, htr3, hx19_3, _, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3,
          hvregs3⟩ => ?_
    refine ⟨newAlicePtr, ?_, hsp3.trans hsp2', by rw [htr3, htr2, htr1, htr], hcro3,
      hx19_3, hx22_3.trans hx22_2, hx23_3, hx24_3, hx25_3.trans hx25_2,
      hx27_3.trans hx27_2, hx28_3.trans hx28_2, hx29_3.trans hx29_2,
      hvregs3.trans hvregs2⟩
    rw [vecU8Buf_pos_eq A newAlicePtr alice.bytes hpos hlen_lt63 hnew_nz]
    simp only [sepConj_assoc, hsp1, hsp2']
    exact entails_pure_3rd ⟨hlen_le, hcap_lt, hptr⟩ (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 400000 in
private theorem seg_pq_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (s0 s : State) (coroPtr pqCap pqPtr ctxPtr : BitVec 64)
    (pqBytes : List (BitVec 8))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1b68#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 32#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1bac#64) s
      (A.pool ∗ stackAt s.sp allocHookStack ∗
        vecU8At A (coroPtr + 0x170#64) pqCap pqPtr pqBytes ∗
        ((s.sp + 0x98#64) ↦₆₄ 32#64))
      (fun s1 P_f =>
        ∃ newPqPtr : BitVec 64,
          (P_f ⊢
            A.pool ∗ stackAt s.sp allocHookStack ∗
            vecU8At A (coroPtr + 0x170#64) pqCap pqPtr pqBytes ∗
            vecU8Buf A (BitVec.ofNat 64 pqBytes.length) newPqPtr pqBytes ∗
            ((s.sp + 0x98#64) ↦₆₄ 32#64)) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = newPqPtr ∧
          s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x23 = s.readReg64 .x23 ∧
          s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
          s1.readReg64 .x26 = BitVec.ofNat 64 pqBytes.length ∧
          s1.readReg64 .x27 = ctxPtr ∧ s1.readReg64 .x28 = 32#64 ∧
          s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have h178 : coroPtr + 0x170#64 + 8#64 = coroPtr + 0x178#64 := by bv_arith
  have h180 : coroPtr + 0x170#64 + 16#64 = coroPtr + 0x180#64 := by bv_arith
  rcases eq_nil_or_length_pos pqBytes with hnil | hpos
  · subst hnil
    rw [vecU8At_eq_of_nil A (coroPtr + 0x170#64) pqCap pqPtr, h178, h180]
    simp only [sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hcap_lt, hptr⟩ => ?_
    refine ret_sepWP_lscro_frame_placed hcro
      (seg5b_nil_placed_wp ext s coroPtr hpc hrun hx19)
      (by sep_focus)
      fun s1 _ _ hcro1
        ⟨hsp1, htr1, hx19_1, _, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
          hx27_1, hx28_1, hx29_1, hvregs1⟩ => ?_
    refine ⟨1#64, ?_, hsp1, htr1.trans htr, hcro1,
      hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
      hx27_1.trans hx27, hx28_1.trans hx28, hx29_1, hvregs1⟩
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, vecU8Buf_nil_eq A,
      sepConj_emp, emp_sepConj, sepConj_assoc]
    exact entails_pure_3rd ⟨hcap_lt, hptr⟩ (Entails.of_eq (by ac_rfl))
  · rw [vecU8At_eq_of_pos A (coroPtr + 0x170#64) pqCap pqPtr pqBytes hpos, h178, h180]
    simp only [sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hlen_lt63 : pqBytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hlen_le hcap_lt
    have hlen_lt64 : pqBytes.length < 2 ^ 64 := by omega
    have hlen_nz : BitVec.ofNat 64 pqBytes.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpos hlen_lt64
    refine bind_sepWP_lscro_frame_placed hcro
      (seg5b1_placed_wp ext hshim s coroPtr pqPtr (BitVec.ofNat 64 pqBytes.length)
        hlen_nz hpc hrun hsp_align hx19)
      (by sep_focus)
      fun s1 hpc1 hrun1 hcro1
        ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
          hx27_1, hx28_1, hx29_1, hvregs1⟩ => ?_
    have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    refine P3P4.SepWPp.bind_sepWPp_frame_dep
      (alloc_1b84_placed_ok ext halloc hpanic s0 s1 pqBytes.length emp hpos hlen_lt63
        hcro1 hpc1 hrun1 hsp1_al (htr1.trans htr) hx0_1 hx1_1)
      (by rw [hsp1]; sep_focus)
      fun s2 hpc2 hrun2 ⟨hnew_nz, hsp2, htr2, hcs2, hcro2⟩ => ?_
    set newPqPtr := s2.readReg64 .x0
    have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
    have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
    have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
    have hx22_2 : s2.readReg64 .x22 = s.readReg64 .x22 := hcs2.2.2.2.1.trans hx22_1
    have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hcs2.2.2.2.2.1.trans hx23_1
    have hx24_2 : s2.readReg64 .x24 = s.readReg64 .x24 := hcs2.2.2.2.2.2.1.trans hx24_1
    have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hcs2.2.2.2.2.2.2.1.trans hx25_1
    have hx26_2 : s2.readReg64 .x26 = BitVec.ofNat 64 pqBytes.length :=
      hcs2.2.2.2.2.2.2.2.1.trans hx26_1
    have hx27_2 : s2.readReg64 .x27 = pqPtr := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
    have hx28_2 : s2.readReg64 .x28 = ctxPtr :=
      hcs2.2.2.2.2.2.2.2.2.2.1.trans (hx28_1.trans hx27)
    have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 :=
      hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s :=
      hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    refine ret_sepWP_lscro_frame_placed hcro2
      (seg5b2_placed_wp ext hmemcpy s2 coroPtr pqPtr newPqPtr 32#64 pqBytes
        hnew_nz hlen_lt64 hpc2 hrun2 hsp2_al rfl hx19_2 hx26_2 hx27_2)
      (by simp only [hsp1, hsp2']; sep_focus)
      fun s3 _ _ hcro3
        ⟨hsp3, htr3, hx19_3, _, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3,
          hx27_3, hx28_3, hx29_3, hvregs3⟩ => ?_
    refine ⟨newPqPtr, ?_, hsp3.trans hsp2', by rw [htr3, htr2, htr1, htr], hcro3,
      hx19_3, hx21_3, hx22_3.trans hx22_2, hx23_3.trans hx23_2,
      hx24_3.trans hx24_2, hx25_3.trans hx25_2, hx26_3,
      hx27_3.trans hx28_2, hx28_3, hx29_3.trans hx29_2,
      hvregs3.trans hvregs2⟩
    rw [vecU8Buf_pos_eq A newPqPtr pqBytes hpos hlen_lt63 hnew_nz]
    simp only [sepConj_assoc, hsp1, hsp2']
    exact entails_pure_3rd ⟨hlen_le, hcap_lt, hptr⟩ (Entails.of_eq (by ac_rfl))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1

/-! ## 3. Public Top-Level Placed Segment 4 Theorem (`cloneKeysTail_vregs_placed_ok`) -/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxRecDepth 200000

private theorem sepWPp_done_tail_placed {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = ret) (hrun : s.status = .Running) (hQ : Q s P) :
    SepWPp prog ret s P Q Qp :=
  fun _ hm _ => ⟨s, Steps.refl s, Or.inl ⟨hpc, hrun, P, hm, hQ⟩⟩

set_option maxHeartbeats 800000 in
/-- Placed Segment 4 with `calleeSavedVRegs` (`+0x1b20 → +0x1bac`, `genP3J3Placed → genP3J4Placed`). -/
theorem cloneKeysTail_vregs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (_hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (_hsp_root : rootStack ≤ sp.toNat)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1b20#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1bac#64) s
      (genP3J3Placed A sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3J4Placed A sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
          rest recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  dsimp only [genP3J3Placed, genP3TailSpillScratch]
  refine SepWPp.exists_elim fun w => ?_
  refine SepWPp.pure_elim
    fun ⟨hsp, hx19, hx22, hx23, hx25, hx26, hx27, hx28, hx29, hrc_eq, hsc_rel, hsc_inl⟩ => ?_
  subst hsp
  rw [M3a1.sessionStateAt_tail_eq A coroPtr recG st]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hss_pure => ?_
  obtain ⟨regW0, regW1, hreg_eq, hreg_pts⟩ := exists_unpack32_pair_of_length_8 hss_pure.2.2.2.2.1
  have h24c : coroPtr + 0x248#64 + 4#64 = coroPtr + 0x24c#64 := by bv_arith
  rw [hreg_pts (coroPtr + 0x248#64), h24c]
  let F_rest : SepProp :=
    M3a1.tailSessionRestAt A coroPtr recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFramePlaced A s.sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc
        msgG msg ∗
      vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
      vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
      optSenderChainHeap A w.sender' st.senderChain ∗
      vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
        (w.chains'.zip st.receiverChains) ∗
      OptPendClone A recG.pending w.pendCap' w.pendPtr' ∗
      OptKybClone A recG.kyber w.kybCap' w.kybPtr' ∗
      ((s.sp + 0x8#64) ↦₆₄ w.kybPtr') ∗ ((s.sp + 0x10#64) ↦₆₄ w.d10) ∗
      ((s.sp + 0x18#64) ↦₆₄ w.pendPtr') ∗ ((s.sp + 0x24#64) ↦₃₂ w.w24) ∗
      ((s.sp + 0x28#64) ↦₃₂ w.w28) ∗ ((s.sp + 0x2c#64) ↦₃₂ w.w2c) ∗
      ((s.sp + 0x48#64) ↦₆₄ w.c0) ∗ ((s.sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
      ((s.sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
      ((s.sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
      ((s.sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
      ((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
      genP3SenderInlineWords s.sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5
  refine SepWPp.weaken_pre
    (P' := (∃∗ wt : GenP3TailSpill,
      ((s.sp + 0x30#64) ↦₃₂ wt.u_30) ∗ ((s.sp + 0x34#64) ↦₃₂ wt.u_34) ∗
      ((s.sp + 0x38#64) ↦₆₄ wt.u_38) ∗ ((s.sp + 0x40#64) ↦₆₄ wt.u_40)) ∗
      (vecGhostAt A recG.alice (coroPtr + 0xf8#64 + 0x60#64) ∗
        vecU8At A (coroPtr + 0x170#64) recG.pq.cap recG.pq.ptr st.pqRatchetState ∗
        ((coroPtr + 0x248#64) ↦₃₂ regW0) ∗ ((coroPtr + 0x24c#64) ↦₃₂ regW1) ∗
        ((s.sp + 0x98#64) ↦₆₄ 32#64) ∗
        A.pool ∗ stackAt s.sp chainCloneStack ∗ F_rest))
    (by
      have h158 : coroPtr + 0xf8#64 + 0x60#64 = coroPtr + 0x158#64 := by bv_arith
      rw [h158]; dsimp only [F_rest]; exact Entails.of_eq (by ac_rfl)) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun wt => ?_
  have h158 : coroPtr + 0xf8#64 + 0x60#64 = coroPtr + 0x158#64 := by bv_arith
  rw [h158, stackAt_chainClone_eq_alloc s.sp]
  simp only [sepConj_assoc]
  refine SepWPp.bind_oom_frame
    (M3a1.seg_alice_placed_ok ext hpanic hshim halloc hmemcpy s0 s coroPtr
      (BitVec.ofNat 64 st.receiverChains.length) w.kybCap' wt.u_38 wt.u_40
      regW0 regW1 wt.u_30 wt.u_34 recG.alice
      hcro hpc hrun hsp_align htr hx19 hx23 hx26)
    (by sep_focus)
    fun s1 _ hpc1 hrun1
      ⟨newAlicePtr, hent1, hsp1, htr1, hcro1, hx19_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx27_1, hx28_1, hx29_1, hvregs1⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hent1) ?_
  simp only [sepConj_assoc]
  have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine SepWPp.bind_oom_frame
    (M3a1.seg_pq_placed_ok ext hpanic hshim halloc hmemcpy s0 s1 coroPtr recG.pq.cap recG.pq.ptr
      ctxPtr st.pqRatchetState hcro1 hpc1 hrun1 hsp1_al htr1 hx19_1
      (hx27_1.trans hx27) (hx28_1.trans hx28))
    (by simp only [hsp1]; sep_focus)
    fun s2 _ hpc2 hrun2
      ⟨newPqPtr, hent2, hsp2, htr2, hcro2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2,
        hx26_2, hx27_2, hx28_2, hx29_2, hvregs2⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hent2) ?_
  refine sepWPp_done_tail_placed hpc2 hrun2 ⟨?_, htr2, hcro2, hvregs2.trans hvregs1⟩
  dsimp only [genP3J4Placed, F_rest]
  refine Entails.sepExists_right
    { toGenP3J3Witness := w
      newAlicePtr := newAlicePtr
      newPqPtr := newPqPtr
      regW0 := regW0
      regW1 := regW1 } ?_
  refine Entails.pure_right
    ⟨hsp2.trans hsp1, hx19_2, hx21_2,
     hx22_2.trans (hx22_1.trans hx22),
     hx23_2.trans hx23_1,
     hx24_2.trans hx24_1,
     hx25_2.trans (hx25_1.trans hx25),
     hx26_2, hx27_2, hx28_2,
     hx29_2.trans (hx29_1.trans hx29),
     hreg_eq, hrc_eq, hsc_rel, hsc_inl⟩ ?_
  rw [M3a1.sessionStateAt_tail_eq A coroPtr recG st, hreg_pts (coroPtr + 0x248#64), h24c,
      stackAt_chainClone_eq_alloc s.sp]
  simp only [hsp1, sepConj_assoc]
  exact Entails.pure_right hss_pure (Entails.of_eq (by ac_rfl))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
