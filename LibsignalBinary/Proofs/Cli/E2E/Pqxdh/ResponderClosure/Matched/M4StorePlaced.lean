/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4SaveIdPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StoreStepsPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveId
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP4
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsStoreSession
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsStoreSessionProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Unwind

/-!
# Relocatable Matched-Session Substage P4.4 (`store_session`, `+0x3cc → x30`)

Relocatable `[LibsignalPlacement]` counterpart of `Matched.M4Store` on Block `518`
(`lsProg_518 (Rust.withPanics ext)`, `(blkPl_518).base = lsmpl.base 518`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.E2E.Pqxdh.ResponderClosure.extractLsb_0_32_append_32
  CryptoVerification.E2E.Pqxdh.ResponderClosure.extractLsb_32_32_append_32
  CryptoVerification.E2E.Pqxdh.ResponderClosure.setWidth_32_append_32
  CryptoVerification.E2E.Pqxdh.ResponderClosure.append_1_32_getElem_zero

/-! ## Block-`518` Substage P4.4 basic-block segments -/

set_option maxHeartbeats 800000 in
theorem p4_seg4a_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State)
    (coroPtr remoteAddrPtr sessionStorePtr sessionStoreVt storeSessionShimAddr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x3cc#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext)) storeSessionShimAddr s
      (((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
       ((coroPtr + 0x90#64) ↦₆₄ sessionStoreVt) ∗
       ((sessionStoreVt + 0x20#64) ↦₆₄ᵣ storeSessionShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
          ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
          ((coroPtr + 0x90#64) ↦₆₄ sessionStoreVt) ∗
          ((sessionStoreVt + 0x20#64) ↦₆₄ᵣ storeSessionShimAddr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = sessionStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x2 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x3e0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p4_seg4b_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr storeSessionFutPtr storeSessionFutVt storeSessionPollAddr
    u_2c8 u_2d0 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x3e0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = storeSessionFutPtr)
    (hx1 : s.readReg64 .x1 = storeSessionFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext)) storeSessionPollAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ u_2c8) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ u_2d0) ∗
       ((storeSessionFutVt + 0x18#64) ↦₆₄ᵣ storeSessionPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ storeSessionFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ storeSessionFutVt) ∗
          ((storeSessionFutVt + 0x18#64) ↦₆₄ᵣ storeSessionPollAddr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = storeSessionFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x3f8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = storeSessionFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = storeSessionFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p4_seg4c_gen_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr storeSessionFutPtr storeSessionFutVt storeSessionDropAddr w0
    o2 o3 o4 o5 u_340 u_348 u_350 u_358 : BitVec 64)
    (o1 o6 u_360 : BitVec 32)
    (hw0_ne_pend : w0 + 3#64 ≠ 0#64)
    (hdrop_nz : storeSessionDropAddr ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x3f8#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (lsProg_518 (Rust.withPanics ext)) storeSessionDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ storeSessionFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ storeSessionFutVt) ∗
       (storeSessionFutVt ↦₆₄ᵣ storeSessionDropAddr) ∗
       stagingCellsAt (s.sp + 0x340#64) u_340 u_348 u_350 u_358 u_360 ∗
       pollCellsAt (s.sp + 0x3e0#64) w0 o1 o2 o3 o4 o5 o6)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ storeSessionFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ storeSessionFutVt) ∗
          (storeSessionFutVt ↦₆₄ᵣ storeSessionDropAddr) ∗
          stagingCellsAt (s.sp + 0x340#64) o2 o3 o4 o5 o6 ∗
          pollCellsAt (s.sp + 0x3e0#64) w0 o1 o2 o3 o4 o5 o6) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = storeSessionFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = storeSessionFutPtr ∧
        s1.readReg64 .x22 = o1.zeroExtend 64 ∧
        s1.readReg64 .x23 = storeSessionFutVt ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x444#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hw0_beq : (w0 + 3#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_pend
  have hdrop_beq : (storeSessionDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  unfold stagingCellsAt pollCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by simp only [BitVec.add_zero]), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p4_seg4d_ok_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr storeSessionFutPtr storeSessionFutVt futSize futAlign
    curStateWord0 ptextMid0 ptextMid1 u_370 u_378 : BitVec 64)
    (ptextHead ptextTail u_380 : BitVec 32)
    (hsize_nz : futSize ≠ 0#64)
    (hcur_ne : curStateWord0 + 1#64 ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x444#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = storeSessionFutPtr)
    (hx23 : s.readReg64 .x23 = storeSessionFutVt)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 512) s
      (((coroPtr + 0xf8#64) ↦₆₄ curStateWord0) ∗
       ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
       ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
       ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
       ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
       ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       A.live storeSessionFutPtr futSize.toNat futAlign.toNat ∗
       memRegion storeSessionFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf8#64) ↦₆₄ curStateWord0) ∗
          ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
          ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
          ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
          ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
          ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₃₂ ptextTail) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = ptextHead.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x48c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hcur_beq : (curStateWord0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcur_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = storeSessionFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = storeSessionFutVt := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  wp_steps
  wp_call hdealloc (storeSessionFutPtr, futSize.toNat, futAlign.toNat)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p4_seg4d_err_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr storeSessionFutPtr storeSessionFutVt futSize futAlign w0 : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hw0_ne_ok : w0 + 2#64 ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x444#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = storeSessionFutPtr)
    (hx23 : s.readReg64 .x23 = storeSessionFutVt)
    (hx28 : s.readReg64 .x28 = w0) :
    SepWP (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x550#64) s
      (((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live storeSessionFutPtr futSize.toNat futAlign.toNat ∗
       memRegion storeSessionFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x8 = s.sp + 0x340#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hw0_beq : (w0 + 2#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_ok
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = storeSessionFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = storeSessionFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = w0 := hx28
  wp_steps
  wp_call hdealloc (storeSessionFutPtr, futSize.toNat, futAlign.toNat)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p4_seg4e_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr prevStatesPtr
    ptextMid0 ptextMid1 w_380 w_388
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (ptextHead w_390 u_ret08 u_ret2c : BitVec 32)
    (b_2c0 : BitVec 8)
    (hpc : s.pc = (blkPl_518).base + 0x48c#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = ptextHead.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext)) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗
       ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗
       ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗
       ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗
       ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
       ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
       ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
       ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
       ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
       ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
       ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((outPtr + 0x8#64) ↦₃₂ ptextHead) ∗
          ((outPtr + 0xc#64) ↦₆₄ ptextMid0) ∗
          ((outPtr + 0x14#64) ↦₆₄ ptextMid1) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
          ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
          ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
          ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
          ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
          ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
          ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
          ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = ptextHead.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-! ## Placed vtable and framing helpers for `store_session` -/

def storeSessionVtablesPlacedAt {A : RustAlloc} (kit : SessionStoreSpec A 0#64) : SepProp :=
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
  ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
  ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))

theorem storeSessionVtablesPlacedAt_intro [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} (vt : SessionOnlyVtablesPlacedOk kit)
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ storeSessionVtablesPlacedAt kit ∗ P := by
  unfold storeSessionVtablesPlacedAt
  simp only [sepConj_assoc]
  exact vt.storeSlot hro (vt.storeFutDrop hro
    (vt.storeFutSize hro (vt.storeFutAlign hro (vt.storeFutPoll hro hP))))

private theorem p4_fold_sret_ok_m4_placed {A : RustAlloc} (outPtr ptCap ptPtr w_24 : BitVec 64)
    (u_384 w_2c : BitVec 32) (pt : List (BitVec 8))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64) :
    (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
    ((outPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
    ((outPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
    ((outPtr + 0x14#64) ↦₆₄
      ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
    ((outPtr + 0x1c#64) ↦₆₄ (u_384 ++ (BitVec.ofNat 64 pt.length).extractLsb' 32 32)) ∗
    ((outPtr + 0x24#64) ↦₆₄ w_24) ∗
    ((outPtr + 0x2c#64) ↦₃₂ w_2c) ∗
    (ptPtr ↦ₛ pt) ∗
    (if ptCap = 0#64 then emp
     else A.live ptPtr ptCap.toNat 1 ∗
       memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ⊢
    vecResultAt A outPtr (.ok pt) := by
  rw [pointsTo32_pair_out1c']
  have hreplace :
      ∀ {A B R P Q : SepProp},
        (A ⊢ B) → P = A ∗ R → B ∗ R = Q → (P ⊢ Q) := by
    intro A B R P Q hab hp hq
    rw [hp, ← hq]
    exact sepConj_mono_left hab
  exact Entails.trans
    (hreplace (memRegion16_out20_fold' outPtr w_24 u_384 w_2c) (by sep_focus) (by ac_rfl))
    (p4_fold_decResultAt_ok A outPtr ptCap ptPtr pt hpt_le hcap_lt hptr_nz)

private theorem sp370_words_entails_memRegion36_m4_placed (sp v0 v1 v2 v3 : BitVec 64)
    (v4 : BitVec 32) :
    ((sp + 0x370#64) ↦₆₄ v0) ∗ ((sp + 0x378#64) ↦₆₄ v1) ∗ ((sp + 0x380#64) ↦₆₄ v2) ∗
    ((sp + 0x388#64) ↦₆₄ v3) ∗ ((sp + 0x390#64) ↦₃₂ v4) ⊢ memRegion (sp + 0x370#64) 36 := by
  have h := stagingCellsAt_entails_memRegion36 (sp + 0x370#64) v0 v1 v2 v3 v4
  unfold stagingCellsAt at h
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

private theorem coro2c8_16_split_eq_m4_placed (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x2c8#64) 16 =
      ∃∗ u_2d0 : BitVec 64, ∃∗ u_2c8 : BitVec 64,
        ((coroPtr + 0x2c8#64) ↦₆₄ u_2c8) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ u_2d0) := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x2c8#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x2d0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (coroPtr + 0x2c8#64),
      ProofLib.memRegion_eight (coroPtr + 0x2d0#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem coro2c8_16_fold_m4_placed (coroPtr v0 v1 : BitVec 64) :
    ((coroPtr + 0x2c8#64) ↦₆₄ v0) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ v1) ⊢
      memRegion (coroPtr + 0x2c8#64) 16 := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x2c8#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x2d0#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

private theorem prevSessionsEmptyAt_sessionRecordAt_fold_placed (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hExtra : SessionExtraRel G ss) :
    prevSessionsEmptyAt A coroPtr g ∗ sessionStateAt A (coroPtr + 0xf8#64) G ss.state ⊢
      sessionRecordAt A (coroPtr + 0xe0#64) ⟨g.prevCap, g.prevPtr, some G⟩ ⟨some ss⟩ := by
  unfold sessionRecordAt prevSessionsEmptyAt sessionStateReprAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_right hExtra (Entails.refl _))

private theorem prevSessionsEmptyAt_sessionRecordAt_unfold_placed (A : RustAlloc)
    (coroPtr : BitVec 64) (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8))) :
    sessionRecordAt A (coroPtr + 0xe0#64) ⟨g.prevCap, g.prevPtr, some G⟩ ⟨some ss⟩ ⊢
      prevSessionsEmptyAt A coroPtr g ∗ sessionStateAt A (coroPtr + 0xf8#64) G ss.state := by
  unfold sessionRecordAt prevSessionsEmptyAt sessionStateReprAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_left fun _ => Entails.refl _)

/-! ## General-`prevSessionsEmptyAt` `Ok` epilogue (`+0x444 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
theorem stageP4_storeSession_ok_tail_prevEmpty_vregs_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State)
    (coroPtr boxPtr outPtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (g : RecordGhost) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : storeSessionCallStack kit ≤ 2 ^ 64)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x444#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = boxPtr)
    (hx23 : s.readReg64 .x23 = 0#64 + kit.storeFutVtOff)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) G st ∗
       ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       (ptPtr ↦ₛ pt) ∗
       (if ptCap = 0#64 then emp
        else A.live ptPtr ptCap.toNat 1 ∗
          memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
       ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live boxPtr kit.storeBoxSize 8 ∗
       memRegion boxPtr kit.storeBoxSize ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion outPtr 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp (storeSessionCallStack kit))
      (fun sf P_f =>
        Steps (lsProg_518 (Rust.withPanics ext)) s sf ∧
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          memRegion (coroPtr + 0x280#64) 24 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          vecResultAt A outPtr (.ok pt) ∗
          ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
          ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp (storeSessionCallStack kit)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  refine SepWPp.with_steps ?_
  have hbox_eq : kit.storeBoxSize = (BitVec.ofNat 64 kit.storeBoxSize).toNat :=
    (Nat.mod_eq_of_lt kit.storeBoxSize_lt).symm
  have hsp_al : s.spAligned = true := hsp_align
  let ptLen := BitVec.ofNat 64 pt.length
  have hpt_coro :
      ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗ ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
      ((coroPtr + 0x290#64) ↦₆₄ ptLen) =
      ((coroPtr + 0x280#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((coroPtr + 0x284#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((coroPtr + 0x28c#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((coroPtr + 0x294#64) ↦₃₂ ptLen.extractLsb' 32 32) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words3_eq_head_mid_tail (coroPtr + 0x280#64) ptCap ptPtr ptLen
  have hbox_sz :
      A.live boxPtr kit.storeBoxSize 8 ∗ memRegion boxPtr kit.storeBoxSize =
      A.live boxPtr (BitVec.ofNat 64 kit.storeBoxSize).toNat (8#64 : BitVec 64).toNat ∗
        memRegion boxPtr (BitVec.ofNat 64 kit.storeBoxSize).toNat := by
    rw [← hbox_eq]; rfl
  refine P3P4.SepWPp.weaken_frame (p4_sessionStateAt_expose_cap_ne A (coroPtr + 0xf8#64) G st)
    (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hcap_ne => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpt_coro) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hbox_sz) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq' s.sp)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w_390 => SepWPp.exists_elim fun w_388 =>
    SepWPp.exists_elim fun u_384 => SepWPp.exists_elim fun u_380 =>
    SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  have hstep1 := p4_seg4d_ok_placed_wp ext hdealloc s coroPtr boxPtr
    (0#64 + kit.storeFutVtOff) (BitVec.ofNat 64 kit.storeBoxSize) 8#64
    G.localIk.cap
    (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
    (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
    u_370 u_378 (ptCap.extractLsb' 0 32) (ptLen.extractLsb' 32 32) u_380
    kit.storeBoxSize_ne_zero hcap_ne hpc hrun hsp_al hx19 hx21 hx23 hx24 hx28
  refine bind_sepWP_lscro_frame hcro hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, _, _, hlr1, hvregs1_0⟩
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (p4_sessionStateAt_expose_cap A (coroPtr + 0xf8#64) G st).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpt_coro.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (coro280_words3_entails_memRegion24 coroPtr ptCap ptPtr ptLen) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_dropSS3 kit s.sp hsp_ub)) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  simp only [sepConj_assoc]
  refine call_lscro_nopanic
    (x := (⟨coroPtr + 0xf8#64, G, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (coroPtr + 0xf8#64) G st ∗ A.pool ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
    hcro1 (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hDropSS3)
    hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
    hx0_1 (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_dropSS3 kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (pointsTo32_pair_sp380' s.sp (ptLen.extractLsb' 32 32) u_384))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion48_eq_exists_pollCells outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2] using hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = (ptCap.extractLsb' 0 32).zeroExtend 64 :=
    hx22_cs2.trans hx22_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun o6_u => SepWPp.exists_elim fun o5_u =>
    SepWPp.exists_elim fun o3_u => SepWPp.exists_elim fun o2_u =>
    SepWPp.exists_elim fun o1_u => SepWPp.exists_elim fun o0_u =>
    SepWPp.exists_elim fun w0_u => ?_
  refine P3P4.SepWPp.weaken_frame (prevSessionsEmptyAt_unpack A coroPtr g) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  by_cases hprev_z : g.prevCap = 0#64
  · simp only [hprev_z, ↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
    have hstep3 := p4_seg4e_placed_wp ext s2 coroPtr outPtr g.prevPtr
      (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
      (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
      (u_384 ++ ptLen.extractLsb' 32 32) w_388
      w0_u o1_u o2_u o3_u o5_u
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (ptCap.extractLsb' 0 32) w_390 o0_u o6_u b_2c0
      hpc2 hrun2 hsp2_al hx19_2 hx22_2 hx25_2 hx26_2
    rw [hsp2] at hstep3
    unfold pollCellsAt
    simp only [BitVec.add_zero, sepConj_assoc] at hstep3 ⊢
    refine bind_sepWP_lscro_frame hcro2 hstep3 (by sep_focus)
      fun sf hpcf hrunf hcrof hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f,
      hx27f, hx28f, hx29f, _, hvregsf_2⟩
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (p4_fold_sret_ok_m4_placed outPtr ptCap ptPtr w_388 u_384 w_390 pt hpt_le hcap_lt hptr_nz)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (sp370_words_entails_memRegion36_m4_placed s.sp
        (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
        (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
        (u_384 ++ ptLen.extractLsb' 32 32) w_388 w_390)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64) (by sep_focus) ?_
    refine SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), ?_⟩
    refine ⟨hspf, by rw [htrf, htr2_1, htr1], ?_,
      hvregsf_2.trans (hvregs_cs2.trans (hvregs1_0.trans hvregs)), hcrof⟩
    exact ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, trivial⟩
  · simp only [hprev_z, ↓reduceIte, sepConj_assoc]
    have hstep3 := p4_seg4e_dealloc_placed_wp ext hdealloc s2 coroPtr outPtr g.prevCap g.prevPtr
      (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
      (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
      (u_384 ++ ptLen.extractLsb' 32 32) w_388
      w0_u o1_u o2_u o3_u o5_u
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (ptCap.extractLsb' 0 32) w_390 o0_u o6_u b_2c0
      hprev_z hprev_lt hpc2 hrun2 hsp2_al hx19_2 hx22_2 hx25_2 hx26_2
    rw [hsp2] at hstep3
    unfold pollCellsAt
    simp only [BitVec.add_zero, sepConj_assoc] at hstep3 ⊢
    refine bind_sepWP_lscro_frame hcro2 hstep3 (by sep_focus)
      fun sf hpcf hrunf hcrof hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f,
      hx27f, hx28f, hx29f, _, hvregsf_2⟩
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (p4_fold_sret_ok_m4_placed outPtr ptCap ptPtr w_388 u_384 w_390 pt hpt_le hcap_lt hptr_nz)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (sp370_words_entails_memRegion36_m4_placed s.sp
        (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
        (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
        (u_384 ++ ptLen.extractLsb' 32 32) w_388 w_390)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64) (by sep_focus) ?_
    refine SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), ?_⟩
    refine ⟨hspf, by rw [htrf, htr2_1, htr1], ?_,
      hvregsf_2.trans (hvregs_cs2.trans (hvregs1_0.trans hvregs)), hcrof⟩
    exact ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, trivial⟩

/-! ## Spatial bundles and matched-session Substage P4.4 -/

/-- Shared resources across entry, `Ok(())` exit, and `Err(())` exit of matched `P4.4`
under `[LibsignalPlacement]`. -/
def stageP4MatchedStoreSharedPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64)
    (s0 s : State)
    (coroPtr remoteAddrPtr sessionStorePtr : BitVec 64)
    (peer : AddrGhost) : SepProp :=
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
  ((coroPtr + 0x90#64) ↦₆₄ kit.ss_vt) ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  memRegion (s.sp + 0x340#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  protocolAddressAt A peer remoteAddrPtr ∗
  A.pool ∗
  stackAt s.sp (storeSessionCallStack kit)

def stageP4MatchedStorePrePlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64)
    (s0 s : State)
    (coroPtr outPtr remoteAddrPtr sessionStorePtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (sst0 : kit.StoreState)
    (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8))) : SepProp :=
  stageP4MatchedStoreSharedPlaced kit s0 s coroPtr remoteAddrPtr sessionStorePtr peer ∗
  prevSessionsEmptyAt A coroPtr g ∗
  sessionStateAt A (coroPtr + 0xf8#64) G ss.state ∗
  ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
  ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
  ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  kit.storeAt sessionStorePtr sst0

def stageP4MatchedStoreOkPostPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64)
    (s0 s : State)
    (coroPtr outPtr remoteAddrPtr sessionStorePtr : BitVec 64)
    (pt : List (BitVec 8))
    (peer : AddrGhost) (sst0 : kit.StoreState) (ss : Session (List (BitVec 8))) : SepProp :=
  stageP4MatchedStoreSharedPlaced kit s0 s coroPtr remoteAddrPtr sessionStorePtr peer ∗
  storeSessionVtablesPlacedAt kit ∗
  vecResultAt A outPtr (.ok pt) ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  kit.storeAt sessionStorePtr (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ()))

def stageP4MatchedStoreErrPostPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64)
    (s0 s : State)
    (coroPtr outPtr remoteAddrPtr sessionStorePtr : BitVec 64)
    (peer : AddrGhost) (sst0 : kit.StoreState) (ss : Session (List (BitVec 8))) : SepProp :=
  stageP4MatchedStoreSharedPlaced kit s0 s coroPtr remoteAddrPtr sessionStorePtr peer ∗
  storeSessionVtablesPlacedAt kit ∗
  storePollPlacedOutAt outPtr (.error ()) ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  kit.storeAt sessionStorePtr (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ()))

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` matched-session Substage P4.4 (`store_session`,
`(blkPl_518).base + 0x3cc → s0.readReg64 .x30`) on general `prevSessionsEmptyAt A coroPtr g`. -/
theorem stageP4_matched_storeSession_vregs_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hkit : SessionOnlyKitPlacedOkSE kit Scope encRecord (Rust.withPanics ext))
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    {Qfs : Prop}
    (s0 s : State)
    (coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (sst0 : kit.StoreState)
    (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ok : kit.addrOk peer.val)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : storeSessionCallStack kit ≤ 2 ^ 64)
    (hfs : FsAt kit.envOk Qfs (lsProg_518 (Rust.withPanics ext)) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x3cc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (sf : State) (Pf : SepProp),
      Steps (lsProg_518 (Rust.withPanics ext)) s sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4MatchedStoreOkPostPlaced kit s0 s coroPtr outPtr remoteAddrPtr sessionStorePtr
        pt peer sst0 ss ∗ F) →
      Q sf Pf)
    (hErr : ∀ (sf : State) (Pf : SepProp),
      Steps (lsProg_518 (Rust.withPanics ext)) s sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4MatchedStoreErrPostPlaced kit s0 s coroPtr outPtr remoteAddrPtr sessionStorePtr
        peer sst0 ss ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stageP4MatchedStorePrePlaced kit s0 s coroPtr outPtr remoteAddrPtr sessionStorePtr
        ptCap ptPtr b_2c0 pt peer sst0 g G ss ∗ F)
      Q (PanicOomProp s0) := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  have hbox_eq : kit.storeBoxSize = (BitVec.ofNat 64 kit.storeBoxSize).toNat :=
    (Nat.mod_eq_of_lt kit.storeBoxSize_lt).symm
  have hsp_al : s.spAligned = true := hsp_align
  refine SepWPp.intro_ro (R_ro := storeSessionVtablesPlacedAt kit)
    (fun hm => storeSessionVtablesPlacedAt_intro hsVt hcro.2 hm) ?_
  unfold stageP4MatchedStorePrePlaced stageP4MatchedStoreSharedPlaced storeSessionVtablesPlacedAt
  simp only [sepConj_assoc]
  have h4a := p4_seg4a_placed_wp ext s coroPtr remoteAddrPtr sessionStorePtr kit.ss_vt
    (0#64 + kit.storeShimOff) hpc hrun hx19
  refine SepWPp.bind_sepWP_frame_steps h4a (by sep_focus)
    fun s1 P1 hpc1 hrun1 hst1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1,
      hx24_1, hx25_1, hx26_1, hx27_1, _, _, hlr1, hvregs1_0⟩ => ?_
  refine P3P4.SepWPp.weaken_frame hP1 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_shim kit s.sp hsp_ub))
    (by sep_focus) ?_
  have hvregs1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hvregs1_0.trans hvregs
  have hcro1 := hcro.of_keepsFrozen hst1.keepsFrozen
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_al
  have htr_pfx1 : s0.trace <+: s1.trace := htr1 ▸ htr_pfx
  refine call_rocl_frame
    (x := ({ self := sessionStorePtr, addrA := remoteAddrPtr,
             recA := coroPtr + 0xe0#64 } : StoreShimCall))
    (φ := s1.readReg64 .x0 = sessionStorePtr ∧ s1.readReg64 .x1 = remoteAddrPtr ∧
          s1.readReg64 .x2 = coroPtr + 0xe0#64)
    (T := A.pool ∗ stackAt s.sp kit.storeShimStack)
    hcro1 htr_pfx1 (hkit.storeShim (by decide)) hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [kitStoreShimSpec]; rw [hsp1]; exact Entails.of_eq (by ac_rfl))
    ⟨hx0_1, hx1_1, hx2_1⟩ (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 hst2 => ?_)
  dsimp only [kitStoreShimSpec]
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_2, _, _, htr2_1⟩ => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_shim kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (coro2c8_16_split_eq_m4_placed coroPtr))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_2d0 => SepWPp.exists_elim fun u_2c8 => ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2, _, _, hvregs_cs2⟩
  have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs_cs2.trans hvregs1
  let boxPtr := s2.readReg64 .x0
  have h4b := p4_seg4b_placed_wp ext s2 coroPtr ctxPtr boxPtr
    (0#64 + kit.storeFutVtOff) (0#64 + kit.storePollOff) u_2c8 u_2d0
    hpc2 hrun2 rfl hx1_2 (hx19_cs2.trans hx19_1) (hx27_cs2.trans (hx27_1.trans hx27))
  refine SepWPp.bind_sepWP_frame_steps h4b (by sep_focus)
    fun s3 P3 hpc3 hrun3 hst3 ⟨hP3, hsp3_2, htr3_2, hx0_3, _, hx8_3, hx19_3,
      hx24_3, hx25_3, hx26_3, _, _, _, hlr3, hvregs3_2⟩ => ?_
  refine P3P4.SepWPp.weaken_frame hP3 (by sep_focus) ?_
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3_2.trans hvregs2
  have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
  have hcro3 := hcro2.of_keepsFrozen hst3.keepsFrozen
  have hsp3_al : s3.spAligned = true := by simpa [State.spAligned, hsp3] using hsp_al
  have hst_to3 : Steps (lsProg_518 (Rust.withPanics ext)) s s3 :=
    hst1.trans (hst2.trans hst3)
  have htr_to3 : s3.trace = s.trace := by rw [htr3_2, htr2_1, htr1]
  have htr_pfx3 : s0.trace <+: s3.trace := htr_to3 ▸ htr_pfx
  have henv3 : kit.envOk s3.fs.files := (hfs.of_steps_nil hst_to3 htr_to3).envOk_here
  have hrec_fold := prevSessionsEmptyAt_sessionRecordAt_fold_placed A coroPtr g G ss hExtra
  have hrec_unfold := prevSessionsEmptyAt_sessionRecordAt_unfold_placed A coroPtr g G ss
  refine P3P4.SepWPp.weaken_frame hrec_fold (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_poll kit s.sp hsp_ub))
    (by sep_focus) ?_
  let pollCall : StorePollCall :=
    { fut := boxPtr
      out := s.sp + 0x3e0#64
      call := { addrA := remoteAddrPtr, addr := peer, recA := coroPtr + 0xe0#64,
                g := ⟨g.prevCap, g.prevPtr, some G⟩, record := ⟨some ss⟩ } }
  refine call_rocl_frame
    (spec := kitStorePollPlacedSpecE kit encRecord)
    (x := (pollCall, sessionStorePtr, sst0))
    (φ := kit.envOk s3.fs.files ∧
          s3.readReg64 .x0 = boxPtr ∧ s3.readReg64 .x8 = s.sp + 0x3e0#64 ∧
          kit.RecOk ⟨some ss⟩ ∧ kit.addrOk peer.val)
    (T := kit.storeBoxAt boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 0#8 ∗
          kit.storeAt sessionStorePtr sst0 ∗ memRegion (s.sp + 0x3e0#64) 48 ∗
          protocolAddressAt A peer remoteAddrPtr ∗
          sessionRecordAt A (coroPtr + 0xe0#64) ⟨g.prevCap, g.prevPtr, some G⟩ ⟨some ss⟩ ∗
          A.pool ∗ stackAt s.sp kit.storePollStack)
    hcro3 htr_pfx3 (hkit.storePoll (by decide)) hpc3 hrun3 hsp3_al hlr3
    (by
      dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec, pollCall]
      rw [hsp3]
      refine Entails.pure_left fun ⟨henv, hx0', hx8', hrok, haok⟩ => ?_
      refine Entails.pure_right henv (Entails.pure_right ⟨hx0', hx8', hrok, haok⟩ ?_)
      exact Entails.of_eq (by ac_rfl))
    ⟨henv3, hx0_3, by rw [hx8_3, hsp2], hrec_ok, haddr_ok⟩ (by sep_focus)
    (hnext := fun s4 hpc4 hrun4 hsp4_3 hsp4_al hcs4 hcro4 hst4 => ?_)
  dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec, pollCall]
  rw [hsp3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.pure_elim fun ⟨hrel, htr4_3⟩ => ?_
  refine P3P4.SepWPp.weaken_frame hrec_unfold (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_poll kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x340#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_360s => SepWPp.exists_elim fun u_358s =>
    SepWPp.exists_elim fun u_350s => SepWPp.exists_elim fun u_348s =>
    SepWPp.exists_elim fun u_340s => ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  rcases hcs4 with ⟨hx19_cs4, _, _, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, hvregs_cs4⟩
  have hvregs4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hvregs_cs4.trans hvregs3
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx24_4 : s4.readReg64 .x24 = s4.sp + 0x370#64 := by
    rw [hx24_cs4, hx24_3, hx24_cs2, hx24_1, hx24, hsp4]
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by
    rw [hx25_cs4, hx25_3, hx25_cs2, hx25_1, hx25, hsp4]
  have hx26_4 : s4.readReg64 .x26 = outPtr :=
    hx26_cs4.trans (hx26_3.trans (hx26_cs2.trans (hx26_1.trans hx26)))
  have hbox_dealloc :
      A.live boxPtr kit.storeBoxSize 8 ∗
      kit.storeBoxAt boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 1#8 ⊢
      A.live boxPtr (BitVec.ofNat 64 kit.storeBoxSize).toNat (8#64 : BitVec 64).toNat ∗
      memRegion boxPtr (BitVec.ofNat 64 kit.storeBoxSize).toNat := by
    refine Entails.trans (sepConj_mono_right
      (kit.storeBoxAt_memRegion boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 1#8)) ?_
    rw [← hbox_eq]; exact Entails.refl _
  have hfold_2c8 := coro2c8_16_fold_m4_placed coroPtr boxPtr (0#64 + kit.storeFutVtOff)
  rcases ans with ⟨⟩ | ⟨⟩
  · refine P3P4.SepWPp.weaken_frame (storePollPlacedErr_unpack_repack (s.sp + 0x3e0#64))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun o1 =>
      SepWPp.exists_elim fun o2 => SepWPp.exists_elim fun o3 =>
      SepWPp.exists_elim fun o4 => SepWPp.exists_elim fun o5 =>
      SepWPp.exists_elim fun o6 => SepWPp.exists_elim fun H_err =>
      SepWPp.pure_elim fun ⟨hw0_eq, hrepack⟩ => ?_
    have hw0_ne_pend : w0 + 3#64 ≠ 0#64 := by rw [hw0_eq]; decide
    have hw0_ne_ok : w0 + 2#64 ≠ 0#64 := by rw [hw0_eq]; decide
    have h4c := p4_seg4c_gen_placed_wp ext s4 coroPtr boxPtr
      (0#64 + kit.storeFutVtOff) (0#64 + kit.storeFutDropOff) w0
      o2 o3 o4 o5 u_340s u_348s u_350s u_358s o1 o6 u_360s
      hw0_ne_pend (kit.storeFutDrop_ne_zero rfl)
      hpc4 hrun4 hsp4_al hx19_4 hx24_4 hx25_4
    rw [hsp4] at h4c
    refine SepWPp.bind_sepWP_frame_steps h4c (by sep_focus)
      fun s5 P5 hpc5 hrun5 hst5 ⟨hP5, hsp5_4, htr5_4, _, hx19_5, hx21_5, hx22_5,
        hx23_5, hx24_5, hx25_5, hx26_5, _, hx28_5, _, hlr5, hvregs5_4⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP5 (by sep_focus) ?_
    have hcro5 := hcro4.of_keepsFrozen hst5.keepsFrozen
    have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5_4] using hsp_al
    refine call_futDrop_lscro hcro5 (hkit.storeFutDrop (by decide)) hpc5 hrun5 hsp5_al hlr5
      fun s6 hpc6 hrun6 hsp6_5 hsp6_al hcs6 htr6_5 hcro6 hst6 => ?_
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5_4
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, hx22_cs6, hx23_cs6, hx24_cs6, hx25_cs6,
      hx26_cs6, _, hx28_cs6, _, hvregs_cs6⟩
    refine P3P4.SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_errUnwind kit s.sp hsp_ub))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
      (by sep_focus) ?_
    have h4d_err := p4_seg4d_err_placed_wp ext hdealloc s6 coroPtr boxPtr
      (0#64 + kit.storeFutVtOff) (BitVec.ofNat 64 kit.storeBoxSize) 8#64 w0
      kit.storeBoxSize_ne_zero hw0_ne_ok hpc6 hrun6 hsp6_al
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      (hx28_cs6.trans hx28_5)
    rw [hsp6] at h4d_err
    refine SepWPp.bind_sepWP_frame_steps h4d_err (by sep_focus)
      fun s7 P7 hpc7 hrun7 hst7 ⟨hP7, hsp7_6, htr7_6, hx8_7, hx19_7, hx22_7,
        hx24_7, hx25_7, hx26_7, _, hx28_7, _, hvregs7_6⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP7 (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hsp7 : s7.sp = s.sp := hsp7_6
    have hcro7 := hcro6.of_keepsFrozen hst7.keepsFrozen
    have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hsp7]; exact hsp_align
    have hx22_7' : s7.readReg64 .x22 = o1.zeroExtend 64 :=
      hx22_7.trans (hx22_cs6.trans hx22_5)
    have hx24_7' : s7.readReg64 .x24 = s7.sp + 0x370#64 := by
      rw [hx24_7, hx24_cs6, hx24_5, hsp7]
    have hx25_7' : s7.readReg64 .x25 = s7.sp + 0x210#64 := by
      rw [hx25_7, hx25_cs6, hx25_5, hsp7]
    have hx26_7' : s7.readReg64 .x26 = outPtr :=
      hx26_7.trans (hx26_cs6.trans (hx26_5.trans hx26_4))
    have hunwind := stageP4_err_unwind_550_prevEmpty_vregs_placed_ok ext hdealloc hDropSS3 s0 s7
      coroPtr (s.sp + 0x340#64) ptCap ptPtr outPtr w0 o2 o3 o4 o5 o1 o6 b_2c0 pt g G ss.state
      (PanicOomProp s0) hpt_le herr_ub hcro7 hpc7 hrun7 hsp7_align hx8_7 hx19_7 hx22_7'
      hx24_7' hx25_7' hx26_7' hx28_7
      (hvregs7_6.trans (hvregs_cs6.trans (hvregs5_4.trans hvregs4)))
    rw [hsp7] at hunwind
    refine SepWPp.frame_ret_oom hunwind (by sep_focus)
      fun sf P1 hpcf hrunf ⟨hst_unw, hP1, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    have hst_all : Steps (lsProg_518 (Rust.withPanics ext)) s sf :=
      hst_to3.trans (hst4.trans (hst5.trans (hst6.trans (hst7.trans hst_unw))))
    have htr_all : sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()) := by
      rw [htrf, htr7_6, htr6_5, htr5_4, htr4_3, htr_to3]
    refine hErr sf _ hst_all hrel hpcf hrunf hspf htr_all hcsf hvregsf hcrof ?_
    have hreplace :
        ∀ {A B R P Q : SepProp},
          (A ⊢ B) → P = A ∗ R → B ∗ R = Q → (P ⊢ Q) := by
      intro A B R P Q hab hp hq
      rw [hp, ← hq]
      exact sepConj_mono_left hab
    refine Entails.trans (sepConj_mono_left hP1) ?_
    unfold stageP4MatchedStoreErrPostPlaced stageP4MatchedStoreSharedPlaced storeSessionVtablesPlacedAt
    simp only [sepConj_assoc]
    rw [stack_storeSession_to_errUnwind kit s.sp hsp_ub]
    exact hreplace (hrepack outPtr) (by sep_focus) (by ac_rfl)
  · have hstore_ok_eq :
        storePollPlacedOutAt (s.sp + 0x3e0#64) (.ok ()) =
        storePollOutAt 0#64 (s.sp + 0x3e0#64) (.ok ()) := rfl
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (hstore_ok_eq.trans (storePollOk_eq_exists_pollCells 0#64 (s.sp + 0x3e0#64))))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun o1 => SepWPp.exists_elim fun o6 =>
      SepWPp.exists_elim fun o5 => SepWPp.exists_elim fun o4 =>
      SepWPp.exists_elim fun o3 => SepWPp.exists_elim fun o2 => ?_
    have h4c := p4_seg4c_gen_placed_wp ext s4 coroPtr boxPtr
      (0#64 + kit.storeFutVtOff) (0#64 + kit.storeFutDropOff)
      0xfffffffffffffffe#64 o2 o3 o4 o5 u_340s u_348s u_350s u_358s o1 o6 u_360s
      (by decide) (kit.storeFutDrop_ne_zero rfl)
      hpc4 hrun4 hsp4_al hx19_4 hx24_4 hx25_4
    rw [hsp4] at h4c
    refine SepWPp.bind_sepWP_frame_steps h4c (by sep_focus)
      fun s5 P5 hpc5 hrun5 hst5 ⟨hP5, hsp5_4, htr5_4, _, hx19_5, hx21_5, _,
        hx23_5, hx24_5, hx25_5, hx26_5, _, hx28_5, _, hlr5, hvregs5_4⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP5 (by sep_focus) ?_
    have hcro5 := hcro4.of_keepsFrozen hst5.keepsFrozen
    have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5_4] using hsp_al
    refine call_futDrop_lscro hcro5 (hkit.storeFutDrop (by decide)) hpc5 hrun5 hsp5_al hlr5
      fun s6 hpc6 hrun6 hsp6_5 _ hcs6 htr6_5 hcro6 hst6 => ?_
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5_4
    have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, _, hx23_cs6, hx24_cs6, hx25_cs6,
      hx26_cs6, _, hx28_cs6, _, hvregs_cs6⟩
    have hbox_dealloc_ok :
        A.live boxPtr kit.storeBoxSize 8 ∗
        kit.storeBoxAt boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 1#8 ⊢
        A.live boxPtr kit.storeBoxSize 8 ∗ memRegion boxPtr kit.storeBoxSize :=
      sepConj_mono_right
        (kit.storeBoxAt_memRegion boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 1#8)
    refine P3P4.SepWPp.weaken_frame hbox_dealloc_ok (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (stagingCellsAt_entails_memRegion36 (s.sp + 0x340#64) _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hx24_6' : s6.readReg64 .x24 = s6.sp + 0x370#64 := by
      rw [hx24_cs6, hx24_5, hsp6]
    have hx25_6' : s6.readReg64 .x25 = s6.sp + 0x210#64 := by
      rw [hx25_cs6, hx25_5, hsp6]
    have hx26_6' : s6.readReg64 .x26 = outPtr :=
      hx26_cs6.trans (hx26_5.trans hx26_4)
    have htail := stageP4_storeSession_ok_tail_prevEmpty_vregs_placed ext kit hdealloc hDropSS3
      s0 s6 coroPtr boxPtr outPtr ptCap ptPtr b_2c0 pt g G ss.state (PanicOomProp s0)
      hpt_le hcap_lt hptr_nz hsp_ub hcro6 hpc6 hrun6 hsp6_align
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      hx24_6' hx25_6' hx26_6' (hx28_cs6.trans hx28_5)
      (hvregs_cs6.trans (hvregs5_4.trans hvregs4))
    rw [hsp6] at htail
    refine SepWPp.frame_ret_oom htail (by sep_focus)
      fun sf P1 hpcf hrunf ⟨hst_tail, hP1, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    have hst_all : Steps (lsProg_518 (Rust.withPanics ext)) s sf :=
      hst_to3.trans (hst4.trans (hst5.trans (hst6.trans hst_tail)))
    have htr_all : sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()) := by
      rw [htrf, htr6_5, htr5_4, htr4_3, htr_to3]
    refine hOk sf _ hst_all hrel hpcf hrunf hspf htr_all hcsf hvregsf hcrof ?_
    refine Entails.trans (sepConj_mono_left hP1) ?_
    unfold stageP4MatchedStoreOkPostPlaced stageP4MatchedStoreSharedPlaced storeSessionVtablesPlacedAt
    simp only [sepConj_assoc]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
