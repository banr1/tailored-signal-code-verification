/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4UnwindPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StepsPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveId
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP4
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveId
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Unwind

/-!
# Relocatable Matched-Session Substage P4.1 (`save_identity` and Skip `P4.2`/`P4.3`)

Relocatable `[LibsignalPlacement]` counterpart of `Matched.M4SaveId` on Block `518`
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

/-! ## Block-`518` Substage P4.1 basic-block segments -/

set_option maxHeartbeats 800000 in
theorem p4_seg1a_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr idStorePtr idStoreVt saveIdentityShimAddr
    remoteAddrPtr remoteIkPtr ptextMid0 ptextMid1
    u_250 u_258 u_coro284 u_coro28c v_3d0 : BitVec 64)
    (ptextHead ptextTail u_260 u_coro280 u_coro294 : BitVec 32)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (lsProg_518 (Rust.withPanics ext)) saveIdentityShimAddr s
      (((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0xa0#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x280#64) ↦₃₂ u_coro280) ∗
       ((coroPtr + 0x284#64) ↦₆₄ u_coro284) ∗
       ((coroPtr + 0x28c#64) ↦₆₄ u_coro28c) ∗
       ((coroPtr + 0x294#64) ↦₃₂ u_coro294) ∗
       ((idStoreVt + 0x28#64) ↦₆₄ᵣ saveIdentityShimAddr) ∗
       ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
       ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
       ((s.sp + 0x250#64) ↦₆₄ u_250) ∗
       ((s.sp + 0x258#64) ↦₆₄ u_258) ∗
       ((s.sp + 0x260#64) ↦₃₂ u_260) ∗
       ((s.sp + 0x278#64) ↦₃₂ ptextHead) ∗
       ((s.sp + 0x27c#64) ↦₆₄ ptextMid0) ∗
       ((s.sp + 0x284#64) ↦₆₄ ptextMid1) ∗
       ((s.sp + 0x28c#64) ↦₃₂ ptextTail) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0xa0#64) ↦₆₄ idStoreVt) ∗
          ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
          ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
          ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
          ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
          ((idStoreVt + 0x28#64) ↦₆₄ᵣ saveIdentityShimAddr) ∗
          ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
          ((s.sp + 0x250#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x258#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x260#64) ↦₃₂ ptextTail) ∗
          ((s.sp + 0x278#64) ↦₃₂ ptextHead) ∗
          ((s.sp + 0x27c#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x284#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x28c#64) ↦₃₂ ptextTail) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧ s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x2 = remoteIkPtr ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x3564#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p4_seg1b_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr saveIdFutPtr saveIdFutVt saveIdentityPollAddr
    u_2c8 u_2d0 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x3564#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = saveIdFutPtr)
    (hx1 : s.readReg64 .x1 = saveIdFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext)) saveIdentityPollAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ u_2c8) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ u_2d0) ∗
       ((saveIdFutVt + 0x18#64) ↦₆₄ᵣ saveIdentityPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ saveIdFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ saveIdFutVt) ∗
          ((saveIdFutVt + 0x18#64) ↦₆₄ᵣ saveIdentityPollAddr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = saveIdFutPtr ∧ s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x6c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = saveIdFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = saveIdFutVt := hx1
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
theorem p4_seg1c_gen_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr saveIdFutPtr saveIdFutVt saveIdentityDropAddr w0
    w_3ec w_3f4 w_3fc w_404 u_2b0 u_2b8 u_2c0 u_2c8 : BitVec 64)
    (w_3e8 w_40c u_2d0 : BitVec 32)
    (hw0_ne_pend : w0 + 3#64 ≠ 0#64)
    (hdrop_nz : saveIdentityDropAddr ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x6c#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (lsProg_518 (Rust.withPanics ext)) saveIdentityDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ saveIdFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ saveIdFutVt) ∗
       (saveIdFutVt ↦₆₄ᵣ saveIdentityDropAddr) ∗
       stagingCellsAt (s.sp + 0x2b0#64) u_2b0 u_2b8 u_2c0 u_2c8 u_2d0 ∗
       pollCellsAt (s.sp + 0x3e0#64) w0 w_3e8 w_3ec w_3f4 w_3fc w_404 w_40c)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ saveIdFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ saveIdFutVt) ∗
          (saveIdFutVt ↦₆₄ᵣ saveIdentityDropAddr) ∗
          stagingCellsAt (s.sp + 0x2b0#64) w_3ec w_3f4 w_3fc w_404 w_40c ∗
          pollCellsAt (s.sp + 0x3e0#64) w0 w_3e8 w_3ec w_3f4 w_3fc w_404 w_40c) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = saveIdFutPtr ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = saveIdFutPtr ∧ s1.readReg64 .x22 = w_3e8.zeroExtend 64 ∧
        s1.readReg64 .x23 = saveIdFutVt ∧ s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x2ec#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hw0_beq : (w0 + 3#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_pend
  have hdrop_beq : (saveIdentityDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
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
theorem p4_seg1d_err_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr saveIdFutPtr saveIdFutVt futSize futAlign w0 : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hw0_ne_ok : w0 + 2#64 ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x2ec#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = saveIdFutPtr)
    (hx23 : s.readReg64 .x23 = saveIdFutVt)
    (hx28 : s.readReg64 .x28 = w0) :
    SepWP (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x550#64) s
      (((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live saveIdFutPtr futSize.toNat futAlign.toNat ∗
       memRegion saveIdFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x8 = s.sp + 0x2b0#64 ∧
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
  have hx21' : s.readReg64 (Reg.gpr 21#5) = saveIdFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = saveIdFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = w0 := hx28
  wp_steps
  wp_call hdealloc (saveIdFutPtr, futSize.toNat, futAlign.toNat)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-! ## Placed vtable, poll-slot, and `withLsRoCl` call helpers -/

theorem saveIdVtablesAt_placed_intro [LibsignalPlacement] {A : RustAlloc}
    {ikit : IdentityStoreSpec A 0#64} (hvt : IdentityVtablesPlacedOk ikit)
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ saveIdVtablesAt ikit ∗ P := by
  unfold saveIdVtablesAt
  simp only [sepConj_assoc]
  exact hvt.saveSlot hro (hvt.saveFutDrop hro
    (hvt.saveFutSize hro (hvt.saveFutAlign hro (hvt.saveFutPoll hro hP))))

theorem savePollPlacedErr_unpack_repack (p : BitVec 64) :
    savePollPlacedOutAt p (.error ()) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
      ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32, ∃∗ H_err : SepProp,
        ⌜w0 = 0x800000000000001A#64 ∧
          (∀ outPtr : BitVec 64,
            pollCellsAt outPtr w0 o1 o2 o3 o4 o5 o6 ∗ H_err ⊢
              savePollPlacedOutAt outPtr (.error ()))⌝ ∗
        pollCellsAt p w0 o1 o2 o3 o4 o5 o6 ∗ H_err := by
  dsimp only [savePollPlacedOutAt]
  refine Entails.sepExists_elim fun strPtr => Entails.sepExists_elim fun vt => ?_
  dsimp only [errTailPlacedAt]
  simp only [sepConj_assoc]
  refine Entails.trans
    (fiveWords_tail_unpack_repack p 0x800000000000001A#64 strPtr 10#64 1#64 vt strPtr rfl) ?_
  refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun o1 =>
    Entails.sepExists_elim fun o2 => Entails.sepExists_elim fun o3 =>
    Entails.sepExists_elim fun o4 => Entails.sepExists_elim fun o5 =>
    Entails.sepExists_elim fun o6 => Entails.sepExists_elim fun H_err => ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right o1
    (Entails.sepExists_right o2 (Entails.sepExists_right o3
    (Entails.sepExists_right o4 (Entails.sepExists_right o5
    (Entails.sepExists_right o6 (Entails.sepExists_right H_err ?_)))))))
  refine Entails.pure_left fun ⟨hw0, hrep⟩ =>
    Entails.pure_right ⟨hw0, fun outPtr => ?_⟩ (Entails.refl _)
  refine Entails.trans (hrep outPtr) ?_
  refine Entails.sepExists_right strPtr (Entails.sepExists_right vt ?_)
  exact Entails.of_eq (by ac_rfl)

theorem storePollPlacedErr_unpack_repack (p : BitVec 64) :
    storePollPlacedOutAt p (.error ()) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
      ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32, ∃∗ H_err : SepProp,
        ⌜w0 = 0x800000000000001A#64 ∧
          (∀ outPtr : BitVec 64,
            pollCellsAt outPtr w0 o1 o2 o3 o4 o5 o6 ∗ H_err ⊢
              storePollPlacedOutAt outPtr (.error ()))⌝ ∗
        pollCellsAt p w0 o1 o2 o3 o4 o5 o6 ∗ H_err :=
  savePollPlacedErr_unpack_repack p

theorem call_rocl_frame [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (withLsRoCl lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : (⌜φ⌝ ∗ T) ⊢ spec.pre x s) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      Steps prog s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsRoCl lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [hP, sepConj_assoc] at hm
    have hm1 : s.mem ⊨ (⌜φ⌝ ∗ T) ∗ (F ∗ R) := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hφ, hm⟩
    exact Arm64.Satisfies.mono (sepConj_mono_left hspec) hm1
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ |
    ⟨_, hoom_post⟩
  rotate_right
  · dsimp only [withLsRoCl] at hoom_post
    rw [hoom_false] at hoom_post
    exact (not_satisfies_false_sepConj hoom_post).elim
  · dsimp only [withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hcrom, hpost⟩
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hcrom hsteps R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsRoCl] at hpost
    rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, allowPanic_oom_of_trace_prefix htr⟩)⟩
  · dsimp only [withLsRoCl] at hpost
    rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

theorem call_futDrop_lscro [LibsignalPlacement] {prog : Program}
    {ret entry ret_pc : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (StoreKit.withLsRoCl lsmpl futDropSpec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      sf.trace = s.trace →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      Steps prog s sf →
      SepWPp prog ret sf P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (StoreKit.withLsRoCl lsmpl futDropSpec).pre () s ∗ (P ∗ R) := by
    dsimp only [StoreKit.withLsRoCl, futDropSpec]
    rw [emp_sepConj, satisfies_pure_sepConj]
    exact ⟨hcro, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall () (P ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ |
    ⟨_, hpost⟩
  · dsimp only [StoreKit.withLsRoCl, futDropSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hcrl_sm, hpost⟩
    rw [satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm htrm
        hcrl_sm hsteps R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [StoreKit.withLsRoCl, futDropSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [StoreKit.withLsRoCl, futDropSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [StoreKit.withLsRoCl, futDropSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim

/-! ## Spatial bundles and matched-session Substage P4.1 -/

def stageP4MatchedSaveIdSharedPlaced [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64)
    (s0 s : State)
    (coroPtr remoteAddrPtr remoteIkPtr idStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) : SepProp :=
  ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0xa0#64) ↦₆₄ ikit.id_vt) ∗
  ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
  ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
  memRegion (s.sp + 0x250#64) 20 ∗
  ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
  ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x2b0#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  protocolAddressAt A peer remoteAddrPtr ∗
  (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool ∗
  stackAt s.sp (saveIdCallStack ikit)

def stageP4MatchedSaveIdPrePlaced [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64)
    (s0 s : State)
    (coroPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (ist0 : ikit.IdState)
    (g : RecordGhost) (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  stageP4MatchedSaveIdSharedPlaced ikit s0 s coroPtr remoteAddrPtr remoteIkPtr idStorePtr
    ptCap ptPtr v_3d0 pt peer remoteIk ∗
  prevSessionsEmptyAt A coroPtr g ∗
  sessionStateAt A (coroPtr + 0xf8#64) G st ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist0

def stageP4MatchedSaveIdOkPostPlaced [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64)
    (s0 s : State)
    (coroPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (ist0 : ikit.IdState) (c : IdentityChange)
    (g : RecordGhost) (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  stageP4MatchedSaveIdSharedPlaced ikit s0 s coroPtr remoteAddrPtr remoteIkPtr idStorePtr
    ptCap ptPtr v_3d0 pt peer remoteIk ∗
  saveIdVtablesAt ikit ∗
  prevSessionsEmptyAt A coroPtr g ∗
  sessionStateAt A (coroPtr + 0xf8#64) G st ∗
  ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
  ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
  ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))

def stageP4MatchedSaveIdErrPostPlaced [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64)
    (s0 s : State)
    (coroPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (ist0 : ikit.IdState) :
    SepProp :=
  stageP4MatchedSaveIdSharedPlaced ikit s0 s coroPtr remoteAddrPtr remoteIkPtr idStorePtr
    ptCap ptPtr v_3d0 pt peer remoteIk ∗
  saveIdVtablesAt ikit ∗
  savePollPlacedOutAt outPtr (.error ()) ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr (ikit.saveUpdate ist0 peer.val remoteIk (.error ()))

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` matched-session Substage P4.1
(`(blkPl_518).base + 0x34dc → +0x3cc` / `x30` when `opkIdIsSome = 2#32`). -/
theorem stageP4_matched_saveIdentity_vregs_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (ikit : IdentityStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hikit : IdentityStoreKitPlacedOkI ikit (Rust.withPanics ext))
    (hiVt : IdentityVtablesPlacedOk ikit)
    {Qfs : Prop}
    (s0 s : State)
    (coroPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (ist0 : ikit.IdState)
    (g : RecordGhost) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (haddrOk : ikit.addrOk peer.val)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : saveIdCallStack ikit ≤ 2 ^ 64)
    (hfs : FsAt ikit.envOk Qfs (lsProg_518 (Rust.withPanics ext)) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (c : IdentityChange) (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 (Rust.withPanics ext)) s s1 →
      ikit.saveRel ist0 peer.val remoteIk (.ok c) →
      s1.pc = (blkPl_518).base + 0x3cc#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 →
      s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢ stageP4MatchedSaveIdOkPostPlaced ikit s0 s coroPtr outPtr remoteAddrPtr remoteIkPtr
        idStorePtr ptCap ptPtr v_3d0 b_2c0 pt peer remoteIk ist0 c g G st ∗ F) →
      SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s1 P1 Q (PanicOomProp s0))
    (hErr : ∀ (sf : State) (Pf : SepProp),
      Steps (lsProg_518 (Rust.withPanics ext)) s sf →
      ikit.saveRel ist0 peer.val remoteIk (.error ()) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4MatchedSaveIdErrPostPlaced ikit s0 s coroPtr outPtr remoteAddrPtr remoteIkPtr
        idStorePtr ptCap ptPtr v_3d0 pt peer remoteIk ist0 ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stageP4MatchedSaveIdPrePlaced ikit s0 s coroPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
        ptCap ptPtr v_3d0 b_2c0 pt peer remoteIk ist0 g G st ∗ F)
      Q (PanicOomProp s0) := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  have hbox_eq : ikit.saveBoxSize = (BitVec.ofNat 64 ikit.saveBoxSize).toNat :=
    (Nat.mod_eq_of_lt ikit.saveBoxSize_lt).symm
  have hsp_al : s.spAligned = true := hsp_align
  refine SepWPp.intro_ro (R_ro := saveIdVtablesAt ikit)
    (fun hm => saveIdVtablesAt_placed_intro hiVt hcro.2 hm) ?_
  unfold stageP4MatchedSaveIdPrePlaced stageP4MatchedSaveIdSharedPlaced saveIdVtablesAt
  simp only [sepConj_assoc]
  let ptLen := BitVec.ofNat 64 pt.length
  have hpt_sp :
      ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗ ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
      ((s.sp + 0x288#64) ↦₆₄ ptLen) =
      ((s.sp + 0x278#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((s.sp + 0x27c#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((s.sp + 0x284#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((s.sp + 0x28c#64) ↦₃₂ ptLen.extractLsb' 32 32) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      words3_eq_head_mid_tail (s.sp + 0x278#64) ptCap ptPtr ptLen
  have hpt_coro :
      ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗ ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
      ((coroPtr + 0x290#64) ↦₆₄ ptLen) =
      ((coroPtr + 0x280#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((coroPtr + 0x284#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((coroPtr + 0x28c#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((coroPtr + 0x294#64) ↦₃₂ ptLen.extractLsb' 32 32) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      words3_eq_head_mid_tail (coroPtr + 0x280#64) ptCap ptPtr ptLen
  have h280_un :
      memRegion (coroPtr + 0x280#64) 24 =
      ∃∗ u3 : BitVec 32, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 32,
        ((coroPtr + 0x280#64) ↦₃₂ u0) ∗ ((coroPtr + 0x284#64) ↦₆₄ u1) ∗
        ((coroPtr + 0x28c#64) ↦₆₄ u2) ∗ ((coroPtr + 0x294#64) ↦₃₂ u3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion24_eq_unaligned_cells (coroPtr + 0x280#64)
  have h250_un :
      memRegion (s.sp + 0x250#64) 20 =
      ∃∗ u2 : BitVec 32, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((s.sp + 0x250#64) ↦₆₄ u0) ∗ ((s.sp + 0x258#64) ↦₆₄ u1) ∗
        ((s.sp + 0x260#64) ↦₃₂ u2) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_eq_cells (s.sp + 0x250#64)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpt_sp) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq h280_un) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_coro294 => SepWPp.exists_elim fun u_coro28c =>
    SepWPp.exists_elim fun u_coro284 => SepWPp.exists_elim fun u_coro280 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq h250_un) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  have h1a := p4_seg1a_placed_wp ext s coroPtr idStorePtr ikit.id_vt
    (0#64 + ikit.saveShimOff) remoteAddrPtr remoteIkPtr
    (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
    (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
    u_250 u_258 u_coro284 u_coro28c v_3d0
    (ptCap.extractLsb' 0 32) (ptLen.extractLsb' 32 32) u_260 u_coro280 u_coro294
    hpc hrun hsp_al hx19 hx25 hx28
  refine SepWPp.bind_sepWP_frame_steps h1a (by sep_focus)
    fun s1 P1 hpc1 hrun1 hst1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1,
      hx19_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hlr1, hvregs1⟩ => ?_
  refine P3P4.SepWPp.weaken_frame hP1 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpt_coro.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpt_sp.symm) (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ ptLen.extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      cells20_entails_memRegion20 (s.sp + 0x250#64) _ _ _
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hcro1 := hcro.of_keepsFrozen hst1.keepsFrozen
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_al
  have htr1_pfx : s0.trace <+: s1.trace := htr1 ▸ htr_pfx
  have hfs1 := hfs.of_steps_nil hst1 htr1
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_shim ikit s.sp hsp_ub))
    (by sep_focus) ?_
  refine call_rocl_frame
    (x := ({ self := idStorePtr, addrA := remoteAddrPtr, keyA := remoteIkPtr } : IdentityShimCall))
    (φ := s1.readReg64 .x0 = idStorePtr ∧ s1.readReg64 .x1 = remoteAddrPtr ∧
          s1.readReg64 .x2 = remoteIkPtr)
    (T := A.pool ∗ stackAt s.sp ikit.saveShimStack)
    hcro1 htr1_pfx (hikit.saveShim (by decide)) hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [kitSaveShimSpec]; rw [hsp1]; exact Entails.of_eq (by ac_rfl))
    ⟨hx0_1, hx1_1, hx2_1⟩ (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 hst2 => ?_)
  dsimp only [kitSaveShimSpec]
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_2, _, _, htr2_1⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_shim ikit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have htr2_pfx : s0.trace <+: s2.trace := htr2_1 ▸ htr1_pfx
  have hfs2 := hfs1.of_steps_nil hst2 htr2_1
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs_cs2⟩
  let saveIdFutPtr := s2.readReg64 .x0
  have h2c8_un :
      memRegion (coroPtr + 0x2c8#64) 16 =
      ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((coroPtr + 0x2c8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ u1) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion16_eq_cells (coroPtr + 0x2c8#64)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq h2c8_un) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_2d0 => SepWPp.exists_elim fun u_2c8 => ?_
  have h1b := p4_seg1b_placed_wp ext s2 coroPtr ctxPtr saveIdFutPtr
    (0#64 + ikit.saveFutVtOff) (0#64 + ikit.savePollOff) u_2c8 u_2d0
    hpc2 hrun2 rfl hx1_2 (hx19_cs2.trans hx19_1) (hx27_cs2.trans (hx27_1.trans hx27))
  refine SepWPp.bind_sepWP_frame_steps h1b (by sep_focus)
    fun s3 P3 hpc3 hrun3 hst3 ⟨hP3, hsp3_2, htr3_2, hx0_3, _, hx8_3,
      hx19_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _, hlr3, hvregs3_2⟩ => ?_
  refine P3P4.SepWPp.weaken_frame hP3 (by sep_focus) ?_
  have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
  have hcro3 := hcro2.of_keepsFrozen hst3.keepsFrozen
  have hsp3_al : s3.spAligned = true := by simpa [State.spAligned, hsp3] using hsp_al
  have htr3_pfx : s0.trace <+: s3.trace := htr3_2 ▸ htr2_pfx
  have hfs3 := hfs2.of_steps_nil hst3 htr3_2
  rw [hsp2] at hx8_3
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_poll ikit s.sp hsp_ub))
    (by sep_focus) ?_
  let pollCall : IdentityPollCall :=
    { fut := saveIdFutPtr
      out := s.sp + 0x3e0#64
      call := { addrA := remoteAddrPtr, addr := peer, keyA := remoteIkPtr, key := remoteIk } }
  refine call_rocl_frame
    (spec := kitSavePollPlacedSpecI ikit)
    (x := (pollCall, idStorePtr, ist0))
    (φ := ikit.envOk s3.fs.files ∧ s3.readReg64 .x0 = saveIdFutPtr ∧
          s3.readReg64 .x8 = s.sp + 0x3e0#64 ∧ ikit.addrOk peer.val)
    (T := ikit.saveBoxAt saveIdFutPtr idStorePtr remoteAddrPtr remoteIkPtr 0#8 ∗
          ikit.identityAt idStorePtr ist0 ∗ memRegion (s.sp + 0x3e0#64) 48 ∗
          protocolAddressAt A peer remoteAddrPtr ∗
          (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗ A.pool ∗
          stackAt s.sp ikit.savePollStack ∗ (lsLogFilterAddr ↦₆₄ 0#64))
    hcro3 htr3_pfx (hikit.savePoll (by decide)) hpc3 hrun3 hsp3_al hlr3
    (by
      dsimp only [kitSavePollPlacedSpecI, StoreKit.withLsLogOff, kitSavePollPlacedSpecE,
        withEnvPre, kitSavePollPlacedSpec, FromRecordCallees.lsLogOff, pollCall]
      rw [hsp3]
      simp only [sepConj_assoc]
      refine Entails.pure_left fun ⟨henv, hx0', hx8', haok⟩ => ?_
      refine Entails.pure_right henv (Entails.pure_right ⟨hx0', hx8', haok⟩ ?_)
      exact Entails.of_eq (by ac_rfl))
    ⟨hfs3.envOk_here, hx0_3, hx8_3, haddrOk⟩ (by sep_focus)
    (hnext := fun s4 hpc4 hrun4 hsp4_3 hsp4_al hcs4 hcro4 hst4 => ?_)
  dsimp only [kitSavePollPlacedSpecI, StoreKit.withLsLogOff, kitSavePollPlacedSpecE,
    withEnvPre, kitSavePollPlacedSpec, FromRecordCallees.lsLogOff, pollCall]
  rw [hsp3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => ?_
  refine SepWPp.pure_elim fun ⟨hrel, htr4_3⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_poll ikit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x2b0#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_2d0s => SepWPp.exists_elim fun u_2c8s =>
    SepWPp.exists_elim fun u_2c0s => SepWPp.exists_elim fun u_2b8s =>
    SepWPp.exists_elim fun u_2b0s => ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  rcases hcs4 with ⟨hx19_cs4, _, _, _, _, hx24_cs4, hx25_cs4, hx26_cs4, hx27_cs4, hx28_cs4, _, hvregs_cs4⟩
  have hvregs_4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 :=
    hvregs_cs4.trans (hvregs3_2.trans (hvregs_cs2.trans (hvregs1.trans hvregs)))
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx24_4 : s4.readReg64 .x24 = s4.sp + 0x370#64 := by
    rw [hx24_cs4, hx24_3, hx24_cs2, hx24_1, hx24, hsp4]
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by
    rw [hx25_cs4, hx25_3, hx25_cs2, hx25_1, hsp4]
  have hx26_4 : s4.readReg64 .x26 = outPtr :=
    hx26_cs4.trans (hx26_3.trans (hx26_cs2.trans (hx26_1.trans hx26)))
  have hx27_4 : s4.readReg64 .x27 = ctxPtr := hx27_cs4.trans hx27_3
  have htr3_s : s3.trace = s.trace := htr3_2.trans (htr2_1.trans htr1)
  have hst_to4 : Steps (lsProg_518 (Rust.withPanics ext)) s s4 :=
    hst1.trans (hst2.trans (hst3.trans hst4))
  have hfold_2c8 :
      ((coroPtr + 0x2c8#64) ↦₆₄ saveIdFutPtr) ∗
      ((coroPtr + 0x2d0#64) ↦₆₄ (0#64 + ikit.saveFutVtOff)) ⊢
      memRegion (coroPtr + 0x2c8#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      cells16_entails_memRegion16 (coroPtr + 0x2c8#64) _ _
  have hbox_dealloc :
      A.live saveIdFutPtr ikit.saveBoxSize 8 ∗
      ikit.saveBoxAt saveIdFutPtr idStorePtr remoteAddrPtr remoteIkPtr 1#8 ⊢
      A.live saveIdFutPtr (BitVec.ofNat 64 ikit.saveBoxSize).toNat (8#64).toNat ∗
      memRegion saveIdFutPtr (BitVec.ofNat 64 ikit.saveBoxSize).toNat := by
    refine Entails.trans (sepConj_mono_right (ikit.saveBoxAt_memRegion _ _ _ _ _)) ?_
    rw [← hbox_eq]; exact Entails.refl _
  rcases ans with ⟨⟩ | c
  · -- Err () arm: +0x6c → saveFutDrop → +0x2ec → +0x550 → x30
    refine P3P4.SepWPp.weaken_frame (savePollPlacedErr_unpack_repack (s.sp + 0x3e0#64))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun o1 =>
      SepWPp.exists_elim fun o2 => SepWPp.exists_elim fun o3 =>
      SepWPp.exists_elim fun o4 => SepWPp.exists_elim fun o5 =>
      SepWPp.exists_elim fun o6 => SepWPp.exists_elim fun H_err => ?_
    refine SepWPp.pure_elim fun ⟨hw0_eq, hrepack⟩ => ?_
    subst hw0_eq
    have h1c := p4_seg1c_gen_placed_wp ext s4 coroPtr saveIdFutPtr
      (0#64 + ikit.saveFutVtOff) (0#64 + ikit.saveFutDropOff)
      0x800000000000001A#64 o2 o3 o4 o5 u_2b0s u_2b8s u_2c0s u_2c8s o1 o6 u_2d0s
      (by decide) (ikit.saveFutDrop_ne_zero rfl) hpc4 hrun4 hsp4_al hx19_4 hx24_4 hx25_4
    rw [hsp4] at h1c
    refine SepWPp.bind_sepWP_frame_steps h1c (by sep_focus)
      fun s5 P5 hpc5 hrun5 hst5 ⟨hP5, hsp5_4, htr5_4, _, hx19_5, hx21_5, hx22_5, hx23_5,
        hx24_5, hx25_5, hx26_5, _, hx28_5, _, hlr5, hvregs5_4⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP5 (by sep_focus) ?_
    have hsp5 : s5.sp = s.sp := hsp5_4
    have hcro5 := hcro4.of_keepsFrozen hst5.keepsFrozen
    have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_al
    refine call_futDrop_lscro hcro5 (hikit.saveFutDrop (by decide)) hpc5 hrun5 hsp5_al hlr5
      fun s6 hpc6 hrun6 hsp6_5 hsp6_al hcs6 htr6_5 hcro6 hst6 => ?_
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, hx22_cs6, hx23_cs6, hx24_cs6, hx25_cs6,
      hx26_cs6, _, hx28_cs6, _, hvregs_cs6⟩
    refine P3P4.SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_errUnwind ikit s.sp hsp_ub))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
      (by sep_focus) ?_
    have h1d_err := p4_seg1d_err_placed_wp ext hdealloc s6 coroPtr saveIdFutPtr
      (0#64 + ikit.saveFutVtOff) (BitVec.ofNat 64 ikit.saveBoxSize) 8#64
      0x800000000000001A#64 ikit.saveBoxSize_ne_zero (by decide) hpc6 hrun6 hsp6_al
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      (hx28_cs6.trans hx28_5)
    rw [hsp6] at h1d_err
    refine SepWPp.bind_sepWP_frame_steps h1d_err (by sep_focus)
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
      coroPtr (s.sp + 0x2b0#64) ptCap ptPtr outPtr 0x800000000000001A#64
      o2 o3 o4 o5 o1 o6 b_2c0 pt g G st (PanicOomProp s0)
      hpt_le herr_ub hcro7 hpc7 hrun7 hsp7_align hx8_7 hx19_7 hx22_7'
      hx24_7' hx25_7' hx26_7' hx28_7
      (hvregs7_6.trans (hvregs_cs6.trans (hvregs5_4.trans hvregs_4)))
    rw [hsp7] at hunwind
    refine SepWPp.frame_ret_oom hunwind (by sep_focus)
      fun sf P1 hpcf hrunf ⟨hst_unw, hP1, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    have hst_all : Steps (lsProg_518 (Rust.withPanics ext)) s sf :=
      hst_to4.trans (hst5.trans (hst6.trans (hst7.trans hst_unw)))
    have htr_all : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) := by
      rw [htrf, htr7_6, htr6_5, htr5_4, htr4_3, htr3_s]
    refine hErr sf _ hst_all hrel hpcf hrunf hspf htr_all hcsf hvregsf hcrof ?_
    have hreplace :
        ∀ {A B R P Q : SepProp},
          (A ⊢ B) → P = A ∗ R → B ∗ R = Q → (P ⊢ Q) := by
      intro A B R P Q hab hp hq
      rw [hp, ← hq]
      exact sepConj_mono_left hab
    refine Entails.trans (sepConj_mono_left hP1) ?_
    unfold stageP4MatchedSaveIdErrPostPlaced stageP4MatchedSaveIdSharedPlaced saveIdVtablesAt
    rw [stack_saveId_to_errUnwind ikit s.sp hsp_ub]
    exact hreplace (hrepack outPtr) (by sep_focus) (by ac_rfl)
  · -- Ok c arm: +0x6c → saveFutDrop → +0x2ec → +0x3cc (skipping P4.2 and P4.3)
    have hsave_ok_eq :
        savePollPlacedOutAt (s.sp + 0x3e0#64) (.ok c) =
        savePollOutAt 0#64 (s.sp + 0x3e0#64) (.ok c) := rfl
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (hsave_ok_eq.trans (savePollOk_eq_exists_pollCells 0#64 (s.sp + 0x3e0#64) c)))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun o6 => SepWPp.exists_elim fun o5 =>
      SepWPp.exists_elim fun o4 => SepWPp.exists_elim fun o3 =>
      SepWPp.exists_elim fun o2 => ?_
    have h1c := p4_seg1c_gen_placed_wp ext s4 coroPtr saveIdFutPtr
      (0#64 + ikit.saveFutVtOff) (0#64 + ikit.saveFutDropOff)
      0xfffffffffffffffe#64 o2 o3 o4 o5 u_2b0s u_2b8s u_2c0s u_2c8s
      (if c == .replacedExisting then 1#32 else 0#32) o6 u_2d0s
      (by decide) (ikit.saveFutDrop_ne_zero rfl) hpc4 hrun4 hsp4_al hx19_4 hx24_4 hx25_4
    rw [hsp4] at h1c
    refine SepWPp.bind_sepWP_frame_steps h1c (by sep_focus)
      fun s5 P5 hpc5 hrun5 hst5 ⟨hP5, hsp5_4, htr5_4, _, hx19_5, hx21_5, _, hx23_5,
        hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, _, hlr5, hvregs5_4⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP5 (by sep_focus) ?_
    have hsp5 : s5.sp = s.sp := hsp5_4
    have hcro5 := hcro4.of_keepsFrozen hst5.keepsFrozen
    have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_al
    refine call_futDrop_lscro hcro5 (hikit.saveFutDrop (by decide)) hpc5 hrun5 hsp5_al hlr5
      fun s6 hpc6 hrun6 hsp6_5 hsp6_al hcs6 htr6_5 hcro6 hst6 => ?_
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, _, hx23_cs6, hx24_cs6, hx25_cs6,
      hx26_cs6, hx27_cs6, hx28_cs6, _, hvregs_cs6⟩
    refine P3P4.SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_errUnwind ikit s.sp hsp_ub))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
      (by sep_focus) ?_
    have h1d_skip := p4_seg1d_skip_placed_wp ext hdealloc s6 coroPtr saveIdFutPtr
      (0#64 + ikit.saveFutVtOff) (BitVec.ofNat 64 ikit.saveBoxSize) 8#64
      hpc6 hrun6 hsp6_al
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      (hx28_cs6.trans hx28_5)
    simp only [ikit.saveBoxSize_ne_zero, ↓reduceIte, hsp6] at h1d_skip
    refine SepWPp.bind_sepWP_frame_steps h1d_skip (by sep_focus)
      fun s7 P7 hpc7 hrun7 hst7 ⟨hP7, hsp7_6, htr7_6,
        hx19_7, hx24_7, hx25_7, hx26_7, hx27_7, hx28_7, _, hvregs7_6⟩ => ?_
    refine P3P4.SepWPp.weaken_frame hP7 (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_errUnwind ikit s.sp hsp_ub).symm)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (stagingCellsAt_entails_memRegion36 (s.sp + 0x2b0#64) _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hst_all : Steps (lsProg_518 (Rust.withPanics ext)) s s7 :=
      hst_to4.trans (hst5.trans (hst6.trans hst7))
    have htr_all : s7.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) := by
      rw [htr7_6, htr6_5, htr5_4, htr4_3, htr3_s]
    have hcro7 := hcro6.of_keepsFrozen hst7.keepsFrozen
    refine hOk c s7 _ hst_all hrel hpc7 hrun7 hsp7_6 htr_all
      hx19_7 (hx24_7.trans (hx24_cs6.trans hx24_5))
      (hx25_7.trans (hx25_cs6.trans hx25_5))
      (hx26_7.trans (hx26_cs6.trans (hx26_5.trans hx26_4)))
      (hx27_7.trans (hx27_cs6.trans (hx27_5.trans hx27_4)))
      hx28_7 hcro7
      (hvregs7_6.trans (hvregs_cs6.trans (hvregs5_4.trans hvregs_4))) ?_
    unfold stageP4MatchedSaveIdOkPostPlaced stageP4MatchedSaveIdSharedPlaced saveIdVtablesAt
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
