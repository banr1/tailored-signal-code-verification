/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4UnwindPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable Stage P4 Error-Unwind Tail with `calleeSavedVRegs`

Relocatable `[LibsignalPlacement]` counterpart of `StageP4VRegsErrUnwind` on Block `518`
(`lsProg_518 ext`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

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
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## Block-518 error-unwind basic-block segments -/

theorem p4_err_550_zero_vregs_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr slot ptPtr o2 o3 o4 o5 u_370 u_378 u_380 u_388 : BitVec 64)
    (o6 u_390 : BitVec 32)
    (hpc : s.pc = (blkPl_518).base + 0x550#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = slot)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x3588#64) s
      (((coroPtr + 0x280#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       stagingCellsAt slot o2 o3 o4 o5 o6 ∗
       stagingCellsAt (s.sp + 0x370#64) u_370 u_378 u_380 u_388 u_390)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x280#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
          stagingCellsAt slot o2 o3 o4 o5 o6 ∗
          stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  unfold stagingCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hx8' : s.readReg64 (Reg.gpr 8#5) = slot := hx8
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], rfl⟩

theorem p4_err_550_nonzero_vregs_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr slot ptCap ptPtr o2 o3 o4 o5 u_370 u_378 u_380 u_388 : BitVec 64)
    (o6 u_390 : BitVec 32)
    (hcap_nz : ptCap ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x550#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = slot)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x3588#64) s
      (((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       stagingCellsAt slot o2 o3 o4 o5 o6 ∗
       stagingCellsAt (s.sp + 0x370#64) u_370 u_378 u_380 u_388 u_390 ∗
       A.live ptPtr ptCap.toNat 1 ∗
       memRegion ptPtr ptCap.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
          ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
          stagingCellsAt slot o2 o3 o4 o5 o6 ∗
          stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcap_beq : (ptCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  unfold stagingCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hx8' : s.readReg64 (Reg.gpr 8#5) = slot := hx8
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  wp_steps
  wp_call hdealloc (ptPtr, ptCap.toNat, 1)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p4_err_3588_vregs_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr ssCap : BitVec 64)
    (hcap_ne : ssCap + 1#64 ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x3588#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      ((coroPtr + 0xf8#64) ↦₆₄ ssCap)
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ ssCap)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x359c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcur_beq : (ssCap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], rfl⟩

theorem p4_err_tail_359c_vregs_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr errTag prevStatesPtr
    o2 o3 o4 o5 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 o6 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hpc : s.pc = (blkPl_518).base + 0x359c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (lsProg_518 ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       pollCellsAt outPtr u_ret0 u_ret08 u_ret0c u_ret14 u_ret1c u_ret24 u_ret2c ∗
       stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
          stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  unfold pollCellsAt stagingCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    rfl⟩

/-! ## Composed error-unwind theorems (`+0x3588 → ret` and `+0x550 → ret`) -/

set_option maxHeartbeats 800000 in
/-- Composed `(blkPl_518).base + 0x3588 → s0.readReg64 .x30` unwind preserving `calleeSavedVRegs s0`
under `[LibsignalPlacement]`. -/
theorem stageP4_err_unwind_3588_vregs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State) (coroPtr outPtr errTag prevStatesPtr o2 o3 o4 o5 : BitVec 64)
    (w_22 o6 : BitVec 32) (b_2c0 : BitVec 8)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hsp_ub : stageP4ErrUnwindStack ≤ 2 ^ 64)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (sessionStateAt A (coroPtr + 0xf8#64) G st ∗
       ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp stageP4ErrUnwindStack)
      (fun sf P_f =>
        Steps (lsProg_518 ext) s sf ∧
        (P_f ⊢
          pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          memRegion (coroPtr + 0xf8#64) 344 ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp stageP4ErrUnwindStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  refine SepWPp.with_steps ?_
  refine P3P4.SepWPp.weaken_frame (p4_sessionStateAt_expose_cap_ne A (coroPtr + 0xf8#64) G st)
    (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hcap_ne => ?_
  have hstep1 := p4_err_3588_vregs_placed_wp ext s coroPtr G.localIk.cap hcap_ne hpc hrun hx19
  refine bind_sepWP_lscro_frame hcro hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hlr1, hvregs1⟩
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (p4_sessionStateAt_expose_cap A (coroPtr + 0xf8#64) G st).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_errUnwind_to_dropSS3 s.sp hsp_ub)) (by sep_focus) ?_
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
    (Entails.of_eq (stack_errUnwind_to_dropSS3 s.sp hsp_ub).symm) (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = w_22.zeroExtend 64 := hx22_cs2.trans (hx22_1.trans hx22)
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = errTag := hx28_cs2.trans (hx28_1.trans hx28)
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion48_eq_exists_pollCells outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun o6_u => SepWPp.exists_elim fun o5_u =>
    SepWPp.exists_elim fun o4_u => SepWPp.exists_elim fun o3_u =>
    SepWPp.exists_elim fun o2_u => SepWPp.exists_elim fun o1_u =>
    SepWPp.exists_elim fun w0_u => ?_
  have hstep3 := p4_err_tail_359c_vregs_placed_wp ext s2 coroPtr outPtr errTag prevStatesPtr
    o2 o3 o4 o5 w0_u o2_u o3_u o4_u o5_u
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    w_22 o6 o1_u o6_u b_2c0
    hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
  rw [hsp2] at hstep3
  refine bind_sepWP_lscro_frame hcro2 hstep3 (by sep_focus)
    fun sf hpcf hrunf hcrof hregsf => ?_
  rcases hregsf with ⟨hspf, htrf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f,
    hx27f, hx28f, hx29f, _, hvregsf⟩
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (stagingCellsAt_entails_memRegion36 (s.sp + 0x370#64) o2 o3 o4 o5 o6) (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), ?_⟩
  refine ⟨hspf, by rw [htrf, htr2_1, htr1], ?_,
    hvregsf.trans (hvregs_cs2.trans (hvregs1.trans hvregs)), hcrof⟩
  exact ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, trivial⟩

set_option maxHeartbeats 1000000 in
/-- Composed `(blkPl_518).base + 0x550 → s0.readReg64 .x30` unwind preserving `calleeSavedVRegs s0`
under `[LibsignalPlacement]`. -/
theorem stageP4_err_unwind_550_vregs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State)
    (coroPtr slot ptCap ptPtr outPtr errTag prevStatesPtr o2 o3 o4 o5 : BitVec 64)
    (w_22 o6 : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : stageP4ErrUnwindStack ≤ 2 ^ 64)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x550#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = slot)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (ptPtr ↦ₛ pt) ∗
       (if ptCap = 0#64 then emp
        else A.live ptPtr ptCap.toNat 1 ∗
          memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       stagingCellsAt slot o2 o3 o4 o5 o6 ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       sessionStateAt A (coroPtr + 0xf8#64) G st ∗
       ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp stageP4ErrUnwindStack)
      (fun sf P_f =>
        Steps (lsProg_518 ext) s sf ∧
        (P_f ⊢
          pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          memRegion (coroPtr + 0xf8#64) 344 ∗
          memRegion (coroPtr + 0x280#64) 24 ∗
          memRegion slot 36 ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp stageP4ErrUnwindStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by

  refine SepWPp.with_steps ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x370#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_390 => SepWPp.exists_elim fun u_388 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  by_cases hcap_z : ptCap = 0#64
  · subst hcap_z
    refine P3P4.SepWPp.weaken_frame (ptextBuf_dealloc_zero A ptPtr pt hpt_le) (by sep_focus) ?_
    simp only [emp_sepConj, sepConj_emp, sepConj_assoc]
    have hstep0 := p4_err_550_zero_vregs_placed_wp ext s coroPtr slot ptPtr
      o2 o3 o4 o5 u_370 u_378 u_380 u_388 o6 u_390
      hpc hrun hsp_align hx8 hx19 hx24
    refine bind_sepWP_lscro_frame hcro hstep0 (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hvregs1⟩
    refine P3P4.SepWPp.weaken_frame
      (coro280_words3_entails_memRegion24 coroPtr 0#64 ptPtr (BitVec.ofNat 64 pt.length))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (stagingCellsAt_entails_memRegion36 slot o2 o3 o4 o5 o6) (by sep_focus) ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hx22_1' : s1.readReg64 .x22 = w_22.zeroExtend 64 := hx22_1.trans hx22
    have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hx25, hsp1]
    have hx26_1' : s1.readReg64 .x26 = outPtr := hx26_1.trans hx26
    have hx28_1' : s1.readReg64 .x28 = errTag := hx28_1.trans hx28
    have htail := stageP4_err_unwind_3588_vregs_placed_ok ext hDropSS3 s0 s1
      coroPtr outPtr errTag prevStatesPtr o2 o3 o4 o5 w_22 o6 b_2c0 G st (fun _ _ => False)
      hsp_ub hcro1 hpc1 hrun1 hsp1_align hx19_1 hx22_1' hx25_1' hx26_1' hx28_1'
      (hvregs1.trans hvregs)
    rw [hsp1] at htail
    refine SepWPp.bind_false_frame htail (by sep_focus)
      fun sf P_f hpcf hrunf ⟨_, hentf, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hentf) ?_
    refine SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), ?_⟩
    exact ⟨hspf, by rw [htrf, htr1], hcsf, hvregsf, hcrof⟩
  · refine P3P4.SepWPp.weaken_frame
      (ptextBuf_dealloc_nonzero A ptCap ptPtr pt hcap_z hpt_le) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub)) (by sep_focus) ?_
    simp only [sepConj_assoc]
    have hstep0 := p4_err_550_nonzero_vregs_placed_wp ext hdealloc s coroPtr slot ptCap ptPtr
      o2 o3 o4 o5 u_370 u_378 u_380 u_388 o6 u_390
      hcap_z hpc hrun hsp_align hx8 hx19 hx24
    refine bind_sepWP_lscro_frame hcro hstep0 (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hvregs1⟩
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (coro280_words3_entails_memRegion24 coroPtr ptCap ptPtr (BitVec.ofNat 64 pt.length))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (stagingCellsAt_entails_memRegion36 slot o2 o3 o4 o5 o6) (by sep_focus) ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hx22_1' : s1.readReg64 .x22 = w_22.zeroExtend 64 := hx22_1.trans hx22
    have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hx25, hsp1]
    have hx26_1' : s1.readReg64 .x26 = outPtr := hx26_1.trans hx26
    have hx28_1' : s1.readReg64 .x28 = errTag := hx28_1.trans hx28
    have htail := stageP4_err_unwind_3588_vregs_placed_ok ext hDropSS3 s0 s1
      coroPtr outPtr errTag prevStatesPtr o2 o3 o4 o5 w_22 o6 b_2c0 G st (fun _ _ => False)
      hsp_ub hcro1 hpc1 hrun1 hsp1_align hx19_1 hx22_1' hx25_1' hx26_1' hx28_1'
      (hvregs1.trans hvregs)
    rw [hsp1] at htail
    refine SepWPp.bind_false_frame htail (by sep_focus)
      fun sf P_f hpcf hrunf ⟨_, hentf, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hentf) ?_
    refine SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), ?_⟩
    exact ⟨hspf, by rw [htrf, htr1], hcsf, hvregsf, hcrof⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
