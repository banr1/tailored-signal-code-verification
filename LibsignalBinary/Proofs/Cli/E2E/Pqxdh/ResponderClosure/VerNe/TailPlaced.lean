/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Tail
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.ErrK2Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2Placed
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNeBlocks
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import all Init.Data.String.Defs

/-!
# Relocatable Version-Mismatch Error Tail (`+0x2cfc → s0.readReg64 .x30`)

Relocatable (`[LibsignalPlacement]`) proof of the version-mismatch error tail
(`(blkPl_518).base + 0x2cfc → s0.readReg64 .x30` with `errs.len = 2`) on `lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.CliHandshake.RespClosurePlaced

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-- Relocatable `[LibsignalPlacement]` Stage P3/P4 `VerNe` tail
(`(blkPl_518).base + 0x2cfc → s0.readReg64 .x30` with `errs.len = 2`) on `lsProg_518 ext`. -/
def OverVerNeTail2cfcCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State))
    (s0 s s7 : State) (coroPtr ctxPtr outPtr errsPtr prevCap prevPtr : BitVec 64)
    (msgVer0 msgVer1 : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8))),
    (lsProg_518 ext).CodeLoaded s7.mem → s7.pc = (blkPl_518).base + 0x2cfc#64 →
    s7.status = .Running → s7.sp = s.sp → (s.sp &&& 15#64 == 0#64) = true →
    s7.trace = s0.trace → s7.readReg64 .x19 = coroPtr →
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer0) ∗
       memRegion (errsPtr + 12#64) 36 ∗ ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 56#64) ↦₃₂ msgVer1) ∗ memRegion (errsPtr + 60#64) 36 ∗
       memRegion (errsPtr + 96#64) 96 ∗ A.live errsPtr 192 8 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ pqLogLevelCellPlaced ∗
       memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          pqLogLevelCellPlaced ∗
          recordResultAt A outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s7)
      (P3P4.PanicOomProp s0)

/-! ## Basic blocks (`+0x2cfc → +0x33b0`, `+0x33b4 → lsmpl.base 513`, `+0x3410` loop and exit) -/

private theorem cond_eq_adds64_of_ne_neg1_tail_pl {w : BitVec 64} (h : w ≠ 0xffffffffffffffff#64) :
    ConditionHolds CondCode.EQ (addsPState64 w 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]; revert h; bv_omega

set_option maxHeartbeats 800000 in
private theorem p3_ver_ne_2cfc_33b0_cli_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (s : State) (coroPtr retPtr savedX27 ssCap : BitVec 64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (blkPl_518).base + 0x2cfc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x33b0#64) s
      (((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗ pqLogLevelCellPlaced)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗ pqLogLevelCellPlaced) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = 17#64 ∧
        s1.readReg64 .x1 = 1#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧ s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1_tail_pl hcap_ne
  unfold pqLogLevelCellPlaced lsLogFilterAddr
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
private theorem p3_ver_ne_33b4_dropspe_cli_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr dfPtr errsPtr ro0 ro1
    u_df0 u_df8 u_270 u_278 u_280 u_288 : BitVec 64)
    (u_df10 u_290 : BitVec 8)
    (hdf_nz : dfPtr ≠ 0#64) (hpc : s.pc = (blkPl_518).base + 0x33b4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = dfPtr) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 511) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ ro0) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ ro1) ∗
       ((dfPtr + 0x0#64) ↦₆₄ u_df0) ∗ ((dfPtr + 0x8#64) ↦₆₄ u_df8) ∗
       ((dfPtr + 0x10#64) ↦₈ u_df10) ∗
       ((s.sp + 0x270#64) ↦₆₄ u_270) ∗ ((s.sp + 0x278#64) ↦₆₄ u_278) ∗
       ((s.sp + 0x280#64) ↦₆₄ u_280) ∗ ((s.sp + 0x288#64) ↦₆₄ u_288) ∗
       ((s.sp + 0x290#64) ↦₈ u_290))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ ro0) ∗
          ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ ro1) ∗
          ((dfPtr + 0x0#64) ↦₆₄ ro0) ∗ ((dfPtr + 0x8#64) ↦₆₄ ro1) ∗
          ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗ ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
          ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗
          ((s.sp + 0x290#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = errsPtr ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = errsPtr ∧
        s1.readReg64 .x22 = errsPtr ∧ s1.readReg64 .x23 = 2#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x3410#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdf_beq : (dfPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hdf_nz
  have hx0' : s.readReg64 (Reg.gpr 0#5) = dfPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 600000 in
private theorem p3_ver_ne_3410_loop_cli_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr errsPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x3410#64) (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = errsPtr)
    (hx22 : s.readReg64 .x22 = errsPtr) (hx23 : s.readReg64 .x23 = 2#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 511) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = errsPtr + 0x30#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = errsPtr + 0x30#64 ∧ s1.readReg64 .x22 = errsPtr ∧
        s1.readReg64 .x23 = 1#64 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x3410#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = errsPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = errsPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 2#64 := hx23
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
private theorem p3_ver_ne_3410_exit_cli_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr errsPtr ssCap
    v_27c v_284 v_290 v_298
    u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (blkPl_518).base + 0x3410#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = errsPtr) (hx23 : s.readReg64 .x23 = 1#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ A.live errsPtr 192 8 ∗ memRegion errsPtr 192 ∗
       A.pool ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x250#64) ↦₆₄ u_250) ∗ ((s.sp + 0x258#64) ↦₆₄ u_258) ∗
       ((s.sp + 0x260#64) ↦₃₂ u_260) ∗ ((s.sp + 0x278#64) ↦₃₂ v_278) ∗
       ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
       ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
       ((s.sp + 0x298#64) ↦₆₄ v_298) ∗ ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗ ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       ((s.sp + 0x384#64) ↦₆₄ u_384) ∗ ((s.sp + 0x38c#64) ↦₆₄ u_38c))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x250#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x258#64) ↦₆₄ v_284) ∗ ((s.sp + 0x260#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x278#64) ↦₃₂ v_278) ∗ ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x284#64) ↦₆₄ v_284) ∗ ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x290#64) ↦₆₄ v_290) ∗ ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
          ((s.sp + 0x370#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x378#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x380#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x384#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x38c#64) ↦₆₄ v_298)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = v_278.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x359c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1_tail_pl hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = errsPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0x8000000000000018#64 := hx28
  wp_steps
  wp_call hdealloc (errsPtr, 192, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-! ## Framing helpers and Part A (`+0x2cfc → +0x3410`) -/

private theorem bind_sepWP_cl_frame_tail {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpc hrun hLm hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem call_raw_nopanic_cl_tail {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      prog.CodeLoaded sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hLm R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_false] at hpost
    exact (allowPanic_not_exited hpost).elim
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

private theorem bind_sepWP_cro_frame_tail [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hL : prog.CodeLoaded s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      prog.CodeLoaded sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hcrom : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
    hcro.of_keepsFrozen hsteps.keepsFrozen
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpc hrun hcrom hLm hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem call_lscl_nopanic_tail [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hL : prog.CodeLoaded s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      prog.CodeLoaded sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [hspec]
    have h1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hcro.1, hm⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h1
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · dsimp only [withLsCodeLoaded] at _hoom_post; rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hcrom : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
      hcro.of_keepsFrozen hsteps.keepsFrozen
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hcrom hLm R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hpan_false] at hpost; exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost; rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

private theorem call_lscl_ro_nopanic_tail [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hL : prog.CodeLoaded s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl spec)))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      prog.CodeLoaded sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hpre_eq : (withLsRoLoaded lsmpl spec).pre x s = (⌜φ ∧ LibsignalRoLoaded lsmpl s.mem⌝ ∗ T) := by
    dsimp only [withLsRoLoaded]
    rw [hspec, sepConj_assoc, sepConj_comm T, ← sepConj_assoc, pure_sepConj_pure]
  exact call_lscl_nopanic_tail (spec := withLsRoLoaded lsmpl spec) (x := x)
    (φ := φ ∧ LibsignalRoLoaded lsmpl s.mem) (T := T) (F := F)
    hcro hL hcall hpc hrun hsp hlr hpre_eq ⟨hφ, hcro.2⟩ hP hpan_false hexit_false hoom_false hnext

private theorem pointsToBytesRO_decryptionFailed_tail_pl (a : BitVec 64) :
    (a ↦ᵣ decryptionFailedStr) =
      (a ↦₆₄ᵣ 0x6974707972636564#64) ∗ ((a + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
        ((a + 16#64) ↦₈ᵣ 0x64#8) := by
  have hsplit : decryptionFailedStr =
      [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8] ++
      ([0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8] ++ [0x64#8]) := by rfl_kernel
  rw [hsplit, pointsToBytesRO_append, pointsToBytesRO_append]
  change (a ↦ᵣ [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8]) ∗
    (((a + 8#64) ↦ᵣ [0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8]) ∗
     ((a + 8#64 + 8#64) ↦ᵣ [0x64#8])) = _
  rw [pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO_cons,
    pointsToBytesRO_nil, sepConj_emp, show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  simp only [BitVec.reduceAppend]

private theorem intro_lsro_decryptionFailed_tail_pl [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s
      (((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hro0 : s.mem ⊨ ((lsmpl.ρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦ᵣ decryptionFailedStr) ∗ (P ∗ R) :=
    lsro_intro_chk hcro.2 (by rfl_kernel) hm
  change s.mem ⊨ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦ᵣ decryptionFailedStr) ∗ (P ∗ R) at hro0
  rw [pointsToBytesRO_decryptionFailed_tail_pl] at hro0
  have hro1 : s.mem ⊨ (((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8) ∗ P) ∗ R := by
    simpa only [sepConj_assoc] using hro0
  exact SepWPp.drop_frame (P_drop := (lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8)
    (by ac_rfl) hwp R hro1 hL

private theorem sepWPp_add_cro_tail [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P
      (fun sf P_f => Q sf P_f ∧ StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem) Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQ⟩ | hpan⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hQ, hcro.of_keepsFrozen hsteps.keepsFrozen⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

private theorem errs48_48_96_join_tail_pl (errsPtr : BitVec 64) :
    memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 48 ∗ memRegion (errsPtr + 0x60#64) 96 =
      memRegion errsPtr 192 := by
  have h1 :
      memRegion (errsPtr + 0x30#64) 48 ∗ memRegion (errsPtr + 0x60#64) 96 =
        memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr + 0x30#64) (n := 48) (k := 96)
          (b' := errsPtr + 0x60#64) rfl (by bv_omega) (by decide)]
  rw [h1, ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144)
        (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]

private theorem p3_oom_tail_3798_tail_placed_ok [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x3798#64) (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_518 ext) ret s P Q (P3P4.PanicOomProp s0) := by
  have hp : (lsProg_518 ext).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked :=
    (ls_externAt?_of_mem (prog := lsProg_518 ext) (i := 518) (by decide)).trans hpanic
  have hstep : SepWP (lsProg_518 ext) (lsρ lsHandleErrorSym) s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.trace = s.trace) := by
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine bind_sepWP_cl_frame_tail hL hstep (emp_sepConj P).symm
    fun s1 hpc1 hrun1 _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hp) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

set_option maxHeartbeats 800000 in
private theorem p3_alloc_33b0_tail_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (F : SepProp)
    (hL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x33b0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x33b4#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ (lsProg_518 ext).CodeLoaded s2.mem)
      (P3P4.PanicOomProp s0) := by
  have hbl : SepWP (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧ s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x33b4#64) := by
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine bind_sepWP_cl_frame_tail hL hbl (emp_sepConj _).symm
    fun s1 hpc1 hrun1 hL1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hlay : LayoutOk 17 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  have hφ : (s1.readReg64 .x0).toNat = 17 ∧ (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk 17 1 :=
    ⟨by rw [hx0_1]; rfl, by rw [hx1_1]; rfl, hlay⟩
  refine call_raw_nopanic_cl_tail (spec := rustAllocSpec A) (x := (17, 1))
    (T := A.pool ∗ stackAt s.sp allocHookStack) (F := F)
    hL1 halloc hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [rustAllocSpec]; rw [hsp1])
    hφ (emp_sepConj _) (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hL2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := hcs1.trans hcs2
  dsimp only [rustAllocSpec]
  rw [hsp1]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · have hoom0 : (s2.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr2 => ?_
    have hcbz : SepWP (lsProg_518 ext) ((blkPl_518).base + 0x3798#64) s2 emp
        (fun s3 P_f => (P_f ⊢ emp) ∧ s3.sp = s2.sp ∧ s3.trace = s2.trace) := by
      have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      wp_steps
      refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        ⟨Entails.refl _, rfl, rfl⟩
    refine bind_sepWP_cl_frame_tail hL2 hcbz (emp_sepConj _).symm
      fun s3 hpc3 hrun3 hL3 ⟨_, htr3⟩ => ?_
    rw [emp_sepConj, ← sepConj_assoc]
    exact p3_oom_tail_3798_tail_placed_ok ext hpanic s0 s3 _ _ _ hL3 hpc3 hrun3
      (by rw [htr3, htr2, htr1, htr])
  · have hoom0 : (s2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
    refine SepWPp.done hpc2 hrun2
      ⟨Entails.of_eq (by ac_rfl), hoom, hsp2, htr2.trans htr1, hcs, hL2⟩

set_option maxHeartbeats 1000000 in
private theorem over_ver_ne_tail_partA_cli_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s s7 : State) (coroPtr ctxPtr outPtr errsPtr : BitVec 64)
    (msgVer0 msgVer1 : BitVec 32) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro7 : StoreKit.LibsignalCodeRoLoaded lsmpl s7.mem)
    (hL7 : (lsProg_518 ext).CodeLoaded s7.mem)
    (hpc7 : s7.pc = (blkPl_518).base + 0x2cfc#64) (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr7 : s7.trace = s0.trace) (hx19_7 : s7.readReg64 .x19 = coroPtr) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x3410#64) s7
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer0) ∗
       memRegion (errsPtr + 12#64) 36 ∗ ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 56#64) ↦₃₂ msgVer1) ∗ memRegion (errsPtr + 60#64) 36 ∗
       memRegion (errsPtr + 96#64) 96 ∗ sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
       pqLogLevelCellPlaced ∗ memRegion (s.sp + 0x270#64) 48 ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
      (fun s11 P_f =>
        (∃ dfPtr w3' w4 : BitVec 64, dfPtr ≠ 0#64 ∧ w3'.extractLsb' 0 8 = 3#8 ∧
          (P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion errsPtr 192 ∗
            A.live dfPtr 17 1 ∗ ((dfPtr + 0x0#64) ↦₆₄ 0x6974707972636564#64) ∗
            ((dfPtr + 0x8#64) ↦₆₄ 0x656c696166206e6f#64) ∗ ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
            ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗ ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
            ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗
            ((s.sp + 0x290#64) ↦₆₄ w3') ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗
            sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ pqLogLevelCellPlaced ∗
            A.pool ∗ stackAt s.sp growOneSpeStack)) ∧
        s11.sp = s.sp ∧ s11.trace = s0.trace ∧ s11.readReg64 .x19 = coroPtr ∧
        s11.readReg64 .x22 = errsPtr ∧ s11.readReg64 .x23 = 1#64 ∧
        s11.readReg64 .x24 = s.sp + 0x370#64 ∧ s11.readReg64 .x25 = s.sp + 0x210#64 ∧
        s11.readReg64 .x26 = outPtr ∧ s11.readReg64 .x27 = ctxPtr ∧
        s11.readReg64 .x28 = 0x8000000000000018#64 ∧
        calleeSavedVRegs s11 = calleeSavedVRegs s7 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s11.mem ∧ (lsProg_518 ext).CodeLoaded s11.mem)
      (P3P4.PanicOomProp s0) := by
  have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hs7_sp]; exact hsp_align
  refine P3P4.SepWPp.weaken_frame
    (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hstep7b := p3_ver_ne_2cfc_33b0_cli_placed_wp ext hshim s7 coroPtr outPtr ctxPtr recG.localIk.cap
    (cap_ne_noneCap_of_lt hcap_lt) hpc7 hrun7 hsp7_align hx19_7
  rw [hs7_sp] at hstep7b
  refine bind_sepWP_cro_frame_tail hcro7 hL7 hstep7b (by sep_focus)
    fun s7b hpc7b hrun7b hcro7b hL7b hregs7b => ?_
  rcases hregs7b with ⟨hsp7b, htr7b, hx0_7b, hx1_7b, hx19_7b, hx24_7b, hx25_7b,
    hx26_7b, hx27_7b, _, hvregs_7b⟩
  have hpack_ss7b :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG st ⊢
      sessionStateAt A (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG st hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss7b (by sep_focus) ?_
  have hstack_alloc :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp7b_align : (s7b.sp &&& 15#64 == 0#64) = true := by rw [hsp7b]; exact hsp_align
  have htr7b_0 : s7b.trace = s0.trace := htr7b.trans htr7
  have halloc17 := sepWPp_add_cro_tail hcro7b
    (p3_alloc_33b0_tail_placed_ok (A := A) ext halloc hpanic s0 s7b
      emp hL7b hpc7b hrun7b hsp7b_align htr7b_0 hx0_7b hx1_7b)
  rw [sepConj_emp, hsp7b] at halloc17
  refine SepWPp.bind_sepWPp_frame_raw
    halloc17 (by sep_focus)
    fun s8 P_m8 hpc8 hrun8 ⟨⟨hP8, hdf_ne, hsp8_7b, htr8_7b, hcs8, hL8⟩, hcro8⟩ => ?_
  rw [sepConj_emp] at hP8
  refine P3P4.SepWPp.weaken_frame hP8 (by sep_focus) ?_
  have hstack_restore8 :
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore8 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion_17_split_eq (s8.readReg64 .x0)))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_df10 => SepWPp.exists_elim fun u_df8 =>
    SepWPp.exists_elim fun u_df0 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x270#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_270 => SepWPp.exists_elim fun u_278 =>
    SepWPp.exists_elim fun u_280 => SepWPp.exists_elim fun u_288 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3))
    (by sep_focus) ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7b
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8_s]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, hx27_cs8, _, _, hvregs_cs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7b
  have hx24_8 : s8.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs8.trans hx24_7b
  have hx25_8 : s8.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs8.trans hx25_7b
  have hx26_8 : s8.readReg64 .x26 = outPtr := hx26_cs8.trans hx26_7b
  have hx27_8 : s8.readReg64 .x27 = ctxPtr := hx27_cs8.trans hx27_7b
  refine intro_lsro_decryptionFailed_tail_pl hcro8 ?_
  have hstep9 := p3_ver_ne_33b4_dropspe_cli_placed_wp ext s8 coroPtr (s8.readReg64 .x0) errsPtr
    0x6974707972636564#64 0x656c696166206e6f#64
    u_df0 u_df8 u_270 u_278 u_280 u_288 u_df10 (w3.extractLsb' 0 8)
    hdf_ne hpc8 hrun8 hsp8_align rfl hx19_8
  rw [hsp8_s] at hstep9
  refine bind_sepWP_cro_frame_tail hcro8 hL8 hstep9 (by sep_focus)
    fun s9 hpc9 hrun9 hcro9 hL9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx19_9, hx21_9, hx22_9, hx23_9,
    hx24_9, hx25_9, hx26_9, hx27_9, hx28_9, _, hx30_9, hvregs_9⟩
  refine SepWPp.drop_frame
    (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus) ?_
  have hsp9_s : s9.sp = s.sp := hsp9_8
  have hsp9_al : s9.spAligned = true := by simpa only [State.spAligned, hsp9_s] using hsp_align
  have hstack_spe :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 480 ∗ stackAt s.sp dropSpeStack :=
    stackAt_split_bottom s.sp dropSpeStack 480 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_spe) (by sep_focus) ?_
  refine call_lscl_ro_nopanic_tail
    (spec := dropSpe2VerSpec A)
    (x := (errsPtr, msgVer0))
    (φ := s9.readReg64 .x0 = errsPtr)
    (T := (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer0) ∗
          memRegion (errsPtr + 12#64) 36 ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    hcro9 hL9 (drop_spe2_ver_placed_ok_at (A := A)) hpc9 hrun9 hsp9_al hx30_9
    (by dsimp only [dropSpe2VerSpec]; rw [hsp9_s])
    hx0_9
    (by sep_focus)
    (hnext := fun s10 hpc10 hrun10 hsp10_9 _ hcs10 hcro10 hL10 => ?_)
  dsimp only [dropSpe2VerSpec]
  rw [hsp9_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr10_9 => ?_
  have hsp10_s : s10.sp = s.sp := hsp10_9.trans hsp9_s
  have hsp10_align : (s10.sp &&& 15#64 == 0#64) = true := by rw [hsp10_s]; exact hsp_align
  rcases hcs10 with ⟨hx19_cs10, _, hx21_cs10, hx22_cs10, hx23_cs10, hx24_cs10, hx25_cs10,
    hx26_cs10, hx27_cs10, hx28_cs10, _, hvregs_cs10⟩
  have hx19_10 : s10.readReg64 .x19 = coroPtr := hx19_cs10.trans hx19_9
  have hx21_10 : s10.readReg64 .x19 = coroPtr := hx19_10
  have hx21_10' : s10.readReg64 .x21 = errsPtr := hx21_cs10.trans hx21_9
  have hx22_10 : s10.readReg64 .x22 = errsPtr := hx22_cs10.trans hx22_9
  have hx23_10 : s10.readReg64 .x23 = 2#64 := hx23_cs10.trans hx23_9
  have hloop := p3_ver_ne_3410_loop_cli_placed_wp ext s10 coroPtr errsPtr
    hpc10 hrun10 hsp10_align hx19_10 hx21_10' hx22_10 hx23_10
  refine bind_sepWP_cro_frame_tail hcro10 hL10 hloop (emp_sepConj _).symm
    fun s10b hpc10b hrun10b hcro10b hL10b hregs10b => ?_
  rw [emp_sepConj]
  rcases hregs10b with ⟨hsp10b_10, htr10b_10, hx0_10b, hx19_10b, _, hx22_10b, hx23_10b,
    hx24_10b, hx25_10b, hx26_10b, hx27_10b, hx28_10b, _, hx30_10b, hvregs_10b⟩
  have hsp10b_s : s10b.sp = s.sp := hsp10b_10.trans hsp10_s
  have hsp10b_al : s10b.spAligned = true := by simpa only [State.spAligned, hsp10b_s] using hsp_align
  have herrs_off :
      ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
      ((errsPtr + 56#64) ↦₃₂ msgVer1) ∗
      memRegion (errsPtr + 60#64) 36 =
      ((errsPtr + 0x30#64) ↦₆₄ 0x8000000000000006#64) ∗
      (((errsPtr + 0x30#64) + 8#64) ↦₃₂ msgVer1) ∗
      memRegion ((errsPtr + 0x30#64) + 12#64) 36 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq herrs_off) (by sep_focus) ?_
  refine call_lscl_ro_nopanic_tail
    (spec := dropSpe2VerSpec A)
    (x := (errsPtr + 0x30#64, msgVer1))
    (φ := s10b.readReg64 .x0 = errsPtr + 0x30#64)
    (T := ((errsPtr + 0x30#64) ↦₆₄ 0x8000000000000006#64) ∗
          (((errsPtr + 0x30#64) + 8#64) ↦₃₂ msgVer1) ∗
          memRegion ((errsPtr + 0x30#64) + 12#64) 36 ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    hcro10b hL10b (drop_spe2_ver_placed_ok_at (A := A)) hpc10b hrun10b hsp10b_al hx30_10b
    (by dsimp only [dropSpe2VerSpec]; rw [hsp10b_s])
    hx0_10b
    (by sep_focus)
    (hnext := fun s11 hpc11 hrun11 hsp11_10b _ hcs11 hcro11 hL11 => ?_)
  dsimp only [dropSpe2VerSpec]
  rw [hsp10b_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr11_10b => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs48_48_96_join_tail_pl errsPtr)) (by sep_focus) ?_
  have hstack_restore11 :
      memRegion (s.sp - 4608#64) 480 ∗ stackAt s.sp dropSpeStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_spe]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore11 (by sep_focus) ?_
  rcases hcs11 with ⟨hx19_cs11, _, _, hx22_cs11, hx23_cs11, hx24_cs11, hx25_cs11,
    hx26_cs11, hx27_cs11, hx28_cs11, _, hvregs_cs11⟩
  have hsp11_s : s11.sp = s.sp := hsp11_10b.trans hsp10b_s
  have htr11_0 : s11.trace = s0.trace :=
    htr11_10b.trans (htr10b_10.trans (htr10_9.trans (htr9_8.trans (htr8_7b.trans htr7b_0))))
  have hx19_11 : s11.readReg64 .x19 = coroPtr := hx19_cs11.trans hx19_10b
  have hx22_11 : s11.readReg64 .x22 = errsPtr := hx22_cs11.trans hx22_10b
  have hx23_11 : s11.readReg64 .x23 = 1#64 := hx23_cs11.trans hx23_10b
  have hx24_11 : s11.readReg64 .x24 = s.sp + 0x370#64 :=
    hx24_cs11.trans (hx24_10b.trans (hx24_cs10.trans (hx24_9.trans hx24_8)))
  have hx25_11 : s11.readReg64 .x25 = s.sp + 0x210#64 :=
    hx25_cs11.trans (hx25_10b.trans (hx25_cs10.trans (hx25_9.trans hx25_8)))
  have hx26_11 : s11.readReg64 .x26 = outPtr :=
    hx26_cs11.trans (hx26_10b.trans (hx26_cs10.trans (hx26_9.trans hx26_8)))
  have hx27_11 : s11.readReg64 .x27 = ctxPtr :=
    hx27_cs11.trans (hx27_10b.trans (hx27_cs10.trans (hx27_9.trans hx27_8)))
  have hx28_11 : s11.readReg64 .x28 = 0x8000000000000018#64 :=
    hx28_cs11.trans (hx28_10b.trans (hx28_cs10.trans hx28_9))
  have hvregs_11_7 : calleeSavedVRegs s11 = calleeSavedVRegs s7 := by
    rw [hvregs_cs11, hvregs_10b, hvregs_cs10, hvregs_9, hvregs_cs8, hvregs_7b]
  refine SepWPp.done hpc11 hrun11 ?_
  refine ⟨⟨s8.readReg64 .x0, w3', w4, hdf_ne, hw3'_head, Entails.of_eq (by ac_rfl)⟩,
    hsp11_s, htr11_0, hx19_11, hx22_11, hx23_11, hx24_11, hx25_11, hx26_11, hx27_11, hx28_11,
    hvregs_11_7, hcro11, hL11⟩

/-! ## Part B (`+0x3410 → s0.readReg64 .x30`) and combined tail theorem -/

/-- Pointwise (`A`, `ext`) body of `OverK2SegCliPlacedStmt`. -/
def OverK2SegCliPlacedAt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (s : State) (coroPtr outPtr errTag prevCap prevPtr
      w_370 w_378 w_380 w_388
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8)),
    s.pc = (blkPl_518).base + 0x359c#64 →
    s.status = .Running →
    (s.sp &&& 15#64 == 0#64) = true →
    s.readReg64 .x19 = coroPtr →
    s.readReg64 .x22 = w_22.zeroExtend 64 →
    s.readReg64 .x25 = s.sp + 0x210#64 →
    s.readReg64 .x26 = outPtr →
    s.readReg64 .x28 = errTag →
    SepWP (lsProg_518 ext) retAddr s
      (prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
          A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
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
        calleeSavedVRegs s1 = calleeSavedVRegs s)

set_option maxHeartbeats 1000000 in
private theorem over_ver_ne_tail_partB_cli_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hK2 : OverK2SegCliPlacedAt A ext)
    (s0 s s11 : State) (coroPtr outPtr errsPtr prevCap prevPtr dfPtr w3' w4 : BitVec 64)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hdf_ne : dfPtr ≠ 0#64) (hw3'_head : w3'.extractLsb' 0 8 = 3#8)
    (hcro11 : StoreKit.LibsignalCodeRoLoaded lsmpl s11.mem)
    (hL11 : (lsProg_518 ext).CodeLoaded s11.mem)
    (hpc11 : s11.pc = (blkPl_518).base + 0x3410#64) (hrun11 : s11.status = .Running)
    (hs11_sp : s11.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr11 : s11.trace = s0.trace) (hx19_11 : s11.readReg64 .x19 = coroPtr)
    (hx22_11 : s11.readReg64 .x22 = errsPtr) (hx23_11 : s11.readReg64 .x23 = 1#64)
    (hx24_11 : s11.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_11 : s11.readReg64 .x25 = s.sp + 0x210#64) (hx26_11 : s11.readReg64 .x26 = outPtr)
    (hx28_11 : s11.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s11
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ A.live errsPtr 192 8 ∗ memRegion errsPtr 192 ∗
       A.live dfPtr 17 1 ∗ ((dfPtr + 0x0#64) ↦₆₄ 0x6974707972636564#64) ∗
       ((dfPtr + 0x8#64) ↦₆₄ 0x656c696166206e6f#64) ∗ ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗ ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
       ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗
       ((s.sp + 0x290#64) ↦₆₄ w3') ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          recordResultAt A outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s11)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr dfPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) 17#64 dfPtr 17#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  have hstack_alloc :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp11_align : (s11.sp &&& 15#64 == 0#64) = true := by rw [hs11_sp]; exact hsp_align
  have hx24_11' : s11.readReg64 .x24 = s11.sp + 0x370#64 := by rw [hx24_11, hs11_sp]
  have hx25_11' : s11.readReg64 .x25 = s11.sp + 0x210#64 := by rw [hx25_11, hs11_sp]
  have hstep12 := p3_ver_ne_3410_exit_cli_placed_wp ext hdealloc s11 coroPtr errsPtr recG.localIk.cap
    (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)
    w3' w4 u_250 u_258 u_370 u_378 u_384 u_38c
    ((17#64 : BitVec 64).extractLsb' 0 32) ((17#64 : BitVec 64).extractLsb' 32 32)
    u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc11 hrun11 hsp11_align
    hx19_11 hx22_11 hx23_11 hx24_11' hx25_11' hx28_11
  rw [hs11_sp] at hstep12
  refine bind_sepWP_cro_frame_tail hcro11 hL11 hstep12 (by sep_focus)
    fun s12 hpc12 hrun12 hcro12 hL12 hregs12 => ?_
  rcases hregs12 with ⟨hsp12_11, htr12_11, hx0_12, hx19_12, hx22_12, _, hx25_12,
    hx26_12, _, hx28_12, _, hx30_12, hvregs_12⟩
  have hstack_restore8 :
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore8 (by sep_focus) ?_
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG st ⊢
      sessionStateAt A (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG st hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (words6_entails_memRegion48 (s.sp + 0x270#64)
      0x8000000000000018#64 17#64 dfPtr 17#64 w3' w4)
    (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄
        (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄
        ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ (17#64 : BitVec 64).extractLsb' 32 32) ⊢
      memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64)
        (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
        ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)
        ((17#64 : BitVec 64).extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  have hsp12_s : s12.sp = s.sp := hsp12_11
  have hsp12_al : s12.spAligned = true := by simpa only [State.spAligned, hsp12_s] using hsp_align
  refine call_lscl_nopanic_tail
    (spec := dropSessionStructureLocal2Spec A)
    (x := (⟨coroPtr + 0xf8#64, recG, st⟩ : DropSessionStructureGhost))
    (φ := s12.readReg64 .x0 = coroPtr + 0xf8#64)
    (T := sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack)
    hcro12 hL12 hDropSS3 hpc12 hrun12 hsp12_al hx30_12
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp12_s])
    hx0_12 (by sep_focus)
    (hnext := fun s13 hpc13 hrun13 hsp13_12 _ hcs13 hcro13 hL13 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp12_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr13_12 => ?_
  have hstack_k2 :
      stackAt s.sp dropSessionStructure2Stack =
        memRegion (s.sp - 4192#64) 96 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 96 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_k2) (by sep_focus) ?_
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64)
    ((17#64 : BitVec 64).extractLsb' 32 32) w3' w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (P3P4.outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ret2c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0 => ?_
  have hsp13_s : s13.sp = s.sp := hsp13_12.trans hsp12_s
  have hsp13_align : (s13.sp &&& 15#64 == 0#64) = true := by rw [hsp13_s]; exact hsp_align
  rcases hcs13 with ⟨hx19_cs13, _, _, hx22_cs13, _, _, hx25_cs13, hx26_cs13, _, hx28_cs13, _, hvregs_cs13⟩
  have hx19_13 : s13.readReg64 .x19 = coroPtr := hx19_cs13.trans hx19_12
  have hx22_13 : s13.readReg64 .x22 = ((17#64 : BitVec 64).extractLsb' 0 32).zeroExtend 64 :=
    hx22_cs13.trans hx22_12
  have hx25_13 : s13.readReg64 .x25 = s13.sp + 0x210#64 := by rw [hx25_cs13, hx25_12, hsp13_s]
  have hx26_13 : s13.readReg64 .x26 = outPtr := hx26_cs13.trans (hx26_12.trans hx26_11)
  have hx28_13 : s13.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs13.trans hx28_12
  have hk2 := hK2 s13 coroPtr outPtr 0x8000000000000018#64
    prevCap prevPtr
    (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)
    (w3'.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3'.extractLsb' 32 32)
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    ((17#64 : BitVec 64).extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0 enc
    hpc13 hrun13 hsp13_align hx19_13 hx22_13 hx25_13 hx26_13 hx28_13
  rw [hsp13_s] at hk2
  refine bind_sepWP_cro_frame_tail hcro13 hL13 hk2 (by sep_focus)
    fun sf hpcf hrunf hcrof hLf hregsf => ?_
  rcases hregsf with ⟨hspf_s, htrf_13, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregs_f⟩
  refine P3P4.SepWPp.weaken_frame
    (hdrP_coro_344_entails_368 coroPtr prevCap prevPtr 1#64) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sp370_36_err_fold s.sp
      (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
      ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)
      w3' w4 ((17#64 : BitVec 64).extractLsb' 32 32))
    (by sep_focus) ?_
  have hrepack_out1c := (repack20_32_64_64_to_64_64_32 (outPtr + 0x1c#64)
    ((17#64 : BitVec 64).extractLsb' 32 32) w3' w4).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out1c
  have hrepack_out8 := (words3_repack_w32_2w64_w32 (outPtr + 0x8#64) 17#64 dfPtr 17#64).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out8
  have hout_words :
      ((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗ ((outPtr + 0x8#64) ↦₆₄ 17#64) ∗
      ((outPtr + 0x10#64) ↦₆₄ dfPtr) ∗ ((outPtr + 0x18#64) ↦₆₄ 17#64) ∗
      ((outPtr + 0x20#64) ↦₆₄ w3') ∗ ((outPtr + 0x28#64) ↦₆₄ w4) ⊢
      words6At outPtr 0x8000000000000018#64 17#64 dfPtr 17#64 w3' w4 := by
    unfold words6At; rw [BitVec.add_zero]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame hout_words (by sep_focus) ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A
    outPtr dfPtr w3' w4 hdf_ne hw3'_head
  refine P3P4.SepWPp.weaken_frame hrec (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_k2.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2.symm) (by sep_focus) ?_
  have htrf_0 : sf.trace = s0.trace :=
    htrf_13.trans (htr13_12.trans (htr12_11.trans htr11))
  have hvregsf_11 : calleeSavedVRegs sf = calleeSavedVRegs s11 := by
    rw [hvregs_f, hvregs_cs13, hvregs_12]
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨Entails.of_eq (by ac_rfl), hspf_s, htrf_0,
    ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
    hcrof, hLf, hvregsf_11⟩

set_option maxHeartbeats 600000 in
/-- Pointwise (`A`, `ext`) `StoreKit.LibsignalCodeRoLoaded`-threaded Stage P3/P4 `VerNe` tail
(`(blkPl_518).base + 0x2cfc → s0.readReg64 .x30`) on `lsProg_518 ext`. -/
theorem over_ver_ne_tail_2cfc_cro_placed_at [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hK2 : OverK2SegCliPlacedAt A ext)
    (s0 s s7 : State) (coroPtr ctxPtr outPtr errsPtr prevCap prevPtr : BitVec 64)
    (msgVer0 msgVer1 : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro7 : StoreKit.LibsignalCodeRoLoaded lsmpl s7.mem)
    (hL7 : (lsProg_518 ext).CodeLoaded s7.mem)
    (hpc7 : s7.pc = (blkPl_518).base + 0x2cfc#64) (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr7 : s7.trace = s0.trace) (hx19_7 : s7.readReg64 .x19 = coroPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer0) ∗
       memRegion (errsPtr + 12#64) 36 ∗ ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 56#64) ↦₃₂ msgVer1) ∗ memRegion (errsPtr + 60#64) 36 ∗
       memRegion (errsPtr + 96#64) 96 ∗ A.live errsPtr 192 8 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ pqLogLevelCellPlaced ∗
       memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          pqLogLevelCellPlaced ∗
          recordResultAt A outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s7)
      (P3P4.PanicOomProp s0) := by
  have hpartA := over_ver_ne_tail_partA_cli_placed_ok ext hshim halloc hpanic
    s0 s s7 coroPtr ctxPtr outPtr errsPtr msgVer0 msgVer1 recG st
    hcro7 hL7 hpc7 hrun7 hs7_sp hsp_align htr7 hx19_7
  refine SepWPp.bind_sepWPp_frame_raw hpartA (by sep_focus)
    fun s11 P_m11 hpc11 hrun11
      ⟨⟨dfPtr, w3', w4, hdf_ne, hw3'_head, hP11⟩,
       hs11_sp, htr11, hx19_11, hx22_11, hx23_11, hx24_11, hx25_11, hx26_11, _, hx28_11,
       hvregs_11, hcro11, hL11⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP11) ?_
  have hpartB := over_ver_ne_tail_partB_cli_placed_ok ext hdealloc hDropSS3 hK2
    s0 s s11 coroPtr outPtr errsPtr prevCap prevPtr dfPtr w3' w4 b_2c0 enc recG st
    hdf_ne hw3'_head hcro11 hL11 hpc11 hrun11 hs11_sp hsp_align htr11
    hx19_11 hx22_11 hx23_11 hx24_11 hx25_11 hx26_11 hx28_11
  refine P3P4.SepWPp.ret_sepWPp_frame hpartB (by sep_focus)
    fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hLf, hvregs_f⟩ => ?_
  exact ⟨Entails.of_eq (by ac_rfl), hspf, htrf, hcc, hcrof, hLf, hvregs_f.trans hvregs_11⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
