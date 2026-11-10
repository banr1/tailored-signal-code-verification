/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNe
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymB
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2Placed
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.SessionRecordCallees
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNe
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNeBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErr
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import all Init.Data.String.Defs

/-!
# Relocatable Stage P3 Version-Mismatch Path over `prevSessionsEmptyAt`

Relocatable `[LibsignalPlacement]` and `[LibsignalFullPlacement]` counterparts of
`Matched.M3PrevVerNe` on Block `518` (`lsProg_518 (Rust.withPanics ext)`).
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

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.LibsignalTripleRatchet.Getters

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

abbrev dpClosureEntryVerPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_518).base

/-- `(blkPl_518).base + 0x1e04 → lsmpl.base 519` (`pqxdh_log_closure`) under
`[LibsignalPlacement]`. -/
theorem p3_ver_ne_1e04_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr u3e0 : BitVec 64) (msgVer u3e8 : BitVec 32)
    (hpc : s.pc = (blkPl_518).base + 7684#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx9 : s.readReg64 .x9 = msgVer.setWidth 64)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 519) s
      (((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗ ((s.sp + 0x3e8#64) ↦₃₂ u3e8))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗ ((s.sp + 0x3e8#64) ↦₃₂ msgVer)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0x3b0#64 ∧
        s1.readReg64 .x2 = 7#64 ∧ s1.readReg64 .x3 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x4 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = (blkPl_518).base + 7728#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx9' : s.readReg64 (Reg.gpr 9#5) = msgVer.setWidth 64 := hx9
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- `(blkPl_518).base + 0x1e30 → lsmpl.base 42` (`grow_one_spe`) under
`[LibsignalPlacement]`. -/
theorem p3_err_ver_b_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 7728#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 42) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0x3c8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = (blkPl_518).base + 7752#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- `(blkPl_518).base + 0x1e48 → lsmpl.base 512` (`dropSessionStructure3`) under
`[LibsignalPlacement]`. -/
theorem p3_err_ver_c_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr errsPtr errTag e1 e2 e3 e4 e5 u_c0 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 7752#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = 0#64) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ errTag) ∗ ((s.sp + 0x3e8#64) ↦₆₄ e1) ∗ ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗ ((s.sp + 0x400#64) ↦₆₄ e4) ∗ ((s.sp + 0x408#64) ↦₆₄ e5) ∗
       ((errsPtr + 0x0#64) ↦₆₄ u_e0) ∗ ((errsPtr + 0x8#64) ↦₆₄ u_e1) ∗ ((errsPtr + 0x10#64) ↦₆₄ u_e2) ∗
       ((errsPtr + 0x18#64) ↦₆₄ u_e3) ∗ ((errsPtr + 0x20#64) ↦₆₄ u_e4) ∗ ((errsPtr + 0x28#64) ↦₆₄ u_e5))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xc0#64) ↦₆₄ s.readReg64 .x27) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ errTag) ∗ ((s.sp + 0x3e8#64) ↦₆₄ e1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗ ((s.sp + 0x400#64) ↦₆₄ e4) ∗
          ((s.sp + 0x408#64) ↦₆₄ e5) ∗ ((errsPtr + 0x0#64) ↦₆₄ errTag) ∗ ((errsPtr + 0x8#64) ↦₆₄ e1) ∗
          ((errsPtr + 0x10#64) ↦₆₄ e2) ∗ ((errsPtr + 0x18#64) ↦₆₄ e3) ∗ ((errsPtr + 0x20#64) ↦₆₄ e4) ∗
          ((errsPtr + 0x28#64) ↦₆₄ e5)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 7800#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 0#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have herr0 : 0#64 * 0x30#64 + errsPtr = errsPtr := by bv_arith
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- `(blkPl_518).base + 0x1e78 → +0x33b0` under `[LibsignalPlacement]`. -/
theorem p3_err_ver_d_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimSpec)
    (s : State) (coroPtr retPtr savedX27 ssCap u_3e0 : BitVec 64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (blkPl_518).base + 7800#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (dpClosureEntryVerPlaced + 0x33b0#64) s
      (((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗ ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗ (lsLogFilterAddr ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          (lsLogFilterAddr ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = 17#64 ∧ s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧ s1.readReg64 .x26 = retPtr ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1 hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [dpClosureEntryVerPlaced, lsLogFilterAddr] at hpc ⊢
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- `(blkPl_518).base + 0x33b4 → drop_spe2` under `[LibsignalPlacement]`. -/
theorem p3_err_ver_e_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr dfPtr errsPtr ro0 ro1
    u_df0 u_df8 u_270 u_278 u_280 u_288 : BitVec 64)
    (u_df10 u_290 : BitVec 8)
    (hdf_nz : dfPtr ≠ 0#64)
    (hpc : s.pc = dpClosureEntryVerPlaced + 0x33b4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = dfPtr)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 511) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ ro0) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ ro1) ∗
       ((dfPtr + 0x0#64) ↦₆₄ u_df0) ∗ ((dfPtr + 0x8#64) ↦₆₄ u_df8) ∗
       ((dfPtr + 0x10#64) ↦₈ u_df10) ∗ ((s.sp + 0x270#64) ↦₆₄ u_270) ∗
       ((s.sp + 0x278#64) ↦₆₄ u_278) ∗ ((s.sp + 0x280#64) ↦₆₄ u_280) ∗
       ((s.sp + 0x288#64) ↦₆₄ u_288) ∗ ((s.sp + 0x290#64) ↦₈ u_290))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ ro0) ∗
          ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ ro1) ∗
          ((dfPtr + 0x0#64) ↦₆₄ ro0) ∗ ((dfPtr + 0x8#64) ↦₆₄ ro1) ∗
          ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗ ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗
          ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗ ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗
          ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗ ((s.sp + 0x290#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = errsPtr ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = errsPtr ∧ s1.readReg64 .x22 = errsPtr ∧
        s1.readReg64 .x23 = 1#64 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryVerPlaced + 0x3410#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdf_beq : (dfPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hdf_nz
  have hx0' : s.readReg64 (Reg.gpr 0#5) = dfPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [dpClosureEntryVerPlaced, lsρ] at hpc ⊢
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- `(blkPl_518).base + 0x3410 → lsmpl.base 512` under `[LibsignalPlacement]`. -/
theorem p3_err_ver_f_placed_wp [LibsignalPlacement] {A : RustAlloc} (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr errsPtr ssCap v_27c v_284 v_290 v_298 u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32) (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = dpClosureEntryVerPlaced + 0x3410#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = errsPtr) (hx22 : s.readReg64 .x22 = errsPtr) (hx23 : s.readReg64 .x23 = 1#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ A.live errsPtr 192 8 ∗ memRegion errsPtr 192 ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x250#64) ↦₆₄ u_250) ∗ ((s.sp + 0x258#64) ↦₆₄ u_258) ∗
       ((s.sp + 0x260#64) ↦₃₂ u_260) ∗ ((s.sp + 0x278#64) ↦₃₂ v_278) ∗ ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
       ((s.sp + 0x284#64) ↦₆₄ v_284) ∗ ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
       ((s.sp + 0x298#64) ↦₆₄ v_298) ∗ ((s.sp + 0x370#64) ↦₆₄ u_370) ∗ ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₃₂ u_380) ∗ ((s.sp + 0x384#64) ↦₆₄ u_384) ∗ ((s.sp + 0x38c#64) ↦₆₄ u_38c))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
          ((s.sp + 0x250#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x258#64) ↦₆₄ v_284) ∗ ((s.sp + 0x260#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x278#64) ↦₃₂ v_278) ∗ ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x290#64) ↦₆₄ v_290) ∗ ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
          ((s.sp + 0x370#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x378#64) ↦₆₄ v_284) ∗ ((s.sp + 0x380#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x384#64) ↦₆₄ v_290) ∗ ((s.sp + 0x38c#64) ↦₆₄ v_298)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = v_278.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryVerPlaced + 0x359c#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1 hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = errsPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = errsPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0x8000000000000018#64 := hx28
  dsimp only [dpClosureEntryVerPlaced] at hpc ⊢; wp_steps; wp_call hdealloc (errsPtr, 192, 8); wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

private theorem p3_err_tail_prev_zero_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr errTag prevStatesPtr w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24 savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hpc : s.pc = dpClosureEntryVerPlaced + 0x359c#64) (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr) (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (lsProg_518 ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗ ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗
       ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗ ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗ ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ w_378) ∗ ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗ ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗ ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
       ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗ ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗ ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
       ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗ ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗ ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗ ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
          ((s.sp + 0x388#64) ↦₆₄ w_388) ∗ ((s.sp + 0x390#64) ↦₃₂ w_390) ∗ ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
          ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗ ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗ ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
          ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗ ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧ s1.readReg64 .x21 = savedX21 ∧
        s1.readReg64 .x22 = savedX22 ∧ s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧ s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x28 = savedX28 ∧ s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  dsimp only [dpClosureEntryVerPlaced] at hpc; wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨by sep_frame,
    by simp_all [arm64_norm], rfl, rfl, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

private theorem mul24_eq_m3ver_placed {prevCap : BitVec 64} (_h : prevCap.toNat * 24 < 2 ^ 63) :
    24#64 * prevCap = BitVec.ofNat 64 (prevCap.toNat * 24) ∧
    prevCap * 24#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
  constructor <;> bv_omega

private theorem p3_err_tail_prev_dealloc_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr outPtr errTag prevCap prevPtr w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24 savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64) (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = dpClosureEntryVerPlaced + 0x359c#64) (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr) (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (lsProg_518 ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗ ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗
       ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗ ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗ ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ w_378) ∗ ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗ ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗ ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
       ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗ ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗ ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
       ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          A.pool ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗ ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗ ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗ ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
          ((s.sp + 0x388#64) ↦₆₄ w_388) ∗ ((s.sp + 0x390#64) ↦₃₂ w_390) ∗ ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
          ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗ ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗ ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
          ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗ ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧ s1.readReg64 .x21 = savedX21 ∧
        s1.readReg64 .x22 = savedX22 ∧ s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧ s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x28 = savedX28 ∧ s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr) := by
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  obtain ⟨hmul1, hmul2⟩ := mul24_eq_m3ver_placed hcap_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  dsimp only [dpClosureEntryVerPlaced] at hpc; wp_steps; wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8); wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨by simp only [BitVec.add_zero]; sep_frame,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Relocatable `[LibsignalPlacement]` spec for `pqxdh_log_closure` (Block `519`). -/
def pqxdhLogClosurePlacedSpec [LibsignalPlacement] : Spec Unit where
  pre := fun _ s => FromRecordCallees.lsLogOff ∗ stackAt s.sp pqxdhClosureStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ FromRecordCallees.lsLogOff ∗ stackAt s0.sp pqxdhClosureStack

private theorem stackAt_pqxdhClosure_placed (sp : BitVec 64) :
    stackAt sp pqxdhClosureStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 432#64) ↦₆₄ v0) ∗ ((sp - 424#64) ↦₆₄ v1) ∗
        ((sp - 416#64) ↦₆₄ v2) ∗ ((sp - 408#64) ↦₆₄ v3)) ∗
      stackAt (sp - 96#64) 304 ∗
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗ ((sp - 80#64) ↦₆₄ w2) ∗
        ((sp - 72#64) ↦₆₄ w3) ∗ ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
        ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗ ((sp - 32#64) ↦₆₄ w8) ∗
        ((sp - 24#64) ↦₆₄ w9) ∗ ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 336 12 (by decide)
  have h2 := stackAt_split_bottom (sp - 96#64) 304 32 (by decide)
  have hsub : (sp - 96#64) - BitVec.ofNat 64 (304 + 32) = sp - 432#64 := by
    rw [BitVec.sub_sub]; rfl
  rw [hsub, show (32 : Nat) = 8 * 4 by rfl,
      ProofLib.memRegion_cells (sp - 432#64) 4 (by decide)] at h2
  change stackAt sp pqxdhClosureStack = stackAt (sp - 96#64) 336 ∗ cells (sp - 96#64) 12 at h1
  have hc4 : cells (sp - 432#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 432#64) ↦₆₄ v0) ∗ ((sp - 424#64) ↦₆₄ v1) ∗
        ((sp - 416#64) ↦₆₄ v2) ∗ ((sp - 408#64) ↦₆₄ v3)) := by
    cells_unfold
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗ ((sp - 80#64) ↦₆₄ w2) ∗
        ((sp - 72#64) ↦₆₄ w3) ∗ ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
        ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗ ((sp - 32#64) ↦₆₄ w8) ∗
        ((sp - 24#64) ↦₆₄ w9) ∗ ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11)) := by
    cells_unfold
  rw [h1, h2, hc4, hc12, sepConj_assoc]

/-- Block `519` (`pqxdhLogClosurePlacedSpec`) verified under `[LibsignalFullPlacement]`. -/
theorem pqxdh_log_closure_placed_ok [LibsignalFullPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok
      ((CryptoVerification.CliHandshake.Placed.blkPC_519).rebase
        (CryptoVerification.CliHandshake.Placed.blkPl_519).base H)
      (CryptoVerification.CliHandshake.Placed.blkPl_519).base
      pqxdhLogClosurePlacedSpec := by
  unfold pqxdhLogClosurePlacedSpec FromRecordCallees.lsLogOff lsLogFilterAddr
  simp only [stackAt_pqxdhClosure_placed, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  wp_steps
  wp_done

private theorem lscro_of_steps_ver [LibsignalPlacement] {prog : Program} {s sm : State}
    (hsteps : Steps prog s sm) (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
  hcro.of_keepsFrozen hsteps.keepsFrozen

private theorem bind_sepWP_lscro_frame_ver [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim hoom | exact (not_satisfies_false_sepConj hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpcm hrunm (lscro_of_steps_ver hsteps hcro) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem call_raw_nopanic_ver [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right; · rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (lscro_of_steps_ver hsteps hcro) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_false] at hpost; exact (allowPanic_not_exited hpost).elim
  · rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

private theorem call_lscl_nopanic_ver [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  refine call_raw_nopanic_ver (spec := withLsCodeLoaded lsmpl spec) (x := x)
    (φ := φ ∧ LibsignalCodeLoaded lsmpl s.mem) (T := T) (F := F)
    hcro hcall hpc hrun hsp hlr
    (by dsimp only [withLsCodeLoaded]; rw [hspec, sepConj_assoc, sepConj_comm T, ← sepConj_assoc, pure_sepConj_pure])
    ⟨hφ, hcro.1⟩ hP hpan_false hexit_false hnext hoom_false

private theorem call_lscl_ro_nopanic_ver [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl spec)))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  have hpre_eq : (withLsRoLoaded lsmpl spec).pre x s = (⌜φ ∧ LibsignalRoLoaded lsmpl s.mem⌝ ∗ T) := by
    dsimp only [withLsRoLoaded]
    rw [hspec, sepConj_assoc, sepConj_comm T, ← sepConj_assoc, pure_sepConj_pure]
  exact call_lscl_nopanic_ver (spec := withLsRoLoaded lsmpl spec) (x := x)
    (φ := φ ∧ LibsignalRoLoaded lsmpl s.mem) (T := T) (F := F)
    hcro hcall hpc hrun hsp hlr hpre_eq ⟨hφ, hcro.2⟩ hP hpan_false hexit_false hnext hoom_false

private theorem call_lscl_oom_ver [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_oom : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (P3P4.PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (P3P4.PanicOomProp s0) := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro.1, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right; · dsimp only [withLsCodeLoaded] at hoom_post; rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim
  · dsimp only [withLsCodeLoaded] at hpost; rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (lscro_of_steps_ver hsteps hcro) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hpan_oom, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm, _, hpost,
      allowPanic_oom_of_prefix (F := F) (htr ▸ List.prefix_refl _)⟩)⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

private theorem pointsToBytesRO_decryptionFailed_ver (a : BitVec 64) :
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
  rw [pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO8_eq_pointsTo64RO,
    pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp, show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  simp only [BitVec.reduceAppend, sepConj_assoc]

private theorem intro_lsro_decryptionFailed_ver [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s
      (((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P)
      Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hro0 : s.mem ⊨ ((lsmpl.ρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦ᵣ decryptionFailedStr) ∗ (P ∗ R) :=
    lsro_intro_chk hcro.2 (by rfl_kernel) hm
  change s.mem ⊨ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦ᵣ decryptionFailedStr) ∗ (P ∗ R) at hro0
  rw [pointsToBytesRO_decryptionFailed_ver] at hro0
  have hro1 :
      s.mem ⊨
        (((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
         ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
         ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8) ∗ P) ∗ R := by
    simpa only [sepConj_assoc] using hro0
  exact SepWPp.drop_frame
    (P_all := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
              ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
              ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8) ∗ P)
    (P_drop := (lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8)
    (by ac_rfl) hwp R hro1 hL

open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux

set_option maxHeartbeats 1200000 in
/-- General-`prevCap` common error epilogue (`lsmpl.base 512 → s0.readReg64 .x30`) under `[LibsignalPlacement]`. -/
theorem stageP3_err_tail_common_prevEmpty_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State) (coroPtr outPtr errTag w0 w1 w2 w3 w4 : BitVec 64) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = lsmpl.base 512) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 = dpClosureEntryVerPlaced + 0x359c#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ prevSessionsEmptyAt A coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢ memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr errTag w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  refine call_lscl_nopanic_ver (x := (⟨coroPtr + 0xf8#64, recG, recSt⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hcro hDropSS3 hpc hrun hsp_al hx30 (by dsimp only [dropSessionStructureLocal2Spec]) hx0 (by sep_focus)
    (hnext := fun s1 hpc1 hrun1 hsp1_s _ hcs1 hcro1 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1_s => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  rcases hcs1 with ⟨hx19_cs1, _, _, hx22_cs1, _, _, hx25_cs1, hx26_cs1, _, hx28_cs1, _, hvregs_cs1⟩
  have hx19_1 : s1.readReg64 .x19 = coroPtr := hx19_cs1.trans hx19
  have hx22_1 : s1.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64 := hx22_cs1.trans hx22
  have hx25_1 : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_cs1, hx25, hsp1_s]
  have hx26_1 : s1.readReg64 .x26 = outPtr := hx26_cs1.trans hx26
  have hx28_1 : s1.readReg64 .x28 = errTag := hx28_cs1.trans hx28
  refine P3P4.SepWPp.weaken_frame (prevSessionsEmptyAt_unpack A coroPtr g) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝)
    (P₂ := ⌜g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64) (w2.extractLsb' 32 32) w3 w4
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
  have hrepack_out1c := (repack20_32_64_64_to_64_64_32 (outPtr + 0x1c#64)
    (w2.extractLsb' 32 32) w3 w4).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out1c
  have hrepack_out8 := (words3_repack_w32_2w64_w32 (outPtr + 0x8#64) w0 w1 w2).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out8
  have hout_words :
      ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₆₄ w0) ∗
      ((outPtr + 0x10#64) ↦₆₄ w1) ∗ ((outPtr + 0x18#64) ↦₆₄ w2) ∗
      ((outPtr + 0x20#64) ↦₆₄ w3) ∗ ((outPtr + 0x28#64) ↦₆₄ w4) ⊢
      words6At outPtr errTag w0 w1 w2 w3 w4 := by
    unfold words6At; rw [BitVec.add_zero]; exact Entails.refl _
  by_cases hcap : g.prevCap = 0#64
  · simp only [hcap, ↓reduceIte, emp_sepConj, sepConj_emp]
    have hstep2 := p3_err_tail_prev_zero_placed_wp ext s1 coroPtr outPtr errTag g.prevPtr
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hpc1 hrun1 hsp1_align hx19_1 hx22_1 hx25_1 hx26_1 hx28_1
    rw [hsp1_s] at hstep2
    refine bind_sepWP_lscro_frame_ver hcro1 hstep2 (by sep_focus)
      fun sf hpcf hrunf hcrof hregsf => ?_
    rcases hregsf with ⟨hspf_s, htrf_1, hvregs_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine P3P4.SepWPp.weaken_frame (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (sp370_36_err_fold s.sp
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        w3 w4 (w2.extractLsb' 32 32))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hout_words (by sep_focus) ?_
    exact SepWPp.done hpcf hrunf ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
      hspf_s, htrf_1.trans (htr1_s.trans htr),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hcrof, hvregs_f.trans hvregs_cs1⟩
  · simp only [hcap, ↓reduceIte]
    have hstack_alloc :
        stackAt s.sp dropSessionStructure2Stack =
          memRegion (s.sp - 4192#64) 96 ∗ stackAt s.sp allocHookStack :=
      stackAt_split_bottom s.sp allocHookStack 96 (by decide)
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
    have hstep2 := p3_err_tail_prev_dealloc_placed_wp ext hdealloc s1 coroPtr outPtr errTag
      g.prevCap g.prevPtr
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hcap hprev_lt hpc1 hrun1 hsp1_align hx19_1 hx22_1 hx25_1 hx26_1 hx28_1
    rw [hsp1_s] at hstep2
    refine bind_sepWP_lscro_frame_ver hcro1 hstep2 (by sep_focus)
      fun sf hpcf hrunf hcrof hregsf => ?_
    rcases hregsf with ⟨hspf_s, htrf_1, hvregs_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (sp370_36_err_fold s.sp
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        w3 w4 (w2.extractLsb' 32 32))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hout_words (by sep_focus) ?_
    exact SepWPp.done hpcf hrunf ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
      hspf_s, htrf_1.trans (htr1_s.trans htr),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hcrof, hvregs_f.trans hvregs_cs1⟩

def stageP3ErrPostPrevEmptyM3Placed [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr : BitVec 64) (e : SignalProtocolError) : SepProp :=
  (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
    ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
    ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  FromRecordCallees.lsLogOff ∗
  recordResultAt A outPtr (.error (SessionState.recordError .preKey e)) ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

set_option maxHeartbeats 800000 in
private theorem p3_alloc_33b0_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (F : SepProp)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryVerPlaced + 0x33b0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) (dpClosureEntryVerPlaced + 0x33b4#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      (P3P4.PanicOomProp s0) := by
  have hbl : SepWP (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧ s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧ s1.readReg64 .x30 = dpClosureEntryVerPlaced + 0x33b4#64) := by
    dsimp only [dpClosureEntryVerPlaced] at hpc ⊢; wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl, by simp_all [arm64_norm], by simp_all [arm64_norm],
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp_all [arm64_norm]⟩
  refine bind_sepWP_lscro_frame_ver hcro hbl (emp_sepConj _).symm
    fun s1 hpc1 hrun1 hcro1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hφ : (s1.readReg64 .x0).toNat = 17 ∧ (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk 17 1 :=
    ⟨by rw [hx0_1]; rfl, by rw [hx1_1]; rfl, by decide, ⟨0, rfl⟩, by decide⟩
  refine call_raw_nopanic_ver (spec := rustAllocSpec A) (x := (17, 1))
    (T := A.pool ∗ stackAt s.sp allocHookStack) (F := F)
    hcro1 halloc hpc1 hrun1 hsp1_al hlr1 (by dsimp only [rustAllocSpec]; rw [hsp1]) hφ (emp_sepConj _)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := hcs1.trans hcs2
  dsimp only [rustAllocSpec]; rw [hsp1]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · have hoom0 : (s2.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr2 => ?_
    have hoom_steps : SepWP (lsProg_518 ext) (lsρ lsHandleErrorSym) s2 emp
        (fun s3 P_f => (P_f ⊢ emp) ∧ s3.trace = s2.trace) := by
      have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      dsimp only [lsHandleErrorSym, dpClosureEntryVerPlaced] at hpc2 ⊢
      wp_steps
      exact SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
    refine bind_sepWP_lscro_frame_ver hcro2 hoom_steps (emp_sepConj _).symm
      fun s3 hpc3 hrun3 _ htr3 => ?_
    have hext : (lsProg_518 ext).externAt? s3.pc = some Rust.panicked := by
      rw [hpc3]; exact (ls_externAt?_of_mem (prog := lsProg_518 ext) (i := 518) (by decide)).trans hpanic
    exact SepWPp.panic hrun3 hext fun R hm =>
      allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq
        (by simp only [Rust.panicked, htr3, htr2, htr1, htr])) hm
  · have hoom0 : (s2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
    exact SepWPp.done hpc2 hrun2 ⟨Entails.of_eq (by ac_rfl), hoom, hsp2, htr2.trans htr1, hcs, hcro2⟩

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` Stage P3 version-mismatch tail (`+0x33b0 → exit`). -/
theorem stageP3_err_ver_tail_prevEmpty_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s s7 : State) (coroPtr outPtr errsPtr : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro7 : StoreKit.LibsignalCodeRoLoaded lsmpl s7.mem)
    (hpc7 : s7.pc = dpClosureEntryVerPlaced + 0x33b0#64) (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr7 : s7.trace = s0.trace) (hx0_7 : s7.readReg64 .x0 = 17#64)
    (hx1_7 : s7.readReg64 .x1 = 1#64) (hx19_7 : s7.readReg64 .x19 = coroPtr)
    (hx24_7 : s7.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_7 : s7.readReg64 .x25 = s.sp + 0x210#64) (hx26_7 : s7.readReg64 .x26 = outPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
       memRegion (errsPtr + 12#64) 36 ∗ memRegion (errsPtr + 48#64) 144 ∗ A.live errsPtr 192 8 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ prevSessionsEmptyAt A coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          recordResultAt A outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s7)
      (P3P4.PanicOomProp s0) := by
  have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hs7_sp]; exact hsp_align
  have hstack_alloc : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have halloc17 := p3_alloc_33b0_placed_ok ext halloc hpanic s0 s7 emp
    hcro7 hpc7 hrun7 hsp7_align htr7 hx0_7 hx1_7
  rw [sepConj_emp, hs7_sp] at halloc17
  refine SepWPp.bind_sepWPp_frame_raw halloc17 (by sep_focus)
    fun s8 P_m8 hpc8 hrun8 ⟨hP8, hdf_ne, hsp8_7, htr8_7, hcs8, hcro8⟩ => ?_
  rw [sepConj_emp] at hP8
  refine P3P4.SepWPp.weaken_frame hP8 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion_17_split_eq (s8.readReg64 .x0))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_df10 => SepWPp.exists_elim fun u_df8 => SepWPp.exists_elim fun u_df0 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x270#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_270 => SepWPp.exists_elim fun u_278 =>
    SepWPp.exists_elim fun u_280 => SepWPp.exists_elim fun u_288 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8_s]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, _, _, hvregs_cs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx24_8 : s8.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs8.trans hx24_7
  have hx25_8 : s8.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs8.trans hx25_7
  have hx26_8 : s8.readReg64 .x26 = outPtr := hx26_cs8.trans hx26_7
  refine intro_lsro_decryptionFailed_ver hcro8 ?_
  have hstep9 := p3_err_ver_e_placed_wp ext s8 coroPtr (s8.readReg64 .x0) errsPtr
    0x6974707972636564#64 0x656c696166206e6f#64 u_df0 u_df8 u_270 u_278 u_280 u_288 u_df10
    (w3.extractLsb' 0 8) hdf_ne hpc8 hrun8 hsp8_align rfl hx19_8
  rw [hsp8_s] at hstep9
  refine bind_sepWP_lscro_frame_ver hcro8 hstep9 (by sep_focus) fun s9 hpc9 hrun9 hcro9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx19_9, hx21_9, hx22_9, hx23_9,
    hx24_9, hx25_9, hx26_9, _, hx28_9, _, hx30_9, hvregs_9⟩
  refine SepWPp.drop_frame
    (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s8.readReg64 .x0))) (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus) ?_
  have hsp9_s : s9.sp = s.sp := hsp9_8
  have hsp9_al : s9.spAligned = true := by simpa only [State.spAligned, hsp9_s] using hsp_align
  have hstack_spe : stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 480 ∗ stackAt s.sp dropSpeStack :=
    stackAt_split_bottom s.sp dropSpeStack 480 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_spe) (by sep_focus) ?_
  refine call_lscl_ro_nopanic_ver (spec := dropSpe2VerSpec A) (x := (errsPtr, msgVer))
    (φ := s9.readReg64 .x0 = errsPtr)
    (T := (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
          memRegion (errsPtr + 12#64) 36 ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    hcro9 (drop_spe2_ver_placed_ok_at (A := A)) hpc9 hrun9 hsp9_al hx30_9
    (by dsimp only [dropSpe2VerSpec]; rw [hsp9_s]) hx0_9 (by sep_focus)
    (hnext := fun s10 hpc10 hrun10 hsp10_9 _ hcs10 hcro10 => ?_)
  dsimp only [dropSpe2VerSpec]; rw [hsp9_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr10_9 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs48_144_join errsPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_spe.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) 17#64 (s8.readReg64 .x0) 17#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun u_250 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp10_s : s10.sp = s.sp := hsp10_9.trans hsp9_s
  have hsp10_align : (s10.sp &&& 15#64 == 0#64) = true := by rw [hsp10_s]; exact hsp_align
  rcases hcs10 with ⟨hx19_cs10, _, hx21_cs10, hx22_cs10, hx23_cs10, hx24_cs10, hx25_cs10,
    hx26_cs10, _, hx28_cs10, _, hvregs_cs10⟩
  have hstep11 := p3_err_ver_f_placed_wp ext hdealloc s10 coroPtr errsPtr recG.localIk.cap
    ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)
    w3' w4 u_250 u_258 u_370 u_378 u_384 u_38c
    ((17#64 : BitVec 64).extractLsb' 0 32) ((17#64 : BitVec 64).extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc10 hrun10 hsp10_align
    (hx19_cs10.trans hx19_9) (hx21_cs10.trans hx21_9) (hx22_cs10.trans hx22_9)
    (hx23_cs10.trans hx23_9) (by rw [hx24_cs10, hx24_9, hx24_8, hsp10_s])
    (by rw [hx25_cs10, hx25_9, hx25_8, hsp10_s]) (hx28_cs10.trans hx28_9)
  rw [hsp10_s] at hstep11
  refine bind_sepWP_lscro_frame_ver hcro10 hstep11 (by sep_focus) fun s11 hpc11 hrun11 hcro11 hregs11 => ?_
  rcases hregs11 with ⟨hsp11_10, htr11_10, hx0_11, hx19_11, hx22_11, _, hx25_11,
    hx26_11, _, hx28_11, _, hx30_11, hvregs_11⟩
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG st ⊢ sessionStateAt A (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG st hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000018#64 17#64 (s8.readReg64 .x0) 17#64 w3' w4)
    (by sep_focus) ?_
  have hfold250 : ((s.sp + 0x250#64) ↦₆₄ ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ (17#64 : BitVec 64).extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion20_fold (s.sp + 0x250#64)
      ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
      ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)
      ((17#64 : BitVec 64).extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hstack_drop2 : stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  have hsp11_align : (s11.sp &&& 15#64 == 0#64) = true := by rw [hsp11_10]; exact hsp_align
  have hcommon := stageP3_err_tail_common_prevEmpty_placed_ok ext hdealloc hDropSS3
    s0 s11 coroPtr outPtr 0x8000000000000018#64 17#64 (s8.readReg64 .x0) 17#64 w3' w4 b_2c0 g recG st
    hcro11 hpc11 hrun11 hsp11_align (htr11_10.trans (htr10_9.trans (htr9_8.trans (htr8_7.trans htr7))))
    hx0_11 hx19_11 hx22_11 (by rw [hx25_11, hsp11_10]) (hx26_11.trans (hx26_cs10.trans (hx26_9.trans hx26_8)))
    hx28_11 hx30_11
  rw [hsp11_10] at hcommon
  refine P3P4.SepWPp.ret_sepWPp_frame hcommon (by sep_focus)
    fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A
    outPtr (s8.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  refine ⟨?_, hspf, htrf, hcc, hcrof, by rw [hvregs_f, hvregs_11, hvregs_cs10, hvregs_9, hvregs_cs8]⟩
  refine Entails.trans (entails_replace_sub hrec (by sep_focus) rfl) ?_
  exact entails_replace_sub (Entails.of_eq hstack_drop2.symm) (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` Stage P3 version-mismatch path
(`(blkPl_518).base + 0x1e04 → s0.readReg64 .x30`) over general `prevSessionsEmptyAt A coroPtr g`. -/
theorem stageP3_ver_ne_prevEmpty_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec A)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hLogClosure : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 7684#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace) (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr) (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ prevSessionsEmptyAt A coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (P3P4.PanicOomProp s0) := by
  unfold stageP3ErrPostPrevEmptyM3Placed; dsimp only [SessionState.recordError]
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hs1_sp]; exact hsp_align
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x3e0#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u3e0 => SepWPp.exists_elim fun u3e8_w =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo64_split_sp3e8 s.sp u3e8_w)) (by sep_focus) ?_
  have hstep1 := p3_ver_ne_1e04_placed_wp ext s1 coroPtr u3e0 msgVer
    (u3e8_w.extractLsb' 0 32) hpc1 hrun1 hsp1_align hx9_1 hx19_1
  rw [hs1_sp] at hstep1
  refine bind_sepWP_lscro_frame_ver hcro1 hstep1 (by sep_focus) fun s2 hpc2 hrun2 hcro2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, _, _, _, _, hx19_2, hx24_2, hx27_2, _, hx30_2, hvregs_2⟩
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_1] using hsp_align
  have hstack_log : stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_lscl_nopanic_ver (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := FromRecordCallees.lsLogOff ∗ stackAt s.sp pqxdhClosureStack)
    hcro2 hLogClosure hpc2 hrun2 hsp2_al hx30_2
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_1, pure_true, emp_sepConj]) trivial (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 _ hcs3 hcro3 => ?_)
  dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr3_2 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log.symm) (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2.trans hsp2_1
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  rcases hcs3 with ⟨hx19_cs3, _, _, _, _, hx24_cs3, _, _, hx27_cs3, _, _, hvregs_cs3⟩
  have hstep3 := p3_err_ver_b_placed_wp ext s3 coroPtr hpc3 hrun3 hsp3_align (hx19_cs3.trans hx19_2)
  rw [hsp3_s] at hstep3
  refine bind_sepWP_lscro_frame_ver hcro3 hstep3 (by sep_focus) fun s4 hpc4 hrun4 hcro4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_3, htr4_3, hx0_4, hx19_4, hx21_4, hx24_4, hx27_4, _, hx30_4, hvregs_4⟩
  have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_3] using hsp_align
  have htr4_0 : s4.trace = s0.trace := htr4_3.trans (htr3_2.trans (htr2_1.trans htr1))
  refine call_lscl_oom_ver (spec := growOneSpeSpec A)
    (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8)))) (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
    hcro4 htr4_0 hGrow hpc4 hrun4 hsp4_al hx30_4
    (by rw [growOneSpe_pre_zero_eq A s4 (s.sp + 0x3c8#64) initErrsPtr hx0_4 hinit_ne, hsp4_3,
          pure_true, emp_sepConj]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus) (hnext := fun s5 hpc5 hrun5 hsp5_4 _ hcs5 hcro5 => ?_)
  rw [growOneSpe_post_zero_eq A s4 s5 (s.sp + 0x3c8#64) initErrsPtr, hsp4_3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => SepWPp.pure_elim fun htr5_4 => SepWPp.pure_elim fun _ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo32_pair_sp3e8 s.sp msgVer (u3e8_w.extractLsb' 32 32))) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs192_split_eq errsPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_3
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, _, hx24_cs5, _, _, hx27_cs5, _, _, hvregs_cs5⟩
  have hx27_5 : s5.readReg64 .x27 = ctxPtr :=
    hx27_cs5.trans (hx27_4.trans (hx27_cs3.trans (hx27_2.trans hx27_1)))
  have hstep5 := p3_err_ver_c_placed_wp ext s5 coroPtr errsPtr 0x8000000000000006#64
    (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5 ctxPtr u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc5 hrun5 hsp5_align (hx19_cs5.trans hx19_4) (hx21_cs5.trans hx21_4)
    (by rw [hx24_cs5, hx24_4, hx24_cs3, hx24_2, hx24_1, hsp5_s])
  rw [hsp5_s, hx27_5] at hstep5
  refine bind_sepWP_lscro_frame_ver hcro5 hstep5 (by sep_focus) fun s6 hpc6 hrun6 hcro6 hregs6 => ?_
  rcases hregs6 with ⟨hsp6_5, htr6_5, hx0_6, hx19_6, _, _, _, hx30_6, hvregs_6⟩
  refine P3P4.SepWPp.weaken_frame (errs48_fold_ver errsPtr e2 e3 e4 e5 msgVer (u3e8_w.extractLsb' 32 32)) (by sep_focus) ?_
  have hsp6_al : s6.spAligned = true := by simpa only [State.spAligned, hsp6_5] using hsp_align
  have hstack_drop2 : stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_lscl_nopanic_ver (x := (⟨s.sp + 0xa90#64, G₁, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hcro6 hDropSS3 hpc6 hrun6 hsp6_al hx30_6
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_5]) hx0_6 (by sep_focus)
    (hnext := fun s6b hpc6b hrun6b hsp6b_6 _ hcs6b hcro6b => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_5, sepConj_assoc]
  refine SepWPp.pure_elim fun htr6b_6 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hlog_eq : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp6b_s : s6b.sp = s.sp := hsp6b_6.trans hsp6_5
  have hsp6b_align : (s6b.sp &&& 15#64 == 0#64) = true := by rw [hsp6b_s]; exact hsp_align
  rcases hcs6b with ⟨hx19_cs6b, _, _, _, _, _, _, _, _, _, _, hvregs_cs6b⟩
  have hprev_f0 : prevSessionsEmptyAt A coroPtr g =
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      (((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
       vecBuf A 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr []) := by
    unfold prevSessionsEmptyAt vecAt vecHeader; dsimp only [List.length_nil]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hprev_f0) (by sep_focus) ?_
  simp only [sepConj_assoc]
  have hstep7 := p3_err_ver_d_placed_wp ext hshim s6b coroPtr outPtr ctxPtr recG.localIk.cap
    0x8000000000000006#64 (cap_ne_noneCap_of_lt hcap_lt) hpc6b hrun6b hsp6b_align (hx19_cs6b.trans hx19_6)
  rw [hsp6b_s] at hstep7
  refine bind_sepWP_lscro_frame_ver hcro6b hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6b, htr7_6b, hx0_7, hx1_7, hx19_7, hx24_7, hx25_7, hx26_7, _, _, hvregs_7⟩
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hprev_f0.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG st ⊢ sessionStateAt A (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG st hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  have hfold3e0_48 : ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      ((s.sp + 0x3e8#64) ↦₆₄ (u3e8_w.extractLsb' 32 32 ++ msgVer)) ∗ ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗
      ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗ ((s.sp + 0x400#64) ↦₆₄ e4) ∗ ((s.sp + 0x408#64) ↦₆₄ e5) ⊢
      memRegion (s.sp + 0x3e0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using words6_entails_memRegion48 (s.sp + 0x3e0#64)
      0xffffffffffffffff#64 (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5
  refine P3P4.SepWPp.weaken_frame hfold3e0_48 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp).symm) (by sep_focus) ?_
  have htail := stageP3_err_ver_tail_prevEmpty_placed_ok ext halloc hdealloc hDropSS3 hpanic
    s0 s s7 coroPtr outPtr errsPtr msgVer b_2c0 g recG st
    hcro7 hpc7 hrun7 hsp7_6b hsp_align (htr7_6b.trans (htr6b_6.trans (htr6_5.trans (htr5_4.trans htr4_0))))
    hx0_7 hx1_7 hx19_7 hx24_7 hx25_7 hx26_7
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus)
    fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  refine ⟨?_, hspf, htrf, hcc, hcrof,
    by rw [hvregs_f, hvregs_7, hvregs_cs6b, hvregs_6, hvregs_cs5, hvregs_4, hvregs_cs3, hvregs_2]⟩
  refine Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64 ?_))
  exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))

/-! ## `[LibsignalFullPlacement]` / `LibsignalFrozen` wrappers for Block `519` -/

theorem lscro_of_frozen [LibsignalPlacement] {m : Memory} (hfr : LibsignalFrozen lsmpl m) :
    StoreKit.LibsignalCodeRoLoaded lsmpl m :=
  ⟨LibsignalCodeLoaded.of_codeLoaded hfr.2, hfr.1⟩

/-- Block `519` own-program `withLsFrozen` contract under `[LibsignalFullPlacement]`. -/
theorem pqxdh_log_closure_frozen_placed_ok [LibsignalFullPlacement]
    (H : LibsignalHooks) :
    subroutine_ok
      ((CryptoVerification.CliHandshake.Placed.blkPC_519).rebase
        (CryptoVerification.CliHandshake.Placed.blkPl_519).base H)
      (lsmpl.base 519)
      (withLsFrozen lsmpl pqxdhLogClosurePlacedSpec) :=
  _root_.LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.subroutine_ok_withLsFrozen_of_plain
    (pqxdh_log_closure_placed_ok H)

/-- Lift Block `519` (`pqxdhLogClosurePlacedSpec`) to any `callerProg` under `[LibsignalFullPlacement]`. -/
theorem pqxdh_log_closure_frozen_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] :
    subroutine_ok callerProg (lsmpl.base 519)
      (withLsFrozen lsmpl pqxdhLogClosurePlacedSpec) :=
  _root_.LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.ls_subroutine_ok_withLsFrozen_of_block_frc
    (pqxdh_log_closure_frozen_placed_ok H)

/-- Strengthen any `SepWPp` postcondition with `LibsignalFrozen lsmpl sf.mem` via `Steps.keepsFrozen`. -/
theorem sepWPp_strengthen_frozen [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hwp : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P (fun sf P_f => Q sf P_f ∧ LibsignalFrozen lsmpl sf.mem) Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQ⟩ | hpan⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hQ,
      libsignalFrozen_of_keepsFrozen hfr hsteps.keepsFrozen⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

theorem bind_sepWP_lsfr_frame_ver [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalFrozen lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim hoom | exact (not_satisfies_false_sepConj hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpcm hrunm (libsignalFrozen_of_keepsFrozen hfr hsteps.keepsFrozen)
      hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem call_lsfr_nopanic_ver [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsFrozen lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalFrozen lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsFrozen lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsFrozen]; rw [hspec]
    have h1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜LibsignalFrozen lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hfr, hm⟩
    exact Arm64.Satisfies.mono (Entails.of_eq (by ac_rfl)) h1
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right; · dsimp only [withLsFrozen] at hoom_post; rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim
  · dsimp only [withLsFrozen] at hpost; rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (libsignalFrozen_of_keepsFrozen hfr hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsFrozen] at hpost; rw [hpan_false] at hpost; exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsFrozen] at hpost; rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalFullPlacement]` Stage P3 version-mismatch path
(`(blkPl_518).base + 0x1e04 → s0.readReg64 .x30`) over general `prevSessionsEmptyAt A coroPtr g`,
discharging Block `519` internally from `LibsignalFrozen lsmpl s1.mem`. -/
theorem stageP3_ver_ne_prevEmpty_full_placed_ok [LibsignalFullPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec A)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hfr1 : LibsignalFrozen lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 7684#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace) (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr) (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ prevSessionsEmptyAt A coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (P3P4.PanicOomProp s0) := by
  unfold stageP3ErrPostPrevEmptyM3Placed; dsimp only [SessionState.recordError]
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hs1_sp]; exact hsp_align
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x3e0#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u3e0 => SepWPp.exists_elim fun u3e8_w =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo64_split_sp3e8 s.sp u3e8_w)) (by sep_focus) ?_
  have hstep1 := p3_ver_ne_1e04_placed_wp ext s1 coroPtr u3e0 msgVer
    (u3e8_w.extractLsb' 0 32) hpc1 hrun1 hsp1_align hx9_1 hx19_1
  rw [hs1_sp] at hstep1
  refine bind_sepWP_lsfr_frame_ver hfr1 hstep1 (by sep_focus) fun s2 hpc2 hrun2 hfr2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, _, _, _, _, hx19_2, hx24_2, hx27_2, _, hx30_2, hvregs_2⟩
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_1] using hsp_align
  have hstack_log : stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_lsfr_nopanic_ver (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := FromRecordCallees.lsLogOff ∗ stackAt s.sp pqxdhClosureStack)
    hfr2 (pqxdh_log_closure_frozen_placed_ok_of_block (callerProg := lsProg_518 ext))
    hpc2 hrun2 hsp2_al hx30_2
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_1, pure_true, emp_sepConj]) trivial (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 _ hcs3 hfr3 => ?_)
  have hcro3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := lscro_of_frozen hfr3
  dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr3_2 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log.symm) (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2.trans hsp2_1
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  rcases hcs3 with ⟨hx19_cs3, _, _, _, _, hx24_cs3, _, _, hx27_cs3, _, _, hvregs_cs3⟩
  have hstep3 := p3_err_ver_b_placed_wp ext s3 coroPtr hpc3 hrun3 hsp3_align (hx19_cs3.trans hx19_2)
  rw [hsp3_s] at hstep3
  refine bind_sepWP_lscro_frame_ver hcro3 hstep3 (by sep_focus) fun s4 hpc4 hrun4 hcro4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_3, htr4_3, hx0_4, hx19_4, hx21_4, hx24_4, hx27_4, _, hx30_4, hvregs_4⟩
  have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_3] using hsp_align
  have htr4_0 : s4.trace = s0.trace := htr4_3.trans (htr3_2.trans (htr2_1.trans htr1))
  refine call_lscl_oom_ver (spec := growOneSpeSpec A)
    (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8)))) (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
    hcro4 htr4_0 hGrow hpc4 hrun4 hsp4_al hx30_4
    (by rw [growOneSpe_pre_zero_eq A s4 (s.sp + 0x3c8#64) initErrsPtr hx0_4 hinit_ne, hsp4_3,
          pure_true, emp_sepConj]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus) (hnext := fun s5 hpc5 hrun5 hsp5_4 _ hcs5 hcro5 => ?_)
  rw [growOneSpe_post_zero_eq A s4 s5 (s.sp + 0x3c8#64) initErrsPtr, hsp4_3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => SepWPp.pure_elim fun htr5_4 => SepWPp.pure_elim fun _ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo32_pair_sp3e8 s.sp msgVer (u3e8_w.extractLsb' 32 32))) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs192_split_eq errsPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_3
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, _, hx24_cs5, _, _, hx27_cs5, _, _, hvregs_cs5⟩
  have hx27_5 : s5.readReg64 .x27 = ctxPtr :=
    hx27_cs5.trans (hx27_4.trans (hx27_cs3.trans (hx27_2.trans hx27_1)))
  have hstep5 := p3_err_ver_c_placed_wp ext s5 coroPtr errsPtr 0x8000000000000006#64
    (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5 ctxPtr u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc5 hrun5 hsp5_align (hx19_cs5.trans hx19_4) (hx21_cs5.trans hx21_4)
    (by rw [hx24_cs5, hx24_4, hx24_cs3, hx24_2, hx24_1, hsp5_s])
  rw [hsp5_s, hx27_5] at hstep5
  refine bind_sepWP_lscro_frame_ver hcro5 hstep5 (by sep_focus) fun s6 hpc6 hrun6 hcro6 hregs6 => ?_
  rcases hregs6 with ⟨hsp6_5, htr6_5, hx0_6, hx19_6, _, _, _, hx30_6, hvregs_6⟩
  refine P3P4.SepWPp.weaken_frame (errs48_fold_ver errsPtr e2 e3 e4 e5 msgVer (u3e8_w.extractLsb' 32 32)) (by sep_focus) ?_
  have hsp6_al : s6.spAligned = true := by simpa only [State.spAligned, hsp6_5] using hsp_align
  have hstack_drop2 : stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_lscl_nopanic_ver (x := (⟨s.sp + 0xa90#64, G₁, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hcro6 hDropSS3 hpc6 hrun6 hsp6_al hx30_6
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_5]) hx0_6 (by sep_focus)
    (hnext := fun s6b hpc6b hrun6b hsp6b_6 _ hcs6b hcro6b => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_5, sepConj_assoc]
  refine SepWPp.pure_elim fun htr6b_6 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hlog_eq : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp6b_s : s6b.sp = s.sp := hsp6b_6.trans hsp6_5
  have hsp6b_align : (s6b.sp &&& 15#64 == 0#64) = true := by rw [hsp6b_s]; exact hsp_align
  rcases hcs6b with ⟨hx19_cs6b, _, _, _, _, _, _, _, _, _, _, hvregs_cs6b⟩
  have hprev_f0 : prevSessionsEmptyAt A coroPtr g =
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      (((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
       vecBuf A 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr []) := by
    unfold prevSessionsEmptyAt vecAt vecHeader; dsimp only [List.length_nil]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hprev_f0) (by sep_focus) ?_
  simp only [sepConj_assoc]
  have hstep7 := p3_err_ver_d_placed_wp ext hshim s6b coroPtr outPtr ctxPtr recG.localIk.cap
    0x8000000000000006#64 (cap_ne_noneCap_of_lt hcap_lt) hpc6b hrun6b hsp6b_align (hx19_cs6b.trans hx19_6)
  rw [hsp6b_s] at hstep7
  refine bind_sepWP_lscro_frame_ver hcro6b hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6b, htr7_6b, hx0_7, hx1_7, hx19_7, hx24_7, hx25_7, hx26_7, _, _, hvregs_7⟩
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hprev_f0.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG st ⊢ sessionStateAt A (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG st hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  have hfold3e0_48 : ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      ((s.sp + 0x3e8#64) ↦₆₄ (u3e8_w.extractLsb' 32 32 ++ msgVer)) ∗ ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗
      ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗ ((s.sp + 0x400#64) ↦₆₄ e4) ∗ ((s.sp + 0x408#64) ↦₆₄ e5) ⊢
      memRegion (s.sp + 0x3e0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using words6_entails_memRegion48 (s.sp + 0x3e0#64)
      0xffffffffffffffff#64 (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5
  refine P3P4.SepWPp.weaken_frame hfold3e0_48 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp).symm) (by sep_focus) ?_
  have htail := stageP3_err_ver_tail_prevEmpty_placed_ok ext halloc hdealloc hDropSS3 hpanic
    s0 s s7 coroPtr outPtr errsPtr msgVer b_2c0 g recG st
    hcro7 hpc7 hrun7 hsp7_6b hsp_align (htr7_6b.trans (htr6b_6.trans (htr6_5.trans (htr5_4.trans htr4_0))))
    hx0_7 hx1_7 hx19_7 hx24_7 hx25_7 hx26_7
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus)
    fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  refine ⟨?_, hspf, htrf, hcc, hcrof,
    by rw [hvregs_f, hvregs_7, hvregs_cs6b, hvregs_6, hvregs_cs5, hvregs_4, hvregs_cs3, hvregs_2]⟩
  refine Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64 ?_))
  exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
