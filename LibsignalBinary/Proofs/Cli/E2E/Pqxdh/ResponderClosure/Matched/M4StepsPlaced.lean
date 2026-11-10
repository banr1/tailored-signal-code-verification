/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Steps
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Relocatable Matched-Session Stage P4 Skip-PreKey Segment
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.LibsignalPublicApi.StoreKit

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-- `(blkPl_518).base + 0x02ec → +0x03cc` (`opkIdIsSome = 2#32`) under `[LibsignalPlacement]`. -/
theorem p4_seg1d_skip_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr saveIdFutPtr saveIdFutVt futSize futAlign : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x2ec#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = saveIdFutPtr)
    (hx23 : s.readReg64 .x23 = saveIdFutVt)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x3cc#64) s
      (((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
       ((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       (if futSize = 0#64 then emp
        else A.live saveIdFutPtr futSize.toNat futAlign.toNat ∗
          memRegion saveIdFutPtr futSize.toNat) ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
          ((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = saveIdFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = saveIdFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  by_cases hsize : futSize = 0#64
  · subst hsize
    simp only [↓reduceIte, emp_sepConj]
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], rfl⟩
  · have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize
    simp only [hsize, ↓reduceIte, sepConj_assoc]
    wp_steps
    wp_call hdealloc (saveIdFutPtr, futSize.toNat, futAlign.toNat)
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
