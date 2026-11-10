/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7d
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part E

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant7e.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

variable [LibsignalPlacement]

/-! ## 1. Unaligned Copy & Stack Layout Helpers -/

/-- Entry block `+1056 -> +3480` when `s.receivingEk` is `none` or has `ptsNeeded = 576`,
    additionally recording preservation of `x23` and `x25`. -/
theorem v7_entry_1056_to_3480_full_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA c1 w0 cap_dec x23_val x25_val : BitVec 64)
    (optDecPb : Option PolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec (optDecPb.map pbToProtoPolyDecoder))
    (hpts : v7_receivingEkPtsOk optDecPb)
    (hpc1 : s1.pc = lsmpl.base 333 + 1056#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx26_1 : s1.readReg64 .x26 = s0.readReg64 .x0)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3480#64) s1
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder) ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x1 = c1 ∧
        sm.readReg64 .x9 = w0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x26 = s0.readReg64 .x0 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  cases optDecPb with
  | none =>
    simp only [Option.map_none, v7_optDecoderCapProp] at hcap_dec
    subst hcap_dec
    dsimp only [Option.map_none, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 1056#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 3480#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
    wp_done
  | some d =>
    simp only [Option.map_some, v7_optDecoderCapProp] at hcap_dec
    unfold v7_receivingEkPtsOk at hpts
    have hd_pts : (pbToProtoPolyDecoder d).ptsNeeded = 576#32 := by
      change d.ptsNeeded = 576#32
      exact beq_iff_eq.mp hpts
    have hne := v4_ptsCap_add_one_ne_zero hcap_dec
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_left
        (v7_optProtoPolyDecoderTail_expose_pts A pbA cap_dec (pbToProtoPolyDecoder d)))) ?_
    rw [hd_pts]
    dsimp only [Option.map_some, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 1056#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 3480#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hun := v7_optProtoPolyDecoderTail_unexpose_pts A pbA cap_dec (pbToProtoPolyDecoder d)
      rw [hd_pts] at hun
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((pbA + 184#64) ↦₆₄ cap_dec) ∗
          (((pbA + 208#64) ↦₃₂ 576#32) ∗
           v7_optProtoPolyDecoderTailWithoutPts A (pbA + 184#64) cap_dec (pbToProtoPolyDecoder d)) ∗
          Frame by ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_left hun)
    · wp_done

end CryptoVerification.SpqrV1.States.FromPb
