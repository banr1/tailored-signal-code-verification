/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7d
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part D

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant7d.lean`.
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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

variable [LibsignalPlacement]

/-! ## 1. Dispatch (`+36 -> +1056`) with `x9` -/

/-- Placed jump-table dispatch (`+36 -> +1056` in Block `333`) for the niche-encoded `Ct1Sampled`
variant, additionally recording `sm.readReg64 .x9 = w0` (loaded by `ldr x9, [x0]` at `+40`). -/
theorem v7_dispatch_ct1Sampled_placed
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA w0 : BitVec 64) (Rest : SepProp)
    (hw0 : w0 = noneCap ∨ w0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1056#64) s1
      ((pbA ↦₆₄ w0) ∗
        statesFromPbJumpTablePlacedAt ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢ (pbA ↦₆₄ w0) ∗ statesFromPbJumpTablePlacedAt ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = w0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x0 = pbA ∧
        sm.readReg64 .x25 = s0.sp - 608#64 ∧
        sm.readReg64 .x21 = s0.sp - 1008#64 ∧
        sm.readReg64 .x13 = s0.sp - 1136#64 ∧
        sm.readReg64 .x23 = s0.sp - 1552#64 ∧
        TraceCalleeSaved sm s0) := by
  rw [statesFromPbJumpTablePlacedAt_eq]
  change s1.pc = (blkPl_333).base + 36#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 1056#64) s1 _ _
  dsimp only [statesFromPbJumpTableBytesAt, statesFromPbJumpTableSym, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  rcases hw0 with rfl | hlt
  · dsimp only [noneCap]
    wp_steps; wp_done
  · have hne2 := cap_add_two_beq_zero_false hlt
    have hcc := cap_xor_highBit_cc_11_false hlt
    wp_steps; wp_done

/-! ## 2. Entry `ptsNeeded` Check (`+1056 -> +3480` and `+1056 -> +4632`) -/

/-- Placed entry `ptsNeeded` check (`+1056 -> +3480`) when `v7_receivingEkPtsOk s.receivingEk` holds:
loads `x22 = cap_dec` from `[pbA + 184]` and branches to `+3480` either because `cap_dec = noneCap`
(`s.receivingEk = none`) or because `d.ptsNeeded == 576#32` (`s.receivingEk = some d`). -/
theorem v7_entry_1056_to_3480_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA c1 w0 cap_dec x21_val x23_val x25_val : BitVec 64)
    (optDecPb : Option PolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec (optDecPb.map pbToProtoPolyDecoder))
    (hpts : v7_receivingEkPtsOk optDecPb)
    (hpc1 : s1.pc = lsmpl.base 333 + 1056#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
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
        sm.readReg64 .x21 = x21_val ∧
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

/-- Placed helper for `+1092 -> +1096` (`bl` Block `286`): calls `drop_glue::<ProtoUnchunkedCt1SentEkReceived>`
    with `x0 = pbA`. -/
theorem v7_call_drop_proto_unchunked_ct1_sent_1092_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1092#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1096#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        protoUnchunkedCt1SentEkReceivedAt A pbA (v7_ct1SentToCt1SentEkReceived u) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion pbA 128 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdrop := v7_sub_ok_drop_proto_unchunked_ct1_sent_ek_received_mem_placed hA hcl1
  simp only [withMemEq, dropProtoUnchunkedCt1SentEkReceivedSpec] at hdrop
  refine SepWP.weaken_pre
    (sepConj_mono_left (v7_stackAt_encoderFromPbStack_to_dropStack32 (s0.sp - 2400#64))) ?_
  dsimp only [protoUnchunkedCt1SentEkReceivedSize, BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
  change s1.pc = (blkPl_333).base + 1092#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 1096#64) s1 _ _
  wp_steps
  wp_apply
  refine EncoderFromPb.align_pre ?_ ?_
  · have hst := v7_stackAt_dropStack32_to_encoderFromPbStack (s0.sp - 2400#64)
    have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
    rw [haddr] at hst
    nth_rw 1 [← hsp1] at hst
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt s1.sp dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
        (memRegion pbA 128 ∗ A.pool ∗ Frame) by ac_rfl)) ?_
    exact sepConj_mono_left hst
  · wp_done

/-- Placed bad `ptsNeeded` path (`+1056 -> +1080 -> +4528 -> +4632`):
when `s.receivingEk = some d` and `(d.ptsNeeded == 576#32) = false`, drops `s.uc` (if `some`),
sets `w28 = 2` (`.msgDecode`), drops `s.sendingCt1` and `s.receivingEk` via `+4528`,
and reaches `+4632` with `memRegion pbA 224`. -/
theorem v7_entry_bad_pts_1056_to_4632_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA w0 cap_dec : BitVec 64)
    (optUcPb : Option V1State.Unchunked.Ct1Sent)
    (optEncPb : Option PolynomialEncoder)
    (d : PolynomialDecoder) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hcap_uc : v7_optUcCapProp w0 optUcPb)
    (hcap_dec : v7_optDecoderCapProp cap_dec (some (pbToProtoPolyDecoder d)))
    (hpts : (d.ptsNeeded == 576#32) = false)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1056#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 optUcPb) ∗
        optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion pbA 224 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 2#64 ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 4528#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
      A.pool ∗
      (memRegion pbA 128 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = 2#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have hne_dec := v4_ptsCap_add_one_ne_zero hcap_dec
    have hpts' : ((pbToProtoPolyDecoder d).ptsNeeded == 576#32) = false := hpts
    have hpts_sub := v7_ptsNeeded_sub_576_beq_zero hpts'
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 optUcPb) ∗
           optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
           ((pbA + 184#64) ↦₆₄ cap_dec) ∗
           A.pool ∗ Frame) by ac_rfl))
        (sepConj_mono_left
          (v7_optProtoPolyDecoderTail_expose_pts A pbA cap_dec (pbToProtoPolyDecoder d)))) ?_
    cases optUcPb with
    | none =>
      unfold v7_optUcCapProp at hcap_uc
      subst hcap_uc
      dsimp only [v7_optProtoUnchunkedCt1SentTail]
      dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx9_1 ⊢
      change s1.pc = (blkPl_333).base + 1056#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4528#64) s1 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hun_dec := v7_optProtoPolyDecoderTail_unexpose_pts A pbA cap_dec (pbToProtoPolyDecoder d)
        have hun_uc := v7_optProtoUnchunkedCt1Sent_unexpose_none pbA
        dsimp only [noneCap] at hun_uc
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 208#64) ↦₃₂ (pbToProtoPolyDecoder d).ptsNeeded) ∗
             v7_optProtoPolyDecoderTailWithoutPts A (pbA + 184#64) cap_dec (pbToProtoPolyDecoder d)) ∗
            ((pbA ↦₆₄ 18446744073709551615#64) ∗ memRegion (pbA + 8#64) 120) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
             ((pbA + 184#64) ↦₆₄ cap_dec) ∗
             A.pool ∗ Frame) by ac_rfl)) ?_
        exact Entails.trans
          (sepConj_mono hun_dec (sepConj_mono_left hun_uc))
          (Entails.of_eq (by ac_rfl))
      · wp_done
    | some u =>
      unfold v7_optUcCapProp at hcap_uc
      have hne_uc := cap_add_one_beq_zero_false hcap_uc
      refine seq_clean_lscl hcl1
        (mid := lsmpl.base 333 + 1092#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          protoUnchunkedCt1SentEkReceivedAt A pbA (v7_ct1SentToCt1SentEkReceived u) ∗
          A.pool ∗
          (optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
           Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = pbA ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s1.pc = (blkPl_333).base + 1056#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 1092#64) s1 _ _
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hun_dec := v7_optProtoPolyDecoderTail_unexpose_pts A pbA cap_dec (pbToProtoPolyDecoder d)
          have hun_uc := v7_optProtoUnchunkedCt1Sent_unexpose_some A pbA w0 u
          rw [v7_protoUnchunkedCt1SentAt_eq] at hun_uc
          refine Entails.trans
            (Entails.of_eq (show _ =
              (((pbA + 208#64) ↦₃₂ (pbToProtoPolyDecoder d).ptsNeeded) ∗
               v7_optProtoPolyDecoderTailWithoutPts A (pbA + 184#64) cap_dec (pbToProtoPolyDecoder d)) ∗
              ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 (some u)) ∗
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               A.pool ∗
               optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
               ((pbA + 184#64) ↦₆₄ cap_dec) ∗
               Frame) by ac_rfl)) ?_
          exact Entails.trans
            (sepConj_mono hun_dec (sepConj_mono_left hun_uc))
            (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx27_2, htr2⟩
        refine EncoderFromPb.seq_clean
          (mid := lsmpl.base 333 + 1096#64)
          (P_mid :=
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion pbA 128 ∗
            A.pool ∗
            (optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
             Frame))
          (Q := fun sm =>
            sm.sp = s0.sp - 2400#64 ∧
            sm.readReg64 .x19 = out ∧
            sm.readReg64 .x22 = cap_dec ∧
            sm.readReg64 .x27 = pbA ∧
            TraceCalleeSaved sm s0)
          (v7_call_drop_proto_unchunked_ct1_sent_1092_placed hA s0 s2 out pbA cap_dec u _
            hcl2 hsp0_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx27_2 htr2)
          ?_
        intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
        change s3.pc = (blkPl_333).base + 1096#64 at hpc3
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4528#64) s3 _ _
        wp_steps
        refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
        wp_done
  · intro s4 hpc4 hrun4 hcl4 ⟨hsp4, hx19_4, hx22_4, hx27_4, hx28_4, htr4⟩
    refine SepWP.mono
      (v7_cleanup_4528_placed hA s0 s4 out pbA cap_dec 2#64
        (optEncPb.map pbToProtoPolyEncoder) (some (pbToProtoPolyDecoder d))
        (memRegion pbA 128 ∗ Frame)
        hcl4 hcap_dec hsp0_align hpc4 hrun4 hsp4 hx19_4 hx22_4 hx27_4 hx28_4 htr4)
      ?_
    intro sm Pm _ _ ⟨hPm, hq⟩
    refine ⟨Entails.trans hPm ?_, hq⟩
    have hm184 := ProofLib.memRegion_split pbA 128 56 (by decide)
    have hm224 := ProofLib.memRegion_split pbA 184 40 (by decide)
    rw [hm224, hm184]
    exact Entails.of_eq (by ac_rfl)

/-! ## 3. `<Ct1Sent>::from_pb` Phase (`+3480 -> +3648` and Error Exits) -/

/-- Placed `s.uc = none` error path at `+3480 -> +4524 -> +4528 -> +4632`:
when `w0 = noneCap` (`x9 = noneCap`), `+3480..+3484` branches to `+4524`, sets `w28 = 0`,
and runs `v7_cleanup_4528_placed` to reach `+4632` with `memRegion pbA 224`. -/
theorem v7_uc_none_3480_to_4632_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (optEncPb : Option PolynomialEncoder)
    (optDecPb : Option PolynomialDecoder) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hcap_dec : v7_optDecoderCapProp cap_dec (optDecPb.map pbToProtoPolyDecoder))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3480#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = noneCap)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((pbA ↦₆₄ noneCap) ∗ v7_optProtoUnchunkedCt1SentTail A pbA noneCap none) ∗
        optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder)) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion pbA 224 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 4528#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder)) ∗
      A.pool ∗
      (memRegion pbA 128 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = 0#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [v7_optProtoUnchunkedCt1SentTail]
    dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx9_1 ⊢
    change s1.pc = (blkPl_333).base + 3480#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4528#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hun_uc := v7_optProtoUnchunkedCt1Sent_unexpose_none pbA
      dsimp only [noneCap] at hun_uc
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((pbA ↦₆₄ 18446744073709551615#64) ∗ memRegion (pbA + 8#64) 120) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder)) ∗
           A.pool ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hun_uc) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    refine SepWP.mono
      (v7_cleanup_4528_placed hA s0 s2 out pbA cap_dec 0#64
        (optEncPb.map pbToProtoPolyEncoder) (optDecPb.map pbToProtoPolyDecoder)
        (memRegion pbA 128 ∗ Frame)
        hcl2 hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2)
      ?_
    intro sm Pm _ _ ⟨hPm, hq⟩
    refine ⟨Entails.trans hPm ?_, hq⟩
    have hm184 := ProofLib.memRegion_split pbA 128 56 (by decide)
    have hm224 := ProofLib.memRegion_split pbA 184 40 (by decide)
    rw [hm224, hm184]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb
