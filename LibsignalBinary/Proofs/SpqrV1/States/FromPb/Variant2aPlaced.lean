/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 1 (`KeysSampled`, `+1104`) — Part A

Relocatable Block-`333` callee helpers and `uc` / `sendingHdr` error-cleanup paths (`+3872`, `+3936`, `+4332`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

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
open CryptoVerification.SpqrV1.States.Recv
  (drop_glue_proto_poly_encoder_cl_on drop_glue_proto_poly_encoder_mem_on)
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_sub_sub_lit v1_shl8_extract_0_8 v1_bv_add_add_lit

/-! ## `withLsCodeLoaded` Sequencing Helpers and Callee Relocation Lemmas for `States::from_pb` (Block `333`) -/

/-- Relocatable `PolyEncoder::from_pb` (Block `374`) contract lifted to `lsProg_333`. -/
def EncoderFromPbPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 374)
    (withLsCodeLoaded lsmpl (encoderFromPbSpec A))

theorem seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

theorem v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec A)) :=
  drop_glue_proto_poly_encoder_cl_on (callerProg := lsProg_333 (Rust.withPanics ext)) hA.dealloc

theorem v1_drop_glue_proto_poly_encoder_mem_ok_at_statesFromPb_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooks A ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) (lsmpl.base 271)
      (withMemEq m (dropProtoPolyEncoderSpec A)) :=
  drop_glue_proto_poly_encoder_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hA.dealloc hcl

theorem v1_encoder_from_pb_ok_at_statesFromPb_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (henc : EncoderFromPbPlacedOkExt A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec A)) :=
  henc

theorem v1_dealloc_ok_at_statesFromPb_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) :=
  spqr_hook_ok_of_mem hA.dealloc

/-- Shared `Err(Error::StateDecode)` exit at `+5940` (`+5940 -> +60 -> s0.x30`):
    when `x26` has low byte `0#8` (`spqrErrorByte .stateDecode`) and `x19 = out`,
    writes `[out + 16..32] = (x22, x8)`, `x8 = noneCap`, `[out + 8] = x26`, and branches to `+60`. -/
theorem v1_err_5940_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5940#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rw [memRegion_out_928_split_32 out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v24
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v0
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 60#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (out ↦₆₄ v0) ∗
      ((out + 8#64) ↦₈ spqrErrorByte .stateDecode) ∗
      memRegion (out + 9#64) 919 ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x8 = noneCap ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · change s1.pc = (blkPl_333).base + 5940#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 60#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htail := out_8_32_entails_err_tail out (s1.readReg64 .x26)
        (s1.readReg64 .x22) (s1.readReg64 .x8)
      rw [hx26_1] at htail
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ s1.readReg64 .x26) ∗
           ((out + 16#64) ↦₆₄ s1.readReg64 .x22) ∗
           ((out + 24#64) ↦₆₄ s1.readReg64 .x8) ∗
           memRegion (out + 32#64) 896) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60_placed (A := A) (F := F) (ext := ext) s0 s2 out .stateDecode v0 Rest
      hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

/-- Drop `Option<ProtoPolynomialEncoder>` at `fsp + 1496` and return `Err(StateDecode)` (`+4332 -> s0.x30`). -/
theorem v1_drop_sendingHdr_4332_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4332#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hex := v1_optProtoPolyEncoderHeap_extract_w0 A optEnc w0 w8 w16 w24 w32 w40 w48
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono (v1_memRegion_1496_split_232 (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_left hex)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
  apply ProofLib.SepWP.exists_left; intro w232
  apply SepWP.pure_elim; intro hw0_cond
  have hmerge := v1_merge_stack_1496_56_752 (s0.sp - 2400#64) w232
  cases optEnc with
  | none =>
    subst hw0_cond
    dsimp only [v1_optProtoPolyEncoderHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 5940#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (A.pool ∗ Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        (sm.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 4332#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5940#64) s1 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hw_mem := v1_optProtoPolyEncoderWordsAt_entails_56
          (s0.sp - 2400#64 + 1496#64) 18446744073709551615#64 w8 w16 w24 w32 w40 w48
        dsimp only [v1_optProtoPolyEncoderWordsAt] at hw_mem
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 232 ∗
           ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
           memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
           (((s0.sp - 2400#64 + 1496#64) ↦₆₄ 18446744073709551615#64) ∗
            ((s0.sp - 2400#64 + 1496#64 + 8#64) ↦₆₄ w8) ∗
            ((s0.sp - 2400#64 + 1496#64 + 16#64) ↦₆₄ w16) ∗
            ((s0.sp - 2400#64 + 1496#64 + 24#64) ↦₆₄ w24) ∗
            ((s0.sp - 2400#64 + 1496#64 + 32#64) ↦₆₄ w32) ∗
            ((s0.sp - 2400#64 + 1496#64 + 40#64) ↦₆₄ w40) ∗
            ((s0.sp - 2400#64 + 1496#64 + 48#64) ↦₆₄ w48)) ∗
           memRegion (s0.sp - 2400#64 + 1552#64) 752) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left hw_mem))))) ?_
        exact Entails.trans (sepConj_mono_left hmerge) (Entails.of_eq (by ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
      have herr := v1_err_5940_placed (A := A) (F := F) (ext := ext) s0 s2 out (A.pool ∗ Rest)
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2
      refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩
  | some pbEnc =>
    have hpack := v1_optProtoPolyEncoderAt_pack_some A (s0.sp - 2400#64 + 1496#64) pbEnc
      w0 w8 w16 w24 w32 w40 w48
    have hne := cap_add_one_beq_zero_false hw0_cond
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have h904 : s0.sp - 2400#64 + 1496#64 = s0.sp - 904#64 := by bv_omega
    refine seq_clean_lscl hcl1
      (mid := lsmpl.base 333 + 4352#64)
      (P_mid :=
        protoPolynomialEncoderAt A (s0.sp - 904#64) pbEnc ∗
        A.pool ∗
        stackAt (s0.sp - 2400#64) dropStack48 ∗
        (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
         memRegion (s0.sp - 2400#64) 232 ∗
         ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
         memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
         memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = s0.sp - 904#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = s1.readReg64 .x26 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 4332#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4352#64) s1 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), ← h904]
        refine Entails.trans (Entails.of_eq (show _ =
          (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48) ∗
          (A.pool ∗ stackAt (s0.sp - 2400#64) dropStack48 ∗
           (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
            memRegion (s0.sp - 2400#64) 232 ∗
            ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
            memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
            memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by
            dsimp only [v1_optProtoPolyEncoderWordsAt]; ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hpack) (Entails.of_eq (by ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx19_2, hx26_2, htr2⟩
      have hdrop := v1_drop_glue_proto_poly_encoder_mem_ok_at_statesFromPb_placed hA hcl2
      simp only [withMemEq, dropProtoPolyEncoderSpec] at hdrop
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 5940#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          (A.pool ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          (sm.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 4352#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5940#64) s2 _ _
        wp_steps
        wp_call hdrop ⟨s0.sp - 904#64, pbEnc⟩
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have h7552 : s0.sp - 2400#64 - 5152#64 = s0.sp - 7552#64 := by bv_omega
          rw [v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), h7552, ← h904, hsp2]
          dsimp only [protoPolynomialEncoderSize]
          simp only [arm64_norm] at hmerge ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 232 ∗
             ((s0.sp - 2168#64) ↦₆₄ w232) ∗
             memRegion (s0.sp - 2160#64) 1256 ∗
             memRegion (s0.sp - 904#64) 56 ∗
             memRegion (s0.sp - 848#64) 752) ∗
            (memRegion (s0.sp - 7552#64) 1008 ∗
             stackAt (s0.sp - 2400#64) dropStack48 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hmerge) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
        have herr := v1_err_5940_placed (A := A) (F := F) (ext := ext) s0 s3 out (A.pool ∗ Rest)
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
        refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

theorem v1_drop_sendingHdr_4204_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4204#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 4332#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1496 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [spqrErrorByte, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 4204#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4332#64) s1 _ _
    wp_steps; wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    exact v1_drop_sendingHdr_4332_placed (A := A) (F := F) hA s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48 Rest hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2

/-! ## Error Cleanup for `uc` (`ek`, `dk`, `auth`) + `sendingHdr` (`+3872 -> +3936 -> +4328 -> +4332`) -/

/-- Cleanup `ek` (`x9 = ptr_ek`, `x20 = cap_ek`), `dk` (`[fsp+216] = ptr_dk`, `[fsp+224] = cap_dk`),
    and `sendingHdr` at `fsp + 1496..1552`, returning `Err(StateDecode)` (`+3936 -> s0.x30`). -/
theorem v1_drop_uc_and_sendingHdr_3936_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out cap_ek ptr_ek cap_dk ptr_dk w192 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = cap_ek)
    (hx9_1 : s1.readReg64 .x9 = ptr_ek)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A cap_ek ptr_ek ∗
        vecCapPtrDealloc A cap_dk ptr_dk ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v1_dealloc_ok_at_statesFromPb_placed hA
  simp only [rustDeallocSpec] at hdealloc
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 3956#64)
    (P_mid :=
      memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      memRegion (s0.sp - 2400#64) 192 ∗
      ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
      memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
      ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
      memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      vecCapPtrDealloc A cap_dk ptr_dk ∗
      A.pool ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x20 = cap_ek ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
    change s1.pc = (blkPl_333).base + 3936#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 3956#64) s1 _ _
    by_cases hc_ek : (cap_ek == 0#64) = true <;>
      simp only [hc_ek, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply
      refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, htr2⟩
    refine seq_clean_lscl hcl2
      (mid := lsmpl.base 333 + 4332#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        Rest)
      (Q := fun s3 =>
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        (s3.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
        TraceCalleeSaved s3 s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc, spqrErrorByte, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
      change s2.pc = (blkPl_333).base + 3956#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4332#64) s2 _ _
      by_cases hc_dk : (cap_dk == 0#64) = true <;>
        simp only [hc_dk, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
          have hm := v1_merge_stack_192_216_224_1496 (s0.sp - 2400#64) w192 ptr_dk cap_dk
          simp only [arm64_norm] at hm ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 192 ∗
             ((s0.sp - 2208#64) ↦₆₄ w192) ∗
             memRegion (s0.sp - 2200#64) 16 ∗
             ((s0.sp - 2184#64) ↦₆₄ ptr_dk) ∗
             ((s0.sp - 2176#64) ↦₆₄ cap_dk) ∗
             memRegion (s0.sp - 2168#64) 1264) ∗
            (memRegion (s0.sp - 7552#64) 1056 ∗
             stackAt (s0.sp - 2400#64) allocHookStack ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 848#64) 752 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
        · wp_done
      · wp_steps; wp_apply; wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp2]
          have hm := v1_merge_stack_192_216_224_1496 (s0.sp - 2400#64) (s2.readReg64 .x22) ptr_dk cap_dk
          simp only [arm64_norm] at hm ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 192 ∗
             ((s0.sp - 2208#64) ↦₆₄ s2.readReg64 .x22) ∗
             memRegion (s0.sp - 2200#64) 16 ∗
             ((s0.sp - 2184#64) ↦₆₄ ptr_dk) ∗
             ((s0.sp - 2176#64) ↦₆₄ cap_dk) ∗
             memRegion (s0.sp - 2168#64) 1264) ∗
            (memRegion (s0.sp - 7552#64) 1056 ∗
             stackAt (s0.sp - 2400#64) allocHookStack ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 848#64) 752 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
        · wp_done
    · intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
      exact v1_drop_sendingHdr_4332_placed (A := A) (F := F) hA s0 s3 out optEnc
        w0 w8 w16 w24 w32 w40 w48 Rest hcl3 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3

/-- Cleanup `optAuth` (`x25 = u56, x28 = u64, x23 = u80, x24 = u88`), `ek`, `dk`, and `sendingHdr`,
    returning `Err(StateDecode)` (`+3872 -> +3936 -> s0.x30`). -/
theorem v1_drop_uc_and_sendingHdr_3872_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out cap_ek ptr_ek cap_dk ptr_dk w192 : BitVec 64)
    (optAuth : Option ProtoAuthenticator) (u56 u64 u72 u80 u88 u96 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = cap_ek)
    (hx9_1 : s1.readReg64 .x9 = ptr_ek)
    (hx25_1 : s1.readReg64 .x25 = u56)
    (hx28_1 : s1.readReg64 .x28 = u64)
    (hx23_1 : s1.readReg64 .x23 = u80)
    (hx24_1 : s1.readReg64 .x24 = u88)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A cap_ek ptr_ek ∗
        vecCapPtrDealloc A cap_dk ptr_dk ∗
        v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  cases optAuth with
  | none =>
    dsimp only [v1_optProtoAuthHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; intro hu56
    subst hu56
    refine seq_clean_lscl hcl1
      (mid := lsmpl.base 333 + 3936#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A cap_ek ptr_ek ∗
        vecCapPtrDealloc A cap_dk ptr_dk ∗
        A.pool ∗
        Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = cap_ek ∧
        s2.readReg64 .x9 = ptr_ek ∧
        TraceCalleeSaved s2 s0)
      ?_ ?_
    · dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx25_1 ⊢
      change s1.pc = (blkPl_333).base + 3872#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 3936#64) s1 _ _
      wp_steps; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, hx9_2, htr2⟩
      exact v1_drop_uc_and_sendingHdr_3936_placed (A := A) (F := F) hA s0 s2 out
        cap_ek ptr_ek cap_dk ptr_dk w192 optEnc w0 w8 w16 w24 w32 w40 w48 Rest
        hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx9_2 htr2
  | some auth =>
    dsimp only [v1_optProtoAuthHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; rintro ⟨hu56, _, _⟩
    have hcmn : (u56 + 1#64 == 0#64) = false :=
      Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hu56)
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
    have hdealloc := v1_dealloc_ok_at_statesFromPb_placed hA
    simp only [rustDeallocSpec] at hdealloc
    have hd_root := vecU8Payload_entails_dealloc A u56 u64 auth.rootKey
    have hd_mac := vecU8Payload_entails_dealloc A u80 u88 auth.macKey
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A u56 u64 auth.rootKey ∗
      vecU8Payload A u80 u88 auth.macKey ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 192 ∗
       ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
       memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
       ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
       ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
       memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       vecCapPtrDealloc A cap_ek ptr_ek ∗
       vecCapPtrDealloc A cap_dk ptr_dk ∗
       A.pool ∗
       Rest) by ac_rfl))
      (sepConj_mono hd_root (sepConj_mono_left hd_mac))) ?_
    rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
    wp_simp_pre [sepConj_assoc]
    refine seq_clean_lscl hcl1
      (mid := lsmpl.base 333 + 3908#64)
      (P_mid :=
        vecCapPtrDealloc A u80 u88 ∗
        memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
        stackAt (s0.sp - 2400#64) allocHookStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A cap_ek ptr_ek ∗
        vecCapPtrDealloc A cap_dk ptr_dk ∗
        A.pool ∗
        Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = cap_ek ∧
        s2.readReg64 .x9 = ptr_ek ∧
        s2.readReg64 .x23 = u80 ∧
        s2.readReg64 .x24 = u88 ∧
        TraceCalleeSaved s2 s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      change s1.pc = (blkPl_333).base + 3872#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 3908#64) s1 _ _
      by_cases hc_r : (u56 == 0#64) = true <;>
        simp only [hc_r, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply; wp_steps
        refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, hx9_2, hx23_2, hx24_2, htr2⟩
      refine seq_clean_lscl hcl2
        (mid := lsmpl.base 333 + 3936#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 192 ∗
          ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
          memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
          memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A cap_ek ptr_ek ∗
          vecCapPtrDealloc A cap_dk ptr_dk ∗
          A.pool ∗
          Rest)
        (Q := fun s3 =>
          s3.sp = s0.sp - 2400#64 ∧
          s3.readReg64 .x19 = out ∧
          s3.readReg64 .x20 = cap_ek ∧
          s3.readReg64 .x9 = ptr_ek ∧
          TraceCalleeSaved s3 s0)
        ?_ ?_
      · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
        change s2.pc = (blkPl_333).base + 3908#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 3936#64) s2 _ _
        by_cases hc_m : (u80 == 0#64) = true <;>
          simp only [hc_m, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine EncoderFromPb.align_pre ?_ ?_
          · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
            simp only [arm64_norm]
            exact Entails.of_eq (by ac_rfl)
          · wp_done
        · wp_steps; wp_apply; wp_steps
          refine EncoderFromPb.align_pre ?_ ?_
          · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp2]
            simp only [arm64_norm]
            exact Entails.of_eq (by ac_rfl)
          · wp_done
      · intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, hx20_3, hx9_3, htr3⟩
        exact v1_drop_uc_and_sendingHdr_3936_placed (A := A) (F := F) hA s0 s3 out
          cap_ek ptr_ek cap_dk ptr_dk w192 optEnc w0 w8 w16 w24 w32 w40 w48 Rest
          hcl3 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx9_3 htr3

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced (
  EncoderFromPbPlacedOkExt
  seq_clean_lscl
  v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb_placed
  v1_drop_glue_proto_poly_encoder_mem_ok_at_statesFromPb_placed
  v1_encoder_from_pb_ok_at_statesFromPb_placed
  v1_dealloc_ok_at_statesFromPb_placed
  v1_err_5940_placed
  v1_drop_sendingHdr_4332_placed
  v1_drop_sendingHdr_4204_placed
  v1_drop_uc_and_sendingHdr_3936_placed
  v1_drop_uc_and_sendingHdr_3872_placed
)
end CryptoVerification.SpqrV1.States.FromPb
