/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Relocatable Variant 10 (`Ct2Sampled`, `+1632`) — Error & Cleanup Paths

Proves `[LibsignalPlacement]` Block `333` drop/dealloc bridges, OOM cold path (`+11572`), shared
error epilogues (`+2084`, `+2064`), and `Authenticator` cleanup deallocation paths (`+5844`, `+7236`,
`+7212`, `+5820`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

section

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## 1. Subroutine Bridges and OOM Cold Path (`+11572`) -/

/-- Subroutine contract for `core::ptr::drop_in_place<ProtoPolynomialEncoder>` on `lsProg_333`. -/
theorem v10_sub_ok_drop_proto_poly_encoder_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec A)) :=
  v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb_placed hA

/-- Subroutine contract for `alloc::__rust_dealloc` on `lsProg_333`. -/
theorem v10_sub_ok_dealloc_125316_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym)
      (rustDeallocSpec A) :=
  spqr_hook_ok_of_mem hA.dealloc

/-- Shared OOM cold path at `+11572` (`mov w0, #1; mov x1, x28; bl handle_error`). -/
theorem v10_states_from_pb_oom_11572_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (target_pc : BitVec 64) (P R : SepProp)
    (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11572#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hpanic := fromPb_externAt?_handleError hA
  clear hA
  change s.pc = (blkPl_333).base + 11572#64 at hpc
  change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s P Q _
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
  simpa only [statesFromPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm

/-! ## 2. Shared Error Epilogues at `+2084` and `+2064` -/

/-- Shared `Err(err)` exit at `+2084` (`lsmpl.base 333 + 2084 -> s0.x30`):
when `x21` has low byte `spqrErrorByte err` and `x19 = out`, writes `x21` to `[out + 8]`,
`noneCap, x26` to `[out + 16..32]`, and branches to `+60`. -/
theorem v10_states_from_pb_err_2084_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2084#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : (s1.readReg64 .x21).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
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
      ((out + 8#64) ↦₈ spqrErrorByte err) ∗
      memRegion (out + 9#64) 919 ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x8 = noneCap ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 2084#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 60#64) _ _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htail := out_8_32_entails_err_tail out (s1.readReg64 .x21)
        18446744073709551615#64 (s1.readReg64 .x26)
      rw [hx21_1] at htail
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ s1.readReg64 .x21) ∗
           ((out + 16#64) ↦₆₄ 18446744073709551615#64) ∗
           ((out + 24#64) ↦₆₄ s1.readReg64 .x26) ∗
           memRegion (out + 32#64) 896) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60_placed s0 s2 out err v0 Rest hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

/-- Shared `+2064` error epilogue (`lsmpl.base 333 + 2064 -> s0.x30`):
given `x23 = encAddr`, `x22 = noneCap` (`optEnc = none`) or `x22 = cap` with `cap.toNat < 2 ^ 63`
(`optEnc = some enc`), drops `optEnc` into `memRegion encAddr 56` and returns `Err(.stateDecode)`. -/
theorem v10_states_from_pb_err_2064_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out encAddr : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2064#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = encAddr)
    (hx22_1 : match optEnc with
      | none => s1.readReg64 .x22 = noneCap
      | some _ => (s1.readReg64 .x22).toNat < 2 ^ 63)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoPolynomialEncoderAt A encAddr optEnc ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion encAddr 56 ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 2084#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      (memRegion encAddr 56 ∗ A.pool ∗ Rest))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = 0#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · cases optEnc with
    | none =>
      rw [optProtoPolynomialEncoderAt_none']
      dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx22_1 ⊢
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 2064#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 2084#64) _ _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hm := optProtoPolyEncoder_none_entails_memRegion_56 encAddr
        dsimp only [noneCap] at hm
        refine Entails.trans
          (Entails.of_eq (show _ =
            ((encAddr ↦₆₄ 18446744073709551615#64) ∗ memRegion (encAddr + 8#64) 48) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             memRegion (s0.sp - 2400#64) 2304 ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
      · wp_done
    | some enc =>
      rw [optProtoPolynomialEncoderAt_some']
      have hne_none := cap_add_one_beq_zero_false hx22_1
      have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
        spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
      have hdrop := v1_drop_glue_proto_poly_encoder_mem_ok_at_statesFromPb_placed hA hcl1
      simp only [withMemEq, dropProtoPolyEncoderSpec] at hdrop
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_dropStack48 (s0.sp - 2400#64))) ?_
      dsimp only [protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 2064#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 2084#64) _ _ _
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_dropStack48_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp1] at hst
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp dropStack48 ∗ memRegion (s0.sp - 7552#64) 1008) ∗
            (memRegion (s0.sp - 2400#64) 2304 ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             (memRegion encAddr 56 ∗ A.pool ∗ Rest)) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, htr2⟩
    have hx21_b : (s2.readReg64 .x21).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx21_2]; rfl
    have hep := v10_states_from_pb_err_2084_placed (A := A) (F := F) (ext := ext) s0 s2 out .stateDecode
      (memRegion encAddr 56 ∗ A.pool ∗ Rest)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_b htr2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-! ## 3. Shared Error-Cleanup Deallocation Paths at `+5844`, `+7236`, `+7212`, and `+5820` -/

/-- Shared `+5844` transition (`+5844 -> +2084`): `mov x21, xzr; b +2084`. -/
theorem v10_states_from_pb_err_5844_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 5844#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2084#64) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 5844#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 2084#64) _ _ _
  wp_steps
  wp_done

/-- Shared `+7236` transition (`+7236 -> +2084`): when `(ca2 == 0#64) = false`,
deallocates `vecCapPtrDealloc A ca2 pa2` using `[sp + 184] = pa2` and `x26 = ca2`,
sets `x21 = 0`, and jumps to `+2084`. -/
theorem v10_states_from_pb_err_7236_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hca2_ne : (ca2 == 0#64) = false)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7236#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  dsimp only [vecCapPtrDealloc]
  simp only [hca2_ne, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v10_sub_ok_dealloc_125316_placed hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 7236#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 2084#64) _ _ _
  wp_steps
  wp_apply
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
    have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
    have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
    rw [haddr] at hst
    nth_rw 1 [← hsp1] at hst
    rw [h184]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
        (((s0.sp - 2216#64) ↦₆₄ pa2) ∗ A.pool ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_left hst
  · wp_done

/-- Shared `+7212` error-cleanup path (`+7212 -> +2084`):
deallocates `vecCapPtrDealloc A ca1 pa1` (`[sp + 200] = ca1`, `x21 = pa1`) and
`vecCapPtrDealloc A ca2 pa2` (`x26 = ca2`, `[sp + 184] = pa2`), sets `x21 = 0`, and reaches `+2084`. -/
theorem v10_states_from_pb_err_7212_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7212#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 7232#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x26 = ca2 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hca1 : (ca1 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hca1, ↓reduceIte, sepConj_emp, emp_sepConj]
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 7212#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 7232#64) _ _ _
      wp_steps
      wp_done
    · have hbeq : (ca1 == 0#64) = false := Bool.eq_false_iff.mpr hca1
      dsimp only [vecCapPtrDealloc]
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
        spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
      have hdealloc := v10_sub_ok_dealloc_125316_placed hA
      simp only [rustDeallocSpec] at hdealloc
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 7212#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 7232#64) _ _ _
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
        have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp1] at hst
        rw [h200, h184]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2200#64) ↦₆₄ ca1) ∗
             ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
             (if (ca2 == 0#64) = true then emp else A.live pa2 ca2.toNat 1 ∗ memRegion pa2 ca2.toNat) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  ·
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    by_cases hca2 : (ca2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hca2, ↓reduceIte, sepConj_emp, emp_sepConj]
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 5844#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗
          Rest)
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rw [← ls_blockPlacement_base (i := 333)] at hpc2 ⊢
        change s2.pc = (blkPl_333).base + 7232#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5844#64) _ _ _
        wp_steps
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, htr3⟩
        exact v10_states_from_pb_err_5844_placed s0 s3 out _ hpc3 hrun3 hsp3 hx19_3 htr3
    · have hbeq : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 7236#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          vecCapPtrDealloc A ca2 pa2 ∗
          A.pool ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x26 = ca2 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rw [← ls_blockPlacement_base (i := 333)] at hpc2 ⊢
        change s2.pc = (blkPl_333).base + 7232#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7236#64) _ _ _
        wp_steps
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
        have h7236 := v10_states_from_pb_err_7236_placed hA s0 s3 out ca2 pa2
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest)
          hbeq hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
        refine SepWP.mono h7236 ?_
        intro sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx21_f, htr_f⟩
        refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, hx21_f, htr_f⟩

/-- Shared `+5820` error-cleanup path (`+5820 -> +2084`):
deallocates `vecCapPtrDealloc A ca1 pa1` (`[sp + 200] = ca1`, `x21 = pa1`) and
`vecCapPtrDealloc A ca2 pa2` (`x26 = ca2`, `[sp + 184] = pa2`), sets `x21 = 0`, and reaches `+2084`. -/
theorem v10_states_from_pb_err_5820_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5820#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 5840#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x26 = ca2 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hca1 : (ca1 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hca1, ↓reduceIte, sepConj_emp, emp_sepConj]
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 5820#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5840#64) _ _ _
      wp_steps
      wp_done
    · have hbeq : (ca1 == 0#64) = false := Bool.eq_false_iff.mpr hca1
      dsimp only [vecCapPtrDealloc]
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
        spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
      have hdealloc := v10_sub_ok_dealloc_125316_placed hA
      simp only [rustDeallocSpec] at hdealloc
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 5820#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5840#64) _ _ _
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
        have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp1] at hst
        rw [h200, h184]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2200#64) ↦₆₄ ca1) ∗
             ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
             (if (ca2 == 0#64) = true then emp else A.live pa2 ca2.toNat 1 ∗ memRegion pa2 ca2.toNat) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  ·
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    by_cases hca2 : (ca2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hca2, ↓reduceIte, sepConj_emp, emp_sepConj]
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 5844#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗
          Rest)
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rw [← ls_blockPlacement_base (i := 333)] at hpc2 ⊢
        change s2.pc = (blkPl_333).base + 5840#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5844#64) _ _ _
        wp_steps
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, htr3⟩
        exact v10_states_from_pb_err_5844_placed s0 s3 out _ hpc3 hrun3 hsp3 hx19_3 htr3
    · have hbeq : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 7236#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          vecCapPtrDealloc A ca2 pa2 ∗
          A.pool ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x26 = ca2 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rw [← ls_blockPlacement_base (i := 333)] at hpc2 ⊢
        change s2.pc = (blkPl_333).base + 5840#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7236#64) _ _ _
        wp_steps
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
        have h7236 := v10_states_from_pb_err_7236_placed hA s0 s3 out ca2 pa2
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest)
          hbeq hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
        refine SepWP.mono h7236 ?_
        intro sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx21_f, htr_f⟩
        refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, hx21_f, htr_f⟩

end

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  v10_sub_ok_drop_proto_poly_encoder_placed
  v10_sub_ok_dealloc_125316_placed
  v10_states_from_pb_oom_11572_placed
  v10_states_from_pb_err_2084_placed
  v10_states_from_pb_err_2064_placed
  v10_states_from_pb_err_5844_placed
  v10_states_from_pb_err_7236_placed
  v10_states_from_pb_err_7212_placed
  v10_states_from_pb_err_5820_placed
)

end CryptoVerification.SpqrV1.States.FromPb
