/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsd
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 2 (`HeaderSent`, `+508`) — Part D

Relocatable Block-`333` subroutine bridges and cleanup paths (`+9132`, `+9112`, `+11024`, `+11240`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlaced

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
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm] v2hsd_bv_add_add_lit

/-! ## Subroutine Call Bridges -/

theorem v2hsd_sub_ok_drop_poly16_11028_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooks A ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 265)
      (withMemEq m (dropGluePoly16Spec A)) :=
  States.Recv.drop_glue_poly16_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hA.dealloc hcl

theorem v2hsd_sub_ok_drop_poly_encoder_11244_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooks A ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 272)
      (withMemEq m (dropGluePolyEncoderSpec A)) :=
  States.Recv.drop_glue_poly_encoder_local2_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hA.dealloc hcl

theorem drop_unchunked_ek_sent_cl_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_280 (Rust.withPanics ext)) (lsmpl.base 280)
      (withLsCodeLoaded lsmpl (dropUnchunkedEkSentSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 280)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_unchunked_ek_sent_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem v2hsd_sub_ok_drop_unchunked_ek_sent_11252_placed [LibsignalPlacement] {A : RustAlloc}
    {F : ShaCompress} {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooks A ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 280)
      (withMemEq m (dropUnchunkedEkSentSpec A F)) :=
  lscall_blk_cl (drop_unchunked_ek_sent_cl_placed_ok hA.dealloc) hcl (by decide)

theorem v2hsd_sub_ok_decoder_from_pb_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdec : DecoderFromPbPlacedOkExt A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376)
      (withLsCodeLoaded lsmpl (decoderFromPbSpec A)) :=
  hdec

/-! ## Cleanup Paths (`+9132`, `+9112`, `+11256`, `+11240`, `+11024`) -/

/-- Cleanup at `+9132 -> +9212`: loads `ca2` from `[sp + 232]` and `pa2` from `[sp + 184]`,
deallocates `(ca2, pa2)` and `(ca3, pa3)`, and reaches `+9212`. -/
theorem v2hsd_cleanup_9132_to_9212_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 pa3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9132#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 9192#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      A.pool ∗
      (((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗ Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hca2 : (ca2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 9132#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9192#64) s1 _ _
      simp only [hca2, ↓reduceIte, emp_sepConj]
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    · have hca2_f : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 9184#64)
        (P_mid :=
          stackAt fsp encoderFromPbStack ∗
          vecCapPtrDealloc A ca2 pa2 ∗
          A.pool ∗
          (((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A ca3 pa3 ∗
           (((fsp + 184#64) ↦₆₄ pa2) ∗
            ((fsp + 232#64) ↦₆₄ ca2) ∗ Frame)))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x0 = pa2 ∧
          sm.readReg64 .x1 = ca2 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = d0 ∧
          sm.readReg64 .x26 = ca3 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s1.pc = (blkPl_333).base + 9132#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 9184#64) s1 _ _
        wp_steps
        refine Drop.align_pre (by ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx22_2, hx26_2, htr2⟩
        have h9184 := v2hsc_cleanup_9184_to_9192_placed hA s0 s2 fsp out d0 ca2 pa2 ca3
          (((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A ca3 pa3 ∗
           (((fsp + 184#64) ↦₆₄ pa2) ∗
            ((fsp + 232#64) ↦₆₄ ca2) ∗ Frame))
          hca2_f hfsp_align hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2 hx22_2 hx26_2 htr2
        exact SepWP.mono h9184 fun sm Pm _ _ ⟨hPm, hq⟩ =>
          ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9192 := v2hsc_cleanup_9192_to_9212_placed hA s0 s2 fsp out d0 ca3 pa3
      (((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx26_2 htr2
    exact SepWP.mono h9192 fun sm Pm _ _ ⟨hPm, hq⟩ =>
      ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩

/-- Cleanup at `+9112 -> +9212` (`<PolyEncoder>::from_pb = Err`): deallocates `(ca1, pa1)`
(`[sp + 200] = ca1`, `[sp + 1272] = pa1`), `(ca2, pa2)` (`[sp + 232] = ca2`, `[sp + 184] = pa2`),
and `(ca3, pa3)` (`x26 = ca3`, `[sp + 176] = pa3`). -/
theorem v2hsd_cleanup_9112_to_9212_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9112#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := v2hsc_sub_ok_dealloc_placed (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 9132#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      A.pool ∗
      (((fsp + 200#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗ Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · refine SepWP.weaken_pre
      (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
    have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
    rw [show vecCapPtrDealloc A ca1 pa1 =
      (if (ca1 == 0#64) = true then emp else A.live pa1 ca1.toNat 1 ∗ memRegion pa1 ca1.toNat) from rfl]
    change s1.pc = (blkPl_333).base + 9112#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9132#64) s1 _ _
    by_cases hca1 : (ca1 == 0#64) = true <;>
      simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
            (((fsp + 184#64) ↦₆₄ pa2) ∗
             ((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 176#64) ↦₆₄ pa3) ∗
             vecCapPtrDealloc A ca2 pa2 ∗
             vecCapPtrDealloc A ca3 pa3 ∗
             A.pool ∗
             (((fsp + 200#64) ↦₆₄ ca1) ∗
              ((fsp + 1272#64) ↦₆₄ pa1) ∗ Frame)) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
    · wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [hsp1]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
            (((fsp + 184#64) ↦₆₄ pa2) ∗
             ((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 176#64) ↦₆₄ pa3) ∗
             vecCapPtrDealloc A ca2 pa2 ∗
             vecCapPtrDealloc A ca3 pa3 ∗
             A.pool ∗
             (((fsp + 200#64) ↦₆₄ ca1) ∗
              ((fsp + 1272#64) ↦₆₄ pa1) ∗ Frame)) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9132 := v2hsd_cleanup_9132_to_9212_placed hA s0 s2 fsp out d0 ca2 pa2 ca3 pa3
      (((fsp + 200#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx26_2 htr2
    exact SepWP.mono h9132 fun sm Pm _ _ ⟨hPm, hq⟩ =>
      ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩

/-- Execution segment `+11256 -> +9228` (`mov w23, wzr; b +9228`): sets `x23 = 0#64` and jumps to `+9228`. -/
theorem v2hsd_cleanup_11256_to_9228_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 11256#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      Rest
      (fun sm Pm =>
        (Pm ⊢ Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  change s1.pc = (blkPl_333).base + 11256#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9228#64) s1 _ _
  wp_steps
  wp_done

/-- Cleanup at `+11240 -> +9228` (`0x5cc8c -> 0x5c4b0`, when `<PolyDecoder>::from_pb = Err`):
drops `polyEncoderAt A (fsp + 1392) enc`, drops `unchunkedEkSentAt A (fsp + 1264) uc`,
sets `x23 = 0#64`, and jumps to `+9228`. -/
theorem v2hsd_cleanup_11240_to_9228_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out : BitVec 64)
    (enc : PolyEncoder) (uc : LibsignalSpqrV1.Unchunked.SendEk.EkSent (spqrAuthApi F))
    (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11240#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A (fsp + 1392#64) enc ∗
        unchunkedEkSentAt A (fsp + 1264#64) uc ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 11256#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      memRegion (fsp + 1392#64) 400 ∗
      memRegion (fsp + 1264#64) 80 ∗
      A.pool ∗
      Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · refine SepWP.weaken_pre
      (sepConj_mono_left (v2hsd_stackAt_encoderFromPbStack_to_dropStack32 fsp)) ?_
    refine seq_clean_lscl hcl1 (mid := lsmpl.base 333 + 11248#64)
      (P_mid :=
        (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
        memRegion (fsp + 1392#64) 400 ∗
        unchunkedEkSentAt A (fsp + 1264#64) uc ∗
        A.pool ∗
        Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · have hdrop_enc := v2hsd_sub_ok_drop_poly_encoder_11244_placed hA hcl1
      simp only [withMemEq, dropGluePolyEncoderSpec, dropGluePoly16Stack] at hdrop_enc
      dsimp only [polyEncoderSize, BitVec.ofNat_eq_ofNat] at hdrop_enc hpc1 ⊢
      change s1.pc = (blkPl_333).base + 11240#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 11248#64) s1 _ _
      wp_steps
      wp_apply
      refine Drop.align_pre (by rw [hsp1]; ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
      have hdrop_uc := v2hsd_sub_ok_drop_unchunked_ek_sent_11252_placed (F := F) hA hcl2
      simp only [withMemEq, dropUnchunkedEkSentSpec] at hdrop_uc
      rcases uc with ⟨epoch, ⟨rootKey, macKey⟩, hdr⟩
      dsimp only [unchunkedEkSentSize, BitVec.ofNat_eq_ofNat] at hdrop_uc hpc2 ⊢
      change s2.pc = (blkPl_333).base + 11248#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 11256#64) s2 _ _
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v2hsd_stackAt_dropStack32_to_encoderFromPbStack fsp
        rw [hsp2]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
            (memRegion (fsp + 1392#64) 400 ∗
             memRegion (fsp + 1264#64) 80 ∗
             A.pool ∗ Frame) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    exact v2hsd_cleanup_11256_to_9228_placed s0 s2 fsp out _ hpc2 hrun2 hsp2 hx19_2 htr2

/-- Execution segment `+11024 -> +11032`: drops `[Poly; 16]` at `fsp + 1400#64` (`x23 + 8#64`) via `v2hsd_sub_ok_drop_poly16_11028_placed`
and combines with the tag and tail to leave `memRegion (fsp + 1392#64) 400`. -/
theorem v2hsd_drop_poly16_11024_to_11032_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out ca3 : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11024#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11032#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A (fsp + 1392#64) enc ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) := by
  have hdrop := v2hsd_sub_ok_drop_poly16_11028_placed hA hcl1
  simp only [withMemEq, dropGluePoly16Spec, dropGluePoly16Stack] at hdrop
  refine SepWP.weaken_pre (v2hsd_drop_poly16_pre A fsp enc Frame) ?_
  apply ProofLib.SepWP.exists_left; intro tag
  apply ProofLib.SepWP.exists_left; intro vecs
  apply ProofLib.SepWP.pure_elim; intro hvecs_len
  dsimp only [polyArrayBytes, BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
  change s1.pc = (blkPl_333).base + 11024#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 11032#64) s1 _ _
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hdrop ⊢
  wp_steps
  wp_apply
  refine EncoderFromPb.align_pre ?_ ?_
  · have hst := v2hsd_stackAt_dropStack32_to_encoderFromPbStack fsp
    have hjoin := v2hsd_polyEncoder_1392_join fsp tag
    rw [hsp1]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
        (((fsp + 1392#64) ↦₆₄ tag) ∗
          memRegion (fsp + 1400#64) 384 ∗
          memRegion (fsp + 1784#64) 8) ∗
        (A.pool ∗ Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hst (sepConj_mono_left hjoin)) (Entails.of_eq (by ac_rfl))
  · wp_done

/-- Execution segment `+11072 -> +11256`: deallocates `(ca3, pa3)` (`x26 = ca3`, `[sp + 176] = pa3`). -/
theorem v2hsd_cleanup_11072_to_11256_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out ca3 pa3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11072#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11256#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := v2hsc_sub_ok_dealloc_placed (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  change s1.pc = (blkPl_333).base + 11072#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 11256#64) s1 _ _
  by_cases hca3 : (ca3 == 0#64) = true <;>
    simp only [hca3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre (sepConj_mono_left hst) ?_
    wp_done
  · wp_steps
    wp_apply
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 176#64) ↦₆₄ pa3) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

/-- Execution segment `+11052 -> +11072`: deallocates `(ca2, pa2)` (`[sp + 232] = ca2`, `[sp + 184] = pa2`). -/
theorem v2hsd_cleanup_11052_to_11072_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out ca2 pa2 ca3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11052#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11072#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := v2hsc_sub_ok_dealloc_placed (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  change s1.pc = (blkPl_333).base + 11052#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 11072#64) s1 _ _
  by_cases hca2 : (ca2 == 0#64) = true <;>
    simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre (sepConj_mono_left hst) ?_
    wp_done
  · wp_steps
    wp_apply
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 232#64) ↦₆₄ ca2) ∗
           ((fsp + 184#64) ↦₆₄ pa2) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

/-- Execution segment `+11032 -> +11052`: deallocates `(ca1, pa1)` (`[sp + 200] = ca1`, `[sp + 1272] = pa1`). -/
theorem v2hsd_cleanup_11032_to_11052_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out ca1 pa1 ca3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11032#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11052#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := v2hsc_sub_ok_dealloc_placed (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  change s1.pc = (blkPl_333).base + 11032#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 11052#64) s1 _ _
  by_cases hca1 : (ca1 == 0#64) = true <;>
    simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre (sepConj_mono_left hst) ?_
    wp_done
  · wp_steps
    wp_apply
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 200#64) ↦₆₄ ca1) ∗
           ((fsp + 1272#64) ↦₆₄ pa1) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

/-- Full cleanup at `+11024 -> +9228` (`receivingCt1 = none`): drops `[Poly; 16]` at `fsp + 1400`,
deallocates `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)`, sets `x23 = 0#64`, and reaches `+9228`. -/
theorem v2hsd_cleanup_11024_to_9228_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11024#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A (fsp + 1392#64) enc ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 11032#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 200#64) ↦₆₄ ca1) ∗
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      vecCapPtrDealloc A ca1 pa1 ∗
      A.pool ∗
      (memRegion (fsp + 1392#64) 400 ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 176#64) ↦₆₄ pa3) ∗
       vecCapPtrDealloc A ca2 pa2 ∗
       vecCapPtrDealloc A ca3 pa3 ∗
       Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have h11024 := v2hsd_drop_poly16_11024_to_11032_placed hA s0 s1 fsp out ca3 enc
      (((fsp + 200#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 176#64) ↦₆₄ pa3) ∗
       vecCapPtrDealloc A ca1 pa1 ∗
       vecCapPtrDealloc A ca2 pa2 ∗
       vecCapPtrDealloc A ca3 pa3 ∗
       Frame)
      hcl1 hfsp_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 htr1
    exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono h11024 fun sm Pm _ _ ⟨hPm, hq⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩)
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 11052#64)
      (P_mid :=
        stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        A.pool ∗
        (memRegion (fsp + 1392#64) 400 ∗
         ((fsp + 200#64) ↦₆₄ ca1) ∗
         ((fsp + 1272#64) ↦₆₄ pa1) ∗
         ((fsp + 176#64) ↦₆₄ pa3) ∗
         vecCapPtrDealloc A ca3 pa3 ∗
         Frame))
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · have h11032 := v2hsd_cleanup_11032_to_11052_placed hA s0 s2 fsp out ca1 pa1 ca3
        (memRegion (fsp + 1392#64) 400 ∗
         ((fsp + 232#64) ↦₆₄ ca2) ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         ((fsp + 176#64) ↦₆₄ pa3) ∗
         vecCapPtrDealloc A ca2 pa2 ∗
         vecCapPtrDealloc A ca3 pa3 ∗
         Frame)
        hfsp_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2
      exact SepWP.mono h11032 fun sm Pm _ _ ⟨hPm, hq⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 11072#64)
        (P_mid :=
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          vecCapPtrDealloc A ca3 pa3 ∗
          A.pool ∗
          (memRegion (fsp + 1392#64) 400 ∗
           ((fsp + 200#64) ↦₆₄ ca1) ∗
           ((fsp + 1272#64) ↦₆₄ pa1) ∗
           ((fsp + 232#64) ↦₆₄ ca2) ∗
           ((fsp + 184#64) ↦₆₄ pa2) ∗
           Frame))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x26 = ca3 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · have h11052 := v2hsd_cleanup_11052_to_11072_placed hA s0 s3 fsp out ca2 pa2 ca3
          (memRegion (fsp + 1392#64) 400 ∗
           ((fsp + 200#64) ↦₆₄ ca1) ∗
           ((fsp + 1272#64) ↦₆₄ pa1) ∗
           ((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A ca3 pa3 ∗
           Frame)
          hfsp_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
        exact SepWP.mono h11052 fun sm Pm _ _ ⟨hPm, hq⟩ =>
          ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩
      · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx26_4, htr4⟩
        refine EncoderFromPb.seq_clean
          (mid := lsmpl.base 333 + 11256#64)
          (P_mid :=
            stackAt fsp encoderFromPbStack ∗
            memRegion (fsp + 1392#64) 400 ∗
            ((fsp + 200#64) ↦₆₄ ca1) ∗
            ((fsp + 1272#64) ↦₆₄ pa1) ∗
            ((fsp + 232#64) ↦₆₄ ca2) ∗
            ((fsp + 184#64) ↦₆₄ pa2) ∗
            ((fsp + 176#64) ↦₆₄ pa3) ∗
            A.pool ∗ Frame)
          (Q := fun sm =>
            sm.sp = fsp ∧
            sm.readReg64 .x19 = out ∧
            TraceCalleeSaved sm s0)
          ?_ ?_
        · have h11072 := v2hsd_cleanup_11072_to_11256_placed hA s0 s4 fsp out ca3 pa3
            (memRegion (fsp + 1392#64) 400 ∗
             ((fsp + 200#64) ↦₆₄ ca1) ∗
             ((fsp + 1272#64) ↦₆₄ pa1) ∗
             ((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 184#64) ↦₆₄ pa2) ∗
             Frame)
            hfsp_align hpc4 hrun4 hsp4 hx19_4 hx26_4 htr4
          exact SepWP.mono h11072 fun sm Pm _ _ ⟨hPm, hq⟩ =>
            ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩
        · intro s5 hpc5 hrun5 ⟨hsp5, hx19_5, htr5⟩
          exact v2hsd_cleanup_11256_to_9228_placed s0 s5 fsp out _ hpc5 hrun5 hsp5 hx19_5 htr5

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlaced (
  v2hsd_sub_ok_drop_poly16_11028_placed
  v2hsd_sub_ok_drop_poly_encoder_11244_placed
  drop_unchunked_ek_sent_cl_placed_ok
  v2hsd_sub_ok_drop_unchunked_ek_sent_11252_placed
  v2hsd_sub_ok_decoder_from_pb_placed
  v2hsd_cleanup_9132_to_9212_placed
  v2hsd_cleanup_9112_to_9212_placed
  v2hsd_cleanup_11256_to_9228_placed
  v2hsd_cleanup_11240_to_9228_placed
  v2hsd_drop_poly16_11024_to_11032_placed
  v2hsd_cleanup_11072_to_11256_placed
  v2hsd_cleanup_11052_to_11072_placed
  v2hsd_cleanup_11032_to_11052_placed
  v2hsd_cleanup_11024_to_9228_placed
)

end CryptoVerification.SpqrV1.States.FromPb
