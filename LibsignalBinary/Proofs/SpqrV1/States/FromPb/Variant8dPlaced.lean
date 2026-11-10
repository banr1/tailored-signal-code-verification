/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8d
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8c
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 8 (`EkReceivedCt1Sampled`, `+1764`, Block `333`) — Part D

Relocatable (`Obj.MultiPlacedLib`) `<PolyEncoder>::from_pb` setup and result dispatch
(`+10836 -> +10900`, `+10904 -> +10916 | +11264`), 5-vector error cleanup (`+10916 -> +4240`), and
`Ok(enc)` epilogue staging (`+11264 -> +8180`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dPlaced

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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local arm64_norm, local wp_norm]
  v8_orr_x27_w80
  v8_w80_d97
  v8_w80_h101
  v8_w80_b103
  v8_zext32_setWidth8
  v8_fsp_1888_add_89
  v8_fsp_1888_add_93
  v8_fsp_1888_add_113
  v8_fsp_1888_add_137
  v8_fsp_848_add_39
  v8_fsp_848_add_15

/-! ## 1. `PolyEncoder::from_pb` Result Check (`+10904`) and Error Cleanup (`+10916 -> +4240`) -/

/-- Step `+10904 -> +10916` (`lsmpl.base 333 + 10904 -> + 10916`, 3 instructions) when `PolyEncoder::from_pb`
returns `Err` (`[sp + 1888] = 2#64`). -/
theorem v8_check_enc_res_10904_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 10904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10916#64) s
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = s.readReg64 .x19 ∧
        s2.readReg64 .x21 = s.readReg64 .x21 ∧
        s2.readReg64 .x22 = s.readReg64 .x22 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧
        s2.readReg64 .x28 = s.readReg64 .x28 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  change s.pc = (blkPl_333).base + 10904#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10916#64) s _ _
  wp_steps
  wp_done

/-- Step `+10904 -> +11264` (`lsmpl.base 333 + 10904 -> + 11264`, 3 instructions) when `PolyEncoder::from_pb`
returns `Ok(enc)` (`tag = 0#64 ∨ tag = 1#64`). -/
theorem v8_check_enc_res_10904_ok_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (tag : BitVec 64) (htag : tag = 0#64 ∨ tag = 1#64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 10904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11264#64) s
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x15 = tag ∧
        s2.readReg64 .x19 = s.readReg64 .x19 ∧
        s2.readReg64 .x21 = s.readReg64 .x21 ∧
        s2.readReg64 .x22 = s.readReg64 .x22 ∧
        s2.readReg64 .x23 = s.readReg64 .x23 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧
        s2.readReg64 .x28 = s.readReg64 .x28 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  change s.pc = (blkPl_333).base + 10904#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 11264#64) s _ _
  rcases htag with rfl | rfl
  · wp_steps; wp_done
  · wp_steps; wp_done

/-- Tail at `+10992 -> +4240` (`lsmpl.base 333 + 10992 -> + 4240`):
loads `x1 = [sp + 64]` (`ca5`), sets `x9 = x21` (`pa5`), and deallocates `(ca5, pa5)` via `+11220`
or branches directly to `+4240` via `+11004`. -/
theorem v8_cleanup_vec5_10992_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out ca5 pa5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10992#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
        vecCapPtrDealloc A ca5 pa5 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v1_dealloc_ok_at_statesFromPb_placed hA
  simp only [rustDeallocSpec] at hdealloc
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
  dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  change s1.pc = (blkPl_333).base + 10992#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4240#64) s1 _ _
  by_cases hca5 : (ca5 == 0#64) = true <;>
    simp only [hca5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_
    wp_done
  · wp_steps; wp_apply; wp_steps
    refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_
    wp_done

/-- 5-vector cleanup at `+10916 -> +4240` (`lsmpl.base 333 + 10916 -> + 4240`) when `PolyEncoder::from_pb` returns `Err`:
deallocates `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)`, `(ca4, pa4)`, `(ca5, pa5)`,
sets `x20 = 0#64`, and branches to `+4240`. -/
theorem v8_cleanup_5vecs_10916_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10916#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (hx22_1 : s1.readReg64 .x22 = ca1) (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗ vecCapPtrDealloc A ca3 pa3 ∗
        vecCapPtrDealloc A ca4 pa4 ∗ vecCapPtrDealloc A ca5 pa5 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v1_dealloc_ok_at_statesFromPb_placed hA
  simp only [rustDeallocSpec] at hdealloc
  have h10992 := v8_cleanup_vec5_10992_placed hA s0
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
  dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc h10992 hpc1 ⊢
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 10940#64)
    (P_mid :=
      memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
      (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
      (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      (if (ca2 == 0#64) = true then emp else A.live pa2 ca2.toNat 1 ∗ memRegion pa2 ca2.toNat) ∗
      (if (ca3 == 0#64) = true then emp else A.live pa3 ca3.toNat 1 ∗ memRegion pa3 ca3.toNat) ∗
      (if (ca4 == 0#64) = true then emp else A.live pa4 ca4.toNat 1 ∗ memRegion pa4 ca4.toNat) ∗
      (if (ca5 == 0#64) = true then emp else A.live pa5 ca5.toNat 1 ∗ memRegion pa5 ca5.toNat) ∗
      A.pool ∗ Rest)
    (Q := fun s2 => s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x0 = pa2 ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = pa5 ∧ s2.readReg64 .x26 = ca3 ∧ s2.readReg64 .x28 = ca2 ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · change s1.pc = (blkPl_333).base + 10916#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10940#64) s1 _ _
    by_cases hca1 : (ca1 == 0#64) = true <;>
      simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx21_2, hx26_2, hx28_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 10960#64)
      (P_mid :=
        memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        (if (ca3 == 0#64) = true then emp else A.live pa3 ca3.toNat 1 ∗ memRegion pa3 ca3.toNat) ∗
        (if (ca4 == 0#64) = true then emp else A.live pa4 ca4.toNat 1 ∗ memRegion pa4 ca4.toNat) ∗
        (if (ca5 == 0#64) = true then emp else A.live pa5 ca5.toNat 1 ∗ memRegion pa5 ca5.toNat) ∗
        A.pool ∗ Rest)
      (Q := fun s3 => s3.sp = s0.sp - 2400#64 ∧ s3.readReg64 .x0 = pa3 ∧ s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = pa5 ∧ s3.readReg64 .x26 = ca3 ∧ TraceCalleeSaved s3 s0)
      ?_ ?_
    · change s2.pc = (blkPl_333).base + 10940#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10960#64) s2 _ _
      by_cases hca2 : (ca2 == 0#64) = true <;>
        simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply; wp_steps
        refine EncoderFromPb.align_pre (by rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx0_3, hx19_3, hx21_3, hx26_3, htr3⟩
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 10980#64)
        (P_mid :=
          memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          (if (ca4 == 0#64) = true then emp else A.live pa4 ca4.toNat 1 ∗ memRegion pa4 ca4.toNat) ∗
          (if (ca5 == 0#64) = true then emp else A.live pa5 ca5.toNat 1 ∗ memRegion pa5 ca5.toNat) ∗
          A.pool ∗ Rest)
        (Q := fun s4 => s4.sp = s0.sp - 2400#64 ∧ s4.readReg64 .x0 = pa4 ∧ s4.readReg64 .x1 = ca4 ∧
          s4.readReg64 .x19 = out ∧ s4.readReg64 .x21 = pa5 ∧ TraceCalleeSaved s4 s0)
        ?_ ?_
      · change s3.pc = (blkPl_333).base + 10960#64 at hpc3
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10980#64) s3 _ _
        by_cases hca3 : (ca3 == 0#64) = true <;>
          simp only [hca3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
        · wp_steps; wp_apply; wp_steps
          refine EncoderFromPb.align_pre (by rw [hsp3]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · intro s4 hpc4 hrun4 ⟨hsp4, hx0_4, hx1_4, hx19_4, hx21_4, htr4⟩
        refine EncoderFromPb.seq_clean
          (mid := lsmpl.base 333 + 10992#64)
          (P_mid :=
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
            (if (ca5 == 0#64) = true then emp else A.live pa5 ca5.toNat 1 ∗ memRegion pa5 ca5.toNat) ∗
            A.pool ∗
            ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
             (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
             (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ Rest))
          (Q := fun s5 => s5.sp = s0.sp - 2400#64 ∧ s5.readReg64 .x19 = out ∧
            s5.readReg64 .x21 = pa5 ∧ TraceCalleeSaved s5 s0)
          ?_ ?_
        · change s4.pc = (blkPl_333).base + 10980#64 at hpc4
          change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
            ((blkPl_333).base + 10992#64) s4 _ _
          by_cases hca4 : (ca4 == 0#64) = true <;>
            simp only [hca4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine EncoderFromPb.align_pre ?_ ?_
            · rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
              simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
            · wp_done
          · wp_steps; wp_apply
            refine EncoderFromPb.align_pre ?_ ?_
            · rw [v8_stackAt_encoderFromPb_split_7552 s0.sp, hsp4]
              simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
            · wp_done
        · intro s5 hpc5 hrun5 ⟨hsp5, hx19_5, hx21_5, htr5⟩
          have h5 := h10992 s5 out ca5 pa5
            ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
             (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
             (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ Rest)
            hsp0_align hpc5 hrun5 hsp5 hx19_5 hx21_5 htr5
          refine SepWP.mono h5 fun sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx20_f, htr_f⟩ => ?_
          rw [v8_stackAt_encoderFromPb_split_7552 s0.sp] at hPf
          exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, hx20_f, htr_f⟩

/-! ## 2. `PolyEncoder::from_pb` Setup (`+10836 -> +10900`) -/

/-- Steps `+10836 -> +10900` (`lsmpl.base 333 + 10836 -> + 10900`) when `w0.toNat < 2 ^ 63` (`sendingCt1 = some encPb`):
copies the 56-byte `Proto.PolyEncoder` header to `fsp + 240..296` and sets `x0 = fsp + 1888`, `x1 = fsp + 240`. -/
theorem v8_copy_enc_10836_to_10900_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA pa5 l1 u8 l2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (z240 z248 z256 z264 z272 z280 z288 : BitVec 64)
    (Rest : SepProp)
    (hw0_lt : w0.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10836#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa5)
    (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = l2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10900#64) s1
      ((((s0.sp - 2400#64) + 240#64) ↦₆₄ z240) ∗
        (((s0.sp - 2400#64) + 248#64) ↦₆₄ z248) ∗
        (((s0.sp - 2400#64) + 256#64) ↦₆₄ z256) ∗
        (((s0.sp - 2400#64) + 264#64) ↦₆₄ z264) ∗
        (((s0.sp - 2400#64) + 272#64) ↦₆₄ z272) ∗
        (((s0.sp - 2400#64) + 280#64) ↦₆₄ z280) ∗
        (((s0.sp - 2400#64) + 288#64) ↦₆₄ z288) ∗
        (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗
        (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
        ((pbA + 144#64) ↦₆₄ w8) ∗
        ((pbA + 152#64) ↦₆₄ w16) ∗
        ((pbA + 160#64) ↦₆₄ w24) ∗
        ((pbA + 168#64) ↦₆₄ w32) ∗
        ((pbA + 176#64) ↦₆₄ w40) ∗
        ((pbA + 184#64) ↦₆₄ w48) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
          (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗
          (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
          ((pbA + 144#64) ↦₆₄ w8) ∗
          ((pbA + 152#64) ↦₆₄ w16) ∗
          ((pbA + 160#64) ↦₆₄ w24) ∗
          ((pbA + 168#64) ↦₆₄ w32) ∗
          ((pbA + 176#64) ↦₆₄ w40) ∗
          ((pbA + 184#64) ↦₆₄ w48) ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
        sm.readReg64 .x1 = (s0.sp - 2400#64) + 240#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa5 ∧
        sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = l2 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hw0_ne : (w0 + 1#64 == 0#64) = false := v10_cap_add_one_beq_zero_false hw0_lt
  change s1.pc = (blkPl_333).base + 10836#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10900#64) s1 _ _
  wp_simp_pre only [v8_fsp_1528_split_1_7_rest, v8_pbA_144_realign_rest, v8_fsp_248_split_for_stur, sepConj_assoc]
  iterate 12 wp_step
  wp_simp_pre only [v8_pbA_144_unrealign_rest, sepConj_assoc]
  iterate 3 wp_step
  wp_simp_pre only [v8_fsp_257_realign_rest, sepConj_assoc]
  wp_step
  wp_simp_pre only [v8_fsp_248_realign_rest, v8_fsp_1528_unsplit_1_7_rest, sepConj_assoc]
  dsimp only [v1_optProtoPolyEncoderWordsAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_done

/-! ## 3. Staging `Ok(enc)` for Shared Epilogue (`+11264 -> +8180`, 77 instructions) -/

set_option maxHeartbeats 1600000 in
/-- Symbolic execution of `+11264 -> +8180` (`lsmpl.base 333 + 11264 -> + 8180`, 77 instructions). -/
theorem v8_stage_11264_to_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out tag l1 pa1 l2 pa2 ca3 pa3 pa4 ca5 pa5 w2280 : BitVec 64)
    (bs : List (BitVec 8))
    (d96 : BitVec 32) (u104 u112 u160 : BitVec 64) (d172 : BitVec 32) (u192 u208 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u887 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 11264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx15 : s.readReg64 .x15 = tag)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = pa5)
    (hx22 : s.readReg64 .x22 = l1)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = l2)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (((fsp + 64#64) ↦₆₄ ca5) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ pa1) ∗
        ((fsp + 216#64) ↦₆₄ pa4) ∗
        v8_stagingSlotsPre fsp d96 u104 u112 u160 d172 u192 u208 u232
          uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
          u832 uq848 u864 u880 u887 ∗
        v8_encCellsAt (fsp + 1888#64) bs ∗
        ((fsp + 2280#64) ↦₆₄ w2280) ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((fsp + 64#64) ↦₆₄ ca5) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 200#64) ↦₆₄ pa1) ∗
          ((fsp + 216#64) ↦₆₄ pa4) ∗
          v8_stagingSlotsPost fsp bs pa5 l2 ∗
          v8_encCellsAt (fsp + 1888#64) bs ∗
          ((fsp + 2280#64) ↦₆₄ w2280) ∗
          Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x6 = fsp + 576#64 ∧
        s2.readReg64 .x8 = 10#64 ∧
        s2.readReg64 .x15 = tag ∧
        s2.readReg64 .x20 = v8_wordAt bs 8 ∧
        s2.readReg64 .x13 = v8_wordAt bs 16 ∧
        s2.readReg64 .x25 = v8_wordAt bs 24 ∧
        s2.readReg64 .x30 = v8_wordAt bs 32 ∧
        s2.readReg64 .x9 = v8_wordAt bs 40 ∧
        s2.readReg64 .x14 = v8_wordAt bs 48 ∧
        s2.readReg64 .x18 = v8_wordAt bs 56 ∧
        s2.readReg64 .x17 = v8_wordAt bs 64 ∧
        s2.readReg64 .x0 = v8_wordAt bs 72 ∧
        (s2.readReg32 .x3).setWidth 8 = (v8_wordAt bs 80).extractLsb' 0 8 ∧
        s2.readReg32 .x27 = (v8_wordAt bs 80).extractLsb' 8 32 ∧
        ((s2.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v8_wordAt bs 80).extractLsb' 40 16 ∧
        ((s2.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v8_wordAt bs 80).extractLsb' 56 8 ∧
        s2.readReg64 .x4 = v8_wordAt bs 88 ∧
        s2.readReg64 .x5 = v8_wordAt bs 96 ∧
        (s2.readReg32 .x21).setWidth 8 = loByte (v8_wordAt bs 104) ∧
        s2.readReg64 .x7 = v8_wordAt bs 120 ∧
        s2.readReg64 .x2 = w2280 ∧
        s2.readReg64 .x11 = l1 ∧
        s2.readReg64 .x22 = pa1 ∧
        s2.readReg64 .x24 = l1 ∧
        s2.readReg64 .x10 = pa2 ∧
        s2.readReg64 .x26 = ca3 ∧
        s2.readReg64 .x12 = pa3 ∧
        s2.readReg64 .x1 = 2080#64 ∧
        s2.readReg64 .x28 = pa4 ∧
        s2.readReg64 .x16 = ca5 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x23 = fsp + 848#64 ∧
        TraceCalleeSaved s2 s0) := by
  subst hsp
  unfold v8_stagingSlotsPre v8_stagingSlotsPost v8_encCellsAt
  simp only [pointsTo128, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  change s.pc = (blkPl_333).base + 11264#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 8180#64) s _ _
  wp_simp_pre only [v8_fsp_1976_split_rest, v8_fsp_2024_realign_rest, sepConj_assoc]
  iterate 5 wp_step
  wp_simp_pre only [v8_fsp_2000_realign_rest, sepConj_assoc]
  iterate 40 wp_step
  wp_simp_pre only [v8_fsp_2024_unrealign_rest, sepConj_assoc]
  iterate 13 wp_step
  wp_simp_pre only [v8_fsp_880_realign_rest, sepConj_assoc]
  iterate 15 wp_step
  wp_simp_pre only [v8_fsp_856_realign_rest, sepConj_assoc]
  iterate 4 wp_step
  wp_simp_pre only [v8_fsp_856_unrealign_midQ128_rest, v8_fsp_1976_unsplit_rest,
    v8_fsp_2000_unrealign_rest, sepConj_assoc]
  wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dPlaced (
  v8_check_enc_res_10904_err_placed
  v8_check_enc_res_10904_ok_placed
  v8_cleanup_vec5_10992_placed
  v8_cleanup_5vecs_10916_placed
  v8_copy_enc_10836_to_10900_placed
  v8_stage_11264_to_8180_placed
)

end CryptoVerification.SpqrV1.States.FromPb
