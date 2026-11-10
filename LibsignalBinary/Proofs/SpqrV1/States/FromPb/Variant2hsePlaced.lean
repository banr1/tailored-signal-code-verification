/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 2 (`HeaderSent`, `+508`) — Part E

Relocatable Block-`333` `Unchunked::EkSent` assembly (`+8908..+9032`), `sendingEk = none`
cleanup, and `ProtoPolynomialEncoder` staging (`+9036..+9096`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsePlaced

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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v2hse_bv_add_add_lit
  v2hse_pa1_d1273
  v2hse_pa1_b1279
  v2hse_pa1_h1277
  v2hse_pa1_b1272
  v2hse_fsp_1264_add_9
  v2hse_fsp_1264_add_13

/-! ## `+8908 .. +9032` Stepping -/

/-- Execution segment `+8908 -> +8932`: shifts `x26 = (pa1.extractLsb' 8 56).zeroExtend 64`,
and deallocates `(cap_ek, ptr_ek)` (`x24 = cap_ek`, `x25 = ptr_ek`). -/
theorem v2hse_dealloc_8908_to_8932_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out d0 pa1 cap_ek ptr_ek pbA epoch : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 8908#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx24_1 : s1.readReg64 .x24 = cap_ek)
    (hx25_1 : s1.readReg64 .x25 = ptr_ek)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8932#64) s1
      (stackAt fsp encoderFromPbStack ∗
        vecCapPtrDealloc A cap_ek ptr_ek ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt fsp encoderFromPbStack ∗ A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := v2hsc_sub_ok_dealloc_placed (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  change s1.pc = (blkPl_333).base + 8908#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 8932#64) s1 _ _
  by_cases hcap : (cap_ek == 0#64) = true <;>
    simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
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
          (A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

/-- Execution segment `+8932 -> +8960` when `ca1.toNat < 2 ^ 63`: loads `x25 = ca1` from `[sp + 200]`,
skips `b.eq +9148`, computes `x8`, `x9`, `x10 = fsp + 1264`, and stores `pa1.extractLsb' 8 32`
at `[fsp + 1273]`. -/
theorem v2hse_step_8932_to_8960_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out d0 ca1 pa1 pbA epoch d1273_old : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hca1 : ca1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 8932#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx26_1 : s1.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8960#64) s1
      (((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1273#64) ↦₃₂ d1273_old.setWidth 32) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1273#64) ↦₃₂ pa1.extractLsb' 8 32) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 48 16).zeroExtend 64 ∧
        sm.readReg64 .x9 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 32 32).zeroExtend 64 ∧
        sm.readReg64 .x10 = fsp + 1264#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = ca1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) := by
  have hca1_ne := cap_add_one_beq_zero_false hca1
  change s1.pc = (blkPl_333).base + 8932#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 8960#64) s1 _ _
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- Execution segment `+8960 -> +9032`: finishes assembling `v2hse_unchunkedEkSentWordsAt (fsp + 1264)`
from `[sp + 96] = la3`, `[sp + 152] = ca3`, `[sp + 176] = pa3`, `[sp + 184] = pa2`,
`[sp + 232] = ca2`, loads `x8 = cap_enc` from `[sp + 976]`, and sets `pstate = addsPState64 cap_enc 1#64`. -/
theorem v2hse_step_8960_to_9032_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State)
    (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA
     u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 8960#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx8_1 : s1.readReg64 .x8 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 48 16).zeroExtend 64)
    (hx9_1 : s1.readReg64 .x9 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 32 32).zeroExtend 64)
    (hx10_1 : s1.readReg64 .x10 = fsp + 1264#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9032#64) s1
      (((fsp + 96#64) ↦₆₄ la3) ∗
        ((fsp + 152#64) ↦₆₄ ca3) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 976#64) ↦₆₄ cap_enc) ∗
        ((fsp + 1264#64) ↦₆₄ u0) ∗
        ((fsp + 1272#64) ↦₈ u8.extractLsb' 0 8) ∗
        ((fsp + 1273#64) ↦₃₂ pa1.extractLsb' 8 32) ∗
        ((fsp + 1277#64) ↦₁₆ u8.extractLsb' 40 16) ∗
        ((fsp + 1279#64) ↦₈ u8.extractLsb' 56 8) ∗
        ((fsp + 1280#64) ↦₆₄ u16) ∗
        ((fsp + 1288#64) ↦₆₄ u24) ∗
        ((fsp + 1296#64) ↦₆₄ u32) ∗
        ((fsp + 1304#64) ↦₆₄ u40) ∗
        ((fsp + 1312#64) ↦₆₄ u48) ∗
        ((fsp + 1320#64) ↦₆₄ u56) ∗
        ((fsp + 1328#64) ↦₆₄ u64) ∗
        ((fsp + 1336#64) ↦₆₄ u72) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 96#64) ↦₆₄ la3) ∗
          ((fsp + 152#64) ↦₆₄ ca3) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 976#64) ↦₆₄ cap_enc) ∗
          v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 ca1 ca2 pa2 ca2 ca3 pa3 la3 epoch ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pa2 ∧
        sm.readReg64 .x8 = cap_enc ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = ca1 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        sm.pstate = addsPState64 cap_enc 1#64 ∧
        TraceCalleeSaved sm s0) := by
  change s1.pc = (blkPl_333).base + 8960#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9032#64) s1 _ _
  wp_steps
  wp_simp_pre only [v2hse_1272_unsplit_rest, sepConj_assoc]
  refine EncoderFromPb.align_pre ?_ ?_
  · unfold v2hse_unchunkedEkSentWordsAt
    simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    exact Entails.of_eq (by ac_rfl)
  · wp_done

/-- Combined `+8932 -> +9032`: starting with `memRegion (fsp + 1264) 80`, steps through `+8960`
to `+9032` and produces `v2hse_unchunkedEkSentWordsAt (fsp + 1264)`. -/
theorem v2hse_step_8932_to_9032_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State)
    (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hca1 : ca1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 8932#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx26_1 : s1.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9032#64) s1
      (((fsp + 96#64) ↦₆₄ la3) ∗
        ((fsp + 152#64) ↦₆₄ ca3) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 976#64) ↦₆₄ cap_enc) ∗
        memRegion (fsp + 1264#64) 80 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 96#64) ↦₆₄ la3) ∗
          ((fsp + 152#64) ↦₆₄ ca3) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 976#64) ↦₆₄ cap_enc) ∗
          v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 ca1 ca2 pa2 ca2 ca3 pa3 la3 epoch ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pa2 ∧
        sm.readReg64 .x8 = cap_enc ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = ca1 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        sm.pstate = addsPState64 cap_enc 1#64 ∧
        TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (v2hse_memRegion_1264_80_split fsp))))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u72
  apply ProofLib.SepWP.exists_left; intro u64
  apply ProofLib.SepWP.exists_left; intro u56
  apply ProofLib.SepWP.exists_left; intro u48
  apply ProofLib.SepWP.exists_left; intro u40
  apply ProofLib.SepWP.exists_left; intro u32
  apply ProofLib.SepWP.exists_left; intro u24
  apply ProofLib.SepWP.exists_left; intro u16
  apply ProofLib.SepWP.exists_left; intro u8
  apply ProofLib.SepWP.exists_left; intro u0
  wp_simp_pre only [v2hse_1272_split_rest, sepConj_assoc]
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 8960#64)
    (P_mid :=
      ((fsp + 200#64) ↦₆₄ ca1) ∗
      ((fsp + 1273#64) ↦₃₂ pa1.extractLsb' 8 32) ∗
      (((fsp + 96#64) ↦₆₄ la3) ∗
       ((fsp + 152#64) ↦₆₄ ca3) ∗
       ((fsp + 176#64) ↦₆₄ pa3) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗
       ((fsp + 976#64) ↦₆₄ cap_enc) ∗
       ((fsp + 1264#64) ↦₆₄ u0) ∗
       ((fsp + 1272#64) ↦₈ u8.extractLsb' 0 8) ∗
       ((fsp + 1277#64) ↦₁₆ u8.extractLsb' 40 16) ∗
       ((fsp + 1279#64) ↦₈ u8.extractLsb' 56 8) ∗
       ((fsp + 1280#64) ↦₆₄ u16) ∗
       ((fsp + 1288#64) ↦₆₄ u24) ∗
       ((fsp + 1296#64) ↦₆₄ u32) ∗
       ((fsp + 1304#64) ↦₆₄ u40) ∗
       ((fsp + 1312#64) ↦₆₄ u48) ∗
       ((fsp + 1320#64) ↦₆₄ u56) ∗
       ((fsp + 1328#64) ↦₆₄ u64) ∗
       ((fsp + 1336#64) ↦₆₄ u72) ∗
       Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x8 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 48 16).zeroExtend 64 ∧
      sm.readReg64 .x9 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 32 32).zeroExtend 64 ∧
      sm.readReg64 .x10 = fsp + 1264#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x23 = pa1 ∧
      sm.readReg64 .x25 = ca1 ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = epoch ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have hd1273 : u8.extractLsb' 8 32 = ((u8 >>> 8).setWidth 32) := by bv_kernel
    rw [hd1273]
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (v2hse_step_8932_to_8960_placed s0 s1 fsp out d0 ca1 pa1 pbA epoch (u8 >>> 8) _
        hfsp_align hca1 hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 htr1)
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx9_2, hx10_2, hx19_2, hx22_2, hx23_2, hx25_2, hx27_2, hx28_2, htr2⟩
    have h8960 := v2hse_step_8960_to_9032_placed (ext := ext) s0 s2 fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA
      u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 (((fsp + 200#64) ↦₆₄ ca1) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx8_2 hx9_2 hx10_2 hx19_2 hx22_2 hx23_2 hx25_2 hx27_2 hx28_2 htr2
    exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono h8960 fun sm Pm _ _ ⟨hPm, hq⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩)

/-- When `cap_enc = noneCap` at `+9032`, takes `b.eq +9152` and runs `v2hsc_cleanup_9152_to_9212_placed`
to deallocate `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)` and reach `+9212`. -/
theorem v2hse_none_enc_9032_to_9212_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9032#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
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
          memRegion (fsp + 1264#64) 80 ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 9152#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A ca1 pa1 ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      A.pool ∗ Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x0 = pa2 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x25 = ca1 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hpstate1 ⊢
    change s1.pc = (blkPl_333).base + 9032#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9152#64) s1 _ _
    wp_steps
    wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx25_2, hx26_2, htr2⟩
    unfold v2hse_unchunkedEkSentWordsAt
    simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    have h9152 := v2hsc_cleanup_9152_to_9212_placed hA s0 s2 fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3
      (((fsp + 1264#64) ↦₆₄ ca1) ∗
       ((fsp + 1280#64) ↦₆₄ la1) ∗
       ((fsp + 1288#64) ↦₆₄ ca2) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗
       ((fsp + 1304#64) ↦₆₄ la2) ∗
       ((fsp + 1312#64) ↦₆₄ ca3) ∗
       ((fsp + 1320#64) ↦₆₄ pa3) ∗
       ((fsp + 1328#64) ↦₆₄ la3) ∗
       ((fsp + 1336#64) ↦₆₄ epoch) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx25_2 hx26_2 htr2
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono h9152 fun sm Pm _ _ ⟨hPm, hq⟩ => ?_)
    refine ⟨Entails.trans hPm ?_, hq⟩
    have hm80 := v2hse_unchunkedEkSentWordsAt_entails_80 (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch
    unfold v2hse_unchunkedEkSentWordsAt at hm80
    simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm80
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 1264#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗
       ((fsp + 1280#64) ↦₆₄ la1) ∗
       ((fsp + 1288#64) ↦₆₄ ca2) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗
       ((fsp + 1304#64) ↦₆₄ la2) ∗
       ((fsp + 1312#64) ↦₆₄ ca3) ∗
       ((fsp + 1320#64) ↦₆₄ pa3) ∗
       ((fsp + 1328#64) ↦₆₄ la3) ∗
       ((fsp + 1336#64) ↦₆₄ epoch)) ∗
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗
       ((fsp + 176#64) ↦₆₄ pa3) ∗
       A.pool ∗ Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hm80) (Entails.of_eq (by ac_rfl))

/-! ## Encoder Copy (`+9036 .. +9096`) -/

set_option maxHeartbeats 800000 in
/-- Execution segment `+9036 -> +9096`: copies the 56-byte `ProtoPolynomialEncoder` words
`(w0, w8, w16, w24, w32, w40, w48)` into `fsp + 1792..1848`. -/
theorem v2hse_copy_enc_9032_to_9096_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out d0 ca3 pbA w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9036#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx8_1 : s1.readReg64 .x8 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9096#64) s1
      (((fsp + 984#64) ↦₆₄ w8) ∗
        ((pbA + 96#64) ↦₆₄ w8) ∗
        ((pbA + 104#64) ↦₆₄ w16) ∗
        ((pbA + 112#64) ↦₆₄ w24) ∗
        ((pbA + 120#64) ↦₆₄ w32) ∗
        ((pbA + 128#64) ↦₆₄ w40) ∗
        ((pbA + 136#64) ↦₆₄ w48) ∗
        memRegion (fsp + 1792#64) 56 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 984#64) ↦₆₄ w8) ∗
          ((pbA + 96#64) ↦₆₄ w8) ∗
          ((pbA + 104#64) ↦₆₄ w16) ∗
          ((pbA + 112#64) ↦₆₄ w24) ∗
          ((pbA + 120#64) ↦₆₄ w32) ∗
          ((pbA + 128#64) ↦₆₄ w40) ∗
          ((pbA + 136#64) ↦₆₄ w48) ∗
          v2hse_protoPolyEncoderWordsAt (fsp + 1792#64) w0 w8 w16 w24 w32 w40 w48 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1792#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = s1.readReg64 .x21 ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = s1.readReg64 .x23 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = s1.readReg64 .x28 ∧
        TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (v2hse_memRegion_1792_56_split fsp))))))))) ?_
  wp_simp_pre [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro e48
  apply ProofLib.SepWP.exists_left; intro e40
  apply ProofLib.SepWP.exists_left; intro e32
  apply ProofLib.SepWP.exists_left; intro e24
  apply ProofLib.SepWP.exists_left; intro e16
  apply ProofLib.SepWP.exists_left; intro e8
  apply ProofLib.SepWP.exists_left; intro e0
  change s1.pc = (blkPl_333).base + 9036#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9096#64) s1 _ _
  wp_simp_pre only [v2hse_fsp984_split_rest, v2hse_pbA96_to_unaligned16_rest,
    v2hse_fsp1800_to_unaligned16_rest, sepConj_assoc]
  iterate 10 wp_step
  wp_simp_pre only [v2hse_pbA96_to_threeWords_rest, sepConj_assoc]
  iterate 4 wp_step
  wp_simp_pre only [v2hse_fsp1800_to_threeWords_mixed_rest, v2hse_fsp984_unsplit_rest, sepConj_assoc]
  wp_step
  unfold v2hse_protoPolyEncoderWordsAt
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsePlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsePlaced (
  v2hse_dealloc_8908_to_8932_placed
  v2hse_step_8932_to_8960_placed
  v2hse_step_8960_to_9032_placed
  v2hse_step_8932_to_9032_placed
  v2hse_none_enc_9032_to_9212_placed
  v2hse_copy_enc_9032_to_9096_placed
)

end CryptoVerification.SpqrV1.States.FromPb
