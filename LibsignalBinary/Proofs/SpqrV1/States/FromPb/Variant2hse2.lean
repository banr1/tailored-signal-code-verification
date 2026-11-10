/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsd
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part E2

`<PolyEncoder>::from_pb` call at `+9096`, `Err` cleanup (`+9100 -> +9212`), and `Ok`
`PolyEncoder` stack relocation (`+9100 -> +9248 -> +9328`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_memset
  stubOff_handle_error
  fnOff_poly_encoder_from_pb
  fnOff_poly_decoder_from_pb

theorem v2hse2_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## `<PolyEncoder>::from_pb` Call (`+9096 -> +32996` / `+9100`) -/

theorem v2hse2_sub_ok_encoder_from_pb {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (henc : EncoderFromPbOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 32996#64)
      (encoderFromPbSpec A) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 32996) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff fnOff_poly_encoder_from_pb (by decide))
    henc

/-- Execute `bl 0x62188` at `+9096` to `<PolyEncoder>::from_pb` entry (`+32996`). -/
theorem v2hse2_bl_encoder_9096_to_32996
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out d0 ca3 pbA : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9096#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 1792#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx24_1 : s1.readReg64 .x24 = fsp + 1888#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 32996#64) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
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
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9100#64 ∧
        TraceCalleeSaved sm s0) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 9096 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-! ## `<PolyEncoder>::from_pb = Err` Cleanup (`+9100 -> +9112 -> +9212`) -/

theorem v2hse2_resultPolyEncoder_err_entails_tag_392 (A : RustAlloc) (fsp : BitVec 64)
    (err : PolynomialError) :
    resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ⊢
      ((fsp + 1888#64) ↦₆₄ 2#64) ∗ memRegion (fsp + 1896#64) 392 := by
  dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag,
    resultPolyEncoderErrByteOff, resultPolyEncoderErrTailSize]
  have hm8 : ((fsp + 1896#64) ↦₈ polynomialErrorByte err) ∗ memRegion (fsp + 1897#64) 391 ⊢
      memRegion (fsp + 1896#64) 392 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1896#64) (n := 1) (k := 391)
          (b' := fsp + 1897#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (fsp + 1896#64) (polynomialErrorByte err))
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  have ha1897 : (fsp + 1888#64) + 9#64 = fsp + 1897#64 := by bv_omega
  rw [ha1896, ha1897]
  exact sepConj_mono_right hm8

theorem v2hse2_1888_tag_392_to_memRegion_400 (fsp tag : BitVec 64) :
    ((fsp + 1888#64) ↦₆₄ tag) ∗ memRegion (fsp + 1896#64) 392 ⊢
      memRegion (fsp + 1888#64) 400 := by
  rw [ProofLib.memRegion_split' (b := fsp + 1888#64) (n := 8) (k := 392)
        (b' := fsp + 1896#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

/-- When `<PolyEncoder>::from_pb` returns `.error err` at `fsp + 1888`, steps `+9100 -> +9112`,
deallocates `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)` via `v2hsd_cleanup_9112_to_9212`, and reaches `+9212`. -/
theorem v2hse2_enc_err_9100_to_9212
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64)
    (err : PolynomialError) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  unfold v2hse_unchunkedEkSentWordsAt
  simp only [v2hse2_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (v2hse2_resultPolyEncoder_err_entails_tag_392 A fsp err))) ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9112#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 200#64) ↦₆₄ ca1) ∗
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A ca1 pa1 ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      A.pool ∗
      (memRegion (fsp + 1888#64) 400 ∗
       ((fsp + 1264#64) ↦₆₄ ca1) ∗
       ((fsp + 1280#64) ↦₆₄ la1) ∗
       ((fsp + 1288#64) ↦₆₄ ca2) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗
       ((fsp + 1304#64) ↦₆₄ la2) ∗
       ((fsp + 1312#64) ↦₆₄ ca3) ∗
       ((fsp + 1320#64) ↦₆₄ pa3) ∗
       ((fsp + 1328#64) ↦₆₄ la3) ∗
       ((fsp + 1336#64) ↦₆₄ epoch) ∗
       Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 9100 12
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_simp_pre [sepConj_assoc]
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have h400 := v2hse2_1888_tag_392_to_memRegion_400 fsp 2#64
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1888#64) ↦₆₄ 2#64) ∗ memRegion (fsp + 1896#64) 392) ∗
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 200#64) ↦₆₄ ca1) ∗
         ((fsp + 1272#64) ↦₆₄ pa1) ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         ((fsp + 232#64) ↦₆₄ ca2) ∗
         ((fsp + 176#64) ↦₆₄ pa3) ∗
         vecCapPtrDealloc A ca1 pa1 ∗
         vecCapPtrDealloc A ca2 pa2 ∗
         vecCapPtrDealloc A ca3 pa3 ∗
         A.pool ∗
         ((fsp + 1264#64) ↦₆₄ ca1) ∗
         ((fsp + 1280#64) ↦₆₄ la1) ∗
         ((fsp + 1288#64) ↦₆₄ ca2) ∗
         ((fsp + 1296#64) ↦₆₄ pa2) ∗
         ((fsp + 1304#64) ↦₆₄ la2) ∗
         ((fsp + 1312#64) ↦₆₄ ca3) ∗
         ((fsp + 1320#64) ↦₆₄ pa3) ∗
         ((fsp + 1328#64) ↦₆₄ la3) ∗
         ((fsp + 1336#64) ↦₆₄ epoch) ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h400) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9112 := v2hsd_cleanup_9112_to_9212 hA s0 s2 fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3
      (memRegion (fsp + 1888#64) 400 ∗
       ((fsp + 1264#64) ↦₆₄ ca1) ∗
       ((fsp + 1280#64) ↦₆₄ la1) ∗
       ((fsp + 1288#64) ↦₆₄ ca2) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗
       ((fsp + 1304#64) ↦₆₄ la2) ∗
       ((fsp + 1312#64) ↦₆₄ ca3) ∗
       ((fsp + 1320#64) ↦₆₄ pa3) ∗
       ((fsp + 1328#64) ↦₆₄ la3) ∗
       ((fsp + 1336#64) ↦₆₄ epoch) ∗
       Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx26_2 htr2
    refine SepWP.mono h9112 fun sm Pm _ _ ⟨hPm, hq⟩ => ⟨Entails.trans hPm ?_, hq⟩
    have hm80 := v2hse_unchunkedEkSentWordsAt_entails_80 (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch
    unfold v2hse_unchunkedEkSentWordsAt at hm80
    simp only [v2hse2_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm80
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
       memRegion (fsp + 1888#64) 400 ∗
       ((fsp + 200#64) ↦₆₄ ca1) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗
       ((fsp + 176#64) ↦₆₄ pa3) ∗
       A.pool ∗ Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hm80) (Entails.of_eq (by ac_rfl))

/-! ## `<PolyEncoder>::from_pb = Ok(enc)` Move (`+9100 -> +9248 -> +9328`) -/

def v2hse2_polyEncoderTag (enc : PolyEncoder) : BitVec 64 :=
  match enc.s with
  | .points _ => 0#64
  | .polys _ => 1#64

theorem v2hse2_polyEncoderTag_eq (enc : PolyEncoder) :
    v2hse2_polyEncoderTag enc = 0#64 ∨ v2hse2_polyEncoderTag enc = 1#64 := by
  unfold v2hse2_polyEncoderTag
  cases enc.s <;> simp

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_polyEncoderTag_sub_two_beq_zero (enc : PolyEncoder) :
    (v2hse2_polyEncoderTag enc - 2#64 == 0#64) = false := by
  rcases v2hse2_polyEncoderTag_eq enc with h | h <;> rw [h] <;> rfl

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_polyEncoderTag_bne_two (enc : PolyEncoder) :
    (v2hse2_polyEncoderTag enc != 2#64) = true := by
  rcases v2hse2_polyEncoderTag_eq enc with h | h <;> rw [h] <;> rfl

theorem v2hse2_resultPolyEncoder_ok_eq (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    resultPolyEncoderFromPbAt A a (.ok enc) = polyEncoderAt A a enc := rfl

theorem v2hse2_stackAt_encoderFromPbStack_eq_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack =
      memRegion (fsp - 4096#64) 4096 ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ memRegion (fsp - 4096#64) 4096 at h
  rw [h, sepConj_comm]

theorem v2hse2_pointsTo32_pair_eq_pointsTo64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes]
  change (a ↦ₛ unpack32 lo) ∗ ((a + BitVec.ofNat 64 (unpack32 lo).length) ↦ₛ unpack32 hi) = _
  rw [← ProofLib.pointsToBytes_append a (unpack32 lo) (unpack32 hi)]
  congr 1
  unfold unpack64 unpack32
  simp only [List.singleton_append, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem v2hse2_polyEncoderAt_relocate (A : RustAlloc) (a1 : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a1 enc ⊢
      ∃∗ bs : { l : List (BitVec 8) // l.length = 384 },
      ∃∗ hi32 : BitVec 32, ∃∗ P_heap : SepProp,
        ⌜(∀ a2 : BitVec 64,
          (a2 ↦₆₄ v2hse2_polyEncoderTag enc) ∗ ((a2 + 8#64) ↦ₛ bs.val) ∗
           ((a2 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
            polyEncoderAt A a2 enc)⌝ ∗
        (a1 ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((a1 + 8#64) ↦ₛ bs.val) ∗
        ((a1 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
        P_heap := by
  unfold polyEncoderAt encoderStateAt polyEncoderPointsTag polyEncoderPolysTag
    polyEncoderVecsOff polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize v2hse2_polyEncoderTag
  rw [ProofLib.memRegion_four (a1 + 396#64)]
  cases hs : enc.s with
  | points pts =>
    dsimp only
    rw [pointListOf_eq_vecGF16ListOf A pts (a1 + 8#64)]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (vecGF16ListOf_entails_headers_heaps A (pts.map Point.value) (a1 + 8#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi32
    apply Entails.sepExists_elim; intro pins
    apply Entails.pure_left; intro hpts_len
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpins_len
    have hbs_len : (vecHeadersBytesOf pins (pts.map Point.value)).length = 384 := by
      rw [length_vecHeadersBytesOf pins (pts.map Point.value) hpins_len, List.length_map, hpts_len.1]
      rfl
    have ha1_396 : a1 + 396#64 = (a1 + 392#64) + 4#64 := by bv_omega
    rw [ha1_396, v2hse2_pointsTo32_pair_eq_pointsTo64 (a1 + 392#64) enc.idx hi32]
    refine Entails.sepExists_right ⟨vecHeadersBytesOf pins (pts.map Point.value), hbs_len⟩
      (Entails.sepExists_right hi32
        (Entails.sepExists_right (vecGF16HeapList A pins (pts.map Point.value)) ?_))
    refine Entails.pure_right (fun a2 => ?_) (Entails.of_eq (by ac_rfl))
    rw [pointListOf_eq_vecGF16ListOf A pts (a2 + 8#64),
        ← v2hse2_pointsTo32_pair_eq_pointsTo64 (a2 + 392#64) enc.idx hi32]
    have ha2_396 : (a2 + 392#64) + 4#64 = a2 + 396#64 := by bv_omega
    rw [ha2_396]
    have hvec2 := headers_heaps_entails_vecGF16ListOf A pins (pts.map Point.value) (a2 + 8#64) hpins_len
    have hm4 : ((a2 + 396#64) ↦₃₂ hi32) ⊢ memRegion (a2 + 396#64) 4 := by
      rw [ProofLib.memRegion_four (a2 + 396#64)]
      exact Entails.sepExists_right hi32 (Entails.refl _)
    refine Entails.trans (Entails.of_eq (show _ =
      (a2 ↦₆₄ 0#64) ∗
      (((a2 + 8#64) ↦ₛ vecHeadersBytesOf pins (pts.map Point.value)) ∗
       vecGF16HeapList A pins (pts.map Point.value)) ∗
      ((a2 + 392#64) ↦₃₂ enc.idx) ∗
      ((a2 + 396#64) ↦₃₂ hi32) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono hvec2 (sepConj_mono_right hm4))) ?_
    exact Entails.pure_right hpts_len (Entails.of_eq (by ac_rfl))
  | polys ps =>
    dsimp only
    rw [polyListOf_eq_vecGF16ListOf A ps (a1 + 8#64)]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (vecGF16ListOf_entails_headers_heaps A (ps.map LibsignalSpqrV1.Poly.coefficients) (a1 + 8#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi32
    apply Entails.sepExists_elim; intro pins
    apply Entails.pure_left; intro hps_len
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpins_len
    have hbs_len : (vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients)).length = 384 := by
      rw [length_vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients) hpins_len, List.length_map, hps_len]
      rfl
    have ha1_396 : a1 + 396#64 = (a1 + 392#64) + 4#64 := by bv_omega
    rw [ha1_396, v2hse2_pointsTo32_pair_eq_pointsTo64 (a1 + 392#64) enc.idx hi32]
    refine Entails.sepExists_right ⟨vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients), hbs_len⟩
      (Entails.sepExists_right hi32
        (Entails.sepExists_right (vecGF16HeapList A pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ?_))
    refine Entails.pure_right (fun a2 => ?_) (Entails.of_eq (by ac_rfl))
    rw [polyListOf_eq_vecGF16ListOf A ps (a2 + 8#64),
        ← v2hse2_pointsTo32_pair_eq_pointsTo64 (a2 + 392#64) enc.idx hi32]
    have ha2_396 : (a2 + 392#64) + 4#64 = a2 + 396#64 := by bv_omega
    rw [ha2_396]
    have hvec2 := headers_heaps_entails_vecGF16ListOf A pins (ps.map LibsignalSpqrV1.Poly.coefficients) (a2 + 8#64) hpins_len
    have hm4 : ((a2 + 396#64) ↦₃₂ hi32) ⊢ memRegion (a2 + 396#64) 4 := by
      rw [ProofLib.memRegion_four (a2 + 396#64)]
      exact Entails.sepExists_right hi32 (Entails.refl _)
    refine Entails.trans (Entails.of_eq (show _ =
      (a2 ↦₆₄ 1#64) ∗
      (((a2 + 8#64) ↦ₛ vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ∗
       vecGF16HeapList A pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ∗
      ((a2 + 392#64) ↦₃₂ enc.idx) ∗
      ((a2 + 396#64) ↦₃₂ hi32) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono hvec2 (sepConj_mono_right hm4))) ?_
    exact Entails.pure_right hps_len (Entails.of_eq (by ac_rfl))

theorem v2hse2_bs384_w392_split_368 (bs : List (BitVec 8)) (hbs : bs.length = 384) (w392 : BitVec 64) :
    ∃ (w8 w16 w24 : BitVec 64) (tail368 : { l : List (BitVec 8) // l.length = 368 }),
      bs.take 8 = unpack64 w8 ∧
      ∀ a : BitVec 64,
        ((a + 8#64) ↦ₛ bs) ∗ ((a + 392#64) ↦₆₄ w392) =
          ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
          ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦ₛ tail368.val) := by
  have ht0 : (bs.take 8).length = 8 := by rw [List.length_take, hbs]; decide
  have ht1 : ((bs.drop 8).take 8).length = 8 := by rw [List.length_take, List.length_drop, hbs]; decide
  have ht2 : ((bs.drop 16).take 8).length = 8 := by rw [List.length_take, List.length_drop, hbs]; decide
  obtain ⟨w8, hw8⟩ := ProofLib.exists_unpack64_of_length_8 ht0
  obtain ⟨w16, hw16⟩ := ProofLib.exists_unpack64_of_length_8 ht1
  obtain ⟨w24, hw24⟩ := ProofLib.exists_unpack64_of_length_8 ht2
  have htail_len : (bs.drop 24 ++ unpack64 w392).length = 368 := by
    rw [List.length_append, List.length_drop, hbs, unpack64_length]
  refine ⟨w8, w16, w24, ⟨bs.drop 24 ++ unpack64 w392, htail_len⟩, hw8, fun a => ?_⟩
  have hbs0 : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  have hbs1 : bs.drop 8 = (bs.drop 8).take 8 ++ bs.drop 16 := by
    change bs.drop 8 = (bs.drop 8).take 8 ++ bs.drop (8 + 8)
    rw [← List.drop_drop, List.take_append_drop]
  have hbs2 : bs.drop 16 = (bs.drop 16).take 8 ++ bs.drop 24 := by
    change bs.drop 16 = (bs.drop 16).take 8 ++ bs.drop (16 + 8)
    rw [← List.drop_drop, List.take_append_drop]
  have hp0 : ((a + 8#64) ↦ₛ bs) =
      ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦ₛ bs.drop 8) := by
    conv_lhs => rw [hbs0]
    rw [ProofLib.pointsToBytes_append (a + 8#64) (bs.take 8) (bs.drop 8), ht0,
        hw8, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha16 : (a + 8#64) + BitVec.ofNat 64 8 = a + 16#64 := by bv_omega
    rw [ha16]
  have hp1 : ((a + 16#64) ↦ₛ bs.drop 8) =
      ((a + 16#64) ↦₆₄ w16) ∗ ((a + 24#64) ↦ₛ bs.drop 16) := by
    conv_lhs => rw [hbs1]
    rw [ProofLib.pointsToBytes_append (a + 16#64) ((bs.drop 8).take 8) (bs.drop 16), ht1,
        hw16, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha24 : (a + 16#64) + BitVec.ofNat 64 8 = a + 24#64 := by bv_omega
    rw [ha24]
  have hp2 : ((a + 24#64) ↦ₛ bs.drop 16) =
      ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦ₛ bs.drop 24) := by
    conv_lhs => rw [hbs2]
    rw [ProofLib.pointsToBytes_append (a + 24#64) ((bs.drop 16).take 8) (bs.drop 24), ht2,
        hw24, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha32 : (a + 24#64) + BitVec.ofNat 64 8 = a + 32#64 := by bv_omega
    rw [ha32]
  have hp3 : ((a + 32#64) ↦ₛ bs.drop 24) ∗ ((a + 392#64) ↦₆₄ w392) =
      ((a + 32#64) ↦ₛ (bs.drop 24 ++ unpack64 w392)) := by
    rw [ProofLib.pointsToBytes_append (a + 32#64) (bs.drop 24) (unpack64 w392),
        List.length_drop, hbs, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha392 : (a + 32#64) + BitVec.ofNat 64 (384 - 24) = a + 392#64 := by bv_omega
    rw [ha392]
  rw [hp0, hp1, hp2]
  simp only [sepConj_assoc, hp3]

theorem v2hse2_memRegion_1392_400_split_32_368 (fsp : BitVec 64) :
    memRegion (fsp + 1392#64) 400 ⊢
      (∃∗ e0 : BitVec 64, (fsp + 1392#64) ↦₆₄ e0) ∗
      (∃∗ e8 : BitVec 64, (fsp + 1400#64) ↦₆₄ e8) ∗
      (∃∗ e16 : BitVec 64, (fsp + 1408#64) ↦₆₄ e16) ∗
      (∃∗ e24 : BitVec 64, (fsp + 1416#64) ↦₆₄ e24) ∗
      memRegion (fsp + 1424#64) 368 := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v2hse2_1888_32_368_entails_memRegion_400
    (fsp tag w8 w16 w24 : BitVec 64)
    (tail368 : { l : List (BitVec 8) // l.length = 368 }) :
    ((fsp + 1888#64) ↦₆₄ tag) ∗
    ((fsp + 1896#64) ↦₆₄ w8) ∗
    ((fsp + 1904#64) ↦₆₄ w16) ∗
    ((fsp + 1912#64) ↦₆₄ w24) ∗
    ((fsp + 1920#64) ↦ₛ tail368.val) ⊢
      memRegion (fsp + 1888#64) 400 := by
  have hm368 : ((fsp + 1920#64) ↦ₛ tail368.val) ⊢ memRegion (fsp + 1920#64) 368 := by
    have h := ProofLib.pointsToBytes_entails_memRegion (fsp + 1920#64) tail368.val
    rw [tail368.property] at h
    exact h
  exact collapse_top <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    hm368

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_x25_add_105_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (105#64).signExtend 64 = fsp + 1897#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_x25_add_105 (fsp : BitVec 64) :
    fsp + 1792#64 + 105#64 = fsp + 1897#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_fsp_1897_add_8 (fsp : BitVec 64) :
    fsp + 1897#64 + 8#64 = fsp + 1905#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_x24_add_32 (fsp : BitVec 64) :
    fsp + 1888#64 + 32#64 = fsp + 1920#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_fsp_1392_add_32 (fsp : BitVec 64) :
    fsp + 1392#64 + 32#64 = fsp + 1424#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_fsp_240_add_8 (fsp : BitVec 64) :
    fsp + 240#64 + 8#64 = fsp + 248#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_fsp_add_255_sext (fsp : BitVec 64) :
    fsp + (255#64).signExtend 64 = fsp + 255#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_fsp_1264_add_137_sext (fsp : BitVec 64) :
    (fsp + 1264#64) + (137#64).signExtend 64 = fsp + 1401#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_fsp_1264_add_137 (fsp : BitVec 64) :
    fsp + 1264#64 + 137#64 = fsp + 1401#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_fsp_1401_add_8 (fsp : BitVec 64) :
    fsp + 1401#64 + 8#64 = fsp + 1409#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_zext64_setWidth32_setWidth8 (b : BitVec 8) :
    ((b.zeroExtend 64).setWidth 32).setWidth 8 = b := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_zext32_setWidth8 (b : BitVec 8) :
    (b.zeroExtend 32).setWidth 8 = b := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse2_zext64_setWidth8 (b : BitVec 8) :
    (b.zeroExtend 64).setWidth 8 = b := by bv_kernel

theorem v2hse2_memRegion_240_24_split (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 24 ⊢
      (∃∗ d0 : BitVec 64, (fsp + 240#64) ↦₆₄ d0) ∗
      (∃∗ d8 : BitVec 64, (fsp + 248#64) ↦₆₄ d8) ∗
      (∃∗ d16 : BitVec 64, (fsp + 256#64) ↦₆₄ d16) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    mem64_entails _

theorem v2hse2_lsr8_lsl8 (v : BitVec 64) :
    (v >>> 8) <<< 8 = v &&& 0xffffffffffffff00#64 := by bv_kernel

theorem v2hse2_unshift_lsr56 (w0 v : BitVec 64) :
    (unshiftWord w0 (loByte v)) >>> 56 = v &&& 0xff#64 := by
  unfold unshiftWord loByte; bv_kernel

theorem v2hse2_overlapWord7_unshift_lsr8 (w0 w8 : BitVec 64) :
    overlapWord7 (unshiftWord w0 (loByte w8)) (w8 >>> 8) = w8 := by
  unfold overlapWord7
  rw [v2hse2_unshift_lsr56 w0 w8, v2hse2_lsr8_lsl8 w8]
  bv_kernel

theorem v2hse2_pointsTo64_split_7_1 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦ₛ EncoderFromPb.loBytes7 w) ∗ ((a + 7#64) ↦ₛ [(w >>> 56).setWidth 8]) := by
  rw [pointsTo64_eq_pointsToBytes]
  change (a ↦ₛ unpack64 w) =
    (a ↦ₛ EncoderFromPb.loBytes7 w) ∗
    ((a + BitVec.ofNat 64 (EncoderFromPb.loBytes7 w).length) ↦ₛ [(w >>> 56).setWidth 8])
  rw [← ProofLib.pointsToBytes_append a (EncoderFromPb.loBytes7 w) [(w >>> 56).setWidth 8]]
  rfl

theorem v2hse2_pointsTo64_split_7_1_entails_8 (a w : BitVec 64) (b7 : BitVec 8) :
    (a ↦ₛ EncoderFromPb.loBytes7 w) ∗ ((a + 7#64) ↦ₛ [b7]) ⊢ memRegion a 8 := by
  rw [ProofLib.memRegion_split a 7 1 (by decide)]
  refine sepConj_mono ?_ ?_
  · have hlen : (EncoderFromPb.loBytes7 w).length = 7 := rfl
    exact hlen ▸ ProofLib.pointsToBytes_entails_memRegion a (EncoderFromPb.loBytes7 w)
  · have hlen1 : ([b7] : List (BitVec 8)).length = 1 := rfl
    exact hlen1 ▸ ProofLib.pointsToBytes_entails_memRegion (a + 7#64) [b7]

theorem v2hse2_fsp_248_realign_rest (fsp u1 d16 : BitVec 64) (Rest : SepProp) :
    ((fsp + 248#64) ↦₆₄ u1) ∗ ((fsp + 256#64) ↦₆₄ d16) ∗ Rest =
      ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 u1) ∗
      ((fsp + 255#64) ↦₆₄ overlapWord7 u1 d16) ∗
      ((fsp + 263#64) ↦ₛ [(d16 >>> 56).setWidth 8]) ∗ Rest := by
  have hsplit := v2hse2_pointsTo64_split_7_1 (fsp + 256#64) d16
  have ha263 : (fsp + 256#64) + 7#64 = fsp + 263#64 := by bv_omega
  rw [ha263] at hsplit
  have hover := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 248#64) u1 d16
  have ha256 : (fsp + 248#64) + 8#64 = fsp + 256#64 := by bv_omega
  have ha255 : (fsp + 248#64) + 7#64 = fsp + 255#64 := by bv_omega
  rw [ha256, ha255] at hover
  rw [hsplit]
  simp only [sepConj_assoc]
  rw [← sepConj_assoc ((fsp + 248#64) ↦₆₄ u1), hover]
  simp only [sepConj_assoc]

theorem v2hse2_fsp_248_unrealign_w24_rest (fsp w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
      ((fsp + 255#64) ↦₆₄ w24) ∗ Rest =
      ((fsp + 248#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((fsp + 256#64) ↦ₛ EncoderFromPb.loBytes7 (w24 >>> 8)) ∗ Rest := by
  have hover := (pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 248#64)
    (unshiftWord w16 (loByte w24)) (w24 >>> 8)).symm
  have ha256 : (fsp + 248#64) + 8#64 = fsp + 256#64 := by bv_omega
  have ha255 : (fsp + 248#64) + 7#64 = fsp + 255#64 := by bv_omega
  rw [ha256, ha255, v2hse2_overlapWord7_unshift_lsr8 w16 w24] at hover
  rw [← sepConj_assoc ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))), hover]
  simp only [sepConj_assoc]

theorem v2hse2_fsp_248_realign_w24_rest (fsp w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 248#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((fsp + 256#64) ↦ₛ EncoderFromPb.loBytes7 (w24 >>> 8)) ∗ Rest =
      ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
      ((fsp + 255#64) ↦₆₄ w24) ∗ Rest :=
  (v2hse2_fsp_248_unrealign_w24_rest fsp w16 w24 Rest).symm

theorem v2hse2_240_spill_entails_memRegion_24
    (fsp u0 u1 w : BitVec 64) (b7 : BitVec 8) :
    ((fsp + 240#64) ↦₆₄ u0) ∗
    ((fsp + 248#64) ↦₆₄ u1) ∗
    (((fsp + 256#64) ↦ₛ EncoderFromPb.loBytes7 w) ∗ ((fsp + 263#64) ↦₈ b7)) ⊢
      memRegion (fsp + 240#64) 24 := by
  rw [← ProofLib.pointsToBytes_singleton (fsp + 263#64) b7]
  have hm8 := v2hse2_pointsTo64_split_7_1_entails_8 (fsp + 256#64) w b7
  have ha263 : (fsp + 256#64) + 7#64 = fsp + 263#64 := by bv_omega
  rw [ha263] at hm8
  exact collapse_top <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    hm8

theorem v2hse2_fsp1896_to_unaligned16_rest (fsp w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗ ((fsp + 1912#64) ↦₆₄ w24) ∗ Rest =
      ((fsp + 1896#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 1897#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
      ((fsp + 1905#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
      ((fsp + 1913#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ Rest := by
  have h := v2hse_threeWords_to_unaligned16 (fsp + 1896#64) w8 w16 w24
  simp only [v2hse2_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hse2_fsp1896_to_threeWords_rest (fsp w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1896#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 1897#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
      ((fsp + 1905#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
      ((fsp + 1913#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ Rest =
      ((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗ ((fsp + 1912#64) ↦₆₄ w24) ∗ Rest :=
  (v2hse2_fsp1896_to_unaligned16_rest fsp w8 w16 w24 Rest).symm

theorem v2hse2_fsp1896_split_rest (fsp w8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1896#64) ↦₆₄ w8) ∗ Rest =
      ((fsp + 1896#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 1897#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 1896#64) w8
  simp only [v2hse2_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hse2_fsp1896_unsplit_rest (fsp w8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1896#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 1897#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗ Rest =
      ((fsp + 1896#64) ↦₆₄ w8) ∗ Rest :=
  (v2hse2_fsp1896_split_rest fsp w8 Rest).symm

theorem v2hse2_fsp1400_to_unaligned16_rest (fsp e8 e16 e24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1400#64) ↦₆₄ e8) ∗ ((fsp + 1408#64) ↦₆₄ e16) ∗ ((fsp + 1416#64) ↦₆₄ e24) ∗ Rest =
      ((fsp + 1400#64) ↦₈ EncoderFromPb.loByte e8) ∗
      ((fsp + 1401#64) ↦₆₄ EncoderFromPb.unshiftWord e8 (EncoderFromPb.loByte e16)) ∗
      ((fsp + 1409#64) ↦₆₄ EncoderFromPb.unshiftWord e16 (EncoderFromPb.loByte e24)) ∗
      ((fsp + 1417#64) ↦ₛ EncoderFromPb.hiBytes7 e24) ∗ Rest := by
  have h := v2hse_threeWords_to_unaligned16 (fsp + 1400#64) e8 e16 e24
  simp only [v2hse2_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hse2_fsp1400_to_threeWords_mixed_rest (fsp w8 w16 w24 e24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1400#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 1401#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
      ((fsp + 1409#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
      ((fsp + 1417#64) ↦ₛ EncoderFromPb.hiBytes7 e24) ∗ Rest =
      ((fsp + 1400#64) ↦₆₄ w8) ∗ ((fsp + 1408#64) ↦₆₄ w16) ∗
      ((fsp + 1416#64) ↦₆₄ v2hse_withLoByte (EncoderFromPb.loByte w24) e24) ∗ Rest := by
  have h := v2hse_unaligned16_to_threeWords_mixed (fsp + 1400#64) w8 w16 w24 e24
  simp only [v2hse2_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

set_option maxHeartbeats 1200000 in
/-- When `<PolyEncoder>::from_pb` returns `.ok enc` at `fsp + 1888`, steps `+9100 -> +9248 -> +9328`,
moving `polyEncoderAt` words from `fsp + 1888..2288` to `fsp + 1392..1792`, storing `v2hse2_polyEncoderTag enc`
to `[sp + 56]`, and setting `pstate = addsPState64 d0 1#64`. -/
theorem v2hse2_enc_ok_move_9100_to_9328
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out d0 ca3 pbA slot56_old w8 w16 w24 : BitVec 64)
    (tail368 : { l : List (BitVec 8) // l.length = 368 })
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx24_1 : s1.readReg64 .x24 = fsp + 1888#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9328#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 1888#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((fsp + 1896#64) ↦₆₄ w8) ∗
        ((fsp + 1904#64) ↦₆₄ w16) ∗
        ((fsp + 1912#64) ↦₆₄ w24) ∗
        ((fsp + 1920#64) ↦ₛ tail368.val) ∗
        memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 240#64) 24 ∗
        ((fsp + 56#64) ↦₆₄ slot56_old) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          ((fsp + 1400#64) ↦₆₄ w8) ∗
          ((fsp + 1408#64) ↦₆₄ w16) ∗
          ((fsp + 1416#64) ↦₆₄ w24) ∗
          ((fsp + 1424#64) ↦ₛ tail368.val) ∗
          memRegion (fsp + 240#64) 24 ∗
          ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = (loByte w8).zeroExtend 64 ∧
        sm.readReg64 .x21 = s1.readReg64 .x21 ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = fsp + 1392#64 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = s1.readReg64 .x28 ∧
        sm.pstate = addsPState64 d0 1#64 ∧
        TraceCalleeSaved sm s0) := by
  subst hsp1
  have hmemcpy := hA.session_memcpy_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy"))
  simp only [sessionMemcpySpec, allocHookStack, stackAt] at hmemcpy
  wp_conv_pre =>
    rw [v2hse2_stackAt_encoderFromPbStack_eq_allocHook s1.sp]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (v2hse2_memRegion_1392_400_split_32_368 s1.sp)
          (sepConj_mono_left (v2hse2_memRegion_240_24_split s1.sp))))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d16
  apply ProofLib.SepWP.exists_left; intro d8
  apply ProofLib.SepWP.exists_left; intro d0_spill
  apply ProofLib.SepWP.exists_left; intro e24
  apply ProofLib.SepWP.exists_left; intro e16
  apply ProofLib.SepWP.exists_left; intro e8
  apply ProofLib.SepWP.exists_left; intro e0
  states_from_pb_fetches_range b (Rust.withPanics ext) 9100 12
  states_from_pb_fetches_range b (Rust.withPanics ext) 9248 80
  dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hmemcpy hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre only [v2hse2_fsp1896_to_unaligned16_rest, sepConj_assoc]
  iterate 4 wp_step
  wp_simp_pre only [v2hse2_fsp1896_to_threeWords_rest, sepConj_assoc]
  iterate 2 wp_step
  wp_simp_pre only [v2hse2_fsp1896_split_rest, sepConj_assoc]
  wp_step
  wp_simp_pre only [v2hse2_fsp1896_unsplit_rest, sepConj_assoc]
  iterate 4 wp_step
  wp_simp_pre only [v2hse2_fsp_248_realign_rest, sepConj_assoc]
  iterate 3 wp_step
  have hlen368 : (368 : Nat) = tail368.val.length := tail368.property.symm
  wp_simp_pre [hlen368, sepConj_assoc]
  wp_call hmemcpy (s1.sp + 1424#64, s1.sp + 1920#64, tail368.val)
  wp_step
  wp_simp_pre only [v2hse2_fsp_248_unrealign_w24_rest, sepConj_assoc]
  wp_step
  wp_simp_pre only [v2hse2_fsp1400_to_unaligned16_rest, sepConj_assoc]
  iterate 4 wp_step
  wp_simp_pre only [v2hse2_fsp_248_realign_w24_rest, sepConj_assoc]
  wp_step
  wp_step
  wp_simp_pre only [v2hse2_fsp1400_to_threeWords_mixed_rest, sepConj_assoc]
  wp_step
  wp_simp_pre only [v2hse2_fsp_248_unrealign_w24_rest, sepConj_assoc]
  refine EncoderFromPb.align_pre ?_ ?_
  · have h1888_400 := v2hse2_1888_32_368_entails_memRegion_400 s1.sp (v2hse2_polyEncoderTag enc) w8 w16 w24 tail368
    have h240_24 := v2hse2_240_spill_entails_memRegion_24 s1.sp
      (unshiftWord w8 (loByte w16)) (unshiftWord w16 (loByte w24)) (w24 >>> 8) ((d16 >>> 56).setWidth 8)
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s1.sp - 4096#64) 4096 ∗ memRegion (s1.sp - 5152#64) 1056) ∗
      (((s1.sp + 1888#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
       ((s1.sp + 1896#64) ↦₆₄ w8) ∗ ((s1.sp + 1904#64) ↦₆₄ w16) ∗
       ((s1.sp + 1912#64) ↦₆₄ w24) ∗ ((s1.sp + 1920#64) ↦ₛ tail368.val)) ∗
      ((s1.sp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
      ((s1.sp + 1400#64) ↦₆₄ w8) ∗ ((s1.sp + 1408#64) ↦₆₄ w16) ∗
      ((s1.sp + 1416#64) ↦₆₄ w24) ∗ ((s1.sp + 1424#64) ↦ₛ tail368.val) ∗
      (((s1.sp + 240#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
       ((s1.sp + 248#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
       (((s1.sp + 256#64) ↦ₛ EncoderFromPb.loBytes7 (w24 >>> 8)) ∗
        ((s1.sp + 263#64) ↦₈ (d16 >>> 56).setWidth 8))) ∗
      ((s1.sp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
      Frame by ac_rfl)) ?_
    rw [← v2hse2_stackAt_encoderFromPbStack_eq_allocHook s1.sp]
    exact sepConj_mono (Entails.refl _) (sepConj_mono h1888_400
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono h240_24 (Entails.refl _))))))))
  · wp_done

end CryptoVerification.SpqrV1.States.FromPb
