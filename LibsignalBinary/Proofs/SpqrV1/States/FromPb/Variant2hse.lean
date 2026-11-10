/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsc
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part E

`Unchunked::EkSent` stack assembly (`+8908..+9032`), `sendingEk = none` branch (`+9032 -> +9212`),
and 56-byte `ProtoPolynomialEncoder` staging (`+9036..+9096`).
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
  fnOff_drop_poly16
  fnOff_drop_proto_poly_encoder
  fnOff_drop_poly_encoder_local2
  fnOff_drop_ek_sent
  fnOff_poly_encoder_from_pb
  fnOff_poly_decoder_from_pb
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

theorem v2hse_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## `unchunkedEkSentAt` Word/Heap Decomposition & `+8908 .. +9032` Stepping -/

def v2hse_unchunkedEkSentWordsAt (a ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64) : SepProp :=
  (a ↦₆₄ ca1) ∗ ((a + 8#64) ↦₆₄ pa1) ∗ ((a + 16#64) ↦₆₄ la1) ∗
  ((a + 24#64) ↦₆₄ ca2) ∗ ((a + 32#64) ↦₆₄ pa2) ∗ ((a + 40#64) ↦₆₄ la2) ∗
  ((a + 48#64) ↦₆₄ ca3) ∗ ((a + 56#64) ↦₆₄ pa3) ∗ ((a + 64#64) ↦₆₄ la3) ∗
  ((a + 72#64) ↦₆₄ epoch)

def v2hse_vecU8Heap (A : RustAlloc) (cap ptr len : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜len = BitVec.ofNat 64 bs.length ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
  (if cap = 0#64 then emp
   else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
     memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem v2hse_vecU8_unpack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
        ⌜cap.toNat < 2 ^ 63⌝ ∗
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) ∗
        v2hse_vecU8Heap A cap ptr len bs := by
  unfold vecU8 vecU8At vecHeader v2hse_vecU8Heap
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap ?_
  refine Entails.sepExists_right ptr ?_
  refine Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
     (if cap = 0#64 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hle, hcap, hptr⟩
  refine Entails.pure_right hcap ?_
  have hpure : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length ∧
      bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 := ⟨rfl, hle, hcap, hptr⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v2hse_vecU8_pack (A : RustAlloc) (a cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) ∗
      v2hse_vecU8Heap A cap ptr len bs ⊢
    vecU8 A a bs := by
  unfold vecU8 vecU8At vecHeader v2hse_vecU8Heap
  refine Entails.sepExists_right cap ?_
  refine Entails.sepExists_right ptr ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜len = BitVec.ofNat 64 bs.length ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len) ∗
     (if cap = 0#64 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, hle, hcap, hptr⟩
  have hpure : bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 := ⟨hle, hcap, hptr⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v2hse_vecU8Heap_entails_dealloc (A : RustAlloc) (cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    v2hse_vecU8Heap A cap ptr len bs ⊢ vecCapPtrDealloc A cap ptr := by
  unfold v2hse_vecU8Heap vecCapPtrDealloc
  apply Entails.pure_left; rintro ⟨_, hle, hcap, _⟩
  by_cases hc : cap = 0#64
  · subst hc; simp only [beq_self_eq_true, ↓reduceIte]; exact Entails.refl _
  · have hcf : (cap == 0#64) = false := beq_false_of_ne hc
    simp only [hc, hcf, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepConj_mono_right
    have h1 := ProofLib.pointsToBytes_entails_memRegion ptr bs
    have hadd : bs.length + (cap.toNat - bs.length) = cap.toNat := Nat.add_sub_of_le hle
    have h2 : memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
        memRegion ptr cap.toNat := by
      rw [← ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length) hadd.symm rfl (by omega)]
    rw [← h2]
    exact sepConj_mono_left h1

theorem v2hse_unchunkedEkSentAt_pack (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (uc : Unchunked.SendEk.EkSent (spqrAuthApi F))
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 : BitVec 64) :
    v2hse_unchunkedEkSentWordsAt a ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 uc.epoch ∗
      v2hse_vecU8Heap A ca1 pa1 la1 uc.auth.rootKey ∗
      v2hse_vecU8Heap A ca2 pa2 la2 uc.auth.macKey ∗
      v2hse_vecU8Heap A ca3 pa3 la3 uc.dk ⊢
    unchunkedEkSentAt A a uc := by
  unfold unchunkedEkSentAt authenticatorAt v2hse_unchunkedEkSentWordsAt
  have h1 := v2hse_vecU8_pack A a ca1 pa1 la1 uc.auth.rootKey
  have h2 := v2hse_vecU8_pack A (a + 24#64) ca2 pa2 la2 uc.auth.macKey
  have h3 := v2hse_vecU8_pack A (a + 48#64) ca3 pa3 la3 uc.dk
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h2 h3 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    (((a ↦₆₄ ca1) ∗ ((a + 8#64) ↦₆₄ pa1) ∗ ((a + 16#64) ↦₆₄ la1)) ∗
     v2hse_vecU8Heap A ca1 pa1 la1 uc.auth.rootKey) ∗
    ((((a + 24#64) ↦₆₄ ca2) ∗ ((a + 32#64) ↦₆₄ pa2) ∗ ((a + 40#64) ↦₆₄ la2)) ∗
     v2hse_vecU8Heap A ca2 pa2 la2 uc.auth.macKey) ∗
    ((((a + 48#64) ↦₆₄ ca3) ∗ ((a + 56#64) ↦₆₄ pa3) ∗ ((a + 64#64) ↦₆₄ la3)) ∗
     v2hse_vecU8Heap A ca3 pa3 la3 uc.dk) ∗
    ((a + 72#64) ↦₆₄ uc.epoch) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem v2hse_unchunkedEkSentWordsAt_entails_80
    (a ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64) :
    v2hse_unchunkedEkSentWordsAt a ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ⊢
      memRegion a 80 := by
  unfold v2hse_unchunkedEkSentWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v2hse_memRegion_1264_80_split (fsp : BitVec 64) :
    memRegion (fsp + 1264#64) 80 ⊢
      (∃∗ u0 : BitVec 64, (fsp + 1264#64) ↦₆₄ u0) ∗
      (∃∗ u8 : BitVec 64, (fsp + 1272#64) ↦₆₄ u8) ∗
      (∃∗ u16 : BitVec 64, (fsp + 1280#64) ↦₆₄ u16) ∗
      (∃∗ u24 : BitVec 64, (fsp + 1288#64) ↦₆₄ u24) ∗
      (∃∗ u32 : BitVec 64, (fsp + 1296#64) ↦₆₄ u32) ∗
      (∃∗ u40 : BitVec 64, (fsp + 1304#64) ↦₆₄ u40) ∗
      (∃∗ u48 : BitVec 64, (fsp + 1312#64) ↦₆₄ u48) ∗
      (∃∗ u56 : BitVec 64, (fsp + 1320#64) ↦₆₄ u56) ∗
      (∃∗ u64 : BitVec 64, (fsp + 1328#64) ↦₆₄ u64) ∗
      (∃∗ u72 : BitVec 64, (fsp + 1336#64) ↦₆₄ u72) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    mem64_entails _

theorem v2hse_pointsTo64_split_1_4_2_1 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗
      ((a + 1#64) ↦₃₂ w.extractLsb' 8 32) ∗
      ((a + 5#64) ↦₁₆ w.extractLsb' 40 16) ∗
      ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hb1 : (w.extractLsb' 8 32).extractLsb' 0 8 = w.extractLsb' 8 8 := by bv_kernel
  have hb2 : (w.extractLsb' 8 32).extractLsb' 8 8 = w.extractLsb' 16 8 := by bv_kernel
  have hb3 : (w.extractLsb' 8 32).extractLsb' 16 8 = w.extractLsb' 24 8 := by bv_kernel
  have hb4 : (w.extractLsb' 8 32).extractLsb' 24 8 = w.extractLsb' 32 8 := by bv_kernel
  have hb5 : (w.extractLsb' 40 16).extractLsb' 0 8 = w.extractLsb' 40 8 := by bv_kernel
  have hb6 : (w.extractLsb' 40 16).extractLsb' 8 8 = w.extractLsb' 48 8 := by bv_kernel
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      ProofLib.pointsTo32_eq_pointsToBytes (a + 1#64) (w.extractLsb' 8 32),
      ProofLib.pointsTo16_eq_pointsToBytes (a + 5#64) (w.extractLsb' 40 16)]
  simp only [unpack64, unpack32, unpack16,
    ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
    hb1, hb2, hb3, hb4, hb5, hb6,
    sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]

theorem v2hse_1272_split_rest (fsp u8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1272#64) ↦₆₄ u8) ∗ Rest =
      ((fsp + 1272#64) ↦₈ u8.extractLsb' 0 8) ∗
      ((fsp + 1273#64) ↦₃₂ u8.extractLsb' 8 32) ∗
      ((fsp + 1277#64) ↦₁₆ u8.extractLsb' 40 16) ∗
      ((fsp + 1279#64) ↦₈ u8.extractLsb' 56 8) ∗ Rest := by
  have h := v2hse_pointsTo64_split_1_4_2_1 (fsp + 1272#64) u8
  have ha1 : (fsp + 1272#64) + 1#64 = fsp + 1273#64 := by bv_omega
  have ha5 : (fsp + 1272#64) + 5#64 = fsp + 1277#64 := by bv_omega
  have ha7 : (fsp + 1272#64) + 7#64 = fsp + 1279#64 := by bv_omega
  rw [ha1, ha5, ha7] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v2hse_1272_unsplit_rest (fsp u8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1272#64) ↦₈ u8.extractLsb' 0 8) ∗
      ((fsp + 1273#64) ↦₃₂ u8.extractLsb' 8 32) ∗
      ((fsp + 1277#64) ↦₁₆ u8.extractLsb' 40 16) ∗
      ((fsp + 1279#64) ↦₈ u8.extractLsb' 56 8) ∗ Rest =
      ((fsp + 1272#64) ↦₆₄ u8) ∗ Rest :=
  (v2hse_1272_split_rest fsp u8 Rest).symm

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse_pa1_d1273 (pa1 : BitVec 64) :
    ((pa1.extractLsb' 8 56).zeroExtend 64).setWidth 32 = pa1.extractLsb' 8 32 := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse_pa1_b1279 (pa1 : BitVec 64) :
    (((pa1.extractLsb' 8 56).setWidth 64).extractLsb' 48 16).setWidth 8 =
      pa1.extractLsb' 56 8 := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse_pa1_h1277 (pa1 : BitVec 64) :
    (((pa1.extractLsb' 8 56).setWidth 64).extractLsb' 32 32).setWidth 16 =
      pa1.extractLsb' 40 16 := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse_pa1_b1272 (pa1 : BitVec 64) :
    (pa1.setWidth 32).setWidth 8 = pa1.extractLsb' 0 8 := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse_fsp_1264_add_9 (fsp : BitVec 64) :
    (fsp + 1264#64) + 9#64 = fsp + 1273#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse_fsp_1264_add_13 (fsp : BitVec 64) :
    (fsp + 1264#64) + 13#64 = fsp + 1277#64 := by bv_omega

/-- Execution segment `+8908 -> +8932`: shifts `x26 = (pa1.extractLsb' 8 56).zeroExtend 64`,
and deallocates `(cap_ek, ptr_ek)` (`x24 = cap_ek`, `x25 = ptr_ek`). -/
theorem v2hse_dealloc_8908_to_8932
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out d0 pa1 cap_ek ptr_ek pbA epoch : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8908#64)
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
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8932#64) s1
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
  have hdealloc := v2hsc_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  states_from_pb_fetches_range b (Rust.withPanics ext) 8908 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
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
theorem v2hse_step_8932_to_8960
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out d0 ca1 pa1 pbA epoch d1273_old : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hca1 : ca1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8932#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx26_1 : s1.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8960#64) s1
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
  states_from_pb_fetches_range b (Rust.withPanics ext) 8932 28
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- Execution segment `+8960 -> +9032`: finishes assembling `v2hse_unchunkedEkSentWordsAt (fsp + 1264)`
from `[sp + 96] = la3`, `[sp + 152] = ca3`, `[sp + 176] = pa3`, `[sp + 184] = pa2`,
`[sp + 232] = ca2`, loads `x8 = cap_enc` from `[sp + 976]`, and sets `pstate = addsPState64 cap_enc 1#64`. -/
theorem v2hse_step_8960_to_9032
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State)
    (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA
     u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8960#64)
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
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9032#64) s1
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
  states_from_pb_fetches_range b (Rust.withPanics ext) 8960 72
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_simp_pre only [v2hse_1272_unsplit_rest, sepConj_assoc]
  refine EncoderFromPb.align_pre ?_ ?_
  · unfold v2hse_unchunkedEkSentWordsAt
    simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    exact Entails.of_eq (by ac_rfl)
  · wp_done

/-- Combined `+8932 -> +9032`: starting with `memRegion (fsp + 1264) 80`, steps through `+8960`
to `+9032` and produces `v2hse_unchunkedEkSentWordsAt (fsp + 1264)`. -/
theorem v2hse_step_8932_to_9032
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State)
    (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hca1 : ca1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8932#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx26_1 : s1.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9032#64) s1
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
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8960#64)
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
      (v2hse_step_8932_to_8960 s0 s1 fsp out d0 ca1 pa1 pbA epoch (u8 >>> 8) _
        hfsp_align hca1 hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 htr1)
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx9_2, hx10_2, hx19_2, hx22_2, hx23_2, hx25_2, hx27_2, hx28_2, htr2⟩
    have h8960 := v2hse_step_8960_to_9032 s0 s2 fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA
      u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 (((fsp + 200#64) ↦₆₄ ca1) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx8_2 hx9_2 hx10_2 hx19_2 hx22_2 hx23_2 hx25_2 hx27_2 hx28_2 htr2
    exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono h8960 fun sm Pm _ _ ⟨hPm, hq⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩)

/-- When `cap_enc = noneCap` at `+9032`, takes `b.eq +9152` and runs `v2hsc_cleanup_9152_to_9212`
to deallocate `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)` and reach `+9212`. -/
theorem v2hse_none_enc_9032_to_9212
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9032#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9212#64) s1
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
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9152#64)
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
  · states_from_pb_fetches_range b (Rust.withPanics ext) 9032 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hpstate1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx25_2, hx26_2, htr2⟩
    unfold v2hse_unchunkedEkSentWordsAt
    simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    have h9152 := v2hsc_cleanup_9152_to_9212 hA s0 s2 fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3
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

/-! ## Unaligned 3-Word (`24`B) Copy Helpers & (`+9032 .. +9108`) -/

def v2hse_withLoByte (b : BitVec 8) (w : BitVec 64) : BitVec 64 :=
  (w &&& 0xffffffffffffff00#64) ||| b.zeroExtend 64

theorem v2hse_loByte_withLoByte (b : BitVec 8) (w : BitVec 64) :
    EncoderFromPb.loByte (v2hse_withLoByte b w) = b := by
  dsimp only [EncoderFromPb.loByte, v2hse_withLoByte]
  bv_kernel

theorem v2hse_hiBytes7_withLoByte (b : BitVec 8) (w : BitVec 64) :
    EncoderFromPb.hiBytes7 (v2hse_withLoByte b w) = EncoderFromPb.hiBytes7 w := by
  simp only [EncoderFromPb.hiBytes7, unpack64, v2hse_withLoByte, List.drop, List.cons.injEq]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem v2hse_threeWords_to_unaligned16 (a u0 u8 u16 : BitVec 64) :
    (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u8) ∗ ((a + 16#64) ↦₆₄ u16) =
      (a ↦₈ EncoderFromPb.loByte u0) ∗
      ((a + 1#64) ↦₆₄ EncoderFromPb.unshiftWord u0 (EncoderFromPb.loByte u8)) ∗
      ((a + 9#64) ↦₆₄ EncoderFromPb.unshiftWord u8 (EncoderFromPb.loByte u16)) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 u16) := by
  have h1 := EncoderFromPb.pair64_to_byte_word_tail7 (a + 8#64) u8 u16
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha9 : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  have ha17 : (a + 8#64) + 9#64 = a + 17#64 := by bv_omega
  rw [ha16, ha9, ha17] at h1
  have h0 : ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₈ EncoderFromPb.loByte u8)) =
      ((a ↦₈ EncoderFromPb.loByte u0) ∗ ((a + 1#64) ↦₆₄ EncoderFromPb.unshiftWord u0 (EncoderFromPb.loByte u8))) := by
    rw [ProofLib.pointsTo64_eq_pointsToBytes a u0,
        ProofLib.pointsTo64_eq_pointsToBytes (a + 1#64),
        ← ProofLib.pointsToBytes_cons,
        EncoderFromPb.loByte_cons_unpack64_unshiftWord u0 (EncoderFromPb.loByte u8),
        ProofLib.pointsToBytes_append a (unpack64 u0) [EncoderFromPb.loByte u8],
        unpack64_length]
    simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]
  rw [h1, ← sepConj_assoc, ← sepConj_assoc, h0, sepConj_assoc, sepConj_assoc]

theorem v2hse_unaligned16_to_threeWords (a u0 u8 u16 : BitVec 64) :
    (a ↦₈ EncoderFromPb.loByte u0) ∗
      ((a + 1#64) ↦₆₄ EncoderFromPb.unshiftWord u0 (EncoderFromPb.loByte u8)) ∗
      ((a + 9#64) ↦₆₄ EncoderFromPb.unshiftWord u8 (EncoderFromPb.loByte u16)) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 u16) =
      (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u8) ∗ ((a + 16#64) ↦₆₄ u16) :=
  (v2hse_threeWords_to_unaligned16 a u0 u8 u16).symm

theorem v2hse_unaligned16_to_threeWords_mixed (a u0 u8 u16 d16 : BitVec 64) :
    (a ↦₈ EncoderFromPb.loByte u0) ∗
      ((a + 1#64) ↦₆₄ EncoderFromPb.unshiftWord u0 (EncoderFromPb.loByte u8)) ∗
      ((a + 9#64) ↦₆₄ EncoderFromPb.unshiftWord u8 (EncoderFromPb.loByte u16)) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 d16) =
      (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u8) ∗
      ((a + 16#64) ↦₆₄ v2hse_withLoByte (EncoderFromPb.loByte u16) d16) := by
  have h := v2hse_unaligned16_to_threeWords a u0 u8 (v2hse_withLoByte (EncoderFromPb.loByte u16) d16)
  rwa [v2hse_loByte_withLoByte, v2hse_hiBytes7_withLoByte] at h

theorem v2hse_pbA96_to_unaligned16_rest (pbA w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗ Rest =
      ((pbA + 96#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((pbA + 97#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
      ((pbA + 105#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
      ((pbA + 113#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ Rest := by
  have h := v2hse_threeWords_to_unaligned16 (pbA + 96#64) w8 w16 w24
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hse_pbA96_to_threeWords_rest (pbA w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((pbA + 96#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((pbA + 97#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
      ((pbA + 105#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
      ((pbA + 113#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ Rest =
      ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗ Rest :=
  (v2hse_pbA96_to_unaligned16_rest pbA w8 w16 w24 Rest).symm

theorem v2hse_fsp1800_to_unaligned16_rest (fsp e8 e16 e24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1800#64) ↦₆₄ e8) ∗ ((fsp + 1808#64) ↦₆₄ e16) ∗ ((fsp + 1816#64) ↦₆₄ e24) ∗ Rest =
      ((fsp + 1800#64) ↦₈ EncoderFromPb.loByte e8) ∗
      ((fsp + 1801#64) ↦₆₄ EncoderFromPb.unshiftWord e8 (EncoderFromPb.loByte e16)) ∗
      ((fsp + 1809#64) ↦₆₄ EncoderFromPb.unshiftWord e16 (EncoderFromPb.loByte e24)) ∗
      ((fsp + 1817#64) ↦ₛ EncoderFromPb.hiBytes7 e24) ∗ Rest := by
  have h := v2hse_threeWords_to_unaligned16 (fsp + 1800#64) e8 e16 e24
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hse_fsp1800_to_threeWords_mixed_rest (fsp w8 w16 w24 e24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1800#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 1801#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
      ((fsp + 1809#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
      ((fsp + 1817#64) ↦ₛ EncoderFromPb.hiBytes7 e24) ∗ Rest =
      ((fsp + 1800#64) ↦₆₄ w8) ∗ ((fsp + 1808#64) ↦₆₄ w16) ∗
      ((fsp + 1816#64) ↦₆₄ v2hse_withLoByte (EncoderFromPb.loByte w24) e24) ∗ Rest := by
  have h := v2hse_unaligned16_to_threeWords_mixed (fsp + 1800#64) w8 w16 w24 e24
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hse_fsp984_split_rest (fsp w8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 984#64) ↦₆₄ w8) ∗ Rest =
      ((fsp + 984#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 985#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 984#64) w8
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hse_fsp984_unsplit_rest (fsp w8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 984#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 985#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗ Rest =
      ((fsp + 984#64) ↦₆₄ w8) ∗ Rest :=
  (v2hse_fsp984_split_rest fsp w8 Rest).symm

structure v2hse_ProtoPolyEncoderPure (pb : ProtoPolynomialEncoder) (w16 w40 w48 : BitVec 64) : Prop where
  hw16 : w16 = BitVec.ofNat 64 pb.pts.length
  hw40 : w40 = BitVec.ofNat 64 pb.polys.length
  hw48 : w48.setWidth 32 = pb.idx

def v2hse_protoPolyEncoderWordsAt (a w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
  ((a + 48#64) ↦₆₄ w48)

def v2hse_protoPolyEncoderHeap (A : RustAlloc) (pb : ProtoPolynomialEncoder)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  ⌜v2hse_ProtoPolyEncoderPure pb w16 w40 w48⌝ ∗
  vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ∗
  vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys

theorem v2hse_pointsTo32_pad4_entails_64 (a : BitVec 64) (idx : BitVec 32) :
    (a ↦₃₂ idx) ∗ memRegion (a + 4#64) 4 ⊢
      ∃∗ w : BitVec 64, ⌜w.setWidth 32 = idx⌝ ∗ (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_four (a + 4#64), sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro hi
  refine Entails.sepExists_right (hi ++ idx) ?_
  have hlo : (hi ++ idx).setWidth 32 = idx := by bv_kernel
  have h64 : (a ↦₆₄ (hi ++ idx)) = (a ↦₃₂ idx) ∗ ((a + 4#64) ↦₃₂ hi) := by
    rw [ProofLib.pointsTo64_eq_pointsToBytes, ProofLib.pointsTo32_eq_pointsToBytes,
        ProofLib.pointsTo32_eq_pointsToBytes]
    simp only [unpack64, unpack32, ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
      sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    have b0 : (hi ++ idx).extractLsb' 0 8 = idx.extractLsb' 0 8 := by bv_kernel
    have b1 : (hi ++ idx).extractLsb' 8 8 = idx.extractLsb' 8 8 := by bv_kernel
    have b2 : (hi ++ idx).extractLsb' 16 8 = idx.extractLsb' 16 8 := by bv_kernel
    have b3 : (hi ++ idx).extractLsb' 24 8 = idx.extractLsb' 24 8 := by bv_kernel
    have b4 : (hi ++ idx).extractLsb' 32 8 = hi.extractLsb' 0 8 := by bv_kernel
    have b5 : (hi ++ idx).extractLsb' 40 8 = hi.extractLsb' 8 8 := by bv_kernel
    have b6 : (hi ++ idx).extractLsb' 48 8 = hi.extractLsb' 16 8 := by bv_kernel
    have b7 : (hi ++ idx).extractLsb' 56 8 = hi.extractLsb' 24 8 := by bv_kernel
    rw [b0, b1, b2, b3, b4, b5, b6, b7]
  rw [h64]
  exact Entails.pure_right hlo (Entails.refl _)

theorem v2hse_pointsTo64_entails_32_pad4 (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦₃₂ w.setWidth 32) ∗ memRegion (a + 4#64) 4 := by
  have hsplit : (a ↦₆₄ w) = (a ↦₃₂ w.setWidth 32) ∗ ((a + 4#64) ↦₃₂ (w.extractLsb' 32 32)) := by
    rw [ProofLib.pointsTo64_eq_pointsToBytes, ProofLib.pointsTo32_eq_pointsToBytes,
        ProofLib.pointsTo32_eq_pointsToBytes]
    simp only [unpack64, unpack32, ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
      sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    have b0 : (w.setWidth 32).extractLsb' 0 8 = w.extractLsb' 0 8 := by bv_kernel
    have b1 : (w.setWidth 32).extractLsb' 8 8 = w.extractLsb' 8 8 := by bv_kernel
    have b2 : (w.setWidth 32).extractLsb' 16 8 = w.extractLsb' 16 8 := by bv_kernel
    have b3 : (w.setWidth 32).extractLsb' 24 8 = w.extractLsb' 24 8 := by bv_kernel
    have b4 : (w.extractLsb' 32 32).extractLsb' 0 8 = w.extractLsb' 32 8 := by bv_kernel
    have b5 : (w.extractLsb' 32 32).extractLsb' 8 8 = w.extractLsb' 40 8 := by bv_kernel
    have b6 : (w.extractLsb' 32 32).extractLsb' 16 8 = w.extractLsb' 48 8 := by bv_kernel
    have b7 : (w.extractLsb' 32 32).extractLsb' 24 8 = w.extractLsb' 56 8 := by bv_kernel
    rw [b0, b1, b2, b3, b4, b5, b6, b7]
  rw [hsplit]
  exact sepConj_mono_right (pointsTo32_entails_memRegion_4 _ _)

theorem v2hse_protoPolyEncoderAt_unpack (A : RustAlloc) (a : BitVec 64) (pb : ProtoPolynomialEncoder) :
    protoPolynomialEncoderAt A a pb ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64,
        ⌜w0.toNat < 2 ^ 63⌝ ∗
        v2hse_protoPolyEncoderWordsAt a w0 w8 w16 w24 w32 w40 w48 ∗
        v2hse_protoPolyEncoderHeap A pb w0 w8 w16 w24 w32 w40 w48 := by
  unfold protoPolynomialEncoderAt vecVecU8At vecOf vecAt vecHeader
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
    v2hse_protoPolyEncoderWordsAt v2hse_protoPolyEncoderHeap
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w8
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w24
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w32
  have htail := v2hse_pointsTo32_pad4_entails_64 (a + 0x30#64) pb.idx
  have ha52 : (a + 0x30#64) + 4#64 = a + 0x34#64 := by bv_omega
  rw [ha52] at htail
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right htail)) ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w48
  have hw0 : vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ⊢
      ⌜w0.toNat < 2 ^ 63⌝ ∗ vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts := by
    unfold vecBuf Poly.vecHeaderBytes
    apply Entails.pure_left; rintro ⟨hle, hcap, hptr⟩
    have hlt : w0.toNat < 2 ^ 63 := by omega
    exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hcap, hptr⟩ (Entails.refl _))
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right hw0)) ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right w8
    (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length) (Entails.sepExists_right w24
      (Entails.sepExists_right w32 (Entails.sepExists_right (BitVec.ofNat 64 pb.polys.length)
        (Entails.sepExists_right w48 ?_))))))
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w0.toNat < 2 ^ 63⌝ ∗ ⌜w48.setWidth 32 = pb.idx⌝ ∗
    (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      ((a + 48#64) ↦₆₄ w48)) ∗
     (vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ∗
      vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys)) by ac_rfl)) ?_
  apply Entails.pure_left; intro hlt
  apply Entails.pure_left; intro hidx
  refine Entails.pure_right hlt ?_
  have hpure : v2hse_ProtoPolyEncoderPure pb (BitVec.ofNat 64 pb.pts.length)
      (BitVec.ofNat 64 pb.polys.length) w48 := ⟨rfl, rfl, hidx⟩
  exact sepConj_mono_right (Entails.pure_right hpure (Entails.refl _))

theorem v2hse_protoPolyEncoderAt_pack (A : RustAlloc) (a : BitVec 64) (pb : ProtoPolynomialEncoder)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v2hse_protoPolyEncoderWordsAt a w0 w8 w16 w24 w32 w40 w48 ∗
      v2hse_protoPolyEncoderHeap A pb w0 w8 w16 w24 w32 w40 w48 ⊢
    protoPolynomialEncoderAt A a pb := by
  unfold protoPolynomialEncoderAt vecVecU8At vecOf vecAt vecHeader
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
    v2hse_protoPolyEncoderWordsAt v2hse_protoPolyEncoderHeap
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜v2hse_ProtoPolyEncoderPure pb w16 w40 w48⌝ ∗
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
     ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
     ((a + 48#64) ↦₆₄ w48) ∗
     vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ∗
     vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, rfl, hidx⟩
  rw [sepExists_sepConj_left]; refine Entails.sepExists_right w0 ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_right w8 ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; refine Entails.sepExists_right w24 ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; refine Entails.sepExists_right w32 ?_
  have htail := v2hse_pointsTo64_entails_32_pad4 (a + 48#64) w48
  rw [hidx] at htail
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at htail ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    ((a + 48#64) ↦₆₄ w48) ∗
    (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts) ∗
     (((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys)) by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))

theorem v2hse_memRegion_1792_56_split (fsp : BitVec 64) :
    memRegion (fsp + 1792#64) 56 ⊢
      (∃∗ e0 : BitVec 64, (fsp + 1792#64) ↦₆₄ e0) ∗
      (∃∗ e8 : BitVec 64, (fsp + 1800#64) ↦₆₄ e8) ∗
      (∃∗ e16 : BitVec 64, (fsp + 1808#64) ↦₆₄ e16) ∗
      (∃∗ e24 : BitVec 64, (fsp + 1816#64) ↦₆₄ e24) ∗
      (∃∗ e32 : BitVec 64, (fsp + 1824#64) ↦₆₄ e32) ∗
      (∃∗ e40 : BitVec 64, (fsp + 1832#64) ↦₆₄ e40) ∗
      (∃∗ e48 : BitVec 64, (fsp + 1840#64) ↦₆₄ e48) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    mem64_entails _

set_option maxHeartbeats 800000 in
/-- Execution segment `+9036 -> +9096`: copies the 56-byte `ProtoPolynomialEncoder` words
`(w0, w8, w16, w24, w32, w40, w48)` into `fsp + 1792..1848`. -/
theorem v2hse_copy_enc_9032_to_9096
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out d0 ca3 pbA w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9036#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx8_1 : s1.readReg64 .x8 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9096#64) s1
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
  states_from_pb_fetches_range b (Rust.withPanics ext) 9036 60
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
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

end CryptoVerification.SpqrV1.States.FromPb

