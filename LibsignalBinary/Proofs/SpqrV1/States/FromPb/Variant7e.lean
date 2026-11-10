/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7d
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# SPQR V1 `<States>::from_pb`: Variant 7 (`Ct1Sampled`, niche variant) — Part E

`<Ct1Sent>::from_pb` phase (`+3480..+3648`) and `<PolyEncoder>::from_pb` phase (`+3648..+7348`)
for Variant 7.
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-! ## 1. Unaligned Copy & Stack Layout Helpers -/

/-- Entry block `+1056 -> +3480` when `s.receivingEk` is `none` or has `ptsNeeded = 576`,
    additionally recording preservation of `x23` and `x25`. -/
theorem v7_entry_1056_to_3480_full
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA c1 w0 cap_dec x23_val x25_val : BitVec 64)
    (optDecPb : Option PolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec (optDecPb.map pbToProtoPolyDecoder))
    (hpts : v7_receivingEkPtsOk optDecPb)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1056#64)
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
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3480#64) s1
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
    states_from_pb_fetches_range b (Rust.withPanics ext) 1056 12
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, Option.map_none, noneCap,
      BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
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
    states_from_pb_fetches_range b (Rust.withPanics ext) 1056 24
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, Option.map_some,
      BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
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

theorem v7_byte_pointsTo64_eq_pointsTo64_byte (a w : BitVec 64) (b : BitVec 8) :
    (a ↦₆₄ w) ∗ ((a + 8#64) ↦₈ b) =
      (a ↦₈ EncoderFromPb.loByte w) ∗ ((a + 1#64) ↦₆₄ EncoderFromPb.unshiftWord w b) := by
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      ProofLib.pointsTo64_eq_pointsToBytes (a + 1#64),
      ← ProofLib.pointsToBytes_cons,
      EncoderFromPb.loByte_cons_unpack64_unshiftWord w b,
      ProofLib.pointsToBytes_append a (unpack64 w) [b], unpack64_length]
  simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]

theorem v7_triple64_to_byte_qword_tail7 (a w8 w16 w24 : BitVec 64) :
    (a ↦₆₄ w8) ∗ ((a + 8#64) ↦₆₄ w16) ∗ ((a + 16#64) ↦₆₄ w24) =
      (a ↦₈ EncoderFromPb.loByte w8) ∗
      ((a + 1#64) ↦₁₂₈
        (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24) ++
         EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 w24) := by
  have hp := EncoderFromPb.pair64_to_byte_word_tail7 (a + 8#64) w16 w24
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  have ha17 : a + 8#64 + 9#64 = a + 17#64 := by bv_omega
  rw [ha16, ha9, ha17] at hp
  have hq := EncoderFromPb.pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))
    (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24))
  have ha9' : a + 1#64 + 8#64 = a + 9#64 := by bv_omega
  rw [ha9'] at hq
  rw [hp, ← sepConj_assoc, ← sepConj_assoc,
      v7_byte_pointsTo64_eq_pointsTo64_byte a w8 (EncoderFromPb.loByte w16),
      sepConj_assoc (a ↦₈ EncoderFromPb.loByte w8),
      sepConj_assoc (a ↦₈ EncoderFromPb.loByte w8), hq]



theorem v7_byte_qword_mem7_to_triple64 (a w8 w16 w24 : BitVec 64) :
    (a ↦₈ EncoderFromPb.loByte w8) ∗
    ((a + 1#64) ↦₁₂₈
      (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24) ++
       EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))) ∗
    memRegion (a + 17#64) 7 ⊢
    ∃∗ u16 : BitVec 64,
      (a ↦₆₄ w8) ∗ ((a + 8#64) ↦₆₄ w16) ∗ ((a + 16#64) ↦₆₄ u16) := by
  have hq := EncoderFromPb.pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))
    (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24))
  have ha9 : a + 1#64 + 8#64 = a + 9#64 := by bv_omega
  rw [ha9] at hq
  rw [← hq, ← sepConj_assoc, ← sepConj_assoc,
      ← v7_byte_pointsTo64_eq_pointsTo64_byte a w8 (EncoderFromPb.loByte w16),
      sepConj_assoc, sepConj_assoc]
  have hjoin : ((a + 8#64) ↦₈ EncoderFromPb.loByte w16) ∗
      (((a + 9#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
       memRegion (a + 17#64) 7) ⊢
      ((a + 8#64) ↦₆₄ w16) ∗ (∃∗ u16 : BitVec 64, (a + 16#64) ↦₆₄ u16) := by
    have hb : ((a + 8#64) ↦₈ EncoderFromPb.loByte w16) ∗
        ((a + 9#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) =
        ((a + 8#64) ↦₆₄ w16) ∗ ((a + 16#64) ↦₈ EncoderFromPb.loByte w24) := by
      have h := (v7_byte_pointsTo64_eq_pointsTo64_byte (a + 8#64) w16 (EncoderFromPb.loByte w24)).symm
      have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
      have ha9' : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
      rw [ha16, ha9'] at h
      exact h
    rw [← sepConj_assoc, hb, sepConj_assoc]
    refine sepConj_mono_right ?_
    have hm : memRegion (a + 16#64) 1 ∗ memRegion (a + 17#64) 7 = memRegion (a + 16#64) 8 := by
      rw [← ProofLib.memRegion_split' (b := a + 16#64) (n := 1) (k := 7)
        (b' := a + 17#64) rfl (by bv_omega) (by decide)]
    rw [← ProofLib.memRegion_eight (a + 16#64), ← hm]
    exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)
  refine Entails.trans (sepConj_mono_right hjoin) ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right]
  exact Entails.refl _

/-- Pure condition on the exposed `cap` word at `d` of `optProtoPolynomialEncoderAt A d m`. -/
def v7_optEncoderCapProp (cap : BitVec 64) : Option ProtoPolynomialEncoder → Prop
  | none => cap = noneCap
  | some _ => cap.toNat < 2 ^ 63

/-- Remainder of `optProtoPolynomialEncoderAt A d m` after splitting out `d ↦₆₄ cap`. -/
def v7_optProtoPolyEncoderTail (A : RustAlloc) (d cap : BitVec 64)
    (m : Option ProtoPolynomialEncoder) : SepProp :=
  match m with
  | none => ⌜cap = noneCap⌝ ∗ memRegion (d + 8#64) 48
  | some pb =>
    ∃∗ ptr : BitVec 64,
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      protoPolynomialEncoderRestAt A d cap ptr pb

theorem v7_optProtoPolyEncoder_expose_cap (A : RustAlloc) (d : BitVec 64)
    (m : Option ProtoPolynomialEncoder) :
    optProtoPolynomialEncoderAt A d m ⊢
      ∃∗ cap : BitVec 64,
        ⌜v7_optEncoderCapProp cap m⌝ ∗
        (d ↦₆₄ cap) ∗ v7_optProtoPolyEncoderTail A d cap m := by
  cases m with
  | none =>
    rw [optProtoPolynomialEncoderAt_none']
    refine Entails.sepExists_right noneCap ?_
    unfold v7_optEncoderCapProp v7_optProtoPolyEncoderTail
    refine Entails.pure_right rfl ?_
    exact sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))
  | some pb =>
    rw [optProtoPolynomialEncoderAt_some']
    refine Entails.trans (protoPolynomialEncoderAt_expose_cap A d pb) ?_
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    apply Entails.pure_left; intro hlt
    refine Entails.sepExists_right cap ?_
    unfold v7_optEncoderCapProp v7_optProtoPolyEncoderTail
    refine Entails.pure_right hlt ?_
    refine Entails.trans ?_
      (sepConj_mono_right (Entails.sepExists_right ptr (Entails.pure_right hlt (Entails.refl _))))
    exact Entails.of_eq (by ac_rfl)

theorem v7_optProtoPolyEncoder_unexpose_cap (A : RustAlloc) (d cap : BitVec 64)
    (m : Option ProtoPolynomialEncoder) :
    (d ↦₆₄ cap) ∗ v7_optProtoPolyEncoderTail A d cap m ⊢
      optProtoPolynomialEncoderAt A d m := by
  cases m with
  | none =>
    unfold v7_optProtoPolyEncoderTail
    rw [← sepConj_assoc, sepConj_comm (d ↦₆₄ cap), sepConj_assoc]
    apply Entails.pure_left; intro hcap
    subst hcap
    rw [optProtoPolynomialEncoderAt_none']
    exact Entails.refl _
  | some pb =>
    unfold v7_optProtoPolyEncoderTail
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ptr
    rw [← sepConj_assoc, sepConj_comm (d ↦₆₄ cap), sepConj_assoc]
    apply Entails.pure_left; intro _
    rw [optProtoPolynomialEncoderAt_some']
    exact protoPolynomialEncoderAt_unexpose_cap A d cap ptr pb

theorem v7_stackAt_encoderFromPbStack_to_ct1Sent (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp ct1SentFromPbStack ∗
        memRegion (fsp - BitVec.ofNat 64 encoderFromPbStack) (encoderFromPbStack - ct1SentFromPbStack) := by
  have h := ProofLib.stackAt_split_bottom fsp ct1SentFromPbStack (encoderFromPbStack - ct1SentFromPbStack) (by decide)
  have heq : ct1SentFromPbStack + (encoderFromPbStack - ct1SentFromPbStack) = encoderFromPbStack := by decide
  rw [heq] at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v7_stackAt_ct1Sent_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp ct1SentFromPbStack ∗
      memRegion (fsp - BitVec.ofNat 64 encoderFromPbStack) (encoderFromPbStack - ct1SentFromPbStack) ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp ct1SentFromPbStack (encoderFromPbStack - ct1SentFromPbStack) (by decide)
  have heq : ct1SentFromPbStack + (encoderFromPbStack - ct1SentFromPbStack) = encoderFromPbStack := by decide
  rw [heq] at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Word-Bundle Unpack/Pack for `ProtoUnchunkedCt1Sent` (`128`B) and `ProtoPolynomialEncoder` (`56`B) -/

def v7_vecU8Heap (A : RustAlloc) (bs : List (BitVec 8)) (cap ptr len : BitVec 64) : SepProp :=
  ⌜len = BitVec.ofNat 64 bs.length ∧ cap.toNat < 2 ^ 63⌝ ∗
  vecU8Payload A cap ptr bs

theorem v7_vecU8_unpack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) ∗
        v7_vecU8Heap A bs cap ptr len := by
  refine Entails.trans (vecU8_unpack A a bs) ?_
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  apply Entails.pure_left; rintro ⟨_, hcap⟩
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_))
  unfold v7_vecU8Heap
  have hpure : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length ∧ cap.toNat < 2 ^ 63 :=
    ⟨rfl, hcap⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v7_vecU8_pack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8))
    (cap ptr len : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) ∗
      v7_vecU8Heap A bs cap ptr len ⊢
    vecU8 A a bs := by
  unfold v7_vecU8Heap
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜len = BitVec.ofNat 64 bs.length ∧ cap.toNat < 2 ^ 63⌝ ∗
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len) ∗
     vecU8Payload A cap ptr bs) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, _⟩
  exact vecU8_of_header_payload A a cap ptr bs

def v7_optProtoAuthHeap (A : RustAlloc) :
    Option ProtoAuthenticator →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some auth, w0, w8, w16, w24, w32, w40 =>
    v7_vecU8Heap A auth.rootKey w0 w8 w16 ∗
    v7_vecU8Heap A auth.macKey w24 w32 w40

theorem v7_optProtoAuthAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optAuth : Option ProtoAuthenticator) :
    optProtoAuthenticatorAt A a optAuth ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64,
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
         ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40)) ∗
        v7_optProtoAuthHeap A optAuth w0 w8 w16 w24 w32 w40 := by
  cases optAuth with
  | none =>
    dsimp only [optProtoAuthenticatorAt, v7_optProtoAuthHeap]
    have hsplit : memRegion (a + 8#64) 40 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
        (∃∗ w40 : BitVec 64, (a + 40#64) ↦₆₄ w40) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40 ?_)))))
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some auth =>
    dsimp only [optProtoAuthenticatorAt, protoAuthenticatorAt, v7_optProtoAuthHeap]
    refine Entails.trans
      (sepConj_mono (v7_vecU8_unpack A a auth.rootKey)
        (v7_vecU8_unpack A (a + 24#64) auth.macKey)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w8
    apply Entails.sepExists_elim; intro w16
    refine Entails.sepExists_right w0 (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40 ?_)))))
    exact Entails.of_eq (by ac_rfl)

theorem v7_optProtoAuthAt_pack (A : RustAlloc) (a : BitVec 64)
    (optAuth : Option ProtoAuthenticator)
    (w0 w8 w16 w24 w32 w40 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
     ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40)) ∗
      v7_optProtoAuthHeap A optAuth w0 w8 w16 w24 w32 w40 ⊢
    optProtoAuthenticatorAt A a optAuth := by
  cases optAuth with
  | none =>
    dsimp only [optProtoAuthenticatorAt, v7_optProtoAuthHeap]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜w0 = noneCap⌝ ∗
      ((a ↦₆₄ w0) ∗
       (((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
        ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40))) by ac_rfl)) ?_
    apply Entails.pure_left; rintro rfl
    refine sepConj_mono_right ?_
    exact collapse_top <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _
  | some auth =>
    dsimp only [optProtoAuthenticatorAt, protoAuthenticatorAt, v7_optProtoAuthHeap]
    have hpack := sepConj_mono
      (v7_vecU8_pack A a auth.rootKey w0 w8 w16)
      (v7_vecU8_pack A (a + 24#64) auth.macKey w24 w32 w40)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack
    refine Entails.trans (Entails.of_eq (by ac_rfl)) hpack

/-- 15 64-bit words at `a + 8..a + 128` (`120` bytes) of `ProtoUnchunkedCt1Sent`. -/
def v7_ucTailWordsAt
    (a w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : BitVec 64) : SepProp :=
  ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
  ((a + 48#64) ↦₆₄ w48) ∗ ((a + 56#64) ↦₆₄ w56) ∗ ((a + 64#64) ↦₆₄ w64) ∗
  ((a + 72#64) ↦₆₄ w72) ∗ ((a + 80#64) ↦₆₄ w80) ∗ ((a + 88#64) ↦₆₄ w88) ∗
  ((a + 96#64) ↦₆₄ w96) ∗ ((a + 104#64) ↦₆₄ w104) ∗ ((a + 112#64) ↦₆₄ w112) ∗
  ((a + 120#64) ↦₆₄ w120)

theorem v7_ucWordsAt_entails_128
    (a w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : BitVec 64) :
    (a ↦₆₄ w0) ∗
      v7_ucTailWordsAt a w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ⊢
      memRegion a 128 := by
  unfold v7_ucTailWordsAt
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
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

def v7_ucTailHeap (A : RustAlloc) (w0 : BitVec 64) (u : V1State.Unchunked.Ct1Sent)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : BitVec 64) : SepProp :=
  ⌜w16 = BitVec.ofNat 64 u.hdr.length ∧ w120 = u.epoch⌝ ∗
  vecU8Payload A w0 w8 u.hdr ∗
  v7_vecU8Heap A u.es w24 w32 w40 ∗
  v7_vecU8Heap A u.ct1 w48 w56 w64 ∗
  v7_optProtoAuthHeap A u.auth w72 w80 w88 w96 w104 w112

theorem v7_ucTail_unpack (A : RustAlloc) (a w0 : BitVec 64) (u : V1State.Unchunked.Ct1Sent) :
    v7_optProtoUnchunkedCt1SentTail A a w0 (some u) ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64,
      ∃∗ w48 : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ w64 : BitVec 64,
      ∃∗ w72 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w88 : BitVec 64,
      ∃∗ w96 : BitVec 64, ∃∗ w104 : BitVec 64, ∃∗ w112 : BitVec 64,
      ∃∗ w120 : BitVec 64,
        v7_ucTailWordsAt a w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ∗
        v7_ucTailHeap A w0 u w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 := by
  unfold v7_optProtoUnchunkedCt1SentTail protoUnchunkedCt1SentEkReceivedRestAt
  dsimp only [v7_ct1SentToCt1SentEkReceived]
  apply Entails.sepExists_elim; intro w8
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (v7_vecU8_unpack A (a + 24#64) u.es)
        (sepConj_mono (v7_vecU8_unpack A (a + 48#64) u.ct1)
          (sepConj_mono_left (v7_optProtoAuthAt_unpack A (a + 72#64) u.auth)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro w72
  apply Entails.sepExists_elim; intro w80
  apply Entails.sepExists_elim; intro w88
  apply Entails.sepExists_elim; intro w96
  apply Entails.sepExists_elim; intro w104
  apply Entails.sepExists_elim; intro w112
  apply Entails.sepExists_elim; intro w48
  apply Entails.sepExists_elim; intro w56
  apply Entails.sepExists_elim; intro w64
  apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro w32
  apply Entails.sepExists_elim; intro w40
  refine Entails.sepExists_right w8 (Entails.sepExists_right (BitVec.ofNat 64 u.hdr.length)
    (Entails.sepExists_right w24 (Entails.sepExists_right w32 (Entails.sepExists_right w40
      (Entails.sepExists_right w48 (Entails.sepExists_right w56 (Entails.sepExists_right w64
        (Entails.sepExists_right w72 (Entails.sepExists_right w80 (Entails.sepExists_right w88
          (Entails.sepExists_right w96 (Entails.sepExists_right w104 (Entails.sepExists_right w112
            (Entails.sepExists_right u.epoch ?_))))))))))))))
  unfold v7_ucTailWordsAt v7_ucTailHeap vecU8Payload
  have hpure : BitVec.ofNat 64 u.hdr.length = BitVec.ofNat 64 u.hdr.length ∧ u.epoch = u.epoch :=
    ⟨rfl, rfl⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v7_ucAt_pack (A : RustAlloc) (a w0 : BitVec 64) (u : V1State.Unchunked.Ct1Sent)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : BitVec 64) :
    (a ↦₆₄ w0) ∗
      v7_ucTailWordsAt a w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ∗
      v7_ucTailHeap A w0 u w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ⊢
    protoUnchunkedCt1SentAt A a u := by
  refine Entails.trans ?_ (v7_optProtoUnchunkedCt1Sent_unexpose_some A a w0 u)
  refine sepConj_mono_right ?_
  unfold v7_optProtoUnchunkedCt1SentTail protoUnchunkedCt1SentEkReceivedRestAt
    v7_ucTailWordsAt v7_ucTailHeap
  dsimp only [v7_ct1SentToCt1SentEkReceived]
  refine Entails.sepExists_right w8 ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w16 = BitVec.ofNat 64 u.hdr.length ∧ w120 = u.epoch⌝ ∗
    (((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
     vecU8Payload A w0 w8 u.hdr ∗
     ((((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40)) ∗
      v7_vecU8Heap A u.es w24 w32 w40) ∗
     ((((a + 48#64) ↦₆₄ w48) ∗ ((a + 56#64) ↦₆₄ w56) ∗ ((a + 64#64) ↦₆₄ w64)) ∗
      v7_vecU8Heap A u.ct1 w48 w56 w64) ∗
     ((((a + 72#64) ↦₆₄ w72) ∗ ((a + 80#64) ↦₆₄ w80) ∗ ((a + 88#64) ↦₆₄ w88) ∗
       ((a + 96#64) ↦₆₄ w96) ∗ ((a + 104#64) ↦₆₄ w104) ∗ ((a + 112#64) ↦₆₄ w112)) ∗
      v7_optProtoAuthHeap A u.auth w72 w80 w88 w96 w104 w112) ∗
     ((a + 120#64) ↦₆₄ w120)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, rfl⟩
  have hes := v7_vecU8_pack A (a + 24#64) u.es w24 w32 w40
  have hct1 := v7_vecU8_pack A (a + 48#64) u.ct1 w48 w56 w64
  have hauth := v7_optProtoAuthAt_pack A (a + 72#64) u.auth w72 w80 w88 w96 w104 w112
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hes hct1 hauth
  unfold vecU8Payload
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hes (sepConj_mono hct1 (sepConj_mono_left hauth)))))) ?_
  exact Entails.of_eq (by ac_rfl)

def v7_u32Pad4Prop (w : BitVec 64) (lo32 : BitVec 32) : Prop :=
  ∃ bs : List (BitVec 8), bs.length = 4 ∧ unpack32 lo32 ++ bs = unpack64 w

theorem v7_u32_pad4_to_u64 (a : BitVec 64) (lo32 : BitVec 32) :
    (a ↦₃₂ lo32) ∗ memRegion (a + 4#64) 4 ⊢
      ∃∗ w : BitVec 64, ⌜v7_u32Pad4Prop w lo32⌝ ∗ (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_eq_exists_bytes (a + 4#64) 4 (by decide),
      sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [← sepConj_assoc, sepConj_comm (a ↦₃₂ lo32), sepConj_assoc]
  apply Entails.pure_left; intro hbs
  have h8 : (unpack32 lo32 ++ bs).length = 8 := by
    rw [List.length_append, unpack32_length, hbs]
  obtain ⟨w, hw⟩ := ProofLib.exists_unpack64_of_length_8 h8
  have hcell : (a ↦₃₂ lo32) ∗ ((a + 4#64) ↦ₛ bs) = (a ↦₆₄ w) := by
    rw [ProofLib.pointsTo32_eq_pointsToBytes a lo32]
    have h := (ProofLib.pointsToBytes_append a (unpack32 lo32) bs).symm
    rw [unpack32_length] at h
    rw [h, hw, ← ProofLib.pointsTo64_eq_pointsToBytes a w]
  rw [hcell]
  exact Entails.sepExists_right w (Entails.pure_right ⟨bs, hbs, hw⟩ (Entails.refl _))

theorem v7_u64_to_u32_pad4 (a : BitVec 64) (w : BitVec 64) (lo32 : BitVec 32)
    (hlo : v7_u32Pad4Prop w lo32) :
    (a ↦₆₄ w) ⊢ (a ↦₃₂ lo32) ∗ memRegion (a + 4#64) 4 := by
  rcases hlo with ⟨bs, hbs, hw⟩
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w, ← hw,
      ProofLib.pointsToBytes_append a (unpack32 lo32) bs,
      unpack32_length, ← ProofLib.pointsTo32_eq_pointsToBytes a lo32]
  exact sepConj_mono_right (hbs ▸ ProofLib.pointsToBytes_entails_memRegion (a + 4#64) bs)

/-- 6 64-bit words at `d + 8..d + 56` (`48` bytes) of `ProtoPolynomialEncoder`. -/
def v7_encTailWordsAt (d w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  ((d + 8#64) ↦₆₄ w8) ∗ ((d + 16#64) ↦₆₄ w16) ∗
  ((d + 24#64) ↦₆₄ w24) ∗ ((d + 32#64) ↦₆₄ w32) ∗ ((d + 40#64) ↦₆₄ w40) ∗
  ((d + 48#64) ↦₆₄ w48)

theorem v7_encWordsAt_entails_56 (d w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    (d ↦₆₄ w0) ∗ v7_encTailWordsAt d w8 w16 w24 w32 w40 w48 ⊢ memRegion d 56 := by
  unfold v7_encTailWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

def v7_encTailHeap (A : RustAlloc) (cap : BitVec 64) (pb : ProtoPolynomialEncoder)
    (w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  ⌜cap.toNat < 2 ^ 63 ∧ w16 = BitVec.ofNat 64 pb.pts.length ∧
    w40 = BitVec.ofNat 64 pb.polys.length ∧ v7_u32Pad4Prop w48 pb.idx⌝ ∗
  vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) cap w8 pb.pts ∗
  vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys

theorem v7_encTail_unpack (A : RustAlloc) (d cap : BitVec 64) (pb : ProtoPolynomialEncoder) :
    v7_optProtoPolyEncoderTail A d cap (some pb) ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64,
      ∃∗ w48 : BitVec 64,
        v7_encTailWordsAt d w8 w16 w24 w32 w40 w48 ∗
        v7_encTailHeap A cap pb w8 w16 w24 w32 w40 w48 := by
  unfold v7_optProtoPolyEncoderTail protoPolynomialEncoderRestAt
    vecVecU8At vecOf vecAt vecHeader
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
  apply Entails.sepExists_elim; intro w8
  apply Entails.pure_left; intro hlt
  have h48 := v7_u32_pad4_to_u64 (d + 48#64) pb.idx
  have hd52 : (d + 48#64) + 4#64 = d + 52#64 := by bv_omega
  rw [hd52] at h48
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h48)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro w48
  apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro w32
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜v7_u32Pad4Prop w48 pb.idx⌝ ∗
    (((d + 8#64) ↦₆₄ w8) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) cap w8 pb.pts ∗
     ((d + 24#64) ↦₆₄ w24) ∗ ((d + 32#64) ↦₆₄ w32) ∗
     ((d + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys ∗
     ((d + 48#64) ↦₆₄ w48)) by ac_rfl)) ?_
  apply Entails.pure_left; intro hidx
  refine Entails.sepExists_right w8 (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length)
    (Entails.sepExists_right w24 (Entails.sepExists_right w32
      (Entails.sepExists_right (BitVec.ofNat 64 pb.polys.length)
        (Entails.sepExists_right w48 ?_)))))
  unfold v7_encTailWordsAt v7_encTailHeap
  have hpure : cap.toNat < 2 ^ 63 ∧
      BitVec.ofNat 64 pb.pts.length = BitVec.ofNat 64 pb.pts.length ∧
      BitVec.ofNat 64 pb.polys.length = BitVec.ofNat 64 pb.polys.length ∧
      v7_u32Pad4Prop w48 pb.idx := ⟨hlt, rfl, rfl, hidx⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v7_encAt_pack (A : RustAlloc) (d cap : BitVec 64) (pb : ProtoPolynomialEncoder)
    (w8 w16 w24 w32 w40 w48 : BitVec 64) :
    (d ↦₆₄ cap) ∗
      v7_encTailWordsAt d w8 w16 w24 w32 w40 w48 ∗
      v7_encTailHeap A cap pb w8 w16 w24 w32 w40 w48 ⊢
    protoPolynomialEncoderAt A d pb := by
  rw [← optProtoPolynomialEncoderAt_some' A d pb]
  refine Entails.trans ?_ (v7_optProtoPolyEncoder_unexpose_cap A d cap (some pb))
  refine sepConj_mono_right ?_
  unfold v7_optProtoPolyEncoderTail protoPolynomialEncoderRestAt
    vecVecU8At vecOf vecAt vecHeader
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
    v7_encTailWordsAt v7_encTailHeap
  refine Entails.sepExists_right w8 ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜cap.toNat < 2 ^ 63 ∧ w16 = BitVec.ofNat 64 pb.pts.length ∧
      w40 = BitVec.ofNat 64 pb.polys.length ∧ v7_u32Pad4Prop w48 pb.idx⌝ ∗
    (((d + 8#64) ↦₆₄ w8) ∗ ((d + 16#64) ↦₆₄ w16) ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) cap w8 pb.pts ∗
     ((((d + 24#64) ↦₆₄ w24) ∗ ((d + 32#64) ↦₆₄ w32) ∗ ((d + 40#64) ↦₆₄ w40)) ∗
      vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys) ∗
     ((d + 48#64) ↦₆₄ w48)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hlt, rfl, rfl, hidx⟩
  refine Entails.pure_right hlt ?_
  have h48 := v7_u64_to_u32_pad4 (d + 48#64) w48 pb.idx hidx
  have hd52 : (d + 48#64) + 4#64 = d + 52#64 := by bv_omega
  rw [hd52] at h48
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono ?_ h48
  refine Entails.sepExists_right w24 (Entails.sepExists_right w32 ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

def v7_u32PairProp (w : BitVec 64) (lo32 hi32 : BitVec 32) : Prop :=
  unpack32 lo32 ++ unpack32 hi32 = unpack64 w

theorem v7_u32_pair_to_u64 (a : BitVec 64) (lo32 hi32 : BitVec 32) :
    (a ↦₃₂ lo32) ∗ ((a + 4#64) ↦₃₂ hi32) ⊢
      ∃∗ w : BitVec 64, ⌜v7_u32PairProp w lo32 hi32⌝ ∗ (a ↦₆₄ w) := by
  have h8 : (unpack32 lo32 ++ unpack32 hi32).length = 8 := by
    rw [List.length_append, unpack32_length, unpack32_length]
  obtain ⟨w, hw⟩ := ProofLib.exists_unpack64_of_length_8 h8
  have hcell : (a ↦₃₂ lo32) ∗ ((a + 4#64) ↦₃₂ hi32) = (a ↦₆₄ w) := by
    rw [ProofLib.pointsTo32_eq_pointsToBytes a lo32,
        ProofLib.pointsTo32_eq_pointsToBytes (a + 4#64) hi32]
    have h := (ProofLib.pointsToBytes_append a (unpack32 lo32) (unpack32 hi32)).symm
    rw [unpack32_length] at h
    rw [h, hw, ← ProofLib.pointsTo64_eq_pointsToBytes a w]
  rw [hcell]
  exact Entails.sepExists_right w (Entails.pure_right hw (Entails.refl _))

theorem v7_u64_to_u32_pair (a : BitVec 64) (w : BitVec 64) (lo32 hi32 : BitVec 32)
    (hp : v7_u32PairProp w lo32 hi32) :
    (a ↦₆₄ w) ⊢ (a ↦₃₂ lo32) ∗ ((a + 4#64) ↦₃₂ hi32) := by
  unfold v7_u32PairProp at hp
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w, ← hp,
      ProofLib.pointsToBytes_append a (unpack32 lo32) (unpack32 hi32),
      unpack32_length,
      ← ProofLib.pointsTo32_eq_pointsToBytes a lo32,
      ← ProofLib.pointsTo32_eq_pointsToBytes (a + 4#64) hi32]
  exact Entails.refl _

def v7_u8Pad7Prop (w : BitVec 64) (b0 : BitVec 8) : Prop :=
  ∃ bs : List (BitVec 8), bs.length = 7 ∧ b0 :: bs = unpack64 w

theorem v7_u8_pad7_to_u64 (a : BitVec 64) (b0 : BitVec 8) :
    (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜v7_u8Pad7Prop w b0⌝ ∗ (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_eq_exists_bytes (a + 1#64) 7 (by decide),
      sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [← sepConj_assoc, sepConj_comm (a ↦₈ b0), sepConj_assoc]
  apply Entails.pure_left; intro hbs
  have h8 : (b0 :: bs).length = 8 := by simp [hbs]
  obtain ⟨w, hw⟩ := ProofLib.exists_unpack64_of_length_8 h8
  have hcell : (a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ bs) = (a ↦₆₄ w) := by
    rw [← ProofLib.pointsToBytes_cons a b0 bs, hw, ← ProofLib.pointsTo64_eq_pointsToBytes a w]
  rw [hcell]
  exact Entails.sepExists_right w (Entails.pure_right ⟨bs, hbs, hw⟩ (Entails.refl _))

theorem v7_u64_to_u8_pad7 (a : BitVec 64) (w : BitVec 64) (b0 : BitVec 8)
    (hp : v7_u8Pad7Prop w b0) :
    (a ↦₆₄ w) ⊢ (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 := by
  rcases hp with ⟨bs, hbs, hw⟩
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w, ← hw, ProofLib.pointsToBytes_cons a b0 bs]
  exact sepConj_mono_right (hbs ▸ ProofLib.pointsToBytes_entails_memRegion (a + 1#64) bs)

/-- 4 64-bit words at `d + 8..d + 40` (`32` bytes) of `ProtoPolynomialDecoder`. -/
def v7_decTailWordsAt (d w8 w16 w24 w32 : BitVec 64) : SepProp :=
  ((d + 8#64) ↦₆₄ w8) ∗ ((d + 16#64) ↦₆₄ w16) ∗
  ((d + 24#64) ↦₆₄ w24) ∗ ((d + 32#64) ↦₆₄ w32)

theorem v7_decWordsAt_entails_40 (d w0 w8 w16 w24 w32 : BitVec 64) :
    (d ↦₆₄ w0) ∗ v7_decTailWordsAt d w8 w16 w24 w32 ⊢ memRegion d 40 := by
  unfold v7_decTailWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

def v7_decTailHeap (A : RustAlloc) (cap : BitVec 64) (pb : ProtoPolynomialDecoder)
    (w8 w16 w24 w32 : BitVec 64) : SepProp :=
  ⌜pb.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ w8 ≠ 0 ∧
    w16 = BitVec.ofNat 64 pb.pts.length ∧
    v7_u32PairProp w24 pb.ptsNeeded pb.polys ∧
    v7_u8Pad7Prop w32 (boolByte pb.isComplete)⌝ ∗
  (if cap = 0 then emp
   else A.live w8 (cap.toNat * 24) 8 ∗
     arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
     memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24))
       ((cap.toNat - pb.pts.length) * 24))

theorem v7_decTail_unpack (A : RustAlloc) (d cap : BitVec 64) (pb : ProtoPolynomialDecoder) :
    v7_optProtoPolyDecoderTail A d cap (some pb) ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64,
        v7_decTailWordsAt d w8 w16 w24 w32 ∗
        v7_decTailHeap A cap pb w8 w16 w24 w32 := by
  unfold v7_optProtoPolyDecoderTail
    protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
    protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
    protoPolynomialDecoderPadSize
  apply Entails.sepExists_elim; intro w8
  apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
  have h24 := v7_u32_pair_to_u64 (d + 24#64) pb.ptsNeeded pb.polys
  have hd28 : (d + 24#64) + 4#64 = d + 0x1c#64 := by bv_omega
  rw [hd28] at h24
  have h32 := v7_u8_pad7_to_u64 (d + 32#64) (boolByte pb.isComplete)
  have hd33 : (d + 32#64) + 1#64 = d + 0x21#64 := by bv_omega
  rw [hd33] at h32
  have h24_32 :
      ((d + 0x18#64) ↦₃₂ pb.ptsNeeded) ∗ ((d + 0x1c#64) ↦₃₂ pb.polys) ∗
      ((d + 0x20#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (d + 0x21#64) 7 ⊢
      (∃∗ w24 : BitVec 64, ⌜v7_u32PairProp w24 pb.ptsNeeded pb.polys⌝ ∗ ((d + 24#64) ↦₆₄ w24)) ∗
      (∃∗ w32 : BitVec 64, ⌜v7_u8Pad7Prop w32 (boolByte pb.isComplete)⌝ ∗ ((d + 32#64) ↦₆₄ w32)) := by
    rw [← sepConj_assoc ((d + 0x18#64) ↦₃₂ pb.ptsNeeded)]
    exact sepConj_mono h24 h32
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h24_32))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w32
  apply Entails.sepExists_elim; intro w24
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜v7_u32PairProp w24 pb.ptsNeeded pb.polys⌝ ∗
    ⌜v7_u8Pad7Prop w32 (boolByte pb.isComplete)⌝ ∗
    (((d + 8#64) ↦₆₄ w8) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
     (if cap = 0 then emp
      else A.live w8 (cap.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
        memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24))
          ((cap.toNat - pb.pts.length) * 24)) ∗
     ((d + 24#64) ↦₆₄ w24) ∗ ((d + 32#64) ↦₆₄ w32)) by ac_rfl)) ?_
  apply Entails.pure_left; intro hp24
  apply Entails.pure_left; intro hp32
  refine Entails.sepExists_right w8 (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length)
    (Entails.sepExists_right w24 (Entails.sepExists_right w32 ?_)))
  unfold v7_decTailWordsAt v7_decTailHeap
  have hpure : pb.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ w8 ≠ 0 ∧
      BitVec.ofNat 64 pb.pts.length = BitVec.ofNat 64 pb.pts.length ∧
      v7_u32PairProp w24 pb.ptsNeeded pb.polys ∧
      v7_u8Pad7Prop w32 (boolByte pb.isComplete) :=
    ⟨hle, hlt, hne, rfl, hp24, hp32⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v7_decAt_pack (A : RustAlloc) (d cap : BitVec 64) (pb : ProtoPolynomialDecoder)
    (w8 w16 w24 w32 : BitVec 64) :
    (d ↦₆₄ cap) ∗
      v7_decTailWordsAt d w8 w16 w24 w32 ∗
      v7_decTailHeap A cap pb w8 w16 w24 w32 ⊢
    protoPolynomialDecoderAt A d pb := by
  refine Entails.trans ?_ (v7_optProtoPolyDecoder_unexpose_some A d cap pb)
  refine sepConj_mono_right ?_
  unfold v7_optProtoPolyDecoderTail
    protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
    protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
    protoPolynomialDecoderPadSize v7_decTailWordsAt v7_decTailHeap
  refine Entails.sepExists_right w8 ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜pb.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ w8 ≠ 0 ∧
      w16 = BitVec.ofNat 64 pb.pts.length ∧
      v7_u32PairProp w24 pb.ptsNeeded pb.polys ∧
      v7_u8Pad7Prop w32 (boolByte pb.isComplete)⌝ ∗
    (((d + 8#64) ↦₆₄ w8) ∗ ((d + 16#64) ↦₆₄ w16) ∗
     (if cap = 0 then emp
      else A.live w8 (cap.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
        memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24))
          ((cap.toNat - pb.pts.length) * 24)) ∗
     ((d + 24#64) ↦₆₄ w24) ∗ ((d + 32#64) ↦₆₄ w32)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hle, hlt, hne, rfl, hp24, hp32⟩
  refine Entails.pure_right ⟨hle, hlt, hne⟩ ?_
  have h24 := v7_u64_to_u32_pair (d + 24#64) w24 pb.ptsNeeded pb.polys hp24
  have hd28 : (d + 24#64) + 4#64 = d + 0x1c#64 := by bv_omega
  rw [hd28] at h24
  have h32 := v7_u64_to_u8_pad7 (d + 32#64) w32 (boolByte pb.isComplete) hp32
  have hd33 : (d + 32#64) + 1#64 = d + 0x21#64 := by bv_omega
  rw [hd33] at h32
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.trans (sepConj_mono h24 h32) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb
