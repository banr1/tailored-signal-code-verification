/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3a
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3b
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 3 (`Ct1Received`, `+692`) — Execution Segments

**Checked by Lean.**

Forward execution segments (`+692..+1012` and `+4984 -> +8180`) and composition for
`InnerState.ct1Received`.
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

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

@[local simp, local arm64_norm, local wp_norm]
theorem v3cr_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## `+692 -> +4176` (`uc = none`) and `+692 -> +784` (`uc = some u`): 160B PB Copy -/

theorem v3cr_triple64_to_unaligned_24_rest (a w1 w2 w3 : BitVec 64) (Rest : SepProp) :
    (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗ Rest =
      (a ↦₈ loByte w1) ∗ ((a + 1#64) ↦₆₄ unshiftWord w1 (loByte w2)) ∗
      ((a + 9#64) ↦₆₄ unshiftWord w2 (loByte w3)) ∗ ((a + 17#64) ↦ₛ loBytes7 (w3 >>> 8)) ∗ Rest := by
  have h := congrArg (· ∗ Rest) (v3cr_triple64_eq_byte_128_tail7 a w1 w2 w3)
  rw [pointsTo128_eq_pair64 (a + 1#64), extractLsb'_0_64_append, extractLsb'_64_64_append,
      v3a_hiBytes7_eq_loBytes7_shr8 w3, show a + 1#64 + 8#64 = a + 9#64 by bv_omega] at h
  exact (by ac_rfl : _ = ((a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3)) ∗ Rest).trans
    (h.trans (by ac_rfl))

theorem v3cr_fsp_904_triple64_rest (fsp w1 w2 w3 : BitVec 64) (Rest : SepProp) :
    ((fsp + 904#64) ↦₆₄ w1) ∗ ((fsp + 912#64) ↦₆₄ w2) ∗ ((fsp + 920#64) ↦₆₄ w3) ∗ Rest =
      ((fsp + 904#64) ↦₈ loByte w1) ∗ ((fsp + 905#64) ↦₆₄ unshiftWord w1 (loByte w2)) ∗
      ((fsp + 913#64) ↦₆₄ unshiftWord w2 (loByte w3)) ∗
      ((fsp + 921#64) ↦ₛ loBytes7 (w3 >>> 8)) ∗ Rest := by
  have h := v3cr_triple64_to_unaligned_24_rest (fsp + 904#64) w1 w2 w3 Rest
  simpa only [v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] using h

theorem v3cr_fsp_248_triple64_rest (fsp w1 w2 w3 : BitVec 64) (Rest : SepProp) :
    ((fsp + 248#64) ↦₆₄ w1) ∗ ((fsp + 256#64) ↦₆₄ w2) ∗ ((fsp + 264#64) ↦₆₄ w3) ∗ Rest =
      ((fsp + 248#64) ↦₈ loByte w1) ∗ ((fsp + 249#64) ↦₆₄ unshiftWord w1 (loByte w2)) ∗
      ((fsp + 257#64) ↦₆₄ unshiftWord w2 (loByte w3)) ∗
      ((fsp + 265#64) ↦ₛ loBytes7 (w3 >>> 8)) ∗ Rest := by
  have h := v3cr_triple64_to_unaligned_24_rest (fsp + 248#64) w1 w2 w3 Rest
  simpa only [v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] using h

theorem v3cr_memRegion_104_entails_ucWordsAt (a : BitVec 64) :
    memRegion a 104 ⊢
      ∃∗ d8 : BitVec 64, ∃∗ d16 : BitVec 64, ∃∗ d24 : BitVec 64, ∃∗ d32 : BitVec 64,
      ∃∗ d40 : BitVec 64, ∃∗ d48 : BitVec 64, ∃∗ d56 : BitVec 64, ∃∗ d64 : BitVec 64,
      ∃∗ d72 : BitVec 64, ∃∗ d80 : BitVec 64, ∃∗ d88 : BitVec 64, ∃∗ d96 : BitVec 64,
      ∃∗ d104 : BitVec 64,
        v1_ucWordsAt a d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 := by
  unfold v1_ucWordsAt
  refine Entails.trans (split_top (split_step0 (mem64_entails a) (v3cr_split_96_words a))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro d104; apply Entails.sepExists_elim; intro d96
  apply Entails.sepExists_elim; intro d88; apply Entails.sepExists_elim; intro d80
  apply Entails.sepExists_elim; intro d72; apply Entails.sepExists_elim; intro d64
  apply Entails.sepExists_elim; intro d56; apply Entails.sepExists_elim; intro d48
  apply Entails.sepExists_elim; intro d40; apply Entails.sepExists_elim; intro d32
  apply Entails.sepExists_elim; intro d24; apply Entails.sepExists_elim; intro d16
  apply Entails.sepExists_elim; intro d8
  exact Entails.sepExists_right d8 (Entails.sepExists_right d16 (Entails.sepExists_right d24
    (Entails.sepExists_right d32 (Entails.sepExists_right d40 (Entails.sepExists_right d48
      (Entails.sepExists_right d56 (Entails.sepExists_right d64 (Entails.sepExists_right d72
        (Entails.sepExists_right d80 (Entails.sepExists_right d88 (Entails.sepExists_right d96
          (Entails.sepExists_right d104 (Entails.of_eq (by ac_rfl))))))))))))))

theorem v3cr_memRegion_56_entails_encWordsAt (a : BitVec 64) :
    memRegion a 56 ⊢
      ∃∗ e0 : BitVec 64, ∃∗ e8 : BitVec 64, ∃∗ e16 : BitVec 64, ∃∗ e24 : BitVec 64,
      ∃∗ e32 : BitVec 64, ∃∗ e40 : BitVec 64, ∃∗ e48 : BitVec 64,
        v1_optProtoPolyEncoderWordsAt a e0 e8 e16 e24 e32 e40 e48 := by
  unfold v1_optProtoPolyEncoderWordsAt
  have h : memRegion a 56 ⊢
      (∃∗ e0 : BitVec 64, a ↦₆₄ e0) ∗ (∃∗ e8 : BitVec 64, (a + 8#64) ↦₆₄ e8) ∗
      (∃∗ e16 : BitVec 64, (a + 16#64) ↦₆₄ e16) ∗ (∃∗ e24 : BitVec 64, (a + 24#64) ↦₆₄ e24) ∗
      (∃∗ e32 : BitVec 64, (a + 32#64) ↦₆₄ e32) ∗ (∃∗ e40 : BitVec 64, (a + 40#64) ↦₆₄ e40) ∗
      (∃∗ e48 : BitVec 64, (a + 48#64) ↦₆₄ e48) :=
    split_top <| split_step0 (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <| mem64_entails _
  refine Entails.trans h ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro e48; apply Entails.sepExists_elim; intro e40
  apply Entails.sepExists_elim; intro e32; apply Entails.sepExists_elim; intro e24
  apply Entails.sepExists_elim; intro e16; apply Entails.sepExists_elim; intro e8
  apply Entails.sepExists_elim; intro e0
  exact Entails.sepExists_right e0 (Entails.sepExists_right e8 (Entails.sepExists_right e16
    (Entails.sepExists_right e24 (Entails.sepExists_right e32 (Entails.sepExists_right e40
      (Entails.sepExists_right e48 (Entails.of_eq (by ac_rfl))))))))

theorem v3cr_sepWP_memRegion_104 {prog : Program} {t : BitVec 64} {s : State}
    {a : BitVec 64} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : ∀ d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 : BitVec 64,
      SepWP prog t s (v1_ucWordsAt a d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗ Rest) post) :
    SepWP prog t s (memRegion a 104 ∗ Rest) post := by
  refine SepWP.weaken_pre (sepConj_mono_left (v3cr_memRegion_104_entails_ucWordsAt a)) ?_
  iterate 13 (rw [sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro _)
  exact h _ _ _ _ _ _ _ _ _ _ _ _ _

theorem v3cr_sepWP_memRegion_56 {prog : Program} {t : BitVec 64} {s : State}
    {a : BitVec 64} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : ∀ e0 e8 e16 e24 e32 e40 e48 : BitVec 64,
      SepWP prog t s (v1_optProtoPolyEncoderWordsAt a e0 e8 e16 e24 e32 e40 e48 ∗ Rest) post) :
    SepWP prog t s (memRegion a 56 ∗ Rest) post := by
  refine SepWP.weaken_pre (sepConj_mono_left (v3cr_memRegion_56_entails_encWordsAt a)) ?_
  iterate 7 (rw [sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro _)
  exact h _ _ _ _ _ _ _

theorem v3cr_copy_pb_692_none
    {b : BitVec 64} {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
     d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
     e0 e8 e16 e24 e32 e40 e48 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 692#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4176#64) s1
      (v1_ucWordsAt (pbA + 8#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_ucWordsAt (fsp + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) e0 e8 e16 e24 e32 e40 e48 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_ucWordsAt (pbA + 8#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_ucWordsAt (fsp + 1392#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = 0#64 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1
  states_from_pb_fetches_range b (Rust.withPanics ext) 692 92
  states_from_pb_fetches_range b (Rust.withPanics ext) 4172 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt, sepConj_assoc]
  wp_steps
  simp only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt, sepConj_assoc]; wp_done

theorem v3cr_copy_pb_692_some
    {b : BitVec 64} {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
     d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
     e0 e8 e16 e24 e32 e40 e48 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hu8_lt : u8.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 692#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64) (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 784#64) s1
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_ucWordsAt (fsp + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) e0 e8 e16 e24 e32 e40 e48 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_ucWordsAt (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x8 = u8 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x29 = s1.readReg64 .x29 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1
  have hu8_ne1 := v10_cap_add_one_beq_zero_false hu8_lt
  states_from_pb_fetches_range b (Rust.withPanics ext) 692 92
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt, sepConj_assoc]
  wp_steps
  simp only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt, sepConj_assoc]; wp_done

/-! ## Unaligned 24-Byte Copy Helpers & (`+784 -> fnAddr ekSentCt1ReceivedFromPbName`) -/

@[local arm64_norm, local wp_norm]
theorem v3cr_pbA_17_add_8 (pbA : BitVec 64) : (pbA + 17#64) + 8#64 = pbA + 25#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_pbA_40_add_8 (pbA : BitVec 64) : (pbA + 40#64) + 8#64 = pbA + 48#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_pbA_56_add_8 (pbA : BitVec 64) : (pbA + 56#64) + 8#64 = pbA + 64#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_pbA_72_add_8 (pbA : BitVec 64) : (pbA + 72#64) + 8#64 = pbA + 80#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_pbA_88_add_8 (pbA : BitVec 64) : (pbA + 88#64) + 8#64 = pbA + 96#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_pbA_121_add_8 (pbA : BitVec 64) : (pbA + 121#64) + 8#64 = pbA + 129#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_pbA_144_add_8 (pbA : BitVec 64) : (pbA + 144#64) + 8#64 = pbA + 152#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_fsp_905_add_8 (fsp : BitVec 64) : (fsp + 905#64) + 8#64 = fsp + 913#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_fsp_928_add_8 (fsp : BitVec 64) : (fsp + 928#64) + 8#64 = fsp + 936#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_fsp_944_add_8 (fsp : BitVec 64) : (fsp + 944#64) + 8#64 = fsp + 952#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_fsp_960_add_8 (fsp : BitVec 64) : (fsp + 960#64) + 8#64 = fsp + 968#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_fsp_976_add_8 (fsp : BitVec 64) : (fsp + 976#64) + 8#64 = fsp + 984#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_fsp_249_add_8 (fsp : BitVec 64) : (fsp + 249#64) + 8#64 = fsp + 257#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_fsp_272_add_8 (fsp : BitVec 64) : (fsp + 272#64) + 8#64 = fsp + 280#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_fsp_848_add_48 (fsp : BitVec 64) : (fsp + 848#64) + 48#64 = fsp + 896#64 := by bv_omega

theorem v3cr_fnAddr_rel_ek_sent_ct1_received_from_pb (b : BitVec 64) (X : String → Option (State → State)) :
    (libsignalSessionCode.rebase b X).fnAddr ekSentCt1ReceivedFromPbName =
      (libsignalSessionCode.rebase b X).fnAddr statesFromPbName + 18368#64 :=
  Program.fnAddr_rel (k := 18368) (b := b) (X := X)
    statesFromPb_fnOff fnOff_ek_sent_ct1_received_from_pb (by decide)

theorem v3cr_copy_uc_to_call_784
    {b : BitVec 64} {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
     d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 784#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx8_1 : s1.readReg64 .x8 = u8) (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64) (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedFromPbName) s1
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        ((fsp + 1400#64) ↦₆₄ u16) ∗
        v1_ucWordsAt (fsp + 896#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          ((fsp + 1400#64) ↦₆₄ u16) ∗
          v1_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 1888#64 ∧ sm.readReg64 .x1 = fsp + 896#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s1.readReg64 .x29 ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 860#64 ∧
        TraceCalleeSaved sm s1) := by
  subst hsp1
  rw [v3cr_fnAddr_rel_ek_sent_ct1_received_from_pb]
  states_from_pb_fetches_range b (Rust.withPanics ext) 784 76
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre only [v1_ucWordsAt, v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
    v3cr_fsp_904_triple64_rest,
    v10_pbA_16_realign_rest, v3cr_fsp_1400_split_1_7_rest, sepConj_assoc]
  iterate 13 wp_step
  wp_simp_pre only [v10_pbA_16_unrealign_rest, v3cr_fsp_1400_unsplit_1_7_rest, sepConj_assoc]
  iterate 4 wp_step
  wp_simp_pre only [v3cr_fsp_913_realign_rest, sepConj_assoc]
  wp_step; wp_step
  wp_simp_pre only [v3cr_fsp_904_realign_rest, sepConj_assoc]
  simp only [v1_ucWordsAt, sepConj_assoc]; wp_done

/-! ## (`+860 -> +4176 | +4884 | +924`): Post-`EkSentCt1Received.from_pb` Dispatch -/

theorem v3cr_post_uc_860_err
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s1 : State) (fsp out w1896 w1904 w1912 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4176#64) s1
      (((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = w1896 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1; states_from_pb_fetches_range b (Rust.withPanics ext) 860 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem v3cr_post_uc_860_ok_none
    {b : BitVec 64} {ext : String → Option (State → State)} (s1 : State)
    (fsp out ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep v176 v224 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hca1_lt : ca1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4884#64) s1
      (((fsp + 176#64) ↦₆₄ v176) ∗ ((fsp + 224#64) ↦₆₄ v224) ∗ ((fsp + 1496#64) ↦₆₄ noneCap) ∗
        v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 1496#64) ↦₆₄ noneCap) ∗
          v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = pa2 ∧ sm.readReg64 .x1 = ca1 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa4 ∧ sm.readReg64 .x22 = pa1 ∧
        sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x28 = ca2 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1; have hca1_ne1 := v10_cap_add_one_beq_zero_false hca1_lt
  states_from_pb_fetches_range b (Rust.withPanics ext) 860 64
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches; wp_simp_pre only [v1_ucWordsAt, sepConj_assoc]; wp_steps
  simp only [v1_ucWordsAt, sepConj_assoc]; wp_done

theorem v3cr_post_uc_860_ok_some
    {b : BitVec 64} {ext : String → Option (State → State)} (s1 : State)
    (fsp out pbA ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep w0 v176 v224 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hca1_lt : ca1.toNat < 2 ^ 63) (hw0_lt : w0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64) (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 924#64) s1
      (((fsp + 176#64) ↦₆₄ v176) ∗ ((fsp + 224#64) ↦₆₄ v224) ∗ ((fsp + 1496#64) ↦₆₄ w0) ∗
        v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 1496#64) ↦₆₄ w0) ∗
          v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = pa2 ∧ sm.readReg64 .x1 = ca1 ∧ sm.readReg64 .x8 = w0 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa4 ∧ sm.readReg64 .x22 = pa1 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x24 = la1 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = ca2 ∧
        sm.readReg64 .x29 = s1.readReg64 .x29 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1
  have hca1_ne1 := v10_cap_add_one_beq_zero_false hca1_lt
  have hw0_ne1 := v10_cap_add_one_beq_zero_false hw0_lt
  states_from_pb_fetches_range b (Rust.withPanics ext) 860 64
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches; wp_simp_pre only [v1_ucWordsAt, sepConj_assoc]; wp_steps
  simp only [v1_ucWordsAt, sepConj_assoc]; wp_done

/-! ## (`+924 -> fnAddr encoderFromPbName`): Saving `uc` Fields & Copying `sendingEk` -/

theorem v3cr_copy_enc_to_call_924
    {b : BitVec 64} {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
     w0 w8 w16 w24 w32 w40 w48 v64 v96 v184 v192 v200
     e0 e8 e16 e24 e32 e40 e48 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 924#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2) (hx1_1 : s1.readReg64 .x1 = ca1)
    (hx8_1 : s1.readReg64 .x8 = w0) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa4) (hx22_1 : s1.readReg64 .x22 = pa1)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64) (hx24_1 : s1.readReg64 .x24 = la1)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = ca2) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encoderFromPbName) s1
      (((fsp + 64#64) ↦₆₄ v64) ∗ ((fsp + 96#64) ↦₆₄ v96) ∗
        ((fsp + 184#64) ↦₆₄ v184) ∗ ((fsp + 192#64) ↦₆₄ v192) ∗ ((fsp + 200#64) ↦₆₄ v200) ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 240#64) e0 e8 e16 e24 e32 e40 e48 ∗
        ((fsp + 1504#64) ↦₆₄ w8) ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 64#64) ↦₆₄ uc_ep) ∗ ((fsp + 96#64) ↦₆₄ la3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 192#64) ↦₆₄ la4) ∗ ((fsp + 200#64) ↦₆₄ ca1) ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
          ((fsp + 1504#64) ↦₆₄ w8) ∗
          v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 1888#64 ∧ sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = la2 ∧ sm.readReg64 .x21 = pa4 ∧
        sm.readReg64 .x22 = pa1 ∧ sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x24 = la1 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = ca2 ∧ sm.readReg64 .x29 = s1.readReg64 .x29 ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1012#64 ∧
        TraceCalleeSaved sm s1) := by
  subst hsp1
  rw [v10_fnAddr_rel_encoder_from_pb]
  states_from_pb_fetches_range b (Rust.withPanics ext) 924 88
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre only [v1_optProtoPolyEncoderWordsAt, v1_ucWordsAt,
    v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
    v3cr_fsp_248_triple64_rest,
    v3cr_pbA_120_realign_rest, v3cr_fsp_1504_split_1_7_rest, sepConj_assoc]
  iterate 14 wp_step
  wp_simp_pre only [v3cr_pbA_120_unrealign_rest, v3cr_fsp_1504_unsplit_1_7_rest, sepConj_assoc]
  iterate 6 wp_step
  wp_simp_pre only [v3cr_fsp_257_realign_rest, sepConj_assoc]
  wp_step; wp_step
  wp_simp_pre only [v3cr_fsp_248_realign_rest, sepConj_assoc]
  simp only [v1_optProtoPolyEncoderWordsAt, v1_ucWordsAt, sepConj_assoc]; wp_done

/-! ## (`+1012 -> +1024 | +4984`): Post-`<PolyEncoder>::from_pb` Branch -/

theorem v3cr_post_enc_1012_err
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s1 : State) (fsp out pa1 pa4 ca3 ca2 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1012#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa4)
    (hx22_1 : s1.readReg64 .x22 = pa1) (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = ca2) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1024#64) s1
      (((fsp + 1888#64) ↦₆₄ 2#64) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1888#64) ↦₆₄ 2#64) ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa4 ∧
        sm.readReg64 .x22 = pa1 ∧ sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x28 = ca2 ∧
        TraceCalleeSaved sm s1) := by
  subst hsp1; states_from_pb_fetches_range b (Rust.withPanics ext) 1012 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem v3cr_post_enc_1012_ok
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s1 : State) (fsp out tag la2 pa4 pa1 la1 ca3 ca2 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (htag_ne2 : (tag - 2#64 == 0#64) = false)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1012#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = la2)
    (hx21_1 : s1.readReg64 .x21 = pa4) (hx22_1 : s1.readReg64 .x22 = pa1)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64) (hx24_1 : s1.readReg64 .x24 = la1)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64) (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = ca2) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4984#64) s1
      (((fsp + 1888#64) ↦₆₄ tag) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1888#64) ↦₆₄ tag) ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x15 = tag ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = la2 ∧ sm.readReg64 .x21 = pa4 ∧ sm.readReg64 .x22 = pa1 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x24 = la1 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = ca2 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1; states_from_pb_fetches_range b (Rust.withPanics ext) 1012 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches; wp_steps; wp_done

/-! ## (`+4984 -> +8180`): `PolyEncoder` Relocation & `InnerState.ct1Received` Composition -/

@[local arm64_norm, local wp_norm]
theorem v3cr_fsp_1792_add_233 (fsp : BitVec 64) : (fsp + 1792#64) + 233#64 = fsp + 2025#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_fsp_848_add_15 (fsp : BitVec 64) : (fsp + 848#64) + 15#64 = fsp + 863#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v3cr_fsp_848_add_39 (fsp : BitVec 64) : (fsp + 848#64) + 39#64 = fsp + 887#64 := by bv_omega

def v3cr_unchunkedEkSentCt1ReceivedHeap (A : RustAlloc) {F : ShaCompress}
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64) : SepProp :=
  ⌜la1 = BitVec.ofNat 64 st.auth.rootKey.length ∧ la2 = BitVec.ofNat 64 st.auth.macKey.length ∧
    la3 = BitVec.ofNat 64 st.dk.length ∧ la4 = BitVec.ofNat 64 st.ct1.length ∧ uc_ep = st.epoch⌝ ∗
  vecU8Payload A ca1 pa1 st.auth.rootKey ∗ vecU8Payload A ca2 pa2 st.auth.macKey ∗
  vecU8Payload A ca3 pa3 st.dk ∗ vecU8Payload A ca4 pa4 st.ct1

theorem v3cr_unchunkedEkSentCt1ReceivedAt_open (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    unchunkedEkSentCt1ReceivedAt A (F := F) a st ⊢
      ∃∗ ca1 : BitVec 64, ∃∗ pa1 : BitVec 64, ∃∗ la1 : BitVec 64,
      ∃∗ ca2 : BitVec 64, ∃∗ pa2 : BitVec 64, ∃∗ la2 : BitVec 64,
      ∃∗ ca3 : BitVec 64, ∃∗ pa3 : BitVec 64, ∃∗ la3 : BitVec 64,
      ∃∗ ca4 : BitVec 64, ∃∗ pa4 : BitVec 64, ∃∗ la4 : BitVec 64, ∃∗ uc_ep : BitVec 64,
        v1_ucWordsAt a ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) st
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep := by
  dsimp only [unchunkedEkSentCt1ReceivedAt, authenticatorAt, v1_ucWordsAt, v3cr_unchunkedEkSentCt1ReceivedHeap]
  refine Entails.trans (sepConj_mono (sepConj_mono (vecU8_unpack A a st.auth.rootKey)
    (vecU8_unpack A (a + 24#64) st.auth.macKey))
    (sepConj_mono (vecU8_unpack A (a + 48#64) st.dk)
      (sepConj_mono (vecU8_unpack A (a + 72#64) st.ct1) (Entails.refl _)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro ca4; apply Entails.sepExists_elim; intro pa4; apply Entails.sepExists_elim; intro ca3
  apply Entails.sepExists_elim; intro pa3; apply Entails.sepExists_elim; intro ca2; apply Entails.sepExists_elim; intro pa2
  apply Entails.sepExists_elim; intro ca1; apply Entails.sepExists_elim; intro pa1
  simp only [v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜st.auth.rootKey.length < 2 ^ 63 ∧ ca1.toNat < 2 ^ 63⌝ ∗ ⌜st.auth.macKey.length < 2 ^ 63 ∧ ca2.toNat < 2 ^ 63⌝ ∗
    ⌜st.dk.length < 2 ^ 63 ∧ ca3.toNat < 2 ^ 63⌝ ∗ ⌜st.ct1.length < 2 ^ 63 ∧ ca4.toNat < 2 ^ 63⌝ ∗
    ((a ↦₆₄ ca1) ∗ ((a + 8#64) ↦₆₄ pa1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
     ((a + 24#64) ↦₆₄ ca2) ∗ ((a + 32#64) ↦₆₄ pa2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
     ((a + 48#64) ↦₆₄ ca3) ∗ ((a + 56#64) ↦₆₄ pa3) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 st.dk.length) ∗
     ((a + 72#64) ↦₆₄ ca4) ∗ ((a + 80#64) ↦₆₄ pa4) ∗ ((a + 88#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
     ((a + 96#64) ↦₆₄ st.epoch) ∗
     vecU8Payload A ca1 pa1 st.auth.rootKey ∗ vecU8Payload A ca2 pa2 st.auth.macKey ∗
     vecU8Payload A ca3 pa3 st.dk ∗ vecU8Payload A ca4 pa4 st.ct1) by ac_rfl)) ?_
  apply Entails.pure_left; intro _; apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _; apply Entails.pure_left; intro _
  refine Entails.sepExists_right ca1 (Entails.sepExists_right pa1
    (Entails.sepExists_right (BitVec.ofNat 64 st.auth.rootKey.length) (Entails.sepExists_right ca2
      (Entails.sepExists_right pa2 (Entails.sepExists_right (BitVec.ofNat 64 st.auth.macKey.length)
        (Entails.sepExists_right ca3 (Entails.sepExists_right pa3
          (Entails.sepExists_right (BitVec.ofNat 64 st.dk.length) (Entails.sepExists_right ca4
            (Entails.sepExists_right pa4 (Entails.sepExists_right (BitVec.ofNat 64 st.ct1.length)
              (Entails.sepExists_right st.epoch ?_))))))))))))
  refine Entails.trans (Entails.of_eq (show _ =
    ((a ↦₆₄ ca1) ∗ ((a + 8#64) ↦₆₄ pa1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
     ((a + 24#64) ↦₆₄ ca2) ∗ ((a + 32#64) ↦₆₄ pa2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
     ((a + 48#64) ↦₆₄ ca3) ∗ ((a + 56#64) ↦₆₄ pa3) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 st.dk.length) ∗
     ((a + 72#64) ↦₆₄ ca4) ∗ ((a + 80#64) ↦₆₄ pa4) ∗ ((a + 88#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
     ((a + 96#64) ↦₆₄ st.epoch)) ∗
    (vecU8Payload A ca1 pa1 st.auth.rootKey ∗ vecU8Payload A ca2 pa2 st.auth.macKey ∗
     vecU8Payload A ca3 pa3 st.dk ∗ vecU8Payload A ca4 pa4 st.ct1) by ac_rfl)) ?_
  have hp : BitVec.ofNat 64 st.auth.rootKey.length = BitVec.ofNat 64 st.auth.rootKey.length ∧
      BitVec.ofNat 64 st.auth.macKey.length = BitVec.ofNat 64 st.auth.macKey.length ∧
      BitVec.ofNat 64 st.dk.length = BitVec.ofNat 64 st.dk.length ∧
      BitVec.ofNat 64 st.ct1.length = BitVec.ofNat 64 st.ct1.length ∧ st.epoch = st.epoch := ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine Entails.trans (sepConj_mono_right (Entails.pure_right hp (Entails.refl _))) ?_
  simp only [sepConj_assoc]; exact Entails.refl _

theorem v3cr_unchunkedEkSentCt1ReceivedAt_close (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64) :
    v1_ucWordsAt a ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) st
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ⊢
    unchunkedEkSentCt1ReceivedAt A (F := F) a st := by
  dsimp only [unchunkedEkSentCt1ReceivedAt, authenticatorAt, v1_ucWordsAt, v3cr_unchunkedEkSentCt1ReceivedHeap]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜la1 = BitVec.ofNat 64 st.auth.rootKey.length ∧ la2 = BitVec.ofNat 64 st.auth.macKey.length ∧
      la3 = BitVec.ofNat 64 st.dk.length ∧ la4 = BitVec.ofNat 64 st.ct1.length ∧ uc_ep = st.epoch⌝ ∗
    (((a ↦₆₄ ca1) ∗ ((a + 8#64) ↦₆₄ pa1) ∗ ((a + 16#64) ↦₆₄ la1) ∗ vecU8Payload A ca1 pa1 st.auth.rootKey) ∗
     (((a + 24#64) ↦₆₄ ca2) ∗ ((a + 32#64) ↦₆₄ pa2) ∗ ((a + 40#64) ↦₆₄ la2) ∗ vecU8Payload A ca2 pa2 st.auth.macKey) ∗
     (((a + 48#64) ↦₆₄ ca3) ∗ ((a + 56#64) ↦₆₄ pa3) ∗ ((a + 64#64) ↦₆₄ la3) ∗ vecU8Payload A ca3 pa3 st.dk) ∗
     (((a + 72#64) ↦₆₄ ca4) ∗ ((a + 80#64) ↦₆₄ pa4) ∗ ((a + 88#64) ↦₆₄ la4) ∗ vecU8Payload A ca4 pa4 st.ct1) ∗
     ((a + 96#64) ↦₆₄ uc_ep)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
  have h1 := vecU8_of_header_payload A a ca1 pa1 st.auth.rootKey
  have h2 := vecU8_of_header_payload A (a + 24#64) ca2 pa2 st.auth.macKey
  have h3 := vecU8_of_header_payload A (a + 48#64) ca3 pa3 st.dk
  have h4 := vecU8_of_header_payload A (a + 72#64) ca4 pa4 st.ct1
  simp only [v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h2 h3 h4
  exact Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (Entails.refl _)))))
    (Entails.of_eq (by ac_rfl))

theorem v3cr_unchunkedHeap_entails_dealloc (A : RustAlloc) {F : ShaCompress}
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64) :
    v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) st ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ⊢
    vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗
      vecCapPtrDealloc A ca3 pa3 ∗ vecCapPtrDealloc A ca4 pa4 := by
  unfold v3cr_unchunkedEkSentCt1ReceivedHeap; apply Entails.pure_left; intro _
  exact sepConj_mono (vecU8Payload_entails_dealloc A ca1 pa1 _)
    (sepConj_mono (vecU8Payload_entails_dealloc A ca2 pa2 _)
      (sepConj_mono (vecU8Payload_entails_dealloc A ca3 pa3 _) (vecU8Payload_entails_dealloc A ca4 pa4 _)))

private theorem v3cr_vecU8Payload_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Payload A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Payload A cap ptr bs := by
  unfold vecU8Payload; apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
  exact Entails.pure_right h2 (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))

theorem v3cr_unchunkedHeap_ca1_lt (A : RustAlloc) {F : ShaCompress}
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64) :
    v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) st ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ⊢
    ⌜ca1.toNat < 2 ^ 63⌝ ∗
      v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) st ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep := by
  unfold v3cr_unchunkedEkSentCt1ReceivedHeap
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left (v3cr_vecU8Payload_cap_lt A ca1 pa1 st.auth.rootKey)))
    (Entails.of_eq (by ac_rfl))

theorem v3cr_chunkedCt1ReceivedAt_close (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64) (ucSt : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) (enc : PolyEncoder) :
    (out ↦₆₄ 5#64) ∗ polyEncoderAt A (out + 8#64) enc ∗
      unchunkedEkSentCt1ReceivedAt A (F := F) (out + 408#64) ucSt ∗ memRegion (out + 512#64) 416 ⊢
    resultChunkedStatesAt A (F := F) out (.ok (.ct1Received { uc := ucSt, sending_ek := enc })) := by
  dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedCt1ReceivedAt]; exact Entails.of_eq (by ac_rfl)

theorem v3cr_fsp_848_pair_to_128 (fsp w0 w1 : BitVec 64) :
    ((fsp + 848#64) ↦₆₄ w0) ∗ ((fsp + 856#64) ↦₆₄ w1) = ((fsp + 848#64) ↦₁₂₈ (w1 ++ w0)) := by
  have h := pointsTo64_pair_eq_pointsTo128 (fsp + 848#64) w0 w1
  have ha : (fsp + 848#64) + 8#64 = fsp + 856#64 := by bv_omega
  rwa [ha] at h

theorem v3cr_fsp_848_871_before_863_pair_eq (fsp w0 w1 u864 : BitVec 64) (Rest : SepProp) :
    ((fsp + 848#64) ↦₆₄ w0) ∗ ((fsp + 856#64) ↦₆₄ w1) ∗
      ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗ Rest =
    ((fsp + 848#64) ↦₆₄ w0) ∗ ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 w1) ∗
      ((fsp + 863#64) ↦₆₄ overlapWord7 w1 u864) ∗ Rest := by
  have h := v3a_fsp_848_871_before_863_eq fsp (w1 ++ w0) u864 Rest
  rwa [← v3cr_fsp_848_pair_to_128, sepConj_assoc ((fsp + 848#64) ↦₆₄ w0),
       extractLsb'_0_64_append, extractLsb'_64_64_append] at h

theorem v3cr_fsp_848_871_after_863_pair_eq (fsp w136 w144 w152 : BitVec 64) (Rest : SepProp) :
    ((fsp + 848#64) ↦₆₄ unshiftWord w136 (loByte w144)) ∗
      ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w144 (loByte w152))) ∗
      ((fsp + 863#64) ↦₆₄ w152) ∗ Rest =
    ((fsp + 848#64) ↦₆₄ unshiftWord w136 (loByte w144)) ∗
      ((fsp + 856#64) ↦₆₄ unshiftWord w144 (loByte w152)) ∗
      ((fsp + 864#64) ↦ₛ EncoderFromPb.hiBytes7 w152) ∗ Rest := by
  have h := v3a_fsp_848_871_after_863_eq fsp w136 w144 w152 Rest
  rwa [extractLsb'_0_64_append, extractLsb'_64_64_append,
       ← v3cr_fsp_848_pair_to_128, sepConj_assoc ((fsp + 848#64) ↦₆₄ _)] at h

theorem v3cr_fsp_880_895_after_887_rest_eq (fsp u880 w120 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880) ∗ ((fsp + 887#64) ↦₆₄ w120) ∗ Rest =
      ((fsp + 880#64) ↦₆₄ (loByte w120 ++ u880.extractLsb' 0 56)) ∗
      ((fsp + 888#64) ↦ₛ EncoderFromPb.hiBytes7 w120) ∗ Rest := by
  rw [← sepConj_assoc, v3a_fsp_880_895_after_887_eq, sepConj_assoc]; rfl

set_option maxHeartbeats 3200000 in
/-- Execution segment `+4984 -> +8180` (`0x5b41c -> 0x5c098`, 69 instructions):
unpacks the `PolyEncoder` from `fsp + 1888..2288` and the `unchunkedEkSentCt1ReceivedAt` words
from stack slots `fsp + 64, 96, 176, 184, 192, 200, 224` and registers `x20, x21, x22, x24, x26, x28`,
populating `epilogueStackSlots` for the shared epilogue at `+8180`. -/
theorem v3cr_pack_enc_4984_to_8180
    {b : BitVec 64} {ext : String → Option (State → State)} (s1 : State)
    (fsp out w_tag ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
     e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 e_w80 e_w88 e_w96
     e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152 : BitVec 64)
    (e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
     e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 : BitVec 128)
    (e_w384 e_w392 u160 u208 u232 : BitVec 64) (u172 : BitVec 32)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (u832 : BitVec 64) (q848 : BitVec 128) (u864 u880 u887 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4984#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx15_1 : s1.readReg64 .x15 = w_tag) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = la2) (hx21_1 : s1.readReg64 .x21 = pa4)
    (hx22_1 : s1.readReg64 .x22 = pa1) (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx24_1 : s1.readReg64 .x24 = la1) (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3) (hx28_1 : s1.readReg64 .x28 = ca2) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64) s1
      (((fsp + 64#64) ↦₆₄ uc_ep) ∗ ((fsp + 96#64) ↦₆₄ la3) ∗ ((fsp + 160#64) ↦₆₄ u160) ∗
        ((fsp + 172#64) ↦₃₂ u172) ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 192#64) ↦₆₄ la4) ∗ ((fsp + 200#64) ↦₆₄ ca1) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗
        ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 232#64) ↦₆₄ u232) ∗
        ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗ ((fsp + 640#64) ↦₁₂₈ q640) ∗
        ((fsp + 656#64) ↦₁₂₈ q656) ∗ ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
        ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗ ((fsp + 736#64) ↦₁₂₈ q736) ∗
        ((fsp + 752#64) ↦₁₂₈ q752) ∗ ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
        ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗ ((fsp + 832#64) ↦₆₄ u832) ∗
        ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ loBytes7 u864) ∗
        ((fsp + 880#64) ↦ₛ loBytes7 u880) ∗ ((fsp + 887#64) ↦₆₄ u887) ∗
        v3cr_polyEncoderWordsAt (fsp + 1888#64)
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 64#64) ↦₆₄ uc_ep) ∗ ((fsp + 96#64) ↦₆₄ la3) ∗ ((fsp + 160#64) ↦₆₄ la2) ∗
          ((fsp + 172#64) ↦₃₂ (loByte e_w136).zeroExtend 32) ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 192#64) ↦₆₄ la4) ∗ ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 208#64) ↦₆₄ e_w8) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 608#64) ↦₁₂₈ e_q160) ∗ ((fsp + 624#64) ↦₁₂₈ e_q176) ∗ ((fsp + 640#64) ↦₁₂₈ e_q192) ∗
          ((fsp + 656#64) ↦₁₂₈ e_q208) ∗ ((fsp + 672#64) ↦₁₂₈ e_q224) ∗ ((fsp + 688#64) ↦₁₂₈ e_q240) ∗
          ((fsp + 704#64) ↦₁₂₈ e_q256) ∗ ((fsp + 720#64) ↦₁₂₈ e_q272) ∗ ((fsp + 736#64) ↦₁₂₈ e_q288) ∗
          ((fsp + 752#64) ↦₁₂₈ e_q304) ∗ ((fsp + 768#64) ↦₁₂₈ e_q320) ∗ ((fsp + 784#64) ↦₁₂₈ e_q336) ∗
          ((fsp + 800#64) ↦₁₂₈ e_q352) ∗ ((fsp + 816#64) ↦₁₂₈ e_q368) ∗ ((fsp + 832#64) ↦₆₄ e_w384) ∗
          ((fsp + 848#64) ↦₆₄ unshiftWord e_w136 (loByte e_w144)) ∗
          ((fsp + 856#64) ↦₆₄ unshiftWord e_w144 (loByte e_w152)) ∗
          ((fsp + 864#64) ↦ₛ hiBytes7 e_w152) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord e_w112 (loByte e_w120)) ∗
          ((fsp + 888#64) ↦ₛ hiBytes7 e_w120) ∗
          v3cr_polyEncoderWordsAt (fsp + 1888#64)
            w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
            e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
            e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
            e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = e_w80 ∧ sm.readReg64 .x1 = la3 ∧
        sm.readReg64 .x2 = e_w392 ∧ sm.readReg32 .x3 = (e_w88.extractLsb' 0 8).zeroExtend 32 ∧
        sm.readReg64 .x4 = e_w96 ∧ sm.readReg64 .x5 = e_w104 ∧
        sm.readReg64 .x6 = fsp + 576#64 ∧ sm.readReg64 .x7 = e_w128 ∧
        sm.readReg64 .x8 = 5#64 ∧ sm.readReg64 .x9 = e_w48 ∧
        sm.readReg64 .x10 = pa2 ∧ sm.readReg64 .x11 = ca1 ∧
        sm.readReg64 .x12 = pa3 ∧ sm.readReg64 .x13 = e_w24 ∧
        sm.readReg64 .x14 = e_w56 ∧ sm.readReg64 .x15 = w_tag ∧
        sm.readReg64 .x16 = uc_ep ∧ sm.readReg64 .x17 = e_w72 ∧
        sm.readReg64 .x18 = e_w64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = e_w16 ∧ sm.readReg32 .x21 = (loByte e_w112).zeroExtend 32 ∧
        sm.readReg64 .x22 = pa1 ∧ sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = la1 ∧ sm.readReg64 .x25 = e_w32 ∧
        sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x27 = v3a_pack88 e_w88 ∧
        sm.readReg64 .x28 = pa4 ∧ sm.readReg64 .x30 = e_w40 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1
  states_from_pb_fetches_range b (Rust.withPanics ext) 4984 276
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, v3cr_polyEncoderWordsAt,
    v3a_tripleVecGF16WordsAt, v3cr_quadPairsWordsAt, v3cr_pairVecGF16WordsAt,
    BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre only [v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
    v3a_fsp_1976_realign_rest, v3a_fsp_2024_realign_rest, sepConj_assoc]
  iterate 3 wp_step
  wp_simp_pre only [v3a_fsp_2024_unrealign_rest, pointsTo128,
    v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  iterate 9 wp_step
  wp_simp_pre only [v3a_fsp_2000_realign_rest, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  iterate 12 wp_step
  wp_simp_pre only [v3cr_fsp_848_871_before_863_pair_eq, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  wp_step
  wp_simp_pre only [v3cr_fsp_848_871_after_863_pair_eq, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  iterate 12 wp_step
  wp_simp_pre only [v3cr_fsp_880_895_after_887_rest_eq, v3a_fsp_2000_unrealign_rest,
    v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  iterate 32 wp_step
  wp_simp_pre only [v3a_fsp_1976_unrealign_rest, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  have hz1 : ∀ w : BitVec 64, (loByte w).zeroExtend 32 = BitVec.setWidth 32 (BitVec.setWidth 8 w) := by
    intro w; unfold loByte; bv_kernel
  have hz2 : ∀ w : BitVec 64, (w.extractLsb' 0 8).zeroExtend 32 = BitVec.setWidth 32 (BitVec.setWidth 8 w) := by
    intro w; bv_kernel
  have hz3 : ∀ w : BitVec 64, (loByte w).zeroExtend 64 = BitVec.zeroExtend 64 (BitVec.setWidth 8 w) := by
    intro w; unfold loByte; bv_kernel
  have hp88 : BitVec.zeroExtend 64 (BitVec.extractLsb' 8 32 e_w88) |||
      BitVec.zeroExtend 64 (BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.extractLsb' 40 16 e_w88) |||
          BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (BitVec.extractLsb' 56 8 e_w88) <<< 16))) <<< 32 =
      v3a_pack88 e_w88 := by unfold v3a_pack88; bv_kernel
  simp only [pointsTo128, BitVec.extractLsb'_zero, hz1, hz2, hz3, hp88, v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  refine SepWP.done rfl hrun1 ⟨Entails.of_eq (by ac_rfl), ?_⟩
  dsimp only [TraceCalleeSaved, CalleeSavedPreserved]
  simp only [wp_norm, arm64_norm, *]

theorem v3cr_split_104_72 (fsp : BitVec 64) :
    memRegion (fsp + 104#64) 72 ⊢
      (∃∗ w104 : BitVec 64, ((fsp + 104#64) ↦₆₄ w104)) ∗ (∃∗ w112 : BitVec 64, ((fsp + 112#64) ↦₆₄ w112)) ∗
      (∃∗ w120 : BitVec 64, ((fsp + 120#64) ↦₆₄ w120)) ∗ memRegion (fsp + 128#64) 32 ∗
      (∃∗ u160 : BitVec 64, ((fsp + 160#64) ↦₆₄ u160)) ∗ memRegion (fsp + 168#64) 4 ∗
      (∃∗ u172 : BitVec 32, ((fsp + 172#64) ↦₃₂ u172)) := by
  exact split_top <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    mem32_entails _

theorem v3cr_split_208_16 (fsp : BitVec 64) :
    memRegion (fsp + 208#64) 16 ⊢
      (∃∗ u208 : BitVec 64, ((fsp + 208#64) ↦₆₄ u208)) ∗
      memRegion (fsp + 216#64) 8 := by
  exact split_top <| split_step (mem64_entails _) <| Entails.refl _

theorem v3cr_memRegion_328_entails_bs (a : BitVec 64) :
    memRegion a 328 ⊢ ∃∗ bs : List (BitVec 8), ⌜bs.length = 328⌝ ∗ (a ↦ₛ bs) := by
  refine Entails.trans (memRegion_328_entails_bs a) ?_
  apply Entails.sepExists_elim; intro ⟨bs, hbs⟩
  exact Entails.sepExists_right bs (Entails.pure_right hbs (Entails.refl _))

theorem v3cr_split_232_1656 (fsp : BitVec 64) :
    memRegion (fsp + 232#64) 1656 ⊢
      (∃∗ u232 : BitVec 64, ((fsp + 232#64) ↦₆₄ u232)) ∗
      (∃∗ bs240 : List (BitVec 8), ⌜bs240.length = 328⌝ ∗ ((fsp + 240#64) ↦ₛ bs240)) ∗
      memRegion (fsp + 568#64) 8 ∗
      (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗
      ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗
       memRegion (fsp + 599#64) 9) ∗
      memRegion (fsp + 608#64) 287 ∗
      memRegion (fsp + 895#64) 993 := by
  exact split_top <|
    split_step (mem64_entails _) <| split_step (v3cr_memRegion_328_entails_bs _) <|
    split_step (Entails.refl _) <| split_step (mem128_entails _) <|
    split_step (memRegion_loBytes7_gap_at fsp 592#64 599#64 8) <|
    split_step (Entails.refl _) <| Entails.refl _

theorem v3cr_collapse_0_64_72_24 (fsp uc_ep : BitVec 64) :
    memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ uc_ep) ∗ memRegion (fsp + 72#64) 24 ⊢
      memRegion fsp 92 ∗ (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92)) := by
  have h96 : memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ uc_ep) ∗ memRegion (fsp + 72#64) 24 ⊢
      memRegion fsp 96 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have hsplit : memRegion fsp 96 ⊢
      memRegion fsp 92 ∗ (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92)) :=
    split_top <| split_step0 (Entails.refl _) <| mem32_entails _
  exact Entails.trans h96 hsplit

theorem v3cr_post_4984_to_epilogue_stack
    (fsp la3 la2 pa3 pa2 la4 ca1 e_w8 ca4 ca2 : BitVec 64)
    (d92 : BitVec 32) (w104 w112 w120 : BitVec 64)
    (bs240 : List (BitVec 8)) (q576 : BitVec 128) (w592 : BitVec 64)
    (e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
     e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 : BitVec 128)
    (e_w384 e_w136 e_w144 e_w152 e_w112 e_w120 : BitVec 64)
    (w_tag e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 e_w80 e_w88 e_w96 e_w104 e_w128 e_w392 : BitVec 64) :
    ((fsp + 96#64) ↦₆₄ la3) ∗ ((fsp + 160#64) ↦₆₄ la2) ∗
    ((fsp + 172#64) ↦₃₂ (loByte e_w136).zeroExtend 32) ∗
    ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 192#64) ↦₆₄ la4) ∗
    ((fsp + 200#64) ↦₆₄ ca1) ∗ ((fsp + 208#64) ↦₆₄ e_w8) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗
    ((fsp + 232#64) ↦₆₄ ca2) ∗ ((fsp + 608#64) ↦₁₂₈ e_q160) ∗ ((fsp + 624#64) ↦₁₂₈ e_q176) ∗
    ((fsp + 640#64) ↦₁₂₈ e_q192) ∗ ((fsp + 656#64) ↦₁₂₈ e_q208) ∗ ((fsp + 672#64) ↦₁₂₈ e_q224) ∗
    ((fsp + 688#64) ↦₁₂₈ e_q240) ∗ ((fsp + 704#64) ↦₁₂₈ e_q256) ∗ ((fsp + 720#64) ↦₁₂₈ e_q272) ∗
    ((fsp + 736#64) ↦₁₂₈ e_q288) ∗ ((fsp + 752#64) ↦₁₂₈ e_q304) ∗ ((fsp + 768#64) ↦₁₂₈ e_q320) ∗
    ((fsp + 784#64) ↦₁₂₈ e_q336) ∗ ((fsp + 800#64) ↦₁₂₈ e_q352) ∗ ((fsp + 816#64) ↦₁₂₈ e_q368) ∗
    ((fsp + 832#64) ↦₆₄ e_w384) ∗
    ((fsp + 848#64) ↦₆₄ unshiftWord e_w136 (loByte e_w144)) ∗
    ((fsp + 856#64) ↦₆₄ unshiftWord e_w144 (loByte e_w152)) ∗
    ((fsp + 864#64) ↦ₛ hiBytes7 e_w152) ∗
    ((fsp + 880#64) ↦₆₄ unshiftWord e_w112 (loByte e_w120)) ∗
    ((fsp + 888#64) ↦ₛ hiBytes7 e_w120) ∗
    (v3cr_polyEncoderWordsAt (fsp + 1888#64)
      w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
      e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
      e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
      e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
     memRegion (fsp + 2288#64) 16) ∗
    memRegion fsp 92 ∗ ((fsp + 92#64) ↦₃₂ d92) ∗
    ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
    memRegion (fsp + 128#64) 32 ∗ memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 216#64) 8 ∗
    ((fsp + 240#64) ↦ₛ bs240) ∗ memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗
    ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion (fsp + 599#64) 9 ∗
    memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 993 ⊢
    epilogueStackSlots fsp
      d92 ((loByte e_w136).zeroExtend 32)
      w104 w112 w120 la2 la4 e_w8 ca4 ca2 bs240 q576 w592
      e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
      e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384
      (unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144))
      (e_w152 >>> 8) (unshiftWord e_w112 (loByte e_w120)) (e_w120 >>> 8)
      (e_w8 ++ w_tag) (e_w24 ++ e_w16) e_w32 ∗
    epilogueStackGaps fsp := by
  have h96 := Drop.pointsTo64_entails_memRegion (fsp + 96#64) la3
  have h176 : ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ⊢ memRegion (fsp + 176#64) 16 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Drop.pointsTo64_entails_memRegion _ _
  have h200 := Drop.pointsTo64_entails_memRegion (fsp + 200#64) ca1
  have h1888 := v3a_polyEncoderWordsAt_to_epilogue_1888 fsp
    w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
    e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
    e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
    e_w384 e_w392
  rw [← sepConj_assoc ((fsp + 848#64) ↦₆₄ _),
      v3cr_fsp_848_pair_to_128 fsp (unshiftWord e_w136 (loByte e_w144)) (unshiftWord e_w144 (loByte e_w152)),
      v3a_hiBytes7_eq_loBytes7_shr8 e_w152, v3a_hiBytes7_eq_loBytes7_shr8 e_w120]
  refine Entails.trans (Entails.of_eq (show _ =
    ((fsp + 96#64) ↦₆₄ la3) ∗ (((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2)) ∗
    ((fsp + 200#64) ↦₆₄ ca1) ∗
    (v3cr_polyEncoderWordsAt (fsp + 1888#64)
      w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
      e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
      e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
      e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
     memRegion (fsp + 2288#64) 16) ∗
    (((fsp + 160#64) ↦₆₄ la2) ∗ ((fsp + 172#64) ↦₃₂ (loByte e_w136).zeroExtend 32) ∗
     ((fsp + 192#64) ↦₆₄ la4) ∗ ((fsp + 208#64) ↦₆₄ e_w8) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗
     ((fsp + 232#64) ↦₆₄ ca2) ∗ ((fsp + 608#64) ↦₁₂₈ e_q160) ∗ ((fsp + 624#64) ↦₁₂₈ e_q176) ∗
     ((fsp + 640#64) ↦₁₂₈ e_q192) ∗ ((fsp + 656#64) ↦₁₂₈ e_q208) ∗ ((fsp + 672#64) ↦₁₂₈ e_q224) ∗
     ((fsp + 688#64) ↦₁₂₈ e_q240) ∗ ((fsp + 704#64) ↦₁₂₈ e_q256) ∗ ((fsp + 720#64) ↦₁₂₈ e_q272) ∗
     ((fsp + 736#64) ↦₁₂₈ e_q288) ∗ ((fsp + 752#64) ↦₁₂₈ e_q304) ∗ ((fsp + 768#64) ↦₁₂₈ e_q320) ∗
     ((fsp + 784#64) ↦₁₂₈ e_q336) ∗ ((fsp + 800#64) ↦₁₂₈ e_q352) ∗ ((fsp + 816#64) ↦₁₂₈ e_q368) ∗
     ((fsp + 832#64) ↦₆₄ e_w384) ∗
     ((fsp + 848#64) ↦₁₂₈ (unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144))) ∗
     ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (e_w152 >>> 8)) ∗
     ((fsp + 880#64) ↦₆₄ unshiftWord e_w112 (loByte e_w120)) ∗
     ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (e_w120 >>> 8)) ∗
     memRegion fsp 92 ∗ ((fsp + 92#64) ↦₃₂ d92) ∗
     ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
     memRegion (fsp + 128#64) 32 ∗ memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 216#64) 8 ∗
     ((fsp + 240#64) ↦ₛ bs240) ∗ memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗
     ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion (fsp + 599#64) 9 ∗
     memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 993) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono h96 (sepConj_mono h176 (sepConj_mono h200 (sepConj_mono_left h1888)))) ?_
  unfold epilogueStackSlots epilogueStackGaps
  exact Entails.of_eq (by ac_rfl)

theorem v3cr_epilogueOutFull_ct1Received_close
    (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (ucSt : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) (enc : PolyEncoder)
    (w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
     e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152 : BitVec 64)
    (e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 : BitVec 128)
    (e_w384 e_w392 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
     w512 w520 w528 : BitVec 64) (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    epilogueOutFull out
      5#64 w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 e_w80
      (((e_w88.extractLsb' 0 8).zeroExtend 32).setWidth 8)
      ((v3a_pack88 e_w88).setWidth 32)
      (((v3a_pack88 e_w88 >>> 32).setWidth 32).setWidth 16)
      (((v3a_pack88 e_w88 >>> 48).setWidth 32).setWidth 8)
      e_w96 e_w104
      (((loByte e_w112).zeroExtend 32).setWidth 8)
      (unshiftWord e_w112 (loByte e_w120))
      (overlapWord7 (unshiftWord e_w112 (loByte e_w120)) (e_w120 >>> 8))
      e_w128
      (((loByte e_w136).zeroExtend 32).setWidth 8)
      (unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144))
      (overlapWord7
        ((unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144)).extractLsb' 64 64)
        (e_w152 >>> 8))
      e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
      e_w384 e_w392 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
      w512 w520 w528 b536 q537 w552 bs240 q888 q904 w920 ∗
    v3cr_polyEncoderHeap A enc w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
      e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
      e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
    v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
      ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ⊢
    resultChunkedStatesAt A (F := F) out (.ok (.ct1Received { uc := ucSt, sending_ek := enc })) := by
  have henc := v3a_epilogueOutFull_polyEncoder_close A out enc 5#64
    w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
    e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
    e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
    e_w384 e_w392 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    w512 w520 w528 b536 q537 w552 bs240 q888 q904 w920
  have huc :
      (((out + 408#64) ↦₆₄ ca1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ la1) ∗
       ((out + 432#64) ↦₆₄ ca2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ la2) ∗
       ((out + 456#64) ↦₆₄ ca3) ∗ ((out + 464#64) ↦₆₄ pa3) ∗ ((out + 472#64) ↦₆₄ la3) ∗
       ((out + 480#64) ↦₆₄ ca4) ∗ ((out + 488#64) ↦₆₄ pa4) ∗ ((out + 496#64) ↦₆₄ la4) ∗ ((out + 504#64) ↦₆₄ uc_ep)) ∗
      v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ⊢
      unchunkedEkSentCt1ReceivedAt A (F := F) (out + 408#64) ucSt := by
    have h0 := v3cr_unchunkedEkSentCt1ReceivedAt_close A (F := F) (out + 408#64) ucSt
      ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    dsimp only [v1_ucWordsAt] at h0; simpa only [arm64_norm] using h0
  have htail := epilogueOut_tail_512_entails_416 out w512 w520 w528 b536 q537 w552 bs240 hbs240 q888 q904 w920
  rw [← sepConj_assoc]
  refine Entails.trans (sepConj_mono_left henc) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 5#64) ∗ polyEncoderAt A (out + 8#64) enc ∗
    ((((out + 408#64) ↦₆₄ ca1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ la1) ∗
      ((out + 432#64) ↦₆₄ ca2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ la2) ∗
      ((out + 456#64) ↦₆₄ ca3) ∗ ((out + 464#64) ↦₆₄ pa3) ∗ ((out + 472#64) ↦₆₄ la3) ∗
      ((out + 480#64) ↦₆₄ ca4) ∗ ((out + 488#64) ↦₆₄ pa4) ∗ ((out + 496#64) ↦₆₄ la4) ∗ ((out + 504#64) ↦₆₄ uc_ep)) ∗
     v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep) ∗
    (((out + 512#64) ↦₆₄ w512) ∗ ((out + 520#64) ↦₆₄ w520) ∗ ((out + 528#64) ↦₆₄ w528) ∗
     (((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗ ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗
      ((out + 560#64) ↦ₛ bs240) ∗ ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920))) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono huc htail))) ?_
  exact v3cr_chunkedCt1ReceivedAt_close A (F := F) out ucSt enc

/-! ## Top-Level Variant 3 (`Ct1Received`, `+692`) Composition -/

def v3cr_optProtoUcHeap (A : RustAlloc) (optUc : Option V1State.Unchunked.EkSentCt1Received)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) : SepProp :=
  match optUc with
  | none => ⌜u8 = noneCap⌝
  | some pb =>
    ⌜pb.dk.length < 2 ^ 63 ∧ u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 pb.dk.length ∧
      pb.ct1.length < 2 ^ 63 ∧ u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 pb.ct1.length ∧ u104 = pb.epoch⌝ ∗
    vecU8Payload A u8 u16 pb.dk ∗ vecU8Payload A u32 u40 pb.ct1 ∗
    v1_optProtoAuthHeap A pb.auth u56 u64 u72 u80 u88 u96

theorem v3cr_optProtoUc_unpack (A : RustAlloc) (a : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSentCt1Received) :
    optProtoUnchunkedEkSentCt1ReceivedAt A a optUc ⊢
      ∃∗ u8 : BitVec 64, ∃∗ u16 : BitVec 64, ∃∗ u24 : BitVec 64, ∃∗ u32 : BitVec 64,
      ∃∗ u40 : BitVec 64, ∃∗ u48 : BitVec 64, ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64,
      ∃∗ u72 : BitVec 64, ∃∗ u80 : BitVec 64, ∃∗ u88 : BitVec 64, ∃∗ u96 : BitVec 64,
      ∃∗ u104 : BitVec 64,
        v1_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v3cr_optProtoUcHeap A optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 := by
  cases optUc with
  | none =>
    dsimp only [optProtoUnchunkedEkSentCt1ReceivedAt, v3cr_optProtoUcHeap, v1_ucWordsAt]
    refine Entails.trans (sepConj_mono_right (v3cr_split_96_words a)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u104; apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u88; apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u72; apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u56; apply Entails.sepExists_elim; intro u48
    apply Entails.sepExists_elim; intro u40; apply Entails.sepExists_elim; intro u32
    apply Entails.sepExists_elim; intro u24; apply Entails.sepExists_elim; intro u16
    refine Entails.sepExists_right noneCap (Entails.sepExists_right u16 (Entails.sepExists_right u24
      (Entails.sepExists_right u32 (Entails.sepExists_right u40 (Entails.sepExists_right u48
        (Entails.sepExists_right u56 (Entails.sepExists_right u64 (Entails.sepExists_right u72
          (Entails.sepExists_right u80 (Entails.sepExists_right u88 (Entails.sepExists_right u96
            (Entails.sepExists_right u104 ?_))))))))))))
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some pb =>
    dsimp only [optProtoUnchunkedEkSentCt1ReceivedAt, protoUnchunkedEkSentCt1ReceivedAt,
      v3cr_optProtoUcHeap, v1_ucWordsAt]
    refine Entails.trans (sepConj_mono (vecU8_unpack A a pb.dk)
      (sepConj_mono (vecU8_unpack A (a + 24#64) pb.ct1)
        (sepConj_mono (v3cr_optProtoAuth_unpack A (a + 48#64) pb.auth) (Entails.refl _)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u56; apply Entails.sepExists_elim; intro u64; apply Entails.sepExists_elim; intro u72
    apply Entails.sepExists_elim; intro u80; apply Entails.sepExists_elim; intro u88; apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u32; apply Entails.sepExists_elim; intro u40; apply Entails.sepExists_elim; intro u8
    apply Entails.sepExists_elim; intro u16
    simp only [v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜pb.dk.length < 2 ^ 63 ∧ u8.toNat < 2 ^ 63⌝ ∗ ⌜pb.ct1.length < 2 ^ 63 ∧ u32.toNat < 2 ^ 63⌝ ∗
      ((a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
       ((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
       ((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ u72) ∗
       ((a + 72#64) ↦₆₄ u80) ∗ ((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96) ∗ ((a + 96#64) ↦₆₄ pb.epoch) ∗
       vecU8Payload A u8 u16 pb.dk ∗ vecU8Payload A u32 u40 pb.ct1 ∗
       v1_optProtoAuthHeap A pb.auth u56 u64 u72 u80 u88 u96) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨hdk_len, hu8⟩; apply Entails.pure_left; rintro ⟨hct1_len, hu32⟩
    refine Entails.sepExists_right u8 (Entails.sepExists_right u16
      (Entails.sepExists_right (BitVec.ofNat 64 pb.dk.length) (Entails.sepExists_right u32
        (Entails.sepExists_right u40 (Entails.sepExists_right (BitVec.ofNat 64 pb.ct1.length)
          (Entails.sepExists_right u56 (Entails.sepExists_right u64 (Entails.sepExists_right u72
            (Entails.sepExists_right u80 (Entails.sepExists_right u88 (Entails.sepExists_right u96
              (Entails.sepExists_right pb.epoch ?_))))))))))))
    have hp : pb.dk.length < 2 ^ 63 ∧ u8.toNat < 2 ^ 63 ∧
        BitVec.ofNat 64 pb.dk.length = BitVec.ofNat 64 pb.dk.length ∧
        pb.ct1.length < 2 ^ 63 ∧ u32.toNat < 2 ^ 63 ∧
        BitVec.ofNat 64 pb.ct1.length = BitVec.ofNat 64 pb.ct1.length ∧
        pb.epoch = pb.epoch := ⟨hdk_len, hu8, rfl, hct1_len, hu32, rfl, rfl⟩
    exact Entails.trans (Entails.pure_right hp (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v3cr_protoUc_pack (A : RustAlloc) (a : BitVec 64)
    (pb : V1State.Unchunked.EkSentCt1Received)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) :
    v1_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
      v3cr_optProtoUcHeap A (some pb) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ⊢
      protoUnchunkedEkSentCt1ReceivedAt A a pb := by
  dsimp only [protoUnchunkedEkSentCt1ReceivedAt, v3cr_optProtoUcHeap, v1_ucWordsAt]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜pb.dk.length < 2 ^ 63 ∧ u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 pb.dk.length ∧
      pb.ct1.length < 2 ^ 63 ∧ u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 pb.ct1.length ∧ u104 = pb.epoch⌝ ∗
    (((a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ u24) ∗ vecU8Payload A u8 u16 pb.dk) ∗
     (((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ u48) ∗ vecU8Payload A u32 u40 pb.ct1) ∗
     ((((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ u72) ∗
       ((a + 72#64) ↦₆₄ u80) ∗ ((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96)) ∗
      v1_optProtoAuthHeap A pb.auth u56 u64 u72 u80 u88 u96) ∗ ((a + 96#64) ↦₆₄ u104)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨_, _, rfl, _, _, rfl, rfl⟩
  have hdk := vecU8_of_header_payload A a u8 u16 pb.dk
  have hct1 := vecU8_of_header_payload A (a + 24#64) u32 u40 pb.ct1
  have hauth := v3cr_optProtoAuth_pack A (a + 48#64) pb.auth u56 u64 u72 u80 u88 u96
  simp only [v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hct1 hauth
  exact sepConj_mono hdk (sepConj_mono hct1 (sepConj_mono hauth (Entails.refl _)))

theorem v3cr_chunkedCt1ReceivedAt_unpack (A : RustAlloc) (pbA : BitVec 64)
    (pbSt : V1State.Chunked.Ct1Received) :
    protoChunkedCt1ReceivedAt A (pbA + 8#64) pbSt ⊢
      ∃∗ u8 : BitVec 64, ∃∗ u16 : BitVec 64, ∃∗ u24 : BitVec 64, ∃∗ u32 : BitVec 64,
      ∃∗ u40 : BitVec 64, ∃∗ u48 : BitVec 64, ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64,
      ∃∗ u72 : BitVec 64, ∃∗ u80 : BitVec 64, ∃∗ u88 : BitVec 64, ∃∗ u96 : BitVec 64,
      ∃∗ u104 : BitVec 64, ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64,
        v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48 ∗
        v3cr_optProtoUcHeap A pbSt.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderHeap A (pbSt.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 := by
  dsimp only [protoChunkedCt1ReceivedAt]
  have h112 : pbA + 8#64 + 104#64 = pbA + 112#64 := by bv_omega
  rw [h112]
  refine Entails.trans (sepConj_mono (v3cr_optProtoUc_unpack A (pbA + 8#64) pbSt.uc)
    (v1_optProtoPolyEncoderAt_unpack A (pbA + 112#64) (pbSt.sendingEk.map pbToProtoPolyEncoder))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w8; apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w24; apply Entails.sepExists_elim; intro w32; apply Entails.sepExists_elim; intro w40
  apply Entails.sepExists_elim; intro w48; apply Entails.sepExists_elim; intro u8; apply Entails.sepExists_elim; intro u16
  apply Entails.sepExists_elim; intro u24; apply Entails.sepExists_elim; intro u32; apply Entails.sepExists_elim; intro u40
  apply Entails.sepExists_elim; intro u48; apply Entails.sepExists_elim; intro u56; apply Entails.sepExists_elim; intro u64
  apply Entails.sepExists_elim; intro u72; apply Entails.sepExists_elim; intro u80; apply Entails.sepExists_elim; intro u88
  apply Entails.sepExists_elim; intro u96; apply Entails.sepExists_elim; intro u104
  refine Entails.sepExists_right u8 (Entails.sepExists_right u16 (Entails.sepExists_right u24
    (Entails.sepExists_right u32 (Entails.sepExists_right u40 (Entails.sepExists_right u48
      (Entails.sepExists_right u56 (Entails.sepExists_right u64 (Entails.sepExists_right u72
        (Entails.sepExists_right u80 (Entails.sepExists_right u88 (Entails.sepExists_right u96
          (Entails.sepExists_right u104 (Entails.sepExists_right w0 (Entails.sepExists_right w8
            (Entails.sepExists_right w16 (Entails.sepExists_right w24 (Entails.sepExists_right w32
              (Entails.sepExists_right w40 (Entails.sepExists_right w48 ?_)))))))))))))))))))
  rw [← v1_uc_and_enc_words_eq_pb128]
  exact Entails.of_eq (by ac_rfl)

theorem v3_collapse_1888_400 (fsp ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64) :
    v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      memRegion (fsp + 1992#64) 296 ⊢
      memRegion (fsp + 1888#64) polyEncoderSize := by
  dsimp only [polyEncoderSize]
  have h104 := v1_ucWordsAt_entails_104 (fsp + 1888#64)
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
  rw [ProofLib.memRegion_split' (b := fsp + 1888#64) (n := 104) (k := 296)
    (b' := fsp + 1992#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left h104

theorem v3_collapse_fsp_296_1592 (fsp w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    memRegion (fsp + 296#64) 1096 ∗
      memRegion (fsp + 1392#64) 104 ∗
      v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (fsp + 1552#64) 336 ⊢
      memRegion (fsp + 296#64) 1592 := by
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48
  rw [ProofLib.memRegion_split' (b := fsp + 296#64) (n := 1096) (k := 496)
        (b' := fsp + 1392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1392#64) (n := 104) (k := 392)
        (b' := fsp + 1496#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1496#64) (n := 56) (k := 336)
        (b' := fsp + 1552#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h56))

theorem v3_collapse_fsp_232_1656 (fsp : BitVec 64) :
    memRegion (fsp + 232#64) 8 ∗
      memRegion (fsp + 240#64) protoPolynomialEncoderSize ∗
      memRegion (fsp + 296#64) 1592 ⊢
      memRegion (fsp + 232#64) 1656 := by
  dsimp only [protoPolynomialEncoderSize]
  rw [ProofLib.memRegion_split' (b := fsp + 232#64) (n := 8) (k := 1648)
        (b' := fsp + 240#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 240#64) (n := 56) (k := 1592)
        (b' := fsp + 296#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem v3_collapse_pbA_112_224 (pbA w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    memRegion pbA 112 ∗
      v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (pbA + 168#64) 56 ⊢
      memRegion pbA optProtoInnerStateSize := by
  dsimp only [optProtoInnerStateSize]
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48
  rw [ProofLib.memRegion_split pbA 112 112 (by decide),
      ProofLib.memRegion_split' (b := pbA + 112#64) (n := 56) (k := 56)
        (b' := pbA + 168#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_left h56)

theorem v3_encoderFromPbOnPanic_entails (s0 s sf : State) (F : SepProp)
    (htr : TraceCalleeSaved s s0) :
    encoderFromPbOnPanic s sf ∗ F ⊢ statesFromPbOnPanic s0 sf := by
  unfold encoderFromPbOnPanic statesFromPbOnPanic allocFailedIn
  rw [htr.1, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

end CryptoVerification.SpqrV1.States.FromPb

