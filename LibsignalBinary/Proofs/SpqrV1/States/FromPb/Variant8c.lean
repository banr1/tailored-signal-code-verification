/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8a
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8b
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 8 (`EkReceivedCt1Sampled`, `+1764`) — Part C

Length/auth validation (`+1872 -> +1972 -> +10544 | +1984`), `Authenticator` key-buffer cloning and
input buffer cleanup (`+1984 -> +10680 -> +10740 -> +10836`), and the `sendingCt1 = none` 5-vector
cleanup path (`+10836 -> +11120 -> +4240`).
-/

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
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
open CryptoVerification.Swarm.IC10.Variant10a

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

/-! ## 1. `+1872 -> +1972 -> +10544 | +1984` and Length/Auth Error Theorems -/

/-- Combined step `+1872 -> +1972` when `u24 = 2080#64 ∧ u72 = 960#64 ∧ u48 = 1152#64`. -/
theorem v8_step_1872_to_1972_len_ok
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1972#64) s1
      (memRegion (s0.sp - 2400#64) 1392 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
        v8_ucWordsAt (pbA + 8#64)
          u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (s0.sp - 2400#64) 896 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v8_ucWordsAt (pbA + 8#64)
            u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre
    (sepConj_mono_left (v8_memRegion_1392_split_896_128_368 (s0.sp - 2400#64))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro z1016
  apply ProofLib.SepWP.exists_left; intro z1008
  apply ProofLib.SepWP.exists_left; intro z1000
  apply ProofLib.SepWP.exists_left; intro z992
  apply ProofLib.SepWP.exists_left; intro z984
  apply ProofLib.SepWP.exists_left; intro z976
  apply ProofLib.SepWP.exists_left; intro z968
  apply ProofLib.SepWP.exists_left; intro z960
  apply ProofLib.SepWP.exists_left; intro z952
  apply ProofLib.SepWP.exists_left; intro z944
  apply ProofLib.SepWP.exists_left; intro z936
  apply ProofLib.SepWP.exists_left; intro z928
  apply ProofLib.SepWP.exists_left; intro z920
  apply ProofLib.SepWP.exists_left; intro z912
  apply ProofLib.SepWP.exists_left; intro z904
  apply ProofLib.SepWP.exists_left; intro z896
  have hcopy := v8_copy_uc_1872_to_1936 s0 s1 out pbA
    u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128
    z896 z904 z912 z920 z960 z968 z976 z984 z992 z1000 z1008 z1016
    (memRegion (s0.sp - 2400#64) 896 ∗
      ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
      ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
      ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
      ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
      memRegion (s0.sp - 2400#64 + 1024#64) 368 ∗
      ((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
      ((s0.sp - 2400#64 + 1392#64 + 16#64) ↦₆₄ 2080#64) ∗
      ((s0.sp - 2400#64 + 1392#64 + 24#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 1392#64 + 32#64) ↦₆₄ u40) ∗
      ((s0.sp - 2400#64 + 1392#64 + 40#64) ↦₆₄ 1152#64) ∗
      ((s0.sp - 2400#64 + 1392#64 + 48#64) ↦₆₄ u56) ∗
      ((s0.sp - 2400#64 + 1392#64 + 56#64) ↦₆₄ u64) ∗
      ((s0.sp - 2400#64 + 1392#64 + 64#64) ↦₆₄ 960#64) ∗
      ((s0.sp - 2400#64 + 1392#64 + 72#64) ↦₆₄ u80) ∗
      ((s0.sp - 2400#64 + 1392#64 + 80#64) ↦₆₄ u88) ∗
      ((s0.sp - 2400#64 + 1392#64 + 88#64) ↦₆₄ u96) ∗
      ((s0.sp - 2400#64 + 1392#64 + 96#64) ↦₆₄ u104) ∗
      ((s0.sp - 2400#64 + 1392#64 + 104#64) ↦₆₄ u112) ∗
      ((s0.sp - 2400#64 + 1392#64 + 112#64) ↦₆₄ u120) ∗
      ((s0.sp - 2400#64 + 1392#64 + 120#64) ↦₆₄ u128) ∗
      Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hx27_1 htr1
  have h1400 : (s0.sp - 2400#64 + 1392#64) + 8#64 = s0.sp - 2400#64 + 1400#64 := by bv_omega
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1936#64)
    (P_mid :=
      ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
      ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗
      ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
      ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
      ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
      ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
      ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗
      ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
      ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
      ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
      ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
      ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
      ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
      ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
      (memRegion (s0.sp - 2400#64) 896 ∗
       memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
       v8_ucWordsAt (pbA + 8#64)
         u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
       Rest))
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x9 = 2080#64 ∧
      s2.readVReg128 0#5 = 1152#64 ++ u40 ∧
      s2.readVReg128 1#5 = u64 ++ u56 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x26 = u8 ∧
      s2.readReg64 .x27 = pbA ∧
      TraceCalleeSaved s2 s0)
    (SepWP.weaken_pre
      (by
        dsimp only [v8_ucWordsAt]
        rw [h1400]
        exact Entails.of_eq (by ac_rfl))
      (SepWP.mono hcopy fun s2 P2 _ _ ⟨hP2, hsp2, hx9_2, hq0_2, hq1_2, hx19_2, hx26_2, hx27_2, htr2⟩ => ?_)) ?_
  · refine ⟨Entails.trans hP2 ?_, hsp2, hx9_2, hq0_2, hq1_2, hx19_2, hx26_2, hx27_2, htr2⟩
    have hm496 := v8_merge_368_ucWords_496 (s0.sp - 2400#64)
      u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128
    dsimp only [v8_ucWordsAt] at hm496 ⊢
    rw [h1400] at hm496
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64 + 1024#64) 368 ∗
       (((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 1392#64 + 16#64) ↦₆₄ 2080#64) ∗
        ((s0.sp - 2400#64 + 1392#64 + 24#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 1392#64 + 32#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 1392#64 + 40#64) ↦₆₄ 1152#64) ∗
        ((s0.sp - 2400#64 + 1392#64 + 48#64) ↦₆₄ u56) ∗
        ((s0.sp - 2400#64 + 1392#64 + 56#64) ↦₆₄ u64) ∗
        ((s0.sp - 2400#64 + 1392#64 + 64#64) ↦₆₄ 960#64) ∗
        ((s0.sp - 2400#64 + 1392#64 + 72#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 1392#64 + 80#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 1392#64 + 88#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 1392#64 + 96#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 1392#64 + 104#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1392#64 + 112#64) ↦₆₄ u120) ∗
        ((s0.sp - 2400#64 + 1392#64 + 120#64) ↦₆₄ u128))) ∗
      (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
       ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗
       ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
       ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
       ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
       ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
       ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
       ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗
       ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
       ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
       ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
       ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
       ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
       ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
       ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
       memRegion (s0.sp - 2400#64) 896 ∗
       ((pbA + 8#64) ↦₆₄ u8) ∗
       ((pbA + 8#64 + 8#64) ↦₆₄ u16) ∗
       ((pbA + 8#64 + 16#64) ↦₆₄ 2080#64) ∗
       ((pbA + 8#64 + 24#64) ↦₆₄ u32) ∗
       ((pbA + 8#64 + 32#64) ↦₆₄ u40) ∗
       ((pbA + 8#64 + 40#64) ↦₆₄ 1152#64) ∗
       ((pbA + 8#64 + 48#64) ↦₆₄ u56) ∗
       ((pbA + 8#64 + 56#64) ↦₆₄ u64) ∗
       ((pbA + 8#64 + 64#64) ↦₆₄ 960#64) ∗
       ((pbA + 8#64 + 72#64) ↦₆₄ u80) ∗
       ((pbA + 8#64 + 80#64) ↦₆₄ u88) ∗
       ((pbA + 8#64 + 88#64) ↦₆₄ u96) ∗
       ((pbA + 8#64 + 96#64) ↦₆₄ u104) ∗
       ((pbA + 8#64 + 104#64) ↦₆₄ u112) ∗
       ((pbA + 8#64 + 112#64) ↦₆₄ u120) ∗
       ((pbA + 8#64 + 120#64) ↦₆₄ u128) ∗
       Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hm496) (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hq0_2, hq1_2, hx19_2, hx26_2, hx27_2, htr2⟩
    have hchk := v8_check_lengths_1936_ok s0 s2 out pbA
      u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u128
      z928 z936 z944 z952
      (memRegion (s0.sp - 2400#64) 896 ∗
       memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
       v8_ucWordsAt (pbA + 8#64)
         u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
       Rest)
      hsp0_align hpc2 hrun2 hsp2 hx9_2 hq0_2 hq1_2 hx19_2 hx27_2 htr2
    refine SepWP.mono hchk fun sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx26_f, hx27_f, htr_f⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f,
       hx19_f, Eq.trans hx26_f hx26_2, hx27_f, htr_f⟩

/-- At `+1972` (`0x5a858`), when `u80 = noneCap` (`u.auth = none`),
branches to `+10544` (`0x5c9d4`). -/
theorem v8_check_auth_1972_none
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1972#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10544#64) s1
      (v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u128 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  states_from_pb_fetches_range b (Rust.withPanics ext) 1972 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre [v8_ucWordsAt, sepConj_assoc]
  wp_steps
  simp only [v8_ucWordsAt, sepConj_assoc]
  wp_done

/-- At `+1972` (`0x5a858`), when `u80.toNat < 2 ^ 63` (`u.auth = some authPb`),
falls through to `+1984` (`0x5a864`) with `x23 = u80`. -/
theorem v8_check_auth_1972_some
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (hu80_lt : u80.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1972#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1984#64) s1
      (v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = u80 ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hu80_ne : (u80 + 1#64 == 0#64) = false := v10_cap_add_one_beq_zero_false hu80_lt
  states_from_pb_fetches_range b (Rust.withPanics ext) 1972 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre [v8_ucWordsAt, sepConj_assoc]
  wp_steps
  simp only [v8_ucWordsAt, sepConj_assoc]
  wp_done

/-! ## 2. `Authenticator::from_pb` Cloning (`+1984 -> +10680 -> +10740 -> +10836`) -/

/-- Cold OOM panic block at `+11632` (`0x5ce14`): `mov w0, #1; mov x1, x22; bl +13728` (`+(num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))`). -/
theorem v8_oom_11632_entails
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (target_pc : BitVec 64) (P : SepProp)
    (Q : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11632#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s P Q
      (fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf) := by
  have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error")))
    (by rw [hfn, stubOff_handle_error])
  states_from_pb_fetches_range b (Rust.withPanics ext) 11632 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpanic hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error")))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
  unfold statesFromPbOnPanic
  exact Entails.pure_right
    (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *]))
    (entails_anyHeap _)

private theorem v8_clone_rootKey_1984_to_10680_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : V10Alloc b A ext)
    (s0 s1 : State) (out pbA u8 u80 u88 u128 v120 v200 : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1984#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = u80)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10680#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 120#64) ↦₆₄ v120) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗ (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
        (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗ vecU8Payload A u80 u88 rootKey ∗ A.pool ∗ Rest)
      (fun sm Pm => ∃ p1_new : BitVec 64,
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 120#64) ↦₆₄ u128) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1_new) ∗
          (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗ (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
          (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗ vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
          vecCapPtrDealloc A u80 u88 ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 rootKey.length ∧ sm.readReg64 .x23 = u80 ∧
        sm.readReg64 .x24 = u88 ∧ sm.readReg64 .x26 = u8 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have h120 : (s0.sp - 2400#64) + 120#64 = s0.sp - 2280#64 := by bv_omega
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  have h976 : (s0.sp - 2400#64) + 976#64 = s0.sp - 1424#64 := by bv_omega
  have h984 : (s0.sp - 2400#64) + 984#64 = s0.sp - 1416#64 := by bv_omega
  have h1016 : (s0.sp - 2400#64) + 1016#64 = s0.sp - 1384#64 := by bv_omega
  have hpure :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 120#64) ↦₆₄ v120) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗ (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
        (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗ vecU8Payload A u80 u88 rootKey ∗ A.pool ∗ Rest =
      ⌜rootKey.length ≤ u80.toNat ∧ u80.toNat < 2 ^ 63 ∧ u88 ≠ 0#64⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ v120) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
       (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗ (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
       (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗
       (if u80 = 0#64 then emp
        else A.live u88 u80.toNat 1 ∗ (u88 ↦ₛ rootKey) ∗
          memRegion (u88 + BitVec.ofNat 64 rootKey.length) (u80.toNat - rootKey.length)) ∗
       A.pool ∗ Rest) := by unfold vecU8Payload; ac_rfl
  rw [hpure]
  refine SepWPp.pure_left fun ⟨hr_le, hr_cap, _⟩ => ?_
  have hr_cases : rootKey = [] ∨ 0 < rootKey.length := by cases rootKey <;> simp
  rcases hr_cases with rfl | hr_pos
  · simp only [List.length_nil, BitVec.ofNat_eq_ofNat]
    refine v10_sepWPp_seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10672#64)
      (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 120#64) ↦₆₄ u128) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗ (((s0.sp - 2400#64) + 984#64) ↦₆₄ 0#64) ∗
        (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗ vecCapPtrDealloc A u80 u88 ∗ A.pool ∗ Rest)
      (Q_regs := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = 0#64 ∧
        sm.readReg64 .x23 = u80 ∧ sm.readReg64 .x24 = u88 ∧ sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 1984 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h120, h200, h976, h984, h1016]
        have hite := v10_ite_nil_entails_vecCapPtrDealloc A u80 u88
        refine Entails.trans (Entails.of_eq (show _ =
          (if u80 = 0#64 then emp else A.live u88 u80.toNat 1 ∗ (u88 ↦ₛ ([] : List (BitVec 8))) ∗
            memRegion (u88 + 0#64) (u80.toNat - 0)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2280#64) ↦₆₄ u128) ∗
           ((s0.sp - 2200#64) ↦₆₄ v200) ∗ ((s0.sp - 1424#64) ↦₆₄ u88) ∗
           ((s0.sp - 1416#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1384#64) ↦₆₄ u128) ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hite) (Entails.of_eq (by ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, htr2⟩
      apply SepWPp.of_sepWP_ret; refine v10_sepWP_exists_post 1#64 ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 10672 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h120, h200, h976, h984, h1016]
        have hv0 := vecU8Payload_zero A
        refine Entails.trans (Entails.of_eq (show _ =
          emp ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2280#64) ↦₆₄ u128) ∗
           ((s0.sp - 2200#64) ↦₆₄ 1#64) ∗ ((s0.sp - 1424#64) ↦₆₄ u88) ∗
           ((s0.sp - 1416#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1384#64) ↦₆₄ u128) ∗
           vecCapPtrDealloc A u80 u88 ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hv0) (Entails.of_eq (by ac_rfl))
      · wp_done
  · have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hc1_ne : u80 ≠ 0#64 := cap_ne_zero_of_pos hr_pos hr_le
    have hr_lt63 : rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : rootKey.length < 2 ^ 64 := by omega
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false := ofNat_beq_zero_false hr_pos hr_lt64
    have hr_toNat : (BitVec.ofNat 64 rootKey.length).toNat = rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hlay : LayoutOk rootKey.length 1 := ⟨hr_pos, hpow1, by omega⟩
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hshim := hA.shim_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    have halloc := hA.alloc_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc"))
    have hmc := hA.session_memcpy_region_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy"))
    have hoom_step := @v8_oom_11632_entails b ext s0
    simp only [hc1_ne, ↓reduceIte, sepConj_assoc]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    states_from_pb_fetches_range b (Rust.withPanics ext) 1984 60
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
      at hshim halloc hmc hoom_step hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + 2020#64)
    wp_steps; wp_apply; wp_steps; nth_rw 1 [← hsp1]; nth_rw 1 [← h_1]; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte]; rw [v10_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      have htr_sf1 : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htrace]; simp only [wp_norm, arm64_norm, *]
      refine v10_sepWPp_seq_clean (mid := entry + 11632#64)
        (P_mid := A.pool ∗ stackAt sf.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056 ∗
          ((s0.sp - 2280#64) ↦₆₄ u128) ∗ ((s0.sp - 2200#64) ↦₆₄ v200) ∗
          ((s0.sp - 1424#64) ↦₆₄ u88) ∗ ((s0.sp - 1416#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
          ((s0.sp - 1384#64) ↦₆₄ u128) ∗ A.live u88 u80.toNat 1 ∗ (u88 ↦ₛ rootKey) ∗
          memRegion (u88 + BitVec.ofNat 64 rootKey.length) (u80.toNat - rootKey.length) ∗ Rest)
        (Q_regs := fun sm => sm.trace = s0.trace ++ [allocFailedEvent]) ?_ ?_
      · wp_steps; wp_done
      · intro s3 hpc3 hrun3 htr3; exact hoom_step s3 _ _ _ hpc3 hrun3 htr3
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
      rw [v10_pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      have hsp_sf1 : sf_1.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret; refine v10_sepWP_exists_post (sf_1.readReg64 (Reg.gpr 0#5)) ?_
      wp_steps
      have hsp_eq_sf : sf_1.sp = sf.sp := by simp only [wp_norm, arm64_norm, *]
      wp_simp_pre [← hsp_eq_sf]; wp_apply; wp_simp_pre [hsp_eq_sf]; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h120, h200, h976, h984, h1016]
        have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp_sf1] at hst; rw [hsp_sf] at hst
        have hv_new := vecU8Payload_pos A (sf_1.readReg64 (Reg.gpr 0#5)) rootKey hr_pos hr_lt63 hoom
        have hv_old := v10_live_bytes_entails_vecCapPtrDealloc A u80 u88 rootKey hc1_ne hr_le
        refine Entails.trans (Entails.of_eq (show _ =
          (stackAt sf.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          (A.live (sf_1.readReg64 (Reg.gpr 0#5)) rootKey.length 1 ∗ (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ rootKey)) ∗
          (A.live u88 u80.toNat 1 ∗ (u88 ↦ₛ rootKey) ∗
            memRegion (u88 + BitVec.ofNat 64 rootKey.length) (u80.toNat - rootKey.length)) ∗
          (((s0.sp - 2280#64) ↦₆₄ u128) ∗ ((s0.sp - 2200#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
           ((s0.sp - 1424#64) ↦₆₄ u88) ∗ ((s0.sp - 1416#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
           ((s0.sp - 1384#64) ↦₆₄ u128) ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hst (sepConj_mono hv_new (sepConj_mono_left hv_old)))
          (Entails.of_eq (by ac_rfl))
      · wp_done

private theorem v8_clone_macKey_10680_to_10740_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : V10Alloc b A ext)
    (s0 s1 : State) (out pbA u8 l1 u80 u88 u104 u112 v184 : BitVec 64)
    (macKey : List (BitVec 8)) (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10680#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = u80) (hx24_1 : s1.readReg64 .x24 = u88)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10740#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
        (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
        vecU8Payload A u104 u112 macKey ∗ A.pool ∗ Rest)
      (fun sm Pm => ∃ p2_new : BitVec 64,
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
          (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
          vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
          vecCapPtrDealloc A u104 u112 ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = u112 ∧
        sm.readReg64 .x22 = l1 ∧ sm.readReg64 .x23 = u80 ∧ sm.readReg64 .x24 = u88 ∧
        sm.readReg64 .x26 = u8 ∧ sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = BitVec.ofNat 64 macKey.length ∧ TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
  have h1000 : (s0.sp - 2400#64) + 1000#64 = s0.sp - 1400#64 := by bv_omega
  have h1008 : (s0.sp - 2400#64) + 1008#64 = s0.sp - 1392#64 := by bv_omega
  have hpure :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
        (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
        vecU8Payload A u104 u112 macKey ∗ A.pool ∗ Rest =
      ⌜macKey.length ≤ u104.toNat ∧ u104.toNat < 2 ^ 63 ∧ u112 ≠ 0#64⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
       (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
       (if u104 = 0#64 then emp
        else A.live u112 u104.toNat 1 ∗ (u112 ↦ₛ macKey) ∗
          memRegion (u112 + BitVec.ofNat 64 macKey.length) (u104.toNat - macKey.length)) ∗
       A.pool ∗ Rest) := by unfold vecU8Payload; ac_rfl
  rw [hpure]
  refine SepWPp.pure_left fun ⟨hm_le, hm_cap, _⟩ => ?_
  have hm_cases : macKey = [] ∨ 0 < macKey.length := by cases macKey <;> simp
  rcases hm_cases with rfl | hm_pos
  · simp only [List.length_nil, BitVec.ofNat_eq_ofNat]
    apply SepWPp.of_sepWP_ret; refine v10_sepWP_exists_post 1#64 ?_
    states_from_pb_fetches_range b (Rust.withPanics ext) 10680 60
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [h184, h1000, h1008]
      have hv0 := vecU8Payload_zero A
      have hite := v10_ite_nil_entails_vecCapPtrDealloc A u104 u112
      refine Entails.trans (Entails.of_eq (show _ =
        emp ∗ (if u104 = 0#64 then emp else A.live u112 u104.toNat 1 ∗ (u112 ↦ₛ ([] : List (BitVec 8))) ∗
          memRegion (u112 + 0#64) (u104.toNat - 0)) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2216#64) ↦₆₄ 1#64) ∗
         ((s0.sp - 1400#64) ↦₆₄ u112) ∗ ((s0.sp - 1392#64) ↦₆₄ 0#64) ∗ A.pool ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hv0 (sepConj_mono_left hite)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hc2_ne : u104 ≠ 0#64 := cap_ne_zero_of_pos hm_pos hm_le
    have hm_lt63 : macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : macKey.length < 2 ^ 64 := by omega
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false := ofNat_beq_zero_false hm_pos hm_lt64
    have hm_toNat : (BitVec.ofNat 64 macKey.length).toNat = macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hlay : LayoutOk macKey.length 1 := ⟨hm_pos, hpow1, by omega⟩
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hshim := hA.shim_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    have halloc := hA.alloc_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc"))
    have hmc := hA.session_memcpy_region_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy"))
    have hoom_step := @v10_oom_11572_entails b ext s0
    simp only [hc2_ne, ↓reduceIte, sepConj_assoc]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    states_from_pb_fetches_range b (Rust.withPanics ext) 10680 60
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
      at hshim halloc hmc hoom_step hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + 10708#64)
    wp_steps; wp_apply; wp_steps; nth_rw 1 [← hsp1]; nth_rw 1 [← h_1]; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte]; rw [v10_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      have htr_sf1 : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htrace]; simp only [wp_norm, arm64_norm, *]
      refine v10_sepWPp_seq_clean (mid := entry + 11572#64)
        (P_mid := A.pool ∗ stackAt sf.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056 ∗
          ((s0.sp - 2216#64) ↦₆₄ v184) ∗ ((s0.sp - 1400#64) ↦₆₄ u112) ∗
          ((s0.sp - 1392#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
          A.live u112 u104.toNat 1 ∗ (u112 ↦ₛ macKey) ∗
          memRegion (u112 + BitVec.ofNat 64 macKey.length) (u104.toNat - macKey.length) ∗ Rest)
        (Q_regs := fun sm => sm.trace = s0.trace ++ [allocFailedEvent]) ?_ ?_
      · wp_steps; wp_done
      · intro s3 hpc3 hrun3 htr3; exact hoom_step s3 _ _ _ hpc3 hrun3 htr3
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
      rw [v10_pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      have hsp_sf1 : sf_1.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret; refine v10_sepWP_exists_post (sf_1.readReg64 (Reg.gpr 0#5)) ?_
      wp_steps
      have hsp_eq_sf : sf_1.sp = sf.sp := by simp only [wp_norm, arm64_norm, *]
      wp_simp_pre [← hsp_eq_sf]; wp_apply; wp_simp_pre [hsp_eq_sf]; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h184, h1000, h1008]
        have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp_sf1] at hst; rw [hsp_sf] at hst
        have hv_new := vecU8Payload_pos A (sf_1.readReg64 (Reg.gpr 0#5)) macKey hm_pos hm_lt63 hoom
        have hv_old := v10_live_bytes_entails_vecCapPtrDealloc A u104 u112 macKey hc2_ne hm_le
        refine Entails.trans (Entails.of_eq (show _ =
          (stackAt sf.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          (A.live (sf_1.readReg64 (Reg.gpr 0#5)) macKey.length 1 ∗ (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ macKey)) ∗
          (A.live u112 u104.toNat 1 ∗ (u112 ↦ₛ macKey) ∗
            memRegion (u112 + BitVec.ofNat 64 macKey.length) (u104.toNat - macKey.length)) ∗
          (((s0.sp - 2216#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
           ((s0.sp - 1400#64) ↦₆₄ u112) ∗ ((s0.sp - 1392#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
           A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hst (sepConj_mono hv_new (sepConj_mono_left hv_old)))
          (Entails.of_eq (by ac_rfl))
      · wp_done

theorem Ext4K.v8_clone_rootKey_1984_to_10680
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA u8 u80 u88 u128 v120 v200 : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1984#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = u80)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10680#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 120#64) ↦₆₄ v120) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗ (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
        (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗ vecU8Payload A u80 u88 rootKey ∗ A.pool ∗ Rest)
      (fun sm Pm => ∃ p1_new : BitVec 64,
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 120#64) ↦₆₄ u128) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1_new) ∗
          (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗ (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
          (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗ vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
          vecCapPtrDealloc A u80 u88 ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 rootKey.length ∧ sm.readReg64 .x23 = u80 ∧
        sm.readReg64 .x24 = u88 ∧ sm.readReg64 .x26 = u8 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) :=
  v8_clone_rootKey_1984_to_10680_v10a (.of_4k hA) s0 s1 out pbA u8 u80
    u88 u128 v120 v200 rootKey Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hx27_1 htr1

theorem v8_clone_rootKey_1984_to_10680
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA u8 u80 u88 u128 v120 v200 : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1984#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = u80)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10680#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 120#64) ↦₆₄ v120) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗ (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
        (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗ vecU8Payload A u80 u88 rootKey ∗ A.pool ∗ Rest)
      (fun sm Pm => ∃ p1_new : BitVec 64,
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 120#64) ↦₆₄ u128) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1_new) ∗
          (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗ (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
          (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗ vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
          vecCapPtrDealloc A u80 u88 ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 rootKey.length ∧ sm.readReg64 .x23 = u80 ∧
        sm.readReg64 .x24 = u88 ∧ sm.readReg64 .x26 = u8 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) :=
  v8_clone_rootKey_1984_to_10680_v10a (.of_allocContracts hA) s0 s1 out pbA u8 u80
    u88 u128 v120 v200 rootKey Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hx27_1 htr1

theorem Ext4K.v8_clone_macKey_10680_to_10740
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA u8 l1 u80 u88 u104 u112 v184 : BitVec 64)
    (macKey : List (BitVec 8)) (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10680#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = u80) (hx24_1 : s1.readReg64 .x24 = u88)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10740#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
        (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
        vecU8Payload A u104 u112 macKey ∗ A.pool ∗ Rest)
      (fun sm Pm => ∃ p2_new : BitVec 64,
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
          (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
          vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
          vecCapPtrDealloc A u104 u112 ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = u112 ∧
        sm.readReg64 .x22 = l1 ∧ sm.readReg64 .x23 = u80 ∧ sm.readReg64 .x24 = u88 ∧
        sm.readReg64 .x26 = u8 ∧ sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = BitVec.ofNat 64 macKey.length ∧ TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) :=
  v8_clone_macKey_10680_to_10740_v10a (.of_4k hA) s0 s1 out pbA u8 l1
    u80 u88 u104 u112 v184 macKey Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1
    hx26_1 hx27_1 htr1

theorem v8_clone_macKey_10680_to_10740
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA u8 l1 u80 u88 u104 u112 v184 : BitVec 64)
    (macKey : List (BitVec 8)) (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10680#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = u80) (hx24_1 : s1.readReg64 .x24 = u88)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10740#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
        (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
        vecU8Payload A u104 u112 macKey ∗ A.pool ∗ Rest)
      (fun sm Pm => ∃ p2_new : BitVec 64,
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
          (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
          vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
          vecCapPtrDealloc A u104 u112 ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = u112 ∧
        sm.readReg64 .x22 = l1 ∧ sm.readReg64 .x23 = u80 ∧ sm.readReg64 .x24 = u88 ∧
        sm.readReg64 .x26 = u8 ∧ sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = BitVec.ofNat 64 macKey.length ∧ TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) :=
  v8_clone_macKey_10680_to_10740_v10a (.of_allocContracts hA) s0 s1 out pbA u8 l1
    u80 u88 u104 u112 v184 macKey Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1
    hx26_1 hx27_1 htr1

theorem v8_stackAt_encoderFromPb_split_7552 (sp0 : BitVec 64) :
    stackAt (sp0 - 2400#64) encoderFromPbStack =
      memRegion (sp0 - 7552#64) 1056 ∗ stackAt (sp0 - 2400#64) allocHookStack := by
  rw [stackAt_encoderFromPb_split_allocHook (sp0 - 2400#64)]
  have h : (sp0 - 2400#64) - 5152#64 = sp0 - 7552#64 := by bv_omega
  rw [h]

private theorem v8_dealloc_old_auth_10740_to_10836_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : V10Alloc b A ext)
    (s0 s1 : State) (out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 l1 l2 : BitVec 64)
    (v64 v176 v216 v224 : BitVec 64) (Rest : SepProp)
    (hl1_lt : l1.toNat < 2 ^ 63) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10740#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = u112)
    (hx22_1 : s1.readReg64 .x22 = l1) (hx23_1 : s1.readReg64 .x23 = u80)
    (hx24_1 : s1.readReg64 .x24 = u88) (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA) (hx28_1 : s1.readReg64 .x28 = l2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10836#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗
        (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
        (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
        (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
        vecCapPtrDealloc A u80 u88 ∗ vecCapPtrDealloc A u104 u112 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
          (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
          (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
          (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
          A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = u64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = u64 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = l2 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hl1_ne : (l1 + 1#64 == 0#64) = false := v10_cap_add_one_beq_zero_false hl1_lt
  have hdealloc := v10_sub_ok_dealloc_125316_v10a hA
  simp only [rustDeallocSpec] at hdealloc
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10800#64)
    (P_mid :=
      memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
      (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
      (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
      (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
      (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
      (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
      vecCapPtrDealloc A u104 u112 ∗ A.pool ∗ Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x9 = u64 ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x20 = u112 ∧ s2.readReg64 .x21 = u64 ∧ s2.readReg64 .x22 = l1 ∧
      s2.readReg64 .x26 = u8 ∧ s2.readReg64 .x27 = pbA ∧ s2.readReg64 .x28 = l2 ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 10740 60
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
      BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_cases hu80 : (u80 == 0#64) = true <;>
      simp only [hu80, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx19_2, hx20_2, hx21_2, hx22_2, hx26_2, hx27_2, hx28_2, htr2⟩
    states_from_pb_fetches_range b (Rust.withPanics ext) 10800 36
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
      BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_cases hu104 : (u104 == 0#64) = true <;>
      simp only [hu104, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre (by rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done

theorem Ext4K.v8_dealloc_old_auth_10740_to_10836
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 l1 l2 : BitVec 64)
    (v64 v176 v216 v224 : BitVec 64) (Rest : SepProp)
    (hl1_lt : l1.toNat < 2 ^ 63) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10740#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = u112)
    (hx22_1 : s1.readReg64 .x22 = l1) (hx23_1 : s1.readReg64 .x23 = u80)
    (hx24_1 : s1.readReg64 .x24 = u88) (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA) (hx28_1 : s1.readReg64 .x28 = l2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10836#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗
        (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
        (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
        (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
        vecCapPtrDealloc A u80 u88 ∗ vecCapPtrDealloc A u104 u112 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
          (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
          (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
          (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
          A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = u64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = u64 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = l2 ∧ TraceCalleeSaved sm s0) :=
  v8_dealloc_old_auth_10740_to_10836_v10a (.of_4k hA) s0 s1 out pbA
    u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 l1 l2 v64 v176 v216 v224 Rest hl1_lt hsp0_align hpc1
    hrun1 hsp1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1 htr1

theorem v8_dealloc_old_auth_10740_to_10836
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 l1 l2 : BitVec 64)
    (v64 v176 v216 v224 : BitVec 64) (Rest : SepProp)
    (hl1_lt : l1.toNat < 2 ^ 63) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10740#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = u112)
    (hx22_1 : s1.readReg64 .x22 = l1) (hx23_1 : s1.readReg64 .x23 = u80)
    (hx24_1 : s1.readReg64 .x24 = u88) (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA) (hx28_1 : s1.readReg64 .x28 = l2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10836#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗
        (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
        (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
        (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
        vecCapPtrDealloc A u80 u88 ∗ vecCapPtrDealloc A u104 u112 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
          (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
          (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
          (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
          A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = u64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = u64 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = l2 ∧ TraceCalleeSaved sm s0) :=
  v8_dealloc_old_auth_10740_to_10836_v10a (.of_allocContracts hA) s0 s1 out pbA
    u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 l1 l2 v64 v176 v216 v224 Rest hl1_lt hsp0_align hpc1
    hrun1 hsp1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1 htr1

/-! ## 3. 5-Vector Cleanup Path (`+10836 -> +11120 -> +4240`) -/

/-- At `+10836` (`0x5caf8`), when `[sp + 1520] = noneCap` (`sendingCt1 = none`),
`ldr x8, [sp, #1520]; cmn x8, #1; b.eq +11120` branches to `+11120`. -/
theorem v8_check_sendingCt1_10836_none
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pa5 ca1 ca2 ca3 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10836#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = pa5) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa5) (hx22_1 : s1.readReg64 .x22 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3) (hx28_1 : s1.readReg64 .x28 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11120#64) s1
      ((((s0.sp - 2400#64) + 1520#64) ↦₆₄ noneCap) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ (((s0.sp - 2400#64) + 1520#64) ↦₆₄ noneCap) ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = pa5 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa5 ∧ sm.readReg64 .x22 = ca1 ∧ sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = ca2 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  states_from_pb_fetches_range b (Rust.withPanics ext) 10836 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

private theorem v8_cleanup_vec5_11212_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : V10Alloc b A ext)
    (s0 s1 : State) (out ca5 pa5 : BitVec 64) (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11212#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = pa5) (hx19_1 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ vecCapPtrDealloc A ca5 pa5 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v10_sub_ok_dealloc_125316_v10a hA
  simp only [rustDeallocSpec] at hdealloc
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
  states_from_pb_fetches_range b (Rust.withPanics ext) 11004 8
  states_from_pb_fetches_range b (Rust.withPanics ext) 11212 28
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  by_cases hca5 : (ca5 == 0#64) = true <;>
    simp only [hca5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · wp_steps; wp_apply; wp_steps
    refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done

private theorem v8_cleanup_5vecs_11120_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : V10Alloc b A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11120#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = pa5) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa5) (hx22_1 : s1.readReg64 .x22 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3) (hx28_1 : s1.readReg64 .x28 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗ vecCapPtrDealloc A ca3 pa3 ∗
        vecCapPtrDealloc A ca4 pa4 ∗ vecCapPtrDealloc A ca5 pa5 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v10_sub_ok_dealloc_125316_v10a hA
  simp only [rustDeallocSpec] at hdealloc
  have h11212 := v8_cleanup_vec5_11212_v10a hA s0
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
  states_from_pb_fetches_range b (Rust.withPanics ext) 11120 92
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    BitVec.ofNat_eq_ofNat] at hdealloc h11212 hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine EncoderFromPb.seq_clean (mid := entry + 11144#64)
    (P_mid := memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
      (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
      (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      (if (ca2 == 0#64) = true then emp else A.live pa2 ca2.toNat 1 ∗ memRegion pa2 ca2.toNat) ∗
      (if (ca3 == 0#64) = true then emp else A.live pa3 ca3.toNat 1 ∗ memRegion pa3 ca3.toNat) ∗
      (if (ca4 == 0#64) = true then emp else A.live pa4 ca4.toNat 1 ∗ memRegion pa4 ca4.toNat) ∗
      (if (ca5 == 0#64) = true then emp else A.live pa5 ca5.toNat 1 ∗ memRegion pa5 ca5.toNat) ∗ A.pool ∗ Rest)
    (Q := fun s2 => s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x9 = pa5 ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = pa5 ∧ s2.readReg64 .x26 = ca3 ∧ s2.readReg64 .x28 = ca2 ∧ TraceCalleeSaved s2 s0) ?_ ?_
  · by_cases hca1 : (ca1 == 0#64) = true <;>
      simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx19_2, hx21_2, hx26_2, hx28_2, htr2⟩
    refine EncoderFromPb.seq_clean (mid := entry + 11168#64)
      (P_mid := memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        (if (ca3 == 0#64) = true then emp else A.live pa3 ca3.toNat 1 ∗ memRegion pa3 ca3.toNat) ∗
        (if (ca4 == 0#64) = true then emp else A.live pa4 ca4.toNat 1 ∗ memRegion pa4 ca4.toNat) ∗
        (if (ca5 == 0#64) = true then emp else A.live pa5 ca5.toNat 1 ∗ memRegion pa5 ca5.toNat) ∗ A.pool ∗ Rest)
      (Q := fun s3 => s3.sp = s0.sp - 2400#64 ∧ s3.readReg64 .x9 = pa5 ∧ s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = pa5 ∧ s3.readReg64 .x26 = ca3 ∧ TraceCalleeSaved s3 s0) ?_ ?_
    · by_cases hca2 : (ca2 == 0#64) = true <;>
        simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply; wp_steps
        refine EncoderFromPb.align_pre (by rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx9_3, hx19_3, hx21_3, hx26_3, htr3⟩
      refine EncoderFromPb.seq_clean (mid := entry + 11192#64)
        (P_mid := memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          (if (ca4 == 0#64) = true then emp else A.live pa4 ca4.toNat 1 ∗ memRegion pa4 ca4.toNat) ∗
          (if (ca5 == 0#64) = true then emp else A.live pa5 ca5.toNat 1 ∗ memRegion pa5 ca5.toNat) ∗ A.pool ∗ Rest)
        (Q := fun s4 => s4.sp = s0.sp - 2400#64 ∧ s4.readReg64 .x9 = pa5 ∧ s4.readReg64 .x19 = out ∧
          s4.readReg64 .x21 = pa5 ∧ TraceCalleeSaved s4 s0) ?_ ?_
      · by_cases hca3 : (ca3 == 0#64) = true <;>
          simp only [hca3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
        · wp_steps; wp_apply; wp_steps
          refine EncoderFromPb.align_pre (by rw [hsp3]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · intro s4 hpc4 hrun4 ⟨hsp4, hx9_4, hx19_4, hx21_4, htr4⟩
        refine EncoderFromPb.seq_clean (mid := entry + 11212#64)
          (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
            (if (ca5 == 0#64) = true then emp else A.live pa5 ca5.toNat 1 ∗ memRegion pa5 ca5.toNat) ∗ A.pool ∗
            ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
             (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
             (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ Rest))
          (Q := fun s5 => s5.sp = s0.sp - 2400#64 ∧ s5.readReg64 .x9 = pa5 ∧ s5.readReg64 .x19 = out ∧
            TraceCalleeSaved s5 s0) ?_ ?_
        · by_cases hca4 : (ca4 == 0#64) = true <;>
            simp only [hca4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine EncoderFromPb.align_pre ?_ ?_
            · rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
            · wp_done
          · wp_steps; wp_apply; wp_steps; refine EncoderFromPb.align_pre ?_ ?_
            · rw [v8_stackAt_encoderFromPb_split_7552 s0.sp, hsp4]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
            · wp_done
        · intro s5 hpc5 hrun5 ⟨hsp5, hx9_5, hx19_5, htr5⟩
          have h5 := h11212 s5 out ca5 pa5
            ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
             (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
             (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ Rest)
            hsp0_align hpc5 hrun5 hsp5 hx9_5 hx19_5 htr5
          refine SepWP.mono h5 fun sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx20_f, htr_f⟩ => ?_
          rw [v8_stackAt_encoderFromPb_split_7552 s0.sp] at hPf
          exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, hx20_f, htr_f⟩

theorem Ext4K.v8_cleanup_vec5_11212
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out ca5 pa5 : BitVec 64) (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11212#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = pa5) (hx19_1 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ vecCapPtrDealloc A ca5 pa5 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_vec5_11212_v10a (.of_4k hA) s0 s1 out ca5 pa5 Rest hsp0_align hpc1 hrun1 hsp1 hx9_1 hx19_1 htr1

theorem v8_cleanup_vec5_11212
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s1 : State) (out ca5 pa5 : BitVec 64) (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11212#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = pa5) (hx19_1 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ vecCapPtrDealloc A ca5 pa5 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_vec5_11212_v10a (.of_allocContracts hA) s0 s1 out ca5 pa5 Rest hsp0_align hpc1 hrun1 hsp1 hx9_1 hx19_1 htr1

theorem Ext4K.v8_cleanup_5vecs_11120
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11120#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = pa5) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa5) (hx22_1 : s1.readReg64 .x22 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3) (hx28_1 : s1.readReg64 .x28 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗ vecCapPtrDealloc A ca3 pa3 ∗
        vecCapPtrDealloc A ca4 pa4 ∗ vecCapPtrDealloc A ca5 pa5 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_5vecs_11120_v10a (.of_4k hA) s0 s1 out ca1 pa1 ca2 pa2
    ca3 pa3 ca4 pa4 ca5 pa5 Rest hsp0_align hpc1 hrun1 hsp1 hx9_1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1 htr1

theorem v8_cleanup_5vecs_11120
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11120#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = pa5) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa5) (hx22_1 : s1.readReg64 .x22 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3) (hx28_1 : s1.readReg64 .x28 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗ vecCapPtrDealloc A ca3 pa3 ∗
        vecCapPtrDealloc A ca4 pa4 ∗ vecCapPtrDealloc A ca5 pa5 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_5vecs_11120_v10a (.of_allocContracts hA) s0 s1 out ca1 pa1 ca2 pa2
    ca3 pa3 ca4 pa4 ca5 pa5 Rest hsp0_align hpc1 hrun1 hsp1 hx9_1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1 htr1

end CryptoVerification.SpqrV1.States.FromPb
