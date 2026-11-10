/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant2hsb` -/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open V1State.Chunked
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

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

open CryptoVerification.SpqrV1.Alloc
attribute [local simp, local arm64_norm, local wp_norm] v2hs_bv_add_add_lit
attribute [local simp, local arm64_norm, local wp_norm] v2hs_bv_sub_sub_lit

namespace Ext4K

private theorem sub_ok_dealloc_125316_4k_Variant2hsb
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName +
        (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) :=
  hA.dealloc_ok_at statesFromPbName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))

set_option maxHeartbeats 800000 in
/-- `Authenticator::from_pb` segment (`+3436 -> +8700`) in Variant 2:
    allocates and copies `auth.rootKey` into `pa1 = s1.readReg64 .x23` (or `1#64` if empty). -/
theorem v2hs_auth_from_pb_step1_3436_8700
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (target_pc fsp out d_w0 : BitVec 64)
    (u32 u40 u56 u64 u80 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3436#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (hx28 : s.readReg64 .x28 = u80)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa1 : BitVec 64) (s1 : State),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8700#64 →
      s1.status = .Running →
      (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
       s1.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
       s1.readReg64 .x21 = s.readReg64 .x21 ∧
       s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = pa1 ∧
       s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
       s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
       s1.readReg64 .x28 = u80 ∧
       TraceCalleeSaved s1 s0) →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 216#64) ↦₆₄ u40) ∗
         vecCapPtrDealloc A u32 u40 ∗
         vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
         A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 216#64) ↦₆₄ u40) ∗
       vecU8Payload A u32 u40 auth.rootKey ∗
       A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hr_cases : auth.rootKey = [] ∨ 0 < auth.rootKey.length := by cases auth.rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · refine sepWPp_seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8700#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        vecCapPtrDealloc A u32 u40 ∗
        vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) 1#64 auth.rootKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
        s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s1 s0)
      ?_ (hnext 1#64)
    clear hnext; rw [hr_nil] at hx20 ⊢
    states_from_pb_fetches_range b (Rust.withPanics ext) 3436 4
    states_from_pb_fetches_range b (Rust.withPanics ext) 8696 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, List.length_nil, BitVec.ofNat_eq_ofNat] at hpc hx20 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A u32 u40 []
      have hn := v2hs_vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A u32 u40 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (v2hs_vecU8Payload_pos_unpack A u32 u40 auth.rootKey hr_pos)))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
          (⌜auth.rootKey.length ≤ u32.toNat ∧ u32.toNat < 2 ^ 63 ∧
            u40 ≠ 0#64 ∧ u32 ≠ 0#64⌝ ∗
           (A.live u40 u32.toNat 1 ∗ (u40 ↦ₛ auth.rootKey) ∗
            memRegion (u40 + BitVec.ofNat 64 auth.rootKey.length) (u32.toNat - auth.rootKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.rootKey.length ≤ u32.toNat ∧ u32.toNat < 2 ^ 63 ∧
          u40 ≠ 0#64 ∧ u32 ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
         A.live u40 u32.toNat 1 ∗ (u40 ↦ₛ auth.rootKey) ∗
         memRegion (u40 + BitVec.ofNat 64 auth.rootKey.length) (u32.toNat - auth.rootKey.length) ∗
         A.pool ∗ Frame) by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hr_le, hr_cap, hptr0, hcap0_ne⟩ => ?_
    have hr_lt63 : auth.rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 auth.rootKey.length == 0#64) = false := ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hr_lay3 : auth.rootKey.length + 1 ≤ 2 ^ 63 := hr_lt63
    have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [stackAt_encoderFromPb_split_allocHook fsp]; wp_simp_pre [sepConj_assoc]
    have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
    have hshim := hA.shim_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
    have halloc := hA.alloc_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
    have hmc := hA.session_memcpy_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy")); simp only [sessionMemcpySpec] at hmc
    have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
      (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))) (by rw [hfn, stubOff_handle_error])
    states_from_pb_fetches_range b (Rust.withPanics ext) 3436 44
    states_from_pb_fetches_range b (Rust.withPanics ext) 11608 12
    dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hshim halloc hmc hpanic hpc hnext ⊢
    clear hfn hA
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 3456#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.rootKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [v2hs_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [v2hs_pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      refine sepWPp_seq_clean (mid := entry + 8700#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
          vecCapPtrDealloc A u32 u40 ∗
          vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) (sf_1.readReg64 Reg.x0) auth.rootKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
          s1.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
          s1.readReg64 .x21 = s.readReg64 .x21 ∧
          s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = sf_1.readReg64 Reg.x0 ∧
          s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
          s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = u80 ∧
          TraceCalleeSaved s1 s0)
        ?_ (hnext (sf_1.readReg64 Reg.x0))
      clear hnext
      have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp, hsp_sf1]
        have hd := v2hs_vecU8Payload_pos_dealloc A u32 u40 auth.rootKey hr_le hr_cap hptr0 hcap0_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.rootKey hr_pos hr_lt63 hoom0
        simp only [arm64_norm] at hd hp ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live u40 u32.toNat 1 ∗ (u40 ↦ₛ auth.rootKey) ∗
           memRegion (u40 + BitVec.ofNat 64 auth.rootKey.length) (u32.toNat - auth.rootKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.rootKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.rootKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
          ((fsp + 216#64) ↦₆₄ u40) ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

set_option maxHeartbeats 800000 in
/-- `Authenticator::from_pb` segment (`+8700 -> +8884`) in Variant 2:
    allocates and copies `auth.macKey` into `pa2` stored at `[fsp + 184]` (or `1#64` if empty). -/
theorem v2hs_auth_from_pb_step2_8700_8884
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (target_pc fsp out d_w0 pa1 w184 : BitVec 64)
    (u32 u56 u64 u72 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8700#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa2 : BitVec 64) (s2 : State),
      s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8884#64 →
      s2.status = .Running →
      (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
       s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
       s2.readReg64 .x21 = s.readReg64 .x21 ∧
       s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
       s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
       s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
       TraceCalleeSaved s2 s0) →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc s2
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         ((fsp + 232#64) ↦₆₄ u72) ∗
         vecCapPtrDealloc A u56 u64 ∗
         vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
         A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗
       vecU8Payload A u56 u64 auth.macKey ∗
       A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hm_cases : auth.macKey = [] ∨ 0 < auth.macKey.length := by cases auth.macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · refine sepWPp_seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8884#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ 1#64) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ vecCapPtrDealloc A u56 u64 ∗
        vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) 1#64 auth.macKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x21 = s.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
        s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
        TraceCalleeSaved s2 s0)
      ?_ (hnext 1#64)
    clear hnext; subst hu72; rw [hm_nil]
    states_from_pb_fetches_range b (Rust.withPanics ext) 8700 8
    states_from_pb_fetches_range b (Rust.withPanics ext) 8876 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, List.length_nil, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A u56 u64 []
      have hn := v2hs_vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A u56 u64 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ 1#64) ∗
        ((fsp + 232#64) ↦₆₄ 0#64) ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · subst hu72
    refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (v2hs_vecU8Payload_pos_unpack A u56 u64 auth.macKey hm_pos))))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
          ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
          (⌜auth.macKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧
            u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
           (A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.macKey) ∗
            memRegion (u64 + BitVec.ofNat 64 auth.macKey.length) (u56.toNat - auth.macKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.macKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧
          u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
         ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
         A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.macKey) ∗
         memRegion (u64 + BitVec.ofNat 64 auth.macKey.length) (u56.toNat - auth.macKey.length) ∗
         A.pool ∗ Frame) by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hm_le, hm_cap, hptr1, hcap1_ne⟩ => ?_
    have hm_lt63 : auth.macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : auth.macKey.length < 2 ^ 64 := by omega
    have hm_toNat : (BitVec.ofNat 64 auth.macKey.length).toNat = auth.macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hm_ne0 : (BitVec.ofNat 64 auth.macKey.length == 0#64) = false := ofNat_beq_zero_false hm_pos hm_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hm_lay3 : auth.macKey.length + 1 ≤ 2 ^ 63 := hm_lt63
    have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [stackAt_encoderFromPb_split_allocHook fsp]; wp_simp_pre [sepConj_assoc]
    have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
    have hshim := hA.shim_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
    have halloc := hA.alloc_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
    have hmc := hA.session_memcpy_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy")); simp only [sessionMemcpySpec] at hmc
    have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
      (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))) (by rw [hfn, stubOff_handle_error])
    states_from_pb_fetches_range b (Rust.withPanics ext) 8700 48
    states_from_pb_fetches_range b (Rust.withPanics ext) 11572 12
    dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hshim halloc hmc hpanic hpc hnext ⊢
    clear hfn hA
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 8724#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.macKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [v2hs_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
      rw [v2hs_pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      refine sepWPp_seq_clean (mid := entry + 8884#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗
          ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
          vecCapPtrDealloc A u56 u64 ∗
          vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (sf_1.readReg64 Reg.x0) auth.macKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
          s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
          s2.readReg64 .x21 = s.readReg64 .x21 ∧
          s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
          s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
          s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
          TraceCalleeSaved s2 s0)
        ?_ (hnext (sf_1.readReg64 Reg.x0))
      clear hnext
      have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp, hsp_sf1]
        have hd := v2hs_vecU8Payload_pos_dealloc A u56 u64 auth.macKey hm_le hm_cap hptr1 hcap1_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.macKey hm_pos hm_lt63 hoom1
        simp only [arm64_norm] at hd hp ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.macKey) ∗
           memRegion (u64 + BitVec.ofNat 64 auth.macKey.length) (u56.toNat - auth.macKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.macKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.macKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
          ((fsp + 184#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗
          ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

/-- `Authenticator::from_pb` segment (`+8884 -> +8944`) in Variant 2:
    deallocates `auth.rootKey` and `auth.macKey` protobuf buffers and loads `x25 = u48`, `x26 = pa1 >>> 8`, `x28 = u80`. -/
theorem v2hs_auth_from_pb_step3_8884_8944
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (out d_w0 pa1 : BitVec 64)
    (u32 u40 u56 u64 u80 : BitVec 64)
    (auth : ProtoAuthenticator) (Rest : SepProp)
    (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8884#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8944#64) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
        vecCapPtrDealloc A u32 u40 ∗
        vecCapPtrDealloc A u56 u64 ∗
        A.pool ∗
        Rest)
      (fun s3 P3 =>
        (P3 ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2400#64 + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
          A.pool ∗
          Rest) ∧
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = s.readReg64 .x21 ∧
        s3.readReg64 .x22 = d_w0 ∧
        s3.readReg64 .x23 = pa1 ∧
        s3.readReg64 .x25 = BitVec.ofNat 64 auth.rootKey.length ∧
        s3.readReg64 .x26 = pa1 >>> 8 ∧
        s3.readReg64 .x27 = s.readReg64 .x27 ∧
        s3.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s3 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hr_lt63
  have hcmn : ¬((BitVec.ofNat 64 auth.rootKey.length + 1#64 == 0#64) = true) :=
    cap_add_one_beq_zero_false hr_toNat
  have hdealloc := sub_ok_dealloc_125316_4k_Variant2hsb (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  wp_simp_pre [arm64_norm, sepConj_assoc]
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8912#64)
    (P_mid :=
      memRegion (s0.sp - 7552#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      ((s0.sp - 2200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((s0.sp - 2184#64) ↦₆₄ u40) ∗
      ((s0.sp - 2176#64) ↦₆₄ u80) ∗
      vecCapPtrDealloc A u56 u64 ∗
      A.pool ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = s.readReg64 .x21 ∧
      s2.readReg64 .x22 = d_w0 ∧
      s2.readReg64 .x23 = pa1 ∧
      s2.readReg64 .x24 = u56 ∧
      s2.readReg64 .x25 = u64 ∧
      s2.readReg64 .x26 = pa1 >>> 8 ∧
      s2.readReg64 .x27 = s.readReg64 .x27 ∧
      s2.readReg64 .x28 = u80 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 8884 28
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
      BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_cases hc_r : (u32 == 0#64) = true <;>
      simp only [hc_r, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre (by rw [hsp]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
    states_from_pb_fetches_range b (Rust.withPanics ext) 8912 32
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
      BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_cases hc_m : (u56 == 0#64) = true <;>
      simp only [hc_m, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
      · wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
      · wp_done

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb
