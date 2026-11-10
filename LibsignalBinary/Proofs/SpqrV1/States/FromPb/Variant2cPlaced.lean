/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2c
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 1 (`KeysSampled`, `+1104`) — Part C

Relocatable Block-`333` `macKey` clone, input-buffer deallocation (`+8756 -> +4016`), and
error cleanup (`+5916`, `+5860`, `+4116`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2cPlaced

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
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
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1c_bv_add_add_lit v1c_bv_sub_sub_lit

/-! ## `Authenticator::from_pb` MAC-Key Clone (`+8756 -> +9804`) and Buffer Deallocation (`+9804 -> +4016`) -/

set_option maxHeartbeats 800000 in
/-- `Authenticator::from_pb` segment (`+8756 -> +9804`) in Variant 1:
    allocates and copies `auth.macKey` into `[fsp + 184] := pa2` (or `1#64` if empty). -/
theorem v1_auth_from_pb_step2_8756_9804_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (target_pc fsp out pbA pa1 : BitVec 64)
    (u8 u56 u64 u80 u88 w184 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8756#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = u80)
    (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa2 : BitVec 64) (s2 : State),
      s2.pc = lsmpl.base 333 + 9804#64 →
      s2.status = .Running →
      (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
       s2.readReg64 .x21 = u8 ∧
       s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
       s2.readReg64 .x23 = u80 ∧ s2.readReg64 .x24 = u88 ∧
       s2.readReg64 .x25 = u56 ∧ s2.readReg64 .x26 = pa1 ∧
       s2.readReg64 .x27 = pbA ∧ s2.readReg64 .x28 = u64 ∧
       TraceCalleeSaved s2 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s2
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         vecCapPtrDealloc A u80 u88 ∗
         vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
         A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗
       vecU8Payload A u80 u88 auth.macKey ∗
       A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hm_cases : auth.macKey = [] ∨ 0 < auth.macKey.length := by cases auth.macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · refine CryptoVerification.SpqrV1.States.FromPb.sepWPp_seq_clean
      (mid := lsmpl.base 333 + 9804#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ 1#64) ∗
        vecCapPtrDealloc A u80 u88 ∗
        vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) 1#64 auth.macKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = u8 ∧
        s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x23 = u80 ∧ s2.readReg64 .x24 = u88 ∧
        s2.readReg64 .x25 = u56 ∧ s2.readReg64 .x26 = pa1 ∧
        s2.readReg64 .x27 = pbA ∧ s2.readReg64 .x28 = u64 ∧
        TraceCalleeSaved s2 s0)
      ?_ (hnext 1#64)
    clear hnext; rw [hm_nil] at hx9 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hpc hx9 ⊢
    change s.pc = (blkPl_333).base + 8756#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9804#64) s _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A u80 u88 []
      have hn := vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A u80 u88 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ 1#64) ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecU8Payload_pos_unpack A u80 u88 auth.macKey hm_pos)))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
          (⌜auth.macKey.length ≤ u80.toNat ∧ u80.toNat < 2 ^ 63 ∧
            u88 ≠ 0#64 ∧ u80 ≠ 0#64⌝ ∗
           (A.live u88 u80.toNat 1 ∗ (u88 ↦ₛ auth.macKey) ∗
            memRegion (u88 + BitVec.ofNat 64 auth.macKey.length) (u80.toNat - auth.macKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.macKey.length ≤ u80.toNat ∧ u80.toNat < 2 ^ 63 ∧
          u88 ≠ 0#64 ∧ u80 ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
         A.live u88 u80.toNat 1 ∗ (u88 ↦ₛ auth.macKey) ∗
         memRegion (u88 + BitVec.ofNat 64 auth.macKey.length) (u80.toNat - auth.macKey.length) ∗
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
    have hshim : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec := by
      simpa only [lsProg_333, blkPl_333] using
        (spqr_hook_ok_of_mem hA.shim : subroutine_ok (lsProg_333 (Rust.withPanics ext))
          (lsρ spqrRustNoAllocShimSym) sessionShimSpec)
    simp only [sessionShimSpec] at hshim
    have halloc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) := by
      simpa only [lsProg_333, blkPl_333] using
        (spqr_hook_ok_of_mem hA.alloc : subroutine_ok (lsProg_333 (Rust.withPanics ext))
          (lsρ spqrRustAllocSym) (rustAllocSpec A))
    simp only [rustAllocSpec] at halloc
    have hmc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec := by
      simpa only [lsProg_333, blkPl_333] using
        (spqr_hook_ok_of_mem hA.memcpy : subroutine_ok (lsProg_333 (Rust.withPanics ext))
          (lsρ spqrMemcpySym) sessionMemcpySpec)
    simp only [sessionMemcpySpec] at hmc
    have hpanic := fromPb_externAt?_handleError hA
    change s.pc = (blkPl_333).base + 8756#64 at hpc
    change ∀ (pa2 : BitVec 64) (s2 : State),
      s2.pc = (blkPl_333).base + 9804#64 → _ → _ →
      SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s2 _ _ _ at hnext
    change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s _ _ _
    clear hA
    apply SepWPp.of_sepWP (mid := (blkPl_333).base + 8780#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.macKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      refine CryptoVerification.SpqrV1.States.FromPb.sepWPp_seq_clean (mid := (blkPl_333).base + 9804#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗
          vecCapPtrDealloc A u80 u88 ∗
          vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (sf_1.readReg64 Reg.x0) auth.macKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
          s2.readReg64 .x21 = u8 ∧
          s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
          s2.readReg64 .x23 = u80 ∧ s2.readReg64 .x24 = u88 ∧
          s2.readReg64 .x25 = u56 ∧ s2.readReg64 .x26 = pa1 ∧
          s2.readReg64 .x27 = pbA ∧ s2.readReg64 .x28 = u64 ∧
          TraceCalleeSaved s2 s0)
        ?_ (hnext (sf_1.readReg64 Reg.x0))
      clear hnext
      have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp, hsp_sf1]
        have hd := vecU8Payload_pos_dealloc A u80 u88 auth.macKey hm_le hm_cap hptr1 hcap1_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.macKey hm_pos hm_lt63 hoom1
        simp only [arm64_norm] at hd hp ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live u88 u80.toNat 1 ∗ (u88 ↦ₛ auth.macKey) ∗
           memRegion (u88 + BitVec.ofNat 64 auth.macKey.length) (u80.toNat - auth.macKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.macKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.macKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
          ((fsp + 184#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

/-- `Authenticator::from_pb` segment (`+9804 -> +4016`) in Variant 1:
    deallocates `auth.rootKey` and `auth.macKey` protobuf buffers and sets up registers for `+4016`. -/
theorem v1_auth_from_pb_step3_9804_4016_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (out pbA pa1 : BitVec 64)
    (u8 u32 u56 u64 u80 u88 : BitVec 64)
    (auth : ProtoAuthenticator) (Rest : SepProp)
    (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9804#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = u80)
    (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4016#64) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        vecCapPtrDealloc A u56 u64 ∗
        vecCapPtrDealloc A u80 u88 ∗
        A.pool ∗
        Rest)
      (fun s3 P3 =>
        (P3 ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
          A.pool ∗
          Rest) ∧
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        s3.readReg64 .x20 = pa1 >>> 8 ∧
        s3.readReg64 .x21 = u8 ∧
        s3.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
        s3.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 ∧
        s3.readReg64 .x26 = pa1 ∧
        s3.readReg64 .x27 = pbA ∧
        s3.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s3 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hr_lt63
  have hcmn : (BitVec.ofNat 64 auth.rootKey.length + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hr_toNat)
  have hdealloc := v1_dealloc_ok_at_statesFromPb_placed hA
  simp only [rustDeallocSpec] at hdealloc
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 9824#64)
    (P_mid :=
      memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
      vecCapPtrDealloc A u80 u88 ∗
      A.pool ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = u8 ∧
      s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
      s2.readReg64 .x23 = u80 ∧
      s2.readReg64 .x24 = u88 ∧
      s2.readReg64 .x26 = pa1 ∧
      s2.readReg64 .x27 = pbA ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
    change s.pc = (blkPl_333).base + 9804#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9824#64) s _ _
    by_cases hc_r : (u56 == 0#64) = true <;>
      simp only [hc_r, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply
      refine EncoderFromPb.align_pre (by rw [hsp]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 4008#64)
      (P_mid :=
        memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
        stackAt (s0.sp - 2400#64) allocHookStack ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        A.pool ∗
        Rest)
      (Q := fun s3 =>
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        s3.readReg64 .x20 = pa1 >>> 8 ∧
        s3.readReg64 .x21 = u8 ∧
        s3.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
        s3.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 ∧
        s3.readReg64 .x26 = pa1 ∧
        s3.readReg64 .x27 = pbA ∧
        s3.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s3 s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
      change s2.pc = (blkPl_333).base + 9824#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4008#64) s2 _ _
      by_cases hc_m : (u80 == 0#64) = true <;>
        simp only [hc_m, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply
        refine EncoderFromPb.align_pre (by rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx20_3, hx21_3, hx22_3, hx25_3, hx26_3, hx27_3, hx28_3, htr3⟩
      change s3.pc = (blkPl_333).base + 4008#64 at hpc3
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4016#64) s3 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · simp only [arm64_norm]
        exact Entails.of_eq (by ac_rfl)
      · wp_done

/-! ## Cleanup Helpers for `sendingHdr = none` (`+5860`) and `from_pb` Error (`+4116`) -/

/-- Shared tail at `+5916`: deallocates `dk` (`x28 = cap_dk`, `[fsp + 216] = ptr_dk`)
    and exits via `v1_err_5940_placed` with `Err(StateDecode)`. -/
theorem v1_cleanup_dk_5916_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out u32 u40 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5916#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx28_1 : s1.readReg64 .x28 = u32)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 216 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        memRegion (s0.sp - 2400#64 + 224#64) 2080 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u32 u40 ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v1_dealloc_ok_at_statesFromPb_placed hA
  simp only [rustDeallocSpec] at hdealloc
  have hm2304 : memRegion (s0.sp - 2400#64) 216 ∗
      ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
      memRegion (s0.sp - 2400#64 + 224#64) 2080 ⊢
      memRegion (s0.sp - 2400#64) 2304 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (SpqrV1.Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 5940#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      (A.pool ∗ Rest))
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      (s2.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, spqrErrorByte, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
    change s1.pc = (blkPl_333).base + 5916#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5940#64) s1 _ _
    by_cases hc_dk : (u32 == 0#64) = true <;>
      simp only [hc_dk, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
        simp only [arm64_norm] at hm2304 ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 216 ∗
           ((s0.sp - 2184#64) ↦₆₄ u40) ∗
           memRegion (s0.sp - 2176#64) 2080) ∗
          (memRegion (s0.sp - 7552#64) 1056 ∗
           stackAt (s0.sp - 2400#64) allocHookStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm2304) (Entails.of_eq (by ac_rfl))
      · wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp1]
        simp only [arm64_norm] at hm2304 ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 216 ∗
           ((s0.sp - 2184#64) ↦₆₄ u40) ∗
           memRegion (s0.sp - 2176#64) 2080) ∗
          (memRegion (s0.sp - 7552#64) 1056 ∗
           stackAt (s0.sp - 2400#64) allocHookStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm2304) (Entails.of_eq (by ac_rfl))
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    have herr := v1_err_5940_placed (A := A) (F := F) (ext := ext) s0 s2 out (A.pool ∗ Rest)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2
    refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-- Cleanup at `+5860` when `s.sendingHdr = none`: deallocates cloned `auth.rootKey`, cloned
    `auth.macKey`, `ek`, and `dk`, returning `Err(StateDecode)`. -/
theorem v1_cleanup_sendingHdr_none_5860_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pa1 pa2 u8 u16 u32 u40 u72 u96 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5860#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx0_1 : s1.readReg64 .x0 = pa1)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = u8)
    (hx22_1 : s1.readReg64 .x22 = u72)
    (hx28_1 : s1.readReg64 .x28 = u32)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 24 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u72 pa1 ∗
        vecCapPtrDealloc A u96 pa2 ∗
        vecCapPtrDealloc A u8 u16 ∗
        vecCapPtrDealloc A u32 u40 ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v1_dealloc_ok_at_statesFromPb_placed hA
  simp only [rustDeallocSpec] at hdealloc
  have hm216 : memRegion (s0.sp - 2400#64) 176 ∗
      ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
      memRegion (s0.sp - 2400#64 + 192#64) 24 ⊢
      memRegion (s0.sp - 2400#64) 216 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (SpqrV1.Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (SpqrV1.Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have hm2080 : ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
      memRegion (s0.sp - 2400#64 + 240#64) 2064 ⊢
      memRegion (s0.sp - 2400#64 + 224#64) 2080 :=
    collapse_top <| collapse_step (SpqrV1.Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (SpqrV1.Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 5876#64)
    (P_mid :=
      memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      memRegion (s0.sp - 2400#64) 176 ∗
      ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
      memRegion (s0.sp - 2400#64 + 192#64) 24 ∗
      ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
      memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      vecCapPtrDealloc A u96 pa2 ∗
      vecCapPtrDealloc A u8 u16 ∗
      vecCapPtrDealloc A u32 u40 ∗
      A.pool ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = u8 ∧
      s2.readReg64 .x28 = u32 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
    change s1.pc = (blkPl_333).base + 5860#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5876#64) s1 _ _
    by_cases hc1 : (u72 == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply
      refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx28_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 5896#64)
      (P_mid :=
        memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
        stackAt (s0.sp - 2400#64) allocHookStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 24 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u8 u16 ∗
        vecCapPtrDealloc A u32 u40 ∗
        A.pool ∗
        Rest)
      (Q := fun s3 =>
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = u8 ∧
        s3.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s3 s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
      change s2.pc = (blkPl_333).base + 5876#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5896#64) s2 _ _
      by_cases hc2 : (u96 == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply
        refine EncoderFromPb.align_pre (by rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, hx28_3, htr3⟩
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 5916#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 216 ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          memRegion (s0.sp - 2400#64 + 224#64) 2080 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A u32 u40 ∗
          A.pool ∗
          Rest)
        (Q := fun s4 =>
          s4.sp = s0.sp - 2400#64 ∧
          s4.readReg64 .x19 = out ∧
          s4.readReg64 .x28 = u32 ∧
          TraceCalleeSaved s4 s0)
        ?_ ?_
      · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc3 ⊢
        change s3.pc = (blkPl_333).base + 5896#64 at hpc3
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5916#64) s3 _ _
        by_cases hc3 : (u8 == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine EncoderFromPb.align_pre ?_ ?_
          · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
            simp only [arm64_norm] at hm216 hm2080 ⊢
            refine Entails.trans (Entails.of_eq (show _ =
              (memRegion (s0.sp - 2400#64) 176 ∗
               ((s0.sp - 2224#64) ↦₆₄ u16) ∗
               ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
               memRegion (s0.sp - 2208#64) 24) ∗
              (((s0.sp - 2176#64) ↦₆₄ u32) ∗
               ((s0.sp - 2168#64) ↦₆₄ u96) ∗
               memRegion (s0.sp - 2160#64) 2064) ∗
              (memRegion (s0.sp - 7552#64) 1056 ∗
               stackAt (s0.sp - 2400#64) allocHookStack ∗
               ((s0.sp - 2184#64) ↦₆₄ u40) ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                vecCapPtrDealloc A u32 u40 ∗ A.pool ∗ Rest) by dsimp only [vecCapPtrDealloc]; ac_rfl)) ?_
            exact Entails.trans (sepConj_mono hm216 (sepConj_mono_left hm2080)) (Entails.of_eq (by dsimp only [vecCapPtrDealloc]; ac_rfl))
          · wp_done
        · wp_steps; wp_apply
          refine EncoderFromPb.align_pre ?_ ?_
          · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp3]
            simp only [arm64_norm] at hm216 hm2080 ⊢
            refine Entails.trans (Entails.of_eq (show _ =
              (memRegion (s0.sp - 2400#64) 176 ∗
               ((s0.sp - 2224#64) ↦₆₄ u16) ∗
               ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
               memRegion (s0.sp - 2208#64) 24) ∗
              (((s0.sp - 2176#64) ↦₆₄ u32) ∗
               ((s0.sp - 2168#64) ↦₆₄ u96) ∗
               memRegion (s0.sp - 2160#64) 2064) ∗
              (memRegion (s0.sp - 7552#64) 1056 ∗
               stackAt (s0.sp - 2400#64) allocHookStack ∗
               ((s0.sp - 2184#64) ↦₆₄ u40) ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
               vecCapPtrDealloc A u32 u40 ∗ A.pool ∗ Rest) by dsimp only [vecCapPtrDealloc]; ac_rfl)) ?_
            exact Entails.trans (sepConj_mono hm216 (sepConj_mono_left hm2080)) (Entails.of_eq (by dsimp only [vecCapPtrDealloc]; ac_rfl))
          · wp_done
      · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx28_4, htr4⟩
        exact v1_cleanup_dk_5916_placed (A := A) (F := F) hA s0 s4 out u32 u40 Rest
          hsp0_align hpc4 hrun4 hsp4 hx19_4 hx28_4 htr4

/-- Cleanup at `+4116` when `<PolyEncoder>::from_pb` returns `.error`:
    deallocates cloned `auth.rootKey`, cloned `auth.macKey`, `ek`, and `dk`,
    returning `Err(StateDecode)`. -/
theorem v1_cleanup_enc_err_4116_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pa1 pa2 u8 u16 u32 u40 u72 u96 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4116#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = u72)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx28_1 : s1.readReg64 .x28 = u32)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u72 pa1 ∗
        vecCapPtrDealloc A u96 pa2 ∗
        vecCapPtrDealloc A u8 u16 ∗
        vecCapPtrDealloc A u32 u40 ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v1_dealloc_ok_at_statesFromPb_placed hA
  simp only [rustDeallocSpec] at hdealloc
  have hm216 : memRegion (s0.sp - 2400#64) 176 ∗
      ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
      memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
      ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
      memRegion (s0.sp - 2400#64 + 208#64) 8 ⊢
      memRegion (s0.sp - 2400#64) 216 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (SpqrV1.Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (SpqrV1.Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (SpqrV1.Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have hm2080 : ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
      memRegion (s0.sp - 2400#64 + 240#64) 2064 ⊢
      memRegion (s0.sp - 2400#64 + 224#64) 2080 :=
    collapse_top <| collapse_step (SpqrV1.Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (SpqrV1.Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 4136#64)
    (P_mid :=
      memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      memRegion (s0.sp - 2400#64) 176 ∗
      ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
      memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
      ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
      memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
      ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
      memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      vecCapPtrDealloc A u96 pa2 ∗
      vecCapPtrDealloc A u8 u16 ∗
      vecCapPtrDealloc A u32 u40 ∗
      A.pool ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x26 = u8 ∧
      s2.readReg64 .x28 = u32 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
    change s1.pc = (blkPl_333).base + 4116#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4136#64) s1 _ _
    by_cases hc1 : (u72 == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply
      refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, hx28_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 4156#64)
      (P_mid :=
        memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
        stackAt (s0.sp - 2400#64) allocHookStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u8 u16 ∗
        vecCapPtrDealloc A u32 u40 ∗
        A.pool ∗
        Rest)
      (Q := fun s3 =>
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        s3.readReg64 .x26 = u8 ∧
        s3.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s3 s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
      change s2.pc = (blkPl_333).base + 4136#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4156#64) s2 _ _
      by_cases hc2 : (u96 == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply
        refine EncoderFromPb.align_pre (by rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, hx28_3, htr3⟩
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 5916#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 216 ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          memRegion (s0.sp - 2400#64 + 224#64) 2080 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A u32 u40 ∗
          A.pool ∗
          Rest)
        (Q := fun s4 =>
          s4.sp = s0.sp - 2400#64 ∧
          s4.readReg64 .x19 = out ∧
          s4.readReg64 .x28 = u32 ∧
          TraceCalleeSaved s4 s0)
        ?_ ?_
      · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc3 ⊢
        change s3.pc = (blkPl_333).base + 4156#64 at hpc3
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5916#64) s3 _ _
        by_cases hc3 : (u8 == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine EncoderFromPb.align_pre ?_ ?_
          · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
            simp only [arm64_norm] at hm216 hm2080 ⊢
            refine Entails.trans (Entails.of_eq (show _ =
              (memRegion (s0.sp - 2400#64) 176 ∗
               ((s0.sp - 2224#64) ↦₆₄ u16) ∗
               ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
               memRegion (s0.sp - 2208#64) 8 ∗
               ((s0.sp - 2200#64) ↦₆₄ pa1) ∗
               memRegion (s0.sp - 2192#64) 8) ∗
              (((s0.sp - 2176#64) ↦₆₄ u32) ∗
               ((s0.sp - 2168#64) ↦₆₄ u96) ∗
               memRegion (s0.sp - 2160#64) 2064) ∗
              (memRegion (s0.sp - 7552#64) 1056 ∗
               stackAt (s0.sp - 2400#64) allocHookStack ∗
               ((s0.sp - 2184#64) ↦₆₄ u40) ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                vecCapPtrDealloc A u32 u40 ∗ A.pool ∗ Rest) by dsimp only [vecCapPtrDealloc]; ac_rfl)) ?_
            exact Entails.trans (sepConj_mono hm216 (sepConj_mono_left hm2080)) (Entails.of_eq (by dsimp only [vecCapPtrDealloc]; ac_rfl))
          · wp_done
        · wp_steps; wp_apply
          refine EncoderFromPb.align_pre ?_ ?_
          · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp3]
            simp only [arm64_norm] at hm216 hm2080 ⊢
            refine Entails.trans (Entails.of_eq (show _ =
              (memRegion (s0.sp - 2400#64) 176 ∗
               ((s0.sp - 2224#64) ↦₆₄ u16) ∗
               ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
               memRegion (s0.sp - 2208#64) 8 ∗
               ((s0.sp - 2200#64) ↦₆₄ pa1) ∗
               memRegion (s0.sp - 2192#64) 8) ∗
              (((s0.sp - 2176#64) ↦₆₄ u32) ∗
               ((s0.sp - 2168#64) ↦₆₄ u96) ∗
               memRegion (s0.sp - 2160#64) 2064) ∗
              (memRegion (s0.sp - 7552#64) 1056 ∗
               stackAt (s0.sp - 2400#64) allocHookStack ∗
               ((s0.sp - 2184#64) ↦₆₄ u40) ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
               vecCapPtrDealloc A u32 u40 ∗ A.pool ∗ Rest) by dsimp only [vecCapPtrDealloc]; ac_rfl)) ?_
            exact Entails.trans (sepConj_mono hm216 (sepConj_mono_left hm2080)) (Entails.of_eq (by dsimp only [vecCapPtrDealloc]; ac_rfl))
          · wp_done
      · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx28_4, htr4⟩
        exact v1_cleanup_dk_5916_placed (A := A) (F := F) hA s0 s4 out u32 u40 Rest
          hsp0_align hpc4 hrun4 hsp4 hx19_4 hx28_4 htr4

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2cPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2cPlaced (
  v1_auth_from_pb_step2_8756_9804_placed
  v1_auth_from_pb_step3_9804_4016_placed
  v1_cleanup_dk_5916_placed
  v1_cleanup_sendingHdr_none_5860_placed
  v1_cleanup_enc_err_4116_placed
)

end CryptoVerification.SpqrV1.States.FromPb
