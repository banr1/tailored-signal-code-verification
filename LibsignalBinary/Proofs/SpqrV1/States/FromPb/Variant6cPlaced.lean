/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 6 (`HeaderReceived`, `+1464`, Block `333`) — Part C

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant6c.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6cPlaced

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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## 1. `SepWPp` OOM Panic Helpers (`v6hr_*`) -/

theorem v6hr_oom_11596_entails_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (target_pc : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11596#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf) := by
  have hpanic := fromPb_externAt?_handleError hA
  change s.pc = (blkPl_333).base + 11596#64 at hpc
  change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s P Q _
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
  unfold statesFromPbOnPanic
  exact Entails.pure_right
    (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) (entails_anyHeap _)

theorem v6hr_oom_11620_entails_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (target_pc : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11620#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf) := by
  have hpanic := fromPb_externAt?_handleError hA
  change s.pc = (blkPl_333).base + 11620#64 at hpc
  change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s P Q _
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
  unfold statesFromPbOnPanic
  exact Entails.pure_right
    (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) (entails_anyHeap _)

/-! ## 2. Cloning `Authenticator` Buffers (`+3796 -> +8812` and `+8812 -> +9852`) -/

/-- Clones `authPb.rootKey` at `+3796 -> +8812`:
stores `p2` at `[fsp + 208]`, `ep` at `[fsp + 128]`, `p0` at `[fsp + 144]`, `d116` at `[fsp + 200]`,
and `p1_new` at `[fsp + 192]`, producing `vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey`
and weakening the original buffer to `vecCapPtrDealloc A c1 p1` (or panicking on OOM via `+11596`). -/
theorem v6hr_clone_rootKey_3796_to_8812_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State)
    (out c0 p0 c1 p1 c2 p2 l2 ep c3 l3 w120 v128 v144 v192 v208 : BitVec 64)
    (d112 d116 d184 d200 : BitVec 32) (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3796#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = ep) (hx9_1 : s1.readReg64 .x9 = p0)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (_hx13_1 : s1.readReg64 .x13 = w120) (hx14_1 : s1.readReg64 .x14 = p2)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = c0)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 rootKey.length)
    (hx23_1 : s1.readReg64 .x23 = l3) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = l2) (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = c3) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8812#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 128#64) ↦₆₄ v128) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ v144) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₃₂ d200) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ v208) ∗
        vecU8Payload A c1 p1 rootKey ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        ∃ (p1_new : BitVec 64) (d184' : BitVec 32),
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184') ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗
            (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
            vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecCapPtrDealloc A c1 p1 ∗ A.pool ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = c0 ∧ sm.readReg64 .x21 = c2 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 rootKey.length ∧ sm.readReg64 .x23 = l3 ∧
          sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = l2 ∧ sm.readReg64 .x26 = p1 ∧
          sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have h128 : (s0.sp - 2400#64) + 128#64 = s0.sp - 2272#64 := by bv_omega
  have h144 : (s0.sp - 2400#64) + 144#64 = s0.sp - 2256#64 := by bv_omega
  have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
  have h192 : (s0.sp - 2400#64) + 192#64 = s0.sp - 2208#64 := by bv_omega
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  have h208 : (s0.sp - 2400#64) + 208#64 = s0.sp - 2192#64 := by bv_omega
  have hpure :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 128#64) ↦₆₄ v128) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ v144) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₃₂ d200) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ v208) ∗
        vecU8Payload A c1 p1 rootKey ∗ A.pool ∗ Rest =
      ⌜rootKey.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0#64⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((s0.sp - 2400#64) + 128#64) ↦₆₄ v128) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ v144) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₃₂ d200) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ v208) ∗
       (if c1 = 0#64 then emp
        else A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
          memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length)) ∗
       A.pool ∗ Rest) := by unfold vecU8Payload; ac_rfl
  rw [hpure]
  refine SepWPp.pure_left fun ⟨hr_le, hr_cap, _⟩ => ?_
  have hr_cases : rootKey = [] ∨ 0 < rootKey.length := by cases rootKey <;> simp
  rcases hr_cases with rfl | hr_pos
  · simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx22_1 ⊢
    refine v6hr_sepWPp_seq_clean
      (mid := lsmpl.base 333 + 8804#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A c1 p1 ∗ A.pool ∗ Rest)
      (Q_regs := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = c0 ∧ sm.readReg64 .x21 = c2 ∧
        sm.readReg64 .x22 = 0#64 ∧ sm.readReg64 .x23 = l3 ∧ sm.readReg64 .x24 = c1 ∧
        sm.readReg64 .x25 = l2 ∧ sm.readReg64 .x26 = p1 ∧ sm.readReg64 .x28 = c3 ∧
        TraceCalleeSaved sm s0) ?_ ?_
    · change s1.pc = (blkPl_333).base + 3796#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 8804#64) s1 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h128, h144, h184, h192, h200, h208]
        have hite := v6hr_ite_nil_entails_vecCapPtrDealloc A c1 p1
        refine Entails.trans
          (Entails.of_eq (show _ =
            (if c1 = 0#64 then emp
             else A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ ([] : List (BitVec 8))) ∗
               memRegion (p1 + 0#64) (c1.toNat - 0)) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             ((s0.sp - 2272#64) ↦₆₄ ep) ∗ ((s0.sp - 2256#64) ↦₆₄ p0) ∗
             ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
             ((s0.sp - 2200#64) ↦₃₂ d116) ∗ ((s0.sp - 2192#64) ↦₆₄ p2) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hite) (Entails.of_eq (by ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx11_2, hx12_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx28_2, htr2⟩
      apply SepWPp.of_sepWP_ret
      refine v6hr_sepWP_exists_post 1#64 (v6hr_sepWP_exists_post d184 ?_)
      change s2.pc = (blkPl_333).base + 8804#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 8812#64) s2 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h192]
        have hv0 := vecU8Payload_zero A
        refine Entails.trans
          (Entails.of_eq (show _ =
            emp ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
             (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ 1#64) ∗
             (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
             vecCapPtrDealloc A c1 p1 ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hv0) (Entails.of_eq (by ac_rfl))
      · wp_done
  · have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hc1_ne : c1 ≠ 0#64 := cap_ne_zero_of_pos hr_pos hr_le
    have hr_lt63 : rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : rootKey.length < 2 ^ 64 := by omega
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hr_toNat : (BitVec.ofNat 64 rootKey.length).toNat = rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hlay : LayoutOk rootKey.length 1 := ⟨hr_pos, hpow1, by omega⟩
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
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
    have hoom_step := v6hr_oom_11596_entails_placed hA s0
    simp only [hc1_ne, ↓reduceIte, sepConj_assoc]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    change s1.pc = (blkPl_333).base + 3796#64 at hpc1
    change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8812#64) s1 _ _ _
    apply SepWPp.of_sepWP (mid := (blkPl_333).base + 3840#64)
    wp_steps; wp_apply; wp_steps
    nth_rw 1 [← hsp1]; nth_rw 1 [← h_1]
    wp_call halloc (rootKey.length, 1); apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte]
      rw [v6hr_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      have htr_sf1 : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htrace]; simp only [wp_norm, arm64_norm, *]
      refine v6hr_sepWPp_seq_clean (mid := (blkPl_333).base + 11596#64)
        (P_mid :=
          A.pool ∗ stackAt sf.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056 ∗
            ((s0.sp - 2272#64) ↦₆₄ ep) ∗ ((s0.sp - 2256#64) ↦₆₄ p0) ∗
            ((s0.sp - 2216#64) ↦₃₂ d112) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
            ((s0.sp - 2200#64) ↦₃₂ d116) ∗ ((s0.sp - 2192#64) ↦₆₄ p2) ∗
            A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
            memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length) ∗ Rest)
        (Q_regs := fun sm => sm.trace = s0.trace ++ [allocFailedEvent]) ?_ ?_
      · wp_steps; wp_done
      · intro s3 hpc3 hrun3 htr3; exact hoom_step s3 _ _ _ hpc3 hrun3 htr3
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
      rw [v6hr_pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      have hsp_eq : sf_1.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      refine v6hr_sepWP_exists_post (sf_1.readReg64 (Reg.gpr 0#5)) (v6hr_sepWP_exists_post d112 ?_)
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h128, h144, h184, h192, h200, h208]
        have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp_eq] at hst
        have hv_new := vecU8Payload_pos A (sf_1.readReg64 (Reg.gpr 0#5)) rootKey hr_pos hr_lt63 hoom
        have hv_old := v6hr_live_bytes_entails_vecCapPtrDealloc A c1 p1 rootKey hc1_ne hr_le
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt sf_1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (A.live (sf_1.readReg64 (Reg.gpr 0#5)) rootKey.length 1 ∗ (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ rootKey)) ∗
            (A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
              memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length)) ∗
            (((s0.sp - 2272#64) ↦₆₄ ep) ∗ ((s0.sp - 2256#64) ↦₆₄ p0) ∗
             ((s0.sp - 2216#64) ↦₃₂ d112) ∗ ((s0.sp - 2208#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
             ((s0.sp - 2200#64) ↦₃₂ d116) ∗ ((s0.sp - 2192#64) ↦₆₄ p2) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono hst (sepConj_mono hv_new (sepConj_mono_left hv_old))) ?_
        exact Entails.of_eq (by ac_rfl)
      · wp_done

/-- Clones `authPb.macKey` at `+8812 -> +9852`:
saves `c0` (`x20`) in `x27`, stores `l2` at `[fsp + 216]` and `p2_new` at `[fsp + 136]`,
producing `vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey`
and weakening the original buffer to `vecCapPtrDealloc A c2 p2` (or panicking on OOM via `+11620`). -/
theorem v6hr_clone_macKey_8812_to_9852_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State)
    (out c0 c1 p1 l1 c2 p2 c3 l3 v136 v216 : BitVec 64)
    (d112 d116 : BitVec 32) (macKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 8812#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = c0)
    (hx21_1 : s1.readReg64 .x21 = c2) (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = l3) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 macKey.length)
    (hx26_1 : s1.readReg64 .x26 = p1) (hx28_1 : s1.readReg64 .x28 = c3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9852#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗ (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗
        vecU8Payload A c2 p2 macKey ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        ∃ p2_new : BitVec 64,
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗
            (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
            vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = c2 ∧ sm.readReg64 .x22 = l1 ∧
          sm.readReg64 .x23 = l3 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x26 = p1 ∧
          sm.readReg64 .x27 = c0 ∧ sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have h136 : (s0.sp - 2400#64) + 136#64 = s0.sp - 2264#64 := by bv_omega
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  have h208 : (s0.sp - 2400#64) + 208#64 = s0.sp - 2192#64 := by bv_omega
  have h216 : (s0.sp - 2400#64) + 216#64 = s0.sp - 2184#64 := by bv_omega
  have hpure :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗ (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗
        vecU8Payload A c2 p2 macKey ∗ A.pool ∗ Rest =
      ⌜macKey.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0#64⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗ (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗
       (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗
       (if c2 = 0#64 then emp
        else A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
          memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length)) ∗
       A.pool ∗ Rest) := by unfold vecU8Payload; ac_rfl
  rw [hpure]
  refine SepWPp.pure_left fun ⟨hm_le, hm_cap, _⟩ => ?_
  have hm_cases : macKey = [] ∨ 0 < macKey.length := by cases macKey <;> simp
  rcases hm_cases with rfl | hm_pos
  · simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx25_1 ⊢
    refine v6hr_sepWPp_seq_clean
      (mid := lsmpl.base 333 + 9844#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗ (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ 0#64) ∗
        vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest)
      (Q_regs := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = c2 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = l3 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x26 = p1 ∧
        sm.readReg64 .x27 = c0 ∧ sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0) ?_ ?_
    · change s1.pc = (blkPl_333).base + 8812#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9844#64) s1 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h136, h200, h208, h216]
        have hite := v6hr_ite_nil_entails_vecCapPtrDealloc A c2 p2
        refine Entails.trans
          (Entails.of_eq (show _ =
            (if c2 = 0#64 then emp
             else A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ ([] : List (BitVec 8))) ∗
               memRegion (p2 + 0#64) (c2.toNat - 0)) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2200#64) ↦₃₂ d116) ∗
             ((s0.sp - 2192#64) ↦₆₄ p2) ∗ ((s0.sp - 2184#64) ↦₆₄ 0#64) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hite) (Entails.of_eq (by ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx11_2, hx12_2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, hx28_2, htr2⟩
      apply SepWPp.of_sepWP_ret
      refine v6hr_sepWP_exists_post 1#64 ?_
      change s2.pc = (blkPl_333).base + 9844#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9852#64) s2 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h136]
        have hv0 := vecU8Payload_zero A
        refine Entails.trans
          (Entails.of_eq (show _ =
            emp ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             ((s0.sp - 2264#64) ↦₆₄ 1#64) ∗ (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗
             (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ 0#64) ∗
             vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hv0) (Entails.of_eq (by ac_rfl))
      · wp_done
  · have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hc2_ne : c2 ≠ 0#64 := cap_ne_zero_of_pos hm_pos hm_le
    have hm_lt63 : macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : macKey.length < 2 ^ 64 := by omega
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false :=
      ofNat_beq_zero_false hm_pos hm_lt64
    have hm_toNat : (BitVec.ofNat 64 macKey.length).toNat = macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hlay : LayoutOk macKey.length 1 := ⟨hm_pos, hpow1, by omega⟩
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
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
    have hoom_step := v6hr_oom_11620_entails_placed hA s0
    simp only [hc2_ne, ↓reduceIte, sepConj_assoc]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    change s1.pc = (blkPl_333).base + 8812#64 at hpc1
    change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9852#64) s1 _ _ _
    apply SepWPp.of_sepWP (mid := (blkPl_333).base + 8844#64)
    wp_steps; wp_apply; wp_steps
    nth_rw 1 [← hsp1]; nth_rw 1 [← h_1]
    wp_call halloc (macKey.length, 1); apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte]
      rw [v6hr_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      have htr_sf1 : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htrace]; simp only [wp_norm, arm64_norm, *]
      refine v6hr_sepWPp_seq_clean (mid := (blkPl_333).base + 11620#64)
        (P_mid :=
          A.pool ∗ stackAt sf.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056 ∗
            ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2200#64) ↦₃₂ d116) ∗
            ((s0.sp - 2192#64) ↦₆₄ p2) ∗
            ((s0.sp - 2184#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
            A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
            memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length) ∗ Rest)
        (Q_regs := fun sm => sm.trace = s0.trace ++ [allocFailedEvent]) ?_ ?_
      · wp_steps; wp_done
      · intro s3 hpc3 hrun3 htr3; exact hoom_step s3 _ _ _ hpc3 hrun3 htr3
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
      rw [v6hr_pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      have hsp_eq : sf_1.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      refine v6hr_sepWP_exists_post (sf_1.readReg64 (Reg.gpr 0#5)) ?_
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h136, h200, h208, h216]
        have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp_eq] at hst
        have hv_new := vecU8Payload_pos A (sf_1.readReg64 (Reg.gpr 0#5)) macKey hm_pos hm_lt63 hoom
        have hv_old := v6hr_live_bytes_entails_vecCapPtrDealloc A c2 p2 macKey hc2_ne hm_le
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt sf_1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (A.live (sf_1.readReg64 (Reg.gpr 0#5)) macKey.length 1 ∗ (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ macKey)) ∗
            (A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
              memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length)) ∗
            (((s0.sp - 2264#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
             ((s0.sp - 2200#64) ↦₃₂ d116) ∗ ((s0.sp - 2192#64) ↦₆₄ p2) ∗
             ((s0.sp - 2184#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono hst (sepConj_mono hv_new (sepConj_mono_left hv_old))) ?_
        exact Entails.of_eq (by ac_rfl)
      · wp_done

/-! ## 3. Deallocation Helpers (`+9852 -> +9936`, `+10416 -> +10396`, `+10492 -> +10396`) -/

theorem v6hr_dealloc_auth_9852_to_9936_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State)
    (out c0 c1 p1 p1_new l1 c2 p2 c3 l3 : BitVec 64)
    (d112 d116 : BitVec 32) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9852#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = l1) (hx23_1 : s1.readReg64 .x23 = l3)
    (hx24_1 : s1.readReg64 .x24 = c1) (hx26_1 : s1.readReg64 .x26 = p1)
    (hx27_1 : s1.readReg64 .x27 = c0) (hx28_1 : s1.readReg64 .x28 = c3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9936#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
          A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x23 = l3 ∧
        sm.readReg64 .x24 = p1_new >>> 8 ∧ sm.readReg64 .x25 = p1_new ∧
        sm.readReg64 .x26 = l1 ∧ sm.readReg64 .x27 = c0 ∧
        sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have h192 : (s0.sp - 2400#64) + 192#64 = s0.sp - 2208#64 := by bv_omega
  have h208 : (s0.sp - 2400#64) + 208#64 = s0.sp - 2192#64 := by bv_omega
  have hw11 : (d112.zeroExtend 64).setWidth 32 = d112 := by bv_kernel
  have hw12 : (d116.zeroExtend 64).setWidth 32 = d116 := by bv_kernel
  have hdealloc := v9_sub_ok_dealloc_placed hA
  have hstep1 :
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 9892#64) s1
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
          vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest)
        (fun s2 P2 =>
          (P2 ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
            vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest) ∧
          s2.sp = s0.sp - 2400#64 ∧
          s2.readReg64 .x11 = d112.zeroExtend 64 ∧ s2.readReg64 .x12 = d116.zeroExtend 64 ∧
          s2.readReg64 .x19 = out ∧ s2.readReg64 .x21 = c2 ∧ s2.readReg64 .x22 = l1 ∧
          s2.readReg64 .x23 = l3 ∧ s2.readReg64 .x25 = p1_new ∧ s2.readReg64 .x27 = c0 ∧
          s2.readReg64 .x28 = c3 ∧ TraceCalleeSaved s2 s0) := by
    by_cases hc1 : (c1 == 0#64) = true
    · have hc1_eq : c1 = 0#64 := of_decide_eq_true hc1
      subst hc1_eq; nth_rw 1 [vecCapPtrDealloc]
      simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
      change s1.pc = (blkPl_333).base + 9852#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9892#64) s1 _ _
      wp_steps; wp_done
    · simp only [Bool.not_eq_true] at hc1
      nth_rw 1 [vecCapPtrDealloc]
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      simp only [sepConj_assoc]
      change s1.pc = (blkPl_333).base + 9852#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9892#64) s1 _ _
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h192, h208]
        have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp1] at hst
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2208#64) ↦₆₄ p1_new) ∗ ((s0.sp - 2192#64) ↦₆₄ p2) ∗
             vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl))
      · wp_done
  refine SepWP.seq hstep1 ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx11_2, hx12_2, hx19_2, hx21_2, hx22_2, hx23_2, hx25_2, hx27_2, hx28_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  by_cases hc2 : (c2 == 0#64) = true
  · have hc2_eq : c2 = 0#64 := of_decide_eq_true hc2
    subst hc2_eq; nth_rw 1 [vecCapPtrDealloc]
    simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
    change s2.pc = (blkPl_333).base + 9892#64 at hpc2
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9936#64) s2 _ _
    wp_steps; wp_done
  · simp only [Bool.not_eq_true] at hc2
    nth_rw 1 [vecCapPtrDealloc]
    simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWP.weaken_pre
      (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    change s2.pc = (blkPl_333).base + 9892#64 at hpc2
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9936#64) s2 _ _
    wp_steps; wp_apply; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [h192, h208]
      have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
      have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
      rw [haddr] at hst; nth_rw 1 [← hsp2] at hst
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt s2.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          (((s0.sp - 2208#64) ↦₆₄ p1_new) ∗ ((s0.sp - 2192#64) ↦₆₄ p2) ∗
           A.pool ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl))
    · wp_done

theorem v6hr_dealloc_c0_10456_to_10396_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State) (out c0 p0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10456#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗ vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have h144 : (s0.sp - 2400#64) + 144#64 = s0.sp - 2256#64 := by bv_omega
  have hdealloc := v9_sub_ok_dealloc_placed hA
  by_cases hc0 : (c0 == 0#64) = true
  · have hc0_eq : c0 = 0#64 := of_decide_eq_true hc0
    subst hc0_eq; nth_rw 1 [vecCapPtrDealloc]
    simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 10536#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗ A.pool ∗ Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = out ∧ TraceCalleeSaved s2 s0) ?_ ?_
    · change s1.pc = (blkPl_333).base + 10456#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10536#64) s1 _ _
      wp_steps; wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
      change s2.pc = (blkPl_333).base + 10536#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10396#64) s2 _ _
      wp_steps; wp_done
  · simp only [Bool.not_eq_true] at hc0
    nth_rw 1 [vecCapPtrDealloc]
    simp only [hc0, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWP.weaken_pre
      (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    change s1.pc = (blkPl_333).base + 10456#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10396#64) s1 _ _
    wp_steps; wp_apply; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [h144]
      have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
      have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
      rw [haddr] at hst; nth_rw 1 [← hsp1] at hst
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          (((s0.sp - 2256#64) ↦₆₄ p0) ∗ A.pool ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl))
    · wp_done

theorem v6hr_dealloc_c0_10532_to_10396_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State) (out c0 p0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10532#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗ vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have h144 : (s0.sp - 2400#64) + 144#64 = s0.sp - 2256#64 := by bv_omega
  have hdealloc := v9_sub_ok_dealloc_placed hA
  by_cases hc0 : (c0 == 0#64) = true
  · have hc0_eq : c0 = 0#64 := of_decide_eq_true hc0
    subst hc0_eq; nth_rw 1 [vecCapPtrDealloc]
    simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
    change s1.pc = (blkPl_333).base + 10532#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10396#64) s1 _ _
    wp_steps; wp_done
  · simp only [Bool.not_eq_true] at hc0
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 10460#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗ vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x27 = c0 ∧ TraceCalleeSaved s2 s0) ?_ ?_
    · change s1.pc = (blkPl_333).base + 10532#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10460#64) s1 _ _
      wp_steps; wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx27_2, htr2⟩
      nth_rw 1 [vecCapPtrDealloc]
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      simp only [sepConj_assoc]
      change s2.pc = (blkPl_333).base + 10460#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10396#64) s2 _ _
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h144]
        have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp2] at hst
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s2.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2256#64) ↦₆₄ p0) ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl))
      · wp_done

theorem v6hr_dealloc_cloned_10416_to_10396_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State)
    (out c0 p0 l1 p1_new l2 p2_new : BitVec 64)
    (rootKey macKey hdr : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10416#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1) (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        vecU8Payload A l1 p1_new rootKey ∗ vecU8Payload A l2 p2_new macKey ∗
        vecU8Payload A c0 p0 hdr ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have h136 : (s0.sp - 2400#64) + 136#64 = s0.sp - 2264#64 := by bv_omega
  have h144 : (s0.sp - 2400#64) + 144#64 = s0.sp - 2256#64 := by bv_omega
  have h216 : (s0.sp - 2400#64) + 216#64 = s0.sp - 2184#64 := by bv_omega
  have hdealloc := v9_sub_ok_dealloc_placed hA
  have hv1 := v6hr_vecU8Payload_entails_vecCapPtrDealloc A l1 p1_new rootKey
  have hv2 := v6hr_vecU8Payload_entails_vecCapPtrDealloc A l2 p2_new macKey
  have hv0 := v6hr_vecU8Payload_entails_vecCapPtrDealloc A c0 p0 hdr
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono_left hv0))))))) ?_
  have hstep1 :
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10436#64) s1
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
          vecCapPtrDealloc A l1 p1_new ∗ vecCapPtrDealloc A l2 p2_new ∗
          vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest)
        (fun s2 P2 =>
          (P2 ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
            vecCapPtrDealloc A l2 p2_new ∗ vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest) ∧
          s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = out ∧
          s2.readReg64 .x27 = c0 ∧ TraceCalleeSaved s2 s0) := by
    by_cases hl1 : (l1 == 0#64) = true
    · have hl1_eq : l1 = 0#64 := of_decide_eq_true hl1
      subst hl1_eq; nth_rw 1 [vecCapPtrDealloc]
      simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
      change s1.pc = (blkPl_333).base + 10416#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10436#64) s1 _ _
      wp_steps; wp_done
    · simp only [Bool.not_eq_true] at hl1
      nth_rw 1 [vecCapPtrDealloc]
      simp only [hl1, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      simp only [sepConj_assoc]
      change s1.pc = (blkPl_333).base + 10416#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10436#64) s1 _ _
      wp_steps; wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h136, h144, h216]
        have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp1] at hst
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2264#64) ↦₆₄ p2_new) ∗ ((s0.sp - 2256#64) ↦₆₄ p0) ∗
             ((s0.sp - 2184#64) ↦₆₄ l2) ∗ vecCapPtrDealloc A l2 p2_new ∗
             vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl))
      · wp_done
  refine SepWP.seq hstep1 ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx19_2, hx27_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hstep2 :
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10456#64) s2
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
          vecCapPtrDealloc A l2 p2_new ∗ vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest)
        (fun s3 P3 =>
          (P3 ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            vecCapPtrDealloc A c0 p0 ∗ A.pool ∗
            ((((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
             (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗ Rest)) ∧
          s3.sp = s0.sp - 2400#64 ∧ s3.readReg64 .x19 = out ∧
          s3.readReg64 .x27 = c0 ∧ TraceCalleeSaved s3 s0) := by
    by_cases hl2 : (l2 == 0#64) = true
    · have hl2_eq : l2 = 0#64 := of_decide_eq_true hl2
      subst hl2_eq; nth_rw 1 [vecCapPtrDealloc]
      simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
      change s2.pc = (blkPl_333).base + 10436#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10456#64) s2 _ _
      wp_steps
      refine EncoderFromPb.align_pre (by rw [h216]; exact Entails.of_eq (by ac_rfl)) ?_
      wp_done
    · simp only [Bool.not_eq_true] at hl2
      nth_rw 1 [vecCapPtrDealloc]
      simp only [hl2, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      simp only [sepConj_assoc]
      change s2.pc = (blkPl_333).base + 10436#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10456#64) s2 _ _
      wp_steps; wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h136, h144, h216]
        have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp2] at hst
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s2.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2256#64) ↦₆₄ p0) ∗ vecCapPtrDealloc A c0 p0 ∗ A.pool ∗
             (((s0.sp - 2264#64) ↦₆₄ p2_new) ∗ ((s0.sp - 2184#64) ↦₆₄ l2) ∗ Rest)) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl))
      · wp_done
  refine SepWP.seq hstep2 ?_
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx27_3, htr3⟩
  refine SepWP.weaken_pre hP3 ?_
  exact SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
    (v6hr_dealloc_c0_10456_to_10396_placed hA s0 s3 out c0 p0 _
      hsp0_align hpc3 hrun3 hsp3 hx19_3 hx27_3 htr3)

theorem v6hr_dealloc_cloned_10492_to_10396_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State)
    (out c0 p0 l1 p1_new l2 p2_new : BitVec 64)
    (rootKey macKey hdr : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10492#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1) (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        vecU8Payload A l1 p1_new rootKey ∗ vecU8Payload A l2 p2_new macKey ∗
        vecU8Payload A c0 p0 hdr ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have h136 : (s0.sp - 2400#64) + 136#64 = s0.sp - 2264#64 := by bv_omega
  have h144 : (s0.sp - 2400#64) + 144#64 = s0.sp - 2256#64 := by bv_omega
  have h216 : (s0.sp - 2400#64) + 216#64 = s0.sp - 2184#64 := by bv_omega
  have hdealloc := v9_sub_ok_dealloc_placed hA
  have hv1 := v6hr_vecU8Payload_entails_vecCapPtrDealloc A l1 p1_new rootKey
  have hv2 := v6hr_vecU8Payload_entails_vecCapPtrDealloc A l2 p2_new macKey
  have hv0 := v6hr_vecU8Payload_entails_vecCapPtrDealloc A c0 p0 hdr
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono_left hv0))))))) ?_
  have hstep1 :
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10512#64) s1
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
          vecCapPtrDealloc A l1 p1_new ∗ vecCapPtrDealloc A l2 p2_new ∗
          vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest)
        (fun s2 P2 =>
          (P2 ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
            vecCapPtrDealloc A l2 p2_new ∗ vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest) ∧
          s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = out ∧
          s2.readReg64 .x27 = c0 ∧ TraceCalleeSaved s2 s0) := by
    by_cases hl1 : (l1 == 0#64) = true
    · have hl1_eq : l1 = 0#64 := of_decide_eq_true hl1
      subst hl1_eq; nth_rw 1 [vecCapPtrDealloc]
      simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
      change s1.pc = (blkPl_333).base + 10492#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10512#64) s1 _ _
      wp_steps; wp_done
    · simp only [Bool.not_eq_true] at hl1
      nth_rw 1 [vecCapPtrDealloc]
      simp only [hl1, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      simp only [sepConj_assoc]
      change s1.pc = (blkPl_333).base + 10492#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10512#64) s1 _ _
      wp_steps; wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h136, h144, h216]
        have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp1] at hst
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2264#64) ↦₆₄ p2_new) ∗ ((s0.sp - 2256#64) ↦₆₄ p0) ∗
             ((s0.sp - 2184#64) ↦₆₄ l2) ∗ vecCapPtrDealloc A l2 p2_new ∗
             vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl))
      · wp_done
  refine SepWP.seq hstep1 ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx19_2, hx27_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hstep2 :
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10532#64) s2
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
          vecCapPtrDealloc A l2 p2_new ∗ vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest)
        (fun s3 P3 =>
          (P3 ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            vecCapPtrDealloc A c0 p0 ∗ A.pool ∗
            ((((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
             (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗ Rest)) ∧
          s3.sp = s0.sp - 2400#64 ∧ s3.readReg64 .x19 = out ∧
          s3.readReg64 .x27 = c0 ∧ TraceCalleeSaved s3 s0) := by
    by_cases hl2 : (l2 == 0#64) = true
    · have hl2_eq : l2 = 0#64 := of_decide_eq_true hl2
      subst hl2_eq; nth_rw 1 [vecCapPtrDealloc]
      simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
      change s2.pc = (blkPl_333).base + 10512#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10532#64) s2 _ _
      wp_steps
      refine EncoderFromPb.align_pre (by rw [h216]; exact Entails.of_eq (by ac_rfl)) ?_
      wp_done
    · simp only [Bool.not_eq_true] at hl2
      nth_rw 1 [vecCapPtrDealloc]
      simp only [hl2, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      simp only [sepConj_assoc]
      change s2.pc = (blkPl_333).base + 10512#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10532#64) s2 _ _
      wp_steps; wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h136, h144, h216]
        have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp2] at hst
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s2.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2256#64) ↦₆₄ p0) ∗ vecCapPtrDealloc A c0 p0 ∗ A.pool ∗
             (((s0.sp - 2264#64) ↦₆₄ p2_new) ∗ ((s0.sp - 2184#64) ↦₆₄ l2) ∗ Rest)) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl))
      · wp_done
  refine SepWP.seq hstep2 ?_
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx27_3, htr3⟩
  refine SepWP.weaken_pre hP3 ?_
  exact SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
    (v6hr_dealloc_c0_10532_to_10396_placed hA s0 s3 out c0 p0 _
      hsp0_align hpc3 hrun3 hsp3 hx19_3 hx27_3 htr3)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6cPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6cPlaced (
  v6hr_oom_11596_entails_placed
  v6hr_oom_11620_entails_placed
  v6hr_clone_rootKey_3796_to_8812_placed
  v6hr_clone_macKey_8812_to_9852_placed
  v6hr_dealloc_auth_9852_to_9936_placed
  v6hr_dealloc_c0_10456_to_10396_placed
  v6hr_dealloc_c0_10532_to_10396_placed
  v6hr_dealloc_cloned_10416_to_10396_placed
  v6hr_dealloc_cloned_10492_to_10396_placed
)

end CryptoVerification.SpqrV1.States.FromPb
