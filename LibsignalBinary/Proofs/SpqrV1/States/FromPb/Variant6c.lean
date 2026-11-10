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
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 6 (`HeaderReceived`, `+1464`) — Part C
Cloning (`+3796 -> +8812 -> +9852`) and deallocation (`+9852 -> +9936`, `+10416`, `+10492`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.defProp false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff stubOff_rust_no_alloc_shim stubOff_rust_alloc
  stubOff_rust_dealloc stubOff_memcpy stubOff_handle_error

/-! ## 1. `SepWPp` & `vecU8Payload` Helpers (`v6hr_*`) -/

theorem v6hr_sepWPp_seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

theorem v6hr_sepWP_exists_post {α : Type} {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {Q : α → State → SepProp → Prop} (a : α)
    (h : SepWP prog target s P (Q a)) :
    SepWP prog target s P (fun sm Pm => ∃ x : α, Q x sm Pm) :=
  SepWP.mono h fun _ _ _ _ hq => ⟨a, hq⟩

theorem v6hr_pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

theorem v6hr_live_bytes_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64)
    (bs : List (BitVec 8)) (hc : c ≠ 0#64) (hle : bs.length ≤ c.toNat) :
    A.live p c.toNat 1 ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length) ⊢
      vecCapPtrDealloc A c p := by
  unfold vecCapPtrDealloc
  have hcf : (c == 0#64) = false := beq_false_of_ne hc
  simp only [hcf, Bool.false_eq_true, ↓reduceIte]
  apply sepConj_mono_right
  have h1 := ProofLib.pointsToBytes_entails_memRegion p bs
  have hadd : bs.length + (c.toNat - bs.length) = c.toNat := Nat.add_sub_of_le hle
  have h2 : memRegion p bs.length ∗ memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length) =
      memRegion p c.toNat := by
    rw [← ProofLib.memRegion_split' (b := p) (n := bs.length) (k := c.toNat - bs.length)
      (b' := p + BitVec.ofNat 64 bs.length) hadd.symm rfl (by omega)]
  rw [← h2]; exact sepConj_mono_left h1

theorem v6hr_ite_nil_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64) :
    (if c = 0#64 then emp
     else A.live p c.toNat 1 ∗ (p ↦ₛ ([] : List (BitVec 8))) ∗
       memRegion (p + 0#64) (c.toNat - 0)) ⊢
      vecCapPtrDealloc A c p := by
  unfold vecCapPtrDealloc
  by_cases hc : c = 0#64
  · subst hc; simp only [beq_self_eq_true, ↓reduceIte]; exact Entails.refl _
  · have hcf : (c == 0#64) = false := beq_false_of_ne hc
    simp only [hc, hcf, Bool.false_eq_true, ↓reduceIte,
      ProofLib.pointsToBytes_nil, emp_sepConj, BitVec.add_zero, Nat.sub_zero]
    exact Entails.refl _

theorem v6hr_vecU8Payload_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Payload A c p bs ⊢ vecCapPtrDealloc A c p := by
  unfold vecU8Payload
  apply Entails.pure_left; intro ⟨hle, _, _⟩
  by_cases hc : c = 0#64
  · subst hc; simp only [↓reduceIte]; unfold vecCapPtrDealloc; simp only [beq_self_eq_true, ↓reduceIte]; exact Entails.refl _
  · simp only [hc, ↓reduceIte]; exact v6hr_live_bytes_entails_vecCapPtrDealloc A c p bs hc hle

theorem v6hr_oom_11596_entails
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (target_pc : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11596#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s P Q
      (fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf) := by
  have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))) (by rw [hfn, stubOff_handle_error])
  states_from_pb_fetches_range b (Rust.withPanics ext) 11596 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpanic hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error")))
  wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
  unfold statesFromPbOnPanic
  exact Entails.pure_right
    (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) (entails_anyHeap _)

theorem v6hr_oom_11620_entails
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (target_pc : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11620#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s P Q
      (fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf) := by
  have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))) (by rw [hfn, stubOff_handle_error])
  states_from_pb_fetches_range b (Rust.withPanics ext) 11620 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpanic hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error")))
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
theorem v6hr_clone_rootKey_3796_to_8812_gen
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hshim_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec)
    (halloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hmc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withStack sessionMemcpyRegionSpec allocHookStack))
    (s0 s1 : State) (out c0 p0 c1 p1 c2 p2 l2 ep c3 l3 w120 v128 v144 v192 v208 : BitVec 64)
    (d112 d116 d184 d200 : BitVec 32) (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3796#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = ep) (hx9_1 : s1.readReg64 .x9 = p0)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64) (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (_hx13_1 : s1.readReg64 .x13 = w120) (hx14_1 : s1.readReg64 .x14 = p2)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = c0) (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 rootKey.length)
    (hx23_1 : s1.readReg64 .x23 = l3) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = l2) (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = c3) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8812#64) s1
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
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8804#64)
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
    · states_from_pb_fetches_range b (Rust.withPanics ext) 3796 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps
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
      states_from_pb_fetches_range b (Rust.withPanics ext) 8804 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps
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
    have hshim := sub_ok_at_of_fnAddr hshim_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) (by simp only [arm64_norm])
    have halloc := sub_ok_at_of_fnAddr halloc_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc")) (by simp only [arm64_norm])
    have hmc := sub_ok_at_of_fnAddr hmc_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy")) (by simp only [arm64_norm])
    have hoom_step := @v6hr_oom_11596_entails b ext s0
    simp only [hc1_ne, ↓reduceIte, sepConj_assoc]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    states_from_pb_fetches_range b (Rust.withPanics ext) 3796 76
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
      at hshim halloc hmc hoom_step hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 3840#64)
    wp_steps; wp_apply; wp_steps
    nth_rw 1 [← hsp1]; nth_rw 1 [← h_1]
    wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte]
      rw [v6hr_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      have htr_sf1 : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htrace]; simp only [wp_norm, arm64_norm, *]
      refine v6hr_sepWPp_seq_clean (mid := entry + 11596#64)
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
      have hsp_eq : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      refine v6hr_sepWP_exists_post (sf_1.readReg64 (Reg.gpr 0#5)) (v6hr_sepWP_exists_post d112 ?_)
      wp_steps
      have hsp_eq_sf : sf_1.sp = sf.sp := by simp only [wp_norm, arm64_norm, *]
      wp_simp_pre [← hsp_eq_sf]; wp_apply; wp_simp_pre [hsp_eq_sf]; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h128, h144, h184, h192, h200, h208]
        have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp_eq] at hst
        have hv_new := vecU8Payload_pos A (sf_1.readReg64 (Reg.gpr 0#5)) rootKey hr_pos hr_lt63 hoom
        have hv_old := v6hr_live_bytes_entails_vecCapPtrDealloc A c1 p1 rootKey hc1_ne hr_le
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt sf.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
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

def v6hr_clone_rootKey_3796_to_8812 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :=
  v6hr_clone_rootKey_3796_to_8812_gen hA.shim hA.alloc
    (subroutine_ok_withStack_of_subroutine_ok hA.session_memcpy_region allocHookStack)

/-- Clones `authPb.macKey` at `+8812 -> +9852`:
saves `c0` (`x20`) in `x27`, stores `l2` at `[fsp + 216]` and `p2_new` at `[fsp + 136]`,
producing `vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey`
and weakening the original buffer to `vecCapPtrDealloc A c2 p2` (or panicking on OOM via `+11620`). -/
theorem v6hr_clone_macKey_8812_to_9852_gen
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hshim_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec)
    (halloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hmc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withStack sessionMemcpyRegionSpec allocHookStack))
    (s0 s1 : State) (out c0 c1 p1 l1 c2 p2 c3 l3 v136 v216 : BitVec 64)
    (d112 d116 : BitVec 32) (macKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8812#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64) (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = c0)
    (hx21_1 : s1.readReg64 .x21 = c2) (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = l3) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 macKey.length)
    (hx26_1 : s1.readReg64 .x26 = p1) (hx28_1 : s1.readReg64 .x28 = c3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9852#64) s1
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
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9844#64)
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
    · states_from_pb_fetches_range b (Rust.withPanics ext) 8812 12
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps
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
      states_from_pb_fetches_range b (Rust.withPanics ext) 9844 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps
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
    have hshim := sub_ok_at_of_fnAddr hshim_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) (by simp only [arm64_norm])
    have halloc := sub_ok_at_of_fnAddr halloc_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc")) (by simp only [arm64_norm])
    have hmc := sub_ok_at_of_fnAddr hmc_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy")) (by simp only [arm64_norm])
    have hoom_step := @v6hr_oom_11620_entails b ext s0
    simp only [hc2_ne, ↓reduceIte, sepConj_assoc]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    states_from_pb_fetches_range b (Rust.withPanics ext) 8812 64
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
      at hshim halloc hmc hoom_step hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 8844#64)
    wp_steps; wp_apply; wp_steps
    nth_rw 1 [← hsp1]; nth_rw 1 [← h_1]
    wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte]
      rw [v6hr_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      have htr_sf1 : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htrace]; simp only [wp_norm, arm64_norm, *]
      refine v6hr_sepWPp_seq_clean (mid := entry + 11620#64)
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
      have hsp_eq : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      refine v6hr_sepWP_exists_post (sf_1.readReg64 (Reg.gpr 0#5)) ?_
      wp_steps
      have hsp_eq_sf : sf_1.sp = sf.sp := by simp only [wp_norm, arm64_norm, *]
      wp_simp_pre [← hsp_eq_sf]; wp_apply; wp_simp_pre [hsp_eq_sf]; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h136, h200, h208, h216]
        have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp_eq] at hst
        have hv_new := vecU8Payload_pos A (sf_1.readReg64 (Reg.gpr 0#5)) macKey hm_pos hm_lt63 hoom
        have hv_old := v6hr_live_bytes_entails_vecCapPtrDealloc A c2 p2 macKey hc2_ne hm_le
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt sf.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
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

def v6hr_clone_macKey_8812_to_9852 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :=
  v6hr_clone_macKey_8812_to_9852_gen hA.shim hA.alloc
    (subroutine_ok_withStack_of_subroutine_ok hA.session_memcpy_region allocHookStack)

/-! ## 3. Deallocation Helpers (`+9852 -> +9936`, `+10416 -> +10396`, `+10492 -> +10396`) -/

theorem v6hr_dealloc_auth_9852_to_9936_gen
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr LibsignalTripleRatchet.deallocName) (rustDeallocSpec A))
    (s0 s1 : State) (out c0 c1 p1 p1_new l1 c2 p2 c3 l3 : BitVec 64)
    (d112 d116 : BitVec 32) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9852#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64) (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = l1) (hx23_1 : s1.readReg64 .x23 = l3)
    (hx24_1 : s1.readReg64 .x24 = c1) (hx26_1 : s1.readReg64 .x26 = p1)
    (hx27_1 : s1.readReg64 .x27 = c0) (hx28_1 : s1.readReg64 .x28 = c3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9936#64) s1
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
  have hstep1 :
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9892#64) s1
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
      states_from_pb_fetches_range b (Rust.withPanics ext) 9852 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_done
    · simp only [Bool.not_eq_true] at hc1
      nth_rw 1 [vecCapPtrDealloc]
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      simp only [sepConj_assoc]
      have hdealloc := sub_ok_at_of_fnAddr hdealloc_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")) (by simp only [arm64_norm])
      states_from_pb_fetches_range b (Rust.withPanics ext) 9852 40
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
        at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_apply; wp_steps
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
    states_from_pb_fetches_range b (Rust.withPanics ext) 9892 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps; wp_done
  · simp only [Bool.not_eq_true] at hc2
    nth_rw 1 [vecCapPtrDealloc]
    simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWP.weaken_pre
      (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    have hdealloc := sub_ok_at_of_fnAddr hdealloc_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")) (by simp only [arm64_norm])
    states_from_pb_fetches_range b (Rust.withPanics ext) 9892 44
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
      at hdealloc hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps; wp_apply; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [h192, h208]
      have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
      have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
      rw [haddr] at hst; nth_rw 1 [← hsp2] at hst
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt s2.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          (((s0.sp - 2208#64) ↦₆₄ p1_new) ∗ ((s0.sp - 2192#64) ↦₆₄ p2) ∗ A.pool ∗ Rest) by ac_rfl))
        (Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl)))
    · wp_done

def v6hr_dealloc_auth_9852_to_9936 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :=
  v6hr_dealloc_auth_9852_to_9936_gen hA.dealloc

theorem v6hr_dealloc_c0_10456_to_10396_gen
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr LibsignalTripleRatchet.deallocName) (rustDeallocSpec A))
    (s0 s1 : State) (out c0 p0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10456#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10396#64) s1
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
  by_cases hc0 : (c0 == 0#64) = true
  · have hc0_eq : c0 = 0#64 := of_decide_eq_true hc0
    subst hc0_eq; nth_rw 1 [vecCapPtrDealloc]
    simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10536#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗ A.pool ∗ Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = out ∧ TraceCalleeSaved s2 s0) ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 10456 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
      states_from_pb_fetches_range b (Rust.withPanics ext) 10536 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_done
  · simp only [Bool.not_eq_true] at hc0
    nth_rw 1 [vecCapPtrDealloc]
    simp only [hc0, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWP.weaken_pre
      (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    have hdealloc := sub_ok_at_of_fnAddr hdealloc_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")) (by simp only [arm64_norm])
    states_from_pb_fetches_range b (Rust.withPanics ext) 10456 28
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
      at hdealloc hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps; wp_apply; wp_steps
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

theorem v6hr_dealloc_c0_10532_to_10396_gen
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr LibsignalTripleRatchet.deallocName) (rustDeallocSpec A))
    (s0 s1 : State) (out c0 p0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10532#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10396#64) s1
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
  by_cases hc0 : (c0 == 0#64) = true
  · have hc0_eq : c0 = 0#64 := of_decide_eq_true hc0
    subst hc0_eq; nth_rw 1 [vecCapPtrDealloc]
    simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
    states_from_pb_fetches_range b (Rust.withPanics ext) 10532 12
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps; wp_done
  · simp only [Bool.not_eq_true] at hc0
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10460#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗ vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x27 = c0 ∧ TraceCalleeSaved s2 s0) ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 10532 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx27_2, htr2⟩
      nth_rw 1 [vecCapPtrDealloc]
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      simp only [sepConj_assoc]
      have hdealloc := sub_ok_at_of_fnAddr hdealloc_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")) (by simp only [arm64_norm])
      states_from_pb_fetches_range b (Rust.withPanics ext) 10460 24
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
        at hdealloc hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_apply; wp_steps
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

theorem v6hr_dealloc_cloned_10416_to_10396_gen
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr LibsignalTripleRatchet.deallocName) (rustDeallocSpec A))
    (s0 s1 : State) (out c0 p0 l1 p1_new l2 p2_new : BitVec 64)
    (rootKey macKey hdr : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10416#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1) (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10396#64) s1
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
  have hv1 := v6hr_vecU8Payload_entails_vecCapPtrDealloc A l1 p1_new rootKey
  have hv2 := v6hr_vecU8Payload_entails_vecCapPtrDealloc A l2 p2_new macKey
  have hv0 := v6hr_vecU8Payload_entails_vecCapPtrDealloc A c0 p0 hdr
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono_left hv0))))))) ?_
  have hstep1 :
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10436#64) s1
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
      states_from_pb_fetches_range b (Rust.withPanics ext) 10416 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_done
    · simp only [Bool.not_eq_true] at hl1
      nth_rw 1 [vecCapPtrDealloc]
      simp only [hl1, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      simp only [sepConj_assoc]
      have hdealloc := sub_ok_at_of_fnAddr hdealloc_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")) (by simp only [arm64_norm])
      states_from_pb_fetches_range b (Rust.withPanics ext) 10416 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
        at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_apply
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
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10456#64) s2
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
      states_from_pb_fetches_range b (Rust.withPanics ext) 10436 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps
      refine EncoderFromPb.align_pre (by rw [h216]; exact Entails.of_eq (by ac_rfl)) ?_
      wp_done
    · simp only [Bool.not_eq_true] at hl2
      nth_rw 1 [vecCapPtrDealloc]
      simp only [hl2, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      simp only [sepConj_assoc]
      have hdealloc := sub_ok_at_of_fnAddr hdealloc_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")) (by simp only [arm64_norm])
      states_from_pb_fetches_range b (Rust.withPanics ext) 10436 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
        at hdealloc hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_apply
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
  refine SepWP.seq hstep2 fun s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx27_3, htr3⟩ =>
    SepWP.weaken_pre hP3 (SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
      (v6hr_dealloc_c0_10456_to_10396_gen hdealloc_fn s0 s3 out c0 p0 _
        hsp0_align hpc3 hrun3 hsp3 hx19_3 hx27_3 htr3))

def v6hr_dealloc_cloned_10416_to_10396 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :=
  v6hr_dealloc_cloned_10416_to_10396_gen hA.dealloc

theorem v6hr_dealloc_cloned_10492_to_10396_gen
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr LibsignalTripleRatchet.deallocName) (rustDeallocSpec A))
    (s0 s1 : State) (out c0 p0 l1 p1_new l2 p2_new : BitVec 64)
    (rootKey macKey hdr : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10492#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1) (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10396#64) s1
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
  have hv1 := v6hr_vecU8Payload_entails_vecCapPtrDealloc A l1 p1_new rootKey
  have hv2 := v6hr_vecU8Payload_entails_vecCapPtrDealloc A l2 p2_new macKey
  have hv0 := v6hr_vecU8Payload_entails_vecCapPtrDealloc A c0 p0 hdr
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono_left hv0))))))) ?_
  have hstep1 :
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10512#64) s1
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
      states_from_pb_fetches_range b (Rust.withPanics ext) 10492 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_done
    · simp only [Bool.not_eq_true] at hl1
      nth_rw 1 [vecCapPtrDealloc]
      simp only [hl1, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      simp only [sepConj_assoc]
      have hdealloc := sub_ok_at_of_fnAddr hdealloc_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")) (by simp only [arm64_norm])
      states_from_pb_fetches_range b (Rust.withPanics ext) 10492 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
        at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_apply
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
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10532#64) s2
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
      states_from_pb_fetches_range b (Rust.withPanics ext) 10512 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps
      refine EncoderFromPb.align_pre (by rw [h216]; exact Entails.of_eq (by ac_rfl)) ?_
      wp_done
    · simp only [Bool.not_eq_true] at hl2
      nth_rw 1 [vecCapPtrDealloc]
      simp only [hl2, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      simp only [sepConj_assoc]
      have hdealloc := sub_ok_at_of_fnAddr hdealloc_fn statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")) (by simp only [arm64_norm])
      states_from_pb_fetches_range b (Rust.withPanics ext) 10512 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
        at hdealloc hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_apply
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
  refine SepWP.seq hstep2 fun s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx27_3, htr3⟩ =>
    SepWP.weaken_pre hP3 (SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
      (v6hr_dealloc_c0_10532_to_10396_gen hdealloc_fn s0 s3 out c0 p0 _
        hsp0_align hpc3 hrun3 hsp3 hx19_3 hx27_3 htr3))

def v6hr_dealloc_cloned_10492_to_10396 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :=
  v6hr_dealloc_cloned_10492_to_10396_gen hA.dealloc

theorem v6hr_from_pb_ptsNeeded_ne (F : ShaCompress)
    (uc : Option V1State.Unchunked.HeaderReceived) (decPb : PolynomialDecoder)
    (hne : decPb.ptsNeeded ≠ 576#32) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := uc, receivingEk := some decPb }) } =
    .error (.err .msgDecode) := by
  have hne_nat : decPb.ptsNeeded.toNat ≠ 576 := fun h => hne (BitVec.eq_of_toNat_eq (by simpa using h))
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb
  simp [ENCAPSULATION_KEY_SIZE, hne_nat, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

theorem v6hr_from_pb_uc_none_dec_none (F : ShaCompress) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := none, receivingEk := none }) } =
    .error (.err .stateDecode) := rfl

theorem v6hr_from_pb_uc_none_dec_some (F : ShaCompress) (decPb : PolynomialDecoder)
    (heq : decPb.ptsNeeded = 576#32) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := none, receivingEk := some decPb }) } =
    .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb
  simp [ENCAPSULATION_KEY_SIZE, heq, bind, Except.bind, pure, Except.pure]

theorem v6hr_from_pb_auth_none_dec_none (F : ShaCompress)
    (hdr : List (BitVec 8)) (epoch : BitVec 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := some { hdr := hdr, auth := none, epoch := epoch }, receivingEk := none }) } =
    .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb Unchunked.SendCt.HeaderReceived.from_pb
  by_cases hlen : (hdr.length == HEADER_SIZE) = true <;> simp [hlen, bind, Except.bind, pure, Except.pure]

theorem v6hr_from_pb_auth_none_dec_some (F : ShaCompress)
    (hdr : List (BitVec 8)) (epoch : BitVec 64) (decPb : PolynomialDecoder) (heq : decPb.ptsNeeded = 576#32) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := some { hdr := hdr, auth := none, epoch := epoch }, receivingEk := some decPb }) } =
    .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb Unchunked.SendCt.HeaderReceived.from_pb
  by_cases hlen : (hdr.length == HEADER_SIZE) = true <;>
    simp [ENCAPSULATION_KEY_SIZE, heq, hlen, bind, Except.bind, pure, Except.pure]

theorem v6hr_from_pb_hdr_ne64_dec_none (F : ShaCompress)
    (hdr : List (BitVec 8)) (authPb : ProtoAuthenticator) (epoch : BitVec 64) (hne : hdr.length ≠ 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := some { hdr := hdr, auth := some authPb, epoch := epoch }, receivingEk := none }) } =
    .error (.err .stateDecode) := by
  have hlen : (hdr.length == HEADER_SIZE) = false := beq_false_of_ne hne
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb Unchunked.SendCt.HeaderReceived.from_pb
  simp [hlen, bind, Except.bind, pure, Except.pure]

theorem v6hr_from_pb_hdr_ne64_dec_some (F : ShaCompress)
    (hdr : List (BitVec 8)) (authPb : ProtoAuthenticator) (epoch : BitVec 64)
    (decPb : PolynomialDecoder) (heq : decPb.ptsNeeded = 576#32) (hne : hdr.length ≠ 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := some { hdr := hdr, auth := some authPb, epoch := epoch }, receivingEk := some decPb }) } =
    .error (.err .stateDecode) := by
  have hlen : (hdr.length == HEADER_SIZE) = false := beq_false_of_ne hne
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb Unchunked.SendCt.HeaderReceived.from_pb
  simp [ENCAPSULATION_KEY_SIZE, heq, hlen, bind, Except.bind, pure, Except.pure]

end CryptoVerification.SpqrV1.States.FromPb

