/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5b
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5b (`AllocContracts4K`: Arm 9 `ct1Acknowledged` Step Lemmas)

Lifts `ct1Acknowledged_step_424_to_1812` and `ct1Acknowledged_step_1812_to_1900`
from `AllocContracts` to `SpqrV1.Alloc.AllocContracts4K`.
-/

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bExt

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.States.IntoPb
open scoped CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RustHeap
  (RustAlloc LayoutOk allocHookStack rustAllocSpec rustDeallocSpec allocFailedEvent)
open CryptoVerification.LibsignalTripleRatchet
  (tripleRatchetProgAtExt withStack sessionShimSpec sessionMemcpyRegionSpec)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.States.IntoPb.DecoderPb (sepWPp_pure_mid)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.States.IntoPb
  (statesIntoPbName statesIntoPb_fnOff
   statesIntoPbOnPanic StatesIntoPbPanic TraceCalleeSaved
   states_into_pb_panic_1700 ct1AcknowledgedScratchCells
   vecU8Heap vecU8CloneTail vecU8CloneTail_entails_dealloc vecU8Heap_nil_intro
   vecU8Heap_of_exact_alloc
   ofNat_beq_zero_false' ofNat_ne_zero_true bv_sub_sub_lit' bv_add_add_lit')

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

local macro "states_into_pb_fetches_4k " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbBin $b $H statesIntoPb_fnOff
      (num% (ls_off% "<spqr::v1::chunked::states::States>::into_pb")) $k0 $len)

/-- Step 3 (`+424 -> +1812`): clone `s.uc.ct1` under `AllocContracts4K`. -/
theorem ct1Acknowledged_step_424_to_1812_4k
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext)
    (s0 s : State) (out stA cap_ct1 ptr_ct1 epoch : BitVec 64)
    (ct1 : List (BitVec 8))
    (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : ct1.length < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 424#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = epoch)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (ptr_new : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1812#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x28 = s0.sp - 256#64 →
      sm.readReg64 .x27 = epoch →
      sm.readReg64 .x26 = s0.sp - 480#64 →
      sm.readReg64 .x24 = ptr_ct1 →
      sm.readReg64 .x23 = cap_ct1 →
      sm.readReg64 .x22 = ptr_new →
      sm.readReg64 .x21 = BitVec.ofNat 64 ct1.length →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x19 = out →
      TraceCalleeSaved sm s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm
        (vecU8Heap A (BitVec.ofNat 64 ct1.length) ptr_new (BitVec.ofNat 64 ct1.length) ct1 ∗
         vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
         A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      ((ptr_ct1 ↦ₛ ct1) ∗
       vecU8CloneTail A cap_ct1 ptr_ct1 ct1 ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
      Q (StatesIntoPbPanic s0 R) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  by_cases hlen_zero : ct1.length = 0
  · have hnil : ct1 = [] := List.eq_nil_of_length_eq_zero hlen_zero
    subst hnil
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx21 hlen hnext ⊢
    refine CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1812#64)
      (P_mid :=
        vecU8Heap A 0#64 1#64 0#64 [] ∗
        vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
      (Q_mid := fun sm =>
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x28 = s0.sp - 256#64 ∧
        sm.readReg64 .x27 = epoch ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x22 = 1#64 ∧
        sm.readReg64 .x21 = 0#64 ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · states_into_pb_fetches_4k b (Rust.withPanics ext) 424 4
      states_into_pb_fetches_4k b (Rust.withPanics ext) 1808 4
      dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (CryptoVerification.libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::into_pb" = entry
      examples_hide_fetches
      wp_steps
      have hdealloc := vecU8CloneTail_entails_dealloc A cap_ct1 ptr_ct1 []
      have hnil := vecU8Heap_nil_intro A
        (vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
         A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
      simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hnil
      have hent :
          (ptr_ct1 ↦ₛ []) ∗ vecU8CloneTail A cap_ct1 ptr_ct1 [] ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame ⊢
          vecU8Heap A 0#64 1#64 0#64 [] ∗
          vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame := by
        rw [show (ptr_ct1 ↦ₛ []) ∗ vecU8CloneTail A cap_ct1 ptr_ct1 [] ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame =
            ((ptr_ct1 ↦ₛ []) ∗ vecU8CloneTail A cap_ct1 ptr_ct1 []) ∗
            (A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame) by sep_ac_rfl]
        exact Entails.trans (sepConj_mono_left hdealloc) hnil
      exact SepWP.weaken_pre hent (by wp_done)
    · intro sm hpcm hrunm ⟨hspm, hx29m, hx28m, hx27m, hx26m, hx24m, hx23m,
        hx22m, hx21m, hx20m, hx19m, htrm⟩
      exact hnext sm 1#64 hpcm hrunm hspm hx29m hx28m hx27m hx26m hx24m hx23m
        hx22m hx21m hx20m hx19m htrm
  · have hpos : 0 < ct1.length := Nat.pos_of_ne_zero hlen_zero
    have hbeq0 : (BitVec.ofNat 64 ct1.length == 0#64) = false :=
      ofNat_beq_zero_false' hpos (by omega)
    have hne0 : (BitVec.ofNat 64 ct1.length != 0#64) = true :=
      ofNat_ne_zero_true hpos (by omega)
    have htoNat_len : (BitVec.ofNat 64 ct1.length).toNat = ct1.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk ct1.length 1 := ⟨hpos, hpow2, by omega⟩
    have hshim := hA.shim_ok_at statesIntoPbName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    have halloc := hA.alloc_ok_at statesIntoPbName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "__rustc::__rust_alloc"))
    have hmemcpy := hA.session_memcpy_region_ok_at statesIntoPbName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy"))
    have hpanic : ∀ (sm : State) (P_mid : SepProp),
        sm.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1700#64 →
        sm.status = .Running →
        sm.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm P_mid Q
          (StatesIntoPbPanic s0 R) := by
      intro sm P_mid hpcm hrunm htrm
      have heq : (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesIntoPbOnPanic s0 sf ∗ R)) =
          StatesIntoPbPanic s0 R := by
        funext sf P_f
        simp only [StatesIntoPbPanic, statesIntoPbOnPanic, sepConj_assoc]
      rw [← heq]
      exact states_into_pb_panic_1700 s0 sm P_mid R hpcm hrunm htrm
    simp only [sessionShimSpec] at hshim
    simp only [rustAllocSpec] at halloc
    simp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy
    states_into_pb_fetches_4k b (Rust.withPanics ext) 424 48
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
      BitVec.ofNat_eq_ofNat] at hpc hshim halloc hmemcpy hpanic ⊢
    generalize_entry (CryptoVerification.libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 448#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte]
      refine sepWPp_pure_mid fun htr_oom => ?_
      refine CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean (mid := entry + 1700#64)
        (P_mid :=
          A.pool ∗
          stackAt sf.sp allocHookStack ∗
          (ptr_ct1 ↦ₛ ct1) ∗
          vecU8CloneTail A cap_ct1 ptr_ct1 ct1 ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
        ?_ ?_
      · wp_steps
        wp_done
      · intro sm hpcm hrunm htrm
        exact hpanic sm _ hpcm hrunm htrm
    · have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom
      have hoom_bne : (sf_1.readReg64 (Reg.gpr 0#5) != 0#64) = true :=
        bne_iff_ne.mpr hoom
      conv => arg 4; simp only [hoom, ↓reduceIte, htoNat_len]; simp only [sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
      refine CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean (mid := entry + 1812#64)
        (P_mid :=
          vecU8Heap A (BitVec.ofNat 64 ct1.length) ptr_c
            (BitVec.ofNat 64 ct1.length) ct1 ∗
          vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
        (Q_mid := fun sm =>
          sm.sp = s0.sp - 1520#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x28 = s0.sp - 256#64 ∧
          sm.readReg64 .x27 = epoch ∧
          sm.readReg64 .x26 = s0.sp - 480#64 ∧
          sm.readReg64 .x24 = ptr_ct1 ∧
          sm.readReg64 .x23 = cap_ct1 ∧
          sm.readReg64 .x22 = ptr_c ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 ct1.length ∧
          sm.readReg64 .x20 = stA ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rw [← ‹sf_1.sp = sf.sp›]
        wp_steps
        wp_apply
        wp_steps
        have hbuf := vecU8Heap_of_exact_alloc A ptr_c ct1 hpos hlen hoom
        have hdealloc := vecU8CloneTail_entails_dealloc A cap_ct1 ptr_ct1 ct1
        have hent :
            (ptr_c ↦ₛ ct1) ∗ (ptr_ct1 ↦ₛ ct1) ∗ stackAt sf_1.sp allocHookStack ∗
            A.pool ∗ A.live ptr_c ct1.length 1 ∗
            vecU8CloneTail A cap_ct1 ptr_ct1 ct1 ∗ Frame ⊢
            vecU8Heap A (BitVec.ofNat 64 ct1.length) ptr_c
              (BitVec.ofNat 64 ct1.length) ct1 ∗
            vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame := by
          rw [‹sf_1.sp = sf.sp›, ‹sf.sp = s.sp›, hsp]
          refine Entails.trans (Entails.of_eq (show _ =
            ((ptr_c ↦ₛ ct1) ∗ A.live ptr_c ct1.length 1) ∗
            ((ptr_ct1 ↦ₛ ct1) ∗ vecU8CloneTail A cap_ct1 ptr_ct1 ct1) ∗
            (A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
          exact sepConj_mono hbuf (sepConj_mono hdealloc (Entails.refl _))
        exact SepWP.weaken_pre hent (by wp_done)
      · intro sm hpcm hrunm ⟨hspm, hx29m, hx28m, hx27m, hx26m, hx24m, hx23m,
          hx22m, hx21m, hx20m, hx19m, htrm⟩
        exact hnext sm ptr_c hpcm hrunm hspm hx29m hx28m hx27m hx26m hx24m hx23m
          hx22m hx21m hx20m hx19m htrm

/-- Step 4 (`+1812 -> +1900`): move `a0..a5`, copy `hdr0..hdr2, es0..es2`, deallocate
    `(cap_ct1, ptr_ct1)` under `AllocContracts4K`, and set up `<PolyDecoder>::into_pb`. -/
theorem ct1Acknowledged_step_1812_to_1900_4k
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s : State) (out stA cap_ct1 ptr_ct1 ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64)
    (y0 y1 y2 y3 y4 y5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1812#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = epoch)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64) s
      ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       ct1AcknowledgedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
         w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
       vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
           ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
           ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
          ct1AcknowledgedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
            hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1904#64 ∧
        sm.readReg64 .x0 = s0.sp - 352#64 ∧
        sm.readReg64 .x1 = s0.sp - 1232#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x27 = epoch ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x22 = ptr_new ∧
        sm.readReg64 .x21 = len_ct1 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hdealloc := hA.dealloc_ok_at statesIntoPbName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "__rustc::__rust_dealloc"))
  simp only [rustDeallocSpec] at hdealloc
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  states_into_pb_fetches_4k b (Rust.withPanics ext) 1812 92
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName, ct1AcknowledgedScratchCells,
    vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc hdealloc ⊢
  generalize_entry (CryptoVerification.libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  by_cases hc : (cap_ct1 == 0#64) = true
  · have hc_bne : (cap_ct1 != 0#64) = false := by
      rcases eq_or_ne cap_ct1 0#64 with rfl | hne
      · rfl
      · exact False.elim (hne (beq_iff_eq.mp hc))
    simp only [hc, ↓reduceIte, sepConj_emp, emp_sepConj]
    wp_steps
    refine CryptoVerification.SpqrV1.Drop.align_pre (by sep_ac_rfl) ?_
    wp_done
  · have hc_beq : (cap_ct1 == 0#64) = false := Bool.eq_false_iff.mpr hc
    have hc_bne : (cap_ct1 != 0#64) = true := by
      rw [bne_iff_ne]; intro h; exact hc (beq_iff_eq.mpr h)
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    wp_steps
    wp_apply
    wp_steps
    refine CryptoVerification.SpqrV1.Drop.align_pre (by rw [hsp]; sep_ac_rfl) ?_
    wp_done

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SpqrV1.States.IntoPb
export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bExt
  (ct1Acknowledged_step_424_to_1812_4k
   ct1Acknowledged_step_1812_to_1900_4k)
end CryptoVerification.SpqrV1.States.IntoPb
-- AUTO-BRIDGE END
