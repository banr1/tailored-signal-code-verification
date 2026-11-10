/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5a: Arm 8 (`States.ekReceivedCt1Sampled`)

**Checked by Lean.**

Verifies Arm 8 (`States.ekReceivedCt1Sampled`, tag `10`, jump table index `8`,
`+1644 -> +1760 -> +2248/+2252 -> +2324 -> +2340 -> +1544`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

/-! ## 1. Step Lemmas for Arm 8 (`+1644 -> +1760 -> +2252 -> +2324 -> +2340 -> +1544`) -/

/-- Step 1b (`+60 -> +1760`): jump via index `8` (`tag = 10#64` -> `+1644`), load `auth`,
    `cap_ct1`, `ptr_ct1`, `len_ct1`, and `epoch` from `stA`, stage `auth` into
    `s0.sp - 1360..1312`, and take `tbz x21, #0x3f, +1760`. -/
theorem ekReceivedCt1Sampled_step_60_to_1760 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 cap_ct1 ptr_ct1 epoch : BitVec 64) (len_ct1 : Nat)
    (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 : BitVec 64)
    (Rest : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : len_ct1 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 60#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (hx8 : s.readReg64 .x8 = 10#64)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1760#64) s
      (statesIntoPbJumpTableAt b ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
       ((stA + 528#64) ↦₆₄ epoch) ∗
       ekReceivedScratchCells s0.sp
         t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
         u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
       Rest)
      (fun sm Pm =>
        (Pm ⊢
          statesIntoPbJumpTableAt b ∗
          ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
          ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
          ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
          ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
          ((stA + 528#64) ↦₆₄ epoch) ∗
          ekReceivedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
            u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
          Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 len_ct1 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hadrp := fnAddr_adrp_5ce6c (H := Rust.withPanics ext) hb
  have hmsb := ofNat_lt_2pow63_msb_zero hlen
  have hand := ofNat_lt_2pow63_and_highBit_zero hlen
  have hlsr := ofNat_lt_2pow63_lsr63_zero hlen
  states_into_pb_fetches_range b (Rust.withPanics ext) 60 40
  states_into_pb_fetches_range b (Rust.withPanics ext) 1644 52
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
    statesIntoPbJumpTableAt, statesIntoPbJumpTableBytes, ekReceivedScratchCells,
    BitVec.ofNat_eq_ofNat] at hadrp hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  wp_steps
  refine DropGlueFacts.align_pre (by ac_rfl) ?_
  wp_done

/-- Step 3 (`+1760 -> +2252`): clone `s.uc.ct1`. -/
theorem ekReceivedCt1Sampled_step_1760_to_2252
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (out stA cap_ct1 ptr_ct1 epoch : BitVec 64)
    (ct1 : List (BitVec 8))
    (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : ct1.length < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1760#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (ptr_new : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 2252#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x21 = BitVec.ofNat 64 ct1.length →
      sm.readReg64 .x22 = ptr_new →
      sm.readReg64 .x23 = cap_ct1 →
      sm.readReg64 .x24 = ptr_ct1 →
      sm.readReg64 .x26 = s0.sp - 480#64 →
      sm.readReg64 .x27 = s0.sp - 1360#64 →
      sm.readReg64 .x28 = epoch →
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
    refine DecoderPb.SepWPp.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 2252#64)
      (P_mid :=
        vecU8Heap A 0#64 1#64 0#64 [] ∗
        vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
      (Q_mid := fun sm =>
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x21 = 0#64 ∧
        sm.readReg64 .x22 = 1#64 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · states_into_pb_fetches_range b (Rust.withPanics ext) 1760 4
      states_into_pb_fetches_range b (Rust.withPanics ext) 2248 4
      dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b
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
            (A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame) by ac_rfl]
        exact Entails.trans (sepConj_mono_left hdealloc) hnil
      exact SepWP.weaken_pre hent (by wp_done)
    · intro sm hpcm hrunm ⟨hspm, hx29m, hx19m, hx20m, hx21m, hx22m, hx23m, hx24m,
        hx26m, hx27m, hx28m, htrm⟩
      exact hnext sm 1#64 hpcm hrunm hspm hx29m hx19m hx20m hx21m hx22m hx23m hx24m
        hx26m hx27m hx28m htrm
  · have hpos : 0 < ct1.length := Nat.pos_of_ne_zero hlen_zero
    have hbeq0 : (BitVec.ofNat 64 ct1.length == 0#64) = false :=
      ofNat_beq_zero_false' hpos (by omega)
    have hne0 : (BitVec.ofNat 64 ct1.length != 0#64) = true :=
      ofNat_ne_zero_true hpos (by omega)
    have htoNat_len : (BitVec.ofNat 64 ct1.length).toNat = ct1.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk ct1.length 1 := ⟨hpos, hpow2, by omega⟩
    have hshim := shim_ok_at2_ext hA (name := statesIntoPbName)
      (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    have halloc := alloc_ok_at_norm_ext hA (name := statesIntoPbName)
      (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "__rustc::__rust_alloc"))
    have hmemcpy := memcpy_ok_at2_ext hA (name := statesIntoPbName)
      (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy"))
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
    simp only [noAllocShimSpec] at hshim
    simp only [rustAllocSpec] at halloc
    simp only [framelessMemcpySpec] at hmemcpy
    states_into_pb_fetches_range b (Rust.withPanics ext) 1760 48
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
      BitVec.ofNat_eq_ofNat] at hpc hshim halloc hmemcpy hpanic ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 1784#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte]
      refine DecoderPb.sepWPp_pure_mid fun htr_oom => ?_
      refine DecoderPb.SepWPp.seq_clean (mid := entry + 1700#64)
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
      refine DecoderPb.sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
      refine DecoderPb.SepWPp.seq_clean (mid := entry + 2252#64)
        (P_mid :=
          vecU8Heap A (BitVec.ofNat 64 ct1.length) ptr_c
            (BitVec.ofNat 64 ct1.length) ct1 ∗
          vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
        (Q_mid := fun sm =>
          sm.sp = s0.sp - 1520#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = stA ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 ct1.length ∧
          sm.readReg64 .x22 = ptr_c ∧
          sm.readReg64 .x23 = cap_ct1 ∧
          sm.readReg64 .x24 = ptr_ct1 ∧
          sm.readReg64 .x26 = s0.sp - 480#64 ∧
          sm.readReg64 .x27 = s0.sp - 1360#64 ∧
          sm.readReg64 .x28 = epoch ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · wp_steps
        wp_apply
        wp_steps
        have hbuf := vecU8Heap_of_exact_alloc A ptr_c ct1 hpos hlen hoom
        have hdealloc := vecU8CloneTail_entails_dealloc A cap_ct1 ptr_ct1 ct1
        have hent :
            (ptr_c ↦ₛ ct1) ∗ (ptr_ct1 ↦ₛ ct1) ∗
            A.pool ∗ stackAt sf.sp allocHookStack ∗
            A.live ptr_c ct1.length 1 ∗
            vecU8CloneTail A cap_ct1 ptr_ct1 ct1 ∗ Frame ⊢
            vecU8Heap A (BitVec.ofNat 64 ct1.length) ptr_c
              (BitVec.ofNat 64 ct1.length) ct1 ∗
            vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame := by
          rw [‹sf.sp = s.sp›, hsp]
          refine Entails.trans (Entails.of_eq (show _ =
            ((ptr_c ↦ₛ ct1) ∗ A.live ptr_c ct1.length 1) ∗
            ((ptr_ct1 ↦ₛ ct1) ∗ vecU8CloneTail A cap_ct1 ptr_ct1 ct1) ∗
            (A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame) by ac_rfl)) ?_
          exact sepConj_mono hbuf (sepConj_mono hdealloc (Entails.refl _))
        exact SepWP.weaken_pre hent (by wp_done)
      · intro sm hpcm hrunm ⟨hspm, hx29m, hx19m, hx20m, hx21m, hx22m, hx23m, hx24m,
          hx26m, hx27m, hx28m, htrm⟩
        exact hnext sm ptr_c hpcm hrunm hspm hx29m hx19m hx20m hx21m hx22m hx23m hx24m
          hx26m hx27m hx28m htrm

/-- Step 4 (`+2252 -> +2324`): move `auth` from `s0.sp - 1360..1312` to `s0.sp - 256..208`,
    load `es` and `ek` from `stA + 456..504` into `s0.sp - 480..432`, and deallocate
    `(cap_ct1, ptr_ct1)` via `cbz x23, +2324; bl __rust_dealloc`. -/
theorem ekReceivedCt1Sampled_step_2252_to_2324
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (out stA cap_ct1 ptr_ct1 ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2 : BitVec 64)
    (t6 t7 t8 t8' t9 t10 t11 t12 t13 t14 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 2252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 2324#64) s
      (((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       ekReceivedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 t6 t7 t8 t8' t9 t10 t11 t12 t13 t14
         u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
       vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
          ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
          ekReceivedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 t6 t7 t8 t8' t9 t10 t11 t12 t13 t14
            es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x21 = len_ct1 ∧
        sm.readReg64 .x22 = ptr_new ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hdealloc := dealloc_ok_at_norm_ext hA (name := statesIntoPbName)
    (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "__rustc::__rust_dealloc"))
  simp only [rustDeallocSpec] at hdealloc
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  states_into_pb_fetches_range b (Rust.withPanics ext) 2252 72
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName, ekReceivedScratchCells,
    vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b
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
    refine DropGlueFacts.align_pre (by ac_rfl) ?_
    wp_done
  · have hc_beq : (cap_ct1 == 0#64) = false := Bool.eq_false_iff.mpr hc
    have hc_bne : (cap_ct1 != 0#64) = true := by
      rw [bne_iff_ne]; intro h; exact hc (beq_iff_eq.mpr h)
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    wp_steps
    wp_apply
    refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
    wp_done

/-- Step 5 (`+2324 -> +2340`): call `<PolyEncoder>::into_pb(s0.sp - 1232, stA + 8)`. -/
theorem ekReceivedCt1Sampled_step_2324_to_2340
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64) (encoderIntoPbSpec A))
    (s0 s : State) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (enc : PolyEncoder)
    (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 2324#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 2340#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x21 = len_ct1 →
      sm.readReg64 .x22 = ptr_new →
      sm.readReg64 .x27 = s0.sp - 1360#64 →
      sm.readReg64 .x28 = epoch →
      TraceCalleeSaved sm s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm
        ((((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
          ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
          ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
          ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
         protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
         memRegion (stA + 8#64) polyEncoderSize ∗
         A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (memRegion (s0.sp - 1232#64) 56 ∗
       polyEncoderAt A (stA + 8#64) enc ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      Q (StatesIntoPbPanic s0 R) := by
  rcases htrace with ⟨htrace, hvregs⟩
  refine DecoderPb.SepWPp.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64)
    (P_mid :=
      memRegion (s0.sp - 1232#64) 56 ∗
      polyEncoderAt A (stA + 8#64) enc ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
    (Q_mid := fun sm =>
      sm.sp = s0.sp - 1520#64 ∧
      sm.readReg64 .x29 = s0.sp - 96#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = stA ∧
      sm.readReg64 .x21 = len_ct1 ∧
      sm.readReg64 .x22 = ptr_new ∧
      sm.readReg64 .x27 = s0.sp - 1360#64 ∧
      sm.readReg64 .x28 = epoch ∧
      sm.readReg64 .x0 = s0.sp - 1232#64 ∧
      sm.readReg64 .x1 = stA + 8#64 ∧
      sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 2340#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_into_pb_fetches_range b (Rust.withPanics ext) 2324 16
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_done
  · intro s_call hpc_call hrun_call ⟨hsp_c, hx29_c, hx19_c, hx20_c, hx21_c, hx22_c,
      hx27_c, hx28_c, hx0_c, hx1_c, hx30_c, htr_c⟩
    have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
    exact call_encoderIntoPb_expose henc
      (s0.sp - 1232#64) (stA + 8#64) enc
      hpc_call hrun_call hsp_c hfsp_align hx30_c htr_c hx0_c hx1_c
      (by change _ = (memRegion (s0.sp - 1232#64) 56 ∗ polyEncoderAt A (stA + 8#64) enc ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame; ac_rfl)
      (fun sm e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspm hcc htrm => by
        refine SepWPp.weaken_pre ?_
          (hnext sm e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspm
            (hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx29_c)
            (hcc.1.trans hx19_c)
            (hcc.2.1.trans hx20_c)
            (hcc.2.2.1.trans hx21_c)
            (hcc.2.2.2.1.trans hx22_c)
            (hcc.2.2.2.2.2.2.2.2.1.trans hx27_c)
            (hcc.2.2.2.2.2.2.2.2.2.1.trans hx28_c)
            htrm)
        exact Entails.of_eq (by simp only [arm64_norm]))

/-- Step 6 (`+2340 -> +1544`): pack `es`, `ek`, `ct1`, `auth`, `epoch`, and `sending_ct1.intoPb`
    into `epilogueStagingCells` and branch to `+1544`. -/
theorem ekReceivedCt1Sampled_step_2340_to_1544 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : BitVec 64)
    (w8 w16 w24 w32 w40 w48
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 2340#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1544#64) s
      (ekReceivedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
         es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
        ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
        ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
        ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48
         w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184
         w192 w200 w208 w216 ∗
       Rest)
      (fun sm Pm =>
        (Pm ⊢
          ekReceivedScratchCells s0.sp
            es0 es1 es2 ek0 ek1 ek2 t6 ptr_new len_ct1 a0 a1 a2 a3 a4 a5 epoch
            es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
          (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
           ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
           ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
           ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
          epilogueStagingCells s0.sp
            es0 es1 es2 ek0 ek1 ek2
            ptr_new len_ct1 a0 a1 a2 a3 a4 a5
            epoch e0 e1 e2 e3 e4 e5 e6
            w192 w200 w208 w216 ∗
          Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = len_ct1 ∧
        sm.readReg64 .x22 = 0x8000000000000008#64 ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  states_into_pb_fetches_range b (Rust.withPanics ext) 2340 120
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
    ekReceivedScratchCells, epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  wp_steps
  refine DropGlueFacts.align_pre (by ac_rfl) ?_
  wp_done

/-! ## 2. Main Variant Theorem: `states_into_pb_ekReceivedCt1Sampled` -/

/-- Arm 8 (`States.ekReceivedCt1Sampled`, tag `10`, jump table index `8` -> `+1644`). -/
theorem states_into_pb_ekReceivedCt1Sampled
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (henc : EncoderIntoPbOkExt b A ext)
    (s : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b (.ekReceivedCt1Sampled s)) := by
  have henc_raw := sub_ok_encoderIntoPb_raw henc
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb_align⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.ekReceivedCt1Sampled s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_wpp s0 s0 out stA (.ekReceivedCt1Sampled s) _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedEkReceivedCt1Sampled_expose A stA s))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro a0
  apply SepWPp.exists_elim; intro a1
  apply SepWPp.exists_elim; intro a2
  apply SepWPp.exists_elim; intro a3
  apply SepWPp.exists_elim; intro a4
  apply SepWPp.exists_elim; intro a5
  apply SepWPp.exists_elim; intro es0
  apply SepWPp.exists_elim; intro es1
  apply SepWPp.exists_elim; intro es2
  apply SepWPp.exists_elim; intro ek0
  apply SepWPp.exists_elim; intro ek1
  apply SepWPp.exists_elim; intro ek2
  apply SepWPp.exists_elim; intro cap_ct1
  apply SepWPp.exists_elim; intro ptr_ct1
  rw [show memRegion out optProtoInnerStateSize ∗
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stA ↦₆₄ 10#64) ∗
      polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
      ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
      ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
      ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
      (ptr_ct1 ↦ₛ s.uc.ct1) ∗
      vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A es0 es1 es2 s.uc.es ∗
      vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
      memRegion (stA + 536#64) 392 ∗
      statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack =
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ 10#64) ∗
       (statesIntoPbJumpTableAt b ∗
        memRegion out optProtoInnerStateSize ∗
        polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
        ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
        ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
        ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
        ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
        ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
        (ptr_ct1 ↦ₛ s.uc.ct1) ∗
        vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A es0 es1 es2 s.uc.es ∗
        vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
        memRegion (stA + 536#64) 392 ∗ A.pool)) by ac_rfl]
  apply SepWPp.pure_elim; intro hlen
  have hpro := states_into_pb_prologue_60 s0 out stA 10#64
    (statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392 ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine DecoderPb.SepWPp.seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩
  have h1424 :
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416 ⊢
      memRegion (s0.sp - 1520#64) 1424 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1520#64) (n := 8) (k := 1416)
          (b' := s0.sp - 1512#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (Drop.pointsTo64_entails_memRegion (s0.sp - 1520#64) 0#64)
  refine SepWPp.weaken_pre
    (by
      rw [show stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ 10#64) ∗
          (statesIntoPbJumpTableAt b ∗
           memRegion out optProtoInnerStateSize ∗
           polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
           ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
           ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
           ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
           ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
           ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A es0 es1 es2 s.uc.es ∗
           vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
           memRegion (stA + 536#64) 392 ∗ A.pool) =
          (((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
           statesIntoPbSavedCells s0 ∗
           (stA ↦₆₄ 10#64) ∗
           statesIntoPbJumpTableAt b ∗
           memRegion out optProtoInnerStateSize ∗
           polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
           ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
           ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
           ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
           ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
           ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A es0 es1 es2 s.uc.es ∗
           vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
           memRegion (stA + 536#64) 392 ∗ A.pool) by ac_rfl]
      exact sepConj_mono_left (Entails.trans h1424 (memRegion_1424_split_epilogue s0.sp))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro w8
  apply SepWPp.exists_elim; intro w16
  apply SepWPp.exists_elim; intro w24
  apply SepWPp.exists_elim; intro w32
  apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w48
  apply SepWPp.exists_elim; intro w64
  apply SepWPp.exists_elim; intro w72
  apply SepWPp.exists_elim; intro w80
  apply SepWPp.exists_elim; intro w88
  apply SepWPp.exists_elim; intro w96
  apply SepWPp.exists_elim; intro w104
  apply SepWPp.exists_elim; intro w112
  apply SepWPp.exists_elim; intro w120
  apply SepWPp.exists_elim; intro w128
  apply SepWPp.exists_elim; intro w136
  apply SepWPp.exists_elim; intro w144
  apply SepWPp.exists_elim; intro w152
  apply SepWPp.exists_elim; intro w160
  apply SepWPp.exists_elim; intro w168
  apply SepWPp.exists_elim; intro w176
  apply SepWPp.exists_elim; intro w184
  apply SepWPp.exists_elim; intro w192
  apply SepWPp.exists_elim; intro w200
  apply SepWPp.exists_elim; intro w208
  apply SepWPp.exists_elim; intro w216
  have hscratch_split :
      ∀ (Rest : SepProp),
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        memRegion (s0.sp - 1360#64) 880 ∗
        memRegion (s0.sp - 480#64) 176 ∗
        memRegion (s0.sp - 256#64) 160 ∗ Rest ⊢
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        (∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64,
         ∃∗ t4 : BitVec 64, ∃∗ t5 : BitVec 64, ∃∗ t6 : BitVec 64, ∃∗ t7 : BitVec 64,
         ∃∗ t8 : BitVec 64, ∃∗ t9 : BitVec 64, ∃∗ t10 : BitVec 64, ∃∗ t11 : BitVec 64,
         ∃∗ t12 : BitVec 64, ∃∗ t13 : BitVec 64, ∃∗ t14 : BitVec 64, ∃∗ t15 : BitVec 64,
         ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
         ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
         ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
           ekReceivedScratchCells s0.sp
             t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
             u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
           memRegion (s0.sp - 1232#64) 56 ∗
           memRegion (s0.sp - 1176#64) 696 ∗
           memRegion (s0.sp - 432#64) 128 ∗
           memRegion (s0.sp - 208#64) 112) ∗ Rest := by
    intro Rest
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       memRegion (s0.sp - 256#64) 160) ∗ Rest by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left (memRegion_ekReceived_scratch_split s0.sp))
  refine SepWPp.weaken_pre (hscratch_split _) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro t0
  apply SepWPp.exists_elim; intro t1
  apply SepWPp.exists_elim; intro t2
  apply SepWPp.exists_elim; intro t3
  apply SepWPp.exists_elim; intro t4
  apply SepWPp.exists_elim; intro t5
  apply SepWPp.exists_elim; intro t6
  apply SepWPp.exists_elim; intro t7
  apply SepWPp.exists_elim; intro t8
  apply SepWPp.exists_elim; intro t9
  apply SepWPp.exists_elim; intro t10
  apply SepWPp.exists_elim; intro t11
  apply SepWPp.exists_elim; intro t12
  apply SepWPp.exists_elim; intro t13
  apply SepWPp.exists_elim; intro t14
  apply SepWPp.exists_elim; intro t15
  apply SepWPp.exists_elim; intro u0
  apply SepWPp.exists_elim; intro u1
  apply SepWPp.exists_elim; intro u2
  apply SepWPp.exists_elim; intro u3
  apply SepWPp.exists_elim; intro u4
  apply SepWPp.exists_elim; intro u5
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v1
  apply SepWPp.exists_elim; intro v2
  apply SepWPp.exists_elim; intro v3
  apply SepWPp.exists_elim; intro v4
  apply SepWPp.exists_elim; intro v5
  have hstep2 := ekReceivedCt1Sampled_step_60_to_1760 s0 s1 out stA
    a0 a1 a2 a3 a4 a5 cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1.length
    t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    (memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392 ∗ A.pool)
    hb_align hsp0_align hlen hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
  refine DecoderPb.SepWPp.seq_clean
    (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep2) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx20_2, hx21_2, hx23_2, hx24_2,
    hx26_2, hx27_2, hx28_2, htr2⟩
  rw [stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)]
  refine SepWPp.weaken_pre ?_
    (ekReceivedCt1Sampled_step_1760_to_2252 hA s0 s2 out stA cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1
      (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
       ekReceivedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
         u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
       memRegion (s0.sp - 1232#64) 56 ∗
       memRegion (s0.sp - 1176#64) 696 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112 ∗
       memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 10#64) ∗
       statesIntoPbJumpTableAt b ∗
       memRegion out optProtoInnerStateSize ∗
       polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
       ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
       memRegion (stA + 536#64) 392)
      R hsp0_align hlen hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx23_2 hx24_2
      hx26_2 hx27_2 hx28_2 htr2 ?_)
  · exact Entails.of_eq (by ac_rfl)
  intro s3 ptr_new hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
    hx26_3 hx27_3 hx28_3 htr3
  have hstep4 := ekReceivedCt1Sampled_step_2252_to_2324 hA s0 s3 out stA
    cap_ct1 ptr_ct1 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2
    t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    (vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
    hx26_3 hx27_3 hx28_3 htr3
  refine DecoderPb.SepWPp.seq_clean
    (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep4) ?_
  intro s4 hpc4 hrun4 ⟨hsp4, hx29_4, hx19_4, hx20_4, hx21_4, hx22_4, hx27_4, hx28_4, htr4⟩
  have hrecomb_stack :
      memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗ stackAt (s0.sp - 1520#64) allocHookStack =
      stackAt (s0.sp - 1520#64) encoderIntoPbStack :=
    (stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)).symm
  refine SepWPp.weaken_pre ?_
    (ekReceivedCt1Sampled_step_2324_to_2340 henc_raw s0 s4 out stA ptr_new
      (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch s.sending_ct1
      (((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       ekReceivedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
         es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1176#64) 696 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112 ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 10#64) ∗
       statesIntoPbJumpTableAt b ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
       memRegion (stA + 536#64) 392)
      R hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hx20_4 hx21_4 hx22_4 hx27_4 hx28_4 htr4 ?_)
  · rw [← hrecomb_stack]
    exact Entails.of_eq (by ac_rfl)
  intro s5 e0 e1 e2 e3 e4 e5 e6 hpc5 hrun5 hsp5 hx29_5 hx19_5 hx20_5 hx21_5 hx22_5
    hx27_5 hx28_5 htr5
  have hstep6 := ekReceivedCt1Sampled_step_2340_to_1544 s0 s5 out stA ptr_new
    (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2
    e0 e1 e2 e3 e4 e5 e6
    t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
    (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     memRegion (stA + 8#64) polyEncoderSize ∗
     A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc5 hrun5 hsp5 hx29_5 hx19_5 hx20_5 hx21_5 hx22_5 hx27_5 hx28_5 htr5
  refine DecoderPb.SepWPp.seq_clean
    (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep6) ?_
  intro s6 hpc6 hrun6 ⟨hsp6, hx29_6, hx19_6, hx21_6, hx22_6, htr6⟩
  have hscratch := ekReceivedScratchCells_entails_memRegions s0.sp
    es0 es1 es2 ek0 ek1 ek2 t6 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
    es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
  have hstA := stA_ekReceivedCt1Sampled_entails_928 stA
    a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2
    cap_ct1 ptr_ct1 (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
  have hpre_epi :
      ekReceivedScratchCells s0.sp
        es0 es1 es2 ek0 ek1 ek2 t6 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
        es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
      (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
       ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
       ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
       ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
      epilogueStagingCells s0.sp
        es0 es1 es2 ek0 ek1 ek2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch e0 e1 e2 e3 e4 e5 e6
        w192 w200 w208 w216 ∗
      (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       memRegion (stA + 8#64) polyEncoderSize ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1176#64) 696 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 10#64) ∗
       statesIntoPbJumpTableAt b ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
       memRegion (stA + 536#64) 392) ⊢
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        es0 es1 es2 ek0 ek1 ek2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch e0 e1 e2 e3 e4 e5 e6
        w192 w200 w208 w216 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTableAt b ∗ A.pool) := by
    refine Entails.trans (Entails.of_eq (show _ =
      (ekReceivedScratchCells s0.sp
         es0 es1 es2 ek0 ek1 ek2 t6 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
         es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
        ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
        ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
        ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
       memRegion (s0.sp - 1176#64) 696 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112) ∗
      ((stA ↦₆₄ 10#64) ∗
       memRegion (stA + 8#64) polyEncoderSize ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (stA + 536#64) 392) ∗
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       epilogueStagingCells s0.sp
         es0 es1 es2 ek0 ek1 ek2
         ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
         s.uc.epoch e0 e1 e2 e3 e4 e5 e6
         w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗
       protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       statesIntoPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hscratch (sepConj_mono hstA (Entails.refl _))) ?_
    exact Entails.of_eq (by ac_rfl)
  apply SepWPp.of_sepWP_ret
  have hep := states_into_pb_epilogue s0 s6 out
    es0 es1 es2 ek0 ek1 ek2
    ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
    s.uc.epoch e0 e1 e2 e3 e4 e5 e6
    w192 w200 w208 w216
    (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
     vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc6 hrun6 hsp6 hx29_6 hx19_6 htr6
  rw [hx22_6, hx21_6] at hep
  unfold StatesIntoPbPost
  refine SepWP.strengthen_entails_const ?_ (SepWP.weaken_pre hpre_epi hep)
  have hout := outWords28_entails_ekReceivedCt1Sampled A out
    es0 es1 es2 ek0 ek1 ek2
    (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
    a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
    w192 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
       0x8000000000000008#64
       es0 es1 es2 ek0 ek1 ek2
       (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
       a0 a1 a2 a3 a4 a5 s.uc.epoch
       e0 e1 e2 e3 e4 e5 e6
       w192 w200 w208 w216 ∗
     protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
     vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack) by ac_rfl)) ?_
  exact sepConj_mono_left hout

end CryptoVerification.SpqrV1.States.IntoPb
