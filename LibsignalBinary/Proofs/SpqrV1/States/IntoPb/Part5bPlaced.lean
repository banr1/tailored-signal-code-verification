/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5b
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5Placed
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 5b Placed: Arm 9 (`States.ct1Acknowledged`) Step Lemmas

Relocatable `[LibsignalPlacement]` step lemmas on Block `334` for Arm 9 (`States.ct1Acknowledged`,
tag `11`), re-exporting representation exposure and scratch helpers from `Part5b.lean`.
-/

@[expose] public section

set_option autoImplicit false

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

open CryptoVerification.SpqrV1.States.IntoPb.Placed

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

/-! ## Step Lemmas for Arm 9 (`+60 -> +360 -> +376 -> +424 -> +1812 -> +1884 -> +1904 -> +1544`) -/

/-- Step 1b (`+60 -> +372` in Block `334`): jump-table dispatch for tag `11#64` (index `9` -> `+360`) and setup
    for `memcpy(s0.sp - 1360, stA + 8, 528)` at `+372`. -/
theorem ct1Acknowledged_step_60_to_372_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64)
    (Rest : SepProp)
    (hpc : s.pc = (blkPl_334).base + 60#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (hx8 : s.readReg64 .x8 = 11#64)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") s
      (statesIntoPbJumpTablePlacedAt ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ statesIntoPbJumpTablePlacedAt ∗ Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x30 = (blkPl_334).base + 376#64 ∧
        sm.readReg64 .x0 = s0.sp - 1360#64 ∧
        sm.readReg64 .x1 = stA + 8#64 ∧
        (sm.readReg64 .x2).toNat = 528 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x28 = s0.sp - 256#64 ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  dsimp only [statesIntoPbJumpTablePlacedAt, statesIntoPbJumpTableBytes, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

/-- Step 2 (`+376 -> +424` in Block `334`): load `cap_ct1`, `ptr_ct1`, `len_ct1`, `epoch` from `s0.sp - 1264..1240`,
    copy `a0..a5` from `stA + 8..48` to `s0.sp - 480..440` (`u0..u5`), and take fallthrough of
    `tbnz x21, #0x3f, +1696`. -/
theorem ct1Acknowledged_step_376_to_424_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 cap_ct1 ptr_ct1 epoch : BitVec 64)
    (len_ct1 : Nat)
    (u0 u1 u2 u3 u4 u5 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64)
    (y0 y1 y2 y3 y4 y5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : len_ct1 < 2 ^ 63)
    (hpc : s.pc = (blkPl_334).base + 376#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 424#64) s
      ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
        ((s0.sp - 1240#64) ↦₆₄ epoch)) ∗
       ct1AcknowledgedScratchCells s0.sp
         u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
         w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
       Rest)
      (fun sm Pm =>
        (Pm ⊢
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
           ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
           ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
          (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
           ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
           ((s0.sp - 1240#64) ↦₆₄ epoch)) ∗
          ct1AcknowledgedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
            w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
          Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x28 = s0.sp - 256#64 ∧
        sm.readReg64 .x27 = epoch ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 len_ct1 ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hmsb := ofNat_lt_2pow63_msb_zero hlen
  have hand := ofNat_lt_2pow63_and_highBit_zero hlen
  have hlsr := ofNat_lt_2pow63_lsr63_zero hlen
  dsimp only [ct1AcknowledgedScratchCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  refine DropGlueFacts.align_pre (by ac_rfl) ?_
  wp_done

/-- Step 3 (`+424 -> +1812` in Block `334`): clone `s.uc.ct1`. -/
theorem ct1Acknowledged_step_424_to_1812_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : StatesIntoPbAllocPlaced A ext)
    (s0 s : State) (out stA cap_ct1 ptr_ct1 epoch : BitVec 64)
    (ct1 : List (BitVec 8))
    (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : ct1.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_334).base + 424#64)
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
      sm.pc = (blkPl_334).base + 1812#64 →
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
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm
        (vecU8Heap A (BitVec.ofNat 64 ct1.length) ptr_new (BitVec.ofNat 64 ct1.length) ct1 ∗
         vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
         A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
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
      (mid := (blkPl_334).base + 1812#64)
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
    · wp_steps
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
    have hshim := hA.shim_ok
    have halloc := hA.alloc_ok
    have hmemcpy := hA.memcpy_ok
    have hpanic : ∀ (sm : State) (P_mid : SepProp),
        sm.pc = (blkPl_334).base + 1700#64 →
        sm.status = .Running →
        sm.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm P_mid Q
          (StatesIntoPbPanic s0 R) := by
      intro sm P_mid hpcm hrunm htrm
      have heq : (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesIntoPbOnPanic s0 sf ∗ R)) =
          StatesIntoPbPanic s0 R := by
        funext sf P_f
        simp only [StatesIntoPbPanic, statesIntoPbOnPanic, sepConj_assoc]
      rw [← heq]
      exact states_into_pb_panic_1700_placed hA s0 sm P_mid R hpcm hrunm htrm
    simp only [noAllocShimSpec] at hshim
    simp only [rustAllocSpec] at halloc
    simp only [framelessMemcpySpec] at hmemcpy
    dsimp only [BitVec.ofNat_eq_ofNat] at hpc hshim halloc hmemcpy hpanic ⊢
    apply SepWPp.of_sepWP (mid := (blkPl_334).base + 448#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte]
      refine DecoderPb.sepWPp_pure_mid fun htr_oom => ?_
      refine DecoderPb.SepWPp.seq_clean (mid := (blkPl_334).base + 1700#64)
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
      refine DecoderPb.SepWPp.seq_clean (mid := (blkPl_334).base + 1812#64)
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
      · intro sm hpcm hrunm ⟨hspm, hx29m, hx28m, hx27m, hx26m, hx24m, hx23m,
          hx22m, hx21m, hx20m, hx19m, htrm⟩
        exact hnext sm ptr_c hpcm hrunm hspm hx29m hx28m hx27m hx26m hx24m hx23m
          hx22m hx21m hx20m hx19m htrm

/-- Step 4 (`+1812 -> +1900` in Block `334`): move `a0..a5` from `s0.sp - 480..440` (`u0..u5`) to
    `s0.sp - 160..120` (`y0..y5`), copy `hdr0..hdr2, es0..es2` from `stA + 56..96` to
    `s0.sp - 256..216` (`w0..w5`), deallocate `(cap_ct1, ptr_ct1)` via `__rust_dealloc`,
    and set up `<PolyDecoder>::into_pb(s0.sp - 352, s0.sp - 1232)` at `+1900` (`lsmpl.base 377`). -/
theorem ct1Acknowledged_step_1812_to_1900_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (s0 s : State) (out stA cap_ct1 ptr_ct1 ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64)
    (y0 y1 y2 y3 y4 y5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 1812#64)
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
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) s
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
        sm.readReg64 .x30 = (blkPl_334).base + 1904#64 ∧
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
  have hdealloc := hA.dealloc_ok
  simp only [rustDeallocSpec] at hdealloc
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  dsimp only [ct1AcknowledgedScratchCells, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc hdealloc ⊢
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
    wp_steps
    refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
    wp_done

/-- Step 5 (`+1904 -> +1544` in Block `334`): pack `hdr`, `es`, `ct1`, `auth`, `epoch`, and `receiving_ek.intoPb`
    into `epilogueStagingCells` and branch to `+1544`. -/
theorem ct1Acknowledged_step_1904_to_1544_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w8 w16 w24 w32 w40 w48
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 1904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx27 : s.readReg64 .x27 = epoch)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 1544#64) s
      (ct1AcknowledgedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
         hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 352#64) ↦₆₄ d0) ∗ ((s0.sp - 344#64) ↦₆₄ d1) ∗
        ((s0.sp - 336#64) ↦₆₄ d2) ∗ ((s0.sp - 328#64) ↦₆₄ d3) ∗
        ((s0.sp - 320#64) ↦₆₄ d4)) ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48
         w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184
         w192 w200 w208 w216 ∗
       Rest)
      (fun sm Pm =>
        (Pm ⊢
          ct1AcknowledgedScratchCells s0.sp
            hdr0 hdr1 hdr2 es0 es1 es2
            ptr_new len_ct1 a0 a1 a2 a3 a4 a5 epoch
            hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
          (((s0.sp - 352#64) ↦₆₄ d0) ∗ ((s0.sp - 344#64) ↦₆₄ d1) ∗
           ((s0.sp - 336#64) ↦₆₄ d2) ∗ ((s0.sp - 328#64) ↦₆₄ d3) ∗
           ((s0.sp - 320#64) ↦₆₄ d4)) ∗
          epilogueStagingCells s0.sp
            hdr0 hdr1 hdr2 es0 es1 es2
            ptr_new len_ct1 a0 a1 a2 a3 a4 a5
            epoch d0 d1 d2 d3 d4 w176 w184
            w192 w200 w208 w216 ∗
          Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = len_ct1 ∧
        sm.readReg64 .x22 = 0x8000000000000009#64 ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  dsimp only [ct1AcknowledgedScratchCells, epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  refine DropGlueFacts.align_pre (by ac_rfl) ?_
  wp_done

end CryptoVerification.SpqrV1.States.IntoPb
