/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5d
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5Placed
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Placed
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 5d Placed: Arm 7 (`States.ct1Sampled`) Step Lemmas

Relocatable `[LibsignalPlacement]` step lemmas on Block `334` for Arm 7 (`States.ct1Sampled`),
re-exporting representation exposure and reassembly helpers from `Part5d.lean`.
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

/-! ## Step Lemmas for Arm 7 (`+60 -> +1712 -> +2028 -> +2100 -> +2116 -> +2128 -> +1544`) -/

/-- Step 1b (`+60 -> +1712` in Block `334`): jump via index `7` (`x8 = polyEncoderTag enc` -> `+828`),
    load `auth`, `cap_ct1`, `ptr_ct1`, `len_ct1`, and `epoch` from `stA + 400..520`,
    stage `auth` into `s0.sp - 1360..1312` (`t0..t5`), and take `tbz x22, #0x3f, +1712`. -/
theorem ct1Sampled_step_60_to_1712_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64) (enc : PolyEncoder)
    (a0 a1 a2 a3 a4 a5 cap_ct1 ptr_ct1 epoch : BitVec 64) (len_ct1 : Nat)
    (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : len_ct1 < 2 ^ 63)
    (hpc : s.pc = (blkPl_334).base + 60#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (hx8 : s.readReg64 .x8 = polyEncoderTag enc)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 1712#64) s
      (statesIntoPbJumpTablePlacedAt ∗
       ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
       ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
       ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
       ((stA + 520#64) ↦₆₄ epoch) ∗
       ekReceivedScratchCells s0.sp
         t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
         u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
       Rest)
      (fun sm Pm =>
        (Pm ⊢
          statesIntoPbJumpTablePlacedAt ∗
          ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
          ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
          ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
          ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
          ((stA + 520#64) ↦₆₄ epoch) ∗
          ekReceivedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
            u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
          Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 len_ct1 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hmsb := ofNat_lt_2pow63_msb_zero hlen
  have hand := ofNat_lt_2pow63_and_highBit_zero hlen
  have hlsr := ofNat_lt_2pow63_lsr63_zero hlen
  dsimp only [statesIntoPbJumpTablePlacedAt, statesIntoPbJumpTableBytes, ekReceivedScratchCells,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  rcases polyEncoderTag_eq_zero_or_one enc with htag | htag <;>
    (rw [htag] at hx8; wp_steps; refine DropGlueFacts.align_pre (by ac_rfl) ?_; wp_done)

/-- Step 2 (`+1712 -> +2028` in Block `334`): clone `s.uc.ct1` into `x21 = ptr_new` (or panic at `+884` on OOM). -/
theorem ct1Sampled_step_1712_to_2028_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : StatesIntoPbAllocPlaced A ext)
    (s0 s : State) (out stA cap_ct1 ptr_ct1 epoch : BitVec 64)
    (ct1 : List (BitVec 8))
    (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : ct1.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_334).base + 1712#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ct1.length)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (ptr_new : BitVec 64),
      sm.pc = (blkPl_334).base + 2028#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x21 = ptr_new →
      sm.readReg64 .x22 = BitVec.ofNat 64 ct1.length →
      sm.readReg64 .x23 = cap_ct1 →
      sm.readReg64 .x24 = ptr_ct1 →
      sm.readReg64 .x26 = s0.sp - 480#64 →
      sm.readReg64 .x27 = s0.sp - 1360#64 →
      sm.readReg64 .x28 = epoch →
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
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx22 hlen hnext ⊢
    refine DecoderPb.SepWPp.seq_clean
      (mid := (blkPl_334).base + 2028#64)
      (P_mid :=
        vecU8Heap A 0#64 1#64 0#64 [] ∗
        vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
      (Q_mid := fun sm =>
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x21 = 1#64 ∧
        sm.readReg64 .x22 = 0#64 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = epoch ∧
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
    have hshim := hA.shim_ok
    have halloc := hA.alloc_ok
    have hmemcpy := hA.memcpy_ok
    have hpanic : ∀ (sm : State) (P_mid : SepProp),
        sm.pc = (blkPl_334).base + 884#64 →
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
      exact states_into_pb_panic_884_placed hA s0 sm P_mid R hpcm hrunm htrm
    simp only [noAllocShimSpec] at hshim
    simp only [rustAllocSpec] at halloc
    simp only [framelessMemcpySpec] at hmemcpy
    dsimp only [BitVec.ofNat_eq_ofNat] at hpc hshim halloc hmemcpy hpanic ⊢
    apply SepWPp.of_sepWP (mid := (blkPl_334).base + 1736#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte]
      refine DecoderPb.sepWPp_pure_mid fun htr_oom => ?_
      refine DecoderPb.SepWPp.seq_clean (mid := (blkPl_334).base + 884#64)
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
      refine DecoderPb.SepWPp.seq_clean (mid := (blkPl_334).base + 2028#64)
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
          sm.readReg64 .x21 = ptr_c ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 ct1.length ∧
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

/-- Step 3 (`+2028 -> +2100` in Block `334`): move `auth` from `s0.sp - 1360..1312` (`t0..t5`) to
    `s0.sp - 256..208` (`v0..v5`), load `hdr` and `es` from `stA + 448..488` into
    `s0.sp - 480..432` (`u0..u5`), and deallocate `(cap_ct1, ptr_ct1)` via
    `cbz x23, +2100; bl __rust_dealloc`. -/
theorem ct1Sampled_step_2028_to_2100_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (s0 s : State) (out stA cap_ct1 ptr_ct1 ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 : BitVec 64)
    (t6 t7 t8 t8' t9 t10 t11 t12 t13 t14 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2028#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = ptr_new)
    (hx22 : s.readReg64 .x22 = len_ct1)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 2100#64) s
      (((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
       ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
       ekReceivedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 t6 t7 t8 t8' t9 t10 t11 t12 t13 t14
         u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
       vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
          ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
          ekReceivedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 t6 t7 t8 t8' t9 t10 t11 t12 t13 t14
            hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x21 = ptr_new ∧
        sm.readReg64 .x22 = len_ct1 ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hdealloc := hA.dealloc_ok
  simp only [rustDeallocSpec] at hdealloc
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  dsimp only [ekReceivedScratchCells, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc hdealloc ⊢
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

/-- Step 4 (`+2100 -> +2116` in Block `334`): call `<PolyEncoder>::into_pb(s0.sp - 1232, stA)`. -/
theorem ct1Sampled_step_2100_to_2116_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (henc : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec A))
    (s0 s : State) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (enc : PolyEncoder)
    (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = ptr_new)
    (hx22 : s.readReg64 .x22 = len_ct1)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      sm.pc = (blkPl_334).base + 2116#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x21 = ptr_new →
      sm.readReg64 .x22 = len_ct1 →
      sm.readReg64 .x23 = s0.sp - 1360#64 →
      sm.readReg64 .x27 = s0.sp - 1360#64 →
      sm.readReg64 .x28 = epoch →
      TraceCalleeSaved sm s0 →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm
        ((((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
          ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
          ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
          ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
         protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
         memRegion stA polyEncoderSize ∗
         A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion (s0.sp - 1232#64) 56 ∗
       polyEncoderAt A stA enc ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      Q (StatesIntoPbPanic s0 R) := by
  rcases htrace with ⟨htrace, hvregs⟩
  refine DecoderPb.SepWPp.seq_clean
    (mid := lsmpl.base 375)
    (P_mid :=
      memRegion (s0.sp - 1232#64) 56 ∗
      polyEncoderAt A stA enc ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
    (Q_mid := fun sm =>
      sm.sp = s0.sp - 1520#64 ∧
      sm.readReg64 .x29 = s0.sp - 96#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = stA ∧
      sm.readReg64 .x21 = ptr_new ∧
      sm.readReg64 .x22 = len_ct1 ∧
      sm.readReg64 .x23 = s0.sp - 1360#64 ∧
      sm.readReg64 .x27 = s0.sp - 1360#64 ∧
      sm.readReg64 .x28 = epoch ∧
      sm.readReg64 .x0 = s0.sp - 1232#64 ∧
      sm.readReg64 .x1 = stA ∧
      sm.readReg64 .x30 = (blkPl_334).base + 2116#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · wp_steps
    wp_done
  · intro s_call hpc_call hrun_call ⟨hsp_c, hx29_c, hx19_c, hx20_c, hx21_c, hx22_c,
      hx23_c, hx27_c, hx28_c, hx0_c, hx1_c, hx30_c, htr_c⟩
    have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
    exact call_encoderIntoPb_expose_placed henc
      (s0.sp - 1232#64) stA enc
      hpc_call hrun_call hsp_c hfsp_align hx30_c htr_c hx0_c hx1_c
      (by change _ = (memRegion (s0.sp - 1232#64) 56 ∗ polyEncoderAt A stA enc ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame; ac_rfl)
      (fun sm e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspm hcc htrm => by
        refine SepWPp.weaken_pre ?_
          (hnext sm e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspm
            (hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx29_c)
            (hcc.1.trans hx19_c)
            (hcc.2.1.trans hx20_c)
            (hcc.2.2.1.trans hx21_c)
            (hcc.2.2.2.1.trans hx22_c)
            (hcc.2.2.2.2.1.trans hx23_c)
            (hcc.2.2.2.2.2.2.2.2.1.trans hx27_c)
            (hcc.2.2.2.2.2.2.2.2.2.1.trans hx28_c)
            htrm)
        exact Entails.of_eq (by simp only [arm64_norm]))

/-- Step 5 (`+2116 -> +2128` in Block `334`): call `<PolyDecoder>::into_pb(s0.sp - 1176, stA + 528)`. -/
theorem ct1Sampled_step_2116_to_2128_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec A))
    (s0 s : State) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (dec : PolyDecoder)
    (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = ptr_new)
    (hx22 : s.readReg64 .x22 = len_ct1)
    (hx23 : s.readReg64 .x23 = s0.sp - 1360#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (d0 d1 d2 d3 d4 : BitVec 64),
      sm.pc = (blkPl_334).base + 2128#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x21 = ptr_new →
      sm.readReg64 .x22 = len_ct1 →
      sm.readReg64 .x27 = s0.sp - 1360#64 →
      sm.readReg64 .x28 = epoch →
      TraceCalleeSaved sm s0 →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm
        ((((s0.sp - 1176#64) ↦₆₄ d0) ∗ ((s0.sp - 1168#64) ↦₆₄ d1) ∗
          ((s0.sp - 1160#64) ↦₆₄ d2) ∗ ((s0.sp - 1152#64) ↦₆₄ d3) ∗
          ((s0.sp - 1144#64) ↦₆₄ d4)) ∗
         protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 dec.intoPb ∗
         memRegion (stA + 528#64) polyDecoderSize ∗
         A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion (s0.sp - 1176#64) 40 ∗
       polyDecoderAt A (stA + 528#64) dec ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      Q (StatesIntoPbPanic s0 R) := by
  rcases htrace with ⟨htrace, hvregs⟩
  refine DecoderPb.SepWPp.seq_clean
    (mid := lsmpl.base 377)
    (P_mid :=
      memRegion (s0.sp - 1176#64) 40 ∗
      polyDecoderAt A (stA + 528#64) dec ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
    (Q_mid := fun sm =>
      sm.sp = s0.sp - 1520#64 ∧
      sm.readReg64 .x29 = s0.sp - 96#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = ptr_new ∧
      sm.readReg64 .x22 = len_ct1 ∧
      sm.readReg64 .x27 = s0.sp - 1360#64 ∧
      sm.readReg64 .x28 = epoch ∧
      sm.readReg64 .x0 = s0.sp - 1176#64 ∧
      sm.readReg64 .x1 = stA + 528#64 ∧
      sm.readReg64 .x30 = (blkPl_334).base + 2128#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · wp_steps
    wp_done
  · intro s_call hpc_call hrun_call ⟨hsp_c, hx29_c, hx19_c, hx21_c, hx22_c,
      hx27_c, hx28_c, hx0_c, hx1_c, hx30_c, htr_c⟩
    have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
    exact call_decoderIntoPb_expose_placed hdec
      (s0.sp - 1176#64) (stA + 528#64) dec
      hpc_call hrun_call hsp_c hfsp_align hx30_c htr_c hx0_c hx1_c
      (by change _ = (memRegion (s0.sp - 1176#64) 40 ∗ polyDecoderAt A (stA + 528#64) dec ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame; ac_rfl)
      (fun sm d0 d1 d2 d3 d4 hpcm hrunm hspm hcc htrm => by
        refine SepWPp.weaken_pre ?_
          (hnext sm d0 d1 d2 d3 d4 hpcm hrunm hspm
            (hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx29_c)
            (hcc.1.trans hx19_c)
            (hcc.2.2.1.trans hx21_c)
            (hcc.2.2.2.1.trans hx22_c)
            (hcc.2.2.2.2.2.2.2.2.1.trans hx27_c)
            (hcc.2.2.2.2.2.2.2.2.2.1.trans hx28_c)
            htrm)
        exact Entails.of_eq (by simp only [arm64_norm]))

/-- Step 6 (`+2128 -> +1544` in Block `334`): pack `hdr`, `es`, `ct1`, `auth`, `epoch`,
    `sending_ct1.intoPb`, and `receiving_ek.intoPb` into `epilogueStagingCells`
    (with `x22 = hdr0` and `x21 = ptr_new`) and branch to `+1544`. -/
theorem ct1Sampled_step_2128_to_1544_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : BitVec 64)
    (w8 w16 w24 w32 w40 w48
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2128#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = ptr_new)
    (hx22 : s.readReg64 .x22 = len_ct1)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 1544#64) s
      (ekReceivedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
         hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
        ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
        ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
        ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
       (((s0.sp - 1176#64) ↦₆₄ d0) ∗ ((s0.sp - 1168#64) ↦₆₄ d1) ∗
        ((s0.sp - 1160#64) ↦₆₄ d2) ∗ ((s0.sp - 1152#64) ↦₆₄ d3) ∗
        ((s0.sp - 1144#64) ↦₆₄ d4)) ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48
         w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184
         w192 w200 w208 w216 ∗
       Rest)
      (fun sm Pm =>
        (Pm ⊢
          ekReceivedScratchCells s0.sp
            hdr0 hdr1 hdr2 es0 es1 es2 len_ct1 t7 len_ct1 a0 a1 a2 a3 a4 a5 epoch
            hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
          (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
           ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
           ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
           ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
          (((s0.sp - 1176#64) ↦₆₄ d0) ∗ ((s0.sp - 1168#64) ↦₆₄ d1) ∗
           ((s0.sp - 1160#64) ↦₆₄ d2) ∗ ((s0.sp - 1152#64) ↦₆₄ d3) ∗
           ((s0.sp - 1144#64) ↦₆₄ d4)) ∗
          epilogueStagingCells s0.sp
            hdr1 hdr2 es0 es1 es2 len_ct1
            len_ct1 a0 a1 a2 a3 a4 a5
            epoch e0 e1 e2 e3 e4 e5 e6
            d0 d1 d2 d3 d4 ∗
          Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = ptr_new ∧
        sm.readReg64 .x22 = hdr0 ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  dsimp only [ekReceivedScratchCells, epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  refine DropGlueFacts.align_pre (by ac_rfl) ?_
  wp_done

end CryptoVerification.SpqrV1.States.IntoPb
