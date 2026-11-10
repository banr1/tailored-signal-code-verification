/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErr
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Relocatable `ChainEpochPB` Error Drop Blocks

Relocatable `[LibsignalPlacement]` proofs of the `ChainEpochPB` drop and `DecodeError` unwind blocks.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.DecodeState.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Common stack/heap frame during `ChainEpochPB` error drop under `[LibsignalPlacement]`. -/
abbrev decodeStateEpochErrTailFramePlaced [LibsignalPlacement] (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 : State) : SepProp :=
  v1StateJumpTablesPlacedAt ∗
  x.st.at A ∗
  memRegion x.outPtr 352 ∗
  A.pool ∗
  stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
  memRegion (s0.sp - 1392#64) 352 ∗
  protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
  memRegion (s0.sp - 576#64) 240 ∗
  memRegion (s0.sp - 336#64) 240 ∗
  decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)

/-- Complete `ChainEpochPB` error frame under `[LibsignalPlacement]`. -/
abbrev decodeStateEpochErrFramePlaced [LibsignalPlacement] (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 : State) : SepProp :=
  chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
  decodeStateEpochErrTailFramePlaced H_inner A x curSt s0

set_option maxHeartbeats 800000 in
/-- Drop `curEpoch.recv : Option EpochDirectionPB` at `[sp + 0x2f8]` (`s0.sp - 632#64`) and
    continue to `decodeState_err_push_53c9c_placed` (`+1984`, 16 instructions). -/
theorem decodeState_err_drop_epoch_recv_53c5c_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (optRecv : Option EpochDirectionPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1984#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx1 : s.readReg64 .x1 = errBox)
    (hx20 : s.readReg64 .x20 = errBox)
    (hP : P =
      decodeErrorAtStackLen A errBox n ∗
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      memRegion (s0.sp - 680#64) 48 ∗
      optEpochDirectionPBAt A (s0.sp - 632#64) optRecv ∗
      decodeStateEpochErrTailFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hdealloc := hc.dealloc
  simp only [rustDeallocSpec] at hdealloc
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrTailFramePlaced] at hpc hdealloc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2048#64)
  cases optRecv with
  | none =>
    rw [optEpochDirectionPBAt_none]
    have ha624 : (s0.sp - 632#64) + 8#64 = s0.sp - 624#64 := by bv_omega
    rw [ha624]
    wp_steps
    refine SepWP.fold (epochDirection_recv_none_to_56 s0.sp noneCap) (by sep_focus) ?_
    refine SepWP.fold (epoch_regions_to_err_frame s0.sp) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    exact decodeState_err_push_53c9c_placed hc x curSt w0 n s0 _ _ R post hpost herr hn
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx1]; dsimp only [decodeStateErrFramePlaced]; ac_rfl)
  | some d =>
    rw [optEpochDirectionPBAt_some]
    unfold epochDirectionPBAt
    have ha608 : (s0.sp - 632#64) + 0x18#64 = s0.sp - 608#64 := by bv_omega
    have ha584 : (s0.sp - 632#64) + 0x30#64 = s0.sp - 584#64 := by bv_omega
    have ha580 : (s0.sp - 632#64) + 0x34#64 = s0.sp - 580#64 := by bv_omega
    rw [ha608, ha584, ha580]
    refine SepWP.fold (rustBytesVecAt_unfold_drop A (s0.sp - 632#64) d.next) (by sep_focus) ?_
    wp_pull_exists
    rename_i cap1 ptr1
    wp_focus_pure; rintro ⟨_, hlt1, hptr1⟩
    refine SepWP.fold (rustBytesVecAt_unfold_drop A (s0.sp - 608#64) d.prev) (by sep_focus) ?_
    wp_pull_exists
    rename_i cap2 ptr2
    wp_focus_pure; rintro ⟨_, hlt2, hptr2⟩
    have hcmn1 : ¬((cap1 + 1#64 == 0#64) = true) := cap_add_one_beq_zero_false hlt1
    refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
    wp_steps
    by_cases hc1 : cap1 = 0#64 <;> by_cases hc2 : cap2 = 0#64
    · have hb1 : (cap1 == 0#64) = true := beq_iff_eq.mpr hc1
      have hb2 : (cap2 == 0#64) = true := beq_iff_eq.mpr hc2
      simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
      refine SepWP.fold (epochDirection_recv_raw_to_56 s0.sp 0#64 ptr1 (BitVec.ofNat 64 d.next.length)
        0#64 ptr2 (BitVec.ofNat 64 d.prev.length) d.ctr) (by sep_focus) ?_
      refine SepWP.fold (epoch_regions_to_err_frame s0.sp) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      exact decodeState_err_push_53c9c_placed hc x curSt w0 n s0 _ _ R post hpost herr hn
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx1]; dsimp only [decodeStateErrFramePlaced]; ac_rfl)
    · have hb1 : (cap1 == 0#64) = true := beq_iff_eq.mpr hc1
      have hb2 : (cap2 == 0#64) = false := beq_eq_false_iff_ne.mpr hc2
      simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      wp_apply
      wp_conv_pre => simp only [*]
      wp_steps
      refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
      refine SepWP.fold (epochDirection_recv_raw_to_56 s0.sp 0#64 ptr1 (BitVec.ofNat 64 d.next.length)
        cap2 ptr2 (BitVec.ofNat 64 d.prev.length) d.ctr) (by sep_focus) ?_
      refine SepWP.fold (epoch_regions_to_err_frame s0.sp) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      exact decodeState_err_push_53c9c_placed hc x curSt w0 n s0 _ _ R post hpost herr hn
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0A
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; dsimp only [decodeStateErrFramePlaced]; ac_rfl)
    · have hb1 : (cap1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc1
      have hb2 : (cap2 == 0#64) = true := beq_iff_eq.mpr hc2
      simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      wp_apply
      wp_conv_pre => simp only [*]
      wp_steps
      refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
      refine SepWP.fold (epochDirection_recv_raw_to_56 s0.sp cap1 ptr1 (BitVec.ofNat 64 d.next.length)
        0#64 ptr2 (BitVec.ofNat 64 d.prev.length) d.ctr) (by sep_focus) ?_
      refine SepWP.fold (epoch_regions_to_err_frame s0.sp) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      exact decodeState_err_push_53c9c_placed hc x curSt w0 n s0 _ _ R post hpost herr hn
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0A
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; dsimp only [decodeStateErrFramePlaced]; ac_rfl)
    · have hb1 : (cap1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc1
      have hb2 : (cap2 == 0#64) = false := beq_eq_false_iff_ne.mpr hc2
      simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      wp_apply
      wp_conv_pre => simp only [*]
      wp_steps
      wp_apply
      wp_conv_pre => simp only [*]
      wp_steps
      refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
      refine SepWP.fold (epochDirection_recv_raw_to_56 s0.sp cap1 ptr1 (BitVec.ofNat 64 d.next.length)
        cap2 ptr2 (BitVec.ofNat 64 d.prev.length) d.ctr) (by sep_focus) ?_
      refine SepWP.fold (epoch_regions_to_err_frame s0.sp) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      exact decodeState_err_push_53c9c_placed hc x curSt w0 n s0 _ _ R post hpost herr hn
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0A
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; dsimp only [decodeStateErrFramePlaced]; ac_rfl)

set_option maxHeartbeats 800000 in
/-- Drop `d : EpochDirectionPB` (`curEpoch.send = some d`) at `[sp + 0x2c0]` (`s0.sp - 688#64`)
    after `x8 = cap1` has already been loaded and checked `≠ -1`, then continue to
    `decodeState_err_drop_epoch_recv_53c5c_placed` (`+1932`, 13 instructions). -/
theorem decodeState_err_drop_epoch_send_some_53c28_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (optRecv : Option EpochDirectionPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox cap1 ptr1 : BitVec 64)
    (nextBs prevBs : List (BitVec 8)) (ctr : BitVec 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1932#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx8 : s.readReg64 .x8 = cap1)
    (hx1 : s.readReg64 .x1 = errBox)
    (hx20 : s.readReg64 .x20 = errBox)
    (hP : P =
      decodeErrorAtStackLen A errBox n ∗
      ((s0.sp - 688#64) ↦₆₄ cap1) ∗
      ((s0.sp - 680#64) ↦₆₄ ptr1) ∗
      ((s0.sp - 672#64) ↦₆₄ BitVec.ofNat 64 nextBs.length) ∗
      (if cap1 = 0#64 then emp else A.live ptr1 cap1.toNat 1 ∗ memRegion ptr1 cap1.toNat) ∗
      rustBytesVecAt A (s0.sp - 664#64) prevBs ∗
      ((s0.sp - 640#64) ↦₃₂ ctr) ∗
      memRegion (s0.sp - 636#64) 4 ∗
      optEpochDirectionPBAt A (s0.sp - 632#64) optRecv ∗
      decodeStateEpochErrTailFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hdealloc := hc.dealloc
  simp only [rustDeallocSpec] at hdealloc
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrTailFramePlaced] at hpc hdealloc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1984#64)
  refine SepWP.fold (rustBytesVecAt_unfold_drop A (s0.sp - 664#64) prevBs) (by sep_focus) ?_
  wp_pull_exists
  rename_i cap2 ptr2
  wp_focus_pure; rintro ⟨_, hlt2, hptr2⟩
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
  by_cases hc1 : cap1 = 0#64 <;> by_cases hc2 : cap2 = 0#64
  · have hb1 : (cap1 == 0#64) = true := beq_iff_eq.mpr hc1
    have hb2 : (cap2 == 0#64) = true := beq_iff_eq.mpr hc2
    have hx8_b : (s.readReg64 .x8 == 0#64) = true := by rw [hx8]; exact hb1
    simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
    wp_steps
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
    refine SepWP.fold (epochDirection_send_raw_to_48 s0.sp ptr1 (BitVec.ofNat 64 nextBs.length)
      0#64 ptr2 (BitVec.ofNat 64 prevBs.length) ctr) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    exact decodeState_err_drop_epoch_recv_53c5c_placed hc x curSt optRecv n hn errBox 0#64 s0 _ _ R post hpost herr
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx20])
      (by dsimp only [decodeStateEpochErrTailFramePlaced]; ac_rfl)
  · have hb1 : (cap1 == 0#64) = true := beq_iff_eq.mpr hc1
    have hb2 : (cap2 == 0#64) = false := beq_eq_false_iff_ne.mpr hc2
    have hx8_b : (s.readReg64 .x8 == 0#64) = true := by rw [hx8]; exact hb1
    simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
    wp_steps
    wp_apply
    wp_conv_pre => simp only [*]
    wp_steps
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
    refine SepWP.fold (epochDirection_send_raw_to_48 s0.sp ptr1 (BitVec.ofNat 64 nextBs.length)
      cap2 ptr2 (BitVec.ofNat 64 prevBs.length) ctr) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    exact decodeState_err_drop_epoch_recv_53c5c_placed hc x curSt optRecv n hn errBox 0#64 s0 _ _ R post hpost herr
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0A
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateEpochErrTailFramePlaced]; ac_rfl)
  · have hb1 : (cap1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc1
    have hb2 : (cap2 == 0#64) = true := beq_iff_eq.mpr hc2
    have hx8_b : (s.readReg64 .x8 == 0#64) = false := by rw [hx8]; exact hb1
    simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
    wp_steps
    wp_apply
    wp_conv_pre => simp only [hx8, *]
    wp_steps
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
    refine SepWP.fold (epochDirection_send_raw_to_48 s0.sp ptr1 (BitVec.ofNat 64 nextBs.length)
      0#64 ptr2 (BitVec.ofNat 64 prevBs.length) ctr) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    exact decodeState_err_drop_epoch_recv_53c5c_placed hc x curSt optRecv n hn errBox cap1 s0 _ _ R post hpost herr
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0A
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateEpochErrTailFramePlaced]; ac_rfl)
  · have hb1 : (cap1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc1
    have hb2 : (cap2 == 0#64) = false := beq_eq_false_iff_ne.mpr hc2
    have hx8_b : (s.readReg64 .x8 == 0#64) = false := by rw [hx8]; exact hb1
    simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
    wp_steps
    wp_apply
    wp_conv_pre => simp only [hx8, *]
    wp_steps
    wp_apply
    wp_conv_pre => simp only [*]
    wp_steps
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
    refine SepWP.fold (epochDirection_send_raw_to_48 s0.sp ptr1 (BitVec.ofNat 64 nextBs.length)
      cap2 ptr2 (BitVec.ofNat 64 prevBs.length) ctr) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    exact decodeState_err_drop_epoch_recv_53c5c_placed hc x curSt optRecv n hn errBox cap1 s0 _ _ R post hpost herr
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0A
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateEpochErrTailFramePlaced]; ac_rfl)

/-- Drop `curEpoch : ChainEpochPB` at `[sp + 0x2c0]` (`s0.sp - 688#64`) with `errBox` in `x1`,
    then continue to `decodeState_err_push_53c9c_placed` (`+1916`). -/
theorem decodeState_err_drop_epoch_53c18_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1916#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx1 : s.readReg64 .x1 = errBox)
    (hP : P =
      decodeErrorAtStackLen A errBox n ∗
      decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  unfold chainEpochPBAt
  have ha632 : (s0.sp - 688#64) + 0x38#64 = s0.sp - 632#64 := by bv_omega
  rw [ha632]
  rcases hsend : curEpoch.send with _ | d
  · rw [optEpochDirectionPBAt_none]
    have ha680 : (s0.sp - 688#64) + 8#64 = s0.sp - 680#64 := by bv_omega
    rw [ha680]
    apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1984#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    exact decodeState_err_drop_epoch_recv_53c5c_placed hc x curSt curEpoch.recv n hn errBox noneCap s0 _ _ R post hpost herr
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx1])
      (by dsimp only [decodeStateEpochErrTailFramePlaced]; ac_rfl)
  · rw [optEpochDirectionPBAt_some]
    unfold epochDirectionPBAt
    have ha664 : (s0.sp - 688#64) + 0x18#64 = s0.sp - 664#64 := by bv_omega
    have ha640 : (s0.sp - 688#64) + 0x30#64 = s0.sp - 640#64 := by bv_omega
    have ha636 : (s0.sp - 688#64) + 0x34#64 = s0.sp - 636#64 := by bv_omega
    rw [ha664, ha640, ha636]
    apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1932#64)
    refine SepWP.fold (rustBytesVecAt_unfold_drop A (s0.sp - 688#64) d.next) (by sep_focus) ?_
    wp_pull_exists
    rename_i cap1 ptr1
    wp_focus_pure; rintro ⟨_, hlt1, _⟩
    have hcmn1 : ¬((cap1 + 1#64 == 0#64) = true) := cap_add_one_beq_zero_false hlt1
    wp_steps
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    exact decodeState_err_drop_epoch_send_some_53c28_placed hc x curSt curEpoch.recv n hn errBox cap1 ptr1
      d.next d.prev d.ctr s0 _ _ R post hpost herr
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx1])
      (by dsimp only [decodeStateEpochErrTailFramePlaced]; ac_rfl)

/-- Alternate entry (`+2936`, 5 instructions) to drop `curEpoch : ChainEpochPB`
    at `[sp + 0x2c0]` (`s0.sp - 688#64`) with `errBox` in `x1`. -/
theorem decodeState_err_drop_epoch_54014_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2936#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx1 : s.readReg64 .x1 = errBox)
    (hP : P =
      decodeErrorAtStackLen A errBox n ∗
      decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  unfold chainEpochPBAt
  have ha632 : (s0.sp - 688#64) + 0x38#64 = s0.sp - 632#64 := by bv_omega
  rw [ha632]
  rcases hsend : curEpoch.send with _ | d
  · rw [optEpochDirectionPBAt_none]
    have ha680 : (s0.sp - 688#64) + 8#64 = s0.sp - 680#64 := by bv_omega
    have hcmn_ne : (noneCap + 1#64 != 0#64) = false := rfl
    rw [ha680]
    apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1984#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    exact decodeState_err_drop_epoch_recv_53c5c_placed hc x curSt curEpoch.recv n hn errBox noneCap s0 _ _ R post hpost herr
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx1])
      (by dsimp only [decodeStateEpochErrTailFramePlaced]; ac_rfl)
  · rw [optEpochDirectionPBAt_some]; unfold epochDirectionPBAt
    have ha664 : (s0.sp - 688#64) + 0x18#64 = s0.sp - 664#64 := by bv_omega
    have ha640 : (s0.sp - 688#64) + 0x30#64 = s0.sp - 640#64 := by bv_omega
    have ha636 : (s0.sp - 688#64) + 0x34#64 = s0.sp - 636#64 := by bv_omega
    rw [ha664, ha640, ha636]
    apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1932#64)
    refine SepWP.fold (rustBytesVecAt_unfold_drop A (s0.sp - 688#64) d.next) (by sep_focus) ?_
    wp_pull_exists; rename_i cap1 ptr1; wp_focus_pure; rintro ⟨_, hlt1, _⟩
    have hcmn1 : ¬((cap1 + 1#64 == 0#64) = true) := cap_add_one_beq_zero_false hlt1
    have hcmn1_ne : (cap1 + 1#64 != 0#64) = true := by
      rw [bne_iff_ne]; exact fun h => hcmn1 (beq_iff_eq.mpr h)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    exact decodeState_err_drop_epoch_send_some_53c28_placed hc x curSt curEpoch.recv n hn errBox cap1 ptr1
      d.next d.prev d.ctr s0 _ _ R post hpost herr
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx1])
      (by dsimp only [decodeStateEpochErrTailFramePlaced]; ac_rfl)

/-- Shared `DecodeError::from` call at `+1900` (4 instructions)
    using `[x29 - 0xe8]` (`s0.sp - 328#64`), followed by `decodeState_err_drop_epoch_53c18_placed`. -/
theorem decodeState_err_from_epoch_53c08_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (w_e8 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hpc : s.pc = decodeStatePlacedEntry + 1900#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      ((s0.sp - 328#64) ↦₆₄ w_e8) ∗
      memRegion (s0.sp - 320#64) 40 ∗
      memRegion (s0.sp - 336#64) 8 ∗
      memRegion (s0.sp - 280#64) 184 ∗
      chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hfrom := hc.decodeErrorFrom
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hfrom ⊢
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have ha320 : (s0.sp - 328#64) + 8#64 = s0.sp - 320#64 := by bv_omega
  rw [← ha320]
  refine SepWPp.call_decodeErrorFrom (H_inner := H_inner) (b := 0#64) (x_outer := x) hfrom
    (s0.sp - 328#64) (s.readReg64 .x8)
    (ret_pc := (blkPl_325).base + 1912#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx29]) (hw := hw)
    (hP := by sep_focus) ?_
  intro s1 w_e8' hpc1 hrun1 hsp1 htr1 hcs1 _hx0_ne
  rw [ha320]
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1916#64)
  wp_steps 1
  refine SepWP.fold (scratch_336_fold_e8_40 s0.sp w_e8') (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_drop_epoch_53c18_placed hc x curSt curEpoch 0 (by decide) (s1.readReg64 .x0)
    s0 _ _ R post hpost herr
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm])
    (by dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]; ac_rfl)

/-- `ChainEpochPB` key overflow error (`+1872`, 3 instructions, placed). -/
theorem decodeState_err_epoch_key_overflow_53bec_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1872#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1900#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i w_e8
  refine SepWP.fold (scratch_320_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_320_fold_8 s0.sp (s.readReg64 .x1)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_epoch_53c08_placed hc x curSt curEpoch w_e8 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29]) (by ac_rfl)

/-- `ChainEpochPB` invalid wire type error (`+1884`, 3 instructions, placed). -/
theorem decodeState_err_epoch_invalid_wt_53bf8_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1884#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1900#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i w_e8
  refine SepWP.fold (scratch_320_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_320_fold_8 s0.sp (s.readReg64 .x0)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_epoch_53c08_placed hc x curSt curEpoch w_e8 s0 _ _ R post hpost herr
    (by simp only [arm64_norm]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29]) (by ac_rfl)

/-- `ChainEpochPB` zero tag error (`+1896`, 1 instruction, placed). -/
theorem decodeState_err_epoch_zero_tag_53c04_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1896#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1900#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i w_e8; wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_epoch_53c08_placed hc x curSt curEpoch w_e8 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29]) (by ac_rfl)

/-- `ChainEpochPB` truncated length error (`+2956`, 2 instructions, placed). -/
theorem decodeState_err_epoch_truncated_54028_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2956#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1900#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i w_e8; wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_epoch_53c08_placed hc x curSt curEpoch w_e8 s0 _ _ R post hpost herr
    (by simp only [arm64_norm]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29]) (by ac_rfl)

/-- `ChainEpochPB` corrupt length limit error (`+2972`, 2 instructions, placed). -/
theorem decodeState_err_epoch_corrupt_54038_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2972#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1900#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  rename_i w_e8
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_epoch_53c08_placed hc x curSt curEpoch w_e8 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29]) (by ac_rfl)

/-- Shared `DecodeError::push` call (`+2916`, 5 instructions) for
    `ChainEpochPB` field merge errors (`send` / `recv`), continuing to `decodeState_err_drop_epoch_54014_placed`. -/
theorem decodeState_err_push_epoch_54000_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 2) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2916#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      decodeErrorAtStackLen A errBox n ∗
      ((s0.sp - 328#64) ↦₆₄ errBox) ∗
      memRegion (s0.sp - 320#64) 40 ∗
      memRegion (s0.sp - 336#64) 8 ∗
      memRegion (s0.sp - 280#64) 184 ∗
      chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hpush := hc.decodeErrorPush
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hpush ⊢
  apply SepWPp.of_sepWP (mid := lsmpl.base 257)
  wp_steps 4
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorPush (H_inner := H_inner) (b := 0#64) (x_outer := x) hpush
    (s0.sp - 328#64) errBox n
    (ret_pc := (blkPl_325).base + 2932#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx29]) (hn := by omega)
    (hP := by sep_focus) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2936#64)
  wp_steps 1
  refine SepWP.fold (scratch_336_fold_e8_40 s0.sp errBox) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_drop_epoch_54014_placed hc x curSt curEpoch (n + 1) (by omega) errBox
    s0 _ _ R post hpost herr
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm])
    (by dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]; ac_rfl)

/-- `ChainEpochPB::send` (`EpochDirection::merge`) error exit (`+2872`, 6 instructions, placed). -/
theorem decodeState_err_epoch_send_merge_53fd4_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 2) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2872#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = errBox)
    (hP : P =
      decodeErrorAtStackLen A errBox n ∗
      decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2916#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  wp_steps 6
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_epoch_54000_placed hc x curSt curEpoch n hn errBox s0 _ _ R post hpost herr
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- `ChainEpochPB::recv` (`EpochDirection::merge`) error exit (`+2896`, 5 instructions, placed). -/
theorem decodeState_err_epoch_recv_merge_53fec_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 2) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2896#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = errBox)
    (hP : P =
      decodeErrorAtStackLen A errBox n ∗
      decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2916#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  wp_steps 5
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_epoch_54000_placed hc x curSt curEpoch n hn errBox s0 _ _ R post hpost herr
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- `ChainPB::epoch` tag-3 wire-type mismatch (`x0 ≠ 2`, before `ChainEpochPB` initialization,
    `+2708`, 8 instructions, placed). -/
theorem decodeState_err_chain_epoch_wt_53f30_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2708#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hfrom := hc.decodeErrorFrom
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hfrom ⊢
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (scratch_320_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  wp_steps 6
  refine SepWP.fold (scratch_320_fold_1_1 s0.sp (BitVec.zeroExtend 8 (s.readReg64 .x0)) 2#8) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have ha320 : (s0.sp - 328#64) + 8#64 = s0.sp - 320#64 := by bv_omega
  rw [← ha320]
  refine SepWPp.call_decodeErrorFrom (H_inner := H_inner) (b := 0#64) (x_outer := x) hfrom
    (s0.sp - 328#64) 0x8000000000000006#64
    (ret_pc := (blkPl_325).base + 2732#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx29]) (hw := by decide)
    (hP := by sep_focus) ?_
  intro s1 w_e8' hpc1 hrun1 hsp1 htr1 hcs1 _hx0_ne
  rw [ha320]
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2048#64)
  wp_steps 2
  refine SepWP.fold (scratch_336_fold_e8_40 s0.sp w_e8') (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53c9c_placed hc x curSt w0 0 s0 _ _ R post hpost herr (by decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm]; dsimp only [decodeStateErrFramePlaced]; ac_rfl)

end CryptoVerification.SpqrV1.Top.DecodeState
