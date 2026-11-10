/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSub
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state`: `ChainEpochPB` Error Drop & Unwind Blocks

**Checked by Lean.** Verifies the error-unwinding and `ChainEpochPB` drop blocks (`0x53bec..0x53c7c`,
`0x53f30..0x53f4c`, `0x53fd4..0x5403c`) for the nested `ChainEpochPB` merge loop.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection
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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `EpochDirectionPB` / `ChainEpochPB` Drop Memory Helpers -/

theorem optEpochDirectionPBAt_none (A : RustAlloc) (a : BitVec 64) :
    optEpochDirectionPBAt A a none = (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48 := rfl

theorem optEpochDirectionPBAt_some (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    optEpochDirectionPBAt A a (some d) = epochDirectionPBAt A a d := rfl

theorem rustBytesVecAt_unfold_drop (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    rustBytesVecAt A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if cap = 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold rustBytesVecAt vecU8 vecU8At vecHeader
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  change
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢ _
  have hreord :
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0#64 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by ac_rfl
  rw [hreord]
  apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
  apply Entails.pure_right ⟨hle, hlt, hptr⟩
  by_cases hc : cap = 0#64
  · simp only [hc, ↓reduceIte]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    have hsplit : memRegion ptr cap.toNat =
        memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
      rw [← ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
      congr 1
      omega
    rw [hsplit]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)))))

theorem epochDirection_send_raw_to_48 (sp ptr1 len1 cap2 ptr2 len2 : BitVec 64) (ctr : BitVec 32) :
    ((sp - 680#64) ↦₆₄ ptr1) ∗ ((sp - 672#64) ↦₆₄ len1) ∗
      ((sp - 664#64) ↦₆₄ cap2) ∗ ((sp - 656#64) ↦₆₄ ptr2) ∗ ((sp - 648#64) ↦₆₄ len2) ∗
      ((sp - 640#64) ↦₃₂ ctr) ∗ memRegion (sp - 636#64) 4 ⊢
      memRegion (sp - 680#64) 48 := by
  have h1 : memRegion (sp - 680#64) 48 =
      memRegion (sp - 680#64) 8 ∗ memRegion (sp - 672#64) 40 :=
    ProofLib.memRegion_split' (b := sp - 680#64) (n := 8) (k := 40) (b' := sp - 672#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 672#64) 40 =
      memRegion (sp - 672#64) 8 ∗ memRegion (sp - 664#64) 32 :=
    ProofLib.memRegion_split' (b := sp - 672#64) (n := 8) (k := 32) (b' := sp - 664#64) rfl (by bv_omega) (by decide)
  have h3 : memRegion (sp - 664#64) 32 =
      memRegion (sp - 664#64) 8 ∗ memRegion (sp - 656#64) 24 :=
    ProofLib.memRegion_split' (b := sp - 664#64) (n := 8) (k := 24) (b' := sp - 656#64) rfl (by bv_omega) (by decide)
  have h4 : memRegion (sp - 656#64) 24 =
      memRegion (sp - 656#64) 8 ∗ memRegion (sp - 648#64) 16 :=
    ProofLib.memRegion_split' (b := sp - 656#64) (n := 8) (k := 16) (b' := sp - 648#64) rfl (by bv_omega) (by decide)
  have h5 : memRegion (sp - 648#64) 16 =
      memRegion (sp - 648#64) 8 ∗ memRegion (sp - 640#64) 8 :=
    ProofLib.memRegion_split' (b := sp - 648#64) (n := 8) (k := 8) (b' := sp - 640#64) rfl (by bv_omega) (by decide)
  have h6 : memRegion (sp - 640#64) 8 =
      memRegion (sp - 640#64) 4 ∗ memRegion (sp - 636#64) 4 :=
    ProofLib.memRegion_split' (b := sp - 640#64) (n := 4) (k := 4) (b' := sp - 636#64) rfl (by bv_omega) (by decide)
  rw [h1, h2, h3, h4, h5, h6]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ ptr1)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ len1)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ cap2)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ ptr2)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ len2)
            (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ ctr))))))

theorem epochDirection_recv_raw_to_56 (sp cap1 ptr1 len1 cap2 ptr2 len2 : BitVec 64) (ctr : BitVec 32) :
    ((sp - 632#64) ↦₆₄ cap1) ∗ ((sp - 624#64) ↦₆₄ ptr1) ∗ ((sp - 616#64) ↦₆₄ len1) ∗
      ((sp - 608#64) ↦₆₄ cap2) ∗ ((sp - 600#64) ↦₆₄ ptr2) ∗ ((sp - 592#64) ↦₆₄ len2) ∗
      ((sp - 584#64) ↦₃₂ ctr) ∗ memRegion (sp - 580#64) 4 ⊢
      memRegion (sp - 632#64) 56 := by
  have h0 : memRegion (sp - 632#64) 56 =
      memRegion (sp - 632#64) 8 ∗ memRegion (sp - 624#64) 48 :=
    ProofLib.memRegion_split' (b := sp - 632#64) (n := 8) (k := 48) (b' := sp - 624#64) rfl (by bv_omega) (by decide)
  have h1 : memRegion (sp - 624#64) 48 =
      memRegion (sp - 624#64) 8 ∗ memRegion (sp - 616#64) 40 :=
    ProofLib.memRegion_split' (b := sp - 624#64) (n := 8) (k := 40) (b' := sp - 616#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 616#64) 40 =
      memRegion (sp - 616#64) 8 ∗ memRegion (sp - 608#64) 32 :=
    ProofLib.memRegion_split' (b := sp - 616#64) (n := 8) (k := 32) (b' := sp - 608#64) rfl (by bv_omega) (by decide)
  have h3 : memRegion (sp - 608#64) 32 =
      memRegion (sp - 608#64) 8 ∗ memRegion (sp - 600#64) 24 :=
    ProofLib.memRegion_split' (b := sp - 608#64) (n := 8) (k := 24) (b' := sp - 600#64) rfl (by bv_omega) (by decide)
  have h4 : memRegion (sp - 600#64) 24 =
      memRegion (sp - 600#64) 8 ∗ memRegion (sp - 592#64) 16 :=
    ProofLib.memRegion_split' (b := sp - 600#64) (n := 8) (k := 16) (b' := sp - 592#64) rfl (by bv_omega) (by decide)
  have h5 : memRegion (sp - 592#64) 16 =
      memRegion (sp - 592#64) 8 ∗ memRegion (sp - 584#64) 8 :=
    ProofLib.memRegion_split' (b := sp - 592#64) (n := 8) (k := 8) (b' := sp - 584#64) rfl (by bv_omega) (by decide)
  have h6 : memRegion (sp - 584#64) 8 =
      memRegion (sp - 584#64) 4 ∗ memRegion (sp - 580#64) 4 :=
    ProofLib.memRegion_split' (b := sp - 584#64) (n := 4) (k := 4) (b' := sp - 580#64) rfl (by bv_omega) (by decide)
  rw [h0, h1, h2, h3, h4, h5, h6]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ cap1)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ ptr1)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ len1)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ cap2)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ ptr2)
            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ len2)
              (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ ctr)))))))

theorem epochDirection_recv_none_to_56 (sp w : BitVec 64) :
    ((sp - 632#64) ↦₆₄ w) ∗ memRegion (sp - 624#64) 48 ⊢
      memRegion (sp - 632#64) 56 := by
  rw [ProofLib.memRegion_split' (b := sp - 632#64) (n := 8) (k := 48) (b' := sp - 624#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 632#64) w)

theorem epoch_regions_to_err_frame (sp : BitVec 64) :
    memRegion (sp - 680#64) 48 ∗ memRegion (sp - 632#64) 56 ∗ memRegion (sp - 576#64) 240 ⊢
      memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 := by
  have h1 : memRegion (sp - 680#64) 48 =
      memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 8 :=
    ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 8) (b' := sp - 640#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 640#64) 304 =
      memRegion (sp - 640#64) 8 ∗ memRegion (sp - 632#64) 296 :=
    ProofLib.memRegion_split' (b := sp - 640#64) (n := 8) (k := 296) (b' := sp - 632#64) rfl (by bv_omega) (by decide)
  have h3 : memRegion (sp - 632#64) 296 =
      memRegion (sp - 632#64) 56 ∗ memRegion (sp - 576#64) 240 :=
    ProofLib.memRegion_split' (b := sp - 632#64) (n := 56) (k := 240) (b' := sp - 576#64) rfl (by bv_omega) (by decide)
  rw [h1, h2, h3]
  exact Entails.of_eq (by ac_rfl)

/-- Common stack/heap frame during `ChainEpochPB` error drop (excluding `[sp + 0x2c0..0x330]` =
    `s0.sp - 688#64 .. s0.sp - 576#64`, which holds the `112`-byte `ChainEpochPB`). -/
abbrev decodeStateEpochErrTailFrame (H_inner : V1InnerHeapPred) (b : BitVec 64)
    (A : RustAlloc) (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 : State) : SepProp :=
  v1StateJumpTablesAt b ∗
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

/-- Complete `ChainEpochPB` error frame: `chainEpochPBAt A (s0.sp - 688#64) curEpoch` +
    `decodeStateEpochErrTailFrame H_inner b A x curSt s0`. -/
abbrev decodeStateEpochErrFrame (H_inner : V1InnerHeapPred) (b : BitVec 64)
    (A : RustAlloc) (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 : State) : SepProp :=
  chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
  decodeStateEpochErrTailFrame H_inner b A x curSt s0

/-! ## `ChainEpochPB` Error Drop Path (`0x53c5c..0x53c98`, `0x53c28..0x53c58`, `0x53c18..0x53c24`, `0x54014..0x54024`) -/

set_option maxHeartbeats 800000 in
/-- Drop `curEpoch.recv : Option EpochDirectionPB` at `[sp + 0x2f8]` (`s0.sp - 632#64`) and
    continue to `decodeState_err_push_53c9c` (`0x53c5c..0x53c98`, offset `1984`, 16 instructions). -/
theorem decodeState_err_drop_epoch_recv_53c5c {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (optRecv : Option EpochDirectionPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1984#64)
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
      decodeStateEpochErrTailFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hdealloc := hc.dealloc_at
  simp only [rustDeallocSpec] at hdealloc
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateEpochErrTailFrame] at hpc hdealloc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1984 64
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2048#64)
  cases optRecv with
  | none =>
    rw [optEpochDirectionPBAt_none]
    have ha624 : (s0.sp - 632#64) + 8#64 = s0.sp - 624#64 := by bv_omega
    rw [ha624]
    wp_steps
    refine SepWP.fold (epochDirection_recv_none_to_56 s0.sp noneCap) (by sep_focus) ?_
    refine SepWP.fold (epoch_regions_to_err_frame s0.sp) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    exact decodeState_err_push_53c9c hc x curSt w0 n s0 _ _ R post hpost herr hn
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx1]; dsimp only [decodeStateErrFrame]; ac_rfl)
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
      exact decodeState_err_push_53c9c hc x curSt w0 n s0 _ _ R post hpost herr hn
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx1]; dsimp only [decodeStateErrFrame]; ac_rfl)
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
      exact decodeState_err_push_53c9c hc x curSt w0 n s0 _ _ R post hpost herr hn
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0A
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; dsimp only [decodeStateErrFrame]; ac_rfl)
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
      exact decodeState_err_push_53c9c hc x curSt w0 n s0 _ _ R post hpost herr hn
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0A
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; dsimp only [decodeStateErrFrame]; ac_rfl)
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
      exact decodeState_err_push_53c9c hc x curSt w0 n s0 _ _ R post hpost herr hn
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0A
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; dsimp only [decodeStateErrFrame]; ac_rfl)

set_option maxHeartbeats 800000 in
/-- Drop `d : EpochDirectionPB` (`curEpoch.send = some d`) at `[sp + 0x2c0]` (`s0.sp - 688#64`)
    after `x8 = cap1` has already been loaded and checked `≠ -1`, then continue to
    `decodeState_err_drop_epoch_recv_53c5c` (`0x53c28..0x53c58`, offset `1932`, 13 instructions). -/
theorem decodeState_err_drop_epoch_send_some_53c28 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (optRecv : Option EpochDirectionPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox cap1 ptr1 : BitVec 64)
    (nextBs prevBs : List (BitVec 8)) (ctr : BitVec 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1932#64)
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
      decodeStateEpochErrTailFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hdealloc := hc.dealloc_at
  simp only [rustDeallocSpec] at hdealloc
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateEpochErrTailFrame] at hpc hdealloc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1932 52
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1984#64)
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
    exact decodeState_err_drop_epoch_recv_53c5c hc x curSt optRecv n hn errBox 0#64 s0 _ _ R post hpost herr
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx20])
      (by dsimp only [decodeStateEpochErrTailFrame]; ac_rfl)
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
    exact decodeState_err_drop_epoch_recv_53c5c hc x curSt optRecv n hn errBox 0#64 s0 _ _ R post hpost herr
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0A
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateEpochErrTailFrame]; ac_rfl)
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
    exact decodeState_err_drop_epoch_recv_53c5c hc x curSt optRecv n hn errBox cap1 s0 _ _ R post hpost herr
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0A
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateEpochErrTailFrame]; ac_rfl)
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
    exact decodeState_err_drop_epoch_recv_53c5c hc x curSt optRecv n hn errBox cap1 s0 _ _ R post hpost herr
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0A
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateEpochErrTailFrame]; ac_rfl)

/-- Drop `curEpoch : ChainEpochPB` at `[sp + 0x2c0]` (`s0.sp - 688#64`) with `errBox` in `x1`,
    then continue to `decodeState_err_push_53c9c` (`0x53c18..0x53c98`, offset `1916`). -/
theorem decodeState_err_drop_epoch_53c18 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1916#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx1 : s.readReg64 .x1 = errBox)
    (hP : P =
      decodeErrorAtStackLen A errBox n ∗
      decodeStateEpochErrFrame H_inner b A x curSt curEpoch s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateEpochErrFrame,
    decodeStateEpochErrTailFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  unfold chainEpochPBAt
  have ha632 : (s0.sp - 688#64) + 0x38#64 = s0.sp - 632#64 := by bv_omega
  rw [ha632]
  decodeState_fetches b (Rust.withPanics ext) 1916 16
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  rcases hsend : curEpoch.send with _ | d
  · rw [optEpochDirectionPBAt_none]
    have ha680 : (s0.sp - 688#64) + 8#64 = s0.sp - 680#64 := by bv_omega
    rw [ha680]
    apply SepWPp.of_sepWP (mid := entry + 1984#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    exact decodeState_err_drop_epoch_recv_53c5c hc x curSt curEpoch.recv n hn errBox noneCap s0 _ _ R post hpost herr
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx1])
      (by dsimp only [decodeStateEpochErrTailFrame]; ac_rfl)
  · rw [optEpochDirectionPBAt_some]
    unfold epochDirectionPBAt
    have ha664 : (s0.sp - 688#64) + 0x18#64 = s0.sp - 664#64 := by bv_omega
    have ha640 : (s0.sp - 688#64) + 0x30#64 = s0.sp - 640#64 := by bv_omega
    have ha636 : (s0.sp - 688#64) + 0x34#64 = s0.sp - 636#64 := by bv_omega
    rw [ha664, ha640, ha636]
    apply SepWPp.of_sepWP (mid := entry + 1932#64)
    refine SepWP.fold (rustBytesVecAt_unfold_drop A (s0.sp - 688#64) d.next) (by sep_focus) ?_
    wp_pull_exists
    rename_i cap1 ptr1
    wp_focus_pure; rintro ⟨_, hlt1, _⟩
    have hcmn1 : ¬((cap1 + 1#64 == 0#64) = true) := cap_add_one_beq_zero_false hlt1
    wp_steps
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    exact decodeState_err_drop_epoch_send_some_53c28 hc x curSt curEpoch.recv n hn errBox cap1 ptr1
      d.next d.prev d.ctr s0 _ _ R post hpost herr
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx1])
      (by dsimp only [decodeStateEpochErrTailFrame]; ac_rfl)

/-- Alternate entry (`0x54014..0x54024`, offset `2936`, 5 instructions) to drop `curEpoch : ChainEpochPB`
    at `[sp + 0x2c0]` (`s0.sp - 688#64`) with `errBox` in `x1`. -/
theorem decodeState_err_drop_epoch_54014 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2936#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx1 : s.readReg64 .x1 = errBox)
    (hP : P =
      decodeErrorAtStackLen A errBox n ∗
      decodeStateEpochErrFrame H_inner b A x curSt curEpoch s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateEpochErrFrame,
    decodeStateEpochErrTailFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  unfold chainEpochPBAt
  have ha632 : (s0.sp - 688#64) + 0x38#64 = s0.sp - 632#64 := by bv_omega
  rw [ha632]
  decodeState_fetches b (Rust.withPanics ext) 2936 20
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  rcases hsend : curEpoch.send with _ | d
  · rw [optEpochDirectionPBAt_none]
    have ha680 : (s0.sp - 688#64) + 8#64 = s0.sp - 680#64 := by bv_omega
    have hcmn_ne : (noneCap + 1#64 != 0#64) = false := rfl
    rw [ha680]
    apply SepWPp.of_sepWP (mid := entry + 1984#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    exact decodeState_err_drop_epoch_recv_53c5c hc x curSt curEpoch.recv n hn errBox noneCap s0 _ _ R post hpost herr
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx1])
      (by dsimp only [decodeStateEpochErrTailFrame]; ac_rfl)
  · rw [optEpochDirectionPBAt_some]; unfold epochDirectionPBAt
    have ha664 : (s0.sp - 688#64) + 0x18#64 = s0.sp - 664#64 := by bv_omega
    have ha640 : (s0.sp - 688#64) + 0x30#64 = s0.sp - 640#64 := by bv_omega
    have ha636 : (s0.sp - 688#64) + 0x34#64 = s0.sp - 636#64 := by bv_omega
    rw [ha664, ha640, ha636]
    apply SepWPp.of_sepWP (mid := entry + 1932#64)
    refine SepWP.fold (rustBytesVecAt_unfold_drop A (s0.sp - 688#64) d.next) (by sep_focus) ?_
    wp_pull_exists; rename_i cap1 ptr1; wp_focus_pure; rintro ⟨_, hlt1, _⟩
    have hcmn1 : ¬((cap1 + 1#64 == 0#64) = true) := cap_add_one_beq_zero_false hlt1
    have hcmn1_ne : (cap1 + 1#64 != 0#64) = true := by
      rw [bne_iff_ne]; exact fun h => hcmn1 (beq_iff_eq.mpr h)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    exact decodeState_err_drop_epoch_send_some_53c28 hc x curSt curEpoch.recv n hn errBox cap1 ptr1
      d.next d.prev d.ctr s0 _ _ R post hpost herr
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx1])
      (by dsimp only [decodeStateEpochErrTailFrame]; ac_rfl)

/-! ## `ChainEpochPB` Error Exit Basic Blocks (`0x53bec..0x53c14`, `0x53f30..0x53f4c`, `0x53fd4..0x54010`, `0x54028..0x5402c`, `0x54038..0x5403c`) -/

theorem scratch_336_split_e8_40 (sp : BitVec 64) :
    memRegion (sp - 336#64) 240 ⊢
      memRegion (sp - 336#64) 8 ∗
      memRegion (sp - 320#64) 40 ∗
      memRegion (sp - 280#64) 184 ∗
      (∃∗ w_e8 : BitVec 64, (sp - 328#64) ↦₆₄ w_e8) := by
  have h1 : memRegion (sp - 336#64) 240 =
      memRegion (sp - 336#64) 8 ∗ memRegion (sp - 328#64) 232 :=
    ProofLib.memRegion_split' (b := sp - 336#64) (n := 8) (k := 232) (b' := sp - 328#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 328#64) 232 =
      memRegion (sp - 328#64) 8 ∗ memRegion (sp - 320#64) 224 :=
    ProofLib.memRegion_split' (b := sp - 328#64) (n := 8) (k := 224) (b' := sp - 320#64) rfl (by bv_omega) (by decide)
  have h3 : memRegion (sp - 320#64) 224 =
      memRegion (sp - 320#64) 40 ∗ memRegion (sp - 280#64) 184 :=
    ProofLib.memRegion_split' (b := sp - 320#64) (n := 40) (k := 184) (b' := sp - 280#64) rfl (by bv_omega) (by decide)
  rw [h1, h2, h3, ProofLib.memRegion_eight (sp - 328#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_336_fold_e8_40 (sp w_e8 : BitVec 64) :
    memRegion (sp - 336#64) 8 ∗
      ((sp - 328#64) ↦₆₄ w_e8) ∗
      memRegion (sp - 320#64) 40 ∗
      memRegion (sp - 280#64) 184 ⊢
      memRegion (sp - 336#64) 240 := by
  have h1 : memRegion (sp - 336#64) 240 =
      memRegion (sp - 336#64) 8 ∗ memRegion (sp - 328#64) 232 :=
    ProofLib.memRegion_split' (b := sp - 336#64) (n := 8) (k := 232) (b' := sp - 328#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 328#64) 232 =
      memRegion (sp - 328#64) 8 ∗ memRegion (sp - 320#64) 224 :=
    ProofLib.memRegion_split' (b := sp - 328#64) (n := 8) (k := 224) (b' := sp - 320#64) rfl (by bv_omega) (by decide)
  have h3 : memRegion (sp - 320#64) 224 =
      memRegion (sp - 320#64) 40 ∗ memRegion (sp - 280#64) 184 :=
    ProofLib.memRegion_split' (b := sp - 320#64) (n := 40) (k := 184) (b' := sp - 280#64) rfl (by bv_omega) (by decide)
  rw [h1, h2, h3]
  exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 328#64) w_e8))

theorem scratch_320_split_8 (sp : BitVec 64) :
    memRegion (sp - 320#64) 40 ⊢
      memRegion (sp - 312#64) 32 ∗
      (∃∗ w1 : BitVec 64, (sp - 320#64) ↦₆₄ w1) := by
  have s1 := ProofLib.memRegion_split (sp - 320#64) 8 32 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 320 8] at s1
  rw [s1, ProofLib.memRegion_eight (sp - 320#64)]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_320_fold_8 (sp w1 : BitVec 64) :
    ((sp - 320#64) ↦₆₄ w1) ∗ memRegion (sp - 312#64) 32 ⊢ memRegion (sp - 320#64) 40 := by
  have s1 := ProofLib.memRegion_split (sp - 320#64) 8 32 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 320 8] at s1
  rw [s1]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 320#64) w1)

theorem scratch_320_split_1_1 (sp : BitVec 64) :
    memRegion (sp - 320#64) 40 ⊢
      memRegion (sp - 318#64) 38 ∗
      (∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8,
        ((sp - 320#64) ↦₈ b0) ∗ ((sp - 319#64) ↦₈ b1)) := by
  have s1 := ProofLib.memRegion_split (sp - 320#64) 1 39 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 320 1] at s1
  have s2 := ProofLib.memRegion_split (sp - 319#64) 1 38 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 319 1] at s2
  rw [s1, s2, ProofLib.memRegion_one (sp - 320#64), ProofLib.memRegion_one (sp - 319#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_320_fold_1_1 (sp : BitVec 64) (b0 b1 : BitVec 8) :
    ((sp - 320#64) ↦₈ b0) ∗ ((sp - 319#64) ↦₈ b1) ∗ memRegion (sp - 318#64) 38 ⊢
      memRegion (sp - 320#64) 40 := by
  have s1 := ProofLib.memRegion_split (sp - 320#64) 1 39 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 320 1] at s1
  have s2 := ProofLib.memRegion_split (sp - 319#64) 1 38 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 319 1] at s2
  rw [s1, s2]
  exact sepConj_mono (pointsTo8_entails_memRegion1 _ b0)
    (sepConj_mono (pointsTo8_entails_memRegion1 _ b1) (Entails.refl _))

/-- Shared `DecodeError::from` call at `0x53c08..0x53c14` (offset `1900`, 4 instructions)
    using `[x29 - 0xe8]` (`s0.sp - 328#64`), followed by `decodeState_err_drop_epoch_53c18`. -/
theorem decodeState_err_from_epoch_53c08 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (w_e8 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1900#64)
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
      v1StateJumpTablesAt b ∗
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
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hfrom := hc.decodeErrorFrom_at
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc hfrom ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1900 16
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x459a8#64 - 0x4e0a4#64))
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have ha320 : (s0.sp - 328#64) + 8#64 = s0.sp - 320#64 := by bv_omega
  rw [← ha320]
  refine SepWPp.call_decodeErrorFrom hfrom (s0.sp - 328#64) (s.readReg64 .x8)
    (ret_pc := entry + 1912#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx29]) (hw := hw)
    (hP := by sep_focus) ?_
  intro s1 w_e8' hpc1 hrun1 hsp1 htr1 hcs1 _hx0_ne
  rw [ha320]
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPp.of_sepWP (mid := entry + 1916#64)
  wp_steps 1
  refine SepWP.fold (scratch_336_fold_e8_40 s0.sp w_e8') (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_drop_epoch_53c18 hc x curSt curEpoch 0 (by decide) (s1.readReg64 .x0)
    s0 _ _ R post hpost herr
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm])
    (by dsimp only [decodeStateEpochErrFrame, decodeStateEpochErrTailFrame]; ac_rfl)

/-- `ChainEpochPB` key overflow error (`0x53bec..0x53bf4`, offset `1872`, 3 instructions). -/
theorem decodeState_err_epoch_key_overflow_53bec {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1872#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFrame H_inner b A x curSt curEpoch s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateEpochErrFrame,
    decodeStateEpochErrTailFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1872 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1900#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i w_e8
  refine SepWP.fold (scratch_320_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_320_fold_8 s0.sp (s.readReg64 .x1)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_epoch_53c08 hc x curSt curEpoch w_e8 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29]) (by ac_rfl)

/-- `ChainEpochPB` invalid wire type error (`0x53bf8..0x53c00`, offset `1884`, 3 instructions). -/
theorem decodeState_err_epoch_invalid_wt_53bf8 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1884#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFrame H_inner b A x curSt curEpoch s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateEpochErrFrame,
    decodeStateEpochErrTailFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1884 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1900#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i w_e8
  refine SepWP.fold (scratch_320_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_320_fold_8 s0.sp (s.readReg64 .x0)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_epoch_53c08 hc x curSt curEpoch w_e8 s0 _ _ R post hpost herr
    (by simp only [arm64_norm]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29]) (by ac_rfl)

/-- `ChainEpochPB` zero tag error (`0x53c04`, offset `1896`, 1 instruction). -/
theorem decodeState_err_epoch_zero_tag_53c04 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1896#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFrame H_inner b A x curSt curEpoch s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateEpochErrFrame,
    decodeStateEpochErrTailFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1896 4
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1900#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i w_e8; wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_epoch_53c08 hc x curSt curEpoch w_e8 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29]) (by ac_rfl)

/-- `ChainEpochPB` truncated length error (`0x54028..0x5402c`, offset `2956`, 2 instructions). -/
theorem decodeState_err_epoch_truncated_54028 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2956#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFrame H_inner b A x curSt curEpoch s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateEpochErrFrame,
    decodeStateEpochErrTailFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2956 8
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1900#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i w_e8; wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_epoch_53c08 hc x curSt curEpoch w_e8 s0 _ _ R post hpost herr
    (by simp only [arm64_norm]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29]) (by ac_rfl)

/-- `ChainEpochPB` corrupt length limit error (`0x54038..0x5403c`, offset `2972`, 2 instructions). -/
theorem decodeState_err_epoch_corrupt_54038 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2972#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFrame H_inner b A x curSt curEpoch s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateEpochErrFrame,
    decodeStateEpochErrTailFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2972 8
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1900#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  rename_i w_e8
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_epoch_53c08 hc x curSt curEpoch w_e8 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29]) (by ac_rfl)

/-- Shared `DecodeError::push` call (`0x54000..0x54010`, offset `2916`, 5 instructions) for
    `ChainEpochPB` field merge errors (`send` / `recv`), continuing to `decodeState_err_drop_epoch_54014`. -/
theorem decodeState_err_push_epoch_54000 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 2) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2916#64)
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
      v1StateJumpTablesAt b ∗
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
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hpush := hc.decodeErrorPush_at
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc hpush ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2916 20
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x456b0#64 - 0x4e0a4#64))
  wp_steps 4
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorPush hpush (s0.sp - 328#64) errBox n
    (ret_pc := entry + 2932#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx29]) (hn := by omega)
    (hP := by sep_focus) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPp.of_sepWP (mid := entry + 2936#64)
  wp_steps 1
  refine SepWP.fold (scratch_336_fold_e8_40 s0.sp errBox) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_drop_epoch_54014 hc x curSt curEpoch (n + 1) (by omega) errBox
    s0 _ _ R post hpost herr
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm])
    (by dsimp only [decodeStateEpochErrFrame, decodeStateEpochErrTailFrame]; ac_rfl)

/-- `ChainEpochPB::send` (`EpochDirection::merge`) error exit (`0x53fd4..0x53fe8`, offset `2872`, 6 instructions). -/
theorem decodeState_err_epoch_send_merge_53fd4 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 2) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2872#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = errBox)
    (hP : P =
      decodeErrorAtStackLen A errBox n ∗
      decodeStateEpochErrFrame H_inner b A x curSt curEpoch s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateEpochErrFrame,
    decodeStateEpochErrTailFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2872 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2916#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  wp_steps 6
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_epoch_54000 hc x curSt curEpoch n hn errBox s0 _ _ R post hpost herr
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- `ChainEpochPB::recv` (`EpochDirection::merge`) error exit (`0x53fec..0x53ffc`, offset `2896`, 5 instructions). -/
theorem decodeState_err_epoch_recv_merge_53fec {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 2) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2896#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = errBox)
    (hP : P =
      decodeErrorAtStackLen A errBox n ∗
      decodeStateEpochErrFrame H_inner b A x curSt curEpoch s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateEpochErrFrame,
    decodeStateEpochErrTailFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2896 20
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2916#64)
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  wp_steps 5
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_epoch_54000 hc x curSt curEpoch n hn errBox s0 _ _ R post hpost herr
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx29])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- `ChainPB::epoch` tag-3 wire-type mismatch (`x0 ≠ 2`, before `ChainEpochPB` initialization,
    `0x53f30..0x53f4c`, offset `2708`, 8 instructions). -/
theorem decodeState_err_chain_epoch_wt_53f30 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2708#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hfrom := hc.decodeErrorFrom_at
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc hfrom ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2708 32
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x459a8#64 - 0x4e0a4#64))
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (scratch_320_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  wp_steps 6
  refine SepWP.fold (scratch_320_fold_1_1 s0.sp (BitVec.zeroExtend 8 (s.readReg64 .x0)) 2#8) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have ha320 : (s0.sp - 328#64) + 8#64 = s0.sp - 320#64 := by bv_omega
  rw [← ha320]
  refine SepWPp.call_decodeErrorFrom hfrom (s0.sp - 328#64) 0x8000000000000006#64
    (ret_pc := entry + 2732#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx29]) (hw := by decide)
    (hP := by sep_focus) ?_
  intro s1 w_e8' hpc1 hrun1 hsp1 htr1 hcs1 _hx0_ne
  rw [ha320]
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPp.of_sepWP (mid := entry + 2048#64)
  wp_steps 2
  refine SepWP.fold (scratch_336_fold_e8_40 s0.sp w_e8') (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53c9c hc x curSt w0 0 s0 _ _ R post hpost herr (by decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm]; dsimp only [decodeStateErrFrame]; ac_rfl)

end CryptoVerification.SpqrV1.Top.DecodeState
