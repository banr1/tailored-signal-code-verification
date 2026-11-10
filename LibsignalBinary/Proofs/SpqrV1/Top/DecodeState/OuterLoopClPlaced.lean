/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopClPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepClPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlaced
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded Verification of `spqr::decode_state` (Block `325`) — Outer Loop, Prologue, and Top Theorem

**Checked by Lean.**

Verifies code-loaded empty-input handling, outer-loop field-key dispatch and length-bounded
induction, prologue initialization, and `decodeState_cl_placed_ok` under `LibsignalPlacement`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification
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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup v1StateJumpTablesPlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Pure & Framing Helpers for Empty Input (`+1604`) and Success Exit (`+1676`) -/

private theorem spqrDecodeState_eq_of_mergeLoopBin_top_err {bs : List (BitVec 8)} (hne : bs ≠ [])
    (h : mergeLoopBin PqRatchetState.mergeField bs.length default bs 0 100 = none) :
    spqrDecodeState bs = .error .stateDecode := by
  have hopt := spqrDecodeState_toOption_eq_mergeLoopBin hne
  rw [h] at hopt
  cases bs with
  | nil => exact (hne rfl).elim
  | cons b tl =>
    unfold Proto.spqrDecodeState at hopt
    unfold spqrDecodeState Proto.spqrDecodeState
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hopt ⊢
    rcases hm : PqRatchetState.decode (b :: tl) with e | st
    · rfl
    · simp [hm, Except.toOption] at hopt

private theorem spqrDecodeState_eq_of_mergeLoopBin_top_ok {bs : List (BitVec 8)} {st : PqRatchetState}
    (hne : bs ≠ [])
    (h : mergeLoopBin PqRatchetState.mergeField bs.length default bs 0 100 = some st) :
    spqrDecodeState bs = .ok st := by
  have hopt := spqrDecodeState_toOption_eq_mergeLoopBin hne
  rw [h] at hopt
  cases bs with
  | nil => exact (hne rfl).elim
  | cons b tl =>
    unfold Proto.spqrDecodeState at hopt
    unfold spqrDecodeState Proto.spqrDecodeState
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hopt ⊢
    rcases hm : PqRatchetState.decode (b :: tl) with e | st'
    · simp [hm, Except.toOption] at hopt
    · simp only [hm, Except.toOption, Option.some.injEq] at hopt
      subst hopt
      rfl

private theorem memRegion_352_empty_split (outPtr : BitVec 64) :
    memRegion outPtr 352 ⊢
      memRegion (outPtr + 8#64) 40 ∗
      memRegion (outPtr + 56#64) 72 ∗
      memRegion (outPtr + 136#64) 216 ∗
      (∃∗ w128 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w0 : BitVec 64,
        (outPtr ↦₆₄ w0) ∗ ((outPtr + 48#64) ↦₆₄ w48) ∗ ((outPtr + 128#64) ↦₆₄ w128)) := by
  rw [ProofLib.memRegion_split' (b := outPtr) (n := 8) (k := 344)
      (b' := outPtr + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 8#64) (n := 40) (k := 304)
      (b' := outPtr + 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 48#64) (n := 8) (k := 296)
      (b' := outPtr + 56#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 56#64) (n := 72) (k := 224)
      (b' := outPtr + 128#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 128#64) (n := 8) (k := 216)
      (b' := outPtr + 136#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight outPtr,
    ProofLib.memRegion_eight (outPtr + 48#64),
    ProofLib.memRegion_eight (outPtr + 128#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

private theorem fold_decodeStateResultAt_empty (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (outPtr : BitVec 64) {bs : List (BitVec 8)} (hbs : bs = []) :
    (outPtr ↦₆₄ (-1#64)) ∗ memRegion (outPtr + 8#64) 40 ∗
      ((outPtr + 48#64) ↦₆₄ (-1#64)) ∗ memRegion (outPtr + 56#64) 72 ∗
      ((outPtr + 128#64) ↦₆₄ (-3#64)) ∗ memRegion (outPtr + 136#64) 216 ⊢
      decodeStateResultAt H_inner A outPtr (spqrDecodeState bs) := by
  subst hbs
  unfold spqrDecodeState
  rw [spqrDecodeState_nil, pqRatchetState_default_eq]
  unfold decodeStateResultAt protoPqRatchetStateAt
    optVersionNegotiationPBAt optChainPBAt optProtoPqRatchetInnerAt
    noneCap none3Cap
  dsimp only
  have ha56 : (outPtr + 48#64) + 8#64 = outPtr + 56#64 := by bv_omega
  have ha136 : (outPtr + 128#64) + 8#64 = outPtr + 136#64 := by bv_omega
  rw [ha56, ha136]
  exact Entails.of_eq (by ac_rfl)

private theorem stack_1392_fold_1296 (sp w0 : BitVec 64) :
    ((sp - 1392#64) ↦₆₄ w0) ∗ memRegion (sp - 1384#64) 1288 ⊢
      memRegion (sp - 1392#64) 1296 := by
  let sz : Nat := 1288
  rw [ProofLib.memRegion_split' (b := sp - 1392#64) (n := 8) (k := sz) (N := 1296)
      (b' := sp - 1384#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 1392#64) w0)

private theorem head_ne_none2Cap_branch {w : BitVec 64} (hne : w ≠ none2Cap) :
    (w + 2#64 == 0#64) = false ∧ (w + 2#64 != 0#64) = true := by
  have h0 : w + 2#64 ≠ 0#64 := by
    intro h
    apply hne
    change w = -2#64
    bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr h0, bne_iff_ne.mpr h0⟩

private theorem state_1040_fold_352 (sp w0 w1 : BitVec 64) {bs336 : List (BitVec 8)}
    (hlen : bs336.length = 336) :
    ((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1) ∗ ((sp - 1024#64) ↦ₛ bs336) ⊢
      memRegion (sp - 1040#64) 352 := by
  have h16 : ((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1) ⊢ memRegion (sp - 1040#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 8) (k := 8)
        (b' := sp - 1032#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono
      (ProofLib.pointsTo64_entails_memRegion _ w0)
      (ProofLib.pointsTo64_entails_memRegion _ w1)
  have h336 : ((sp - 1024#64) ↦ₛ bs336) ⊢ memRegion (sp - 1024#64) 336 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (sp - 1024#64) bs336
  rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 16) (k := 336)
      (b' := sp - 1024#64) rfl (by bv_omega) (by decide)]
  have hassoc :
      ((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1) ∗ ((sp - 1024#64) ↦ₛ bs336) =
      (((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1)) ∗ ((sp - 1024#64) ↦ₛ bs336) := by ac_rfl
  rw [hassoc]
  exact sepConj_mono h16 h336

private theorem memRegion_352_split_head16_tail336 (outPtr : BitVec 64) :
    memRegion outPtr 352 ⊢
      memRegion (outPtr + 16#64) 336 ∗
      (∃∗ out1 : BitVec 64, ∃∗ out0 : BitVec 64,
        (outPtr ↦₆₄ out0) ∗ ((outPtr + 8#64) ↦₆₄ out1)) := by
  rw [ProofLib.memRegion_split' (b := outPtr) (n := 8) (k := 344)
      (b' := outPtr + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 8#64) (n := 8) (k := 336)
      (b' := outPtr + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight outPtr,
    ProofLib.memRegion_eight (outPtr + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

/-- Post-loop success exit (`+1676..+1724`, 13 instructions) -> `+2500`. -/
theorem decodeState_ok_exit_53b28_cl_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A ext)
    (x : DecodeStateGhost) (w0_scr : BitVec 64) (curSt : PqRatchetState)
    (hok : spqrDecodeState x.st.bytes = .ok curSt)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1676#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0_scr) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes [] ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) 0 curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A x s0) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy := hc.session_memcpy allocHookStack
  simp only [sessionMemcpySpec] at hmemcpy
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A x [] 0 curSt s0) (by sep_focus) ?_
  refine SepWP.fold (scratch_688_fold_48 s0.sp w0_scr)
    (by dsimp only [decodeStateErrFramePlaced]; sep_focus) ?_
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hmemcpy ⊢
  refine SepWP.fold (protoPqRatchetStateAt_entails_head16_tail336 H_inner A (s0.sp - 1040#64) curSt)
    (by sep_focus) ?_
  wp_pull_exists
  rename_i w0 w1 bs336
  wp_focus_pure; rintro ⟨hw0_ne, hbs336_len⟩
  have ⟨hcmn_eq_f, hcmn_ne_t⟩ := head_ne_none2Cap_branch hw0_ne
  rw [ProofLib.memRegion_split' (b := s0.sp - 1392#64) (n := 336) (k := 16)
      (b' := s0.sp - 1056#64) rfl (by bv_omega) (by decide)]
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
  wp_steps 5
  wp_apply
  wp_conv_pre => simp only [*]
  refine SepWP.fold (state_1040_fold_352 s0.sp w0 w1 hbs336_len) (by sep_focus) ?_
  refine SepWP.fold (memRegion_352_split_head16_tail336 x.outPtr) (by sep_focus) ?_
  wp_pull_exists
  wp_steps 6
  wp_apply
  wp_conv_pre => simp only [*]
  refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
  have h336_sp : ((s0.sp - 1392#64) ↦ₛ bs336) ⊢ memRegion (s0.sp - 1392#64) 336 := by
    rw [← hbs336_len]; exact pointsToBytes_entails_memRegion (s0.sp - 1392#64) bs336
  refine SepWP.fold h336_sp (by sep_focus) ?_
  refine SepWP.fold (lower_352_fold s0.sp) (by sep_focus) ?_
  refine SepWP.fold (frame_4chunks_to_1296 s0.sp) (by sep_focus) ?_
  wp_steps 2
  have hfold_ok :
      (x.outPtr ↦₆₄ w0) ∗ ((x.outPtr + 8#64) ↦₆₄ w1) ∗ ((x.outPtr + 16#64) ↦ₛ bs336) ∗
        (relocProtoPqRatchetStateTailAt H_inner A w0 w1 curSt).1 bs336 ⊢
        decodeStateResultAt H_inner A x.outPtr (spqrDecodeState x.st.bytes) := by
    rw [hok]
    exact head16_tail336_entails_protoPqRatchetStateAt H_inner A x.outPtr w0 w1 bs336 curSt hbs336_len
  refine SepWP.fold hfold_ok (by sep_focus) ?_
  exact decodeState_epilogue_53e60_placed x s0 _ _ R post hpost
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hs0A
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-! ## 2. Outer Loop Tag Dispatch (`+160..+180`) & Single Iteration (`+116..+180`) -/

attribute [local irreducible] Proto.mergeMessage mergeLoopBin Proto.spqrDecodeState

/-- Outer loop tag dispatch at `+160` (6 instructions) given `1 ≤ tag < 2 ^ 29`:
    dispatches `tag = 3` (`+312`), `tag = 2` (`+244`), `tag = 1` (`+184`), and
    `tag ∉ {1, 2, 3}` (`+456`), reaching `entry + 1576` on success. -/
theorem decodeState_outer_dispatch_5353c_cl_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64) (curSt : PqRatchetState)
    (rest1 : List (BitVec 8)) (tag : Nat) (iwt : WireType)
    (htag1_le : 1 ≤ tag) (htag29 : tag < 2 ^ 29)
    (hrest1_le : rest1.length ≤ x.st.bytes.length) (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (match (PqRatchetState.mergeField curSt (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 100).toOption with
       | none => none
       | some (st', rest2) => mergeLoopBin PqRatchetState.mergeField rest2.length st' rest2 0 100) = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R) (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hnext : ∀ (w0' : BitVec 64) (st' : PqRatchetState) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      rest2.length ≤ rest1.length → IsDropSuffix rest1 rest2 →
      (PqRatchetState.mergeField curSt (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 100).toOption =
        some (st', rest2) →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length st' ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A x s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  by_cases htag3 : tag = 3
  · subst htag3
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 312#64)
    wp_steps 2
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    refine decodeState_v1_entry_535d4_cl_placed (v27 := 8#64) hc x w0 curSt rest1 iwt
      hrest1_le hrest1_suf hlen_bound
      (fun hnone => herr_of_none (by
        rw [show BitVec.ofNat 32 3 = 3#32 from rfl, hnone]))
      s0 _ _ R post hpost hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23])
      (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
      (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27])
      (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29]) rfl ?_
    intro w0' st' rest2 sf P' hmf hle2 hsuf2
    exact hnext w0' st' rest2 sf P' hle2 hsuf2 hmf
  · by_cases htag2 : tag = 2
    · subst htag2
      rcases curSt with ⟨optVn, optCh, inner⟩
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 244#64)
      wp_steps 4
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      refine decodeState_chain_entry_53590_cl_placed hc x w0 optVn optCh inner rest1 iwt
        hrest1_le hrest1_suf hlen_bound
        (fun hnone => herr_of_none (by
          rw [show BitVec.ofNat 32 2 = 2#32 from rfl, pqRatchetState_mergeField_tag2, hnone]; rfl))
        s0 _ _ R post hpost hs0A
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23])
        (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
        (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27])
        (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29]) rfl ?_
      intro w0' ch' rest2 sf P' hmf hle2 hsuf2
      exact hnext w0' ⟨optVn, some ch', inner⟩ rest2 sf P' hle2 hsuf2
        (by rw [show BitVec.ofNat 32 2 = 2#32 from rfl, pqRatchetState_mergeField_tag2, hmf]; rfl)
    · by_cases htag1 : tag = 1
      · subst htag1
        rcases curSt with ⟨optVn, optCh, inner⟩
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 184#64)
        wp_steps 6
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        refine decodeState_vn_entry_53554_cl_placed (v27 := 8#64) hc x w0 optVn optCh inner rest1 iwt
          hrest1_le hrest1_suf hlen_bound
          (fun hnone => herr_of_none (by
            rw [show BitVec.ofNat 32 1 = 1#32 from rfl, pqRatchetState_mergeField_tag1, hnone]; rfl))
          s0 _ _ R post hpost hs0A
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
          (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
          (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
          (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23])
          (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
          (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27])
          (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29]) rfl ?_
        intro vn' rest2 sf P' hmf hle2 hsuf2
        exact hnext w0 ⟨some vn', optCh, inner⟩ rest2 sf P' hle2 hsuf2
          (by rw [show BitVec.ofNat 32 1 = 1#32 from rfl, pqRatchetState_mergeField_tag1, hmf]; rfl)
      · -- tag ≥ 4
        have ⟨_, _, _, _, hbeq3, hbne3⟩ := tag_cmp32_of_gt (c := 3) (by omega) htag29
        have ⟨_, _, _, _, hbeq2, hbne2⟩ := tag_cmp32_of_gt (c := 2) (by omega) htag29
        have ⟨_, _, _, _, hbeq1, hbne1⟩ := tag_cmp32_of_gt (c := 1) (by omega) htag29
        have htw32 := tag_setWidth32_ofNat tag
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 456#64)
        wp_steps 6
        apply SepWP.done
          (by simp only [arm64_norm, hx1, htw32, hbeq3, hbne3, hbeq2, hbne2, hbeq1, hbne1])
          (by simp only [arm64_norm, hrun])
        refine decodeState_outer_skip_53664_cl_placed (v27 := 8#64) hc x w0 curSt rest1 iwt tag
          (by omega) hrest1_le hrest1_suf hlen_bound
          (fun hnone => herr_of_none (by
            rw [pqRatchetState_mergeField_other curSt tag htag1 htag2 htag3 (by omega) iwt rest1 100, hnone]; rfl))
          s0 _ _ R post hpost hs0A
          (by dsimp only [decodeStatePlacedEntry]
              simp only [arm64_norm, hx1, htw32, hbeq3, hbne3, hbeq2, hbne2, hbeq1, hbne1])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
          (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
          (by simp only [arm64_norm, hx1, htw32])
          (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
          (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23])
          (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
          (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27])
          (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29]) rfl ?_
        intro rest2 sf P' hsf hle2 hsuf2
        exact hnext w0 curSt rest2 sf P' hle2 hsuf2
          (by rw [pqRatchetState_mergeField_other curSt tag htag1 htag2 htag3 (by omega) iwt rest1 100, hsf]; rfl)

/-- One outer-loop iteration (`+116..+180`) when `¬ cur.length ≤ 0`:
    decodes the field key via `decodeVarint2` and dispatches to the corresponding field handler,
    reaching `entry + 1576` on success. -/
theorem decodeState_outer_body_53510_cl_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64) (curSt : PqRatchetState)
    (cur : List (BitVec 8)) (hgt : ¬ cur.length ≤ 0)
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : mergeLoopBin PqRatchetState.mergeField cur.length curSt cur 0 100 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R) (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hnext : ∀ (w0' : BitVec 64) (st' : PqRatchetState) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      rest2.length < cur.length → rest2.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes rest2 →
      mergeLoopBin PqRatchetState.mergeField cur.length curSt cur 0 100 =
        mergeLoopBin PqRatchetState.mergeField rest2.length st' rest2 0 100 →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length st' ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A x s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hdv_call := hc.decodeVarint2
  subst hP
  rw [sliceCursorAfter_eq_split hcur_le hcur_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc hdv_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_decodeVarint2_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur
    (ret_pc := (blkPl_325).base + 124#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx29, hx29_f0])
    (hlen := by omega) (hP := by sep_focus) ?_ ?_
  · intro s1 key rest1 hdv hlt1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_key
    have hle1 : rest1.length ≤ cur.length := Nat.le_of_lt hlt1
    have hrest1_le : rest1.length ≤ x.st.bytes.length := Nat.le_trans hle1 hcur_le
    have hrest1_suf : IsDropSuffix x.st.bytes rest1 := suffix_trans hcur_le hcur_suf hle1 hsuf1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx1_key hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    by_cases hk : 2 ^ 32 ≤ key.toNat
    · -- key ≥ 2 ^ 32
      have hk_ne : (key >>> 32 == 0#64) = false := key_lsr32_ne_zero_of_ge hk
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1628#64)
      wp_steps 4
      refine SepWP.fold (after_decodeVarint2_to_errFrame_placed H_inner A x hcur_le hcur_suf hle1 curSt s0)
        (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_ne]) (by simp only [arm64_norm, hrun1])
      exact (decodeState_err_53af8_cl_placed hc.toDecodeStateCalleeContractsClPlaced x curSt w0 s0 _ _ R post hpost
        (herr_of_none (mergeLoopBin_of_key_ge protoPrefixStep_pqRatchetState_mergeField hgt hdv hk))
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_ne])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [decodeStateErrFramePlaced, arm64_norm]; ac_rfl))
    · -- key < 2 ^ 32
      have hk_zero : key >>> 32 = 0#64 := key_lsr32_eq_zero_of_lt hk
      rcases hwt : WireType.ofNat? (key.toNat % 8) with _ | iwt
      · -- invalid wire type
        rcases key_and7_of_wt_none hwt with hand7 | hand7
        · apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1640#64)
          wp_steps 7
          refine SepWP.fold (after_decodeVarint2_to_errFrame_placed H_inner A x hcur_le hcur_suf hle1 curSt s0)
            (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7]) (by simp only [arm64_norm, hrun1])
          exact (decodeState_err_53b04_cl_placed hc.toDecodeStateCalleeContractsClPlaced x curSt w0 s0 _ _ R post hpost
            (herr_of_none (mergeLoopBin_of_wt_none protoPrefixStep_pqRatchetState_mergeField hgt hdv hk hwt))
            (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
            (by simp only [decodeStateErrFramePlaced, arm64_norm]; ac_rfl))
        · apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1640#64)
          wp_steps 7
          refine SepWP.fold (after_decodeVarint2_to_errFrame_placed H_inner A x hcur_le hcur_suf hle1 curSt s0)
            (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7]) (by simp only [arm64_norm, hrun1])
          exact (decodeState_err_53b04_cl_placed hc.toDecodeStateCalleeContractsClPlaced x curSt w0 s0 _ _ R post hpost
            (herr_of_none (mergeLoopBin_of_wt_none protoPrefixStep_pqRatchetState_mergeField hgt hdv hk hwt))
            (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
            (by simp only [decodeStateErrFramePlaced, arm64_norm]; ac_rfl))
      · -- valid wire type iwt
        have hand7 : key &&& 7#64 = BitVec.ofNat 64 iwt.toNat := key_and7_of_wt_some hwt
        have ⟨hwt_ult, hwt_ule⟩ := wt_ult6 iwt
        have hlsr3 : BitVec.truncate 32 key >>> 3 = BitVec.ofNat 32 (key.toNat / 8) := key_lsr3_32_eq hk
        have hlsr3_64 : BitVec.zeroExtend 64 (BitVec.truncate 32 key) >>> 3 = BitVec.ofNat 64 (key.toNat / 8) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
            Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
          change ((key.toNat % 4294967296) % 18446744073709551616) / 8 = (key.toNat / 8) % 18446744073709551616
          rw [Nat.mod_eq_of_lt (by omega : key.toNat < 4294967296),
            Nat.mod_eq_of_lt (by omega : key.toNat < 18446744073709551616),
            Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 18446744073709551616)]
        have htag29 : key.toNat / 8 < 2 ^ 29 := tag_lt_pow29_of_key_lt hk
        have hze : BitVec.zeroExtend 64 (BitVec.ofNat 32 (key.toNat / 8)) = BitVec.ofNat 64 (key.toNat / 8) :=
          tag_zeroExtend64_ofNat32 htag29
        have htw32 : BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) = BitVec.ofNat 32 (key.toNat / 8) :=
          tag_setWidth32_ofNat (key.toNat / 8)
        by_cases htag0 : key.toNat / 8 < 1
        · -- tag = 0
          have htag_eq0 : key.toNat / 8 = 0 := by omega
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1652#64)
          wp_steps 9
          refine SepWP.fold (after_decodeVarint2_to_errFrame_placed H_inner A x hcur_le hcur_suf hle1 curSt s0)
            (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hlsr3_64, hze, htw32, htag_eq0])
            (by simp only [arm64_norm, hrun1])
          exact (decodeState_err_53b10_cl_placed hc.toDecodeStateCalleeContractsClPlaced x curSt w0 s0 _ _ R post hpost
            (herr_of_none (mergeLoopBin_of_tag_zero protoPrefixStep_pqRatchetState_mergeField hgt hdv hk hwt htag0))
            (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hlsr3_64, hze, htw32, htag_eq0])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [decodeStateErrFramePlaced, arm64_norm]; ac_rfl))
        · -- tag ≥ 1
          have hloop_step := mergeLoopBin_of_key_ok protoPrefixStep_pqRatchetState_mergeField
            (m := curSt) (limit := 0) (depth' := 100) hgt hdv hk hwt htag0
          simp only [Nat.sub_zero] at hloop_step
          have hcbz64 := tag_cbz64_false (by omega : 1 ≤ key.toNat / 8) htag29
          have hcbz32 := tag_cbz32_false (by omega : 1 ≤ key.toNat / 8) htag29
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 160#64)
          wp_steps 9
          refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
            hcur_le hcur_suf hle1) (by sep_focus) ?_
          refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A)
            (a := s0.sp - 1040#64) (rem1 := cur.length) (rem2 := rest1.length)
            (st := curSt) hle1) (by sep_focus) ?_
          apply SepWP.done
            (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hlsr3_64, hze, htw32, hcbz64, hcbz32])
            (by simp only [arm64_norm, hrun1])
          refine decodeState_outer_dispatch_5353c_cl_placed hc x w0 curSt rest1 (key.toNat / 8) iwt
            (by omega) htag29 hrest1_le hrest1_suf hlen_bound
            (fun hnone => herr_of_none (by
              rw [hloop_step]
              revert hnone
              rcases (PqRatchetState.mergeField curSt (BitVec.ofNat 32 (key.toNat / 8)) (codecWireTypeToProto iwt) rest1 100).toOption with _ | ⟨_, _⟩ <;>
                intro hnone <;> exact hnone))
            s0 _ _ R post hpost hs0A
            (by dsimp only [decodeStatePlacedEntry]
                simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hlsr3_64, hze, htw32, hcbz64, hcbz32])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, hand7, *])
            (by simp only [arm64_norm, hlsr3, hlsr3_64, htw32, hze, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by dsimp only [decodeStateLoopCommonPlaced]; ac_rfl) ?_
          intro w0' st' rest2 sf P' hle2 hsuf2 hmf
          exact hnext w0' st' rest2 sf P'
            (Nat.lt_of_le_of_lt hle2 hlt1) (Nat.le_trans hle2 hrest1_le)
            (suffix_trans hrest1_le hrest1_suf hle2 hsuf2) (by rw [hloop_step, hmf])
  · intro s1 hdv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 _
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hnone_loop : mergeLoopBin PqRatchetState.mergeField cur.length curSt cur 0 100 = none := by
      have h := mergeLoopBin_of_decodeVarint_none protoPrefixStep_pqRatchetState_mergeField
        (m := curSt) (limit := 0) (depth' := 100) hgt hdv
      simpa using h
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2392#64)
    refine SepWP.fold (loopCommon_calleeErr_to_errFrame_placed H_inner A x hcur_le hcur_suf
      cur.length curSt s0) (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
    refine SepWP.fold (scratch_688_fold_48 s0.sp w0)
      (by dsimp only [decodeStateErrFramePlaced]; sep_focus) ?_
    wp_steps 2
    apply SepWP.done
      (by simp only [arm64_norm, hpc1, hx0_1, *])
      (by simp only [arm64_norm, hrun1])
    refine SepWPpIPlaced.of_sepWP_ret_lscl fun hcl => ?_
    exact decodeState_err_tail_53df4_cl_placed hc.toDecodeStateCalleeContractsClPlaced x curSt 0 s0 _ hcl _ R post hpost
      (herr_of_none hnone_loop)
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hpc1, hx0_1, *])
      (by simp only [arm64_norm, hrun1])
      (by simp only [arm64_norm, hsp1])
      hs0A
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *])
      (by simp only [decodeStateErrFramePlaced, arm64_norm]; ac_rfl)

/-! ## 3. Outer Loop (`+1576`) by Induction on Remaining Slice Length -/

private theorem len_cbz64_false {n : Nat} (h1 : 1 ≤ n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)] at h2
  omega

/-- Outer loop latch at `+1576`:
    - If `cur = []` (`x20 = 0`), branches to `+1676` (`decodeState_ok_exit_53b28_cl_placed`).
    - If `cur ≠ []` (`x20 ≠ 0`), branches to `+116` (`decodeState_outer_body_53510_cl_placed`) and recurses. -/
theorem decodeState_outer_loop_53ac4_cl_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A ext)
    (x : DecodeStateGhost) (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R) (hs0A : s0.spAligned = true) :
    ∀ (fuel : Nat) (w0 : BitVec 64) (curSt : PqRatchetState) (cur : List (BitVec 8))
      (s : State) (P : SepProp),
      cur.length ≤ fuel →
      cur.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes cur →
      (mergeLoopBin PqRatchetState.mergeField cur.length curSt cur 0 100 = none →
        spqrDecodeState x.st.bytes = .error .stateDecode) →
      (∀ stFinal, mergeLoopBin PqRatchetState.mergeField cur.length curSt cur 0 100 = some stFinal →
        spqrDecodeState x.st.bytes = .ok stFinal) →
      s.pc = decodeStatePlacedEntry + 1576#64 →
      s.status = .Running → s.sp = s0.sp - 1392#64 → TraceVRegs s s0 →
      s.readReg64 .x19 = x.outPtr →
      s.readReg64 .x20 = BitVec.ofNat 64 cur.length →
      s.readReg64 .x21 = 0x8000000000000006#64 →
      s.readReg64 .x22 = s0.sp - 1040#64 →
      s.readReg64 .x23 = -1#64 →
      s.readReg64 .x24 = s0.sp - 912#64 →
      s.readReg64 .x25 = s0.sp - 688#64 →
      s.readReg64 .x26 = -2#64 →
      s.readReg64 .x27 = 8#64 →
      s.readReg64 .x28 = 1#64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
        (decodeStatePanicPostPlaced H_inner A x s0 R)
  | 0, w0, curSt, cur, s, P, hfuel, _, _, _, hok_of_some,
    hpc, hrun, hsp, htr, hx19, hx20, _, hx22, _, _, _, _, _, _, _, hP => by
    have hcur_nil : cur = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hcur_nil
    have hloop_eq : mergeLoopBin PqRatchetState.mergeField ([] : List (BitVec 8)).length curSt [] 0 100 = some curSt :=
      mergeLoopBin_eq_limit PqRatchetState.mergeField 0 curSt [] 0 100 rfl
    have hok : spqrDecodeState x.st.bytes = .ok curSt := hok_of_some curSt hloop_eq
    subst hP
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, List.length_nil] at hpc hx20 ⊢
    apply SepWPpIPlaced.of_sepWPp
    apply SepWPp.of_sepWP_ret
    wp_steps 2
    exact decodeState_ok_exit_53b28_cl_placed hc.toDecodeStateCalleeContractsClPlaced x w0 curSt hok s0 _ _ R post hpost hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hpc, hx20])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx22]) rfl
  | fuel + 1, w0, curSt, cur, s, P, hfuel, hcur_le, hcur_suf, herr_of_none, hok_of_some,
    hpc, hrun, hsp, htr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hP => by
    by_cases hgt : ¬ cur.length ≤ 0
    · -- cur.length > 0
      have hcbz : (BitVec.ofNat 64 cur.length == 0#64) = false :=
        len_cbz64_false (by omega) (by omega)
      subst hP
      dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 116#64)
      wp_steps 1
      apply SepWP.done (by simp only [arm64_norm, hpc, hx20, hcbz]) (by simp only [arm64_norm, hrun])
      refine decodeState_outer_body_53510_cl_placed hc x w0 curSt cur hgt hcur_le hcur_suf hlen_bound
        herr_of_none s0 _ _ R post hpost hs0A
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hpc, hx20, hcbz])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
        (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
        (by simp only [arm64_norm, hx29]) rfl ?_
      intro w0' st' rest2 sf P' hlt2 hle2 hsuf2 hloop_eq
      exact decodeState_outer_loop_53ac4_cl_placed hc x hlen_bound s0 R post hpost hs0A
        fuel w0' st' rest2 sf P' (by omega) hle2 hsuf2
        (fun hnone => herr_of_none (by rw [hloop_eq, hnone]))
        (fun stFinal hsome => hok_of_some stFinal (by rw [hloop_eq, hsome]))
    · -- cur.length = 0
      exact decodeState_outer_loop_53ac4_cl_placed hc x hlen_bound s0 R post hpost hs0A
        0 w0 curSt cur s P (by omega) hcur_le hcur_suf herr_of_none hok_of_some
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP

/-! ## 4. Prologue (`+0..+112`) and Top-Level Theorem `decodeState_cl_placed_ok` -/

private theorem vecArg_expose_len (A : RustAlloc) (st : VecArg) :
    st.at A ⊢
      (st.v ↦₆₄ st.cap) ∗ ((st.v + 8#64) ↦₆₄ st.ptr) ∗
      ((st.v + 16#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
      vecU8Heap A st.cap st.ptr st.bytes := by
  rw [VecArg.at, vecU8At_eq_header_heap, vecHeader]
  exact Entails.of_eq (by ac_rfl)

private theorem vecArg_fold_len (A : RustAlloc) (st : VecArg) :
    (st.v ↦₆₄ st.cap) ∗ ((st.v + 8#64) ↦₆₄ st.ptr) ∗
      ((st.v + 16#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
      vecU8Heap A st.cap st.ptr st.bytes ⊢
      st.at A := by
  rw [VecArg.at, vecU8At_eq_header_heap, vecHeader]
  exact Entails.of_eq (by ac_rfl)

private theorem nonempty_prologue_frame_assemble (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (st : VecArg) :
    ((sp - 1056#64) ↦₆₄ st.ptr) ∗
      ((sp - 1048#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
      (st.ptr ↦ₛ st.bytes) ∗
      ((sp - 1040#64) ↦₆₄ (-1#64)) ∗ memRegion (sp - 1032#64) 40 ∗
      ((sp - 992#64) ↦₆₄ (-1#64)) ∗ memRegion (sp - 984#64) 72 ∗
      ((sp - 912#64) ↦₆₄ (-3#64)) ∗ memRegion (sp - 904#64) 216 ⊢
      sliceCursorAfter (sp - 1056#64) st.ptr st.bytes st.bytes ∗
      protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) st.bytes.length default := by
  rw [pqRatchetState_default_eq]
  unfold sliceCursorAfter protoPqRatchetStateCapOkAt
    optVersionNegotiationPBCapOkAt optChainPBCapOkAt optProtoPqRatchetInnerCapOkAt
    noneCap none3Cap
  dsimp only
  have hsub0 : st.bytes.length - st.bytes.length = 0 := Nat.sub_self _
  have hptr0 : st.ptr + BitVec.ofNat 64 0 = st.ptr := by simp
  have ha1048 : (sp - 1056#64) + 8#64 = sp - 1048#64 := by bv_omega
  have ha1032 : (sp - 1040#64) + 8#64 = sp - 1032#64 := by bv_omega
  have ha992 : (sp - 1040#64) + 48#64 = sp - 992#64 := by bv_omega
  have ha984 : (sp - 992#64) + 8#64 = sp - 984#64 := by bv_omega
  have ha912 : (sp - 1040#64) + 128#64 = sp - 912#64 := by bv_omega
  have ha904 : (sp - 912#64) + 8#64 = sp - 904#64 := by bv_omega
  rw [hsub0, hptr0, ha1048, ha1032, ha992, ha984, ha912, ha904]
  exact Entails.of_eq (by ac_rfl)

private theorem decodeState_nonempty_frame_split_s0 (sp0 : BitVec 64) :
    ((sp0 - 1392#64) ↦₆₄ 0#64) ∗ memRegion (sp0 - 1384#64) 1288 ⊢
      memRegion (sp0 - 1392#64) 336 ∗
      memRegion (sp0 - 1032#64) 40 ∗
      memRegion (sp0 - 984#64) 72 ∗
      memRegion (sp0 - 904#64) 216 ∗
      memRegion (sp0 - 688#64) 352 ∗
      memRegion (sp0 - 328#64) 224 ∗
      memRegion (sp0 - 104#64) 8 ∗
      (∃∗ bRef : BitVec 64, ∃∗ in0 : BitVec 64, ∃∗ ch0 : BitVec 64,
       ∃∗ vn0 : BitVec 64, ∃∗ cLen : BitVec 64, ∃∗ cPtr : BitVec 64,
        ((sp0 - 1056#64) ↦₆₄ cPtr) ∗ ((sp0 - 1048#64) ↦₆₄ cLen) ∗
        ((sp0 - 1040#64) ↦₆₄ vn0) ∗ ((sp0 - 992#64) ↦₆₄ ch0) ∗
        ((sp0 - 912#64) ↦₆₄ in0) ∗ ((sp0 - 336#64) ↦₆₄ bRef)) := by
  have hsplit := decodeState_nonempty_frame_split (sp0 - 1392#64) 0#64
  have h1 : sp0 - 1392#64 + 8#64 = sp0 - 1384#64 := bv_sub_add_lit sp0 1392 8
  have h2 : sp0 - 1392#64 + 360#64 = sp0 - 1032#64 := bv_sub_add_lit sp0 1392 360
  have h3 : sp0 - 1392#64 + 408#64 = sp0 - 984#64 := bv_sub_add_lit sp0 1392 408
  have h4 : sp0 - 1392#64 + 488#64 = sp0 - 904#64 := bv_sub_add_lit sp0 1392 488
  have h5 : sp0 - 1392#64 + 704#64 = sp0 - 688#64 := bv_sub_add_lit sp0 1392 704
  have h6 : sp0 - 1392#64 + 1064#64 = sp0 - 328#64 := bv_sub_add_lit sp0 1392 1064
  have h7 : sp0 - 1392#64 + 1288#64 = sp0 - 104#64 := bv_sub_add_lit sp0 1392 1288
  have h8 : sp0 - 1392#64 + 336#64 = sp0 - 1056#64 := bv_sub_add_lit sp0 1392 336
  have h9 : sp0 - 1392#64 + 344#64 = sp0 - 1048#64 := bv_sub_add_lit sp0 1392 344
  have h10 : sp0 - 1392#64 + 352#64 = sp0 - 1040#64 := bv_sub_add_lit sp0 1392 352
  have h11 : sp0 - 1392#64 + 400#64 = sp0 - 992#64 := bv_sub_add_lit sp0 1392 400
  have h12 : sp0 - 1392#64 + 480#64 = sp0 - 912#64 := bv_sub_add_lit sp0 1392 480
  have h13 : sp0 - 1392#64 + 1056#64 = sp0 - 336#64 := bv_sub_add_lit sp0 1392 1056
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13] at hsplit
  exact hsplit

/-- Stack frame initialization (`+52..+116`) on the non-empty input path. -/
theorem decodeState_prologue_init_534d0_cl_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A ext)
    (x : DecodeStateGhost) (hbs_nil : x.st.bytes ≠ [])
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 52#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = x.st.ptr)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 x.st.bytes.length)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      (x.st.ptr ↦ₛ x.st.bytes) ∗
      vecArgRestAt A x.st ∗
      memRegion (s0.sp - 1384#64) 1288 ∗
      ((s0.sp - 1392#64) ↦₆₄ 0#64) ∗
      v1StateJumpTablesPlacedAt ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hgt0 : ¬ x.st.bytes.length ≤ 0 := by
    have := List.length_pos_of_ne_nil hbs_nil; omega
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 116#64)
  refine SepWP.fold (decodeState_nonempty_frame_split_s0 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  wp_steps 16
  refine SepWP.fold (nonempty_prologue_frame_assemble H_inner A s0.sp x.st) (by sep_focus) ?_
  refine SepWP.fold (scratch_688_split_48 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  rename_i w0_scr
  apply SepWP.done (by simp only [arm64_norm, hpc]) (by simp only [arm64_norm, hrun])
  refine decodeState_outer_body_53510_cl_placed hc x w0_scr default x.st.bytes hgt0
    (Nat.le_refl _) (by unfold IsDropSuffix; simp) hlen_bound
    (spqrDecodeState_eq_of_mergeLoopBin_top_err hbs_nil)
    s0 _ _ R post hpost hs0A
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hpc])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, hx29])
    (by unfold decodeStateLoopCommonPlaced; simp only [arm64_norm, hsp, hx29]; ac_rfl) ?_
  intro w0' st' rest2 sf P' _ hle2 hsuf2 hloop_eq
  exact decodeState_outer_loop_53ac4_cl_placed hc x hlen_bound s0 R post hpost hs0A
    rest2.length w0' st' rest2 sf P' (Nat.le_refl _) hle2 hsuf2
    (fun hnone => spqrDecodeState_eq_of_mergeLoopBin_top_err hbs_nil (by rw [hloop_eq, hnone]))
    (fun stFinal hsome => spqrDecodeState_eq_of_mergeLoopBin_top_ok hbs_nil (by rw [hloop_eq, hsome]))

/-- Full execution of `spqr::decode_state` from entry `+0`. -/
theorem decodeState_entry_5349c_cl_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A ext)
    (x : DecodeStateGhost) (s0 : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s0.pc = decodeStatePlacedEntry)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = x.outPtr)
    (hx0 : s0.readReg64 .x0 = x.st.v)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt s0.sp decodeStateStackX) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s0 P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  subst hP
  rw [stackAt_decodeState_entry_split s0.sp]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  by_cases hbs_nil : x.st.bytes = []
  · -- empty input
    have hlen0 : BitVec.ofNat 64 x.st.bytes.length = 0#64 := by rw [hbs_nil]; rfl
    apply SepWPpIPlaced.of_sepWPp
    apply SepWPp.of_sepWP_ret
    wp_pull_exists
    unfold decodeStateSavedAt
    refine SepWP.fold (vecArg_expose_len A x.st) (by sep_focus) ?_
    wp_steps 12
    refine SepWP.fold (vecArg_fold_len A x.st) (by sep_focus) ?_
    exact decodeState_empty_53ae0_placed x 0#64 hbs_nil s0 _ _ R post hpost
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hpc, hx0, hlen0])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm])
      hs0A
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hx8])
      (by unfold decodeStateSavedAt; simp only [arm64_norm]; ac_rfl)
  · -- non-empty input
    have hgt0 : ¬ x.st.bytes.length ≤ 0 := by
      have := List.length_pos_of_ne_nil hbs_nil; omega
    have hcbz : (BitVec.ofNat 64 x.st.bytes.length == 0#64) = false :=
      len_cbz64_false (by omega) (by omega)
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 52#64)
    wp_pull_exists
    unfold decodeStateSavedAt
    refine SepWP.fold (vecArg_split_bytes A x.st hbs_nil) (by sep_focus) ?_
    unfold vecArgRestAt
    wp_focus_pure; intro hpure_st
    wp_steps 13
    have hfold_rest :
        (x.st.v ↦₆₄ x.st.cap) ∗ ((x.st.v + 8#64) ↦₆₄ x.st.ptr) ∗
          ((x.st.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.bytes.length) ∗
          A.live x.st.ptr x.st.cap.toNat 1 ∗
          memRegion (x.st.ptr + BitVec.ofNat 64 x.st.bytes.length) (x.st.cap.toNat - x.st.bytes.length) ⊢
          vecArgRestAt A x.st := by
      unfold vecArgRestAt
      refine Entails.trans (Entails.of_eq ?_)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (Entails.pure_right hpure_st (Entails.refl _)))))
      ac_rfl
    refine SepWP.fold hfold_rest (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hpc, hx0, hcbz]) (by simp only [arm64_norm, hrun])
    exact decodeState_prologue_init_534d0_cl_placed hc x hbs_nil hlen_bound s0 _ _ R post hpost hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hpc, hx0, hcbz])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx8])
      (by simp only [arm64_norm])
      (by unfold decodeStateSavedAt; simp only [arm64_norm]; ac_rfl)

/-- `spqr::decode_state` (Block `325`) satisfies `DecodeStatePlacedOkX H_inner A ext`
    given `DecodeStateCalleeContractsClPlacedX H_inner A ext`. -/
theorem decodeState_cl_placed_ok [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A ext) :
    DecodeStatePlacedOkX H_inner A ext := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  change s0.mem ⊨ ((spqrDecodeStatePlacedSpec H_inner A).pre x s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  dsimp only [spqrDecodeStatePlacedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hlen_bound⟩, hm⟩
  exact ⟨_, R, hm, decodeState_entry_5349c_cl_placed hc x s0 _ R
    (decodeStatePostPlaced H_inner A x s0 R) rfl halign hpc hrun hx8 hx0 hlen_bound rfl hinv⟩

end CryptoVerification.SpqrV1.Top.DecodeState
