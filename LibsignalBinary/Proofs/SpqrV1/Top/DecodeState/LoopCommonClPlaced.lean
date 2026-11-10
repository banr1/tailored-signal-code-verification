/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlaced
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# Code-Loaded Shared Call Wrappers for `spqr::decode_state` (Block `325`)

Proves panic-aware code-loaded call wrappers (`decode_varint`, `skip_field`, and
`ChainParams::merge`) for `spqr::decode_state` under `LibsignalPlacement`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

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

/-! ## Code-Loaded Panic-Aware Call Wrappers (`decode_varint`, `skip_field`, `ChainParams::merge`) -/

theorem SepWPpIPlaced.call_decodeVarint2_cl [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (Varint.decodeVarint2Spec A)))
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hP : P = ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (v : BitVec 64) (rest : List (BitVec 8)),
      decodeVarint bs = some (v, rest) →
      rest.length < bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = v →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R))
    (herr : ∀ sf : State,
      decodeVarint bs = none →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 1#64 → sf.readReg64 .x1 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_dv : DecodeVarintSlowGhost := ⟨bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - Varint.decodeVarint2Stack) ∗ F
  have hpre : s.mem ⊨ (withLsCodeLoaded lsmpl (Varint.decodeVarint2Spec A)).pre x_dv s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv.1, ?_⟩
    dsimp only [Varint.decodeVarint2Spec, x_dv]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur Varint.decodeVarint2Stack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x_dv (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (Varint.decodeVarint2Spec A).post x_dv s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [Varint.decodeVarint2Spec, x_dv] at hpost
    rw [hsp] at hpost
    rcases hdv : decodeVarint bs with _ | ⟨v, rest⟩
    · simp only [hdv] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 1#64⌝ ∗ (⌜sm.readReg64 .x1 ≠ 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - Varint.decodeVarint2Stack) ∗
              stackAt sp_cur Varint.decodeVarint2Stack) ∗
            decodeErrorAtStackLen A (sm.readReg64 .x1) 0 ∗
            memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_1, hx1_ne, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur Varint.decodeVarint2Stack (by decide))))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm hdv hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_1 hx1_ne
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hdv] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64 ∧ sm.readReg64 .x1 = v⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - Varint.decodeVarint2Stack) ∗
              stackAt sp_cur Varint.decodeVarint2Stack) ∗
            sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, ⟨hx0_0, hx1_v⟩, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur Varint.decodeVarint2Stack (by decide))))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ := hok sm v rest hdv (decodeVarint_length hdv) (decodeVarint_suffix hdv)
        hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 hx1_v
        (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ (Varint.decodeVarint2Spec A).onPanic x_dv s sm ∗ (F_ext ∗ R') at hpost
    rw [← sepConj_assoc] at hpost
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, ?_⟩)⟩
    intro hm'
    dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, Varint.decodeVarint2Spec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · dsimp only [Varint.decodeVarint2Spec, withLsCodeLoaded] at hpost
    exact (allowPanic_not_exited hpost).elim
  · exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_skipField3_cl [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipField3Spec A)))
    (wt : WireType) (tag depth : Nat) (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag)
    (htag : tag < 2 ^ 32)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hx3 : (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 depth)
    (hdepth : depth ≤ 100)
    (hlen : bs.length < 2 ^ 63)
    (hP : P = ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (rest : List (BitVec 8)),
      skipField (2 * bs.length + 2) depth tag wt bs = some rest →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R))
    (herr : ∀ sf : State,
      skipField (2 * bs.length + 2) depth tag wt bs = none →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_sf : SkipFieldGhost := ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  have hM : skipField3Stack depth ≤ v1StateMergeStack := by
    have h100 : skipField3Stack 100 ≤ v1StateMergeStack := by decide
    have hmono : skipField3Stack depth ≤ skipField3Stack 100 := by unfold skipField3Stack; omega
    omega
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - skipField3Stack depth) ∗ F
  have hpre : s.mem ⊨ (withLsCodeLoaded lsmpl (skipField3Spec A)).pre x_sf s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv.1, ?_⟩
    dsimp only [skipField3Spec, x_sf]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, htag, hx2, hx3, by omega, hlen⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur (skipField3Stack depth) hM)))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x_sf (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (skipField3Spec A).post x_sf s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [skipField3Spec, x_sf] at hpost
    rw [hsp] at hpost
    rcases hsf : skipField (2 * bs.length + 2) depth tag wt bs with _ | rest
    · simp only [hsf] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - skipField3Stack depth) ∗
              stackAt sp_cur (skipField3Stack depth)) ∗
            decodeErrorAtStackLen A (sm.readReg64 .x0) 0 ∗
            memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_ne, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur (skipField3Stack depth) hM)))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm hsf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hsf] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - skipField3Stack depth) ∗
              stackAt sp_cur (skipField3Stack depth)) ∗
            sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_0, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur (skipField3Stack depth) hM)))))) hpost1
      have hle := (skip_length (2 * bs.length + 2)).1 depth tag wt bs rest hsf
      have hsuf := (skip_suffix (2 * bs.length + 2)).1 depth tag wt bs rest hsf
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm rest hsf hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ (skipField3Spec A).onPanic x_sf s sm ∗ (F_ext ∗ R') at hpost
    rw [← sepConj_assoc] at hpost
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, ?_⟩)⟩
    intro hm'
    dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, skipField3Spec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · dsimp only [skipField3Spec, withLsCodeLoaded] at hpost
    exact (allowPanic_not_exited hpost).elim
  · exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_chainParamsMerge_cl [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (chainParamsMergeSpec A)))
    (wt : WireType) (msgPtr : BitVec 64) (msg : ChainParamsPB)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = msgPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hP : P = (chainParamsPBAt msgPtr msg ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : ChainParamsPB) (rest : List (BitVec 8)),
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption = some (m', rest) →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          chainParamsPBAt msgPtr m' ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R))
    (herr : ∀ (sf : State) (n : Nat) (m' : ChainParamsPB),
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption = none →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 1 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A (sf.readReg64 .x0) n ∗
          chainParamsPBAt msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_cp : ChainParamsMergeGhost := ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - chainParamsMergeStack) ∗ F
  have hpre : s.mem ⊨ (withLsCodeLoaded lsmpl (chainParamsMergeSpec A)).pre x_cp s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv.1, ?_⟩
    dsimp only [chainParamsMergeSpec, x_cp]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur chainParamsMergeStack (by decide)))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x_cp (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (chainParamsMergeSpec A).post x_cp s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [chainParamsMergeSpec, x_cp] at hpost
    rw [hsp] at hpost
    rcases hcp : (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption with _ | ⟨m', rest⟩
    · simp only [hcp, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨m', n, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗ (⌜n ≤ 1⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - chainParamsMergeStack) ∗
              stackAt sp_cur chainParamsMergeStack) ∗
            decodeErrorAtStackLen A (sm.readReg64 .x0) n ∗
            chainParamsPBAt msgPtr m' ∗
            memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_ne, hn, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur chainParamsMergeStack (by decide))))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm n m' hcp hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne hn
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hcp] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - chainParamsMergeStack) ∗
              stackAt sp_cur chainParamsMergeStack) ∗
            chainParamsPBAt msgPtr m' ∗
            sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_0, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur chainParamsMergeStack (by decide))))))) hpost1
      have ⟨hle, hsuf⟩ := proto_mergeMessage_suffix hcp
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm m' rest hcp hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ (chainParamsMergeSpec A).onPanic x_cp s sm ∗ (F_ext ∗ R') at hpost
    rw [← sepConj_assoc] at hpost
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, ?_⟩)⟩
    intro hm'
    dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, chainParamsMergeSpec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · dsimp only [chainParamsMergeSpec, withLsCodeLoaded] at hpost
    exact (allowPanic_not_exited hpost).elim
  · exact False.elim (not_satisfies_false_sepConj hpost)

end CryptoVerification.SpqrV1.Top.DecodeState
