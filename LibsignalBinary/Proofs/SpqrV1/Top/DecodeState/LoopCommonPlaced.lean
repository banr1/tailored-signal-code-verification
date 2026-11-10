/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlaced
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# Relocatable `[LibsignalPlacement]` Verification of `spqr::decode_state` (Block `325`) — Shared Loop Frame & Call Wrappers
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

/-! ## 1. `SepWPpIPlaced` (`LibsignalCodeRoLoaded lsmpl`-Threading `SepWPp`) & Stack Frame Helpers -/

/-- `SepWPp` enriched with `LibsignalCodeRoLoaded lsmpl s.mem`, automatically preserved across `Steps`
    (`SepWPpIPlaced.of_sepWP`) and available to `withLsCodeRoLoaded lsmpl` callee contracts. -/
def SepWPpIPlaced [LibsignalPlacement] (prog : Program) (ret : BitVec 64) (s : State) (P : SepProp)
    (Q Q_err : State → SepProp → Prop) : Prop :=
  LibsignalCodeRoLoaded lsmpl s.mem → SepWPp prog ret s P Q Q_err

theorem SepWPpIPlaced.of_sepWPp [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Q_err) :
    SepWPpIPlaced prog ret s P Q Q_err :=
  fun _ => h

theorem SepWPpIPlaced.of_sepWP [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64} {s : State}
    {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpIPlaced prog ret sm Pm Q Q_err)) :
    SepWPpIPlaced prog ret s P Q Q_err := by
  intro hinv R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ := hnext (hinv.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPpIPlaced.exists_elim [LibsignalPlacement] {α : Type} {prog : Program} {ret : BitVec 64}
    {s : State} {P : α → SepProp} {Q Q_err : State → SepProp → Prop}
    (h : ∀ x, SepWPpIPlaced prog ret s (P x) Q Q_err) :
    SepWPpIPlaced prog ret s (∃∗ x, P x) Q Q_err :=
  fun hinv => SepWPp.exists_elim (fun x => h x hinv)

theorem SepWPpIPlaced.mono_pre [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : P ⊢ P') (hwp : SepWPpIPlaced prog ret s P' Q Q_err) :
    SepWPpIPlaced prog ret s P Q Q_err :=
  fun hinv => SepWPp.mono_pre h (hwp hinv)

/-- Shared stack & heap frame across the active loops of `spqr::decode_state` under `[LibsignalPlacement]`. -/
abbrev decodeStateLoopCommonPlaced [LibsignalPlacement] (A : RustAlloc)
    (x : DecodeStateGhost) (s0 : State) : SepProp :=
  v1StateJumpTablesPlacedAt ∗
  vecArgRestAt A x.st ∗
  memRegion x.outPtr 352 ∗
  A.pool ∗
  stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
  memRegion (s0.sp - 1392#64) 336 ∗
  ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
  memRegion (s0.sp - 328#64) 224 ∗
  memRegion (s0.sp - 104#64) 8 ∗
  decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)

/-- Fold `memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes) ∗ protoPqRatchetStateAt ... ∗
    memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗ decodeStateLoopCommonPlaced`
    into `decodeStateErrFramePlaced`. -/
theorem loopCommon_to_errFrame_placed [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      (x.st.ptr ↦ₛ x.st.bytes) ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A x s0 ⊢
      decodeStateErrFramePlaced H_inner A x curSt s0 := by
  dsimp only [decodeStateLoopCommonPlaced, decodeStateErrFramePlaced]
  have hst := vecArg_join_bytes A x.st
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        (v1StateJumpTablesPlacedAt ∗ vecArgRestAt A x.st ∗ memRegion x.outPtr 352 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          memRegion (s0.sp - 1392#64) 336 ∗ ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
          memRegion (s0.sp - 328#64) 224 ∗ memRegion (s0.sp - 104#64) 8 ∗
          decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) =
      v1StateJumpTablesPlacedAt ∗
        ((x.st.ptr ↦ₛ x.st.bytes) ∗ vecArgRestAt A x.st) ∗
        memRegion x.outPtr 352 ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
        (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗ memRegion (s0.sp - 328#64) 224 ∗
          memRegion (s0.sp - 104#64) 8) ∗
        decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono hst (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono hlow (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hup)))))))))

/-- Fold `sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur` + `protoPqRatchetStateCapOkAt`
    + `decodeStateLoopCommonPlaced` directly into `decodeStateErrFramePlaced`. -/
theorem loopCommon_cursor_to_errFrame_placed [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (x : DecodeStateGhost) (cur : List (BitVec 8)) (remLen : Nat) (curSt : PqRatchetState) (s0 : State) :
    sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remLen curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A x s0 ⊢
      decodeStateErrFramePlaced H_inner A x curSt s0 := by
  have h1 := sliceCursorAfter_to_memRegion s0.sp x.st.ptr x.st.bytes cur
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) remLen curSt
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) ?_
  rw [sepConj_assoc]
  exact loopCommon_to_errFrame_placed H_inner A x curSt s0

/-- Fold callee error cursor output (`memRegion slot 16 ∗ ((ptr + ...) ↦ₛ cur) ∗ (ptr ↦ₛ take)`)
    + `protoPqRatchetStateCapOkAt` + `decodeStateLoopCommonPlaced` into `decodeStateErrFramePlaced`. -/
theorem loopCommon_calleeErr_to_errFrame_placed [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (x : DecodeStateGhost) {cur : List (BitVec 8)} (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur) (remLen : Nat) (curSt : PqRatchetState) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remLen curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A x s0 ⊢
      decodeStateErrFramePlaced H_inner A x curSt s0 := by
  have h1 := pointsToBytes_prefix_join (ptr := x.st.ptr) hcur_le hcur_suf
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) remLen curSt
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remLen curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 =
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
          ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remLen curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_right (sepConj_mono h1 (sepConj_mono_left h2))) ?_
  exact loopCommon_to_errFrame_placed H_inner A x curSt s0

/-- Fold callee error cursor output + `protoPqRatchetStateAt` + `decodeStateLoopCommonPlaced` into `decodeStateErrFramePlaced`. -/
theorem loopCommon_calleeErr_proto_to_errFrame_placed [LibsignalPlacement] (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (x : DecodeStateGhost) {cur : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (curSt : PqRatchetState) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A x s0 ⊢
      decodeStateErrFramePlaced H_inner A x curSt s0 := by
  have h1 := pointsToBytes_prefix_join (ptr := x.st.ptr) hcur_le hcur_suf
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 =
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
          ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h1)) ?_
  exact loopCommon_to_errFrame_placed H_inner A x curSt s0

/-! ## 2. Panic-Aware Call Wrappers (`decode_varint`, `skip_field`, `bytes::merge`, `ChainParams::merge`) -/

theorem SepWPpIPlaced.call_decodeVarint2 [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (Varint.decodeVarint2Spec A))
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
  have hpre : s.mem ⊨ (Varint.decodeVarint2Spec A).pre x_dv s ∗ (F_ext ∗ R') := by
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
  · dsimp only [Varint.decodeVarint2Spec, x_dv] at hpost
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
        herr sm hdv hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_1 hx1_ne (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
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
        hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 hx1_v (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, ?_⟩)⟩
    intro hm'
    dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, Varint.decodeVarint2Spec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · dsimp only [Varint.decodeVarint2Spec] at hpost
    exact (allowPanic_not_exited hpost).elim
  · exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_skipField3 [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (skipField3Spec A))
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
  have hpre : s.mem ⊨ (skipField3Spec A).pre x_sf s ∗ (F_ext ∗ R') := by
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
  · dsimp only [skipField3Spec, x_sf] at hpost
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
        herr sm hsf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
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
        hok sm rest hsf hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, ?_⟩)⟩
    intro hm'
    dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, skipField3Spec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · dsimp only [skipField3Spec] at hpost
    exact (allowPanic_not_exited hpost).elim
  · exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_bytesMerge3 [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (wt : WireType) (valPtr : BitVec 64) (valBs : List (BitVec 8))
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
    (hx1 : s.readReg64 .x1 = valPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hP : P = (vecU8CapOkAt A valPtr bs.length valBs ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (v rest : List (BitVec 8)),
      (Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption = some (v, rest) →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          vecU8CapOkAt A valPtr rest.length v ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R))
    (herr : ∀ sf : State,
      (Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption = none →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          rustBytesVecAt A valPtr valBs ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
  intro hinv R' hm hL
  rw [hP] at hm
  unfold vecU8CapOkAt at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨valCap, valBuf, hm⟩
  have hm_pure : s.mem ⊨ ⌜BytesMergeCapOk valCap bs.length⌝ ∗
      (((vecU8At A valPtr valCap valBuf valBs ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr bs ∗ A.pool ∗
        stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F) ∗ R') := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    ac_rfl
  rw [satisfies_pure_sepConj] at hm_pure
  rcases hm_pure with ⟨hcap_ok, hm⟩
  let sp_cur := s0.sp - 1392#64
  let x_bm : BytesMergeGhost := ⟨wt, valPtr, valCap, valBuf, valBs, bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - bytesMerge3Stack) ∗ F
  have hpre : s.mem ⊨ (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)).pre x_bm s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    dsimp only [bytesMerge3RawSpec, x_bm]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hcap_ok⟩, ?_⟩
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur bytesMerge3Stack (by decide)))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x_bm (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (bytesMerge3RawSpec A).post x_bm s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [bytesMerge3RawSpec, x_bm] at hpost
    have hmb_eq : mergeBytes wt bs = (Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption := by
      have h := proto_mergeBytes_toOption (codecWireTypeToProto wt) bs
      rw [protoWireTypeToCodec_codecWireTypeToProto] at h
      exact h.symm
    rw [hmb_eq, hsp] at hpost
    rcases hmb : (Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption with _ | ⟨v, rest⟩
    · simp only [hmb] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗
          (vecU8At A valPtr valCap valBuf valBs ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - bytesMerge3Stack) ∗
                stackAt sp_cur bytesMerge3Stack) ∗
              decodeErrorAtStackLen A (sm.readReg64 .x0) 0 ∗
              memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_ne, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hvec : vecU8At A valPtr valCap valBuf valBs ⊢ rustBytesVecAt A valPtr valBs := by
        unfold rustBytesVecAt
        exact Entails.sepExists_right valCap (Entails.sepExists_right valBuf (Entails.refl _))
      have hpost1' := Satisfies.mono (sepConj_mono hvec (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur bytesMerge3Stack (by decide)))))))) hpost1
      have hpost2 : sm.mem ⊨
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt sp_cur v1StateMergeStack ∗
            decodeErrorAtStackLen A (sm.readReg64 .x0) 0 ∗
            rustBytesVecAt A valPtr valBs ∗
            memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R' :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost1'
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm hmb hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hmb] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - bytesMerge3Stack) ∗
              stackAt sp_cur bytesMerge3Stack) ∗
            vecU8CapOkAt A valPtr rest.length v ∗
            sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext, vecU8CapOkAt]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_0, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur bytesMerge3Stack (by decide))))))) hpost1
      have ⟨hle, hsuf⟩ := proto_mergeBytes_suffix hmb
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm v rest hmb hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ (bytesMerge3RawSpec A).onPanic x_bm s sm ∗ (F_ext ∗ R') at hpost
    rw [← sepConj_assoc] at hpost
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, ?_⟩)⟩
    intro hm'
    dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, bytesMerge3RawSpec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · dsimp only [bytesMerge3RawSpec, withLsCodeRoLoaded] at hpost
    exact (allowPanic_not_exited hpost).elim
  · exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_chainParamsMerge [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (chainParamsMergeSpec A))
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
  have hpre : s.mem ⊨ (chainParamsMergeSpec A).pre x_cp s ∗ (F_ext ∗ R') := by
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
  · dsimp only [chainParamsMergeSpec, x_cp] at hpost
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
        herr sm n m' hcp hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne hn (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
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
        hok sm m' rest hcp hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, ?_⟩)⟩
    intro hm'
    dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, chainParamsMergeSpec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · dsimp only [chainParamsMergeSpec] at hpost
    exact (allowPanic_not_exited hpost).elim
  · exact False.elim (not_satisfies_false_sepConj hpost)

end CryptoVerification.SpqrV1.Top.DecodeState
