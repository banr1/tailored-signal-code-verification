/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Outer Loop, Jump-Table Dispatch, and `skip_field` Arm for `V1State::merge` (`0x4e7e8`)

Proves the epilogue/error exits, shared loop latch (`+2700`), key decode (`+216..+268`),
11-way jump-table dispatch (`+268..+296`), `skip_field` arm (`+192..+212`), and outer loop
induction for `V1State::merge` (Block `298`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Auth hiding bv64_sub_zero bv64_add_zero
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open ChunkedMerge

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
  optProtoInnerStateJumpTableAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero v1StateMerge_fnOff

/-- Uniform step contract for tag arm `k` (`1 ≤ k ≤ 11`) at entry offset `entryOff`. -/
abbrev V1StateTagStepHyp (img : Obj.Image) (b : BitVec 64) (A : RustAlloc)
    (H : String → Option (State → State)) (k : Nat) (entryOff : BitVec 64) : Prop :=
  ∀ {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat},
    V1StateTagEntryHyp img b H s0 x m rest iwt limit s →
    s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + entryOff →
    V1StateTagCont img b A H s0 x R k m rest iwt limit →
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0)

/-! ## 1. Stack Frame Splits at `s0.sp - 576#64` (`SP + 240`) for `DecodeError::{from,push}` -/

theorem v1Loop_memRegion_720_split_err1 (sp : BitVec 64) :
    memRegion (sp - 816#64) 720 =
      (∃∗ v0 : BitVec 64,
        memRegion (sp - 816#64) 240 ∗
        ((sp - 576#64) ↦₆₄ v0) ∗
        memRegion (sp - 568#64) 40 ∗
        memRegion (sp - 528#64) 432) := by
  have h1 := memRegion_split' (b := sp - 816#64) (b' := sp - 576#64) (n := 240) (k := 480) (N := 720) rfl (by bv_omega) (by decide)
  have h2 := memRegion_split' (b := sp - 576#64) (b' := sp - 568#64) (n := 8) (k := 472) (N := 480) rfl (by bv_omega) (by decide)
  have h3 := memRegion_split' (b := sp - 568#64) (b' := sp - 528#64) (n := 40) (k := 432) (N := 472) rfl (by bv_omega) (by decide)
  rw [h1, h2, h3, Prost.memRegion_eight (sp - 576#64), sepExists_sepConj_left, sepExists_sepConj_right]

theorem v1Loop_memRegion_720_split_err2 (sp : BitVec 64) :
    memRegion (sp - 816#64) 720 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        memRegion (sp - 816#64) 240 ∗
        ((sp - 576#64) ↦₆₄ v0) ∗
        ((sp - 568#64) ↦₆₄ v1) ∗
        memRegion (sp - 560#64) 32 ∗
        memRegion (sp - 528#64) 432) := by
  rw [v1Loop_memRegion_720_split_err1 sp]
  congr 1; funext v0
  have h := memRegion_split' (b := sp - 568#64) (b' := sp - 560#64) (n := 8) (k := 32) (N := 40) rfl (by bv_omega) (by decide)
  rw [h, Prost.memRegion_eight (sp - 568#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem v1Loop_err2_entails_memRegion40 (sp v1 : BitVec 64) :
    ((sp - 568#64) ↦₆₄ v1) ∗ memRegion (sp - 560#64) 32 ⊢ memRegion (sp - 568#64) 40 := by
  have h := memRegion_split' (b := sp - 568#64) (b' := sp - 560#64) (n := 8) (k := 32) (N := 40) rfl (by bv_omega) (by decide)
  rw [h, Prost.memRegion_eight (sp - 568#64), sepExists_sepConj_left]
  exact Entails.sepExists_intro (P := fun x => ((sp - 568#64) ↦₆₄ x) ∗ memRegion (sp - 560#64) 32) v1

theorem v1Loop_err1_join_720 (sp v0 : BitVec 64) :
    memRegion (sp - 816#64) 240 ∗
      ((sp - 576#64) ↦₆₄ v0) ∗
      memRegion (sp - 568#64) 40 ∗
      memRegion (sp - 528#64) 432 ⊢
    memRegion (sp - 816#64) 720 := by
  rw [v1Loop_memRegion_720_split_err1 sp]
  exact Entails.sepExists_intro
    (P := fun x => memRegion (sp - 816#64) 240 ∗ ((sp - 576#64) ↦₆₄ x) ∗ memRegion (sp - 568#64) 40 ∗ memRegion (sp - 528#64) 432) v0

theorem v1Loop_err48_join_720 (sp : BitVec 64) :
    memRegion (sp - 816#64) 240 ∗
      memRegion (sp - 576#64) 48 ∗
      memRegion (sp - 528#64) 432 ⊢
    memRegion (sp - 816#64) 720 := by
  have h1 := memRegion_split' (b := sp - 816#64) (b' := sp - 576#64) (n := 240) (k := 480) (N := 720) rfl (by bv_omega) (by decide)
  have h2 := memRegion_split' (b := sp - 576#64) (b' := sp - 528#64) (n := 48) (k := 432) (N := 480) rfl (by bv_omega) (by decide)
  rw [h1, h2]
  exact Entails.refl _

/-! ## 2. Shared Epilogue Return (`+128..+160`), `DecodeError::from` Exit (`+112..+128`), and `DecodeError::push` Exit (`+3376..+3416`) -/

set_option synthInstance.maxSize 512

theorem decodeErrorWith_le4_intro (A : RustAlloc) (e : BitVec 64) {n : Nat} (hn : n ≤ 4) :
    decodeErrorAtStackLen A e n ⊢ ∃∗ k : Nat, ⌜k ≤ 4⌝ ∗ decodeErrorAtStackLen A e k :=
  Entails.trans (Entails.pure_right hn (Entails.refl _))
    (Entails.sepExists_right n (Entails.refl _))

/-- Epilogue return at `+128` (`0x4e868`) on error (`x1 = err ≠ 0#64`, `n_err ≤ 4`). -/
theorem v1Loop_err_ret_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State} {err : BitVec 64} {n_err : Nat}
    (hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hn : n_err ≤ 4) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx1 : s.readReg64 (Reg.gpr 1#5) = err) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  rcases htr with ⟨htr, hvregs⟩
  v1StateMerge_fetches b H 128 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_ret
  unfold WppPost v1StateMergeSpec
  (conv => arg 4; simp only [hnone, v1StateErrFrame, v1StateSavedRegsAt, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1])
  apply SepWP.exists_elim; intro is'
  wp_steps
  apply SepWP.fold (decodeErrorWith_le4_intro A err hn) (by sep_focus)
  apply SepWP.fold (Entails.sepExists_intro (P := fun is'' => optProtoInnerStateAt A x.msgPtr is'') is') (by sep_focus)
  apply SepWP.fold (stackAt_v1StateMerge_epilogue s0.sp s0) (by unfold v1StateSavedRegsAt; sep_focus)
  wp_done

/-- Epilogue return at `+128` (`0x4e868`) on success (`x1 = 0#64`). -/
theorem v1Loop_ok_ret_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State} {m' : V1State} {rest : List (BitVec 8)}
    (hsome : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = some (m', rest))
    (hbound : OptInnerStatePolyBound rest.length m'.innerState) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx1 : s.readReg64 (Reg.gpr 1#5) = 0#64) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  rcases htr with ⟨htr, hvregs⟩
  v1StateMerge_fetches b H 128 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_ret
  unfold WppPost v1StateMergeSpec
  (conv => arg 4; simp only [hsome, v1StateLoopPre, v1StateSavedRegsAt, sepConj_assoc, arm64_norm, htr, hsp, hx1, hbound])
  wp_steps
  apply SepWP.fold (stackAt_v1StateMerge_epilogue s0.sp s0) (by unfold v1StateSavedRegsAt; sep_focus)
  wp_done

/-- Shared exit at `+112` (`0x4e858`): stores `X8 = w` (`KindNoHeap w`) at `[SP, #240]` (`s0.sp - 576#64`),
calls `DecodeError::from`, and returns via `v1Loop_err_ret_exit`. -/
theorem v1Loop_from_err_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffc5b8#64) (decodeErrorFromSpec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx8 : s.readReg64 (Reg.gpr 8#5) = w) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  have herr_ret := @v1Loop_err_ret_exit b A H x R s0
  v1StateMerge_fetches b H 112 16
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 0xffffffffffffc5b8#64)
  (conv => arg 4; rw [v1StateBelow_decodeError (s0.sp - 816#64), v1Loop_memRegion_720_split_err1 s0.sp, v1StateErrFrame]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, hx8])
  apply SepWP.exists_elim; intro is'
  apply SepWP.exists_elim; intro v240
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 576#64, w))
    (ret_pc := entry + 124#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp, hx8]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcm hrunm hspm
  apply SepWPp.of_sepWP (mid := entry + 128#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp])
  apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
  replace htrm : sm.v1TraceEq s := ⟨htrm, by simpa only [arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.2.2⟩
  apply SepWP.fold (v1StateBelow_decodeError_entails (s0.sp - 816#64)) (by sep_focus)
  apply SepWP.fold (v1Loop_err48_join_720 s0.sp) (by sep_focus)
  apply SepWP.fold (Entails.sepExists_intro (P := fun is'' => optProtoInnerStateAt A x.msgPtr is'') is') (by sep_focus)
  wp_steps; wp_reach
  apply SepWPp.weaken_pre
    (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
      memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
    (by dsimp only [v1StateErrFrame]; sep_entail)
  exact herr_ret hnone (by decide : 0 ≤ 4) hve_ne hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])

/-- Shared exit at `+3376` (`0x4f518`): stores `X21 = err` at `[SP, #240]` (`s0.sp - 576#64`),
calls `DecodeError::push`, reloads `X1 = err`, and jumps to `+128`. -/
theorem v1Loop_push_err_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffc2c0#64) (decodeErrorPushSpec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State} {err : BitVec 64} {n_err : Nat}
    (hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hn : n_err ≤ 3) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 3376#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx21 : s.readReg64 (Reg.gpr 21#5) = err) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  subst hx21
  have herr_ret := @v1Loop_err_ret_exit b A H x R s0
  v1StateMerge_fetches b H 3376 44
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 0xffffffffffffc2c0#64)
  (conv => arg 4; rw [v1StateBelow_decodeError (s0.sp - 816#64), v1Loop_memRegion_720_split_err1 s0.sp, v1StateErrFrame]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro is'
  apply SepWP.exists_elim; intro v240
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 576#64, s.readReg64 (Reg.gpr 21#5), n_err))
    (ret_pc := entry + 3412#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp]; rfl)
    (by omega : n_err < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcm hrunm hspm
  apply SepWPp.of_sepWP (mid := entry + 128#64)
  (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp])
  apply SepWP.pure_elim; intro htrm
  replace htrm : sm.v1TraceEq s := ⟨htrm, by simpa only [arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.2.2⟩
  apply SepWP.fold (v1StateBelow_decodeError_entails (s0.sp - 816#64)) (by sep_focus)
  apply SepWP.fold (Entails.sepExists_intro (P := fun is'' => optProtoInnerStateAt A x.msgPtr is'') is') (by sep_focus)
  wp_steps
  apply SepWP.fold (v1Loop_err1_join_720 s0.sp (s.readReg64 (Reg.gpr 21#5))) (by sep_focus)
  wp_reach
  apply SepWPp.weaken_pre
    (P' := decodeErrorAtStackLen A (s.readReg64 (Reg.gpr 21#5)) (n_err + 1) ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
      memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
    (by dsimp only [v1StateErrFrame]; sep_entail)
  exact herr_ret hnone (by omega : n_err + 1 ≤ 4) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])

/-- Constructs `V1StateTagCont` at the shared loop latch `+2700` (`0x4f274`) from the loop-header continuation at `+216` (`0x4e8c0`). -/
theorem v1Loop_latch_cont {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffc2c0#64) (decodeErrorPushSpec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 : State} {k : Nat} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hnone_of_field_none :
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = none →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont_loop : ∀ (m' : V1State) (rest' : List (BitVec 8)) (s' : State),
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = some (m', rest') →
      OptInnerStatePolyBound rest'.length m'.innerState →
      rest'.length ≤ rest.length →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      V1StateLoopRegs b s0 x limit s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest')
        (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0)) :
    V1StateTagCont img b A H s0 x R k m rest iwt limit where
  onOk := by
    intro m' rest' s' hfield hbound hrest'_le hpc hrun hsp htr hx21 hregs hinv
    rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
    v1StateMerge_fetches b H 2700 12
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry; examples_hide_fetches
    apply SepWPp.of_sepWP_img (mid := entry + 216#64) hinv
    wp_steps; wp_reach; intro hinv'
    exact hcont_loop m' rest' _ hfield hbound hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx22],
       by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
       by simp only [arm64_norm, hx29]⟩ hinv'
  onErr := by
    intro hfield s' err n_err hpc hrun hsp htr hx21 herr hn
    have hnone := hnone_of_field_none hfield
    have hcbnz : (err == 0#64) = false := beq_eq_false_iff_ne.mpr herr
    have hpush := @v1Loop_push_err_exit b A H hPushCall x R s0
    v1StateMerge_fetches b H 2700 4
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry; examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 3376#64)
    wp_steps; wp_reach
    exact hpush hnone hn herr hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx21])

/-! ## 3. Loop Header (`+216..+296`), `skip_field` Arm (`+192..+212`), and 11-Way Jump-Table Dispatch -/

theorem v1Loop_discr_tail_entails_cap (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (is : Option V1State.InnerState) (d : BitVec 64) (hd : InnerStateDiscrFull bsLen is d) :
    (a ↦₆₄ d) ∗ optProtoInnerStateCapTailAt A a bsLen is d ⊢
      optProtoInnerStateCapAt A a bsLen is :=
  discr_entails_optProtoInnerStateCapAt A a bsLen is d (innerStateDiscrFull_imp_discr hd)

private theorem setWidth8_ofNat64_wt_v1 (wt : WireType) :
    (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat := by
  cases wt <;> decide

private theorem setWidth8_zext64_trunc32_ofNat64_wt_v1 (wt : WireType) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 wt.toNat))) =
      BitVec.ofNat 8 wt.toNat := by
  cases wt <;> decide

/-- Loop exit at `+216` (`0x4e8c0`) when `cur.length ≤ limit`. -/
theorem v1Loop_le_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffc5b8#64) (decodeErrorFromSpec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : limit < 2 ^ 63) (hbound : OptInnerStatePolyBound cur.length m.innerState)
    (hnone_of_lt : cur.length < limit →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hsome_of_eq : cur.length = limit →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = some (m, cur))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegs b s0 x limit s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  rcases hregs with ⟨_hx19, _hx20, _hx22, _hx23, _hx24, _hx25, hx26, _hx27, hx28, _hx29⟩
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hsome := hsome_of_eq heq_lim
    have hok_ret := fun {s' : State} => @v1Loop_ok_ret_exit b A H x R s0 s' m cur
    v1StateMerge_fetches b H 216 12; v1StateMerge_fetches b H 3304 12
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry; examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 128#64)
    (conv => arg 4; rw [v1StateLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' := v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (by dsimp only [v1StateLoopPre, sliceCursorAfter]; sep_entail)
    exact hok_ret hsome hbound hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm])
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hfrom_err := @v1Loop_from_err_exit b A H hFromCall x R s0
    v1StateMerge_fetches b H 216 12; v1StateMerge_fetches b H 3304 4; v1StateMerge_fetches b H 3360 16
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry; examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 112#64)
    (conv => arg 4; rw [v1StateLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr cur.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre
      (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [v1StateErrFrame]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm])

/-- Loop header key decode at `+216..+268` (`0x4e8c0..0x4e8f4`) when `¬ cur.length ≤ limit`. -/
theorem v1Loop_decode_key_step {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffc5b8#64) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffece4#64) (decodeVarint2Spec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_loop_none :
      mergeLoopBin V1State.mergeField (cur.length - limit) m cur limit 99 = none →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 268#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = key →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8) →
      V1StateLoopRegs b s0 x limit s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegs b s0 x limit s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  revert hinv; change SepWPpIn img (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
    (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
    (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0)
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have herr_ret := @v1Loop_err_ret_exit b A H x R s0
  have hfrom_err := @v1Loop_from_err_exit b A H hFromCall x R s0
  v1StateMerge_fetches b H 216 52; v1StateMerge_fetches b H 3316 16
  v1StateMerge_fetches b H 3332 12; v1StateMerge_fetches b H 3344 16
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffece4#64)
  (conv => arg 4; rw [v1StateLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, v1StateBelow_decodeVarint2 (s0.sp - 816#64)]; simp only [sepConj_assoc])
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 236#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hx29_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_loop_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_v1State_mergeField hgt_lim hd)
    intro _hinv_m
    apply SepWPp.of_sepWP (mid := entry + 128#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr cur.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre
      (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [v1StateErrFrame]; sep_entail)
    exact herr_ret hnone (by decide : 0 ≤ 4) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_loop_none (mergeLoopBin_of_key_ge protoPrefixStep_v1State_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge
      intro _hinv_m
      apply SepWPp.of_sepWP (mid := entry + 112#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
      apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, v1Loop_memRegion_720_split_err2 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (v1Loop_err2_entails_memRegion40 s0.sp key) (by sep_focus)
      apply SepWP.fold (v1Loop_err1_join_720 s0.sp v_err0) (by sep_focus)
      apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr cur.length m.innerState)
        (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
      wp_reach
      apply SepWPp.weaken_pre
        (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
          v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [v1StateErrFrame]; sep_entail)
      exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_loop_none (mergeLoopBin_of_wt_none protoPrefixStep_v1State_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        intro _hinv_m
        apply SepWPp.of_sepWP (mid := entry + 112#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
        apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, v1Loop_memRegion_720_split_err2 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (v1Loop_err2_entails_memRegion40 s0.sp (key &&& 7#64)) (by sep_focus)
        apply SepWP.fold (v1Loop_err1_join_720 s0.sp v_err0) (by sep_focus)
        apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr cur.length m.innerState)
          (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
        wp_reach
        apply SepWPp.weaken_pre
          (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
            v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [v1StateErrFrame]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_loop_none (mergeLoopBin_of_tag_zero protoPrefixStep_v1State_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          intro _hinv_m
          apply SepWPp.of_sepWP (mid := entry + 112#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
          apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr cur.length m.innerState)
            (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt]; simp only [sepConj_assoc])
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach
          apply SepWPp.weaken_pre
            (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
              v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
            (by dsimp only [v1StateErrFrame]; sep_entail)
          exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpIn.of_sepWP (mid := entry + 268#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
          apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (optProtoInnerStateCapAt_mono A x.msgPtr m.innerState hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach
          intro hinv'
          apply SepWPp.weaken_pre (P' := v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (by dsimp only [v1StateLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1])
            (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m], by simp only [arm64_norm, hx22_m],
             by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
             by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
             by simp only [arm64_norm, hx29_m]⟩ hinv'

/-- Unknown-tag `skip_field` arm at `+192..+212` (`0x4e8a8..0x4e8bc`). -/
theorem v1Loop_skip_step {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd38c#64) (skipField3Spec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_skip : skipField (2 * rest.length + 2) 99 tag iwt rest = none →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 99 tag iwt rest = some rest' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      V1StateLoopRegs b s0 x limit s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx8 : (s.readReg64 (Reg.gpr 8#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hregs : V1StateLoopRegs b s0 x limit s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  revert hinv; change SepWPpIn img (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
    (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
    (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0)
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr_ret := @v1Loop_err_ret_exit b A H x R s0
  v1StateMerge_fetches b H 192 24
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffd38c#64)
  (conv => arg 4; rw [v1StateLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, v1StateBelow_skipField99 (s0.sp - 816#64)]; simp only [sepConj_assoc])
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨iwt, tag, 99, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 208#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx8, hx19, setWidth8_ofNat64_wt_v1]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 99 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hx29_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 99 tag iwt rest with
  | none =>
    have hnone := hnone_of_skip hsf
    intro _hinv_m
    apply SepWPp.of_sepWP (mid := entry + 128#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (v1StateBelow_skipField99_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre
      (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [v1StateErrFrame]; sep_entail)
    exact herr_ret hnone (by decide : 0 ≤ 4) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpIn.of_sepWP (mid := entry + 216#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (v1StateBelow_skipField99_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_mono A x.msgPtr m.innerState hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    intro hinv'
    apply SepWPp.weaken_pre (P' := v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (by dsimp only [v1StateLoopPre]; sep_entail)
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m], by simp only [arm64_norm, hx22_m],
       by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hx29_m]⟩ hinv'

private theorem key_tag_gt_11 {key : BitVec 64} (h : 11 < key.toNat / 8) :
    (BitVec.ule 96#64 key) = true ∧ (BitVec.ult key 96#64) = false := by
  have hge : 96 ≤ key.toNat := by omega
  simp only [BitVec.ule, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq, decide_eq_false_iff_not]
  change 96 ≤ key.toNat ∧ ¬ key.toNat < 96
  omega

private theorem key_tag_le_11 {key : BitVec 64} (h : key.toNat / 8 ≤ 11) :
    (BitVec.ule 96#64 key) = false ∧ (BitVec.ult key 96#64) = true := by
  have hlt : key.toNat < 96 := by omega
  simp only [BitVec.ule, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq, decide_eq_false_iff_not]
  change ¬ 96 ≤ key.toNat ∧ key.toNat < 96
  omega

theorem v1Loop_jump_arm {img : Obj.Image} {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {key : BitVec 64} {limit : Nat}
    {k : Nat} {off : BitVec 64}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (_hbs_lt : x.bs.length < 2 ^ 63) (hb_align : (b &&& 0xfff#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (hbound : OptInnerStatePolyBound rest.length m.innerState)
    (hk_le : key.toNat / 8 ≤ 11)
    (htag_k : key.toNat / 8 = k)
    (hk_cases : k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
      k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
      k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
      k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64)
    (harm : ∀ s' : State, V1StateTagEntryHyp img b H s0 x m rest iwt limit s' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + off →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (_hx1 : s.readReg64 (Reg.gpr 1#5) = key)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8))
    (hregs : V1StateLoopRegs b s0 x limit s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  revert hinv; change SepWPpIn img (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
    (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
    (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0)
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  obtain ⟨hule96, hult96⟩ := key_tag_le_11 hk_le
  rw [htag_k] at hx8
  v1StateMerge_fetches b H 268 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + off)
  (conv => arg 4; rw [v1StateLoopPre, v1StateJumpTablesAt, v1StateMergeJumpTableExpanded]; simp only [sepConj_assoc])
  apply SepWP.fold (optProtoInnerStateCapAt_entails_discrFull A x.msgPtr rest.length m.innerState) (by sep_focus)
  (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro d; apply SepWP.pure_elim; intro hd
  rcases hk_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> {
    wp_steps
    apply SepWP.fold (v1Loop_discr_tail_entails_cap A x.msgPtr rest.length m.innerState d hd) (by sep_focus)
    wp_reach
    intro hinv'
    apply SepWPp.weaken_pre (P' := v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (by dsimp only [v1StateLoopPre, v1StateJumpTablesAt, v1StateMergeJumpTableExpanded]; sep_entail)
    exact harm _ ⟨hsp_align, beq_iff_eq.mp hb_align, hrest_le, hrest_lt, hrest_suf, hbound,
      by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp], by simp only [arm64_norm, htr],
      by simp only [arm64_norm, hx0]; cases iwt <;> rfl, by simp only [arm64_norm]; exact hd,
      ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx22],
       by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
       by simp only [arm64_norm, hx29]⟩, hinv'⟩ (by simp only [arm64_norm])
  }

theorem v1Loop_mergeField_suffix {m m' : V1State} {k : Nat} {off : BitVec 64} {iwt : WireType} {rest rest' : List (BitVec 8)}
    (hk_cases : k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
      k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
      k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
      k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64)
    (h : (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = some (m', rest')) :
    rest'.length ≤ rest.length ∧ IsDropSuffix rest rest' := by
  rcases hk_cases with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
    ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> {
    first
      | rw [v1State_mergeField_tag1, Option.map_eq_some_iff] at h
      | rw [v1State_mergeField_tag2, Option.map_eq_some_iff] at h
      | rw [v1State_mergeField_tag3, Option.map_eq_some_iff] at h
      | rw [v1State_mergeField_tag4, Option.map_eq_some_iff] at h
      | rw [v1State_mergeField_tag5, Option.map_eq_some_iff] at h
      | rw [v1State_mergeField_tag6, Option.map_eq_some_iff] at h
      | rw [v1State_mergeField_tag7, Option.map_eq_some_iff] at h
      | rw [v1State_mergeField_tag8, Option.map_eq_some_iff] at h
      | rw [v1State_mergeField_tag9, Option.map_eq_some_iff] at h
      | rw [v1State_mergeField_tag10, Option.map_eq_some_iff] at h
      | rw [v1State_mergeField_tag11, Option.map_eq_some_iff] at h
    rcases h with ⟨⟨v', r⟩, hmsg, heq⟩
    injection heq with _ hr; subst hr
    exact proto_mergeMessage_suffix hmsg
  }

theorem v1Loop_dispatch_known_tag {img : Obj.Image} {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffc2c0#64) (decodeErrorPushSpec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {key : BitVec 64} {limit : Nat}
    {k : Nat} {off : BitVec 64}
    (htag : V1StateTagStepHyp img b A H k off)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hb_align : (b &&& 0xfff#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (hbound : OptInnerStatePolyBound rest.length m.innerState)
    (hk_le : key.toNat / 8 ≤ 11) (htag_k : key.toNat / 8 = k)
    (hk_cases : k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
      k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
      k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
      k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64)
    (hnone_of_field_none :
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = none →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont_loop : ∀ (m' : V1State) (rest' : List (BitVec 8)) (s' : State),
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = some (m', rest') →
      OptInnerStatePolyBound rest'.length m'.innerState →
      rest'.length ≤ rest.length →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      V1StateLoopRegs b s0 x limit s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest')
        (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = key)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8))
    (hregs : V1StateLoopRegs b s0 x limit s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) :=
  v1Loop_jump_arm hsp_align hbs_lt hb_align hrest_le hrest_lt hrest_suf hbound hk_le htag_k hk_cases
    (fun _ hentry hpc' => htag hentry hpc' (v1Loop_latch_cont hPushCall hsp_align hnone_of_field_none hcont_loop))
    hpc hrun hsp htr hx0 hx1 hx8 hregs hinv

theorem v1Loop_dispatch_unknown_tag {img : Obj.Image} {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd38c#64) (skipField3Spec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {key : BitVec 64} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : key.toNat / 8 < 2 ^ 32)
    (hk_gt : 11 < key.toNat / 8)
    (hnone_of_skip : skipField (2 * rest.length + 2) 99 (key.toNat / 8) iwt rest = none →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 99 (key.toNat / 8) iwt rest = some rest' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      V1StateLoopRegs b s0 x limit s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = key)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8))
    (hregs : V1StateLoopRegs b s0 x limit s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  revert hinv; change SepWPpIn img (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
    (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
    (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0)
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  obtain ⟨hule96, hult96⟩ := key_tag_gt_11 hk_gt
  have hskip := @v1Loop_skip_step img b A H hSkipCall x R s0
  v1StateMerge_fetches b H 268 8
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 192#64)
  wp_steps; wp_reach
  intro hinv'
  exact hskip hsp_align hrest_le hrest_lt hrest_suf htag_lt hnone_of_skip hcont
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx8, sf_truncate32_ofNat64])
    ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx22],
     by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
     by simp only [arm64_norm, hx29]⟩ hinv'

/-- Main outer loop induction at `+216` (`0x4e8c0`) for `V1State.mergeField`. -/
theorem v1Loop_loop_ok {img : Obj.Image} {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffc5b8#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffc2c0#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffece4#64) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd38c#64) (skipField3Spec A))
    (htag1 : V1StateTagStepHyp img b A H 1 300#64)
    (htag2 : V1StateTagStepHyp img b A H 2 564#64)
    (htag3 : V1StateTagStepHyp img b A H 3 428#64)
    (htag4 : V1StateTagStepHyp img b A H 4 476#64)
    (htag5 : V1StateTagStepHyp img b A H 5 336#64)
    (htag6 : V1StateTagStepHyp img b A H 6 604#64)
    (htag7 : V1StateTagStepHyp img b A H 7 652#64)
    (htag8 : V1StateTagStepHyp img b A H 8 516#64)
    (htag9 : V1StateTagStepHyp img b A H 9 748#64)
    (htag10 : V1StateTagStepHyp img b A H 10 380#64)
    (htag11 : V1StateTagStepHyp img b A H 11 700#64)
    {x : V1StateMergeGhost} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hb_align : (b &&& 0xfff#64 == 0#64) = true)
    (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      OptInnerStatePolyBound cur.length m.innerState →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        (mergeLoopBin V1State.mergeField (cur.length - limit) m cur limit 99).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 216#64 →
      s.status = .Running → s.sp = s0.sp - 816#64 → s.v1TraceEq s0 →
      V1StateLoopRegs b s0 x limit s → ImgCallInv img s →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
        (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hbound hres hpc hrun hsp htr hregs _hinv
    exact v1Loop_le_exit hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt hbound
      (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
      (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
      hpc hrun hsp htr hregs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hbound hres hpc hrun hsp htr hregs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact v1Loop_le_exit hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt hbound
        (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
        (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
        hpc hrun hsp htr hregs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine v1Loop_decode_key_step hFromCall hVarintCall hle_lim hsp_align hcur_le hcur_lt hcur_suf
        (fun hml => by rw [hres, hml]; rfl) ?_ hpc hrun hsp htr hregs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx8' hregs' hinv'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hbound_rest : OptInnerStatePolyBound rest.length m.innerState := optInnerStatePolyBound_mono hbound hrest_le_cur
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := m) (depth' := 99) protoPrefixStep_v1State_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases hk_le : key.toNat / 8 ≤ 11
      · have hknown : ∀ (k : Nat) (off : BitVec 64),
            V1StateTagStepHyp img b A H k off → key.toNat / 8 = k →
            (k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
             k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
             k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
             k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64) →
            SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
              (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
              (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
          intro k off htag htag_k hk_cases
          refine v1Loop_dispatch_known_tag hPushCall htag hsp_align hbs_lt hb_align hrest_le hrest_lt hrest_suf
            hbound_rest hk_le htag_k hk_cases
            (fun hfn => by rw [hres, hstep, htag_k, hfn]; rfl) ?_ hpc' hrun' hsp' htr' hx0' hx1' hx8' hregs' hinv'
          intro m' rest' s'' hfsome hbound' hr'_le hpc'' hrun'' hsp'' htr'' hregs'' hinv''
          obtain ⟨_, hr'_suf⟩ := v1Loop_mergeField_suffix hk_cases hfsome
          exact ih m' rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le hr'_suf) hbound'
            (by rw [hres, hstep, htag_k, hfsome]) hpc'' hrun'' hsp'' htr'' hregs'' hinv''
        have hk_cases11 : key.toNat / 8 = 1 ∨ key.toNat / 8 = 2 ∨ key.toNat / 8 = 3 ∨
            key.toNat / 8 = 4 ∨ key.toNat / 8 = 5 ∨ key.toNat / 8 = 6 ∨ key.toNat / 8 = 7 ∨
            key.toNat / 8 = 8 ∨ key.toNat / 8 = 9 ∨ key.toNat / 8 = 10 ∨ key.toNat / 8 = 11 := by omega
        rcases hk_cases11 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
        · exact hknown 1 300#64 htag1 h1 (by decide)
        · exact hknown 2 564#64 htag2 h2 (by decide)
        · exact hknown 3 428#64 htag3 h3 (by decide)
        · exact hknown 4 476#64 htag4 h4 (by decide)
        · exact hknown 5 336#64 htag5 h5 (by decide)
        · exact hknown 6 604#64 htag6 h6 (by decide)
        · exact hknown 7 652#64 htag7 h7 (by decide)
        · exact hknown 8 516#64 htag8 h8 (by decide)
        · exact hknown 9 748#64 htag9 h9 (by decide)
        · exact hknown 10 380#64 htag10 h10 (by decide)
        · exact hknown 11 700#64 htag11 h11 (by decide)
      · have hk_gt : 11 < key.toNat / 8 := by omega
        rw [v1State_mergeField_other m iwt rest 99 htag_lt (Or.inr hk_gt)] at hstep
        refine v1Loop_dispatch_unknown_tag hSkipCall hsp_align hrest_le hrest_lt hrest_suf htag_lt hk_gt
          (fun hsf_none => by rw [hres, hstep, hsf_none]; rfl) ?_ hpc' hrun' hsp' htr' hx0' hx1' hx8' hregs' hinv'
        intro rest' s'' hsf_some hpc'' hrun'' hsp'' htr'' hregs'' hinv''
        have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some
        exact ih m rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
          (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some))
          (optInnerStatePolyBound_mono hbound_rest hr'_le)
          (by rw [hres, hstep, hsf_some]; rfl) hpc'' hrun'' hsp'' htr'' hregs'' hinv''

section Placed

open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

attribute [local irreducible] optProtoInnerStateJumpTablePlacedAt

/-- Uniform step contract for tag arm `k` (`1 ≤ k ≤ 11`) at entry offset `entryOff`. -/
abbrev V1StateTagStepHypPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (k : Nat) (entryOff : BitVec 64) : Prop :=
  ∀ {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat},
    V1StateTagEntryHypPlaced H s0 x m rest iwt limit s →
    s.pc = (blkPl_298).base + entryOff →
    V1StateTagContPlaced A H s0 x R k m rest iwt limit →
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0)



/-- Epilogue return at `+128` (`0x4e868`) on error (`x1 = err ≠ 0#64`, `n_err ≤ 4`). -/
theorem v1Loop_err_ret_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State} {err : BitVec 64} {n_err : Nat}
    (hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hn : n_err ≤ 4) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx1 : s.readReg64 (Reg.gpr 1#5) = err) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  rcases htr with ⟨htr, hvregs⟩
  apply SepWPp.of_sepWP_ret
  unfold WppPost v1StateMergePlacedSpec
  (conv => arg 4; simp only [hnone, v1StateErrFramePlaced, v1StateSavedRegsAt, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1])
  apply SepWP.exists_elim; intro is'
  wp_steps
  apply SepWP.fold (decodeErrorWith_le4_intro A err hn) (by sep_focus)
  apply SepWP.fold (Entails.sepExists_intro (P := fun is'' => optProtoInnerStateAt A x.msgPtr is'') is') (by sep_focus)
  apply SepWP.fold (stackAt_v1StateMerge_epilogue s0.sp s0) (by unfold v1StateSavedRegsAt; sep_focus)
  wp_done

/-- Epilogue return at `+128` (`0x4e868`) on success (`x1 = 0#64`). -/
theorem v1Loop_ok_ret_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State} {m' : V1State} {rest : List (BitVec 8)}
    (hsome : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = some (m', rest))
    (hbound : OptInnerStatePolyBound rest.length m'.innerState) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx1 : s.readReg64 (Reg.gpr 1#5) = 0#64) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  rcases htr with ⟨htr, hvregs⟩
  apply SepWPp.of_sepWP_ret
  unfold WppPost v1StateMergePlacedSpec
  (conv => arg 4; simp only [hsome, v1StateLoopPrePlaced, v1StateSavedRegsAt, sepConj_assoc, arm64_norm, htr, hsp, hx1, hbound])
  wp_steps
  apply SepWP.fold (stackAt_v1StateMerge_epilogue s0.sp s0) (by unfold v1StateSavedRegsAt; sep_focus)
  wp_done

/-- Shared exit at `+112` (`0x4e858`): stores `X8 = w` (`KindNoHeap w`) at `[SP, #240]` (`s0.sp - 576#64`),
calls `DecodeError::from`, and returns via `v1Loop_err_ret_exit_placed`. -/
theorem v1Loop_from_err_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx8 : s.readReg64 (Reg.gpr 8#5) = w) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  have herr_ret := @v1Loop_err_ret_exit_placed _ A H x R s0
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  (conv => arg 4; rw [v1StateBelow_decodeError (s0.sp - 816#64), v1Loop_memRegion_720_split_err1 s0.sp, v1StateErrFramePlaced]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, hx8])
  apply SepWP.exists_elim; intro is'
  apply SepWP.exists_elim; intro v240
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 576#64, w))
    (ret_pc := (blkPl_298).base + 124#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp, hx8]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcm hrunm hspm
  apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp])
  apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
  replace htrm : sm.v1TraceEq s := ⟨htrm, by simpa only [arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.2.2⟩
  apply SepWP.fold (v1StateBelow_decodeError_entails (s0.sp - 816#64)) (by sep_focus)
  apply SepWP.fold (v1Loop_err48_join_720 s0.sp) (by sep_focus)
  apply SepWP.fold (Entails.sepExists_intro (P := fun is'' => optProtoInnerStateAt A x.msgPtr is'') is') (by sep_focus)
  wp_steps; wp_reach
  apply SepWPp.weaken_pre
    (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
      memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
    (by dsimp only [v1StateErrFramePlaced]; sep_entail)
  exact herr_ret hnone (by decide : 0 ≤ 4) hve_ne hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])

/-- Shared exit at `+3376` (`0x4f518`): stores `X21 = err` at `[SP, #240]` (`s0.sp - 576#64`),
calls `DecodeError::push`, reloads `X1 = err`, and jumps to `+128`. -/
theorem v1Loop_push_err_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State} {err : BitVec 64} {n_err : Nat}
    (hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hn : n_err ≤ 3) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 3376#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx21 : s.readReg64 (Reg.gpr 21#5) = err) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  subst hx21
  have herr_ret := @v1Loop_err_ret_exit_placed _ A H x R s0
  apply SepWPp.of_sepWP (mid := lsmpl.base 257)
  (conv => arg 4; rw [v1StateBelow_decodeError (s0.sp - 816#64), v1Loop_memRegion_720_split_err1 s0.sp, v1StateErrFramePlaced]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro is'
  apply SepWP.exists_elim; intro v240
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 576#64, s.readReg64 (Reg.gpr 21#5), n_err))
    (ret_pc := (blkPl_298).base + 3412#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp]; rfl)
    (by omega : n_err < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcm hrunm hspm
  apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
  (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp])
  apply SepWP.pure_elim; intro htrm
  replace htrm : sm.v1TraceEq s := ⟨htrm, by simpa only [arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.2.2⟩
  apply SepWP.fold (v1StateBelow_decodeError_entails (s0.sp - 816#64)) (by sep_focus)
  apply SepWP.fold (Entails.sepExists_intro (P := fun is'' => optProtoInnerStateAt A x.msgPtr is'') is') (by sep_focus)
  wp_steps
  apply SepWP.fold (v1Loop_err1_join_720 s0.sp (s.readReg64 (Reg.gpr 21#5))) (by sep_focus)
  wp_reach
  apply SepWPp.weaken_pre
    (P' := decodeErrorAtStackLen A (s.readReg64 (Reg.gpr 21#5)) (n_err + 1) ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
      memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
    (by dsimp only [v1StateErrFramePlaced]; sep_entail)
  exact herr_ret hnone (by omega : n_err + 1 ≤ 4) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])

/-- Constructs `V1StateTagCont` at the shared loop latch `+2700` (`0x4f274`) from the loop-header continuation at `+216` (`0x4e8c0`). -/
theorem v1Loop_latch_cont_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 : State} {k : Nat} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hnone_of_field_none :
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = none →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont_loop : ∀ (m' : V1State) (rest' : List (BitVec 8)) (s' : State),
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = some (m', rest') →
      OptInnerStatePolyBound rest'.length m'.innerState →
      rest'.length ≤ rest.length →
      s'.pc = (blkPl_298).base + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      V1StateLoopRegsPlaced s0 x limit s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest')
        (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0)) :
    V1StateTagContPlaced A H s0 x R k m rest iwt limit where
  onOk := by
    intro m' rest' s' hfield hbound hrest'_le hpc hrun hsp htr hx21 hregs hinv
    rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 216#64) hinv
    wp_steps; wp_reach; intro hinv'
    exact hcont_loop m' rest' _ hfield hbound hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx22],
       by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
       by simp only [arm64_norm, hx29]⟩ hinv'
  onErr := by
    intro hfield s' err n_err hpc hrun hsp htr hx21 herr hn
    have hnone := hnone_of_field_none hfield
    have hcbnz : (err == 0#64) = false := beq_eq_false_iff_ne.mpr herr
    have hpush := @v1Loop_push_err_exit_placed _ A H hPushCall x R s0
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 3376#64)
    wp_steps; wp_reach
    exact hpush hnone hn herr hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx21])



/-- Loop exit at `+216` (`0x4e8c0`) when `cur.length ≤ limit`. -/
theorem v1Loop_le_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : limit < 2 ^ 63) (hbound : OptInnerStatePolyBound cur.length m.innerState)
    (hnone_of_lt : cur.length < limit →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hsome_of_eq : cur.length = limit →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = some (m, cur))
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x limit s) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  rcases hregs with ⟨_hx19, _hx20, _hx22, _hx23, _hx24, _hx25, hx26, _hx27, hx28, _hx29⟩
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hsome := hsome_of_eq heq_lim
    have hok_ret := fun {s' : State} => @v1Loop_ok_ret_exit_placed _ A H x R s0 s' m cur
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
    (conv => arg 4; rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' := v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (by dsimp only [v1StateLoopPrePlaced, sliceCursorAfter]; sep_entail)
    exact hok_ret hsome hbound hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm])
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hfrom_err := @v1Loop_from_err_exit_placed _ A H hFromCall x R s0
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 112#64)
    (conv => arg 4; rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr cur.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre
      (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [v1StateErrFramePlaced]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm])

/-- Loop header key decode at `+216..+268` (`0x4e8c0..0x4e8f4`) when `¬ cur.length ≤ limit`. -/
theorem v1Loop_decode_key_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (decodeVarint2Spec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_loop_none :
      mergeLoopBin V1State.mergeField (cur.length - limit) m cur limit 99 = none →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_298).base + 268#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = key →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8) →
      V1StateLoopRegsPlaced s0 x limit s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x limit s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  revert hinv; change SepWPpLscro lsmpl ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
    (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
    (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0)
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have herr_ret := @v1Loop_err_ret_exit_placed _ A H x R s0
  have hfrom_err := @v1Loop_from_err_exit_placed _ A H hFromCall x R s0
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
  (conv => arg 4; rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, v1StateBelow_decodeVarint2 (s0.sp - 816#64)]; simp only [sepConj_assoc])
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := (blkPl_298).base + 236#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hx29_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_loop_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_v1State_mergeField hgt_lim hd)
    intro _hinv_m
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr cur.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre
      (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [v1StateErrFramePlaced]; sep_entail)
    exact herr_ret hnone (by decide : 0 ≤ 4) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_loop_none (mergeLoopBin_of_key_ge protoPrefixStep_v1State_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge
      intro _hinv_m
      apply SepWPp.of_sepWP (mid := (blkPl_298).base + 112#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
      apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, v1Loop_memRegion_720_split_err2 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (v1Loop_err2_entails_memRegion40 s0.sp key) (by sep_focus)
      apply SepWP.fold (v1Loop_err1_join_720 s0.sp v_err0) (by sep_focus)
      apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr cur.length m.innerState)
        (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
      wp_reach
      apply SepWPp.weaken_pre
        (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
          v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [v1StateErrFramePlaced]; sep_entail)
      exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_loop_none (mergeLoopBin_of_wt_none protoPrefixStep_v1State_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        intro _hinv_m
        apply SepWPp.of_sepWP (mid := (blkPl_298).base + 112#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
        apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, v1Loop_memRegion_720_split_err2 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (v1Loop_err2_entails_memRegion40 s0.sp (key &&& 7#64)) (by sep_focus)
        apply SepWP.fold (v1Loop_err1_join_720 s0.sp v_err0) (by sep_focus)
        apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr cur.length m.innerState)
          (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
        wp_reach
        apply SepWPp.weaken_pre
          (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
            v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [v1StateErrFramePlaced]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_loop_none (mergeLoopBin_of_tag_zero protoPrefixStep_v1State_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          intro _hinv_m
          apply SepWPp.of_sepWP (mid := (blkPl_298).base + 112#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
          apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr cur.length m.innerState)
            (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt]; simp only [sepConj_assoc])
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach
          apply SepWPp.weaken_pre
            (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
              v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
            (by dsimp only [v1StateErrFramePlaced]; sep_entail)
          exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpLscro.of_sepWP (mid := (blkPl_298).base + 268#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
          apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (optProtoInnerStateCapAt_mono A x.msgPtr m.innerState hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach
          intro hinv'
          apply SepWPp.weaken_pre (P' := v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (by dsimp only [v1StateLoopPrePlaced]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1])
            (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m], by simp only [arm64_norm, hx22_m],
             by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
             by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
             by simp only [arm64_norm, hx29_m]⟩ hinv'

/-- Unknown-tag `skip_field` arm at `+192..+212` (`0x4e8a8..0x4e8bc`). -/
theorem v1Loop_skip_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263) (skipField3Spec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_skip : skipField (2 * rest.length + 2) 99 tag iwt rest = none →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 99 tag iwt rest = some rest' →
      s'.pc = (blkPl_298).base + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      V1StateLoopRegsPlaced s0 x limit s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_298).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx8 : (s.readReg64 (Reg.gpr 8#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hregs : V1StateLoopRegsPlaced s0 x limit s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  revert hinv; change SepWPpLscro lsmpl ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
    (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
    (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0)
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr_ret := @v1Loop_err_ret_exit_placed _ A H x R s0
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 263)
  (conv => arg 4; rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hrest_le hrest_suf, v1StateBelow_skipField99 (s0.sp - 816#64)]; simp only [sepConj_assoc])
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨iwt, tag, 99, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 208#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx8, hx19, setWidth8_ofNat64_wt_v1]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 99 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hx29_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 99 tag iwt rest with
  | none =>
    have hnone := hnone_of_skip hsf
    intro _hinv_m
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (v1StateBelow_skipField99_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre
      (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [v1StateErrFramePlaced]; sep_entail)
    exact herr_ret hnone (by decide : 0 ≤ 4) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpLscro.of_sepWP (mid := (blkPl_298).base + 216#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (v1StateBelow_skipField99_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_mono A x.msgPtr m.innerState hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    intro hinv'
    apply SepWPp.weaken_pre (P' := v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (by dsimp only [v1StateLoopPrePlaced]; sep_entail)
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m], by simp only [arm64_norm, hx22_m],
       by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hx29_m]⟩ hinv'


theorem v1Loop_jump_arm_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {key : BitVec 64} {limit : Nat}
    {k : Nat} {off : BitVec 64}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (_hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (hbound : OptInnerStatePolyBound rest.length m.innerState)
    (hk_le : key.toNat / 8 ≤ 11)
    (htag_k : key.toNat / 8 = k)
    (hk_cases : k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
      k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
      k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
      k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64)
    (harm : ∀ s' : State, V1StateTagEntryHypPlaced H s0 x m rest iwt limit s' →
      s'.pc = (blkPl_298).base + off →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_298).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (_hx1 : s.readReg64 (Reg.gpr 1#5) = key)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8))
    (hregs : V1StateLoopRegsPlaced s0 x limit s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  revert hinv; change SepWPpLscro lsmpl ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
    (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
    (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0)
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  obtain ⟨hule96, hult96⟩ := key_tag_le_11 hk_le
  rw [htag_k] at hx8
  apply SepWPpLscro.of_sepWP (mid := (blkPl_298).base + off)
  (conv => arg 4; rw [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, v1StateMergeJumpTablePlacedExpanded]; simp only [sepConj_assoc])
  apply SepWP.fold (optProtoInnerStateCapAt_entails_discrFull A x.msgPtr rest.length m.innerState) (by sep_focus)
  (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro d; apply SepWP.pure_elim; intro hd
  rcases hk_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> {
    wp_steps
    apply SepWP.fold (v1Loop_discr_tail_entails_cap A x.msgPtr rest.length m.innerState d hd) (by sep_focus)
    wp_reach
    intro hinv'
    apply SepWPp.weaken_pre (P' := v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, v1StateMergeJumpTablePlacedExpanded]; sep_entail)
    exact harm _ ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hbound,
      by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp], by simp only [arm64_norm, htr],
      by simp only [arm64_norm, hx0]; cases iwt <;> rfl, by simp only [arm64_norm]; exact hd,
      ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx22],
       by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
       by simp only [arm64_norm, hx29]⟩, hinv'⟩ (by simp only [arm64_norm])
  }


theorem v1Loop_dispatch_known_tag_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {key : BitVec 64} {limit : Nat}
    {k : Nat} {off : BitVec 64}
    (htag : V1StateTagStepHypPlaced A H k off)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (hbound : OptInnerStatePolyBound rest.length m.innerState)
    (hk_le : key.toNat / 8 ≤ 11) (htag_k : key.toNat / 8 = k)
    (hk_cases : k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
      k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
      k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
      k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64)
    (hnone_of_field_none :
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = none →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont_loop : ∀ (m' : V1State) (rest' : List (BitVec 8)) (s' : State),
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = some (m', rest') →
      OptInnerStatePolyBound rest'.length m'.innerState →
      rest'.length ≤ rest.length →
      s'.pc = (blkPl_298).base + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      V1StateLoopRegsPlaced s0 x limit s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest')
        (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_298).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = key)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8))
    (hregs : V1StateLoopRegsPlaced s0 x limit s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) :=
  v1Loop_jump_arm_placed hsp_align hbs_lt hrest_le hrest_lt hrest_suf hbound hk_le htag_k hk_cases
    (fun _ hentry hpc' => htag hentry hpc' (v1Loop_latch_cont_placed hPushCall hsp_align hnone_of_field_none hcont_loop))
    hpc hrun hsp htr hx0 hx1 hx8 hregs hinv

theorem v1Loop_dispatch_unknown_tag_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263) (skipField3Spec A))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {key : BitVec 64} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : key.toNat / 8 < 2 ^ 32)
    (hk_gt : 11 < key.toNat / 8)
    (hnone_of_skip : skipField (2 * rest.length + 2) 99 (key.toNat / 8) iwt rest = none →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 99 (key.toNat / 8) iwt rest = some rest' →
      s'.pc = (blkPl_298).base + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      V1StateLoopRegsPlaced s0 x limit s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_298).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = key)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8))
    (hregs : V1StateLoopRegsPlaced s0 x limit s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  revert hinv; change SepWPpLscro lsmpl ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
    (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
    (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0)
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  obtain ⟨hule96, hult96⟩ := key_tag_gt_11 hk_gt
  have hskip := @v1Loop_skip_step_placed _ A H hSkipCall x R s0
  apply SepWPpLscro.of_sepWP (mid := (blkPl_298).base + 192#64)
  wp_steps; wp_reach
  intro hinv'
  exact hskip hsp_align hrest_le hrest_lt hrest_suf htag_lt hnone_of_skip hcont
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx8, sf_truncate32_ofNat64])
    ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx22],
     by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
     by simp only [arm64_norm, hx29]⟩ hinv'

/-- Main outer loop induction at `+216` (`0x4e8c0`) for `V1State.mergeField`. -/
theorem v1Loop_loop_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263) (skipField3Spec A))
    (htag1 : V1StateTagStepHypPlaced A H 1 300#64)
    (htag2 : V1StateTagStepHypPlaced A H 2 564#64)
    (htag3 : V1StateTagStepHypPlaced A H 3 428#64)
    (htag4 : V1StateTagStepHypPlaced A H 4 476#64)
    (htag5 : V1StateTagStepHypPlaced A H 5 336#64)
    (htag6 : V1StateTagStepHypPlaced A H 6 604#64)
    (htag7 : V1StateTagStepHypPlaced A H 7 652#64)
    (htag8 : V1StateTagStepHypPlaced A H 8 516#64)
    (htag9 : V1StateTagStepHypPlaced A H 9 748#64)
    (htag10 : V1StateTagStepHypPlaced A H 10 380#64)
    (htag11 : V1StateTagStepHypPlaced A H 11 700#64)
    {x : V1StateMergeGhost} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      OptInnerStatePolyBound cur.length m.innerState →
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        (mergeLoopBin V1State.mergeField (cur.length - limit) m cur limit 99).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_298).base + 216#64 →
      s.status = .Running → s.sp = s0.sp - 816#64 → s.v1TraceEq s0 →
      V1StateLoopRegsPlaced s0 x limit s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
        (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hbound hres hpc hrun hsp htr hregs _hinv
    exact v1Loop_le_exit_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt hbound
      (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
      (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
      hpc hrun hsp htr hregs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hbound hres hpc hrun hsp htr hregs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact v1Loop_le_exit_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt hbound
        (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
        (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
        hpc hrun hsp htr hregs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine v1Loop_decode_key_step_placed hFromCall hVarintCall hle_lim hsp_align hcur_le hcur_lt hcur_suf
        (fun hml => by rw [hres, hml]; rfl) ?_ hpc hrun hsp htr hregs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx8' hregs' hinv'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hbound_rest : OptInnerStatePolyBound rest.length m.innerState := optInnerStatePolyBound_mono hbound hrest_le_cur
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := m) (depth' := 99) protoPrefixStep_v1State_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases hk_le : key.toNat / 8 ≤ 11
      · have hknown : ∀ (k : Nat) (off : BitVec 64),
            V1StateTagStepHypPlaced A H k off → key.toNat / 8 = k →
            (k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
             k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
             k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
             k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64) →
            SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
              (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
              (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
          intro k off htag htag_k hk_cases
          refine v1Loop_dispatch_known_tag_placed hPushCall htag hsp_align hbs_lt hrest_le hrest_lt hrest_suf
            hbound_rest hk_le htag_k hk_cases
            (fun hfn => by rw [hres, hstep, htag_k, hfn]; rfl) ?_ hpc' hrun' hsp' htr' hx0' hx1' hx8' hregs' hinv'
          intro m' rest' s'' hfsome hbound' hr'_le hpc'' hrun'' hsp'' htr'' hregs'' hinv''
          obtain ⟨_, hr'_suf⟩ := v1Loop_mergeField_suffix hk_cases hfsome
          exact ih m' rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le hr'_suf) hbound'
            (by rw [hres, hstep, htag_k, hfsome]) hpc'' hrun'' hsp'' htr'' hregs'' hinv''
        have hk_cases11 : key.toNat / 8 = 1 ∨ key.toNat / 8 = 2 ∨ key.toNat / 8 = 3 ∨
            key.toNat / 8 = 4 ∨ key.toNat / 8 = 5 ∨ key.toNat / 8 = 6 ∨ key.toNat / 8 = 7 ∨
            key.toNat / 8 = 8 ∨ key.toNat / 8 = 9 ∨ key.toNat / 8 = 10 ∨ key.toNat / 8 = 11 := by omega
        rcases hk_cases11 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
        · exact hknown 1 300#64 htag1 h1 (by decide)
        · exact hknown 2 564#64 htag2 h2 (by decide)
        · exact hknown 3 428#64 htag3 h3 (by decide)
        · exact hknown 4 476#64 htag4 h4 (by decide)
        · exact hknown 5 336#64 htag5 h5 (by decide)
        · exact hknown 6 604#64 htag6 h6 (by decide)
        · exact hknown 7 652#64 htag7 h7 (by decide)
        · exact hknown 8 516#64 htag8 h8 (by decide)
        · exact hknown 9 748#64 htag9 h9 (by decide)
        · exact hknown 10 380#64 htag10 h10 (by decide)
        · exact hknown 11 700#64 htag11 h11 (by decide)
      · have hk_gt : 11 < key.toNat / 8 := by omega
        rw [v1State_mergeField_other m iwt rest 99 htag_lt (Or.inr hk_gt)] at hstep
        refine v1Loop_dispatch_unknown_tag_placed hSkipCall hsp_align hrest_le hrest_lt hrest_suf htag_lt hk_gt
          (fun hsf_none => by rw [hres, hstep, hsf_none]; rfl) ?_ hpc' hrun' hsp' htr' hx0' hx1' hx8' hregs' hinv'
        intro rest' s'' hsf_some hpc'' hrun'' hsp'' htr'' hregs'' hinv''
        have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some
        exact ih m rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
          (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some))
          (optInnerStatePolyBound_mono hbound_rest hr'_le)
          (by rw [hres, hstep, hsf_some]; rfl) hpc'' hrun'' hsp'' htr'' hregs'' hinv''


end Placed

end CryptoVerification.SpqrV1.Prost.MessageMerge
