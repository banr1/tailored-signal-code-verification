/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded Outer Loop, Jump-Table Dispatch, and `skip_field` Arm for `V1State::merge`

Code-loaded (`withLsCodeRoLoaded lsmpl`) `[LibsignalPlacement]` exits, latch continuation, key
decode, `skip_field` arm, and outer loop induction for `V1State::merge` (Block `298`).
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopClPlaced
end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopClPlaced

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
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
  optProtoInnerStateJumpTableAt optProtoInnerStateJumpTablePlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero v1StateMerge_fnOff

private theorem setWidth8_ofNat64_wt_v1 (wt : WireType) :
    (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat := by
  cases wt <;> decide

private theorem key_tag_gt_11 {key : BitVec 64} (h : 11 < key.toNat / 8) :
    (BitVec.ule 96#64 key) = true ∧ (BitVec.ult key 96#64) = false := by
  have hge : 96 ≤ key.toNat := by omega
  simp only [BitVec.ule, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq, decide_eq_false_iff_not]
  change 96 ≤ key.toNat ∧ ¬ key.toNat < 96
  omega

/-- Uniform step contract for tag arm `k` (`1 ≤ k ≤ 11`) at entry offset `entryOff` (`ClPlaced`). -/
abbrev V1StateTagStepHypClPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (k : Nat) (entryOff : BitVec 64) : Prop :=
  ∀ {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat},
    V1StateTagEntryHypPlaced H s0 x m rest iwt limit s →
    s.pc = (blkPl_298).base + entryOff →
    V1StateTagContClPlaced A H s0 x R k m rest iwt limit →
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0)

/-- Shared exit at `+112`: stores `X8 = w` (`KindNoHeap w`) at `[SP, #240]` (`s0.sp - 576#64`),
calls `DecodeError::from`, and returns via `v1Loop_err_ret_exit_placed`. -/
theorem v1Loop_from_err_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx8 : s.readReg64 (Reg.gpr 8#5) = w)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  have herr_ret := @v1Loop_err_ret_exit_placed _ A H x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
  (conv => arg 4; rw [v1StateBelow_decodeError (s0.sp - 816#64), v1Loop_memRegion_720_split_err1 s0.sp, v1StateErrFramePlaced]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, hx8])
  apply SepWP.exists_elim; intro is'
  apply SepWP.exists_elim; intro v240
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c) (x := (s0.sp - 576#64, w))
    (ret_pc := (blkPl_298).base + 124#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp, hx8]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeErrorFromSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _hinv_m
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

/-- Shared exit at `+3376`: stores `X21 = err` at `[SP, #240]` (`s0.sp - 576#64`),
calls `DecodeError::push`, reloads `X1 = err`, and jumps to `+128`. -/
theorem v1Loop_push_err_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State} {err : BitVec 64} {n_err : Nat}
    (hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hn : n_err ≤ 3) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 3376#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx21 : s.readReg64 (Reg.gpr 21#5) = err)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  subst hx21
  have herr_ret := @v1Loop_err_ret_exit_placed _ A H x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 257) hinv
  (conv => arg 4; rw [v1StateBelow_decodeError (s0.sp - 816#64), v1Loop_memRegion_720_split_err1 s0.sp, v1StateErrFramePlaced]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro is'
  apply SepWP.exists_elim; intro v240
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c) (x := (s0.sp - 576#64, s.readReg64 (Reg.gpr 21#5), n_err))
    (ret_pc := (blkPl_298).base + 3412#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp]; rfl)
    (by omega : n_err < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeErrorPushSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _hinv_m
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

/-- Constructs `V1StateTagContClPlaced` at the shared loop latch `+2700` from the loop-header continuation at `+216`. -/
theorem v1Loop_latch_cont_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
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
    V1StateTagContClPlaced A H s0 x R k m rest iwt limit where
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
    intro hfield s' err n_err hpc hrun hsp htr hx21 herr hn hinv
    have hnone := hnone_of_field_none hfield
    have hcbnz : (err == 0#64) = false := beq_eq_false_iff_ne.mpr herr
    have hpush := @v1Loop_push_err_exit_cl_placed _ A H hPushCall x R s0
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 3376#64) hinv
    wp_steps; wp_reach; intro hinv'
    exact hpush hnone hn herr hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx21]) hinv'

/-- Loop exit at `+216` when `cur.length ≤ limit`. -/
theorem v1Loop_le_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
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
    (hregs : V1StateLoopRegsPlaced s0 x limit s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
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
    have hfrom_err := @v1Loop_from_err_exit_cl_placed _ A H hFromCall x R s0
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 112#64) hinv
    (conv => arg 4; rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr cur.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    wp_reach; intro hinv'
    apply SepWPp.weaken_pre
      (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [v1StateErrFramePlaced]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm]) hinv'

/-- Loop header key decode at `+216..+268` when `¬ cur.length ≤ limit`. -/
theorem v1Loop_decode_key_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
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
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have herr_ret := @v1Loop_err_ret_exit_placed _ A H x R s0
  have hfrom_err := @v1Loop_from_err_exit_cl_placed _ A H hFromCall x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  (conv => arg 4; rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, v1StateBelow_decodeVarint2 (s0.sp - 816#64)]; simp only [sepConj_assoc])
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c) (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := (blkPl_298).base + 236#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeVarint2Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hx29_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_loop_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_v1State_mergeField hgt_lim hd)
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
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 112#64) hinv_m
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
      wp_reach; intro hinv_e
      apply SepWPp.weaken_pre
        (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
          v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [v1StateErrFramePlaced]; sep_entail)
      exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hinv_e
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_loop_none (mergeLoopBin_of_wt_none protoPrefixStep_v1State_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 112#64) hinv_m
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
        wp_reach; intro hinv_e
        apply SepWPp.weaken_pre
          (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
            v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [v1StateErrFramePlaced]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hinv_e
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_loop_none (mergeLoopBin_of_tag_zero protoPrefixStep_v1State_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 112#64) hinv_m
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
          wp_reach; intro hinv_e
          apply SepWPp.weaken_pre
            (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
              v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
            (by dsimp only [v1StateErrFramePlaced]; sep_entail)
          exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hinv_e
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 268#64) hinv_m
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

/-- Unknown-tag `skip_field` arm at `+192..+212`. -/
theorem v1Loop_skip_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
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
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr_ret := @v1Loop_err_ret_exit_placed _ A H x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinv
  (conv => arg 4; rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hrest_le hrest_suf, v1StateBelow_skipField99 (s0.sp - 816#64)]; simp only [sepConj_assoc])
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c) (x := ⟨iwt, tag, 99, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 208#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx8, hx19, setWidth8_ofNat64_wt_v1]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 99 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [skipField3Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hx29_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 99 tag iwt rest with
  | none =>
    have hnone := hnone_of_skip hsf
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
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 216#64) hinv_m
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

theorem v1Loop_dispatch_known_tag_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : V1StateMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {key : BitVec 64} {limit : Nat}
    {k : Nat} {off : BitVec 64}
    (htag : V1StateTagStepHypClPlaced A H k off)
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
    (fun _ hentry hpc' => htag hentry hpc' (v1Loop_latch_cont_cl_placed hPushCall hsp_align hnone_of_field_none hcont_loop))
    hpc hrun hsp htr hx0 hx1 hx8 hregs hinv

theorem v1Loop_dispatch_unknown_tag_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
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
  have hskip := @v1Loop_skip_step_cl_placed _ A H hSkipCall x R s0
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

/-- Main outer loop induction at `+216` for `V1State.mergeField`. -/
theorem v1Loop_loop_ok_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    (htag1 : V1StateTagStepHypClPlaced A H 1 300#64)
    (htag2 : V1StateTagStepHypClPlaced A H 2 564#64)
    (htag3 : V1StateTagStepHypClPlaced A H 3 428#64)
    (htag4 : V1StateTagStepHypClPlaced A H 4 476#64)
    (htag5 : V1StateTagStepHypClPlaced A H 5 336#64)
    (htag6 : V1StateTagStepHypClPlaced A H 6 604#64)
    (htag7 : V1StateTagStepHypClPlaced A H 7 652#64)
    (htag8 : V1StateTagStepHypClPlaced A H 8 516#64)
    (htag9 : V1StateTagStepHypClPlaced A H 9 748#64)
    (htag10 : V1StateTagStepHypClPlaced A H 10 380#64)
    (htag11 : V1StateTagStepHypClPlaced A H 11 700#64)
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
    intro m cur s hcur_n hcur_le hcur_suf hbound hres hpc hrun hsp htr hregs hinv
    exact v1Loop_le_exit_cl_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt hbound
      (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
      (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
      hpc hrun hsp htr hregs hinv
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hbound hres hpc hrun hsp htr hregs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact v1Loop_le_exit_cl_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt hbound
        (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
        (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
        hpc hrun hsp htr hregs hinv
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine v1Loop_decode_key_step_cl_placed hFromCall hVarintCall hle_lim hsp_align hcur_le hcur_lt hcur_suf
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
            V1StateTagStepHypClPlaced A H k off → key.toNat / 8 = k →
            (k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
             k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
             k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
             k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64) →
            SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
              (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
              (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
          intro k off htag htag_k hk_cases
          refine v1Loop_dispatch_known_tag_cl_placed hPushCall htag hsp_align hbs_lt hrest_le hrest_lt hrest_suf
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
        refine v1Loop_dispatch_unknown_tag_cl_placed hSkipCall hsp_align hrest_le hrest_lt hrest_suf htag_lt hk_gt
          (fun hsf_none => by rw [hres, hstep, hsf_none]; rfl) ?_ hpc' hrun' hsp' htr' hx0' hx1' hx8' hregs' hinv'
        intro rest' s'' hsf_some hpc'' hrun'' hsp'' htr'' hregs'' hinv''
        have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some
        exact ih m rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
          (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some))
          (optInnerStatePolyBound_mono hbound_rest hr'_le)
          (by rw [hres, hstep, hsf_some]; rfl) hpc'' hrun'' hsp'' htr'' hregs'' hinv''

end CryptoVerification.SpqrV1.Prost.MessageMerge
