/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlaced
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded `[LibsignalPlacement]` Error Exits for `spqr::decode_state` (Block `325`)

Proves the code-loaded shared epilogue (`+2500..+2528`), `DecodeError` drop/unwind tail
(`+2392..+2528`), and top-level `DecodeError::push` error-exit blocks under `LibsignalPlacement`.
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Lift a `LibsignalCodeLoaded`-indexed return `SepWP` into `SepWPpIPlaced`. -/
theorem SepWPpIPlaced.of_sepWP_ret_lscl [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : LibsignalCodeLoaded lsmpl s.mem → SepWP prog ret s P Q) :
    SepWPpIPlaced prog ret s P Q Q_err :=
  fun hinv => SepWPp.of_sepWP_ret (h hinv.1)

set_option maxHeartbeats 800000 in
/-- Inlined `drop_glue::<DecodeError>` + `Err(Error::StateDecode)` write + epilogue
    (`+2416..+2528`, 29 instructions), using `DecodeStateCalleeContractsClPlaced`. -/
theorem decodeState_err_drop_53e0c_cl_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A ext)
    (x : DecodeStateGhost) (n : Nat) (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStatePlacedSpecX H_inner A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      decodeErrorAtStackLen A (s.readReg64 .x20) n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 1296 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hdealloc := hc.dealloc
  simp only [rustDeallocSpec] at hdealloc
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP hpost
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hdealloc ⊢
  refine SepWP.weaken_pre (sepConj_mono_left (decodeErrorWith_unfold A (s.readReg64 .x20) n)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro ptr
  apply ProofLib.SepWP.exists_left; intro w
  wp_focus_pure; rintro ⟨hn_cap, hcap_lt, hptr, hw⟩
  have hbr := kindNoHeap_branch_false hw
  refine SepWP.fold (memRegion_352_err_split x.outPtr) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
  unfold decodeStateSavedAt
  by_cases hcap0 : cap = 0
  · have hcap_beq : (cap == 0#64) = true := beq_iff_eq.mpr hcap0
    have hite : (if cap = 0 then emp else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) = emp := by
      simp [hcap0]
    rw [hite, emp_sepConj]
    wp_steps
    refine SepWP.fold (box72_entails_memRegion (s.readReg64 .x20) cap ptr (BitVec.ofNat 64 n) w)
      (by sep_focus) ?_
    wp_apply
    wp_conv_pre => simp only [*]
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
    wp_steps
    try dsimp only [decodeStatePlacedSpecX, spqrDecodeStatePlacedSpec]
    refine SepWP.fold (fold_decodeStateResultAt_err H_inner A x.outPtr herr) (by sep_focus) ?_
    refine SepWP.fold (decodeState_stack_restore_1296 s0.sp
      (s0.readReg64 .x29) (s0.readReg64 .x30)
      (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
      (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
      unfold decodeStateSavedAt
      sep_focus) ?_
    wp_done
  · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hshl : (cap <<< 5).toNat = cap.toNat * 32 := shl5_toNat hcap_lt
    have hite : (if cap = 0 then emp else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) =
        (A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) :=
      ite_eq_right_iff.mpr fun h => absurd h hcap0
    rw [hite]
    wp_steps
    wp_apply
    wp_conv_pre => simp only [*]
    wp_steps
    refine SepWP.fold (box72_entails_memRegion (s.readReg64 .x20) cap ptr (BitVec.ofNat 64 n) w)
      (by sep_focus) ?_
    wp_apply
    wp_conv_pre => simp only [*]
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
    wp_steps
    try dsimp only [decodeStatePlacedSpecX, spqrDecodeStatePlacedSpec]
    refine SepWP.fold (fold_decodeStateResultAt_err H_inner A x.outPtr herr) (by sep_focus) ?_
    refine SepWP.fold (decodeState_stack_restore_1296 s0.sp
      (s0.readReg64 .x29) (s0.readReg64 .x30)
      (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
      (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
      unfold decodeStateSavedAt
      sep_focus) ?_
    wp_done

/-- Error tail (`+2392..+2532`): copies partially-decoded `proto::PqRatchetState`, drops it via
code-loaded `drop_in_place<proto::PqRatchetState>` (Block `270`), and drops the boxed `DecodeError`. -/
theorem decodeState_err_tail_53df4_cl_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (n : Nat)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStatePlacedSpecX H_inner A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2392#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      decodeErrorAtStackLen A (s.readReg64 .x20) n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 688#64) 352 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy := hc.session_memcpy allocHookStack
  simp only [sessionMemcpySpec] at hmemcpy
  have hdrop := hc.dropProtoPqRatchetState
  simp only [withLsCl, dropProtoPqRatchetStatePlacedSpec] at hdrop
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hmemcpy hdrop ⊢
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 270)
  refine SepWP.fold (protoPqRatchetState_to_memcpy H_inner A (s0.sp - 1040#64) (s0.sp - 688#64) curSt)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro srcBs
  wp_focus_pure; intro hsrc_len
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
  wp_steps
  wp_apply
  wp_conv_pre => simp only [*]
  refine SepWP.fold (protoPqRatchetState_of_memcpy H_inner A (s0.sp - 1040#64) (s0.sp - 688#64) curSt hsrc_len)
    (by sep_focus) ?_
  refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) dropOptProtoInnerStateStack (by decide))
    (by sep_focus) ?_
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · simp only [arm64_norm, *]
  intro _hcl_call
  wp_apply
  wp_conv_pre => simp only [*]
  refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) dropOptProtoInnerStateStack (by decide))
    (by sep_focus) ?_
  refine SepWP.fold (frame_4chunks_to_1296 s0.sp) (by sep_focus) ?_
  exact decodeState_err_drop_53e0c_cl_placed hc x n s0 _ _ R post hpost herr
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hs0A
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-! ## Panic-Aware Call Helpers (`DecodeError::push`, `DecodeError::from`) in `SepWPpIPlaced` -/

theorem SepWPpIPlaced.call_decodeErrorPush_cl [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)))
    (d e : BitVec 64) (n : Nat) {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = d)
    (hn : n < 2 ^ 32)
    (hP : P = ((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e n ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      SepWPpIPlaced prog ret sf
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e (n + 1) ∗ A.pool ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - decodeErrorHookStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hpre : s.mem ⊨ (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)).pre (d, e, n) s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv.1, ?_⟩
    dsimp only [decodeErrorPushSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hn⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur decodeErrorHookStack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (d, e, n) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (decodeErrorPushSpec A).post (d, e, n) s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [decodeErrorPushSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    rw [hlr] at hpcm; rw [hsp] at hspm
    have hpost1 : sm.mem ⊨
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e (n + 1) ∗ A.pool ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - decodeErrorHookStack) ∗
            stackAt sp_cur decodeErrorHookStack)) ∗ F) ∗ R' := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; ac_rfl
    have hpost2 : sm.mem ⊨
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e (n + 1) ∗ A.pool ∗
          stackAt sp_cur v1StateMergeStack) ∗ F) ∗ R' :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur decodeErrorHookStack (by decide))))))) hpost1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm (htr.step htrm hcsm) hcsm
        (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ (decodeErrorPushSpec A).onPanic (d, e, n) s sm ∗ (F_ext ∗ R') at hpost
    rw [← sepConj_assoc] at hpost
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, ?_⟩)⟩
    intro hm'
    dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, decodeErrorPushSpec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · dsimp only [decodeErrorPushSpec, withLsCodeLoaded] at hpost
    exact (allowPanic_not_exited hpost).elim
  · exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_decodeErrorFrom_cl [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)))
    (k w : BitVec 64) {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = k)
    (hw : KindNoHeap w)
    (hP : P = ((k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (v_k : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        ((decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - decodeErrorHookStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hpre : s.mem ⊨ (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)).pre (k, w) s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv.1, ?_⟩
    dsimp only [decodeErrorFromSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hw⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur decodeErrorHookStack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (k, w) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (decodeErrorFromSpec A).post (k, w) s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [decodeErrorFromSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_ne, htrm⟩, hpost⟩
    rw [hlr] at hpcm; rw [hsp] at hspm
    rw [ProofLib.memRegion_split' (b := k) (n := 8) (k := 40)
        (b' := k + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight k] at hpost
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨v_k, hpost⟩
    have hpost1 : sm.mem ⊨
        ((decodeErrorAtStackLen A (sm.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - decodeErrorHookStack) ∗
            stackAt sp_cur decodeErrorHookStack)) ∗ F) ∗ R' := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; ac_rfl
    have hpost2 : sm.mem ⊨
        ((decodeErrorAtStackLen A (sm.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool ∗ stackAt sp_cur v1StateMergeStack) ∗ F) ∗ R' :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur decodeErrorHookStack (by decide)))))))) hpost1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm v_k hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne
        (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ (decodeErrorFromSpec A).onPanic (k, w) s sm ∗ (F_ext ∗ R') at hpost
    rw [← sepConj_assoc] at hpost
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, ?_⟩)⟩
    intro hm'
    dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, decodeErrorFromSpec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · dsimp only [decodeErrorFromSpec, withLsCodeLoaded] at hpost
    exact (allowPanic_not_exited hpost).elim
  · exact False.elim (not_satisfies_false_sepConj hpost)

/-- Error push at `+2384..+2388` (2 instructions) followed by `decodeState_err_tail_53df4_cl_placed`. -/
theorem decodeState_err_push_53dec_cl_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (errBox : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hn : n < 2 ^ 32)
    (hpc : s.pc = decodeStatePlacedEntry + 2384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 688#64)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ errBox) ∗
      decodeErrorAtStackLen A errBox n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hpush := hc.decodeErrorPush
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hpush ⊢
  refine SepWPpIPlaced.of_sepWP (mid := lsmpl.base 257) ?_
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPpIPlaced.call_decodeErrorPush_cl hpush (s0.sp - 688#64) errBox n
    (ret_pc := (blkPl_325).base + 2388#64)
    (hpc := by simp only [arm64_norm])
    (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [arm64_norm])
    (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0])
    (hn := hn)
    (hP := by sep_focus) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
  refine SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2392#64) ?_
  wp_steps 1
  refine SepWP.fold (scratch_688_fold_48 s0.sp errBox) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpIPlaced.of_sepWP_ret_lscl fun hcl => ?_
  exact decodeState_err_tail_53df4_cl_placed hc x curSt (n + 1) s0 _ hcl _ R post hpost herr
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hs0A
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- Error push at `+2352..+2388` (10 instructions): sets `("PqRatchetState", "version_negotiation")`
and delegates to `decodeState_err_push_53dec_cl_placed`. -/
theorem decodeState_err_push_53dcc_cl_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hn : n < 2 ^ 32)
    (hpc : s.pc = decodeStatePlacedEntry + 2352#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeErrorAtStackLen A (s.readReg64 .x1) n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  refine SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2384#64) ?_
  wp_steps 8
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53dec_cl_placed hc x curSt (s.readReg64 .x1) n s0 _ _ R post hpost herr hn
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm, hsp])
    hs0A
    (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm])

/-- Error push at `+2112..+2144` (9 instructions): sets `("PqRatchetState", "chain")`
and jumps to `+2384` (`decodeState_err_push_53dec_cl_placed`). -/
theorem decodeState_err_push_53cdc_cl_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hn : n < 2 ^ 32)
    (hpc : s.pc = decodeStatePlacedEntry + 2112#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeErrorAtStackLen A (s.readReg64 .x1) n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  refine SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2384#64) ?_
  wp_steps 9
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53dec_cl_placed hc x curSt (s.readReg64 .x1) n s0 _ _ R post hpost herr hn
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm, hsp])
    hs0A
    (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm])

end CryptoVerification.SpqrV1.Top.DecodeState
