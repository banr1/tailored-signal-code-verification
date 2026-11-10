/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExit
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Verification of `spqr::decode_state` (Block `325`) — Stack Frame & Error Exits
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

/-! ## 1. Relocatable Postcondition Helpers -/

abbrev decodeStatePostPlaced [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (x : DecodeStateGhost) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStatePlacedSpecX H_inner A).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev decodeStatePanicPostPlaced [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (x : DecodeStateGhost) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStatePlacedSpecX H_inner A).onPanic x s0 sf ∗ R)

/-! ## 2. Shared Epilogue `0x53e60..0x53e7c` and Error Tail `0x53df4..0x53e5c` -/

/-- Shared epilogue `0x53e60..0x53e7c` (`+2500..+2528`, 8 instructions):
    restores `sp := sp + 0x510`, pops `x20, x19, ..., x29, x30`, `sp := sp + 0x60`, and returns. -/
theorem decodeState_epilogue_53e60_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStatePlacedSpecX H_inner A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hpc : s.pc = decodeStatePlacedEntry + 2500#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      decodeStateResultAt H_inner A x.outPtr (spqrDecodeState x.st.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 1296 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP hpost
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  unfold decodeStateSavedAt
  wp_steps
  dsimp only [decodeStatePlacedSpecX, spqrDecodeStatePlacedSpec]
  refine SepWP.fold (decodeState_stack_restore_1296 s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
    unfold decodeStateSavedAt
    sep_focus) ?_
  wp_done

set_option maxHeartbeats 800000 in
/-- Inlined `drop_glue::<DecodeError>` + `Err(Error::StateDecode)` write + epilogue
    (`0x53e0c..0x53e7c`, `+2416..+2528`, 29 instructions). -/
theorem decodeState_err_drop_53e0c_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
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

/-- Error tail (`0x53df4..0x53e7c`, offsets `2392..2532`):
copies the partially-decoded `proto::PqRatchetState` at `[sp + 0x160]` (`s0.sp - 1040#64`) into
`[sp + 0x2c0]` (`s0.sp - 688#64`) via `memcpy(..., 352)`, drops it via
`drop_in_place<proto::PqRatchetState>`, and executes `decodeState_err_drop_53e0c_placed` on the boxed
`DecodeError` in `x20`. -/
theorem decodeState_err_tail_53df4_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
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
  simp only [dropProtoPqRatchetStatePlacedSpec] at hdrop
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hmemcpy hdrop ⊢
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
  wp_apply
  wp_conv_pre => simp only [*]
  refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) dropOptProtoInnerStateStack (by decide))
    (by sep_focus) ?_
  refine SepWP.fold (frame_4chunks_to_1296 s0.sp) (by sep_focus) ?_
  exact decodeState_err_drop_53e0c_placed hc x n s0 _ _ R post hpost herr
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hs0A
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-! ## 3. Panic-Aware Call Helpers (`DecodeError::push`, `DecodeError::from`) & `0x53cdc..0x53df0` -/

theorem SepWPp.call_decodeErrorPush_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorPushSpec A))
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
      SepWPp prog ret sf
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e (n + 1) ∗ A.pool ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPp prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) :=
  SepWPp.call_decodeErrorPush (H_inner := H_inner) (b := 0#64) (x_outer := x_outer)
    hcall d e n hpc hrun hsp hs0A hlr htr hx0 hn hP hnext

theorem SepWPp.call_decodeErrorFrom_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorFromSpec A))
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
      SepWPp prog ret sf
        ((decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPp prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) :=
  SepWPp.call_decodeErrorFrom (H_inner := H_inner) (b := 0#64) (x_outer := x_outer)
    hcall k w hpc hrun hsp hs0A hlr htr hx0 hw hP hnext

/-- Error push at `0x53dec..0x53df0` (`+2384..+2388`, 2 instructions) followed by `decodeState_err_tail_53df4_placed`:
calls `DecodeError::push` on `x0 = s0.sp - 688#64` holding `errBox`, loads `x20 := [sp + 0x2c0]`,
and drops `curSt` and `errBox`. -/
theorem decodeState_err_push_53dec_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
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
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hpush := hc.decodeErrorPush
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hpush ⊢
  apply SepWPp.of_sepWP (mid := lsmpl.base 257)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorPush_placed hpush (s0.sp - 688#64) errBox n
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
  apply SepWPp.of_sepWP_ret
  wp_steps 1
  refine SepWP.fold (scratch_688_fold_48 s0.sp errBox) (by sep_focus) ?_
  exact decodeState_err_tail_53df4_placed hc x curSt (n + 1) s0 _ _ R post hpost herr
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hs0A
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- Error push at `0x53dcc..0x53df0` (`+2352..+2388`, 10 instructions):
stores `x1` (`errBox`) at `[sp + 0x2c0]` (`s0.sp - 688#64`), sets `("PqRatchetState", "version_negotiation")`,
and delegates to `decodeState_err_push_53dec_placed`. -/
theorem decodeState_err_push_53dcc_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
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
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2384#64)
  wp_steps 8
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53dec_placed hc x curSt (s.readReg64 .x1) n s0 _ _ R post hpost herr hn
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm, hsp])
    hs0A
    (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm])

/-- Error push at `0x53cdc..0x53cfc` (`+2112..+2144`, 9 instructions):
stores `x1` (`errBox`) at `[sp + 0x2c0]` (`s0.sp - 688#64`), sets `("PqRatchetState", "chain")`,
and jumps to `0x53dec` (`decodeState_err_push_53dec_placed`). -/
theorem decodeState_err_push_53cdc_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
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
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2384#64)
  wp_steps 9
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53dec_placed hc x curSt (s.readReg64 .x1) n s0 _ _ R post hpost herr hn
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm, hsp])
    hs0A
    (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm])

end CryptoVerification.SpqrV1.Top.DecodeState
