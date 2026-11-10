/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1Placed
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1
import ProofLib.SepLogic.WPp

/-!
# Relocatable V1 Ratchet Error Tail & `<Message>::deserialize` Continuation for `spqr::recv`

Relocatable shared error-cleanup tail (`+2500..+2536 -> +1040`) and post-`<Message>::deserialize`
error/relocation steps (`+1568..+1636`, `+2060..+2104`) for `spqr::recv` (Block `329`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Recv.Placed

variable [LibsignalPlacement]

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Placed Shared Error Tail (`+2500 .. +2536 -> +1040`, `w26 = 0`) -/

/-- Drop `pre_pb.chain` at `s0.sp - 4592#64` (`+2524 .. +2536`), check `tbz w26, #0, +1040`
    (`w26 = 0`), join the stack frame, and return via `step_epilogue_placed`. -/
theorem step_drop_chain_2524_placed {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem}
    (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2524#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (_hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      memRegion (s0.sp - 4640#64) 48 ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 4416 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  apply sepWP_seq_lscl hcl
  wp_steps 3
  refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack80 (by decide)))
    (by sep_focus) ?_
  have hdrop_chain := subroutine_ok_withMemEq_of_lscl hC.dropOptProtoChain_ok hcl1
  dsimp only [spqrRecvPlacedProg, Drop.dropOptProtoSpqrChainSpec] at hdrop_chain
  wp_call hdrop_chain ⟨s0.sp - 4592#64, pre_pb.chain⟩
  have hsp_eq : stackAt s.sp dropStack80 = stackAt (s0.sp - 4992#64) dropStack80 := by rw [hsp]
  refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack80 (by decide)).symm)
    (by sep_focus) ?_
  wp_steps 1
  refine SepWP.focus_weaken (ownFrame_join_err_2524 s0.sp) (by sep_focus) ?_
  exact step_epilogue_placed A M ext st msg ret s0 _ _ R post hpost
    (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
    (by simp only [arm64_norm, *]) (by ac_rfl)

/-- Shared error cleanup tail at `+2500 .. +2536` (`-> +1040` when `w26 = 0`): drops
    `pre_pb.versionNegotiation` at `s0.sp - 4640#64` (`sp + 0x160`), calls
    `drop_in_place<Option<Chain>>` on `pre_pb.chain` at `s0.sp - 4592#64` (`sp + 0x190`), checks
    `tbz w26, #0, +1040`, and returns via `step_epilogue_placed` (`+1040 .. +1072`). -/
theorem step_drop_vn_chain_2500_placed {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem}
    (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2500#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 4416 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hdealloc_raw := hC.dealloc_ok
  simp only [rustDeallocSpec] at hdealloc_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  cases hvn : pre_pb.versionNegotiation with
  | none =>
    dsimp only [optVersionNegotiationPBTailAt]
    wp_focus_pure; intro hw0
    subst hw0
    have hsle : (1#64).sle noneCap = false := rfl
    apply sepWP_seq_lscl hcl
    wp_steps 3
    refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
    refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
    exact step_drop_chain_2524_placed A M ext hC st msg ret pre_pb s0 _ _ R post hpost hs0_align
      (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) hcl1
  | some vn =>
    refine SepWP.focus_weaken (vnTail_sub4640_some_entails_dealloc A s0.sp w0 w1 vn) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc]
    by_cases hc0 : (w0 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hw0
      apply sepWP_seq_lscl hcl
      wp_steps 3
      refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
      refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
      exact step_drop_chain_2524_placed A M ext hC st msg ret pre_pb s0 _ _ R post hpost hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl) hcl1
    · have hslt := Drop.cap_ne_zero_slt_one_false hcap_lt hc0
      have hsle := cap_ne_zero_one_sle_true hcap_lt hc0
      have hlt_false := Drop.cap_ne_zero_lt_one_false hcap_lt hc0
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)))
        (by sep_focus) ?_
      apply sepWP_seq_lscl hcl (mid := (blkPl_329).base + 2524#64)
      wp_steps 6
      wp_call hdealloc_raw ⟨w1, w0.toNat, 1⟩
      refine ProofLib.SepWP.done (by simp only [spqrRecvPlacedEntry, arm64_norm, *]) (by simp only [arm64_norm, *]) fun hcl1 => ?_
      have hsp_eq : stackAt s.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp]
      refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp w0 w1) (by sep_focus) ?_
      exact step_drop_chain_2524_placed A M ext hC st msg ret pre_pb s0 _ _ R post hpost hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl) hcl1

/-! ## 2. Placed `<Message>::deserialize` (`+1532 .. +1636` & `+2060 .. +2104`) -/

/-- Error branch of `<Message>::deserialize` at `+2060 .. +2104` (`-> +2500`): stores `err` to
    scratch `[sp + 0x2c0 + 231..255]` and to `ret`, drops `pre_pb.inner` at `s0.sp - 4512#64`,
    and jumps to `step_drop_vn_chain_2500_placed` (`+2500`). -/
theorem step_msgDeserialize_err_2060_placed {H_inner : V1InnerHeapPred}
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State) (w0 w1 : BitVec 64)
    (err : Error) (q0 : BitVec 128) (w2 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .error err)
    (htag : BitVec.truncate 8 q0 = spqrErrorTag err)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2060#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      Drop.optProtoInnerStateAt A (s0.sp - 4512#64) pb.innerState ∗
      memRegion (s0.sp - 4288#64) 1232 ∗
      memRegion (s0.sp - 3056#64) 8 ∗
      ((s0.sp - 3048#64) ↦₈ 0xff#8) ∗
      memRegion (s0.sp - 3047#64) 7 ∗
      ((s0.sp - 3040#64) ↦₁₂₈ q0) ∗
      ((s0.sp - 3024#64) ↦₆₄ w2) ∗
      memRegion (s0.sp - 3016#64) 8 ∗
      memRegion (s0.sp - 3008#64) 2912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r3 r2 r1 r0
  refine SepWP.focus_weaken (memRegion_1232_split_err_2060 s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i s0_128 s1_64
  rw [pointsTo128_sub_eq s0.sp 3040 3032 q0 rfl,
      pointsTo128_sub_eq s0.sp 4057 4049 s0_128 rfl]
  apply sepWP_seq_lscl hcl
  wp_steps 11
  refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)))
    (by sep_focus) ?_
  unfold spqrRecvRoPlacedAt Prost.MessageMerge.v1StateJumpTablesPlacedAt
  apply sepWP_seq_lscl hcl1 (mid := (blkPl_329).base + 2500#64)
  have hdrop_inner := subroutine_ok_withMemEq_of_lscl hC.dropOptProtoInnerState_ok hcl1
  dsimp only [spqrRecvPlacedProg, Drop.dropOptProtoInnerStatePlacedSpec] at hdrop_inner
  wp_call hdrop_inner ⟨s0.sp - 4512#64, pb.innerState⟩
  have hsp_eq : stackAt s.sp dropStack96 = stackAt (s0.sp - 4992#64) dropStack96 := by rw [hsp]
  refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)).symm)
    (by sep_focus) ?_
  wp_steps 1
  refine ProofLib.SepWP.done (by simp only [spqrRecvPlacedEntry, arm64_norm, *]) (by simp only [arm64_norm, *]) fun hcl3 => ?_
  have h224 : memRegion (s0.sp - 4512#64) Drop.optProtoInnerStateSize = memRegion (s0.sp - 4512#64) 224 := rfl
  rw [h224]
  have hro_fold :
      Drop.optProtoInnerStateJumpTablePlacedAt ∗
        Prost.MessageMerge.v1StateMergeJumpTablePlacedExpanded ∗
        statesFromPbJumpTablePlacedAt ∗
        statesRecvRoPlacedAt ∗
        statesIntoPbJumpTablePlacedAt =
      spqrRecvRoPlacedAt := by
    unfold spqrRecvRoPlacedAt Prost.MessageMerge.v1StateJumpTablesPlacedAt
    ac_rfl
  refine SepWP.focus_weaken (Entails.of_eq hro_fold) (by sep_focus) ?_
  refine SepWP.focus_weaken (recv_err_q0_foldX A ret (q0.extractLsb' 64 64) w2 q0 err htag) (by sep_focus) ?_
  have hres_eq : recvResultExactKeyAt A ret (.error (err == .stateDecode)) =
      recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [(spqrV1Recv_v1_msgDeserialize_err F K hpre hdec hinner hmv hmin hmsg).1]
  rw [hres_eq]
  refine SepWP.focus_weaken (Entails.of_eq (pointsTo128_sub_eq s0.sp 4057 4049 q0 rfl).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (pointsTo128_sub_eq s0.sp 3040 3032 q0 rfl).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (memRegion_1232_join_err_2060 s0.sp q0 w2) (by sep_focus) ?_
  refine SepWP.focus_weaken (messageErrorAt_sub3056_to_memRegion_48 s0.sp q0 w2) (by sep_focus) ?_
  refine SepWP.focus_weaken (memRegion_join_4288_for_1532 s0.sp) (by sep_focus) ?_
  refine SepWP.focus_weaken (memRegion_join_4512_224_4192 s0.sp) (by sep_focus) ?_
  exact step_drop_vn_chain_2500_placed A (spqrV1Recv F K) ext hC st msg ret pre_pb w0 w1 s0 _ _ R post
    hpost hs0_align
    (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl) hcl3

/-- Ok branch of `<Message>::deserialize` at `+1568 .. +1636`: copies the 48-byte `messageAt
    spqrPolyApi (s0.sp - 3056#64) sckaMsg` to `s0.sp - 4112#64` (`sp + 0x370`), sets `x0 = s0.sp
    - 4512#64`, `x8 = s0.sp - 2096#64`, `x24 = s0.sp - 2096#64`, and reaches `+1636` (`bl
    <States>::from_pb`). -/
theorem step_msg_relocate_1568_placed (ext : String → Option (State → State))
    (sckaMsg : Message spqrPolyApi) (tag : BitVec 8) (bs39 : List (BitVec 8))
    (hbs39 : bs39.length = 39)
    (hfold_msg : ∀ a' : BitVec 64,
      (a' ↦₆₄ sckaMsg.epoch) ∗ ((a' + 0x08#64) ↦₈ tag) ∗ ((a' + 0x09#64) ↦ₛ bs39) ⊢
        messageAt spqrPolyApi a' sckaMsg)
    (s0 s : State) (P F_rest : SepProp) (post : State → SepProp → Prop)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1568#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hx8 : (s.readReg64 .x8).truncate 8 = tag)
    (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hP : P =
      memRegion (s0.sp - 4288#64) 1232 ∗
      ((s0.sp - 3056#64) ↦₆₄ sckaMsg.epoch) ∗
      ((s0.sp - 3048#64) ↦₈ tag) ∗
      ((s0.sp - 3047#64) ↦ₛ bs39) ∗
      memRegion (s0.sp - 3008#64) 2912 ∗
      F_rest)
    (hnext : ∀ s1 : State,
      s1.pc = spqrRecvPlacedEntry + 1636#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 4992#64 →
      TraceVRegs s1 s →
      s1.readReg64 .x0 = s0.sp - 4512#64 →
      s1.readReg64 .x8 = s0.sp - 2096#64 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x24 = s0.sp - 2096#64 →
      s1.readReg64 .x25 = s0.sp - 4640#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s0.sp - 3056#64 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1
        (memRegion (s0.sp - 4288#64) 176 ∗
          messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
          memRegion (s0.sp - 4064#64) 3968 ∗
          F_rest) post) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  obtain ⟨bs15, b24, bs15', q1, q0, w40, hbs15, hb24, hbs15', hsplit39, hq1, hq0⟩ :=
    bytes39_expose_copy_atoms hbs39
  have hsrc_split :
      ((s0.sp - 3047#64) ↦ₛ bs39) =
        ((s0.sp - 3047#64) ↦ₛ bs15) ∗ ((s0.sp - 3032#64) ↦₁₂₈ q0) ∗ ((s0.sp - 3016#64) ↦₆₄ w40) := by
    have h := hsplit39 (s0.sp - 3056#64)
    have ha9 : (s0.sp - 3056#64) + 0x09#64 = s0.sp - 3047#64 := by bv_omega
    have ha24 : (s0.sp - 3056#64) + 24#64 = s0.sp - 3032#64 := by bv_omega
    have ha25 : (s0.sp - 3056#64) + 25#64 = s0.sp - 3031#64 := by bv_omega
    have ha40 : (s0.sp - 3056#64) + 40#64 = s0.sp - 3016#64 := by bv_omega
    rw [ha9, ha24, ha25, ha40] at h
    have hq0_src : ((s0.sp - 3032#64) ↦ₛ b24) ∗ ((s0.sp - 3031#64) ↦ₛ bs15') =
        ((s0.sp - 3032#64) ↦₁₂₈ q0) := by
      have h0 := hq0 (s0.sp - 3032#64)
      have ha1 : (s0.sp - 3032#64) + 1#64 = s0.sp - 3031#64 := by bv_omega
      rwa [ha1] at h0
    rw [h, ← sepConj_assoc ((s0.sp - 3032#64) ↦ₛ b24), hq0_src]
  have hsrc_swap :
      ((s0.sp - 3047#64) ↦ₛ bs15) ∗ ((s0.sp - 3032#64) ↦₁₂₈ q0) =
        ((s0.sp - 3047#64) ↦₁₂₈ q1) ∗ ((s0.sp - 3031#64) ↦ₛ bs15') := by
    have h0 := (hq0 (s0.sp - 3032#64)).symm
    have ha1 : (s0.sp - 3032#64) + 1#64 = s0.sp - 3031#64 := by bv_omega
    rw [ha1] at h0
    have h1 := hq1 (s0.sp - 3047#64)
    have ha15 : (s0.sp - 3047#64) + 15#64 = s0.sp - 3032#64 := by bv_omega
    rw [ha15] at h1
    rw [h0, ← sepConj_assoc, h1]
  have hscr_split_q0 :
      ((s0.sp - 4049#64) ↦₁₂₈ q0) =
        ((s0.sp - 4049#64) ↦ₛ b24) ∗ ((s0.sp - 4048#64) ↦ₛ bs15') := by
    have h0 := (hq0 (s0.sp - 4049#64)).symm
    have ha1 : (s0.sp - 4049#64) + 1#64 = s0.sp - 4048#64 := by bv_omega
    rwa [ha1] at h0
  have hscr_to_q1 :
      memRegion (s0.sp - 4064#64) 15 ∗ ((s0.sp - 4049#64) ↦ₛ b24) ⊢
        ∃∗ s_q1 : BitVec 128, (s0.sp - 4064#64) ↦₁₂₈ s_q1 := by
    have h := memRegion_15_and_byte1_to_pointsTo128 (s0.sp - 4064#64) hb24
    have ha15 : (s0.sp - 4064#64) + 15#64 = s0.sp - 4049#64 := by bv_omega
    rwa [ha15] at h
  have hscr_swap_q1_q0 :
      ((s0.sp - 4064#64) ↦₁₂₈ q1) ∗ ((s0.sp - 4048#64) ↦ₛ bs15') =
        ((s0.sp - 4064#64) ↦ₛ bs15) ∗ ((s0.sp - 4049#64) ↦₁₂₈ q0) := by
    have h1 := (hq1 (s0.sp - 4064#64)).symm
    have ha15 : (s0.sp - 4064#64) + 15#64 = s0.sp - 4049#64 := by bv_omega
    rw [ha15] at h1
    rw [h1, sepConj_assoc, ← hscr_split_q0]
  have hdst_split_q1 :
      ((s0.sp - 4103#64) ↦₁₂₈ q1) =
        ((s0.sp - 4103#64) ↦ₛ bs15) ∗ ((s0.sp - 4088#64) ↦ₛ b24) := by
    have h1 := (hq1 (s0.sp - 4103#64)).symm
    have ha15 : (s0.sp - 4103#64) + 15#64 = s0.sp - 4088#64 := by bv_omega
    rwa [ha15] at h1
  have hdst_to_q0 :
      ((s0.sp - 4088#64) ↦ₛ b24) ∗ memRegion (s0.sp - 4087#64) 15 ⊢
        ∃∗ d_q0 : BitVec 128, (s0.sp - 4088#64) ↦₁₂₈ d_q0 := by
    have h := byte1_and_memRegion_15_to_pointsTo128 (s0.sp - 4088#64) hb24
    have ha1 : (s0.sp - 4088#64) + 1#64 = s0.sp - 4087#64 := by bv_omega
    rwa [ha1] at h
  have hdst_fold_msg :
      ((s0.sp - 4112#64) ↦₆₄ sckaMsg.epoch) ∗
        ((s0.sp - 4104#64) ↦₈ tag) ∗
        ((s0.sp - 4103#64) ↦ₛ bs15) ∗
        ((s0.sp - 4088#64) ↦₁₂₈ q0) ∗
        ((s0.sp - 4072#64) ↦₆₄ w40) ⊢
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg := by
    have h0 := (hq0 (s0.sp - 4088#64)).symm
    have ha1 : (s0.sp - 4088#64) + 1#64 = s0.sp - 4087#64 := by bv_omega
    rw [ha1] at h0
    have h := (hsplit39 (s0.sp - 4112#64)).symm
    have ha9 : (s0.sp - 4112#64) + 0x09#64 = s0.sp - 4103#64 := by bv_omega
    have ha24 : (s0.sp - 4112#64) + 24#64 = s0.sp - 4088#64 := by bv_omega
    have ha25 : (s0.sp - 4112#64) + 25#64 = s0.sp - 4087#64 := by bv_omega
    have ha40 : (s0.sp - 4112#64) + 40#64 = s0.sp - 4072#64 := by bv_omega
    rw [ha9, ha24, ha25, ha40] at h
    have ha8 : (s0.sp - 4112#64) + 0x08#64 = s0.sp - 4104#64 := by bv_omega
    have hfm := hfold_msg (s0.sp - 4112#64)
    rw [ha8, ha9] at hfm
    refine Entails.trans (Entails.of_eq ?_) hfm
    rw [h0, ← h]
    ac_rfl
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
  rw [hsrc_split]
  refine SepWP.focus_weaken (memRegion_1232_split_ok_1568 s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i d0 d8 d9 d40 s_q0
  rw [pointsTo128_sub_eq s0.sp 3032 3024 q0 rfl]
  wp_steps 1
  refine SepWP.focus_weaken (Entails.of_eq (pointsTo128_sub_eq s0.sp 3032 3024 q0 rfl).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq hsrc_swap) (by sep_focus) ?_
  rw [pointsTo128_sub_eq s0.sp 3047 3039 q1 rfl,
      pointsTo128_sub_eq s0.sp 4049 4041 s_q0 rfl]
  wp_steps 8
  refine SepWP.focus_weaken (Entails.of_eq (pointsTo128_sub_eq s0.sp 3047 3039 q1 rfl).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (pointsTo128_sub_eq s0.sp 4049 4041 q0 rfl).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq hscr_split_q0) (by sep_focus) ?_
  refine SepWP.focus_weaken hscr_to_q1 (by sep_focus) ?_
  wp_pull_exists; rename_i s_q1
  rw [pointsTo128_sub_eq s0.sp 4064 4056 s_q1 rfl]
  wp_steps 2
  refine SepWP.focus_weaken (Entails.of_eq (pointsTo128_sub_eq s0.sp 4064 4056 q1 rfl).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq hscr_swap_q1_q0) (by sep_focus) ?_
  rw [pointsTo128_sub_eq s0.sp 4049 4041 q0 rfl,
      pointsTo128_sub_eq s0.sp 4103 4095 d9 rfl]
  wp_steps 5
  refine SepWP.focus_weaken (Entails.of_eq (pointsTo128_sub_eq s0.sp 4049 4041 q0 rfl).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (pointsTo128_sub_eq s0.sp 4103 4095 q1 rfl).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq hdst_split_q1) (by sep_focus) ?_
  refine SepWP.focus_weaken hdst_to_q0 (by sep_focus) ?_
  wp_pull_exists; rename_i d_q0
  rw [pointsTo128_sub_eq s0.sp 4088 4080 d_q0 rfl]
  wp_steps 1
  refine SepWP.focus_weaken (Entails.of_eq (pointsTo128_sub_eq s0.sp 4088 4080 q0 rfl).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken hdst_fold_msg (by sep_focus) ?_
  refine SepWP.focus_weaken
    (src_3056_and_scratch_to_memRegion_3968 s0.sp hbs15 hbs15' sckaMsg.epoch w40 tag q1 q0)
    (by sep_focus) ?_
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals first | rfl | simp only [spqrRecvPlacedEntry, arm64_norm, *]

end CryptoVerification.SpqrV1.Top.Recv
