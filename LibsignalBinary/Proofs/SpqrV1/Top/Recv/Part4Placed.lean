/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1Placed
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WPp

/-!
# Relocatable Prologue Bridge & `decode_state` Post-Call Dispatch for `spqr::recv`

Relocatable `SepWPpLS` entry bridge (`+0..+312`) and post-`spqr::decode_state` error/success
dispatch (`+328..+408`) for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Recv.Placed

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Prologue + `msg_preamble` Entry Bridge to `SepWPpLS` (`+0 .. +312`) -/

/-- Lift `step_prologue_preamble_placed` (`+0 .. +312`) into `SepWPpLS`:
    - When `msgPreamble msg.bytes = .error e`, steps through `step_err_msgDecode_placed` (`+276..+288`) and
    `step_epilogue_placed` (`+1040..+1072`) directly to `s0.readReg64 .x30`.
    - When `msgPreamble msg.bytes = .ok pre`, steps to `spqrRecvPlacedEntry + 312#64` and invokes `hok_tail`. -/
theorem step_prologue_to_312_placed (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (P R : SepProp)
    (hpc : s0.pc = spqrRecvPlacedEntry)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = st.v)
    (hx1 : s0.readReg64 .x1 = msg.v)
    (hx8 : s0.readReg64 .x8 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt s0.sp spqrRecvStack)
    (hok_tail : ∀ (pre : MsgPreamble) (msgPtr : BitVec 64) (s1 : State) (P1 : SepProp),
      msgPreamble msg.bytes = .ok pre →
      MsgRemValid msg msgPtr pre.remaining →
      s1.pc = spqrRecvPlacedEntry + 312#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 4992#64 →
      TraceVRegs s1 s0 →
      s1.readReg64 .x0 = st.v →
      s1.readReg64 .x19 = ret →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 →
      s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
      s1.readReg64 .x24 = msgPtr →
      s1.readReg64 .x25 = pre.version.zeroExtend 64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = spqrRecvPlacedPreambleFrame A st msg ret s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s0 P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  cases hpre : msgPreamble msg.bytes with
  | error err =>
    apply SepWPpLS.of_sepWPp
    apply SepWPp.of_sepWP_ret
    refine step_prologue_preamble_placed A ext st msg ret (s0.readReg64 .x30) s0 P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R) ?_ ?_ hpc hrun hsp_align hx0 hx1 hx8 hP
    · intro s1 P1 herr hpc1 hrun1 hsp1 htr1 hx19_1 hP1
      have hrecv : (spqrV1Recv F K).recv st.bytes msg.bytes = .error false :=
        spqrV1Recv_recv_of_err (recv_of_msgPreamble_error (spqrDeps F K) (spqrHkdfWith F) herr)
      have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
        spqrV1Recv_noPanic_of_err (recv_of_msgPreamble_error (spqrDeps F K) (spqrHkdfWith F) herr)
      exact sepWP_spqrRecvPlacedPost_of_post0 hnp
        (step_err_msgDecode_placed A (spqrV1Recv F K) ext st msg ret s0 s1 P1 R
          _ rfl hrecv hpc1 hrun1 hsp1 hsp_align htr1 hx19_1 hP1)
    · intro pre' _ _ _ hok'
      rw [hpre] at hok'
      cases hok'
  | ok pre =>
    apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 312#64)
    refine step_prologue_preamble_placed A ext st msg ret
      (spqrRecvPlacedEntry + 312#64) s0 P
      (fun sm Pm =>
        SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) sm Pm
          (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
          (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R))
      ?_ ?_ hpc hrun hsp_align hx0 hx1 hx8 hP
    · intro s1 P1 herr
      rw [hpre] at herr
      cases herr
    · intro pre' msgPtr s1 P1 hok' hvalid hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1
      apply SepWP.done hpc1 hrun1
      exact hok_tail pre' msgPtr s1 P1 hok' hvalid hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1

/-! ## 2. Relocatable `spqr::decode_state` Post-Call Dispatch (`+328 .. +408`) -/

/-- When `Proto.spqrDecodeState st.bytes = .error e`, steps from `+328` (right after `bl
    spqr::decode_state`) through `+356..+380` (`b +1040`) and `step_epilogue_placed`
    (`+1040..+1072`) to `s0.readReg64 .x30`. -/
theorem step_decode_err_328_placed (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (e : LibsignalSpqrV1.Error)
    (d0 d1 d2 d3 b0 b1 b2 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .error e)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 328#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
      ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
      memRegion (s0.sp - 4960#64) 320 ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      decodeStateResultAt H_inner A (s0.sp - 3056#64) (.error e) ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ b0) ∗ ((s0.sp - 2088#64) ↦₆₄ b1) ∗ ((s0.sp - 2080#64) ↦₆₄ b2) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have ⟨hd_err, he_eq⟩ :=
    CryptoVerification.SpqrV1.Top.Send.decodeState_spqrDeps_of_spqrDecodeState_error F K hdec
  subst he_eq
  have hrecv : (spqrV1Recv F K).recv st.bytes msg.bytes = .error true :=
    spqrV1Recv_recv_of_err (recv_of_decodeState_error (spqrDeps F K) (spqrHkdfWith F) hpre hd_err)
  have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
    spqrV1Recv_noPanic_of_recv_err_true hrecv
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, decodeStateResultAt,
    DecodeState.spqrErrorTag, DecodeState.none2Cap] at hpc ⊢
  have hexp := err_payload_expose (s0.sp - 3056#64) 0#8 343 (by decide) (by decide)
  simp only [bv_sub_add_lit, Nat.reduceSub] at hexp ⊢
  refine SepWP.focus_weaken hexp (by sep_focus) ?_
  wp_pull_exists; rename_i w1 w2 w3
  wp_focus_pure; intro hw1_ent
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r3 r2 r1 r0
  wp_steps 14
  have hfold := recv_err_words_foldX A ret w1 w2 w3 0#8 true (by decide) hw1_ent
  rw [← hrecv] at hfold
  refine SepWP.fold hfold (by sep_focus) ?_
  refine SepWP.focus_weaken
    (ownFrame_join_4896_err_decode s0.sp d0 d1 d2 d3 0xFFFFFFFFFFFFFFFE#64 w1 w2 w3 w1 w2 w3)
    (by sep_focus) ?_
  subst hpost
  exact sepWP_spqrRecvPlacedPost_of_post0 hnp
    (step_epilogue_placed A (spqrV1Recv F K) ext st msg ret s0 _ _ R _ rfl
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hs0_align (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; ac_rfl))

/-- When `Proto.spqrDecodeState st.bytes = .ok pre_pb`, steps from `+328` (right after `bl
    spqr::decode_state`) through `+352` (`b.ne +384`) and `+384..+404` (`bl memcpy` of `320`B)
    to `+408`. -/
theorem step_decode_ok_328_to_408_placed {F : ShaCompress} {K : MlKem}
    (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState)
    (d0 d1 d2 d3 b0 b1 b2 : BitVec 64)
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 328#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = s0.sp - 3056#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
      ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
      memRegion (s0.sp - 4960#64) 320 ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      decodeStateResultAt H_inner A (s0.sp - 3056#64) (.ok pre_pb) ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ b0) ∗ ((s0.sp - 2088#64) ↦₆₄ b1) ∗ ((s0.sp - 2080#64) ↦₆₄ b2) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (htail : ∀ (w0 w1 w2 w3 : BitVec 64) (bs96 : List (BitVec 8)) (sm : State) (Pm : SepProp),
      w0 ≠ DecodeState.none2Cap →
      bs96.length = 96 →
      sm.pc = spqrRecvPlacedEntry + 408#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 4992#64 →
      TraceVRegs sm s0 →
      sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = w0 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s0.sp - 3056#64 →
      sm.readReg64 .x28 = s0.sp - 4288#64 →
      sm.readReg64 .x29 = s.readReg64 .x29 →
      Pm = (spqrRecvRoPlacedAt ∗
        st.at A ∗
        msg.at A ∗
        memRegion ret 48 ∗
        A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
        ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
        ((s0.sp - 4960#64) ↦ₛ bs96) ∗
        (relocVnTailAndChainAt A w0 w1 pre_pb).1 (unpack64 w2 ++ unpack64 w3 ++ bs96) ∗
        Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
        ((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗
        (∃∗ P_tail : SepProp,
          ⌜((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗ P_tail ⊢
            memRegion (s0.sp - 4640#64) 4544⌝ ∗ P_tail) ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWP (spqrRecvPlacedProg ext) (spqrRecvPlacedEntry + 408#64) sm Pm post) :
    SepWP (spqrRecvPlacedProg ext) (spqrRecvPlacedEntry + 408#64) s P post := by
  have hmemcpy_raw := hC.memcpy_ok
  simp only [framelessMemcpySpec] at hmemcpy_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, decodeStateResultAt,
    BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc htail ⊢
  have hsplit := protoPqRatchetStateAt_entails_head32_bs96_bs224 H_inner A (s0.sp - 3056#64) pre_pb
  rw [bv_sub_add_lit s0.sp 3056 8, bv_sub_add_lit s0.sp 3056 16,
      bv_sub_add_lit s0.sp 3056 24, bv_sub_add_lit s0.sp 3056 32] at hsplit
  refine SepWP.focus_weaken hsplit (by sep_focus) ?_
  wp_pull_exists; rename_i w0 w1 w2 w3 bs96 bs224
  wp_focus_pure; rintro ⟨hw0_ne, hbs96, hbs224, hbs320⟩
  have hw0_cmn : (w0 + 2#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    apply hw0_ne
    change w0 = -2#64
    revert w0 heq; bv_kernel
  have hlen_lt : (bs96 ++ bs224).length < 2 ^ 64 := by rw [hbs320]; decide
  have hlen_eq : (320#64 : BitVec 64).toNat = (bs96 ++ bs224).length := hbs320.symm
  have hdst_eq : memRegion (s0.sp - 4960#64) (bs96 ++ bs224).length =
      memRegion (s0.sp - 4960#64) 320 := by rw [hbs320]
  rw [← hdst_eq]
  wp_steps 13
  wp_call hmemcpy_raw ⟨s0.sp - 4960#64, s0.sp - 3024#64, bs96 ++ bs224⟩
  have hbs_inner := bs320_entails_bs96_inner H_inner A (s0.sp - 4992#64) bs96 bs224 pre_pb hbs96 hbs224
  rw [bv_sub_add_lit s0.sp 4992 32, bv_sub_add_lit s0.sp 4992 128,
      optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at hbs_inner
  refine SepWP.focus_weaken hbs_inner (by sep_focus) ?_
  let P_tail : SepProp :=
    memRegion (s0.sp - 4640#64) 1584 ∗
      ((s0.sp - 3056#64) ↦₆₄ w0) ∗ ((s0.sp - 3048#64) ↦₆₄ w1) ∗
      ((s0.sp - 3040#64) ↦₆₄ w2) ∗ ((s0.sp - 3032#64) ↦₆₄ w3) ∗
      ((s0.sp - 3024#64) ↦ₛ (bs96 ++ bs224)) ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      memRegion (s0.sp - 2072#64) 1976
  have hP_tail_join :
      ((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗ P_tail ⊢
        memRegion (s0.sp - 4640#64) 4544 := by
    refine Entails.trans (Entails.of_eq ?_)
      (ownFrame_join_4544_after_decode s0.sp w0 w1 w2 w3 w1 w2 w3 (bs96 ++ bs224) hbs320)
    unfold P_tail; ac_rfl
  have hP_tail_intro :
      P_tail ⊢
        ∃∗ P_t : SepProp,
          ⌜((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗ P_t ⊢
            memRegion (s0.sp - 4640#64) 4544⌝ ∗ P_t :=
    Entails.sepExists_right P_tail (Entails.pure_right hP_tail_join (Entails.refl _))
  refine SepWP.focus_weaken hP_tail_intro (by unfold P_tail; sep_focus) ?_
  exact htail w0 w1 w2 w3 bs96 _ _ hw0_ne hbs96
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv
