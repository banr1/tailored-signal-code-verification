/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1Placed
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet2
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet2Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WPp

/-!
# Relocatable V1 Ratchet First-Half Composition (`+1532..+1856`) for `spqr::recv`

Composes `<Message>::deserialize`, `<States>::from_pb`, and `<States>::recv` (`+1532..+1856`)
in `SepWPpLS` for `spqr::recv` (Block `329`) under `[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.ChainProofs CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Recv.Placed

variable [LibsignalPlacement]

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  Prost.EncodeToVec.extractLsb_lo_append64 Prost.EncodeToVec.extractLsb_hi_append64
  hsp_add_544_eq hsp_add_560_eq

omit [LibsignalPlacement] in
private theorem traceVRegs_trans {s0 s1 s2 : State}
    (h1 : TraceVRegs s2 s1) (h0 : TraceVRegs s1 s0) : TraceVRegs s2 s0 :=
  ⟨h1.1.trans h0.1, h1.2.trans h0.2⟩

/-! ## 1. `<Message>::deserialize` Call, Error Path (`+2060`), and Relocation (`+1568..+1636`) -/

/-- Steps from `+1532` (`spqrRecvPlacedEntry + 1532#64`) through `bl <Message>::deserialize`, branching on
    `Message.deserialize spqrPolyApi pre.epoch pre.remaining`:
    - `.error err`: steps through `+1556..+1564 -> +2060..+2104 -> +2500 -> +1040 -> s0.lr`,
    - `.ok sckaMsg`: relocates `sckaMsg` (`48`B) to `s0.sp - 4112#64` (`sp + 0x370`) and reaches
    `+1636` (`spqrRecvPlacedEntry + 1636#64`). -/
theorem step_msgDeserialize_1532_placed {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1532#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length) (hx24 : s.readReg64 .x24 = remPtr)
    (hx26 : s.readReg64 .x26 = 0#64) (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      Drop.optProtoInnerStateAt A (s0.sp - 4512#64) pb.innerState ∗
      memRegion (s0.sp - 4288#64) 4192 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hok_tail : ∀ (sckaMsg : Message spqrPolyApi) (s1 : State) (P1 : SepProp),
      Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
      s1.pc = spqrRecvPlacedEntry + 1636#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 4512#64 → s1.readReg64 .x8 = s0.sp - 2096#64 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x24 = s0.sp - 2096#64 → s1.readReg64 .x25 = s0.sp - 4640#64 →
      s1.readReg64 .x26 = 0#64 → s1.readReg64 .x27 = s0.sp - 3056#64 →
      s1.readReg64 .x28 = s0.sp - 4288#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
        Drop.optProtoInnerStateAt A (s0.sp - 4512#64) pb.innerState ∗
        memRegion (s0.sp - 4288#64) 176 ∗ messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 3968 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hmd_call := hC.messageDeserialize_ok
  subst hP
  refine SepWPpLS.focus_weaken (msg_expose_rem_bound A msg remPtr pre.remaining hvalid) (by sep_focus) ?_
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro hrem_lt
  refine SepWPpLS.focus_weaken (memRegion_split_4288_for_1532 s0.sp) (by sep_focus) ?_
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 351)
  refine SepWP.mono
    (step_pre_msgDeserialize_1532_placed ext s0 s pre remPtr _ hs0_align hpc hrun hsp hx22 hx23 hx24) ?_
  intro sc P_sc hpc_sc hrun_sc ⟨hP_sc, hsp_sc, htr_sc, hx0_sc, hx1_sc, hx2_sc, hx3_sc,
    hx19_sc, hx20_sc, hx21_sc, hx22_sc, hx23_sc, hx24_sc, hx25_sc, hx26_sc, hx27_sc, hx28_sc, hx29_sc, hx30_sc⟩
  subst hP_sc
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) messageDeserializeStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hmd_call ⟨s0.sp - 3056#64, pre.epoch, remPtr, pre.remaining⟩
    hpc_sc hrun_sc
    (by simp only [State.spAligned, hsp_sc]; exact sp_sub_4992_aligned s0 hs0_align)
    hx30_sc (by rw [htr_sc.1, htr.1]) (fun _ => onPanic_of_allocFailed) (fun _ _ => rfl)
    (by
      dsimp only [messageDeserializeSpecX]
      refine frame_pure_pre ⟨hx0_sc, hx1_sc, hx2_sc, hx3_sc, hrem_lt⟩ (by rw [hsp_sc]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hxfp_c, hvregs_c⟩
  dsimp only [messageDeserializeSpecX]
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm, htr_sc.1, htr.1], by rw [hvregs_c, htr_sc.2, htr.2]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm, hsp_sc]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c, hx19_sc, hx19]
  have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c, hx20_sc, hx20]
  have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c, hx21_sc, hx21]
  have hx22_sm : sm.readReg64 .x22 = pre.epoch := by rw [hx22_c, hx22_sc]
  have hx23_sm : sm.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length := by rw [hx23_c, hx23_sc]
  have hx24_sm : sm.readReg64 .x24 = remPtr := by rw [hx24_c, hx24_sc]
  have hx25_sm : sm.readReg64 .x25 = s0.sp - 4640#64 := by rw [hx25_c, hx25_sc]
  have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c, hx26_sc, hx26]
  have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c, hx27_sc, hx27]
  have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by rw [hx28_c, hx28_sc, hx28]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64
    rw [hxfp_c]; exact hx29_sc.trans hx29
  rw [hsp_sc]
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) messageDeserializeStackX (by decide)).symm)
    (by sep_focus) ?_
  refine SepWPpLS.focus_weaken (msg_unexpose_rem A msg remPtr pre.remaining) (by sep_focus) ?_
  cases hmd : Message.deserialize spqrPolyApi pre.epoch pre.remaining with
  | error err =>
    dsimp only [messageResultAt]
    apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
    refine SepWP.focus_weaken (messageErrorAt_sub3056_expose s0.sp err) (by sep_focus) ?_
    wp_pull_exists; rename_i q0_err w2_err
    wp_focus_pure; intro htag_err
    let Rest_err : SepProp :=
      memRegion (s0.sp - 3056#64) 8 ∗ memRegion (s0.sp - 3047#64) 7 ∗
      ((s0.sp - 3040#64) ↦₁₂₈ q0_err) ∗ ((s0.sp - 3024#64) ↦₆₄ w2_err) ∗
      memRegion (s0.sp - 3016#64) 8 ∗ msg.at A ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ A.pool ∗
      memRegion (s0.sp - 4288#64) 1232 ∗ memRegion (s0.sp - 3008#64) 2912 ∗
      spqrRecvRoPlacedAt ∗ st.at A ∗ memRegion ret 48 ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      Drop.optProtoInnerStateAt A (s0.sp - 4512#64) pb.innerState ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0
    refine SepWP.weaken_pre
      (Entails.of_eq (show _ = ((s0.sp - 3048#64) ↦₈ 0xff#8) ∗ Rest_err by dsimp only [Rest_err]; ac_rfl)) ?_
    refine sepWP_seq_lscl hcl (SepWP.mono
      (step_post_msgDeserialize_err_1556_placed ext s0 sm Rest_err hs0_align hpcm hrunm hspm') ?_)
    intro s_err P_err hpc_err hrun_err ⟨hP_err, hsp_err, hx19_err, hx25_err, hx26_err, htr_err⟩ hcl_err
    subst hP_err
    refine sepWP_spqrRecvPlacedPost_of_post0
      (spqrV1Recv_v1_msgDeserialize_err F K hpre hdec hinner hmv hmin hmd).2 ?_
    exact step_msgDeserialize_err_2060_placed A F K ext hC st msg ret
      pre pre_pb pb w0 w1 err q0_err w2_err hpre hdec hinner hmv hmin hmd htag_err
      s0 s_err _ R _ rfl hs0_align hpc_err hrun_err hsp_err (traceVRegs_trans htr_err htr_sm')
      (hx19_err.trans hx19_sm) (hx25_err.trans hx25_sm) (hx26_err.trans hx26_sm)
      (by dsimp only [Rest_err]; ac_rfl) hcl_err
  | ok sckaMsg =>
    dsimp only [messageResultAt]
    have hexp_msg := messageAt_expose_bytes39 spqrPolyApi (s0.sp - 3056#64) sckaMsg
    rw [bv_sub_add_lit s0.sp 3056 8, bv_sub_add_lit s0.sp 3056 9] at hexp_msg
    simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hexp_msg
    let s0_1636 := s0.writeReg64 .x30 (spqrRecvPlacedEntry + 1636#64)
    have hs0_1636_sp : s0_1636.sp = s0.sp := rfl
    apply SepWPpLS.of_sepWP
      (mid := spqrRecvPlacedEntry + 1636#64)
    refine SepWP.focus_weaken hexp_msg (by sep_focus) ?_
    wp_pull_exists; rename_i tag bs39
    wp_focus_pure; rintro ⟨htag_ne, hbs39, hfold_msg⟩
    let F_rest : SepProp :=
      spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      Drop.optProtoInnerStateAt A (s0.sp - 4512#64) pb.innerState ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0
    let Rest_1556 : SepProp :=
      memRegion (s0.sp - 4288#64) 1232 ∗ ((s0.sp - 3056#64) ↦₆₄ sckaMsg.epoch) ∗
      ((s0.sp - 3047#64) ↦ₛ bs39) ∗ memRegion (s0.sp - 3008#64) 2912 ∗ F_rest
    refine SepWP.weaken_pre
      (Entails.of_eq (show _ = ((s0.sp - 3048#64) ↦₈ tag) ∗ Rest_1556 by dsimp only [Rest_1556, F_rest]; ac_rfl)) ?_
    refine step_post_msgDeserialize_ok_1556_placed ext s0_1636 sm tag Rest_1556 hs0_align hpcm hrunm hspm' htag_ne ?_
    intro s_ok hpc_ok hrun_ok hsp_ok htr_ok hx8_ok hx19_ok hx20_ok hx21_ok hx22_ok hx25_ok hx26_ok hx27_ok hx28_ok hx29_ok
    refine step_msg_relocate_1568_placed ext sckaMsg tag bs39 hbs39 hfold_msg s0_1636 s_ok _ F_rest _
      hs0_align hpc_ok hrun_ok hsp_ok hx8_ok (hx25_ok.trans hx25_sm) (hx27_ok.trans hx27_sm)
      (by simp only [hs0_1636_sp, Rest_1556, F_rest]; ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply ProofLib.SepWP.done hpc1 hrun1
    exact hok_tail sckaMsg s1 _ hmd hpc1 hrun1 hsp1 (traceVRegs_trans htr1 (traceVRegs_trans htr_ok htr_sm'))
      hx0_1 hx8_1
      (hx19_1.trans (hx19_ok.trans hx19_sm)) (hx20_1.trans (hx20_ok.trans hx20_sm))
      (hx21_1.trans (hx21_ok.trans hx21_sm)) (hx22_1.trans (hx22_ok.trans hx22_sm))
      hx24_1 hx25_1 (hx26_1.trans (hx26_ok.trans hx26_sm)) hx27_1
      (hx28_1.trans (hx28_ok.trans hx28_sm)) (hx29_1.trans (hx29_ok.trans hx29_sm))
      (by simp only [hs0_1636_sp, F_rest]; ac_rfl)

/-! ## 2. `<States>::from_pb` Call, Error Path (`+2144 -> +2492`), and Relocation (`+1640..+1736`) -/

/-- Pre-call step `+1636 -> lsmpl.base 333`: executes `bl <States>::from_pb`, setting `x30 =
    spqrRecvPlacedEntry + 1640#64`. -/
theorem step_pre_statesFromPb_1636_placed (ext : String → Option (State → State))
    (s0 s : State) (P : SepProp)
    (hpc : s.pc = spqrRecvPlacedEntry + 1636#64)
    (hrun : s.status = .Running) :
    SepWP (spqrRecvPlacedProg ext) (lsmpl.base 333) s P
      (fun sf Pf =>
        Pf = P ∧ sf.sp = s.sp ∧ TraceVRegs sf s ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = spqrRecvPlacedEntry + 1640#64) := by
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  exact ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      by simp only [arm64_norm, *]⟩

/-- Error branch after `<States>::from_pb` returns `.error (.err err)` at `+1640 .. +1668 ->
    +2144 .. +2160 -> +2492 .. +2500`: writes `err` to `ret`, joins the `4416`B scratch frame at
    `s0.sp - 4512#64`, and finishes via `step_drop_vn_chain_2500_placed`. -/
theorem step_post_statesFromPb_err_1640_placed {H_inner : V1InnerHeapPred}
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi) (err : Error)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .error (.err err))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx26 : s.readReg64 .x26 = 0#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 1968 ∗
      resultChunkedStatesAt A (F := F) (s0.sp - 2096#64) (.error (.err err)) ∗
      memRegion (s0.sp - 1168#64) 1072 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have hfp : s.readReg64 .fp = s0.sp - 96#64 := hx29
  subst hP
  have hexp_err := resultChunkedStatesAt_err_expose A (F := F) (s0.sp - 2096#64) err
  rw [bv_sub_add_lit s0.sp 2096 8, bv_sub_add_lit s0.sp 2096 16,
      bv_sub_add_lit s0.sp 2096 24, bv_sub_add_lit s0.sp 2096 32] at hexp_err
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hexp_err
  refine SepWP.focus_weaken hexp_err (by sep_focus) ?_
  wp_pull_exists; rename_i w1_err w2_err w3_err
  wp_focus_pure; intro hw1_err
  refine SepWP.focus_weaken (memRegion_1168_split_statesFromPb s0.sp) (by sep_focus) ?_
  have h24_fp := memRegion_24_words3 (s0.sp - 144#64)
  rw [bv_sub_add_lit s0.sp 144 8, bv_sub_add_lit s0.sp 144 16] at h24_fp
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24_fp
  refine SepWP.focus_weaken (Entails.of_eq h24_fp) (by sep_focus) ?_
  wp_pull_exists; rename_i f2 f1 f0
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r3 r2 r1 r0
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  apply sepWP_seq_lscl hcl
  wp_steps 15
  refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
  refine SepWP.focus_weaken (hw1_err ret) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (recv_err_byte_foldX A ret w2_err w3_err (States.FromPb.spqrErrorByte err) (err == .stateDecode) (spqrErrorByte_eq_zero_iff hst0))
    (by sep_focus) ?_
  have hres_eq : recvResultExactKeyAt A ret (.error (err == .stateDecode)) =
      recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [(spqrV1Recv_v1_statesFromPb_err F K hpre hdec hinner hmv hmin hmsg hst0).1]
  rw [hres_eq]
  refine SepWP.focus_weaken (memRegion_4416_join_statesFromPb_err s0.sp w1_err w2_err w3_err sckaMsg) (by sep_focus) ?_
  exact step_drop_vn_chain_2500_placed A (spqrV1Recv F K) ext hC st msg ret pre_pb w0 w1 s0 _ _ R post
    hpost hs0_align
    (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl) hcl1

/-- Ok branch after `<States>::from_pb` returns `.ok st0` at `+1640 .. +1736`: relocates `st0`
    (`928`B) from `s0.sp - 2096#64` (`sp + 0xb50`) to `s0.sp - 1160#64` (`sp + 0xef8`) via
    `memcpy` (`896`B) and header copy (`32`B), and sets up registers for `<States>::recv` at
    `+1736`. -/
theorem step_post_statesFromPb_ok_1640_placed {H_inner : V1InnerHeapPred}
    (A : RustAlloc) (F : ShaCompress) {K : MlKem}
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
    (s0 s : State) (P F_rest : SepProp) (post : State → SepProp → Prop)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 2096#64) (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx26 : s.readReg64 .x26 = 0#64) (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4064#64) 1968 ∗
      chunkedStatesAt A (s0.sp - 2096#64) st0 ∗
      memRegion (s0.sp - 1168#64) 1072 ∗ F_rest)
    (hnext : ∀ s1 : State,
      s1.pc = spqrRecvPlacedEntry + 1736#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 1160#64 →
      s1.readReg64 .x2 = s0.sp - 4112#64 → s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 → s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 → s1.readReg64 .x24 = s0.sp - 3056#64 →
      s1.readReg64 .x25 = s0.sp - 4640#64 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1
        (stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          memRegion (s0.sp - 4064#64) 2896 ∗ memRegion (s0.sp - 1168#64) 8 ∗
          chunkedStatesAt A (s0.sp - 1160#64) st0 ∗
          memRegion (s0.sp - 232#64) 136 ∗ F_rest) post) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy := hC.memcpy_ok
  simp only [framelessMemcpySpec] at hmemcpy
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have hfp : s.readReg64 .fp = s0.sp - 96#64 := hx29
  subst hP
  have hreloc := chunkedStatesAt_entails_reloc_words A (s0.sp - 2096#64) st0
  rw [bv_sub_add_lit s0.sp 2096 8, bv_sub_add_lit s0.sp 2096 16,
      bv_sub_add_lit s0.sp 2096 24, bv_sub_add_lit s0.sp 2096 32] at hreloc
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hreloc
  refine SepWP.focus_weaken hreloc (by sep_focus) ?_
  wp_pull_exists; rename_i bs w1_st w2_st w3_st bs896
  wp_focus_pure; rintro ⟨hbs, hbs896⟩
  refine SepWP.focus_weaken (memRegion_1168_split_statesFromPb s0.sp) (by sep_focus) ?_
  have h928_dst := memRegion_928_split_header32_body896 (s0.sp - 1160#64)
  rw [bv_sub_add_lit s0.sp 1160 8, bv_sub_add_lit s0.sp 1160 16,
      bv_sub_add_lit s0.sp 1160 24, bv_sub_add_lit s0.sp 1160 32] at h928_dst
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h928_dst
  refine SepWP.focus_weaken h928_dst (by sep_focus) ?_
  wp_pull_exists; rename_i d0 d1 d2 d3
  have h24_fp := memRegion_24_words3 (s0.sp - 144#64)
  rw [bv_sub_add_lit s0.sp 144 8, bv_sub_add_lit s0.sp 144 16] at h24_fp
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24_fp
  refine SepWP.focus_weaken (Entails.of_eq h24_fp) (by sep_focus) ?_
  wp_pull_exists; rename_i f2 f1 f0
  have h896_dst : memRegion (s0.sp - 1128#64) 896 = memRegion (s0.sp - 1128#64) bs896.length := by
    rw [hbs896]
  rw [h896_dst]
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hmemcpy hpc hnext ⊢
  wp_steps 15
  wp_call hmemcpy ⟨s0.sp - 1128#64, s0.sp - 2064#64, bs896⟩
  wp_steps 9
  have hreassemble_dst := reassemble_chunkedStatesAt_words A (s0.sp - 1160#64) st0 w1_st w2_st w3_st hbs
  rw [bv_sub_add_lit s0.sp 1160 8, bv_sub_add_lit s0.sp 1160 16,
      bv_sub_add_lit s0.sp 1160 24, bv_sub_add_lit s0.sp 1160 32] at hreassemble_dst
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hreassemble_dst
  refine SepWP.focus_weaken hreassemble_dst (by sep_focus) ?_
  have hreassemble_src := reassemble_src_928_after_memcpy (s0.sp - 2096#64) (chunkedStatesWord0 st0) w1_st w2_st w3_st hbs896
  rw [bv_sub_add_lit s0.sp 2096 8, bv_sub_add_lit s0.sp 2096 16,
      bv_sub_add_lit s0.sp 2096 24, bv_sub_add_lit s0.sp 2096 32] at hreassemble_src
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hreassemble_src
  refine SepWP.focus_weaken hreassemble_src (by sep_focus) ?_
  refine SepWP.focus_weaken (memRegion_4064_join_1968_928 s0.sp) (by sep_focus) ?_
  refine SepWP.focus_weaken (memRegion_136_join_fp_spill s0.sp w1_st w2_st w3_st) (by sep_focus) ?_
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals first | rfl | simp only [arm64_norm, *]

/-- Steps from `+1636` (`spqrRecvPlacedEntry + 1636#64`) through `bl <States>::from_pb`, branching on
    `States.from_pb spqrPolyApi (spqrAuthApi F) pb`:
    - `.error (.err err)`: steps through `+1640..+1668 -> +2144..+2160 -> +2492..+2500 -> +1040 -> s0.lr`,
    - `.ok st0`: relocates `st0` (`928`B) to `s0.sp - 1160#64` (`sp + 0xef8`) and reaches `+1736` (`spqrRecvPlacedEntry + 1736#64`). -/
theorem step_statesFromPb_1636_placed {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (hpts : v1StatePtsBound pb)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1636#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 4512#64) (hx8 : s.readReg64 .x8 = s0.sp - 2096#64)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx24 : s.readReg64 .x24 = s0.sp - 2096#64) (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx26 : s.readReg64 .x26 = 0#64) (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      Drop.optProtoInnerStateAt A (s0.sp - 4512#64) pb.innerState ∗
      memRegion (s0.sp - 4288#64) 176 ∗ messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 3968 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hok_tail : ∀ (st0 : States spqrPolyApi (spqrAuthApi F)) (s1 : State) (P1 : SepProp),
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      s1.pc = spqrRecvPlacedEntry + 1736#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 1160#64 →
      s1.readReg64 .x2 = s0.sp - 4112#64 → s1.readReg64 .x19 = ret →
      s1.readReg64 .x20 = w0 → s1.readReg64 .x21 = pre.index.zeroExtend 64 →
      s1.readReg64 .x22 = pre.epoch → s1.readReg64 .x24 = s0.sp - 3056#64 →
      s1.readReg64 .x25 = s0.sp - 4640#64 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 2896 ∗ memRegion (s0.sp - 1168#64) 8 ∗
        chunkedStatesAt A (s0.sp - 1160#64) st0 ∗
        memRegion (s0.sp - 232#64) 136 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hfrom_call := hC.statesFromPb_ok
  subst hP
  refine SepWPpLS.focus_weaken (memRegion_4064_split_2096 s0.sp) (by sep_focus) ?_
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 333)
  refine SepWP.mono (step_pre_statesFromPb_1636_placed ext s0 s _ hpc hrun) ?_
  intro sc P_sc hpc_sc hrun_sc ⟨hP_sc, hsp_sc, htr_sc, hx0_sc, hx8_sc,
    hx19_sc, hx20_sc, hx21_sc, hx22_sc, hx24_sc, hx25_sc, hx26_sc, hx27_sc, _, hx29_sc, hx30_sc⟩
  subst hP_sc
  unfold spqrRecvRoPlacedAt
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesFromPbStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hfrom_call ⟨s0.sp - 2096#64, s0.sp - 4512#64, pb⟩
    hpc_sc hrun_sc
    (by simp only [State.spAligned, hsp_sc, hsp]; exact sp_sub_4992_aligned s0 hs0_align)
    hx30_sc (by rw [htr_sc.1, htr.1]) (fun _ => onPanic_of_allocFailed) (fun _ _ => rfl)
    (by
      dsimp only [statesFromPbPlacedSpecX]
      refine frame_pure_pre ⟨hx8_sc.trans hx8, hx0_sc.trans hx0, hpts⟩
        (by rw [hsp_sc, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, _, hx24_c, hx25_c, hx26_c, hx27_c, _, hxfp_c, hvregs_c⟩
  dsimp only [statesFromPbPlacedSpecX]
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm, htr_sc.1, htr.1], by rw [hvregs_c, htr_sc.2, htr.2]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm, hsp_sc, hsp]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c, hx19_sc, hx19]
  have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c, hx20_sc, hx20]
  have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c, hx21_sc, hx21]
  have hx22_sm : sm.readReg64 .x22 = pre.epoch := by rw [hx22_c, hx22_sc, hx22]
  have hx24_sm : sm.readReg64 .x24 = s0.sp - 2096#64 := by rw [hx24_c, hx24_sc, hx24]
  have hx25_sm : sm.readReg64 .x25 = s0.sp - 4640#64 := by rw [hx25_c, hx25_sc, hx25]
  have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c, hx26_sc, hx26]
  have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c, hx27_sc, hx27]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64
    rw [hxfp_c]; exact hx29_sc.trans hx29
  rw [hsp_sc, hsp]
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesFromPbStackX (by decide)).symm)
    (by sep_focus) ?_
  have hro_fold :
      Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        statesFromPbJumpTablePlacedAt ∗
        statesRecvRoPlacedAt ∗
        statesIntoPbJumpTablePlacedAt ⊢
      spqrRecvRoPlacedAt := Entails.refl _
  refine SepWPpLS.focus_weaken hro_fold (by sep_focus) ?_
  cases hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb with
  | error se =>
    cases se with
    | panic p =>
      rw [resultChunkedStatesAt_panic_false]
      refine SepWPpLS.focus_pure (by sep_focus) False.elim
    | err err =>
      apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
      refine sepWP_spqrRecvPlacedPost_of_post0
        (spqrV1Recv_v1_statesFromPb_err F K hpre hdec hinner hmv hmin hmsg hfrom).2 ?_
      exact step_post_statesFromPb_err_1640_placed A F K ext hC st msg ret
        pre pre_pb pb w0 w1 sckaMsg err hpre hdec hinner hmv hmin hmsg hfrom
        s0 sm _ R _ rfl hs0_align hpcm hrunm hspm' htr_sm' hx19_sm hx25_sm hx26_sm hx29_sm
        (by ac_rfl) hcl
  | ok st0 =>
    dsimp only [resultChunkedStatesAt]
    let s0_1736 := s0.writeReg64 .x30 (spqrRecvPlacedEntry + 1736#64)
    have hs0_1736_sp : s0_1736.sp = s0.sp := rfl
    apply SepWPpLS.of_sepWP
      (mid := spqrRecvPlacedEntry + 1736#64)
    let F_rest : SepProp :=
      spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      memRegion (s0.sp - 4992#64) 352 ∗ ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0
    refine step_post_statesFromPb_ok_1640_placed A F ext hC sckaMsg st0 s0_1736 sm _ F_rest _
      hs0_align hpcm hrunm hspm' hx24_sm hx25_sm hx26_sm hx27_sm hx29_sm
      (by simp only [hs0_1736_sp, F_rest]; ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply ProofLib.SepWP.done hpc1 hrun1
    exact hok_tail st0 s1 _ hfrom hpc1 hrun1 hsp1 (traceVRegs_trans htr1 htr_sm')
      hx0_1 hx1_1 hx2_1
      (hx19_1.trans hx19_sm) (hx20_1.trans hx20_sm)
      (hx21_1.trans hx21_sm) (hx22_1.trans hx22_sm)
      hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      (by simp only [hs0_1736_sp, F_rest]; ac_rfl)

/-! ## 3. `<States>::recv` Call, Error Path (`+2472 -> +2500`), and Relocation (`+1736..+1856`) -/

/-- Pre-call step `+1736 -> lsmpl.base 332`: executes `bl <States>::recv`, setting `x30 =
    spqrRecvPlacedEntry + 1740#64`. -/
theorem step_pre_statesRecv_1736_placed (ext : String → Option (State → State))
    (s0 s : State) (P : SepProp)
    (hpc : s.pc = spqrRecvPlacedEntry + 1736#64)
    (hrun : s.status = .Running) :
    SepWP (spqrRecvPlacedProg ext) (lsmpl.base 332) s P
      (fun sf Pf =>
        Pf = P ∧ sf.sp = s.sp ∧ TraceVRegs sf s ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x2 = s.readReg64 .x2 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = spqrRecvPlacedEntry + 1740#64) := by
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  exact ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      by simp only [arm64_norm, *]⟩

/-- Error branch after `<States>::recv` returns `.error (.err err)` at `+1740 .. +1764 -> +2472
    .. +2500`: writes `err` to `ret`, sets `x26 = 0`, joins the `4416`B scratch frame at `s0.sp
    - 4512#64`, and finishes via `step_drop_vn_chain_2500_placed`. -/
theorem step_post_statesRecv_err_1740_placed {H_inner : V1InnerHeapPred}
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F)) (err : Error)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .error (.err err))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1740#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗ memRegion (s0.sp - 4032#64) 16 ∗
      memRegion (s0.sp - 4016#64) 928 ∗ memRegion (s0.sp - 3088#64) 24 ∗
      memRegion (s0.sp - 3064#64) 8 ∗
      resultV1RecvAt A (F := F) (s0.sp - 3056#64) (.error (.err err)) ∗
      memRegion (s0.sp - 2096#64) 928 ∗ memRegion (s0.sp - 1168#64) 8 ∗
      memRegion (s0.sp - 1160#64) 928 ∗ memRegion (s0.sp - 232#64) 136 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  have hexp_err := resultV1RecvAt_err_expose A (F := F) (s0.sp - 3056#64) err
  rw [bv_sub_add_lit s0.sp 3056 8, bv_sub_add_lit s0.sp 3056 16,
      bv_sub_add_lit s0.sp 3056 24, bv_sub_add_lit s0.sp 3056 32] at hexp_err
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hexp_err
  refine SepWP.focus_weaken hexp_err (by sep_focus) ?_
  wp_pull_exists; rename_i w1_err w2_err w3_err
  wp_focus_pure; intro hw1_err
  have h24_scr := memRegion_24_words3 (s0.sp - 3088#64)
  rw [bv_sub_add_lit s0.sp 3088 8, bv_sub_add_lit s0.sp 3088 16] at h24_scr
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24_scr
  refine SepWP.focus_weaken (Entails.of_eq h24_scr) (by sep_focus) ?_
  wp_pull_exists; rename_i f2 f1 f0
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r3 r2 r1 r0
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  apply sepWP_seq_lscl hcl
  wp_steps 14
  refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
  refine SepWP.focus_weaken (hw1_err ret) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (recv_err_byte_foldX A ret w2_err w3_err (States.RecvCt2Chunk.spqrErrorByte err)
      (err == .stateDecode) (recvCt2_spqrErrorByte_eq_zero_iff err))
    (by sep_focus) ?_
  have hres_eq : recvResultExactKeyAt A ret (.error (err == .stateDecode)) =
      recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [(spqrV1Recv_v1_statesRecv_err F K hpre hdec hinner hmv hmin hmsg hst0 hrecv).1]
  rw [hres_eq]
  refine SepWP.focus_weaken (memRegion_4416_join_statesRecv_err s0.sp w1_err w2_err w3_err sckaMsg) (by sep_focus) ?_
  exact step_drop_vn_chain_2500_placed A (spqrV1Recv F K) ext hC st msg ret pre_pb w0 w1 s0 _ _ R post
    hpost hs0_align
    (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl) hcl1

/-- Ok branch after `<States>::recv` returns `.ok v` at `+1740 .. +1856`: relocates `v.state`
    (`928`B) from `s0.sp - 3056#64` to `s0.sp - 4016#64` (`sp + 976`), moves `v.key` (`32`B) to
    `(x24, x25, [sp + 960 .. + 976])`, checks `cbz x22` (`pre.epoch != 0`), loads `w0` from
    `[sp, #352]`, and sets up `x0, x1, x2` for `spqr::chain_from` at `+1856`. -/
theorem step_post_statesRecv_ok_1740_placed {H_inner : V1InnerHeapPred}
    (A : RustAlloc) (F : ShaCompress) {K : MlKem}
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (pre : MsgPreamble) (w0 : BitVec 64)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (hep0 : (pre.epoch == 0#64) = false)
    (s0 s : State) (P F_rest : SepProp) (post : State → SepProp → Prop)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1740#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64)
    (hx22 : s.readReg64 .x22 = pre.epoch) (hx24 : s.readReg64 .x24 = s0.sp - 3056#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hP : P =
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      memRegion (s0.sp - 4032#64) 16 ∗ memRegion (s0.sp - 4016#64) 928 ∗
      memRegion (s0.sp - 3088#64) 24 ∗ memRegion (s0.sp - 3064#64) 8 ∗
      resultV1RecvAt A (F := F) (s0.sp - 3056#64) (.ok v) ∗
      memRegion (s0.sp - 2096#64) 928 ∗ memRegion (s0.sp - 1168#64) 8 ∗
      memRegion (s0.sp - 1160#64) 928 ∗ memRegion (s0.sp - 232#64) 136 ∗ F_rest)
    (hnext : ∀ (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp) (s1 : State),
      (∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          States.Recv.optEpochSecretAt A dst v.key) →
      s1.pc = spqrRecvPlacedEntry + 1856#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 4592#64 →
      s1.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1
        (stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          ((s0.sp - 4640#64) ↦₆₄ w0) ∗
          ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
          chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
          memRegion (s0.sp - 3088#64) 2992 ∗ F_rest) post) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy := hC.memcpy_ok
  simp only [framelessMemcpySpec] at hmemcpy
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [resultV1RecvAt, v1RecvAt]
  rw [sp_sub_3056_add_928 s0.sp]
  have hreloc := chunkedStatesAt_entails_reloc_words A (s0.sp - 3056#64) v.state
  rw [bv_sub_add_lit s0.sp 3056 8, bv_sub_add_lit s0.sp 3056 16,
      bv_sub_add_lit s0.sp 3056 24, bv_sub_add_lit s0.sp 3056 32] at hreloc
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hreloc
  refine SepWP.focus_weaken hreloc (by sep_focus) ?_
  wp_pull_exists; rename_i bs w1_st w2_st w3_st bs896
  wp_focus_pure; rintro ⟨hbs, hbs896⟩
  have hexp_key := optEpochSecretAt_expose_words A (s0.sp - 2128#64) v.key
  rw [bv_sub_add_lit s0.sp 2128 8, bv_sub_add_lit s0.sp 2128 16,
      bv_sub_add_lit s0.sp 2128 24] at hexp_key
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hexp_key
  refine SepWP.focus_weaken hexp_key (by sep_focus) ?_
  wp_pull_exists; rename_i kw0 kw1 kw2 kw3 P_key
  wp_focus_pure; intro hfold_key
  have h16_key := memRegion_16_split (s0.sp - 4032#64)
  rw [bv_sub_add_lit s0.sp 4032 8] at h16_key
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h16_key
  refine SepWP.focus_weaken (Entails.of_eq h16_key) (by sep_focus) ?_
  wp_pull_exists; rename_i kd1 kd0
  have h928_dst := memRegion_928_split_header32_body896 (s0.sp - 4016#64)
  rw [bv_sub_add_lit s0.sp 4016 8, bv_sub_add_lit s0.sp 4016 16,
      bv_sub_add_lit s0.sp 4016 24, bv_sub_add_lit s0.sp 4016 32] at h928_dst
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h928_dst
  refine SepWP.focus_weaken h928_dst (by sep_focus) ?_
  wp_pull_exists; rename_i d0 d1 d2 d3
  have h24_scr := memRegion_24_words3 (s0.sp - 3088#64)
  rw [bv_sub_add_lit s0.sp 3088 8, bv_sub_add_lit s0.sp 3088 16] at h24_scr
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24_scr
  refine SepWP.focus_weaken (Entails.of_eq h24_scr) (by sep_focus) ?_
  wp_pull_exists; rename_i f2 f1 f0
  have h896_dst : memRegion (s0.sp - 3984#64) 896 = memRegion (s0.sp - 3984#64) bs896.length := by
    rw [hbs896]
  rw [h896_dst]
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hmemcpy hpc hnext ⊢
  wp_steps 12
  wp_call hmemcpy ⟨s0.sp - 3984#64, s0.sp - 3024#64, bs896⟩
  wp_steps 17
  have hreassemble_dst := reassemble_chunkedStatesAt_words A (s0.sp - 4016#64) v.state w1_st w2_st w3_st hbs
  rw [bv_sub_add_lit s0.sp 4016 8, bv_sub_add_lit s0.sp 4016 16,
      bv_sub_add_lit s0.sp 4016 24, bv_sub_add_lit s0.sp 4016 32] at hreassemble_dst
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hreassemble_dst
  refine SepWP.focus_weaken hreassemble_dst (by sep_focus) ?_
  have hreassemble_src := reassemble_src_928_after_memcpy (s0.sp - 3056#64) (chunkedStatesWord0 v.state) w1_st w2_st w3_st hbs896
  rw [bv_sub_add_lit s0.sp 3056 8, bv_sub_add_lit s0.sp 3056 16,
      bv_sub_add_lit s0.sp 3056 24, bv_sub_add_lit s0.sp 3056 32] at hreassemble_src
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hreassemble_src
  refine SepWP.focus_weaken hreassemble_src (by sep_focus) ?_
  refine SepWP.focus_weaken (memRegion_2992_join_statesRecv_ok s0.sp w1_st w2_st w3_st kw0 kw1 kw2 kw3) (by sep_focus) ?_
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext kw0 kw1 kw2 kw3 P_key _ hfold_key ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals first | rfl | simp only [arm64_norm, *]

/-- Steps from `+1736` (`spqrRecvPlacedEntry + 1736#64`) through `bl <States>::recv`, branching on
    `st0.recv K sckaMsg`:
    - `.error (.panic p)`: handled by `statesRecvOnPanic`,
    - `.error (.err err)`: steps through `+1740..+1764 -> +2472..+2500 -> +1040 -> s0.lr`,
    - `.ok v`: relocates `v.state` (`928`B) to `s0.sp - 4016#64`, moves `v.key` (`32`B) to
    `(x24, x25, [s0.sp - 4032#64 .. - 4016#64])`, checks `pre.epoch != 0`, and reaches `+1856` (`spqrRecvPlacedEntry + 1856#64`). -/
theorem step_statesRecv_1736_placed {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
    (hinv : statesRecvPreInv st0)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1736#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 3056#64) (hx1 : s.readReg64 .x1 = s0.sp - 1160#64)
    (hx2 : s.readReg64 .x2 = s0.sp - 4112#64) (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0) (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch) (hx24 : s.readReg64 .x24 = s0.sp - 3056#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 4640#64) (hx26 : s.readReg64 .x26 = s0.sp - 1160#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 2896 ∗ memRegion (s0.sp - 1168#64) 8 ∗
      chunkedStatesAt A (s0.sp - 1160#64) st0 ∗
      memRegion (s0.sp - 232#64) 136 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hok_tail : ∀ (v : V1Recv spqrPolyApi (spqrAuthApi F))
      (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp) (s1 : State) (P1 : SepProp),
      States.recv K st0 sckaMsg = .ok v →
      (∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          States.Recv.optEpochSecretAt A dst v.key) →
      s1.pc = spqrRecvPlacedEntry + 1856#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 4592#64 →
      s1.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64) →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 32 ∗
        ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
        chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2992 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hrecv_call := hC.statesRecv_ok
  subst hP
  refine SepWPpLS.focus_weaken (memRegion_2896_split_statesRecv s0.sp) (by sep_focus) ?_
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 332)
  refine SepWP.mono (step_pre_statesRecv_1736_placed ext s0 s _ hpc hrun) ?_
  intro sc P_sc hpc_sc hrun_sc ⟨hP_sc, hsp_sc, htr_sc, hx0_sc, hx1_sc, hx2_sc,
    hx19_sc, hx20_sc, hx21_sc, hx22_sc, hx24_sc, hx25_sc, hx26_sc, hx27_sc, hx28_sc, hx29_sc, hx30_sc⟩
  subst hP_sc
  unfold spqrRecvRoPlacedAt
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesRecvStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hrecv_call ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩
    hpc_sc hrun_sc
    (by simp only [State.spAligned, hsp_sc, hsp]; exact sp_sub_4992_aligned s0 hs0_align)
    hx30_sc (by rw [htr_sc.1, htr.1])
    (fun sf => onPanic_of_statesRecv hpre hdec hinner hmv hmin hmsg hfrom)
    (fun _ _ => rfl)
    (by
      dsimp only [statesRecvPlacedSpec]
      refine frame_pure_pre
        ⟨hx0_sc.trans hx0, hx1_sc.trans hx1, hx2_sc.trans hx2, hinv⟩
        (by rw [hsp_sc, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, _, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hxfp_c, hvregs_c⟩
  dsimp only [statesRecvPlacedSpec]
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm, htr_sc.1, htr.1], by rw [hvregs_c, htr_sc.2, htr.2]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm, hsp_sc, hsp]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c, hx19_sc, hx19]
  have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c, hx20_sc, hx20]
  have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c, hx21_sc, hx21]
  have hx22_sm : sm.readReg64 .x22 = pre.epoch := by rw [hx22_c, hx22_sc, hx22]
  have hx24_sm : sm.readReg64 .x24 = s0.sp - 3056#64 := by rw [hx24_c, hx24_sc, hx24]
  have hx25_sm : sm.readReg64 .x25 = s0.sp - 4640#64 := by rw [hx25_c, hx25_sc, hx25]
  have hx26_sm : sm.readReg64 .x26 = s0.sp - 1160#64 := by rw [hx26_c, hx26_sc, hx26]
  have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c, hx27_sc, hx27]
  have hx28_sm : sm.readReg64 .x28 = 0#64 := by rw [hx28_c, hx28_sc, hx28]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64
    rw [hxfp_c]; exact hx29_sc.trans hx29
  rw [hsp_sc, hsp]
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesRecvStackX (by decide)).symm)
    (by sep_focus) ?_
  have hro_fold :
      Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        statesFromPbJumpTablePlacedAt ∗
        statesRecvRoPlacedAt ∗
        statesIntoPbJumpTablePlacedAt ⊢
      spqrRecvRoPlacedAt := Entails.refl _
  refine SepWPpLS.focus_weaken hro_fold (by sep_focus) ?_
  have h928_self : memRegion (s0.sp - 1160#64) chunkedStatesSize = memRegion (s0.sp - 1160#64) 928 := rfl
  rw [h928_self]
  have hrecv_eq : st0.recv K sckaMsg = States.recv K st0 sckaMsg := rfl
  rw [hrecv_eq]
  cases hrecv : States.recv K st0 sckaMsg with
  | error se =>
    cases se with
    | panic p =>
      rw [resultV1RecvAt_panic_false]
      refine SepWPpLS.focus_pure (by sep_focus) False.elim
    | err err =>
      apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
      refine sepWP_spqrRecvPlacedPost_of_post0
        (spqrV1Recv_v1_statesRecv_err F K hpre hdec hinner hmv hmin hmsg hfrom hrecv).2 ?_
      exact step_post_statesRecv_err_1740_placed A F K ext hC st msg ret
        pre pre_pb pb w0 w1 sckaMsg st0 err hpre hdec hinner hmv hmin hmsg hfrom hrecv
        s0 sm _ R _ rfl hs0_align hpcm hrunm hspm' htr_sm' hx19_sm hx25_sm hx27_sm hx28_sm
        (by ac_rfl) hcl
  | ok v =>
    have hep0 := msgPreamble_epoch_beq_zero_false hpre hmv
    let s0_1856 := s0.writeReg64 .x30 (spqrRecvPlacedEntry + 1856#64)
    have hs0_1856_sp : s0_1856.sp = s0.sp := rfl
    apply SepWPpLS.of_sepWP
      (mid := spqrRecvPlacedEntry + 1856#64)
    let F_rest : SepProp :=
      spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      memRegion (s0.sp - 4992#64) 352 ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 32 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0
    refine step_post_statesRecv_ok_1740_placed A F ext hC pre w0 v hep0 s0_1856 sm _ F_rest _
      hs0_align hpcm hrunm hspm' hx22_sm hx24_sm hx27_sm
      (by simp only [hs0_1856_sp, F_rest]; ac_rfl) ?_
    intro kw0 kw1 kw2 kw3 P_key s1 hfold_key hpc1 hrun1 hsp1 htr1
      hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply ProofLib.SepWP.done hpc1 hrun1
    exact hok_tail v kw0 kw1 kw2 kw3 P_key s1 _ hrecv hfold_key hpc1 hrun1 hsp1 (traceVRegs_trans htr1 htr_sm')
      hx0_1 hx1_1 hx2_1
      (hx19_1.trans hx19_sm) (hx20_1.trans hx20_sm) (hx21_1.trans hx21_sm)
      hx22_1 hx23_1 hx24_1 hx25_1 (hx26_1.trans hx26_sm) hx27_1
      (hx28_1.trans hx28_sm) (hx29_1.trans hx29_sm)
      (by simp only [hs0_1856_sp, F_rest]; ac_rfl)

/-! ## 4. Composed First-Half V1 Ratchet Step (`+1532 .. +1856`) -/

/-- Composes `step_msgDeserialize_1532_placed`, `step_statesFromPb_1636_placed`, and
    `step_statesRecv_1736_placed` from `+1532` (`spqrRecvPlacedEntry + 1532#64`) to `+1856`
    (`spqrRecvPlacedEntry + 1856#64`). -/
theorem step_v1_ratchet_1532_to_1856_placed {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1532#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length) (hx24 : s.readReg64 .x24 = remPtr)
    (hx26 : s.readReg64 .x26 = 0#64) (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      Drop.optProtoInnerStateAt A (s0.sp - 4512#64) pb.innerState ∗
      memRegion (s0.sp - 4288#64) 4192 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hok_1856 : ∀ (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
      (v : V1Recv spqrPolyApi (spqrAuthApi F))
      (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp) (s1 : State) (P1 : SepProp),
      Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      States.recv K st0 sckaMsg = .ok v →
      (∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          States.Recv.optEpochSecretAt A dst v.key) →
      s1.pc = spqrRecvPlacedEntry + 1856#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 4592#64 →
      s1.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64) →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 32 ∗
        ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
        chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2992 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hpts : v1StatePtsBound pb :=
    v1StatePtsBound_of_spqrDecodeState (F := F) (K := K) hst_len hdec hinner
  refine step_msgDeserialize_1532_placed hC st msg ret pre remPtr pre_pb pb w0 w1
    hpre hvalid hdec hinner hmv hmin s0 s P R hs0_align hpc hrun hsp htr
    hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29 hP ?_
  intro sckaMsg s1636 P1636 hmsg hpc1636 hrun1636 hsp1636 htr1636
    hx0_1636 hx8_1636 hx19_1636 hx20_1636 hx21_1636 hx22_1636 hx24_1636 hx25_1636 hx26_1636 hx27_1636 _ hx29_1636 hP1636
  refine step_statesFromPb_1636_placed hC st msg ret pre pre_pb pb w0 w1 sckaMsg
    hpts hpre hdec hinner hmv hmin hmsg s0 s1636 P1636 R hs0_align
    hpc1636 hrun1636 hsp1636 htr1636
    hx0_1636 hx8_1636 hx19_1636 hx20_1636 hx21_1636 hx22_1636 hx24_1636 hx25_1636 hx26_1636 hx27_1636 hx29_1636 hP1636 ?_
  intro st0 s1736 P1736 hfrom hpc1736 hrun1736 hsp1736 htr1736
    hx0_1736 hx1_1736 hx2_1736 hx19_1736 hx20_1736 hx21_1736 hx22_1736 hx24_1736 hx25_1736 hx26_1736 hx27_1736 hx28_1736 hx29_1736 hP1736
  have hinv : statesRecvPreInv st0 :=
    statesRecvPreInv_of_spqrDecodeState (F := F) (K := K) hst_len hdec hinner hfrom
  refine step_statesRecv_1736_placed hC st msg ret pre pre_pb pb w0 w1 sckaMsg st0
    hinv hpre hdec hinner hmv hmin hmsg hfrom s0 s1736 P1736 R hs0_align
    hpc1736 hrun1736 hsp1736 htr1736
    hx0_1736 hx1_1736 hx2_1736 hx19_1736 hx20_1736 hx21_1736 hx22_1736 hx24_1736 hx25_1736 hx26_1736 hx27_1736 hx28_1736 hx29_1736 hP1736 ?_
  intro v kw0 kw1 kw2 kw3 P_key s1856 P1856 hrecv hfold_key
  exact hok_1856 sckaMsg st0 v kw0 kw1 kw2 kw3 P_key s1856 P1856 hmsg hfrom hrecv hfold_key

end CryptoVerification.SpqrV1.Top.Recv
