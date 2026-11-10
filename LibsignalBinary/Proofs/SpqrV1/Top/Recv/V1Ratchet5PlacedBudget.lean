/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5PlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable V1 Ratchet `Ok` Tail (`+2664 -> ret`)

Envelope-parametric and default `SpqrRecvEnv` proofs of `<Chain>::into_pb`,
`<PqRatchetState>::encode_to_vec`, and the combined V1 `Ok` tail (`+2664 -> ret`) for `spqr::recv`
(Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain EpochSecret Message MlKem MsgPreamble PqRatchetState SpqrApiResult
   States V1State chainFrom msgPreamble spqrAuthApi spqrDecodeState spqrHkdfWith
   spqrPolyApi spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg doReserveStackX)
open CryptoVerification.RustHeap (vecU8 vecU8Buf)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainGhost ChainIntoPbCall chainAt chainIntoPbStackX)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStateEncodeToVecGhost encodeToVecStackOf extractLsb_hi_append64
   extractLsb_lo_append64 pqRatchetStatePBAt)
open CryptoVerification.SpqrV1.ProtoRepr (chainPBAt)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost statesIntoPbStackX)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS encodeRaw_len_lt_of_recv_ok memRegion_224_sub_entails_words28
   protoPqRatchetStateAt_eq_pqRatchetStatePBAt sp_sub_4992_aligned
   spqrRecvCalleeStackX spqrRecvPlacedEntry spqrRecvPlacedProg spqrRecvRoPlacedAt
   spqrRecvRoPlacedAt_expose_statesIntoPb spqrRecvSavedRegs spqrV1Recv_v1_ratchet_ok
   stackAt_spqrRecvCallee_split statesIntoPbJumpTablePlacedAt words27SubAt
   words27SubAt_to_memRegion_224)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
  (ChainIntoPbAllocEnv ChainIntoPbEnv chainIntoPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
  (PqRatchetStateEncodeToVecEnv pqRatchetStateEncodeToVecSpecOf
   pqRatchetStateEncodeToVecSpecOfEnv pqRatchetStateEncodeToVecSpecX)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget (StatesIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContracts SpqrRecvPlacedContractsOfEnv statesIntoPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv spqrRecvBudgetPanicPost spqrRecvPlacedPost spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (SpqrRecvEnv.append_freeOnly seq_vm_clean)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5PlacedBudgetAux
  (frame_pure_pre hsp_add_456 hsp_add_544 hsp_add_560 memRegion_224_split_24_200_v1
   memRegion_2856_split_v1_ok onPanic_false_budget optProtoInnerStateAt_expose_224
   protoPqRatchetState_entails_drop_v1 sp_setPState_v1 sp_sub_96_sub_136
   sp_writeVReg128_v1 toDropContractsBudget)

export LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5PlacedBudgetAux
  (step_v1_drop_newPb_and_vn_2884_placed_ofEnv
   step_v1_drop_newPb_and_vn_2884_placed
   step_v1_ok_epilogue_2820_to_ret_placed_ofEnv
   step_v1_ok_epilogue_2820_to_ret_placed)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64
attribute [local simp, local arm64_norm, local wp_norm]
  sp_sub_96_sub_136 hsp_add_544 hsp_add_560 hsp_add_456
  sp_writeVReg128_v1 sp_setPState_v1

/-! ## 1. `+2688 .. +2820`: Relocate `Option<Inner>` & `<PqRatchetState>::encode_to_vec` -/

/-- Envelope-parametric (`+2688 .. +2820`): copies `st1.into_pb.innerState` (`224`B) from `s0.sp
    - 2096#64` to `s0.sp - 2928#64`, stores `noneCap` (`-1`) at `s0.sp - 3056#64`, calls
    `<PqRatchetState>::encode_to_vec`, and continues via
    `step_v1_ok_epilogue_2820_to_ret_placed_ofEnv`. -/
theorem step_v1_encodeToVec_2688_to_2820_placed_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {Env : List AllocEvent → Prop} (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (st1 : States spqrPolyApi (spqrAuthApi F))
    (chain2 : Chain) (rawKey : Bytes)
    (w0 w1 w790 cap_rk ptr_rk : BitVec 64)
    (hlen_enc : (PqRatchetState.encodeRaw
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }).length < 2 ^ 63)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) },
        if rawKey.isEmpty then none else some rawKey))
    (s0 s : State) (P R : SepProp)
    (hFit_enc : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (PqRatchetStateEncodeToVecEnv
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }))
    (hevs_enc : ∀ evs_enc evs_d,
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) } evs_enc →
      FreeOnlyEvs evs_d → Env ((evs0 ++ evs_enc) ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2688#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ w790) ∗
      memRegion (s0.sp - 3048#64) 40 ∗
      chainPBAt A.repAlloc (s0.sp - 3008#64) chain2.intoPb ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 2096#64) st1.into_pb.innerState ∗
      memRegion (s0.sp - 1872#64) 1640 ∗
      memRegion (s0.sp - 232#64) 88 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have henc_ok := hC.encodeToVec_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  let newPb : PqRatchetState :=
    { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }
  subst hP
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 426)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine seq_vm_clean (mid := lsmpl.base 426)
    (P_mid :=
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      pqRatchetStatePBAt A.repAlloc (s0.sp - 3056#64) newPb ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      memRegion (s0.sp - 2096#64) 24 ∗ memRegion (s0.sp - 2072#64) 200 ∗
      memRegion (s0.sp - 1872#64) 1640 ∗
      memRegion (s0.sp - 232#64) 88 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sc =>
      sc.sp = s0.sp - 4992#64 ∧ TraceVRegs sc s0 ∧
      sc.readReg64 .x0 = s0.sp - 2096#64 ∧ sc.readReg64 .x1 = s0.sp - 3056#64 ∧
      sc.readReg64 .x19 = ret ∧ sc.readReg64 .x21 = cap_rk ∧
      sc.readReg64 .x22 = ptr_rk ∧ sc.readReg64 .x23 = w0 ∧
      sc.readReg64 .x24 = BitVec.ofNat 64 rawKey.length ∧
      sc.readReg64 .x25 = 0xFFFFFFFFFFFFFFFF#64 ∧
      sc.readReg64 .x26 = 0#64 ∧ sc.readReg64 .x29 = s0.sp - 96#64 ∧
      sc.readReg64 .x30 = spqrRecvPlacedEntry + 2820#64)
    ?_ ?_
  · by_vm_steps (
      refine SepWP.focus_weaken
        (optProtoInnerStateAt_expose_224 H_inner A.repAlloc hC.h_inner_eq s0.sp st1.into_pb.innerState)
        (by sep_focus) ?_
      wp_pull_exists; rename_i w0_in d_in H_in
      wp_focus_pure; intro hpack_in
      refine SepWP.focus_weaken (memRegion_224_sub_entails_words28 s0.sp 2928) (by sep_focus) ?_
      wp_pull_exists; rename_i u0 uDst
      have hjoin_src :
          ((s0.sp - 2096#64) ↦₆₄ w0_in) ∗ words27SubAt s0.sp 2096 d_in ⊢
          memRegion (s0.sp - 2096#64) 24 ∗ memRegion (s0.sp - 2072#64) 200 :=
        Entails.trans (words27SubAt_to_memRegion_224 s0.sp 2096 w0_in d_in)
          (memRegion_224_split_24_200_v1 s0.sp)
      dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hpack_in hjoin_src ⊢
      simp only [sepConj_assoc]
      wp_steps 33
      refine SepWP.focus_weaken hpack_in (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin_src (by sep_focus) ?_
      have hpack_pq :
          ((s0.sp - 3056#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
            memRegion (s0.sp - 3048#64) 40 ∗
            chainPBAt A.repAlloc (s0.sp - 3008#64) chain2.intoPb ∗
            optProtoInnerStateAt A.repAlloc (s0.sp - 2928#64) st1.into_pb.innerState ⊢
          pqRatchetStatePBAt A.repAlloc (s0.sp - 3056#64) newPb := by
        dsimp only [newPb]
        rw [← protoPqRatchetStateAt_eq_pqRatchetStatePBAt A.repAlloc (s0.sp - 3056#64)]
        exact protoPqRatchetState_entails_drop_v1 A.repAlloc s0.sp chain2.intoPb st1.into_pb
      refine SepWP.focus_weaken hpack_pq (by sep_focus) ?_
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp only [spqrRecvPlacedEntry, wp_norm, arm64_norm, *]
    )
  · intro sc hpc_sc hrun_sc hvm_sc
      ⟨hsp_sc, htr_sc, hx0_sc, hx1_sc, hx19_sc, hx21_sc, hx22_sc, hx23_sc,
       hx24_sc, hx25_sc, hx26_sc, hx29_sc, hx30_sc⟩
    apply ProofLib.SepWP.done hpc_sc hrun_sc
    rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s sc hvm_sc]
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) (encodeToVecStackOf doReserveStackX) (by decide)))
      (by sep_focus) ?_
    refine LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget.SepWPpLS.call_lscro henc_ok
      ((⟨s0.sp - 2096#64, s0.sp - 3056#64, newPb⟩ : PqRatchetStateEncodeToVecGhost),
        MC.stepEvents evs0 st_cost)
      hpc_sc hrun_sc
      (by simp only [State.spAligned, hsp_sc]; exact hfsp_align)
      hx30_sc
      (by rw [htr_sc.1])
      (fun sm => onPanic_false_budget _ sm)
      (fun _ _ => rfl)
      (by
        dsimp only [pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf,
          pqRatchetStateEncodeToVecSpecOfEnv]
        refine frame_pure_pre ⟨hx0_sc, hx1_sc, hlen_enc, hFit_enc⟩
          (by rw [hsp_sc]; sep_focus))
      ?_
    intro sm hpcm hrunm hspm hcsm
    rcases hcsm with ⟨hx19_c, _, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, _, _, hxfp_c, hvregs_c⟩
    dsimp only [pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf,
      pqRatchetStateEncodeToVecSpecOfEnv]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPpLS.exists_elim; intro evs_enc
    refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, hevs_enc0⟩
    have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm, htr_sc.1], by rw [hvregs_c, htr_sc.2]⟩
    have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm, hsp_sc]
    have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c, hx19_sc]
    have hx21_sm : sm.readReg64 .x21 = cap_rk := by rw [hx21_c, hx21_sc]
    have hx22_sm : sm.readReg64 .x22 = ptr_rk := by rw [hx22_c, hx22_sc]
    have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c, hx23_sc]
    have hx24_sm : sm.readReg64 .x24 = BitVec.ofNat 64 rawKey.length := by rw [hx24_c, hx24_sc]
    have hx25_sm : sm.readReg64 .x25 = 0xFFFFFFFFFFFFFFFF#64 := by rw [hx25_c, hx25_sc]
    have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c, hx26_sc]
    have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
      change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; exact hx29_sc
    have hsp_stk : stackAt sc.sp (encodeToVecStackOf doReserveStackX) =
        stackAt (s0.sp - 4992#64) (encodeToVecStackOf doReserveStackX) := by rw [hsp_sc]
    refine SepWPpLS.focus_weaken (Entails.of_eq hsp_stk) (by sep_focus) ?_
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) (encodeToVecStackOf doReserveStackX) (by decide)).symm)
      (by sep_focus) ?_
    rw [← MC.stepEvents_append]
    exact step_v1_ok_epilogue_2820_to_ret_placed_ofEnv A lim st_cost Env
      (evs0 ++ evs_enc) (fun evs_d hd => hevs_enc evs_enc evs_d hevs_enc0 hd)
      F K ext (toDropContractsBudget hC) st msg ret pre_pb newPb rawKey
      w0 w1 cap_rk ptr_rk hok s0 sm _ R hs0_align
      hpcm hrunm hspm' htr_sm' hx19_sm hx21_sm hx22_sm hx23_sm hx24_sm hx25_sm hx26_sm hx29_sm
      (by sep_ac_rfl)

theorem step_v1_encodeToVec_2688_to_2820_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (st1 : States spqrPolyApi (spqrAuthApi F))
    (chain2 : Chain) (rawKey : Bytes)
    (w0 w1 w790 cap_rk ptr_rk : BitVec 64)
    (hlen_enc : (PqRatchetState.encodeRaw
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }).length < 2 ^ 63)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) },
        if rawKey.isEmpty then none else some rawKey))
    (s0 s : State) (P R : SepProp)
    (evs0 : List AllocEvent)
    (hFit_enc : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (PqRatchetStateEncodeToVecEnv
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }))
    (hevs_enc : ∀ evs_enc,
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) } evs_enc →
      SpqrRecvEnv st msg (evs0 ++ evs_enc))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2688#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ w790) ∗
      memRegion (s0.sp - 3048#64) 40 ∗
      chainPBAt A.repAlloc (s0.sp - 3008#64) chain2.intoPb ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 2096#64) st1.into_pb.innerState ∗
      memRegion (s0.sp - 1872#64) 1640 ∗
      memRegion (s0.sp - 232#64) 88 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v1_encodeToVec_2688_to_2820_placed_ofEnv (Env := SpqrRecvEnv st msg) evs0 hC
    st msg ret pre_pb st1 chain2 rawKey w0 w1 w790 cap_rk ptr_rk hlen_enc hok s0 s P R
    hFit_enc (fun evs_enc _ he hd => SpqrRecvEnv.append_freeOnly (hevs_enc evs_enc he) hd)
    hs0_align hpc hrun hsp htr hx19 hx21 hx22 hx23 hx24 hx26 hx29 hP

/-! ## 2. `+2676 .. +2688`: `<Chain>::into_pb` -/

/-- Envelope-parametric (`+2676 .. +2688`): calls `<Chain>::into_pb` on `chain2` at `s0.sp -
    232#64`, writing `chain2.intoPb` to `s0.sp - 3008#64`, joins `memRegion (s0.sp - 232#64)
    88`, and continues via `step_v1_encodeToVec_2688_to_2820_placed_ofEnv`. -/
theorem step_v1_chainIntoPb_2676_to_2688_placed_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {Env : List AllocEvent → Prop} (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (st1 : States spqrPolyApi (spqrAuthApi F))
    (G : ChainGhost) (chain2 : Chain) (rawKey : Bytes)
    (w0 w1 w790 cap_rk ptr_rk : BitVec 64)
    (hlen_enc : (PqRatchetState.encodeRaw
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }).length < 2 ^ 63)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) },
        if rawKey.isEmpty then none else some rawKey))
    (s0 s : State) (P R : SepProp)
    (hFit_cip : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩))
    (hFit_enc : ∀ evs_cip,
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩ evs_cip →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cip) st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }))
    (hevs_ok : ∀ evs_cip evs_enc evs_d,
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩ evs_cip →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) } evs_enc →
      FreeOnlyEvs evs_d → Env (((evs0 ++ evs_cip) ++ evs_enc) ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2676#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx25 : s.readReg64 .x25 = s0.sp - 3056#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ w790) ∗
      memRegion (s0.sp - 3048#64) 40 ∗
      memRegion (s0.sp - 3008#64) 80 ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 2096#64) st1.into_pb.innerState ∗
      memRegion (s0.sp - 1872#64) 1640 ∗
      chainAt A.repAlloc (s0.sp - 232#64) G chain2 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hchain_into := hC.chainIntoPb_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  subst hP
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 365)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine seq_vm_clean (mid := lsmpl.base 365)
    (P_mid :=
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ w790) ∗
      memRegion (s0.sp - 3048#64) 40 ∗
      memRegion (s0.sp - 3008#64) 80 ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 2096#64) st1.into_pb.innerState ∗
      memRegion (s0.sp - 1872#64) 1640 ∗
      chainAt A.repAlloc (s0.sp - 232#64) G chain2 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sc =>
      sc.sp = s0.sp - 4992#64 ∧ TraceVRegs sc s0 ∧
      sc.readReg64 .x8 = s0.sp - 3008#64 ∧ sc.readReg64 .x0 = s0.sp - 232#64 ∧
      sc.readReg64 .x19 = ret ∧ sc.readReg64 .x21 = cap_rk ∧
      sc.readReg64 .x22 = ptr_rk ∧ sc.readReg64 .x23 = w0 ∧
      sc.readReg64 .x24 = BitVec.ofNat 64 rawKey.length ∧
      sc.readReg64 .x26 = 0#64 ∧ sc.readReg64 .x29 = s0.sp - 96#64 ∧
      sc.readReg64 .x30 = spqrRecvPlacedEntry + 2688#64)
    ?_ ?_
  · by_vm_steps (
      wp_steps 3
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp only [spqrRecvPlacedEntry, wp_norm, arm64_norm, *]
    )
  · intro sc hpc_sc hrun_sc hvm_sc
      ⟨hsp_sc, htr_sc, hx8_sc, hx0_sc, hx19_sc, hx21_sc, hx22_sc, hx23_sc,
       hx24_sc, hx26_sc, hx29_sc, hx30_sc⟩
    apply ProofLib.SepWP.done hpc_sc hrun_sc
    rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s sc hvm_sc]
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)))
      (by sep_focus) ?_
    refine LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget.SepWPpLS.call_lscro hchain_into
      ((⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩ : ChainIntoPbCall),
        MC.stepEvents evs0 st_cost)
      hpc_sc hrun_sc
      (by simp only [State.spAligned, hsp_sc]; exact hfsp_align)
      hx30_sc
      (by rw [htr_sc.1])
      (fun sm => onPanic_false_budget _ sm)
      (fun _ _ => rfl)
      (by
        dsimp only [chainIntoPbSpecX]
        refine frame_pure_pre ⟨hx8_sc, hx0_sc, hFit_cip⟩
          (by rw [hsp_sc]; sep_focus))
      ?_
    intro sm hpcm hrunm hspm hcsm
    rcases hcsm with ⟨hx19_c, _, hx21_c, hx22_c, hx23_c, hx24_c, _, hx26_c, _, _, hxfp_c, hvregs_c⟩
    dsimp only [chainIntoPbSpecX]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPpLS.exists_elim; intro evs_cip
    refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨hevs_cip, htr_sm, _⟩
    have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm, htr_sc.1], by rw [hvregs_c, htr_sc.2]⟩
    have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm, hsp_sc]
    have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c, hx19_sc]
    have hx21_sm : sm.readReg64 .x21 = cap_rk := by rw [hx21_c, hx21_sc]
    have hx22_sm : sm.readReg64 .x22 = ptr_rk := by rw [hx22_c, hx22_sc]
    have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c, hx23_sc]
    have hx24_sm : sm.readReg64 .x24 = BitVec.ofNat 64 rawKey.length := by rw [hx24_c, hx24_sc]
    have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c, hx26_sc]
    have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
      change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; exact hx29_sc
    have hsp_stk : stackAt sc.sp chainIntoPbStackX =
        stackAt (s0.sp - 4992#64) chainIntoPbStackX := by rw [hsp_sc]
    refine SepWPpLS.focus_weaken (Entails.of_eq hsp_stk) (by sep_focus) ?_
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)).symm)
      (by sep_focus) ?_
    rw [← MC.stepEvents_append]
    exact step_v1_encodeToVec_2688_to_2820_placed_ofEnv (Env := Env) (evs0 ++ evs_cip) hC
      st msg ret pre_pb st1 chain2 rawKey w0 w1 w790 cap_rk ptr_rk hlen_enc hok s0 sm _ R
      (hFit_enc evs_cip hevs_cip)
      (fun evs_enc evs_d he hd => hevs_ok evs_cip evs_enc evs_d hevs_cip he hd)
      hs0_align hpcm hrunm hspm' htr_sm' hx19_sm hx21_sm hx22_sm hx23_sm hx24_sm hx26_sm hx29_sm
      (by sep_ac_rfl)

theorem step_v1_chainIntoPb_2676_to_2688_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (st1 : States spqrPolyApi (spqrAuthApi F))
    (G : ChainGhost) (chain2 : Chain) (rawKey : Bytes)
    (w0 w1 w790 cap_rk ptr_rk : BitVec 64)
    (hlen_enc : (PqRatchetState.encodeRaw
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }).length < 2 ^ 63)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) },
        if rawKey.isEmpty then none else some rawKey))
    (s0 s : State) (P R : SepProp)
    (evs0 : List AllocEvent)
    (hFit_cip : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩))
    (hFit_enc : ∀ evs_cip,
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩ evs_cip →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cip) st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }))
    (hevs_ok : ∀ evs_cip evs_enc,
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩ evs_cip →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) } evs_enc →
      SpqrRecvEnv st msg ((evs0 ++ evs_cip) ++ evs_enc))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2676#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx25 : s.readReg64 .x25 = s0.sp - 3056#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ w790) ∗
      memRegion (s0.sp - 3048#64) 40 ∗
      memRegion (s0.sp - 3008#64) 80 ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 2096#64) st1.into_pb.innerState ∗
      memRegion (s0.sp - 1872#64) 1640 ∗
      chainAt A.repAlloc (s0.sp - 232#64) G chain2 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v1_chainIntoPb_2676_to_2688_placed_ofEnv (Env := SpqrRecvEnv st msg) evs0 hC
    st msg ret pre_pb st1 G chain2 rawKey w0 w1 w790 cap_rk ptr_rk hlen_enc hok s0 s P R
    hFit_cip hFit_enc
    (fun evs_cip evs_enc _ hcip henc hd =>
      SpqrRecvEnv.append_freeOnly (hevs_ok evs_cip evs_enc hcip henc) hd)
    hs0_align hpc hrun hsp htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx29 hP

/-! ## 3. `+2664 .. +2916 -> +876 -> +1040 -> ret`: Combined V1 `Ok` Tail -/

/-- Envelope-parametric combined V1 ratchet `Ok` tail (`+2664 .. +2916 -> +876 -> +1040 ->
    ret`): calls `<States>::into_pb`, `<Chain>::into_pb`, `<PqRatchetState>::encode_to_vec`,
    writes `Ok((newStateBytes, outKey))` to `ret`, drops `newPb` and
    `pre_pb.versionNegotiation`, and returns via `step_epilogue_placed_ofEnv`. -/
theorem step_v1_ok_2664_to_ret_placed_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {Env : List AllocEvent → Prop} (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (sckaMsg : Message spqrPolyApi)
    (st0 st1 : States spqrPolyApi (spqrAuthApi F))
    (key : Option EpochSecret) (chain0 chain1 chain2 : Chain)
    (G : ChainGhost) (rawKey : Bytes)
    (w0 w1 cap_rk ptr_rk : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok ⟨key, st1⟩)
    (hep_ne : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hadd : (match key with
      | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
      | none => .ok chain0) = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey))
    (s0 s : State) (P R : SepProp)
    (hFit_sip : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (IntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩))
    (hFit_cip : ∀ evs_sip,
      IntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩ evs_sip →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_sip) st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩))
    (hFit_enc : ∀ evs_sip evs_cip,
      IntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩ evs_sip →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩ evs_cip →
      FitsEnv MC lim (MC.stepEvents ((evs0 ++ evs_sip) ++ evs_cip) st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }))
    (hevs_ok : ∀ evs_sip evs_cip evs_enc evs_d,
      IntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩ evs_sip →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩ evs_cip →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) } evs_enc →
      FreeOnlyEvs evs_d → Env ((((evs0 ++ evs_sip) ++ evs_cip) ++ evs_enc) ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2664#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx25 : s.readReg64 .x25 = s0.sp - 3056#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) st1 ∗
      memRegion (s0.sp - 3088#64) 2856 ∗
      chainAt A.repAlloc (s0.sp - 232#64) G chain2 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hstates_into := hC.statesIntoPb_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  have hok := spqrV1Recv_v1_ratchet_ok hpre hdec hinner hmv hmin hmsg hst0 hrecv hep_ne hcf hadd hrk
  have hlen_enc := encodeRaw_len_lt_of_recv_ok hst_len hok
  have hjmp_eq : statesIntoPbJumpTablePlacedAt =
      CryptoVerification.SpqrV1.Top.InitInner.statesIntoPbJumpTablePlacedAt := rfl
  subst hP
  refine SepWPpLS.focus_weaken (memRegion_2856_split_v1_ok s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPpLS.exists_elim; intro w790
  refine SepWPpLS.focus_weaken spqrRecvRoPlacedAt_expose_statesIntoPb (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPpLS.exists_elim; intro P_ro_into
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro hP_ro_into
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 334)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine seq_vm_clean (mid := lsmpl.base 334)
    (P_mid :=
      statesIntoPbJumpTablePlacedAt ∗ P_ro_into ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) st1 ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ w790) ∗
      memRegion (s0.sp - 3048#64) 40 ∗
      memRegion (s0.sp - 3008#64) 80 ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      memRegion (s0.sp - 2096#64) optProtoInnerStateSize ∗
      memRegion (s0.sp - 1872#64) 1640 ∗
      chainAt A.repAlloc (s0.sp - 232#64) G chain2 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sc =>
      sc.sp = s0.sp - 4992#64 ∧ TraceVRegs sc s0 ∧
      sc.readReg64 .x8 = s0.sp - 2096#64 ∧ sc.readReg64 .x0 = s0.sp - 4016#64 ∧
      sc.readReg64 .x19 = ret ∧ sc.readReg64 .x21 = cap_rk ∧
      sc.readReg64 .x22 = ptr_rk ∧ sc.readReg64 .x23 = w0 ∧
      sc.readReg64 .x24 = BitVec.ofNat 64 rawKey.length ∧
      sc.readReg64 .x25 = s0.sp - 3056#64 ∧
      sc.readReg64 .x26 = 0#64 ∧ sc.readReg64 .x29 = s0.sp - 96#64 ∧
      sc.readReg64 .x30 = spqrRecvPlacedEntry + 2676#64)
    ?_ ?_
  · by_vm_steps (
      wp_steps 3
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp only [spqrRecvPlacedEntry, wp_norm, arm64_norm, *]
    )
  · intro sc hpc_sc hrun_sc hvm_sc
      ⟨hsp_sc, htr_sc, hx8_sc, hx0_sc, hx19_sc, hx21_sc, hx22_sc, hx23_sc,
       hx24_sc, hx25_sc, hx26_sc, hx29_sc, hx30_sc⟩
    apply ProofLib.SepWP.done hpc_sc hrun_sc
    rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s sc hvm_sc]
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesIntoPbStackX (by decide)))
      (by sep_focus) ?_
    rw [hjmp_eq]
    refine LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget.SepWPpLS.call_lscro hstates_into
      ((⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩ : StatesIntoPbGhost F),
        MC.stepEvents evs0 st_cost)
      hpc_sc hrun_sc
      (by simp only [State.spAligned, hsp_sc]; exact hfsp_align)
      hx30_sc
      (by rw [htr_sc.1])
      (fun sm => onPanic_false_budget _ sm)
      (fun _ _ => rfl)
      (by
        dsimp only [statesIntoPbPlacedSpecXOfEnv]
        refine frame_pure_pre ⟨hx8_sc, hx0_sc, hFit_sip⟩
          (by rw [hsp_sc]; sep_focus))
      ?_
    intro sm hpcm hrunm hspm hcsm
    rcases hcsm with ⟨hx19_c, _, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, _, _, hxfp_c, hvregs_c⟩
    dsimp only [statesIntoPbPlacedSpecXOfEnv,
      LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.statesIntoPbPlacedSpecXOfEnv]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPpLS.exists_elim; intro evs_sip
    refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, hevs_sip⟩
    have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm, htr_sc.1], by rw [hvregs_c, htr_sc.2]⟩
    have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm, hsp_sc]
    have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c, hx19_sc]
    have hx21_sm : sm.readReg64 .x21 = cap_rk := by rw [hx21_c, hx21_sc]
    have hx22_sm : sm.readReg64 .x22 = ptr_rk := by rw [hx22_c, hx22_sc]
    have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c, hx23_sc]
    have hx24_sm : sm.readReg64 .x24 = BitVec.ofNat 64 rawKey.length := by rw [hx24_c, hx24_sc]
    have hx25_sm : sm.readReg64 .x25 = s0.sp - 3056#64 := by rw [hx25_c, hx25_sc]
    have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c, hx26_sc]
    have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
      change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; exact hx29_sc
    have hsp_stk : stackAt sc.sp statesIntoPbStackX =
        stackAt (s0.sp - 4992#64) statesIntoPbStackX := by rw [hsp_sc]
    refine SepWPpLS.focus_weaken (Entails.of_eq hsp_stk) (by sep_focus) ?_
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesIntoPbStackX (by decide)).symm)
      (by sep_focus) ?_
    rw [← hjmp_eq]
    refine SepWPpLS.focus_weaken hP_ro_into (by sep_focus) ?_
    rw [← MC.stepEvents_append]
    exact step_v1_chainIntoPb_2676_to_2688_placed_ofEnv (Env := Env) (evs0 ++ evs_sip) hC
      st msg ret pre_pb st1 G chain2 rawKey w0 w1 w790 cap_rk ptr_rk hlen_enc hok s0 sm _ R
      (hFit_cip evs_sip hevs_sip)
      (fun evs_cip hcip => hFit_enc evs_sip evs_cip hevs_sip hcip)
      (fun evs_cip evs_enc evs_d hcip henc hd => hevs_ok evs_sip evs_cip evs_enc evs_d hevs_sip hcip henc hd)
      hs0_align hpcm hrunm hspm' htr_sm' hx19_sm hx21_sm hx22_sm hx23_sm hx24_sm hx25_sm hx26_sm hx29_sm
      (by sep_ac_rfl)

theorem step_v1_ok_2664_to_ret_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (sckaMsg : Message spqrPolyApi)
    (st0 st1 : States spqrPolyApi (spqrAuthApi F))
    (key : Option EpochSecret) (chain0 chain1 chain2 : Chain)
    (G : ChainGhost) (rawKey : Bytes)
    (w0 w1 cap_rk ptr_rk : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok ⟨key, st1⟩)
    (hep_ne : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hadd : (match key with
      | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
      | none => .ok chain0) = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey))
    (s0 s : State) (P R : SepProp)
    (evs0 : List AllocEvent)
    (hFit_sip : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (StatesIntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩))
    (hFit_cip : ∀ evs_sip,
      StatesIntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩ evs_sip →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_sip) st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩))
    (hFit_enc : ∀ evs_sip evs_cip,
      StatesIntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩ evs_sip →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩ evs_cip →
      FitsEnv MC lim (MC.stepEvents ((evs0 ++ evs_sip) ++ evs_cip) st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }))
    (hevs_ok : ∀ evs_sip evs_cip evs_enc,
      StatesIntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩ evs_sip →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩ evs_cip →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) } evs_enc →
      SpqrRecvEnv st msg (((evs0 ++ evs_sip) ++ evs_cip) ++ evs_enc))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2664#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx25 : s.readReg64 .x25 = s0.sp - 3056#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) st1 ∗
      memRegion (s0.sp - 3088#64) 2856 ∗
      chainAt A.repAlloc (s0.sp - 232#64) G chain2 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v1_ok_2664_to_ret_placed_ofEnv (Env := SpqrRecvEnv st msg) evs0 hC
    st msg ret pre pre_pb pb sckaMsg st0 st1 key chain0 chain1 chain2 G rawKey
    w0 w1 cap_rk ptr_rk hst_len hpre hdec hinner hmv hmin hmsg hst0 hrecv hep_ne hcf hadd hrk
    s0 s P R hFit_sip hFit_cip hFit_enc
    (fun evs_sip evs_cip evs_enc _ hsip hcip henc hd =>
      SpqrRecvEnv.append_freeOnly (hevs_ok evs_sip evs_cip evs_enc hsip hcip henc) hd)
    hs0_align hpc hrun hsp htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx29 hP

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5PlacedBudget
