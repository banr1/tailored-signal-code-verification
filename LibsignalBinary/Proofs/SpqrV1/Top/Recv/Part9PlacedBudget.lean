/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9Placed
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9PlacedBudgetAux
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable `Ordering::Greater` (`V0ChainPlacedTail`) for `spqr::recv`

Proves `step_ordering_greater_placed_ofEnv`, `step_ordering_greater_placed`, and
`v0ChainPlacedTailGen_of_contracts` for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain Error MlKem MsgPreamble PqRatchetState V1State VersionNegotiationPB
   chainFrom msgPreamble spqrDecodeState spqrHkdfWith spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg)
open CryptoVerification.SpqrV1.ChainProofs (ChainGhost)
open CryptoVerification.SpqrV1.Drop (optProtoPqRatchetInnerAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (extractLsb_hi_append64 extractLsb_lo_append64)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.ChainFrom (chainFromPbStackX chainPBAt_protoRepr_eq_exists)
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
  (add_one_beq_zero_of_ne_noneCap chainPBAt_expose_cap chainPBAt_unexpose_cap
   word_rest72_to_memRegion_80)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation (chainResultAt)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm (ult_one_toI32)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS chainErrorAt_sub3056_unpack chainRepr_sub_entails_words11 chainWords11
   fp_sub_32_add_eq fp_sub_48_add_eq frame2544_join_v0 frame4544_split_v0 frame_pure_pre
   hsp_add_544_eq' hsp_add_560_eq' memRegion_88_sub2096_words4_rest memRegion_88_sub_entails_words11
   pack_v0_err_sub2088 sp_setPState sp_writeVReg128 spqrRecvCalleeStackX spqrRecvPlacedEntry
   spqrRecvPlacedProg spqrRecvRoPlacedAt spqrRecvSavedRegs spqrV1Recv_gt_chainFrom_err
   stackAt_spqrRecvCallee_split words11SubAt words11SubAt_to_memRegion_88
   words4_rest_sub3056_to_memRegion_88)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkLib_eq_329 blkPC_329 blkPl_329)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (ChainIntoPbAllocEnv ChainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (ChainRecvKeyEnv chainRecvKeyEvents)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (ChainFromAllocEnv ChainFromEnv chainFromPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContracts SpqrRecvPlacedContractsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv spqrRecvBudgetPanicPost spqrRecvPlacedPost spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget (SpqrRecvEnv.append_freeOnly)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget (SepWPpLS.call_lscro)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux
  (V0ChainPlacedTail V0ChainPlacedTailGen)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8PlacedBudget
  (SpqrRecvPlacedContractsOfEnv.toDropContracts step_v0_err_2388_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9PlacedBudgetAux
  (onPanic_false_entails step_v0_after_chainFrom_604_placed step_v0_after_chainFrom_604_placed_ofEnv
   step_v0_chain_none_2108_placed step_v0_chain_none_2108_placed_ofEnv)

export LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9PlacedBudgetAux
  (step_v0_after_chainFrom_604_placed_ofEnv step_v0_after_chainFrom_604_placed
   step_v0_chain_none_2108_placed_ofEnv step_v0_chain_none_2108_placed)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64 ult_one_toI32
attribute [local simp, local arm64_norm, local wp_norm]
  fp_sub_32_add_eq hsp_add_560_eq' fp_sub_48_add_eq hsp_add_544_eq'

/-! ## `step_ordering_greater_placed` (`+496 .. +600` and `+2164 .. +2180`) & `V0ChainPlacedTail` -/

/-- Envelope-parametric `Ordering::Greater` branch (`+496`): dispatches on `pre_pb.chain`:
    - `pre_pb.chain = none`: jumps to `+2108` (`step_v0_chain_none_2108_placed_ofEnv`).
    - `pre_pb.chain = some chPb`: calls `Chain::from_pb` (`lsmpl.base 364`) and branches to `+604`
    (`step_v0_after_chainFrom_604_placed_ofEnv`) on `Ok` or `+2164 -> +2388`
    (`step_v0_err_2388_placed_ofEnv`) on `Err`. -/
theorem step_ordering_greater_placed_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    (st_cost : MC.σ) (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
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
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (s0 s : State) (P R : SepProp)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (hfits_cf : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainFromAllocEnv pre_pb.chain (some vn)))
    (hfits_rk : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf) st_cost)
        (ChainRecvKeyEnv (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩))
    (hfits_into : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩)
          st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩))
    (hfits_enc : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost) (evs_into : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_into)
          st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
    (hevs_rk_err : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (e : Error) (evs_d : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .error (.err e) →
      FreeOnlyEvs evs_d →
      Env
        (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_d))
    (hevs_rk_ok : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost)
        (evs_into evs_enc evs_d : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }
        evs_enc →
      FreeOnlyEvs evs_d →
      Env
        (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++
          evs_into ++ evs_enc ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hfrom_pb_ok := hC.chainFromPb_ok
  subst hP
  refine SepWPpLS.focus_weaken (Entails.of_eq (frame4544_split_v0 s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPpLS.exists_elim; intro d896
  apply SepWPpLS.exists_elim; intro d888
  apply SepWPpLS.exists_elim; intro d880
  cases hchain : pre_pb.chain with
  | none =>
    apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 2108#64)
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    dsimp only [optChainPBAt, CryptoVerification.LibsignalTripleRatchetRepr.noneCap]
    apply sepWP_seg_ls_vm
      (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
      blkLib_eq_329 (mid := (blkPl_329).base + 2108#64)
    intro _m_strip
    wp_steps 3
    refine SepWP.focus_weaken
      (word_rest72_to_memRegion_80 (s0.sp - 4944#64) 0xFFFFFFFFFFFFFFFF#64)
      (by rw [bv_sub_add_lit s0.sp 4944 8 (by decide) (by decide)]; sep_focus) ?_
    refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_v0_chain_none_2108_placed_ofEnv st_cost Env evs0 hC
      st msg ret pre pre_pb vn pb w0 w1 d880 d888 d896
      hst_len hpre hdec hvn hinner hchain hmin hver_gt s0 _ _ R
      hevs_free hfits_cf hfits_rk hfits_into hfits_enc hevs_rk_err hevs_rk_ok
      hs0_align
      (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, htr.1, *],
        by simp only [wp_norm, arm64_norm, htr.2, *]⟩
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by sep_ac_rfl)
  | some chPb =>
    apply SepWPpLS.of_sepWP (mid := lsmpl.base 364)
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    dsimp only [optChainPBAt]
    rw [chainPBAt_protoRepr_eq_exists A.repAlloc (s0.sp - 4944#64) chPb]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists; rename_i gPb
    refine SepWP.focus_weaken
      (chainPBAt_expose_cap A.repAlloc gPb (s0.sp - 4944#64) chPb)
      (by sep_focus) ?_
    wp_focus_pure; intro hcap_pb_ne
    have hz_pb : (gPb.linksCap + 1#64 == 0#64) = false :=
      add_one_beq_zero_of_ne_noneCap hcap_pb_ne
    apply sepWP_seg_ls_vm
      (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
      blkLib_eq_329 (mid := lsmpl.base 364)
    intro _m_strip
    wp_steps 7
    refine SepWP.focus_weaken
      (chainPBAt_unexpose_cap A.repAlloc gPb (s0.sp - 4944#64) chPb)
      (by sep_focus) ?_
    refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromPbStackX (by decide)))
      (by sep_focus) ?_
    refine SepWPpLS.call_lscro hfrom_pb_ok
      (⟨s0.sp - 3056#64, s0.sp - 4944#64, gPb, chPb⟩, MC.stepEvents evs0 st_cost)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
      (show _ = spqrRecvPlacedEntry + 524#64 by simp only [spqrRecvPlacedEntry, arm64_norm, *])
      (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
      (fun _ => onPanic_false_entails)
      (fun _ _ => rfl)
      (by
        dsimp only [chainFromPbSpecX]
        refine frame_pure_pre
          ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            (show _ = LsRetAddr624 ((blkPl_329).base + 524#64) by
              simp only [Reg.lr, spqrRecvPlacedEntry, arm64_norm, *]).mpr
              (lsRetAddr624_blockPlacement_base_add 329 524#64 (by decide) (by decide))⟩
          (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
              sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
      ?_
    intro sm hpcm hrunm hspm hcsm
    have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
    rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, _, _, _, _, _, hx27_c, hx28_c, hxfp_c, _⟩
    dsimp only [chainFromPbSpecX]
    rw [sepExists_sepConj_left]
    apply SepWPpLS.exists_elim; intro evs_fpb
    simp only [sepConj_assoc]
    refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, hevs_fpb⟩
    have hevs_cf : ChainFromEnv pre_pb.chain (some vn) evs_fpb := by
      rw [hchain]; exact hevs_fpb
    have htr_sm' : TraceVRegs sm s0 :=
      ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
    have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm]; simp only [arm64_norm, *]
    have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
    have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
    have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by
      rw [hx21_c]; simp only [arm64_norm, *]
    have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c]; simp only [arm64_norm, *]
    have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by rw [hx28_c]; simp only [arm64_norm, *]
    have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
      change sm.readReg64 Reg.fp = s0.sp - 96#64
      rw [hxfp_c]; simp only [arm64_norm, *]
    rw [← MC.stepEvents_append]
    simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
      sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromPbStackX (by decide)).symm)
      (by sep_focus) ?_
    cases hfpb : Chain.fromPb chPb with
    | error e =>
      have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .error e := by
        simp [chainFrom, hchain, hfpb]
      obtain ⟨herr_recv, hnp⟩ : (spqrV1Recv F K).recv st.bytes msg.bytes =
          .error (e == .stateDecode) ∧ ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
        spqrV1Recv_gt_chainFrom_err hpre hdec hvn hinner hmin hver_gt hcf
      apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 2388#64)
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
      dsimp only [chainResultAt]
      rw [chainErrorAt_sub3056_unpack s0.sp e, memRegion_88_sub2096_words4_rest s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      wp_pull_exists; rename_i u2096_3 u2096_2 u2096_1 d2896 q0_err w3_err
      wp_focus_pure; intro htag_q0
      dsimp only [CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.noneCap]
      apply sepWP_seg_ls_vm
        (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
        blkLib_eq_329 (mid := (blkPl_329).base + 2388#64)
      intro _m_strip
      wp_steps 13
      refine SepWP.focus_weaken
        (words4_rest_sub3056_to_memRegion_88 s0.sp 0xFFFFFFFFFFFFFFFF#64
          (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (frame2544_join_v0 s0.sp (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (pack_v0_err_sub2088 s0.sp e q0_err w3_err htag_q0)
        (by sep_focus) ?_
      refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
      apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact step_v0_err_2388_placed_ofEnv A lim st_cost Env (evs0 ++ evs_fpb)
        (fun evs_d hd => by
          rw [List.append_assoc]
          exact hevs_free (evs_fpb ++ evs_d) (hevs_fpb.append hd))
        F K ext (SpqrRecvPlacedContractsOfEnv.toDropContracts hC)
        st msg ret vn pb e w0 w1 d2896 herr_recv hnp s0 _ _ R hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, htr_sm'.1, *],
          by simp only [wp_norm, arm64_norm, htr_sm'.2, *]⟩
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by sep_ac_rfl)
    | ok chain0 =>
      have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 := by
        simp [chainFrom, hchain, hfpb]
      apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 604#64)
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
      dsimp only [chainResultAt]
      refine SepWP.focus_weaken (chainRepr_sub_entails_words11 A.repAlloc s0.sp 3056 chain0) (by sep_focus) ?_
      refine SepWP.focus_weaken (memRegion_88_sub_entails_words11 s0.sp 2096) (by sep_focus) ?_
      wp_pull_exists; rename_i G_c0 pad_c0 u2096
      wp_focus_pure; intro hcap_c0_ne
      have hz_c0 : (G_c0.linksCap + 1#64 == 0#64) = false :=
        add_one_beq_zero_of_ne_noneCap hcap_c0_ne
      have hto88 := words11SubAt_to_memRegion_88 s0.sp 3056 (chainWords11 G_c0 chain0 pad_c0)
      dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hto88 ⊢
      simp only [sepConj_assoc]
      apply sepWP_seg_ls_vm
        (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
        blkLib_eq_329 (mid := (blkPl_329).base + 604#64)
      intro _m_strip
      wp_steps 20
      refine SepWP.focus_weaken hto88 (by sep_focus) ?_
      refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
      apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact step_v0_after_chainFrom_604_placed_ofEnv st_cost Env (evs0 ++ evs_fpb) hC
        st msg ret pre pre_pb vn pb G_c0 chain0 pad_c0
        w0 w1 G_c0.linksPtr G_c0.linksHead
        (BitVec.ofNat 64 (G_c0.epochs.zip chain0.links).length) u2096.w0
        hst_len hpre hdec hvn hinner hmin hver_gt hcf s0 _ _ R
        (hfits_rk evs_fpb chain0 G_c0 hevs_cf hcf)
        (fun chain1 rawKey gChain hrk =>
          hfits_into evs_fpb chain0 G_c0 chain1 rawKey gChain hevs_cf hcf hrk)
        (fun chain1 rawKey gChain evs_into hrk hinto =>
          hfits_enc evs_fpb chain0 G_c0 chain1 rawKey gChain evs_into hevs_cf hcf hrk hinto)
        (fun e evs_d hrk hd =>
          hevs_rk_err evs_fpb chain0 G_c0 e evs_d hevs_cf hcf hrk hd)
        (fun chain1 rawKey gChain evs_into evs_enc evs_d hrk hinto henc hd =>
          hevs_rk_ok evs_fpb chain0 G_c0 chain1 rawKey gChain evs_into evs_enc evs_d
            hevs_cf hcf hrk hinto henc hd)
        hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, htr_sm'.1, *],
          by simp only [wp_norm, arm64_norm, htr_sm'.2, *]⟩
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]; sep_ac_rfl)

theorem step_ordering_greater_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    (st_cost : MC.σ) (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (hevs0 : SpqrRecvEnv st msg evs0)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (s0 s : State) (P R : SepProp)
    (hfits_cf : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainFromAllocEnv pre_pb.chain (some vn)))
    (hfits_rk : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf) st_cost)
        (ChainRecvKeyEnv (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩))
    (hfits_into : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩)
          st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩))
    (hfits_enc : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost) (evs_into : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_into)
          st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
    (hevs_rk_err : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (e : Error) (evs_d : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .error (.err e) →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg
        (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_d))
    (hevs_rk_ok : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost)
        (evs_into evs_enc evs_d : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }
        evs_enc →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg
        (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++
          evs_into ++ evs_enc ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_ordering_greater_placed_ofEnv st_cost (SpqrRecvEnv st msg) evs0 hC
    st msg ret pre pre_pb vn pb w0 w1 hst_len hpre hdec hvn hinner hmin hver_gt
    s0 s P R (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    hfits_cf hfits_rk hfits_into hfits_enc hevs_rk_err hevs_rk_ok
    hs0_align hpc hrun hsp htr hx19 hx20 hx21 hx27 hx28 hx29 hP

/-- Package `step_ordering_greater_placed_ofEnv` as `V0ChainPlacedTailGen`
    (`Part5PlacedBudgetAux`). -/
theorem v0ChainPlacedTailGen_of_contracts {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    (st_cost : MC.σ) (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
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
    (hst_len : st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (hfits_cf : ∀ (pre_pb : PqRatchetState) (vn : VersionNegotiationPB),
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      FitsEnv MC lim (MC.stepEvents evs0 st_cost)
        (ChainFromAllocEnv pre_pb.chain (some vn)))
    (hfits_rk : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost),
      msgPreamble msg.bytes = .ok pre →
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf) st_cost)
        (ChainRecvKeyEnv (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩))
    (hfits_into : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost),
      msgPreamble msg.bytes = .ok pre →
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩)
          st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩))
    (hfits_enc : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (pb : V1State) (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost) (evs_into : List AllocEvent),
      msgPreamble msg.bytes = .ok pre →
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      pre_pb.inner = some (.v1 pb) →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_into)
          st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
    (hevs_rk_err : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (e : Error) (evs_d : List AllocEvent),
      msgPreamble msg.bytes = .ok pre →
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .error (.err e) →
      FreeOnlyEvs evs_d →
      Env
        (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_d))
    (hevs_rk_ok : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (pb : V1State) (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost)
        (evs_into evs_enc evs_d : List AllocEvent),
      msgPreamble msg.bytes = .ok pre →
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      pre_pb.inner = some (.v1 pb) →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }
        evs_enc →
      FreeOnlyEvs evs_d →
      Env
        (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++
          evs_into ++ evs_enc ++ evs_d)) :
    V0ChainPlacedTailGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R := by
  intro pre _remPtr pre_pb vn pb w0 w1 _w26 s P
    hpre _hrem hdec hvn hinner _hw0 _hw26 hmin hver_gt
    hpc hrun hsp htr hx19 hx20 hx21 _hx22 _hx23 _hx24 _hx26 hx27 hx28 hx29 hP
  exact step_ordering_greater_placed_ofEnv st_cost Env evs0 hC
    st msg ret pre pre_pb vn pb w0 w1 hst_len hpre hdec hvn hinner hmin hver_gt
    s0 s P R hevs_free
    (hfits_cf pre_pb vn hdec hvn)
    (fun evs_cf chain0 G_c0 => hfits_rk pre pre_pb vn evs_cf chain0 G_c0 hpre hdec hvn)
    (fun evs_cf chain0 G_c0 chain1 rawKey gChain =>
      hfits_into pre pre_pb vn evs_cf chain0 G_c0 chain1 rawKey gChain hpre hdec hvn)
    (fun evs_cf chain0 G_c0 chain1 rawKey gChain evs_into =>
      hfits_enc pre pre_pb vn pb evs_cf chain0 G_c0 chain1 rawKey gChain evs_into
        hpre hdec hvn hinner)
    (fun evs_cf chain0 G_c0 e evs_d =>
      hevs_rk_err pre pre_pb vn evs_cf chain0 G_c0 e evs_d hpre hdec hvn)
    (fun evs_cf chain0 G_c0 chain1 rawKey gChain evs_into evs_enc evs_d =>
      hevs_rk_ok pre pre_pb vn pb evs_cf chain0 G_c0 chain1 rawKey gChain evs_into evs_enc evs_d
        hpre hdec hvn hinner)
    hs0_align hpc hrun hsp htr hx19 hx20 hx21 hx27 hx28 hx29 hP

theorem v0ChainPlacedTail_of_contracts {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    (st_cost : MC.σ) (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (hevs0 : SpqrRecvEnv st msg evs0)
    (hst_len : st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hfits_cf : ∀ (pre_pb : PqRatchetState) (vn : VersionNegotiationPB),
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      FitsEnv MC lim (MC.stepEvents evs0 st_cost)
        (ChainFromAllocEnv pre_pb.chain (some vn)))
    (hfits_rk : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost),
      msgPreamble msg.bytes = .ok pre →
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf) st_cost)
        (ChainRecvKeyEnv (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩))
    (hfits_into : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost),
      msgPreamble msg.bytes = .ok pre →
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩)
          st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩))
    (hfits_enc : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (pb : V1State) (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost) (evs_into : List AllocEvent),
      msgPreamble msg.bytes = .ok pre →
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      pre_pb.inner = some (.v1 pb) →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_into)
          st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
    (hevs_rk_err : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (e : Error) (evs_d : List AllocEvent),
      msgPreamble msg.bytes = .ok pre →
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .error (.err e) →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg
        (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_d))
    (hevs_rk_ok : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (pb : V1State) (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost)
        (evs_into evs_enc evs_d : List AllocEvent),
      msgPreamble msg.bytes = .ok pre →
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      pre_pb.inner = some (.v1 pb) →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }
        evs_enc →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg
        (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++
          evs_into ++ evs_enc ++ evs_d)) :
    V0ChainPlacedTail A lim st_cost evs0 F K ext st msg ret s0 R :=
  v0ChainPlacedTailGen_of_contracts st_cost (SpqrRecvEnv st msg) evs0 hC
    st msg ret hst_len s0 R hs0_align
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    hfits_cf hfits_rk hfits_into hfits_enc hevs_rk_err hevs_rk_ok

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9PlacedBudget
