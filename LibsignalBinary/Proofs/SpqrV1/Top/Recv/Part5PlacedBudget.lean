/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Version Dispatch for `spqr::recv`

Budget-threaded `versionNegotiation = some vn` dispatch (`+448`), frame reassembly (`+408..+444`),
and combined `spqr::decode_state` + version dispatch (`+312..+496 / +1076 / +1532`) for
`spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1
  (MlKem MsgPreamble PqRatchetState V1State VersionNegotiationPB msgPreamble
   spqrDecodeState spqrDeps spqrHkdfWith spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (cap_add_one_beq_zero_false none3Cap' optProtoInnerStateAt optProtoPqRatchetInnerAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStateStackX none2Cap
   optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.Recv
  (InnerWordInv MsgRemValid SepWPpLS SepWPpLS.focus_pure SepWPpLS.focus_weaken
   SepWPpLS.of_sepWP_ret cset_ne_eq frame_pure_pre head16_bs96_entails_vnTailAndChainAt
   one_ule_zeroExtend64_of_gt optProtoPqRatchetInnerAt_expose_word
   optVersionNegotiationPBTailAt_none_eq optVersionNegotiationPBTailAt_some_cap_lt
   optVersionNegotiationPBTailAt_some_expose_minVersion ownFrame_split_for_decode
   pqRatchetStateToPb_inner_none recv_vn_some_inner_none recv_vn_some_lt relocVnTailAndChainAt
   sp_sub_4992_aligned spqrRecvCalleeStackX spqrRecvPlacedEntry spqrRecvPlacedProg
   spqrRecvRoPlacedAt spqrRecvSavedRegs spqrV1Recv_noPanic_of_err spqrV1Recv_noPanic_of_recv_ok
   spqrV1Recv_recv_of_err spqrV1Recv_recv_of_ok stackAt_spqrRecvCallee_split
   statesFromPbJumpTablePlacedAt statesIntoPbJumpTablePlacedAt statesRecvRoPlacedAt
   ugt_zeroExtend32_one_of_gt ule_one_zeroExtend64_false_of_gt ule_zeroExtend64_false_of_lt
   ule_zeroExtend64_true_of_ge ult_zeroExtend64_false_of_ge ult_zeroExtend64_true_of_lt
   version_eq_zero_of_lt_one version_trichotomy zeroExtend32_bne_one_of_gt)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open CryptoVerification.SpqrV1.Top.Send (decodeState_spqrDeps_of_spqrDecodeState_ok)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (spqrDecodeStatePlacedSpec spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv sepWP_spqrRecvPlacedPostOfEnv_of_post0
   spqrRecvBudgetPanicPost spqrRecvPlacedPost spqrRecvPlacedPostOfEnv spqrRecvPlacedPreambleFrame)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (SpqrRecvDropContractsBudget SpqrRecvEnv.append_freeOnly seq_vm_clean)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
  (SepWPpLS.call_lscro step_err_minVersion_752_placed_ofEnv step_ok_none_912_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4PlacedBudget
  (step_decode_err_328_placed_ofEnv step_decode_ok_328_to_408_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux
  (InitInnerPlacedTail InitInnerPlacedTailGen V0ChainPlacedTail V0ChainPlacedTailGen
   V1RatchetPlacedTailLS V1RatchetPlacedTailLSGen step_equal_792_pLS_ofEnv
   step_vn_none_744_placed_ofEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpySpec)

export CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS.of_sepWP_ret SepWPpLS.pre_mono SepWPpLS.focus_weaken SepWPpLS.focus_pure)
export LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux
  (V0ChainPlacedTailGen V0ChainPlacedTail InitInnerPlacedTailGen InitInnerPlacedTail)
export LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux
  (V1RatchetPlacedTailLSGen V1RatchetPlacedTailLS step_equal_792_pLS_gen step_equal_792_pLS_ofEnv)
export LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux
  (step_equal_792_pLS step_vn_none_744_placed_ofEnv step_vn_none_744_placed)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

private theorem align_pre_wp {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

/-! ## 1. Version Dispatch at `+448` (`pre_pb.versionNegotiation = some vn`) -/

/-- Envelope-parametric dispatch at `+448` when `pre_pb.versionNegotiation = some vn`. -/
theorem step_vn_some_448_placed_ofEnv {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        optProtoInnerStateAt A.repAlloc a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (w0 w1 w26 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hw0_ne : w0 ≠ none2Cap)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp)
    (htail_gt : V0ChainPlacedTailGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (htail_lt : InitInnerPlacedTailGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (htail_eq : V1RatchetPlacedTailLSGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 448#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = if (w26 + 3#64 != 0#64) = true then 1#64 else 0#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
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
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  subst hP
  by_cases hlt_min : pre.version < vn.minVersion.truncate 8
  · have herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error false :=
      spqrV1Recv_recv_of_err
        (recv_vn_some_lt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn hlt_min)
    have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
      spqrV1Recv_noPanic_of_err
        (recv_vn_some_lt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn hlt_min)
    have hult := ult_zeroExtend64_true_of_lt hlt_min
    have hule := ule_zeroExtend64_false_of_lt hlt_min
    apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    rw [hvn]
    refine SepWP.focus_weaken
      (optVersionNegotiationPBTailAt_some_expose_minVersion A.repAlloc s0.sp w0 w1 vn) (by sep_focus) ?_
    wp_pull_exists; rename_i P_vn
    wp_focus_pure; intro hunexp
    wp_steps 3
    refine SepWP.focus_weaken hunexp (by sep_focus) ?_
    refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 hnp ?_
    exact step_err_minVersion_752_placed_ofEnv A lim st_cost Env evs0 hevs_free
      (spqrV1Recv F K) ext hC st msg ret pre_pb w0 w1 w26
      hw26 herr s0 _ _ R _ rfl hs0_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [← hvn]; simp only [wp_norm, arm64_norm, *]; sep_ac_rfl) hcl
  · have hult := ult_zeroExtend64_false_of_ge hlt_min
    have hule := ule_zeroExtend64_true_of_ge hlt_min
    cases hinner : pre_pb.inner with
    | none =>
      have hw26_eq : w26 = none3Cap' := by
        rw [hinner] at hw26; exact hw26
      subst hw26_eq
      have hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none) :=
        spqrV1Recv_recv_of_ok
          (recv_vn_some_inner_none (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn
            (pqRatchetStateToPb_inner_none hinner) hlt_min)
      apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
      rw [hvn]
      refine SepWP.focus_weaken
        (optVersionNegotiationPBTailAt_some_expose_minVersion A.repAlloc s0.sp w0 w1 vn) (by sep_focus) ?_
      wp_pull_exists; rename_i P_vn
      wp_focus_pure; intro hunexp
      wp_steps 5
      refine SepWP.focus_weaken hunexp (by sep_focus) ?_
      refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
      exact step_ok_none_912_placed_ofEnv A lim st_cost Env evs0 hevs_free
        (spqrV1Recv F K) ext hC st msg ret pre_pb w0 w1 none3Cap'
        hw26 hok s0 _ _ R _ rfl hs0_align
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [← hvn, ← hinner]; simp only [wp_norm, arm64_norm, *]; sep_ac_rfl) hcl
    | some inn =>
      cases inn with
      | v1 pb =>
        have hw26_ne : ¬((w26 + 3#64 == 0#64) = true) := by
          rw [hinner] at hw26; exact hw26
        have hw26_bne : (w26 + 3#64 != 0#64) = true := by
          simp [bne, hw26_ne]
        have hx8_1 : s.readReg64 .x8 = 1#64 := by
          rw [hx8, hw26_bne]; rfl
        rcases version_trichotomy pre.version with hlt | heq | hgt
        · have hv0 : pre.version = 0#8 := version_eq_zero_of_lt_one hlt
          apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 1076#64)
          dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
          rw [hvn]
          refine SepWP.focus_weaken
            (optVersionNegotiationPBTailAt_some_expose_minVersion A.repAlloc s0.sp w0 w1 vn) (by sep_focus) ?_
          wp_pull_exists; rename_i P_vn
          wp_focus_pure; intro hunexp
          rw [hv0] at hx25 hult hule
          dsimp at hx25 hult hule
          wp_steps 12
          refine SepWP.focus_weaken hunexp (by sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          exact htail_lt pre remPtr pre_pb vn pb w0 w1 w26 _ _
            hpre hvalid hdec hvn hinner hw0_ne hw26 hlt_min hlt
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by rw [hv0]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by rw [← hinner]; simp only [wp_norm, arm64_norm, *]; sep_ac_rfl)
        · apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 792#64)
          dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
          rw [hvn]
          refine SepWP.focus_weaken
            (optVersionNegotiationPBTailAt_some_expose_minVersion A.repAlloc s0.sp w0 w1 vn) (by sep_focus) ?_
          wp_pull_exists; rename_i P_vn
          wp_focus_pure; intro hunexp
          rw [heq] at hx25 hult hule
          dsimp at hx25 hult hule
          wp_steps 10
          refine SepWP.focus_weaken hunexp (by sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          exact step_equal_792_pLS_ofEnv H_inner A lim st_cost Env evs0 F K ext hmemcpy_ok h_inner_eq
            st msg ret pre remPtr pre_pb pb w0 w1
            hpre hvalid hdec hinner hw0_ne heq
            (by intro vn' hvn'; rw [hvn] at hvn'; cases hvn'; exact heq ▸ hlt_min)
            s0 _ _ R htail_eq hs0_align
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by rw [← hvn, ← hinner]; simp only [wp_norm, arm64_norm, *]; sep_ac_rfl)
        · have hule1 := one_ule_zeroExtend64_of_gt hgt
          have hule1_false := ule_one_zeroExtend64_false_of_gt hgt
          have hbne1 := zeroExtend32_bne_one_of_gt hgt
          have hugt1 := ugt_zeroExtend32_one_of_gt hgt
          apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 496#64)
          dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
          rw [hvn]
          refine SepWP.focus_weaken
            (optVersionNegotiationPBTailAt_some_expose_minVersion A.repAlloc s0.sp w0 w1 vn) (by sep_focus) ?_
          wp_pull_exists; rename_i P_vn
          wp_focus_pure; intro hunexp
          wp_steps 12
          refine SepWP.focus_weaken hunexp (by sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          exact htail_gt pre remPtr pre_pb vn pb w0 w1 w26 _ _
            hpre hvalid hdec hvn hinner hw0_ne hw26 hlt_min hgt
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by rw [← hinner]; simp only [wp_norm, arm64_norm, *]; sep_ac_rfl)

theorem step_vn_some_448_placed {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        optProtoInnerStateAt A.repAlloc a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (w0 w1 w26 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hw0_ne : w0 ≠ none2Cap)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp)
    (htail_gt : V0ChainPlacedTail A lim st_cost evs0 F K ext st msg ret s0 R)
    (htail_lt : InitInnerPlacedTail A lim st_cost evs0 F K ext st msg ret s0 R)
    (htail_eq : V1RatchetPlacedTailLS A lim st_cost evs0 F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 448#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = if (w26 + 3#64 != 0#64) = true then 1#64 else 0#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
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
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_vn_some_448_placed_ofEnv H_inner A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC hmemcpy_ok h_inner_eq st msg ret pre remPtr pre_pb vn w0 w1 w26
    hpre hvalid hdec hvn hw0_ne hw26 s0 s P R htail_gt htail_lt htail_eq
    hs0_align hpc hrun hsp htr
    hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP

/-! ## 2. Frame Reassembly and Branch to `+744` / `+448` (`+408 .. +444`) -/

/-- Envelope-parametric step across `+408 .. +444`, reassembling `pre_pb` at `s0.sp - 4992#64`
    and `memRegion (s0.sp - 4640#64) 4544`, transporting `A.pool` across stack stores via
    `VmPreserved`, and dispatching via `step_vn_none_744_placed_ofEnv` (`+744`) or
    `step_vn_some_448_placed_ofEnv` (`+448`). -/
theorem step_dispatch_408_placed_ofEnv {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        optProtoInnerStateAt A.repAlloc a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (d0 d1 d2 d3 w0 w1 w2 w3 : BitVec 64) (bs96 : List (BitVec 8))
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hw0_ne : w0 ≠ none2Cap)
    (hbs96 : bs96.length = 96)
    (s0 s : State) (P R : SepProp)
    (htail_gt : V0ChainPlacedTailGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (htail_lt : InitInnerPlacedTailGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (htail_eq : V1RatchetPlacedTailLSGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
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
      ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
      ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
      ((s0.sp - 4960#64) ↦ₛ bs96) ∗
      (relocVnTailAndChainAt A.repAlloc w0 w1 pre_pb).1 (unpack64 w2 ++ unpack64 w3 ++ bs96) ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      ((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗
      (∃∗ P_tail : SepProp,
        ⌜((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗ P_tail ⊢
          memRegion (s0.sp - 4640#64) 4544⌝ ∗ P_tail) ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  rcases htr with ⟨htr_eq, hvregs⟩
  have hreassemble :=
    head16_bs96_entails_vnTailAndChainAt A.repAlloc (s0.sp - 4992#64) w0 w1 w2 w3 bs96 pre_pb hbs96
  rw [bv_sub_add_lit s0.sp 4992 16, bv_sub_add_lit s0.sp 4992 24,
      bv_sub_add_lit s0.sp 4992 32, bv_sub_add_lit s0.sp 4992 48] at hreassemble
  subst hP
  cases hvn : pre_pb.versionNegotiation with
  | none =>
    apply SepWPpLS.of_sepWP (mid := (blkPl_329).base + 744#64)
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    wp_pull_exists; rename_i P_tail
    wp_focus_pure; intro hP_tail_join
    refine SepWP.focus_weaken
      (optProtoPqRatchetInnerAt_expose_word A.repAlloc (s0.sp - 4864#64) pre_pb.inner)
      (by sep_focus) ?_
    wp_pull_exists; rename_i w26 P_inner
    wp_focus_pure; intro hw26
    wp_focus_pure; intro hunexp_inner
    refine seq_vm_clean (mid := (blkPl_329).base + 744#64)
      (P_mid :=
        spqrRecvRoPlacedAt ∗
        st.at A.repAlloc ∗
        msg.at A.repAlloc ∗
        memRegion ret 48 ∗
        A.pool lim (MC.stepEvents evs0 st_cost) s ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        ((s0.sp - 4992#64) ↦₆₄ noneCap) ∗
        ((s0.sp - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc noneCap w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
        optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
        memRegion (s0.sp - 4640#64) 4544 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun s1 =>
        s1.sp = s0.sp - 4992#64 ∧
        TraceVRegs s1 s0 ∧
        s1.readReg64 .x8 = (if (w26 + 3#64 == 0#64) = true then 0#64 else 1#64) ∧
        s1.readReg64 .x19 = ret ∧
        s1.readReg64 .x20 = noneCap ∧
        s1.readReg64 .x21 = pre.index.zeroExtend 64 ∧
        s1.readReg64 .x22 = pre.epoch ∧
        s1.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length ∧
        s1.readReg64 .x24 = remPtr ∧
        s1.readReg64 .x25 = pre.version.zeroExtend 64 ∧
        s1.readReg64 .x26 = w26 ∧
        s1.readReg64 .x27 = s0.sp - 3056#64 ∧
        s1.readReg64 .x28 = s0.sp - 4288#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64)
      ?_ ?_
    · by_vm_steps (
        wp_steps 9
        refine SepWP.focus_weaken hreassemble (by sep_focus) ?_
        refine SepWP.focus_weaken hunexp_inner (by sep_focus) ?_
        refine SepWP.focus_weaken hP_tail_join (by sep_focus) ?_
        rw [hvn]
        refine SepWP.focus_weaken
          (optVersionNegotiationPBTailAt_none_eq A.repAlloc w0 w1 (s0.sp - 4976#64))
          (by sep_focus) ?_
        wp_focus_pure; intro hw0; subst hw0
        wp_steps 1
        rw [← hvn]
        refine align_pre_wp (by sep_ac_rfl) ?_
        wp_done
      )
    · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, htr1, hx8_1, hx19_1, hx20_1, hx21_1, hx22_1,
        hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
      rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm1]
      apply SepWP.done hpc1 hrun1
      exact step_vn_none_744_placed_ofEnv H_inner A lim st_cost Env evs0 hevs_free
        F K ext hC hmemcpy_ok h_inner_eq st msg ret pre remPtr pre_pb w1 w26
        hpre hvalid hdec hvn hw26 s0 s1 _ R htail_eq hs0_align
        hpc1 hrun1 hsp1 htr1
        (by rw [hx8_1, cset_ne_eq]; rfl)
        hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 rfl
  | some vn =>
    apply SepWPpLS.of_sepWP (mid := (blkPl_329).base + 448#64)
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    wp_pull_exists; rename_i P_tail
    wp_focus_pure; intro hP_tail_join
    refine SepWP.focus_weaken
      (optProtoPqRatchetInnerAt_expose_word A.repAlloc (s0.sp - 4864#64) pre_pb.inner)
      (by sep_focus) ?_
    wp_pull_exists; rename_i w26 P_inner
    wp_focus_pure; intro hw26
    wp_focus_pure; intro hunexp_inner
    refine seq_vm_clean (mid := (blkPl_329).base + 448#64)
      (P_mid :=
        spqrRecvRoPlacedAt ∗
        st.at A.repAlloc ∗
        msg.at A.repAlloc ∗
        memRegion ret 48 ∗
        A.pool lim (MC.stepEvents evs0 st_cost) s ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        ((s0.sp - 4992#64) ↦₆₄ w0) ∗
        ((s0.sp - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
        optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
        memRegion (s0.sp - 4640#64) 4544 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun s1 =>
        s1.sp = s0.sp - 4992#64 ∧
        TraceVRegs s1 s0 ∧
        s1.readReg64 .x8 = (if (w26 + 3#64 == 0#64) = true then 0#64 else 1#64) ∧
        s1.readReg64 .x19 = ret ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = pre.index.zeroExtend 64 ∧
        s1.readReg64 .x22 = pre.epoch ∧
        s1.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length ∧
        s1.readReg64 .x24 = remPtr ∧
        s1.readReg64 .x25 = pre.version.zeroExtend 64 ∧
        s1.readReg64 .x26 = w26 ∧
        s1.readReg64 .x27 = s0.sp - 3056#64 ∧
        s1.readReg64 .x28 = s0.sp - 4288#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64)
      ?_ ?_
    · by_vm_steps (
        wp_steps 9
        refine SepWP.focus_weaken hreassemble (by sep_focus) ?_
        refine SepWP.focus_weaken hunexp_inner (by sep_focus) ?_
        refine SepWP.focus_weaken hP_tail_join (by sep_focus) ?_
        rw [hvn]
        refine SepWP.focus_weaken
          (optVersionNegotiationPBTailAt_some_cap_lt A.repAlloc w0 w1 (s0.sp - 4976#64) vn)
          (by sep_focus) ?_
        wp_focus_pure; intro hcap_lt
        have hne_none := cap_add_one_beq_zero_false hcap_lt
        wp_steps 1
        rw [← hvn]
        refine align_pre_wp (by sep_ac_rfl) ?_
        wp_done
      )
    · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, htr1, hx8_1, hx19_1, hx20_1, hx21_1, hx22_1,
        hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
      rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm1]
      apply SepWP.done hpc1 hrun1
      exact step_vn_some_448_placed_ofEnv H_inner A lim st_cost Env evs0 hevs_free
        F K ext hC hmemcpy_ok h_inner_eq st msg ret pre remPtr pre_pb vn w0 w1 w26
        hpre hvalid hdec hvn hw0_ne hw26 s0 s1 _ R htail_gt htail_lt htail_eq hs0_align
        hpc1 hrun1 hsp1 htr1
        (by rw [hx8_1, cset_ne_eq]; rfl)
        hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 rfl

theorem step_dispatch_408_placed {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        optProtoInnerStateAt A.repAlloc a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (d0 d1 d2 d3 w0 w1 w2 w3 : BitVec 64) (bs96 : List (BitVec 8))
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hw0_ne : w0 ≠ none2Cap)
    (hbs96 : bs96.length = 96)
    (s0 s : State) (P R : SepProp)
    (htail_gt : V0ChainPlacedTail A lim st_cost evs0 F K ext st msg ret s0 R)
    (htail_lt : InitInnerPlacedTail A lim st_cost evs0 F K ext st msg ret s0 R)
    (htail_eq : V1RatchetPlacedTailLS A lim st_cost evs0 F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
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
      ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
      ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
      ((s0.sp - 4960#64) ↦ₛ bs96) ∗
      (relocVnTailAndChainAt A.repAlloc w0 w1 pre_pb).1 (unpack64 w2 ++ unpack64 w3 ++ bs96) ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      ((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗
      (∃∗ P_tail : SepProp,
        ⌜((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗ P_tail ⊢
          memRegion (s0.sp - 4640#64) 4544⌝ ∗ P_tail) ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_dispatch_408_placed_ofEnv H_inner A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC hmemcpy_ok h_inner_eq st msg ret pre remPtr pre_pb
    d0 d1 d2 d3 w0 w1 w2 w3 bs96 hpre hvalid hdec hw0_ne hbs96 s0 s P R
    htail_gt htail_lt htail_eq hs0_align hpc hrun hsp htr
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hx29 hP

/-! ## 3. `bl spqr::decode_state` and Full Version Dispatch (`+312 .. +496` / `+1076` / `+1532`) -/

/-- Envelope-parametric step from `+312` through `bl spqr::decode_state` (`lsmpl.base 325`),
    error/success handling at `+328..+408`, and version dispatch at `+408..+496` / `+744..+952`,
    continuing via `V0ChainPlacedTailGen` (`+496`), `InitInnerPlacedTailGen` (`+1076`), or
    `V1RatchetPlacedTailLSGen` (`+1532`). -/
theorem step_decode_and_dispatch_placed_ofEnv {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (DecPreEnv DecPostEnv : DecodeStateGhost → List AllocEvent → Prop)
    (Env : List AllocEvent → Prop)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        optProtoInnerStateAt A.repAlloc a opt)
    (hdec_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpecOfEnv H_inner A lim DecPreEnv DecPostEnv)))
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (s0 s : State) (P R : SepProp)
    (hFit_dec : FitsEnv MC lim st_cost (DecPreEnv ⟨st, s0.sp - 3056#64⟩))
    (hEnv_dec : ∀ evs_dec, DecPostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
      ∀ evs_d, FreeOnlyEvs evs_d → Env (evs_dec ++ evs_d))
    (htail_gt : ∀ evs_dec, DecPostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
      V0ChainPlacedTailGen A lim (MC.stepEvents evs_dec st_cost) F K ext st msg ret s0
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (htail_lt : ∀ evs_dec, DecPostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
      InitInnerPlacedTailGen A lim (MC.stepEvents evs_dec st_cost) F K ext st msg ret s0
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (htail_eq : ∀ evs_dec, DecPostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
      V1RatchetPlacedTailLSGen A lim (MC.stepEvents evs_dec st_cost) F K ext st msg ret s0
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 312#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  rcases htr with ⟨htr_eq, hvregs⟩
  subst hP
  unfold spqrRecvPlacedPreambleFrame
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 325)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hdec_ok hpc ⊢
  refine SepWP.focus_weaken (ownFrame_split_for_decode s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i d0 d1 d2 d3 b0 b1 b2
  refine seq_vm_clean (mid := lsmpl.base 325)
    (P_mid :=
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cost s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
      ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
      memRegion (s0.sp - 4960#64) 320 ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      memRegion (s0.sp - 3056#64) 352 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ b0) ∗ ((s0.sp - 2088#64) ↦₆₄ b1) ∗ ((s0.sp - 2080#64) ↦₆₄ b2) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun s1 =>
      s1.sp = s0.sp - 4992#64 ∧
      TraceVRegs s1 s0 ∧
      s1.readReg64 .x0 = st.v ∧
      s1.readReg64 .x8 = s0.sp - 3056#64 ∧
      s1.readReg64 .x19 = ret ∧
      s1.readReg64 .x21 = pre.index.zeroExtend 64 ∧
      s1.readReg64 .x22 = pre.epoch ∧
      s1.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length ∧
      s1.readReg64 .x24 = remPtr ∧
      s1.readReg64 .x25 = pre.version.zeroExtend 64 ∧
      s1.readReg64 .x26 = s0.sp - 3056#64 ∧
      s1.readReg64 .x27 = s0.sp - 3056#64 ∧
      s1.readReg64 .x29 = s0.sp - 96#64 ∧
      s1.readReg64 Reg.lr = spqrRecvPlacedEntry + 328#64)
    ?_ ?_
  · dsimp only [spqrRecvPlacedEntry]
    by_vm_steps (
      wp_steps 4
      refine align_pre_wp (by sep_ac_rfl) ?_
      wp_done
    )
  · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, ⟨htr1, hvregs1⟩, hx0_1, hx8_1, hx19_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx29_1, hlr1⟩
    rw [← A.pool_transport lim st_cost s s1 hvm1]
    apply SepWP.done hpc1 hrun1
    unfold spqrRecvRoPlacedAt
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) decodeStateStackX (by decide)))
      (by sep_focus) ?_
    have hs1_align : s1.spAligned = true := by
      rw [State.spAligned, hsp1]; exact hfsp_align
    refine LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget.SepWPpLS.call_lscro
      hdec_ok (⟨st, s0.sp - 3056#64⟩, st_cost)
      hpc1 hrun1 hs1_align hlr1
      (by rw [htr1])
      (fun _ => Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm)
        (Entails.pure_left fun h => False.elim h))
      (fun _ _ => rfl)
      (by
        dsimp only [spqrDecodeStatePlacedSpecOfEnv]
        rw [← hsp1]
        exact frame_pure_pre ⟨hx8_1, hx0_1, hst_len, hFit_dec⟩ (by sep_focus))
      ?_
    intro sm hpcm hrunm hspm hcsm
    have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
    rcases hcsm with ⟨hx19_c, _, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, _, hxfp_c, _⟩
    dsimp only [spqrDecodeStatePlacedSpecOfEnv]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPpLS.exists_elim; intro evs_dec
    refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, hevs_dec⟩
    have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm, htr1], by rw [hvregs_c, hvregs1]⟩
    have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm, hsp1]
    have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c, hx19_1]
    have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c, hx21_1]
    have hx22_sm : sm.readReg64 .x22 = pre.epoch := by rw [hx22_c, hx22_1]
    have hx23_sm : sm.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length := by rw [hx23_c, hx23_1]
    have hx24_sm : sm.readReg64 .x24 = remPtr := by rw [hx24_c, hx24_1]
    have hx25_sm : sm.readReg64 .x25 = pre.version.zeroExtend 64 := by rw [hx25_c, hx25_1]
    have hx26_sm : sm.readReg64 .x26 = s0.sp - 3056#64 := by rw [hx26_c, hx26_1]
    have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c, hx27_1]
    have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
      change sm.readReg64 Reg.fp = s0.sp - 96#64
      rw [hxfp_c]; exact hx29_1
    have hsp_stk : stackAt s1.sp decodeStateStackX = stackAt (s0.sp - 4992#64) decodeStateStackX := by
      rw [hsp1]
    refine SepWPpLS.focus_weaken (Entails.of_eq hsp_stk) (by sep_focus) ?_
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) decodeStateStackX (by decide)).symm)
      (by sep_focus) ?_
    have hro_fold :
        v1StateJumpTablesPlacedAt ∗
          statesFromPbJumpTablePlacedAt ∗
          statesRecvRoPlacedAt ∗
          statesIntoPbJumpTablePlacedAt ⊢
        spqrRecvRoPlacedAt := Entails.refl _
    refine SepWPpLS.focus_weaken hro_fold (by sep_focus) ?_
    cases hdec : spqrDecodeState st.bytes with
    | error e =>
      have hevs_err : Env evs_dec := by
        simpa using hEnv_dec evs_dec hevs_dec [] (fun _ h => nomatch h)
      apply SepWPpLS.of_sepWP_ret
      exact step_decode_err_328_placed_ofEnv H_inner A lim st_cost Env evs_dec hevs_err
        F K ext st msg ret pre e d0 d1 d2 d3 b0 b1 b2
        hpre hdec s0 sm _ R _ rfl hs0_align
        hpcm hrunm hspm' htr_sm' hx19_sm hx27_sm
        (by sep_ac_rfl)
    | ok pre_pb =>
      apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 408#64)
      refine step_decode_ok_328_to_408_placed H_inner A lim (MC.stepEvents evs_dec st_cost)
        ext hmemcpy_ok h_inner_eq st msg ret pre_pb
        d0 d1 d2 d3 b0 b1 b2 s0 sm _ _ hs0_align
        hpcm hrunm hspm' htr_sm' hx19_sm hx26_sm hx27_sm
        (by sep_ac_rfl)
        ?_
      intro w0 w1 w2 w3 bs96 sm2 Pm2 hw0_ne hbs96 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hPm2
      apply SepWP.done hpc2 hrun2
      exact step_dispatch_408_placed_ofEnv H_inner A lim st_cost Env evs_dec
        (hEnv_dec evs_dec hevs_dec) F K ext hC hmemcpy_ok h_inner_eq st msg ret pre remPtr pre_pb
        d0 d1 d2 d3 w0 w1 w2 w3 bs96 hpre hvalid hdec hw0_ne hbs96 s0 sm2 Pm2 R
        (htail_gt evs_dec hevs_dec) (htail_lt evs_dec hevs_dec) (htail_eq evs_dec hevs_dec)
        hs0_align hpc2 hrun2 hsp2 htr2
        hx19_2 hx20_2
        (by rw [hx21_2, hx21_sm])
        (by rw [hx22_2, hx22_sm])
        (by rw [hx23_2, hx23_sm])
        (by rw [hx24_2, hx24_sm])
        (by rw [hx25_2, hx25_sm])
        hx27_2 hx28_2
        (by rw [hx29_2, hx29_sm])
        hPm2

theorem step_decode_and_dispatch_placed {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        optProtoInnerStateAt A.repAlloc a opt)
    (hdec_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec H_inner A lim)))
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (s0 s : State) (P R : SepProp)
    (hFit_dec : FitsEnv MC lim st_cost (DecodeStateEnv ⟨st, s0.sp - 3056#64⟩))
    (hEnv_dec : ∀ evs_dec, DecodeStateEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
      SpqrRecvEnv st msg evs_dec)
    (htail_gt : ∀ evs_dec, DecodeStateEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
      V0ChainPlacedTail A lim st_cost evs_dec F K ext st msg ret s0 R)
    (htail_lt : ∀ evs_dec, DecodeStateEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
      InitInnerPlacedTail A lim st_cost evs_dec F K ext st msg ret s0 R)
    (htail_eq : ∀ evs_dec, DecodeStateEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
      V1RatchetPlacedTailLS A lim st_cost evs_dec F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 312#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_decode_and_dispatch_placed_ofEnv H_inner A lim st_cost
    DecodeStateEnv DecodeStateEnv (SpqrRecvEnv st msg)
    F K ext hC hmemcpy_ok h_inner_eq hdec_ok st msg ret pre remPtr hst_len hpre hvalid s0 s P R
    hFit_dec
    (fun evs_dec hdec_evs _ hd => SpqrRecvEnv.append_freeOnly (hEnv_dec evs_dec hdec_evs) hd)
    htail_gt htail_lt htail_eq hs0_align hpc hrun hsp htr
    hx0 hx19 hx21 hx22 hx23 hx24 hx25 hx29 hP

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudget
