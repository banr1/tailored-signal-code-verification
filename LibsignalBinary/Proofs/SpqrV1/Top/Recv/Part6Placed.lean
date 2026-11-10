/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1Placed
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import ProofLib.SepLogic.WPp

/-!
# Relocatable `Ordering::Less` Continuations for `spqr::recv`

Relocatable `.rodata` exposure helpers and the `spqr::chain_from` error (`+1320`) and
post-`Chain::into_pb` (`+1424`) continuations of `Ordering::Less` in `spqr::recv` (Block `329`).
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
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Recv.Placed

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

theorem spqrRecvRoPlacedAt_expose_logOff :
    spqrRecvRoPlacedAt ⊢
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      (∃∗ P_ro : SepProp, ⌜(lsLogFilterAddr ↦₆₄ 0#64) ∗ P_ro ⊢ spqrRecvRoPlacedAt⌝ ∗ P_ro) := by
  have h1 : ∀ P Q R S T U : SepProp,
      P ∗ Q ∗ (R ∗ ((lsLogFilterAddr ↦₆₄ 0#64) ∗ S) ∗ T ∗ U) ∗ statesIntoPbJumpTablePlacedAt =
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ (P ∗ Q ∗ (R ∗ S ∗ T ∗ U) ∗ statesIntoPbJumpTablePlacedAt) := by
    intro P Q R S T U; ac_rfl
  refine Entails.trans (Entails.of_eq (h1 _ _ _ _ _ _)) ?_
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right _ (Entails.pure_right ?_ (Entails.refl _))
  exact Entails.of_eq (h1 _ _ _ _ _ _).symm

theorem spqrRecvRoPlacedAt_expose_statesIntoPb :
    spqrRecvRoPlacedAt ⊢
      statesIntoPbJumpTablePlacedAt ∗
      (∃∗ P_ro : SepProp, ⌜statesIntoPbJumpTablePlacedAt ∗ P_ro ⊢ spqrRecvRoPlacedAt⌝ ∗ P_ro) := by
  unfold spqrRecvRoPlacedAt
  refine Entails.trans
    (Entails.of_eq (show
      Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        statesFromPbJumpTablePlacedAt ∗
        statesRecvRoPlacedAt ∗
        statesIntoPbJumpTablePlacedAt =
      statesIntoPbJumpTablePlacedAt ∗
        (Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
          statesFromPbJumpTablePlacedAt ∗
          statesRecvRoPlacedAt) by ac_rfl)) ?_
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right _ (Entails.pure_right ?_ (Entails.refl _))
  exact Entails.of_eq (by ac_rfl)

/-- Error path of `spqr::chain_from` in `Ordering::Less` (`+1320 .. +1348 -> +2424 .. +2456 ->
    +2540`). -/
theorem step_initInner_chainFrom_err_1320_placed {H_inner : V1InnerHeapPred} (A : RustAlloc)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State)
    (e : Error) (w0 w1 : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1320#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (s0.sp - 4992#64) vn ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 3056#64) none ∗
      memRegion (s0.sp - 2832#64) 736 ∗
      chainErrorAt (s0.sp - 2096#64) e ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hnone3 : (Drop.none3Cap' + 3#64 == 0#64) = true := rfl
  have hnone1 : (Top.ChainFromVersionNegotiation.noneCap + 1#64 == 0#64) = true := rfl
  apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [← vnTail_some_eq_versionNegotiationPBAt A (s0.sp - 4992#64) w0 w1 vn,
      bv_sub_add_lit s0.sp 4992 8,
      bv_sub_add_lit s0.sp 4992 16]
  dsimp only [Drop.optProtoPqRatchetInnerAt]
  rw [bv_sub_add_lit s0.sp 3056 8,
      chainErrorAt_unpack_words4 (s0.sp - 2096#64) e,
      bv_sub_add_lit s0.sp 2096 8,
      bv_sub_add_lit s0.sp 2096 16,
      bv_sub_add_lit s0.sp 2096 24,
      bv_sub_add_lit s0.sp 2096 32,
      frame1584_split_err s0.sp,
      ret_48_split ret]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i q0_err w3_err d0 d1 d2 r0 r1 r2 r3
  wp_focus_pure; intro htag_q0
  have htag_eq : BitVec.truncate 8 ((q0_err.extractLsb' 64 64) ++ (q0_err.extractLsb' 0 64)) =
      Top.ChainFromVersionNegotiation.spqrErrorTag e := by
    have hq : (q0_err.extractLsb' 64 64) ++ (q0_err.extractLsb' 0 64) = q0_err := by bv_kernel
    rw [hq, htag_q0]
  have hret_fold :
      ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 8#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((ret + 16#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((ret + 24#64) ↦₆₄ w3_err) ∗
        memRegion (ret + 32#64) 16) ⊢
      recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [herr]
    exact recv_err_q0_foldX A ret (q0_err.extractLsb' 64 64) w3_err q0_err e htag_q0
  have hw4_join := words4_rest_to_memRegion_88 (s0.sp - 2096#64)
    Top.ChainFromVersionNegotiation.noneCap (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err
  rw [bv_sub_add_lit s0.sp 2096 8,
      bv_sub_add_lit s0.sp 2096 16,
      bv_sub_add_lit s0.sp 2096 24,
      bv_sub_add_lit s0.sp 2096 32] at hw4_join
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hw4_join
  apply sepWP_seq_lscl hcl
  wp_steps 17
  refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
  refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
  refine SepWP.focus_weaken hw4_join (by sep_focus) ?_
  refine SepWP.focus_weaken
    (frame4544_join_err_2424 s0.sp (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err Drop.none3Cap')
    (by sep_focus) ?_
  refine sepWP_spqrRecvPlacedPost_of_post0 hnp ?_
  exact step_drop_pre_2540_placed A (spqrV1Recv F K) ext hC st msg ret vn pb w0 w1
    s0 _ _ R _ rfl hs0_align
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by ac_rfl) hcl1

/-- Continuation after `Chain::into_pb` in `Ordering::Less` (`+1424 .. +1528 -> +824 .. +880 ->
    +2540`). -/
theorem step_initInner_chainFrom_ok_1424_placed {H_inner : V1InnerHeapPred} (A : RustAlloc)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State) (ch : Chain)
    (w0 w1 w160 d0 d1 d2 : BitVec 64)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1424#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (s0.sp - 4992#64) vn ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      ((s0.sp - 4640#64) ↦₆₄ w160) ∗
      memRegion (s0.sp - 4632#64) 40 ∗
      ProtoRepr.chainPBAt A (s0.sp - 4592#64) ch.intoPb ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d0) ∗
      ((s0.sp - 4104#64) ↦₆₄ d1) ∗
      ((s0.sp - 4096#64) ↦₆₄ d2) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 3056#64) none ∗
      memRegion (s0.sp - 2832#64) 736 ∗
      memRegion (s0.sp - 2096#64) 88 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hdrop_chain := hC.dropOptProtoChain_ok
  dsimp only [Drop.dropOptProtoSpqrChainSpec] at hdrop_chain
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have hnone3 : (Drop.none3Cap' + 3#64 == 0#64) = true := rfl
  have hslt_m1 : BitVec.slt 0xFFFFFFFFFFFFFFFF#64 1#64 = true := rfl
  apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hdrop_chain hpc ⊢
  have hopt_some : ProtoRepr.chainPBAt A (s0.sp - 4592#64) ch.intoPb =
      ProtoRepr.optChainPBAt A (s0.sp - 4592#64) (some ch.intoPb) := rfl
  rw [← vnTail_some_eq_versionNegotiationPBAt A (s0.sp - 4992#64) w0 w1 vn,
      bv_sub_add_lit s0.sp 4992 8,
      bv_sub_add_lit s0.sp 4992 16,
      hopt_some]
  refine SepWP.focus_weaken (memRegion_224_sub_entails_words28 s0.sp 4512) (by sep_focus) ?_
  wp_pull_exists; rename_i u0 uDst
  refine SepWP.focus_weaken (optProtoPqRatchetInnerAt_none_sub_entails_words27 A s0.sp 3056) (by sep_focus) ?_
  wp_pull_exists; rename_i uSrc
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r0 r1 r2 r3
  have hret_fold :
      ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 1#64) ∗ ((ret + 16#64) ↦₆₄ 0#64) ∗
        ((ret + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (ret + 32#64) 16) ⊢
      recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [hok]
    exact recv_ok_empty_foldX A ret
  have hjoin_dst := words27SubAt_to_memRegion_224 s0.sp 4512 Drop.none3Cap' uSrc
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hjoin_dst
  have hjoin_src := words27SubAt_to_memRegion_224 s0.sp 3056 Drop.none3Cap' uSrc
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hjoin_src
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  simp only [sepConj_assoc]
  apply sepWP_seq_lscl hcl
  wp_steps 37
  refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
  apply sepWP_seq_lscl hcl1 (mid := (blkPl_329).base + 2540#64)
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack80 (by decide)))
    (by sep_focus) ?_
  wp_call (subroutine_ok_withMemEq_of_lscl hdrop_chain hcl1) ⟨s0.sp - 4592#64, some ch.intoPb⟩
  have hsp_eq : stackAt s.sp dropStack80 = stackAt (s0.sp - 4992#64) dropStack80 := by rw [hsp]
  refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack80 (by decide)).symm)
    (by sep_focus) ?_
  wp_steps 2
  refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) fun hcl2 => ?_
  refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
  refine SepWP.focus_weaken hjoin_dst (by sep_focus) ?_
  refine SepWP.focus_weaken hjoin_src (by sep_focus) ?_
  refine SepWP.focus_weaken (frame4544_join_ok_880 s0.sp 0xFFFFFFFFFFFFFFFF#64 d0 d1 d2) (by sep_focus) ?_
  refine sepWP_spqrRecvPlacedPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
  exact step_drop_pre_2540_placed A (spqrV1Recv F K) ext hC st msg ret vn pb w0 w1
    s0 _ _ R _ rfl hs0_align
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by ac_rfl) hcl2

end CryptoVerification.SpqrV1.Top.Recv
