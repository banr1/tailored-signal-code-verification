/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Relocatable `Ordering::Greater` (`V0ChainPlacedTail`) for `spqr::recv`

Relocatable symbolic execution of the V0 chain-ratchet branch (`+496..+740`, `+2108..+2420`,
`+2920..+2948`) of `spqr::recv` (Block `329`), discharging `V0ChainPlacedTail`.
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
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.Send
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

@[simp] private theorem except_bind_ok_iff {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by cases m <;> simp [Bind.bind, Except.bind]
@[simp] private theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl
@[simp] private theorem decoderFromPbStateDecode_none :
    decoderFromPbStateDecode spqrPolyApi none = .error (.err .stateDecode) := rfl
@[simp] private theorem pure_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) : (pure x >>= f) = f x := rfl
@[simp] private theorem ok_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl
@[simp] private theorem except_mapError_eq_ok_iff {ε ε' α : Type} {f : ε → ε'} {m : Except ε α} {a : α} :
    m.mapError f = .ok a ↔ m = .ok a := by cases m <;> simp [Except.mapError]
@[simp] private theorem liftSpqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    liftSpqrPanic r = .ok v ↔ r = .ok v := by cases r <;> simp [liftSpqrPanic]
@[simp] private theorem liftM_spqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    (liftM r : Except StatesPanic α) = .ok v ↔ r = .ok v := by
  cases r <;> simp [liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
@[simp] private theorem statesResult_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε] {r : Except ε α} {v : α} :
    StatesResult.ofPanic r = .ok v ↔ r = .ok v := by cases r <;> simp [StatesResult.ofPanic]

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  Prost.EncodeToVec.extractLsb_lo_append64 Prost.EncodeToVec.extractLsb_hi_append64
  ult_one_toI32
attribute [local simp, local arm64_norm, local wp_norm]
  fp_sub_32_add_eq hsp_add_560_eq' fp_sub_48_add_eq hsp_add_544_eq'

/-! ## 1. `step_v0_after_chainFrom_604_placed` (`+604 .. +740 -> +2184 / +2540`) -/

/-- Placed shared continuation after `chain_from` succeeds in `Ordering::Greater` (`+604 ..
    +740`): moves `chain0 : Chain` (`88`B) into `s0.sp - 4288#64`, calls `Chain::recv_key(0,
    pre.index)` (`lsmpl.base 366`), and branches to `step_v0_recvKey_ok_2184_placed` (`+2184`)
    on `Ok` or drops `chain1` (`lsmpl.base 269`) and jumps to `step_drop_pre_2540_placed`
    (`+2540`) on `Err`. -/
theorem step_v0_after_chainFrom_604_placed {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (G_c0 : ChainProofs.ChainGhost) (chain0 : Chain) (pad_c0 : BitVec 32)
    (w0 w1 d880 d888 d896 d2896 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 604#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = G_c0.linksCap)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = s0.sp - 2096#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 352 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d880) ∗
      ((s0.sp - 4104#64) ↦₆₄ d888) ∗
      ((s0.sp - 4096#64) ↦₆₄ d896) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      memRegion (s0.sp - 3056#64) 88 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      words11SubAt s0.sp 2096 { chainWords11 G_c0 chain0 pad_c0 with w0 := d2896 } ∗
      chainAtHeap A G_c0 chain0 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hrk_ok := hC.chainRecvKey_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have hfits : ChainProofs.RecvPrevFits chain0 :=
    recvPrevFits_of_chainFrom (F := F) (K := K) hst_len hdec hcf
  subst hP
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 366)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine SepWP.focus_weaken (memRegion_88_sub_entails_words11 s0.sp 4288) (by sep_focus) ?_
  wp_pull_exists; rename_i u4288
  rw [memRegion_88_sub3056_split_32_56 s0.sp, frame1912_split_err_2388 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i d48 d40 d32
  have hchainAt := words11SubAt_entails_chainAt A s0.sp 4288 G_c0 chain0 pad_c0
  dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hchainAt ⊢
  simp only [sepConj_assoc]
  wp_steps 19
  refine SepWP.focus_weaken hchainAt (by sep_focus) ?_
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainRecvKeyStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hrk_ok
    (⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ : ChainRecvKeyGhost)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = spqrRecvPlacedEntry + 680#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun sm => by
      dsimp only [chainRecvKeySpecX]
      have hpan := onPanic_of_chainRecvKey (F := F) (K := K) hpre hdec hvn hinner hmin hver_gt hcf s0 sm
      simpa only [State.trace_setPC, State.trace_setMem, State.trace_writeReg64,
        State.trace_writeVReg128, State.trace_setPState, allocFailedIn, htr] using hpan)
    (fun _ _ => rfl)
    (by
      dsimp only [chainRecvKeySpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *],
          by simp only [arm64_norm, *],
          hfits⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, _, _, _, _, hx27_c, hx28_c, hxfp_c, _⟩
  dsimp only [chainRecvKeySpecX]
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by
    rw [hx20_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = s0.sp - 3056#64 := by
    rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = s0.sp - 2096#64 := by
    rw [hx22_c]; simp only [arm64_norm, *]
  have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by
    rw [hx27_c]; simp only [arm64_norm, *]
  have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by
    rw [hx28_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64
    rw [hxfp_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainRecvKeyStackX (by decide)).symm)
    (by sep_focus) ?_
  cases hrk : chain0.recvKey (spqrHkdfWith F) 0#64 pre.index with
  | error ce =>
    cases ce with
    | panic p =>
      dsimp only [recvKeyPostAt]
      exact SepWPpLS.focus_pure (by sep_focus) False.elim
    | err e =>
      obtain ⟨herr_recv, hnp⟩ : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode) ∧
          ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
        spqrV1Recv_gt_recvKey_err hpre hdec hvn hinner hmin hver_gt hcf hrk
      apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
      dsimp only [recvKeyPostAt]
      refine SepWP.focus_weaken (recvKeyErrAt_entails_code_memRegion23 (s0.sp - 3056#64) e) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (err_payload_expose (s0.sp - 3056#64) (Top.ChainFromVersionNegotiation.spqrErrorTag e) 23 (by decide) (by decide))
        (by sep_focus) ?_
      wp_pull_exists; rename_i w3_err w2_err w1_err
      wp_focus_pure; intro hret8_err
      dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
      rw [memRegion_zero, emp_sepConj]
      unfold chainRepr
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      wp_pull_exists; rename_i G_c1
      rw [ret_48_split ret]
      wp_pull_exists; rename_i r3 r2 r1 r0
      apply sepWP_seq_lscl hcl
      wp_steps 15
      refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
      have hret_fold :
          ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
            ((ret + 8#64) ↦₆₄ w3_err) ∗
            ((ret + 16#64) ↦₆₄ w2_err) ∗
            ((ret + 24#64) ↦₆₄ w1_err) ∗
            memRegion (ret + 32#64) 16) ⊢
          recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
        rw [herr_recv]
        exact recv_err_words_foldX A ret w3_err w2_err w1_err
          (Top.ChainFromVersionNegotiation.spqrErrorTag e) (e == .stateDecode)
          (spqrErrorTag_eq_zero_iff e).to_iff hret8_err
      apply sepWP_seq_lscl hcl1 (mid := (blkPl_329).base + 2540#64)
      refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) Drop.dropSpqrChainStack (by decide)))
        (by sep_focus) ?_
      have hdrop_chain := subroutine_ok_withMemEq_of_lscl hC.dropChain_ok hcl1
      dsimp only [spqrRecvPlacedProg, Drop.dropSpqrChainSpec] at hdrop_chain
      wp_call hdrop_chain (⟨s0.sp - 4288#64, G_c1, chain0⟩ : Drop.DropSpqrChainGhost)
      simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
        sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) Drop.dropSpqrChainStack (by decide)).symm)
        (by sep_focus) ?_
      wp_steps 1
      refine ProofLib.SepWP.done (by simp only [spqrRecvPlacedEntry, arm64_norm, *]) (by simp only [arm64_norm, *]) fun hcl2 => ?_
      refine SepWP.focus_weaken
        (tail680_join_1952 s0.sp G_c0.linksPtr G_c0.linksHead d48 (chainWords11 G_c0 chain0 pad_c0))
        (by dsimp only [chainWords11]; sep_focus) ?_
      refine SepWP.focus_weaken
        (frame4544_join_err_740 s0.sp d880 d888 d896 1#64 w3_err w2_err w1_err
          w3_err w2_err w1_err (BitVec.ofNat 64 (G_c0.epochs.zip chain0.links).length)
          G_c0.nextRoot.cap G_c0.nextRoot.ptr)
        (by sep_focus) ?_
      refine sepWP_spqrRecvPlacedPost_of_post0 hnp ?_
      exact step_drop_pre_2540_placed A (spqrV1Recv F K) ext hC st msg ret vn pb w0 w1
        s0 _ _ R _ rfl hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; ac_rfl) hcl2
  | ok res =>
    rcases res with ⟨chain1, rawKey⟩
    have hok_recv := spqrV1Recv_gt_recvKey_ok (F := F) (K := K) hpre hdec hvn hinner hmin hver_gt hcf hrk
    have henc_len := encodeRaw_v0_state_len_lt (F := F) (K := K) hst_len hpre hdec hvn hinner hmin hver_gt hcf hrk
    apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 2184#64)
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
    dsimp only [recvKeyPostAt, recvKeyOkAt]
    rw [bv_sub_add_lit s0.sp 3056 8 (by decide) (by decide)]
    dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
    refine SepWP.focus_weaken (vecU8_sub_entails_header_buf A s0.sp 3048 rawKey) (by sep_focus) ?_
    wp_pull_exists; rename_i cap_rk ptr_rk
    dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
    wp_steps 7
    refine SepWP.focus_weaken
      (tail680_join_1952 s0.sp G_c0.linksPtr G_c0.linksHead d48 (chainWords11 G_c0 chain0 pad_c0))
      (by dsimp only [chainWords11]; sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_872_sub2968_split_ok_680 s0.sp))
      (by sep_focus) ?_
    wp_pull_exists; rename_i u5 u4
    apply ProofLib.SepWP.done (by simp only [spqrRecvPlacedEntry, arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_v0_recvKey_ok_2184_placed hC st msg ret vn pb chain1 rawKey w0 w1 cap_rk ptr_rk
      d880 d888 d896 0#64 cap_rk ptr_rk (BitVec.ofNat 64 rawKey.length) u4 u5
      (BitVec.ofNat 64 (G_c0.epochs.zip chain0.links).length) G_c0.nextRoot.cap G_c0.nextRoot.ptr
      henc_len hok_recv s0 _ _ R hs0_align
      (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl)

/-! ## 2. `step_v0_chain_none_2108_placed` (`+2108 .. +2140`, `+2384 .. +2388`, `+2920 .. +2948`) -/

/-- When `pre_pb.chain = none` in `Ordering::Greater`, `+2108` checks `vn.direction` and `vn.chainParams`:
    - Invalid `vn.direction` (`> 1`): jumps to `+2384` (`Error::StateDecode`) -> `step_v0_err_2388_placed`.
    - `vn.chainParams = none`: writes `15#8` (`Error::ChainNotAvailable`) at `+2132..+2140` -> `step_v0_err_2388_placed`.
    - `vn.chainParams = some cp`: jumps to `+2920`, calls `Chain::new` (`lsmpl.base 363`), and jumps to `+604` (`step_v0_after_chainFrom_604_placed`). -/
theorem step_v0_chain_none_2108_placed {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 d880 d888 d896 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hchain : pre_pb.chain = none)
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2108#64)
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
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 352 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d880) ∗
      ((s0.sp - 4104#64) ↦₆₄ d888) ∗
      ((s0.sp - 4096#64) ↦₆₄ d896) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      memRegion (s0.sp - 3056#64) 88 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      memRegion (s0.sp - 2096#64) 88 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hnew_ok := hC.chainNew_ok
  subst hP
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (vn_some_unpack_sub4992 A s0.sp w0 w1 vn))
    (by sep_focus) ?_
  rcases direction_fromI32_or vn.direction with
    ⟨dir, hdir_val, hdir_opt, hcond_hi⟩ | ⟨hdir_opt, hcond_hi⟩
  · cases hcp : vn.chainParams with
    | none =>
      have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .error .chainNotAvailable := by
        simp [chainFrom, chainFromVersionNegotiation, hchain, hdir_opt, hcp]
      obtain ⟨herr_recv, hnp⟩ : (spqrV1Recv F K).recv st.bytes msg.bytes =
          .error (Error.chainNotAvailable == .stateDecode) ∧ ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
        spqrV1Recv_gt_chainFrom_err hpre hdec hvn hinner hmin hver_gt hcf
      apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 2388#64)
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
      dsimp only [Top.ChainFromVersionNegotiation.optChainParamsPBAt]
      rw [memRegion_88_sub2096_split_byte8 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      wp_pull_exists; rename_i b0_err d2896
      wp_steps 9
      have hcp_fold :
          ((s0.sp - 4968#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 4968#64 + 4#64) 8 =
            Top.ChainFromVersionNegotiation.optChainParamsPBAt (s0.sp - 4968#64) vn.chainParams := by
        rw [hcp]; rfl
      refine SepWP.focus_weaken (Entails.of_eq hcp_fold) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (vn_some_unpack_sub4992 A s0.sp w0 w1 vn).symm)
        (by sep_focus) ?_
      have htag_cna : (15#8 : BitVec 8) = Top.ChainFromVersionNegotiation.spqrErrorTag .chainNotAvailable := rfl
      rw [htag_cna]
      refine SepWP.focus_weaken
        (byte_memRegion79_sub2096_to_v0_err s0.sp .chainNotAvailable)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (frame2544_join_v0 s0.sp d880 d888 d896) (by sep_focus) ?_
      apply ProofLib.SepWP.done (by simp only [spqrRecvPlacedEntry, arm64_norm, *]) (by simp only [arm64_norm, *])
      exact step_v0_err_2388_placed A F K ext hC st msg ret vn pb .chainNotAvailable
        w0 w1 d2896 herr_recv hnp s0 _ _ R hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl)
    | some cp =>
      let chain0 := chainNewVal (spqrHkdfWith F) vn.authKey dir cp
      have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 := by
        simp [chainFrom, chainFromVersionNegotiation, hchain, hdir_opt, hcp]; rfl
      apply SepWPpLS.of_sepWP (mid := lsmpl.base 363)
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
      refine SepWP.focus_weaken (vecU8At_sub4992_unpack A s0.sp w0 w1 vn.authKey) (by sep_focus) ?_
      wp_focus_pure; intro hlen64
      dsimp only [Top.ChainFromVersionNegotiation.optChainParamsPBAt]
      rw [bv_sub_add_lit s0.sp 4968 4 (by decide) (by decide),
          bv_sub_add_lit s0.sp 4968 8 (by decide) (by decide)]
      dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
      wp_steps 10
      apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPpLS.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainNewStackX (by decide)))
        (by sep_focus) ?_
      refine SepWPpLS.call_lscro hnew_ok
        (⟨s0.sp - 2096#64, false, w1, vn.authKey, dir, cp⟩ : ChainNewGhost)
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
        (rfl : _ = spqrRecvPlacedEntry + 2936#64)
        (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
        (fun sm => by
          dsimp only [chainNewSpecX]
          simpa only [State.trace_setPC, State.trace_setMem, State.trace_writeReg64,
            State.trace_writeVReg128, State.trace_setPState, allocFailedIn, htr] using onPanic_of_allocFailed)
        (fun _ _ => rfl)
        (by
          dsimp only [chainNewSpecX]
          refine frame_pure_pre
            ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
              by simp only [arm64_norm, *],
              by simp only [arm64_norm, *],
              by simp only [arm64_norm, *],
              by simp only [arm64_norm, *],
              hlen64⟩
            (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
                sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
        ?_
      intro sm hpcm hrunm hspm hcsm
      have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
      rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, _, _, _, _, hx27_c, hx28_c, hxfp_c, _⟩
      dsimp only [chainNewSpecX]
      refine SepWPpLS.focus_pure (by sep_focus) ?_; intro htr_sm
      have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
      have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm]; simp only [arm64_norm, *]
      have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
      have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
      have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c]; simp only [arm64_norm, *]
      have hx22_sm : sm.readReg64 .x22 = s0.sp - 2096#64 := by rw [hx22_c]; simp only [arm64_norm, *]
      have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c]; simp only [arm64_norm, *]
      have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by rw [hx28_c]; simp only [arm64_norm, *]
      have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
        change sm.readReg64 Reg.fp = s0.sp - 96#64
        rw [hxfp_c]; simp only [arm64_norm, *]
      simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
        sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
      refine SepWPpLS.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainNewStackX (by decide)).symm)
        (by sep_focus) ?_
      refine SepWPpLS.focus_weaken (vecU8At_sub4992_repack A s0.sp w0 w1 vn.authKey) (by sep_focus) ?_
      have hcp_fold :
          ((s0.sp - 4968#64) ↦₃₂ 1#32) ∗
            ((s0.sp - 4964#64) ↦₃₂ cp.maxJump) ∗
            ((s0.sp - 4960#64) ↦₃₂ cp.maxOooKeys) =
          Top.ChainFromVersionNegotiation.optChainParamsPBAt (s0.sp - 4968#64) vn.chainParams := by
        rw [hcp]
        dsimp only [Top.ChainFromVersionNegotiation.optChainParamsPBAt]
        rw [bv_sub_add_lit s0.sp 4968 4 (by decide) (by decide),
            bv_sub_add_lit s0.sp 4968 8 (by decide) (by decide)]
      refine SepWPpLS.focus_weaken (Entails.of_eq hcp_fold) (by sep_focus) ?_
      refine SepWPpLS.focus_weaken
        (Entails.of_eq (vn_some_unpack_sub4992 A s0.sp w0 w1 vn).symm)
        (by sep_focus) ?_
      refine SepWPpLS.focus_weaken
        (Entails.trans (chainNew_post_entails_chainRepr A (s0.sp - 2096#64) chain0)
          (chainRepr_sub_entails_words11 A s0.sp 2096 chain0))
        (by sep_focus) ?_
      apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 604#64)
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
      wp_pull_exists; rename_i G_c0 pad_c0
      wp_focus_pure; intro hcap_c0_ne
      have hz_c0 : (G_c0.linksCap + 1#64 == 0#64) = false :=
        add_one_beq_zero_of_ne_noneCap hcap_c0_ne
      have hnz_c0 : (G_c0.linksCap + 1#64 != 0#64) = true := by
        simp [bne, hz_c0]
      dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
      simp only [sepConj_assoc]
      wp_steps 4
      apply ProofLib.SepWP.done (by simp only [spqrRecvPlacedEntry, arm64_norm, bne, *]) (by simp only [arm64_norm, *])
      exact step_v0_after_chainFrom_604_placed hC st msg ret pre pre_pb vn pb G_c0 chain0 pad_c0
        w0 w1 d880 d888 d896 G_c0.linksCap
        hst_len hpre hdec hvn hinner hmin hver_gt hcf s0 _ _ R hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]; ac_rfl)
  · have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .error .stateDecode := by
      simp [chainFrom, chainFromVersionNegotiation, hchain, hdir_opt]
    obtain ⟨herr_recv, hnp⟩ : (spqrV1Recv F K).recv st.bytes msg.bytes =
        .error (Error.stateDecode == .stateDecode) ∧ ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
      spqrV1Recv_gt_chainFrom_err hpre hdec hvn hinner hmin hver_gt hcf
    apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 2388#64)
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    rw [memRegion_88_sub2096_split_byte8 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists; rename_i b0_err d2896
    wp_steps 5
    refine SepWP.focus_weaken
      (Entails.of_eq (vn_some_unpack_sub4992 A s0.sp w0 w1 vn).symm)
      (by sep_focus) ?_
    have htag_sd : (0#8 : BitVec 8) = Top.ChainFromVersionNegotiation.spqrErrorTag .stateDecode := rfl
    rw [htag_sd]
    refine SepWP.focus_weaken
      (byte_memRegion79_sub2096_to_v0_err s0.sp .stateDecode)
      (by sep_focus) ?_
    refine SepWP.focus_weaken (frame2544_join_v0 s0.sp d880 d888 d896) (by sep_focus) ?_
    apply ProofLib.SepWP.done (by simp only [spqrRecvPlacedEntry, arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_v0_err_2388_placed A F K ext hC st msg ret vn pb .stateDecode
      w0 w1 d2896 herr_recv hnp s0 _ _ R hs0_align
      (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl)

/-! ## 3. `step_ordering_greater_placed : V0ChainPlacedTail` (`+496 .. +600` and `+2164 .. +2180`) -/

/-- Placed `Ordering::Greater` branch (`+496`): dispatches on `pre_pb.chain`:
    - `pre_pb.chain = none`: jumps to `+2108` (`step_v0_chain_none_2108_placed`).
    - `pre_pb.chain = some chPb`: calls `Chain::from_pb` (`lsmpl.base 364`) and branches to `+604`
    (`step_v0_after_chainFrom_604_placed`) on `Ok` or `+2164 -> +2388` (`step_v0_err_2388_placed`) on `Err`. -/
theorem step_ordering_greater_placed {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp)
    (hs0_align : s0.spAligned = true) :
    V0ChainPlacedTail A F K ext st msg ret s0 R := by
  intro pre remPtr pre_pb vn pb w0 w1 w26 s P
    hpre _hrem hdec hvn hinner _hw0 _hw26 hmin hver_gt
    hpc hrun hsp htr hx19 hx20 hx21 _hx22 _hx23 _hx24 _hx26 hx27 hx28 hx29 hP
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
    dsimp only [ProtoRepr.optChainPBAt, LibsignalTripleRatchetRepr.noneCap]
    wp_steps 3
    refine SepWP.focus_weaken
      (word_rest72_to_memRegion_80 (s0.sp - 4944#64) 0xFFFFFFFFFFFFFFFF#64)
      (by rw [bv_sub_add_lit s0.sp 4944 8 (by decide) (by decide)]; sep_focus) ?_
    apply ProofLib.SepWP.done (by simp only [spqrRecvPlacedEntry, arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_v0_chain_none_2108_placed hC st msg ret pre pre_pb vn pb w0 w1 d880 d888 d896
      hst_len hpre hdec hvn hinner hchain hmin hver_gt s0 _ _ R hs0_align
      (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl)
  | some chPb =>
    apply SepWPpLS.of_sepWP (mid := lsmpl.base 364)
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    dsimp only [ProtoRepr.optChainPBAt]
    rw [chainPBAt_protoRepr_eq_exists A (s0.sp - 4944#64) chPb]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists; rename_i gPb
    refine SepWP.focus_weaken
      (chainPBAt_expose_cap A gPb (s0.sp - 4944#64) chPb)
      (by sep_focus) ?_
    wp_focus_pure; intro hcap_pb_ne
    have hz_pb : (gPb.linksCap + 1#64 == 0#64) = false :=
      add_one_beq_zero_of_ne_noneCap hcap_pb_ne
    wp_steps 7
    refine SepWP.focus_weaken
      (chainPBAt_unexpose_cap A gPb (s0.sp - 4944#64) chPb)
      (by sep_focus) ?_
    apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromPbStackX (by decide)))
      (by sep_focus) ?_
    refine SepWPpLS.call_lscro hfrom_pb_ok
      (⟨s0.sp - 3056#64, s0.sp - 4944#64, gPb, chPb⟩ : ChainFromPbCall)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
      (rfl : _ = spqrRecvPlacedEntry + 524#64)
      (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
      (fun sm => by
        dsimp only [chainFromPbSpecX]
        simpa only [State.trace_setPC, State.trace_setMem, State.trace_writeReg64,
          State.trace_writeVReg128, State.trace_setPState, allocFailedIn, htr] using onPanic_of_allocFailed)
      (fun _ _ => rfl)
      (by
        dsimp only [chainFromPbSpecX]
        refine frame_pure_pre
          ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
          (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
              sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
      ?_
    intro sm hpcm hrunm hspm hcsm
    have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
    rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, _, _, _, _, _, hx27_c, hx28_c, hxfp_c, _⟩
    dsimp only [chainFromPbSpecX]
    refine SepWPpLS.focus_pure (by sep_focus) ?_; intro htr_sm
    have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
    have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm]; simp only [arm64_norm, *]
    have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
    have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
    have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c]; simp only [arm64_norm, *]
    have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c]; simp only [arm64_norm, *]
    have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by rw [hx28_c]; simp only [arm64_norm, *]
    have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
      change sm.readReg64 Reg.fp = s0.sp - 96#64
      rw [hxfp_c]; simp only [arm64_norm, *]
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
      dsimp only [Top.ChainFromVersionNegotiation.noneCap]
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
      apply ProofLib.SepWP.done (by simp only [spqrRecvPlacedEntry, arm64_norm, *]) (by simp only [arm64_norm, *])
      exact step_v0_err_2388_placed A F K ext hC st msg ret vn pb e w0 w1 d2896
        herr_recv hnp s0 _ _ R hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl)
    | ok chain0 =>
      have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 := by
        simp [chainFrom, hchain, hfpb]
      apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 604#64)
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
      dsimp only [chainResultAt]
      refine SepWP.focus_weaken (chainRepr_sub_entails_words11 A s0.sp 3056 chain0) (by sep_focus) ?_
      refine SepWP.focus_weaken (memRegion_88_sub_entails_words11 s0.sp 2096) (by sep_focus) ?_
      wp_pull_exists; rename_i G_c0 pad_c0 u2096
      wp_focus_pure; intro hcap_c0_ne
      have hz_c0 : (G_c0.linksCap + 1#64 == 0#64) = false :=
        add_one_beq_zero_of_ne_noneCap hcap_c0_ne
      have hto88 := words11SubAt_to_memRegion_88 s0.sp 3056 (chainWords11 G_c0 chain0 pad_c0)
      dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hto88 ⊢
      simp only [sepConj_assoc]
      wp_steps 20
      refine SepWP.focus_weaken hto88 (by sep_focus) ?_
      apply ProofLib.SepWP.done (by simp only [spqrRecvPlacedEntry, arm64_norm, *]) (by simp only [arm64_norm, *])
      exact step_v0_after_chainFrom_604_placed hC st msg ret pre pre_pb vn pb G_c0 chain0 pad_c0
        w0 w1 G_c0.linksPtr G_c0.linksHead (BitVec.ofNat 64 (G_c0.epochs.zip chain0.links).length) u2096.w0
        hst_len hpre hdec hvn hinner hmin hver_gt hcf s0 _ _ R hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]; ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv
