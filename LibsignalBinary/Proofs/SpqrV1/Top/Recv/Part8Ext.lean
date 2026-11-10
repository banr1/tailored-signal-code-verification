/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsExt
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: Extended Hook-Stack (`*Ext`) `Ordering::Greater` Continuation

Proves `step_v0_recvKey_ok_2184_ext` (`+2184..+2380 -> +1040`) for `spqr::recv` under
`SpqrRecvContractsExt`.
-/

@[expose] public section

set_option autoImplicit false

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
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
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
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64
attribute [local simp, local arm64_norm, local wp_norm]
  fp_sub_32_eq hsp_add_560_eq_v0 fp_sub_48_eq hsp_add_544_eq_v0

/-- Contract-parameterized (`*Ext`) success continuation of `Chain::recv_key` in
    `Ordering::Greater` (`+2184 .. +2380 -> +1040`). -/
theorem step_v0_recvKey_ok_2184_ext {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State)
    (chain1 : Chain) (rawKey : Bytes)
    (w0 w1 cap_rk ptr_rk : BitVec 64)
    (d880 d888 d896 u0 u1 u2 u3 u4 u5 e0 e1 e2 : BitVec 64)
    (henc_len :
      (PqRatchetState.encodeRaw
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }).length < 2 ^ 63)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) },
        some rawKey))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2184#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = s0.sp - 3056#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 2096#64)
    (hP : P =
      spqrRecvRoAt img.base ∗
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
      chainRepr A (s0.sp - 4288#64) chain1 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d880) ∗
      ((s0.sp - 4104#64) ↦₆₄ d888) ∗
      ((s0.sp - 4096#64) ↦₆₄ d896) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      ((s0.sp - 3056#64) ↦₆₄ u0) ∗
      ((s0.sp - 3048#64) ↦₆₄ u1) ∗
      ((s0.sp - 3040#64) ↦₆₄ u2) ∗
      ((s0.sp - 3032#64) ↦₆₄ u3) ∗
      ((s0.sp - 3024#64) ↦₆₄ u4) ∗
      ((s0.sp - 3016#64) ↦₆₄ u5) ∗
      memRegion (s0.sp - 3008#64) 80 ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ cap_rk) ∗
      ((s0.sp - 2088#64) ↦₆₄ ptr_rk) ∗
      ((s0.sp - 2080#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
      RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ∗
      ((s0.sp - 2072#64) ↦₆₄ e0) ∗
      ((s0.sp - 2064#64) ↦₆₄ e1) ∗
      ((s0.sp - 2056#64) ↦₆₄ e2) ∗
      memRegion (s0.sp - 2048#64) 1952 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hb : img.base &&& 0xfff#64 = 0#64 := hC.base_aligned
  have hinto_pb := spqrRecv_chainIntoPb_ok_ext hC
  have henc_ok := spqrRecv_encodeToVec_ok_ext hC
  have hdrop_st := spqrRecv_dropPqRatchetState_ok hC.hdealloc
  simp only [Drop.dropProtoPqRatchetStateSpec] at hdrop_st
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  apply SepWPpI.of_sepWP
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
      bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::into_pb"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hdrop_st hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 2184 28
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 2212 124
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 2336 48
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  unfold chainRepr
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i G_c1
  wp_steps 7
  apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpI.call_inImage hinto_pb ⟨s0.sp - 3008#64, s0.sp - 4288#64, G_c1, chain1⟩
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = entry + 2212#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed)
    (fun _ _ => rfl)
    (by
      dsimp only [chainIntoPbSpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_cm, _, _, hx22_cm, _⟩
  dsimp only [chainIntoPbSpecX]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_cm]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = s0.sp - 2096#64 := by
    rw [hx22_cm]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)).symm)
    (by sep_focus) ?_
  apply SepWPpI.of_sepWP
    (mid := entry +
      bv% (ls_rel% "spqr::recv" "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
  refine SepWP.focus_weaken
    (words3_sub2096_to_memRegion_24 s0.sp cap_rk ptr_rk (BitVec.ofNat 64 rawKey.length))
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    ((relocOptVersionNegotiationPBTailAt A w0 w1 (some vn)).2.to_bytes (s0.sp - 4976#64))
    (by sep_focus) ?_
  wp_pull_exists; rename_i bs32
  wp_focus_pure; intro hlen32
  refine SepWP.focus_weaken (bytes32_expose_words4_move s0.sp hlen32) (by sep_focus) ?_
  wp_pull_exists; rename_i v2 v3 v4 v5
  wp_focus_pure; intro hdst32
  rw [← optProtoPqRatchetInnerAt_eq_drop hC.h_inner_eq]
  refine SepWP.focus_weaken
    ((relocOptProtoPqRatchetInnerAt H_inner A (some (.v1 pb))).2.to_bytes (s0.sp - 4864#64))
    (by sep_focus) ?_
  wp_pull_exists; rename_i bs224
  wp_focus_pure; intro hlen224
  refine SepWP.focus_weaken (bytes224_expose_words28_move s0.sp hlen224) (by sep_focus) ?_
  wp_pull_exists; rename_i w_in0 d_in
  wp_focus_pure; intro hdst224
  refine SepWP.focus_weaken (memRegion_224_sub_entails_words28 s0.sp 2928) (by sep_focus) ?_
  wp_pull_exists; rename_i u_in0 u_in
  have hassemble := assemble_pqRatchetStatePBAt_3056 hC.h_inner_eq s0.sp w0 w1 vn chain1.intoPb pb hlen32 hlen224
  rw [← hdst32, ← hdst224] at hassemble
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hassemble ⊢
  simp only [sepConj_assoc]
  wp_steps 31
  refine SepWP.focus_weaken hassemble (by sep_focus) ?_
  apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) (encodeToVecStackOf doReserveStackX) (by decide)))
    (by sep_focus) ?_
  refine SepWPpI.call_inImage henc_ok
    (⟨s0.sp - 2096#64, s0.sp - 3056#64,
      { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }⟩ :
      PqRatchetStateEncodeToVecGhost)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hspm']; exact hs0_align)
    (rfl : _ = entry + 2336#64)
    (by simp only [arm64_norm, htr_sm']; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed)
    (fun _ _ => rfl)
    (by
      dsimp only [pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], henc_len⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']; sep_focus))
    ?_
  intro sn hpcn hrunn hspn hcsn
  have hvregs_cn := hcsn.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsn with ⟨hx19_cn, _, _, hx22_cn, _⟩
  dsimp only [pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sn
  have htr_sn' : TraceVRegs sn s0 := ⟨by rw [htr_sn]; simp only [arm64_norm, *], by rw [hvregs_cn]; simp only [arm64_norm, *]⟩
  have hspn' : sn.sp = s0.sp - 4992#64 := by
    rw [hspn]; simp only [arm64_norm, *]
  have hx19_sn : sn.readReg64 .x19 = ret := by
    rw [hx19_cn]; simp only [arm64_norm, *]
  have hx22_sn : sn.readReg64 .x22 = s0.sp - 2096#64 := by
    rw [hx22_cn]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) (encodeToVecStackOf doReserveStackX) (by decide)).symm)
    (by sep_focus) ?_
  apply SepWPpI.of_sepWP_ret
  refine SepWP.focus_weaken
    (vecU8_sub_entails_header_buf A s0.sp 2096
      (PqRatchetState.encodeRaw
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
    (by sep_focus) ?_
  wp_pull_exists; rename_i cap_st ptr_st
  rw [← protoPqRatchetStateAt_eq_pqRatchetStatePBAt]
  refine SepWP.focus_weaken (spqrRecvRoAt_expose_dropJumpTable img.base) (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro
  wp_focus_pure; intro hP_ro
  rw [ret_48_split_6 ret]
  wp_pull_exists; rename_i r5 r4 r3 r2 r1 r0
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  wp_steps 11
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)))
    (by sep_focus) ?_
  wp_call hdrop_st
    ⟨s0.sp - 3056#64,
      { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }⟩
  have hsp_eq_drop : stackAt sn.sp dropStack96 = stackAt (s0.sp - 4992#64) dropStack96 := by rw [hspn']
  refine SepWP.focus_weaken (Entails.of_eq hsp_eq_drop) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)).symm)
    (by sep_focus) ?_
  wp_steps 1
  refine SepWP.focus_weaken hP_ro (by sep_focus) ?_
  have hfold_ret := recv_ok_some_foldX A ret
    (PqRatchetState.encodeRaw
      { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) })
    rawKey cap_st ptr_st cap_rk ptr_rk
  rw [← hok] at hfold_ret
  refine SepWP.focus_weaken hfold_ret (by sep_focus) ?_
  have hjoin := ownFrame_join_4896_ok_2380 s0.sp w0 w1 v2 v3 v4 v5 w_in0 d_in
    cap_rk ptr_rk (BitVec.ofNat 64 rawKey.length)
    cap_st ptr_st
    (BitVec.ofNat 64
      (PqRatchetState.encodeRaw
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }).length)
    cap_rk ptr_rk (BitVec.ofNat 64 rawKey.length)
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hjoin
  unfold Drop.protoPqRatchetStateSize
  refine SepWP.focus_weaken hjoin (by sep_focus) ?_
  refine sepWP_spqrRecvPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
  exact step_epilogue img.base A (spqrV1Recv F K) ext st msg ret s0 _ _ R _ rfl
    (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hs0_align (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv
