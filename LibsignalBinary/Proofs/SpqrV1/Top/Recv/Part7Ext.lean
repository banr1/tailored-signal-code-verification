/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsExt
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: Extended Hook-Stack (`*Ext`) `Ordering::Less` (`InitInnerTail`)

Proves `step_ordering_less_ext` (`+1076..+1420`) for `spqr::recv` under `SpqrRecvContractsExt`.
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
  sp_sub_96_sub_48 hsp_add_544

/-- Contract-parameterized (`*Ext`) success path of `spqr::chain_from` in `Ordering::Less`
    (`+1320 .. +1420 -> +1424`). -/
theorem step_initInner_chainFrom_ok_1320_ext {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State) (ch : Chain)
    (w0 w1 : BitVec 64)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1320#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hP : P =
      spqrRecvRoAt img.base ∗
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
      chainRepr A (s0.sp - 2096#64) ch ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hinto_pb := spqrRecv_chainIntoPb_ok_ext hC
  subst hP
  apply SepWPpI.of_sepWP
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
      bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::into_pb"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1320 104
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  rw [frame1584_split_ok_1320 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i d2 d1 d0 w160
  refine SepWP.focus_weaken (chainRepr_sub_entails_words11 A s0.sp 2096 ch) (by sep_focus) ?_
  wp_pull_exists; rename_i G pad
  wp_focus_pure; intro hcap_ne
  have hz_ch : (G.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ne
  refine SepWP.focus_weaken (memRegion_88_sub_entails_words11 s0.sp 4200) (by sep_focus) ?_
  wp_pull_exists; rename_i dDst
  have hjoin_src := words11SubAt_to_memRegion_88 s0.sp 2096 (chainWords11 G ch pad)
  dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hjoin_src
  have hpack_dst := words11SubAt_entails_chainAt A s0.sp 4200 G ch pad
  dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hpack_dst
  dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  simp only [sepConj_assoc]
  wp_steps 26
  refine SepWP.focus_weaken hjoin_src (by sep_focus) ?_
  refine SepWP.focus_weaken hpack_dst (by sep_focus) ?_
  apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpI.call_inImage hinto_pb ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = entry + 1424#64)
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
  rcases hcsm with ⟨hx19_c, hx20_c, _⟩
  dsimp only [chainIntoPbSpecX]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by
    rw [hx20_c]; simp only [arm64_norm, *]
  simp only [arm64_norm, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)).symm)
    (by sep_focus) ?_
  exact step_initInner_chainFrom_ok_1424 A F K ext hC.base_aligned hC.hdealloc
    st msg ret vn pb ch w0 w1 w160
    G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
    hok s0 sm _ R hs0_align
    (by rw [spqrRecvEntry_eq, hentry]; exact hpcm)
    hrunm hspm' htr_sm' hx19_sm hx20_sm (by ac_rfl)

/-- Contract-parameterized (`*Ext`) `Ordering::Less` (`+1076 .. +1320`) when `vn.direction.ult
    2#32 = true`, calling `spqr::init_inner` at `initInnerStackExt` (`18912`B) and
    `spqr::chain_from` at `chainFromStackExt` (`18176`B). -/
theorem step_ordering_less_dir_some_ext {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_lt : pre.version < 1#8)
    (hdir_lt : vn.direction.ult 2#32 = true)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hsp_ne : s0.sp - 4992#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
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
      ProtoRepr.optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hx25' : s.readReg64 .x25 = 0#64 := by
    rw [hx25, zeroExtend64_eq_zero_of_lt_one hver_lt]
  clear hx25
  obtain ⟨dir, hdir_some, hdir_eq⟩ := direction_fromI32_of_ult_two hdir_lt
  have hule : (2#32).ule vn.direction = false := ult_two_imp_two_ule_false hdir_lt
  have hak_len : 32 + vn.authKey.length < 2 ^ 63 :=
    vn_authKey_len_bound_of_spqrDecodeState (F := F) (K := K) hst_len hdec hvn
  have hinit_ok := spqrRecv_initInner_ok_ext hC
  have hcf_ok := spqrRecv_chainFrom_ok_ext hC
  subst hP
  apply SepWPpI.of_sepWP
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
      bv% (2 ^ 64 - ls_rel% "spqr::init_inner" "spqr::recv"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1076 8
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1148 20
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1252 12
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1284 16
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1300 20
  generalize hentry : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry at *
  have hadrp_1152 := adrp_1152_ldr_ed0 hC.base_aligned hentry
  examples_hide_fetches
  rw [frame4544_split_1076 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i w30_slot b0_slot
  refine SepWP.focus_weaken (spqrRecvRoAt_expose_logOff img.base) (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro_log
  wp_focus_pure; intro hP_ro_log
  refine SepWP.focus_weaken (vn_some_expose_dir_and_initInner A s0.sp w0 w1 vn) (by sep_focus) ?_
  wp_pull_exists; rename_i P_vn
  wp_focus_pure; intro hw1_ne
  wp_focus_pure; intro hP_vn
  wp_steps 14
  refine SepWP.focus_weaken hP_ro_log (by sep_focus) ?_
  refine SepWP.focus_weaken (spqrRecvRoAt_expose_statesIntoPb img.base) (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro_into
  wp_focus_pure; intro hP_ro_into
  have hsplit3967 :
      memRegion (s0.sp - 4111#64) 3967 =
        memRegion (s0.sp - 4111#64) 1055 ∗
        memRegion (s0.sp - 3056#64) Drop.optProtoInnerStateSize ∗
        memRegion (s0.sp - 2832#64) 736 ∗
        memRegion (s0.sp - 2096#64) 88 ∗
        memRegion (s0.sp - 2008#64) 1864 := by
    unfold Drop.optProtoInnerStateSize
    rw [ProofLib.memRegion_split' (b := s0.sp - 4111#64) (n := 1055) (k := 2912)
        (b' := s0.sp - 3056#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 3056#64) (n := 224) (k := 2688)
        (b' := s0.sp - 2832#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 2832#64) (n := 736) (k := 1952)
        (b' := s0.sp - 2096#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 2096#64) (n := 88) (k := 1864)
        (b' := s0.sp - 2008#64) (by decide) (by bv_omega) (by decide)]
  rw [hsplit3967]
  simp only [sepConj_assoc]
  apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) initInnerStackExt (by decide)))
    (by sep_focus) ?_
  refine SepWPpI.call_inImage hinit_ok
    (⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ : InitInnerGhost)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = entry + 1300#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => by
      dsimp only [initInnerSpecExt, initInnerOnPanic]
      exact onPanic_of_allocFailed)
    (fun _ _ => rfl)
    (by
      dsimp only [initInnerSpecExt]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]; rfl,
          by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          hw1_ne, hak_len, hC.base_aligned⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, hx20_c, _⟩
  dsimp only [initInnerSpecExt, initInnerResultAt_v0]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by
    rw [hx20_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) initInnerStackExt (by decide)).symm)
    (by sep_focus) ?_
  refine SepWPpI.focus_weaken hP_vn (by sep_focus) ?_
  refine SepWPpI.focus_weaken hP_ro_into (by sep_focus) ?_
  refine SepWPpI.focus_weaken (frame4544_join_1320 s0.sp 0#8 0#32) (by sep_focus) ?_
  apply SepWPpI.of_sepWP
    (mid := entry + bv% (2 ^ 64 - ls_rel% "spqr::chain_from" "spqr::recv"))
  rw [optChainPBAt_protoRepr_eq_exists A (s0.sp - 4944#64) pre_pb.chain]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i gPb
  have hvn_ref :
      Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (s0.sp - 4992#64) vn ⊢
      ChainFrom.optVersionNegotiationRefAt A ⟨w0, w1⟩ (s0.sp - 4992#64) (some vn) :=
    Entails.pure_right hsp_ne (Entails.refl _)
  refine SepWP.focus_weaken hvn_ref (by sep_focus) ?_
  wp_steps 5
  apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromStackExt (by decide)))
    (by sep_focus) ?_
  refine SepWPpI.call_inImage hcf_ok
    (⟨s0.sp - 2096#64, s0.sp - 4944#64, s0.sp - 4992#64, gPb, ⟨w0, w1⟩, pre_pb.chain, some vn⟩ : ChainFromCall)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hspm']; exact hs0_align)
    (rfl : _ = entry + 1320#64)
    (by simp only [arm64_norm, htr_sm']; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed)
    (fun _ _ => rfl)
    (by
      dsimp only [chainFromSpecExt]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']; sep_focus))
    ?_
  intro sn hpcn hrunn hspn hcsn
  have hvregs_cn := hcsn.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsn with ⟨hx19_cn, hx20_cn, _⟩
  dsimp only [chainFromSpecExt, ChainFrom.optVersionNegotiationRefAt]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sn
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro _
  have htr_sn' : TraceVRegs sn s0 := ⟨by rw [htr_sn]; simp only [arm64_norm, *], by rw [hvregs_cn]; simp only [arm64_norm, *]⟩
  have hspn' : sn.sp = s0.sp - 4992#64 := by
    rw [hspn]; simp only [arm64_norm, *]
  have hx19_sn : sn.readReg64 .x19 = ret := by
    rw [hx19_cn]; simp only [arm64_norm, *]
  have hx20_sn : sn.readReg64 .x20 = w0 := by
    rw [hx20_cn]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromStackExt (by decide)).symm)
    (by sep_focus) ?_
  cases hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) with
  | error err =>
    obtain ⟨herr, hnp⟩ := spqrV1Recv_lt_one_chainFrom_err F K hpre hdec hvn hinner hmin hver_lt hdir_eq hcf
    exact step_initInner_chainFrom_err_1320 A F K ext hC.base_aligned hC.hdealloc
      st msg ret vn pb err w0 w1 herr hnp s0 sn _ R hs0_align
      (by dsimp only [tripleRatchetProgAtExt, spqrRecvName]; rw [hentry]; exact hpcn)
      hrunn hspn' htr_sn' hx19_sn hx20_sn (by dsimp only [chainResultAt]; ac_rfl)
  | ok ch =>
    have hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none) :=
      spqrV1Recv_lt_one_chainFrom_ok F K hpre hdec hvn hinner hmin hver_lt hdir_eq hcf
    exact step_initInner_chainFrom_ok_1320_ext hC st msg ret vn pb ch w0 w1 hok
      s0 sn _ R hs0_align
      (by dsimp only [tripleRatchetProgAtExt, spqrRecvName]; rw [hentry]; exact hpcn)
      hrunn hspn' htr_sn' hx19_sn hx20_sn (by dsimp only [chainResultAt]; ac_rfl)

/-- Combined contract-parameterized (`*Ext`) `Ordering::Less` (`+1076 .. +1420`) tail contract
    when `s0.sp - 4992#64 ≠ 0#64`. -/
theorem step_ordering_less_ext {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 w26 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw26 : InnerWordInv pre_pb.inner w26)
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_lt : pre.version < 1#8)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hsp_ne : s0.sp - 4992#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
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
      ProtoRepr.optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  by_cases hdir_lt : vn.direction.ult 2#32 = true
  · exact step_ordering_less_dir_some_ext hC st msg ret pre pre_pb vn pb w0 w1
      hst_len hpre hdec hvn hinner hmin hver_lt hdir_lt
      s0 s P R hs0_align hsp_ne hpc hrun hsp htr hx19 hx20 hx25 hx29 hP
  · exact step_ordering_less_dir_none A F K ext hC.base_aligned hC.hdealloc
      st msg ret pre pre_pb vn pb w0 w1 w26
      hpre hdec hvn hinner hw26 hmin hver_lt hdir_lt
      s0 s P R hs0_align hpc hrun hsp htr hx19 hx20 hx25 hx26 hx29 hP

end CryptoVerification.SpqrV1.Top.Recv
