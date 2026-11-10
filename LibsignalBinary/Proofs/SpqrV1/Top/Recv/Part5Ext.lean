/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsExt
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: Extended Hook-Stack (`*Ext`) Version Dispatch

**Checked by Lean.** Proves `step_decode_and_dispatch_ext` (`+312..+496`, `+744..+952`) for
`spqr::recv` under `SpqrRecvContractsExt`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sp_writeVReg128 (s : State) (v : VReg) (val : BitVec 128) :
    (s.writeVReg128 v val).sp = s.sp := rfl

private theorem sp_setPState (s : State) (p : PState) :
    (s.setPState p).sp = s.sp := rfl

/-- Relative-offset `memcpy` contract for `spqr::recv` from `AllocContractsX img A ext`
    (`extHookStack ≤ hookStack`). -/
theorem spqrRecv_memcpy_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hAx : AllocContractsX img A ext)
    (hookStack : Nat)
    (hle : extHookStack ≤ hookStack := by decide)
    (hbound : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "memcpy"))
      ((sessionMemcpySpec hookStack).inImage img) := by
  have hrel := Program.fnAddr_rel (k := num% (ls_rel% "spqr::recv" "memcpy"))
    (b := img.base) (X := Rust.withPanics ext) (O := fun _ => none)
    (ls_lemma% fnOff "spqr::recv") (ls_stub% "memcpy") (by decide)
  refine sub_ok_of_addr_eq ?_
    (hAx.session_memcpy_ok_at memcpyName 0 hookStack hle hbound (Nat.add_zero _))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, memcpyName]
  rw [hrel, BitVec.add_zero]

/-- `AllocContractsX` counterpart of `step_equal_792_pI` (`+792 .. +820 -> +1532`). -/
theorem step_equal_792_pI_ext (H_inner : V1InnerHeapPred) {img : Obj.Image} (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hAx : AllocContractsX img A ext)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw0_ne : w0 ≠ DecodeState.none2Cap)
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P R : SepProp)
    (htail : V1RatchetTailI img A F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 792#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
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
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hmemcpy := spqrRecv_memcpy_ok_ext hAx spqrRecvCalleeStackX
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  have hto :
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
        ((s0.sp - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
        optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
        Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ⊢
      ∃∗ bs352 : List (BitVec 8),
        ⌜bs352.length = 352⌝ ∗
        ((s0.sp - 4992#64) ↦ₛ bs352) ∗
        (relocPinnedPqRatchetStateAt H_inner A w0 w1 pre_pb).1 bs352 := by
    have h := (relocPinnedPqRatchetStateAt H_inner A w0 w1 pre_pb).2.to_bytes (s0.sp - 4992#64)
    unfold pinnedPqRatchetStateAt at h
    rw [optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at h
    rw [bv_sub_add_lit s0.sp 4992 8, bv_sub_add_lit s0.sp 4992 16,
        bv_sub_add_lit s0.sp 4992 48, bv_sub_add_lit s0.sp 4992 128] at h
    exact h
  have hsplit_4544 :
      memRegion (s0.sp - 4640#64) 4544 =
        memRegion (s0.sp - 4640#64) 352 ∗ memRegion (s0.sp - 4288#64) 4192 :=
    ProofLib.memRegion_split' (b := s0.sp - 4640#64) (n := 352) (k := 4192)
      (b' := s0.sp - 4288#64) rfl (by bv_omega) (by decide)
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  refine SepWPpI.focus_weaken hto (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPpI.exists_elim; intro bs352
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro hlen352
  rw [hsplit_4544]
  have hof :
      ((s0.sp - 4640#64) ↦ₛ bs352) ∗
        (relocPinnedPqRatchetStateAt H_inner A w0 w1 pre_pb).1 bs352 ⊢
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
        ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
        Drop.optProtoPqRatchetInnerAt A (s0.sp - 4512#64) pre_pb.inner := by
    have h := (relocPinnedPqRatchetStateAt H_inner A w0 w1 pre_pb).2.of_bytes (s0.sp - 4640#64) bs352 hlen352
    unfold pinnedPqRatchetStateAt at h
    rw [optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at h
    rw [bv_sub_add_lit s0.sp 4640 8, bv_sub_add_lit s0.sp 4640 16,
        bv_sub_add_lit s0.sp 4640 48, bv_sub_add_lit s0.sp 4640 128] at h
    exact h
  have hsrc_mem : ((s0.sp - 4992#64) ↦ₛ bs352) ⊢ memRegion (s0.sp - 4992#64) 352 := by
    rw [← hlen352]
    exact ProofLib.pointsToBytes_entails_memRegion (s0.sp - 4992#64) bs352
  have hdst_mem : memRegion (s0.sp - 4640#64) 352 = memRegion (s0.sp - 4640#64) bs352.length := by
    rw [hlen352]
  have hlen_eq : (352#64 : BitVec 64).toNat = bs352.length := hlen352.symm
  rw [hdst_mem]
  apply SepWPpI.of_sepWP
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
      bv% (ls_rel% "spqr::recv" "memcpy"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 792 32
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  wp_steps 4
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.call_inImage hmemcpy ⟨s0.sp - 4640#64, s0.sp - 4992#64, bs352⟩
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; exact hfsp_align)
    (rfl : _ = entry + 808#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => by
      dsimp only [sessionMemcpySpec, libcMemcpySpec]
      rw [← sepConj_emp ⌜False⌝]
      exact Entails.pure_left False.elim)
    (fun _ _ => rfl)
    (by
      dsimp only [sessionMemcpySpec, libcMemcpySpec]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, _, _, hx27_c, hx28_c, hxfp_c, _⟩
  dsimp only [sessionMemcpySpec]
  refine SepWPpI.focus_pure (by sep_focus) ?_; rintro ⟨_, htr_sm⟩
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = pre.epoch := by rw [hx22_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length := by rw [hx23_c]; simp only [arm64_norm, *]
  have hx24_sm : sm.readReg64 .x24 = remPtr := by rw [hx24_c]; simp only [arm64_norm, *]
  have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c]; simp only [arm64_norm, *]
  have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by rw [hx28_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64
    rw [hxfp_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]
  apply SepWPpI.of_sepWP (mid := entry + 1532#64)
  refine SepWP.focus_weaken hsrc_mem (by sep_focus) ?_
  refine SepWP.focus_weaken hof (by sep_focus) ?_
  refine SepWP.focus_weaken
    (optProtoPqRatchetInnerAt_expose_word A (s0.sp - 4512#64) pre_pb.inner) (by sep_focus) ?_
  wp_pull_exists; rename_i w8 P_inner
  wp_focus_pure; intro hw8
  wp_focus_pure; intro hunexp
  have hw8_bne3 : (w8 + 3#64 != 0#64) = true := by
    rw [hinner] at hw8
    dsimp [InnerWordInv] at hw8
    simp [bne, hw8]
  wp_steps 4
  refine SepWP.focus_weaken hunexp (by sep_focus) ?_
  have hinner_eq : Drop.optProtoPqRatchetInnerAt A (s0.sp - 4512#64) pre_pb.inner =
      Drop.optProtoInnerStateAt A (s0.sp - 4512#64) pb.innerState := by
    rw [hinner]; rfl
  rw [hinner_eq]
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact htail pre remPtr pre_pb pb w0 w1 _ _ hpre hvalid hdec hinner hw0_ne hmv hmin
    (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl)

/-- `AllocContractsX` + `DeallocOkExt` counterpart of `step_vn_none_744` (`+744`). -/
theorem step_vn_none_744_ext (H_inner : V1InnerHeapPred) {img : Obj.Image} (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (w1 w26 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = none)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp)
    (htail_eq : V1RatchetTailI img A F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 744#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = if (w26 + 3#64 != 0#64) = true then 1#64 else 0#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = noneCap)
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
      spqrRecvRoAt img.base ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ noneCap) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A noneCap w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  subst hP
  cases hinner : pre_pb.inner with
  | none =>
    have hw26_eq : w26 = none3Cap' := by
      rw [hinner] at hw26; exact hw26
    subst hw26_eq
    have hx8_0 : s.readReg64 .x8 = 0#64 := by
      rw [hx8]; rfl
    have hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none) :=
      spqrV1Recv_recv_of_ok
        (recv_vn_none_inner_none (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn
          (pqRatchetStateToPb_inner_none hinner))
    apply SepWPpI.of_sepWP_ret
    dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    spqr_recv_fetches_range img.base (Rust.withPanics ext) 744 48
    spqr_recv_fetches_range img.base (Rust.withPanics ext) 884 8
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
    examples_hide_fetches
    by_cases hv0 : pre.version = 0#8
    · rw [hv0] at hx25
      wp_steps 5
      refine sepWP_spqrRecvPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
      exact step_ok_none_912 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret pre_pb noneCap w1 none3Cap'
        hw26 hok s0 _ _ R _ rfl hs0_align
        (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [← hinner])
    · have hne0 := zeroExtend32_bne_zero_of_ne hv0
      wp_steps 5
      refine sepWP_spqrRecvPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
      exact step_ok_none_912 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret pre_pb noneCap w1 none3Cap'
        hw26 hok s0 _ _ R _ rfl hs0_align
        (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [← hinner])
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
        have hrust : LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) st.bytes msg.bytes =
            .error (.err .minimumVersion) := by
          refine recv_vn_none_lt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn ?_
          simp [stateVersion, pqRatchetStateToPb_inner_some hinner, Version.toU8, hlt]
        have herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error false :=
          spqrV1Recv_recv_of_err hrust
        have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
          spqrV1Recv_noPanic_of_err hrust
        apply SepWPpI.of_sepWP_ret
        dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
        spqr_recv_fetches_range img.base (Rust.withPanics ext) 744 12
        generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
        examples_hide_fetches
        rw [hv0] at hx25
        wp_steps 2
        refine sepWP_spqrRecvPost_of_post0 hnp ?_
        exact step_err_minVersion_752 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret pre_pb noneCap w1 w26
          hw26 herr s0 _ _ R _ rfl hs0_align
          (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hinner])
      · apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 792#64)
        dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
        spqr_recv_fetches_range img.base (Rust.withPanics ext) 744 48
        generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
        examples_hide_fetches
        rw [heq] at hx25
        wp_steps 5
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        exact step_equal_792_pI_ext H_inner A F K ext hAx h_inner_eq st msg ret pre remPtr pre_pb pb noneCap w1
          hpre hvalid hdec hinner (by decide) heq (by intro vn hvn'; rw [hvn] at hvn'; cases hvn')
          s0 _ _ R htail_eq hs0_align
          (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hinner])
      · have herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error false :=
          spqrV1Recv_recv_of_err
            (recv_vn_none_inner_some_gt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn
              (pqRatchetStateToPb_inner_some hinner) hgt)
        have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
          spqrV1Recv_noPanic_of_err
            (recv_vn_none_inner_some_gt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn
              (pqRatchetStateToPb_inner_some hinner) hgt)
        have hule1 := one_ule_zeroExtend64_of_gt hgt
        have hbne1 := zeroExtend32_bne_one_of_gt hgt
        apply SepWPpI.of_sepWP_ret
        dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
        spqr_recv_fetches_range img.base (Rust.withPanics ext) 744 40
        spqr_recv_fetches_range img.base (Rust.withPanics ext) 884 12
        generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
        examples_hide_fetches
        rw [hvn]
        dsimp only [optVersionNegotiationPBTailAt]
        wp_focus_pure; intro _
        wp_steps 5
        refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
        refine sepWP_spqrRecvPost_of_post0 hnp ?_
        exact step_err_versionMismatch_892 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret pre_pb w26
          hw26 herr s0 _ _ R _ rfl hs0_align
          (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [← hinner]; ac_rfl)

/-- `AllocContractsX` + `DeallocOkExt` counterpart of `step_vn_some_448` (`+448`). -/
theorem step_vn_some_448_ext (H_inner : V1InnerHeapPred) {img : Obj.Image} (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (w0 w1 w26 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hw0_ne : w0 ≠ DecodeState.none2Cap)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp)
    (htail_gt : V0ChainTail img A F K ext st msg ret s0 R)
    (htail_lt : InitInnerTail img A F K ext st msg ret s0 R)
    (htail_eq : V1RatchetTailI img A F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 448#64)
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
      spqrRecvRoAt img.base ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
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
    apply SepWPpI.of_sepWP_ret
    dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    spqr_recv_fetches_range img.base (Rust.withPanics ext) 448 16
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
    examples_hide_fetches
    rw [hvn]
    refine SepWP.focus_weaken
      (optVersionNegotiationPBTailAt_some_expose_minVersion A s0.sp w0 w1 vn) (by sep_focus) ?_
    wp_pull_exists; rename_i P_vn
    wp_focus_pure; intro hunexp
    wp_steps 3
    refine SepWP.focus_weaken hunexp (by sep_focus) ?_
    refine sepWP_spqrRecvPost_of_post0 hnp ?_
    exact step_err_minVersion_752 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret pre_pb w0 w1 w26
      hw26 herr s0 _ _ R _ rfl hs0_align
      (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [← hvn]; ac_rfl)
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
      apply SepWPpI.of_sepWP_ret
      dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      spqr_recv_fetches_range img.base (Rust.withPanics ext) 448 24
      generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
      examples_hide_fetches
      rw [hvn]
      refine SepWP.focus_weaken
        (optVersionNegotiationPBTailAt_some_expose_minVersion A s0.sp w0 w1 vn) (by sep_focus) ?_
      wp_pull_exists; rename_i P_vn
      wp_focus_pure; intro hunexp
      wp_steps 5
      refine SepWP.focus_weaken hunexp (by sep_focus) ?_
      refine sepWP_spqrRecvPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
      exact step_ok_none_912 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret pre_pb w0 w1 none3Cap'
        hw26 hok s0 _ _ R _ rfl hs0_align
        (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [← hvn, ← hinner]; ac_rfl)
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
          apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1076#64)
          dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
          spqr_recv_fetches_range img.base (Rust.withPanics ext) 448 48
          generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
          examples_hide_fetches
          rw [hvn]
          refine SepWP.focus_weaken
            (optVersionNegotiationPBTailAt_some_expose_minVersion A s0.sp w0 w1 vn) (by sep_focus) ?_
          wp_pull_exists; rename_i P_vn
          wp_focus_pure; intro hunexp
          rw [hv0] at hx25 hult hule
          dsimp at hx25 hult hule
          wp_steps 12
          refine SepWP.focus_weaken hunexp (by sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          exact htail_lt pre remPtr pre_pb vn pb w0 w1 w26 _ _
            hpre hvalid hdec hvn hinner hw0_ne hw26 hlt_min hlt
            (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by rw [hv0]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by rw [← hinner]; ac_rfl)
        · apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 792#64)
          dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
          spqr_recv_fetches_range img.base (Rust.withPanics ext) 448 48
          generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
          examples_hide_fetches
          rw [hvn]
          refine SepWP.focus_weaken
            (optVersionNegotiationPBTailAt_some_expose_minVersion A s0.sp w0 w1 vn) (by sep_focus) ?_
          wp_pull_exists; rename_i P_vn
          wp_focus_pure; intro hunexp
          rw [heq] at hx25 hult hule
          dsimp at hx25 hult hule
          wp_steps 10
          refine SepWP.focus_weaken hunexp (by sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          exact step_equal_792_pI_ext H_inner A F K ext hAx h_inner_eq st msg ret pre remPtr pre_pb pb w0 w1
            hpre hvalid hdec hinner hw0_ne heq
            (by intro vn' hvn'; rw [hvn] at hvn'; cases hvn'; exact heq ▸ hlt_min)
            s0 _ _ R htail_eq hs0_align
            (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by rw [← hvn, ← hinner]; ac_rfl)
        · have hule1 := one_ule_zeroExtend64_of_gt hgt
          have hule1_false := ule_one_zeroExtend64_false_of_gt hgt
          have hbne1 := zeroExtend32_bne_one_of_gt hgt
          have hugt1 := ugt_zeroExtend32_one_of_gt hgt
          apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 496#64)
          dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
          spqr_recv_fetches_range img.base (Rust.withPanics ext) 448 48
          generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
          examples_hide_fetches
          rw [hvn]
          refine SepWP.focus_weaken
            (optVersionNegotiationPBTailAt_some_expose_minVersion A s0.sp w0 w1 vn) (by sep_focus) ?_
          wp_pull_exists; rename_i P_vn
          wp_focus_pure; intro hunexp
          wp_steps 12
          refine SepWP.focus_weaken hunexp (by sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          exact htail_gt pre remPtr pre_pb vn pb w0 w1 w26 _ _
            hpre hvalid hdec hvn hinner hw0_ne hw26 hlt_min hgt
            (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by rw [← hinner]; ac_rfl)

/-- `AllocContractsX` + `DeallocOkExt` counterpart of `step_dispatch_408` (`+408 .. +444`). -/
theorem step_dispatch_408_ext (H_inner : V1InnerHeapPred) {img : Obj.Image} (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (d0 d1 d2 d3 w0 w1 w2 w3 : BitVec 64) (bs96 : List (BitVec 8))
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hw0_ne : w0 ≠ DecodeState.none2Cap)
    (hbs96 : bs96.length = 96)
    (s0 s : State) (P R : SepProp)
    (htail_gt : V0ChainTail img A F K ext st msg ret s0 R)
    (htail_lt : InitInnerTail img A F K ext st msg ret s0 R)
    (htail_eq : V1RatchetTailI img A F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 408#64)
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
      spqrRecvRoAt img.base ∗
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
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hreassemble := head16_bs96_entails_vnTailAndChainAt A (s0.sp - 4992#64) w0 w1 w2 w3 bs96 pre_pb hbs96
  rw [bv_sub_add_lit s0.sp 4992 16, bv_sub_add_lit s0.sp 4992 24,
      bv_sub_add_lit s0.sp 4992 32, bv_sub_add_lit s0.sp 4992 48] at hreassemble
  subst hP
  cases hvn : pre_pb.versionNegotiation with
  | none =>
    apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 744#64)
    dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    spqr_recv_fetches_range img.base (Rust.withPanics ext) 408 40
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
    examples_hide_fetches
    wp_pull_exists; rename_i P_tail
    wp_focus_pure; intro hP_tail_join
    refine SepWP.focus_weaken
      (optProtoPqRatchetInnerAt_expose_word A (s0.sp - 4864#64) pre_pb.inner) (by sep_focus) ?_
    wp_pull_exists; rename_i w26 P_inner
    wp_focus_pure; intro hw26
    wp_focus_pure; intro hunexp_inner
    wp_steps 9
    refine SepWP.focus_weaken hreassemble (by sep_focus) ?_
    refine SepWP.focus_weaken hunexp_inner (by sep_focus) ?_
    refine SepWP.focus_weaken hP_tail_join (by sep_focus) ?_
    rw [hvn]
    refine SepWP.focus_weaken (optVersionNegotiationPBTailAt_none_eq A w0 w1 (s0.sp - 4976#64)) (by sep_focus) ?_
    wp_focus_pure; intro hw0; subst hw0
    wp_steps 1
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_vn_none_744_ext H_inner A F K ext hb hAx hdealloc h_inner_eq st msg ret pre remPtr pre_pb w1 w26
      hpre hvalid hdec hvn hw26 s0 _ _ R htail_eq hs0_align
      (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, bne, cset_ne_eq, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [← hvn]; ac_rfl)
  | some vn =>
    apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 448#64)
    dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    spqr_recv_fetches_range img.base (Rust.withPanics ext) 408 40
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
    examples_hide_fetches
    wp_pull_exists; rename_i P_tail
    wp_focus_pure; intro hP_tail_join
    refine SepWP.focus_weaken
      (optProtoPqRatchetInnerAt_expose_word A (s0.sp - 4864#64) pre_pb.inner) (by sep_focus) ?_
    wp_pull_exists; rename_i w26 P_inner
    wp_focus_pure; intro hw26
    wp_focus_pure; intro hunexp_inner
    wp_steps 9
    refine SepWP.focus_weaken hreassemble (by sep_focus) ?_
    refine SepWP.focus_weaken hunexp_inner (by sep_focus) ?_
    refine SepWP.focus_weaken hP_tail_join (by sep_focus) ?_
    rw [hvn]
    refine SepWP.focus_weaken
      (optVersionNegotiationPBTailAt_some_cap_lt A w0 w1 (s0.sp - 4976#64) vn) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    have hne_none := Drop.cap_add_one_beq_zero_false hcap_lt
    wp_steps 1
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_vn_some_448_ext H_inner A F K ext hb hAx hdealloc h_inner_eq st msg ret pre remPtr pre_pb vn w0 w1 w26
      hpre hvalid hdec hvn hw0_ne hw26 s0 _ _ R htail_gt htail_lt htail_eq hs0_align
      (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, bne, cset_ne_eq, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [← hvn]; ac_rfl)

/-- `SepWPpI` + `AllocContractsX` counterpart of `step_decode_ok_328_to_408` (`+328 .. +408`). -/
theorem step_decode_ok_328_to_408_ext (H_inner : V1InnerHeapPred) {img : Obj.Image} (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hAx : AllocContractsX img A ext)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState)
    (d0 d1 d2 d3 b0 b1 b2 : BitVec 64)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 328#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = s0.sp - 3056#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hP : P =
      spqrRecvRoAt img.base ∗
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
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 408#64 →
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
      Pm = (spqrRecvRoAt img.base ∗
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
      SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sm Pm
        (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hmemcpy := spqrRecv_memcpy_ok_ext hAx spqrRecvCalleeStackX
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [decodeStateResultAt]
  have hsplit := protoPqRatchetStateAt_entails_head32_bs96_bs224 H_inner A (s0.sp - 3056#64) pre_pb
  rw [bv_sub_add_lit s0.sp 3056 8, bv_sub_add_lit s0.sp 3056 16,
      bv_sub_add_lit s0.sp 3056 24, bv_sub_add_lit s0.sp 3056 32] at hsplit
  refine SepWPpI.focus_weaken hsplit (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPpI.exists_elim; intro w0
  apply SepWPpI.exists_elim; intro w1
  apply SepWPpI.exists_elim; intro w2
  apply SepWPpI.exists_elim; intro w3
  apply SepWPpI.exists_elim; intro bs96
  apply SepWPpI.exists_elim; intro bs224
  refine SepWPpI.focus_pure (by sep_focus) ?_; rintro ⟨hw0_ne, hbs96, hbs224, hbs320⟩
  have hw0_cmn : (w0 + 2#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    apply hw0_ne
    change w0 = -2#64
    revert w0 heq; bv_kernel
  have hlen_eq : (320#64 : BitVec 64).toNat = (bs96 ++ bs224).length := hbs320.symm
  have hdst_eq : memRegion (s0.sp - 4960#64) (bs96 ++ bs224).length =
      memRegion (s0.sp - 4960#64) 320 := by rw [hbs320]
  rw [← hdst_eq]
  apply SepWPpI.of_sepWP
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
      bv% (ls_rel% "spqr::recv" "memcpy"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 328 80
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  wp_steps 13
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.call_inImage hmemcpy ⟨s0.sp - 4960#64, s0.sp - 3024#64, bs96 ++ bs224⟩
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
          sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; exact hfsp_align)
    (rfl : _ = entry + 408#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => by
      dsimp only [sessionMemcpySpec, libcMemcpySpec]
      rw [← sepConj_emp ⌜False⌝]
      exact Entails.pure_left False.elim)
    (fun _ _ => rfl)
    (by
      dsimp only [sessionMemcpySpec, libcMemcpySpec]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
              sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, _, hx27_c, hx28_c, hxfp_c, _⟩
  dsimp only [sessionMemcpySpec]
  refine SepWPpI.focus_pure (by sep_focus) ?_; rintro ⟨_, htr_sm⟩
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
      sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = s.readReg64 .x21 := by rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = s.readReg64 .x22 := by rw [hx22_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = s.readReg64 .x23 := by rw [hx23_c]; simp only [arm64_norm, *]
  have hx24_sm : sm.readReg64 .x24 = s.readReg64 .x24 := by rw [hx24_c]; simp only [arm64_norm, *]
  have hx25_sm : sm.readReg64 .x25 = s.readReg64 .x25 := by rw [hx25_c]; simp only [arm64_norm, *]
  have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c]; simp only [arm64_norm, *]
  have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by rw [hx28_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s.readReg64 .x29 := by
    change sm.readReg64 Reg.fp = s.readReg64 Reg.fp
    rw [hxfp_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
  have hbs_inner := bs320_entails_bs96_inner H_inner A (s0.sp - 4992#64) bs96 bs224 pre_pb hbs96 hbs224
  rw [bv_sub_add_lit s0.sp 4992 32, bv_sub_add_lit s0.sp 4992 128,
      optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at hbs_inner
  refine SepWPpI.focus_weaken hbs_inner (by sep_focus) ?_
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
  refine SepWPpI.focus_weaken hP_tail_intro (by unfold P_tail; sep_focus) ?_
  exact htail w0 w1 w2 w3 bs96 sm _ hw0_ne hbs96
    hpcm
    hrunm hspm' htr_sm'
    hx19_sm hx20_sm hx21_sm hx22_sm hx23_sm hx24_sm hx25_sm hx27_sm hx28_sm hx29_sm
    (by dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]; ac_rfl)

/-- `SpqrRecvContractsExt` counterpart of `step_decode_and_dispatch` (`+312 .. +496 / +1076 /
    +1532`). -/
theorem step_decode_and_dispatch_ext (H_inner : V1InnerHeapPred) {img : Obj.Image} {A : RustAlloc}
    {F : CryptoGames.LibsignalSession.ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (s0 s : State) (P R : SepProp)
    (htail_gt : V0ChainTail img A F K ext st msg ret s0 R)
    (htail_lt : InitInnerTail img A F K ext st msg ret s0 R)
    (htail_eq : V1RatchetTailI img A F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 312#64)
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
    (hP : P = spqrRecvPreambleFrame img.base A st msg ret s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hdec_call := spqrRecv_decodeState_ok_ext hC
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  subst hP
  unfold spqrRecvPreambleFrame
  apply SepWPpI.of_sepWP
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + bv% (2 ^ 64 - ls_rel% "spqr::decode_state" "spqr::recv"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 312 16
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine SepWP.focus_weaken (ownFrame_split_for_decode s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i d0 d1 d2 d3 b0 b1 b2
  wp_steps 4
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  unfold spqrRecvRoAt
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) decodeStateStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpI.call_inImage hdec_call ⟨st, s0.sp - 3056#64⟩
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; exact sp_sub_4992_aligned s0 hs0_align)
    (rfl : _ = entry + 328#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed)
    (fun _ _ => rfl)
    (by
      dsimp only [decodeStateSpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], hst_len⟩
        (by simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, _, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, _, hxfp_c, _⟩
  dsimp only [decodeStateSpecX]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by
    rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = pre.epoch := by
    rw [hx22_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length := by
    rw [hx23_c]; simp only [arm64_norm, *]
  have hx24_sm : sm.readReg64 .x24 = remPtr := by
    rw [hx24_c]; simp only [arm64_norm, *]
  have hx25_sm : sm.readReg64 .x25 = pre.version.zeroExtend 64 := by
    rw [hx25_c]; simp only [arm64_norm, *]
  have hx26_sm : sm.readReg64 .x26 = s0.sp - 3056#64 := by
    rw [hx26_c]; simp only [arm64_norm, *]
  have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by
    rw [hx27_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64
    rw [hxfp_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) decodeStateStackX (by decide)).symm)
    (by sep_focus) ?_
  have hro_fold :
      Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
        States.FromPb.statesFromPbJumpTableAt img.base ∗
        States.Recv.statesRecvRoAt img.base ∗
        States.IntoPb.statesIntoPbJumpTableAt img.base ⊢
      spqrRecvRoAt img.base := Entails.refl _
  refine SepWPpI.focus_weaken hro_fold (by sep_focus) ?_
  cases hdec : spqrDecodeState st.bytes with
  | error e =>
    apply SepWPpI.of_sepWP_ret
    exact step_decode_err_328 H_inner img.base A F K ext st msg ret pre e d0 d1 d2 d3 b0 b1 b2
      hpre hdec s0 sm _ R _ rfl hs0_align
      (by rw [spqrRecvEntry_eq, hentry]; exact hpcm)
      hrunm hspm' htr_sm' hx19_sm hx27_sm
      (by ac_rfl)
  | ok pre_pb =>
    refine step_decode_ok_328_to_408_ext H_inner A F K ext hC.hAx hC.h_inner_eq st msg ret pre_pb
      d0 d1 d2 d3 b0 b1 b2 s0 sm _ R hs0_align
      (by rw [spqrRecvEntry_eq, hentry]; exact hpcm)
      hrunm hspm' htr_sm' hx19_sm hx26_sm hx27_sm
      (by ac_rfl)
      ?_
    intro w0 w1 w2 w3 bs96 sm2 Pm2 hw0_ne hbs96 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hPm2
    exact step_dispatch_408_ext H_inner A F K ext hC.base_aligned hC.hAx hC.hdealloc hC.h_inner_eq st msg ret pre remPtr pre_pb
      d0 d1 d2 d3 w0 w1 w2 w3 bs96 hpre hvalid hdec hw0_ne hbs96 s0 sm2 Pm2 R
      htail_gt htail_lt htail_eq hs0_align hpc2 hrun2 hsp2 htr2
      hx19_2 hx20_2
      (by rw [hx21_2, hx21_sm])
      (by rw [hx22_2, hx22_sm])
      (by rw [hx23_2, hx23_sm])
      (by rw [hx24_2, hx24_sm])
      (by rw [hx25_2, hx25_sm])
      hx27_2 hx28_2
      (by rw [hx29_2, hx29_sm])
      hPm2

end CryptoVerification.SpqrV1.Top.Recv
