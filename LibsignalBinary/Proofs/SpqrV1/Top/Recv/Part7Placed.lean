/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1Placed
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp

/-!
# Relocatable `Ordering::Less` (`InitInnerPlacedTail`) for `spqr::recv`

Relocatable symbolic execution of the `Ordering::Less` (`+1076..+1420`) branch of `spqr::recv`
(Block `329`), discharging `InitInnerPlacedTail`.
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
open CryptoVerification.LibsignalTripleRatchet.Getters
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
attribute [local simp, local arm64_norm, local wp_norm] sp_sub_96_sub_48 hsp_add_544

/-! ## 1. Success Path of `spqr::chain_from` in `Ordering::Less` (`+1320 .. +1420 -> +1424`) -/

/-- Success path of `spqr::chain_from` in `Ordering::Less` (`+1320 .. +1420 -> +1424`): copies
    `ch : Chain` (`88`B) from `s0.sp - 2096#64` (`sp + 0xb50`) to `s0.sp - 4200#64` (`sp +
    0x318`), calls `Chain::into_pb` (Block `365`) writing to `s0.sp - 4592#64` (`sp + 0x190`),
    and continues to `step_initInner_chainFrom_ok_1424_placed`. -/
theorem step_initInner_chainFrom_ok_1320_placed {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State) (ch : Chain)
    (w0 w1 : BitVec 64)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none))
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
      chainRepr A (s0.sp - 2096#64) ch ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hinto_pb := hC.chainIntoPb_ok
  subst hP
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 365)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
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
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hinto_pb ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = spqrRecvPlacedEntry + 1424#64)
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
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by
    rw [hx20_c]; simp only [arm64_norm, *]
  simp only [arm64_norm, hsp]
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)).symm)
    (by sep_focus) ?_
  exact step_initInner_chainFrom_ok_1424_placed A F K ext hC
    st msg ret vn pb ch w0 w1 w160
    G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
    hok s0 sm _ R hs0_align
    hpcm hrunm hspm' htr_sm' hx19_sm hx20_sm (by ac_rfl)

/-! ## 2. `Ordering::Less` (`InitInnerPlacedTail`, `+1076 .. +1320`) -/

/-- When `¬(vn.direction.ult 2#32 = true)` (`Direction.fromI32? vn.direction = none`),
    `Ordering::Less` (`+1076 .. +1280`) stores `Err(InvalidStateEncoding)` (`tag = 0#8`) at
    `ret` and drops `pre_pb` via `step_drop_vn_936_placed` / `step_drop_pre_952_placed`. -/
theorem step_ordering_less_dir_none_placed {H_inner : V1InnerHeapPred} (A : RustAlloc)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 w26 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw26 : InnerWordInv pre_pb.inner w26)
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_lt : pre.version < 1#8)
    (hdir_ge : ¬(vn.direction.ult 2#32 = true))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
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
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hx25' : s.readReg64 .x25 = 0#64 := by
    rw [hx25, zeroExtend64_eq_zero_of_lt_one hver_lt]
  clear hx25
  have hule : (2#32).ule vn.direction = true := not_ult_two_imp_two_ule hdir_ge
  have hdir_none : Direction.fromI32? vn.direction = none := direction_fromI32_of_two_ule hule
  have herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error true :=
    spqrV1Recv_lt_one_dir_none F K hpre hdec hvn hinner hmin hver_lt hdir_none
  apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
  subst hP
  rw [← hinner]
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [frame4544_split_1076 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i w30_slot b0_slot
  refine SepWP.focus_weaken spqrRecvRoPlacedAt_expose_logOff (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro
  wp_focus_pure; intro hP_ro
  refine SepWP.focus_weaken
    (optVersionNegotiationPBTailAt_some_expose_direction A s0.sp w0 w1 vn) (by sep_focus) ?_
  wp_pull_exists; rename_i P_dir
  wp_focus_pure; intro hP_dir
  refine SepWP.focus_weaken (ret_48_split_byte8 ret) (by sep_focus) ?_
  wp_pull_exists; rename_i r0 b8 r2 r3
  have hfold := recv_err_byte_foldX A ret r2 r3 0#8 true (by decide)
  rw [← herr] at hfold
  apply sepWP_seq_lscl hcl
  wp_steps 14
  refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
  refine SepWP.focus_weaken hP_ro (by sep_focus) ?_
  refine SepWP.focus_weaken hP_dir (by sep_focus) ?_
  refine SepWP.focus_weaken (frame4544_join_1076 s0.sp 0#8 0#32) (by sep_focus) ?_
  refine SepWP.fold hfold (by sep_focus) ?_
  have hvn_dealloc :
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) (some vn) ⊢
      ⌜w0.toNat < 2 ^ 63⌝ ∗
        ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗ memRegion (s0.sp - 4976#64) 32 ∗
        vecCapPtrDealloc A w0 w1 := by
    have h8 : (s0.sp - 4992#64) + 8#64 = s0.sp - 4984#64 := bv_sub_add_lit s0.sp 4992 8
    have h16 : (s0.sp - 4992#64) + 16#64 = s0.sp - 4976#64 := bv_sub_add_lit s0.sp 4992 16
    rw [← h8, ← h16]
    exact vnTail_some_entails_dealloc A (s0.sp - 4992#64) w0 w1 vn
  refine SepWP.focus_weaken hvn_dealloc (by sep_focus) ?_
  wp_focus_pure; intro hcap_lt
  dsimp only [vecCapPtrDealloc]
  by_cases hc0 : (w0 == 0#64) = true <;>
    simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
  · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
    subst hw0
    wp_steps 2
    refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
    refine sepWP_spqrRecvPlacedPost_of_post0 (spqrV1Recv_noPanic_of_recv_err_true herr) ?_
    exact step_drop_pre_952_placed A (spqrV1Recv F K) ext hC st msg ret pre_pb w26 hw26
      s0 _ _ R _ rfl hs0_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; ac_rfl) hcl1
  · wp_steps 1
    refine sepWP_spqrRecvPlacedPost_of_post0 (spqrV1Recv_noPanic_of_recv_err_true herr) ?_
    exact step_drop_vn_936_placed A (spqrV1Recv F K) ext hC st msg ret pre_pb w0 w1 w26 hw26
      s0 _ _ R _ rfl hs0_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; ac_rfl) hcl1

/-- When `vn.direction.ult 2#32 = true` (`Direction.fromI32? vn.direction = some dir`),
    `Ordering::Less` (`+1076 .. +1320`) calls `spqr::init_inner` (`+1296`) with `v = .v0`, calls
    `spqr::chain_from` (`+1316`), and continues to `step_initInner_chainFrom_err_1320_placed` or
    `step_initInner_chainFrom_ok_1320_placed`. -/
theorem step_ordering_less_dir_some_placed {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
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
    (hpc : s.pc = spqrRecvPlacedEntry + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
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
      ProtoRepr.optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hx25' : s.readReg64 .x25 = 0#64 := by
    rw [hx25, zeroExtend64_eq_zero_of_lt_one hver_lt]
  clear hx25
  obtain ⟨dir, hdir_some, hdir_eq⟩ := direction_fromI32_of_ult_two hdir_lt
  have hule : (2#32).ule vn.direction = false := ult_two_imp_two_ule_false hdir_lt
  have hak_len : 32 + vn.authKey.length < 2 ^ 63 :=
    vn_authKey_len_bound_of_spqrDecodeState (F := F) (K := K) hst_len hdec hvn
  have hinit_ok := hC.initInner_ok
  have hcf_ok := hC.chainFrom_ok
  subst hP
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 324)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [frame4544_split_1076 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i w30_slot b0_slot
  refine SepWP.focus_weaken spqrRecvRoPlacedAt_expose_logOff (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro_log
  wp_focus_pure; intro hP_ro_log
  refine SepWP.focus_weaken (vn_some_expose_dir_and_initInner A s0.sp w0 w1 vn) (by sep_focus) ?_
  wp_pull_exists; rename_i P_vn
  wp_focus_pure; intro hw1_ne
  wp_focus_pure; intro hP_vn
  wp_steps 15
  refine SepWP.focus_weaken hP_ro_log (by sep_focus) ?_
  refine SepWP.focus_weaken spqrRecvRoPlacedAt_expose_statesIntoPb (by sep_focus) ?_
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
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) initInnerStack (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hinit_ok
    (⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ : InitInnerGhost)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = spqrRecvPlacedEntry + 1300#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => by
      dsimp only [initInnerPlacedSpecX, initInnerOnPanic]
      exact onPanic_of_allocFailed)
    (fun _ _ => rfl)
    (by
      dsimp only [initInnerPlacedSpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]; rfl,
          by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          hw1_ne, hak_len⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, hx20_c, _⟩
  dsimp only [initInnerPlacedSpecX, initInnerResultAt_v0]
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by
    rw [hx20_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) initInnerStack (by decide)).symm)
    (by sep_focus) ?_
  refine SepWPpLS.focus_weaken hP_vn (by sep_focus) ?_
  refine SepWPpLS.focus_weaken hP_ro_into (by sep_focus) ?_
  refine SepWPpLS.focus_weaken (frame4544_join_1320 s0.sp 0#8 0#32) (by sep_focus) ?_
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 323)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
  rw [optChainPBAt_protoRepr_eq_exists A (s0.sp - 4944#64) pre_pb.chain]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i gPb
  have hvn_ref :
      Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (s0.sp - 4992#64) vn ⊢
      ChainFrom.optVersionNegotiationRefAt A ⟨w0, w1⟩ (s0.sp - 4992#64) (some vn) :=
    Entails.pure_right hsp_ne (Entails.refl _)
  refine SepWP.focus_weaken hvn_ref (by sep_focus) ?_
  wp_steps 5
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hcf_ok
    (⟨s0.sp - 2096#64, s0.sp - 4944#64, s0.sp - 4992#64, gPb, ⟨w0, w1⟩, pre_pb.chain, some vn⟩ : ChainFromCall)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hspm']; exact hs0_align)
    (rfl : _ = spqrRecvPlacedEntry + 1320#64)
    (by simp only [arm64_norm, htr_sm']; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed)
    (fun _ _ => rfl)
    (by
      dsimp only [chainFromSpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']; sep_focus))
    ?_
  intro sn hpcn hrunn hspn hcsn
  have hvregs_cn := hcsn.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsn with ⟨hx19_cn, hx20_cn, _⟩
  dsimp only [chainFromSpecX, ChainFrom.optVersionNegotiationRefAt]
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro htr_sn
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro _
  have htr_sn' : TraceVRegs sn s0 := ⟨by rw [htr_sn]; simp only [arm64_norm, *], by rw [hvregs_cn]; simp only [arm64_norm, *]⟩
  have hspn' : sn.sp = s0.sp - 4992#64 := by
    rw [hspn]; simp only [arm64_norm, *]
  have hx19_sn : sn.readReg64 .x19 = ret := by
    rw [hx19_cn]; simp only [arm64_norm, *]
  have hx20_sn : sn.readReg64 .x20 = w0 := by
    rw [hx20_cn]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromStackX (by decide)).symm)
    (by sep_focus) ?_
  cases hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) with
  | error err =>
    obtain ⟨herr, hnp⟩ := spqrV1Recv_lt_one_chainFrom_err F K hpre hdec hvn hinner hmin hver_lt hdir_eq hcf
    exact step_initInner_chainFrom_err_1320_placed A F K ext hC
      st msg ret vn pb err w0 w1 herr hnp s0 sn _ R hs0_align
      hpcn hrunn hspn' htr_sn' hx19_sn hx20_sn (by dsimp only [chainResultAt]; ac_rfl)
  | ok ch =>
    have hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none) :=
      spqrV1Recv_lt_one_chainFrom_ok F K hpre hdec hvn hinner hmin hver_lt hdir_eq hcf
    exact step_initInner_chainFrom_ok_1320_placed hC st msg ret vn pb ch w0 w1 hok
      s0 sn _ R hs0_align
      hpcn hrunn hspn' htr_sn' hx19_sn hx20_sn (by dsimp only [chainResultAt]; ac_rfl)

/-- Combined `Ordering::Less` (`+1076 .. +1420`) tail contract when `s0.sp - 4992#64 ≠ 0#64`. -/
theorem step_ordering_less_placed {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
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
    (hpc : s.pc = spqrRecvPlacedEntry + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
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
      ProtoRepr.optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  by_cases hdir_lt : vn.direction.ult 2#32 = true
  · exact step_ordering_less_dir_some_placed hC st msg ret pre pre_pb vn pb w0 w1
      hst_len hpre hdec hvn hinner hmin hver_lt hdir_lt
      s0 s P R hs0_align hsp_ne hpc hrun hsp htr hx19 hx20 hx25 hx29 hP
  · exact step_ordering_less_dir_none_placed A F K ext hC
      st msg ret pre pre_pb vn pb w0 w1 w26
      hpre hdec hvn hinner hw26 hmin hver_lt hdir_lt
      s0 s P R hs0_align hpc hrun hsp htr hx19 hx20 hx25 hx26 hx29 hP

end CryptoVerification.SpqrV1.Top.Recv
