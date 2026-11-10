/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1Placed
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import ProofLib.SepLogic.WPp

/-!
# Relocatable `Ordering::Greater` Continuations for `spqr::recv`

Relocatable shared error exit (`+2388..+2420 -> +2540`) and `<Chain>::recv_key` success
continuation (`+2184..+2380 -> +1040`) for `Ordering::Greater` in `spqr::recv` (Block `329`).
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
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  Prost.EncodeToVec.extractLsb_lo_append64 Prost.EncodeToVec.extractLsb_hi_append64
attribute [local simp, local arm64_norm, local wp_norm]
  fp_sub_32_eq hsp_add_560_eq_v0 fp_sub_48_eq hsp_add_544_eq_v0

/-! ## 1. `step_v0_err_2388_placed` (`+2388 .. +2420 -> +2540`) -/

/-- Shared error exit at `+2388 .. +2420 -> +2540` for `Ordering::Greater`: reads the 24-byte
    error payload from `s0.sp - 2088#64 .. s0.sp - 2064#64` (with `x22 = s0.sp - 2096#64`),
    writes `Err(e == .stateDecode)` to `ret` (`x19`), and jumps to `+2540`
    (`step_drop_pre_2540_placed`) to drop `vn` and `pb` at `s0.sp - 4992#64`. -/
theorem step_v0_err_2388_placed {H_inner : V1InnerHeapPred} (A : RustAlloc)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State) (e : Error)
    (w0 w1 w0_err : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2388#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx22 : s.readReg64 .x22 = s0.sp - 2096#64)
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
      memRegion (s0.sp - 4640#64) 2544 ∗
      ((s0.sp - 2096#64) ↦₆₄ w0_err) ∗
      (∃∗ q0 : BitVec 128, ∃∗ w3 : BitVec 64,
        ⌜BitVec.truncate 8 q0 = Top.ChainFromVersionNegotiation.spqrErrorTag e⌝ ∗
        ((s0.sp - 2088#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((s0.sp - 2080#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((s0.sp - 2072#64) ↦₆₄ w3)) ∗
      memRegion (s0.sp - 2064#64) 56 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [frame1912_split_err_2388 s0.sp, ret_48_split ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i d0 d1 d2 q0_err w3_err r0 r1 r2 r3
  wp_focus_pure; intro htag_q0
  have hret_fold :
      ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 8#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((ret + 16#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((ret + 24#64) ↦₆₄ w3_err) ∗
        memRegion (ret + 32#64) 16) ⊢
      recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [herr]
    exact recv_err_q0_foldX A ret (q0_err.extractLsb' 64 64) w3_err q0_err e htag_q0
  apply sepWP_seq_lscl hcl
  wp_steps 9
  refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
  refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
  refine SepWP.focus_weaken
    (frame4544_join_err_2388 s0.sp w0_err
      (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err
      (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err)
    (by sep_focus) ?_
  refine sepWP_spqrRecvPlacedPost_of_post0 hnp ?_
  exact step_drop_pre_2540_placed A (spqrV1Recv F K) ext hC st msg ret vn pb w0 w1
    s0 _ _ R _ rfl hs0_align
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl) hcl1

/-! ## 2. `step_v0_recvKey_ok_2184_placed` (`+2184 .. +2380 -> +1040`) -/

theorem spqrRecvRoPlacedAt_expose_dropJumpTable :
    spqrRecvRoPlacedAt ⊢
      Drop.optProtoInnerStateJumpTablePlacedAt ∗
      (∃∗ P_ro : SepProp, ⌜Drop.optProtoInnerStateJumpTablePlacedAt ∗ P_ro ⊢ spqrRecvRoPlacedAt⌝ ∗ P_ro) := by
  unfold spqrRecvRoPlacedAt Prost.MessageMerge.v1StateJumpTablesPlacedAt
  have h1 : ∀ P Q R S T : SepProp,
      (P ∗ Q) ∗ R ∗ S ∗ T = Q ∗ (P ∗ R ∗ S ∗ T) := by
    intro P Q R S T; ac_rfl
  refine Entails.trans (Entails.of_eq (h1 _ _ _ _ _)) ?_
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right _ (Entails.pure_right ?_ (Entails.refl _))
  exact Entails.of_eq (h1 _ _ _ _ _).symm

/-- Success continuation of `Chain::recv_key` in `Ordering::Greater` (`+2184 .. +2380 ->
    +1040`): calls `Chain::into_pb` (Block `365`), moves `vn` (`48`B) and `inner` (`224`B) into
    `s0.sp - 3056#64`, calls `PqRatchetState::encode_to_vec` (Block `426`), writes
    `Ok((newStateBytes, Some(rawKey)))` to `ret` (`x19`), calls `drop_glue::<PqRatchetState>`
    (Block `270`), and jumps to `step_epilogue_placed` (`+1040`). -/
theorem step_v0_recvKey_ok_2184_placed {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
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
    (hpc : s.pc = spqrRecvPlacedEntry + 2184#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = s0.sp - 3056#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 2096#64)
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
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hinto_pb := hC.chainIntoPb_ok
  have henc_ok := hC.encodeToVec_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 365)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  unfold chainRepr
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i G_c1
  wp_steps 7
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hinto_pb ⟨s0.sp - 3008#64, s0.sp - 4288#64, G_c1, chain1⟩
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = spqrRecvPlacedEntry + 2212#64)
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
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_cm]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = s0.sp - 2096#64 := by
    rw [hx22_cm]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)).symm)
    (by sep_focus) ?_
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 426)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
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
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) (encodeToVecStackOf doReserveStackX) (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro henc_ok
    (⟨s0.sp - 2096#64, s0.sp - 3056#64,
      { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }⟩ :
      PqRatchetStateEncodeToVecGhost)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hspm']; exact hs0_align)
    (rfl : _ = spqrRecvPlacedEntry + 2336#64)
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
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro htr_sn
  have htr_sn' : TraceVRegs sn s0 := ⟨by rw [htr_sn]; simp only [arm64_norm, *], by rw [hvregs_cn]; simp only [arm64_norm, *]⟩
  have hspn' : sn.sp = s0.sp - 4992#64 := by
    rw [hspn]; simp only [arm64_norm, *]
  have hx19_sn : sn.readReg64 .x19 = ret := by
    rw [hx19_cn]; simp only [arm64_norm, *]
  have hx22_sn : sn.readReg64 .x22 = s0.sp - 2096#64 := by
    rw [hx22_cn]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) (encodeToVecStackOf doReserveStackX) (by decide)).symm)
    (by sep_focus) ?_
  apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcn ⊢
  refine SepWP.focus_weaken
    (vecU8_sub_entails_header_buf A s0.sp 2096
      (PqRatchetState.encodeRaw
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
    (by sep_focus) ?_
  wp_pull_exists; rename_i cap_st ptr_st
  rw [← protoPqRatchetStateAt_eq_pqRatchetStatePBAt]
  refine SepWP.focus_weaken spqrRecvRoPlacedAt_expose_dropJumpTable (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro
  wp_focus_pure; intro hP_ro
  rw [ret_48_split_6 ret]
  wp_pull_exists; rename_i r5 r4 r3 r2 r1 r0
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  apply sepWP_seq_lscl hcl
  wp_steps 11
  refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)))
    (by sep_focus) ?_
  have hdrop_st := subroutine_ok_withMemEq_of_lscl hC.dropPqRatchetState_ok hcl1
  dsimp only [spqrRecvPlacedProg, Drop.dropProtoPqRatchetStatePlacedSpec] at hdrop_st
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
  refine sepWP_spqrRecvPlacedPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
  exact step_epilogue_placed A (spqrV1Recv F K) ext st msg ret s0 _ _ R _ rfl
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hs0_align (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv
