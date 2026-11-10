/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSent
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudgetAux
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Outer Step Helpers for `Chunked.HeaderSent::merge` (Block `302`)

Proves the budget-threaded outer `ek_init`, `ct1_init`, `uc_init`, `loop_le_exit`, and
`decode_key_step` lemmas for `Chunked.HeaderSent::merge` on Block `302` with
`withLsCodeRoLoaded lsmpl` callees.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.RustHeap (RustAlloc vecBuf vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix
   key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false w1_tag_eq)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Poly (protoPolynomialDecoderAt protoPolynomialEncoderAt)
open CryptoVerification.SpqrV1.ProtoRepr
  (boolByte optPolynomialDecoderPBAt optPolynomialEncoderPBAt polynomialDecoderPBAt
   polynomialEncoderPBAt vecVecU8At vecVecU8At_eq_exists_pin vecVecU8Buf
   vecVecU8PinnedAt_eq_header_buf)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (cap_add_one_beq_zero_false cap_add_one_bne_zero_true
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedHeaderSentMergeGhost ChunkedInl10CalleeSaved SepWPpLscro
   blkPC_302 blkPl_302 bv64_add_zero bv64_sub_zero
   cells2_memRegion32_entails_40_160
   chunkedHeaderSentMerge_fnOff chunkedHeaderSentPBCapAt
   chunkedHeaderSentPBCapAt_entails_pb chunkedHeaderSentPBCapAt_mono
   chunkedInlBelowStack chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails
   chunkedInlSavedRegs10 chunkedInlStack
   cmp_len_limit_of_eq cmp_len_limit_of_gt cmp_len_limit_of_lt
   codecWireTypeToProto
   default_polyDecoder_entails_pb_inl default_polyEncoder_entails_pb_inl
   default_unchunked3_entails_cap
   memRegion_48_cells1_160 memRegion_48_cells2_160
   memRegion_polyDecoder_none_split_inl memRegion_polyEncoder_none_split_inl
   memRegion_unchunked3_none_split
   mergeLoopBin mergeLoopBin_eq_limit mergeLoopBin_lt_limit
   mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge
   mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none
   optEkSentPBCapAt optPolynomialDecoderPBAt_some_eq optPolynomialEncoderPBAt_some_eq
   polyDecoderToProto polyEncoderToProto
   protoPrefixStep_chunked_headerSent_mergeField
   stackAt_chunkedInl10_epilogue unchunked3CapAt vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget (SpqrMergeLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedHeaderSentMergeEnv ChunkedHeaderSentMergePostEnv
   chunkedHeaderSentMergeSpec chunkedHeaderSentMergeSpecOfEnv
   headerSentPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   decodeVarint2Env_to_spqr fitsEnv_decodeVarint2_of_spqr
   pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc pool_spqr_mono
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm spqrPoolAt spqrPoolAt_of_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudgetAux
  (chunkedHeaderSentErrFrame chunkedHeaderSentLoopPre
   chunkedHeaderSentUcLoopPre chunkedHeaderSent_from_err_exit_placed
   chunkedHeaderSent_ret_err_exit_placed)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedHeaderSentMerge_fnOff

@[local simp, local arm64_norm]
private theorem bv64_add80_add8 (a : BitVec 64) : a + 80#64 + 8#64 = a + 88#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add80_add16 (a : BitVec 64) : a + 80#64 + 16#64 = a + 96#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add80_add24 (a : BitVec 64) : a + 80#64 + 24#64 = a + 104#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add80_add32 (a : BitVec 64) : a + 80#64 + 32#64 = a + 112#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add80_add40 (a : BitVec 64) : a + 80#64 + 40#64 = a + 120#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add80_add48 (a : BitVec 64) : a + 80#64 + 48#64 = a + 128#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add136_add8 (a : BitVec 64) : a + 136#64 + 8#64 = a + 144#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add136_add16 (a : BitVec 64) : a + 136#64 + 16#64 = a + 152#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add136_add24 (a : BitVec 64) : a + 136#64 + 24#64 = a + 160#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add136_add32 (a : BitVec 64) : a + 136#64 + 32#64 = a + 168#64 := by bv_omega

private theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

private theorem vecU8Buf_entails_cap_lt_hs (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

private def polyEncoderRestAt (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (d : PolynomialEncoder) : SepProp :=
  ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
    vecVecU8Buf A pin.cap pin.ptr d.pts ∗ vecVecU8At A (a + 24#64) d.polys ∗ ((a + 48#64) ↦₃₂ d.idx) ∗ memRegion (a + 52#64) 4

private theorem vecVecU8Buf_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (pts : List (List (BitVec 8))) :
    vecVecU8Buf A cap ptr pts ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecVecU8Buf A cap ptr pts := by
  unfold vecVecU8Buf vecBuf
  refine Entails.pure_left fun h => ?_
  exact Entails.pure_right (by omega : cap.toNat < 2 ^ 63) (Entails.pure_right h (Entails.refl _))

private theorem protoPolynomialEncoderAt_entails_cmn_hs (A : RustAlloc) (a : BitVec 64) (d : PolynomialEncoder) :
    protoPolynomialEncoderAt A a (polyEncoderToProto d) ⊢ ∃∗ pin : VecPin, ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ (a ↦₆₄ pin.cap) ∗ polyEncoderRestAt A a pin d := by
  rw [← optPolynomialEncoderPBAt_some_eq]; dsimp only [optPolynomialEncoderPBAt, polynomialEncoderPBAt, polyEncoderRestAt]
  rw [vecVecU8At_eq_exists_pin, sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun pin => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro pin)
  rw [vecVecU8PinnedAt_eq_header_buf]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (vecVecU8Buf_cap_lt A pin.cap pin.ptr d.pts))))) ?_
  sep_entail

private theorem cmn_entails_protoPolynomialEncoderAt_hs (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (d : PolynomialEncoder) :
    (a ↦₆₄ pin.cap) ∗ polyEncoderRestAt A a pin d ⊢ protoPolynomialEncoderAt A a (polyEncoderToProto d) := by
  rw [← optPolynomialEncoderPBAt_some_eq]; dsimp only [optPolynomialEncoderPBAt, polynomialEncoderPBAt, polyEncoderRestAt]; rw [vecVecU8At_eq_exists_pin A a d.pts]
  refine Entails.trans (Entails.of_eq (show _ = (((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.pts.length)) ∗ vecVecU8Buf A pin.cap pin.ptr d.pts) ∗ vecVecU8At A (a + 24#64) d.polys ∗ ((a + 48#64) ↦₃₂ d.idx) ∗ memRegion (a + 52#64) 4 by sep_ac_rfl)) ?_
  refine sepConj_mono_left ?_
  refine Entails.trans ?_ (Entails.sepExists_intro pin)
  rw [vecVecU8PinnedAt_eq_header_buf]; simp only [sepConj_assoc]; exact Entails.refl _

private def polyDecoderRestAt (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (d : PolynomialDecoder) : SepProp :=
  ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
    vecVecU8Buf A pin.cap pin.ptr d.pts ∗ ((a + 24#64) ↦₃₂ d.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ d.polys) ∗
    ((a + 32#64) ↦₈ boolByte d.isComplete) ∗ memRegion (a + 33#64) 7

private theorem protoPolynomialDecoderAt_entails_cmn_hs (A : RustAlloc) (a : BitVec 64) (d : PolynomialDecoder) :
    protoPolynomialDecoderAt A a (polyDecoderToProto d) ⊢
      ∃∗ pin : VecPin, ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ (a ↦₆₄ pin.cap) ∗ polyDecoderRestAt A a pin d := by
  rw [← optPolynomialDecoderPBAt_some_eq]; dsimp only [optPolynomialDecoderPBAt, polynomialDecoderPBAt, polyDecoderRestAt]
  rw [vecVecU8At_eq_exists_pin, sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun pin => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro pin)
  rw [vecVecU8PinnedAt_eq_header_buf]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (vecVecU8Buf_cap_lt A pin.cap pin.ptr d.pts))))) ?_
  sep_entail

private theorem cmn_entails_protoPolynomialDecoderAt_hs (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (d : PolynomialDecoder) :
    (a ↦₆₄ pin.cap) ∗ polyDecoderRestAt A a pin d ⊢
      protoPolynomialDecoderAt A a (polyDecoderToProto d) := by
  rw [← optPolynomialDecoderPBAt_some_eq]; dsimp only [optPolynomialDecoderPBAt, polynomialDecoderPBAt, polyDecoderRestAt]
  rw [vecVecU8At_eq_exists_pin]
  refine Entails.trans (Entails.of_eq (show _ = (((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.pts.length)) ∗ vecVecU8Buf A pin.cap pin.ptr d.pts) ∗ ((a + 24#64) ↦₃₂ d.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ d.polys) ∗ ((a + 32#64) ↦₈ boolByte d.isComplete) ∗ memRegion (a + 33#64) 7 by sep_ac_rfl)) ?_
  refine sepConj_mono_left ?_
  refine Entails.trans ?_ (Entails.sepExists_intro pin)
  rw [vecVecU8PinnedAt_eq_header_buf]; simp only [sepConj_assoc]; exact Entails.refl _

private theorem hs_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : ChunkedHeaderSentMergeGhost)
    (s0 s sf : State) (m : V1State.Chunked.HeaderSent) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hsome : (mergeMessage V1State.Chunked.HeaderSent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrMergeLoopEnv (6 * (x.bs.length - cur.length)) x.bs.length
      (headerSentPolyCapBound x) evs) :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedHeaderSentPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (chunkedHeaderSentMergeSpec A lim).post (x, st) s0 sf := by
  dsimp only [chunkedHeaderSentMergeSpec, chunkedHeaderSentMergeSpecOfEnv,
    ChunkedHeaderSentMergePostEnv]
  rw [hsome, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedHeaderSentPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedInlStack ∗
          (chunkedHeaderSentPBCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  exact sepConj_mono_right (sepConj_mono
    (pool_spqr_mono A lim st hvm (Nat.le_refl _) hevs)
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_302).base

theorem chunkedHeaderSent_ek_init_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_302).base + 320#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) →
      s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) →
      s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (optEkSentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          protoPolynomialEncoderAt A.repAlloc (x.msgPtr + 80#64) (polyEncoderToProto (m.sendingEk.getD default)) ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 136#64) m.receivingCt1 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (headerSentPolyCapBound x) s')
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 292#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  rcases hek : m.sendingEk with _ | d
  · rw [hek] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 320#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedHeaderSentLoopPre, chunkedHeaderSentPBCapAt, hek,
        optPolynomialEncoderPBAt, memRegion_polyEncoder_none_split_inl (x.msgPtr + 80#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro v48; apply SepWP.exists_elim; intro v40
      apply SepWP.exists_elim; intro v32; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
      wp_steps
      have hdef := default_polyEncoder_entails_pb_inl A.repAlloc (x.msgPtr + 80#64)
      simp only [arm64_norm] at hdef
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := optEkSentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          protoPolynomialEncoderAt A.repAlloc (x.msgPtr + 80#64) (polyEncoderToProto (Option.getD none default)) ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 136#64) m.receivingCt1 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (headerSentPolyCapBound x) _)
        (by dsimp only [Option.getD]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩
  · rw [hek] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 320#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedHeaderSentLoopPre, chunkedHeaderSentPBCapAt, hek,
        optPolynomialEncoderPBAt_some_eq])
      (conv => arg 4; simp only [sepConj_assoc, arm64_norm])
      have hcmn_in := protoPolynomialEncoderAt_entails_cmn_hs A.repAlloc (x.msgPtr + 80#64) d
      simp only [arm64_norm] at hcmn_in
      apply SepWP.fold hcmn_in (by sep_focus)
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro pin
      apply SepWP.pure_elim; intro hcap_lt
      have hcmn1 := cap_add_one_beq_zero_false hcap_lt
      have hcmn2 := cap_add_one_bne_zero_true hcap_lt
      wp_steps
      have hcmn_out := cmn_entails_protoPolynomialEncoderAt_hs A.repAlloc (x.msgPtr + 80#64) pin d
      apply SepWP.fold hcmn_out (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := optEkSentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          protoPolynomialEncoderAt A.repAlloc (x.msgPtr + 80#64) (polyEncoderToProto (Option.getD (some d) default)) ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 136#64) m.receivingCt1 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (headerSentPolyCapBound x) _)
        (by dsimp only [Option.getD]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩

theorem chunkedHeaderSent_ct1_init_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_302).base + 268#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) →
      s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) →
      s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (optEkSentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 80#64) m.sendingEk ∗
          protoPolynomialDecoderAt A.repAlloc (x.msgPtr + 136#64) (polyDecoderToProto (m.receivingCt1.getD default)) ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (headerSentPolyCapBound x) s')
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  rcases hct1 : m.receivingCt1 with _ | d
  · rw [hct1] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 268#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedHeaderSentLoopPre, chunkedHeaderSentPBCapAt, hct1,
        optPolynomialDecoderPBAt, memRegion_polyDecoder_none_split_inl (x.msgPtr + 136#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro b32; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
      wp_steps
      have hdef := default_polyDecoder_entails_pb_inl A.repAlloc (x.msgPtr + 136#64)
      simp only [arm64_norm] at hdef
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := optEkSentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 80#64) m.sendingEk ∗
          protoPolynomialDecoderAt A.repAlloc (x.msgPtr + 136#64) (polyDecoderToProto (Option.getD none default)) ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (headerSentPolyCapBound x) _)
        (by dsimp only [Option.getD]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩
  · rw [hct1] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 268#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedHeaderSentLoopPre, chunkedHeaderSentPBCapAt, hct1,
        optPolynomialDecoderPBAt_some_eq])
      (conv => arg 4; simp only [sepConj_assoc, arm64_norm])
      have hcmn_in := protoPolynomialDecoderAt_entails_cmn_hs A.repAlloc (x.msgPtr + 136#64) d
      simp only [arm64_norm] at hcmn_in
      apply SepWP.fold hcmn_in (by sep_focus)
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro pin
      apply SepWP.pure_elim; intro hcap_lt
      have hcmn1 := cap_add_one_beq_zero_false hcap_lt
      have hcmn2 := cap_add_one_bne_zero_true hcap_lt
      wp_steps
      have hcmn_out := cmn_entails_protoPolynomialDecoderAt_hs A.repAlloc (x.msgPtr + 136#64) pin d
      apply SepWP.fold hcmn_out (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := optEkSentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 80#64) m.sendingEk ∗
          protoPolynomialDecoderAt A.repAlloc (x.msgPtr + 136#64) (polyDecoderToProto (Option.getD (some d) default)) ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (headerSentPolyCapBound x) _)
        (by dsimp only [Option.getD]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩

theorem chunkedHeaderSent_uc_init_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_302).base + 368#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) →
      s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          (m.uc.getD default) m.sendingEk m.receivingCt1 x.bs rest (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 344#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  rcases huc : m.uc with _ | uc
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 368#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedHeaderSentLoopPre, chunkedHeaderSentPBCapAt, huc,
        optEkSentPBCapAt, memRegion_unchunked3_none_split x.msgPtr])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro v72; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
      wp_steps
      have hdef :
          (x.msgPtr ↦₆₄ 0#64) ∗ ((x.msgPtr + 8#64) ↦₆₄ 1#64) ∗ ((x.msgPtr + 16#64) ↦₆₄ 0#64) ∗
            ((x.msgPtr + 24#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.msgPtr + 32#64) 40 ∗
            ((x.msgPtr + 72#64) ↦₆₄ 0#64) ⊢
          unchunked3CapAt A.repAlloc x.msgPtr rest.length
            (default : V1State.Unchunked.EkSent).epoch
            (default : V1State.Unchunked.EkSent).auth
            (default : V1State.Unchunked.EkSent).dk := by
        change _ ⊢ unchunked3CapAt A.repAlloc x.msgPtr rest.length 0#64 none []
        simpa only [noneCap, arm64_norm] using
          default_unchunked3_entails_cap A.repAlloc x.msgPtr rest.length
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := chunkedHeaderSentUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
          default m.sendingEk m.receivingCt1 x.bs rest (headerSentPolyCapBound x))
        (by dsimp only [chunkedHeaderSentUcLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 368#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedHeaderSentLoopPre, chunkedHeaderSentPBCapAt, huc,
        optEkSentPBCapAt, unchunked3CapAt])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm, arm64_norm])
      apply SepWP.exists_elim; intro cap_dk
      apply SepWP.exists_elim; intro ptr_dk
      apply SepWP.pure_elim; intro hcap_dk
      (conv => arg 4; rw [vecU8At_eq_header_sep_buf A.repAlloc x.msgPtr cap_dk ptr_dk uc.dk, vecHeader]; simp only [sepConj_assoc])
      apply SepWP.fold (vecU8Buf_entails_cap_lt_hs A.repAlloc cap_dk ptr_dk uc.dk) (by sep_focus)
      (conv => arg 4; simp only [sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.pure_elim; intro hcap_lt
      have hcmn1 := cap_add_one_beq_zero_false hcap_lt
      have hcmn2 := cap_add_one_bne_zero_true hcap_lt
      wp_steps
      have hfold_dk :
          (x.msgPtr ↦₆₄ cap_dk) ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr_dk) ∗
            ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 uc.dk.length) ∗
            vecU8Buf A.repAlloc cap_dk ptr_dk uc.dk ⊢
          (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
            ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A.repAlloc x.msgPtr cap ptr uc.dk) := by
        refine Entails.trans ?_
          (Entails.sepExists_right cap_dk (Entails.sepExists_right ptr_dk (Entails.refl _)))
        refine Entails.pure_right hcap_dk ?_
        rw [vecU8At_eq_header_sep_buf, vecHeader]
        exact Entails.of_eq (by sep_ac_rfl)
      apply SepWP.fold hfold_dk (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := chunkedHeaderSentUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
          uc m.sendingEk m.receivingCt1 x.bs rest (headerSentPolyCapBound x))
        (by dsimp only [chunkedHeaderSentUcLoopPre];
            rw [unchunked3CapAt, spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩

theorem chunkedHeaderSent_loop_le_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hle_lim : cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : outerLimit < 2 ^ 63)
    (hres : (mergeMessage V1State.Chunked.HeaderSent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
      (mergeLoopBin V1State.Chunked.HeaderSent.mergeField (cur.length - outerLimit) m cur outerLimit 98).map
        (fun m' => (m', x.bs.drop (x.bs.length - outerLimit))))
    (hpc : s.pc = (blkPl_302).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (_hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (_hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur
        (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = outerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hml : mergeLoopBin V1State.Chunked.HeaderSent.mergeField (cur.length - outerLimit) m cur outerLimit 98 = some m :=
      mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim
    have hsome : (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur) := by
      rw [hres, hml, ← heq_lim, ← hcur_suf]; rfl
    apply sepWPpLscro_of_ret_vm
    by_vm_steps
      (conv => arg 4; simp only [chunkedHeaderSentLoopPre, spqrPoolAt,
        sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlSavedRegs10,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        sepConj_pure_left_comm, arm64_norm, hsp])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus)
      have hcur_fold :
          (x.slot ↦₆₄ curPtr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 cur.length) ∗
            (x.ptr ↦ₛ x.bs.take (x.bs.length - cur.length)) ∗ (curPtr ↦ₛ cur) ⊢
          sliceCursorAfter x.slot x.ptr x.bs cur := by
        rw [sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
        exact Entails.of_eq (by sep_ac_rfl)
      apply SepWP.fold hcur_fold (by dsimp only [curPtr]; sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
      refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
        by simp only [arm64_norm, wp_norm, hsp],
        by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx27, hx28, hvregs]⟩
      refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (hs_ok_exit_entails A lim st x s0 s _ m cur evs hsome hvm
          (by simp only [arm64_norm, wp_norm, htr])
          (by simp only [arm64_norm, wp_norm]) hevs)
  · have hlt_lim : cur.length < outerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim]; rfl
    have hfrom_err := @chunkedHeaderSent_from_err_exit_placed _ M A lim H hFromCall x st R s0 m
    apply sepWPpLscro_of_vm (mid := entry + 112#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedHeaderSentLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
        sliceCursorAt, memRegion_48_cells1_160 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_stk0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
      apply SepWP.fold (chunkedHeaderSentPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗
          memRegion (s0.sp - 120#64) 40 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - cur.length))
            (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [chunkedHeaderSentErrFrame]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hfrom_err hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm, hsp]) (by simp only [arm64_norm, wp_norm, htr])
        ⟨by simp only [arm64_norm, wp_norm, hx27],
         by simp only [arm64_norm, wp_norm, hx28],
         by simp only [arm64_norm, wp_norm, hvregs]⟩

theorem chunkedHeaderSent_decode_key_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hgt_lim : ¬ cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_loop_none :
      mergeLoopBin V1State.Chunked.HeaderSent.mergeField (cur.length - outerLimit) m cur outerLimit 98 = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_302).base + 220#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
          (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur
        (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hret_err := @chunkedHeaderSent_ret_err_exit_placed _ M A lim H x st R s0 m
  have hfrom_err := @chunkedHeaderSent_from_err_exit_placed _ M A lim H hFromCall x st R s0 m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [chunkedHeaderSentLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 188#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp, hx19]; try rfl)
      (And.intro hcur_lt (fitsEnv_decodeVarint2_of_spqr (by omega) hevs hFit))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    cases hd : decodeVarint cur with
    | none =>
      have hnone := hnone_of_loop_none
        (mergeLoopBin_of_decodeVarint_none protoPrefixStep_chunked_headerSent_mergeField hgt_lim hd)
      apply sepWPpLscro_of_vm (mid := entry + 124#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
          stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
        apply SepWP.exists_elim; intro evs_dv
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
        apply SepWP.fold (chunkedHeaderSentPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - cur.length) + 1))
            hevs (decodeVarint2Env_to_spqr hevs_dv))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            memRegion (s0.sp - 128#64) 48 ∗
            chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - cur.length) + 1)
              (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
        exact hret_err hnone (by omega) (by decide : 0 ≤ 3) hsm1 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨key, rest⟩
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      by_cases hk_ge : 2 ^ 32 ≤ key.toNat
      · have hnone := hnone_of_loop_none
          (mergeLoopBin_of_key_ge protoPrefixStep_chunked_headerSent_mergeField hgt_lim hd hk_ge)
        have hshr := key_shr32_of_ge hk_ge
        apply sepWPpLscro_of_vm (mid := entry + 112#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
            stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
            sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
          apply SepWP.exists_elim; intro evs_dv
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedHeaderSentPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m) (by sep_focus)
          apply SepWP.fold
            (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
              (Nat.le_refl (6 * (x.bs.length - cur.length)))
              hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
            (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp])
          (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro v_err0
          apply SepWP.exists_elim; intro v_err1
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
            rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
          apply SepWP.fold h40 (by sep_focus)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          apply SepWPpLscro.weaken_pre
            (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗
              memRegion (s0.sp - 120#64) 40 ∗
              stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
              chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - cur.length))
                (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
          exact hfrom_err hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr])
            ⟨by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      · have hshr := key_shr32_of_lt hk_ge
        cases hwt : WireType.ofNat? (key.toNat % 8) with
        | none =>
          have hnone := hnone_of_loop_none
            (mergeLoopBin_of_wt_none protoPrefixStep_chunked_headerSent_mergeField hgt_lim hd hk_ge hwt)
          obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
          apply sepWPpLscro_of_vm (mid := entry + 112#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
              stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
              sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
            apply SepWP.exists_elim; intro evs_dv
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
            apply SepWP.fold (chunkedHeaderSentPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (Nat.le_refl (6 * (x.bs.length - cur.length)))
                hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
              (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp])
            (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro v_err0
            apply SepWP.exists_elim; intro v_err1
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
            have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
              rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
            apply SepWP.fold h40 (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗
                memRegion (s0.sp - 120#64) 40 ∗
                stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
                chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - cur.length))
                  (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
              (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
            exact hfrom_err hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr])
              ⟨by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        | some iwt =>
          obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
          obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
          obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
          by_cases hitag0 : key.toNat / 8 < 1
          · have hnone := hnone_of_loop_none
              (mergeLoopBin_of_tag_zero protoPrefixStep_chunked_headerSent_mergeField hgt_lim hd hk_ge hwt hitag0)
            have htag_zero : key.toNat / 8 = 0 := by omega
            apply sepWPpLscro_of_vm (mid := entry + 112#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
                stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
                sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
              apply SepWP.exists_elim; intro evs_dv
              apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
              apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold (chunkedHeaderSentPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m) (by sep_focus)
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (Nat.le_refl (6 * (x.bs.length - cur.length)))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
                (by sep_focus)
              (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp])
              (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
              apply SepWP.exists_elim; intro v_err0
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              apply SepWPpLscro.weaken_pre
                (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗
                  memRegion (s0.sp - 120#64) 40 ∗
                  stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
                  chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - cur.length))
                    (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
                (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
              exact hfrom_err hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
                (by simp only [arm64_norm, wp_norm])
                (by simp only [arm64_norm, wp_norm, hrunm])
                (by simp only [arm64_norm, wp_norm, hspm])
                (by simp only [arm64_norm, wp_norm, htrm, htr])
                ⟨by simp only [arm64_norm, wp_norm, hx27_m],
                 by simp only [arm64_norm, wp_norm, hx28_m],
                 by simp only [arm64_norm, wp_norm, hvregs_m]⟩
          · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
            have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
              rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
              simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
            apply sepWPpLscro_of_vm (mid := entry + 220#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
                stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
                sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
              apply SepWP.exists_elim; intro evs_dv
              apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
              apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold (chunkedHeaderSentPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (by omega : 6 * (x.bs.length - cur.length) ≤ 6 * (x.bs.length - rest.length))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
                (by sep_focus)
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              apply SepWPpLscro.weaken_pre
                (P' := chunkedHeaderSentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
                  (headerSentPolyCapBound x))
                (by dsimp only [chunkedHeaderSentLoopPre]; sep_entail)
              exact hcont key iwt rest _ hd hk_ge hwt hitag0
                (by simp only [arm64_norm, wp_norm])
                (by simp only [arm64_norm, wp_norm, hrunm])
                (by simp only [arm64_norm, wp_norm, hspm])
                (by simp only [arm64_norm, wp_norm, htrm, htr])
                (by simp only [arm64_norm, wp_norm, hsm1, hand_wt])
                (by simp only [arm64_norm, wp_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
                (by simp only [arm64_norm, wp_norm, hx19_m])
                (by simp only [arm64_norm, wp_norm, hx20_m])
                (by simp only [arm64_norm, wp_norm, hx21_m])
                (by simp only [arm64_norm, wp_norm, hx22_m])
                (by simp only [arm64_norm, wp_norm, hx23_m])
                (by simp only [arm64_norm, wp_norm, hx24_m])
                (by simp only [arm64_norm, wp_norm, hx25_m])
                ⟨by simp only [arm64_norm, wp_norm, hx27_m],
                 by simp only [arm64_norm, wp_norm, hx28_m],
                 by simp only [arm64_norm, wp_norm, hvregs_m]⟩

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudgetAux
