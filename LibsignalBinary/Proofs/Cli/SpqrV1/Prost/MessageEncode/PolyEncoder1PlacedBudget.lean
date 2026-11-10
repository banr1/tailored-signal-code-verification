/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoder1PlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `encode<PolynomialEncoder> [local#3]` Verification (Block `456`)

Proves budget-threaded `2^60`-cap and exact `2^59`-cap `subroutine_ok` and `EncodeToVec` contracts
for `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>> [local#3]` on CLI Block `456`
under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoder1PlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget VmPreserved
   allocMemcpyVmSpec fitsEvents_append rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsMemcpySym lsρ ls_subroutine_ok_of_block lsmpl
   withLsCodeLoaded)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeUint32Field)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Poly (protoPolynomialEncoderPinnedAt)
open CryptoVerification.SpqrV1.Varint (encodeRepeatedBytes)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodePolyEncoderPinnedGhost MsgEnc48CalleeSavedPlaced bs0_append_encodePolyEncoderMsg
   encodePolyEncoderMsg encodePolyEncoderMsg_len_split msgEnc48RepeatedStackOf msgEnc48SavedFrame
   polyEncoderElemsAt polyEncoderHeaderBytes polyEncoderRestAt polynomialEncoderPBEncodedLen
   polynomialEncoderPBEncodedLen_le_msg_len satisfies_protoPolynomialEncoderPinnedAt_iff
   subroutine_ok_withMsgEnc48CSPlaced_placed withMsgEnc48CSPlaced)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed (blkPl_460)
open CryptoVerification.Cli.SpqrV1.Varint.Placed (blkPl_448 lsProg_448 blkPl_451)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced (blkPl_480)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed (blkPl_456 lsProg_456)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserve2SpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeRepeatedSpecOf encodeVarintDetSpecOf)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlacedBudget
  (do_reserve2_placed_ok do_reserve2_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeated1PlacedBudget
  (encodeVarint2_det_placed_ok_of_doReserve encode_repeated_1_59_placed_ok_of_callees
   encode_repeated_1_placed_ok_of_callees encode_varint2_det_placed_ok
   encode_varint2_det_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (encodeRepeatedStep pushBytesStep)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncodedLenPlacedBudget
  (polynomialEncoderEncodedLen_local1_pinned_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBaseBudget
  (EncodePolyEncoderEnv encodePolyEncoderEvents encodePolyEncoderPinnedSpec
   encodePolyEncoderPinnedSpecOf encodePolyEncoderPinnedSpecOfEnv encodePolyEncoderPinnedSpecX
   encodePolyEncoderPinnedToUnpinned encodePolyEncoderSpec encodePolyEncoderSpecX
   polynomialEncoderEncodedLenElemsOutSpec subroutine_ok_polyEncLenElemsOut_of_pinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
  (polyEncoder_unpinned_of_pinned_placed_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
  (EncodePolyEncoder1PinnedPlacedOk EncodePolyEncoder1PinnedPlacedOkExt
   EncodePolyEncoder1PinnedPlacedOkExtX EncodePolyEncoder1PinnedPlacedOkX
   EncodePolyEncoder1PlacedOk EncodePolyEncoder1PlacedOkExt
   EncodePolyEncoder1PlacedOkExtX EncodePolyEncoder1PlacedOkX)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1PlacedBudgetAux
  (doReserve2_impossible_ok encodeVarint2_fit_impossible_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
  (encodePolyEncoderExactSpecOf encodeRepeated59ExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedABudget
  (encodeRepeated59SpecOf_of_det_placed subroutine_ok_encodeRepeated59Exact_of_59_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedBudget
  (etv_polyEncoderEncode_exact_of_lscl impossibleEnforcedLimits sepWPp_mono vmTrackBudget)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget
  (encodePolyEncoderExactVmSpecOf subroutine_ok_withLsCodeLoaded_encodePolyEncoderExact_of_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (etvPolyEncoderExactSpecOf)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoder1PlacedBudgetAux
  (step_hdr_1_placed step_idx_1_placed step_pe1_hdr_exact_placed step_pe1_idx_exact_placed
   step_pe1_pts_polys_exact_placed step_polys_1_placed step_pts_1_placed)

/-! ## 1. Subroutine Lifting Helpers -/

private theorem subroutine_ok_withLsCodeLoaded_of_plain [LibsignalPlacement]
    {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (hok : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hok.mono_outcome x R s hpc hrun hpre.2 hsp fun _ h => h

private theorem spAligned_to_and15 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    sp &&& 15#64 = 0#64 := eq_of_beq h

/-! ## 2. Part 1 (`2^60` Cap): `encodePolyEncoderPinnedSpec[X]` & `encodePolyEncoderSpec[X]` -/

theorem encode_polyEncoder_1_pinned_placed_ok_of_callees [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)}
    (hencLen0 : subroutine_ok (lsProg_456 H) (blkPl_480).base
      (withLsCodeLoaded lsmpl (polynomialEncoderEncodedLenElemsOutSpec A.repAlloc)))
    (hencVarint0 : subroutine_ok (lsProg_456 H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)))
    (hencRep0 : subroutine_ok (lsProg_456 H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpecOf resStack A lim)))
    (hdoReserve0 : subroutine_ok (lsProg_456 H) (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A lim))) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderPinnedSpecOf resStack A lim)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  dsimp only [encodePolyEncoderPinnedSpecOf, encodePolyEncoderPinnedSpecOfEnv] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpts58, hpolys58, hfit, hEnv⟩, hm⟩
  have hcap_bounds : x.bs.length ≤ x.cap.toNat ∧ x.cap.toNat < 2 ^ 63 := by
    have hm' : s0.mem ⊨ ⌜x.bs.length ≤ x.cap.toNat ∧ x.cap.toNat < 2 ^ 63 ∧ x.ptr ≠ 0⌝ ∗
        (vecHeader x.v x.cap x.ptr (BitVec.ofNat 64 x.bs.length) ∗
          (if x.cap = 0 then emp else A.repAlloc.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
            memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
          protoPolynomialEncoderPinnedAt A.repAlloc x.g x.encA x.enc ∗
          A.pool lim st0 s0 ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
      rw [vecU8At] at hm
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    rw [satisfies_pure_sepConj] at hm'
    exact ⟨hm'.1.1, hm'.1.2.1⟩
  have hpb_le := polynomialEncoderPBEncodedLen_le_msg_len x.enc
  have hlen_lt : polynomialEncoderPBEncodedLen x.enc < 2 ^ 64 := by
    rcases hfit with h | h <;> omega
  have hmsg_split := encodePolyEncoderMsg_len_split x.enc
  set y := encodePolyEncoderPinnedToUnpinned x
  have hfits_all : FitsEvents M lim st0 (encodePolyEncoderEvents y) := hEnv _ rfl
  set hdrLen := (polyEncoderHeaderBytes x.enc).length
  set s1 := pushBytesStep hdrLen x.cap.toNat x.bs.length
  set idxLen := (encodeUint32Field 1#32 x.enc.idx).length
  set s2 := pushBytesStep idxLen s1.1 (x.bs.length + hdrLen)
  set ptsLen := (encodeRepeatedBytes 2 x.enc.pts).length
  set s3 := encodeRepeatedStep 2 s2.1 (x.bs.length + hdrLen + idxLen) x.enc.pts
  set s4 := encodeRepeatedStep 3 s3.1 (x.bs.length + hdrLen + idxLen + ptsLen) x.enc.polys
  have hevs_def : encodePolyEncoderEvents y = s1.2 ++ (s2.2 ++ (s3.2 ++ s4.2)) := by
    dsimp only [encodePolyEncoderEvents, y, encodePolyEncoderPinnedToUnpinned,
      hdrLen, s1, idxLen, s2, ptsLen, s3, s4]
    simp only [List.append_assoc]
  rw [hevs_def] at hfits_all
  obtain ⟨hfits_s1, hfits_234⟩ := (fitsEvents_append M lim s1.2 _ st0).mp hfits_all
  set st1 := M.stepEvents s1.2 st0
  obtain ⟨hfits_s2, hfits_34⟩ := (fitsEvents_append M lim s2.2 _ st1).mp hfits_234
  set st2 := M.stepEvents s2.2 st1
  obtain ⟨hfits_s3, hfits_s4⟩ := (fitsEvents_append M lim s3.2 s4.2 st2).mp hfits_34
  set st3 := M.stepEvents s3.2 st2
  have halign : s0.sp &&& 15#64 = 0#64 := spAligned_to_and15 hsp
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  let P0 := protoPolynomialEncoderPinnedAt A.repAlloc x.g x.encA x.enc ∗
    vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st0 s0 ∗
    stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  refine ⟨P0, R, Satisfies.mono (Entails.of_eq (by dsimp only [P0]; sep_ac_rfl)) hm, ?_⟩
  refine step_hdr_1_placed hres A lim
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hencLen0)
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hencVarint0)
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hdoReserve0)
    x.encA x.v x.cap x.ptr s0.sp x.g x.enc x.bs st0 hlen_lt
    (by
      rcases hfit with h | h
      · left; omega
      · right; omega)
    hfits_s1 (F := emp) rfl hpc hrun rfl halign rfl hx0 hx1
    (MsgEnc48CalleeSavedPlaced.refl s0) (by dsimp only [P0]; sep_ac_rfl) ?_
  intro sa sv3 cap1 ptr1 ptsElems polysElems hpts_eq hpts_lt24 hpolys_eq hpolys_lt24
    hpca hruna hspa htra hx19a hx20a hcsa hge1 hpres1 hcap1_eq
  set bs1 := x.bs ++ polyEncoderHeaderBytes x.enc
  have hbs1_len : bs1.length = x.bs.length + hdrLen := List.length_append
  have hfit_idx : bs1.length + idxLen ≤ cap1.toNat ∨ bs1.length + idxLen + 10 < 2 ^ 62 := by
    rw [hbs1_len]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega); omega
    · right; omega
  have hfits_s2' : FitsEvents M lim st1 (pushBytesStep idxLen cap1.toNat bs1.length).2 := by
    simpa only [s2, hcap1_eq, hbs1_len] using hfits_s2
  refine step_idx_1_placed hres128 A lim
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hencVarint0)
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hdoReserve0)
    x.encA x.v cap1 ptr1 s0.sp x.g x.enc ptsElems polysElems bs1 st1
    hfit_idx hfits_s2' hpca hruna hspa halign htra hx19a hx20a hcsa
    (F := polyEncoderRestAt A.repAlloc x.encA x.g ptsElems polysElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp)
        (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_ac_rfl) ?_
  intro sb cap2 ptr2 hpcb hrunb hspb htrb hx19b hx20b hcsb hge2 hpres2 hcap2_eq
  have hcap2_s2 : cap2.toNat = s2.1 := by simpa only [s2, hcap1_eq, hbs1_len] using hcap2_eq
  have hst2_eq :
      M.stepEvents (pushBytesStep idxLen cap1.toNat bs1.length).2 st1 = st2 := by
    simp only [st2, s2, s1, hdrLen, hcap1_eq, hbs1_len]
  rw [hst2_eq]
  set bs2 := bs1 ++ encodeUint32Field 1#32 x.enc.idx
  have hbs2_len : bs2.length = x.bs.length + hdrLen + idxLen := by
    rw [List.length_append, hbs1_len]
  have hfit_pts : bs2.length + ptsLen ≤ cap2.toNat ∨ bs2.length + ptsLen + 10 < 2 ^ 62 := by
    rw [hbs2_len]
    rcases hfit with h | h
    · left
      obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by rw [hbs1_len]; omega)
      omega
    · right; omega
  have hfits_s3' : FitsEvents M lim st2 (encodeRepeatedStep 2 cap2.toNat bs2.length x.enc.pts).2 := by
    simpa only [s3, hcap2_s2, hbs2_len] using hfits_s3
  refine step_pts_1_placed A lim
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hencRep0)
    x.encA x.v cap2 ptr2 s0.sp x.g x.enc ptsElems polysElems bs2 st2
    hpts_eq hpts58 hfit_pts hfits_s3' hpcb hrunb hspb halign htrb hx19b hx20b hcsb
    (F := polyEncoderRestAt A.repAlloc x.encA x.g ptsElems polysElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp)
        (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_ac_rfl) ?_
  intro sc cap3 ptr3 hpcc hrunc hspc htrc hx19c hx20c hcsc hge3 hpres3 hcap3_eq
  have hcap3_s3 : cap3.toNat = s3.1 := by simpa only [s3, hcap2_s2, hbs2_len] using hcap3_eq
  have hst3_eq :
      M.stepEvents (encodeRepeatedStep 2 cap2.toNat bs2.length x.enc.pts).2 st2 = st3 := by
    simp only [st3, s3, hcap2_s2, hbs2_len]
  rw [hst3_eq]
  set bs3 := bs2 ++ encodeRepeatedBytes 2 x.enc.pts
  have hbs3_len : bs3.length = x.bs.length + hdrLen + idxLen + ptsLen := by
    rw [List.length_append, hbs2_len]
  have hfit_polys :
      bs3.length + (encodeRepeatedBytes 3 x.enc.polys).length ≤ cap3.toNat ∨
        bs3.length + (encodeRepeatedBytes 3 x.enc.polys).length + 10 < 2 ^ 62 := by
    rw [hbs3_len]
    rcases hfit with h | h
    · left
      obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by rw [hbs1_len]; omega)
      obtain ⟨rfl, _⟩ := hpres3 (by rw [hbs2_len]; omega)
      omega
    · right; omega
  have hfits_s4' : FitsEvents M lim st3 (encodeRepeatedStep 3 cap3.toNat bs3.length x.enc.polys).2 := by
    simpa only [s4, hcap3_s3, hbs3_len] using hfits_s4
  refine step_polys_1_placed hres A lim
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hencRep0)
    x.encA x.v cap3 ptr3 s0.sp sv3 x.g x.enc ptsElems polysElems bs3 st3
    hpolys_eq hpolys58 hfit_polys hfits_s4' hpcc hrunc hspc halign htrc hx19c hx20c hcsc
    (F := polyEncoderRestAt A.repAlloc x.encA x.g ptsElems polysElems)
    (by sep_ac_rfl) ?_
  intro sf cap4 ptr4 hpcf hrunf hspf htrf hccf _hcsf hge4 hpres4 P_f hent
  refine ⟨fun hmPf => ?_, hspf, hccf⟩
  have hmQ := Satisfies.mono (sepConj_mono_left hent) hmPf
  have hst4_eq :
      M.stepEvents (encodeRepeatedStep 3 cap3.toNat bs3.length x.enc.polys).2 st3 =
        M.stepEvents (encodePolyEncoderEvents y) st0 := by
    simp only [hcap3_s3, hbs3_len, s4, st3, st2, st1, ← M.stepEvents_append, hevs_def,
      List.append_assoc]
  have hbs4_eq : bs3 ++ encodeRepeatedBytes 3 x.enc.polys = x.bs ++ encodePolyEncoderMsg x.enc :=
    (bs0_append_encodePolyEncoderMsg x.bs x.enc).symm
  rw [hst4_eq, hbs4_eq] at hmQ
  have hge_all : x.cap.toNat ≤ cap4.toNat :=
    Nat.le_trans hge1 (Nat.le_trans hge2 (Nat.le_trans hge3 hge4))
  have hpres_all :
      x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat →
        cap4 = x.cap ∧ ptr4 = x.ptr := by
    intro hspare
    obtain ⟨rfl, rfl⟩ := hpres1 (by omega)
    obtain ⟨rfl, rfl⟩ := hpres2 (by rw [hbs1_len]; omega)
    obtain ⟨rfl, rfl⟩ := hpres3 (by rw [hbs2_len]; omega)
    exact hpres4 (by rw [hbs3_len]; omega)
  have hmEnc : sf.mem ⊨
      protoPolynomialEncoderPinnedAt A.repAlloc x.g x.encA x.enc ∗
        (vecU8At A.repAlloc x.v cap4 ptr4 (x.bs ++ encodePolyEncoderMsg x.enc) ∗
          A.pool lim (M.stepEvents (encodePolyEncoderEvents y) st0) sf ∗
          stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [satisfies_protoPolynomialEncoderPinnedAt_iff]
    exact ⟨ptsElems, polysElems, hpts_eq, hpts_lt24, hpolys_eq, hpolys_lt24,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmQ⟩
  dsimp only [encodePolyEncoderPinnedSpecOf, encodePolyEncoderPinnedSpecOfEnv]
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  have hmGoal : sf.mem ⊨
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodePolyEncoderMsg x.enc)) ∗
      ((∃∗ evs : List AllocEvent,
          ⌜EncodePolyEncoderEnv (encodePolyEncoderPinnedToUnpinned x) evs⌝ ∗
          A.pool lim (M.stepEvents evs st0) sf) ∗
        protoPolynomialEncoderPinnedAt A.repAlloc x.g x.encA x.enc ∗
        stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨cap4, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨ptr4, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hge_all, hpres_all⟩, ?_⟩
    rw [sepConj_left_comm (vecU8At A.repAlloc x.v cap4 ptr4 (x.bs ++ encodePolyEncoderMsg x.enc))]
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨encodePolyEncoderEvents y, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨rfl, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmEnc
  convert hmGoal using 1; sep_ac_rfl


theorem encode_polyEncoder_1_pinned_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyEncoder1PinnedPlacedOk A lim H :=
  have hmc' : HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec := hmc
  encode_polyEncoder_1_pinned_placed_ok_of_callees (resStack := doReserveStack) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (subroutine_ok_polyEncLenElemsOut_of_pinned
          (polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A.repAlloc H))))
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (encode_repeated_1_placed_ok_of_callees (resStack := doReserveStack) (by decide)
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
        (spqr_hook_ok_of_mem hmc')))
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc))

theorem encode_polyEncoder_1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyEncoder1PlacedOk A lim H :=
  polyEncoder_unpinned_of_pinned_placed_x
    (encode_polyEncoder_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem encode_polyEncoder_1_pinned_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyEncoder1PinnedPlacedOkX A lim H :=
  have hmc' : HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec := hmc
  encode_polyEncoder_1_pinned_placed_ok_of_callees (resStack := doReserveStackX) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (subroutine_ok_polyEncLenElemsOut_of_pinned
          (polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A.repAlloc H))))
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (encode_repeated_1_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
        (spqr_hook_ok_of_mem hmc')))
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))

theorem encode_polyEncoder_1_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyEncoder1PlacedOkX A lim H :=
  polyEncoder_unpinned_of_pinned_placed_x
    (encode_polyEncoder_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

theorem encode_polyEncoder_1_pinned_placed_ok_of_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    EncodePolyEncoder1PinnedPlacedOk A lim H :=
  have hmc' := subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym allocMemcpyVmSpec from hmc))
  encode_polyEncoder_1_pinned_placed_ok_of_callees (resStack := doReserveStack) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (subroutine_ok_polyEncLenElemsOut_of_pinned
          (polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A.repAlloc H))))
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (encode_repeated_1_placed_ok_of_callees (resStack := doReserveStack) (by decide)
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
        hmc'))
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc))

theorem encode_polyEncoder_1_placed_ok_of_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    EncodePolyEncoder1PlacedOk A lim H :=
  polyEncoder_unpinned_of_pinned_placed_x
    (encode_polyEncoder_1_pinned_placed_ok_of_vm h_panic hshim halloc hrealloc hmc)

theorem encode_polyEncoder_1_pinned_placed_ok_x_of_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    EncodePolyEncoder1PinnedPlacedOkX A lim H :=
  have hmc' := subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym allocMemcpyVmSpec from hmc))
  encode_polyEncoder_1_pinned_placed_ok_of_callees (resStack := doReserveStackX) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (subroutine_ok_polyEncLenElemsOut_of_pinned
          (polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A.repAlloc H))))
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (encode_repeated_1_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
        hmc'))
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))

theorem encode_polyEncoder_1_placed_ok_x_of_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    EncodePolyEncoder1PlacedOkX A lim H :=
  polyEncoder_unpinned_of_pinned_placed_x
    (encode_polyEncoder_1_pinned_placed_ok_x_of_vm h_panic hshim halloc hrealloc hmc)

theorem encode_polyEncoder_1_pinned_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyEncoder1PinnedPlacedOkExt A lim ext :=
  encode_polyEncoder_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc

theorem encode_polyEncoder_1_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyEncoder1PlacedOkExt A lim ext :=
  encode_polyEncoder_1_placed_ok h_panic hshim halloc hrealloc hmc

theorem encode_polyEncoder_1_pinned_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyEncoder1PinnedPlacedOkExtX A lim ext :=
  encode_polyEncoder_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc

theorem encode_polyEncoder_1_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyEncoder1PlacedOkExtX A lim ext :=
  encode_polyEncoder_1_placed_ok_x h_panic hshim halloc hrealloc hmc

/-! ## 3. Part 2 (`2^59` Exact Cap): `encodePolyEncoderExactSpecOf` & `etvPolyEncoderExactSpecOf` -/

theorem polyEncoder1_exact_gen_placed_ok [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} {B : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : EncodePolyEncoderPinnedGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok (lsProg_456 H) (blkPl_480).base
      (withMsgEnc48CSPlaced s0 (polynomialEncoderEncodedLenElemsOutSpec B.repAlloc)))
    (hencV : subroutine_ok (lsProg_456 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (hencR : subroutine_ok (lsProg_456 H) (blkPl_448).base
      (withMsgEnc48CSPlaced s0 (encodeRepeated59ExactSpecOf resStack B lim)))
    (hpc : s0.pc = (blkPl_456).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyEncoderExactSpecOf resStack B lim).pre (x, st0) s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_456 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodePolyEncoderExactSpecOf resStack B lim).post (x, st0) s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodePolyEncoderExactSpecOf resStack B lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := spAligned_to_and15 hsp_align
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  have hpre_pure := hpre; dsimp only [encodePolyEncoderExactSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hfit⟩, hpre_mem⟩ := hpre_pure
  have hpre_rewritten : s0.mem ⊨ ((protoPolynomialEncoderPinnedAt B.repAlloc x.g x.encA x.enc ∗
      vecU8At B.repAlloc x.v x.cap x.ptr x.bs ∗ B.pool lim st0 s0 ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ emp) ∗ R := by
    convert hpre_mem using 1; sep_ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodePolyEncoderMsg_len_split x.enc
  have hlen_le_msg := polynomialEncoderPBEncodedLen_le_msg_len x.enc
  have hcap_lt : x.cap.toNat < 2 ^ 64 := BitVec.isLt x.cap
  have hlen_lt : polynomialEncoderPBEncodedLen x.enc < 2 ^ 64 := by omega
  refine step_pe1_hdr_exact_placed hres B lim H hencLen hencV x.encA x.v x.cap x.ptr s0.sp
    x.g x.enc x.bs st0 hlen_lt (by omega) (F := emp)
    rfl hpc hrun rfl halign rfl hx0 hx1 (MsgEnc48CalleeSavedPlaced.refl s0) rfl ?_
  intro s1 sv3 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1
  have hfit_idx : (x.bs ++ polyEncoderHeaderBytes x.enc).length +
      (encodeUint32Field 1#32 x.enc.idx).length ≤ x.cap.toNat := by
    rw [List.length_append]; omega
  refine step_pe1_idx_exact_placed hres128 B lim H hencV x.encA x.v x.cap x.ptr s0.sp x.g x.enc
    ptsElems polysElems (x.bs ++ polyEncoderHeaderBytes x.enc) st0 hfit_idx
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := polyEncoderRestAt B.repAlloc x.encA x.g ptsElems polysElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    (by sep_ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
  let bs_idx := (x.bs ++ polyEncoderHeaderBytes x.enc) ++ encodeUint32Field 1#32 x.enc.idx
  have hfit_pts : bs_idx.length + (encodeRepeatedBytes 2 x.enc.pts).length ≤ x.cap.toNat := by
    dsimp [bs_idx]; rw [List.length_append, List.length_append]; omega
  have hfit_polys : (bs_idx ++ encodeRepeatedBytes 2 x.enc.pts).length +
      (encodeRepeatedBytes 3 x.enc.polys).length ≤ x.cap.toNat := by
    dsimp [bs_idx]; rw [List.length_append, List.length_append, List.length_append]; omega
  refine step_pe1_pts_polys_exact_placed hres B lim H hencR x.encA x.v x.cap x.ptr s0.sp sv3 x.g x.enc
    ptsElems polysElems bs_idx st0 hpts_eq (by omega) hpolys_eq (by omega) hfit_pts hfit_polys
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := polyEncoderRestAt B.repAlloc x.encA x.g ptsElems polysElems ∗ emp)
    (by dsimp [bs_idx]; sep_ac_rfl) ?_
  intro sf _ _ hspf htrf hccf _
  refine ⟨fun hm => ?_, hspf, hccf⟩
  have hm_pack : sf.mem ⊨ (polyEncoderElemsAt x.encA x.g x.enc ptsElems polysElems ∗
      polyEncoderRestAt B.repAlloc x.encA x.g ptsElems polysElems) ∗
      (vecU8At B.repAlloc x.v x.cap x.ptr (x.bs ++ encodePolyEncoderMsg x.enc) ∗
        B.pool lim st0 sf ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [bs0_append_encodePolyEncoderMsg x.bs x.enc]
    convert hm using 1; dsimp [bs_idx]; sep_ac_rfl
  have hm_pinned := (satisfies_protoPolynomialEncoderPinnedAt_iff B.repAlloc x.g x.encA x.enc _ sf.mem).mpr
    ⟨ptsElems, polysElems, hpts_eq, hpts_lt, hpolys_eq, hpolys_lt, hm_pack⟩
  dsimp only [encodePolyEncoderExactSpecOf]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  convert hm_pinned using 1; sep_ac_rfl

private theorem encode_polyEncoder_1_exact_vm_pinned_placed_ok_of_memcpy_and_resStack
    [LibsignalPlacement] {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactVmSpecOf resStack A.repAlloc)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  let B := vmTrackBudget A s0
  have hpreB : s0.mem ⊨
      (encodePolyEncoderExactSpecOf resStack B impossibleEnforcedLimits).pre (x, M.init) s0 ∗ R := by
    dsimp only [encodePolyEncoderExactVmSpecOf] at hpre
    dsimp only [encodePolyEncoderExactSpecOf, B, vmTrackBudget, impossibleEnforcedLimits,
      RustCliAllocBudget.repAlloc]
    simp only [↓reduceIte]
    have hpre1 : s0.mem ⊨ ⌜VmPreserved s0 s0⌝ ∗
        ((⌜s0.readReg64 .x0 = x.encA ∧ s0.readReg64 .x1 = x.v ∧
            x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat⌝ ∗
          protoPolynomialEncoderPinnedAt A.repAlloc x.g x.encA x.enc ∗
          vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
          stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ R) := by
      rw [satisfies_pure_sepConj]; exact ⟨VmPreserved.refl s0, hpre⟩
    convert hpre1 using 1; sep_ac_rfl
  have hencLen := subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (subroutine_ok_polyEncLenElemsOut_of_pinned
          (polynomialEncoderEncodedLen_local1_pinned_placed_ok_x B.repAlloc H))))
  have hencV := subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H)
      (encodeVarint2_fit_impossible_placed_ok (resStack := resStack) (by omega) B H))
  have hencR59 := subroutine_ok_encodeRepeated59Exact_of_59_placed
    (encodeRepeated59SpecOf_of_det_placed
      (encode_repeated_1_59_placed_ok_of_callees (resStack := resStack) (by omega)
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (encodeVarint2_det_placed_ok_of_doReserve (resStack := resStack) (by omega) B
            impossibleEnforcedLimits H (doReserve2_impossible_ok B)))
        (doReserve2_impossible_ok B)
        hmemcpy))
  have hencR := subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
    (ls_subroutine_ok_of_block (callerProg := lsProg_456 H) hencR59)
  obtain ⟨P, hP, hwp⟩ := polyEncoder1_exact_gen_placed_ok hres (B := B)
    (lim := impossibleEnforcedLimits) hencLen hencV hencR hpc hrun hpreB hsp
  refine ⟨P, R, hP, sepWPp_mono ?_ ?_ hwp⟩
  · intro sf Q ⟨hq, hspf, hccf⟩
    refine ⟨fun hm => ?_, hspf, hccf⟩
    have hpost := hq hm
    dsimp only [encodePolyEncoderExactSpecOf, B, vmTrackBudget, impossibleEnforcedLimits,
      RustCliAllocBudget.repAlloc] at hpost
    simp only [↓reduceIte] at hpost
    have hpost1 : sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
        (⌜VmPreserved s0 sf⌝ ∗
          (protoPolynomialEncoderPinnedAt A.repAlloc x.g x.encA x.enc ∗
            vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodePolyEncoderMsg x.enc) ∗
            stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R)) := by
      convert hpost using 1; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost1
    obtain ⟨htrf, hvmp, hrest⟩ := hpost1
    dsimp only [encodePolyEncoderExactVmSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hvmp, htrf⟩, by convert hrest using 1; sep_ac_rfl⟩
  · intro sf P_f hpan hm
    exact hpan hm

theorem encode_polyEncoder_1_exact_vm_pinned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactVmSpecOf doReserveStack A.repAlloc)) :=
  encode_polyEncoder_1_exact_vm_pinned_placed_ok_of_memcpy_and_resStack (by decide)
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec from hmc))

theorem encode_polyEncoder_1_exact_vm_pinned_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactVmSpecOf doReserveStackX A.repAlloc)) :=
  encode_polyEncoder_1_exact_vm_pinned_placed_ok_of_memcpy_and_resStack (by decide)
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec from hmc))

theorem encode_polyEncoder_1_exact_vm_pinned_placed_ok_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactVmSpecOf doReserveStack A.repAlloc)) :=
  encode_polyEncoder_1_exact_vm_pinned_placed_ok_of_memcpy_and_resStack (by decide)
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
      (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym allocMemcpyVmSpec from hmc)))

theorem encode_polyEncoder_1_exact_vm_pinned_placed_ok_x_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactVmSpecOf doReserveStackX A.repAlloc)) :=
  encode_polyEncoder_1_exact_vm_pinned_placed_ok_of_memcpy_and_resStack (by decide)
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
      (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym allocMemcpyVmSpec from hmc)))

theorem encode_polyEncoder_1_exact_pinned_placed_ok_of_memcpy [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStack A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodePolyEncoderExact_of_vm
    (encode_polyEncoder_1_exact_vm_pinned_placed_ok hmc)

theorem encode_polyEncoder_1_exact_pinned_placed_ok_of_memcpy_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStackX A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodePolyEncoderExact_of_vm
    (encode_polyEncoder_1_exact_vm_pinned_placed_ok_x hmc)

theorem encode_polyEncoder_1_exact_pinned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStack A lim)) :=
  encode_polyEncoder_1_exact_pinned_placed_ok_of_memcpy hmc

theorem encode_polyEncoder_1_exact_pinned_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStackX A lim)) :=
  encode_polyEncoder_1_exact_pinned_placed_ok_of_memcpy_x hmc

theorem encode_polyEncoder_1_exact_pinned_placed_ok_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStack A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodePolyEncoderExact_of_vm
    (encode_polyEncoder_1_exact_vm_pinned_placed_ok_of_vm hmc)

theorem encode_polyEncoder_1_exact_pinned_placed_ok_x_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStackX A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodePolyEncoderExact_of_vm
    (encode_polyEncoder_1_exact_vm_pinned_placed_ok_x_of_vm hmc)

theorem etv_polyEncoderEncode_1_exact_vm_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStack A.repAlloc)) :=
  etv_polyEncoderEncode_exact_of_lscl
    (encode_polyEncoder_1_exact_vm_pinned_placed_ok hmc)

theorem etv_polyEncoderEncode_1_exact_vm_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStackX A.repAlloc)) :=
  etv_polyEncoderEncode_exact_of_lscl
    (encode_polyEncoder_1_exact_vm_pinned_placed_ok_x hmc)

theorem etv_polyEncoderEncode_1_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStack A.repAlloc)) :=
  etv_polyEncoderEncode_1_exact_vm_placed_ok hmc

theorem etv_polyEncoderEncode_1_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStackX A.repAlloc)) :=
  etv_polyEncoderEncode_1_exact_vm_placed_ok_x hmc

theorem etv_polyEncoderEncode_1_exact_placed_ok_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStack A.repAlloc)) :=
  etv_polyEncoderEncode_exact_of_lscl
    (encode_polyEncoder_1_exact_vm_pinned_placed_ok_of_vm hmc)

theorem etv_polyEncoderEncode_1_exact_placed_ok_x_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_456 H) (blkPl_456).base
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStackX A.repAlloc)) :=
  etv_polyEncoderEncode_exact_of_lscl
    (encode_polyEncoder_1_exact_vm_pinned_placed_ok_x_of_vm hmc)

abbrev etv_polyEncoderEncode_exact_placed_ok := @etv_polyEncoderEncode_1_exact_placed_ok
abbrev etv_polyEncoderEncode_exact_placed_ok_x := @etv_polyEncoderEncode_1_exact_placed_ok_x

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoder1PlacedBudget
