/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1PlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `encode<PolynomialDecoder> [local#3]` Verification (Block `455`)

Proves budget-threaded `2^60`-cap and exact `2^59`-cap `subroutine_ok` and `EncodeToVec` contracts
for `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>> [local#3]` on CLI Block `455`
under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1PlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAlloc RustCliAllocBudget RustLayoutOk
   VmPreserved allocMemcpyVmSpec rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsMemcpySym
   ls_subroutine_ok_of_block lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeBoolField encodeUint32Field)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Poly (protoPolynomialDecoderPinnedAt)
open CryptoVerification.SpqrV1.Varint (encodeRepeatedBytes)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodePolyDecoderPinnedGhost MsgEnc48CalleeSavedPlaced bs0_append_encodePolyDecoderMsg
   encodePolyDecoderMsg encodePolyDecoderMsg_len_split msgEnc48RepeatedStackOf msgEnc48SavedFrame
   polyDecoderElemsAt polyDecoderHeaderBytes polyDecoderRestAt polynomialDecoderPBEncodedLen
   polynomialDecoderPBEncodedLen_le_msg_len satisfies_protoPolynomialDecoderPinnedAt_iff
   subroutine_ok_withMsgEnc48CSPlaced_placed withMsgEnc48CSPlaced)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed (blkPl_460)
open CryptoVerification.Cli.SpqrV1.Varint.Placed
  (blkPl_448 lsProg_448 blkPl_451)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced (blkPl_493)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed (blkPl_455 lsProg_455)
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
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (VecU8EncodeEnv fitsEnv_vecU8EncodeEnv_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBaseBudget
  (EncodePolyDecoderPinnedEnv encodePolyDecoderPinnedEnv_eq_nil_of_spare
   encodePolyDecoderPinnedExactVmSpecOf encodePolyDecoderPinnedSpec
   encodePolyDecoderPinnedSpecOf encodePolyDecoderPinnedSpecX
   encodePolyDecoderSpec encodePolyDecoderSpecX
   polynomialDecoderEncodedLenElemsOutSpec subroutine_ok_polyDecLenElemsOut_of_pinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlacedBudget
  (polyDecoder_unpinned_of_pinned_placed_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncodedLenPlacedBudget
  (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlacedBudget
  (EncodePolyDecoder1PinnedExactPlacedOk EncodePolyDecoder1PinnedPlacedOkExt
   EncodePolyDecoder1PinnedPlacedOkExtX EncodePolyDecoder1PlacedOkExt
   EncodePolyDecoder1PlacedOkExtX)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
  (encodeRepeated59ExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedABudget
  (encodeRepeated59SpecOf_of_det_placed subroutine_ok_encodeRepeated59Exact_of_59_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedBudget
  (impossibleEnforcedLimits sepWPp_mono vmTrackBudget)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget
  (encodePolyDecoderExactSpecOf encodePolyDecoderExactVmSpecOf
   subroutine_ok_withLsCodeLoaded_encodePolyDecoderExact_of_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactPlacedBudget
  (etv_polyDecoderEncode_exact_of_lscl)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (etvPolyDecoderExactSpecOf)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1PlacedBudgetAux
  (PolyDecoderBudgetInv doReserve2_impossible_ok encodeVarint2_fit_impossible_placed_ok
   noAllocCostModel protoPolynomialDecoderPinnedAt_rawVmRecordBudget rawVmRecordBudget
   rawVmRecordBudget_pool_zeroEnforced step_isComplete_1_placed step_pd1_hdr_exact_placed
   step_pd1_hdr_placed step_pd1_polys_exact_placed step_pd1_ptsNeeded_exact_placed
   step_pd1_pts_isComplete_exact_placed step_polys_1_placed step_ptsNeeded_1_placed
   step_pts_1_placed vacuous_doReserve2_placed_ok vecU8At_rawVmRecordBudget vmRecordBudget
   vmRecordBudget_pool_zeroEnforced vmRecordBudget_repAlloc zeroEnforcedLimits)

/-! ## 1. Subroutine Lifting & Postcondition Helpers -/

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

private theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q1 Q2 Qp1 Qp2 : State → SepProp → Prop} (h : SepWPp prog ret s P Q1 Qp1)
    (hq : ∀ sf Pf, Q1 sf Pf → Q2 sf Pf) (hqp : ∀ sf Pf, Qp1 sf Pf → Qp2 sf Pf) :
    SepWPp prog ret s P Q2 Qp2 := fun R hm hL => by
  obtain ⟨sf, hst, ⟨h1, h2, Pf, hmf, hQ⟩ | ⟨hp, Pf, hmf, hQp⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨h1, h2, Pf, hmf, hq sf Pf hQ⟩⟩
  · exact ⟨sf, hst, Or.inr (Or.inl ⟨hp, Pf, hmf, hqp sf Pf hQp⟩)⟩
  · exact ⟨sf, hst, Or.inr (Or.inr hoom)⟩

private theorem satisfies_encodePolyDecoderPinned_post {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (x : EncodePolyDecoderPinnedGhost) (st0 : M.σ)
    (s0 sf : State) (R : SepProp) (cap' ptr' : BitVec 64) (evs : List AllocEvent)
    (htrf : sf.trace = s0.trace) (hge : x.cap.toNat ≤ cap'.toNat)
    (hpres : x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
      cap' = x.cap ∧ ptr' = x.ptr)
    (hEnv : EncodePolyDecoderPinnedEnv x evs)
    (hsp_ev : x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
      evs = [] ∧ VmPreserved s0 sf)
    (hm : sf.mem ⊨ protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
      (vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
        A.pool lim (M.stepEvents evs st0) sf ∗
        stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R)) :
    sf.mem ⊨ (encodePolyDecoderPinnedSpecOf resStack A lim).post (x, st0) s0 sf ∗ R := by
  dsimp only [encodePolyDecoderPinnedSpecOf]
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  have hmGoal : sf.mem ⊨
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec)) ∗
      ((∃∗ evs : List AllocEvent,
          ⌜EncodePolyDecoderPinnedEnv x evs ∧
            (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
              evs = [] ∧ VmPreserved s0 sf)⌝ ∗
          A.pool lim (M.stepEvents evs st0) sf) ∗
        protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
        stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨cap', ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨ptr', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hge, hpres⟩, ?_⟩
    rw [sepConj_left_comm (vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec))]
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hEnv, hsp_ev⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  convert hmGoal using 1; sep_ac_rfl

/-! ## 2. Part 1 (`2^60` Cap): Core `SepWPp` & `VmPreserved` Assembly for Block `455` -/

theorem polyDecoder1_core_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)}
    {x : EncodePolyDecoderPinnedGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    (_hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hencLen : subroutine_ok (lsProg_455 H) (lsmpl.base 493)
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec A.repAlloc)))
    (hencVarint : subroutine_ok (lsProg_455 H) (lsmpl.base 451)
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hencRep : subroutine_ok (lsProg_455 H) (lsmpl.base 448)
      (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_455 H) (lsmpl.base 460)
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hpc : s0.pc = (blkPl_455).base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyDecoderPinnedSpecOf resStack A lim).pre (x, st0) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_455 H) (s0.readReg64 .lr) s0 P
        (fun sf P_f =>
          (∃ cap' ptr' evs,
            sf.trace = s0.trace ∧
            x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr) ∧
            EncodePolyDecoderPinnedEnv x evs ∧
            ∀ R', sf.mem ⊨ P_f ∗ R' →
              sf.mem ⊨ protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
                (vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
                  A.pool lim (M.stepEvents evs st0) sf ∗
                  stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R')) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun _ _ => False) := by
  have halign : s0.sp &&& 15#64 = 0#64 := spAligned_to_and15 hsp
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  dsimp only [encodePolyDecoderPinnedSpecOf] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hx1, hx2, hpts58, hfit, hEnv⟩, hm⟩
  have hcap_lt : x.cap.toNat < 2 ^ 64 := BitVec.isLt x.cap
  have hlen_split := encodePolyDecoderMsg_len_split x.tag x.dec
  have hlen_le_msg := polynomialDecoderPBEncodedLen_le_msg_len x.tag x.dec
  have hlen_lt : polynomialDecoderPBEncodedLen x.dec < 2 ^ 64 := by
    rcases hfit with h | h <;> omega
  let P0 := protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
    vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st0 s0 ∗
    stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  refine ⟨P0, Satisfies.mono (Entails.of_eq (by dsimp only [P0]; sep_ac_rfl)) hm, ?_⟩
  refine step_pd1_hdr_placed hres A lim hencLen hencVarint x st0 s0.sp
    (PolyDecoderBudgetInv.init hEnv) hlen_lt (by omega)
    (by rcases hfit with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
    (F := emp) rfl hpc hrun rfl halign rfl hw0 hx1 hx2
    (MsgEnc48CalleeSavedPlaced.refl s0) (by dsimp only [P0]; sep_ac_rfl) ?_
  intro s1 sv3 cap1 ptr1 ptsElems evs1 hpts_eq hpts_lt24 hpc1 hrun1 hsp1 htr1
    hx19_1 hx20_1 hcs1 hge1 hpres1 inv1
  set bs1 := x.bs ++ polyDecoderHeaderBytes x.tag x.dec
  have hbs1_len : bs1.length = x.bs.length + (polyDecoderHeaderBytes x.tag x.dec).length :=
    List.length_append
  have hfit_pn :
      bs1.length + (encodeUint32Field 1#32 x.dec.ptsNeeded).length ≤ cap1.toNat ∨
        bs1.length + (encodeUint32Field 1#32 x.dec.ptsNeeded).length + 10 < 2 ^ 62 := by
    rw [hbs1_len]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega); omega
    · right; omega
  refine step_ptsNeeded_1_placed hres128 A lim hencVarint hdoReserve x st0 cap1 ptr1 s0.sp
    ptsElems bs1 evs1 inv1 (by rw [hbs1_len]; omega) hfit_pn
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := polyDecoderRestAt A.repAlloc x.decA x.g ptsElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_ac_rfl) ?_
  intro s2 cap2 ptr2 evs2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hge2 hpres2 inv2
  set bs2 := bs1 ++ encodeUint32Field 1#32 x.dec.ptsNeeded
  have hbs2_len : bs2.length =
      x.bs.length + (polyDecoderHeaderBytes x.tag x.dec).length +
        (encodeUint32Field 1#32 x.dec.ptsNeeded).length := by
    rw [List.length_append, hbs1_len]
  have hfit_pl :
      bs2.length + (encodeUint32Field 2#32 x.dec.polys).length ≤ cap2.toNat ∨
        bs2.length + (encodeUint32Field 2#32 x.dec.polys).length + 10 < 2 ^ 62 := by
    rw [hbs2_len]
    rcases hfit with h | h
    · left
      obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by rw [hbs1_len]; omega)
      omega
    · right; omega
  refine step_polys_1_placed hres128 A lim hencVarint hdoReserve x st0 cap2 ptr2 s0.sp
    ptsElems bs2 evs2 inv2 (by rw [hbs2_len]; omega) hfit_pl
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := polyDecoderRestAt A.repAlloc x.decA x.g ptsElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_ac_rfl) ?_
  intro s3 cap3 ptr3 evs3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 hge3 hpres3 inv3
  set bs3 := bs2 ++ encodeUint32Field 2#32 x.dec.polys
  have hbs3_len : bs3.length =
      x.bs.length + (polyDecoderHeaderBytes x.tag x.dec).length +
        (encodeUint32Field 1#32 x.dec.ptsNeeded).length +
        (encodeUint32Field 2#32 x.dec.polys).length := by
    rw [List.length_append, hbs2_len]
  have hfit_pts :
      bs3.length + (encodeRepeatedBytes 3 x.dec.pts).length ≤ cap3.toNat ∨
        bs3.length + (encodeRepeatedBytes 3 x.dec.pts).length + 10 < 2 ^ 62 := by
    rw [hbs3_len]
    rcases hfit with h | h
    · left
      obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by rw [hbs1_len]; omega)
      obtain ⟨rfl, _⟩ := hpres3 (by rw [hbs2_len]; omega)
      omega
    · right; omega
  refine step_pts_1_placed A lim hencRep x st0 cap3 ptr3 s0.sp
    ptsElems bs3 evs3 inv3 hpts_eq hpts58 (by rw [hbs3_len]; omega) hfit_pts
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3
    (F := polyDecoderRestAt A.repAlloc x.decA x.g ptsElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_ac_rfl) ?_
  intro s4 cap4 ptr4 evs4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 hge4 hpres4 inv4
  set bs4 := bs3 ++ encodeRepeatedBytes 3 x.dec.pts
  have hbs4_len : bs4.length =
      x.bs.length + (polyDecoderHeaderBytes x.tag x.dec).length +
        (encodeUint32Field 1#32 x.dec.ptsNeeded).length +
        (encodeUint32Field 2#32 x.dec.polys).length +
        (encodeRepeatedBytes 3 x.dec.pts).length := by
    rw [List.length_append, hbs3_len]
  have hfit_ic :
      bs4.length + (encodeBoolField 4#32 x.dec.isComplete).length ≤ cap4.toNat ∨
        bs4.length + (encodeBoolField 4#32 x.dec.isComplete).length + 10 < 2 ^ 62 := by
    rw [hbs4_len]
    rcases hfit with h | h
    · left
      obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by rw [hbs1_len]; omega)
      obtain ⟨rfl, _⟩ := hpres3 (by rw [hbs2_len]; omega)
      obtain ⟨rfl, _⟩ := hpres4 (by rw [hbs3_len]; omega)
      omega
    · right; omega
  refine step_isComplete_1_placed hres A lim hdoReserve x st0 cap4 ptr4 s0.sp sv3
    ptsElems bs4 evs4 inv4 (by rw [hbs4_len]; omega) hfit_ic
    hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hcs4
    (F := polyDecoderRestAt A.repAlloc x.decA x.g ptsElems)
    (by sep_ac_rfl) ?_
  intro sf cap5 ptr5 evs5 _hpcf _hrunf hspf htrf hccf _hcsf hge5 hpres5 inv5 P_f hent
  have hge_all : x.cap.toNat ≤ cap5.toNat :=
    Nat.le_trans hge1 (Nat.le_trans hge2 (Nat.le_trans hge3 (Nat.le_trans hge4 hge5)))
  have hpres_all :
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
        cap5 = x.cap ∧ ptr5 = x.ptr := by
    intro hspare
    obtain ⟨rfl, rfl⟩ := hpres1 (by omega)
    obtain ⟨rfl, rfl⟩ := hpres2 (by rw [hbs1_len]; omega)
    obtain ⟨rfl, rfl⟩ := hpres3 (by rw [hbs2_len]; omega)
    obtain ⟨rfl, rfl⟩ := hpres4 (by rw [hbs3_len]; omega)
    exact hpres5 (by rw [hbs4_len]; omega)
  refine ⟨⟨cap5, ptr5, evs5, htrf, hge_all, hpres_all, ⟨cap5.toNat, inv5.chain⟩, ?_⟩, hspf, hccf⟩
  intro R' hmPf
  have hmQ := Satisfies.mono (sepConj_mono_left hent) hmPf
  have hbs5_eq : bs4 ++ encodeBoolField 4#32 x.dec.isComplete =
      x.bs ++ encodePolyDecoderMsg x.tag x.dec :=
    (bs0_append_encodePolyDecoderMsg x.bs x.tag x.dec).symm
  rw [hbs5_eq] at hmQ
  rw [satisfies_protoPolynomialDecoderPinnedAt_iff]
  exact ⟨ptsElems, hpts_eq, hpts_lt24, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmQ⟩

theorem encode_polyDecoder_1_pinned_placed_ok_of_callees [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)}
    (hencLen0 : subroutine_ok (lsProg_455 H) (lsmpl.base 493)
      (withLsCodeLoaded lsmpl (polynomialDecoderEncodedLenElemsOutSpec A.repAlloc)))
    (hencVarint0 : subroutine_ok (lsProg_455 H) (lsmpl.base 451)
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)))
    (hencRep0 : subroutine_ok (lsProg_455 H) (lsmpl.base 448)
      (withLsCodeLoaded lsmpl (encodeRepeatedSpecOf resStack A lim)))
    (hdoReserve0 : subroutine_ok (lsProg_455 H) (lsmpl.base 460)
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecOf resStack A lim)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  by_cases hspare : x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat
  · have hpre_pure := hpre
    dsimp only [encodePolyDecoderPinnedSpecOf] at hpre_pure
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      at hpre_pure
    rcases hpre_pure with ⟨⟨hw0, hx1, hx2, hpts58, _, _⟩, hmem⟩
    have hpreVac : s0.mem ⊨
        (encodePolyDecoderPinnedSpecOf resStack (vmRecordBudget A s0) zeroEnforcedLimits).pre
          (x, ()) s0 ∗ (A.pool lim st0 s0 ∗ R) := by
      dsimp only [encodePolyDecoderPinnedSpecOf]
      rw [vmRecordBudget_pool_zeroEnforced, vmRecordBudget_repAlloc]
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hw0, hx1, hx2, hpts58, Or.inl hspare,
        fitsEnv_vecU8EncodeEnv_of_spare noAllocCostModel zeroEnforcedLimits () hspare⟩, ?_⟩
      have hmem' : s0.mem ⊨ ⌜VmPreserved s0 s0⌝ ∗
          (protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
            vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
            stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ A.pool lim st0 s0 ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨VmPreserved.refl s0, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem'
    have hencVarVac := encodeVarint2_det_placed_ok_of_doReserve (resStack := resStack) (by omega)
      (vmRecordBudget A s0) zeroEnforcedLimits H (vacuous_doReserve2_placed_ok (vmRecordBudget A s0))
    have hencRepVac := encode_repeated_1_placed_ok_of_callees (resStack := resStack) (by omega)
      (A := vmRecordBudget A s0) (lim := zeroEnforcedLimits)
      (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) hencVarVac)
      (vacuous_doReserve2_placed_ok (vmRecordBudget A s0)) hmemcpy
    obtain ⟨P, hP, hwp⟩ := polyDecoder1_core_placed_ok hres
      (vmRecordBudget A s0) zeroEnforcedLimits hcl0
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hencLen0)
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
        (ls_subroutine_ok_of_block (callerProg := lsProg_455 H) hencVarVac))
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
        (ls_subroutine_ok_of_block (callerProg := lsProg_455 H) hencRepVac))
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
        (vacuous_doReserve2_placed_ok (vmRecordBudget A s0)))
      hpc hrun hpreVac hsp
    refine ⟨P, A.pool lim st0 s0 ∗ R, hP, sepWPp_mono_post hwp ?_ (fun _ _ h => h.elim)⟩
    rintro sf P_f ⟨⟨cap', ptr', evs, htrf, _, hpres, hEnv, hmFn⟩, hspf, hccf⟩
    rcases hpres hspare with ⟨rfl, rfl⟩
    have hevs : evs = [] := encodePolyDecoderPinnedEnv_eq_nil_of_spare hspare hEnv
    subst hevs
    refine ⟨fun hmPf => ?_, hspf, hccf⟩
    have hmPost := hmFn (A.pool lim st0 s0 ∗ R) hmPf
    rw [vmRecordBudget_pool_zeroEnforced, vmRecordBudget_repAlloc] at hmPost
    have hmPure : sf.mem ⊨ ⌜VmPreserved s0 sf⌝ ∗
        (protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
          (vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
            A.pool lim (M.stepEvents [] st0) s0 ∗
            stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R)) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmPost
    rw [satisfies_pure_sepConj] at hmPure
    rcases hmPure with ⟨hvm, hmRest⟩
    rw [← A.pool_of_vmPreserved hvm] at hmRest
    exact satisfies_encodePolyDecoderPinned_post A lim x st0 s0 sf R x.cap x.ptr [] htrf
      (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (VecU8EncodeEnv.nil _ _)
      (fun _ => ⟨rfl, hvm⟩) hmRest
  · obtain ⟨P, hP, hwp⟩ := polyDecoder1_core_placed_ok hres A lim hcl0
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hencLen0)
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hencVarint0)
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hencRep0)
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hdoReserve0)
      hpc hrun hpre hsp
    refine ⟨P, R, hP, sepWPp_mono_post hwp ?_ (fun _ _ h => h.elim)⟩
    rintro sf P_f ⟨⟨cap', ptr', evs, htrf, hge, hpres, hEnv, hmFn⟩, hspf, hccf⟩
    refine ⟨fun hmPf => ?_, hspf, hccf⟩
    exact satisfies_encodePolyDecoderPinned_post A lim x st0 s0 sf R cap' ptr' evs htrf
      hge hpres hEnv (fun h => absurd h hspare) (hmFn R hmPf)

/-! ## 3. Exact `< 2^58` 0-Allocation Contracts (`EncodePolyDecoder1PinnedExactPlacedOk`) -/

theorem polyDecoder1_exact_placed_ok_of_memcpy [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢
      ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    {H : String → Option (State → State)}
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec) :
    EncodePolyDecoder1PinnedExactPlacedOk resStack A H := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  dsimp only [encodePolyDecoderPinnedExactVmSpecOf] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hx1, hx2, hpts58, hspare⟩, hmem⟩
  have hpreVac : s0.mem ⊨
      (encodePolyDecoderPinnedSpecOf resStack (rawVmRecordBudget A hblk s0) zeroEnforcedLimits).pre
        (x, ()) s0 ∗ R := by
    dsimp only [encodePolyDecoderPinnedSpecOf]
    rw [rawVmRecordBudget_pool_zeroEnforced,
      protoPolynomialDecoderPinnedAt_rawVmRecordBudget, vecU8At_rawVmRecordBudget]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hw0, hx1, hx2, hpts58, Or.inl hspare,
      fitsEnv_vecU8EncodeEnv_of_spare noAllocCostModel zeroEnforcedLimits () hspare⟩, ?_⟩
    have hmem' : s0.mem ⊨ ⌜VmPreserved s0 s0⌝ ∗
        (protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
          vecU8At A x.v x.cap x.ptr x.bs ∗
          stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨VmPreserved.refl s0, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem'
  have hencLen0 := ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (subroutine_ok_polyDecLenElemsOut_of_pinned
        (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x
          (rawVmRecordBudget A hblk s0).repAlloc H)))
  have hencVarVac := encodeVarint2_det_placed_ok_of_doReserve (resStack := resStack) (by omega)
    (rawVmRecordBudget A hblk s0) zeroEnforcedLimits H
    (vacuous_doReserve2_placed_ok (rawVmRecordBudget A hblk s0))
  have hencRepVac := encode_repeated_1_placed_ok_of_callees (resStack := resStack) (by omega)
    (A := rawVmRecordBudget A hblk s0) (lim := zeroEnforcedLimits)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) hencVarVac)
    (vacuous_doReserve2_placed_ok (rawVmRecordBudget A hblk s0)) hmemcpy
  obtain ⟨P, hP, hwp⟩ := polyDecoder1_core_placed_ok hres
    (rawVmRecordBudget A hblk s0) zeroEnforcedLimits hcl0
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hencLen0)
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
      (ls_subroutine_ok_of_block (callerProg := lsProg_455 H) hencVarVac))
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
      (ls_subroutine_ok_of_block (callerProg := lsProg_455 H) hencRepVac))
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
      (vacuous_doReserve2_placed_ok (rawVmRecordBudget A hblk s0)))
    hpc hrun hpreVac hsp
  refine ⟨P, R, hP, sepWPp_mono_post hwp ?_ (fun _ _ h => h.elim)⟩
  rintro sf P_f ⟨⟨cap', ptr', evs, htrf, _, hpres, hEnv, hmFn⟩, hspf, hccf⟩
  rcases hpres hspare with ⟨rfl, rfl⟩
  have hevs : evs = [] := encodePolyDecoderPinnedEnv_eq_nil_of_spare hspare hEnv
  subst hevs
  refine ⟨fun hmPf => ?_, hspf, hccf⟩
  have hmPost := hmFn R hmPf
  rw [rawVmRecordBudget_pool_zeroEnforced,
    protoPolynomialDecoderPinnedAt_rawVmRecordBudget, vecU8At_rawVmRecordBudget] at hmPost
  have hmPure : sf.mem ⊨ ⌜VmPreserved s0 sf⌝ ∗
      (protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
        vecU8At A x.v x.cap x.ptr (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
        stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmPost
  rw [satisfies_pure_sepConj] at hmPure
  rcases hmPure with ⟨hvm, hmRest⟩
  dsimp only [encodePolyDecoderPinnedExactVmSpecOf]
  simp only [sepConj_assoc]
  rw [satisfies_pure_sepConj]
  exact ⟨⟨hvm, htrf⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmRest⟩

theorem encode_polyDecoder_1_pinned_exact_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢
      ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    {H : String → Option (State → State)}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyDecoder1PinnedExactPlacedOk resStack A H :=
  polyDecoder1_exact_placed_ok_of_memcpy hres A hblk
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec from hmc))

theorem encode_polyDecoder_1_pinned_exact_placed_ok_of_vm [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢
      ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    {H : String → Option (State → State)}
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    EncodePolyDecoder1PinnedExactPlacedOk resStack A H :=
  polyDecoder1_exact_placed_ok_of_memcpy hres A hblk
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
      (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym allocMemcpyVmSpec from hmc)))

theorem encode_polyDecoder_1_pinned_exact_cli_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) (A : RustCliAlloc) {H : String → Option (State → State)}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyDecoder1PinnedExactPlacedOk resStack A.repAlloc H :=
  encode_polyDecoder_1_pinned_exact_placed_ok hres A.repAlloc A.block_valid hmc

theorem encode_polyDecoder_1_pinned_exact_cli_placed_ok_of_vm [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) (A : RustCliAlloc) {H : String → Option (State → State)}
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    EncodePolyDecoder1PinnedExactPlacedOk resStack A.repAlloc H :=
  encode_polyDecoder_1_pinned_exact_placed_ok_of_vm hres A.repAlloc A.block_valid hmc

/-! ## 4. Top-Level `2^60` Placed `subroutine_ok` Exports for Block `455` -/

theorem encode_polyDecoder_1_pinned_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpec A lim)) :=
  have hmc' : HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec := hmc
  encode_polyDecoder_1_pinned_placed_ok_of_callees (resStack := doReserveStack) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (subroutine_ok_polyDecLenElemsOut_of_pinned
          (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A.repAlloc H))))
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (encode_repeated_1_placed_ok_of_callees (resStack := doReserveStack) (by decide)
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
        (spqr_hook_ok_of_mem hmc')))
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc')

theorem encode_polyDecoder_1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderSpec A lim)) :=
  polyDecoder_unpinned_of_pinned_placed_x
    (encode_polyDecoder_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem encode_polyDecoder_1_pinned_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyDecoder1PinnedPlacedOkExtX A lim H :=
  have hmc' : HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec := hmc
  encode_polyDecoder_1_pinned_placed_ok_of_callees (resStack := doReserveStackX) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (subroutine_ok_polyDecLenElemsOut_of_pinned
          (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A.repAlloc H))))
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (encode_repeated_1_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
        (spqr_hook_ok_of_mem hmc')))
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc')

theorem encode_polyDecoder_1_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyDecoder1PlacedOkExtX A lim H :=
  polyDecoder_unpinned_of_pinned_placed_x
    (encode_polyDecoder_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

theorem encode_polyDecoder_1_pinned_placed_ok_of_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpec A lim)) :=
  have hmc' := subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym allocMemcpyVmSpec from hmc))
  encode_polyDecoder_1_pinned_placed_ok_of_callees (resStack := doReserveStack) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (subroutine_ok_polyDecLenElemsOut_of_pinned
          (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A.repAlloc H))))
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (encode_repeated_1_placed_ok_of_callees (resStack := doReserveStack) (by decide)
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
        hmc'))
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    hmc'

theorem encode_polyDecoder_1_placed_ok_of_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderSpec A lim)) :=
  polyDecoder_unpinned_of_pinned_placed_x
    (encode_polyDecoder_1_pinned_placed_ok_of_vm h_panic hshim halloc hrealloc hmc)

theorem encode_polyDecoder_1_pinned_placed_ok_x_of_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    EncodePolyDecoder1PinnedPlacedOkExtX A lim H :=
  have hmc' := subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym allocMemcpyVmSpec from hmc))
  encode_polyDecoder_1_pinned_placed_ok_of_callees (resStack := doReserveStackX) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (subroutine_ok_polyDecLenElemsOut_of_pinned
          (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A.repAlloc H))))
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (encode_repeated_1_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
        hmc'))
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    hmc'

theorem encode_polyDecoder_1_placed_ok_x_of_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    EncodePolyDecoder1PlacedOkExtX A lim H :=
  polyDecoder_unpinned_of_pinned_placed_x
    (encode_polyDecoder_1_pinned_placed_ok_x_of_vm h_panic hshim halloc hrealloc hmc)

theorem encode_polyDecoder_1_pinned_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyDecoder1PinnedPlacedOkExt A lim ext :=
  encode_polyDecoder_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc

theorem encode_polyDecoder_1_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyDecoder1PlacedOkExt A lim ext :=
  encode_polyDecoder_1_placed_ok h_panic hshim halloc hrealloc hmc

theorem encode_polyDecoder_1_pinned_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyDecoder1PinnedPlacedOkExtX A lim (Rust.withPanics ext) :=
  encode_polyDecoder_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc

theorem encode_polyDecoder_1_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyDecoder1PlacedOkExtX A lim (Rust.withPanics ext) :=
  encode_polyDecoder_1_placed_ok_x h_panic hshim halloc hrealloc hmc

/-! ## 5. Part 2 (`2^59` Exact Cap): `encodePolyDecoderExactSpecOf` & `etvPolyDecoderExactSpecOf` -/

theorem polyDecoder1_exact_gen_placed_ok [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} {B : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : EncodePolyDecoderPinnedGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok (lsProg_455 H) (blkPl_493).base
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec B.repAlloc)))
    (hencV : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (hencR : subroutine_ok (lsProg_455 H) (blkPl_448).base
      (withMsgEnc48CSPlaced s0 (encodeRepeated59ExactSpecOf resStack B lim)))
    (hpc : s0.pc = (blkPl_455).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyDecoderExactSpecOf resStack B lim).pre (x, st0) s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_455 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodePolyDecoderExactSpecOf resStack B lim).post (x, st0) s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodePolyDecoderExactSpecOf resStack B lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := spAligned_to_and15 hsp_align
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  have hpre_pure := hpre; dsimp only [encodePolyDecoderExactSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hw0, hx1, hx2, hfit⟩, hpre_mem⟩ := hpre_pure
  have hpre_rewritten : s0.mem ⊨ ((protoPolynomialDecoderPinnedAt B.repAlloc x.g x.decA x.dec ∗
      vecU8At B.repAlloc x.v x.cap x.ptr x.bs ∗ B.pool lim st0 s0 ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ emp) ∗ R := by
    convert hpre_mem using 1; sep_ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodePolyDecoderMsg_len_split x.tag x.dec
  have hlen_le_msg := polynomialDecoderPBEncodedLen_le_msg_len x.tag x.dec
  have hcap_lt : x.cap.toNat < 2 ^ 64 := BitVec.isLt x.cap
  have hlen_lt : polynomialDecoderPBEncodedLen x.dec < 2 ^ 64 := by omega
  refine step_pd1_hdr_exact_placed hres B lim H hencLen hencV x.tag x.decA x.v x.cap x.ptr s0.sp
    x.g x.dec x.bs st0 hlen_lt (by omega) (F := emp)
    rfl hpc hrun rfl halign rfl hw0 hx1 hx2 (MsgEnc48CalleeSavedPlaced.refl s0) rfl ?_
  intro s1 sv3 ptsElems hpts_eq hpts_lt hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1
  let bs_hdr := x.bs ++ polyDecoderHeaderBytes x.tag x.dec
  have hfit_pn : bs_hdr.length + (encodeUint32Field 1#32 x.dec.ptsNeeded).length ≤ x.cap.toNat := by
    dsimp [bs_hdr]; rw [List.length_append]; omega
  refine step_pd1_ptsNeeded_exact_placed hres128 B lim H hencV x.decA x.v x.cap x.ptr s0.sp x.g x.dec
    ptsElems bs_hdr st0 hfit_pn hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := polyDecoderRestAt B.repAlloc x.decA x.g ptsElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    (by dsimp [bs_hdr]; sep_ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
  let bs_pn := bs_hdr ++ encodeUint32Field 1#32 x.dec.ptsNeeded
  have hfit_pl : bs_pn.length + (encodeUint32Field 2#32 x.dec.polys).length ≤ x.cap.toNat := by
    dsimp [bs_pn, bs_hdr]; rw [List.length_append, List.length_append]; omega
  refine step_pd1_polys_exact_placed hres128 B lim H hencV x.decA x.v x.cap x.ptr s0.sp x.g x.dec
    ptsElems bs_pn st0 hfit_pl hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := polyDecoderRestAt B.repAlloc x.decA x.g ptsElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    rfl ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
  let bs_pl := bs_pn ++ encodeUint32Field 2#32 x.dec.polys
  have hfit_rest : bs_pl.length + (encodeRepeatedBytes 3 x.dec.pts).length +
      (encodeBoolField 4#32 x.dec.isComplete).length ≤ x.cap.toNat := by
    dsimp [bs_pl, bs_pn, bs_hdr]
    rw [List.length_append, List.length_append, List.length_append]; omega
  refine step_pd1_pts_isComplete_exact_placed hres B lim H hencR x.decA x.v x.cap x.ptr s0.sp sv3
    x.g x.dec ptsElems bs_pl st0 hpts_eq (by omega) hfit_rest
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3
    (F := polyDecoderRestAt B.repAlloc x.decA x.g ptsElems ∗ emp)
    (by dsimp [bs_pl]; sep_ac_rfl) ?_
  intro sf _ _ hspf htrf hccf _
  refine ⟨fun hm => ?_, hspf, hccf⟩
  have hm_pack : sf.mem ⊨ (polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
      polyDecoderRestAt B.repAlloc x.decA x.g ptsElems) ∗
      (vecU8At B.repAlloc x.v x.cap x.ptr (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
        B.pool lim st0 sf ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [bs0_append_encodePolyDecoderMsg x.bs x.tag x.dec]
    convert hm using 1; dsimp [bs_pl, bs_pn, bs_hdr]; sep_ac_rfl
  have hm_pinned := (satisfies_protoPolynomialDecoderPinnedAt_iff B.repAlloc x.g x.decA x.dec _ sf.mem).mpr
    ⟨ptsElems, hpts_eq, hpts_lt, hm_pack⟩
  dsimp only [encodePolyDecoderExactSpecOf]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  convert hm_pinned using 1; sep_ac_rfl

private theorem encode_polyDecoder_1_exact_vm_pinned_placed_ok_of_memcpy_and_resStack
    [LibsignalPlacement] {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf resStack A.repAlloc)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  let B := vmTrackBudget A s0
  have hpreB : s0.mem ⊨
      (encodePolyDecoderExactSpecOf resStack B impossibleEnforcedLimits).pre (x, M.init) s0 ∗ R := by
    dsimp only [encodePolyDecoderExactVmSpecOf] at hpre
    dsimp only [encodePolyDecoderExactSpecOf, B, vmTrackBudget, impossibleEnforcedLimits,
      RustCliAllocBudget.repAlloc]
    simp only [↓reduceIte]
    have hpre1 : s0.mem ⊨ ⌜VmPreserved s0 s0⌝ ∗
        ((⌜s0.readReg32 .x0 = x.tag ∧ s0.readReg64 .x1 = x.decA ∧ s0.readReg64 .x2 = x.v ∧
            x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat⌝ ∗
          protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
          vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
          stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ R) := by
      rw [satisfies_pure_sepConj]; exact ⟨VmPreserved.refl s0, hpre⟩
    convert hpre1 using 1; sep_ac_rfl
  have hencLen := subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (subroutine_ok_polyDecLenElemsOut_of_pinned
          (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x B.repAlloc H))))
  have hencV := subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H)
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
    (ls_subroutine_ok_of_block (callerProg := lsProg_455 H) hencR59)
  obtain ⟨P, hP, hwp⟩ := polyDecoder1_exact_gen_placed_ok hres (B := B)
    (lim := impossibleEnforcedLimits) hencLen hencV hencR hpc hrun hpreB hsp
  refine ⟨P, R, hP, sepWPp_mono ?_ ?_ hwp⟩
  · intro sf Q ⟨hq, hspf, hccf⟩
    refine ⟨fun hm => ?_, hspf, hccf⟩
    have hpost := hq hm
    dsimp only [encodePolyDecoderExactSpecOf, B, vmTrackBudget, impossibleEnforcedLimits,
      RustCliAllocBudget.repAlloc] at hpost
    simp only [↓reduceIte] at hpost
    have hpost1 : sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
        (⌜VmPreserved s0 sf⌝ ∗
          (protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
            vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
            stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R)) := by
      convert hpost using 1; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost1
    obtain ⟨htrf, hvmp, hrest⟩ := hpost1
    dsimp only [encodePolyDecoderExactVmSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hvmp, htrf⟩, by convert hrest using 1; sep_ac_rfl⟩
  · intro sf P_f hpan hm
    exact hpan hm

theorem encode_polyDecoder_1_exact_vm_pinned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf doReserveStack A.repAlloc)) :=
  encode_polyDecoder_1_exact_vm_pinned_placed_ok_of_memcpy_and_resStack (by decide)
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec from hmc))

theorem encode_polyDecoder_1_exact_vm_pinned_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf doReserveStackX A.repAlloc)) :=
  encode_polyDecoder_1_exact_vm_pinned_placed_ok_of_memcpy_and_resStack (by decide)
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec from hmc))

theorem encode_polyDecoder_1_exact_vm_pinned_placed_ok_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf doReserveStack A.repAlloc)) :=
  encode_polyDecoder_1_exact_vm_pinned_placed_ok_of_memcpy_and_resStack (by decide)
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
      (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym allocMemcpyVmSpec from hmc)))

theorem encode_polyDecoder_1_exact_vm_pinned_placed_ok_x_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf doReserveStackX A.repAlloc)) :=
  encode_polyDecoder_1_exact_vm_pinned_placed_ok_of_memcpy_and_resStack (by decide)
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
      (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym allocMemcpyVmSpec from hmc)))

theorem encode_polyDecoder_1_exact_pinned_placed_ok_of_memcpy [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStack A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodePolyDecoderExact_of_vm
    (encode_polyDecoder_1_exact_vm_pinned_placed_ok hmc)

theorem encode_polyDecoder_1_exact_pinned_placed_ok_of_memcpy_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStackX A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodePolyDecoderExact_of_vm
    (encode_polyDecoder_1_exact_vm_pinned_placed_ok_x hmc)

theorem encode_polyDecoder_1_exact_pinned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStack A lim)) :=
  encode_polyDecoder_1_exact_pinned_placed_ok_of_memcpy hmc

theorem encode_polyDecoder_1_exact_pinned_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStackX A lim)) :=
  encode_polyDecoder_1_exact_pinned_placed_ok_of_memcpy_x hmc

theorem encode_polyDecoder_1_exact_pinned_placed_ok_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStack A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodePolyDecoderExact_of_vm
    (encode_polyDecoder_1_exact_vm_pinned_placed_ok_of_vm hmc)

theorem encode_polyDecoder_1_exact_pinned_placed_ok_x_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStackX A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodePolyDecoderExact_of_vm
    (encode_polyDecoder_1_exact_vm_pinned_placed_ok_x_of_vm hmc)

theorem etv_polyDecoderEncode_1_exact_vm_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStack A.repAlloc)) :=
  etv_polyDecoderEncode_exact_of_lscl
    (encode_polyDecoder_1_exact_vm_pinned_placed_ok hmc)

theorem etv_polyDecoderEncode_1_exact_vm_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStackX A.repAlloc)) :=
  etv_polyDecoderEncode_exact_of_lscl
    (encode_polyDecoder_1_exact_vm_pinned_placed_ok_x hmc)

theorem etv_polyDecoderEncode_1_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStack A.repAlloc)) :=
  etv_polyDecoderEncode_1_exact_vm_placed_ok hmc

theorem etv_polyDecoderEncode_1_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStackX A.repAlloc)) :=
  etv_polyDecoderEncode_1_exact_vm_placed_ok_x hmc

theorem etv_polyDecoderEncode_1_exact_placed_ok_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStack A.repAlloc)) :=
  etv_polyDecoderEncode_exact_of_lscl
    (encode_polyDecoder_1_exact_vm_pinned_placed_ok_of_vm hmc)

theorem etv_polyDecoderEncode_1_exact_placed_ok_x_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStackX A.repAlloc)) :=
  etv_polyDecoderEncode_exact_of_lscl
    (encode_polyDecoder_1_exact_vm_pinned_placed_ok_x_of_vm hmc)

abbrev etv_polyDecoderEncode_exact_placed_ok := @etv_polyDecoderEncode_1_exact_placed_ok
abbrev etv_polyDecoderEncode_exact_placed_ok_x := @etv_polyDecoderEncode_1_exact_placed_ok_x

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1PlacedBudget
