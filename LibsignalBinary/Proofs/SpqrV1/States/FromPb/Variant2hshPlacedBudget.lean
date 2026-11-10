/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hshPlaced
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsaPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsg
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsh

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 2 (`HeaderSent`) — Part H

Relocatable Block-`333` `<PolyEncoder>::from_pb` (`+9096`) and `<PolyDecoder>::from_pb`
(`+9384`) call helpers and `FreeOnlyEvs` `+9100` encoder-error branch under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hshPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsProg_333 lsmpl sepWP_seq_lscl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialError ProtoAuthenticator ProtoPolynomialDecoder ProtoPolynomialEncoder)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderSize polyEncoderSize protoPolynomialDecoderAt protoPolynomialDecoderSize
   protoPolynomialEncoderAt protoPolynomialEncoderSize resultPolyDecoderFromPbAt
   resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (EncoderFromPbGhost encoderFromPbStack fromPbResult)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved decoderFromPbResult decoderFromPbStack resultChunkedStatesAt sp_sub_2400_align
   spqrErrorByte statesFromPbSavedCells statesFromPbStack v1_bv_add_add_lit v1_bv_sub_sub_lit
   v1_optProtoPolyEncoderWordsAt v2hs_ekSentWordsAt v2hs_optProtoDecoderHeap
   v2hs_optProtoDecoderWordsAt v2hs_stack896ScratchRest v2hsc_optProtoPolyDecoderHeap
   v2hsc_optProtoPolyDecoderWordsAt v2hse_unchunkedEkSentWordsAt v2hsh_bv_add_add_lit
   v2hsh_collapse_2304_from_9228 v2hsh_memRegion_1344_960_collapse
   v2hstop_optProtoDecoderHeap_eq_v2hsc v2hstop_optProtoDecoderWordsAt_eq_v2hsc
   v2hstop_vecU8Heap_entails_dealloc v4b_vecU8Heap)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget seq_clean_evs_lscl seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsaPlacedBudget
  (v2hs_err_cleanup_9228_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudget
  (v2hsc_cleanup_9212_to_9228_of_dealloc_placed v2hsc_cleanup_9212_to_9228_of_placedHooks
   v2hsc_cleanup_9212_to_9228_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlacedBudget
  (v2hsd_sub_ok_decoder_from_pb_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2PlacedBudget
  (v2hse2_bl_encoder_9096_to_32996_placed_budget v2hse2_enc_err_9100_to_9212_of_dealloc_placed
   v2hse2_enc_err_9100_to_9212_of_placedHooks v2hse2_enc_err_9100_to_9212_placed
   v2hse2_sub_ok_encoder_from_pb_of_alloc_placed v2hse2_sub_ok_encoder_from_pb_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3PlacedBudget
  (v2hse3_bl_decoder_9384_to_35448_placed_budget)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit v2hsh_bv_add_add_lit

private theorem v2hsh_sepWPp_bind_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Q_mid Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P Q_mid Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm Pm →
      SepWPp prog target sm Pm Q Qp) :
    SepWPp prog target s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ := h1 R hm hL
  rcases hout with ⟨hpcm, hrunm, Pm, hpm, hQm⟩ | hpan | hoom
  · have hcl_m : LibsignalCodeLoaded lsmpl sm.mem :=
      LibsignalCodeLoaded.of_keepsFrozen hcl hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ := h2 sm Pm hpcm hrunm hcl_m hQm R hpm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## `<PolyEncoder>::from_pb` Call Helpers at `+9096` -/

/-- Direct `SepWP` step for `<PolyEncoder>::from_pb` at `+9096 -> +9100` (Block `333 -> 374 -> 333`)
    under `EncoderFromPbAllocEnv` / `EncoderFromPbEnv`. -/
theorem v2hsh_encoder_step_9096_to_9100_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ)
    (s0 s : State) (fsp out d0 pa1 ca3 pbA epoch : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_len : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv pbEnc))
    (hpc : s.pc = lsmpl.base 333 + 9096#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64)
    (hx1 : s.readReg64 .x1 = fsp + 1792#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = d0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = epoch)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9100#64) s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 1792#64) pbEnc ∗
        A.pool lim st s ∗
        Rest)
      (fun s1 P1 =>
        ∃ evs : List AllocEvent,
          EncoderFromPbEnv pbEnc evs ∧
          (P1 ⊢
            stackAt fsp encoderFromPbStack ∗
            resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (fromPbResult pbEnc) ∗
            memRegion (fsp + 1792#64) protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) s1 ∗
            Rest) ∧
          s1.sp = fsp ∧
          s1.readReg64 .x19 = out ∧
          s1.readReg64 .x21 = fsp + 1392#64 ∧
          s1.readReg64 .x22 = d0 ∧
          s1.readReg64 .x23 = pa1 ∧
          s1.readReg64 .x24 = fsp + 1888#64 ∧
          s1.readReg64 .x25 = fsp + 1792#64 ∧
          s1.readReg64 .x26 = ca3 ∧
          s1.readReg64 .x27 = pbA ∧
          s1.readReg64 .x28 = epoch ∧
          TraceCalleeSaved s1 s0) := by
  have hsub := v2hse2_sub_ok_encoder_from_pb_placed henc
  refine seq_clean_lscl_st hcl
    (P_mid := fun sm =>
      (memRegion (fsp + 1888#64) polyEncoderSize ∗
       protoPolynomialEncoderAt A.repAlloc (fsp + 1792#64) pbEnc ∗
       stackAt fsp encoderFromPbStack ∗ Rest) ∗ A.pool lim st sm)
    (Q := fun sm =>
      VmPreserved s sm ∧
      sm.sp = fsp ∧
      sm.readReg64 .x0 = fsp + 1888#64 ∧
      sm.readReg64 .x1 = fsp + 1792#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = s.readReg64 .x21 ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x23 = s.readReg64 .x23 ∧
      sm.readReg64 .x24 = fsp + 1888#64 ∧
      sm.readReg64 .x25 = fsp + 1792#64 ∧
      sm.readReg64 .x26 = ca3 ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = s.readReg64 .x28 ∧
      sm.readReg64 .x30 = lsmpl.base 333 + 9100#64 ∧
      TraceCalleeSaved sm s0)
    (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (v2hse2_bl_encoder_9096_to_32996_placed_budget A lim st (ext := ext)
        s0 s fsp out d0 ca3 pbA
        (memRegion (fsp + 1888#64) polyEncoderSize ∗
         protoPolynomialEncoderAt A.repAlloc (fsp + 1792#64) pbEnc ∗
         stackAt fsp encoderFromPbStack ∗ Rest)
        hpc hrun hsp hx0 hx1 hx19 hx22 hx24 hx25 hx26 hx27 htr)) ?_
  intro sm hpc_m hrun_m hcl_m
    ⟨_hvm_m, hsp_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m,
     hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hlr_m, htr_m⟩
  rw [hx21] at hx21_m; rw [hx23] at hx23_m; rw [hx28] at hx28_m
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      (memRegion (fsp + 1888#64) polyEncoderSize ∗
       protoPolynomialEncoderAt A.repAlloc (fsp + 1792#64) pbEnc ∗
       A.pool lim st sm ∗ stackAt fsp encoderFromPbStack) ∗ Rest by ac_rfl)) ?_
  have hsp_align_m : sm.spAligned = true := by
    unfold State.spAligned
    rw [hsp_m]
    exact hfsp_align
  have hpre_ent :
      (memRegion (fsp + 1888#64) polyEncoderSize ∗
       protoPolynomialEncoderAt A.repAlloc (fsp + 1792#64) pbEnc ∗
       A.pool lim st sm ∗ stackAt fsp encoderFromPbStack) ⊢
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)).pre
        (EncoderFromPbGhost.mk (fsp + 1888#64) (fsp + 1792#64) pbEnc, st) sm := by
    dsimp only [withLsCodeLoaded, encoderFromPbSpec]
    rw [hsp_m, sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl sm.mem⌝, ← sepConj_assoc]
    exact Entails.pure_right hcl_m
      (Entails.pure_right ⟨hx0_m, hx1_m, hpts_len, hfits,
        by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (sm.readReg64 .x30); rw [show sm.readReg64 .x30 = _ from hlr_m]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩ (Entails.refl _))
  refine SepWP.call_subroutine_frame hsub
    (x := (EncoderFromPbGhost.mk (fsp + 1888#64) (fsp + 1792#64) pbEnc, st))
    (F := Rest)
    hpc_m hrun_m hsp_align_m hlr_m
    (fun R' hm => by
      rw [sepConj_assoc] at hm
      exact Satisfies.mono (sepConj_mono_left hpre_ent) hm)
    (fun _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    ?_
    (fun _ _ _ hm => False.elim (not_satisfies_false_sepConj hm))
  intro s1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with
    ⟨hx19_f, _, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, _, hvregs_f⟩
  dsimp only [withLsCodeLoaded, encoderFromPbSpec]
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_elim; intro evs
  rw [sepConj_assoc]
  apply ProofLib.SepWP.pure_elim; rintro ⟨htr_f, _hacp_f, henv⟩
  apply ProofLib.SepWP.done hpc1 hrun1
  refine ⟨evs, henv, ?_,
    by rw [hsp1, hsp_m],
    by rw [hx19_f, hx19_m],
    by rw [hx21_f, hx21_m],
    by rw [hx22_f, hx22_m],
    by rw [hx23_f, hx23_m],
    by rw [hx24_f, hx24_m],
    by rw [hx25_f, hx25_m],
    by rw [hx26_f, hx26_m],
    by rw [hx27_f, hx27_m],
    by rw [hx28_f, hx28_m],
    ⟨htr_f.trans htr_m.1, hvregs_f.trans htr_m.2⟩⟩
  rw [hsp_m]
  exact Entails.of_eq (by ac_rfl)

theorem v2hsh_encoder_step_9096_to_9100_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ)
    (s0 s : State) (fsp out d0 pa1 ca3 pbA epoch : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_len : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv pbEnc))
    (hpc : s.pc = lsmpl.base 333 + 9096#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64)
    (hx1 : s.readReg64 .x1 = fsp + 1792#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = d0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = epoch)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9100#64) s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 1792#64) pbEnc ∗
        A.pool lim st s ∗
        Rest)
      (fun s1 P1 =>
        ∃ evs : List AllocEvent,
          EncoderFromPbEnv pbEnc evs ∧
          (P1 ⊢
            stackAt fsp encoderFromPbStack ∗
            resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (fromPbResult pbEnc) ∗
            memRegion (fsp + 1792#64) protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) s1 ∗
            Rest) ∧
          s1.sp = fsp ∧
          s1.readReg64 .x19 = out ∧
          s1.readReg64 .x21 = fsp + 1392#64 ∧
          s1.readReg64 .x22 = d0 ∧
          s1.readReg64 .x23 = pa1 ∧
          s1.readReg64 .x24 = fsp + 1888#64 ∧
          s1.readReg64 .x25 = fsp + 1792#64 ∧
          s1.readReg64 .x26 = ca3 ∧
          s1.readReg64 .x27 = pbA ∧
          s1.readReg64 .x28 = epoch ∧
          TraceCalleeSaved s1 s0) :=
  v2hsh_encoder_step_9096_to_9100_placed
    (v2hse2_sub_ok_encoder_from_pb_of_alloc_placed hA)
    st s0 s fsp out d0 pa1 ca3 pbA epoch pbEnc Rest
    hcl hfsp_align hpts_len hfits
    hpc hrun hsp hx0 hx1 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 htr

/-- CPS `SepWP` call helper for `<PolyEncoder>::from_pb` at `+9096 -> +9100 -> target_pc`. -/
theorem v2hsh_encoder_call_9096_sepWP_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ)
    (s0 s : State) (target_pc fsp out d0 pa1 ca3 pbA epoch : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (Rest : SepProp)
    (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_len : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv pbEnc))
    (hpc : s.pc = lsmpl.base 333 + 9096#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64)
    (hx1 : s.readReg64 .x1 = fsp + 1792#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = d0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = epoch)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (evs : List AllocEvent) (s1 : State),
      EncoderFromPbEnv pbEnc evs →
      s1.pc = lsmpl.base 333 + 9100#64 →
      s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s1.sp = fsp ∧
       s1.readReg64 .x19 = out ∧
       s1.readReg64 .x21 = fsp + 1392#64 ∧
       s1.readReg64 .x22 = d0 ∧
       s1.readReg64 .x23 = pa1 ∧
       s1.readReg64 .x24 = fsp + 1888#64 ∧
       s1.readReg64 .x25 = fsp + 1792#64 ∧
       s1.readReg64 .x26 = ca3 ∧
       s1.readReg64 .x27 = pbA ∧
       s1.readReg64 .x28 = epoch ∧
       TraceCalleeSaved s1 s0) →
      SepWP (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (fromPbResult pbEnc) ∗
         memRegion (fsp + 1792#64) protoPolynomialEncoderSize ∗
         A.pool lim (M.stepEvents evs st) s1 ∗
         Rest)
        post) :
    SepWP (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 1792#64) pbEnc ∗
        A.pool lim st s ∗
        Rest)
      post :=
  sepWP_seq_lscl hcl
    (SepWP.mono
      (v2hsh_encoder_step_9096_to_9100_placed henc st s0 s fsp out d0 pa1 ca3 pbA epoch
        pbEnc Rest hcl hfsp_align hpts_len hfits
        hpc hrun hsp hx0 hx1 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 htr)
      fun s1 _P1 hpc1 hrun1 ⟨evs, henv, hP1, hregs⟩ hcl1 =>
        SepWP.weaken_pre hP1 (hnext evs s1 henv hpc1 hrun1 hcl1 hregs))

theorem v2hsh_encoder_call_9096_sepWP_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ)
    (s0 s : State) (target_pc fsp out d0 pa1 ca3 pbA epoch : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (Rest : SepProp)
    (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_len : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv pbEnc))
    (hpc : s.pc = lsmpl.base 333 + 9096#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64)
    (hx1 : s.readReg64 .x1 = fsp + 1792#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = d0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = epoch)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (evs : List AllocEvent) (s1 : State),
      EncoderFromPbEnv pbEnc evs →
      s1.pc = lsmpl.base 333 + 9100#64 →
      s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s1.sp = fsp ∧
       s1.readReg64 .x19 = out ∧
       s1.readReg64 .x21 = fsp + 1392#64 ∧
       s1.readReg64 .x22 = d0 ∧
       s1.readReg64 .x23 = pa1 ∧
       s1.readReg64 .x24 = fsp + 1888#64 ∧
       s1.readReg64 .x25 = fsp + 1792#64 ∧
       s1.readReg64 .x26 = ca3 ∧
       s1.readReg64 .x27 = pbA ∧
       s1.readReg64 .x28 = epoch ∧
       TraceCalleeSaved s1 s0) →
      SepWP (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (fromPbResult pbEnc) ∗
         memRegion (fsp + 1792#64) protoPolynomialEncoderSize ∗
         A.pool lim (M.stepEvents evs st) s1 ∗
         Rest)
        post) :
    SepWP (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 1792#64) pbEnc ∗
        A.pool lim st s ∗
        Rest)
      post :=
  v2hsh_encoder_call_9096_sepWP_placed
    (v2hse2_sub_ok_encoder_from_pb_of_alloc_placed hA)
    st s0 s target_pc fsp out d0 pa1 ca3 pbA epoch pbEnc Rest post
    hcl hfsp_align hpts_len hfits
    hpc hrun hsp hx0 hx1 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 htr hnext

/-- CPS `SepWPp` call helper for `<PolyEncoder>::from_pb` at `+9096 -> +9100 -> target_pc` (polymorphic in `Qp`). -/
theorem v2hsh_encoder_call_9096_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ)
    (s0 s : State) (target_pc fsp out d0 pa1 ca3 pbA epoch : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (Rest : SepProp)
    (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_len : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv pbEnc))
    (hpc : s.pc = lsmpl.base 333 + 9096#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64)
    (hx1 : s.readReg64 .x1 = fsp + 1792#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = d0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = epoch)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (evs : List AllocEvent) (s1 : State),
      EncoderFromPbEnv pbEnc evs →
      s1.pc = lsmpl.base 333 + 9100#64 →
      s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s1.sp = fsp ∧
       s1.readReg64 .x19 = out ∧
       s1.readReg64 .x21 = fsp + 1392#64 ∧
       s1.readReg64 .x22 = d0 ∧
       s1.readReg64 .x23 = pa1 ∧
       s1.readReg64 .x24 = fsp + 1888#64 ∧
       s1.readReg64 .x25 = fsp + 1792#64 ∧
       s1.readReg64 .x26 = ca3 ∧
       s1.readReg64 .x27 = pbA ∧
       s1.readReg64 .x28 = epoch ∧
       TraceCalleeSaved s1 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (fromPbResult pbEnc) ∗
         memRegion (fsp + 1792#64) protoPolynomialEncoderSize ∗
         A.pool lim (M.stepEvents evs st) s1 ∗
         Rest)
        post Qp) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 1792#64) pbEnc ∗
        A.pool lim st s ∗
        Rest)
      post Qp :=
  v2hsh_sepWPp_bind_lscl hcl
    (SepWPp.of_sepWP_ret
      (v2hsh_encoder_step_9096_to_9100_placed henc st s0 s fsp out d0 pa1 ca3 pbA epoch
        pbEnc Rest hcl hfsp_align hpts_len hfits
        hpc hrun hsp hx0 hx1 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 htr))
    fun s1 _P1 hpc1 hrun1 hcl1 ⟨evs, henv, hP1, hregs⟩ =>
      SepWPp.weaken_pre hP1 (hnext evs s1 henv hpc1 hrun1 hcl1 hregs)

theorem v2hsh_encoder_call_9096_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ)
    (s0 s : State) (target_pc fsp out d0 pa1 ca3 pbA epoch : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (Rest : SepProp)
    (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_len : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv pbEnc))
    (hpc : s.pc = lsmpl.base 333 + 9096#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64)
    (hx1 : s.readReg64 .x1 = fsp + 1792#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = d0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = epoch)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (evs : List AllocEvent) (s1 : State),
      EncoderFromPbEnv pbEnc evs →
      s1.pc = lsmpl.base 333 + 9100#64 →
      s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s1.sp = fsp ∧
       s1.readReg64 .x19 = out ∧
       s1.readReg64 .x21 = fsp + 1392#64 ∧
       s1.readReg64 .x22 = d0 ∧
       s1.readReg64 .x23 = pa1 ∧
       s1.readReg64 .x24 = fsp + 1888#64 ∧
       s1.readReg64 .x25 = fsp + 1792#64 ∧
       s1.readReg64 .x26 = ca3 ∧
       s1.readReg64 .x27 = pbA ∧
       s1.readReg64 .x28 = epoch ∧
       TraceCalleeSaved s1 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (fromPbResult pbEnc) ∗
         memRegion (fsp + 1792#64) protoPolynomialEncoderSize ∗
         A.pool lim (M.stepEvents evs st) s1 ∗
         Rest)
        post Qp) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 1792#64) pbEnc ∗
        A.pool lim st s ∗
        Rest)
      post Qp :=
  v2hsh_encoder_call_9096_placed
    (v2hse2_sub_ok_encoder_from_pb_of_alloc_placed hA)
    st s0 s target_pc fsp out d0 pa1 ca3 pbA epoch pbEnc Rest post
    hcl hfsp_align hpts_len hfits
    hpc hrun hsp hx0 hx1 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 htr hnext

/-! ## `<PolyDecoder>::from_pb` Call Helpers at `+9384` -/

/-- Direct `SepWP` step for `<PolyDecoder>::from_pb` at `+9384 -> +9388` (Block `333 -> 376 -> 333`)
    under `FromPbDecAllocEnv` / `FromPbDecEnv`. -/
theorem v2hsh_decoder_step_9384_to_9388_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ)
    (s0 s : State) (fsp out x20_val x21_val ca3 x28_val : BitVec 64)
    (pbDec : ProtoPolynomialDecoder) (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hfits : FitsEnv M lim st (FromPbDecAllocEnv pbDec))
    (hpc : s.pc = lsmpl.base 333 + 9384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64)
    (hx1 : s.readReg64 .x1 = fsp + 1848#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = x21_val)
    (hx22 : s.readReg64 .x22 = fsp + 1888#64)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = x28_val)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9388#64) s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyDecoderSize ∗
        protoPolynomialDecoderAt A.repAlloc (fsp + 1848#64) pbDec ∗
        A.pool lim st s ∗
        Rest)
      (fun s1 P1 =>
        ∃ evs : List AllocEvent,
          FromPbDecEnv pbDec evs ∧
          (P1 ⊢
            stackAt fsp encoderFromPbStack ∗
            resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (decoderFromPbResult pbDec) ∗
            memRegion (fsp + 1848#64) protoPolynomialDecoderSize ∗
            A.pool lim (M.stepEvents evs st) s1 ∗
            Rest) ∧
          s1.sp = fsp ∧
          s1.readReg64 .x19 = out ∧
          s1.readReg64 .x20 = x20_val ∧
          s1.readReg64 .x21 = x21_val ∧
          s1.readReg64 .x22 = fsp + 1888#64 ∧
          s1.readReg64 .x23 = fsp + 848#64 ∧
          s1.readReg64 .x25 = fsp + 1792#64 ∧
          s1.readReg64 .x26 = ca3 ∧
          s1.readReg64 .x28 = x28_val ∧
          TraceCalleeSaved s1 s0) := by
  have hsub := v2hsd_sub_ok_decoder_from_pb_placed hdec
  refine seq_clean_lscl_st hcl
    (P_mid := fun sm =>
      (memRegion (fsp + 1888#64) polyDecoderSize ∗
       protoPolynomialDecoderAt A.repAlloc (fsp + 1848#64) pbDec ∗
       stackAt fsp encoderFromPbStack ∗ Rest) ∗ A.pool lim st sm)
    (Q := fun sm =>
      VmPreserved s sm ∧
      sm.sp = fsp ∧
      sm.readReg64 .x0 = fsp + 1888#64 ∧
      sm.readReg64 .x1 = fsp + 1848#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = x20_val ∧
      sm.readReg64 .x21 = x21_val ∧
      sm.readReg64 .x22 = fsp + 1888#64 ∧
      sm.readReg64 .x23 = fsp + 848#64 ∧
      sm.readReg64 .x25 = fsp + 1792#64 ∧
      sm.readReg64 .x26 = ca3 ∧
      sm.readReg64 .x28 = x28_val ∧
      sm.readReg64 .x30 = lsmpl.base 333 + 9388#64 ∧
      TraceCalleeSaved sm s0)
    (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (v2hse3_bl_decoder_9384_to_35448_placed_budget A lim st (ext := ext)
        s0 s fsp out x20_val x21_val ca3 x28_val
        (memRegion (fsp + 1888#64) polyDecoderSize ∗
         protoPolynomialDecoderAt A.repAlloc (fsp + 1848#64) pbDec ∗
         stackAt fsp encoderFromPbStack ∗ Rest)
        hpc hrun hsp hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx25 hx26 hx28 htr)) ?_
  intro sm hpc_m hrun_m hcl_m
    ⟨_hvm_m, hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx22_m,
     hx23_m, hx25_m, hx26_m, hx28_m, hlr_m, htr_m⟩
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      (memRegion (fsp + 1888#64) polyDecoderSize ∗
       protoPolynomialDecoderAt A.repAlloc (fsp + 1848#64) pbDec ∗
       A.pool lim st sm ∗ stackAt fsp encoderFromPbStack) ∗ Rest by ac_rfl)) ?_
  have hsp_align_m : sm.spAligned = true := by
    unfold State.spAligned
    rw [hsp_m]
    exact hfsp_align
  have hpre_ent :
      (memRegion (fsp + 1888#64) polyDecoderSize ∗
       protoPolynomialDecoderAt A.repAlloc (fsp + 1848#64) pbDec ∗
       A.pool lim st sm ∗ stackAt fsp encoderFromPbStack) ⊢
      (withLsCodeLoaded lsmpl (DefsBudget.decoderFromPbSpec M A lim)).pre
        (⟨fsp + 1888#64, fsp + 1848#64, pbDec⟩, st) sm := by
    dsimp only [withLsCodeLoaded, DefsBudget.decoderFromPbSpec, decoderFromPbStack]
    rw [hsp_m, sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl sm.mem⌝, ← sepConj_assoc]
    exact Entails.pure_right hcl_m
      (Entails.pure_right ⟨hx0_m, hx1_m, hfits,
        by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (sm.readReg64 .x30); rw [show sm.readReg64 .x30 = _ from hlr_m]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩ (Entails.refl _))
  refine SepWP.call_subroutine_frame hsub
    (x := (⟨fsp + 1888#64, fsp + 1848#64, pbDec⟩, st))
    (F := Rest)
    hpc_m hrun_m hsp_align_m hlr_m
    (fun R' hm => by
      rw [sepConj_assoc] at hm
      exact Satisfies.mono (sepConj_mono_left hpre_ent) hm)
    (fun _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    ?_
    (fun _ _ _ hm => False.elim (not_satisfies_false_sepConj hm))
  intro s1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, _, hx25_f, hx26_f, _, hx28_f, _, hvregs_f⟩
  dsimp only [withLsCodeLoaded, DefsBudget.decoderFromPbSpec, decoderFromPbStack]
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_elim; intro evs
  rw [sepConj_assoc]
  apply ProofLib.SepWP.pure_elim; rintro ⟨htr_f, _hacp_f, henv⟩
  apply ProofLib.SepWP.done hpc1 hrun1
  refine ⟨evs, henv, ?_,
    by rw [hsp1, hsp_m],
    by rw [hx19_f, hx19_m],
    by rw [hx20_f, hx20_m],
    by rw [hx21_f, hx21_m],
    by rw [hx22_f, hx22_m],
    by rw [hx23_f, hx23_m],
    by rw [hx25_f, hx25_m],
    by rw [hx26_f, hx26_m],
    by rw [hx28_f, hx28_m],
    ⟨htr_f.trans htr_m.1, hvregs_f.trans htr_m.2⟩⟩
  rw [hsp_m]
  exact Entails.of_eq (by ac_rfl)

/-- CPS `SepWP` call helper for `<PolyDecoder>::from_pb` at `+9384 -> +9388 -> target_pc`. -/
theorem v2hsh_decoder_call_9384_sepWP_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ)
    (s0 s : State) (target_pc fsp out x20_val x21_val ca3 x28_val : BitVec 64)
    (pbDec : ProtoPolynomialDecoder) (Rest : SepProp)
    (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hfits : FitsEnv M lim st (FromPbDecAllocEnv pbDec))
    (hpc : s.pc = lsmpl.base 333 + 9384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64)
    (hx1 : s.readReg64 .x1 = fsp + 1848#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = x21_val)
    (hx22 : s.readReg64 .x22 = fsp + 1888#64)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = x28_val)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (evs : List AllocEvent) (s1 : State),
      FromPbDecEnv pbDec evs →
      s1.pc = lsmpl.base 333 + 9388#64 →
      s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s1.sp = fsp ∧
       s1.readReg64 .x19 = out ∧
       s1.readReg64 .x20 = x20_val ∧
       s1.readReg64 .x21 = x21_val ∧
       s1.readReg64 .x22 = fsp + 1888#64 ∧
       s1.readReg64 .x23 = fsp + 848#64 ∧
       s1.readReg64 .x25 = fsp + 1792#64 ∧
       s1.readReg64 .x26 = ca3 ∧
       s1.readReg64 .x28 = x28_val ∧
       TraceCalleeSaved s1 s0) →
      SepWP (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (decoderFromPbResult pbDec) ∗
         memRegion (fsp + 1848#64) protoPolynomialDecoderSize ∗
         A.pool lim (M.stepEvents evs st) s1 ∗
         Rest)
        post) :
    SepWP (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyDecoderSize ∗
        protoPolynomialDecoderAt A.repAlloc (fsp + 1848#64) pbDec ∗
        A.pool lim st s ∗
        Rest)
      post :=
  sepWP_seq_lscl hcl
    (SepWP.mono
      (v2hsh_decoder_step_9384_to_9388_placed hdec st s0 s fsp out x20_val x21_val ca3 x28_val
        pbDec Rest hcl hfsp_align hfits
        hpc hrun hsp hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx25 hx26 hx28 htr)
      fun s1 _P1 hpc1 hrun1 ⟨evs, henv, hP1, hregs⟩ hcl1 =>
        SepWP.weaken_pre hP1 (hnext evs s1 henv hpc1 hrun1 hcl1 hregs))

/-- CPS `SepWPp` call helper for `<PolyDecoder>::from_pb` at `+9384 -> +9388 -> target_pc` (polymorphic in `Qp`). -/
theorem v2hsh_decoder_call_9384_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ)
    (s0 s : State) (target_pc fsp out x20_val x21_val ca3 x28_val : BitVec 64)
    (pbDec : ProtoPolynomialDecoder) (Rest : SepProp)
    (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hfits : FitsEnv M lim st (FromPbDecAllocEnv pbDec))
    (hpc : s.pc = lsmpl.base 333 + 9384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64)
    (hx1 : s.readReg64 .x1 = fsp + 1848#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = x21_val)
    (hx22 : s.readReg64 .x22 = fsp + 1888#64)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = x28_val)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (evs : List AllocEvent) (s1 : State),
      FromPbDecEnv pbDec evs →
      s1.pc = lsmpl.base 333 + 9388#64 →
      s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s1.sp = fsp ∧
       s1.readReg64 .x19 = out ∧
       s1.readReg64 .x20 = x20_val ∧
       s1.readReg64 .x21 = x21_val ∧
       s1.readReg64 .x22 = fsp + 1888#64 ∧
       s1.readReg64 .x23 = fsp + 848#64 ∧
       s1.readReg64 .x25 = fsp + 1792#64 ∧
       s1.readReg64 .x26 = ca3 ∧
       s1.readReg64 .x28 = x28_val ∧
       TraceCalleeSaved s1 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (decoderFromPbResult pbDec) ∗
         memRegion (fsp + 1848#64) protoPolynomialDecoderSize ∗
         A.pool lim (M.stepEvents evs st) s1 ∗
         Rest)
        post Qp) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyDecoderSize ∗
        protoPolynomialDecoderAt A.repAlloc (fsp + 1848#64) pbDec ∗
        A.pool lim st s ∗
        Rest)
      post Qp :=
  v2hsh_sepWPp_bind_lscl hcl
    (SepWPp.of_sepWP_ret
      (v2hsh_decoder_step_9384_to_9388_placed hdec st s0 s fsp out x20_val x21_val ca3 x28_val
        pbDec Rest hcl hfsp_align hfits
        hpc hrun hsp hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx25 hx26 hx28 htr))
    fun s1 _P1 hpc1 hrun1 hcl1 ⟨evs, henv, hP1, hregs⟩ =>
      SepWPp.weaken_pre hP1 (hnext evs s1 henv hpc1 hrun1 hcl1 hregs)

/-! ## `<PolyEncoder>::from_pb = Err` Branch (`+9100 -> +9212 -> +9228 -> ret`) -/

/-- When `<PolyEncoder>::from_pb` returns `.error err` at `fsp + 1888`, deallocates `uc` (`dk`,
    `rootKey`, `macKey`) via `v2hse2_enc_err_9100_to_9212_of_dealloc_placed`, drops `optDec` via
    `v2hsc_cleanup_9212_to_9228_of_dealloc_placed`, and exits via `v2hs_err_cleanup_9228_placed_budget`
    writing `.error (.err .stateDecode)` under `FreeOnlyEvs`. -/
theorem v2hsh_branch_enc_err_9100_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ)
    (s0 s1 : State) (out : BitVec 64)
    (dk : List (BitVec 8)) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (err : PolynomialError) (Rest : SepProp)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9100#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = d_w0)
    (hx26_1 : s1.readReg64 .x26 = u8) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (s0.sp - 2400#64 + 1888#64) (.error err) ∗
        memRegion (s0.sp - 2400#64 + 1792#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 1848#64) 40 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 1392#64) 400 ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hd_dk := v2hstop_vecU8Heap_entails_dealloc A.repAlloc dk u8 u16 u24
  have hd_r : vecU8Payload A.repAlloc u48 pa1 auth.rootKey ⊢ vecCapPtrDealloc A.repAlloc u48 pa1 := by
    rw [hu48]
    exact vecU8Payload_entails_dealloc A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey
  have hd_m : vecU8Payload A.repAlloc u72 pa2 auth.macKey ⊢ vecCapPtrDealloc A.repAlloc u72 pa2 := by
    rw [hu72]
    exact vecU8Payload_entails_dealloc A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey
  have hek_eq :
      v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 =
      v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 := rfl
  let Frame9100 : SepProp :=
    memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
    memRegion (fsp + 2288#64) 16 ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 192 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9100 :
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 2288#64) 16 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
        v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest) ⊢
      stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 ∗
        vecCapPtrDealloc A.repAlloc u48 pa1 ∗ vecCapPtrDealloc A.repAlloc u72 pa2 ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗ A.pool lim st s1 ∗ Frame9100 := by
    rw [hek_eq]; dsimp only [Frame9100]
    refine Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
      vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
      v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗
      (stackAt fsp encoderFromPbStack ∗
       resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
       ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
       v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 ∗
       A.pool lim st s1 ∗
       (memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 2288#64) 16 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
        memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hd_r (sepConj_mono hd_m (sepConj_mono_left hd_dk)))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre9100 ?_
  refine seq_clean_evs_lscl hcl1
    (mid := lsmpl.base 333 + 9212#64)
    (P_evs := fun evs1 s2 =>
      stackAt fsp encoderFromPbStack ∗
      memRegion (fsp + 1888#64) 400 ∗
      ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
      memRegion (fsp + 1264#64) 80 ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗ Frame9100)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s2 s0)
    (v2hse2_enc_err_9100_to_9212_of_dealloc_placed hdealloc s0 s1 fsp out d_w0
      u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 err st Frame9100
      hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1) ?_
  intro evs1 s2 hevs1 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx22_2, htr2⟩
  let Frame9212 : SepProp :=
    memRegion (fsp + 1888#64) 400 ∗
    ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    memRegion (fsp + 1264#64) 80 ∗
    memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
    memRegion (fsp + 2288#64) 16 ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (fsp + 1072#64) 192 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9212 :
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) 400 ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        memRegion (fsp + 1264#64) 80 ∗
        A.pool lim (M.stepEvents evs1 st) s2 ∗ Frame9100) =
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        v2hsc_optProtoPolyDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗
        A.pool lim (M.stepEvents evs1 st) s2 ∗ Frame9212) := by
    dsimp only [Frame9100, Frame9212]
    rw [v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32,
        v2hstop_optProtoDecoderHeap_eq_v2hsc A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32]
    ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre9212) ?_
  refine seq_clean_evs_lscl hcl2
    (mid := lsmpl.base 333 + 9228#64)
    (P_evs := fun evs2 s3 =>
      stackAt fsp encoderFromPbStack ∗
      v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
        (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗
      A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s3 ∗ Frame9212)
    (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = out ∧
      s3.readReg64 .x23 = 0#64 ∧ TraceCalleeSaved s3 s0)
    (v2hsc_cleanup_9212_to_9228_of_dealloc_placed hdealloc s0 s2 fsp out optDec d_w0 d_w8 d_w16
      (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 u72
      (M.stepEvents evs1 st) Frame9212
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htr2) ?_
  intro evs2 s3 hevs2 hpc3 hrun3 _hcl3 ⟨hsp3, hx19_3, hx23_3, htr3⟩
  have h960 := v2hsh_memRegion_1344_960_collapse fsp
  have hcol2304 := v2hsh_collapse_2304_from_9228 fsp u8 u16 u24 u40 u48 u72 u80 pa2
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
  have hpre9228 :
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗
        A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s3 ∗ Frame9212) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        Rest ∗ A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s3 := by
    rw [← v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32]
    dsimp only [Frame9212]
    refine Entails.trans (Entails.of_eq (show _ =
      ((memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16) ∗
       (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
        v2hs_stack896ScratchRest fsp ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗ memRegion (fsp + 1264#64) 80)) ∗
      (stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Rest ∗ A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s3) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left
      (Entails.trans (sepConj_mono_left h960)
        (Entails.trans (Entails.of_eq (by ac_rfl)) hcol2304))) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre9228 ?_
  have hx23_lo : (s3.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx23_3]; rfl
  have h9228 := v2hs_err_cleanup_9228_placed_budget A lim
    (M.stepEvents evs2 (M.stepEvents evs1 st)) (F := F) (ext := ext)
    s0 s3 out .stateDecode Rest
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx23_lo htr3
  refine SepWP.mono h9228 fun sf Pf _ _ ⟨hPf, _hvmf, hspf, hcsf, htrf⟩ => ?_
  refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hspf, hcsf, htrf⟩
  rw [M.stepEvents_append]
  exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

theorem v2hsh_branch_enc_err_9100_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ)
    (s0 s1 : State) (out : BitVec 64)
    (dk : List (BitVec 8)) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (err : PolynomialError) (Rest : SepProp)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9100#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = d_w0)
    (hx26_1 : s1.readReg64 .x26 = u8) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (s0.sp - 2400#64 + 1888#64) (.error err) ∗
        memRegion (s0.sp - 2400#64 + 1792#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 1848#64) 40 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 1392#64) 400 ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hd_dk := v2hstop_vecU8Heap_entails_dealloc A.repAlloc dk u8 u16 u24
  have hd_r : vecU8Payload A.repAlloc u48 pa1 auth.rootKey ⊢ vecCapPtrDealloc A.repAlloc u48 pa1 := by
    rw [hu48]
    exact vecU8Payload_entails_dealloc A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey
  have hd_m : vecU8Payload A.repAlloc u72 pa2 auth.macKey ⊢ vecCapPtrDealloc A.repAlloc u72 pa2 := by
    rw [hu72]
    exact vecU8Payload_entails_dealloc A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey
  have hek_eq :
      v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 =
      v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 := rfl
  let Frame9100 : SepProp :=
    memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
    memRegion (fsp + 2288#64) 16 ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 192 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9100 :
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 2288#64) 16 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
        v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest) ⊢
      stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 ∗
        vecCapPtrDealloc A.repAlloc u48 pa1 ∗ vecCapPtrDealloc A.repAlloc u72 pa2 ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗ A.pool lim st s1 ∗ Frame9100 := by
    rw [hek_eq]; dsimp only [Frame9100]
    refine Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
      vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
      v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗
      (stackAt fsp encoderFromPbStack ∗
       resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
       ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
       v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 ∗
       A.pool lim st s1 ∗
       (memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 2288#64) 16 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
        memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hd_r (sepConj_mono hd_m (sepConj_mono_left hd_dk)))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre9100 ?_
  refine seq_clean_evs_lscl hcl1
    (mid := lsmpl.base 333 + 9212#64)
    (P_evs := fun evs1 s2 =>
      stackAt fsp encoderFromPbStack ∗
      memRegion (fsp + 1888#64) 400 ∗
      ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
      memRegion (fsp + 1264#64) 80 ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗ Frame9100)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s2 s0)
    (v2hse2_enc_err_9100_to_9212_of_placedHooks hA s0 s1 fsp out d_w0
      u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 err st Frame9100
      hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1) ?_
  intro evs1 s2 hevs1 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx22_2, htr2⟩
  let Frame9212 : SepProp :=
    memRegion (fsp + 1888#64) 400 ∗
    ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    memRegion (fsp + 1264#64) 80 ∗
    memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
    memRegion (fsp + 2288#64) 16 ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (fsp + 1072#64) 192 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9212 :
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) 400 ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        memRegion (fsp + 1264#64) 80 ∗
        A.pool lim (M.stepEvents evs1 st) s2 ∗ Frame9100) =
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        v2hsc_optProtoPolyDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗
        A.pool lim (M.stepEvents evs1 st) s2 ∗ Frame9212) := by
    dsimp only [Frame9100, Frame9212]
    rw [v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32,
        v2hstop_optProtoDecoderHeap_eq_v2hsc A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32]
    ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre9212) ?_
  refine seq_clean_evs_lscl hcl2
    (mid := lsmpl.base 333 + 9228#64)
    (P_evs := fun evs2 s3 =>
      stackAt fsp encoderFromPbStack ∗
      v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
        (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗
      A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s3 ∗ Frame9212)
    (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = out ∧
      s3.readReg64 .x23 = 0#64 ∧ TraceCalleeSaved s3 s0)
    (v2hsc_cleanup_9212_to_9228_of_placedHooks hA s0 s2 fsp out optDec d_w0 d_w8 d_w16
      (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 u72
      (M.stepEvents evs1 st) Frame9212
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htr2) ?_
  intro evs2 s3 hevs2 hpc3 hrun3 _hcl3 ⟨hsp3, hx19_3, hx23_3, htr3⟩
  have h960 := v2hsh_memRegion_1344_960_collapse fsp
  have hcol2304 := v2hsh_collapse_2304_from_9228 fsp u8 u16 u24 u40 u48 u72 u80 pa2
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
  have hpre9228 :
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗
        A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s3 ∗ Frame9212) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        Rest ∗ A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s3 := by
    rw [← v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32]
    dsimp only [Frame9212]
    refine Entails.trans (Entails.of_eq (show _ =
      ((memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16) ∗
       (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
        v2hs_stack896ScratchRest fsp ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗ memRegion (fsp + 1264#64) 80)) ∗
      (stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Rest ∗ A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s3) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left
      (Entails.trans (sepConj_mono_left h960)
        (Entails.trans (Entails.of_eq (by ac_rfl)) hcol2304))) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre9228 ?_
  have hx23_lo : (s3.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx23_3]; rfl
  have h9228 := v2hs_err_cleanup_9228_placed_budget A lim
    (M.stepEvents evs2 (M.stepEvents evs1 st)) (F := F) (ext := ext)
    s0 s3 out .stateDecode Rest
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx23_lo htr3
  refine SepWP.mono h9228 fun sf Pf _ _ ⟨hPf, _hvmf, hspf, hcsf, htrf⟩ => ?_
  refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hspf, hcsf, htrf⟩
  rw [M.stepEvents_append]
  exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

theorem v2hsh_branch_enc_err_9100_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ)
    (s0 s1 : State) (out : BitVec 64)
    (dk : List (BitVec 8)) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (err : PolynomialError) (Rest : SepProp)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9100#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = d_w0)
    (hx26_1 : s1.readReg64 .x26 = u8) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (s0.sp - 2400#64 + 1888#64) (.error err) ∗
        memRegion (s0.sp - 2400#64 + 1792#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 1848#64) 40 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 1392#64) 400 ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v2hsh_branch_enc_err_9100_of_dealloc_placed (F := F) hA.dealloc st s0 s1 out dk auth
    u8 u16 u24 u40 u48 u72 u80 pa1 pa2 w0 w8 w16 w24 w32 w40 w48
    optDec d_w0 d_w8 d_w16 d_w24 d_w32 err Rest
    hu48 hu72 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hshPlacedBudget
