/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbProof
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExitPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WPp

/-!
# Closed `[LibsignalPlacement]` Contract for `<PolyDecoder>::from_pb` (`DecoderFromPbClPlaced`)

Discharges the cross-block callee `core::ptr::drop_glue::<[spqr::encoding::polynomial::SortedSet<Pt>; 16]>`
(Block `264`) for `<spqr::encoding::polynomial::PolyDecoder>::from_pb` (Block `376`) under
`withLsCodeLoaded lsmpl`, and lifts the resulting contract to `lsProg_333` (`DecoderFromPbPlacedOkExt`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv (drop_glue_sorted_set_pt16_mem_on)
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Alloc
  (spqrRustAllocSym spqrRustReallocSym spqrRustNoAllocShimSym
   spqrHandleErrorSym spqrMemcpySym spqrMemmoveSym spqr_hook_ok_of_mem)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  fsp_448_add_8 fsp_448_add_16 fsp_448_add_24 fsp_448_add_32 fsp_448_add_40 fsp_448_add_48
  fsp_448_add_56 fsp_448_add_64 fsp_448_add_72 fsp_448_add_80 fsp_448_add_88 fsp_448_add_96
  fsp_456_add_8 fsp_464_add_8 fsp_472_add_8 fsp_480_add_8 fsp_488_add_8 fsp_496_add_8
  fsp_504_add_8 fsp_512_add_8 fsp_520_add_8 fsp_528_add_8
  cap_add_lsl1_lsl3_toNat cap_add_lsl1_ubfm_toNat cur_add8_sub8 cur_add8_add24

/-! ## 1. `withLsCodeLoaded` Sequencing Helpers -/

private theorem ls_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (lsmpl.base j) spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec :=
  hcallee.eq_blockProgram ▸ h

private theorem seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

private theorem sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q_mid : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm → SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h1 fun sm _ hpc hrun hclm ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hclm hq))

private theorem sepWPp_bind_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q_mid Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P Q_mid Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm Pm → SepWPp prog ret sm Pm Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ := h1 R hm hL
  rcases hout with ⟨hpcm, hrunm, Pm, hpm, hQm⟩ | hpan | hoom
  · have hcl_m : LibsignalCodeLoaded lsmpl sm.mem :=
      LibsignalCodeLoaded.of_keepsFrozen hcl hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ := h2 sm Pm hpcm hrunm hcl_m hQm R hpm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## 2. Error Exit B (`+740 -> s0.lr`) with `LibsignalCodeLoaded` -/

theorem fromPb_error_exit_740_cl_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (s0 : State) (fsp out pbA cap_pts ptsPtr w416 w424 w432 : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (sets_err : List SortedSetPt) (hsets_len : sets_err.length = 16)
    (bss : List (List (BitVec 8))) (hbss_len : bss.length = 16)
    (hle : bss.length ≤ cap_pts.toNat)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 740#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx24 : s.readReg64 .x24 = 16#64) (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out 400 ∗ memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        sortedSetPtListOf A (fsp + 32#64) sets_err ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        memRegion (pbA + 24#64) 16 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem hdealloc_sat
  rw [sortedSetPtListOf_eq_vecPtListOf]
  conv => arg 4; rw [memRegion_400_split_err out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro b8
  apply ProofLib.SepWP.exists_left; intro d0
  have hvecs_len : (sets_err.map SortedSetPt.vec).length = NUM_POLYS := by
    simp [hsets_len, NUM_POLYS, CHUNK_SIZE]
  refine align_pre_wp
    (seq_clean_lscl hcl
      (mid := lsmpl.base 264)
      (P := (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₈ b8) ∗ memRegion (out + 9#64) 391 ∗
        memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        vecPtListOf A (fsp + 32#64) (sets_err.map SortedSetPt.vec) ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        memRegion (pbA + 24#64) 16 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (P_mid := (out ↦₆₄ 0xffffffffffffffff#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391 ∗
        memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        vecPtListOf A (fsp + 32#64) (sets_err.map SortedSetPt.vec) ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        memRegion (pbA + 24#64) 16 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (Q := fun sc =>
        sc.sp = fsp ∧ sc.readReg64 .x0 = fsp + 32#64 ∧
        sc.readReg64 .x21 = ptsPtr ∧ sc.readReg64 .x24 = 16#64 ∧
        sc.readReg64 .x29 = fsp + 448#64 ∧ sc.readReg64 .x30 = (blkPl_376).base + 768#64 ∧
        calleeSavedVRegs sc = calleeSavedVRegs s0 ∧ sc.trace = s0.trace) ?_ ?_)
    (by rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]; ac_rfl)
  · dsimp only [Reg.x0, Reg.x20, Reg.x21, Reg.x24, Reg.x29, Reg.x30, BitVec.ofNat_eq_ofNat] at hpc hx21 hx24 hx29 ⊢
    wp_steps 7; wp_done
  · intro sc hpcc hruncc hcl_c ⟨hspc, hx0c, hx21c, hx24c, hx29c, hx30c, hvregsc, htrc⟩
    have hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
        (lsmpl.base 264) (withMemEq sc.mem (dropGlueSortedSetPt16Spec A)) :=
      drop_glue_sorted_set_pt16_mem_on
        (callerProg := (blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) hdealloc_sat hcl_c
    simp only [withMemEq, dropGlueSortedSetPt16Spec] at hdrop
    refine DropGlueFacts.seq_clean
      (mid := (blkPl_376).base + 776#64)
      (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion fsp 448 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ Frame))
      (Q := fun sm =>
        sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 bss.length ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x0, Reg.x20, Reg.x21, Reg.x24, Reg.x29, Reg.x30, BitVec.ofNat_eq_ofNat] at hdrop hpcc hx0c hx21c hx24c hx29c hx30c ⊢
      wp_call hdrop (⟨fsp + 32#64, sets_err.map SortedSetPt.vec⟩ : DropGlueSortedSetPt16Ghost)
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
      have hsp_sf' : sf.sp = fsp := hsp_sf.trans hspc
      refine ⟨?_, ?_⟩
      · rw [← hsp_sf, hsp_sf', fromPb_stackAt_dropGluePoly16_split_bottom fsp]
        unfold resultPolyDecoderFromPbAt noneCap
        dsimp only [resultPolyDecoderErrByteOff, resultPolyDecoderErrTailSize, polynomialErrorByte,
          polyArrayBytes, BitVec.ofNat_eq_ofNat]
        have hfsp448 := fsp_rejoin_448 fsp out pbA ptsPtr w416 w424 w432
        exact replace_sub_entails hfsp448
          (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
            A.pool ∗ stackAt fsp allocHookStack ∗
            (((out ↦₆₄ 0xffffffffffffffff#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391) ∗
              savedRegsAt fsp s0 ∗
              (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
              memRegion (pbA + 24#64) 16 ∗
              (if cap_pts = 0 then emp
                else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
              memRegion (fsp - 4128#64) 32 ∗ Frame)) (by ac_rfl) (by ac_rfl)
      · rw [hbss_len]; simp [wp_norm, arm64_norm, *]
    · intro s1 hpc1 hrun1 ⟨hsp1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
      have hbss_ne : bss ≠ [] := by intro h; simp [h] at hbss_len
      have hlen_bound : bss.length * 24 < 2 ^ 63 := by rw [hbss_len]; decide
      have hrejoin_pb := pbA_rejoin_40 pbA cap_pts ptsPtr 16#64
      have hrejoin_buf := DropGlueFacts.memRegion_rejoin_vecBuf A 24 8 cap_pts ptsPtr bss.length hle hcap_bound
      refine DropGlueFacts.seq_clean
        (fromPb_drop_vec_u8_776_placed_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align bss hbss_ne hlen_bound
          s1 _ hpc1 hrun1 hsp1 hx20_1 hx21_1 hx24_1 hvregs1 htr1) ?_
      intro s2 hpc2 hrun2 ⟨hsp2, hx20_2, hx21_2, hvregs2, htr2⟩
      have hpre_820 :
          memRegion ptsPtr (bss.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
            (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
              memRegion fsp 448 ∗ savedRegsAt fsp s0 ∗
              (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
              memRegion (pbA + 24#64) 16 ∗
              (if cap_pts = 0 then emp
                else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
              memRegion (fsp - 4128#64) 32 ∗ Frame) ⊢
          (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
            savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
            A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
            (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
              memRegion (pbA + 24#64) 16 ∗ Frame) := by
        rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]
        unfold vecVecU8BufDealloc
        exact replace_sub_entails hrejoin_buf
          ((pbA ↦₆₄ cap_pts) ∗ savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
            A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
            resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) (by ac_rfl) (by ac_rfl)
      have hpost_final :
          (pbA ↦₆₄ cap_pts) ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗
            (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
              memRegion (pbA + 24#64) 16 ∗ Frame) ⊢
          resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame :=
        replace_sub_entails hrejoin_pb
          (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) (by ac_rfl) (by ac_rfl)
      exact SepWP.weaken_pre hpre_820
        (SepWP.strengthen_entails_const hpost_final
          (fromPb_tail_820_placed_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
            s2 _ hpc2 hrun2 hsp2 hx20_2 hx21_2 hvregs2 htr2))

/-! ## 3. Closed `[LibsignalPlacement]` Contract for `<PolyDecoder>::from_pb` (Block `376`) -/

set_option maxHeartbeats 800000 in
theorem fromPbDec_cl_placed_ok_core [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (blkPl_376).base
      (withLsCodeLoaded lsmpl (fromPbDecSpecWithStack A fromPbCoreStack)) := by
  have hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem hdealloc_sat
  have hmemcpy : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    spqr_hook_ok_of_mem hmemcpy_sat
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA, pb⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [fromPbDecSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨stackAt s0.sp fromPbCoreStack ∗
      (memRegion out polyDecoderSize ∗ protoPolynomialDecoderAt A pbA pb ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  dsimp only [withLsCodeLoaded, fromPbDecSpecWithStack]
  have hpro := fromPb_save_regs_placed_sepWP (ext := ext) s0 out pbA hsp0_align
    (memRegion out polyDecoderSize ∗ protoPolynomialDecoderAt A pbA pb ∗ A.pool)
    hpc0 hrun0 hx0 hx1
  refine sepWPp_seq_clean_lscl hcl0 hpro ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx0_1, hx1_1, hx29_1, hvregs1, htr1⟩
  let fsp := s0.sp - 544#64
  have hfsp : HiddenEq fsp (s0.sp - 544#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 544#64 hsp0_align
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (by ac_rfl))
      (protoPolynomialDecoderAt_expose A pbA pb
        (savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
          memRegion out polyDecoderSize ∗ A.pool))) ?_
  apply SepWPp.exists_elim; intro cap_pts
  apply SepWPp.exists_elim; intro ptsPtr
  apply SepWPp.pure_elim; rintro ⟨hle, hcap_bound, hlen_bound, _⟩
  by_cases hlen16 : pb.pts.length = 16
  · have hhdr := fromPb_header_ok_placed_sepWP (ext := ext) s1 fsp out pbA
      ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        memRegion out polyDecoderSize ∗ A.pool)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre (by rw [hlen16]; exact Entails.of_eq (by ac_rfl))
      (sepWPp_seq_clean_lscl hcl1 hhdr ?_)
    intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx20_2, hx24_2, hx29_2, hvregs2, htr2⟩
    conv => arg 4; rw [memRegion_448_split fsp, fromPb_stackAt_dropGluePoly16_split_bottom fsp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v432
    apply SepWPp.exists_elim; intro v424
    apply SepWPp.exists_elim; intro v416
    apply SepWPp.exists_elim; intro v24
    apply SepWPp.exists_elim; intro v16
    apply SepWPp.exists_elim; intro v8
    have hinit := fromPb_init_empty_headers_placed_sepWP (ext := ext)
      s2 fsp out pbA ptsPtr v8 v16 v24 hfsp_align
      (memRegion fsp 8 ∗
        ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
        memRegion out polyDecoderSize ∗ A.pool)
      hpc2 hrun2 hsp2 hx0_2 hx20_2 hx24_2 hx29_2
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean_lscl hcl2 hinit ?_)
    intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, hx21_3, hx24_3, hx25_3, hx29_3, hvregs3, htr3⟩
    have hpts_ne : pb.pts ≠ [] := by intro h; simp [h] at hlen16
    let Frame3 : SepProp :=
      ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
        memRegion fsp 8 ∗ memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗ memRegion out polyDecoderSize
    by_cases hall_pts : ∀ bs ∈ pb.pts, bs.length % 4 = 0
    · refine SepWPp.weaken_pre
        (by
          dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, Frame3]
          rw [BitVec.add_zero, BitVec.add_zero, hlen16]
          exact Entails.of_eq (by ac_rfl))
        (fromPb_outer_loop_placed_wpp h_panic hshim_sat halloc_sat hmemmove_sat
          s0 fsp ptsPtr hfsp_align pb.pts hpts_ne 0
          (by omega) v416 v424 v432 s3 Frame3
          hpc3 hrun3 hsp3 hx19_3 hx21_3 hx24_3 hx25_3 hx29_3
          (by rw [htr3, htr2, htr1]) (by rw [hvregs3, hvregs2, hvregs1])
          (fun sm w416 w424 w432 hall hpcm hrunm hspm hx21m _ _ htrm hvregsm => ?_)
          (fun _ _ _ _ _ ⟨bs, hbs, hne⟩ _ _ _ _ _ _ _ _ _ => (hne (hall_pts bs hbs)).elim))
      rw [fromPbDecResult_eq_ok_of_all_mod4 pb hlen16 hall]
      have hout_len : (pb.pts.map fun bs => pushChunks4Total bs { vec := [] }).length = 16 := by
        simp [hlen16]
      have hok := fromPb_success_exit_876_placed_sepWP hdealloc hmemcpy s0 fsp out pbA cap_pts ptsPtr w416 w424 w432
        hfsp hsp0_align hfsp_align pb hlen16
        (pb.pts.map fun bs => pushChunks4Total bs { vec := [] }) hout_len hle hcap_bound
        sm emp hpcm hrunm hspm hx21m hvregsm htrm
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_core_placed s0 sm out pbA _ _ R hok)
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, polyDecoderSize, Frame3]
      rw [BitVec.add_zero, BitVec.add_zero]
      exact Entails.of_eq (by ac_rfl)
    · let s0' : State := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_376).base + 740#64)
      have hr30 : s0'.readReg64 (Reg.gpr 30#5) = (blkPl_376).base + 740#64 := by
        simp [s0', wp_norm, arm64_norm]
      refine sepWPp_bind_lscl hcl3
        (Q_mid := fun sm Pm =>
          ∃ (sets_err : List SortedSetPt) (w416 w424 w432 : BitVec 64),
            (∃ bs ∈ pb.pts, bs.length % 4 ≠ 0) ∧ sets_err.length = pb.pts.length ∧
            sm.sp = fsp ∧ sm.readReg64 .x21 = ptsPtr ∧
            sm.readReg64 .x24 = 16#64 ∧ sm.readReg64 .x29 = fsp + 448#64 ∧
            sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
            (Pm ⊢ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ w416) ∗
              ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
              sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * 0)) sets_err ∗
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * 0)) pb.pts ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame3))
        (SepWPp.weaken_pre
          (by
            dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, Frame3]
            rw [BitVec.add_zero, BitVec.add_zero, hlen16]
            exact Entails.of_eq (by ac_rfl))
          (fromPb_outer_loop_placed_wpp (R := R) h_panic hshim_sat halloc_sat hmemmove_sat
            s0' fsp ptsPtr hfsp_align pb.pts hpts_ne 0
            (by omega) v416 v424 v432 s3 Frame3
            hpc3 hrun3 hsp3 hx19_3 hx21_3 hx24_3 hx25_3 hx29_3
            (by change s3.trace = s0.trace; rw [htr3, htr2, htr1])
            (by change calleeSavedVRegs s3 = calleeSavedVRegs s0; rw [hvregs3, hvregs2, hvregs1])
            (fun _ _ _ _ hall _ _ _ _ _ _ _ _ => (hall_pts hall).elim)
            (fun sm sets_err w416 w424 w432 hex hsets_len hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm =>
              SepWPp.done (hpcm.trans hr30.symm) hrunm
                ⟨sets_err, w416, w424, w432, hex, hsets_len, hspm, hx21m, hx24m, hx29m, htrm, hvregsm, Entails.refl _⟩)))
        ?_
      intro sm Pm hpcm' hrunm hclm ⟨sets_err, w416, w424, w432, hex, hsets_len, hspm, hx21m, hx24m, hx29m, htrm, hvregsm, hPm⟩
      have hpcm : sm.pc = (blkPl_376).base + 740#64 := hpcm'.trans hr30
      refine SepWPp.weaken_pre hPm ?_
      rw [fromPbDecResult_eq_err_of_exists_mod4 pb hlen16 hex]
      have hsets_len16 : sets_err.length = 16 := hsets_len.trans hlen16
      have herr := fromPb_error_exit_740_cl_placed_sepWP hdealloc_sat s0 fsp out pbA cap_pts ptsPtr w416 w424 w432
        hfsp hsp0_align hfsp_align sets_err hsets_len16 pb.pts hlen16 hle hcap_bound
        sm hclm emp hpcm hrunm hspm hx21m hx24m hx29m hvregsm htrm
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_core_placed s0 sm out pbA (.error .serializationInvalid) _ R herr)
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, polyDecoderSize, Frame3]
      rw [BitVec.add_zero, BitVec.add_zero]
      have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
      exact replace_sub_entails hpb16
        (memRegion out 400 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          sortedSetPtListOf A (fsp + 32#64) sets_err ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool ∗ stackAt fsp allocHookStack)
        (by ac_rfl) (by ac_rfl)
  · rw [fromPbDecResult_eq_err_of_len_ne_16 pb hlen16]
    have hnPts : pb.pts.length < 2 ^ 64 := by omega
    have hhdr := fromPb_header_err_placed_sepWP (ext := ext) s1 fsp out pbA
      pb.pts.length hnPts hlen16
      ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        memRegion out polyDecoderSize ∗ A.pool)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.seq_clean hhdr ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx20_2, hx24_2, _, hvregs2, htr2⟩
    have herr := fromPb_error_exit_712_placed_sepWP hdealloc s0 fsp out pbA cap_pts ptsPtr
      hfsp hsp0_align hfsp_align pb.pts hle hcap_bound hlen_bound
      s2 emp hpc2 hrun2 hsp2 hx0_2 hx20_2 hx24_2 (by rw [hvregs2, hvregs1]) (by rw [htr2, htr1])
    refine SepWPp.weaken_pre ?_
      (sepWPp_of_exit_core_placed s0 s2 out pbA (.error .serializationInvalid) _ R herr)
    dsimp only [polyDecoderSize]
    have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
    exact replace_sub_entails hpb16
      (memRegion out 400 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack)
      (by ac_rfl) (by ac_rfl)

private theorem withLsCodeLoaded_fromPbDecSpecWithStack_mono [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {entry : BitVec 64} {stack1 stack2 : Nat}
    (hle : stack1 ≤ stack2) (h64 : stack2 < 2 ^ 64)
    (h : subroutine_ok P entry (withLsCodeLoaded lsmpl (fromPbDecSpecWithStack A stack1))) :
    subroutine_ok P entry (withLsCodeLoaded lsmpl (fromPbDecSpecWithStack A stack2)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  obtain ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  let Rextra := memRegion (s0.sp - BitVec.ofNat 64 stack2) (stack2 - stack1)
  have hsplit : stackAt s0.sp stack2 = Rextra ∗ stackAt s0.sp stack1 := by
    have heq : stack1 + (stack2 - stack1) = stack2 := Nat.add_sub_of_le hle
    have h := ProofLib.stackAt_split_bottom s0.sp stack1 (stack2 - stack1) (by omega)
    dsimp only [Rextra]; rwa [heq] at h
  have hpre1 : s0.mem ⊨ (withLsCodeLoaded lsmpl (fromPbDecSpecWithStack A stack1)).pre x s0 ∗ (Rextra ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, Satisfies.mono ?_ hpre'⟩
    dsimp only [fromPbDecSpecWithStack]
    rw [hsplit]
    exact Entails.of_eq (by ac_rfl)
  refine subroutine_ok.mono_outcome h x (Rextra ∗ R) s0 hpc hrun hpre1 hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan_s, hpan⟩ | ⟨_c, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, Satisfies.mono ?_ hpost⟩
    dsimp only [withLsCodeLoaded, fromPbDecSpecWithStack]
    rw [hsplit]
    exact Entails.of_eq (by ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan_s, Satisfies.mono ?_ hpan⟩)
    dsimp only [withLsCodeLoaded, fromPbDecSpecWithStack, fromPbOnPanic]
    refine Entails.trans (Entails.of_eq (show
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ (Rextra ∗ R) =
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ (anyHeap ∗ Rextra)) ∗ R by ac_rfl)) ?_
    exact sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem withLsCodeLoaded_decoderFromPbSpec_of_fromPbDecSpecWithStack [LibsignalPlacement]
    {A : RustAlloc} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      (withLsCodeLoaded lsmpl (fromPbDecSpecWithStack A decoderFromPbStack))) :
    subroutine_ok P entry (withLsCodeLoaded lsmpl (decoderFromPbSpec A)) := by
  apply subroutine_ok_outcome_intro
  intro ⟨out, pbA, pb⟩ R s0 hpc hrun hpre hal
  refine subroutine_ok.mono_outcome h ⟨out, pbA, pb⟩ R s0 hpc hrun hpre hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, decoderFromPbSpec, fromPbDecSpecWithStack] at hpost ⊢
    rwa [← fromPbDecResult_eq_decoderFromPbResult pb]
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- Closed `[LibsignalPlacement]` contract for `<PolyDecoder>::from_pb` (Block `376`) on `lsProg_376`. -/
theorem decoder_from_pb_cl_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_376 (Rust.withPanics ext))
      (lsmpl.base 376)
      (withLsCodeLoaded lsmpl (decoderFromPbSpec A)) := by
  rw [← ls_blockPlacement_base (i := 376)]
  exact withLsCodeLoaded_decoderFromPbSpec_of_fromPbDecSpecWithStack
    (withLsCodeLoaded_fromPbDecSpecWithStack_mono (by decide) (by decide)
      (fromPbDec_cl_placed_ok_core halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat h_panic))

theorem decoder_from_pb_cl_blockProgram [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 376 (Rust.withPanics ext))
      (lsmpl.base 376)
      (withLsCodeLoaded lsmpl (decoderFromPbSpec A)) :=
  ls_to_blockProgram (decoder_from_pb_cl_placed_ok_ext halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat h_panic)

theorem decoder_from_pb_cl_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 376)
      (withLsCodeLoaded lsmpl (decoderFromPbSpec A)) :=
  ls_subroutine_ok_of_block (decoder_from_pb_cl_placed_ok_ext halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat h_panic) hidx

theorem decoder_from_pb_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 376)
      (withMemEq m (decoderFromPbSpec A)) :=
  lscall_blk_cl (decoder_from_pb_cl_placed_ok_ext halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat h_panic) hcl hidx

/-- Lifted `[LibsignalPlacement]` contract for `<PolyDecoder>::from_pb` (Block `376`) on `lsProg_333`
    (`DecoderFromPbPlacedOkExt A ext`). -/
theorem decoder_from_pb_on_333_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    DecoderFromPbPlacedOkExt A ext :=
  decoder_from_pb_cl_on (callerProg := lsProg_333 (Rust.withPanics ext))
    halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat h_panic

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  fromPb_error_exit_740_cl_placed_sepWP
  fromPbDec_cl_placed_ok_core
  decoder_from_pb_cl_placed_ok_ext
  decoder_from_pb_cl_blockProgram
  decoder_from_pb_cl_on
  decoder_from_pb_mem_on
  decoder_from_pb_on_333_placed_ok_ext
)
end CryptoVerification.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.Poly.DecoderPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  fromPb_error_exit_740_cl_placed_sepWP
  fromPbDec_cl_placed_ok_core
  decoder_from_pb_cl_placed_ok_ext
  decoder_from_pb_cl_blockProgram
  decoder_from_pb_cl_on
  decoder_from_pb_mem_on
  decoder_from_pb_on_333_placed_ok_ext
)
end CryptoVerification.SpqrV1.Poly.DecoderPb
