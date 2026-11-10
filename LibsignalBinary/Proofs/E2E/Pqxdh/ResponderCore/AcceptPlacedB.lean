/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedA
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.SharedCodeSym
import ProofLib.SepLogic.WPp

/-!
# Relocatable `Pqxdh::accept` (Block `79`), Part B: `opk = some` Branch and Combined Contract

Proves `pqxdhAccept_opt_fields_opk_some_placed_ok` (`g.inp.opkBSk?.isSome = true`) on `lsProg_79 H`
under `[LibsignalFullPlacement]`, combines both branches into `pqxdhAccept_opt_fields_placed_ok`,
and lifts the combined contract to any caller block at `lsmpl.base 79`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.Shared (pqxdhVecAppendElementsFastSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
attribute [-arm64_norm] List.append_assoc

/-- `pqxdhAcceptOptFieldsInnerPlacedSpec` restricted to `g.inp.opkBSk?.isSome = true`. -/
def pqxdhAcceptOptFieldsOpkSomeInnerPlacedSpec [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) : Spec AcceptFieldsCallGhost :=
  { pqxdhAcceptOptFieldsInnerPlacedSpec P A with
    pre := fun g s =>
      ⌜g.inp.opkBSk?.isSome = true⌝ ∗ (pqxdhAcceptOptFieldsInnerPlacedSpec P A).pre g s }

set_option maxHeartbeats 6000000 in
/-- Relocatable `Pqxdh::accept` (Block `79`) on the `g.inp.opkBSk?.isSome = true` branch under
`[LibsignalFullPlacement]`. -/
theorem pqxdhAccept_opt_fields_opk_some_placed_ok [LibsignalFullPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec P A)))
    (h_vec_append : subroutine_ok (lsProg_79 H) (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl pqxdhVecAppendElementsFastSpec))
    (h_hkdf_extract : PqxdhHkdfExtractPlacedOk P (lsProg_79 H))
    (h_hkdf_expand : PqxdhHkdfExpandMultiInfoPlacedOk P (lsProg_79 H))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustDeallocSpec A))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_decaps : HookSat H acceptKyberDecapsSym (kyberDecapsStubSpec P))
    (h_pan_rawvec : H acceptHandleRawVecErrorSym = some Rust.panicked)
    (h_pan_alloc : H Keys.lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_79 H) (blkPl_79).base
      (withLsFrozen lsmpl (pqxdhAcceptOptFieldsOpkSomeInnerPlacedSpec P A)) := by
  refine subroutine_ok_withLsFrozen_of_withRoSlice
    (roSym := "libsignal_protocol:.rodata..Lanon.393")
    (roBytes := incomingBaseKeyInvalidBytes) (by decide) ?_
  refine subroutine_ok_withLsFrozen_of_withRoSlice
    (roSym := "libsignal_protocol:.rodata..Lanon.352")
    (roBytes := bytesToBv8 infoPqxdh) (by decide) ?_
  have hshim := hook_ok_79_of_mem h_shim (by decide)
  have halloc := hook_ok_79_of_mem h_alloc (by decide)
  have hdealloc := hook_ok_79_of_mem h_dealloc (by decide)
  have hmemcpy := hook_ok_79_of_mem h_memcpy (by decide)
  have hdecaps := hook_ok_79_of_mem h_decaps (by decide)
  have hpan_rawvec :
      (lsProg_79 H).externAt? (lsρ acceptHandleRawVecErrorSym) = some Rust.panicked :=
    (externAt_79_of_mem (by decide)).trans h_pan_rawvec
  have hpan_alloc : (lsProg_79 H).externAt? (lsρ Keys.lsHandleAllocErrorSym) = some Rust.panicked :=
    (externAt_79_of_mem (by decide)).trans h_pan_alloc
  have hext_none := h_hkdf_extract.1
  have hexp' := h_hkdf_expand 12
  simp only [pqxdhHkdfExpandCellsPlacedSpec, cells, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  clear h_shim h_alloc h_dealloc h_memcpy h_decaps h_pan_rawvec h_pan_alloc
    h_hkdf_extract h_hkdf_expand
  unfold withLsFrozen withRoSlice pqxdhAcceptOptFieldsOpkSomeInnerPlacedSpec
    pqxdhAcceptOptFieldsInnerPlacedSpec rustPanicOnOomPlaced
  wpp_init x s0
  rcases x with ⟨inp, argPtr, pqskPtr, ctSlicePtr, ctBufPtr, outPtr⟩
  dsimp only at *
  have hfr0 : LibsignalFrozen lsmpl s0.mem := ‹_›
  have hF0 : LsFullFrozenInv lsmpl s0 := LsFullFrozenInv.of_frozen hfr0
  have hopk_some_in : inp.opkBSk?.isSome = true := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = argPtr› ‹s0.readReg64 (.gpr 8#5) = outPtr›
  have hws : WellSizedAcceptKeysInput inp := ‹WellSizedAcceptKeysInput inp›
  rcases hws with ⟨hikBSk, _hikBPk, hspkBSk, _hspkBPk, _hopk_sz, hpqSk, _hpqPk, hikAPk, hekAPk,
    hkemCt⟩
  rw (occs := .pos [1]) [stackAt_pqxdh_accept_top s0.sp]
  refine SepWPp.fold (Entails.of_eq (pqsk_region_phaseA_split s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells4_sub4944_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells10_sub80_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'
  unfold pqxdhAcceptOptFieldsAt
  refine SepWPp.of_sepWP_lsfull hF0 (mid := lsmpl.base 202) ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF0_1; try simp only [arm64_norm] at hF0_1
  refine SepWPp.of_sepWP_lsfull hF0_1 (mid := (blkPl_79).base + 52#64) ?_
  wp_call (subroutine_ok_withMemEq_of_withCodeLoaded
    (spec := ecPubKeyIsCanonicalCallSpec P) h_canon hF0_1.code)
    ⟨s0.readReg64 (.gpr 0#5) + 160#64, inp.hdr.ekAPk⟩
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF1; try simp only [arm64_norm] at hF1
  cases hcanon_b : P.isCanonical inp.hdr.ekAPk
  · have hacc_none : Model.acceptKeys P inp = none :=
      acceptKeys_eq_none_of_not_canonical P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
        hikAPk hekAPk hcanon_b
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = false := hcanon_b
    simp only [hcanon_ec, Bool.false_eq_true, ↓reduceIte] at *
    rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP (mid := (blkPl_79).base + 216#64) ?_
    wp_steps; wp_call hshim (); wp_steps
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call halloc (28, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      (fun halloc0 htr0 => ?_) (fun halloc0 halign0 htr0 => ?_)
    · refine SepWPp.of_sepWP (mid := lsρ acceptHandleRawVecErrorSym) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_lhs) (by convert hpan_rawvec using 2; wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
        (by sep_focus) ?_; sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (incoming_alloc_split _)) (by sep_focus) ?_
      sep_elim_exists'
      refine SepWPp.fold
        (Entails.of_eq (rodata_incoming_split1 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")))
        (by sep_focus) ?_
      apply SepWPp.of_sepWP_ret
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      refine SepWP.fold
        (Entails.of_eq (rodata_incoming_1_to_2 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")))
        (by sep_focus) ?_
      wp_steps
      refine SepWP.fold
        (Entails.of_eq (rodata_incoming_split2 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")).symm)
        (by sep_focus) ?_
      refine SepWP.fold (incoming_overlap_prep _ _ _) (by sep_focus) ?_
      sep_elim_exists'; wp_steps
      refine SepWP.fold (err28_anyHeap_intro A _ _ _) (by sep_focus) ?_
      refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5)) 0x8000000000000018#64
        _ _ _ _ (by decide)) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (pqsk_region_phaseA_merge s0.sp _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
      rw [hacc_none]
      clear h_canon h_agree h_vec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
        hpan_rawvec hpan_alloc
      simp only [sepConj_assoc, *]; wp_done
  · have hsp_align_eq : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_align
    have hsp_orr1 : (s0.sp - 4912#64) ||| 1#64 = s0.sp - 4911#64 := sp_sub4912_orr_one hsp_align_eq
    have hsp_orr2 : (s0.sp - 1744#64) ||| 1#64 = s0.sp - 1743#64 := sp_sub1744_orr_one hsp_align_eq
    obtain ⟨ss, hss, hss_len, hfit_ss⟩ := kyberDecaps_some_and_fitBv8_eq hWF hpqSk hkemCt
    have hdecaps_some : (P.kemDecaps inp.pqspkBSk inp.hdr.kemCt).isSome = true := by simp [hss]
    have hss_bv_len : (bytesToBv8 ss).length = 32 := by simp [bytesToBv8, hss_len]
    have hpqSk_drop_len : ((bytesToBv8 inp.pqspkBSk).drop 1).length = 3167 := by
      simp [bytesToBv8, hpqSk]
    have hkemCt_drop_len : ((bytesToBv8 inp.hdr.kemCt).drop 1).length = 1567 := by
      simp [bytesToBv8, hkemCt]
    obtain ⟨s0_w, s1_w, s2_w, s3_w, -, hss_cells⟩ := exists_unpack64_of_length_32 hss_bv_len
    have hro_dbf : infoPqxdh = INFO_PQXDH := by rfl_kernel
    have hinfo_len : BitVec.ofNat 64 INFO_PQXDH.length = 46#64 := by rfl_kernel
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = true := hcanon_b
    have hcanon_keep : AcceptCanonTrue P inp := ⟨hcanon_b⟩
    simp only [hcanon_ec, ↓reduceIte] at *
    clear hcanon_b hcanon_ec
    have hcanon_b : P.isCanonical inp.hdr.ekAPk = true := hcanon_keep.out
    clear hcanon_keep
    rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP_lsfull hF1 (mid := (blkPl_79).base + 72#64) ?_
    wp_steps; wp_call hshim ()
    wp_steps; have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call halloc (192, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2; try simp only [arm64_norm] at hF2
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      (fun halloc192 htr192 => ?_) (fun halloc192 halign192 htr192 => ?_)
    · refine SepWPp.of_sepWP (mid := lsρ acceptHandleRawVecErrorSym) ?_; wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_lhs) (by convert hpan_rawvec using 2; wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (memRegion_192_init_split _)) (by sep_focus) ?_
      sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (alloc_to_calc_stack s0.sp)) (by sep_focus) ?_
      refine SepWPp.of_sepWP_lsfull hF2 (mid := lsmpl.base 207) ?_; wp_steps
      refine SepWP.fold (Entails.of_eq (pointsTo64_4_allOnes_eq_F_X25519 _)) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF3; try simp only [arm64_norm] at hF3
      refine SepWPp_call_hag_placed hWF h_agree hF3 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
        (s0.readReg64 (.gpr 0#5) + 128#64) inp.hdr.ikAPk (by wp_norm_lhs) (by wp_norm_lhs) hsp_align
        (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 120#64) (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hikAPk⟩
        (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
        (fun hdh1 sf1 hi1 u2_1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
        (fun hdh1 sf1 dh1_ptr hpc1 hrun1 hsp1 hcs1 htr1 hF4 => ?_)
      · have hacc_none : Model.acceptKeys P inp = none :=
          acceptKeys_eq_none_of_dh1_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true› hikAPk
            hekAPk hcanon_b hdh1
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
          hcs29, hvregs1⟩
        simp only [arm64_norm]
          at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
        refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
          (by sep_focus) ?_; sep_elim_exists'
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.fold (vec_err_dh1_merge _) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
        wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
        refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
        refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
          0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
        refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
        rw [hacc_none]
        clear h_canon h_agree h_vec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
          hpan_rawvec hpan_alloc
        simp only [sepConj_assoc, *]; wp_done
      · have hdh1_len : (P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 32 := hWF.x25519_len _ _
        have hdh1_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)).length = 32 := by
          simp [bytesToBv8, hdh1_len]
        have hpfx1_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 64 := by
          simp [F_X25519, hdh1_len]
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
          hcs29, hvregs1⟩
        simp only [arm64_norm]
          at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.of_sepWP_lsfull hF4 (mid := lsmpl.base 207) ?_; wp_steps
        wp_call hmemcpy ⟨_, dh1_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)⟩; wp_steps
        refine SepWP.fold (hdh1_bv_len ▸ pointsToBytes_entails_memRegion dh1_ptr _)
          (by sep_focus) ?_; wp_call hdealloc (dh1_ptr, 32, 1); wp_steps
        refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh1_ptr 32#64) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ F_X25519 (P.x25519 inp.spkBSk
          inp.hdr.ikAPk) 32 (by decide))) (by sep_focus) ?_
        refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF5; try simp only [arm64_norm] at hF5
        refine SepWPp_call_hag_placed hWF h_agree hF5 (s0.readReg64 (.gpr 0#5) + 32#64) inp.ikBSk
          (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
          (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
          (ret_pc := (blkPl_79).base + 304#64) (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hikBSk, hekAPk⟩
          (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
          (fun hdh2 sf2 hi2 u2_2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
          (fun hdh2 sf2 dh2_ptr hpc2 hrun2 hsp2 hcs2 htr2 hF6 => ?_)
        · have hacc_none : Model.acceptKeys P inp = none :=
            acceptKeys_eq_none_of_dh2_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
              hikAPk hekAPk hcanon_b hdh1 hdh2
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
               hcs2_29 hvregs2
          refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
            (by sep_focus) ?_; sep_elim_exists'
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.fold (vec_err_dh2_merge _ hpfx1_len) (by sep_focus) ?_
          apply SepWPp.of_sepWP_ret; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
          refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
          refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
            0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
          refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
          rw [hacc_none]
          clear h_canon h_agree h_vec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
            hpan_rawvec hpan_alloc
          simp only [sepConj_assoc, *]; wp_done
        · have hdh2_len : (P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
          have hdh2_bv_len : (bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)).length = 32 := by
            simp [bytesToBv8, hdh2_len]
          have hpfx2_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
            P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 96 := by simp [F_X25519, hdh1_len, hdh2_len]
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
               hcs2_29 hvregs2
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.of_sepWP_lsfull hF6 (mid := lsmpl.base 207) ?_; wp_steps
          wp_call hmemcpy ⟨_, dh2_ptr, bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)⟩; wp_steps
          refine SepWP.fold (hdh2_bv_len ▸ pointsToBytes_entails_memRegion dh2_ptr _)
            (by sep_focus) ?_; wp_call hdealloc (dh2_ptr, 32, 1); wp_steps
          refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh2_ptr 32#64)
            (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
            P.x25519 inp.spkBSk inp.hdr.ikAPk) (P.x25519 inp.ikBSk inp.hdr.ekAPk) 64
            (by simp only [bytesToBv8, List.length_map, hpfx1_len]))) (by sep_focus) ?_
          refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hF7; try simp only [arm64_norm] at hF7
          refine SepWPp_call_hag_placed hWF h_agree hF7 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
            (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
            (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
            (ret_pc := (blkPl_79).base + 404#64) (by wp_norm_lhs) (by wp_norm_lhs)
            ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hekAPk⟩
            (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
            (fun hdh3 sf3 hi3 u2_3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
            (fun hdh3 sf3 dh3_ptr hpc3 hrun3 hsp3 hcs3 htr3 hF8 => ?_)
          · have hacc_none : Model.acceptKeys P inp = none :=
              acceptKeys_eq_none_of_dh3_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
                hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
            dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
                 hcs3_29 hvregs3
            refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
              (by sep_focus) ?_; sep_elim_exists'
            refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
            refine SepWPp.fold (vec_err_dh3_merge _ hpfx2_len) (by sep_focus) ?_
            apply SepWPp.of_sepWP_ret; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
            refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
            refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
              0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
            refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
              (by sep_focus) ?_; rw [hacc_none]
            clear h_canon h_agree h_vec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
              hpan_rawvec hpan_alloc
            simp only [sepConj_assoc, *]; wp_done
          · have hdh3_len : (P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
            have hdh3_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)).length = 32 := by
              simp [bytesToBv8, hdh3_len]
            have hpfx3_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
              P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 128 :=
              by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len]
            dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
                 hcs3_29 hvregs3
            cases hopk_eq : inp.opkBSk? with
            | none => simp [hopk_eq] at hopk_some_in
            | some opkSk =>
              have hopkSk : opkSk.length = 32 := _hopk_sz opkSk hopk_eq
              simp only [↓reduceIte]
              refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
              refine SepWPp.of_sepWP_lsfull hF8 (mid := lsmpl.base 207) ?_; wp_steps
              wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩; wp_steps
              refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
                (by sep_focus) ?_; wp_call hdealloc (dh3_ptr, 32, 1)
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              wp_steps; refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh3_ptr 32#64)
                (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk) (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
                (by simp only [bytesToBv8, List.length_map, hpfx2_len]))) (by sep_focus) ?_
              refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              intro hF8_1; try simp only [arm64_norm] at hF8_1
              refine SepWPp_call_hag_placed hWF h_agree hF8_1 (s0.readReg64 (.gpr 0#5) + 265#64)
                opkSk (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
                (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
                (ret_pc := (blkPl_79).base + 720#64) (by wp_norm_lhs) (by wp_norm_lhs)
                ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hopkSk, hekAPk⟩
                (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
                (fun hdh4 sf4 hi4 u2_4 hpc4 hrun4 hsp4 hcs4 htr4 => ?_)
                (fun hdh4 sf4 dh4_ptr hpc4 hrun4 hsp4 hcs4 htr4 hF8_2 => ?_)
              · have hacc_none : Model.acceptKeys P inp = none :=
                  acceptKeys_eq_none_of_dh4_zero P inp opkSk ‹inp.trustedPeer = true›
                    ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                    ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hdh4
                dsimp only [CalleeSavedPreserved, Reg.fp] at hcs4
                rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25,
                  hcs4_26, hcs4_27, hcs4_28, hcs4_29, hvregs4⟩
                simp only [arm64_norm]
                  at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28
                     hcs4_29 hvregs4
                refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
                  (by sep_focus) ?_; sep_elim_exists'
                refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
                refine SepWPp.fold (vec_err_dh4_merge _ hpfx3_len) (by sep_focus) ?_
                apply SepWPp.of_sepWP_ret; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
                refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
                refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
                  0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
                refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
                  (by sep_focus) ?_; rw [hacc_none]
                clear h_canon h_agree h_vec_append hext_none hexp' hshim halloc hdealloc hmemcpy
                  hdecaps hpan_rawvec hpan_alloc
                simp only [sepConj_assoc, *]; wp_done
              · have hdh4_len : (P.x25519 opkSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
                have hdh4_bv_len : (bytesToBv8 (P.x25519 opkSk inp.hdr.ekAPk)).length = 32 := by
                  simp [bytesToBv8, hdh4_len]
                have hpfx4_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                  P.x25519 opkSk inp.hdr.ekAPk).length = 160 := by
                  simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, hdh4_len]
                have hikm192_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                  P.x25519 opkSk inp.hdr.ekAPk ++ ss).length = 192 := by
                  simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, hdh4_len, hss_len]
                have hikm192_bv : BitVec.ofNat 64 (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                  P.x25519 opkSk inp.hdr.ekAPk ++ ss).length = 192#64 := by rw [hikm192_len]
                have hacc_some : Model.acceptKeys P inp = some (Model.deriveDRKeys P (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss)) :=
                  acceptKeys_eq_some_of_opk_some P inp opkSk ss ‹inp.trustedPeer = true›
                    ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                    ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hdh4 hss
                have hprk192_len : (bytesToBv8 (hkdfExtractRef P none (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++
                  ss))).length = 32 := by simp [bytesToBv8, hkdfExtractRef_length]
                have hprk192_len32 : (hkdfExtractRef P none (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss)).length =
                  32 := hkdfExtractRef_length P none _
                obtain ⟨p0, p1, p2, p3, -, hprk192⟩ := exists_unpack64_of_length_32 hprk192_len
                obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm192, hout192⟩ :=
                  exists_unpack64_hkdfDerive96 P hWF (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss)
                dsimp only [CalleeSavedPreserved, Reg.fp] at hcs4
                rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25,
                  hcs4_26, hcs4_27, hcs4_28, hcs4_29, hvregs4⟩
                simp only [arm64_norm]
                  at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28
                     hcs4_29 hvregs4
                refine SepWPp.fold (Entails.of_eq (calc_to_vecAppend_stack s0.sp)) (by sep_focus) ?_
                refine SepWPp.of_sepWP_lsfull hF8_2 (mid := lsmpl.base 55) ?_; wp_steps
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                intro hF8_3; try simp only [arm64_norm] at hF8_3
                refine SepWPp.of_sepWP_lsfull hF8_3 (mid := (blkPl_79).base + 944#64) ?_
                wp_call (subroutine_ok_withMemEq_of_withCodeLoaded
                  (spec := pqxdhVecAppendElementsFastSpec) h_vec_append hF8_3.code)
                  (s0.sp - 4936#64, _, dh4_ptr, bytesToBv8 (P.x25519 opkSk inp.hdr.ekAPk))
                refine SepWP.fold (vecAppend_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                wp_steps
                refine SepWP.fold (hdh4_bv_len ▸ pointsToBytes_entails_memRegion dh4_ptr _)
                  (by sep_focus) ?_; wp_call hdealloc (dh4_ptr, 32, 1)
                refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk) (P.x25519 opkSk inp.hdr.ekAPk) 128
                  (by simp only [bytesToBv8, List.length_map, hpfx3_len]))) (by sep_focus) ?_
                refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp 0#64 dh4_ptr 32#64 0#64)
                  (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (pqsk_region_phaseB_split s0.sp)) (by sep_focus) ?_
                sep_elim_exists'
                refine SepWP.fold (Entails.of_eq (kemct_region_phaseB_split s0.sp))
                  (by sep_focus) ?_; sep_elim_exists'
                refine SepWP.fold (Entails.of_eq (sub176_split_32_64 s0.sp)) (by sep_focus) ?_
                sep_elim_exists'; wp_steps
                wp_call hmemcpy ⟨s0.sp - 4911#64, pqskPtr + 1#64, (bytesToBv8 inp.pqspkBSk).drop 1⟩
                wp_steps
                wp_call hmemcpy ⟨s0.sp - 1743#64, ctBufPtr + 2#64, (bytesToBv8 inp.hdr.kemCt).drop 1⟩
                refine SepWP.fold (pqsk_head_tail_merge s0.sp hpqSk) (by sep_focus) ?_
                refine SepWP.fold (kemct_head_tail_merge s0.sp hkemCt) (by sep_focus) ?_; wp_steps
                wp_call hdecaps ⟨s0.sp - 4912#64, inp.pqspkBSk, s0.sp - 1744#64, inp.hdr.kemCt,
                  s0.sp - 176#64⟩
                wp_steps; wp_call hshim (); wp_steps; wp_call halloc (32, 1)
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                intro hF9; try simp only [arm64_norm] at hF9
                refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
                  (fun halloc32 htr32 => ?_) (fun halloc32 halign32 htr32 => ?_)
                · refine SepWPp.of_sepWP (mid := lsρ Keys.lsHandleAllocErrorSym) ?_; wp_steps
                  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                  apply SepWPp.panic (by wp_norm_lhs) (by convert hpan_alloc using 2; wp_norm_lhs)
                  exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
                · (conv => arg 4; rw [hfit_ss, ss_sub176_eq s0.sp hss_cells, hro_dbf])
                  refine SepWPp.fold (pqsk_to_extract_region s0.sp hpqSk) (by sep_focus) ?_
                  refine SepWPp.fold (kemct_to_hmac18_region s0.sp hkemCt) (by sep_focus) ?_
                  sep_elim_exists'
                  refine SepWPp.fold (Entails.of_eq (ss_and_vec160_split _ _)) (by sep_focus) ?_
                  sep_elim_exists'; apply SepWPp.of_sepWP_ret; apply SepWP.of_sepWP_lsfull hF9
                  wp_steps
                  refine SepWP.fold (cells4_to_memRegion32 _ s0_w s1_w s2_w s3_w) (by sep_focus) ?_
                  wp_call hdealloc (_, 32, 1)
                  refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                  · simp only [arm64_norm, *]
                  refine SepWP.fold (ss_vec_add160_merge _ hss_cells) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                    P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                    P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk) ss 160
                    (by simp only [bytesToBv8, List.length_map, hpfx4_len]))) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (stack_to_kdf s0.sp)) (by sep_focus) ?_; wp_steps
                  apply SepWP.checkpoint_lsfull (by wp_norm_lhs) (by wp_norm_lhs)
                  intro hF10; try simp only [arm64_norm] at hF10
                  have hF10_cro := hF10.to_lscro
                  wp_call hext_none (s0.sp - 4912#64, _, F_X25519 ++
                    P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                    P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss,
                    s0.sp - 4944#64)
                  refine SepWP.fold (vec_ok_192_merge _ hikm192_len) (by sep_focus) ?_
                  refine SepWP.fold (prk_sub4912_eq s0.sp hprk192) (by sep_focus) ?_
                  refine SepWP.fold (hmacCore_split_sub4880 P s0.sp _) (by sep_focus) ?_
                  sep_elim_exists'; refine SepWP.pure_left_elim fun hhmac192 => ?_; wp_steps
                  apply Keys.SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
                  intro hF11; try simp only [arm64_norm] at hF11
                  have hF11_cro := hF11.to_lscro
                  refine SepWP.fold (hmacState_merge_sub1744 P s0.sp _ hhmac192) (by sep_focus) ?_
                  (conv => arg 4; simp only [arm64_norm, ← hinfo_len])
                  wp_call hexp' (s0.sp - 1744#64, hkdfExtractRef P none (F_X25519 ++
                    P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                    P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss),
                    s0.sp - 4912#64, lsmpl.ρ "libsignal_protocol:.rodata..Lanon.352",
                    INFO_PQXDH, s0.sp - 176#64, s0.sp - 4944#64); sep_elim_exists'
                  refine SepWP.fold (Entails.of_eq (stack_to_kdf s0.sp).symm) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (outPtr_ok104_cells_split (s0.readReg64 (.gpr
                    8#5)))) (by sep_focus) ?_; sep_elim_exists'
                  refine SepWP.fold (okm_sub176_eq s0.sp hokm192) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (sub1680_split_32_48 s0.sp)) (by sep_focus) ?_
                  sep_elim_exists'; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
                  refine SepWP.fold (outPtr_ok104_cells_merge (s0.readReg64 (.gpr 8#5)) hout192)
                    (by sep_focus) ?_
                  refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
                  refine SepWP.fold (sub4912_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    _ _ _ _ _) (by sep_focus) ?_
                  refine SepWP.fold (sub1744_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
                    (by sep_focus) ?_
                  refine SepWP.fold (sub176_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
                    (by sep_focus) ?_
                  refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
                    (by sep_focus) ?_
                  refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
                  · simp only [arm64_norm, *]
                  refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
                    (by sep_focus) ?_; (conv => arg 4; rw [← hro_dbf]); rw [hacc_some]
                  clear h_canon h_agree h_vec_append hext_none hexp' hshim halloc hdealloc hmemcpy
                    hdecaps hpan_rawvec hpan_alloc
                  simp only [sepConj_assoc, *]; wp_done

/-- Combined relocatable `Pqxdh::accept` (Block `79`) contract on `lsProg_79 H` under
`[LibsignalFullPlacement]`. -/
theorem pqxdhAccept_opt_fields_placed_ok [LibsignalFullPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec P A)))
    (h_vec_append : subroutine_ok (lsProg_79 H) (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl pqxdhVecAppendElementsFastSpec))
    (h_hkdf_extract : PqxdhHkdfExtractPlacedOk P (lsProg_79 H))
    (h_hkdf_expand : PqxdhHkdfExpandMultiInfoPlacedOk P (lsProg_79 H))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustDeallocSpec A))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_decaps : HookSat H acceptKyberDecapsSym (kyberDecapsStubSpec P))
    (h_pan_rawvec : H acceptHandleRawVecErrorSym = some Rust.panicked)
    (h_pan_alloc : H Keys.lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_79 H) (blkPl_79).base
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A) := by
  have hnone := pqxdhAccept_opt_fields_opk_none_placed_ok hWF h_canon h_agree
    h_hkdf_extract h_hkdf_expand h_shim h_alloc h_dealloc h_memcpy h_decaps
    h_pan_rawvec h_pan_alloc
  have hsome := pqxdhAccept_opt_fields_opk_some_placed_ok hWF h_canon h_agree h_vec_append
    h_hkdf_extract h_hkdf_expand h_shim h_alloc h_dealloc h_memcpy h_decaps
    h_pan_rawvec h_pan_alloc
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hfr, hpre_inner⟩ := extract_withLsFrozen hpre
  cases hopk : x.inp.opkBSk?
  · refine hnone.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    dsimp only [withLsFrozen, pqxdhAcceptOptFieldsOpkNoneInnerPlacedSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hopk, hpre_inner⟩
  · refine hsome.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    dsimp only [withLsFrozen, pqxdhAcceptOptFieldsOpkSomeInnerPlacedSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨by simp [hopk], hpre_inner⟩

/-- Combined relocatable `Pqxdh::accept` (Block `79`) contract lifted to any `callerProg`
(`[IsLsBlockProg callerProg i H]`, such as `lsProg_75 H`) at `lsmpl.base 79`. -/
theorem pqxdhAccept_opt_fields_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec P A)))
    (h_vec_append : subroutine_ok (lsProg_79 H) (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl pqxdhVecAppendElementsFastSpec))
    (h_hkdf_extract : PqxdhHkdfExtractPlacedOk P (lsProg_79 H))
    (h_hkdf_expand : PqxdhHkdfExpandMultiInfoPlacedOk P (lsProg_79 H))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustDeallocSpec A))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_decaps : HookSat H acceptKyberDecapsSym (kyberDecapsStubSpec P))
    (h_pan_rawvec : H acceptHandleRawVecErrorSym = some Rust.panicked)
    (h_pan_alloc : H Keys.lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A) :=
  ls_subroutine_ok_withLsFrozen_of_block
    (pqxdhAccept_opt_fields_placed_ok hWF h_canon h_agree h_vec_append
      h_hkdf_extract h_hkdf_expand h_shim h_alloc h_dealloc h_memcpy h_decaps
      h_pan_rawvec h_pan_alloc)

end CryptoVerification.E2E.Pqxdh.ResponderCore
