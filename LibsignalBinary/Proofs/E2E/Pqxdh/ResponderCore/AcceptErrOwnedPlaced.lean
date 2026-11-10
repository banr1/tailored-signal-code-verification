/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedA
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.SharedCodeSym

/-!
# Relocatable Owned-Error Rejecting Contract for `Pqxdh::accept` (Block `79`)

Proves `pqxdhAcceptErrOwnedFrozenPlacedSpec` on Block `79` under `[LibsignalFullPlacement]` when
`Model.acceptKeys P g.inp = none`, exposing `pqxdhAcceptErrOwnedAt`, together with its cross-block
caller lift at `lsmpl.base 79`.
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
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
attribute [-arm64_norm] List.append_assoc

/-- Full-library frozen (`withLsFrozen lsmpl`) contract for `Pqxdh::accept` (Block `79`) on the
owned-error rejecting branch (`Model.acceptKeys P g.inp = none`). -/
def pqxdhAcceptErrOwnedFrozenPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec AcceptFieldsCallGhost :=
  withLsFrozen lsmpl (pqxdhAcceptErrOwnedInnerPlacedSpec P A)

/-! ## Separation-logic merge helpers -/

private theorem outPtr_tail64_to_spe_tail_placed (outPtr : BitVec 64) (b40 : BitVec 8) :
    ((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 ⊢
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗ memRegion (outPtr + 56#64) 48 := by
  have hb40 : ((outPtr + 40#64) ↦₈ b40) ⊢ memRegion (outPtr + 40#64) 1 := by
    rw [memRegion_one]
    exact Entails.sepExists_right b40 (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hb40) ?_
  have hm64 :
      memRegion (outPtr + 40#64) 1 ∗ memRegion (outPtr + 41#64) 63 =
        (∃∗ w5 : BitVec 64, (outPtr + 40#64) ↦₆₄ w5) ∗
        (∃∗ w6 : BitVec 64, (outPtr + 48#64) ↦₆₄ w6) ∗
        memRegion (outPtr + 56#64) 48 := by
    rw [← ProofLib.memRegion_split' (b := outPtr + 40#64) (n := 1) (k := 63)
          (b' := outPtr + 41#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outPtr + 40#64) (n := 8) (k := 56)
          (b' := outPtr + 48#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outPtr + 48#64) (n := 8) (k := 48)
          (b' := outPtr + 56#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (outPtr + 40#64),
        ProofLib.memRegion_eight (outPtr + 48#64)]
  rw [hm64]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim fun w6 => Entails.sepExists_elim fun w5 =>
    Entails.sepExists_right w5 (Entails.sepExists_right w6 (Entails.refl _))

private theorem outPtr_err104_owned_merge_placed (A : RustAlloc)
    (outPtr errTag w2 w3 w4 : BitVec 64) (b40 : BitVec 8)
    (hw1 : errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64) :
    pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    (outPtr ↦₃₂ 1#32) ∗
    memRegion (outPtr + 4#64) 4 ∗
    ((outPtr + 8#64) ↦₆₄ errTag) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₈ b40) ∗
    memRegion (outPtr + 41#64) 63 ⊢
    pqxdhAcceptErrOwnedAt A outPtr := by
  have hrearr :
      pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
      ((outPtr ↦₃₂ 1#32) ∗ (memRegion (outPtr + 4#64) 4 ∗ (((outPtr + 8#64) ↦₆₄ errTag) ∗
        (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
          (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63))))))) =
      (outPtr ↦₃₂ 1#32) ∗ (memRegion (outPtr + 4#64) 4 ∗
        ((((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63) ∗
          (((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
            ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
            pqxdhAcceptErrPayloadAt A errTag w2 w3 w4))) := by ac_rfl
  rw [hrearr]
  unfold pqxdhAcceptErrOwnedAt
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono_left (outPtr_tail64_to_spe_tail_placed outPtr b40)) ?_
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w6 => ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  rw [pure_sepConj_of_true hw1]
  simp only [speWordsAt, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

private theorem pqxdhAcceptErrPayloadAt_tag10_intro_placed (A : RustAlloc) (w2 w3 w4 : BitVec 64) :
    emp ⊢ pqxdhAcceptErrPayloadAt A 0x800000000000000a#64 w2 w3 w4 := by
  unfold pqxdhAcceptErrPayloadAt
  refine Entails.sepExists_right false ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← sepConj_emp ⌜True⌝, pure_sepConj_of_true trivial emp]
  exact Entails.refl _

private theorem outPtr_err104_owned_tag10_merge_placed (A : RustAlloc) (outPtr w2 w3 w4 : BitVec 64)
    (b40 : BitVec 8) :
    (outPtr ↦₃₂ 1#32) ∗
    memRegion (outPtr + 4#64) 4 ∗
    ((outPtr + 8#64) ↦₆₄ 0x800000000000000a#64) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₈ b40) ∗
    memRegion (outPtr + 41#64) 63 ⊢
    pqxdhAcceptErrOwnedAt A outPtr := by
  rw [← emp_sepConj ((outPtr ↦₃₂ 1#32) ∗ _)]
  exact Entails.trans
    (sepConj_mono_left (pqxdhAcceptErrPayloadAt_tag10_intro_placed A w2 w3 w4))
    (outPtr_err104_owned_merge_placed A outPtr 0x800000000000000a#64 w2 w3 w4 b40 (by decide))

private theorem err28_payload_intro_placed (A : RustAlloc) (ptr u2 u3 : BitVec 64)
    (hptr : ptr ≠ 0#64) :
    memRegion ptr 12 ∗ ((ptr + 12#64) ↦₆₄ u2) ∗ ((ptr + 20#64) ↦₆₄ u3) ∗ A.live ptr 28 1 ⊢
      pqxdhAcceptErrPayloadAt A 0x8000000000000018#64 28#64 ptr 28#64 := by
  have hm12 : memRegion ptr 12 =
      (∃∗ q0 : BitVec 64, ptr ↦₆₄ q0) ∗ (∃∗ q1 : BitVec 32, (ptr + 8#64) ↦₃₂ q1) := by
    rw [ProofLib.memRegion_split' (b := ptr) (n := 8) (k := 4)
          (b' := ptr + 8#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight ptr, memRegion_four (ptr + 8#64)]
  rw [hm12, sepConj_assoc, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun q0 => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun q1 => ?_
  unfold pqxdhAcceptErrPayloadAt
  refine Entails.sepExists_right true ?_
  simp only [↓reduceIte]
  rw [pure_sepConj_of_true trivial]
  let bs : List (BitVec 8) := unpack64 q0 ++ (unpack32 q1 ++ (unpack64 u2 ++ unpack64 u3))
  refine Entails.sepExists_right bs ?_
  have hbs_len : bs.length = 28 := by
    simp [bs, unpack64_length, unpack32_length]
  have hpure :
      BitVec.ofNat 64 bs.length = 28#64 ∧
      bs.length ≤ (28#64 : BitVec 64).toNat ∧
      (28#64 : BitVec 64).toNat < 2 ^ 63 ∧
      ptr ≠ 0#64 := by
    rw [hbs_len]
    exact ⟨rfl, by decide, by decide, hptr⟩
  rw [pure_sepConj_of_true hpure]
  have h28_ne : (28#64 : BitVec 64) ≠ 0#64 := by decide
  simp only [h28_ne, ↓reduceIte, hbs_len]
  have h28_nat : (28#64 : BitVec 64).toNat = 28 := rfl
  rw [h28_nat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  have hpts :
      (ptr ↦ₛ bs) =
        (ptr ↦₆₄ q0) ∗ ((ptr + 8#64) ↦₃₂ q1) ∗ ((ptr + 12#64) ↦₆₄ u2) ∗ ((ptr + 20#64) ↦₆₄ u3) := by
    dsimp only [bs]
    rw [pointsToBytes_append, unpack64_length,
        pointsToBytes_append, unpack32_length,
        pointsToBytes_append, unpack64_length,
        ← pointsTo64_eq_pointsToBytes,
        ← pointsTo32_eq_pointsToBytes,
        ← pointsTo64_eq_pointsToBytes,
        ← pointsTo64_eq_pointsToBytes]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hpts]
  exact Entails.of_eq (by ac_rfl)

/-! ## Rejecting `Pqxdh::accept` proof on Block `79` -/

set_option maxHeartbeats 3000000 in
/-- Relocatable owned-error rejecting contract for `Pqxdh::accept` (Block `79`) on `lsProg_79 H`
under `[LibsignalFullPlacement]`. -/
theorem pqxdhAccept_err_owned_placed_ok [LibsignalFullPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec P A)))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustDeallocSpec A))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_pan_rawvec : H acceptHandleRawVecErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_79 H) (blkPl_79).base
      (pqxdhAcceptErrOwnedFrozenPlacedSpec P A) := by
  unfold pqxdhAcceptErrOwnedFrozenPlacedSpec
  refine subroutine_ok_withLsFrozen_of_withRoSlice
    (roSym := "libsignal_protocol:.rodata..Lanon.393")
    (roBytes := incomingBaseKeyInvalidBytes) (by decide) ?_
  have hshim := hook_ok_79_of_mem h_shim (by decide)
  have halloc := hook_ok_79_of_mem h_alloc (by decide)
  have hdealloc := hook_ok_79_of_mem h_dealloc (by decide)
  have hmemcpy := hook_ok_79_of_mem h_memcpy (by decide)
  have hpan_rawvec :
      (lsProg_79 H).externAt? (lsρ acceptHandleRawVecErrorSym) = some Rust.panicked :=
    (externAt_79_of_mem (by decide)).trans h_pan_rawvec
  clear h_shim h_alloc h_dealloc h_memcpy h_pan_rawvec
  unfold withLsFrozen withRoSlice pqxdhAcceptErrOwnedInnerPlacedSpec rustPanicOnOomPlaced
  wpp_init x s0
  rcases x with ⟨inp, argPtr, pqskPtr, ctSlicePtr, ctBufPtr, outPtr⟩
  dsimp only at *
  have hfr0 : LibsignalFrozen lsmpl s0.mem := ‹_›
  have hF0 : LsFullFrozenInv lsmpl s0 := LsFullFrozenInv.of_frozen hfr0
  subst ‹s0.readReg64 (.gpr 0#5) = argPtr› ‹s0.readReg64 (.gpr 8#5) = outPtr›
  have hacc_pre : Model.acceptKeys P inp = none := ‹Model.acceptKeys P inp = none›
  have hws : WellSizedAcceptKeysInput inp := ‹WellSizedAcceptKeysInput inp›
  rcases hws with ⟨hikBSk, _hikBPk, hspkBSk, _hspkBPk, _hopk_sz, hpqSk, _hpqPk, hikAPk, hekAPk,
    hkemCt⟩
  rw (occs := .pos [1]) [stackAt_pqxdh_accept_top s0.sp]
  refine SepWPp.fold (Entails.of_eq (pqsk_region_phaseA_split s0.sp)) (by sep_focus) ?_
  sep_elim_exists'
  refine SepWPp.fold (Entails.of_eq (cells4_sub4944_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'
  refine SepWPp.fold (Entails.of_eq (cells10_sub80_eq s0.sp)) (by sep_focus) ?_
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
  · have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = false := hcanon_b
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
        (by sep_focus) ?_
      sep_elim_exists'
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
      sep_elim_exists'
      wp_steps
      refine SepWP.fold (err28_payload_intro_placed A _ _ _ halloc0) (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_err104_owned_merge_placed A (s0.readReg64 (.gpr 8#5)) 0x8000000000000018#64
          28#64 _ 28#64 _ (by decide))
        (by sep_focus) ?_
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (pqsk_region_phaseA_merge s0.sp _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
      clear h_canon h_agree hshim halloc hdealloc hmemcpy hpan_rawvec
      simp only [sepConj_assoc, *]
      wp_done
  · obtain ⟨ss, hss, _, _⟩ := kyberDecaps_some_and_fitBv8_eq hWF hpqSk hkemCt
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = true := hcanon_b
    have hcanon_keep : AcceptCanonTrue P inp := ⟨hcanon_b⟩
    simp only [hcanon_ec, ↓reduceIte] at *
    clear hcanon_b hcanon_ec
    have hcanon_b : P.isCanonical inp.hdr.ekAPk = true := hcanon_keep.out
    clear hcanon_keep
    rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP_lsfull hF1 (mid := (blkPl_79).base + 72#64) ?_
    wp_steps; wp_call hshim (); wp_steps
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call halloc (192, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2; try simp only [arm64_norm] at hF2
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      (fun halloc192 htr192 => ?_) (fun halloc192 halign192 htr192 => ?_)
    · refine SepWPp.of_sepWP (mid := lsρ acceptHandleRawVecErrorSym) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_lhs) (by convert hpan_rawvec using 2; wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (memRegion_192_init_split _)) (by sep_focus) ?_
      sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (alloc_to_calc_stack s0.sp)) (by sep_focus) ?_
      refine SepWPp.of_sepWP_lsfull hF2 (mid := lsmpl.base 207) ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (pointsTo64_4_allOnes_eq_F_X25519 _)) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF3; try simp only [arm64_norm] at hF3
      refine SepWPp_call_hag_placed hWF h_agree hF3 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
        (s0.readReg64 (.gpr 0#5) + 128#64) inp.hdr.ikAPk (by wp_norm_lhs) (by wp_norm_lhs)
        hsp_align (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 120#64) (by wp_norm_lhs)
        (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hikAPk⟩
        (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
        (fun hdh1 sf1 hi1 u2_1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
        (fun hdh1 sf1 dh1_ptr hpc1 hrun1 hsp1 hcs1 htr1 hF4 => ?_)
      · dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
          hcs29, hvregs1⟩
        simp only [arm64_norm]
          at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
        refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
          (by sep_focus) ?_
        sep_elim_exists'
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.fold (vec_err_dh1_merge _) (by sep_focus) ?_
        apply SepWPp.of_sepWP_ret
        wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
        refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
        refine SepWP.fold
          (outPtr_err104_owned_tag10_merge_placed A (s0.readReg64 (.gpr 8#5)) _ _ _ _)
          (by sep_focus) ?_
        refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
        clear h_canon h_agree hshim halloc hdealloc hmemcpy hpan_rawvec
        simp only [sepConj_assoc, *]
        wp_done
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
        refine SepWPp.of_sepWP_lsfull hF4 (mid := lsmpl.base 207) ?_
        wp_steps
        wp_call hmemcpy ⟨_, dh1_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)⟩
        wp_steps
        refine SepWP.fold (hdh1_bv_len ▸ pointsToBytes_entails_memRegion dh1_ptr _)
          (by sep_focus) ?_
        wp_call hdealloc (dh1_ptr, 32, 1); wp_steps
        refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh1_ptr 32#64)
          (by sep_focus) ?_
        refine SepWP.fold
          (Entails.of_eq (pointsToBytes_append_at _ F_X25519
            (P.x25519 inp.spkBSk inp.hdr.ikAPk) 32 (by decide)))
          (by sep_focus) ?_
        refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF5; try simp only [arm64_norm] at hF5
        refine SepWPp_call_hag_placed hWF h_agree hF5 (s0.readReg64 (.gpr 0#5) + 32#64) inp.ikBSk
          (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
          (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 304#64)
          (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hikBSk, hekAPk⟩
          (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
          (fun hdh2 sf2 hi2 u2_2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
          (fun hdh2 sf2 dh2_ptr hpc2 hrun2 hsp2 hcs2 htr2 hF6 => ?_)
        · dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
               hcs2_29 hvregs2
          refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
            (by sep_focus) ?_
          sep_elim_exists'
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.fold (vec_err_dh2_merge _ hpfx1_len) (by sep_focus) ?_
          apply SepWPp.of_sepWP_ret
          wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
          refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
          refine SepWP.fold
            (outPtr_err104_owned_tag10_merge_placed A (s0.readReg64 (.gpr 8#5)) _ _ _ _)
            (by sep_focus) ?_
          refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
          clear h_canon h_agree hshim halloc hdealloc hmemcpy hpan_rawvec
          simp only [sepConj_assoc, *]
          wp_done
        · have hdh2_len : (P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
          have hdh2_bv_len : (bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)).length = 32 := by
            simp [bytesToBv8, hdh2_len]
          have hpfx2_len :
              (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 96 := by
            simp [F_X25519, hdh1_len, hdh2_len]
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
               hcs2_29 hvregs2
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.of_sepWP_lsfull hF6 (mid := lsmpl.base 207) ?_
          wp_steps
          wp_call hmemcpy ⟨_, dh2_ptr, bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)⟩
          wp_steps
          refine SepWP.fold (hdh2_bv_len ▸ pointsToBytes_entails_memRegion dh2_ptr _)
            (by sep_focus) ?_
          wp_call hdealloc (dh2_ptr, 32, 1); wp_steps
          refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh2_ptr 32#64)
            (by sep_focus) ?_
          refine SepWP.fold
            (Entails.of_eq (pointsToBytes_append_at _
              (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk)
              (P.x25519 inp.ikBSk inp.hdr.ekAPk) 64
              (by simp only [bytesToBv8, List.length_map, hpfx1_len])))
            (by sep_focus) ?_
          refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hF7; try simp only [arm64_norm] at hF7
          refine SepWPp_call_hag_placed hWF h_agree hF7 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
            (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
            (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 404#64)
            (by wp_norm_lhs) (by wp_norm_lhs)
            ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hekAPk⟩
            (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
            (fun hdh3 sf3 hi3 u2_3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
            (fun hdh3 sf3 dh3_ptr hpc3 hrun3 hsp3 hcs3 htr3 hF8 => ?_)
          · dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
                 hcs3_29 hvregs3
            refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
              (by sep_focus) ?_
            sep_elim_exists'
            refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
            refine SepWPp.fold (vec_err_dh3_merge _ hpfx2_len) (by sep_focus) ?_
            apply SepWPp.of_sepWP_ret
            wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
            refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
            refine SepWP.fold
              (outPtr_err104_owned_tag10_merge_placed A (s0.readReg64 (.gpr 8#5)) _ _ _ _)
              (by sep_focus) ?_
            refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
              (by sep_focus) ?_
            clear h_canon h_agree hshim halloc hdealloc hmemcpy hpan_rawvec
            simp only [sepConj_assoc, *]
            wp_done
          · have hdh3_len : (P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
            have hdh3_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)).length = 32 := by
              simp [bytesToBv8, hdh3_len]
            have hpfx3_len :
                (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 128 := by
              simp [F_X25519, hdh1_len, hdh2_len, hdh3_len]
            dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
                 hcs3_29 hvregs3
            cases hopk_eq : inp.opkBSk? with
            | none =>
              have hacc_some :=
                acceptKeys_eq_some_of_opk_none P inp ss ‹inp.trustedPeer = true›
                  ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                  ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hss
              rw [hacc_pre] at hacc_some
              cases hacc_some
            | some opkSk =>
              have hopkSk : opkSk.length = 32 := _hopk_sz opkSk hopk_eq
              simp only [↓reduceIte]
              refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
              refine SepWPp.of_sepWP_lsfull hF8 (mid := lsmpl.base 207) ?_
              wp_steps
              wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩
              wp_steps
              refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
                (by sep_focus) ?_
              wp_call hdealloc (dh3_ptr, 32, 1)
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              wp_steps
              refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh3_ptr 32#64)
                (by sep_focus) ?_
              refine SepWP.fold
                (Entails.of_eq (pointsToBytes_append_at _
                  (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                    P.x25519 inp.ikBSk inp.hdr.ekAPk)
                  (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
                  (by simp only [bytesToBv8, List.length_map, hpfx2_len])))
                (by sep_focus) ?_
              refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              intro hF8_1; try simp only [arm64_norm] at hF8_1
              refine SepWPp_call_hag_placed hWF h_agree hF8_1 (s0.readReg64 (.gpr 0#5) + 265#64)
                opkSk (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
                (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
                (ret_pc := (blkPl_79).base + 720#64)
                (by wp_norm_lhs) (by wp_norm_lhs)
                ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hopkSk, hekAPk⟩
                (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
                (fun hdh4 sf4 hi4 u2_4 hpc4 hrun4 hsp4 hcs4 htr4 => ?_)
                (fun hdh4 sf4 dh4_ptr hpc4 hrun4 hsp4 hcs4 htr4 hF8_2 => ?_)
              · dsimp only [CalleeSavedPreserved, Reg.fp] at hcs4
                rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25,
                  hcs4_26, hcs4_27, hcs4_28, hcs4_29, hvregs4⟩
                simp only [arm64_norm]
                  at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28
                     hcs4_29 hvregs4
                refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
                  (by sep_focus) ?_
                sep_elim_exists'
                refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
                refine SepWPp.fold (vec_err_dh4_merge _ hpfx3_len) (by sep_focus) ?_
                apply SepWPp.of_sepWP_ret
                wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
                refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
                refine SepWP.fold
                  (outPtr_err104_owned_tag10_merge_placed A (s0.readReg64 (.gpr 8#5)) _ _ _ _)
                  (by sep_focus) ?_
                refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
                  (by sep_focus) ?_
                clear h_canon h_agree hshim halloc hdealloc hmemcpy hpan_rawvec
                simp only [sepConj_assoc, *]
                wp_done
              · have hacc_some :=
                  acceptKeys_eq_some_of_opk_some P inp opkSk ss ‹inp.trustedPeer = true›
                    ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                    ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hdh4 hss
                rw [hacc_pre] at hacc_some
                cases hacc_some

/-- Relocatable owned-error rejecting contract for `Pqxdh::accept` (Block `79`) lifted to any
`callerProg` (`[IsLsBlockProg callerProg i H]`, such as `lsProg_75 H`) at `lsmpl.base 79`. -/
theorem pqxdhAccept_err_owned_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec P A)))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustDeallocSpec A))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_pan_rawvec : H acceptHandleRawVecErrorSym = some Rust.panicked) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptErrOwnedFrozenPlacedSpec P A) :=
  ls_subroutine_ok_withLsFrozen_of_block
    (pqxdhAccept_err_owned_placed_ok hWF h_canon h_agree
      h_shim h_alloc h_dealloc h_memcpy h_pan_rawvec)

end CryptoVerification.E2E.Pqxdh.ResponderCore
