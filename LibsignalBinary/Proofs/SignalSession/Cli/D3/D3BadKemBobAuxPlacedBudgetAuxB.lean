/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxA
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.SharedCodeSym
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Bad-KEM Error Ownership (`Pqxdh::accept` Block `79`, `opk = some`)

Proves the `opk = some` branch (`pqxdhAccept_badKem_err_owned_opk_some_placed_ok`) of the
budget-threaded owned-error contract for `Pqxdh::accept` (Block `79`) on Bad-KEM.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

open Arm64 ProofLib ProofLib.ProgramReflection SepProp BitVec
open CryptoVerification (
  LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement blkLib_eq_79 blkPC_79
  blkPl_79 libsignalSessionLib lsLogFilterAddr lsMemcpySym lsProg_79 lsmpl lsρ
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (
  withLsCodeRoLoaded withLsFrozen withRoSlice
)
open CryptoVerification.LibsignalTripleRatchet.Keys (lsRustAllocSym lsRustNoAllocShimSym)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput F_X25519 Primitives StructuralPrims WellSizedAcceptKeysInput
  bv_add_neg64 bv_sub_add_lit' bv_sub_sub_lit bytesToBv8
  incomingBaseKeyInvalidBytes readReg_setMem_setPC_pre
  readReg_setPC_pre readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  AcceptCanonTrue LsFullFrozenInv acceptRustDeallocSym alloc_to_alloc_stack_of_eq
  alloc_to_calc_stack alloc_to_calc_stack_of_eq and_ff_hi56_3 and_ff32_hi56_3
  calc_to_alloc_stack calc_to_vecAppend_stack cells_sub4944_4_merge cells_sub80_10_merge
  cells10_sub80_eq cells3_sub4912_to_memRegion24 cells4_sub4944_eq emp_entails_anyHeap
  extractLsb_hi56_3
  hook_ok_79_of_mem incoming_alloc_split incoming_overlap_prep memRegion_192_init_split
  outPtr_err104_split pointsTo64_4_allOnes_eq_F_X25519 pointsToBytes_append_at
  pqsk_region_phaseA_cells_merge pqsk_region_phaseA_merge pqsk_region_phaseA_split
  rodata_incoming_1_to_2 rodata_incoming_split1 rodata_incoming_split2
  stackAt_pqxdh_accept_top subStack_to_alloc subStack_to_alloc_of_eq
  subroutine_ok_withLsFrozen_of_withRoSlice subroutine_ok_withMemEq_of_withCodeLoaded
  vec_err_dh1_merge vec_err_dh2_merge vec_err_dh3_merge vec_err_dh4_merge vec_ok_160_merge
  vecAppend_to_alloc_stack_of_eq zext64_trunc32_hi56_3_and_ff
)
open CryptoVerification.E2E.Pqxdh.ResponderCore.SepWPp (of_sepWP_lsfull)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  AcceptBadKemGhost pkVecTag? pkVecTag?_8_1568_eq_none_cases pqxdhAcceptBadKemFieldsAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxA (
  AcceptBadKemEnv acceptBadKemEvents bv64_ofNat_ne_1569_placed bv64_ofNat_ne_zero_of_pos_placed
  cond_ne_ctLen1569_placed cond_ne_tag8_32_concat_placed cond_ne_tag8_32_placed
  cond_ne_tag8_concat_placed cond_ne_tag8_placed err28_badKem_payload_intro_placed
  fitsEnv_acceptBadKemEnv_iff fitsEvents_mid fitsEvents_pfx lsroCheck_incomingBaseKeyInvalid
  outPtr_badKem_err104_owned_merge_placed outPtr_badKem_err104_plain_merge_placed
  sepWP_instantiate_ro1_post_exists sepWPp_alloc_post
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
  rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (
  SepWPp_call_hag_placed acceptCalculateAgreementPlacedBaseSpec calculateAgreementEvents
  ecPubKeyIsCanonicalCallSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget (pqxdhVecAppendElementsFastSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpySpec noAllocShimSpec)

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxB

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
attribute [-arm64_norm] List.append_assoc
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local irreducible] FitsEvents

def pqxdhAcceptBadKemErrOwnedOpkSomeInnerPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (AcceptBadKemGhost × M.σ) :=
  { D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv with
    pre := fun (g, st) s =>
      ⌜g.inp.opkBSk?.isSome = true⌝ ∗
        (D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A lim
          AcceptErrEnv).pre (g, st) s }

local macro "badkem_ct_exit_placed" s0:ident A:ident ctBufPtr:ident
    hbadKem:ident hct_bd:ident
    h_canon:ident h_agree:ident h_vec_append:ident hshim:ident
    halloc:ident hdealloc:ident hmemcpy:ident
    st_cur:ident evs_out:ident hst_fin:ident henv_out:ident : tactic =>
  `(tactic| (
    rcases pkVecTag?_8_1568_eq_none_cases $hbadKem with
      hct_eq | ⟨b0, rest, hct_eq, hb0⟩ | ⟨rest, hct_eq, hlen_ne⟩
    · subst hct_eq
      wp_simp_pre_fast [List.length_nil]
      wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call $hdealloc (_, 192, 1, $st_cur)
      wp_steps_sync_pool (($s0).readReg64 Reg.lr)
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_badKem_err104_plain_merge_placed ($A).repAlloc 7 (by decide) (by decide)
          (($s0).readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge ($s0).sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge ($s0).sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq ($s0).sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top ($s0).sp).symm) (by sep_focus) ?_
      have hst_rw := $hst_fin; rw [hst_rw]; have _ := $henv_out
      clear $h_canon $h_agree $h_vec_append $hshim $halloc $hdealloc $hmemcpy
      refine sepWP_instantiate_ro1_post_exists $evs_out ?_
      simp only [List.length_nil, sepConj_assoc, *]; wp_done
    · subst hct_eq
      have hne0 : BitVec.ofNat 64 (b0 :: rest).length ≠ 0#64 :=
        bv64_ofNat_ne_zero_of_pos_placed (by simp) $hct_bd
      have hbeq0 : (BitVec.ofNat 64 (b0 :: rest).length == 0#64) = false := beq_false_of_ne hne0
      have hc_tag64 := cond_ne_tag8_placed hb0; have hc_tag64' := cond_ne_tag8_concat_placed hb0
      have hc_tag32 := cond_ne_tag8_32_placed hb0; have hc_tag32' := cond_ne_tag8_32_concat_placed hb0
      refine SepWP.fold (Entails.of_eq (pointsToBytes_cons $ctBufPtr b0 rest)) (by sep_focus) ?_
      wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call $hdealloc (_, 192, 1, $st_cur)
      wp_steps_sync_pool (($s0).readReg64 Reg.lr)
      refine SepWP.fold (Entails.of_eq (pointsToBytes_cons $ctBufPtr b0 rest).symm) (by sep_focus) ?_
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_badKem_err104_plain_merge_placed ($A).repAlloc 31 (by decide) (by decide)
          (($s0).readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge ($s0).sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge ($s0).sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq ($s0).sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top ($s0).sp).symm) (by sep_focus) ?_
      have hst_rw := $hst_fin; rw [hst_rw]; have _ := $henv_out
      clear $h_canon $h_agree $h_vec_append $hshim $halloc $hdealloc $hmemcpy
      refine sepWP_instantiate_ro1_post_exists $evs_out ?_
      simp only [sepConj_assoc, *]; wp_done
    · subst hct_eq
      have hne0 : BitVec.ofNat 64 (8#8 :: rest).length ≠ 0#64 :=
        bv64_ofNat_ne_zero_of_pos_placed (by simp) $hct_bd
      have hbeq0 : (BitVec.ofNat 64 (8#8 :: rest).length == 0#64) = false := beq_false_of_ne hne0
      have hne1569 : BitVec.ofNat 64 (8#8 :: rest).length ≠ 1569#64 :=
        bv64_ofNat_ne_1569_placed hlen_ne $hct_bd
      have hc_len := cond_ne_ctLen1569_placed hne1569
      refine SepWP.fold (Entails.of_eq (pointsToBytes_cons $ctBufPtr 8#8 rest)) (by sep_focus) ?_
      wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call $hdealloc (_, 192, 1, $st_cur)
      wp_steps_sync_pool (($s0).readReg64 Reg.lr)
      refine SepWP.fold (Entails.of_eq (pointsToBytes_cons $ctBufPtr 8#8 rest).symm) (by sep_focus) ?_
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_badKem_err104_plain_merge_placed ($A).repAlloc 34 (by decide) (by decide)
          (($s0).readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge ($s0).sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge ($s0).sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq ($s0).sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top ($s0).sp).symm) (by sep_focus) ?_
      have hst_rw := $hst_fin; rw [hst_rw]; have _ := $henv_out
      clear $h_canon $h_agree $h_vec_append $hshim $halloc $hdealloc $hmemcpy
      refine sepWP_instantiate_ro1_post_exists $evs_out ?_
      simp only [sepConj_assoc, *]; wp_done))

set_option maxHeartbeats 10000000 in
/-- Budget-threaded owned-error rejecting contract for `Pqxdh::accept` (Block `79`) on the
`g.inp.opkBSk?.isSome = true` branch when `pkVecTag? 8#8 1568 g.ctBytes = none`. -/
theorem pqxdhAccept_badKem_err_owned_opk_some_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec M P A lim)))
    (h_vec_append : subroutine_ok (lsProg_79 H) (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl pqxdhVecAppendElementsFastSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_79 H) (blkPl_79).base
      (withLsFrozen lsmpl
        (pqxdhAcceptBadKemErrOwnedOpkSomeInnerPlacedSpec A lim (AcceptBadKemEnv P))) := by
  refine subroutine_ok_withLsFrozen_of_withRoSlice
    (roSym := "libsignal_protocol:.rodata..Lanon.393")
    (roBytes := incomingBaseKeyInvalidBytes) lsroCheck_incomingBaseKeyInvalid ?_
  have hshim := hook_ok_79_of_mem h_shim (by decide)
  have halloc := subroutine_ok_allocNoOom_of_budget (hook_ok_79_of_mem h_alloc (by decide))
  have hdealloc := hook_ok_79_of_mem h_dealloc (by decide)
  have hmemcpy := hook_ok_79_of_mem h_memcpy (by decide)
  simp only [rustCliDeallocBudgetSpec, AllocCallPreserved] at hdealloc
  clear h_shim h_alloc h_dealloc h_memcpy
  unfold withLsFrozen withRoSlice pqxdhAcceptBadKemErrOwnedOpkSomeInnerPlacedSpec
    D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedInnerPlacedSpec
  wpp_init x s0
  rcases x with ⟨⟨inp, ctBytes, argPtr, pqskPtr, ctSlicePtr, ctBufPtr, outPtr⟩, st⟩
  dsimp only at *
  have hfr0 : LibsignalFrozen lsmpl s0.mem := ‹_›
  have hF0 : LsFullFrozenInv lsmpl s0 := LsFullFrozenInv.of_frozen hfr0
  have hopk_some_in : inp.opkBSk?.isSome = true := ‹_›
  have hct_bd : ctBytes.length < 2 ^ 63 := ‹ctBytes.length < 2 ^ 63›
  have hbadKem : pkVecTag? 8#8 1568 ctBytes = none := ‹pkVecTag? 8#8 1568 ctBytes = none›
  have hfits_env : FitsEnv M lim st (AcceptBadKemEnv P inp) := ‹_›
  have hfits_all : FitsEvents M lim st (acceptBadKemEvents P inp) :=
    (fitsEnv_acceptBadKemEnv_iff P inp).mp hfits_env
  subst ‹s0.readReg64 (.gpr 0#5) = argPtr› ‹s0.readReg64 (.gpr 8#5) = outPtr›
  have hws : WellSizedAcceptKeysInput inp := ‹WellSizedAcceptKeysInput inp›
  rcases hws with ⟨hikBSk, _hikBPk, hspkBSk, _hspkBPk, _hopk_sz, _hpqSk, _hpqPk, hikAPk, hekAPk,
    _hkemCt⟩
  rw (occs := .pos [1]) [stackAt_pqxdh_accept_top s0.sp]
  refine SepWPp.fold (Entails.of_eq (pqsk_region_phaseA_split s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells4_sub4944_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells10_sub80_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; unfold pqxdhAcceptBadKemFieldsAt
  refine of_sepWP_lsfull hF0 (mid := lsmpl.base 202) ?_
  wp_steps_sync_pool (lsmpl.base 202); apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF0_1; try simp only [arm64_norm] at hF0_1
  refine of_sepWP_lsfull hF0_1 (mid := (blkPl_79).base + 52#64) ?_
  have hcanon0 := subroutine_ok_withMemEq_of_withCodeLoaded
    (spec := ecPubKeyIsCanonicalCallSpec P) h_canon hF0_1.code
  simp only [ecPubKeyIsCanonicalCallSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderCore.ecPubKeyIsCanonicalCallSpec] at hcanon0
  wp_call hcanon0 ⟨s0.readReg64 (.gpr 0#5) + 160#64, inp.hdr.ekAPk⟩
  refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF1; try simp only [arm64_norm] at hF1
  cases hcanon_b : P.isCanonical inp.hdr.ekAPk
  · have hevs_eq : acceptBadKemEvents P inp = rustAllocEvents 28 1 := by
      simp [acceptBadKemEvents, hcanon_b]
    have hfits28 : FitsEvents M lim st (rustAllocEvents 28 1) := hevs_eq ▸ hfits_all
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = false := hcanon_b
    simp only [hcanon_ec, Bool.false_eq_true, ↓reduceIte] at *; rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP (mid := (blkPl_79).base + 216#64) ?_
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym); wp_call hshim ()
    refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrl28 : LibsignalBinary.Heap.RustLayoutOk 28 1 :=
      ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
    wp_call halloc (28, 1, st); apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine sepWPp_alloc_post (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      fun halloc0 halign0 htr0 => ?_
    refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
      (by sep_focus) ?_; sep_elim_exists'
    refine SepWPp.fold (Entails.of_eq (incoming_alloc_split _)) (by sep_focus) ?_; sep_elim_exists'
    refine SepWPp.fold
      (Entails.of_eq (rodata_incoming_split1 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")))
      (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
    wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    apply sepWP_seg_ls_vm (Q := (blkPC_79).rebase (blkPl_79).base (hooksException H))
      blkLib_eq_79 (mid := s0.readReg64 Reg.lr)
    intro _m_strip; wp_steps
    refine SepWP.fold
      (Entails.of_eq (rodata_incoming_1_to_2 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")))
      (by sep_focus) ?_; wp_steps
    refine SepWP.fold
      (Entails.of_eq (rodata_incoming_split2 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")).symm)
      (by sep_focus) ?_
    refine SepWP.fold (incoming_overlap_prep _ _ _) (by sep_focus) ?_; sep_elim_exists'; wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by wp_norm_lhs)) (hnext := ?_)
    refine SepWP.fold (err28_badKem_payload_intro_placed A.repAlloc _ _ _ halloc0)
      (by dsimp only [RustCliAllocBudget.repAlloc]; sep_focus) ?_
    refine SepWP.fold
      (outPtr_badKem_err104_owned_merge_placed A.repAlloc (s0.readReg64 (.gpr 8#5))
        (speWord 24) 28#64 _ 28#64 _ (by decide)) (by sep_focus) ?_
    refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
    refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (pqsk_region_phaseA_merge s0.sp _) (by sep_focus) ?_
    refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
    · simp only [arm64_norm, *]
    refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
    have henv_out : AcceptBadKemEnv P inp (rustAllocEvents 28 1) := hevs_eq.symm
    clear h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy
    refine sepWP_instantiate_ro1_post_exists (rustAllocEvents 28 1) ?_
    simp only [sepConj_assoc, *]; wp_done
  · have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = true := hcanon_b
    have hcanon_keep : AcceptCanonTrue P inp := ⟨hcanon_b⟩
    simp only [hcanon_ec, ↓reduceIte] at *; clear hcanon_b hcanon_ec
    have hcanon_b : P.isCanonical inp.hdr.ekAPk = true := hcanon_keep.out; clear hcanon_keep
    have hfits192 : FitsEvents M lim st (rustAllocEvents 192 1) := by
      unfold acceptBadKemEvents at hfits_all; dsimp only at hfits_all
      simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfits_all
      by_cases hd1 : P.x25519 inp.spkBSk inp.hdr.ikAPk = List.replicate 32 0
      · simp only [hd1, ↓reduceIte] at hfits_all; exact fitsEvents_pfx hfits_all rfl
      · simp only [hd1, ↓reduceIte] at hfits_all
        by_cases hd2 : P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0
        · simp only [hd2, ↓reduceIte] at hfits_all
          exact fitsEvents_pfx hfits_all (by simp only [List.append_assoc]; rfl)
        · simp only [hd2, ↓reduceIte] at hfits_all
          by_cases hd3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0
          · simp only [hd3, ↓reduceIte] at hfits_all
            exact fitsEvents_pfx hfits_all (by simp only [List.append_assoc]; rfl)
          · simp only [hd3, ↓reduceIte] at hfits_all
            cases hopk_c : inp.opkBSk? <;> simp only [hopk_c] at hfits_all
            · exact fitsEvents_pfx hfits_all (by simp only [List.append_assoc]; rfl)
            · rename_i opkSk_c
              by_cases hd4 : P.x25519 opkSk_c inp.hdr.ekAPk = List.replicate 32 0 <;>
                simp only [hd4, ↓reduceIte] at hfits_all <;>
                exact fitsEvents_pfx hfits_all (by simp only [List.append_assoc]; rfl)
    rw [subStack_to_alloc s0.sp]
    refine of_sepWP_lsfull hF1 (mid := (blkPl_79).base + 72#64) ?_
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym); wp_call hshim ()
    refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrl192 : LibsignalBinary.Heap.RustLayoutOk 192 1 :=
      ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
    wp_call halloc (192, 1, st); apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2; try simp only [arm64_norm] at hF2
    refine sepWPp_alloc_post (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      fun halloc192 halign192 htr192 => ?_
    let st_192 := M.stepEvents (rustAllocEvents 192 1) st
    have hfits_ag1 :
        FitsEvents M lim st_192 (calculateAgreementEvents P inp.spkBSk inp.hdr.ikAPk) := by
      unfold acceptBadKemEvents at hfits_all; dsimp only at hfits_all
      simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfits_all
      by_cases hd1 : P.x25519 inp.spkBSk inp.hdr.ikAPk = List.replicate 32 0
      · exact of_eq_true (by
          simp only [calculateAgreementEvents, hd1, ↓reduceIte]
          exact LibsignalBinary.Heap.fitsEvents_nil M lim _)
      · simp only [calculateAgreementEvents, hd1, ↓reduceIte] at hfits_all ⊢
        by_cases hd2 : P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0
        · simp only [hd2, ↓reduceIte] at hfits_all
          exact fitsEvents_mid hfits_all (by simp only [List.append_assoc]; rfl)
        · simp only [hd2, ↓reduceIte] at hfits_all
          by_cases hd3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0
          · simp only [hd3, ↓reduceIte] at hfits_all
            exact fitsEvents_mid hfits_all (by simp only [List.append_assoc]; rfl)
          · simp only [hd3, ↓reduceIte] at hfits_all
            cases hopk_c : inp.opkBSk? <;> simp only [hopk_c] at hfits_all
            · exact fitsEvents_mid hfits_all (by simp only [List.append_assoc]; rfl)
            · rename_i opkSk_c
              by_cases hd4 : P.x25519 opkSk_c inp.hdr.ekAPk = List.replicate 32 0 <;>
                simp only [hd4, ↓reduceIte] at hfits_all <;>
                exact fitsEvents_mid hfits_all (by simp only [List.append_assoc]; rfl)
    refine SepWPp.fold (Entails.of_eq (memRegion_192_init_split _)) (by sep_focus) ?_
    sep_elim_exists'
    refine SepWPp.fold (Entails.of_eq (alloc_to_calc_stack s0.sp)) (by sep_focus) ?_
    refine of_sepWP_lsfull hF2 (mid := lsmpl.base 207) ?_
    wp_steps_sync_pool (lsmpl.base 207)
    refine SepWP.fold (Entails.of_eq (pointsTo64_4_allOnes_eq_F_X25519 _)) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF3; try simp only [arm64_norm] at hF3
    refine SepWPp_call_hag_placed hWF h_agree hF3.to_frozen
      (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
      (s0.readReg64 (.gpr 0#5) + 128#64) inp.hdr.ikAPk (by wp_norm_lhs) (by wp_norm_lhs) hsp_align
      (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 120#64) (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hikAPk, hfits_ag1⟩
      (by sep_focus)
      (fun hdh1 sf1 hi1 u2_1 hpc1 hrun1 hsp1 hcs1 htr1 _hfr1 => ?_)
      (fun hdh1 sf1 dh1_ptr hpc1 hrun1 hsp1 hcs1 htr1 hfr4 => ?_)
    · have hevs_eq :
          acceptBadKemEvents P inp = rustAllocEvents 192 1 ++ rustDeallocEvents 192 1 := by
        simp [acceptBadKemEvents, hcanon_b, hdh1]
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
      rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
        hcs29, hvregs1⟩
      simp only [arm64_norm]
        at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
      refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
        (by sep_focus) ?_; sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
      refine SepWPp.fold (vec_err_dh1_merge _) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
      wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call hdealloc (_, 192, 1, st_192)
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_badKem_err104_plain_merge_placed A.repAlloc 10 (by decide) (by decide)
          (s0.readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
      have hst_eq : M.stepEvents (rustDeallocEvents 192 1) st_192 =
          M.stepEvents (rustAllocEvents 192 1 ++ rustDeallocEvents 192 1) st := by
        dsimp only [st_192]; rw [← M.stepEvents_append]
      rw [hst_eq]
      have henv_out : AcceptBadKemEnv P inp (rustAllocEvents 192 1 ++ rustDeallocEvents 192 1) :=
        hevs_eq.symm
      clear h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy
      refine sepWP_instantiate_ro1_post_exists (rustAllocEvents 192 1 ++ rustDeallocEvents 192 1) ?_
      simp only [sepConj_assoc, *]; wp_done
    · have hF4 : LsFullFrozenInv lsmpl sf1 := LsFullFrozenInv.of_frozen hfr4
      have hdh1_len : (P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 32 := hWF.x25519_len _ _
      have hdh1_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)).length = 32 := by
        simp [bytesToBv8, hdh1_len]
      have hpfx1_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 64 := by
        simp [F_X25519, hdh1_len]
      let dhCycle := rustAllocEvents 32 1 ++ rustDeallocEvents 32 1
      let st_dh1_a := M.stepEvents (rustAllocEvents 32 1) st_192
      let st_dh1 := M.stepEvents (rustDeallocEvents 32 1) st_dh1_a
      have hst_dh1_eq : st_dh1 = M.stepEvents (rustAllocEvents 192 1 ++ dhCycle) st := by
        dsimp only [st_dh1, st_dh1_a, st_192, dhCycle]
        rw [← M.stepEvents_append, ← M.stepEvents_append]
      have hfits_ag2 :
          FitsEvents M lim st_dh1 (calculateAgreementEvents P inp.ikBSk inp.hdr.ekAPk) := by
        unfold acceptBadKemEvents at hfits_all
        simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1, ↓reduceIte] at hfits_all
        by_cases hd2 : P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0
        · exact of_eq_true (by
            simp only [calculateAgreementEvents, hd2, ↓reduceIte]
            exact LibsignalBinary.Heap.fitsEvents_nil M lim _)
        · simp only [calculateAgreementEvents, hd2, ↓reduceIte] at hfits_all ⊢
          rw [hst_dh1_eq]
          by_cases hd3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0
          · simp only [hd3, ↓reduceIte] at hfits_all
            exact fitsEvents_mid hfits_all (by simp only [dhCycle, List.append_assoc]; rfl)
          · simp only [hd3, ↓reduceIte] at hfits_all
            cases hopk_c : inp.opkBSk? <;> simp only [hopk_c] at hfits_all
            · exact fitsEvents_mid hfits_all (by simp only [dhCycle, List.append_assoc]; rfl)
            · rename_i opkSk
              by_cases hd4 : P.x25519 opkSk inp.hdr.ekAPk = List.replicate 32 0 <;>
                simp only [hd4, ↓reduceIte] at hfits_all <;>
                exact fitsEvents_mid hfits_all (by simp only [dhCycle, List.append_assoc]; rfl)
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
      rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
        hcs29, hvregs1⟩
      simp only [arm64_norm]
        at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
      refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
      refine of_sepWP_lsfull hF4 (mid := lsmpl.base 207) ?_
      wp_steps_sync_pool (lsρ lsMemcpySym)
      wp_call hmemcpy ⟨_, dh1_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)⟩
      refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
      wp_steps_sync_pool (lsρ acceptRustDeallocSym)
      refine SepWP.fold (hdh1_bv_len ▸ pointsToBytes_entails_memRegion dh1_ptr _) (by sep_focus) ?_
      wp_call hdealloc (dh1_ptr, 32, 1, st_dh1_a); wp_steps_sync_pool (lsmpl.base 207)
      refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh1_ptr 32#64) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ F_X25519 (P.x25519 inp.spkBSk
        inp.hdr.ikAPk) 32 (by decide))) (by sep_focus) ?_
      refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF5; try simp only [arm64_norm] at hF5
      refine SepWPp_call_hag_placed hWF h_agree hF5.to_frozen
        (s0.readReg64 (.gpr 0#5) + 32#64) inp.ikBSk
        (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
        (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
        (ret_pc := (blkPl_79).base + 304#64) (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hikBSk, hekAPk, hfits_ag2⟩
        (by sep_focus)
        (fun hdh2 sf2 hi2 u2_2 hpc2 hrun2 hsp2 hcs2 htr2 _hfr2 => ?_)
        (fun hdh2 sf2 dh2_ptr hpc2 hrun2 hsp2 hcs2 htr2 hfr6 => ?_)
      · have hevs_eq : acceptBadKemEvents P inp =
            rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1 := by
          simp only [acceptBadKemEvents, hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1, hdh2,
            ↓reduceIte, dhCycle]
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
        rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
          hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
        simp only [arm64_norm]
          at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
             hcs2_29 hvregs2
        refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
          (by sep_focus) ?_; sep_elim_exists'
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.fold (vec_err_dh2_merge _ hpfx1_len) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
        wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call hdealloc (_, 192, 1, st_dh1)
        wp_steps_sync_pool (s0.readReg64 Reg.lr)
        refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
        refine SepWP.fold
          (outPtr_badKem_err104_plain_merge_placed A.repAlloc 10 (by decide) (by decide)
            (s0.readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
        have hst_eq : M.stepEvents (rustDeallocEvents 192 1) st_dh1 =
            M.stepEvents (rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1) st := by
          rw [hst_dh1_eq, ← M.stepEvents_append]
        rw [hst_eq]
        have henv_out :
            AcceptBadKemEnv P inp (rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1) :=
          hevs_eq.symm
        clear h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy
        refine sepWP_instantiate_ro1_post_exists
          (rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1) ?_
        simp only [sepConj_assoc, *]; wp_done
      · have hF6 : LsFullFrozenInv lsmpl sf2 := LsFullFrozenInv.of_frozen hfr6
        have hdh2_len : (P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
        have hdh2_bv_len : (bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)).length = 32 := by
          simp [bytesToBv8, hdh2_len]
        have hpfx2_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
          P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 96 := by simp [F_X25519, hdh1_len, hdh2_len]
        let st_dh2_a := M.stepEvents (rustAllocEvents 32 1) st_dh1
        let st_dh2 := M.stepEvents (rustDeallocEvents 32 1) st_dh2_a
        have hst_dh2_eq :
            st_dh2 = M.stepEvents (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle) st := by
          dsimp only [st_dh2, st_dh2_a]; rw [hst_dh1_eq, ← M.stepEvents_append, ← M.stepEvents_append]
        have hfits_ag3 :
            FitsEvents M lim st_dh2 (calculateAgreementEvents P inp.spkBSk inp.hdr.ekAPk) := by
          unfold acceptBadKemEvents at hfits_all
          simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1, hdh2, ↓reduceIte]
            at hfits_all
          by_cases hd3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0
          · exact of_eq_true (by
              simp only [calculateAgreementEvents, hd3, ↓reduceIte]
              exact LibsignalBinary.Heap.fitsEvents_nil M lim _)
          · simp only [calculateAgreementEvents, hd3, ↓reduceIte] at hfits_all ⊢
            rw [hst_dh2_eq]
            cases hopk_c : inp.opkBSk? <;> simp only [hopk_c] at hfits_all
            · exact fitsEvents_mid hfits_all (by simp only [dhCycle, List.append_assoc]; rfl)
            · rename_i opkSk
              by_cases hd4 : P.x25519 opkSk inp.hdr.ekAPk = List.replicate 32 0 <;>
                simp only [hd4, ↓reduceIte] at hfits_all <;>
                exact fitsEvents_mid hfits_all (by simp only [dhCycle, List.append_assoc]; rfl)
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
        rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
          hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
        simp only [arm64_norm]
          at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
             hcs2_29 hvregs2
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine of_sepWP_lsfull hF6 (mid := lsmpl.base 207) ?_
        wp_steps_sync_pool (lsρ lsMemcpySym)
        wp_call hmemcpy ⟨_, dh2_ptr, bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)⟩
        refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
        wp_steps_sync_pool (lsρ acceptRustDeallocSym)
        refine SepWP.fold (hdh2_bv_len ▸ pointsToBytes_entails_memRegion dh2_ptr _)
          (by sep_focus) ?_
        wp_call hdealloc (dh2_ptr, 32, 1, st_dh2_a); wp_steps_sync_pool (lsmpl.base 207)
        refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh2_ptr 32#64)
          (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
          P.x25519 inp.spkBSk inp.hdr.ikAPk) (P.x25519 inp.ikBSk inp.hdr.ekAPk) 64
          (by simp only [bytesToBv8, List.length_map, hpfx1_len]))) (by sep_focus) ?_
        refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF7; try simp only [arm64_norm] at hF7
        refine SepWPp_call_hag_placed hWF h_agree hF7.to_frozen
          (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
          (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
          (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
          (ret_pc := (blkPl_79).base + 404#64) (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hekAPk,
            hfits_ag3⟩ (by sep_focus)
          (fun hdh3 sf3 hi3 u2_3 hpc3 hrun3 hsp3 hcs3 htr3 _hfr3 => ?_)
          (fun hdh3 sf3 dh3_ptr hpc3 hrun3 hsp3 hcs3 htr3 hfr8 => ?_)
        · have hevs_eq : acceptBadKemEvents P inp =
              rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1 := by
            simp only [acceptBadKemEvents, hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1,
              hdh2, hdh3, ↓reduceIte, dhCycle]
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
          rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
            hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
          simp only [arm64_norm]
            at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
               hcs3_29 hvregs3
          refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
            (by sep_focus) ?_; sep_elim_exists'
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.fold (vec_err_dh3_merge _ hpfx2_len) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
          wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call hdealloc (_, 192, 1, st_dh2)
          wp_steps_sync_pool (s0.readReg64 Reg.lr)
          refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
          refine SepWP.fold
            (outPtr_badKem_err104_plain_merge_placed A.repAlloc 10 (by decide) (by decide)
              (s0.readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
          have hst_eq : M.stepEvents (rustDeallocEvents 192 1) st_dh2 =
              M.stepEvents
                (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1) st := by
            rw [hst_dh2_eq, ← M.stepEvents_append]
          rw [hst_eq]
          have henv_out : AcceptBadKemEnv P inp
              (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1) :=
            hevs_eq.symm
          clear h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy
          refine sepWP_instantiate_ro1_post_exists
            (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1) ?_
          simp only [sepConj_assoc, *]; wp_done
        · have hF8 : LsFullFrozenInv lsmpl sf3 := LsFullFrozenInv.of_frozen hfr8
          have hdh3_len : (P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
          have hdh3_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)).length = 32 := by
            simp [bytesToBv8, hdh3_len]
          have hpfx3_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
            P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 128 :=
            by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len]
          let st_dh3_a := M.stepEvents (rustAllocEvents 32 1) st_dh2
          let st_dh3 := M.stepEvents (rustDeallocEvents 32 1) st_dh3_a
          have hst_dh3_eq : st_dh3 =
              M.stepEvents (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle) st := by
            dsimp only [st_dh3, st_dh3_a]
            rw [hst_dh2_eq, ← M.stepEvents_append, ← M.stepEvents_append]
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
            have hfits_ag4 :
                FitsEvents M lim st_dh3 (calculateAgreementEvents P opkSk inp.hdr.ekAPk) := by
              unfold acceptBadKemEvents at hfits_all
              simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1, hdh2, hdh3, hopk_eq,
                ↓reduceIte] at hfits_all
              by_cases hd4 : P.x25519 opkSk inp.hdr.ekAPk = List.replicate 32 0
              · exact of_eq_true (by
                  simp only [calculateAgreementEvents, hd4, ↓reduceIte]
                  exact LibsignalBinary.Heap.fitsEvents_nil M lim _)
              · simp only [calculateAgreementEvents, hd4, ↓reduceIte] at hfits_all ⊢
                rw [hst_dh3_eq]
                exact fitsEvents_mid hfits_all (by simp only [dhCycle, List.append_assoc]; rfl)
            simp only [↓reduceIte]
            refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
            refine of_sepWP_lsfull hF8 (mid := lsmpl.base 207) ?_
            wp_steps_sync_pool (lsρ lsMemcpySym)
            wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩
            refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
            wp_steps_sync_pool (lsρ acceptRustDeallocSym)
            refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
              (by sep_focus) ?_; wp_call hdealloc (dh3_ptr, 32, 1, st_dh3_a)
            refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            wp_steps_sync_pool (lsmpl.base 207)
            refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh3_ptr 32#64)
              (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _
              (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk)
              (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
              (by simp only [bytesToBv8, List.length_map, hpfx2_len]))) (by sep_focus) ?_
            refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hF8_1; try simp only [arm64_norm] at hF8_1
            refine SepWPp_call_hag_placed hWF h_agree hF8_1.to_frozen
              (s0.readReg64 (.gpr 0#5) + 265#64) opkSk
              (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
              (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 720#64)
              (by wp_norm_lhs) (by wp_norm_lhs)
              ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hopkSk, hekAPk,
                hfits_ag4⟩ (by sep_focus)
              (fun hdh4 sf4 hi4 u2_4 hpc4 hrun4 hsp4 hcs4 htr4 _hfr4 => ?_)
              (fun hdh4 sf4 dh4_ptr hpc4 hrun4 hsp4 hcs4 htr4 hfr8_2 => ?_)
            · have hevs_eq : acceptBadKemEvents P inp =
                  rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++
                    rustDeallocEvents 192 1 := by
                simp only [acceptBadKemEvents, hcanon_b, Bool.not_true, Bool.false_eq_true,
                  hdh1, hdh2, hdh3, hopk_eq, hdh4, ↓reduceIte, dhCycle]
              dsimp only [CalleeSavedPreserved, Reg.fp] at hcs4
              rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25,
                hcs4_26, hcs4_27, hcs4_28, hcs4_29, hvregs4⟩
              simp only [arm64_norm]
                at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27
                   hcs4_28 hcs4_29 hvregs4
              refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
                (by sep_focus) ?_; sep_elim_exists'
              refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
              refine SepWPp.fold (vec_err_dh4_merge _ hpfx3_len) (by sep_focus) ?_
              apply SepWPp.of_sepWP_ret
              wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call hdealloc (_, 192, 1, st_dh3)
              wp_steps_sync_pool (s0.readReg64 Reg.lr)
              refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
              refine SepWP.fold
                (outPtr_badKem_err104_plain_merge_placed A.repAlloc 10 (by decide) (by decide)
                  (s0.readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
              refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
              refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
              refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
              refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
                (by sep_focus) ?_
              have hst_eq : M.stepEvents (rustDeallocEvents 192 1) st_dh3 =
                  M.stepEvents
                    (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++
                      rustDeallocEvents 192 1) st := by
                rw [hst_dh3_eq, ← M.stepEvents_append]
              rw [hst_eq]
              have henv_out : AcceptBadKemEnv P inp
                  (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++
                    rustDeallocEvents 192 1) := hevs_eq.symm
              clear h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy
              refine sepWP_instantiate_ro1_post_exists
                (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++
                  rustDeallocEvents 192 1) ?_
              simp only [sepConj_assoc, *]; wp_done
            · have hF8_2 : LsFullFrozenInv lsmpl sf4 := LsFullFrozenInv.of_frozen hfr8_2
              have hdh4_len : (P.x25519 opkSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
              have hdh4_bv_len : (bytesToBv8 (P.x25519 opkSk inp.hdr.ekAPk)).length = 32 := by
                simp [bytesToBv8, hdh4_len]
              have hpfx4_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                P.x25519 opkSk inp.hdr.ekAPk).length = 160 := by
                simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, hdh4_len]
              let st_dh4_a := M.stepEvents (rustAllocEvents 32 1) st_dh3
              let st_dh4 := M.stepEvents (rustDeallocEvents 32 1) st_dh4_a
              have hst_dh4_eq : st_dh4 =
                  M.stepEvents
                    (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle) st := by
                dsimp only [st_dh4, st_dh4_a]
                rw [hst_dh3_eq, ← M.stepEvents_append, ← M.stepEvents_append]
              have hevs_eq : acceptBadKemEvents P inp =
                  rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
                    rustDeallocEvents 192 1 := by
                simp only [acceptBadKemEvents, hcanon_b, Bool.not_true, Bool.false_eq_true,
                  hdh1, hdh2, hdh3, hopk_eq, hdh4, ↓reduceIte, dhCycle]
              have hst_fin4 : M.stepEvents (rustDeallocEvents 192 1) st_dh4 =
                  M.stepEvents
                    (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
                      rustDeallocEvents 192 1) st := by
                rw [hst_dh4_eq, ← M.stepEvents_append]
              have henv_out4 : AcceptBadKemEnv P inp
                  (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
                    rustDeallocEvents 192 1) := hevs_eq.symm
              dsimp only [CalleeSavedPreserved, Reg.fp] at hcs4
              rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25,
                hcs4_26, hcs4_27, hcs4_28, hcs4_29, hvregs4⟩
              simp only [arm64_norm]
                at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27
                   hcs4_28 hcs4_29 hvregs4
              refine SepWPp.fold (Entails.of_eq (calc_to_vecAppend_stack s0.sp)) (by sep_focus) ?_
              refine of_sepWP_lsfull hF8_2 (mid := lsmpl.base 55) ?_
              wp_steps_sync_pool (lsmpl.base 55); apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              intro hF8_3; try simp only [arm64_norm] at hF8_3
              refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
                (by sep_focus) ?_; sep_elim_exists'; apply SepWPp.of_sepWP_ret
              have hvec0 := subroutine_ok_withMemEq_of_withCodeLoaded
                (spec := pqxdhVecAppendElementsFastSpec) h_vec_append hF8_3.code
              simp only [pqxdhVecAppendElementsFastSpec, withVmPreserved,
                CryptoVerification.E2E.Pqxdh.Shared.pqxdhVecAppendElementsFastSpec] at hvec0
              wp_call hvec0
                (s0.sp - 4936#64, _, dh4_ptr, bytesToBv8 (P.x25519 opkSk inp.hdr.ekAPk))
              refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
              refine SepWP.fold (vecAppend_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              wp_steps_sync_pool (lsρ acceptRustDeallocSym)
              refine SepWP.fold (hdh4_bv_len ▸ pointsToBytes_entails_memRegion dh4_ptr _)
                (by sep_focus) ?_; wp_call hdealloc (dh4_ptr, 32, 1, st_dh4_a)
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _
                (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk)
                (P.x25519 opkSk inp.hdr.ekAPk) 128
                (by simp only [bytesToBv8, List.length_map, hpfx3_len]))) (by sep_focus) ?_
              refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp 0#64 dh4_ptr 32#64 0#64)
                (by sep_focus) ?_
              refine SepWP.fold (vec_ok_160_merge _ hpfx4_len) (by sep_focus) ?_
              let evs_out4 :=
                rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
                  rustDeallocEvents 192 1
              badkem_ct_exit_placed s0 A ctBufPtr hbadKem hct_bd
                h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy st_dh4
                evs_out4 hst_fin4 henv_out4

end LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxB
