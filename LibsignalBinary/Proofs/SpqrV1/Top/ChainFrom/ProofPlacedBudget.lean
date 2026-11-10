/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.ProofPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
meta import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Verification of `spqr::chain_from` (Block `323`)

Proves `RustCliAllocBudget` `ChainFromPlacedOkX` for `spqr::chain_from` (Block `323`, 76 instructions)
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.ProofPlacedBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
  (ChainNewEnv chainNewSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (ChainFromEnv chainFromPbSpecX chainFromSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsPlacedBudget
  (ChainFromPlacedOkX ChainFromPbPlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.ProofPlacedBudget
  (call_frame_lsCallInv)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (Chain HkdfFn VersionNegotiationPB chainFrom chainFromVersionNegotiation)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainNewGhost bytesAt chainEpochAlign chainEpochSize chainNewStackX chainNewVal)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
  (LsCallInv SepWP.seq_lsCallInv withLsCallInv)
open CryptoVerification.SpqrV1.Top.ChainFrom
  (ChainFromCall ChainFromPbCall chainFromPbStackX chainFromStackX chainPBAt
   optChainPBAt optVersionNegotiationRefAt)
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
  (add_one_beq_zero_of_ne_noneCap chainErrorAt_pack_words4 chainErrorAt_unpack_words4
   chainPBAt_expose_cap chainPBAt_unexpose_cap chainRepr_entails_words11
   extractLsb_hi_append64 extractLsb_lo_append64 memRegion_88_words11
   memRegion_88_words4_rest stackAt_chainFrom_join stackAt_chainFrom_split
   stackAt_chainFrom_split_chainNew word_rest72_to_memRegion_80
   words11_entails_chainRepr words11_to_memRegion_88 words4_rest_to_memRegion_88)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
  (chainResultAt noneCap optChainParamsPBAt versionNegotiationPBAt)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm
  (chainNew_post_entails_chainRepr direction_fromI32_or fold_chainErrorAt
   header_bytesAt_rest_entails_vecU8At memRegion_88_err_split
   readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
   readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre ult_one_toI32
   vecU8At_entails_header_bytesAt_rest vecU8BufRest)
open CryptoVerification.SpqrV1.Top.Placed
  (blkPC_323 blkPl_323)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  ult_one_toI32
  extractLsb_lo_append64 extractLsb_hi_append64

local macro "wp_elim_exists" : tactic =>
  `(tactic| repeat' (apply SepWP.exists_elim; intro _))

private theorem align_pre {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

private theorem sepWP_rw_pre {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

private theorem calleeSavedPreserved_trans {s0 s1 sf : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 sf) :
    CalleeSavedPreserved s0 sf := by
  unfold CalleeSavedPreserved at h01 h12 ⊢
  rcases h01 with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hv⟩
  rcases h12 with ⟨k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, kv⟩
  exact ⟨k19.trans h19, k20.trans h20, k21.trans h21, k22.trans h22, k23.trans h23,
    k24.trans h24, k25.trans h25, k26.trans h26, k27.trans h27, k28.trans h28,
    k29.trans h29, kv.trans hv⟩

/-- High callee-saved registers (`x20..x28` + SIMD `d8..d15`) untouched in registers by `Block 323`. -/
private def ChainFromHighCS (s0 s : State) : Prop :=
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem chainFromHighCS_of_cs {s0 s1 sf : State}
    (h01 : ChainFromHighCS s0 s1) (hcs : CalleeSavedPreserved s1 sf) :
    ChainFromHighCS s0 sf := by
  rcases h01 with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, hv⟩
  unfold CalleeSavedPreserved at hcs
  rcases hcs with ⟨_, k20, k21, k22, k23, k24, k25, k26, k27, k28, _, kv⟩
  exact ⟨k20.trans h20, k21.trans h21, k22.trans h22, k23.trans h23,
    k24.trans h24, k25.trans h25, k26.trans h26, k27.trans h27, k28.trans h28, kv.trans hv⟩

private theorem sepWP_seq_lsCallInv_vm {prog : Program} {pl : Obj.MultiPlacement}
    {mid target_pc : BitVec 64} {s : State} {P P_mid : SepProp}
    {Q : State → Prop} {post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LsCallInv pl sm.mem → VmPreserved s sm → Q sm →
      SepWP prog target_pc sm P_mid post) :
    SepWP prog target_pc s P post :=
  SepWP.seq_lsCallInv hF (SepWP.mono h1 fun sm _ hpcm hrunm ⟨hvm, hent, hQ⟩ hFm =>
    SepWP.weaken_pre hent (h2 sm hpcm hrunm hFm hvm hQ))

private theorem sepWP_chainFrom_finish [LibsignalPlacement]
    {hkdf : HkdfFn} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {call : ChainFromCall} {st : M.σ} {evs : List AllocEvent}
    (hevs : ChainFromEnv call.pb call.vn evs)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withLsCallInv lsmpl (chainFromSpecX hkdf M A lim)).post
          (call, st) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hwp : SepWP ((blkPC_323).rebase (blkPl_323).base H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        VmPreserved s sf ∧
        (P_f ⊢
          chainResultAt A.repAlloc call.out (chainFrom hkdf call.pb call.vn) ∗
          memRegion call.pbPtr 80 ∗
          optVersionNegotiationRefAt A.repAlloc call.vnPin call.vnOptPtr call.vn ∗
          A.pool lim (M.stepEvents evs st) s ∗
          stackAt s0.sp chainFromStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWP ((blkPC_323).rebase (blkPl_323).base H) (s0.readReg64 .lr) s P post := by
  subst hpost
  refine SepWP.mono hwp ?_
  intro sf P_f _ _ ⟨hvm, hent, hspf, hcsf, htrf⟩
  refine ⟨fun hmR => ?_, hspf, hcsf⟩
  have hm1 := Satisfies.mono (sepConj_mono_left hent) hmR
  rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents evs st) hvm] at hm1
  dsimp only [withLsCallInv, chainFromSpecX]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htrf, hevs⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1⟩

private theorem pack_exists64 (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ ∃∗ g : BitVec 64, a ↦₆₄ g :=
  Entails.sepExists_right v (Entails.refl _)

private theorem sepWP_chainFrom_finish_vn_none [LibsignalPlacement]
    {hkdf : HkdfFn} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {call : ChainFromCall} {st : M.σ} {evs : List AllocEvent}
    (hevs : ChainFromEnv call.pb call.vn evs)
    (hvn : call.vn = none) (hvn0 : call.vnOptPtr = 0#64)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withLsCallInv lsmpl (chainFromSpecX hkdf M A lim)).post
          (call, st) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hwp : SepWP ((blkPC_323).rebase (blkPl_323).base H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        VmPreserved s sf ∧
        (P_f ⊢
          chainResultAt A.repAlloc call.out (chainFrom hkdf call.pb call.vn) ∗
          memRegion call.pbPtr 80 ∗
          A.pool lim (M.stepEvents evs st) s ∗
          stackAt s0.sp chainFromStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWP ((blkPC_323).rebase (blkPl_323).base H) (s0.readReg64 .lr) s P post := by
  apply sepWP_chainFrom_finish hevs hpost
  refine SepWP.mono hwp fun sf P_f _ _ ⟨hvm, hent, hspf, hcsf, htrf⟩ => ⟨hvm, ?_, hspf, hcsf, htrf⟩
  rw [hvn] at hent ⊢
  dsimp only [optVersionNegotiationRefAt]
  exact Entails.trans (Entails.pure_right hvn0 hent) (Entails.of_eq (by ac_rfl))

private theorem sepWP_chainFrom_finish_vn_some [LibsignalPlacement]
    {hkdf : HkdfFn} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {call : ChainFromCall} {v : VersionNegotiationPB} {st : M.σ} {evs : List AllocEvent}
    (hevs : ChainFromEnv call.pb call.vn evs)
    (hvn : call.vn = some v) (hvn_ne : call.vnOptPtr ≠ 0#64)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withLsCallInv lsmpl (chainFromSpecX hkdf M A lim)).post
          (call, st) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hwp : SepWP ((blkPC_323).rebase (blkPl_323).base H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        VmPreserved s sf ∧
        (P_f ⊢
          chainResultAt A.repAlloc call.out (chainFrom hkdf call.pb call.vn) ∗
          memRegion call.pbPtr 80 ∗
          versionNegotiationPBAt A.repAlloc call.vnPin call.vnOptPtr v ∗
          A.pool lim (M.stepEvents evs st) s ∗
          stackAt s0.sp chainFromStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWP ((blkPC_323).rebase (blkPl_323).base H) (s0.readReg64 .lr) s P post := by
  apply sepWP_chainFrom_finish hevs hpost
  refine SepWP.mono hwp fun sf P_f _ _ ⟨hvm, hent, hspf, hcsf, htrf⟩ => ⟨hvm, ?_, hspf, hcsf, htrf⟩
  rw [hvn] at hent ⊢
  dsimp only [optVersionNegotiationRefAt]
  exact Entails.trans (Entails.pure_right hvn_ne hent) (Entails.of_eq (by ac_rfl))

private theorem sp_sub_144_aligned (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 144#64) &&& 15#64 == 0#64) = true := by
  rw [beq_iff_eq] at h ⊢
  bv_kernel

set_option maxHeartbeats 1600000 in
/-- Relocatable `spqr::chain_from` (Block `323`, 76 instructions) meets
`withLsCallInv lsmpl (chainFromSpecX hkdf M A lim)`. -/
theorem chainFrom_placed_ok_of_contracts_x [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_from_pb : subroutine_ok ((blkPC_323).rebase (blkPl_323).base H)
      (lsmpl.base 364) (withLsCallInv lsmpl (chainFromPbSpecX M A lim)))
    (h_new : subroutine_ok ((blkPC_323).rebase (blkPl_323).base H)
      (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX hkdf M A lim))) :
    subroutine_ok ((blkPC_323).rebase (blkPl_323).base H)
      (blkPl_323).base
      (withLsCallInv lsmpl (chainFromSpecX hkdf M A lim)) := by
  apply subroutine_ok_of_sepWP_init
  intro ⟨⟨out, pbPtr, vnOptPtr, gPb, vnPin, pb, vn⟩, st⟩ R s0 hpc hrun hpre0 hsp0
  dsimp only [withLsCallInv, chainFromSpecX, Reg.x0, Reg.x1, Reg.x2] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨hinv0, hpre0⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hfits⟩, hpre0⟩
  refine ⟨_, hpre0, ?_⟩
  subst hx0 hx1 hx2
  refine sepWP_rw_pre (by
    simp only [stackAt_chainFrom_split s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right]
    rfl) ?_
  wp_elim_exists
  cases pb with
  | some chainPb =>
    have hcf_eq : chainFrom hkdf (some chainPb) vn = Chain.fromPb chainPb := rfl
    dsimp only [optChainPBAt]
    refine SepWP.fold (chainPBAt_expose_cap A.repAlloc gPb (s0.readReg64 (.gpr 1#5)) chainPb)
      (by sep_focus) ?_
    refine SepWP.focus_pure (by sep_focus) fun hcap_ne => ?_
    have hz_cap : (gPb.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ne
    let P_call_pb : SepProp :=
      memRegion (s0.sp - 120#64) 88 ∗
      chainPBAt A.repAlloc gPb (s0.readReg64 (.gpr 1#5)) chainPb ∗
      A.pool lim st s0 ∗
      stackAt (s0.sp - 144#64) chainFromPbStackX ∗
      memRegion (s0.readReg64 (.gpr 0#5)) 88 ∗
      optVersionNegotiationRefAt A.repAlloc vnPin (s0.readReg64 (.gpr 2#5)) vn ∗
      (∃∗ g0' : BitVec 64, (s0.sp - 144#64) ↦₆₄ g0') ∗
      (∃∗ g1' : BitVec 64, (s0.sp - 136#64) ↦₆₄ g1') ∗
      (∃∗ g2' : BitVec 64, (s0.sp - 128#64) ↦₆₄ g2') ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      memRegion (s0.sp - 8#64) 8
    refine sepWP_seq_lsCallInv_vm (mid := lsmpl.base 364) (P_mid := P_call_pb)
      (Q := fun s1 =>
        s1.sp = s0.sp - 144#64 ∧
        s1.trace = s0.trace ∧
        s1.readReg64 .x8 = s0.sp - 120#64 ∧
        s1.readReg64 .x0 = s0.readReg64 (.gpr 1#5) ∧
        s1.readReg64 .lr = (blkPl_323).base + 44#64 ∧
        s1.readReg64 .x19 = s0.readReg64 (.gpr 0#5) ∧
        ChainFromHighCS s0 s1)
      hinv0 ?_ ?_
    · by_vm_steps (
        wp_steps
        refine SepWP.fold
          (chainPBAt_unexpose_cap A.repAlloc gPb (s0.readReg64 (.gpr 1#5)) chainPb)
          (by sep_focus) ?_
        refine SepWP.fold (pack_exists64 (s0.sp - 144#64) _) (by sep_focus) ?_
        refine SepWP.fold (pack_exists64 (s0.sp - 136#64) _) (by sep_focus) ?_
        refine SepWP.fold (pack_exists64 (s0.sp - 128#64) _) (by sep_focus) ?_
        dsimp only [P_call_pb, ChainFromHighCS, Reg.fp, Reg.lr, Reg.x19]
        refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) ⟨by wp_norm_goal,
          Entails.of_eq (by ac_rfl), ?_⟩
        simp only [Reg.x8, Reg.x0, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
          Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, wp_norm, arm64_norm, and_self]
      )
    · intro s1 hpc1 hrun1 hinv1 hvm01 ⟨hsp1, htr1, hx8_1, hx0_1, hlr1, hx19_1, hhcs1⟩
      have hsp1_align : s1.spAligned = true := by
        dsimp only [State.spAligned] at hsp0 ⊢
        rw [hsp1]
        exact sp_sub_144_aligned s0.sp hsp0
      dsimp only [P_call_pb]
      rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm01]
      apply (call_frame_lsCallInv h_from_pb
        ((⟨s0.sp - 120#64, s0.readReg64 (.gpr 1#5), gPb, chainPb⟩ : ChainFromPbCall), st)
        hinv1 (callee_ret_pc := (blkPl_323).base + 44#64))
      · exact hpc1
      · exact hrun1
      · exact hsp1_align
      · exact hlr1
      · rfl
      · exact ⟨hx8_1, hx0_1, by
          rw [hlr1]
          exact lsRetAddr624_blockPlacement_base_add 323 44#64 (by decide) (by decide)⟩
      · rw [hsp1]; sep_focus
      · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
        dsimp only [chainFromPbSpecX]
        rw [hsp1]
        have hsp_sf' : sf.sp = s0.sp - 144#64 := hsp_sf.trans hsp1
        have hx19_sf : sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 0#5) :=
          hcs_sf.1.trans hx19_1
        have hhcs_sf : ChainFromHighCS s0 sf := chainFromHighCS_of_cs hhcs1 hcs_sf
        rcases hhcs_sf with ⟨hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf, hx25_sf,
          hx26_sf, hx27_sf, hx28_sf, hv_sf⟩
        rw [sepExists_sepConj_left]
        apply SepWP.exists_elim; intro evs
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        wp_elim_exists
        refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
        rcases hpure with ⟨htr_sf, hevs_free⟩
        have htr_sf' : sf.trace = s0.trace := htr_sf.trans htr1
        have hevs_cf : ChainFromEnv (some chainPb) vn evs := hevs_free
        cases hres : Chain.fromPb chainPb with
        | ok ch =>
          dsimp only [chainResultAt]
          refine SepWP.fold (chainRepr_entails_words11 A.repAlloc (s0.sp - 120#64) ch)
            (by sep_focus) ?_
          refine sepWP_rw_pre (by
            simp only [sepExists_sepConj_left, sepConj_assoc]
            rfl) ?_
          apply SepWP.exists_elim; intro G
          apply SepWP.exists_elim; intro pad
          refine SepWP.focus_pure (by sep_focus) fun hcap_ch_ne => ?_
          have hz_ch : (G.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ch_ne
          refine sepWP_rw_pre (by
            simp only [memRegion_88_words11 (s0.readReg64 (.gpr 0#5)),
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            rfl) ?_
          wp_elim_exists
          apply sepWP_chainFrom_finish
            (call := ⟨s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5),
              s0.readReg64 (.gpr 2#5), gPb, vnPin, some chainPb, vn⟩)
            hevs_cf rfl
          rw [hcf_eq, hres]
          conv =>
            arg 5
            ext sf P_f
            dsimp only [chainResultAt]
          by_vm_steps (
            wp_steps
            refine SepWP.fold (words11_entails_chainRepr A.repAlloc (s0.readReg64 (.gpr 0#5)) G ch pad)
              (by sep_focus) ?_
            refine SepWP.fold (words11_to_memRegion_88 (s0.sp - 120#64)
              G.linksCap G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
              G.nextRoot.cap G.nextRoot.ptr (BitVec.ofNat 64 ch.nextRoot.length)
              ch.currentEpoch ch.sendEpoch (ch.params.maxOooKeys ++ ch.params.maxJump)
              (pad ++ ch.dir.toI32)) (by sep_focus) ?_
            refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
            refine align_pre (by sep_ac_rfl) ?_
            wp_done
          )
        | error err =>
          dsimp only [chainResultAt]
          refine sepWP_rw_pre (by
            simp only [chainErrorAt_unpack_words4 (s0.sp - 120#64) err,
              sepExists_sepConj_left, sepConj_assoc]
            rfl) ?_
          apply SepWP.exists_elim; intro q0_err
          apply SepWP.exists_elim; intro w3_err
          refine sepWP_rw_pre (by
            simp only [memRegion_88_words4_rest (s0.readReg64 (.gpr 0#5)),
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            rfl) ?_
          wp_elim_exists
          refine SepWP.focus_pure (by sep_focus) fun htag_q0 => ?_
          refine sepWP_rw_pre (by simp only [noneCap]; rfl) ?_
          apply sepWP_chainFrom_finish
            (call := ⟨s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5),
              s0.readReg64 (.gpr 2#5), gPb, vnPin, some chainPb, vn⟩)
            hevs_cf rfl
          rw [hcf_eq, hres]
          conv =>
            arg 5
            ext sf P_f
            dsimp only [chainResultAt]
          by_vm_steps (
            wp_steps
            refine SepWP.fold
              (chainErrorAt_pack_words4 (s0.readReg64 (.gpr 0#5)) err q0_err w3_err htag_q0)
              (by sep_focus) ?_
            refine SepWP.fold (words4_rest_to_memRegion_88 (s0.sp - 120#64)
              _ (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err)
              (by sep_focus) ?_
            refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
            refine align_pre (by sep_ac_rfl) ?_
            wp_done
          )
  | none =>
    dsimp only [optChainPBAt, noneCap]
    cases vn with
    | none =>
      have hcf_eq : chainFrom hkdf none none = .error .chainNotAvailable := rfl
      have hevs_cf : ChainFromEnv none none [] := rfl
      dsimp only [optVersionNegotiationRefAt]
      refine SepWP.focus_pure (by sep_focus) fun hvn0 => ?_
      refine sepWP_rw_pre (by
        simp only [memRegion_88_err_split (s0.readReg64 (.gpr 0#5)),
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        rfl) ?_
      apply SepWP.exists_elim; intro w2_out
      apply SepWP.exists_elim; intro w1_out
      apply SepWP.exists_elim; intro bs7_out
      apply SepWP.exists_elim; intro b0_out
      apply SepWP.exists_elim; intro w0_out
      refine SepWP.focus_pure (by sep_focus) fun hbs7 => ?_
      apply sepWP_chainFrom_finish_vn_none
        (call := ⟨s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5),
          s0.readReg64 (.gpr 2#5), gPb, vnPin, none, none⟩)
        hevs_cf rfl hvn0 rfl
      rw [hcf_eq]
      conv =>
        arg 5
        ext sf P_f
        dsimp only [chainResultAt]
      by_vm_steps (
        wp_steps
        refine SepWP.fold
          (fold_chainErrorAt (s0.readReg64 (.gpr 0#5)) .chainNotAvailable 15#8 rfl hbs7 w1_out w2_out)
          (by sep_focus) ?_
        refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) _)
          (by sep_focus) ?_
        refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
        refine align_pre (by sep_ac_rfl) ?_
        wp_done
      )
    | some v =>
      dsimp only [optVersionNegotiationRefAt, versionNegotiationPBAt]
      refine SepWP.focus_pure (by sep_focus) fun hvn_ne => ?_
      rcases direction_fromI32_or v.direction with
        ⟨dir, hdir_val, hdir_opt, hcond_hi⟩ | ⟨hdir_opt, hcond_hi⟩
      · cases hcp : v.chainParams with
        | none =>
          have hcf_eq : chainFrom hkdf none (some v) = .error .chainNotAvailable := by
            simp [chainFrom, chainFromVersionNegotiation, hdir_opt, hcp]; rfl
          have hevs_cf : ChainFromEnv none (some v) [] := by
            simp [ChainFromEnv,
              LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget.ChainFromVersionNegotiationEnv,
              hdir_opt, hcp]
          conv =>
            arg 4
            simp only [optChainParamsPBAt, hcp]
          refine sepWP_rw_pre (by
            simp only [memRegion_88_err_split (s0.readReg64 (.gpr 0#5)),
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            rfl) ?_
          apply SepWP.exists_elim; intro w2_out
          apply SepWP.exists_elim; intro w1_out
          apply SepWP.exists_elim; intro bs7_out
          apply SepWP.exists_elim; intro b0_out
          apply SepWP.exists_elim; intro w0_out
          refine SepWP.focus_pure (by sep_focus) fun hbs7 => ?_
          apply sepWP_chainFrom_finish_vn_some
            (call := ⟨s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5),
              s0.readReg64 (.gpr 2#5), gPb, vnPin, none, some v⟩)
            hevs_cf rfl hvn_ne rfl
          rw [hcf_eq]
          conv =>
            arg 5
            ext sf P_f
            simp only [chainResultAt, versionNegotiationPBAt, optChainParamsPBAt, hcp]
          by_vm_steps (
            wp_steps
            refine SepWP.fold
              (fold_chainErrorAt (s0.readReg64 (.gpr 0#5)) .chainNotAvailable 15#8 rfl hbs7 w1_out w2_out)
              (by sep_focus) ?_
            refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) _)
              (by sep_focus) ?_
            refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
            refine align_pre (by sep_ac_rfl) ?_
            wp_done
          )
        | some cp =>
          have hcf_eq : chainFrom hkdf none (some v) =
              .ok (chainNewVal hkdf v.authKey dir cp) := by
            simp [chainFrom, chainFromVersionNegotiation, hdir_opt, hcp]; rfl
          have henv_eq : ChainFromEnv none (some v) = ChainNewEnv := by
            funext evs
            simp [ChainFromEnv,
              LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget.ChainFromVersionNegotiationEnv,
              ChainNewEnv,
              LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget.chainNewEvents,
              LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.chainNewEvents,
              chainEpochSize, chainEpochAlign, hdir_opt, hcp]
          have hfits_new : FitsEnv M lim st ChainNewEnv := henv_eq ▸ hfits
          conv =>
            arg 4
            simp only [optChainParamsPBAt, hcp]
          refine SepWP.fold (vecU8At_entails_header_bytesAt_rest A.repAlloc
            (s0.readReg64 (.gpr 2#5)) vnPin.cap vnPin.ptr v.authKey) (by sep_focus) ?_
          refine SepWP.focus_pure (by sep_focus) fun hlen64 => ?_
          let P_call_new : SepProp :=
            memRegion (s0.readReg64 (.gpr 0#5)) 88 ∗
            bytesAt false vnPin.ptr v.authKey ∗
            A.pool lim st s0 ∗
            stackAt s0.sp chainNewStackX ∗
            memRegion (s0.readReg64 (.gpr 1#5)) 80 ∗
            ((s0.readReg64 (.gpr 2#5)) ↦₆₄ vnPin.cap) ∗
            ((s0.readReg64 (.gpr 2#5) + 8#64) ↦₆₄ vnPin.ptr) ∗
            ((s0.readReg64 (.gpr 2#5) + 16#64) ↦₆₄ BitVec.ofNat 64 v.authKey.length) ∗
            vecU8BufRest A.repAlloc vnPin.cap vnPin.ptr v.authKey.length ∗
            ((s0.readReg64 (.gpr 2#5) + 24#64) ↦₃₂ 1#32) ∗
            ((s0.readReg64 (.gpr 2#5) + 28#64) ↦₃₂ cp.maxJump) ∗
            ((s0.readReg64 (.gpr 2#5) + 32#64) ↦₃₂ cp.maxOooKeys) ∗
            ((s0.readReg64 (.gpr 2#5) + 36#64) ↦₃₂ v.direction) ∗
            ((s0.readReg64 (.gpr 2#5) + 40#64) ↦₃₂ v.minVersion) ∗
            memRegion (s0.readReg64 (.gpr 2#5) + 44#64) 4 ∗
            memRegion (s0.sp - BitVec.ofNat 64 chainFromStackX) 336
          refine sepWP_seq_lsCallInv_vm (mid := lsmpl.base 363) (P_mid := P_call_new)
            (Q := fun s1 =>
              s1.sp = s0.sp ∧
              s1.trace = s0.trace ∧
              s1.readReg64 .lr = s0.readReg64 .lr ∧
              s1.readReg64 .x0 = s0.readReg64 (.gpr 0#5) ∧
              s1.readReg64 .x1 = vnPin.ptr ∧
              s1.readReg64 .x2 = BitVec.ofNat 64 v.authKey.length ∧
              (s1.readReg64 .x3).setWidth 32 = dir.toI32 ∧
              (s1.readReg64 .x4).setWidth 32 = cp.maxJump ∧
              (s1.readReg64 .x5).setWidth 32 = cp.maxOooKeys ∧
              CalleeSavedPreserved s0 s1)
            hinv0 ?_ ?_
          · by_vm_steps (
              wp_steps
              refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) _)
                (by sep_focus) ?_
              refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
              refine sepWP_rw_pre (by
                simp only [stackAt_chainFrom_split_chainNew s0.sp, sepConj_assoc]
                rfl) ?_
              dsimp only [P_call_new]
              wp_done
            )
          · intro s1 hpc1 hrun1 hinv1 hvm01
              ⟨hsp1, htr1, hlr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hcs01⟩
            have hsp1_align : s1.spAligned = true := by
              dsimp only [State.spAligned] at hsp0 ⊢
              rwa [hsp1]
            dsimp only [P_call_new]
            rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm01]
            apply (call_frame_lsCallInv h_new
              ((⟨s0.readReg64 (.gpr 0#5), false, vnPin.ptr, v.authKey, dir, cp⟩ : ChainNewGhost), st)
              hinv1 (callee_ret_pc := s0.readReg64 .lr))
            · exact hpc1
            · exact hrun1
            · exact hsp1_align
            · exact hlr1
            · rfl
            · exact ⟨hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hlen64, hfits_new⟩
            · rw [hsp1]; sep_focus
            · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
              dsimp only [chainNewSpecX]
              rw [hsp1, sepExists_sepConj_left]
              apply SepWP.exists_elim; intro evs
              refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
              rcases hpure with ⟨htr_sf, _hacp, hevs_new⟩
              have hevs_cf : ChainFromEnv none (some v) evs := henv_eq.symm ▸ hevs_new
              have hsp_sf' : sf.sp = s0.sp := hsp_sf.trans hsp1
              have htr_sf' : sf.trace = s0.trace := htr_sf.trans htr1
              have hcs0 : CalleeSavedPreserved s0 sf := calleeSavedPreserved_trans hcs01 hcs_sf
              apply sepWP_chainFrom_finish_vn_some
                (call := ⟨s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5),
                  s0.readReg64 (.gpr 2#5), gPb, vnPin, none, some v⟩)
                hevs_cf rfl hvn_ne rfl
              refine SepWP.fold (chainNew_post_entails_chainRepr A.repAlloc (s0.readReg64 (.gpr 0#5))
                (chainNewVal hkdf v.authKey dir cp))
                (by sep_focus) ?_
              refine SepWP.fold (header_bytesAt_rest_entails_vecU8At A.repAlloc
                (s0.readReg64 (.gpr 2#5)) vnPin.cap vnPin.ptr v.authKey) (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (stackAt_chainFrom_split_chainNew s0.sp).symm)
                (by sep_focus) ?_
              refine SepWP.done hpc_sf hrun_sf ⟨VmPreserved.refl sf, ?_, hsp_sf', hcs0, htr_sf'⟩
              rw [hcf_eq]
              simp only [chainResultAt, versionNegotiationPBAt, optChainParamsPBAt, hcp]
              exact Entails.of_eq (by sep_ac_rfl)
      · have hcf_eq : chainFrom hkdf none (some v) = .error .stateDecode := by
          simp [chainFrom, chainFromVersionNegotiation, hdir_opt]; rfl
        have hevs_cf : ChainFromEnv none (some v) [] := by
          simp [ChainFromEnv,
            LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget.ChainFromVersionNegotiationEnv,
            hdir_opt]
        refine sepWP_rw_pre (by
          simp only [memRegion_88_err_split (s0.readReg64 (.gpr 0#5)),
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          rfl) ?_
        apply SepWP.exists_elim; intro w2_out
        apply SepWP.exists_elim; intro w1_out
        apply SepWP.exists_elim; intro bs7_out
        apply SepWP.exists_elim; intro b0_out
        apply SepWP.exists_elim; intro w0_out
        refine SepWP.focus_pure (by sep_focus) fun hbs7 => ?_
        apply sepWP_chainFrom_finish_vn_some
          (call := ⟨s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5),
            s0.readReg64 (.gpr 2#5), gPb, vnPin, none, some v⟩)
          hevs_cf rfl hvn_ne rfl
        rw [hcf_eq]
        conv =>
          arg 5
          ext sf P_f
          dsimp only [chainResultAt, versionNegotiationPBAt]
        by_vm_steps (
          wp_steps
          refine SepWP.fold
            (fold_chainErrorAt (s0.readReg64 (.gpr 0#5)) .stateDecode 0#8 rfl hbs7 w1_out w2_out)
            (by sep_focus) ?_
          refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) _)
            (by sep_focus) ?_
          refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
          refine align_pre (by sep_ac_rfl) ?_
          wp_done
        )

theorem chainFrom_placed_ok_x [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_from_pb : ChainFromPbPlacedOkX M A lim ext)
    (h_new : subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
      (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX hkdf M A lim))) :
    ChainFromPlacedOkX hkdf M A lim ext :=
  chainFrom_placed_ok_of_contracts_x h_from_pb h_new

end LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.ProofPlacedBudget
