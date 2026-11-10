/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudgetAux
public import LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Cross-Block Budget-Threaded `DhCommit` Step 3 (`+0xa84 → +0xaf0`)

Pinned-capacity proofs of `DhCommit` step 3 (`+0xa84 → +0xaf0`) under `withLsCodeLoaded lsmpl` on
`grow_one`, together with a spec bridge from `ConsumeMessageKey.DefsBudget.growOneSpec`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClStep3PlacedBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open scoped CryptoVerification.RustHeap
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ChainKey PublicKey ReceiverChain)
open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit (
  add_assoc_const chainHeaps growOneStack newChainGhost newReceiverChain optChainKeyHeap
  optChainKeyTailBytes vecBuf_chainAt_expose_bytes vecBuf_chainAt_of_bytes vecBuf_expose_for_grow
)
open CryptoVerification.RustHeap (allocHookStack vecBuf)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudgetAux (
  dhCommit_step3b_pinned_of_wp
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  GrowOne104Env fitsEnv_growOne104_iff growOne104Events
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget (
  DhCommitStep3BlockWp dhCommitStep3Events dhCommitStep3aEvents growOneSpec growOneSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (dhStepNewChainsCap)

private theorem add_lscl_pre {α : Type} [LibsignalPlacement] {spec : Spec α} {arg : α}
    {s : State} {Rest : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hm : s.mem ⊨ spec.pre arg s ∗ Rest) :
    s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre arg s ∗ Rest := by
  dsimp only [withLsCodeLoaded]
  have h1 : s.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗ (spec.pre arg s ∗ Rest) := by
    rw [satisfies_pure_sepConj]; exact ⟨hcl, hm⟩
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h1

private theorem steps_of_sepWP_cl [LibsignalPlacement] {prog : Program} {s : State}
    {target : BitVec 64} {Pre Rest : SepProp} {PostWP : State → SepProp → Prop} {Q : State → Prop}
    (hwp : SepWP prog target s Pre PostWP) (hmem : s.mem ⊨ Pre ∗ Rest)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hL : prog.CodeLoaded s.mem)
    (hcont : ∀ s1 P_out, s1.pc = target → s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem → prog.CodeLoaded s1.mem →
      (s1.mem ⊨ P_out ∗ Rest) → PostWP s1 P_out → ∃ sf, Steps prog s1 sf ∧ Q sf) :
    ∃ sf, Steps prog s sf ∧ Q sf := by
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_out, hm1, hpost1⟩ | ⟨_, hoom⟩⟩ := hwp.elim hmem hL
  · obtain ⟨sf, hsteps2, hQ⟩ := hcont s1 P_out hpc1 hrun1
      (hcl.of_keepsFrozen hsteps1.keepsFrozen) (hL.of_keepsFrozen hsteps1.keepsFrozen) hm1 hpost1
    exact ⟨sf, hsteps1.trans hsteps2, hQ⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem steps_of_call_no_panic {α : Type} {prog : Program} {s : State}
    {entry ret_pc : BitVec 64} {spec : Spec α} {arg : α} {Rest : SepProp} {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc) (hpre : s.mem ⊨ spec.pre arg s ∗ Rest)
    (hL : prog.CodeLoaded s.mem)
    (hpan_false : ∀ sf, spec.onPanic arg s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl)
    (hcont : ∀ s1, s1.pc = ret_pc → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 → prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ Rest) → ∃ sf, Steps prog s1 sf ∧ Q sf) :
    ∃ sf, Steps prog s sf ∧ Q sf := by
  obtain ⟨s1, hsteps1, hout, -⟩ := hcall.no_fault_before_outcome arg Rest s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpc1, hsp1, hrun1⟩, ⟨_, hcs1⟩, hpost1⟩ | ⟨_, hpost1⟩ | ⟨code, _, hpost1⟩ | ⟨_, hpost1⟩
  · rw [show Reg.lr = Reg.x30 from rfl, hlr] at hpc1
    have hsp_align1 : s1.spAligned = true := by unfold State.spAligned at hsp ⊢; rw [hsp1]; exact hsp
    obtain ⟨sf, hsteps2, hQ⟩ :=
      hcont s1 hpc1 hrun1 hsp1 hsp_align1 hcs1 (hL.of_keepsFrozen hsteps1.keepsFrozen) hpost1
    exact ⟨sf, hsteps1.trans hsteps2, hQ⟩
  · rw [hpan_false s1, satisfies_pure_sepConj] at hpost1; exact False.elim hpost1.1
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1; exact False.elim hpost1.1
  · rw [hoom_false s1, satisfies_pure_sepConj] at hpost1; exact False.elim hpost1.1

/-- Bridge `ConsumeMessageKey.DefsBudget.growOneSpec` (`4608`B stack, `GrowOneEnv`) to
`DhCommitStep3Budget.growOneSpec` (`4608`B stack, `GrowOne104Env`) under `withLsCodeLoaded lsmpl`. -/
theorem dhCommitGrowOne_cl_of_cmkGrowOne_cl [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget.growOneSpec M A lim))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (growOneSpec M A lim)) := by
  have hevs_eq : ∀ (cap : BitVec 64) (evs : List AllocEvent),
      LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget.GrowOneEnv cap evs →
      evs = growOne104Events cap := by
    intro cap evs henv
    unfold LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget.GrowOneEnv at henv
    unfold growOne104Events LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowEvents
    rcases henv with ⟨rfl, rfl⟩ | ⟨hne, rfl⟩
    · rfl
    · have hc0 : cap.toNat ≠ 0 := fun h0 => hne (BitVec.eq_of_toNat_eq h0)
      simp only [hc0, ↓reduceIte]
  refine subroutine_ok_outcome_intro (fun ((v, cap, ptr, bs), st) R s0 hpc0 hrun0 hpre0 hsp0 => ?_)
  have hpre_cmk : s0.mem ⊨
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget.growOneSpec M A lim)).pre
          ((v, cap, ptr, bs), st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded, growOneSpec, growOneSpecWithStack, growOneStack,
      LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget.growOneSpec] at hpre0 ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hlen, hptr, hmax, hfits⟩, hmem0⟩
    refine ⟨⟨hx0, hlen, hptr, hmax, fun evs henv => ?_⟩, hmem0⟩
    rw [hevs_eq cap evs henv]
    exact fitsEnv_growOne104_iff.mp hfits
  refine h.mono_outcome ((v, cap, ptr, bs), st) R s0 hpc0 hrun0 hpre_cmk hsp0 (fun sf hout => ?_)
  rcases hout with ⟨hret, hpres, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hpres, ?_⟩
    dsimp only [withLsCodeLoaded, growOneSpec, growOneSpecWithStack, growOneStack,
      LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget.growOneSpec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htr, henv⟩, hpost⟩
    rw [hevs_eq cap evs henv] at hpost
    rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨p', hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hp', _halign⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hp', by refine Satisfies.mono (Entails.of_eq ?_) hpost; sep_ac_rfl⟩
  · exact Or.inr (Or.inl ⟨hpan, hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

theorem dhCommit_step3a_cl_pinned_of_wp [LibsignalPlacement]
    {prog : Program} {entry growEntry deallocEntry : BitVec 64}
    (hwp : DhCommitStep3BlockWp prog entry growEntry deallocEntry)
    {stk : Nat} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hGrow : subroutine_ok prog growEntry
      (withLsCodeLoaded lsmpl (growOneSpecWithStack stk M A lim)))
    (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hfits3a : FitsEvents M lim st0 (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)))
    (hpc : s.pc = entry + 0xa84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨ (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       A.pool lim st0 s ∗ stackAt sp stk) ∗ (Frame ∗ R)) :
    let st1 := M.stepEvents (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)) st0
    let chainsCap1 := dhStepNewChainsCap chainsCap gcs.length
    ∃ sf, Steps prog s sf ∧ ∃ chainsPtr1 : BitVec 64,
        gcs.length < chainsCap1.toNat ∧ sf.pc = entry + 0xa9c#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = BitVec.ofNat 64 gcs.length ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧ (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 gcs ∗
           A.pool lim st1 sf ∗ stackAt sp stk) ∗ (Frame ∗ R)) := by
  intro st1 chainsCap1
  have hexp0 : s.mem ⊨
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       A.pool lim st0 s ∗ stackAt sp stk ∗ (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem; sep_ac_rfl
  by_cases hgrow : BitVec.ofNat 64 gcs.length = chainsCap
  · have hst1_eq : st1 = M.stepEvents (growOne104Events chainsCap) st0 := by
      dsimp only [st1, dhCommitStep3aEvents]; simp only [hgrow, ↓reduceIte]
    have hfits_grow : FitsEnv M lim st0 (GrowOne104Env chainsCap) := by
      rw [fitsEnv_growOne104_iff]
      dsimp only [dhCommitStep3aEvents] at hfits3a
      simpa only [hgrow, ↓reduceIte] using hfits3a
    have hexp := Satisfies.mono
      (sepConj_mono_left (vecBuf_chainAt_expose_bytes A.repAlloc chainsCap chainsPtr gcs)) hexp0
    rw [sepExists_sepConj_left, satisfies_sepExists] at hexp
    rcases hexp with ⟨bs, hexp⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hexp
    rcases hexp with ⟨⟨hbs, hlen_bs, _hle_cap, _hcap_lt, hptr⟩, hexp⟩
    have hlen_eq_cap : gcs.length = chainsCap.toNat := by
      rw [← hgrow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [vecBuf_expose_for_grow A.repAlloc chainsCap chainsPtr gcs bs hlen_bs hlen_eq_cap] at hexp
    have h38_grow : ((sp + 0x38#64) ↦₆₄ chainsCap) = ((sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 gcs.length) := by
      rw [hgrow]
    have hm_grow_wp : s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length)) ∗ ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          (if chainsCap = 0 then emp else A.live chainsPtr bs.length 8 ∗ (chainsPtr ↦ₛ bs)) ∗
          chainHeaps A.repAlloc gcs ∗ A.pool lim st0 s ∗ stackAt sp stk ∗ Frame) ∗ R) := by
      rw [h38_grow] at hexp; change _ at hexp
      refine Satisfies.mono (Entails.of_eq ?_) hexp; sep_ac_rfl
    refine steps_of_sepWP_cl
      (hwp.step3a_grow sp (BitVec.ofNat 64 gcs.length) s hpc hrun hsp hsp_align)
      hm_grow_wp hcl hL ?_
    intro s1 P1 hpc1 hrun1 hcl1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hvm1, hsp1, hsp_align1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    rw [← A.pool_transport lim st0 s s1 hvm1] at hm1'
    have hmax_lt : max (2 * chainsCap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by omega
    have hm_call : s1.mem ⊨
        (growOneSpecWithStack stk M A lim).pre ((sp + 0x38#64, chainsCap, chainsPtr, bs), st0) s1 ∗
        ((((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
          chainHeaps A.repAlloc gcs ∗ Frame) ∗ R) := by
      dsimp only [growOneSpecWithStack]
      rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_1, by omega, hptr, hmax_lt, hfits_grow⟩, ?_⟩
      rw [add_assoc_const sp 0x38#64 8#64 0x40#64]
      rw [← h38_grow] at hm1'
      refine Satisfies.mono (Entails.of_eq ?_) hm1'; sep_ac_rfl
    refine steps_of_call_no_panic hGrow hpc1 hrun1 hsp_align1 hx30_1 (add_lscl_pre hcl1 hm_call) hL1
      (by intro _; rfl) (by intros; rfl) (by intro _; rfl) ?_
    intro s2 hpc2 hrun2 hsp2 hsp_align2 hcs2 hL2 hm2
    dsimp only [withLsCodeLoaded, growOneSpecWithStack] at hm2
    rw [hsp1, sepConj_assoc, satisfies_pure_sepConj] at hm2
    rcases hm2 with ⟨htr2, hm2⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm2
    rcases hm2 with ⟨p', hm2⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
    rcases hm2 with ⟨hp', hm2⟩
    set cap1 := BitVec.ofNat 64 (max (2 * chainsCap.toNat) 4)
    have hcap1_pin : chainsCap1 = cap1 := by
      dsimp only [chainsCap1, dhStepNewChainsCap, cap1]; simp only [hgrow, ↓reduceIte]
    have hcap1_toNat : cap1.toNat = max (2 * chainsCap.toNat) 4 := by
      dsimp only [cap1]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt_cap1 : gcs.length < chainsCap1.toNat := by rw [hcap1_pin]; omega
    have hcap1_ne : cap1 ≠ 0 := by
      intro h0; rw [h0] at hcap1_toNat; change 0 = max (2 * chainsCap.toNat) 4 at hcap1_toNat; omega
    rw [add_assoc_const sp 0x38#64 8#64 0x40#64, ← hst1_eq] at hm2
    have hlive_eq : A.live p' (max (2 * chainsCap.toNat) 4 * 104) 8 = A.repAlloc.live p' (cap1.toNat * 104) 8 := by
      rw [hcap1_toNat]; rfl
    have hmr_eq :
        memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * chainsCap.toNat) 4 - chainsCap.toNat) * 104) =
          memRegion (p' + BitVec.ofNat 64 (gcs.length * 104)) ((cap1.toNat - gcs.length) * 104) := by
      rw [hlen_bs, hcap1_toNat, ← hlen_eq_cap]
    have hpull2 : s2.mem ⊨
        (A.repAlloc.live p' (cap1.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
         memRegion (p' + BitVec.ofNat 64 (gcs.length * 104)) ((cap1.toNat - gcs.length) * 104) ∗
         chainHeaps A.repAlloc gcs) ∗ (((sp + 0x38#64) ↦₆₄ cap1) ∗ ((sp + 0x40#64) ↦₆₄ p') ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         A.pool lim st1 s2 ∗ stackAt sp stk ∗ (Frame ∗ R)) := by
      rw [hlive_eq, hmr_eq] at hm2
      refine Satisfies.mono (Entails.of_eq ?_) hm2; sep_ac_rfl
    have hreasm := vecBuf_chainAt_of_bytes A.repAlloc cap1 p' hcap1_ne hbs (by omega) (by omega) hp'
    have hm2_vec := Satisfies.mono (sepConj_mono_left hreasm) hpull2
    have hm2_final : s2.mem ⊨
        (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ p') ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 p' gcs ∗
         A.pool lim st1 s2 ∗ stackAt sp stk) ∗ (Frame ∗ R) := by
      rw [hcap1_pin]; refine Satisfies.mono (Entails.of_eq ?_) hm2_vec; sep_ac_rfl
    exact ⟨s2, .refl s2, p', hlt_cap1, hpc2, hrun2, by reg_chain, hsp_align2,
      htr2.trans (htr1.trans htrace), by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain, hL2, hm2_final⟩
  · have hcap1_pin : chainsCap1 = chainsCap := by
      dsimp only [chainsCap1, dhStepNewChainsCap]; simp only [hgrow, ↓reduceIte]
    have hst1_eq : st1 = st0 := by
      dsimp only [st1, dhCommitStep3aEvents]; simp only [hgrow, ↓reduceIte]; exact M.stepEvents_nil st0
    have hle_cap : gcs.length ≤ chainsCap.toNat := by
      unfold vecBuf at hexp0; rw [sepConj_assoc, satisfies_pure_sepConj] at hexp0; exact hexp0.1.1
    have hlt_cap : gcs.length < chainsCap1.toNat := by
      rw [hcap1_pin]
      rcases Nat.lt_or_eq_of_le hle_cap with hlt | heq
      · exact hlt
      · exfalso; apply hgrow; rw [heq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hm_nogrow : s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length)) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
          A.pool lim st0 s ∗ stackAt sp stk ∗ Frame) ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hmem; sep_ac_rfl
    refine steps_of_sepWP_cl
      (hwp.step3a_nogrow sp chainsCap (BitVec.ofNat 64 gcs.length) s hpc hrun hsp hsp_align hgrow)
      hm_nogrow hcl hL ?_
    intro s1 P1 hpc1 hrun1 _hcl1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hvm1, hsp1, hsp_align1, htr1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hP1⟩
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    rw [← A.pool_transport lim st0 s s1 hvm1, ← hst1_eq] at hm1'
    have hm1_final : s1.mem ⊨
        (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr gcs ∗
         A.pool lim st1 s1 ∗ stackAt sp stk) ∗ (Frame ∗ R) := by
      rw [hcap1_pin]; refine Satisfies.mono (Entails.of_eq ?_) hm1'; sep_ac_rfl
    exact ⟨s1, .refl s1, chainsPtr, hlt_cap, hpc1, hrun1, hsp1, hsp_align1,
      htr1.trans htrace, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hL1, hm1_final⟩

theorem dhCommit_step3_cl_pinned_of_wp [LibsignalPlacement]
    {prog : Program} {entry growEntry deallocEntry : BitVec 64}
    (hwp : DhCommitStep3BlockWp prog entry growEntry deallocEntry)
    {stk : Nat} (hstk_lo : allocHookStack ≤ stk) (hstk_hi : stk < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hGrow : subroutine_ok prog growEntry
      (withLsCodeLoaded lsmpl (growOneSpecWithStack stk M A lim)))
    (hDealloc : subroutine_ok prog deallocEntry (rustCliDeallocBudgetSpec M A lim))
    (R Frame : SepProp) (s0 s : State) (sp chainsCap chainsPtr boxPtr srkPtr ckPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (srk : PublicKey) (rck : ChainKey) (pad : List (BitVec 8))
    (hlen_lt : gcs.length < 2 ^ 32) (hpad : pad.length = 4) (hsrk_ne : srkPtr ≠ 0)
    (hfits3a : FitsEvents M lim st0 (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)))
    (hpc : s.pc = entry + 0xa84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64) (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr) (hx28 : s.readReg64 .x28 = srkPtr)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨ (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool lim st0 s ∗ stackAt sp stk) ∗ (Frame ∗ R))
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newGC := (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck)
    let st2 := M.stepEvents (dhCommitStep3Events chainsCap (BitVec.ofNat 64 gcs.length)) st0
    let chainsCap1 := dhStepNewChainsCap chainsCap gcs.length
    ∃ sf, Steps prog s sf ∧ ∃ chainsPtr1 : BitVec 64,
        sf.pc = entry + 0xaf0#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧ prog.CodeLoaded sf.mem ∧ (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
           memRegion (sp + 0x190#64) 104 ∗ A.pool lim st2 sf ∗ stackAt sp stk) ∗ (Frame ∗ R)) := by
  intro newGC st2 chainsCap1
  set Step3Rest : SepProp :=
    ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
    memRegion (sp + 0x1b0#64) 72 ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
    (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
    optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗ Frame
  have hm3a : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       A.pool lim st0 s ∗ stackAt sp stk) ∗ (Step3Rest ∗ R) := by
    dsimp only [Step3Rest]; refine Satisfies.mono (Entails.of_eq ?_) hmem; sep_ac_rfl
  obtain ⟨s1, hsteps3a, chainsPtr1, hlt_cap1, hpc1, hrun1, hsp1, hsp_align1, htr1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1,
      hvregs_1, hL1, hm1⟩ :=
    dhCommit_step3a_cl_pinned_of_wp hwp A lim st0 hGrow R Step3Rest s0 s sp chainsCap chainsPtr gcs
      hlen_lt hfits3a hpc hrun hsp hsp_align htrace hcl hL hm3a
  obtain ⟨sf, hsteps3b, hpost⟩ :=
    dhCommit_step3b_pinned_of_wp (hlr_dealloc := hlr_dealloc) hwp.step3b hstk_lo hstk_hi A lim
      (M.stepEvents (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)) st0)
      hDealloc R Frame s0 s s1 sp chainsCap1 chainsPtr1 boxPtr srkPtr ckPtr gcs srk rck pad
      hlt_cap1 hpad hsrk_ne hpc1 hrun1 hsp1 hsp_align1 htr1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
      hx25 hx26 hx27 hx28 hL1 hm1
  have hst2_eq :
      M.stepEvents (rustDeallocEvents 33 1)
        (M.stepEvents (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)) st0) = st2 := by
    dsimp only [st2, dhCommitStep3Events]
    exact (M.stepEvents_append (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length))
      (rustDeallocEvents 33 1) st0).symm
  rw [hst2_eq] at hpost
  exact ⟨sf, hsteps3a.trans hsteps3b, chainsPtr1, hpost⟩

end LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClStep3PlacedBudget
