/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBWPlaced
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded `[LibsignalPlacement]` Post-Loop Deallocation Chains and Error Entry Blocks

Allocation-budget (`RustCliAllocBudget M`) proofs of the post-loop deallocation chains and
error entry blocks (`+0x5e0`, `+0x61c`, `+0x66c`, `+0x678`, `+0x7a8` → `+0x504`) on
`preKeyPlacedProg H`, tracking `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBWPlacedBudget

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding rustDeallocExternSpecWithStack
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters hiding lsRustDeallocSym
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire hiding
  SepWPp ErrTailQPlaced etb_errTailQPlaced_mono
  tail_80c_placed_wpX tail_7f8_placed_wpX tail_7e4_placed_wpX tail_7d0_placed_wpX
  tail_7b8_placed_wpX tail_654_placed_wpX tail_64c_placed_wpX tail_638_placed_wpX
  tail_604_placed_wpX entry_678_placed_wpX entry_66c_placed_wpX entry_5e0_placed_wpX
  entry_61c_placed_wpX entry_7a8_placed_wpX entry_7a8_placed_wpE
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   RustLayoutOk rustDeallocEvents)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
  (freeOnly_rustDeallocEvents preKeyNoPanicQp)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
  (PksmCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget
  (sepWP_done_sync_pool_111 sepWP_seg_111)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (sepWPp_end_noPanic_placed)

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev call_noPanic_budget_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.call_noPanic_budget_pk
private abbrev frame_noPanic_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.frame_noPanic_pk
private abbrev let_state_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.let_state

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
attribute [local simp] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero

theorem sepWPp_anyQp_of_noPanic {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q preKeyNoPanicQp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hok | ⟨_, _, _, hqp⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact False.elim hqp
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## 1. Common Postcondition (`ErrTailQPlaced`) -/

/-- Postcondition of every dealloc-chain leaf under `[LibsignalPlacement]`: at `+0x504`
(`1284`) with `PostEpilogueStatePlaced`, `x19 = sret`, `FreeOnlyEvs evs`, and
`A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R`. -/
abbrev ErrTailQPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 : State) (sp' sret : BitVec 64) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf Pf =>
    PostEpilogueStatePlaced s0 sp' sf ∧ sf.readReg64 .x19 = sret ∧
    ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
      (Pf ⊢ A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)

theorem ErrTailQPlaced.nil [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 sf : State} {sp' sret : BitVec 64} {R Pf : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' sf) (hx19 : sf.readReg64 .x19 = sret)
    (hP : Pf ⊢ A.pool lim st sf ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) :
    ErrTailQPlaced A lim st s0 sp' sret R sf Pf :=
  ⟨hst, hx19, [], FreeOnlyEvs.nil, by rw [M.stepEvents_nil]; exact hP⟩

theorem ErrTailQPlaced.frame_eq [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 sf : State} {sp' sret : BitVec 64} {R G H0 Pf : SepProp}
    (h : ErrTailQPlaced A lim st s0 sp' sret R sf Pf) (heq : R ∗ G = H0) :
    ErrTailQPlaced A lim st s0 sp' sret H0 sf (Pf ∗ G) := by
  rcases h with ⟨hst, hx19, evs, hf, hent⟩
  refine ⟨hst, hx19, evs, hf, Entails.trans (sepConj_mono_left hent) ?_⟩
  rw [← heq]; apply entails_of_eq; sep_ac_rfl

theorem ErrTailQPlaced.prepend_dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 sf : State} {sp' sret : BitVec 64} {R Pf : SepProp} (cap : Nat)
    (h : ErrTailQPlaced A lim (M.stepEvents (rustDeallocEvents cap 1) st) s0 sp' sret R sf Pf) :
    ErrTailQPlaced A lim st s0 sp' sret R sf Pf := by
  rcases h with ⟨hst, hx19, evs, hf, hent⟩
  exact ⟨hst, hx19, rustDeallocEvents cap 1 ++ evs,
    (freeOnly_rustDeallocEvents cap 1).append hf,
    by rw [M.stepEvents_append]; exact hent⟩

theorem etb_errTailQPlaced_mono [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 sf : State} {sp' sret : BitVec 64} {R R' Pf : SepProp}
    (h : ErrTailQPlaced A lim st s0 sp' sret R sf Pf) (hR : R ⊢ R') :
    ErrTailQPlaced A lim st s0 sp' sret R' sf Pf := by
  rcases h with ⟨hst, hx19, evs, hf, hent⟩
  exact ⟨hst, hx19, evs, hf, Entails.trans hent (sepConj_mono_right (sepConj_mono_right hR))⟩

/-! ## 2. Shared Dealloc Chain (`+0x7b8 .. +0x814` → `+0x504`) -/

theorem tail_80c_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret ptr cap : BitVec 64} {R : SepProp}
    {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2060#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap)
    (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ A.pool lim st s ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret R)
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hlayout : RustLayoutOk cap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
  have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  apply sepWP_seg_111; intro _m_strip; wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine let_state_pk ?_; intro s_call
  refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded (ptr, cap.toNat, 1, st) hC.deallocX
    (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
    (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 2068#64) (by simp [s_call, arm64_norm])
    (T := A.pool lim st s_call ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
      stackAt sp' extHookStack)
    (φ := ptr = ptr ∧ cap.toNat = cap.toNat ∧
      (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk cap.toNat 1 ∧
      LsRetAddr624 ((blkPl_111).base + 2068#64))
    (by simp_all [s_call, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
    ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 2068#64 (by decide) (by decide)⟩
    (by rw [hstack]; sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  have hx19_2 : s2.readReg64 .x19 = sret := by simp [hcs2.1, s_call, hx19, arm64_norm]
  have hsp2_eq : s2.sp = sp' := by simp [hsp2, s_call, hsp_eq, arm64_norm]
  have htr2_eq : s2.trace = s0.trace := by simp [htr2, s_call, htr, arm64_norm]
  clear hcs2 hsp2 htr2
  set st1 := M.stepEvents (rustDeallocEvents cap.toNat 1) st
  refine sepWPp_end_noPanic_placed (s0 := s0) hcl2 ?_
  apply sepWP_seg_111; intro _m_strip2
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st1 fun _ hcl3 => ?_
  refine ErrTailQPlaced.prepend_dealloc cap.toNat
    (ErrTailQPlaced.nil
      (PreKeyPostState.of_steps hcl3 (by simp [hsp2_eq, arm64_norm]) hsp_eq hsp
        (by simp [htr2_eq, arm64_norm]))
      (by simp [hx19_2, arm64_norm]) ?_)
  apply entails_of_eq
  simp only [s_call, hstack, hsp_eq, arm64_norm]
  sep_ac_rfl

theorem tail_7f8_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret kyCap kyPtr : BitVec 64}
    (kyAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2040#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st s ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret R)
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases kyAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc kyCap kyPtr false = ⌜kyCap = noneCap ∨ kyCap = 0#64⌝ := rfl
    rw [hdealloc]; refine SepWPp.pure_pre fun hcap => ?_
    rcases hcap with rfl | rfl
    all_goals
      refine sepWPp_end_noPanic_placed (s0 := s0) hcl ?_
      apply sepWP_seg_111; intro _m_strip; wp_steps
      refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
      exact ErrTailQPlaced.nil
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [hx19, arm64_norm]) (by apply entails_of_eq; sep_ac_rfl)
  | true =>
    have hdealloc : deallocSlot A.repAlloc kyCap kyPtr true =
        (⌜0 < kyCap.toNat ∧ kyCap.toNat < 2 ^ 63 ∧ kyPtr ≠ 0#64⌝ ∗
          A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2060#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre
      (P' := A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact tail_80c_placed_wpX hC
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) hpos hlt

theorem tail_7e4_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret bkCap bkPtr kyCap kyPtr : BitVec 64}
    (bkAct kyAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2020#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st s ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases bkAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc bkCap bkPtr false = ⌜bkCap = noneCap ∨ bkCap = 0#64⌝ := rfl
    rw [hdealloc]; refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : bkCap = 0#64 := hcap.resolve_left hbk
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2040#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st _ ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ 0#64)))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_7f8_placed_wpX hC kyAct
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]))
      fun sf Pf h => h.frame_eq (by sep_ac_rfl)
  | true =>
    have hdealloc : deallocSlot A.repAlloc bkCap bkPtr true =
        (⌜0 < bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0#64⌝ ∗
          A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : bkCap ≠ 0#64 := by rintro rfl; simp at hpos
    have hlayout : RustLayoutOk bkCap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine let_state_pk ?_; intro s_call
    refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
      (bkPtr, bkCap.toNat, 1, st) hC.deallocX
      (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
      (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
      (ret_pc := (blkPl_111).base + 2040#64) (by simp [s_call, arm64_norm])
      (T := A.pool lim st s_call ∗ A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗
        stackAt sp' extHookStack)
      (φ := bkPtr = bkPtr ∧ bkCap.toNat = bkCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk bkCap.toNat 1 ∧
        LsRetAddr624 ((blkPl_111).base + 2040#64))
      (by simp_all [s_call, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 2040#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, hx25_cs, _, _, hx28_cs, _⟩
    set st1 := M.stepEvents (rustDeallocEvents bkCap.toNat 1) st
    refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st1 s2 ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap)))
      (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_7f8_placed_wpX (st := st1) hC kyAct
        ⟨by simp [hsp2, s_call, hsp_eq, arm64_norm], hsp2_align, hcl2, by simp [htr2, s_call, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, s_call, hx19, arm64_norm])
        (by simp [hx28_cs, s_call, hx28, arm64_norm])
        (by simp [hx25_cs, s_call, hx25, arm64_norm]))
      fun sf Pf h => (h.frame_eq (by sep_ac_rfl)).prepend_dealloc bkCap.toNat

set_option maxHeartbeats 800000 in
theorem tail_7d0_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (ikAct bkAct kyAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2000#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st s ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases ikAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc ikCap ikPtr false = ⌜ikCap = noneCap ∨ ikCap = 0#64⌝ := rfl
    rw [hdealloc]; refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : ikCap = 0#64 := hcap.resolve_left hik
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2020#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st _ ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_7e4_placed_wpX hC bkAct kyAct
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hbk)
      fun sf Pf h => h.frame_eq (by sep_ac_rfl)
  | true =>
    have hdealloc : deallocSlot A.repAlloc ikCap ikPtr true =
        (⌜0 < ikCap.toNat ∧ ikCap.toNat < 2 ^ 63 ∧ ikPtr ≠ 0#64⌝ ∗
          A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : ikCap ≠ 0#64 := by rintro rfl; simp at hpos
    have hlayout : RustLayoutOk ikCap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine let_state_pk ?_; intro s_call
    refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
      (ikPtr, ikCap.toNat, 1, st) hC.deallocX
      (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
      (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
      (ret_pc := (blkPl_111).base + 2020#64) (by simp [s_call, arm64_norm])
      (T := A.pool lim st s_call ∗ A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat ∗
        stackAt sp' extHookStack)
      (φ := ikPtr = ikPtr ∧ ikCap.toNat = ikCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk ikCap.toNat 1 ∧
        LsRetAddr624 ((blkPl_111).base + 2020#64))
      (by simp_all [s_call, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 2020#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, hx25_cs, _, _, hx28_cs, _⟩
    set st1 := M.stepEvents (rustDeallocEvents ikCap.toNat 1) st
    refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st1 s2 ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_7e4_placed_wpX (st := st1) hC bkAct kyAct
        ⟨by simp [hsp2, s_call, hsp_eq, arm64_norm], hsp2_align, hcl2, by simp [htr2, s_call, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, s_call, hx19, arm64_norm])
        (by simp [hx28_cs, s_call, hx28, arm64_norm])
        (by simp [hx25_cs, s_call, hx25, arm64_norm]) hbk)
      fun sf Pf h => (h.frame_eq (by sep_ac_rfl)).prepend_dealloc ikCap.toNat

set_option maxHeartbeats 800000 in
theorem tail_7b8_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret w0 msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (msgAct ikAct bkAct kyAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1976#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx8 : s.readReg64 .x8 = errTag) (hx26 : s.readReg64 .x26 = msgCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ (sret ↦₆₄ w0) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st s ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        ((sret ↦₆₄ errTag) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases msgAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc msgCap msgPtr false = ⌜msgCap = noneCap ∨ msgCap = 0#64⌝ := rfl
    rw [hdealloc]; refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : msgCap = 0#64 := hcap.resolve_left hmsg
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2000#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc ikCap ikPtr ikAct ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st _ ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sp' + 96#64) ↦₆₄ msgPtr)))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_7d0_placed_wpX hC ikAct bkAct kyAct
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx23, arm64_norm])
        (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hik hbk)
      fun sf Pf h => h.frame_eq (by sep_ac_rfl)
  | true =>
    have hdealloc : deallocSlot A.repAlloc msgCap msgPtr true =
        (⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
          A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : msgCap ≠ 0#64 := by rintro rfl; simp at hpos
    have hlayout : RustLayoutOk msgCap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine let_state_pk ?_; intro s_call
    refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
      (msgPtr, msgCap.toNat, 1, st) hC.deallocX
      (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
      (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
      (ret_pc := (blkPl_111).base + 2000#64) (by simp [s_call, arm64_norm])
      (T := A.pool lim st s_call ∗ A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
        stackAt sp' extHookStack)
      (φ := msgPtr = msgPtr ∧ msgCap.toNat = msgCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk msgCap.toNat 1 ∧
        LsRetAddr624 ((blkPl_111).base + 2000#64))
      (by simp_all [s_call, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 2000#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, hx23_cs, _, hx25_cs, _, _, hx28_cs, _⟩
    set st1 := M.stepEvents (rustDeallocEvents msgCap.toNat 1) st
    refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc ikCap ikPtr ikAct ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st1 s2 ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sp' + 96#64) ↦₆₄ msgPtr)))
      (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_7d0_placed_wpX (st := st1) hC ikAct bkAct kyAct
        ⟨by simp [hsp2, s_call, hsp_eq, arm64_norm], hsp2_align, hcl2, by simp [htr2, s_call, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, s_call, hx19, arm64_norm])
        (by simp [hx23_cs, s_call, hx23, arm64_norm])
        (by simp [hx28_cs, s_call, hx28, arm64_norm])
        (by simp [hx25_cs, s_call, hx25, arm64_norm]) hik hbk)
      fun sf Pf h => (h.frame_eq (by sep_ac_rfl)).prepend_dealloc msgCap.toNat

/-! ## 3. Presence-Error Dealloc Chain (`+0x604 .. +0x668` → `+0x80c` / `+0x504`) -/

theorem tail_654_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret msgCap msgPtr : BitVec 64}
    (msgAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1620#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool lim st s ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases msgAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc msgCap msgPtr false = ⌜msgCap = noneCap ∨ msgCap = 0#64⌝ := rfl
    rw [hdealloc]; refine SepWPp.pure_pre fun hcap => ?_
    rcases hcap with rfl | rfl
    all_goals
      refine sepWPp_end_noPanic_placed (s0 := s0) hcl ?_
      apply sepWP_seg_111; intro _m_strip; wp_steps
      refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
      exact ErrTailQPlaced.nil
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [hx19, arm64_norm]) (by apply entails_of_eq; sep_ac_rfl)
  | true =>
    have hdealloc : deallocSlot A.repAlloc msgCap msgPtr true =
        (⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
          A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2060#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre (P' := (A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_80c_placed_wpX hC
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) hpos hlt)
      fun sf Pf h => h.frame_eq (by sep_ac_rfl)

theorem tail_64c_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret ptr cap msgCap msgPtr : BitVec 64}
    (msgAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1612#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap)
    (hx26 : s.readReg64 .x26 = msgCap)
    (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hlayout : RustLayoutOk cap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
  have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  apply sepWP_seg_111; intro _m_strip; wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine let_state_pk ?_; intro s_call
  refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
    (ptr, cap.toNat, 1, st) hC.deallocX
    (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
    (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 1620#64) (by simp [s_call, arm64_norm])
    (T := A.pool lim st s_call ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
      stackAt sp' extHookStack)
    (φ := ptr = ptr ∧ cap.toNat = cap.toNat ∧
      (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk cap.toNat 1 ∧
      LsRetAddr624 ((blkPl_111).base + 1620#64))
    (by simp_all [s_call, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
    ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 1620#64 (by decide) (by decide)⟩
    (by rw [hstack]; sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, _, hx26_cs, _, _, _⟩
  set st1 := M.stepEvents (rustDeallocEvents cap.toNat 1) st
  refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool lim st1 s2 ∗
      stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗ emp)
    (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, sepConj_emp, arm64_norm]; sep_ac_rfl) ?_
  exact frame_noPanic_pk
    (tail_654_placed_wpX (st := st1) hC msgAct
      ⟨by simp [hsp2, s_call, hsp_eq, arm64_norm], hsp2_align, hcl2,
        by simp [htr2, s_call, htr, arm64_norm]⟩
      hpc2 hrun2 (by simp [hx19_cs, s_call, hx19, arm64_norm])
      (by simp [hx26_cs, s_call, hx26, arm64_norm]))
    fun sf Pf h => (h.frame_eq (by simp [sepConj_emp])).prepend_dealloc cap.toNat

theorem tail_638_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret kyCap kyPtr msgCap msgPtr : BitVec 64}
    (kyAct msgAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1592#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc kyCap kyPtr kyAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases kyAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc kyCap kyPtr false = ⌜kyCap = noneCap ∨ kyCap = 0#64⌝ := rfl
    rw [hdealloc]; refine SepWPp.pure_pre fun hcap => ?_
    rcases hcap with rfl | rfl
    all_goals
      refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1620#64) ?_
      apply sepWP_seg_111; intro _m_strip; wp_steps
      refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
      refine SepWPp.mono_pre (P' := deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool lim st _ ∗
          stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
        (by apply entails_of_eq; sep_ac_rfl) ?_
      exact tail_654_placed_wpX hC msgAct
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx26, arm64_norm])
  | true =>
    have hdealloc : deallocSlot A.repAlloc kyCap kyPtr true =
        (⌜0 < kyCap.toNat ∧ kyCap.toNat < 2 ^ 63 ∧ kyPtr ≠ 0#64⌝ ∗
          A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1612#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre (P' := A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact tail_64c_placed_wpX hC msgAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [hx26, arm64_norm]) hpos hlt

theorem tail_604_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret ikCap ikPtr msgCap msgPtr : BitVec 64}
    (ikAct msgAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1540#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx23 : s.readReg64 .x23 = ikCap) (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases ikAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc ikCap ikPtr false = ⌜ikCap = noneCap ∨ ikCap = 0#64⌝ := rfl
    rw [hdealloc]; refine SepWPp.pure_pre fun hcap => ?_
    rcases hcap with rfl | rfl
    all_goals
      refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1620#64) ?_
      apply sepWP_seg_111; intro _m_strip; wp_steps
      refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
      refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool lim st _ ∗
          stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr))
        (by apply entails_of_eq; sep_ac_rfl) ?_
      exact frame_noPanic_pk
        (tail_654_placed_wpX hC msgAct
          (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
            (by simp [htr, arm64_norm]))
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx26, arm64_norm]))
        fun sf Pf h => h.frame_eq (by sep_ac_rfl)
  | true =>
    have hdealloc : deallocSlot A.repAlloc ikCap ikPtr true =
        (⌜0 < ikCap.toNat ∧ ikCap.toNat < 2 ^ 63 ∧ ikPtr ≠ 0#64⌝ ∗
          A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1612#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre (P' := (A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_64c_placed_wpX hC msgAct
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [hx26, arm64_norm]) hpos hlt)
      fun sf Pf h => h.frame_eq (by sep_ac_rfl)

/-! ## 4. Word-Level Entry Blocks (`+0x5e0`, `+0x61c`, `+0x66c`, `+0x678`, `+0x7a8`) -/

theorem entry_678_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret w0 w1 x27v msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (msgAct ikAct bkAct kyAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1656#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v) (hx26 : s.readReg64 .x26 = msgCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st s ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1976#64) ?_
  apply sepWP_seg_111; intro _m_strip; wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ (sret ↦₆₄ w0) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st _ ∗
      stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      ((sret + 8#64) ↦₆₄ x27v))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  exact frame_noPanic_pk
    (tail_7b8_placed_wpX hC msgAct ikAct bkAct kyAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [errTag, arm64_norm]) (by simp [hx26, arm64_norm])
      (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hmsg hik hbk)
    fun sf Pf h => h.frame_eq (by sep_ac_rfl)

theorem entry_66c_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret w0 w1 x27v ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (ikAct bkAct kyAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1644#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st s ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2000#64) ?_
  apply sepWP_seg_111; intro _m_strip; wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc ikCap ikPtr ikAct ∗
      ((sp' + 104#64) ↦₆₄ ikPtr) ∗ deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st _ ∗
      stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v)))
    (by apply entails_of_eq; simp only [errTag, arm64_norm]; sep_ac_rfl) ?_
  exact frame_noPanic_pk
    (tail_7d0_placed_wpX hC ikAct bkAct kyAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hik hbk)
    fun sf Pf h => h.frame_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
theorem entry_5e0_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret w0 w1 x27v kyCap kyPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    (kyAct ikAct msgAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1504#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hx23 : s.readReg64 .x23 = ikCap) (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases kyAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc kyCap kyPtr false = ⌜kyCap = noneCap ∨ kyCap = 0#64⌝ := rfl
    rw [hdealloc]; refine SepWPp.pure_pre fun hcap => ?_
    rcases hcap with rfl | rfl
    all_goals
      refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1540#64) ?_
      apply sepWP_seg_111; intro _m_strip; wp_steps
      refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
      refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc ikCap ikPtr ikAct ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗ deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool lim st _ ∗
          stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
          ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v)))
        (by apply entails_of_eq; simp only [errTag, arm64_norm]; sep_ac_rfl) ?_
      exact frame_noPanic_pk
        (tail_604_placed_wpX hC ikAct msgAct
          (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
            (by simp [htr, arm64_norm]))
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx23, arm64_norm]) (by simp [hx26, arm64_norm]))
        fun sf Pf h => h.frame_eq (by sep_ac_rfl)
  | true =>
    have hdealloc : deallocSlot A.repAlloc kyCap kyPtr true =
        (⌜0 < kyCap.toNat ∧ kyCap.toNat < 2 ^ 63 ∧ kyPtr ≠ 0#64⌝ ∗
          A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hlayout : RustLayoutOk kyCap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine let_state_pk ?_; intro s_call
    refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
      (kyPtr, kyCap.toNat, 1, st) hC.deallocX
      (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
      (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
      (ret_pc := (blkPl_111).base + 1540#64) (by simp [s_call, arm64_norm])
      (T := A.pool lim st s_call ∗ A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat ∗
        stackAt sp' extHookStack)
      (φ := kyPtr = kyPtr ∧ kyCap.toNat = kyCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk kyCap.toNat 1 ∧
        LsRetAddr624 ((blkPl_111).base + 1540#64))
      (by simp_all [s_call, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 1540#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, hx23_cs, _, _, hx26_cs, _, _, _⟩
    set st1 := M.stepEvents (rustDeallocEvents kyCap.toNat 1) st
    refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc ikCap ikPtr ikAct ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool lim st1 s2 ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v)))
      (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, errTag, arm64_norm]; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_604_placed_wpX (st := st1) hC ikAct msgAct
        ⟨by simp [hsp2, s_call, hsp_eq, arm64_norm], hsp2_align, hcl2, by simp [htr2, s_call, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, s_call, hx19, arm64_norm])
        (by simp [hx23_cs, s_call, hx23, arm64_norm])
        (by simp [hx26_cs, s_call, hx26, arm64_norm]))
      fun sf Pf h => (h.frame_eq (by sep_ac_rfl)).prepend_dealloc kyCap.toNat

set_option maxHeartbeats 800000 in
theorem entry_61c_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret w0 w1 x27v bkCap bkPtr kyCap kyPtr msgCap msgPtr : BitVec 64}
    (bkAct kyAct msgAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1564#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hx26 : s.readReg64 .x26 = msgCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc bkCap bkPtr bkAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A.repAlloc kyCap kyPtr kyAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases bkAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc bkCap bkPtr false = ⌜bkCap = noneCap ∨ bkCap = 0#64⌝ := rfl
    rw [hdealloc]; refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : bkCap = 0#64 := hcap.resolve_left hbk
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1592#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc kyCap kyPtr kyAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ 0#64)))
      (by apply entails_of_eq; simp only [errTag, arm64_norm]; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_638_placed_wpX hC kyAct msgAct
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx26, arm64_norm]))
      fun sf Pf h => h.frame_eq (by sep_ac_rfl)
  | true =>
    have hdealloc : deallocSlot A.repAlloc bkCap bkPtr true =
        (⌜0 < bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0#64⌝ ∗
          A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : bkCap ≠ 0#64 := by rintro rfl; simp at hpos
    have hlayout : RustLayoutOk bkCap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine let_state_pk ?_; intro s_call
    refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
      (bkPtr, bkCap.toNat, 1, st) hC.deallocX
      (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
      (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
      (ret_pc := (blkPl_111).base + 1592#64) (by simp [s_call, arm64_norm])
      (T := A.pool lim st s_call ∗ A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗
        stackAt sp' extHookStack)
      (φ := bkPtr = bkPtr ∧ bkCap.toNat = bkCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk bkCap.toNat 1 ∧
        LsRetAddr624 ((blkPl_111).base + 1592#64))
      (by simp_all [s_call, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 1592#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, hx25_cs, hx26_cs, _, hx28_cs, _⟩
    set st1 := M.stepEvents (rustDeallocEvents bkCap.toNat 1) st
    refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc kyCap kyPtr kyAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool lim st1 s2 ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap)))
      (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, errTag, arm64_norm]; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_638_placed_wpX (st := st1) hC kyAct msgAct
        ⟨by simp [hsp2, s_call, hsp_eq, arm64_norm], hsp2_align, hcl2, by simp [htr2, s_call, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, s_call, hx19, arm64_norm])
        (by simp [hx28_cs, s_call, hx28, arm64_norm])
        (by simp [hx25_cs, s_call, hx25, arm64_norm])
        (by simp [hx26_cs, s_call, hx26, arm64_norm]))
      fun sf Pf h => (h.frame_eq (by sep_ac_rfl)).prepend_dealloc bkCap.toNat

theorem entry_7a8_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret w0 w1 w2 x8v x9v x10v msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (msgAct ikAct bkAct kyAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1960#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx8 : s.readReg64 .x8 = x8v) (hx9 : s.readReg64 .x9 = x9v) (hx10 : s.readReg64 .x10 = x10v)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st s ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x9v) ∗
          ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64))) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1976#64) ?_
  apply sepWP_seg_111; intro _m_strip; wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine SepWPp.mono_pre (P' := (deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ (sret ↦₆₄ w0) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st _ ∗
      stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      (((sret + 8#64) ↦₆₄ x9v) ∗ ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64)))))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  exact frame_noPanic_pk
    (tail_7b8_placed_wpX hC msgAct ikAct bkAct kyAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [errTag, arm64_norm]) (by simp [hx26, arm64_norm])
      (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hmsg hik hbk)
    fun sf Pf h => h.frame_eq (by sep_ac_rfl)

private theorem etbw_sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : SepProp} {Q Q' Qp : Arm64.State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) (hq : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hs, ⟨hpc, hrun, Pf, hmf, hQ, hv⟩ | hpan⟩
  · exact ⟨sf, hs, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hQ, hv⟩⟩
  · exact ⟨sf, hs, Or.inr hpan⟩

private theorem etbw_memRegion248_words2 (sret : BitVec 64) :
    memRegion sret 248 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ memRegion (sret + 16#64) 232 := by
  rw [show (248 : Nat) = 8 + (8 + 232) by decide,
    Prost.memRegion_split sret 8 240 (by decide),
    Prost.memRegion_split (sret + 8#64) 8 232 (by decide),
    ProofLib.memRegion_eight sret,
    ProofLib.memRegion_eight (sret + 8#64),
    sepExists_sepConj_left]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]

private theorem etbw_memRegion248_words3 (sret : BitVec 64) :
    memRegion sret 248 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
          memRegion (sret + 24#64) 224 := by
  rw [etbw_memRegion248_words2 sret, show (232 : Nat) = 8 + 224 by decide,
    Prost.memRegion_split (sret + 16#64) 8 224 (by decide),
    ProofLib.memRegion_eight (sret + 16#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]

theorem entry_7a8_placed_wpE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret x8v x9v x10v msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    {e : SignalProtocolError} (msgAct ikAct bkAct kyAct : Bool) {R : SepProp}
    {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1960#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx8 : s.readReg64 .x8 = x8v) (hx9 : s.readReg64 .x9 = x9v) (hx10 : s.readReg64 .x10 = x10v)
    (hw : speWordsOf e x9v x8v x10v)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (memRegion sret 248 ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st s ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (pksmErrE A.repAlloc [] sret e ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  rw [etbw_memRegion248_words3 sret]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w0 => SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w2 => ?_
  refine SepWPp.mono_pre
    (P' := (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
      deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A.repAlloc kyCap kyPtr kyAct ∗ A.pool lim st s ∗
      stackAt sp' (Prost.skipFieldStackX 100) ∗
      (memRegion (sret + 24#64) 224 ∗ R))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine etbw_sepWPp_mono_post
    (entry_7a8_placed_wpX hC msgAct ikAct bkAct kyAct hst hpc hrun hx19 hx8 hx9 hx10 hx26 hx23 hx28
      hx25 hmsg hik hbk)
    fun _ _ h => etb_errTailQPlaced_mono h ?_
  refine Entails.trans
    (Q := ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x9v) ∗
        ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64))) ∗ memRegion (sret + 24#64) 224) ∗
      (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
    (by apply entails_of_eq; sep_ac_rfl)
    (sepConj_mono_left (etb_speWordsOf_entails_pksmErrE A.repAlloc [] sret x9v x8v x10v e hw))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBWPlacedBudget
