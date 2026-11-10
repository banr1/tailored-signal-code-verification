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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBWPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6ExitsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6StatesPlaced
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded `[LibsignalPlacement]` Pack, `IdentityKey`, and `SignalMessage` Error/Dealloc Tails

Allocation-budget (`RustCliAllocBudget M`) proofs of the `+0x970..+0xa58` deallocation chains,
Kyber `Box<[u8]>` cleanup, and `+0x978` / `+0x9f0` exact-`pksmErrE` error entries on
`preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCWPlacedBudget

open Arm64 Arm64.Obj ProofLib.GenPlacedFetches ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open CryptoGames CryptoGames.Ratchet
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
  SepWPp ErrTailQPlaced etb_errTailQPlaced_mono tail_80c_placed_wpX
  tail_a4c_placed_wpX tail_a38_placed_wpX tail_a28_placed_wpX tail_a24_placed_wpX
  deallocChain_970_placed_wpX tail_a10_placed_wpX tail_990_placed_wpX tail_a0c_placed_wpX
  pan_a68_placed_wpX e_978_copy48_placed_wpE e_978_placed_wpE
  e_9f0_placed_wpE e_9f0_words2_placed_wpE
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk rustDeallocEvents
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget (
  preKeyNoPanicQp
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (
  LsRetAddr624 lsRetAddr624_blockPlacement_base_add
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (
  PksmCalleesPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget (
  sepWP_done_sync_pool_111 sepWP_seg_111
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBWPlacedBudget (
  ErrTailQPlaced etb_errTailQPlaced_mono sepWPp_anyQp_of_noPanic tail_80c_placed_wpX
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustDeallocExternSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget (
  sepWPp_end_noPanic_placed
)

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

private theorem etcw_bv_add_sub_lit (x a b : BitVec 64) : x + a - b = x + (a - b) := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit etcw_bv_add_sub_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
attribute [local simp] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero

theorem ErrTailQPlaced.frame_entails [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 sf : State} {sp' sret : BitVec 64} {R G H0 Pf : SepProp}
    (h : ErrTailQPlaced A lim st s0 sp' sret R sf Pf) (hent : R ∗ G ⊢ H0) :
    ErrTailQPlaced A lim st s0 sp' sret H0 sf (Pf ∗ G) := by
  rcases h with ⟨hst, hx19, evs, hf, hPf⟩
  refine ⟨hst, hx19, evs, hf, Entails.trans (sepConj_mono_left hPf) ?_⟩
  refine Entails.trans
    (Q := A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ (R ∗ G))
    (by apply entails_of_eq; sep_ac_rfl)
    (sepConj_mono_right (sepConj_mono_right hent))

private theorem etcw_sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : SepProp} {Q Q' Qp : Arm64.State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) (hq : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R' hm hL
  rcases h R' hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hqf, hv⟩ | hpan⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hqf, hv⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-! ## 1. Shared Dealloc Chain (`+0xa24 .. +0xa58` → `+0x80c` / `+0x504`) -/

theorem tail_a4c_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret bkCap bkPtr : BitVec 64}
    (bkAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2636#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
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
    refine sepWPp_end_noPanic_placed (s0 := s0) hcl ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    exact ErrTailQPlaced.nil
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [hx19, arm64_norm]) (by apply entails_of_eq; sep_ac_rfl)
  | true =>
    have hdealloc : deallocSlot A.repAlloc bkCap bkPtr true =
        (⌜0 < bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0#64⌝ ∗
          A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : bkCap ≠ 0#64 := by rintro rfl; simp at hpos
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2060#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre
      (P' := (A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap)))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_80c_placed_wpX hC
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) hpos hlt)
      fun _ _ h => h.frame_eq (by sep_ac_rfl)

theorem tail_a38_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret ikCap ikPtr bkCap bkPtr : BitVec 64}
    (ikAct bkAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2616#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases ikAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc ikCap ikPtr false = ⌜ikCap = noneCap ∨ ikCap = 0#64⌝ := rfl
    rw [hdealloc]; refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : ikCap = 0#64 := hcap.resolve_left hik
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2636#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre
      (P' := (deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_a4c_placed_wpX hC bkAct
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm]) hbk)
      fun _ _ h => h.frame_eq (by sep_ac_rfl)
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
    refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded (ikPtr, ikCap.toNat, 1, st) hC.deallocX
      (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
      (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
      (ret_pc := (blkPl_111).base + 2636#64) (by simp [s_call, arm64_norm])
      (T := A.pool lim st s_call ∗ A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat ∗
        stackAt sp' extHookStack)
      (φ := ikPtr = ikPtr ∧ ikCap.toNat = ikCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk ikCap.toNat 1 ∧
        LsRetAddr624 ((blkPl_111).base + 2636#64))
      (by simp_all [s_call, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 2636#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, _, _, _, _, _, _⟩
    set st1 := M.stepEvents (rustDeallocEvents ikCap.toNat 1) st
    refine SepWPp.mono_pre
      (P' := (deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st1 s2 ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_a4c_placed_wpX hC bkAct
        ⟨by simp [hsp2, s_call, hsp_eq, arm64_norm], hsp2_align, hcl2,
          by simp [htr2, s_call, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, s_call, hx19, arm64_norm]) hbk)
      fun _ _ h => (ErrTailQPlaced.prepend_dealloc ikCap.toNat h).frame_eq (by sep_ac_rfl)

theorem tail_a28_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (ikAct bkAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2600#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hpos : 0 < msgCap.toNat) (hlt : msgCap.toNat < 2 ^ 63)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hlayout : RustLayoutOk msgCap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
  have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  apply sepWP_seg_111; intro _m_strip; wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine let_state_pk ?_; intro s_call
  refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded (msgPtr, msgCap.toNat, 1, st) hC.deallocX
    (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
    (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 2616#64) (by simp [s_call, arm64_norm])
    (T := A.pool lim st s_call ∗ A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
      stackAt sp' extHookStack)
    (φ := msgPtr = msgPtr ∧ msgCap.toNat = msgCap.toNat ∧
      (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk msgCap.toNat 1 ∧
      LsRetAddr624 ((blkPl_111).base + 2616#64))
    (by simp_all [s_call, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
    ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 2616#64 (by decide) (by decide)⟩
    (by rw [hstack]; sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_cs, _, _, _, hx23_cs, _, _, _, _, _, _, _⟩
  set st1 := M.stepEvents (rustDeallocEvents msgCap.toNat 1) st
  refine SepWPp.mono_pre
    (P' := (deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool lim st1 s2 ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr))
    (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
  exact frame_noPanic_pk
    (tail_a38_placed_wpX hC ikAct bkAct
      ⟨by simp [hsp2, s_call, hsp_eq, arm64_norm], hsp2_align, hcl2,
        by simp [htr2, s_call, htr, arm64_norm]⟩
      hpc2 hrun2 (by simp [hx19_cs, s_call, hx19, arm64_norm])
      (by simp [hx23_cs, s_call, hx23, arm64_norm]) hik hbk)
    fun _ _ h => (ErrTailQPlaced.prepend_dealloc msgCap.toNat h).frame_eq (by sep_ac_rfl)

theorem tail_a24_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (msgAct ikAct bkAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2596#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases msgAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc msgCap msgPtr false = ⌜msgCap = noneCap ∨ msgCap = 0#64⌝ := rfl
    rw [hdealloc]; refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : msgCap = 0#64 := hcap.resolve_left hmsg
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2616#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre
      (P' := (deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_a38_placed_wpX hC ikAct bkAct
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx23, arm64_norm]) hik hbk)
      fun _ _ h => h.frame_eq (by sep_ac_rfl)
  | true =>
    have hdealloc : deallocSlot A.repAlloc msgCap msgPtr true =
        (⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
          A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : msgCap ≠ 0#64 := by rintro rfl; simp at hpos
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2600#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre
      (P' := A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact tail_a28_placed_wpX hC ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hpos hlt hik hbk

/-! ## 2. Pack Ok Exit (`+0x970`) -/

theorem deallocChain_970_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State} {sp' sret msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (msgAct ikAct bkAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PackOkStatePlaced s0 sp' sret ikCap msgCap s)
    (hpc : s.pc = (blkPl_111).base + 2416#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (⌜msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap⌝ ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ deallocSlot A.repAlloc ikCap ikPtr ikAct ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx19, hx26, hx23⟩
  refine SepWPp.pure_pre fun ⟨hmsg, hik, hbk⟩ => ?_
  refine SepWPp.mono_pre
    (P' := deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
    (by apply entails_of_eq; sep_ac_rfl) ?_
  cases msgAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc msgCap msgPtr false = ⌜msgCap = noneCap ∨ msgCap = 0#64⌝ := rfl
    rw [hdealloc]; refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : msgCap = 0#64 := hcap.resolve_left hmsg
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2616#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre
      (P' := (deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact frame_noPanic_pk
      (tail_a38_placed_wpX hC ikAct bkAct
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx23, arm64_norm]) hik hbk)
      fun _ _ h => h.frame_eq (by sep_ac_rfl)
  | true =>
    have hdealloc : deallocSlot A.repAlloc msgCap msgPtr true =
        (⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
          A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : msgCap ≠ 0#64 := by rintro rfl; simp at hpos
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2600#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre
      (P' := A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact tail_a28_placed_wpX hC ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hpos hlt hik hbk

/-! ## 3. Kyber-Box Free (`+0x990`, `+0xa0c`, `+0xa10` → `+0xa24`) -/

theorem tail_a10_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2576#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kbPtr) (hx25 : s.readReg64 .x25 = kbLen)
    (hkb : kbPtr ≠ 0#64)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (boxSlot A.repAlloc kbPtr kbLen boxAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases boxAct with
  | false =>
    have hbox : boxSlot A.repAlloc kbPtr kbLen false = ⌜kbPtr = 0#64 ∨ kbLen = 0#64⌝ := rfl
    rw [hbox]; refine SepWPp.pure_pre fun hz => ?_
    obtain rfl : kbLen = 0#64 := hz.resolve_left hkb
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2596#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre
      (P' := deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact tail_a24_placed_wpX hC msgAct ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hmsg hik hbk
  | true =>
    have hbox : boxSlot A.repAlloc kbPtr kbLen true =
        (⌜0 < kbLen.toNat ∧ kbLen.toNat < 2 ^ 63 ∧ kbPtr ≠ 0#64⌝ ∗
          A.live kbPtr kbLen.toNat 1 ∗ memRegion kbPtr kbLen.toNat) := rfl
    rw [hbox]; simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : kbLen ≠ 0#64 := by rintro rfl; simp at hpos
    have hlayout : RustLayoutOk kbLen.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine let_state_pk ?_; intro s_call
    refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded (kbPtr, kbLen.toNat, 1, st) hC.deallocX
      (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
      (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
      (ret_pc := (blkPl_111).base + 2596#64) (by simp [s_call, arm64_norm])
      (T := A.pool lim st s_call ∗ A.live kbPtr kbLen.toNat 1 ∗ memRegion kbPtr kbLen.toNat ∗
        stackAt sp' extHookStack)
      (φ := kbPtr = kbPtr ∧ kbLen.toNat = kbLen.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk kbLen.toNat 1 ∧
        LsRetAddr624 ((blkPl_111).base + 2596#64))
      (by simp_all [s_call, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 2596#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, hx23_cs, _, _, hx26_cs, _, _, _, _⟩
    set st1 := M.stepEvents (rustDeallocEvents kbLen.toNat 1) st
    refine SepWPp.mono_pre
      (P' := deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st1 s2 ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    refine etcw_sepWPp_mono_post
      (tail_a24_placed_wpX (st := st1) (s0 := s0) (sret := sret) hC msgAct ikAct bkAct
        ⟨by simp [hsp2, s_call, hsp_eq, arm64_norm], hsp2_align, hcl2,
          by simp [htr2, s_call, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, s_call, hx19, arm64_norm])
        (by simp [hx26_cs, s_call, hx26, arm64_norm]) (by simp [hx23_cs, s_call, hx23, arm64_norm]) hmsg hik hbk)
      (fun _ _ h => ErrTailQPlaced.prepend_dealloc kbLen.toNat h)

theorem tail_990_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2448#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kbPtr) (hx25 : s.readReg64 .x25 = kbLen)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (boxSlot A.repAlloc kbPtr kbLen boxAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  by_cases hz : kbPtr = 0#64
  · subst hz
    refine SepWPp.mono_pre (Entails.trans (sepConj_mono_left (boxSlot_null_elim A.repAlloc kbLen boxAct))
      (entails_of_eq (emp_sepConj _))) ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2596#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre
      (P' := deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact tail_a24_placed_wpX hC msgAct ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hmsg hik hbk
  · refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2576#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre
      (P' := boxSlot A.repAlloc kbPtr kbLen boxAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact tail_a10_placed_wpX hC boxAct msgAct ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hz hmsg hik hbk

theorem tail_a0c_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2572#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kbPtr) (hx25 : s.readReg64 .x25 = kbLen)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (boxSlot A.repAlloc kbPtr kbLen boxAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  by_cases hz : kbPtr = 0#64
  · subst hz
    refine SepWPp.mono_pre (Entails.trans (sepConj_mono_left (boxSlot_null_elim A.repAlloc kbLen boxAct))
      (entails_of_eq (emp_sepConj _))) ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2596#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre
      (P' := deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact tail_a24_placed_wpX hC msgAct ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hmsg hik hbk
  · refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2576#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre
      (P' := boxSlot A.repAlloc kbPtr kbLen boxAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact tail_a10_placed_wpX hC boxAct msgAct ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hz hmsg hik hbk

/-! ## 4. Clone Alloc-Fail Panic (`+0xa68`, re-exported) -/

abbrev pan_a68_placed_wpX :=
  @CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.pan_a68_placed_wpX

/-! ## 5. Kyber-Box Exact-Err Entries (`+0x978`, `+0x9f0`) -/

private theorem etcw_memRegion24_words3 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight]

private theorem etcw_memRegion248_words7 (r : BitVec 64) :
    memRegion r 248 =
      (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (r + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (r + 16#64) ↦₆₄ w2) ∗ (∃∗ w3 : BitVec 64, (r + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (r + 32#64) ↦₆₄ w4) ∗ (∃∗ w5 : BitVec 64, (r + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (r + 48#64) ↦₆₄ w6) ∗ memRegion (r + 56#64) 192 := by
  rw [ProofLib.memRegion_split r 8 240 (by decide),
    ProofLib.memRegion_split (r + 8#64) 24 216 (by decide),
    ProofLib.memRegion_split (r + 8#64 + 24#64) 24 192 (by decide),
    ProofLib.memRegion_eight r,
    etcw_memRegion24_words3 (r + 8#64),
    etcw_memRegion24_words3 (r + 8#64 + 24#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem etcw_words4_entails_memRegion32 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [ProofLib.memRegion_split a 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) w1)
      (sepConj_mono (pointsTo64_entails_memRegion (a + 16#64) w2)
        (pointsTo64_entails_memRegion (a + 24#64) w3)))

private theorem etcw_words5_entails_memRegion40 (a w0 w1 w2 w3 w4 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ⊢ memRegion a 40 := by
  rw [ProofLib.memRegion_split a 8 32 (by decide)]
  refine sepConj_mono (pointsTo64_entails_memRegion a w0) ?_
  have h32 := etcw_words4_entails_memRegion32 (a + 8#64) w1 w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32
  exact h32

private theorem etcw_ikErr_speDetached_intro {A : RustAlloc} {fn : List (BitVec 8)}
    {ik : List (BitVec 8)} {e : SignalProtocolError}
    (hik : PublicKey.deserialize ik = .error e) (w2 w3 w4 w5 : BitVec 64) :
    SepProp.emp ⊢
      pksm0c_speDetached A fn (ikErrWords e).1 (ikErrWords e).2 w2 w3 w4 w5 e := by
  rcases CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.deserialize_error_cases hik with
      rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · show SepProp.emp ⊢ ⌜speWord 7 = speWord 7⌝
    exact Entails.pure_right_only rfl (Entails.refl _)
  · show SepProp.emp ⊢ ⌜speWord 8 = speWord 8 ∧ (t.zeroExtend 64).truncate 8 = t⌝
    exact Entails.pure_right_only ⟨rfl, by bv_bits⟩ (Entails.refl _)
  · show SepProp.emp ⊢ ⌜speWord 9 = speWord 9 ∧ BitVec.ofNat 64 n = BitVec.ofNat 64 n⌝
    exact Entails.pure_right_only ⟨rfl, rfl⟩ (Entails.refl _)

private theorem etcw_ikErr_speDetached_elim {A : RustAlloc} {fn : List (BitVec 8)}
    {ik : List (BitVec 8)} {e : SignalProtocolError}
    (hik : PublicKey.deserialize ik = .error e) (d0 d1 d2 d3 d4 d5 : BitVec 64) :
    pksm0c_speDetached A fn d0 d1 d2 d3 d4 d5 e ⊢ SepProp.emp := by
  rcases CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.deserialize_error_cases hik with
      rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · show ⌜d0 = speWord 7⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _
  · show ⌜d0 = speWord 8 ∧ d1.truncate 8 = t⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _
  · show ⌜d0 = speWord 9 ∧ d1 = BitVec.ofNat 64 n⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _

theorem e_978_copy48_placed_wpE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    (fn : List (BitVec 8)) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {e : SignalProtocolError}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : IdentErrStatePlaced s0 sp' sret kbPtr kbLen ikCap msgCap s)
    (hpc : s.pc = (blkPl_111).base + 2424#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = w0)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 144#64) ↦₆₄ w1) ∗ ((sp' + 152#64) ↦₆₄ w2) ∗ ((sp' + 160#64) ↦₆₄ w3) ∗
        ((sp' + 168#64) ↦₆₄ w4) ∗ ((sp' + 352#64) ↦₆₄ w5) ∗
        pksm0c_speDetached A.repAlloc fn w0 w1 w2 w3 w4 w5 e ∗ memRegion sret 248 ∗
        boxSlot A.repAlloc kbPtr kbLen boxAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (pksmErrE A.repAlloc fn sret e ∗ memRegion (sp' + 144#64) 32 ∗
          memRegion (sp' + 352#64) 8 ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx25, hx26, hx23, hx19⟩
  rw [etcw_memRegion248_words7 sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ => ?_
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2448#64) ?_
  apply sepWP_seg_111; intro _m_strip; wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine SepWPp.mono_pre
    (P' := (boxSlot A.repAlloc kbPtr kbLen boxAct ∗
      deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      (((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ w0) ∗ ((sret + 16#64) ↦₆₄ w1) ∗
          ((sret + 24#64) ↦₆₄ w2) ∗ ((sret + 32#64) ↦₆₄ w3) ∗ ((sret + 40#64) ↦₆₄ w4) ∗
          ((sret + 48#64) ↦₆₄ w5) ∗ memRegion (sret + 56#64) 192 ∗
          pksm0c_speDetached A.repAlloc fn w0 w1 w2 w3 w4 w5 e) ∗
        (((sp' + 144#64) ↦₆₄ w1) ∗ ((sp' + 152#64) ↦₆₄ w2) ∗
          ((sp' + 160#64) ↦₆₄ w3) ∗ ((sp' + 168#64) ↦₆₄ w4)) ∗
        ((sp' + 352#64) ↦₆₄ w5)))
    (by apply entails_of_eq; simp only [errTag, arm64_norm]; sep_ac_rfl) ?_
  have hm32 := etcw_words4_entails_memRegion32 (sp' + 144#64) w1 w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm32
  exact frame_noPanic_pk
    (tail_990_placed_wpX (s0 := s0) (sret := sret) hC boxAct msgAct ikAct bkAct
      (PreKeyPostState.of_steps (s0 := s0) hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hmsg hik hbk)
    fun _ _ h => ErrTailQPlaced.frame_entails h (Entails.trans
      (sepConj_mono_right (sepConj_mono
        (errCopy48_entails_pksmErrE A.repAlloc fn sret w0 w1 w2 w3 w4 w5 e)
        (sepConj_mono hm32
          (pointsTo64_entails_memRegion (sp' + 352#64) w5))))
      (by apply entails_of_eq; sep_ac_rfl))

theorem e_978_placed_wpE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    (fn : List (BitVec 8)) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    {ik : List (BitVec 8)} {e : SignalProtocolError}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hik_err : PublicKey.deserialize ik = .error e)
    (hst : IdentErrStatePlaced s0 sp' sret kbPtr kbLen ikCap msgCap s)
    (hpc : s.pc = (blkPl_111).base + 2424#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = (ikErrWords e).1)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ memRegion (sp' + 152#64) 24 ∗
        speAt A.repAlloc fn (sp' + 312#64) e ∗ memRegion sret 248 ∗
        boxSlot A.repAlloc kbPtr kbLen boxAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (pksmErrE A.repAlloc fn sret e ∗ memRegion (sp' + 144#64) 32 ∗
          memRegion (sp' + 312#64) 48 ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  rw [etcw_memRegion24_words3 (sp' + 152#64)]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (pksm0c_speAt_detach A.repAlloc fn (sp' + 312#64) e)))) ?_
  simp only [pksm0c_speWords6At, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun d0 => SepWPp.exists_pre fun d1 => SepWPp.exists_pre fun d2 =>
    SepWPp.exists_pre fun d3 => SepWPp.exists_pre fun d4 => SepWPp.exists_pre fun w5 =>
    SepWPp.exists_pre fun u3 => SepWPp.exists_pre fun u2 => SepWPp.exists_pre fun u1 => ?_
  have hdet :
      pksm0c_speDetached A.repAlloc fn d0 d1 d2 d3 d4 w5 e ⊢
        pksm0c_speDetached A.repAlloc fn (ikErrWords e).1 (ikErrWords e).2 u1 u2 u3 w5 e :=
    Entails.trans (etcw_ikErr_speDetached_elim hik_err d0 d1 d2 d3 d4 w5)
      (etcw_ikErr_speDetached_intro hik_err u1 u2 u3 w5)
  have hm40 := etcw_words5_entails_memRegion40 (sp' + 312#64) d0 d1 d2 d3 d4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm40
  refine SepWPp.mono_pre
    (P' := ((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ ((sp' + 152#64) ↦₆₄ u1) ∗
      ((sp' + 160#64) ↦₆₄ u2) ∗ ((sp' + 168#64) ↦₆₄ u3) ∗ ((sp' + 352#64) ↦₆₄ w5) ∗
      pksm0c_speDetached A.repAlloc fn (ikErrWords e).1 (ikErrWords e).2 u1 u2 u3 w5 e ∗
      memRegion sret 248 ∗
      boxSlot A.repAlloc kbPtr kbLen boxAct ∗
      deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ (memRegion (sp' + 312#64) 40 ∗ R))
    (by
      refine Entails.trans
        (Q := (((sp' + 312#64) ↦₆₄ d0) ∗ ((sp' + 320#64) ↦₆₄ d1) ∗ ((sp' + 328#64) ↦₆₄ d2) ∗
            ((sp' + 336#64) ↦₆₄ d3) ∗ ((sp' + 344#64) ↦₆₄ d4)) ∗
          pksm0c_speDetached A.repAlloc fn d0 d1 d2 d3 d4 w5 e ∗
          (((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ ((sp' + 152#64) ↦₆₄ u1) ∗
            ((sp' + 160#64) ↦₆₄ u2) ∗ ((sp' + 168#64) ↦₆₄ u3) ∗ ((sp' + 352#64) ↦₆₄ w5) ∗
            memRegion sret 248 ∗
            boxSlot A.repAlloc kbPtr kbLen boxAct ∗
            deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
            deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
            ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
            A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
        (by apply entails_of_eq; sep_ac_rfl) ?_
      refine Entails.trans (sepConj_mono hm40 (sepConj_mono_left hdet)) ?_
      apply entails_of_eq; sep_ac_rfl) ?_
  refine etcw_sepWPp_mono_post
    (e_978_copy48_placed_wpE hC fn boxAct msgAct ikAct bkAct hst hpc hrun hx8 hmsg hik hbk)
    fun _ _ h => etb_errTailQPlaced_mono h ?_
  have h48 : memRegion (sp' + 312#64) 48 =
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
    have hs := ProofLib.memRegion_split (sp' + 312#64) 40 8 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
    exact hs
  rw [h48]
  apply entails_of_eq; sep_ac_rfl

theorem e_9f0_placed_wpE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    (fn : List (BitVec 8)) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    {e : SignalProtocolError}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hst : SigMsgErrStatePlaced s0 sp' sret kbPtr kbLen ikCap msgCap s)
    (hpc : s.pc = (blkPl_111).base + 2544#64)
    (hrun : s.status = .Running)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (speAt A.repAlloc fn (sp' + 176#64) e ∗ memRegion sret 248 ∗
        boxSlot A.repAlloc kbPtr kbLen boxAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (pksmErrE A.repAlloc fn sret e ∗ memRegion (sp' + 176#64) 48 ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, _, hx28, hx25, hx26, hx23, hx19⟩
  rw [etcw_memRegion248_words7 sret]
  refine SepWPp.mono_pre (sepConj_mono_left (pksm0c_speAt_detach A.repAlloc fn (sp' + 176#64) e)) ?_
  simp only [pksm0c_speWords6At, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun u0 => SepWPp.exists_pre fun u1 => SepWPp.exists_pre fun u2 =>
    SepWPp.exists_pre fun u3 => SepWPp.exists_pre fun u4 => SepWPp.exists_pre fun u5 => ?_
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2572#64) ?_
  apply sepWP_seg_111; intro _m_strip; wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  have hm48 := pksm0c_words6_entails_memRegion48 (sp' + 176#64) u0 u1 u2 u3 u4 u5
  unfold pksm0c_speWords6At at hm48
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm48
  refine SepWPp.mono_pre
    (P' := (boxSlot A.repAlloc kbPtr kbLen boxAct ∗
      deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool lim st _ ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      (((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ u0) ∗ ((sret + 16#64) ↦₆₄ u1) ∗
          ((sret + 24#64) ↦₆₄ u2) ∗ ((sret + 32#64) ↦₆₄ u3) ∗ ((sret + 40#64) ↦₆₄ u4) ∗
          ((sret + 48#64) ↦₆₄ u5) ∗ memRegion (sret + 56#64) 192 ∗
          pksm0c_speDetached A.repAlloc fn u0 u1 u2 u3 u4 u5 e) ∗
        (((sp' + 176#64) ↦₆₄ u0) ∗ ((sp' + 184#64) ↦₆₄ u1) ∗ ((sp' + 192#64) ↦₆₄ u2) ∗
          ((sp' + 200#64) ↦₆₄ u3) ∗ ((sp' + 208#64) ↦₆₄ u4) ∗ ((sp' + 216#64) ↦₆₄ u5))))
    (by apply entails_of_eq; simp only [errTag, arm64_norm]; sep_ac_rfl) ?_
  exact frame_noPanic_pk
    (tail_a0c_placed_wpX (s0 := s0) (sret := sret) hC boxAct msgAct ikAct bkAct
      (PreKeyPostState.of_steps (s0 := s0) hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hmsg hik hbk)
    fun _ _ h => ErrTailQPlaced.frame_entails h (Entails.trans
      (sepConj_mono_right (sepConj_mono
        (errCopy48_entails_pksmErrE A.repAlloc fn sret u0 u1 u2 u3 u4 u5 e) hm48))
      (by apply entails_of_eq; sep_ac_rfl))

theorem e_9f0_words2_placed_wpE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    (fn : List (BitVec 8)) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    {ew0 ew1 ew2 ew3 ew4 ew5 : BitVec 64} {e : SignalProtocolError}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp} {Qp : State → SepProp → Prop}
    (hpack : ∀ b : BitVec 64,
      (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢ speAt A.repAlloc fn b e)
    (hst : SigMsgErrStatePlaced s0 sp' sret kbPtr kbLen ikCap msgCap s)
    (hpc : s.pc = (blkPl_111).base + 2544#64)
    (hrun : s.status = .Running)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
        ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
        ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ∗
        memRegion sret 248 ∗
        boxSlot A.repAlloc kbPtr kbLen boxAct ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced A lim st s0 sp' sret
        (pksmErrE A.repAlloc fn sret e ∗ memRegion (sp' + 176#64) 48 ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ R))
      Qp := by
  have hm32 : ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
      ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ⊢
      memRegion (sp' + 192#64) 32 := by
    have h32 := etcw_words4_entails_memRegion32 (sp' + 192#64) ew2 ew3 ew4 ew5
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32
    exact h32
  have hspe : ((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
      ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
      ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ⊢
      speAt A.repAlloc fn (sp' + 176#64) e := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right hm32)) ?_
    have hp := hpack (sp' + 176#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp
    exact hp
  refine SepWPp.mono_pre
    (P' := speAt A.repAlloc fn (sp' + 176#64) e ∗ memRegion sret 248 ∗
      boxSlot A.repAlloc kbPtr kbLen boxAct ∗
      deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
    (by
      refine Entails.trans
        (Q := (((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
            ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
            ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5)) ∗
          (memRegion sret 248 ∗
            boxSlot A.repAlloc kbPtr kbLen boxAct ∗
            deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
            deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
            ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
            A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
        (by apply entails_of_eq; sep_ac_rfl) ?_
      exact sepConj_mono_left hspe) ?_
  exact e_9f0_placed_wpE hC fn boxAct msgAct ikAct bkAct hst hpc hrun hmsg hik hbk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCWPlacedBudget
