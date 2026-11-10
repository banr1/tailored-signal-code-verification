/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Wire.WireCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Post-Loop Cleanup Tails for `<SignalMessage>::try_from`

Provides `VmPreserved` panic-free `SepWPp` combinators, `FreeOnlyEvs` lemmas, and relocatable
`[LibsignalPlacement]` budget-threaded proofs for the post-loop error cleanup chains (`+0x698..+0x640`
and `+0x430..+0x3c8` → `+0x440`) and `post_none_wp_placed` on Block `85`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanupBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ProtoSignalMessage SignalMessage SignalProtocolError)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks libsignalSessionLib lsmpl lsRustDeallocSym)
open CryptoVerification.RustHeap (vecHeader)
open CryptoVerification.LibsignalTripleRatchet
  (blkPC_85 blkPl_85 blkLib_eq_85 extHookStack LibsignalCodeRoLoaded withLsCodeRoLoaded
   decodeErrorAt)
open CryptoVerification.LibsignalTripleRatchetRepr (signalMessageResultAt errTag speWord noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (dropDecodeErrorName dropDecodeErrorStackX skipFieldStackX
   optVecU8At optU32At wireSignalMessageAt wireSignalMessageOf)
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWPp → WSepWPp
open CryptoVerification.LibsignalTripleRatchet.Wire
  (tryFromPlacedProg PostEpilogueStatePlaced LoopExitStatePlaced
   VRegsAt tryFromQp layoutOk_align1
   deallocSlot vecU8Buf vecU8Buf_zero vecU8Buf_dealloc
   cap_sub1_add3_hi_of_pos cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
   cap_slt_one_of_pos slt_one_of_false_cap
   optVecU8At_entails_header_dealloc optU32At_entails_memRegion8
   memRegion16_split8_8 memRegion120_split16
   pointsTo64_pair_entails_memRegion16 wireHeaders_entails_memRegion112
   spe_invalidProto_intro stackAt_sub_split entails_of_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk VmPreserved
   rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
  (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DropDecodeErrorEnv dropDecodeErrorSpecGen dropDecodeErrorSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (TripleRatchetHooksWPlaced DropDecodeErrorOkWPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
attribute [local simp, local wp_norm] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero

/-! ## `FreeOnlyEvs`, pool transport, and panic-free `SepWPp` combinators -/

theorem blk85_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (libsignalSessionLib.blockLib 85).text = true := by
  rfl

macro "wp_steps_sync_85 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_85).rebase (blkPl_85).base (hooksException _))
    blkLib_eq_85 blk85_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  first
    | refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
        (hnext := ?_)
    | refine ProofLib.SepWP.transport_atStatePool
        (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
        (hnext := ?_)
))

theorem rustLayoutOk_align1 {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    RustLayoutOk n 1 :=
  ⟨layoutOk_align1 hpos hlt, by decide⟩

/-- Total-correctness panic postcondition (`fun _ _ => False`), definitionally equal to
`TryFromLoopBudget.noPanicQp`. -/
abbrev postNoPanicQp (_s0 : State) : State → SepProp → Prop :=
  fun _ _ => False

theorem pool_eq_of_vmPreserved {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s₁ s₂ : State} (h : VmPreserved s₁ s₂) :
    A.pool lim st s₂ = A.pool lim st s₁ :=
  congrArg CryptoVerification.RustHeap.RustAlloc.pool (A.atState_eq_of_vmPreserved lim st h)

theorem freeOnly_rustDeallocEvents (size align : Nat) :
    FreeOnlyEvs (rustDeallocEvents size align) :=
  FreeOnlyEvs.singleton align size

theorem freeOnly_dropDecodeErrorEnv {evs : List AllocEvent}
    (h : DropDecodeErrorEnv evs) : FreeOnlyEvs evs := by
  rcases h with rfl | ⟨c, _, _, rfl⟩
  · exact freeOnly_rustDeallocEvents 72 8
  · exact (freeOnly_rustDeallocEvents (c * 32) 8).append (freeOnly_rustDeallocEvents 72 8)

theorem wpp_to_tryFromQp {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : WSepWPp prog ret s P Q (postNoPanicQp s0)) :
    WSepWPp prog ret s P Q (tryFromQp s0) := by
  intro R hm hL
  obtain ⟨sf, hsteps, hok | ⟨_, _, _, hqp⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact False.elim hqp
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem wpp_sync_pre {prog : Program} {ret : BitVec 64} {s : State}
    (P' : State → SepProp) {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P' s) (h : WSepWPp prog ret s (P' s) Q Qp) :
    WSepWPp prog ret s P Q Qp :=
  WSepWPp.mono_pre hent h

theorem wpp_mono_post_noPanic {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {Q Q' : State → SepProp → Prop}
    (hq : ∀ sf Pm, Q' sf Pm → Q sf Pm)
    (h : WSepWPp prog ret s P Q' (postNoPanicQp s0)) :
    WSepWPp prog ret s P Q (postNoPanicQp s0) := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pm, hmm, hqm, hv⟩ | ⟨_, _, _, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pm, hmm, hq sf Pm hqm, hv⟩⟩
  · exact False.elim hqp
  · exact (not_satisfies_false_sepConj hoom).elim

theorem wpp_frame_noPanic {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F : SepProp} {Q Q' : State → SepProp → Prop}
    (h : WSepWPp prog ret s P Q' (postNoPanicQp s0))
    (hq : ∀ sf Pm, Q' sf Pm → Q sf (Pm ∗ F)) :
    WSepWPp prog ret s (P ∗ F) Q (postNoPanicQp s0) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pm, hmm, hqm, hv⟩ | ⟨_, _, _, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pm ∗ F, hmm, hq sf Pm hqm, hv⟩⟩
  · exact False.elim hqp
  · exact (not_satisfies_false_sepConj hoom).elim

theorem wpp_bind_frame_noPanic {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P F P2' : SepProp} {R1 : State → Prop}
    {Q : State → SepProp → Prop}
    (h1 : WSepWPp prog mid s P (fun sm Pm => R1 sm ∧ (Pm ⊢ P2')) (postNoPanicQp s0))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → R1 sm →
      WSepWPp prog ret sm (P2' ∗ F) Q (postNoPanicQp s0)) :
    WSepWPp prog ret s (P ∗ F) Q (postNoPanicQp s0) := by
  refine WSepWPp.bind
    (wpp_frame_noPanic (Q := fun sm Pm => R1 sm ∧ (Pm ⊢ P2' ∗ F)) h1
      fun sm Pm ⟨hr, hent⟩ => ⟨hr, sepConj_mono_left hent⟩) ?_
  intro sm Pm hpcm hrunm ⟨hr, hent⟩
  exact WSepWPp.mono_pre hent (h2 sm hpcm hrunm hr)

theorem wpp_of_sepWP_end_noPanic_placed [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : ProofLib.SepWP prog ret s P
      (fun sf Pf => VRegsAt s sf ∧ (LibsignalCodeRoLoaded lsmpl sf.mem → Q sf Pf))) :
    WSepWPp prog ret s P Q (postNoPanicQp s0) := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hv, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq (hcl.of_keepsFrozen hsteps.keepsFrozen), hv.eq⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem wpp_call_noPanic_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {s0 s : State} {P T F : SepProp} {φ : Prop}
    {Q : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalCodeRoLoaded lsmpl sf.mem →
      CalleeSavedPreserved s sf →
      WSepWPp prog ret sf (spec.post x s sf ∗ F) Q (postNoPanicQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    WSepWPp prog ret s P Q (postNoPanicQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    have hcl_m := hcl.of_keepsFrozen hsteps.keepsFrozen
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [State.spAligned, hspm, ← State.spAligned]; exact hsp
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hcl_m hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withLsCodeRoLoaded] at hpost; rw [hpan sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost; rw [hexit sm code] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hoom; rw [hoom_eq sm] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-! ## Relocatable `[LibsignalPlacement]` cleanup lemmas (Block `85`) -/

theorem cleanup_698_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (st : M.σ) {s0 s : State} {sp' ptr cap : BitVec 64}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1688#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap)
    (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) (_hptr : ptr ≠ 0#64) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcall := hS.alloc.dealloc
  have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
  refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl1
  refine wpp_call_noPanic_placed (ptr, cap.toNat, 1, st) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align [hsp_eq] hsp) hcl1
    (ret_pc := (blkPl_85).base + 1696#64) (by simp [arm64_norm])
    (T := A.pool lim st s ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ stackAt sp' extHookStack)
    (φ := RustLayoutOk cap.toNat 1 ∧ LsRetAddr624 ((blkPl_85).base + 1696#64))
    (by simp [hx0, hx1, hsp_eq, rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
    ⟨rustLayoutOk_align1 hpos hlt,
      lsRetAddr624_blockPlacement_base_add 85 1696#64 (by decide) (by decide)⟩
    (by rw [hstack]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 _
  dsimp only [rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    rustCliDeallocBudgetExternSpecWithStack]
  rw [sepConj_assoc]; refine WSepWPp.pure_pre (fun htr2 => ?_)
  refine wpp_of_sepWP_end_noPanic_placed hcl2 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl3
  refine ⟨PostEpilogueStatePlaced.of_steps hcl3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
      (by simp [htr2, htr, arm64_norm]),
    rustDeallocEvents cap.toNat 1, freeOnly_rustDeallocEvents cap.toNat 1, ?_⟩
  apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; sep_ac_rfl

theorem cleanup_684_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (st : M.σ) {s0 s : State} {sp' adCap adPtr : BitVec 64} (adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1668#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = adCap) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 88#64) ↦₆₄ adPtr) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases adAct with
  | false =>
    have hdealloc : deallocSlot A.repAlloc adCap adPtr false = ⌜adCap = noneCap ∨ adCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine WSepWPp.pure_pre (fun hcap => ?_)
    rcases hcap with rfl | rfl
    · refine wpp_of_sepWP_end_noPanic_placed hcl ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
      intro hcl1
      refine ⟨PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]), [], FreeOnlyEvs.nil, ?_⟩
      apply entails_of_eq; simp only [M.stepEvents_nil, arm64_norm]
    · refine wpp_of_sepWP_end_noPanic_placed hcl ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
      intro hcl1
      refine ⟨PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]), [], FreeOnlyEvs.nil, ?_⟩
      apply entails_of_eq; simp only [M.stepEvents_nil, arm64_norm]
  | true =>
    have hdealloc : deallocSlot A.repAlloc adCap adPtr true =
        (⌜0 < adCap.toNat ∧ adCap.toNat < 2 ^ 63 ∧ adPtr ≠ 0#64⌝ ∗
          A.live adPtr adCap.toNat 1 ∗ memRegion adPtr adCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]
    refine WSepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hnext := @cleanup_698_wp_placed _ M A lim H hS st s0
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1688#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_sync_pre (fun s1 => (A.live adPtr adCap.toNat 1 ∗ memRegion adPtr adCap.toNat ∗
        A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗ ((sp' + 88#64) ↦₆₄ adPtr))
      (by apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (hnext (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) hpos hlt hptr)
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_; apply entails_of_eq; sep_ac_rfl

theorem cleanup_668_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (st : M.σ) {s0 s : State} {sp' pqCap pqPtr adCap adPtr : BitVec 64} (pqAct adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1640#64)
    (hrun : s.status = .Running)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases pqAct with
  | false =>
    have hnext := @cleanup_684_wp_placed _ M A lim H hS st s0
    have hdealloc : deallocSlot A.repAlloc pqCap pqPtr false = ⌜pqCap = noneCap ∨ pqCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine WSepWPp.pure_pre (fun hcap => ?_)
    rcases hcap with rfl | rfl
    · refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1668#64) ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
      intro hcl1
      refine wpp_sync_pre (fun s1 => (deallocSlot A.repAlloc adCap adPtr adAct ∗
          ((sp' + 88#64) ↦₆₄ adPtr) ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗
          ((sp' + 96#64) ↦₆₄ pqPtr))
        (by apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl) ?_
      refine wpp_frame_noPanic
        (hnext adAct (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
            (by simp [htr, arm64_norm]))
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx22, arm64_norm]))
        fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
      refine Entails.trans (sepConj_mono_left hent) ?_; apply entails_of_eq; sep_ac_rfl
    · refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1668#64) ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
      intro hcl1
      refine wpp_sync_pre (fun s1 => (deallocSlot A.repAlloc adCap adPtr adAct ∗
          ((sp' + 88#64) ↦₆₄ adPtr) ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗
          ((sp' + 96#64) ↦₆₄ pqPtr))
        (by apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl) ?_
      refine wpp_frame_noPanic
        (hnext adAct (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
            (by simp [htr, arm64_norm]))
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx22, arm64_norm]))
        fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
      refine Entails.trans (sepConj_mono_left hent) ?_; apply entails_of_eq; sep_ac_rfl
  | true =>
    have hdealloc : deallocSlot A.repAlloc pqCap pqPtr true =
        (⌜0 < pqCap.toNat ∧ pqCap.toNat < 2 ^ 63 ∧ pqPtr ≠ 0#64⌝ ∗
          A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine WSepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_call_noPanic_placed (pqPtr, pqCap.toNat, 1, st) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align [hsp_eq] hsp) hcl1
      (ret_pc := (blkPl_85).base + 1668#64) (by simp [arm64_norm])
      (T := A.pool lim st s ∗ A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat ∗
        stackAt sp' extHookStack)
      (φ := RustLayoutOk pqCap.toNat 1 ∧ LsRetAddr624 ((blkPl_85).base + 1668#64))
      (by
        simp [hsp_eq, rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rustLayoutOk_align1 hpos hlt,
        lsRetAddr624_blockPlacement_base_add 85 1668#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine WSepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨_, _, _, hx22_cs, _⟩
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    let st₁ := M.stepEvents (rustDeallocEvents pqCap.toNat 1) st
    have hnext := @cleanup_684_wp_placed _ M A lim H hS st₁ s0
    refine WSepWPp.mono_pre (P' := (deallocSlot A.repAlloc adCap adPtr adAct ∗
        ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st₁ s2 ∗ stackAt sp' (skipFieldStackX 100)) ∗ ((sp' + 96#64) ↦₆₄ pqPtr))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (hnext adAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx22_2)
      fun sf Pf ⟨hstf, evs₂, hfree₂, hent⟩ =>
        ⟨hstf, rustDeallocEvents pqCap.toNat 1 ++ evs₂,
          (freeOnly_rustDeallocEvents pqCap.toNat 1).append hfree₂, ?_⟩
    rw [M.stepEvents_append]
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; sep_ac_rfl

theorem cleanup_64c_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (st : M.σ) {s0 s : State} {sp' ctCap ctPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (ctAct pqAct adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1612#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = ctCap) (hx28 : s.readReg64 .x28 = ctPtr)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases ctAct with
  | false =>
    have hnext := @cleanup_668_wp_placed _ M A lim H hS st s0
    have hdealloc : deallocSlot A.repAlloc ctCap ctPtr false = ⌜ctCap = noneCap ∨ ctCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine WSepWPp.pure_pre (fun hcap => ?_)
    rcases hcap with rfl | rfl
    · refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1640#64) ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
      intro hcl1
      refine wpp_sync_pre (fun s1 => deallocSlot A.repAlloc pqCap pqPtr pqAct ∗
          ((sp' + 96#64) ↦₆₄ pqPtr) ∗ deallocSlot A.repAlloc adCap adPtr adAct ∗
          ((sp' + 88#64) ↦₆₄ adPtr) ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100))
        (by apply entails_of_eq; simp only [arm64_norm]) ?_
      exact hnext pqAct adAct
        (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm])
    · refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1640#64) ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
      intro hcl1
      refine wpp_sync_pre (fun s1 => deallocSlot A.repAlloc pqCap pqPtr pqAct ∗
          ((sp' + 96#64) ↦₆₄ pqPtr) ∗ deallocSlot A.repAlloc adCap adPtr adAct ∗
          ((sp' + 88#64) ↦₆₄ adPtr) ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100))
        (by apply entails_of_eq; simp only [arm64_norm]) ?_
      exact hnext pqAct adAct
        (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm])
  | true =>
    have hdealloc : deallocSlot A.repAlloc ctCap ctPtr true =
        (⌜0 < ctCap.toNat ∧ ctCap.toNat < 2 ^ 63 ∧ ctPtr ≠ 0#64⌝ ∗
          A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]
    refine WSepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_call_noPanic_placed (ctPtr, ctCap.toNat, 1, st) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align [hsp_eq] hsp) hcl1
      (ret_pc := (blkPl_85).base + 1640#64) (by simp [arm64_norm])
      (T := A.pool lim st s ∗ A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat ∗ stackAt sp' extHookStack)
      (φ := RustLayoutOk ctCap.toNat 1 ∧ LsRetAddr624 ((blkPl_85).base + 1640#64))
      (by simp [hsp_eq, rustDeallocExternSpecWithStack,
            LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
            rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rustLayoutOk_align1 hpos hlt,
        lsRetAddr624_blockPlacement_base_add 85 1640#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]; refine WSepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨_, _, _, hx22_cs, _, _, hx25_cs, _⟩
    have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, hx25, arm64_norm]
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    let st₁ := M.stepEvents (rustDeallocEvents ctCap.toNat 1) st
    have hnext := @cleanup_668_wp_placed _ M A lim H hS st₁ s0
    refine WSepWPp.mono_pre (P' := deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st₁ s2 ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    refine wpp_mono_post_noPanic ?_
      (hnext pqAct adAct ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx25_2 hx22_2)
    intro sf Pf ⟨hstf, evs₂, hfree₂, hent⟩
    refine ⟨hstf, rustDeallocEvents ctCap.toNat 1 ++ evs₂,
      (freeOnly_rustDeallocEvents ctCap.toNat 1).append hfree₂, ?_⟩
    rwa [M.stepEvents_append]

theorem cleanup_640_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (st : M.σ) {s0 s : State} {sp' rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (rk : List (BitVec 8)) (ctAct pqAct adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1600#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = rkPtr) (hx1 : s.readReg64 .x1 = rkCap)
    (hx27 : s.readReg64 .x27 = ctCap) (hx28 : s.readReg64 .x28 = ctPtr)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  by_cases hcap : rkCap = 0#64
  · have hnext := @cleanup_64c_wp_placed _ M A lim H hS st s0
    subst hcap; rw [vecU8Buf_zero]; refine WSepWPp.pure_pre (fun _ => ?_)
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1612#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_sync_pre (fun s1 => deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [arm64_norm]) ?_
    exact hnext ctAct pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx27, arm64_norm]) (by simp [hx28, arm64_norm])
      (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm])
  · refine WSepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A.repAlloc rkCap rkPtr rk hcap)) ?_
    simp only [sepConj_assoc]; refine WSepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_call_noPanic_placed (rkPtr, rkCap.toNat, 1, st) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align [hsp_eq] hsp) hcl1
      (ret_pc := (blkPl_85).base + 1612#64) (by simp [arm64_norm])
      (T := A.pool lim st s ∗ A.live rkPtr rkCap.toNat 1 ∗ memRegion rkPtr rkCap.toNat ∗ stackAt sp' extHookStack)
      (φ := RustLayoutOk rkCap.toNat 1 ∧ LsRetAddr624 ((blkPl_85).base + 1612#64))
      (by simp [hx0, hx1, hsp_eq, rustDeallocExternSpecWithStack,
            LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
            rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rustLayoutOk_align1 hpos hlt,
        lsRetAddr624_blockPlacement_base_add 85 1612#64 (by decide) (by decide)⟩
      (by rw [hstack, A.repAlloc_live_norm]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]; refine WSepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨_, _, _, hx22_cs, _, _, hx25_cs, _, hx27_cs, hx28_cs, _⟩
    have hx27_2 : s2.readReg64 .x27 = ctCap := by simp [hx27_cs, hx27, arm64_norm]
    have hx28_2 : s2.readReg64 .x28 = ctPtr := by simp [hx28_cs, hx28, arm64_norm]
    have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, hx25, arm64_norm]
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    let st₁ := M.stepEvents (rustDeallocEvents rkCap.toNat 1) st
    have hnext := @cleanup_64c_wp_placed _ M A lim H hS st₁ s0
    refine WSepWPp.mono_pre (P' := deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st₁ s2 ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    refine wpp_mono_post_noPanic ?_
      (hnext ctAct pqAct adAct ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx27_2 hx28_2 hx25_2 hx22_2)
    intro sf Pf ⟨hstf, evs₂, hfree₂, hent⟩
    refine ⟨hstf, rustDeallocEvents rkCap.toNat 1 ++ evs₂,
      (freeOnly_rustDeallocEvents rkCap.toNat 1).append hfree₂, ?_⟩
    rwa [M.stepEvents_append]

theorem cleanup_430_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hDropErr : DropDecodeErrorOkWPlaced A lim H)
    (st : M.σ) {s0 s : State} {sp' x19 x24 w0 w1 : BitVec 64}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1072#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx24 : s.readReg64 .x24 = x24)
    (hx26 : s.readReg64 .x26 = speWord 2) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcall := hDropErr; clear hDropErr
  have hstack := stackAt_sub_split sp' dropDecodeErrorStackX (skipFieldStackX 100)
  refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ dropDecodeErrorName) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl1
  refine wpp_call_noPanic_placed (x24, st) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align [hsp_eq] hsp) hcl1
    (ret_pc := (blkPl_85).base + 1080#64) (by simp [arm64_norm])
    (T := decodeErrorAt A.repAlloc x24 ∗ A.pool lim st s ∗ stackAt sp' dropDecodeErrorStackX)
    (φ := LsRetAddr624 ((blkPl_85).base + 1080#64))
    (by simp [hsp_eq, dropDecodeErrorSpecX, dropDecodeErrorSpecGen, dropDecodeErrorStackX, arm64_norm])
    (lsRetAddr624_blockPlacement_base_add 85 1080#64 (by decide) (by decide))
    (by rw [hstack]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropDecodeErrorSpecX, dropDecodeErrorSpecGen]
  simp only [sepConj_assoc]; refine WSepWPp.pure_pre (fun htr2 => ?_)
  simp only [sepExists_sepConj_left]; refine WSepWPp.exists_pre (fun evs => ?_)
  simp only [sepConj_assoc]; refine WSepWPp.pure_pre (fun hevs => ?_)
  rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, _, hx26_cs, _⟩
  have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x19 := by simp [hx19_cs, hx19, arm64_norm]
  have hx26_2 : s2.readReg64 (Reg.gpr 26#5) = speWord 2 := by simp [hx26_cs, hx26, arm64_norm]
  refine wpp_of_sepWP_end_noPanic_placed hcl2 ?_
  wp_steps_sync_85 ((blkPl_85).base + 1088#64)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl3
  refine ⟨PostEpilogueStatePlaced.of_steps hcl3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
      (by simp [htr2, htr, arm64_norm]),
    evs, freeOnly_dropDecodeErrorEnv hevs, ?_⟩
  apply entails_of_eq; simp only [hstack, hsp_eq, dropDecodeErrorStackX, errTag, arm64_norm]; sep_ac_rfl

theorem cleanup_408_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropErr : DropDecodeErrorOkWPlaced A lim H)
    (st : M.σ) {s0 s : State} {sp' x19 x24 w0 w1 adCap adPtr : BitVec 64} (adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1032#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx24 : s.readReg64 .x24 = x24)
    (hx26 : s.readReg64 .x26 = speWord 2) (hx22 : s.readReg64 .x22 = adCap) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 88#64) ↦₆₄ adPtr) ∗ (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases adAct with
  | false =>
    have hnext := @cleanup_430_wp_placed _ M A lim H hDropErr st s0
    clear hDropErr
    have hdealloc : deallocSlot A.repAlloc adCap adPtr false = ⌜adCap = noneCap ∨ adCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine WSepWPp.pure_pre (fun hcap => ?_)
    have hslt := slt_one_of_false_cap hcap
    clear hcap
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1072#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_sync_pre (fun s1 => (decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗ ((sp' + 88#64) ↦₆₄ adPtr))
      (by apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (hnext (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm]) (by simp [hx26, arm64_norm]))
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_; apply entails_of_eq; sep_ac_rfl
  | true =>
    have hdealloc : deallocSlot A.repAlloc adCap adPtr true =
        (⌜0 < adCap.toNat ∧ adCap.toNat < 2 ^ 63 ∧ adPtr ≠ 0#64⌝ ∗
          A.live adPtr adCap.toNat 1 ∗ memRegion adPtr adCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]
    refine WSepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hslt := cap_slt_one_of_pos hpos hlt
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_call_noPanic_placed (adPtr, adCap.toNat, 1, st) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align [hsp_eq] hsp) hcl1
      (ret_pc := (blkPl_85).base + 1056#64) (by simp [arm64_norm])
      (T := A.pool lim st s ∗ A.live adPtr adCap.toNat 1 ∗ memRegion adPtr adCap.toNat ∗ stackAt sp' extHookStack)
      (φ := RustLayoutOk adCap.toNat 1 ∧ LsRetAddr624 ((blkPl_85).base + 1056#64))
      (by simp [hsp_eq, rustDeallocExternSpecWithStack,
            LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
            rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rustLayoutOk_align1 hpos hlt,
        lsRetAddr624_blockPlacement_base_add 85 1056#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]; refine WSepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, hx24_cs, _, hx26_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = speWord 2 := by simp [hx26_cs, hx26, arm64_norm]
    let st₁ := M.stepEvents (rustDeallocEvents adCap.toNat 1) st
    have hnext := @cleanup_430_wp_placed _ M A lim H hDropErr st₁ s0; clear hDropErr
    refine WSepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).base + 1072#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl3
    refine wpp_sync_pre (fun s3 => (decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st₁ s3 ∗ stackAt sp' (skipFieldStackX 100)) ∗ ((sp' + 88#64) ↦₆₄ adPtr))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (hnext (PostEpilogueStatePlaced.of_steps hcl3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
          (by simp [htr2, htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        (by simp [hx19_2, arm64_norm]) (by simp [hx24_2, arm64_norm]) (by simp [hx26_2, arm64_norm]))
      fun sf Pf ⟨hstf, evs₂, hfree₂, hent⟩ =>
        ⟨hstf, rustDeallocEvents adCap.toNat 1 ++ evs₂,
          (freeOnly_rustDeallocEvents adCap.toNat 1).append hfree₂, ?_⟩
    rw [M.stepEvents_append]; refine Entails.trans (sepConj_mono_left hent) ?_; apply entails_of_eq; sep_ac_rfl

theorem cleanup_3f0_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropErr : DropDecodeErrorOkWPlaced A lim H)
    (st : M.σ) {s0 s : State} {sp' x19 x24 w0 w1 pqCap pqPtr adCap adPtr : BitVec 64}
    (pqAct adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1008#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx24 : s.readReg64 .x24 = x24)
    (hx26 : s.readReg64 .x26 = speWord 2)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
            (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases pqAct with
  | false =>
    have hnext := @cleanup_408_wp_placed _ M A lim H hS hDropErr st s0
    clear hDropErr
    have hdealloc : deallocSlot A.repAlloc pqCap pqPtr false = ⌜pqCap = noneCap ∨ pqCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine WSepWPp.pure_pre (fun hcap => ?_)
    have hslt := slt_one_of_false_cap hcap
    clear hcap
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1032#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_sync_pre (fun s1 => (deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗ ((sp' + 96#64) ↦₆₄ pqPtr))
      (by apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (hnext adAct (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
        (by simp [hx26, arm64_norm]) (by simp [hx22, arm64_norm]))
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_; apply entails_of_eq; sep_ac_rfl
  | true =>
    have hdealloc : deallocSlot A.repAlloc pqCap pqPtr true =
        (⌜0 < pqCap.toNat ∧ pqCap.toNat < 2 ^ 63 ∧ pqPtr ≠ 0#64⌝ ∗
          A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]
    refine WSepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hslt := cap_slt_one_of_pos hpos hlt
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_call_noPanic_placed (pqPtr, pqCap.toNat, 1, st) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align [hsp_eq] hsp) hcl1
      (ret_pc := (blkPl_85).base + 1032#64) (by simp [arm64_norm])
      (T := A.pool lim st s ∗ A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat ∗ stackAt sp' extHookStack)
      (φ := RustLayoutOk pqCap.toNat 1 ∧ LsRetAddr624 ((blkPl_85).base + 1032#64))
      (by simp [hsp_eq, rustDeallocExternSpecWithStack,
            LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
            rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rustLayoutOk_align1 hpos hlt,
        lsRetAddr624_blockPlacement_base_add 85 1032#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]; refine WSepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨hx19_cs, _, _, hx22_cs, _, hx24_cs, _, hx26_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = speWord 2 := by simp [hx26_cs, hx26, arm64_norm]
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    let st₁ := M.stepEvents (rustDeallocEvents pqCap.toNat 1) st
    have hnext := @cleanup_408_wp_placed _ M A lim H hS hDropErr st₁ s0; clear hDropErr
    refine WSepWPp.mono_pre (P' := (deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st₁ s2 ∗ stackAt sp' (skipFieldStackX 100)) ∗ ((sp' + 96#64) ↦₆₄ pqPtr))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (hnext adAct ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx19_2 hx24_2 hx26_2 hx22_2)
      fun sf Pf ⟨hstf, evs₂, hfree₂, hent⟩ =>
        ⟨hstf, rustDeallocEvents pqCap.toNat 1 ++ evs₂,
          (freeOnly_rustDeallocEvents pqCap.toNat 1).append hfree₂, ?_⟩
    rw [M.stepEvents_append]; refine Entails.trans (sepConj_mono_left hent) ?_; apply entails_of_eq; sep_ac_rfl

theorem cleanup_3d8_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropErr : DropDecodeErrorOkWPlaced A lim H)
    (st : M.σ) {s0 s : State} {sp' x19 x24 w0 w1 ctCap ctPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (ctAct pqAct adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 984#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx24 : s.readReg64 .x24 = x24)
    (hx26 : s.readReg64 .x26 = speWord 2)
    (hx27 : s.readReg64 .x27 = ctCap) (hx28 : s.readReg64 .x28 = ctPtr)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
            (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases ctAct with
  | false =>
    have hnext := @cleanup_3f0_wp_placed _ M A lim H hS hDropErr st s0
    clear hDropErr
    have hdealloc : deallocSlot A.repAlloc ctCap ctPtr false = ⌜ctCap = noneCap ∨ ctCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine WSepWPp.pure_pre (fun hcap => ?_)
    have hslt := slt_one_of_false_cap hcap
    clear hcap
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1008#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_sync_pre (fun s1 => deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [arm64_norm]) ?_
    exact hnext pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm])
  | true =>
    have hdealloc : deallocSlot A.repAlloc ctCap ctPtr true =
        (⌜0 < ctCap.toNat ∧ ctCap.toNat < 2 ^ 63 ∧ ctPtr ≠ 0#64⌝ ∗
          A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]
    refine WSepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hslt := cap_slt_one_of_pos hpos hlt
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_call_noPanic_placed (ctPtr, ctCap.toNat, 1, st) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align [hsp_eq] hsp) hcl1
      (ret_pc := (blkPl_85).base + 1008#64) (by simp [arm64_norm])
      (T := A.pool lim st s ∗ A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat ∗ stackAt sp' extHookStack)
      (φ := RustLayoutOk ctCap.toNat 1 ∧ LsRetAddr624 ((blkPl_85).base + 1008#64))
      (by simp [hsp_eq, rustDeallocExternSpecWithStack,
            LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
            rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rustLayoutOk_align1 hpos hlt,
        lsRetAddr624_blockPlacement_base_add 85 1008#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]; refine WSepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨hx19_cs, _, _, hx22_cs, _, hx24_cs, hx25_cs, hx26_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = speWord 2 := by simp [hx26_cs, hx26, arm64_norm]
    have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, hx25, arm64_norm]
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    let st₁ := M.stepEvents (rustDeallocEvents ctCap.toNat 1) st
    have hnext := @cleanup_3f0_wp_placed _ M A lim H hS hDropErr st₁ s0; clear hDropErr
    refine WSepWPp.mono_pre (P' := deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st₁ s2 ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    refine wpp_mono_post_noPanic ?_
      (hnext pqAct adAct ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx19_2 hx24_2 hx26_2 hx25_2 hx22_2)
    intro sf Pf ⟨hstf, evs₂, hfree₂, hent⟩
    refine ⟨hstf, rustDeallocEvents ctCap.toNat 1 ++ evs₂,
      (freeOnly_rustDeallocEvents ctCap.toNat 1).append hfree₂, ?_⟩
    rwa [M.stepEvents_append]

theorem cleanup_3c8_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropErr : DropDecodeErrorOkWPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 x24 w0 w1 rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (rkAct ctAct pqAct adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 968#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx24 : s.readReg64 .x24 = x24)
    (hx26 : s.readReg64 .x26 = speWord 2)
    (hx0 : s.readReg64 .x0 = rkPtr) (hx1 : s.readReg64 .x1 = rkCap)
    (hx27 : s.readReg64 .x27 = ctCap) (hx28 : s.readReg64 .x28 = ctPtr)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (deallocSlot A.repAlloc rkCap rkPtr rkAct ∗
        deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
            (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases rkAct with
  | false =>
    have hnext := @cleanup_3d8_wp_placed _ M A lim H hS hDropErr st s0
    clear hDropErr
    have hdealloc : deallocSlot A.repAlloc rkCap rkPtr false = ⌜rkCap = noneCap ∨ rkCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine WSepWPp.pure_pre (fun hcap => ?_)
    have hslt := slt_one_of_false_cap hcap
    clear hcap
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 984#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_sync_pre (fun s1 => deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [arm64_norm]) ?_
    exact hnext ctAct pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx27, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm])
  | true =>
    have hdealloc : deallocSlot A.repAlloc rkCap rkPtr true =
        (⌜0 < rkCap.toNat ∧ rkCap.toNat < 2 ^ 63 ∧ rkPtr ≠ 0#64⌝ ∗
          A.live rkPtr rkCap.toNat 1 ∗ memRegion rkPtr rkCap.toNat) := rfl
    rw [hdealloc]; simp only [sepConj_assoc]
    refine WSepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hslt := cap_slt_one_of_pos hpos hlt
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_call_noPanic_placed (rkPtr, rkCap.toNat, 1, st) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align [hsp_eq] hsp) hcl1
      (ret_pc := (blkPl_85).base + 984#64) (by simp [arm64_norm])
      (T := A.pool lim st s ∗ A.live rkPtr rkCap.toNat 1 ∗ memRegion rkPtr rkCap.toNat ∗ stackAt sp' extHookStack)
      (φ := RustLayoutOk rkCap.toNat 1 ∧ LsRetAddr624 ((blkPl_85).base + 984#64))
      (by simp [hx0, hx1, hsp_eq, rustDeallocExternSpecWithStack,
            LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
            rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rustLayoutOk_align1 hpos hlt,
        lsRetAddr624_blockPlacement_base_add 85 984#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]; refine WSepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨hx19_cs, _, _, hx22_cs, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = speWord 2 := by simp [hx26_cs, hx26, arm64_norm]
    have hx27_2 : s2.readReg64 .x27 = ctCap := by simp [hx27_cs, hx27, arm64_norm]
    have hx28_2 : s2.readReg64 .x28 = ctPtr := by simp [hx28_cs, hx28, arm64_norm]
    have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, hx25, arm64_norm]
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    let st₁ := M.stepEvents (rustDeallocEvents rkCap.toNat 1) st
    have hnext := @cleanup_3d8_wp_placed _ M A lim H hS hDropErr st₁ s0; clear hDropErr
    refine WSepWPp.mono_pre (P' := deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool lim st₁ s2 ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    refine wpp_mono_post_noPanic ?_
      (hnext ctAct pqAct adAct ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx19_2 hx24_2 hx26_2 hx27_2 hx28_2 hx25_2 hx22_2)
    intro sf Pf ⟨hstf, evs₂, hfree₂, hent⟩
    refine ⟨hstf, rustDeallocEvents rkCap.toNat 1 ++ evs₂,
      (freeOnly_rustDeallocEvents rkCap.toNat 1).append hfree₂, ?_⟩
    rwa [M.stepEvents_append]

theorem post_none_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropErr : DropDecodeErrorOkWPlaced A lim H)
    (st : M.σ) {s0 s : State} {sp' x19 x20 x21 x23 x24 : BitVec 64}
    {out : Except SignalProtocolError SignalMessage}
    (herr : out = .error .invalidProtobufEncoding)
    (hst : LoopExitStatePlaced s0 sp' x19 x20 x21 x23 s)
    (hpc : s.pc = (blkPl_85).base + 944#64) (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = x24) (hx24_ne : x24 ≠ 0#64)
    (mErr : ProtoSignalMessage) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (wireSignalMessageOf A.repAlloc (sp' + 176#64) mErr ∗
        decodeErrorAt A.repAlloc x24 ∗
        memRegion (sp' + 88#64) 16 ∗ memRegion x19 120 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ memRegion (sp' + 88#64) 16 ∗ memRegion (sp' + 176#64) 112 ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hregs, hsp, hcl, htr⟩
  have hsp_eq : s.sp = sp' := hregs.sp
  have hx19 : s.readReg64 .x19 = x19 := hregs.x19_eq
  have hx26 : s.readReg64 .x26 = speWord 2 := hregs.x26
  have hnext := @cleanup_3c8_wp_placed _ M A lim H hS hDropErr st s0
  clear hDropErr
  unfold wireSignalMessageOf
  simp only [sepExists_sepConj_left]
  refine WSepWPp.exists_pre fun g => ?_
  unfold wireSignalMessageAt
  have hent_wire :
      optVecU8At A.repAlloc g.rk (sp' + 176#64) mErr.ratchetKey ∗
      optVecU8At A.repAlloc g.ct (sp' + 176#64 + 24#64) mErr.ciphertext ∗
      optVecU8At A.repAlloc g.pq (sp' + 176#64 + 48#64) mErr.pqRatchet ∗
      optVecU8At A.repAlloc g.addr (sp' + 176#64 + 72#64) mErr.addresses ∗
      optU32At (sp' + 176#64 + 96#64) mErr.counter ∗
      optU32At (sp' + 176#64 + 104#64) mErr.previousCounter ⊢
      (∃∗ rkCap, ∃∗ rkPtr, ∃∗ rkLen, ∃∗ rkAct,
        vecHeader (sp' + 176#64) rkCap rkPtr rkLen ∗ deallocSlot A.repAlloc rkCap rkPtr rkAct) ∗
      (∃∗ ctCap, ∃∗ ctPtr, ∃∗ ctLen, ∃∗ ctAct,
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗ deallocSlot A.repAlloc ctCap ctPtr ctAct) ∗
      (∃∗ pqCap, ∃∗ pqPtr, ∃∗ pqLen, ∃∗ pqAct,
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗ deallocSlot A.repAlloc pqCap pqPtr pqAct) ∗
      (∃∗ adCap, ∃∗ adPtr, ∃∗ adLen, ∃∗ adAct,
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗ deallocSlot A.repAlloc adCap adPtr adAct) ∗
      memRegion (sp' + 272#64) 8 ∗ memRegion (sp' + 280#64) 8 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (optVecU8At_entails_header_dealloc A.repAlloc g.rk (sp' + 176#64) mErr.ratchetKey)
      (sepConj_mono (optVecU8At_entails_header_dealloc A.repAlloc g.ct (sp' + 200#64) mErr.ciphertext)
        (sepConj_mono (optVecU8At_entails_header_dealloc A.repAlloc g.pq (sp' + 224#64) mErr.pqRatchet)
          (sepConj_mono (optVecU8At_entails_header_dealloc A.repAlloc g.addr (sp' + 248#64) mErr.addresses)
            (sepConj_mono (optU32At_entails_memRegion8 (sp' + 272#64) mErr.counter)
              (optU32At_entails_memRegion8 (sp' + 280#64) mErr.previousCounter)))))
  refine WSepWPp.mono_pre (sepConj_mono hent_wire
    (sepConj_mono_right (sepConj_mono (memRegion16_split8_8 (sp' + 88#64))
      (sepConj_mono_left (memRegion120_split16 x19))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine WSepWPp.exists_pre fun w1 => WSepWPp.exists_pre fun w0 =>
    WSepWPp.exists_pre fun s96 => WSepWPp.exists_pre fun s88 =>
    WSepWPp.exists_pre fun adCap => WSepWPp.exists_pre fun adPtr =>
    WSepWPp.exists_pre fun adLen => WSepWPp.exists_pre fun adAct =>
    WSepWPp.exists_pre fun pqCap => WSepWPp.exists_pre fun pqPtr =>
    WSepWPp.exists_pre fun pqLen => WSepWPp.exists_pre fun pqAct =>
    WSepWPp.exists_pre fun ctCap => WSepWPp.exists_pre fun ctPtr =>
    WSepWPp.exists_pre fun ctLen => WSepWPp.exists_pre fun ctAct =>
    WSepWPp.exists_pre fun rkCap => WSepWPp.exists_pre fun rkPtr =>
    WSepWPp.exists_pre fun rkLen => WSepWPp.exists_pre fun rkAct => ?_
  have hvh :
      vecHeader (sp' + 176#64) rkCap rkPtr rkLen =
        ((sp' + 176#64) ↦₆₄ rkCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen) ∧
      vecHeader (sp' + 200#64) ctCap ctPtr ctLen =
        ((sp' + 200#64) ↦₆₄ ctCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∧
      vecHeader (sp' + 224#64) pqCap pqPtr pqLen =
        ((sp' + 224#64) ↦₆₄ pqCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen) ∧
      vecHeader (sp' + 248#64) adCap adPtr adLen =
        ((sp' + 248#64) ↦₆₄ adCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen) := by
    simp only [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, and_self]
  rcases hvh with ⟨hvh1, hvh2, hvh3, hvh4⟩
  rw [hvh1, hvh2, hvh3, hvh4]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 968#64) ?_
  wp_steps_sync_85 ((blkPl_85).base + 968#64)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl1
  set F_hdr := vecHeader (sp' + 176#64) rkCap rkPtr rkLen ∗
    vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
    vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
    vecHeader (sp' + 248#64) adCap adPtr adLen ∗
    memRegion (sp' + 272#64) 8 ∗ memRegion (sp' + 280#64) 8 ∗
    memRegion (x19 + 16#64) 104
  refine WSepWPp.mono_pre (P' := (deallocSlot A.repAlloc rkCap rkPtr rkAct ∗
      deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
      deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
      deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
      decodeErrorAt A.repAlloc x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
      A.pool lim st _ ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_hdr)
    (by dsimp only [F_hdr]; apply entails_of_eq; simp only [hvh1, hvh2, hvh3, hvh4, arm64_norm]; sep_ac_rfl) ?_
  refine wpp_frame_noPanic
    (hnext rkAct ctAct pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
    fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have h16 := pointsTo64_pair_entails_memRegion16 (sp' + 88#64) adPtr pqPtr
  have ha96 : sp' + 88#64 + 8#64 = sp' + 96#64 := by bv_omega
  rw [ha96] at h16
  have h112 := wireHeaders_entails_memRegion112 sp' rkCap rkPtr rkLen ctCap ctPtr ctLen
    pqCap pqPtr pqLen adCap adPtr adLen
  have hmsg := spe_invalidProto_intro A.repAlloc x19 herr
  dsimp only [F_hdr]
  refine Entails.trans (Q := (((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr)) ∗
      (vecHeader (sp' + 176#64) rkCap rkPtr rkLen ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        memRegion (sp' + 272#64) 8 ∗ memRegion (sp' + 280#64) 8) ∗
      ((x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗ memRegion (x19 + 16#64) 104) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  exact sepConj_mono h16 (sepConj_mono h112 (sepConj_mono_left hmsg))

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanupBudget
