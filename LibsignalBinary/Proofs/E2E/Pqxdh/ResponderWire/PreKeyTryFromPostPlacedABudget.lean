/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedA
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (Block `111`): Post-Loop Part A

Proves panic-free `RustCliAllocBudget M` specifications for the shared cleanup tails
(`+2060 .. +2648` → `+1284`) and post-loop Segment 1 (`+1120 .. +1476` → `+1668`) of Block `111`
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp
open scoped CryptoVerification CryptoVerification.LibsignalTripleRatchet.Wire
  CryptoVerification.E2E.Pqxdh.ResponderWire
open CryptoGames.LibsignalSession (PublicKey SignalProtocolError)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg libsignalSessionLib libsignalMutatedBlocks
  lsmpl lsRustDeallocSym blkPC_111 blkPl_111 blkLib_eq_111
  LibsignalCodeLoaded withLsCodeLoaded ls_hook_ok_of_mem ls_subroutine_ok_of_block
  subroutine_ok_withLsCodeLoaded_of_plain
)
open CryptoVerification.RustHeap (allocHookStack vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  smallRootStack lsLogOff
)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt speWord)
open CryptoVerification.LibsignalTripleRatchet.Getters (DropSpeGhost dropSpeStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (
  words5At words5At_entails_memRegion
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue (
  append64_extract_lo append64_extract_hi append32_extract_lo append32_extract_hi
  append32_truncate zeroExtend32_truncate8_eq extractLsb0_8_append56
)
open CryptoVerification.LibsignalTripleRatchet.Wire (
  SepWPp SepWPp.pure_pre SepWPp.mono_pre VRegsAt
  vecU8Buf vecU8Buf_zero vecU8Buf_dealloc vecU8At_eq_header_buf
  stackAt_sub_split entails_of_eq cap_add1_eq_of_lt cap_add2_ne_of_lt
  layoutOk_align1
  bv_reconstruct_low8 bv_reconstruct_low8_dec bv_zext8_mask truncate16_zext32
  zeroExtend32_lsr4_truncate8
)
open CryptoVerification.E2E.Pqxdh.ResponderWire (
  PreKeyTryFromArgs PreKeyLoopRegs opkTag preKeyPlacedProg
  KeepsFrozenInv withPreKeyInv extract_withPreKeyInv subroutine_ok_withPreKeyInv_of_plain
  ls_subroutine_ok_pk_of_plain SepWPp.of_sepWP_pk
  PreKeyPostState PreKeyPostState.of_steps
  vecU8Rest vecU8Buf_to_slice_rest slice_rest_to_vecU8Buf
  deserialize_djb_ok post_vecU8At4_lt seg1SpillsAt memRegion96_seg1_unpack
  post_headers_entails_memRegion80 post_memRegion48_split8 post_memRegion48_split33_15
  bv_sub_add_lit' bv_sub_sub_lit
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk VmPreserved
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (
  LsRetAddr624 lsRetAddr624_blockPlacement_base_add
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget (
  deserializeOk33PlacedSpec deserialize_placed_ok
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
  bv_reconstruct_low8 bv_reconstruct_low8_dec bv_zext8_mask truncate16_zext32
  append64_extract_lo append64_extract_hi append32_extract_lo append32_extract_hi
  append32_truncate zeroExtend32_truncate8_eq extractLsb0_8_append56
  zeroExtend32_lsr4_truncate8

/-! ## Panic-Free `SepWPp` Combinators and Callee Predicates -/

abbrev preKeyNoPanicQp : Arm64.State → SepProp → Prop := fun _ _ => False

theorem blk111_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (libsignalSessionLib.blockLib 111).text = true := by
  rfl

macro "wp_steps_sync_111 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_111).rebase (blkPl_111).base (hooksException _))
    blkLib_eq_111 blk111_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
  try conv => arg 3; simp only [State.setMem_setMem]
  try conv => arg 4; pattern (RustCliAllocBudget.pool _ _ _ _); simp only [State.setMem_setMem]
))

theorem freeOnly_rustDeallocEvents (size align : Nat) :
    FreeOnlyEvs (rustDeallocEvents size align) :=
  FreeOnlyEvs.singleton align size

theorem SepWPp.of_sepWP_end_noPanic_pk {prog : Program} {ret : BitVec 64}
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {s : Arm64.State} {P : SepProp} {Q : Arm64.State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h : ProofLib.SepWP prog ret s P (fun sf Pf =>
      VRegsAt s sf ∧ (Inv sf.mem → Q sf Pf))) :
    SepWPp prog ret s P Q preKeyNoPanicQp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hv, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      hq (hkf hinv hsteps.keepsFrozen), hv.eq⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem SepWPp.let_state {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : SepProp} {Q Qp : Arm64.State → SepProp → Prop}
    (k : let sc := s; SepWPp prog ret sc P Q Qp) :
    SepWPp prog ret s P Q Qp := k

theorem SepWPp.frame_noPanic_pk {prog : Program} {ret : BitVec 64}
    {s : Arm64.State} {P F : SepProp} {Q Q' : Arm64.State → SepProp → Prop}
    (h : SepWPp prog ret s P Q preKeyNoPanicQp)
    (hq : ∀ sf Pf, Q sf Pf → Q' sf (Pf ∗ F)) :
    SepWPp prog ret s (P ∗ F) Q' preKeyNoPanicQp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  rcases h (F ∗ R) hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hqf, hv⟩ | ⟨_, _, _, hp⟩ | ⟨hoom1, hoom2⟩⟩
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf ∗ F, hmf, hq sf Pf hqf, hv⟩⟩
  · exact False.elim hp
  · exact (not_satisfies_false_sepConj hoom2).elim

theorem SepWPp.call_noPanic_budget_pk {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {s : Arm64.State} {P T F : SepProp} {φ : Prop}
    {Q : Arm64.State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withPreKeyInv Inv spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hinv : Inv s.mem) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → Inv sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q preKeyNoPanicQp)
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q preKeyNoPanicQp := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withPreKeyInv Inv spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withPreKeyInv]
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [withPreKeyInv] at hpost
    have hinv_m := hkf hinv hsteps.keepsFrozen
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [Arm64.State.spAligned, hspm, ← Arm64.State.spAligned]; exact hsp
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hinv_m hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withPreKeyInv] at hpost
    rw [hpan sm] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [withPreKeyInv] at hpost
    rw [hexit sm code] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [withPreKeyInv] at hpost
    rw [hoom sm] at hpost
    exact (allowPanic_not_exited hpost).elim

def PreKeyDeallocOk [LibsignalPlacement] (Inv : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
    (withPreKeyInv Inv (rustCliDeallocBudgetSpec M A lim))

theorem preKeyDeallocOk_of_hookSat [LibsignalPlacement] {Inv : Memory → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hsat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    PreKeyDeallocOk Inv A lim H :=
  subroutine_ok_withPreKeyInv_of_plain (ls_hook_ok_of_mem hsat)

def PreKeyDropSpeOk [LibsignalPlacement] (Inv : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (preKeyPlacedProg H) (lsmpl.base 5)
    (withPreKeyInv Inv (dropSpeSpec M A lim))

/-! ## Shared Cleanup Tails (`+2060 .. +2648` → `+1284`) -/

theorem cleanup_33c_placed_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A lim H)
    {s0 s : State} {sp' ptr cap : BitVec 64} (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2060#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap)
    (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ A.pool lim st s ∗
        stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have _ : RustLayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 := ⟨⟨layoutOk_align1 hpos hlt, by decide⟩, hptr⟩
  have hstack := stackAt_sub_split sp' allocHookStack smallRootStack (by decide) (by decide)
  refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  wp_steps_sync_111 ((blkPl_111).ρ lsRustDeallocSym)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv1 => ?_⟩
  refine SepWPp.let_state ?_; intro s_call
  refine SepWPp.call_noPanic_budget_pk hkf (ptr, cap.toNat, 1, st) hdealloc
    (by simp_all [s_call, arm64_norm]) (by simp_all [s_call, arm64_norm])
    (by dsimp only [s_call]; tryFromPost_sp_align hsp) hinv1
    (ret_pc := (blkPl_111).base + 2068#64) (by simp_all [s_call, arm64_norm])
    (T := A.pool lim st s_call ∗
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
      stackAt sp' allocHookStack)
    (φ := ptr = ptr ∧ cap.toNat = cap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
      LsRetAddr624 ((blkPl_111).base + 2068#64))
    (by simp_all [s_call, rustCliDeallocBudgetSpec, arm64_norm])
    ⟨rfl, rfl, rfl, lsRetAddr624_blockPlacement_base_add 111 2068#64 (by decide) (by decide)⟩
    (by rw [hstack]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 _
  dsimp only [rustCliDeallocBudgetSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun ⟨hpres2, _⟩ => ?_
  have htr2 : s2.trace = s0.trace := by simp [hpres2.2, s_call, htr, arm64_norm]
  refine SepWPp.of_sepWP_end_noPanic_pk hkf hinv2 ?_
  wp_steps_sync_111 ((blkPl_111).base + 1284#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv3 => ?_⟩
  refine ⟨rustDeallocEvents cap.toNat 1, freeOnly_rustDeallocEvents cap.toNat 1,
    PreKeyPostState.of_steps hinv3
      (by dsimp only [s_call] at hsp2; tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
      (by simp [htr2, arm64_norm]), ?_⟩
  apply entails_of_eq
  simp only [s_call, hstack, hsp_eq, arm64_norm]
  sep_ac_rfl

theorem cleanup_57c_placed_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A lim H)
    {s0 s : State} {sp' bkCap bkPtr : BitVec 64} (bk : List (BitVec 8))
    (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2636#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        vecU8Buf A.repAlloc bkCap bkPtr bk ∗ A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  by_cases hcap : bkCap = 0#64
  · subst hcap
    rw [vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_end_noPanic_pk hkf hinv ?_
    wp_steps_sync_111 ((blkPl_111).base + 1284#64)
    refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨inferInstance, fun hinv1 => ?_⟩
    exact ⟨[], FreeOnlyEvs.nil,
      PreKeyPostState.of_steps hinv1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]),
      by simp only [M.stepEvents_nil]; apply entails_of_eq; sep_ac_rfl⟩
  · refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (vecU8Buf_dealloc A.repAlloc bkCap bkPtr bk hcap)))) ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2060#64) ?_
    wp_steps_sync_111 ((blkPl_111).base + 2060#64)
    refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨inferInstance, fun hinv1 => ?_⟩
    rw [RustCliAllocBudget.repAlloc_live_norm]
    refine SepWPp.mono_pre
      (P' := (A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗ A.pool lim st _ ∗
        stackAt sp' smallRootStack) ∗ (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap)))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    refine SepWPp.frame_noPanic_pk
      (cleanup_33c_placed_wp hkf hdealloc
        (PreKeyPostState.of_steps hinv1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp [arm64_norm]) (by simp_all [arm64_norm]) hpos hlt hptr)
      fun sf Pf ⟨evs, hevs, hstf, hent⟩ => ⟨evs, hevs, hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; sep_ac_rfl

theorem cleanup_568_placed_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A lim H)
    {s0 s : State} {sp' ikCap ikPtr bkCap bkPtr : BitVec 64} (ik bk : List (BitVec 8))
    (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2616#64)
    (hrun : s.status = .Running) (hx23 : s.readReg64 .x23 = ikCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        vecU8Buf A.repAlloc ikCap ikPtr ik ∗ vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hstack := stackAt_sub_split sp' allocHookStack smallRootStack (by decide) (by decide)
  by_cases hcap : ikCap = 0#64
  · subst hcap
    rw [vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2636#64) ?_
    wp_steps_sync_111 ((blkPl_111).base + 2636#64)
    refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨inferInstance, fun hinv1 => ?_⟩
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          vecU8Buf A.repAlloc bkCap bkPtr bk ∗ A.pool lim st _ ∗ stackAt sp' smallRootStack) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    refine SepWPp.frame_noPanic_pk
      (cleanup_57c_placed_wp hkf hdealloc bk
        (PreKeyPostState.of_steps hinv1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]))
      fun sf Pf ⟨evs, hevs, hstf, hent⟩ => ⟨evs, hevs, hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; sep_ac_rfl
  · refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (vecU8Buf_dealloc A.repAlloc ikCap ikPtr ik hcap))))) ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    wp_steps_sync_111 ((blkPl_111).ρ lsRustDeallocSym)
    refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨inferInstance, fun hinv1 => ?_⟩
    rw [RustCliAllocBudget.repAlloc_live_norm]
    refine SepWPp.let_state ?_; intro s_call
    refine SepWPp.call_noPanic_budget_pk hkf (ikPtr, ikCap.toNat, 1, st) hdealloc
      (by simp_all [s_call, arm64_norm]) (by simp_all [s_call, arm64_norm])
      (by dsimp only [s_call]; tryFromPost_sp_align hsp) hinv1
      (ret_pc := (blkPl_111).base + 2636#64) (by simp_all [s_call, arm64_norm])
      (T := A.pool lim st s_call ∗ A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat ∗
        stackAt sp' allocHookStack)
      (φ := ikPtr = ikPtr ∧ ikCap.toNat = ikCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        LsRetAddr624 ((blkPl_111).base + 2636#64))
      (by simp_all [s_call, rustCliDeallocBudgetSpec, arm64_norm])
      ⟨rfl, rfl, rfl, lsRetAddr624_blockPlacement_base_add 111 2636#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus)
      ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 _
    dsimp only [rustCliDeallocBudgetSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpres2, _⟩ => ?_
    have htr2 : s2.trace = s0.trace := by simp [hpres2.2, s_call, htr, arm64_norm]
    set st1 := M.stepEvents (rustDeallocEvents ikCap.toNat 1) st
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          vecU8Buf A.repAlloc bkCap bkPtr bk ∗ A.pool lim st1 s2 ∗ stackAt sp' smallRootStack) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by
        apply entails_of_eq
        simp only [s_call, hstack, hsp_eq, arm64_norm]
        sep_ac_rfl) ?_
    refine SepWPp.frame_noPanic_pk
      (cleanup_57c_placed_wp hkf hdealloc bk
        (PreKeyPostState.of_steps hinv2 (by dsimp only [s_call] at hsp2; tryFromPost_sp [hsp2, hsp_eq])
          hsp_eq hsp htr2) hpc2 hrun2)
      fun sf Pf ⟨evs2, hevs2, hstf, hent⟩ =>
        ⟨rustDeallocEvents ikCap.toNat 1 ++ evs2,
          (freeOnly_rustDeallocEvents ikCap.toNat 1).append hevs2, hstf, ?_⟩
    rw [M.stepEvents_append]
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; sep_ac_rfl

theorem cleanup_558_placed_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A lim H)
    {s0 s : State} {sp' msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (msg ik bk : List (BitVec 8)) (hcap : msgCap ≠ 0#64) (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2600#64)
    (hrun : s.status = .Running) (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ vecU8Buf A.repAlloc msgCap msgPtr msg ∗
        vecU8Buf A.repAlloc ikCap ikPtr ik ∗ vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hstack := stackAt_sub_split sp' allocHookStack smallRootStack (by decide) (by decide)
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left
        (vecU8Buf_dealloc A.repAlloc msgCap msgPtr msg hcap)))))) ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun _ => ?_
  refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  wp_steps_sync_111 ((blkPl_111).ρ lsRustDeallocSym)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv1 => ?_⟩
  rw [RustCliAllocBudget.repAlloc_live_norm]
  refine SepWPp.let_state ?_; intro s_call
  refine SepWPp.call_noPanic_budget_pk hkf (msgPtr, msgCap.toNat, 1, st) hdealloc
    (by simp_all [s_call, arm64_norm]) (by simp_all [s_call, arm64_norm])
    (by dsimp only [s_call]; tryFromPost_sp_align hsp) hinv1
    (ret_pc := (blkPl_111).base + 2616#64) (by simp_all [s_call, arm64_norm])
    (T := A.pool lim st s_call ∗ A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
      stackAt sp' allocHookStack)
    (φ := msgPtr = msgPtr ∧ msgCap.toNat = msgCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
      LsRetAddr624 ((blkPl_111).base + 2616#64))
    (by simp_all [s_call, rustCliDeallocBudgetSpec, arm64_norm])
    ⟨rfl, rfl, rfl, lsRetAddr624_blockPlacement_base_add 111 2616#64 (by decide) (by decide)⟩
    (by rw [hstack]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [rustCliDeallocBudgetSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun ⟨hpres2, _⟩ => ?_
  have htr2 : s2.trace = s0.trace := by simp [hpres2.2, s_call, htr, arm64_norm]
  rcases hcs2 with ⟨_, _, _, _, hx23_cs, _⟩
  have hx23_2 : s2.readReg64 .x23 = ikCap := by simp [hx23_cs, s_call, hx23, arm64_norm]
  set st1 := M.stepEvents (rustDeallocEvents msgCap.toNat 1) st
  refine SepWPp.mono_pre
    (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        vecU8Buf A.repAlloc ikCap ikPtr ik ∗ vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        A.pool lim st1 s2 ∗ stackAt sp' smallRootStack) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr))
    (by
      apply entails_of_eq
      simp only [s_call, hstack, hsp_eq, arm64_norm]
      sep_ac_rfl) ?_
  refine SepWPp.frame_noPanic_pk
    (cleanup_568_placed_wp hkf hdealloc ik bk
      (PreKeyPostState.of_steps hinv2 (by dsimp only [s_call] at hsp2; tryFromPost_sp [hsp2, hsp_eq])
        hsp_eq hsp htr2) hpc2 hrun2 hx23_2)
    fun sf Pf ⟨evs2, hevs2, hstf, hent⟩ =>
      ⟨rustDeallocEvents msgCap.toNat 1 ++ evs2,
        (freeOnly_rustDeallocEvents msgCap.toNat 1).append hevs2, hstf, ?_⟩
  rw [M.stepEvents_append]
  refine Entails.trans (sepConj_mono_left hent) ?_
  apply entails_of_eq; sep_ac_rfl

theorem cleanup_554_placed_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A lim H)
    {s0 s : State} {sp' msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (msg ik bk : List (BitVec 8)) (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2596#64)
    (hrun : s.status = .Running) (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ vecU8Buf A.repAlloc msgCap msgPtr msg ∗
        vecU8Buf A.repAlloc ikCap ikPtr ik ∗ vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  by_cases hcap : msgCap = 0#64
  · subst hcap
    rw [vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2616#64) ?_
    wp_steps_sync_111 ((blkPl_111).base + 2616#64)
    refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨inferInstance, fun hinv1 => ?_⟩
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          vecU8Buf A.repAlloc ikCap ikPtr ik ∗ vecU8Buf A.repAlloc bkCap bkPtr bk ∗
          A.pool lim st _ ∗ stackAt sp' smallRootStack) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    refine SepWPp.frame_noPanic_pk
      (cleanup_568_placed_wp hkf hdealloc ik bk
        (PreKeyPostState.of_steps hinv1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp [hx23, arm64_norm]))
      fun sf Pf ⟨evs, hevs, hstf, hent⟩ => ⟨evs, hevs, hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; sep_ac_rfl
  · have hbeq : (msgCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2600#64) ?_
    wp_steps_sync_111 ((blkPl_111).base + 2600#64)
    refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨inferInstance, fun hinv1 => ?_⟩
    refine SepWPp.let_state ?_; intro s_next
    have hst_next : PreKeyPostState Inv s0 sp' s_next :=
      PreKeyPostState.of_steps hinv1
        (by dsimp only [s_next]; tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by dsimp only [s_next]; simp [htr, arm64_norm])
    have hx23_next : s_next.readReg64 .x23 = ikCap := by
      dsimp only [s_next]; simp [hx23, arm64_norm]
    have hx26_next : s_next.readReg64 .x26 = msgCap := by
      dsimp only [s_next]; simp [hx26, arm64_norm]
    refine SepWPp.mono_pre
      (by dsimp only [s_next]; apply entails_of_eq; sep_ac_rfl)
      (cleanup_558_placed_wp (st := st) (bkCap := bkCap) (bkPtr := bkPtr)
        (msgPtr := msgPtr) (ikPtr := ikPtr) hkf hdealloc msg ik bk hcap hst_next
        (by simp_all [s_next, arm64_norm]) (by simp_all [s_next, arm64_norm])
        hx23_next hx26_next)

/-! ## Segment 1 (`+1120 .. +1476` → `+1668`) -/

theorem post_seg1a_f90_to_0ac_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hDropSpe : PreKeyDropSpeOk Inv A lim H)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberCap kyberPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64} {opkVal : BitVec 32}
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hinv : Inv s.mem)
    (htr : s.trace = s0.trace) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1404#64) s
      (memRegion (sp' + 16#64) 96 ∗
        vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
        vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A.repAlloc (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
        vecU8At A.repAlloc (sp' + 384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
        ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
        A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        PreKeyPostState Inv s0 sp' sf ∧ kyberCap.toNat < 2 ^ 63 ∧ bkCap.toNat < 2 ^ 63 ∧
        ikCap.toNat < 2 ^ 63 ∧ msgCap.toNat < 2 ^ 63 ∧ sf.readReg64 .x29 = sp' + 512#64 ∧
        sf.readReg64 .x28 = kyberCap ∧
        sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
        sf.readReg64 .x25 = kyberPtr ∧
        sf.readReg64 .x24 = 1#64 ∧ sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = 0x44#64 ∧
        sf.readReg64 .x21 = x.ptr ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧ sf.readReg64 .x19 = x.sret ∧
        (Pf ⊢ seg1SpillsAt sp' x opkVal bkCap bkPtr msgPtr ikPtr ∗ memRegion (sp' + 312#64) 48 ∗
          memRegion (sp' + 360#64) 72 ∗
          memRegion (sp' + 432#64) 8 ∗ vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes ∗
          vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
          vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
          vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h27 := hregs.x27
  have h22 := hregs.x22
  have h21 := hregs.x21
  have h20 := hregs.x20
  have h19 := hregs.x19
  have hstackSpe := stackAt_sub_split sp' dropSpeStack smallRootStack (by decide) (by decide)
  rw [← sepConj_assoc (vecU8At A.repAlloc (sp' + 360#64) ikCap ikPtr x.ikBytes),
      ← sepConj_assoc (vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes),
      ← sepConj_assoc (vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr x.kyberBytes)]
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion96_seg1_unpack sp') (sepConj_mono_left (post_vecU8At4_lt A.repAlloc
        (sp' + 312#64) kyberCap kyberPtr (sp' + 336#64) bkCap bkPtr
        (sp' + 360#64) ikCap ikPtr (sp' + 384#64) msgCap msgPtr
        x.kyberBytes x.bkBytes x.ikBytes x.inner))) ?_
  simp only [sepConj_assoc, sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w16 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w24 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w32 => SepWPp.exists_pre fun w40 =>
    SepWPp.exists_pre fun w48 => SepWPp.exists_pre fun w52 =>
    SepWPp.exists_pre fun w56 => SepWPp.exists_pre fun w68 =>
    SepWPp.exists_pre fun w72 => SepWPp.exists_pre fun w80 =>
    SepWPp.exists_pre fun w88 => SepWPp.exists_pre fun w96 =>
    SepWPp.exists_pre fun w104 => ?_
  rw [← sepConj_assoc ((sp' + 16#64) ↦₃₂ w16), ← sepConj_assoc (_ ∗ ((sp' + 20#64) ↦₃₂ w20)),
      ← sepConj_assoc (_ ∗ ((sp' + 24#64) ↦₃₂ w24)), ← sepConj_assoc (_ ∗ ((sp' + 28#64) ↦₃₂ w28)),
      ← sepConj_assoc (_ ∗ ((sp' + 32#64) ↦₆₄ w32)), ← sepConj_assoc (_ ∗ ((sp' + 40#64) ↦₆₄ w40)),
      ← sepConj_assoc (_ ∗ ((sp' + 48#64) ↦₃₂ w48)), ← sepConj_assoc (_ ∗ ((sp' + 52#64) ↦₃₂ w52)),
      ← sepConj_assoc (_ ∗ ((sp' + 56#64) ↦₆₄ w56)),
      ← sepConj_assoc (_ ∗ memRegion (sp' + 64#64) 4),
      ← sepConj_assoc (_ ∗ ((sp' + 68#64) ↦₃₂ w68)), ← sepConj_assoc (_ ∗ ((sp' + 72#64) ↦₆₄ w72)),
      ← sepConj_assoc (_ ∗ ((sp' + 80#64) ↦₆₄ w80)), ← sepConj_assoc (_ ∗ ((sp' + 88#64) ↦₆₄ w88)),
      ← sepConj_assoc (_ ∗ ((sp' + 96#64) ↦₆₄ w96)), sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun ⟨hky_lt, hbk_lt, hik_lt, hmsg_lt⟩ => ?_
  rw [vecU8At_eq_header_buf A.repAlloc (sp' + 312#64),
      vecU8At_eq_header_buf A.repAlloc (sp' + 336#64),
      vecU8At_eq_header_buf A.repAlloc (sp' + 360#64),
      vecU8At_eq_header_buf A.repAlloc (sp' + 384#64)]
  simp only [PreKeyTryFromArgs.kyberBytes_length, PreKeyTryFromArgs.bkBytes_length,
    PreKeyTryFromArgs.ikBytes_length]
  have hky_ne := cap_add2_ne_of_lt hky_lt
  have hbk_eq := cap_add1_eq_of_lt hbk_lt
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_pk hkf hinv (mid := lsmpl.base 5) ?_
  wp_steps_sync_111 (lsmpl.base 5)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv1 => ?_⟩
  refine SepWPp.let_state ?_; intro s_call
  have hw5 :
      ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ 1569#64) ∗ ((sp' + 336#64) ↦₆₄ bkCap) ∗
        ((sp' + 344#64) ↦₆₄ bkPtr) ∗ ((sp' + 352#64) ↦₆₄ 33#64) ⊢ memRegion (sp' + 320#64) 40 := by
    simpa [words5At, BitVec.add_assoc, BitVec.reduceAdd] using
      words5At_entails_memRegion (sp' + 320#64) kyberPtr 1569#64 bkCap bkPtr 33#64
  have hhdr80 := post_headers_entails_memRegion80 sp' ikCap ikPtr msgCap msgPtr
    (BitVec.ofNat 64 x.inner.length) x.regId (opkTag x) opkVal x.spkId x.kpkId
  dsimp only [vecHeader] at hhdr80
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hhdr80
  have hspe : speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre
    (P' := (speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool lim st s_call ∗
      stackAt sp' dropSpeStack) ∗
      (seg1SpillsAt sp' x opkVal bkCap bkPtr msgPtr ikPtr ∗ memRegion (sp' + 360#64) 72 ∗
        memRegion (sp' + 432#64) 8 ∗
        vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes ∗
        vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
        vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
        memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - dropSpeStack)))
    (by
      rw [hspe, hstackSpe]
      dsimp only [seg1SpillsAt]
      refine Entails.trans (Q :=
        (((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ 1569#64) ∗ ((sp' + 336#64) ↦₆₄ bkCap) ∗
        ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 352#64) ↦₆₄ 33#64)) ∗ (((sp' + 360#64) ↦₆₄ ikCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
          ((sp' + 376#64) ↦₆₄ 33#64) ∗
          ((sp' + 384#64) ↦₆₄ msgCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' +
          400#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
          ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
          ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗
          ((sp' + 436#64) ↦₃₂ x.kpkId)) ∗
        (((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ A.pool lim st s_call ∗
          stackAt sp' dropSpeStack ∗
          ((sp' + 16#64) ↦₃₂ x.kpkId) ∗ ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗
          ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗
          ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗ ((sp' + 56#64) ↦₆₄ 33#64) ∗
          memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' +
          80#64) ↦₆₄ bkPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes ∗
          vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
          vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
          vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
          memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - dropSpeStack)))
        (by apply entails_of_eq; sep_ac_rfl) ?_
      refine Entails.trans (sepConj_mono hw5 (sepConj_mono_left hhdr80)) ?_
      apply entails_of_eq; sep_ac_rfl) ?_
  refine SepWPp.call_noPanic_budget_pk hkf
    ((⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost), st) hDropSpe
    (by simp_all [s_call, arm64_norm]) (by simp_all [s_call, arm64_norm])
    (by dsimp only [s_call]; tryFromPost_sp_align hsp) hinv1
    (ret_pc := (blkPl_111).base + 1404#64) (by simp_all [s_call, arm64_norm])
    (T := speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗
      A.pool lim st s_call ∗ stackAt sp' dropSpeStack)
    (φ := sp' + 312#64 = sp' + 312#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_111).base + 1404#64))
    (by simp_all [s_call, dropSpeSpec, arm64_norm])
    ⟨rfl, ⟨111, by decide, 1404, by decide, rfl⟩⟩ (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [dropSpeSpec]
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun evs => SepWPp.pure_pre fun htr2 => ?_
  rw [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs⟩
  refine SepWPp.of_sepWP_end_noPanic_pk hkf hinv2 ?_
  refine ProofLib.SepWP.done hpc2 hrun2 ⟨inferInstance, fun hinv3 => ?_⟩
  refine ⟨evs, hevs,
    ⟨by dsimp only [s_call] at hsp2; tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hinv3,
      by simp [htr2, s_call, htr, arm64_norm]⟩,
    hky_lt, hbk_lt, hik_lt, hmsg_lt,
    by simp [hx29_cs, s_call, h29, arm64_norm],
    by simp [hx28_cs, s_call, arm64_norm],
    by simp [hx27_cs, s_call, h27, arm64_norm],
    by simp [hx26_cs, s_call, arm64_norm],
    by simp [hx25_cs, s_call, arm64_norm],
    by simp [hx24_cs, s_call, arm64_norm],
    by simp [hx23_cs, s_call, arm64_norm],
    by simp [hx22_cs, s_call, h22, arm64_norm],
    by simp [hx21_cs, s_call, h21, arm64_norm],
    by simp [hx20_cs, s_call, h20, arm64_norm],
    by simp [hx19_cs, s_call, h19, arm64_norm], ?_⟩
  have hs_call_sp : s_call.sp = sp' := by simp [s_call, hsp_eq, arm64_norm]
  simp only [hs_call_sp, hstackSpe, arm64_norm]
  apply entails_of_eq; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem post_seg1b_0ac_to_1b4_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hDropSpe : PreKeyDropSpeOk Inv A lim H)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64}
    (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1404#64)
    (hrun : s.status = .Running) (hik_lt : ikCap.toNat < 2 ^ 63) (hmsg_lt : msgCap.toNat < 2 ^ 63)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx24 : s.readReg64 .x24 = 1#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = 0x44#64)
    (hx21 : s.readReg64 .x21 = x.ptr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1668#64) s
      (((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ memRegion (sp' + 312#64) 48 ∗
        vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗ lsLogOff ∗ A.pool lim st s ∗
        stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        PreKeyPostState Inv s0 sp' sf ∧ sf.readReg64 .x29 = sp' + 512#64 ∧
        sf.readReg64 .x28 = kyberCap ∧
        sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
        sf.readReg64 .x25 = kyberPtr ∧
        sf.readReg64 .x24 = 1#64 ∧ sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = 0x44#64 ∧
        sf.readReg64 .x21 = x.ptr ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧ sf.readReg64 .x19 = x.sret ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 312#64) ↦₈ 0#8) ∗
          ((sp' + 313#64) ↦ₛ x.baseKey.toList) ∗
          memRegion (sp' + 345#64) 15 ∗ vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗ lsLogOff ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hcallDeser := ls_subroutine_ok_pk_of_plain
    (callerProg := preKeyPlacedProg H) hcl_of_inv (deserialize_placed_ok H)
  have hik_eq := cap_add1_eq_of_lt hik_lt
  have hmsg_eq := cap_add1_eq_of_lt hmsg_lt
  have hstackSpe := stackAt_sub_split sp' dropSpeStack smallRootStack (by decide) (by decide)
  have hspe : speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (post_memRegion48_split8 (sp' + 312#64))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine SepWPp.exists_pre fun w312_1 => ?_
  refine SepWPp.of_sepWP_pk hkf hinv (mid := lsmpl.base 5) ?_
  wp_steps_sync_111 (lsmpl.base 5)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv1 => ?_⟩
  refine SepWPp.let_state ?_; intro sc1
  refine SepWPp.call_noPanic_budget_pk hkf
    ((⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost), st) hDropSpe
    (by simp_all [sc1, arm64_norm]) (by simp_all [sc1, arm64_norm])
    (by dsimp only [sc1]; simpa [State.spAligned, arm64_norm] using hsp) hinv1
    (ret_pc := (blkPl_111).base + 1424#64) (by simp_all [sc1, arm64_norm])
    (T := speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗
      A.pool lim st sc1 ∗ stackAt sp' dropSpeStack)
    (φ := sp' + 312#64 = sp' + 312#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_111).base + 1424#64))
    (by simp_all [sc1, dropSpeSpec, arm64_norm])
    ⟨rfl, ⟨111, by decide, 1424, by decide, rfl⟩⟩ (by rw [hspe, hstackSpe]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [dropSpeSpec]
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun evs1 => SepWPp.pure_pre fun htr2 => ?_
  rw [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs1 => ?_
  have hsc1_sp : sc1.sp = sp' := by simp [sc1, hsp_eq, arm64_norm]
  rw [hsc1_sp] at hsp2 ⊢
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2, hv_2⟩
  clear hv_2
  dsimp only [sc1] at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  simp only [htr, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19, arm64_norm]
    at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  clear_value sc1; clear sc1 hsc1_sp
  set st1 := M.stepEvents evs1 st
  refine SepWPp.mono_pre
    (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w312_2 => ?_
  refine SepWPp.of_sepWP_pk hkf hinv2 (mid := lsmpl.base 5) ?_
  wp_steps_sync_111 (lsmpl.base 5)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv3 => ?_⟩
  refine SepWPp.let_state ?_; intro sc2
  refine SepWPp.call_noPanic_budget_pk hkf
    ((⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost), st1) hDropSpe
    (by simp_all [sc2, arm64_norm]) (by simp_all [sc2, arm64_norm])
    (by dsimp only [sc2]; simpa [State.spAligned, arm64_norm] using hsp2_align) hinv3
    (ret_pc := (blkPl_111).base + 1444#64) (by simp_all [sc2, arm64_norm])
    (T := speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗
      A.pool lim st1 sc2 ∗ stackAt sp' dropSpeStack)
    (φ := sp' + 312#64 = sp' + 312#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_111).base + 1444#64))
    (by simp_all [sc2, dropSpeSpec, arm64_norm])
    ⟨rfl, ⟨111, by decide, 1444, by decide, rfl⟩⟩ (by rw [hspe]; sep_focus)
    ?_
  intro s4 hpc4 hrun4 hsp4 hsp4_align hinv4 hcs4
  dsimp only [dropSpeSpec]
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun evs2 => SepWPp.pure_pre fun htr4 => ?_
  rw [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs2 => ?_
  have hsc2_sp : sc2.sp = sp' := by simp [sc2, hsp2, arm64_norm]
  rw [hsc2_sp] at hsp4 ⊢
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4,
    hx29_4, hv_4⟩
  clear hv_4
  dsimp only [sc2] at htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
  simp only [htr2, hx29_2, hx28_2, hx27_2, hx26_2, hx25_2, hx24_2, hx23_2, hx22_2, hx21_2, hx20_2,
    hx19_2, arm64_norm]
    at htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
  clear_value sc2; clear sc2 hsc2_sp
  set st2 := M.stepEvents evs2 st1
  refine SepWPp.mono_pre
    (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w312_3 => ?_
  refine SepWPp.of_sepWP_pk hkf hinv4 (mid := lsmpl.base 5) ?_
  wp_steps_sync_111 (lsmpl.base 5)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv5 => ?_⟩
  refine SepWPp.let_state ?_; intro sc3
  refine SepWPp.call_noPanic_budget_pk hkf
    ((⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost), st2) hDropSpe
    (by simp_all [sc3, arm64_norm]) (by simp_all [sc3, arm64_norm])
    (by dsimp only [sc3]; simpa [State.spAligned, arm64_norm] using hsp4_align) hinv5
    (ret_pc := (blkPl_111).base + 1460#64) (by simp_all [sc3, arm64_norm])
    (T := speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗
      A.pool lim st2 sc3 ∗ stackAt sp' dropSpeStack)
    (φ := sp' + 312#64 = sp' + 312#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_111).base + 1460#64))
    (by simp_all [sc3, dropSpeSpec, arm64_norm])
    ⟨rfl, ⟨111, by decide, 1460, by decide, rfl⟩⟩ (by rw [hspe]; sep_focus)
    ?_
  intro s6 hpc6 hrun6 hsp6 hsp6_align hinv6 hcs6
  dsimp only [dropSpeSpec]
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun evs3 => SepWPp.pure_pre fun htr6 => ?_
  rw [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs3 => ?_
  have hsc3_sp : sc3.sp = sp' := by simp [sc3, hsp4, arm64_norm]
  rw [hsc3_sp] at hsp6 ⊢
  rcases hcs6 with ⟨hx19_6, hx20_6, hx21_6, hx22_6, hx23_6, hx24_6, hx25_6, hx26_6, hx27_6, hx28_6,
    hx29_6, hv_6⟩
  clear hv_6
  dsimp only [sc3] at htr6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 hx29_6
  simp only [htr4, hx29_4, hx28_4, hx27_4, hx26_4, hx25_4, hx24_4, hx23_4, hx22_4, hx21_4, hx20_4,
    hx19_4, arm64_norm]
    at htr6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 hx29_6
  clear_value sc3; clear sc3 hsc3_sp
  set st3 := M.stepEvents evs3 st2
  refine SepWPp.mono_pre
    (P' := ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ (bkPtr ↦ₛ x.bkBytes) ∗
      vecU8Rest A.repAlloc bkCap bkPtr x.bkBytes ∗
      memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗ lsLogOff ∗ A.pool lim st3 s6 ∗
        stackAt sp' smallRootStack)
    (by
      rw [post_memRegion48_split33_15 sp']
      simp only [hstackSpe, sepConj_assoc, arm64_norm]
      refine Entails.trans
        (Q := vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗ (memRegion (sp' + 312#64) 33 ∗
          memRegion (sp' + 345#64) 15 ∗
          A.pool lim st3 s6 ∗ stackAt sp' dropSpeStack ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ lsLogOff ∗
          memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - dropSpeStack)))
        (by simp only [smallRootStack, dropSpeStack, arm64_norm]; apply entails_of_eq; sep_ac_rfl) ?_
      refine Entails.trans
        (sepConj_mono_left (vecU8Buf_to_slice_rest A.repAlloc bkCap bkPtr x.bkBytes)) ?_
      simp only [smallRootStack, dropSpeStack, arm64_norm]; apply entails_of_eq; sep_ac_rfl) ?_
  refine SepWPp.of_sepWP_pk hkf hinv6 (mid := lsmpl.base 201) ?_
  wp_steps_sync_111 (lsmpl.base 201)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv7 => ?_⟩
  refine SepWPp.let_state ?_; intro sc4
  have hbk_deser : PublicKey.deserialize x.bkBytes = .ok ⟨x.baseKey⟩ := deserialize_djb_ok x.baseKey
  have hbk_len : (33#64 : BitVec 64).toNat = x.bkBytes.length := by simp
  have hbk_lt63 : x.bkBytes.length < 2 ^ 63 := by simp
  refine SepWPp.call_noPanic_budget_pk hkf (bkPtr, x.bkBytes, ⟨x.baseKey⟩, sp' + 312#64) hcallDeser
    (by simp_all [sc4, arm64_norm]) (by simp_all [sc4, arm64_norm])
    (by dsimp only [sc4]; simpa [State.spAligned, arm64_norm] using hsp6_align) hinv7
    (ret_pc := (blkPl_111).base + 1472#64) (by simp_all [sc4, arm64_norm])
    (T := (bkPtr ↦ₛ x.bkBytes) ∗ memRegion (sp' + 312#64) 33 ∗ lsLogOff)
    (φ := bkPtr = bkPtr ∧ (33#64 : BitVec 64).toNat = x.bkBytes.length ∧ sp' + 312#64 = sp' +
      312#64 ∧ x.bkBytes.length < 2 ^ 63 ∧ PublicKey.deserialize x.bkBytes = .ok ⟨x.baseKey⟩)
    (by simp_all [sc4, deserializeOk33PlacedSpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.ResponderWire.deserializeOk33PlacedSpec, arm64_norm])
    ⟨rfl, hbk_len, rfl, hbk_lt63, hbk_deser⟩ (by sep_focus)
    ?_
  clear hcallDeser
  intro s8 hpc8 hrun8 hsp8 hsp8_align hinv8 hcs8
  dsimp only [deserializeOk33PlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderWire.deserializeOk33PlacedSpec]
  simp only [sepConj_assoc]
  refine SepWPp.pure_pre fun hvm8 => SepWPp.pure_pre fun htr8 => ?_
  have hpool8 : A.pool lim st3 sc4 = A.pool lim st3 s8 :=
    (A.pool_transport lim st3 sc4 s8 hvm8).symm
  rw [hpool8]; clear hvm8 hpool8
  have hsc4_sp : sc4.sp = sp' := by simp [sc4, hsp6, arm64_norm]
  rw [hsc4_sp] at hsp8
  rcases hcs8 with ⟨hx19_8, hx20_8, hx21_8, hx22_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8,
    hx29_8, hv_8⟩
  clear hv_8
  dsimp only [sc4] at htr8 hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8 hx25_8 hx26_8 hx27_8 hx28_8 hx29_8
  simp only [htr6, hx29_6, hx28_6, hx27_6, hx26_6, hx25_6, hx24_6, hx23_6, hx22_6, hx21_6, hx20_6,
    hx19_6, arm64_norm]
    at htr8 hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8 hx25_8 hx26_8 hx27_8 hx28_8 hx29_8
  clear_value sc4; clear sc4 hsc4_sp
  refine SepWPp.of_sepWP_end_noPanic_pk hkf hinv8 ?_
  wp_steps_sync_111 ((blkPl_111).base + 1668#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv9 => ?_⟩
  refine ⟨evs1 ++ evs2 ++ evs3, (hevs1.append hevs2).append hevs3,
    ⟨by simp [hsp8, arm64_norm],
      by simpa [State.spAligned, arm64_norm] using hsp8_align,
      hinv9, by simp [htr8, arm64_norm]⟩,
    by simp [hx29_8, arm64_norm],
    by simp [hx28_8, arm64_norm],
    by simp [hx27_8, arm64_norm],
    by simp [hx26_8, arm64_norm],
    by simp [hx25_8, arm64_norm],
    by simp [hx24_8, arm64_norm],
    by simp [hx23_8, arm64_norm],
    by simp [hx22_8, arm64_norm],
    by simp [hx21_8, arm64_norm],
    by simp [hx20_8, arm64_norm],
    by simp [hx19_8, arm64_norm], ?_⟩
  have hst3 : st3 = M.stepEvents (evs1 ++ evs2 ++ evs3) st := by
    simp only [st3, st2, st1, M.stepEvents_append, List.append_assoc]
  rw [hst3]
  have hrepack := slice_rest_to_vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes
  refine Entails.trans
    (Q := (bkPtr ↦ₛ x.bkBytes) ∗ vecU8Rest A.repAlloc bkCap bkPtr x.bkBytes ∗
      (((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ x.baseKey.toList) ∗
        lsLogOff ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 345#64) 15 ∗
        A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3) st) _ ∗ stackAt sp' smallRootStack))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  rw [← sepConj_assoc (bkPtr ↦ₛ x.bkBytes)]
  refine Entails.trans (sepConj_mono_left hrepack) ?_
  apply entails_of_eq; sep_ac_rfl

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
