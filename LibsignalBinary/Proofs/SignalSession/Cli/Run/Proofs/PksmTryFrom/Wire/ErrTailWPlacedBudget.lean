/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailWPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Loop-Decode Error Tail and Shared Epilogue

Allocation-budget (`RustCliAllocBudget M`) proofs of the shared epilogue (`+0x504..+0x520 → ret`)
and the `+0x460 → +0x504` loop-decode error deallocation chain (`FreeOnlyEvs`) on
`preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailWPlacedBudget

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet SepProp
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr hiding optU32At
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding rustDeallocExternSpecWithStack
open CryptoVerification.LibsignalTripleRatchet.Prost hiding
  memRegion_split dropDecodeErrorSpecGen dropDecodeErrorSpecX
open CryptoVerification.LibsignalTripleRatchet.Getters hiding lsRustDeallocSym
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire hiding
  SepWPp SepWPp.pure_pre SepWPp.exists_pre SepWPp.mono_pre
  epilogue_504_placed_w_wpX epilogue_504_err_placed_w_wpE
  cleanup_4f4_drop_placed_wpX cleanup_4cc_placed_wpX cleanup_4b4_placed_wpX
  cleanup_4a4_placed_wpX cleanup_47c_placed_wpX
  preKey_loopErr_460_to_504_placed_wpE preKey_loopErr_460_placed_wpE
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   RustLayoutOk rustDeallocEvents)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
  (freeOnly_rustDeallocEvents preKeyNoPanicQp)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget
  (sepWP_done_sync_pool_111 sepWP_seg_111)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DropDecodeErrorEnv dropDecodeErrorSpecGen dropDecodeErrorSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (sepWPp_end_noPanic_placed)

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

@[local arm64_norm, local wp_norm]
private theorem etwb_bv_add_neg_120 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 120) = sp' + 392#64 := by bv_omega
@[local arm64_norm, local wp_norm]
private theorem etwb_bv_add_neg_144 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 144) = sp' + 368#64 := by bv_omega

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

/-- `DropDecodeErrorEnv` emits only `dealloc` events. -/
theorem freeOnly_dropDecodeErrorEnv {evs : List AllocEvent} (h : DropDecodeErrorEnv evs) :
    FreeOnlyEvs evs := by
  rcases h with rfl | ⟨c, _, _, rfl⟩
  · exact freeOnly_rustDeallocEvents 72 8
  · exact (freeOnly_rustDeallocEvents (c * 32) 8).append (freeOnly_rustDeallocEvents 72 8)

theorem sepWPp_anyQp_of_noPanic {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q preKeyNoPanicQp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hok | ⟨_, _, _, hqp⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact False.elim hqp
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

private theorem sepWPp_perm {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P' Q Qp) (hP : P ⊢ P') :
    SepWPp prog ret s P Q Qp :=
  Wire.SepWPp.mono_pre hP h

private theorem sepWPp_mono_post_pk {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q' Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) (hQ : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp :=
  LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.sepWPp_mono_post hQ h

private theorem etwb_stackAt_preKeyTryFrom_unsplit (sp : BitVec 64) (s0 : State) :
    stackAt (sp - 608#64) preKeyTryFromSubStack ∗
      memRegion (sp - 608#64) 296 ∗
      memRegion (sp - 608#64 + 296#64) 152 ∗
      memRegion (sp - 608#64 + 448#64) 64 ∗
      preKeyCalleeSavedAt (sp - 608#64) s0 ⊢
      stackAt sp preKeyTryFromStack := by
  rw [stackAt_preKeyTryFrom_split sp]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (preKeyCalleeSavedAt_entails_memRegion96 (sp - 608#64) s0))))

/-! ## 1. Shared Epilogue (`+0x504 .. +0x520` → `s0.readReg64 .x30`) -/

theorem epilogue_504_placed_w_wpX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {s0 s : State} {R : SepProp}
    {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (blkPl_111).base + 1284#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        R ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim st s)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
        (Pf ⊢ ⌜sf.trace = s0.trace⌝ ∗ R ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
          stackAt s0.sp preKeyTryFromStack ∗ A.pool lim st sf))
      Qp := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hsp0 : s0.spAligned = true := by
    rw [State.spAligned, hsp_eq, beq_iff_eq] at hsp
    rw [State.spAligned, beq_iff_eq]
    generalize s0.sp = sp0 at hsp ⊢
    bv_bits
  unfold preKeyCalleeSavedAt
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  refine sepWPp_anyQp_of_noPanic (sepWPp_end_noPanic_placed (s0 := s0) hcl ?_)
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine ⟨by simp_all [arm64_norm], fun hv => ?_, hcl1, by simp [htr, arm64_norm], ?_⟩
  · refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], hv⟩
  · rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hstk := etwb_stackAt_preKeyTryFrom_unsplit s0.sp s0
    unfold preKeyCalleeSavedAt at hstk
    simp only [bv_sub_add_lit', BitVec.reduceSub] at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk))))
    apply entails_of_eq; sep_ac_rfl

theorem epilogue_504_err_placed_w_wpE [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {s0 s : State} {Qp : State → SepProp → Prop}
    (fn : List (BitVec 8)) (e : SignalProtocolError)
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (blkPl_111).base + 1284#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (pksmErrE A.repAlloc fn x.ret e ∗ anyHeap) ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim st s)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
        (Pf ⊢ ⌜sf.trace = s0.trace⌝ ∗
          (pksmErrE A.repAlloc fn x.ret e ∗ anyHeap) ∗
          (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
          stackAt s0.sp preKeyTryFromStack ∗ A.pool lim st sf))
      Qp :=
  epilogue_504_placed_w_wpX hst hpc hrun

/-! ## 2. Loop-Decode Error Deallocation Chain (`+0x47c .. +0x500 → +0x504`) -/

set_option maxHeartbeats 800000 in
theorem cleanup_4f4_drop_placed_wpX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (dropDecodeErrorSpecX A lim)))
    {s0 s : State} {sp' sret x24 w0 w1 : BitVec 64} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1268#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hstack := stackAt_skipFieldStackW_dropDecodeError sp'
  have hdstack : 0x20 + extHookStack = dropDecodeErrorStackX := rfl
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 4) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine let_state_pk ?_; intro s_call
  refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded (x24, st) hDropErr
    (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
    (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 1276#64) (by simp [s_call, arm64_norm])
    (T := decodeErrorAt A.repAlloc x24 ∗ A.pool lim st s_call ∗
      stackAt sp' dropDecodeErrorStackX)
    (φ := x24 = x24)
    (by simp (config := { decide := true }) [s_call, dropDecodeErrorSpecX, dropDecodeErrorSpecGen, hdstack, hsp_eq, arm64_norm, wp_norm])
    rfl (by rw [hstack]; sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropDecodeErrorSpecX, dropDecodeErrorSpecGen]
  simp only [hdstack, sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun evs => ?_
  refine Wire.SepWPp.pure_pre fun hevs => ?_
  rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, _, _, hx27_cs, _⟩
  have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = sret := by
    simp [hx19_cs, s_call, hx19, arm64_norm]
  have hx27_2 : s2.readReg64 (Reg.gpr 27#5) = 0x8000000000000002#64 := by
    simp [hx27_cs, s_call, hx27, arm64_norm]
  have hsp2_eq : s2.sp = sp' := by simp [hsp2, s_call, hsp_eq, arm64_norm]
  have htr2_eq : s2.trace = s0.trace := by simp [htr2, s_call, htr, arm64_norm]
  clear hx19_cs hx27_cs hsp2 htr2
  refine sepWPp_end_noPanic_placed (s0 := s0) hcl2 ?_
  apply sepWP_seg_111; intro _m_strip2
  wp_steps
  refine sepWP_done_sync_pool_111 A lim (M.stepEvents evs st) fun _ hcl3 => ?_
  refine ⟨PreKeyPostState.of_steps hcl3 (by simp [hsp2_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr2_eq, arm64_norm]), evs, freeOnly_dropDecodeErrorEnv hevs, ?_⟩
  apply entails_of_eq
  simp only [s_call, hstack, hsp_eq, errTag, arm64_norm]; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem cleanup_4cc_placed_wpX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (rustDeallocExternSpecWithStack M A lim extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (dropDecodeErrorSpecX A lim)))
    {s0 s : State} {sp' sret x24 w0 w1 msgCap msgPtr : BitVec 64} {Qp : State → SepProp → Prop}
    (msgAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1228#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64)
    (hx26 : s.readReg64 .x26 = msgCap) (hx21 : s.readReg64 .x21 = msgPtr) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
        decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases msgAct with
  | false =>
    change SepWPp _ _ _ (⌜msgCap = noneCap ∨ msgCap = 0#64⌝ ∗ _) _ _
    refine Wire.SepWPp.pure_pre fun hcap => ?_
    have hslt := slt_one_of_false_cap hcap
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1268#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine Wire.SepWPp.mono_pre
      (P' := decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st _ ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact cleanup_4f4_drop_placed_wpX hDropErr
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm]) (by simp [hx27, arm64_norm])
  | true =>
    change SepWPp _ _ _ ((⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
      A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) ∗ _) _ _
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _hptr⟩ => ?_
    have hslt := cap_slt_one_of_pos hpos hlt
    have hlayout : RustLayoutOk msgCap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
    have hstack := stackAt_skipFieldStackX_ext sp'
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine let_state_pk ?_; intro s_call
    refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
      (msgPtr, msgCap.toNat, 1, st) hdeallocX
      (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
      (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
      (ret_pc := (blkPl_111).base + 1252#64) (by simp [s_call, arm64_norm])
      (T := A.pool lim st s_call ∗ A.live msgPtr msgCap.toNat 1 ∗
        memRegion msgPtr msgCap.toNat ∗ stackAt sp' extHookStack)
      (φ := msgPtr = msgPtr ∧ msgCap.toNat = msgCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk msgCap.toNat 1 ∧
        LsRetAddr624 ((blkPl_111).base + 1252#64))
      (by simp_all [s_call, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 1252#64 (by decide) (by decide)⟩ (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, hx24_cs, _, _, hx27_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = sret := by simp [hx19_cs, s_call, hx19, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, s_call, hx24, arm64_norm]
    have hx27_2 : s2.readReg64 .x27 = 0x8000000000000002#64 := by
      simp [hx27_cs, s_call, hx27, arm64_norm]
    have hsp2_eq : s2.sp = sp' := by simp [hsp2, s_call, hsp_eq, arm64_norm]
    have htr2_eq : s2.trace = s0.trace := by simp [htr2, s_call, htr, arm64_norm]
    clear hx19_cs hx24_cs hx27_cs hsp2 htr2
    set st1 := M.stepEvents (rustDeallocEvents msgCap.toNat 1) st
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl2 (mid := (blkPl_111).base + 1268#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st1 fun _ hcl3 => ?_
    refine Wire.SepWPp.mono_pre
      (P' := decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st1 _ ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    exact sepWPp_mono_post_pk
      (cleanup_4f4_drop_placed_wpX (st := st1) hDropErr
        (PreKeyPostState.of_steps hcl3 (by simp [hsp2_eq, arm64_norm]) hsp_eq hsp
          (by simp [htr2_eq, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        (by simp [hx19_2, arm64_norm]) (by simp [hx24_2, arm64_norm]) (by simp [hx27_2, arm64_norm]))
      fun sf Pf ⟨hstf, evs2, hf2, hent2⟩ =>
        ⟨hstf, rustDeallocEvents msgCap.toNat 1 ++ evs2,
         (freeOnly_rustDeallocEvents msgCap.toNat 1).append hf2, by
          rw [M.stepEvents_append]; exact hent2⟩

set_option maxHeartbeats 800000 in
theorem cleanup_4b4_placed_wpX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (rustDeallocExternSpecWithStack M A lim extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (dropDecodeErrorSpecX A lim)))
    {s0 s : State} {sp' sret x24 w0 w1 ikCap ikPtr msgCap msgPtr : BitVec 64}
    {Qp : State → SepProp → Prop}
    (ikAct msgAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1204#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) (hx21 : s.readReg64 .x21 = msgPtr) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
        decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
            (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases ikAct with
  | false =>
    change SepWPp _ _ _ (⌜ikCap = noneCap ∨ ikCap = 0#64⌝ ∗ _) _ _
    refine Wire.SepWPp.pure_pre fun hcap => ?_
    have hslt := slt_one_of_false_cap hcap
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1228#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine Wire.SepWPp.mono_pre
      (P' := (deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
        decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st _ ∗ stackAt sp' (skipFieldStackX 100)) ∗ ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    refine frame_noPanic_pk
      (cleanup_4cc_placed_wpX hdeallocX hDropErr msgAct
        (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
        (by simp [hx27, arm64_norm]) (by simp [hx26, arm64_norm]) (by simp [hx21, arm64_norm]))
      fun sf Pf ⟨hstf, evs, hf, hent⟩ => ⟨hstf, evs, hf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; sep_ac_rfl
  | true =>
    change SepWPp _ _ _ ((⌜0 < ikCap.toNat ∧ ikCap.toNat < 2 ^ 63 ∧ ikPtr ≠ 0#64⌝ ∗
      A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat) ∗ _) _ _
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _hptr⟩ => ?_
    have hslt := cap_slt_one_of_pos hpos hlt
    have hlayout : RustLayoutOk ikCap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
    have hstack := stackAt_skipFieldStackX_ext sp'
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine let_state_pk ?_; intro s_call
    refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
      (ikPtr, ikCap.toNat, 1, st) hdeallocX
      (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
      (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
      (ret_pc := (blkPl_111).base + 1228#64) (by simp [s_call, arm64_norm])
      (T := A.pool lim st s_call ∗ A.live ikPtr ikCap.toNat 1 ∗
        memRegion ikPtr ikCap.toNat ∗ stackAt sp' extHookStack)
      (φ := ikPtr = ikPtr ∧ ikCap.toNat = ikCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk ikCap.toNat 1 ∧
        LsRetAddr624 ((blkPl_111).base + 1228#64))
      (by simp_all [s_call, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 1228#64 (by decide) (by decide)⟩ (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, hx21_cs, _, _, hx24_cs, _, hx26_cs, hx27_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = sret := by simp [hx19_cs, s_call, hx19, arm64_norm]
    have hx21_2 : s2.readReg64 .x21 = msgPtr := by simp [hx21_cs, s_call, hx21, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, s_call, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = msgCap := by simp [hx26_cs, s_call, hx26, arm64_norm]
    have hx27_2 : s2.readReg64 .x27 = 0x8000000000000002#64 := by
      simp [hx27_cs, s_call, hx27, arm64_norm]
    have hsp2_eq : s2.sp = sp' := by simp [hsp2, s_call, hsp_eq, arm64_norm]
    have htr2_eq : s2.trace = s0.trace := by simp [htr2, s_call, htr, arm64_norm]
    clear hx19_cs hx21_cs hx24_cs hx26_cs hx27_cs hsp2 htr2
    set st1 := M.stepEvents (rustDeallocEvents ikCap.toNat 1) st
    refine Wire.SepWPp.mono_pre
      (P' := (deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
        decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st1 s2 ∗ stackAt sp' (skipFieldStackX 100)) ∗ ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    refine frame_noPanic_pk
      (cleanup_4cc_placed_wpX (st := st1) hdeallocX hDropErr msgAct
        ⟨hsp2_eq, hsp2_align, hcl2, htr2_eq⟩
        hpc2 hrun2 hx19_2 hx24_2 hx27_2 hx26_2 hx21_2)
      fun sf Pf ⟨hstf, evs2, hf2, hent2⟩ =>
        ⟨hstf, rustDeallocEvents ikCap.toNat 1 ++ evs2,
         (freeOnly_rustDeallocEvents ikCap.toNat 1).append hf2, ?_⟩
    rw [M.stepEvents_append]
    refine Entails.trans (sepConj_mono_left hent2) ?_
    apply entails_of_eq; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem cleanup_4a4_placed_wpX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (rustDeallocExternSpecWithStack M A lim extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (dropDecodeErrorSpecX A lim)))
    {s0 s : State} {sp' sret x24 w0 w1 bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {Qp : State → SepProp → Prop}
    (bkAct ikAct msgAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1188#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64)
    (hx0 : s.readReg64 .x0 = bkPtr) (hx1 : s.readReg64 .x1 = bkCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) (hx21 : s.readReg64 .x21 = msgPtr) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
        decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
            (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases bkAct with
  | false =>
    change SepWPp _ _ _ (⌜bkCap = noneCap ∨ bkCap = 0#64⌝ ∗ _) _ _
    refine Wire.SepWPp.pure_pre fun hcap => ?_
    have hslt := slt_one_of_false_cap hcap
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1204#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine Wire.SepWPp.mono_pre
      (P' := deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
        decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st _ ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact cleanup_4b4_placed_wpX hdeallocX hDropErr ikAct msgAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx27, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx21, arm64_norm])
  | true =>
    change SepWPp _ _ _ ((⌜0 < bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0#64⌝ ∗
      A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat) ∗ _) _ _
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _hptr⟩ => ?_
    have hslt := cap_slt_one_of_pos hpos hlt
    have hlayout : RustLayoutOk bkCap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
    have hstack := stackAt_skipFieldStackX_ext sp'
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine let_state_pk ?_; intro s_call
    refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
      (bkPtr, bkCap.toNat, 1, st) hdeallocX
      (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
      (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
      (ret_pc := (blkPl_111).base + 1204#64) (by simp [s_call, arm64_norm])
      (T := A.pool lim st s_call ∗ A.live bkPtr bkCap.toNat 1 ∗
        memRegion bkPtr bkCap.toNat ∗ stackAt sp' extHookStack)
      (φ := s_call.readReg64 (Reg.gpr 0#5) = bkPtr ∧
        (s_call.readReg64 (Reg.gpr 1#5)).toNat = bkCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk bkCap.toNat 1 ∧
        LsRetAddr624 ((blkPl_111).base + 1204#64))
      (by simp [s_call, hsp_eq, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨by simp [s_call, hx0, arm64_norm], by simp [s_call, hx1, arm64_norm], rfl, hlayout,
        lsRetAddr624_blockPlacement_base_add 111 1204#64 (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, hx21_cs, _, hx23_cs, hx24_cs, _, hx26_cs, hx27_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = sret := by simp [hx19_cs, s_call, hx19, arm64_norm]
    have hx21_2 : s2.readReg64 .x21 = msgPtr := by simp [hx21_cs, s_call, hx21, arm64_norm]
    have hx23_2 : s2.readReg64 .x23 = ikCap := by simp [hx23_cs, s_call, hx23, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, s_call, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = msgCap := by simp [hx26_cs, s_call, hx26, arm64_norm]
    have hx27_2 : s2.readReg64 .x27 = 0x8000000000000002#64 := by
      simp [hx27_cs, s_call, hx27, arm64_norm]
    have hsp2_eq : s2.sp = sp' := by simp [hsp2, s_call, hsp_eq, arm64_norm]
    have htr2_eq : s2.trace = s0.trace := by simp [htr2, s_call, htr, arm64_norm]
    clear hx19_cs hx21_cs hx23_cs hx24_cs hx26_cs hx27_cs hsp2 htr2
    set st1 := M.stepEvents (rustDeallocEvents bkCap.toNat 1) st
    refine Wire.SepWPp.mono_pre
      (P' := deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
        decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st1 s2 ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    exact sepWPp_mono_post_pk
      (cleanup_4b4_placed_wpX (st := st1) hdeallocX hDropErr ikAct msgAct
        ⟨hsp2_eq, hsp2_align, hcl2, htr2_eq⟩
        hpc2 hrun2 hx19_2 hx24_2 hx27_2 hx23_2 hx26_2 hx21_2)
      fun sf Pf ⟨hstf, evs2, hf2, hent2⟩ =>
        ⟨hstf, rustDeallocEvents bkCap.toNat 1 ++ evs2,
         (freeOnly_rustDeallocEvents bkCap.toNat 1).append hf2, by
          rw [M.stepEvents_append]; exact hent2⟩

set_option maxHeartbeats 800000 in
theorem cleanup_47c_placed_wpX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (rustDeallocExternSpecWithStack M A lim extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (dropDecodeErrorSpecX A lim)))
    {s0 s : State}
    {sp' sret x24 w0 w1 kyberCap kyberPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {Qp : State → SepProp → Prop}
    (kyberAct bkAct ikAct msgAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1148#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64)
    (hx28 : s.readReg64 .x28 = kyberCap) (hx25 : s.readReg64 .x25 = kyberPtr)
    (hx0 : s.readReg64 .x0 = bkPtr) (hx1 : s.readReg64 .x1 = bkCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) (hx21 : s.readReg64 .x21 = msgPtr) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A.repAlloc kyberCap kyberPtr kyberAct ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
        decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
            (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases kyberAct with
  | false =>
    change SepWPp _ _ _ (⌜kyberCap = noneCap ∨ kyberCap = 0#64⌝ ∗ _) _ _
    refine Wire.SepWPp.pure_pre fun hcap => ?_
    have hslt := slt_one_of_false_cap hcap
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1188#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine Wire.SepWPp.mono_pre
      (P' := deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
        decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st _ ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact cleanup_4a4_placed_wpX hdeallocX hDropErr bkAct ikAct msgAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx27, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
      (by simp [hx23, arm64_norm]) (by simp [hx26, arm64_norm]) (by simp [hx21, arm64_norm])
  | true =>
    change SepWPp _ _ _ ((⌜0 < kyberCap.toNat ∧ kyberCap.toNat < 2 ^ 63 ∧ kyberPtr ≠ 0#64⌝ ∗
      A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat) ∗ _) _ _
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _hptr⟩ => ?_
    have hslt := cap_slt_one_of_pos hpos hlt
    have hlayout : RustLayoutOk kyberCap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
    have hstack := stackAt_skipFieldStackX_ext sp'
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine let_state_pk ?_; intro s_call
    refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
      (kyberPtr, kyberCap.toNat, 1, st) hdeallocX
      (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
      (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
      (ret_pc := (blkPl_111).base + 1180#64) (by simp [s_call, arm64_norm])
      (T := A.pool lim st s_call ∗ A.live kyberPtr kyberCap.toNat 1 ∗
        memRegion kyberPtr kyberCap.toNat ∗ stackAt sp' extHookStack)
      (φ := kyberPtr = kyberPtr ∧ kyberCap.toNat = kyberCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk kyberCap.toNat 1 ∧
        LsRetAddr624 ((blkPl_111).base + 1180#64))
      (by simp_all [s_call, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, hlayout, lsRetAddr624_blockPlacement_base_add 111 1180#64 (by decide) (by decide)⟩ (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, _, hx26_cs, hx27_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = sret := by simp [hx19_cs, s_call, hx19, arm64_norm]
    have hx20_2 : s2.readReg64 (Reg.gpr 20#5) = bkPtr := by simp [hx20_cs, s_call, arm64_norm]
    have hx21_2 : s2.readReg64 .x21 = msgPtr := by simp [hx21_cs, s_call, hx21, arm64_norm]
    have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = bkCap := by simp [hx22_cs, s_call, arm64_norm]
    have hx23_2 : s2.readReg64 .x23 = ikCap := by simp [hx23_cs, s_call, hx23, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, s_call, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = msgCap := by simp [hx26_cs, s_call, hx26, arm64_norm]
    have hx27_2 : s2.readReg64 .x27 = 0x8000000000000002#64 := by
      simp [hx27_cs, s_call, hx27, arm64_norm]
    have hsp2_eq : s2.sp = sp' := by simp [hsp2, s_call, hsp_eq, arm64_norm]
    have htr2_eq : s2.trace = s0.trace := by simp [htr2, s_call, htr, arm64_norm]
    clear hx19_cs hx20_cs hx21_cs hx22_cs hx23_cs hx24_cs hx26_cs hx27_cs hsp2 htr2
    set st1 := M.stepEvents (rustDeallocEvents kyberCap.toNat 1) st
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl2 (mid := (blkPl_111).base + 1188#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st1 fun _ hcl3 => ?_
    refine Wire.SepWPp.mono_pre
      (P' := deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
        decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool lim st1 _ ∗ stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [s_call, hstack, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
    exact sepWPp_mono_post_pk
      (cleanup_4a4_placed_wpX (st := st1) hdeallocX hDropErr bkAct ikAct msgAct
        (PreKeyPostState.of_steps hcl3 (by simp [hsp2_eq, arm64_norm]) hsp_eq hsp
          (by simp [htr2_eq, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        (by simp [hx19_2, arm64_norm]) (by simp [hx24_2, arm64_norm])
        (by simp [hx27_2, arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [hx23_2, arm64_norm]) (by simp [hx26_2, arm64_norm]) (by simp [hx21_2, arm64_norm]))
      fun sf Pf ⟨hstf, evs2, hf2, hent2⟩ =>
        ⟨hstf, rustDeallocEvents kyberCap.toNat 1 ++ evs2,
         (freeOnly_rustDeallocEvents kyberCap.toNat 1).append hf2, by
          rw [M.stepEvents_append]; exact hent2⟩

/-! ## 3. Full Loop-Decode Error Tail (`+0x460 → +0x504` and `+0x460 → ret`) -/

set_option maxHeartbeats 1200000 in
theorem preKey_loopErr_460_to_504_placed_wpE [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (rustDeallocExternSpecWithStack M A lim extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (dropDecodeErrorSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 x24 : BitVec 64} {vb : BitVec 8}
    {Qp : State → SepProp → Prop}
    (hst : PreKeyLoopExitStatePlaced s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = x24) (hx24_ne : x24 ≠ 0#64)
    (mErr : ProtoPreKeySignalMessage) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (wirePreKeyOf A.repAlloc (sp' + 312#64) mErr ∗
        decodeErrorAt A.repAlloc x24 ∗ memRegion sp' 296 ∗ memRegion sret 248 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ memRegion sp' 296 ∗ memRegion (sp' + 312#64) 128 ∗
            (pksmErrE A.repAlloc [] sret .invalidProtobufEncoding ∗ anyHeap) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨hregs, hsp, hcl, htr⟩
  have hsp_eq : s.sp = sp' := hregs.sp
  have hx29 : s.readReg64 .x29 = sp' + 512#64 := hregs.x29
  have hx19 : s.readReg64 .x19 = sret := hregs.x19
  have hx27 : s.readReg64 .x27 = 0x8000000000000002#64 := hregs.x27
  have hx24_beq : (x24 == 0#64) = false := beq_eq_false_iff_ne.mpr hx24_ne
  unfold wirePreKeyOf; simp only [sepExists_sepConj_left]
  refine Wire.SepWPp.exists_pre fun g => ?_
  unfold wirePreKeyAt
  have hent_wire :
      optVecU8At A.repAlloc g.kyberCt (sp' + 312#64) mErr.kyberCiphertext ∗
      optVecU8At A.repAlloc g.baseKey (sp' + 312#64 + 0x18#64) mErr.baseKey ∗
      optVecU8At A.repAlloc g.identityKey (sp' + 312#64 + 0x30#64) mErr.identityKey ∗
      optVecU8At A.repAlloc g.message (sp' + 312#64 + 0x48#64) mErr.message ∗
      optU32At (sp' + 312#64 + 0x60#64) mErr.registrationId ∗
      optU32At (sp' + 312#64 + 0x68#64) mErr.preKeyId ∗
      optU32At (sp' + 312#64 + 0x70#64) mErr.signedPreKeyId ∗
      optU32At (sp' + 312#64 + 0x78#64) mErr.kyberPreKeyId ⊢
      (∃∗ kyberCap, ∃∗ kyberPtr, ∃∗ kyberLen, ∃∗ kyberAct,
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
          deallocSlot A.repAlloc kyberCap kyberPtr kyberAct) ∗
      (∃∗ bkCap, ∃∗ bkPtr, ∃∗ bkLen, ∃∗ bkAct,
        vecHeader (sp' + 336#64) bkCap bkPtr bkLen ∗
          deallocSlot A.repAlloc bkCap bkPtr bkAct) ∗
      (∃∗ ikCap, ∃∗ ikPtr, ∃∗ ikLen, ∃∗ ikAct,
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
          deallocSlot A.repAlloc ikCap ikPtr ikAct) ∗
      (∃∗ msgCap, ∃∗ msgPtr, ∃∗ msgLen, ∃∗ msgAct,
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
          deallocSlot A.repAlloc msgCap msgPtr msgAct) ∗
      memRegion (sp' + 408#64) 8 ∗ memRegion (sp' + 416#64) 8 ∗
      memRegion (sp' + 424#64) 8 ∗ memRegion (sp' + 432#64) 8 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono
      (optVecU8At_entails_header_dealloc A.repAlloc g.kyberCt (sp' + 312#64) mErr.kyberCiphertext)
      (sepConj_mono
        (optVecU8At_entails_header_dealloc A.repAlloc g.baseKey (sp' + 336#64) mErr.baseKey)
        (sepConj_mono
          (optVecU8At_entails_header_dealloc A.repAlloc g.identityKey (sp' + 360#64) mErr.identityKey)
          (sepConj_mono
            (optVecU8At_entails_header_dealloc A.repAlloc g.message (sp' + 384#64) mErr.message)
            (sepConj_mono (optU32At_entails_memRegion8 (sp' + 408#64) mErr.registrationId)
              (sepConj_mono (optU32At_entails_memRegion8 (sp' + 416#64) mErr.preKeyId)
                (sepConj_mono (optU32At_entails_memRegion8 (sp' + 424#64) mErr.signedPreKeyId)
                  (optU32At_entails_memRegion8 (sp' + 432#64) mErr.kyberPreKeyId)))))))
  rw (occs := .pos [1]) [memRegion296_split104 sp']
  refine Wire.SepWPp.mono_pre (sepConj_mono hent_wire
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (memRegion248_split16 sret))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w0 =>
    Wire.SepWPp.exists_pre fun w104 =>
    Wire.SepWPp.exists_pre fun msgCap => Wire.SepWPp.exists_pre fun msgPtr =>
    Wire.SepWPp.exists_pre fun msgLen => Wire.SepWPp.exists_pre fun msgAct =>
    Wire.SepWPp.exists_pre fun ikCap => Wire.SepWPp.exists_pre fun ikPtr =>
    Wire.SepWPp.exists_pre fun ikLen => Wire.SepWPp.exists_pre fun ikAct =>
    Wire.SepWPp.exists_pre fun bkCap => Wire.SepWPp.exists_pre fun bkPtr =>
    Wire.SepWPp.exists_pre fun bkLen => Wire.SepWPp.exists_pre fun bkAct =>
    Wire.SepWPp.exists_pre fun kyberCap => Wire.SepWPp.exists_pre fun kyberPtr =>
    Wire.SepWPp.exists_pre fun kyberLen => Wire.SepWPp.exists_pre fun kyberAct => ?_
  have hvh :
      vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen =
        ((sp' + 312#64) ↦₆₄ kyberCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen) ∧
      vecHeader (sp' + 336#64) bkCap bkPtr bkLen =
        ((sp' + 336#64) ↦₆₄ bkCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗ ((sp' + 352#64) ↦₆₄ bkLen) ∧
      vecHeader (sp' + 360#64) ikCap ikPtr ikLen =
        ((sp' + 360#64) ↦₆₄ ikCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗ ((sp' + 376#64) ↦₆₄ ikLen) ∧
      vecHeader (sp' + 384#64) msgCap msgPtr msgLen =
        ((sp' + 384#64) ↦₆₄ msgCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' + 400#64) ↦₆₄ msgLen) := by
    simp only [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, and_self]
  rcases hvh with ⟨hvh1, hvh2, hvh3, hvh4⟩
  rw [hvh1, hvh2, hvh3, hvh4]; simp only [sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1148#64) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  set F_hdr := memRegion sp' 104 ∗ memRegion (sp' + 112#64) 184 ∗
    vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
    vecHeader (sp' + 336#64) bkCap bkPtr bkLen ∗
    vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
    vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
    memRegion (sp' + 408#64) 8 ∗ memRegion (sp' + 416#64) 8 ∗
    memRegion (sp' + 424#64) 8 ∗ memRegion (sp' + 432#64) 8 ∗
    memRegion (sret + 16#64) 232
  refine Wire.SepWPp.mono_pre (P' := (deallocSlot A.repAlloc kyberCap kyberPtr kyberAct ∗
      deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
      deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A.repAlloc msgCap msgPtr msgAct ∗
      decodeErrorAt A.repAlloc x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      A.pool lim st _ ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_hdr)
    (by dsimp only [F_hdr]; apply entails_of_eq; rw [hvh1, hvh2, hvh3, hvh4]; sep_ac_rfl) ?_
  refine frame_noPanic_pk
    (cleanup_47c_placed_wpX hdeallocX hDropErr kyberAct bkAct ikAct msgAct
      (PreKeyPostState.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx27, arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
    fun sf Pf ⟨hstf, evs, hf, hent⟩ => ⟨hstf, evs, hf, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hm296 := memRegion296_repack104 sp' ikPtr
  have hm128 := wirePreKeyHeaders_entails_memRegion128 sp' kyberCap kyberPtr kyberLen
    bkCap bkPtr bkLen ikCap ikPtr ikLen msgCap msgPtr msgLen
  have herr : (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
      memRegion (sret + 16#64) 232 ⊢
      pksmErrE A.repAlloc [] sret .invalidProtobufEncoding ∗ anyHeap := by
    have hc := errCells_invalidProtobufEncoding A.repAlloc [] sret
    exact Entails.trans hc
      (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
        (sepConj_mono_right (entails_anyHeap emp)))
  dsimp only [F_hdr]
  refine Entails.trans ?_
    (Entails.trans
      (sepConj_mono hm296 (sepConj_mono hm128
        (sepConj_mono herr
          (Entails.refl (A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100))))))
      (by apply entails_of_eq; sep_ac_rfl))
  apply entails_of_eq; sep_ac_rfl

theorem preKey_loopErr_460_placed_wpE [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (rustDeallocExternSpecWithStack M A lim extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (dropDecodeErrorSpecX A lim)))
    {x : RunCompose.PksmGhost} {s0 s : State} {vb : BitVec 8} {x24 : BitVec 64}
    {Qp : State → SepProp → Prop}
    (hst : PreKeyLoopExitStatePlaced s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = x24) (hx24_ne : x24 ≠ 0#64)
    (mErr : ProtoPreKeySignalMessage) :
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (wirePreKeyOf A.repAlloc (s0.sp - 608#64 + 312#64) mErr ∗
        decodeErrorAt A.repAlloc x24 ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        A.pool lim st s ∗ stackAt (s0.sp - 608#64) preKeyTryFromSubStack)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ⌜sf.trace = s0.trace⌝ ∗
            (pksmErrE A.repAlloc [] x.ret .invalidProtobufEncoding ∗ anyHeap) ∗
            (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
            stackAt s0.sp preKeyTryFromStack ∗ A.pool lim (M.stepEvents evs st) sf))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  set sp' := s0.sp - 608#64
  have hsub := stackAt_preKeyTryFromSubStack_skipField sp'
  set F_epi := memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - skipFieldStackX 100) ∗
    memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 440#64) 8 ∗
    memRegion (sp' + 448#64) 64 ∗ preKeyCalleeSavedAt sp' s0 ∗
    (x.ptr ↦ₛ x.bytes) ∗ lsLogOff
  refine Wire.SepWPp.mono_pre (P' :=
      (wirePreKeyOf A.repAlloc (sp' + 312#64) mErr ∗ decodeErrorAt A.repAlloc x24 ∗
        memRegion sp' 296 ∗ memRegion x.ret 248 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_epi)
    (by dsimp only [F_epi]; rw [hsub]; apply entails_of_eq; sep_ac_rfl) ?_
  refine Wire.SepWPp.bind
    (Qm := fun s1 P1 => PostEpilogueStatePlaced s0 sp' s1 ∧
      ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (P1 ⊢ (memRegion sp' 296 ∗ memRegion (sp' + 312#64) 128 ∗
          (pksmErrE A.repAlloc [] x.ret .invalidProtobufEncoding ∗ anyHeap) ∗
          A.pool lim (M.stepEvents evs st) s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_epi))
    (frame_noPanic_pk
      (preKey_loopErr_460_to_504_placed_wpE hdeallocX hDropErr hst hpc hrun hx24 hx24_ne mErr)
      fun s1 P1 ⟨hst1, evs, hf, hent1⟩ => ⟨hst1, evs, hf, sepConj_mono_left hent1⟩) ?_
  intro s1 P1 hpc1 hrun1 ⟨hst1, evs, hf, hent1⟩
  refine Wire.SepWPp.mono_pre hent1 ?_; clear hent1
  refine Wire.SepWPp.mono_pre (P' :=
      stackAt sp' preKeyTryFromSubStack ∗ memRegion sp' 296 ∗
        memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗
        preKeyCalleeSavedAt sp' s0 ∗
        (pksmErrE A.repAlloc [] x.ret .invalidProtobufEncoding ∗ anyHeap) ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) s1)
    (by dsimp only [F_epi]; rw [hsub, ← memRegion152_repack_16_128_8 sp'];
        apply entails_of_eq; sep_ac_rfl) ?_
  exact LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.sepWPp_mono_post
    (fun sf Pf ⟨hsp_f, hcs_f, hcl_f, htr_f, hent_f⟩ =>
      ⟨hsp_f, hcs_f, hcl_f, htr_f, evs, hf, hent_f⟩)
    (epilogue_504_err_placed_w_wpE (st := M.stepEvents evs st)
      [] .invalidProtobufEncoding hst1 hpc1 hrun1)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailWPlacedBudget
