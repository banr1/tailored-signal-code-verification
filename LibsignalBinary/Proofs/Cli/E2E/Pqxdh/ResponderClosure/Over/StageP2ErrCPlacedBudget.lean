/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsCPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrCPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Defs
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Stage P2 Over-Path Error Unwind Arms 5 and 6

Threads `RustCliAllocBudget M` and `FreeOnlyEvs` across the `[LibsignalPlacement]` populated-record
Stage P2 error unwind Arms 5 (`+0x125c → x30`) and 6 (`+0x09f4 → x30`) on block 518.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrCPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost dropSessionStructureLocal2Stack
)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded speErrAt speWordsAt withLsRoCl
)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf (
  IdentitySelfStoreSpec regIdPollOutAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved decryptPrekeySavedRegsAt eq_of_sep_emp
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp (weaken_frame)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2_bind_sepWP_qp_frame_placed p2_call_nopanic_lscl_steps_frame_placed
  p2_call_nopanic_rocl_steps_frame_placed p2_dropSs3Stack_eq
  p2_zeroExtend32_extractLsb_lo stageP1EntryPlaced stageP1ProgPlaced
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
  rustDeallocEvents
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (IdentitySelfStoreKitPlacedOkI)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrCPlacedBudget (
  p2_err5_1568_hooks_placed_wp p2_err6a_ext_placed_wp p2_err6b_a_hooks_placed_wp
  p2_err6b_b_1568_hooks_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget (
  p2_bind_sepWP_qp_frame_state_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrAPlacedBudget (
  stageP2_over_err_funnel_hooks_placed_ok
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  decryptPrekeySavedRegsAt sessionStateAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

private theorem p2_bind_free_tr_evs_frame {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_stage F : SepProp} {P_stage_post : List AllocEvent → State → SepProp}
    {Q_evs : List AllocEvent → State → Prop} {Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m =>
        ∃ evs, FreeOnlyEvs evs ∧ sm.trace = s.trace ∧ (P_m ⊢ P_stage_post evs sm) ∧ Q_evs evs sm)
      (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ (evs : List AllocEvent) (sm : State), Steps prog s sm →
      sm.pc = mid → sm.status = .Running → FreeOnlyEvs evs → sm.trace = s.trace → Q_evs evs sm →
      SepWPp prog ret sm (P_stage_post evs sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps,
      ⟨hpcm, hrunm, P_m, hmm, evs, hfree, htr, hent, hregs⟩ | ⟨_, _, _, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post evs sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext evs sm hsteps hpcm hrunm hfree htr hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hpanm
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Budget-Threaded Error Arm 5 (`+0x125c → x30`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded Error Arm 5 (`+0x125c → s0.readReg64 .x30`) along `FreeOnlyEvs`. -/
theorem p2_over_arm5_err_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (s0 s : State) (sp coroPtr outPtr pkBuf skBuf
    w0 w1 w2 w3 w4 w5 u_88 u_a8 u_b8 u_d0 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hw0_ne_pending : w0 ≠ 0xfffffffffffffffd#64) (hw0_ne_ok : w0 ≠ 0xfffffffffffffffe#64)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0x125c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       speWordsAt (sp + 0x3e8#64) w0 w1 w2 w3 w4 w5 ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ sf.trace = s.trace ∧
          (P_f ⊢
            ((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            speWordsAt (sp + 0x3e8#64) w0 w1 w2 w3 w4 w5 ∗
            ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
            ((sp + 0x88#64) ↦₆₄ w0) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ w4) ∗
            ((sp + 0xb8#64) ↦₆₄ w2) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ w3) ∗
            cells (sp + 0xa90#64) 6 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speWordsAt outPtr w0 w1 w2 w3 w4 w5 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp := by
  refine weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp)) (by sep_focus) ?_
  have hx28_s : s.readReg64 .x28 = s.sp + 0xa90#64 := by rw [hx28, hsp_eq]
  have hstep1 := p2_err5_1568_hooks_placed_wp (st := st) ext hH s coroPtr pkBuf skBuf outPtr
    w0 w1 w2 w3 w4 w5 u_88 u_a8 u_b8 u_d0
    hpc hrun hsp_align hx19 hx28_s
  rw [hsp_eq] at hstep1
  refine p2_bind_sepWP_qp_frame_state_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  refine weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp).symm) (by sep_focus) ?_
  rcases hregs1 with ⟨hsp1, htr1, hx10_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs1, _hlive1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1, ← hsp_eq]; exact hsp_align
  have hx25_1' : s1.readReg64 .x25 = sp + 0x210#64 := hx25_1.trans hx25
  have hvregs1_0 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hvregs1.trans hvregs
  change s1.pc = stageP1EntryPlaced + 0x1648#64 at hpc1
  have hfunnel := stageP2_over_err_funnel_hooks_placed_ok
    (st := M.stepEvents (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) st)
    (Qp := fun _ _ => False) hH hDropSs3 s0 s1 sp coroPtr outPtr
    w0 w1 w2 w3 w4 w5 w1 outPtr
    b_2c0 b_390 b_4f2 g recG recSt hw0_ne_pending hw0_ne_ok rfl
    hCode1 hsp1 hsp_lt hpc1 hrun1 hsp1_align
    hx10_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1' hx26_1 hx27_1 hx28_1 hvregs1_0
  refine p2_bind_free_tr_evs_frame hfunnel (by sep_focus)
    fun evs_f sf _ hpcf hrunf hfree_f htrf ⟨hspf, hcsf, hvregsf, hCodef, _⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  have hfree_all : FreeOnlyEvs
      ((rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) ++ evs_f) :=
    ((FreeOnlyEvs.singleton 1 1568).append (FreeOnlyEvs.singleton 1 3168)).append hfree_f
  refine ⟨(rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) ++ evs_f, hfree_all,
    htrf.trans htr1, ?_, hspf, hcsf, hvregsf, hCodef,
    M.liveBytes_stepEvents_freeOnly_le hfree_all st⟩
  rw [M.stepEvents_append]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev p2_over_arm5_err_4k_placed_ok [LibsignalPlacement] :=
  @p2_over_arm5_err_hooks_placed_ok
abbrev p2_over_arm5_err_ext_placed_ok [LibsignalPlacement] :=
  @p2_over_arm5_err_hooks_placed_ok

/-! ## Budget-Threaded Error Arm 6 (`+0x09f4 → x30`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded Error Arm 6 (`+0x09f4 → s0.readReg64 .x30`) from a direct `futDropBudgetSpec`
contract along `FreeOnlyEvs`. -/
theorem p2_over_arm6_err_drop_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {skit : IdentitySelfStoreSpec ikit}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hregId_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + skit.regIdFutDropOff)
      (withLsRoCl lsmpl futDropBudgetSpec))
    (G : SessionGhost) (bobSt : SessionState (List (BitVec 8)))
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (s0 s : State) (sp coroPtr outPtr
    idStorePtr regIdFutPtr pkBuf skBuf
    v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8) (e : skit.RegIdErr)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0x9f4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (regIdPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
       ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
       A.live regIdFutPtr skit.regIdBoxSize 8 ∗
       skit.regIdBoxAt regIdFutPtr idStorePtr 1#8 ∗
       ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
       ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
       ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0x4f8#64) G bobSt ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ sf.trace = s.trace ∧
          (P_f ⊢
            speWordsAt (sp + 0x3e0#64) (skit.regIdErr.w0 e) (skit.regIdErr.w1 e)
              (skit.regIdErr.w2 e) (skit.regIdErr.w3 e) (skit.regIdErr.w4 e)
              (skit.regIdErr.w5 e) ∗
            ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
            ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
            ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
            ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
            ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            memRegion (coroPtr + 0x4f8#64) 344 ∗
            ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
            ((sp + 0x88#64) ↦₆₄ skit.regIdErr.w0 e) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ skit.regIdErr.w4 e) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((sp + 0xb8#64) ↦₆₄ skit.regIdErr.w2 e) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ skit.regIdErr.w3 e) ∗
            cells (sp + 0xa90#64) 6 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt skit.regIdErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp := by
  dsimp only [regIdPollOutAt, speErrAt]
  have hstep1 := p2_err6a_ext_placed_wp ext s coroPtr regIdFutPtr
    (0#64 + skit.regIdFutVtOff) (0#64 + skit.regIdFutDropOff)
    (skit.regIdErr.w0 e) (skit.regIdErr.w1 e) (skit.regIdErr.w2 e)
    (skit.regIdErr.w3 e) (skit.regIdErr.w4 e) (skit.regIdErr.w5 e)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0
    u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0
    (skit.regIdErr.w0_ne_pending e) (skit.regIdFutDrop_ne_zero rfl)
    hpc hrun hsp_align hx19 hx21 hx23 hx26
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, _, hx27_1, hx28_1, _, hx30_1, hvregs1, hvm1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine p2_call_nopanic_rocl_steps_frame_placed (spec := futDropBudgetSpec) (x := ()) (T := emp)
    hCode1 hregId_drop hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [futDropBudgetSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [futDropBudgetSpec]
  refine SepWPp.pure_elim fun ⟨htr2_1, hvm2_1⟩ => ?_
  have hvm2 : VmPreserved s s2 := hvm1.trans hvm2_1
  refine SepWPp.transport_budgetPool hvm2 (by sep_focus) ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, _, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine weaken_frame
    (skit.regIdBoxAt_memRegion regIdFutPtr idStorePtr 1#8) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp)) (by sep_focus) ?_
  have hstep3 := p2_err6b_a_hooks_placed_wp (st := st) ext hH s2 coroPtr regIdFutPtr
    (0#64 + skit.regIdFutVtOff) (skit.regIdErr.w0 e) skit.regIdBoxSize
    (skit.regIdErr.w0_ne_ok e) skit.regIdBoxSize_ne_zero skit.regIdBoxSize_lt
    hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx24_cs2.trans hx24_1)
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame_state_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx0_3, hx19_3, hx22_3, hx23_3, hx25_3, _,
    hx27_3, hx28_3, _, hx30_3, hvregs3_2, _hlive3⟩
  have hsp3_al : s3.spAligned = true := by simp only [State.spAligned, hsp3, ← hsp_eq]; exact hsp_align
  refine weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp).symm) (by sep_focus) ?_
  refine p2_call_nopanic_lscl_steps_frame_placed
    (spec := dropSessionStructureLocal2Spec M A lim)
    (x := ((⟨coroPtr + 0x4f8#64, G, bobSt⟩ : DropSessionStructureGhost),
      M.stepEvents (rustDeallocEvents skit.regIdBoxSize 8) st))
    (T := sessionStateAt A.repAlloc (coroPtr + 0x4f8#64) G bobSt ∗
      A.pool lim (M.stepEvents (rustDeallocEvents skit.regIdBoxSize 8) st) s3 ∗
      stackAt s3.sp dropSessionStructureLocal2Stack)
    hCode3 hDropSs3
    hpc3 hrun3 hsp3_al hx30_3
    rfl
    (And.intro hx0_3 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s3.readReg64 .lr) by
      simp (config := { decide := true }) [show s3.readReg64 .lr = _ from hx30_3, wp_norm]))
    (by rw [hsp3]; sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_ss => SepWPp.pure_elim fun ⟨htr4_3, hevs_ss⟩ => ?_
  have hsp4 : s4.sp = sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4, ← hsp_eq]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, _, _, hx22_cs4, hx23_cs4, _,
    hx25_cs4, _, hx27_cs4, hx28_cs4, _, hvregs4_3⟩
  refine weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp)) (by sep_focus) ?_
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx22_4 : s4.readReg64 .x22 = (skit.regIdErr.w1 e) >>> 32 := by
    rw [hx22_cs4, hx22_3, hx22_cs2, hx22_1]
  have hx23_4 : s4.readReg64 .x23 = ((skit.regIdErr.w1 e).extractLsb' 0 32).zeroExtend 64 := by
    rw [hx23_cs4, hx23_3, hx23_cs2, hx23_1]
  have hx27_4 : s4.readReg64 .x27 = skit.regIdErr.w5 e := by
    rw [hx27_cs4, hx27_3, hx27_cs2, hx27_1]
  have hx28_4 : s4.readReg64 .x28 = s4.sp + 0xa90#64 := by
    rw [hx28_cs4, hx28_3, hx28_cs2, hx28_1, hx28, hsp4]
  have hstep5 := p2_err6b_b_1568_hooks_placed_wp
    (st := M.stepEvents evs_ss (M.stepEvents (rustDeallocEvents skit.regIdBoxSize 8) st))
    ext hH s4 coroPtr pkBuf skBuf outPtr
    (skit.regIdErr.w0 e) (skit.regIdErr.w1 e) (skit.regIdErr.w2 e)
    (skit.regIdErr.w4 e) (skit.regIdErr.w5 e)
    hpc4 hrun4 hsp4_align hx19_4 hx22_4 hx23_4 hx27_4 hx28_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_qp_frame_state_placed hCode4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hCode5 hregs5 => ?_
  refine weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp).symm) (by sep_focus) ?_
  rcases hregs5 with ⟨hsp5, htr5_4, hx10_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
    hx25_5, hx26_5, hx27_5, hx28_5, _, hvregs5_4, _hlive5⟩
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5, ← hsp_eq]; exact hsp_align
  have hx25_5' : s5.readReg64 .x25 = sp + 0x210#64 := by
    rw [hx25_5, hx25_cs4, hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs5 : calleeSavedVRegs s5 = calleeSavedVRegs s0 := by
    rw [hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  change s5.pc = stageP1EntryPlaced + 0x1648#64 at hpc5
  have hfunnel := stageP2_over_err_funnel_hooks_placed_ok
    (st := M.stepEvents (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1)
      (M.stepEvents evs_ss (M.stepEvents (rustDeallocEvents skit.regIdBoxSize 8) st)))
    (Qp := fun _ _ => False) hH hDropSs3 s0 s5 sp coroPtr outPtr
    (skit.regIdErr.w0 e) (skit.regIdErr.w1 e) (skit.regIdErr.w2 e)
    (skit.regIdErr.w3 e) (skit.regIdErr.w4 e) (skit.regIdErr.w5 e)
    (((skit.regIdErr.w1 e).extractLsb' 0 32).zeroExtend 64) outPtr
    b_2c0 b_390 b_4f2 g recG recSt
    (skit.regIdErr.w0_ne_pending e) (skit.regIdErr.w0_ne_ok e)
    (p2_zeroExtend32_extractLsb_lo (skit.regIdErr.w1 e))
    hCode5 hsp5 hsp_lt hpc5 hrun5 hsp5_align
    hx10_5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5' hx26_5 hx27_5 hx28_5 hvregs5
  refine p2_bind_free_tr_evs_frame hfunnel (by sep_focus)
    fun evs_f sf _ hpcf hrunf hfree_f htrf ⟨hspf, hcsf, hvregsf, hCodef, _⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  have hfree_all : FreeOnlyEvs
      (((rustDeallocEvents skit.regIdBoxSize 8 ++ evs_ss) ++
        (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1)) ++ evs_f) :=
    (((FreeOnlyEvs.singleton 8 skit.regIdBoxSize).append hevs_ss).append
      ((FreeOnlyEvs.singleton 1 1568).append (FreeOnlyEvs.singleton 1 3168))).append hfree_f
  refine ⟨((rustDeallocEvents skit.regIdBoxSize 8 ++ evs_ss) ++
      (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1)) ++ evs_f, hfree_all,
    by rw [htrf, htr5_4, htr4_3, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hCodef,
    M.liveBytes_stepEvents_freeOnly_le hfree_all st⟩
  simp only [M.stepEvents_append]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem p2_over_arm6_err_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {skit : IdentitySelfStoreSpec ikit}
    {senv : IdentitySelfStoreBudgetEnv skit}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (G : SessionGhost) (bobSt : SessionState (List (BitVec 8)))
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (s0 s : State) (sp coroPtr outPtr
    idStorePtr regIdFutPtr pkBuf skBuf
    v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8) (e : skit.RegIdErr)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0x9f4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (regIdPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
       ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
       A.live regIdFutPtr skit.regIdBoxSize 8 ∗
       skit.regIdBoxAt regIdFutPtr idStorePtr 1#8 ∗
       ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
       ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
       ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0x4f8#64) G bobSt ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ sf.trace = s.trace ∧
          (P_f ⊢
            speWordsAt (sp + 0x3e0#64) (skit.regIdErr.w0 e) (skit.regIdErr.w1 e)
              (skit.regIdErr.w2 e) (skit.regIdErr.w3 e) (skit.regIdErr.w4 e)
              (skit.regIdErr.w5 e) ∗
            ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
            ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
            ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
            ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
            ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            memRegion (coroPtr + 0x4f8#64) 344 ∗
            ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
            ((sp + 0x88#64) ↦₆₄ skit.regIdErr.w0 e) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ skit.regIdErr.w4 e) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((sp + 0xb8#64) ↦₆₄ skit.regIdErr.w2 e) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ skit.regIdErr.w3 e) ∗
            cells (sp + 0xa90#64) 6 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt skit.regIdErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp :=
  p2_over_arm6_err_drop_hooks_placed_ok hH hDropSs3 (hskitOk.regIdFutDrop (by decide))
    G bobSt g recG recSt s0 s sp coroPtr outPtr
    idStorePtr regIdFutPtr pkBuf skBuf
    v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 b_2c0 b_390 b_4f2 e
    hCode hsp_eq hsp_lt hpc hrun hsp_align hx19 hx21 hx23 hx25 hx26 hx28 hvregs

abbrev p2_over_arm6_err_4k_placed_ok [LibsignalPlacement] :=
  @p2_over_arm6_err_hooks_placed_ok
abbrev p2_over_arm6_err_ext_placed_ok [LibsignalPlacement] :=
  @p2_over_arm6_err_hooks_placed_ok

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrCPlacedBudget
