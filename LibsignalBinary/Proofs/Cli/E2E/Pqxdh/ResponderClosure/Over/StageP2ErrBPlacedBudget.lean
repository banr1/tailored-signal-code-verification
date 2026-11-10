/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrBPlaced
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Defs
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Stage P2 Over-Path Error Unwind Arms 3 and 4

Threads `RustCliAllocBudget M` and `FreeOnlyEvs` across the `[LibsignalPlacement]` populated-record
Stage P2 error unwind Arms 3 (`+0x09c4 → x30`) and 4 (`+0x07bc → x30`) on block 518.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrBPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (dropSessionStructureLocal2Stack)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded PreKeyStoreSpec preKeyGetPollOutAt speErrAt withLsRoCl
)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf (
  IdentitySelfStoreSpec kpPollOutAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved decryptPrekeySavedRegsAt eq_of_sep_emp
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp (weaken_frame)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2_bind_sepWP_qp_frame_placed p2_bytes7At_to_memRegion7 p2_call_nopanic_rocl_steps_frame_placed
  p2_dropSs3Stack_eq p2_err56_to_preKeyRecordOut64 p2_fp80_to_memRegion9
  p2_keyPair64Unaligned_to_memRegion72 p2_kpPollErr_unpack p2_memRegion7_to_bytes7At
  p2_preKeyRecordOut64_to_cells6_a90 stageP1EntryPlaced stageP1ProgPlaced
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
  rustDeallocEvents
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  PreKeyStoreBudgetEnv futDropBudgetSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI PreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrBPlacedBudget (
  p2_err3a_ext_placed_wp p2_err3b_1568_hooks_placed_wp p2_err4a_fp_ext_placed_wp
  p2_err4b_1568_hooks_placed_wp
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

/-! ## Budget-Threaded Error Arm 3 (`+0x09c4 → x30`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded Error Arm 3 (`+0x09c4 → s0.readReg64 .x30`) from a direct `futDropBudgetSpec`
contract along `FreeOnlyEvs`. -/
theorem p2_over_arm3_err_drop_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {pkKit : PreKeyStoreSpec A.repAlloc 0#64}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hopk_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + pkKit.getFutDropOff)
      (withLsRoCl lsmpl futDropBudgetSpec))
    (s0 s : State) (sp coroPtr outPtr preKeyStorePtr opkFutPtr pkBuf skBuf ctxPtr
    v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (opkId : BitVec 32) (b_2c0 b_390 b_4f2 : BitVec 8) (e : pkKit.GetErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0x9c4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (preKeyGetPollOutAt pkKit (sp + 0xa90#64) (.error e) ∗ memRegion (sp + 0xac8#64) 8 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
       A.live opkFutPtr pkKit.getBoxSize 8 ∗
       pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
       ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
       ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ sf.trace = s.trace ∧
          (P_f ⊢
            cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 16 ∗
            ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
            ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
            ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
            ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
            ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ pkKit.getErr.w4 e) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((sp + 0xb8#64) ↦₆₄ pkKit.getErr.w2 e) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ pkKit.getErr.w3 e) ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt pkKit.getErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp := by
  dsimp only [preKeyGetPollOutAt]
  refine weaken_frame (p2_err56_to_preKeyRecordOut64 pkKit.getErr (sp + 0xa90#64) e)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ac8 => ?_
  have hstep1 := p2_err3a_ext_placed_wp ext s coroPtr ctxPtr opkFutPtr
    (0#64 + pkKit.getFutVtOff) (0#64 + pkKit.getFutDropOff)
    (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
    (pkKit.getErr.w3 e) (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) u_ac8
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0
    (pkKit.getFutDrop_ne_zero rfl) hpc hrun hsp_align hx19 hx21 hx23 hx26 hx27
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1, hvm1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine weaken_frame
    (p2_preKeyRecordOut64_to_cells6_a90 sp 0xffffffffffffffff#64
      (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
      (pkKit.getErr.w3 e) (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) u_ac8)
    (by sep_focus) ?_
  refine p2_call_nopanic_rocl_steps_frame_placed (spec := futDropBudgetSpec) (x := ()) (T := emp)
    hCode1 hopk_drop hpc1 hrun1 hsp1_al hx30_1
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
    hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine weaken_frame
    (pkKit.getBoxAt_memRegion opkFutPtr preKeyStorePtr opkId 1#8) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp)) (by sep_focus) ?_
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  have hstep3 := p2_err3b_1568_hooks_placed_wp (st := st) ext hH s2 coroPtr opkFutPtr
    (0#64 + pkKit.getFutVtOff) pkBuf skBuf outPtr
    (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
    (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) pkKit.getBoxSize
    pkKit.getBoxSize_ne_zero pkKit.getBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1)
    (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1) (hx26_cs2.trans hx26_1)
    (hx27_cs2.trans hx27_1) hx28_2
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame_state_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  refine weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp).symm) (by sep_focus) ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2, _hlive3⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  change s3.pc = stageP1EntryPlaced + 0x1648#64 at hpc3
  have hfunnel := stageP2_over_err_funnel_hooks_placed_ok
    (st := M.stepEvents (rustDeallocEvents pkKit.getBoxSize 8 ++ rustDeallocEvents 1568 1 ++
      rustDeallocEvents 3168 1) st)
    (Qp := fun _ _ => False) hH hDropSs3 s0 s3 sp coroPtr outPtr
    (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
    (pkKit.getErr.w3 e) (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) (pkKit.getErr.w1 e) outPtr
    b_2c0 b_390 b_4f2 g recG recSt
    (pkKit.getErr.w0_ne_pending e) (pkKit.getErr.w0_ne_ok e) rfl
    hCode3 hsp3 hsp_lt hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  refine p2_bind_free_tr_evs_frame hfunnel (by sep_focus)
    fun evs_f sf _ hpcf hrunf hfree_f htrf ⟨hspf, hcsf, hvregsf, hCodef, _⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  have hfree_all : FreeOnlyEvs
      ((rustDeallocEvents pkKit.getBoxSize 8 ++ rustDeallocEvents 1568 1 ++
        rustDeallocEvents 3168 1) ++ evs_f) :=
    (((FreeOnlyEvs.singleton 8 pkKit.getBoxSize).append (FreeOnlyEvs.singleton 1 1568)).append
      (FreeOnlyEvs.singleton 1 3168)).append hfree_f
  refine ⟨(rustDeallocEvents pkKit.getBoxSize 8 ++ rustDeallocEvents 1568 1 ++
      rustDeallocEvents 3168 1) ++ evs_f, hfree_all,
    by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hCodef,
    M.liveBytes_stepEvents_freeOnly_le hfree_all st⟩
  dsimp only [speErrAt]
  rw [M.stepEvents_append]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem p2_over_arm3_err_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {pkKit : PreKeyStoreSpec A.repAlloc 0#64}
    {pkEnv : PreKeyStoreBudgetEnv pkKit}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (s0 s : State) (sp coroPtr outPtr preKeyStorePtr opkFutPtr pkBuf skBuf ctxPtr
    v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (opkId : BitVec 32) (b_2c0 b_390 b_4f2 : BitVec 8) (e : pkKit.GetErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0x9c4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (preKeyGetPollOutAt pkKit (sp + 0xa90#64) (.error e) ∗ memRegion (sp + 0xac8#64) 8 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
       A.live opkFutPtr pkKit.getBoxSize 8 ∗
       pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
       ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
       ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ sf.trace = s.trace ∧
          (P_f ⊢
            cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 16 ∗
            ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
            ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
            ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
            ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
            ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ pkKit.getErr.w4 e) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((sp + 0xb8#64) ↦₆₄ pkKit.getErr.w2 e) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ pkKit.getErr.w3 e) ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt pkKit.getErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp :=
  p2_over_arm3_err_drop_hooks_placed_ok hH hDropSs3 (hpkOk.getFutDrop (by decide)) s0 s
    sp coroPtr outPtr preKeyStorePtr opkFutPtr pkBuf skBuf ctxPtr
    v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 opkId b_2c0 b_390 b_4f2 e
    g recG recSt hCode hsp_eq hsp_lt hpc hrun hsp_align hx19 hx21 hx23 hx25 hx26 hx27 hx28 hvregs

abbrev p2_over_arm3_err_4k_placed_ok [LibsignalPlacement] :=
  @p2_over_arm3_err_hooks_placed_ok
abbrev p2_over_arm3_err_ext_placed_ok [LibsignalPlacement] :=
  @p2_over_arm3_err_hooks_placed_ok

/-! ## Budget-Threaded Error Arm 4 (`+0x07bc → x30`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded Error Arm 4 (`+0x07bc → s0.readReg64 .x30`) from a direct `futDropBudgetSpec`
contract along `FreeOnlyEvs`. -/
theorem p2_over_arm4_err_drop_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {skit : IdentitySelfStoreSpec ikit}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkp_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + skit.kpFutDropOff)
      (withLsRoCl lsmpl futDropBudgetSpec))
    (s0 s : State) (sp coroPtr msgPtr ctxPtr outPtr
    idStorePtr idKpFutPtr pkBuf skBuf fp
    v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 : BitVec 64)
    (opkId : BitVec 32) (b_2c0 b_390 b_4f2 b_fp78 : BitVec 8) (e : skit.KpErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0x7bc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx24 : s.readReg64 .x24 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64) (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64)
    (hx27 : s.readReg64 .x27 = ctxPtr) (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = fp)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (kpPollOutAt skit (sp + 0x3e0#64) (.error e) ∗ memRegion (sp + 0x3c8#64) 7 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_fp80) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_fp78) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ∗
       A.live idKpFutPtr skit.kpBoxSize 8 ∗
       skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗
       ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
       ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
       ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗ prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ sf.trace = s.trace ∧
          (P_f ⊢
            memRegion (sp + 0x3e0#64) 72 ∗ memRegion (sp + 0x3c8#64) 7 ∗
            memRegion (fp + 0xffffffffffffff80#64) 9 ∗
            ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
            ((coroPtr + 0x500#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ∗
            ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
            ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
            ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
            ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ skit.kpErr.w4 e) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((sp + 0xb8#64) ↦₆₄ skit.kpErr.w2 e) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ skit.kpErr.w3 e) ∗
            cells (sp + 0xa90#64) 6 ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
            cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗ ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
            ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt skit.kpErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp := by
  refine weaken_frame (p2_kpPollErr_unpack skit (sp + 0x3e0#64) e) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
    SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
    SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
    SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun w6 =>
    SepWPp.exists_elim fun b63 => ?_
  refine weaken_frame (p2_memRegion7_to_bytes7At (sp + 0x3c8#64)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun s0_b => SepWPp.exists_elim fun s1_b =>
    SepWPp.exists_elim fun s2_b => SepWPp.exists_elim fun s3_b =>
    SepWPp.exists_elim fun s4_b => SepWPp.exists_elim fun s5_b =>
    SepWPp.exists_elim fun s6_b => ?_
  have hx24_s : s.readReg64 .x24 = s.sp + 0x370#64 := by rw [hx24, hsp_eq]
  have hstep1 := p2_err4a_fp_ext_placed_wp ext s coroPtr msgPtr ctxPtr idKpFutPtr
    (0#64 + skit.kpFutVtOff) (0#64 + skit.kpFutDropOff) fp
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0
    u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 opkId
    b0 b1 b2 b3 b4 b5 b6 b63 s0_b s1_b s2_b s3_b s4_b s5_b s6_b b_fp78
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w3 e) (skit.kpErr.w4 e) (skit.kpErr.w5 e) w6
    (skit.kpFutDrop_ne_zero rfl) hpc hrun hsp_align hx19 hx21 hx23 hx24_s hx26 hx27 hx29
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, _, hx27_1, hx28_1, _, hx30_1, hvregs1, hvm1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  have h72 := p2_keyPair64Unaligned_to_memRegion72 (sp + 0x3e0#64) b0 b1 b2 b3 b4 b5 b6 b63
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w3 e) (skit.kpErr.w4 e) (skit.kpErr.w5 e) w6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h72
  refine weaken_frame h72 (by sep_focus) ?_
  refine weaken_frame (p2_bytes7At_to_memRegion7 (sp + 0x3c8#64) b0 b1 b2 b3 b4 b5 b6)
    (by sep_focus) ?_
  refine weaken_frame (p2_fp80_to_memRegion9 fp w6 b63) (by sep_focus) ?_
  refine p2_call_nopanic_rocl_steps_frame_placed (spec := futDropBudgetSpec) (x := ()) (T := emp)
    hCode1 hkp_drop hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [futDropBudgetSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [futDropBudgetSpec]
  refine SepWPp.pure_elim fun ⟨htr2_1, hvm2_1⟩ => ?_
  have hvm2 : VmPreserved s s2 := hvm1.trans hvm2_1
  refine SepWPp.transport_budgetPool hvm2 (by sep_focus) ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, _, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine weaken_frame
    (skit.kpBoxAt_memRegion idKpFutPtr idStorePtr 1#8) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp)) (by sep_focus) ?_
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  have hstep3 := p2_err4b_1568_hooks_placed_wp (st := st) ext hH s2 coroPtr idKpFutPtr
    (0#64 + skit.kpFutVtOff) pkBuf skBuf outPtr
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w4 e) (skit.kpErr.w5 e) skit.kpBoxSize
    skit.kpBoxSize_ne_zero skit.kpBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx20_cs2.trans hx20_1) (hx21_cs2.trans hx21_1)
    (hx22_cs2.trans hx22_1) (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1)
    (hx27_cs2.trans hx27_1) hx28_2
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame_state_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  refine weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp).symm) (by sep_focus) ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2, _hlive3⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  change s3.pc = stageP1EntryPlaced + 0x1648#64 at hpc3
  have hfunnel := stageP2_over_err_funnel_hooks_placed_ok
    (st := M.stepEvents (rustDeallocEvents skit.kpBoxSize 8 ++ rustDeallocEvents 1568 1 ++
      rustDeallocEvents 3168 1) st)
    (Qp := fun _ _ => False) hH hDropSs3 s0 s3 sp coroPtr outPtr
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w3 e) (skit.kpErr.w4 e) (skit.kpErr.w5 e) (skit.kpErr.w1 e) outPtr
    b_2c0 b_390 b_4f2 g recG recSt
    (skit.kpErr.w0_ne_pending e) (skit.kpErr.w0_ne_ok e) rfl
    hCode3 hsp3 hsp_lt hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  refine p2_bind_free_tr_evs_frame hfunnel (by sep_focus)
    fun evs_f sf _ hpcf hrunf hfree_f htrf ⟨hspf, hcsf, hvregsf, hCodef, _⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  have hfree_all : FreeOnlyEvs
      ((rustDeallocEvents skit.kpBoxSize 8 ++ rustDeallocEvents 1568 1 ++
        rustDeallocEvents 3168 1) ++ evs_f) :=
    (((FreeOnlyEvs.singleton 8 skit.kpBoxSize).append (FreeOnlyEvs.singleton 1 1568)).append
      (FreeOnlyEvs.singleton 1 3168)).append hfree_f
  refine ⟨(rustDeallocEvents skit.kpBoxSize 8 ++ rustDeallocEvents 1568 1 ++
      rustDeallocEvents 3168 1) ++ evs_f, hfree_all,
    by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hCodef,
    M.liveBytes_stepEvents_freeOnly_le hfree_all st⟩
  dsimp only [speErrAt]
  rw [M.stepEvents_append]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem p2_over_arm4_err_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
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
    (s0 s : State) (sp coroPtr msgPtr ctxPtr outPtr
    idStorePtr idKpFutPtr pkBuf skBuf fp
    v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 : BitVec 64)
    (opkId : BitVec 32) (b_2c0 b_390 b_4f2 b_fp78 : BitVec 8) (e : skit.KpErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0x7bc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx24 : s.readReg64 .x24 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64) (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64)
    (hx27 : s.readReg64 .x27 = ctxPtr) (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = fp)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (kpPollOutAt skit (sp + 0x3e0#64) (.error e) ∗ memRegion (sp + 0x3c8#64) 7 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_fp80) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_fp78) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ∗
       A.live idKpFutPtr skit.kpBoxSize 8 ∗
       skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗
       ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
       ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
       ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗ prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ sf.trace = s.trace ∧
          (P_f ⊢
            memRegion (sp + 0x3e0#64) 72 ∗ memRegion (sp + 0x3c8#64) 7 ∗
            memRegion (fp + 0xffffffffffffff80#64) 9 ∗
            ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
            ((coroPtr + 0x500#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ∗
            ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
            ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
            ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
            ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ skit.kpErr.w4 e) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((sp + 0xb8#64) ↦₆₄ skit.kpErr.w2 e) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ skit.kpErr.w3 e) ∗
            cells (sp + 0xa90#64) 6 ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
            cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗ ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
            ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt skit.kpErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp :=
  p2_over_arm4_err_drop_hooks_placed_ok hH hDropSs3 (hskitOk.kpFutDrop (by decide)) s0 s
    sp coroPtr msgPtr ctxPtr outPtr idStorePtr idKpFutPtr pkBuf skBuf fp
    v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 opkId b_2c0 b_390 b_4f2 b_fp78 e
    g recG recSt hCode hsp_eq hsp_lt hpc hrun hsp_align hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx28
    hx29 hvregs

abbrev p2_over_arm4_err_4k_placed_ok [LibsignalPlacement] :=
  @p2_over_arm4_err_hooks_placed_ok
abbrev p2_over_arm4_err_ext_placed_ok [LibsignalPlacement] :=
  @p2_over_arm4_err_hooks_placed_ok

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrBPlacedBudget
