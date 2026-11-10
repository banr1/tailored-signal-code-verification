/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case1
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudgetFd
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded Relocatable `OTR::from_session_state` Case 1 (`st.senderChain = none`)

Proves `FdsGe3Closed` preservation for the `[LibsignalPlacement]` `RustCliAllocBudget` Case 1
branch of `<OutgoingTripleRatchet>::from_session_state`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case1BudgetFd

open Arm64 ProofLib
open CryptoGames.LibsignalSession (OutgoingTripleRatchet SignalProtocolError)
open CryptoVerification (LibsignalPlacement blkPC_19 blkPl_19 lsρ)
open CryptoVerification.LibsignalTripleRatchet (OtrFromGhost)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet (
  ent_of_eq issStr_missingSenderChain_len missingSenderChainSym otrFrom_model_none
  otrResultAt_iss_intro ret200_split_br1 rodata_missingSenderChain_placed_intro
  sessionStateAt_eq_from_none sessionStateAt_from_none_fold sessionStateAt_sender_none
  stackAt_prologue stackAt_prologue_fold zeroExtend32_setWidth16 zeroExtend32_setWidth8
  zeroExtend64_setWidth16 zeroExtend64_setWidth32 zeroExtend64_setWidth8
)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.FromSessionStateFacts (fold_entails)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget (otrFromRawPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudgetFd (
  otrFromCasePlacedSpecFd otrFromRawPlacedSpecFd
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudgetFd.FromSessionStateFacts (
  finish_otrFrom_placed_fd
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_setWidth32 zeroExtend64_setWidth16 zeroExtend32_setWidth16
  zeroExtend64_setWidth8 zeroExtend32_setWidth8

/-- Relocatable `[LibsignalPlacement]` Case 1 (`st.senderChain = none`, `missingSenderChain`)
under `RustCliAllocBudget M` preserving `FdsGe3Closed`. -/
theorem otrFrom_case1_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromCasePlacedSpecFd M A lim (fun x => x.st.senderChain = none)) := by
  dsimp only [otrFromCasePlacedSpecFd, otrFromRawPlacedSpecFd, withFdsGe3Closed, otrFromRawPlacedSpec]
  wp_init a s0
  rcases a with ⟨⟨ss, G, st, ret⟩, stB⟩
  dsimp only at *
  have h_1 : st.senderChain = none := by assumption
  have hfds_0 : FdsGe3Closed s0.fs := by assumption
  have h_3 : CryptoVerification.LibsignalRoLoaded CryptoVerification.lsmpl s0.mem := by assumption
  refine CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.SepWP.add_rodata
    (fun hm => rodata_missingSenderChain_placed_intro h_3 hm) ?_
  refine SepWP.fold (sessionStateAt_sender_none A.repAlloc ss G st h_1) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hGs => ?_
  conv =>
    arg 4
    rw [sessionStateAt_eq_from_none A.repAlloc ss G st h_1 hGs,
        stackAt_prologue s0.sp,
        ret200_split_br1 ret]
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro r11
  apply SepWP.exists_elim; intro r10
  apply SepWP.exists_elim; intro r9
  apply SepWP.exists_elim; intro r8
  apply SepWP.exists_elim; intro r7
  apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5
  apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  have hmod := otrFrom_model_none ⟨ss, G, st, ret⟩ h_1
  have hmod1 := congrArg Prod.fst hmod
  have hmod2 := congrArg Prod.snd hmod
  have hnopanic : (.error (.invalidSessionStructure .missingSenderChain) :
      Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8)))) ≠ .error .panic := by
    decide
  have hagree : G.AgreeExceptPq G := rfl
  refine finish_otrFrom_placed_fd ⟨ss, G, st, ret⟩ stB G [] FreeOnlyEvs.nil _ _
    hmod1 hmod2 hnopanic hagree (by dsimp only [AllocCostModel.stepEvents]; wp_done) ?_
  dsimp only [AllocCostModel.stepEvents]
  refine fold_entails (sessionStateAt_from_none_fold A.repAlloc ss G st h_1 hGs) (by sep_focus) ?_
  refine fold_entails
    (otrResultAt_iss_intro A.repAlloc ret (lsρ missingSenderChainSym) 20#64 G.pq
      .missingSenderChain issStr_missingSenderChain_len.symm)
    (by sep_focus) ?_
  refine fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  exact ent_of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case1BudgetFd
