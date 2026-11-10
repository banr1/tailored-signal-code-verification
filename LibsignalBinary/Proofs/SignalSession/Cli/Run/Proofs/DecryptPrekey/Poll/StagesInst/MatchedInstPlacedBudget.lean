/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFoldPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Path B Stage P2 Instantiation

Proves budget-threaded `stageP2Matched_framed_cli_placed_ok : StageP2MatchedFramedCliPlacedStmt`
under `[LibsignalPlacement]` via `M2TopPlacedBudget.stageP2_matched_ok_framed_placed`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget

noncomputable section

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement lsBlackBoxU8Sym lsRustNoAllocShimSym ls_hook_ok_ultra_of_mem
   ls_subroutine_ok_of_block lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (stageP1ProgPlaced)
open CryptoVerification.CliHandshake.Placed (lsProg_530)
open scoped CryptoVerification.CliHandshake.Placed
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open scoped CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (noAllocShimSpec)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli
  (CliGhostHooks cliGhostExterns cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym
   cliSignedPreKeyVtSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (cliExternsPlaced_row cliGhostExterns_other withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (dpPollProgPlaced preKeyMsgAt_eq_base_idKey_sep preKeyMsgRemBaseIdKeyAt
   sepWPp_conseq_pre sepWPp_entails_post sepWPp_lift_entails_post
   x29_eq_sp0_sub_60 x29_eq_sp_add_c70)
open CryptoVerification.SignalSession.Cli.Slots (blackBox_row_placed)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
  (drop_session_structure4_placed_ok_at)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget
  (strToOwnedLocal2Spec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlacedBudget
  (str_to_owned_local2_placed_ok_at)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
  (stageP2_matched_ok_framed_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
  (StageP2MatchedFramedCliPlacedStmt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFoldPlacedBudget
  (matched_mismatch_fold_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFoldPlacedBudget
  (matched_match_fold_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPrePlacedBudget
  (matchedInnerFramePlaced matched_entry_unpack_placed)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec publicKeySerializeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
  (public_key_serialize_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
  (dropSessionStructureLocal2Spec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem dpPollProgPlaced_eq_withPanics [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) := by
  dsimp only [dpPollProgPlaced, stageP1ProgPlaced]
  rw [withPanics_cliGhostExterns mmpl gh W]

private theorem hookSat_withPanics_placed (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) {sym : String} {α : Type} {spec : Spec α}
    (hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym spec) :
    HookSat (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) sym spec := by
  rw [withPanics_cliGhostExterns mmpl gh W]
  exact hsat

private theorem hookSat_noAllocShimBudget_of_withVmPreserved {H : String → Option (State → State)}
    (hsat : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases hsat with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

private theorem cliExternsPlaced_blackBox_withPanics (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsBlackBoxU8Sym =
      some blackBoxHook := by
  rw [withPanics_cliGhostExterns mmpl gh W,
    cliGhostExterns_other gh _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  exact cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)

private theorem cliPublicKeySerialize_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)) :=
  ls_subroutine_ok_of_block (i := 518) (j := 205)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (public_key_serialize_placed_ok
        (hookSat_withPanics_placed mmpl gh W
          (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim))
        (hookSat_withPanics_placed mmpl gh W hh.codecHooks.alloc)))

private theorem cliStrToOwnedLocal2_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A lim)) :=
  str_to_owned_local2_placed_ok_at (i := 518)
    (ls_hook_ok_ultra_of_mem (i := 530)
      (hookSat_withPanics_placed mmpl gh W
        ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸
          hh.codecHooks.shim))
      (by decide))
    (ls_hook_ok_ultra_of_mem (i := 530)
      (hookSat_withPanics_placed mmpl gh W hh.codecHooks.alloc) (by decide))
    (ls_hook_ok_ultra_of_mem (i := 530)
      (hookSat_withPanics_placed mmpl gh W hh.memcpyRO) (by decide))

private theorem cliDealloc_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim) :=
  ls_hook_ok_ultra_of_mem (i := 518)
    (hookSat_withPanics_placed mmpl gh W hh.codecHooks.dealloc)
    (by decide)

private theorem cliDropSessionStructureLocal2_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_ok_at (i := 518)
    (hookSat_withPanics_placed mmpl gh W hh.codecHooks.dealloc)
    (by decide)

set_option maxHeartbeats 800000 in
/-- Instantiation of budget-threaded `StageP2MatchedFramedCliPlacedStmt` on
`cliGhostExterns gh (cliExternsPlaced mmpl W)` via `M2TopPlacedBudget.stageP2_matched_ok_framed_placed`. -/
theorem stageP2Matched_framed_cli_placed_ok [LibsignalPlacement] :
    StageP2MatchedFramedCliPlacedStmt := by
  intro M A lim DecPkEnv ReadEnv DeserEnv st_b
    mmpl gh W B S Scope y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_frame Q Qpan
    hh _hread _hdeser hfits hcoins hMatch hcro htr hsp1 hsp0 hsp_root hpc1 hrun1 halign1 hregs
    hmismatch hmatch
  rw [dpPollProgPlaced_eq_withPanics mmpl gh W] at hmismatch hmatch ⊢
  rcases hregs with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, hx28, hx29, hvregs1⟩
  have hunpack :=
    matched_entry_unpack_placed (Scope := Scope) y st_b sess s0 s1 sp rngPtr v_a8 v_b8 v_d0
  refine sepWPp_conseq_pre (sepConj_mono_left hunpack) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun g => ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun w => ?_
  let F_in := matchedInnerFramePlaced A.repAlloc y rngPtr sp
  have hpre_assoc :
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2MatchedPrePlaced
        (A.atState lim st_b s1) s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
        y.g.peerA (y.g.msgA + 0xc8#64)
        w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
        w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
        w.u_2a8 (v_b8.extractLsb' 0 32)
        y.g.msg.messageVersion y.g.msg.message.messageVersion
        w.b_4f1 0#8 0#8 0#8 w.b_3ac
        y.g.msg.baseKey y.g.msg.identityKey g ⟨some sess⟩ F_in) ∗ F_frame =
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget.stageP2MatchedPrePlaced
        A lim st_b s0 s1 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
        y.g.peerA (y.g.msgA + 0xc8#64)
        w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
        w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
        w.u_2a8 (v_b8.extractLsb' 0 32)
        y.g.msg.messageVersion y.g.msg.message.messageVersion
        w.b_4f1 0#8 0#8 0#8 w.b_3ac
        y.g.msg.baseKey y.g.msg.identityKey g ⟨some sess⟩ (F_in ∗ F_frame) := by
    dsimp only [
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2MatchedPrePlaced,
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget.stageP2MatchedPrePlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedPrePlaced,
      lsLogOff]
    sep_ac_rfl
  rw [hpre_assoc]
  refine sepWPp_entails_post ?_
  exact stageP2_matched_ok_framed_placed
    (cliPublicKeySerialize_placed_ok mmpl gh W hh)
    (cliStrToOwnedLocal2_placed_ok mmpl gh W hh)
    (cliDealloc_placed_ok mmpl gh W hh)
    (cliExternsPlaced_blackBox_withPanics mmpl gh W)
    (cliDropSessionStructureLocal2_placed_ok mmpl gh W hh)
    st_b s0 s1
    sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
    y.g.peerA (y.g.msgA + 0xc8#64)
    w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
    w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
    w.u_2a8 (v_b8.extractLsb' 0 32)
    y.g.msg.messageVersion y.g.msg.message.messageVersion
    w.b_4f1 0#8 0#8 0#8 w.b_3ac
    y.g.msg.baseKey y.g.msg.identityKey
    g ⟨some sess⟩ sess (F_in ∗ F_frame)
    rfl hMatch.1 hMatch.2 hfits
    hcro hsp1 hsp_root hpc1 hrun1 halign1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28
    (x29_eq_sp_add_c70 hsp0 hx29)
    (fun hne evs hevs sf Pf hpcf hrunf hsteps hspf htrf hcsf hvregsf hcrof hent => by
      have hfold :=
        matched_mismatch_fold_placed y (M.stepEvents evs st_b) s0 sf sp rngPtr
          (v_b8.extractLsb' 0 32) w
      have hpost_assoc :
          LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget.stageP2MatchedMismatchPostPlaced
            A lim (M.stepEvents evs st_b) s0 sf sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
            y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
            y.g.peerA (y.g.msgA + 0xc8#64)
            w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
            w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
            w.u_2a8 (v_b8.extractLsb' 0 32)
            y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
            y.g.msg.baseKey y.g.msg.identityKey (F_in ∗ F_frame) =
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2MatchedMismatchPostPlaced
            (A.atState lim (M.stepEvents evs st_b) sf) s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
            y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
            y.g.peerA (y.g.msgA + 0xc8#64)
            w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
            w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
            w.u_2a8 (v_b8.extractLsb' 0 32)
            y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
            y.g.msg.baseKey y.g.msg.identityKey F_in ∗ F_frame := by
        dsimp only [
          LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget.stageP2MatchedMismatchPostPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2MatchedMismatchPostPlaced,
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedMismatchPostPlaced,
          lsLogOff]
        sep_ac_rfl
      rw [hpost_assoc] at hent
      exact ⟨_, Entails.trans hent (sepConj_mono_left hfold),
        hmismatch hne evs sf _ hevs hpcf hrunf hsteps (hspf.trans hsp0)
          htrf hcsf (hvregsf.trans hvregs1) hcrof (Entails.refl _)⟩)
    (fun heq evs hevs s2 recG opkHi kyberPreKeyId signedPreKeyId _hgcur hextra hsteps
        hpc2 hrun2 hsp2 halign2 htr2 hx19_2 hx27_2 hx29_2 hvregs2 hcro2 => by
      have hx29_2' := x29_eq_sp0_sub_60 hsp0 hx29_2
      refine sepWPp_lift_entails_post ?_
      refine sepWPp_conseq_pre
        (matched_match_fold_placed y (M.stepEvents evs st_b) sess s0 s2 sp rngPtr v_d0 g recG
          opkHi kyberPreKeyId signedPreKeyId F_frame hcoins
          hsp2 hx19_2 hx27_2) ?_
      exact hmatch heq evs s2 g recG y.g.msgA y.g.msgG.msg
        (((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
        opkHi kyberPreKeyId signedPreKeyId
        hevs rfl hextra
        (Entails.of_eq (by rw [preKeyMsgAt_eq_base_idKey_sep]; sep_ac_rfl))
        hsteps hpc2 hrun2 hsp2 halign2 htr2 hx19_2 hx27_2 hx29_2'
        (hvregs2.trans hvregs1) hcro2)

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget
