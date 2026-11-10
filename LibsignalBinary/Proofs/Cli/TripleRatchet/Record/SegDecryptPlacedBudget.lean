/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Record.SegDecrypt
public import LibsignalBinary.Proofs.TripleRatchet.Record.SegDecryptBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegDecryptPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable CLI `SegDecrypt`

Threads `RustCliAllocBudget M` and `SeamBudget` across `segDecrypt_placed_ok` and
`segDecrypt_full_placed_ok` (`+0x69c → +0x1e8c / +0x850`) on CLI Block `463`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegDecryptPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost uuidTryParse
  okTagVec speWord utf8
  sessionStateAt protocolAddressAt signalMessageAt vecResultAt speAt
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel RecordDecryptGhost TryDecryptGhost
  rootStack
  recordResultAt recordResultTag sessionMemcpyRegionSpec
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost SetSessionStateGhost lsLogOff
  logClosurePlacedSpec logClosureSpec
)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  sessionStateAt_eq_inline_sep_heap sessionStateAt_move_bytes_twice
)
open CryptoVerification.LibsignalTripleRatchet.Record (
  regionOutcome recordOkRel_of_clone_dec
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts (
  mkTryDecryptGhost speTag recordError_of_speTag_ne_speWord23
  model_panic_of_tryDecrypt_panic model_err_of_tryDecrypt_err model_ok_of_tryDecrypt_ok
  words6At memRegion48_eq_words6At speAt_decomp6
  stackAt_root_split_closure memRegion_192_split48
  errsAt_nil_unfold closureStack_to_growStack growStack_to_rootStack
  sessionStateAt_exists_intro noPanic_onPanic_entails segDecrypt_replace_pre
  segDecrypt_of_sepWP_placed segDecrypt_of_sepWP_ret_placed segDecrypt_call_placed
  isDupErr decryptTarget
  stackAt_root_split_set setStack_to_rootStack
  memRegion_5f0_split344 memRegion_5f0_join344
  errsAt_nil_exists_intro sessionStateAt_ok_exists_intro
  stackAt_root_split_dropLocal2 dropLocal2Stack_to_rootStack
  eq_duplicatedMessage_of_isDupErr speTag_add2_ne_zero speTag_ne_speWord23_of_not_isDupErr
  memRegion_5f0_split_b40 words6_b40_to_memRegion words6_4b0_to_memRegion spe_errsAt_entails
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts.SegDecryptRegReadSimp (
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463 blkLib_463 blkLib_eq_463)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (
  ls_hook_ok_226
  recVPCPlaced recFPCPlaced recJPCPlaced recExitPlaced recFramePlaced
  cli_tapeAfter_tryDecrypt_entails
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  FitsEnv SeqEnv FreeOnlyEvs
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv growOneSpeSpec setSessionStateSpec dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
  FromMEnv FromVPostTdEnv RecordDecryptEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget (
  live_repAlloc protocolAddressAt_atState signalMessageAt_atState
  sessionStateAt_atState vecResultAt_atState recordResultAt_atState errsAt_atState
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget (
  cliRecFramePlaced_atState
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget (
  tryDecryptPlacedSpec recordDecryptPlacedSpec
  FStatePlaced JStatePlaced SegDecryptPlacedSpec
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget (
  sepWP_cut_here
)
open scoped LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

private theorem tryDecrypt_onPanic_entails_b {C : Crypto} {S : SpqrModel}
    {x : RecordDecryptGhost} {G₁ : SessionGhost}
    {s0 s sf : State} {F : SepProp} {sp : BitVec 64}
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat)
    (htr : s.trace = s0.trace) :
    (⌜(((mkTryDecryptGhost sp x G₁).model C S uuidTryParse).1 = .error .panic ∨
        S.recvPanics (mkTryDecryptGhost sp x G₁).st.pqRatchetState
          (mkTryDecryptGhost sp x G₁).msg.pqRatchet) ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜((x.model C S uuidTryParse).1 = .error .panic ∨
        (x.st.version.toNat = x.msg.messageVersion.toNat ∧
          S.recvPanics x.st.pqRatchetState x.msg.pqRatchet)) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hpan, hpref⟩ => ?_
  rw [htr] at hpref
  refine Entails.pure_right ⟨?_, hpref⟩ (entails_anyHeap _)
  rcases hpan with hmod | hrecv
  · exact Or.inl (model_panic_of_tryDecrypt_panic C S sp x G₁ heq hmod)
  · exact Or.inr ⟨heq, hrecv⟩

theorem seg_of_sepWPp_JF_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)}
    {x : RecordDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (hm : s.mem ⊨ P ∗ R)
    (hL : ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem)
    (hwp : SepWPp ((blkPC_463).rebase (blkPl_463).base H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (∃ st', JStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' R s0 sf) ∨
        (∃ st', FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' R s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).onPanic
          (x, st_init) s0 sf ∗ R))) :
    ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
      ((∃ st', JStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' R s0 s') ∨
       (∃ st', FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' R s0 s') ∨
       regionOutcome (recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv)
         recExitPlaced (x, st_init) R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hJF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · rcases hJF hmf with hJ | hF
    · exact ⟨sf, hsteps, Or.inl hJ⟩
    · exact ⟨sf, hsteps, Or.inr (Or.inl hF)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1600000 in
theorem segDecrypt_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)} :
    SegDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv H := by
  intro hmemcpy_sat htry_rel hset_rel hdrop_rel hgrow_rel hclosure_rel
    x st_init st G₁ R s0 s hV hsp_bound hL
  rcases hV with ⟨hsb, hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hfl, hvregs⟩,
    ⟨hrem_ne, hseeds, hrc_len⟩, hclone, heq, hmem⟩
  dsimp only [recVPCPlaced] at hpc
  have hmemcpy_rel := ls_hook_ok_226 (by decide) hmemcpy_sat
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  have hfit_td : FitsEnv M lim st (tdEnv (tryDecryptEnvArgs (mkTryDecryptGhost s.sp x G₁))) :=
    hsb.1.seq_left
  rw [hsp0] at hsp_bound hmem
  rw [cliRecFramePlaced_atState, sessionStateAt_atState, sessionStateAt_atState,
    errsAt_atState] at hmem
  unfold recFramePlaced at hmem
  rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp] at hmem
  simp only [← sepConj_assoc] at hmem
  apply seg_of_sepWPp_JF_placed hmem hL
    (target := decryptTarget (blkPl_463).base ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1)
  apply segDecrypt_of_sepWP_placed hfl (mid := lsmpl.base 434)
  apply sepWP_cut_here (mid := lsmpl.base 434)
  by_vm_open (
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    ⟨by wp_norm_lhs, fun _hvm => ?_⟩
  refine SepWP.transport_budgetPool _hvm (hnext := ?_)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  have hsp_bound1 : rootStack ≤
      ((((((((s.writeReg64 (Reg.gpr 2#5) x.remA).writeReg64
              (Reg.gpr 3#5) x.locA).writeReg64
            (Reg.gpr 4#5) x.msgA).writeReg64
          (Reg.gpr 0#5) (s.sp + 1200#64)).writeReg64
        (Reg.gpr 1#5) (s.sp + 3232#64)).writeReg64
      (Reg.gpr 5#5) 2#64).writeReg64
    (Reg.gpr 6#5) 0#64).writeReg64 (Reg.gpr 30#5) ((blkPl_463).base + bv% (1720)) |>.setPC
      (lsmpl.base 434)).sp.toNat := hsp_bound
  have hfit_td1 : FitsEnv M lim st
      (tdEnv (tryDecryptEnvArgs
        { ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
          rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
          msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
          cur := x.cur, rest := x.rest })) := hfit_td
  cli_segDecrypt_wpp_call_b htry_rel
    ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
       rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
       msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
       cur := x.cur, rest := x.rest : TryDecryptGhost }, st) hF1
    (tryDecrypt_onPanic_entails_b heq (by simp only [wp_norm, arm64_norm, htr]))
  apply SepWPp.exists_elim
  intro evs_td
  apply SepWPp.exists_elim
  intro G₂
  apply SepWPp.pure_elim
  rintro ⟨hevs_td, ⟨hnpan, htr_sf⟩, hdec⟩
  have hmk :
      ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
         rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
         msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
         cur := x.cur, rest := x.rest : TryDecryptGhost }) = mkTryDecryptGhost s.sp x G₁ := rfl
  rw [hmk] at hevs_td hnpan hdec ⊢
  have hsb₁ : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
      (M.stepEvents evs_td st) FromVPostTdEnv :=
    hsb.step (fun _ _ => SeqEnv.append) hevs_td
  rcases hres : ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1 with e | pt
  · -- Error branch
    dsimp only [decryptTarget, vecResultAt]
    have he_npan : e ≠ .panic := fun h => hnpan (h ▸ hres)
    cases hdup : isDupErr e
    · -- Non-duplicate Error -> FStatePlaced
      have hsb_M : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
          (M.stepEvents evs_td st) FromMEnv :=
        hsb₁.weaken (fun _ h => Or.inr h)
      have hfit_grow : FitsEnv M lim (M.stepEvents evs_td st) (GrowOneSpeEnv 0#64) :=
        hsb_M.1.seq_left
      have htag_ne23 : speTag e ≠ speWord 23 := speTag_ne_speWord23_of_not_isDupErr hdup
      have hmodel_err : x.model C S uuidTryParse =
          (.error (.invalidMessage .whisper .decryptionFailed), x.st) := by
        rw [model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl),
          recordError_of_speTag_ne_speWord23 he_npan htag_ne23]
      have hmodel_err1 : (x.model C S uuidTryParse).1 =
          .error (.invalidMessage .whisper .decryptionFailed) := congrArg Prod.fst hmodel_err
      have htag_add2 : speTag e + 2#64 ≠ 0#64 := speTag_add2_ne_zero he_npan
      have htag_ne23' : speTag e ≠ 9223372036854775831#64 := htag_ne23
      apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 462)
      refine segDecrypt_replace_pre
        (speAt_decomp6 A.repAlloc (utf8 "decrypt") (s.sp + 1200#64) e he_npan) (by sep_focus) ?_
      rw [memRegion_5f0_split_b40 s.sp, memRegion48_eq_words6At (s.sp + 2880#64),
        stackAt_root_split_closure s.sp, errsAt_nil_unfold A.repAlloc s.sp]
      unfold words6At
      segDecrypt_wp_extract_exists
      rename_i u0 u1 u2 u3 u4 u5 w1 w2 w3 w4 w5 H_spe hreassemble
      generalize htag_def : speTag e = tag at htag_add2 htag_ne23' hreassemble ⊢
      apply sepWP_cut_here (mid := (blkPl_463).base + 5992#64)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWP.transport_budgetPool (s1 := sf) (by simp only [wp_norm, arm64_norm]) (hnext := ?_)
      apply sepWP_cut_here (mid := lsmpl.base 462)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      cli_segDecrypt_wpp_call_b hclosure_rel () hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_placed hF_sf_1 (mid := lsmpl.base 42)
      segDecrypt_wp_extract_exists
      rename_i hcl
      refine SepWP.transport_budgetPool hcl.1 (hnext := ?_)
      rw [hsp_sf]
      refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
      apply sepWP_cut_here (mid := lsmpl.base 42)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3
      cli_segDecrypt_wpp_call_b hgrow_rel
        ((s.sp + 0x5d8#64, 0#64, 8#64, []), M.stepEvents evs_td st) hF3
        noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_placed hF_sf_2
      segDecrypt_wp_extract_exists
      rename_i evs_grow p' hgrow_post
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      apply sepWP_cut_here (mid := (blkPl_463).base + 2128#64)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      rw [hsp_sf_1, live_repAlloc A]
      refine segDecrypt_replace_pre
        (spe_errsAt_entails A.repAlloc s.sp p' e tag w1 w2 w3 w4 w5 H_spe hgrow_post.2.1 (hreassemble p'))
        (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_4b0_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_b40_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (sessionStateAt_exists_intro A.repAlloc (s.sp + 3232#64) G₂
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) (by sep_focus) ?_
      refine segDecrypt_replace_pre (cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF4 hmf
      right
      refine ⟨M.stepEvents evs_grow (M.stepEvents evs_td st),
        hsb_M.step (fun _ _ => SeqEnv.append) hgrow_post.1.2,
        by dsimp only [recFPCPlaced]; wp_norm_lhs, ?_, hmodel_err1, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hgrow_post.1.1, hcl.2, htr_sf, htr],
                hF4,
                by simp only [wp_norm, arm64_norm, *]⟩
      · rw [hsp0, cliRecFramePlaced_atState, sessionStateAt_atState]
        conv_rhs =>
          simp only [sessionStateAt_atState, errsAt_atState]
        unfold recFramePlaced
        rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
      )))
    · -- Duplicate Error -> JStatePlaced
      have hsb_free : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
          (M.stepEvents evs_td st) FreeOnlyEvs :=
        hsb₁.weaken (fun _ h => Or.inl h)
      obtain ⟨i, c, rfl⟩ := eq_duplicatedMessage_of_isDupErr hdup
      have hmodel_dup : x.model C S uuidTryParse = (.error (.duplicatedMessage i c), x.st) :=
        model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl)
      have hmodel_dup1 : (x.model C S uuidTryParse).1 = .error (.duplicatedMessage i c) :=
        congrArg Prod.fst hmodel_dup
      apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 442)
      dsimp only [speAt]
      rw [stackAt_root_split_dropLocal2 s.sp]
      apply sepWP_cut_here (mid := lsmpl.base 442)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      cli_segDecrypt_wpp_call_b hdrop_rel
        ({ ss := s.sp + 3232#64, G := G₂,
           st := ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 : DropSessionStructureGhost },
         M.stepEvents evs_td st)
        hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_placed hF_sf_1
      segDecrypt_wp_extract_exists
      rename_i evs_drop hevs_drop
      rw [hsp_sf]
      refine segDecrypt_replace_pre (dropLocal2Stack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (errsAt_nil_exists_intro A.repAlloc s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3 hmf
      left
      refine ⟨M.stepEvents evs_drop (M.stepEvents evs_td st),
        hsb_free.step (fun _ _ => FreeOnlyEvs.append) hevs_drop.2,
        by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_dup1]; nofun,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by rw [hmodel_dup1]; dsimp only [recordResultTag, speWord]; wp_norm_lhs, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hevs_drop.1, htr_sf, htr],
                hF3,
                by simp only [wp_norm, arm64_norm, *]⟩
      · rw [hsp0, hmodel_dup1, cliRecFramePlaced_atState, sessionStateAt_atState,
          recordResultAt_atState]
        conv_rhs =>
          simp only [errsAt_atState]
        unfold recFramePlaced
        rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
        dsimp only [recordResultAt, vecResultAt, speAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
      )
  · -- Ok branch
    have hsb_free : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
        (M.stepEvents evs_td st) FreeOnlyEvs :=
      hsb₁.weaken (fun _ h => Or.inl h)
    dsimp only [decryptTarget, vecResultAt]
    have hmodel_ok : x.model C S uuidTryParse =
        (.ok pt, ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) :=
      model_ok_of_tryDecrypt_ok C S s.sp x G₁ heq (Prod.ext hres rfl)
    have hmodel_ok1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel_ok]
    have hmodel_ok2 : (x.model C S uuidTryParse).2 =
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 := by rw [hmodel_ok]
    rw [hres] at hdec
    have hrel : x.G.AfterRecordDecrypt G₂ := recordOkRel_of_clone_dec hclone hdec
    apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.ρ "memcpy")
    rw [sessionStateAt_eq_inline_sep_heap A.repAlloc (s.sp + 3232#64) G₂
      ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2,
      memRegion_5f0_split344 s.sp, stackAt_root_split_set s.sp]
    unfold lsLogOff
    segDecrypt_wp_extract_exists
    rename_i bs hbs
    rw [← hbs.1]
    apply sepWP_cut_here (mid := (blkPl_463).base + 1736#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWP.transport_budgetPool (s1 := sf) (by simp only [wp_norm, arm64_norm]) (hnext := ?_)
    apply sepWP_cut_here (mid := lsmpl.ρ "memcpy")
    by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, fun _hvm => ?_⟩
    refine SepWP.transport_budgetPool _hvm (hnext := ?_)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF2
    cli_segDecrypt_wpp_call_b hmemcpy_rel (s.sp + 1520#64, s.sp + 3232#64, bs) hF2
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_placed hF_sf_1 (mid := lsmpl.base 48)
    segDecrypt_wp_extract_exists
    rename_i hmc
    first
      | refine SepWP.transport_budgetPool hmc.1 (hnext := ?_)
      | (have hvm_mc : VmPreserved sf sf_1 :=
           VmPreserved.trans (by simp only [wp_norm, arm64_norm]) hmc.1
         refine SepWP.transport_budgetPool hvm_mc (hnext := ?_))
    apply sepWP_cut_here (mid := lsmpl.base 48)
    by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, fun _hvm => ?_⟩
    refine SepWP.transport_budgetPool _hvm (hnext := ?_)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF3
    cli_segDecrypt_wpp_call_b hset_rel
      ({ record := s.sp + 288#64, src := s.sp + 1520#64,
         cur := some (x.G, x.st), bs := bs : SetSessionStateGhost },
       M.stepEvents evs_td st) hF3
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_ret_placed hF_sf_2
    segDecrypt_wp_extract_exists
    rename_i evs_set hevs_set
    apply sepWP_cut_here (mid := (blkPl_463).base + 7820#64)
    by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, fun _hvm => ?_⟩
    refine SepWP.transport_budgetPool _hvm (hnext := ?_)
    rw [hsp_sf_1]
    refine segDecrypt_replace_pre
      (sessionStateAt_move_bytes_twice A.repAlloc (s.sp + 3232#64) (s.sp + 1520#64) (s.sp + 312#64)
        G₂ ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hbs.2) (by sep_focus) ?_
    refine segDecrypt_replace_pre (memRegion_5f0_join344 s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (setStack_to_rootStack s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (sessionStateAt_ok_exists_intro A.repAlloc (s.sp + 312#64) x.G G₂
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hrel) (by sep_focus) ?_
    refine segDecrypt_replace_pre (errsAt_nil_exists_intro A.repAlloc s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF4 hmf
    left
    refine ⟨M.stepEvents evs_set (M.stepEvents evs_td st),
      hsb_free.step (fun _ _ => FreeOnlyEvs.append) hevs_set.2.1,
      by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_ok1]; nofun,
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by rw [hmodel_ok1]; dsimp only [recordResultTag, okTagVec]; wp_norm_lhs, ?_⟩
    · refine ⟨by wp_norm_lhs,
              by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
              by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
              by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
              by simp only [wp_norm, arm64_norm, hevs_set.1, hmc.2.2, htr_sf, htr],
              hF4,
              by simp only [wp_norm, arm64_norm, *]⟩
    · rw [hsp0, hmodel_ok1, hmodel_ok2, cliRecFramePlaced_atState, recordResultAt_atState]
      conv_rhs =>
        simp only [sessionStateAt_atState, errsAt_atState]
      unfold recFramePlaced lsLogOff
      rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
      dsimp only [recordResultAt, vecResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
    )))
  )

set_option maxHeartbeats 1600000 in
/-- `[LibsignalFullPlacement]` `withLsFrozen` variant of `segDecrypt_placed_ok` discharging the
log-closure premise internally. -/
theorem segDecrypt_full_placed_ok [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)} :
    LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.SegDecryptFullPlacedSpec
      C A lim ctl uuidTryParse S tdEnv H := by
  intro hmemcpy_sat htry_rel hset_rel hdrop_rel hgrow_rel
    x st_init st G₁ R s0 s hV hsp_bound hFroz hL
  have _ := CryptoVerification.CliRatchet.DecPlaced.instIsLsBlockProg_463 H
  have hclosure_rel :=
    LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureVmPlacedBudget.log_closure_coins_frozen_vm_placed_ok_of_block
      (callerProg := (blkPC_463).rebase (blkPl_463).base H)
  rcases hV with ⟨hsb, hpc, ⟨hrun, hsp, hsp_align, hx29, htr, _hfl, hvregs⟩,
    ⟨hrem_ne, hseeds, hrc_len⟩, hclone, heq, hmem⟩
  dsimp only [recVPCPlaced] at hpc
  have hmemcpy_rel := ls_hook_ok_226 (by decide) hmemcpy_sat
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  have hfit_td : FitsEnv M lim st (tdEnv (tryDecryptEnvArgs (mkTryDecryptGhost s.sp x G₁))) :=
    hsb.1.seq_left
  rw [hsp0] at hsp_bound hmem
  rw [cliRecFramePlaced_atState, sessionStateAt_atState, sessionStateAt_atState,
    errsAt_atState] at hmem
  unfold recFramePlaced at hmem
  rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp] at hmem
  simp only [← sepConj_assoc] at hmem
  apply seg_of_sepWPp_JF_placed hmem hL
    (target := decryptTarget (blkPl_463).base ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1)
  apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hFroz (mid := lsmpl.base 434)
  apply sepWP_cut_here (mid := lsmpl.base 434)
  by_vm_open (
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    ⟨by wp_norm_lhs, fun _hvm => ?_⟩
  refine SepWP.transport_budgetPool _hvm (hnext := ?_)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  have hsp_bound1 : rootStack ≤
      ((((((((s.writeReg64 (Reg.gpr 2#5) x.remA).writeReg64
              (Reg.gpr 3#5) x.locA).writeReg64
            (Reg.gpr 4#5) x.msgA).writeReg64
          (Reg.gpr 0#5) (s.sp + 1200#64)).writeReg64
        (Reg.gpr 1#5) (s.sp + 3232#64)).writeReg64
      (Reg.gpr 5#5) 2#64).writeReg64
    (Reg.gpr 6#5) 0#64).writeReg64 (Reg.gpr 30#5) ((blkPl_463).base + bv% (1720)) |>.setPC
      (lsmpl.base 434)).sp.toNat := hsp_bound
  have hfit_td1 : FitsEnv M lim st
      (tdEnv (tryDecryptEnvArgs
        { ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
          rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
          msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
          cur := x.cur, rest := x.rest })) := hfit_td
  cli_segDecrypt_wpp_call_lsfull_b htry_rel
    ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
       rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
       msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
       cur := x.cur, rest := x.rest : TryDecryptGhost }, st) hF1
    (tryDecrypt_onPanic_entails_b heq (by simp only [wp_norm, arm64_norm, htr]))
  apply SepWPp.exists_elim
  intro evs_td
  apply SepWPp.exists_elim
  intro G₂
  apply SepWPp.pure_elim
  rintro ⟨hevs_td, ⟨hnpan, htr_sf⟩, hdec⟩
  have hmk :
      ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
         rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
         msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
         cur := x.cur, rest := x.rest : TryDecryptGhost }) = mkTryDecryptGhost s.sp x G₁ := rfl
  rw [hmk] at hevs_td hnpan hdec ⊢
  have hsb₁ : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
      (M.stepEvents evs_td st) FromVPostTdEnv :=
    hsb.step (fun _ _ => SeqEnv.append) hevs_td
  rcases hres : ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1 with e | pt
  · -- Error branch
    dsimp only [decryptTarget, vecResultAt]
    have he_npan : e ≠ .panic := fun h => hnpan (h ▸ hres)
    cases hdup : isDupErr e
    · -- Non-duplicate Error -> FStatePlaced
      have hsb_M : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
          (M.stepEvents evs_td st) FromMEnv :=
        hsb₁.weaken (fun _ h => Or.inr h)
      have hfit_grow : FitsEnv M lim (M.stepEvents evs_td st) (GrowOneSpeEnv 0#64) :=
        hsb_M.1.seq_left
      have htag_ne23 : speTag e ≠ speWord 23 := speTag_ne_speWord23_of_not_isDupErr hdup
      have hmodel_err : x.model C S uuidTryParse =
          (.error (.invalidMessage .whisper .decryptionFailed), x.st) := by
        rw [model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl),
          recordError_of_speTag_ne_speWord23 he_npan htag_ne23]
      have hmodel_err1 : (x.model C S uuidTryParse).1 =
          .error (.invalidMessage .whisper .decryptionFailed) := congrArg Prod.fst hmodel_err
      have htag_add2 : speTag e + 2#64 ≠ 0#64 := speTag_add2_ne_zero he_npan
      have htag_ne23' : speTag e ≠ 9223372036854775831#64 := htag_ne23
      apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hF_sf (mid := lsmpl.base 462)
      refine segDecrypt_replace_pre
        (speAt_decomp6 A.repAlloc (utf8 "decrypt") (s.sp + 1200#64) e he_npan) (by sep_focus) ?_
      rw [memRegion_5f0_split_b40 s.sp, memRegion48_eq_words6At (s.sp + 2880#64),
        stackAt_root_split_closure s.sp, errsAt_nil_unfold A.repAlloc s.sp]
      unfold words6At
      segDecrypt_wp_extract_exists
      rename_i u0 u1 u2 u3 u4 u5 w1 w2 w3 w4 w5 H_spe hreassemble
      generalize htag_def : speTag e = tag at htag_add2 htag_ne23' hreassemble ⊢
      apply sepWP_cut_here (mid := (blkPl_463).base + 5992#64)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWP.transport_budgetPool (s1 := sf) (by simp only [wp_norm, arm64_norm]) (hnext := ?_)
      apply sepWP_cut_here (mid := lsmpl.base 462)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      cli_segDecrypt_wpp_call_lsfull_b hclosure_rel () hF2 noPanic_onPanic_entails
      apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hF_sf_1 (mid := lsmpl.base 42)
      segDecrypt_wp_extract_exists
      rename_i hcl
      refine SepWP.transport_budgetPool hcl.1 (hnext := ?_)
      rw [hsp_sf]
      refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
      apply sepWP_cut_here (mid := lsmpl.base 42)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3
      cli_segDecrypt_wpp_call_lsfull_b hgrow_rel
        ((s.sp + 0x5d8#64, 0#64, 8#64, []), M.stepEvents evs_td st) hF3
        noPanic_onPanic_entails
      apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_ret_lsfull hF_sf_2
      segDecrypt_wp_extract_exists
      rename_i evs_grow p' hgrow_post
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      apply sepWP_cut_here (mid := (blkPl_463).base + 2128#64)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      rw [hsp_sf_1, live_repAlloc A]
      refine segDecrypt_replace_pre
        (spe_errsAt_entails A.repAlloc s.sp p' e tag w1 w2 w3 w4 w5 H_spe hgrow_post.2.1 (hreassemble p'))
        (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_4b0_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_b40_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (sessionStateAt_exists_intro A.repAlloc (s.sp + 3232#64) G₂
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) (by sep_focus) ?_
      refine segDecrypt_replace_pre (cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF4 hmf
      right
      refine ⟨M.stepEvents evs_grow (M.stepEvents evs_td st),
        hsb_M.step (fun _ _ => SeqEnv.append) hgrow_post.1.2,
        by dsimp only [recFPCPlaced]; wp_norm_lhs, ?_, hmodel_err1, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hgrow_post.1.1, hcl.2, htr_sf, htr],
                CryptoVerification.Cli.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen hF4,
                by simp only [wp_norm, arm64_norm, *]⟩
      · rw [hsp0, cliRecFramePlaced_atState, sessionStateAt_atState]
        conv_rhs =>
          simp only [sessionStateAt_atState, errsAt_atState]
        unfold recFramePlaced
        rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
      )))
    · -- Duplicate Error -> JStatePlaced
      have hsb_free : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
          (M.stepEvents evs_td st) FreeOnlyEvs :=
        hsb₁.weaken (fun _ h => Or.inl h)
      obtain ⟨i, c, rfl⟩ := eq_duplicatedMessage_of_isDupErr hdup
      have hmodel_dup : x.model C S uuidTryParse = (.error (.duplicatedMessage i c), x.st) :=
        model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl)
      have hmodel_dup1 : (x.model C S uuidTryParse).1 = .error (.duplicatedMessage i c) :=
        congrArg Prod.fst hmodel_dup
      apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hF_sf (mid := lsmpl.base 442)
      dsimp only [speAt]
      rw [stackAt_root_split_dropLocal2 s.sp]
      apply sepWP_cut_here (mid := lsmpl.base 442)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      cli_segDecrypt_wpp_call_lsfull_b hdrop_rel
        ({ ss := s.sp + 3232#64, G := G₂,
           st := ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 : DropSessionStructureGhost },
         M.stepEvents evs_td st)
        hF2 noPanic_onPanic_entails
      apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_ret_lsfull hF_sf_1
      segDecrypt_wp_extract_exists
      rename_i evs_drop hevs_drop
      rw [hsp_sf]
      refine segDecrypt_replace_pre (dropLocal2Stack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (errsAt_nil_exists_intro A.repAlloc s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3 hmf
      left
      refine ⟨M.stepEvents evs_drop (M.stepEvents evs_td st),
        hsb_free.step (fun _ _ => FreeOnlyEvs.append) hevs_drop.2,
        by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_dup1]; nofun,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by rw [hmodel_dup1]; dsimp only [recordResultTag, speWord]; wp_norm_lhs, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hevs_drop.1, htr_sf, htr],
                CryptoVerification.Cli.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen hF3,
                by simp only [wp_norm, arm64_norm, *]⟩
      · rw [hsp0, hmodel_dup1, cliRecFramePlaced_atState, sessionStateAt_atState,
          recordResultAt_atState]
        conv_rhs =>
          simp only [errsAt_atState]
        unfold recFramePlaced
        rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
        dsimp only [recordResultAt, vecResultAt, speAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
      )
  · -- Ok branch
    have hsb_free : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
        (M.stepEvents evs_td st) FreeOnlyEvs :=
      hsb₁.weaken (fun _ h => Or.inl h)
    dsimp only [decryptTarget, vecResultAt]
    have hmodel_ok : x.model C S uuidTryParse =
        (.ok pt, ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) :=
      model_ok_of_tryDecrypt_ok C S s.sp x G₁ heq (Prod.ext hres rfl)
    have hmodel_ok1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel_ok]
    have hmodel_ok2 : (x.model C S uuidTryParse).2 =
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 := by rw [hmodel_ok]
    rw [hres] at hdec
    have hrel : x.G.AfterRecordDecrypt G₂ := recordOkRel_of_clone_dec hclone hdec
    apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hF_sf (mid := lsmpl.ρ "memcpy")
    rw [sessionStateAt_eq_inline_sep_heap A.repAlloc (s.sp + 3232#64) G₂
      ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2,
      memRegion_5f0_split344 s.sp, stackAt_root_split_set s.sp]
    unfold lsLogOff
    segDecrypt_wp_extract_exists
    rename_i bs hbs
    rw [← hbs.1]
    apply sepWP_cut_here (mid := (blkPl_463).base + 1736#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWP.transport_budgetPool (s1 := sf) (by simp only [wp_norm, arm64_norm]) (hnext := ?_)
    apply sepWP_cut_here (mid := lsmpl.ρ "memcpy")
    by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, fun _hvm => ?_⟩
    refine SepWP.transport_budgetPool _hvm (hnext := ?_)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF2
    cli_segDecrypt_wpp_call_lsfull_b hmemcpy_rel (s.sp + 1520#64, s.sp + 3232#64, bs) hF2
      noPanic_onPanic_entails
    apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hF_sf_1 (mid := lsmpl.base 48)
    segDecrypt_wp_extract_exists
    rename_i hmc
    first
      | refine SepWP.transport_budgetPool hmc.1 (hnext := ?_)
      | (have hvm_mc : VmPreserved sf sf_1 :=
           VmPreserved.trans (by simp only [wp_norm, arm64_norm]) hmc.1
         refine SepWP.transport_budgetPool hvm_mc (hnext := ?_))
    apply sepWP_cut_here (mid := lsmpl.base 48)
    by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, fun _hvm => ?_⟩
    refine SepWP.transport_budgetPool _hvm (hnext := ?_)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF3
    cli_segDecrypt_wpp_call_lsfull_b hset_rel
      ({ record := s.sp + 288#64, src := s.sp + 1520#64,
         cur := some (x.G, x.st), bs := bs : SetSessionStateGhost },
       M.stepEvents evs_td st) hF3
      noPanic_onPanic_entails
    apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_ret_lsfull hF_sf_2
    segDecrypt_wp_extract_exists
    rename_i evs_set hevs_set
    apply sepWP_cut_here (mid := (blkPl_463).base + 7820#64)
    by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, fun _hvm => ?_⟩
    refine SepWP.transport_budgetPool _hvm (hnext := ?_)
    rw [hsp_sf_1]
    refine segDecrypt_replace_pre
      (sessionStateAt_move_bytes_twice A.repAlloc (s.sp + 3232#64) (s.sp + 1520#64) (s.sp + 312#64)
        G₂ ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hbs.2) (by sep_focus) ?_
    refine segDecrypt_replace_pre (memRegion_5f0_join344 s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (setStack_to_rootStack s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (sessionStateAt_ok_exists_intro A.repAlloc (s.sp + 312#64) x.G G₂
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hrel) (by sep_focus) ?_
    refine segDecrypt_replace_pre (errsAt_nil_exists_intro A.repAlloc s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF4 hmf
    left
    refine ⟨M.stepEvents evs_set (M.stepEvents evs_td st),
      hsb_free.step (fun _ _ => FreeOnlyEvs.append) hevs_set.2.1,
      by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_ok1]; nofun,
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by rw [hmodel_ok1]; dsimp only [recordResultTag, okTagVec]; wp_norm_lhs, ?_⟩
    · refine ⟨by wp_norm_lhs,
              by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
              by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
              by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
              by simp only [wp_norm, arm64_norm, hevs_set.1, hmc.2.2, htr_sf, htr],
              CryptoVerification.Cli.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen hF4,
              by simp only [wp_norm, arm64_norm, *]⟩
    · rw [hsp0, hmodel_ok1, hmodel_ok2, cliRecFramePlaced_atState, recordResultAt_atState]
      conv_rhs =>
        simp only [sessionStateAt_atState, errsAt_atState]
      unfold recFramePlaced lsLogOff
      rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
      dsimp only [recordResultAt, vecResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
    )))
  )

end LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegDecryptPlacedBudget
