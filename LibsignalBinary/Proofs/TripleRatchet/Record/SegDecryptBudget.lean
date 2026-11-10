/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.SegDecrypt
public import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
public meta import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Decrypt and Dispatch Segment (`SegDecryptBudget`)

Relocatable `RustCliAllocBudget` / `SeamBudget` verification of the `try_decrypt_with_state` call
and 3-way outcome dispatch (`+0x69c → +0x1e8c / +0x850`, block 197).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Record.SegDecryptBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost uuidTryParse
  okTagVec speWord utf8
  sessionStateAt vecResultAt speAt
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel RecordDecryptGhost TryDecryptGhost rootStack recordResultAt recordResultTag
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost SetSessionStateGhost lsLogOff
)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  sessionStateAt_eq_inline_sep_heap sessionStateAt_move_bytes_twice
)
open CryptoVerification.LibsignalTripleRatchet.Record (
  blkPC_197 blkPl_197 blkLib_eq_197
  ls_hook_ok_226
  recVPCPlaced recFPCPlaced recJPCPlaced recExitPlaced recFramePlaced
  regionOutcome recordOkRel_of_clone_dec
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts (
  mkTryDecryptGhost speTag recordError_of_speTag_ne_speWord23
  model_panic_of_tryDecrypt_panic model_err_of_tryDecrypt_err model_ok_of_tryDecrypt_ok
  words6At memRegion48_eq_words6At speAt_decomp6
  stackAt_root_split_closure memRegion_192_split48
  errsAt_nil_unfold closureStack_to_growStack growStack_to_rootStack
  sessionStateAt_exists_intro noPanic_onPanic_entails segDecrypt_replace_pre
  segDecrypt_of_sepWP_placed segDecrypt_of_sepWP_ret_placed
  isDupErr decryptTarget
  stackAt_root_split_set setStack_to_rootStack
  memRegion_5f0_split344 memRegion_5f0_join344
  errsAt_nil_exists_intro sessionStateAt_ok_exists_intro
  tapeAfter_tryDecrypt_entails
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
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEnv SeqEnv FreeOnlyEvs
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (GrowOneSpeEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
  FromMEnv FromVPostTdEnv RecordDecryptEnv
  recordDecryptPlacedSpec VStatePlaced FStatePlaced JStatePlaced SegDecryptPlacedSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget (
  live_repAlloc sessionStateAt_atState vecResultAt_atState recordResultAt_atState
  errsAt_atState recFramePlaced_atState
  checkBlockNoSvc0_197
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

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
    (hL : ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem)
    (hwp : SepWPp ((blkPC_197).rebase (blkPl_197).base H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (∃ st', JStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' R s0 sf) ∨
        (∃ st', FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' R s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).onPanic
          (x, st_init) s0 sf ∗ R))) :
    ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
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
/-- Relocatable budget-threaded `SegDecrypt` contract (`+0x69c → +0x1e8c / +0x850`). -/
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
  rw [recFramePlaced_atState, sessionStateAt_atState, sessionStateAt_atState,
    errsAt_atState] at hmem
  unfold recFramePlaced at hmem
  rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp] at hmem
  simp only [← sepConj_assoc] at hmem
  apply seg_of_sepWPp_JF_placed hmem hL
    (target := decryptTarget (blkPl_197).base ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1)
  apply segDecrypt_of_sepWP_placed hfl (mid := lsmpl.base 131)
  wp_steps_sync_197 (lsmpl.base 131)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  have hsp_bound1 : rootStack ≤
      ((((((((s.writeReg64 (Reg.gpr 2#5) x.remA).writeReg64
              (Reg.gpr 3#5) x.locA).writeReg64
            (Reg.gpr 4#5) x.msgA).writeReg64
          (Reg.gpr 0#5) (s.sp + 1200#64)).writeReg64
        (Reg.gpr 1#5) (s.sp + 3232#64)).writeReg64
      (Reg.gpr 5#5) 2#64).writeReg64
    (Reg.gpr 6#5) 0#64).writeReg64 (Reg.gpr 30#5) ((blkPl_197).base + bv% (1720)) |>.setPC
      (lsmpl.base 131)).sp.toNat := hsp_bound
  have hfit_td1 : FitsEnv M lim st
      (tdEnv (tryDecryptEnvArgs
        { ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
          rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
          msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
          cur := x.cur, rest := x.rest })) := hfit_td
  segDecrypt_wpp_call_b htry_rel
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
    · -- Non-duplicate error -> FStatePlaced
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
      apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 159)
      refine segDecrypt_replace_pre
        (speAt_decomp6 A.repAlloc (utf8 "decrypt") (s.sp + 1200#64) e he_npan) (by sep_focus) ?_
      rw [memRegion_5f0_split_b40 s.sp, memRegion48_eq_words6At (s.sp + 2880#64),
        stackAt_root_split_closure s.sp, errsAt_nil_unfold A.repAlloc s.sp]
      unfold words6At
      segDecrypt_wp_extract_exists
      rename_i u0 u1 u2 u3 u4 u5 w1 w2 w3 w4 w5 H_spe hreassemble
      generalize htag_def : speTag e = tag at htag_add2 htag_ne23' hreassemble ⊢
      wp_steps_sync_197 (lsmpl.base 159)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      segDecrypt_wpp_call_b hclosure_rel () hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_placed hF_sf_1 (mid := lsmpl.base 42)
      segDecrypt_wp_extract_exists
      rename_i hcl
      refine SepWP.transport_budgetPool hcl.1 (hnext := ?_)
      rw [hsp_sf]
      refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
      wp_steps_sync_197 (lsmpl.base 42)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3
      segDecrypt_wpp_call_b hgrow_rel
        ((s.sp + 0x5d8#64, 0#64, 8#64, []), M.stepEvents evs_td st) hF3
        noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_placed hF_sf_2
      segDecrypt_wp_extract_exists
      rename_i evs_grow p' hgrow_post
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      wp_steps_sync_197 ((blkPl_197).base + 2128#64)
      rw [hsp_sf_1, hsp_sf, live_repAlloc A]
      refine segDecrypt_replace_pre
        (spe_errsAt_entails A.repAlloc s.sp p' e tag w1 w2 w3 w4 w5 H_spe hgrow_post.2.1 (hreassemble p'))
        (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_4b0_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_b40_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (sessionStateAt_exists_intro A.repAlloc (s.sp + 3232#64) G₂
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) (by sep_focus) ?_
      refine segDecrypt_replace_pre (tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
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
      · rw [hsp0, recFramePlaced_atState, sessionStateAt_atState]
        conv_rhs =>
          simp only [sessionStateAt_atState, errsAt_atState]
        unfold recFramePlaced
        rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
    · -- Duplicate error -> JStatePlaced
      have hsb_free : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
          (M.stepEvents evs_td st) FreeOnlyEvs :=
        hsb₁.weaken (fun _ h => Or.inl h)
      obtain ⟨i, c, rfl⟩ := eq_duplicatedMessage_of_isDupErr hdup
      have hmodel_dup : x.model C S uuidTryParse = (.error (.duplicatedMessage i c), x.st) :=
        model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl)
      have hmodel_dup1 : (x.model C S uuidTryParse).1 = .error (.duplicatedMessage i c) :=
        congrArg Prod.fst hmodel_dup
      apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 139)
      dsimp only [speAt]
      rw [stackAt_root_split_dropLocal2 s.sp]
      wp_steps_sync_197 (lsmpl.base 139)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      segDecrypt_wpp_call_b hdrop_rel
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
      refine segDecrypt_replace_pre (tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
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
      · rw [hsp0, hmodel_dup1, recFramePlaced_atState, sessionStateAt_atState,
          recordResultAt_atState]
        conv_rhs =>
          simp only [errsAt_atState]
        unfold recFramePlaced
        rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
        dsimp only [recordResultAt, vecResultAt, speAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
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
    wp_steps_sync_197 (lsmpl.ρ "memcpy")
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF2
    segDecrypt_wpp_call_b hmemcpy_rel (s.sp + 1520#64, s.sp + 3232#64, bs) hF2
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_placed hF_sf_1 (mid := lsmpl.base 48)
    segDecrypt_wp_extract_exists
    rename_i hmc
    refine SepWP.transport_budgetPool hmc.1 (hnext := ?_)
    wp_steps_sync_197 (lsmpl.base 48)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF3
    segDecrypt_wpp_call_b hset_rel
      ({ record := s.sp + 288#64, src := s.sp + 1520#64,
         cur := some (x.G, x.st), bs := bs : SetSessionStateGhost },
       M.stepEvents evs_td st) hF3
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_ret_placed hF_sf_2
    segDecrypt_wp_extract_exists
    rename_i evs_set hevs_set
    wp_steps_sync_197 ((blkPl_197).base + 7820#64)
    rw [hsp_sf_1, hsp_sf]
    refine segDecrypt_replace_pre
      (sessionStateAt_move_bytes_twice A.repAlloc (s.sp + 3232#64) (s.sp + 1520#64) (s.sp + 312#64)
        G₂ ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hbs.2) (by sep_focus) ?_
    refine segDecrypt_replace_pre (memRegion_5f0_join344 s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (setStack_to_rootStack s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (sessionStateAt_ok_exists_intro A.repAlloc (s.sp + 312#64) x.G G₂
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hrel) (by sep_focus) ?_
    refine segDecrypt_replace_pre (errsAt_nil_exists_intro A.repAlloc s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
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
    · rw [hsp0, hmodel_ok1, hmodel_ok2, recFramePlaced_atState, recordResultAt_atState]
      conv_rhs =>
        simp only [sessionStateAt_atState, errsAt_atState]
      unfold recFramePlaced lsLogOff
      rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
      dsimp only [recordResultAt, vecResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf

end LibsignalBinary.Proofs.TripleRatchet.Record.SegDecryptBudget
