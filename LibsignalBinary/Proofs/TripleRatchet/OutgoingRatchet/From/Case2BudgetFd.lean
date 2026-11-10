/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2Budget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudgetFd
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded Relocatable `OTR::from_session_state` Case 2 (`256 ≤ st.version.toNat`)

Proves `FdsGe3Closed` preservation for the `[LibsignalPlacement]` `RustCliAllocBudget` Case 2
branch of `<OutgoingTripleRatchet>::from_session_state`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2BudgetFd

open Arm64 ProofLib
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (OutgoingTripleRatchet PublicKey SignalProtocolError)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
  blkLib_eq_19 blkPC_19 blkPC_201 blkPl_19 blkPl_201
  lsRustDeallocSym ls_hook_ok_of_mem lscall_blk lsmpl lsρ sepWP_seq_lscl
)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex (
  deserializePlacedSpec publicKey_deserialize_ok_inversion
)
open CryptoVerification.LibsignalTripleRatchet (OtrFromGhost)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet (
  addsPState64_neg1_eq_false agreeExceptPq_of_sender
  bytes32_eq_1_4_2_8_8_8_1 bytes32_eq_4_2_1_8_8_8_1
  bytes32_fold_1_4_2_8_8_8_1 bytes32_fold_4_2_1_8_8_8_1 bytes32_split_sp151
  ck_scratch_entails_memRegion40_sp152 elevenBytes_218_to_821_sp152 ent_of_eq
  frame288_fold_phaseA frame288_split_phaseA issStr_versionTooLarge_len keyToBytes32_length
  localIk_bytes0_7_hi8 localIk_bytes0_7_low32 localIk_bytes0_7_mid16
  memRegion40_split_ck_sp_entails memRegion40_split_deser_sp
  otrFrom_model_verTooLarge otrResultAt_iss_intro pq_empty_cells_intro
  ret16_pointsTo64_of_1_4_2_1 ret200_split_br2 rodata_versionTooLarge_placed_intro
  sessionStateAt_eq_from_some sessionStateAt_eq_from_some_self
  sessionStateAt_from_some_pq_empty_fold sessionStateAt_sender_some
  sevenBytes_124_to_421_sp232 sevenBytes_421_to_124_sp151
  sevenBytes_after_store_at_0_sp232 shift40_shift16_eq_shift56
  sret_srk_entails_memRegion40 stackAt_dealloc stackAt_prologue stackAt_prologue_fold
  subsPState32_255_ls_iff vecU8Buf_bounds vecU8Buf_dealloc
  vecU8Buf_eq_bytes_live_of_ne_zero vecU8Buf_fold_of_ne_zero vecU8_cap_ne_zero_of_ge
  versionTooLargeSym version_word_eq
  zeroExtend32_setWidth16 zeroExtend32_setWidth8
  zeroExtend64_setWidth16 zeroExtend64_setWidth32 zeroExtend64_setWidth8
)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.FromSessionStateFacts (fold_entails)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2Budget
  (deserializePlacedBudgetSpec)
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
  localIk_bytes0_7_low32 localIk_bytes0_7_mid16 localIk_bytes0_7_hi8
  shift40_shift16_eq_shift56

private theorem fdsGe3Closed_of_allocCallPreserved {s0 sf : State}
    (hacp : AllocCallPreserved s0 sf) (hfds : FdsGe3Closed s0.fs) :
    FdsGe3Closed sf.fs := by
  rw [hacp.1]
  exact hfds

theorem otrFrom_case2_placed_ok_of_contracts_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_19).rebase (blkPl_19).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdeser : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base (withFdsGe3Closed deserializePlacedBudgetSpec)) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromCasePlacedSpecFd M A lim
        (fun x => ∃ sc, x.st.senderChain = some sc ∧ 256 ≤ x.st.version.toNat)) := by
  dsimp only [otrFromCasePlacedSpecFd, otrFromRawPlacedSpecFd, withFdsGe3Closed, otrFromRawPlacedSpec]
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  wp_init a s0
  rcases a with ⟨⟨ss, G, st, ret⟩, stB⟩
  dsimp only at *
  have hcase : ∃ sc, st.senderChain = some sc ∧ 256 ≤ st.version.toNat := by assumption
  have hfds_0 : FdsGe3Closed s0.fs := by assumption
  have hcl_0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hro_0 : LibsignalRoLoaded lsmpl s0.mem := by assumption
  rcases hcase with ⟨sc, hsc, hver⟩
  apply sepWP_seq_lscl hcl_0 (mid := lsmpl.base 201)
  refine CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.SepWP.add_rodata
    (fun hm => rodata_versionTooLarge_placed_intro hro_0 hm) ?_
  refine SepWP.fold (sessionStateAt_sender_some A.repAlloc ss G st sc hsc) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro sg
  refine SepWP.focus_pure (by sep_focus) fun hGs => ?_
  conv =>
    arg 4
    rw [sessionStateAt_eq_from_some_self A.repAlloc ss G st sg sc hGs hsc,
        sessionStateAt_eq_from_some A.repAlloc ss G st sg sc hGs hsc G.pq st.pqRatchetState,
        stackAt_prologue s0.sp,
        frame288_split_phaseA s0.sp,
        memRegion40_split_deser_sp s0.sp,
        ret200_split_br2 ret]
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
  apply SepWP.exists_elim; intro v_deser
  apply SepWP.exists_elim; intro tag0_deser
  apply SepWP.exists_elim; intro ue0
  apply SepWP.exists_elim; intro ud8
  apply SepWP.exists_elim; intro uc8
  apply SepWP.exists_elim; intro uc0
  apply SepWP.exists_elim; intro u9e
  apply SepWP.exists_elim; intro u9c
  apply SepWP.exists_elim; intro u98
  apply SepWP.exists_elim; intro u90
  apply SepWP.exists_elim; intro u88
  apply SepWP.exists_elim; intro u84
  apply SepWP.exists_elim; intro u80
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro b23
  apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro b16
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  refine SepWP.focus_pure (by sep_focus) fun hinv1 => ?_
  refine SepWP.focus_pure (by sep_focus) fun hinv2 => ?_
  rcases hinv2 with ⟨hdeser_srk, hpriv_eq, hpriv_clamp, hsrk_len⟩
  refine SepWP.fold (vecU8Buf_bounds A.repAlloc sg.srk.cap sg.srk.ptr sg.srk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hsrk_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A.repAlloc sg.priv.cap sg.priv.ptr sg.priv.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpriv_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A.repAlloc sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hck_bds => ?_
  refine SepWP.fold (vecU8Buf_dealloc A.repAlloc G.pq.cap G.pq.ptr st.pqRatchetState) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpq_bds => ?_
  obtain ⟨_, hsrk_ge33⟩ := publicKey_deserialize_ok_inversion hdeser_srk
  have hsrk_cap_ne0 : sg.srk.cap ≠ 0 :=
    vecU8_cap_ne_zero_of_ge hsrk_bds.1 (by omega)
  have hsrk_ne_neg1 : (sg.srk.cap + 1#64 == 0#64) = false :=
    addsPState64_neg1_eq_false hsrk_bds.2.1
  have hsrk_len_lt : sg.srk.bytes.length < 2 ^ 63 :=
    Nat.lt_of_le_of_lt hsrk_bds.1 hsrk_bds.2.1
  have hsrk_len_toNat : (BitVec.ofNat 64 sg.srk.bytes.length).toNat = sg.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_len : sg.priv.bytes.length = 32 := by
    rw [hpriv_eq, List.Vector.toList_length]
  have hpriv_cap_ne0 : sg.priv.cap ≠ 0 :=
    vecU8_cap_ne_zero_of_ge hpriv_bds.1 (by omega)
  have hck_cap_ne0 : sg.ck.cap ≠ 0 := by
    have h1 := hck_bds.1
    rw [keyToBytes32_length] at h1
    exact vecU8_cap_ne_zero_of_ge h1 (by decide)
  have hck_ne_neg1 : (sg.ck.cap + 1#64 == 0#64) = false :=
    addsPState64_neg1_eq_false hck_bds.2.1
  have hv_deser_len : v_deser.toList.length = 32 := v_deser.toList_length
  have hsrk_pk_len : sc.ratchetKey.publicKey.bytes.toList.length = 32 :=
    sc.ratchetKey.publicKey.bytes.toList_length
  have hpriv_pk_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
    sc.ratchetKey.privateKey.bytes.toList_length
  have hck_key_len : (keyToBytes32 sc.chainKey.key).length = 32 :=
    keyToBytes32_length sc.chainKey.key
  have hver_ls :
      ConditionHolds CondCode.LS
        (subsPState32 (if (st.sessionVersion == 0#32) = true then 2#32 else st.sessionVersion) 255#32) =
      false := by
    rw [version_word_eq st, subsPState32_255_ls_iff st.version, decide_eq_false_iff_not, not_not]
    exact hver
  conv =>
    arg 4
    rw [vecU8Buf_eq_bytes_live_of_ne_zero A.repAlloc sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A.repAlloc sg.priv.cap sg.priv.ptr sg.priv.bytes hpriv_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A.repAlloc sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0,
        hpriv_eq, hpriv_pk_len,
        bytes32_eq_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len,
        bytes32_eq_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len]
  wp_steps_sync_pool (lsmpl.base 201)
  simp only [State.setMem_setMem]
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_deser
  have hdeser_call :=
    lscall_blk (callerProg := (blkPC_19).rebase (blkPl_19).base H) hdeser hcl_deser
  simp only [withFdsGe3Closed, deserializePlacedBudgetSpec, withVmPreserved, deserializePlacedSpec,
    sepConj_assoc] at hdeser_call
  wp_call hdeser_call
    (sg.srk.ptr, sg.srk.bytes, sc.ratchetKey.publicKey,
    s0.sp - 152#64, tag0_deser, v_deser.toList)
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  have hmod := otrFrom_model_verTooLarge ⟨ss, G, st, ret⟩ hsc hver
  have hmod1 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).1 =
      .error (.invalidSessionStructure .versionTooLarge) :=
    congrArg Prod.fst hmod
  have hmod2 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).2 = { st with pqRatchetState := [] } :=
    congrArg Prod.snd hmod
  have hnopanic : (.error (.invalidSessionStructure .versionTooLarge) :
      Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8)))) ≠ .error .panic := by
    decide
  have hagree : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩ } := rfl
  have hagree' : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩, sender := some sg } :=
    agreeExceptPq_of_sender G ⟨0#64, 1#64⟩ sg hGs
  by_cases hpq0 : G.pq.cap = (0 : BitVec 64)
  · have hpq_beq : (G.pq.cap == 0#64) = true := beq_iff_eq.mpr hpq0
    rw [ite_eq_left_iff.mpr (fun h => absurd hpq0 h)]
    apply sepWP_seg_ls_vm
      (Q := (blkPC_19).rebase (blkPl_19).base (hooksException H))
      blkLib_eq_19 (mid := s0.readReg64 (Reg.gpr 30#5)); intro _m_strip
    refine SepWP.fold (bytes32_split_sp151 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
    wp_steps
    refine SepWP.fold (sevenBytes_421_to_124_sp151 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
    wp_steps
    refine SepWP.fold (sevenBytes_after_store_at_0_sp232 s0.sp u9c u9e sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
    wp_steps 33
    refine SepWP.fold (sevenBytes_124_to_421_sp232 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
    refine SepWP.fold (sret_srk_entails_memRegion40 s0.sp _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (memRegion40_split_ck_sp_entails s0.sp) (by sep_focus) ?_
    wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c3
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c0
    wp_steps
    refine SepWP.fold (elevenBytes_218_to_821_sp152 s0.sp (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
    wp_steps
    refine SepWP.fold (ck_scratch_entails_memRegion40_sp152 s0.sp _ _ _) (by sep_focus) ?_
    refine SepWP.fold (frame288_fold_phaseA s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (bytes32_fold_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len) (by sep_focus) ?_
    refine SepWP.fold (vecU8Buf_fold_of_ne_zero A.repAlloc sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_cap_ne0) (by sep_focus) ?_
    refine SepWP.fold (bytes32_fold_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
    refine SepWP.fold (vecU8Buf_fold_of_ne_zero A.repAlloc sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0) (by sep_focus) ?_
    refine SepWP.fold (vecU8Buf_fold_of_ne_zero A.repAlloc sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0) (by sep_focus) ?_
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    try rw [hsp_sf]
    refine finish_otrFrom_placed_fd ⟨ss, G, st, ret⟩ stB { G with pq := ⟨0#64, 1#64⟩ } [] FreeOnlyEvs.nil _ _
      hmod1 hmod2 hnopanic hagree (by dsimp only [AllocCostModel.stepEvents]; wp_done) ?_
    dsimp only [AllocCostModel.stepEvents]
    refine fold_entails (ret16_pointsTo64_of_1_4_2_1 ret (lsρ versionTooLargeSym) _ _ _ _ ?_ ?_ ?_ ?_) (by sep_focus) ?_
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    refine fold_entails
      (otrResultAt_iss_intro A.repAlloc ret (lsρ versionTooLargeSym) 26#64 G.pq
        .versionTooLarge issStr_versionTooLarge_len.symm)
      (by sep_focus) ?_
    refine fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine fold_entails (pq_empty_cells_intro A.repAlloc ss) (by sep_focus) ?_
    refine fold_entails (sessionStateAt_from_some_pq_empty_fold A.repAlloc ss G st sg sc hGs hsc hinv1 hdeser_srk hpriv_eq hpriv_clamp hsrk_len) (by sep_focus) ?_
    exact ent_of_eq (by sep_ac_rfl)
  · have hpq_beq : (G.pq.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hpq0
    have hpq_pos : 0 < G.pq.cap.toNat :=
      Nat.pos_of_ne_zero (fun h0 => hpq0 (BitVec.eq_of_toNat_eq h0))
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay_pq : LayoutOk G.pq.cap.toNat 1 :=
      ⟨hpq_pos, hpow2, by have := hpq_bds.2.1; omega⟩
    rw [ite_eq_right_iff.mpr (fun h => absurd h hpq0)]
    try simp only [RustCliAllocBudget.repAlloc_live]
    apply sepWP_seg_ls_vm
      (Q := (blkPC_19).rebase (blkPl_19).base (hooksException H))
      blkLib_eq_19 (mid := lsρ lsRustDeallocSym); intro _m_strip
    refine SepWP.fold (bytes32_split_sp151 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
    wp_steps
    refine SepWP.fold (sevenBytes_421_to_124_sp151 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
    wp_steps
    refine SepWP.fold (sevenBytes_after_store_at_0_sp232 s0.sp u9c u9e sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
    wp_steps 33
    refine SepWP.fold (sevenBytes_124_to_421_sp232 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
    refine SepWP.fold (sret_srk_entails_memRegion40 s0.sp _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (memRegion40_split_ck_sp_entails s0.sp) (by sep_focus) ?_
    wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c3
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c0
    wp_steps
    refine SepWP.fold (elevenBytes_218_to_821_sp152 s0.sp (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
    wp_steps
    refine SepWP.fold (ck_scratch_entails_memRegion40_sp152 s0.sp _ _ _) (by sep_focus) ?_
    refine SepWP.fold (frame288_fold_phaseA s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (bytes32_fold_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len) (by sep_focus) ?_
    refine SepWP.fold (vecU8Buf_fold_of_ne_zero A.repAlloc sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_cap_ne0) (by sep_focus) ?_
    refine SepWP.fold (bytes32_fold_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
    refine SepWP.fold (vecU8Buf_fold_of_ne_zero A.repAlloc sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0) (by sep_focus) ?_
    refine SepWP.fold (vecU8Buf_fold_of_ne_zero A.repAlloc sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0) (by sep_focus) ?_
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWP.fold (ent_of_eq (stackAt_dealloc s0.sp)) (by sep_focus) ?_
    wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1, stB)
    have htr_d := ‹AllocCallPreserved _ _›.2.1
    have hfds_d := fdsGe3Closed_of_allocCallPreserved (by assumption) (by assumption)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    try rw [hsp_sf_1]
    try rw [hsp_sf]
    refine finish_otrFrom_placed_fd ⟨ss, G, st, ret⟩ stB { G with pq := ⟨0#64, 1#64⟩ }
      (rustDeallocEvents G.pq.cap.toNat 1) (FreeOnlyEvs.singleton 1 G.pq.cap.toNat) _ _
      hmod1 hmod2 hnopanic hagree (by wp_done) ?_
    refine fold_entails (ent_of_eq (stackAt_dealloc s0.sp).symm) (by sep_focus) ?_
    refine fold_entails (ret16_pointsTo64_of_1_4_2_1 ret (lsρ versionTooLargeSym) _ _ _ _ ?_ ?_ ?_ ?_) (by sep_focus) ?_
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    refine fold_entails
      (otrResultAt_iss_intro A.repAlloc ret (lsρ versionTooLargeSym) 26#64 G.pq
        .versionTooLarge issStr_versionTooLarge_len.symm)
      (by sep_focus) ?_
    refine fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine fold_entails (pq_empty_cells_intro A.repAlloc ss) (by sep_focus) ?_
    refine fold_entails (sessionStateAt_from_some_pq_empty_fold A.repAlloc ss G st sg sc hGs hsc hinv1 hdeser_srk hpriv_eq hpriv_clamp hsrk_len) (by sep_focus) ?_
    exact ent_of_eq (by sep_ac_rfl)

theorem otrFrom_case2_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hdeser : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base (withFdsGe3Closed deserializePlacedBudgetSpec)) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromCasePlacedSpecFd M A lim
        (fun x => ∃ sc, x.st.senderChain = some sc ∧ 256 ≤ x.st.version.toNat)) :=
  otrFrom_case2_placed_ok_of_contracts_fd
    (ls_hook_ok_of_mem h_dealloc)
    hdeser

end LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2BudgetFd
