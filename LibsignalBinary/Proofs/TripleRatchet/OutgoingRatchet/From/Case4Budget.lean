/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2Budget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case3Budget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case4
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `OTR::from_session_state` Case 4 (`st.remoteIdentity = some rem`)

Proves the `[LibsignalPlacement]` `RustCliAllocBudget` contract for the `Ok` branch
(`st.remoteIdentity = some rem`) of `<OutgoingTripleRatchet>::from_session_state`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case4Budget

open Arm64 ProofLib
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
  blkLib_19 blkLib_eq_19 blkPC_19 blkPC_201 blkPC_211 blkPC_29 blkPC_5
  blkPl_19 blkPl_201 blkPl_211 blkPl_29 blkPl_5
  lscall_blk lscall_blk_cl lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex (
  deserializePlacedSpec publicKey_deserialize_ok_inversion
)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.LibsignalTripleRatchet (OtrFromGhost)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet (
  addsPState64_neg1_eq_false agreeExceptPq_of_sender
  bytes32_eq_1_4_2_8_8_8_1 bytes32_eq_4_2_1_8_8_8_1
  bytes32_fold_1_4_2_8_8_8_1 bytes32_fold_4_2_1_8_8_8_1
  bytes32_split_localIk_sp151 bytes32_split_sp151
  ck_scratch_entails_memRegion40_sp152 elevenBytes_218_to_821_sp152 ent_of_eq
  frame128_fold_phaseB_64 frame128_split_phaseB frame15_split
  frame288_fold_phaseA frame288_split_phaseA frame33_fold frame33_split
  keyToBytes32_length localIk_bytes0_7_hi8 localIk_bytes0_7_low32 localIk_bytes0_7_mid16
  lscall_blk_ro memRegion40_split_ck_sp_entails memRegion40_split_deser_sp
  memRegion48_split_dropSpe memRegion56_fold_ok missingRemoteIdentitySym
  otrFrom_model_no_panic otrFrom_model_ok otrResultAt_ok_intro pack8
  pkTryFromOkPlacedSpec pointsTo64_of_1_1_4_2_sp152 pq_empty_cells_intro
  remoteIdentityOkAt_some_split_sp152 ret120_fold_remoteIk ret120_split_remoteIk
  ret152_fold_ck ret152_split_ck ret200_split_ok ret24_fold_srk ret24_split_srk
  ret56_fold_priv ret56_split_priv ret88_fold_localIk ret88_split_localIk
  rodata_missingRemoteIdentity_placed_intro sepWP_seq_lscl_ro
  sessionStateAt_eq_from_some sessionStateAt_eq_from_some_self
  sessionStateAt_from_some_pq_empty_fold sessionStateAt_sender_some
  sevenBytes_124_to_421_sp232 sevenBytes_421_to_124_sp151 sevenBytes_421_to_124_sp232
  sevenBytes_after_store_at_0_ret24 sevenBytes_after_store_at_0_sp232
  shift40_shift16_eq_shift56 sp184_pair8_to_16 sp352_344_pair32_to_64
  spe_missingRemote_at_sp152 sret_localIk_entails_memRegion34_6
  sret_srk_entails_memRegion40 stackAt_dropSpe stackAt_prologue stackAt_prologue_fold
  stackAt_remoteIk subsPState32_255_ls_iff vecU8Buf_bounds
  vecU8Buf_eq_bytes_live_of_ne_zero vecU8Buf_fold_of_ne_zero vecU8_cap_ne_zero_of_ge
  version_word_eq withLsRoLoaded zeroExtend32_setWidth16 zeroExtend32_setWidth8
  zeroExtend64_setWidth16 zeroExtend64_setWidth32 zeroExtend64_setWidth8
)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.FromSessionStateFacts (
  fold_entails frame15_fold_16
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropSpeSpec remoteIdentityKeyPlacedSpec
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2Budget (
  deserializePlacedBudgetSpec deserialize_vm_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case3Budget (
  pkTryFromOkPlacedBudgetSpec pkTryFromOk_vm_placed_ok_at
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget (
  otrFromCasePlacedSpec otrFromRawPlacedSpec
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget.FromSessionStateFacts (
  finish_otrFrom_placed
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_setWidth32 zeroExtend64_setWidth16 zeroExtend32_setWidth16
  zeroExtend64_setWidth8 zeroExtend32_setWidth8
  localIk_bytes0_7_low32 localIk_bytes0_7_mid16 localIk_bytes0_7_hi8
  shift40_shift16_eq_shift56

/-! ## Relocatable `[LibsignalPlacement]` Case 4 (`st.remoteIdentity = some rem`) -/

private theorem checkBlockNoSvc0_19 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_19.text = true := by
  decide +kernel

set_option maxHeartbeats 3200000 in
theorem otrFrom_case4_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdeser : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base deserializePlacedBudgetSpec)
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A.repAlloc)))
    (hdropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec M A lim))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromCasePlacedSpec M A lim
        (fun x => ∃ sc rem, x.st.senderChain = some sc ∧
          ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = some rem)) := by
  dsimp only [otrFromCasePlacedSpec, otrFromRawPlacedSpec]
  have hpkTryFrom := pkTryFromOk_vm_placed_ok_at (prog := (blkPC_211).rebase (blkPl_211).base H)
  wp_init a s0
  rcases a with ⟨⟨ss, G, st, ret⟩, stB⟩
  dsimp only at *
  have hcase : ∃ sc rem, st.senderChain = some sc ∧
      ¬ 256 ≤ st.version.toNat ∧ st.remoteIdentity = some rem := by assumption
  have hcl_0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hro_0 : LibsignalRoLoaded lsmpl s0.mem := by assumption
  rcases hcase with ⟨sc, rem, hsc, hver, hrem⟩
  apply sepWP_seq_lscl_ro hcl_0 hro_0 (mid := lsmpl.base 201)
  refine CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.SepWP.add_rodata
    (fun hm => rodata_missingRemoteIdentity_placed_intro hro_0 hm) ?_
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
        ret200_split_ok ret]
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro r11; apply SepWP.exists_elim; intro r10
  apply SepWP.exists_elim; intro r9; apply SepWP.exists_elim; intro r8
  apply SepWP.exists_elim; intro r7; apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5; apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3; apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1; apply SepWP.exists_elim; intro r0
  apply SepWP.exists_elim; intro v_deser; apply SepWP.exists_elim; intro tag0_deser
  apply SepWP.exists_elim; intro ue0; apply SepWP.exists_elim; intro ud8
  apply SepWP.exists_elim; intro uc8; apply SepWP.exists_elim; intro uc0
  apply SepWP.exists_elim; intro u9e; apply SepWP.exists_elim; intro u9c
  apply SepWP.exists_elim; intro u98; apply SepWP.exists_elim; intro u90
  apply SepWP.exists_elim; intro u88; apply SepWP.exists_elim; intro u84
  apply SepWP.exists_elim; intro u80; apply SepWP.exists_elim; intro ver0
  apply SepWP.exists_elim; intro pc0; apply SepWP.exists_elim; intro idx0
  apply SepWP.exists_elim; intro v5; apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w0
  refine SepWP.focus_pure (by sep_focus) fun hinv1 => ?_
  refine SepWP.focus_pure (by sep_focus) fun hinv2 => ?_
  obtain ⟨hdeser_lik, hrem_inv, hchains_len, hpend_some, hreg_len, _, _⟩ := id hinv1
  have hrem_inv' : PublicKey.deserialize G.remoteIk.bytes = .ok rem.publicKey := by
    rwa [hrem] at hrem_inv
  rcases hinv2 with ⟨hdeser_srk, hpriv_eq, hpriv_clamp, hsrk_len⟩
  refine SepWP.fold (vecU8Buf_bounds A.repAlloc G.localIk.cap G.localIk.ptr G.localIk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hlik_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A.repAlloc sg.srk.cap sg.srk.ptr sg.srk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hsrk_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A.repAlloc sg.priv.cap sg.priv.ptr sg.priv.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpriv_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A.repAlloc sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hck_bds => ?_
  obtain ⟨_, hlik_ge33⟩ := publicKey_deserialize_ok_inversion hdeser_lik
  have hlik_cap_ne0 : G.localIk.cap ≠ 0 := vecU8_cap_ne_zero_of_ge hlik_bds.1 (by omega)
  have hlik_len_lt : G.localIk.bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hlik_bds.1 hlik_bds.2.1
  have hlik_len_toNat : (BitVec.ofNat 64 G.localIk.bytes.length).toNat = G.localIk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlik_pk_len : st.localIdentity.publicKey.bytes.toList.length = 32 :=
    st.localIdentity.publicKey.bytes.toList_length
  obtain ⟨_, hsrk_ge33⟩ := publicKey_deserialize_ok_inversion hdeser_srk
  have hsrk_cap_ne0 : sg.srk.cap ≠ 0 := vecU8_cap_ne_zero_of_ge hsrk_bds.1 (by omega)
  have hsrk_ne_neg1 : (sg.srk.cap + 1#64 == 0#64) = false := addsPState64_neg1_eq_false hsrk_bds.2.1
  have hsrk_len_lt : sg.srk.bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hsrk_bds.1 hsrk_bds.2.1
  have hsrk_len_toNat : (BitVec.ofNat 64 sg.srk.bytes.length).toNat = sg.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_len : sg.priv.bytes.length = 32 := by rw [hpriv_eq, List.Vector.toList_length]
  have hpriv_cap_ne0 : sg.priv.cap ≠ 0 := vecU8_cap_ne_zero_of_ge hpriv_bds.1 (by omega)
  have hck_cap_ne0 : sg.ck.cap ≠ 0 := by
    have h1 := hck_bds.1; rw [keyToBytes32_length] at h1
    exact vecU8_cap_ne_zero_of_ge h1 (by decide)
  have hck_ne_neg1 : (sg.ck.cap + 1#64 == 0#64) = false := addsPState64_neg1_eq_false hck_bds.2.1
  have hv_deser_len : v_deser.toList.length = 32 := v_deser.toList_length
  have hsrk_pk_len : sc.ratchetKey.publicKey.bytes.toList.length = 32 :=
    sc.ratchetKey.publicKey.bytes.toList_length
  have hpriv_pk_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
    sc.ratchetKey.privateKey.bytes.toList_length
  have hrem_pk_len : rem.publicKey.bytes.toList.length = 32 :=
    rem.publicKey.bytes.toList_length
  have hck_key_len : (keyToBytes32 sc.chainKey.key).length = 32 :=
    keyToBytes32_length sc.chainKey.key
  have hver_ls :
      ConditionHolds CondCode.LS
        (subsPState32 (if (st.sessionVersion == 0#32) = true then 2#32 else st.sessionVersion) 255#32) =
      true := by
    rw [version_word_eq st, subsPState32_255_ls_iff st.version, decide_eq_true_eq]
    exact hver
  conv =>
    arg 4
    rw [vecU8Buf_eq_bytes_live_of_ne_zero A.repAlloc G.localIk.cap G.localIk.ptr G.localIk.bytes hlik_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A.repAlloc sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A.repAlloc sg.priv.cap sg.priv.ptr sg.priv.bytes hpriv_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A.repAlloc sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0,
        hpriv_eq, hpriv_pk_len,
        bytes32_eq_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len,
        bytes32_eq_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len]
  apply sepWP_seg_ls_vm
    (Q := (blkPC_19).rebase (blkPl_19).base (hooksException H))
    blkLib_eq_19 checkBlockNoSvc0_19 (mid := lsmpl.base 201); intro _m_strip0
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by wp_norm_lhs))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_1 hro_1
  apply sepWP_seq_lscl_ro hcl_1 hro_1 (mid := lsmpl.base 211)
  have hdeser_call :=
    lscall_blk (callerProg := (blkPC_19).rebase (blkPl_19).base H) hdeser hcl_1
  simp only [deserializePlacedBudgetSpec, withVmPreserved, deserializePlacedSpec, sepConj_assoc] at hdeser_call
  wp_call hdeser_call
    (sg.srk.ptr, sg.srk.bytes, sc.ratchetKey.publicKey,
    s0.sp - 152#64, tag0_deser, v_deser.toList)
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  apply sepWP_seg_ls_vm
    (Q := (blkPC_19).rebase (blkPl_19).base (hooksException H))
    blkLib_eq_19 checkBlockNoSvc0_19 (mid := lsmpl.base 211); intro _m_strip
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
  apply SepWP.exists_elim; intro c3; apply SepWP.exists_elim; intro c2; apply SepWP.exists_elim; intro c0
  wp_steps
  refine SepWP.fold (elevenBytes_218_to_821_sp152 s0.sp (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (frame128_split_phaseB s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro s78; apply SepWP.exists_elim; intro s70
  apply SepWP.exists_elim; intro s68; apply SepWP.exists_elim; intro s64
  apply SepWP.exists_elim; intro s60; apply SepWP.exists_elim; intro s5c
  apply SepWP.exists_elim; intro s50; apply SepWP.exists_elim; intro s48
  apply SepWP.exists_elim; intro s40; apply SepWP.exists_elim; intro s38
  apply SepWP.exists_elim; intro s30; apply SepWP.exists_elim; intro s2c
  apply SepWP.exists_elim; intro s28; apply SepWP.exists_elim; intro s24
  apply SepWP.exists_elim; intro s20; apply SepWP.exists_elim; intro s18
  apply SepWP.exists_elim; intro s10; apply SepWP.exists_elim; intro s08
  apply SepWP.exists_elim; intro s00
  refine SepWP.fold (ent_of_eq (frame33_split s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro ub8; apply SepWP.exists_elim; intro ub4
  apply SepWP.exists_elim; intro ub0; apply SepWP.exists_elim; intro ua8
  apply SepWP.exists_elim; intro ua0
  refine SepWP.fold (ent_of_eq (frame15_split s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro ud4; apply SepWP.exists_elim; intro ud0; apply SepWP.exists_elim; intro uc9
  wp_steps
  refine SepWP.fold (ck_scratch_entails_memRegion40_sp152 s0.sp _ _ _) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by wp_norm_lhs))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_2 hro_2
  apply sepWP_seq_lscl_ro hcl_2 hro_2 (mid := lsmpl.base 29)
  have hpk_call := lscall_blk_cl (callerProg := (blkPC_19).rebase (blkPl_19).base H)
    (spec := pkTryFromOkPlacedBudgetSpec) hpkTryFrom hcl_2
  simp only [pkTryFromOkPlacedBudgetSpec, withVmPreserved, pkTryFromOkPlacedSpec, sepConj_assoc] at hpk_call
  wp_call hpk_call
    (G.localIk.ptr, G.localIk.bytes, st.localIdentity.publicKey, s0.sp - 152#64)
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  refine SepWP.fold (bytes32_split_localIk_sp151 s0.sp st.localIdentity.publicKey.bytes.toList hlik_pk_len) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A.repAlloc sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A.repAlloc sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A.repAlloc sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A.repAlloc G.localIk.cap G.localIk.ptr G.localIk.bytes hlik_cap_ne0) (by sep_focus) ?_
  apply sepWP_seg_ls_vm
    (Q := (blkPC_19).rebase (blkPl_19).base (hooksException H))
    blkLib_eq_19 checkBlockNoSvc0_19 (mid := lsmpl.base 29); intro _m_strip
  wp_steps
  refine SepWP.fold (sret_localIk_entails_memRegion34_6 s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (stackAt_remoteIk s0.sp)) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by wp_norm_lhs))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_3 hro_3
  apply sepWP_seq_lscl_ro hcl_3 hro_3 (mid := lsmpl.base 5)
  have hrem_call := lscall_blk_cl (callerProg := (blkPC_19).rebase (blkPl_19).base H)
    (spec := remoteIdentityKeyPlacedSpec A.repAlloc) hremIk hcl_3
  simp only [remoteIdentityKeyPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Getters.remoteIdentityKeyPlacedSpec,
    sepConj_assoc] at hrem_call
  wp_call hrem_call ⟨ss, G.remoteIk, st.remoteIdentity, s0.sp - 152#64⟩
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  try rw [hsp_sf_2]
  try rw [hsp_sf_1]
  try rw [hsp_sf]
  refine SepWP.fold (ent_of_eq (stackAt_remoteIk s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (remoteIdentityOkAt_some_split_sp152 s0.sp st.remoteIdentity rem hrem) (by sep_focus) ?_
  refine SepWP.fold (sp184_pair8_to_16 s0.sp _ _) (by sep_focus) ?_
  apply sepWP_seg_ls_vm
    (Q := (blkPC_19).rebase (blkPl_19).base (hooksException H))
    blkLib_eq_19 checkBlockNoSvc0_19 (mid := lsmpl.base 5); intro _m_strip
  wp_steps
  refine SepWP.fold (pointsTo64_of_1_1_4_2_sp152 s0.sp _ _ _ _) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w152
  wp_steps
  refine SepWP.fold (sp352_344_pair32_to_64 s0.sp _ _ _ _) (by sep_focus) ?_
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by wp_norm_lhs))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.fold (spe_missingRemote_at_sp152 A.repAlloc s0.sp (lsρ missingRemoteIdentitySym) _ _ _ _ _ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; dsimp only [speWord]; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine SepWP.fold (ent_of_eq (stackAt_dropSpe s0.sp)) (by sep_focus) ?_
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_4 hro_4
  have hdrop_call := lscall_blk_ro (callerProg := (blkPC_19).rebase (blkPl_19).base H)
    (spec := dropSpeSpec M A lim) hdropSpe hcl_4 hro_4
  simp only [dropSpeSpec, sepConj_assoc] at hdrop_call
  wp_call hdrop_call
    (⟨s0.sp - 152#64, [], .invalidSessionStructure .missingRemoteIdentity⟩, stB)
  try rw [hsp_sf_3]
  try rw [hsp_sf_2]
  try rw [hsp_sf_1]
  try rw [hsp_sf]
  refine SepWP.fold (ent_of_eq (stackAt_dropSpe s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (memRegion48_split_dropSpe s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d8
  apply SepWP.exists_elim; intro d0
  refine SepWP.fold (ret24_split_srk ret v1.toList v1.toList_length) (by sep_focus) ?_
  refine SepWP.fold (ret56_split_priv ret v2.toList v2.toList_length) (by sep_focus) ?_
  refine SepWP.fold (ret88_split_localIk ret v3.toList v3.toList_length) (by sep_focus) ?_
  refine SepWP.fold (ret120_split_remoteIk ret v4.toList v4.toList_length) (by sep_focus) ?_
  refine SepWP.fold (ret152_split_ck ret v5.toList v5.toList_length) (by sep_focus) ?_
  apply sepWP_seg_ls_vm
    (Q := (blkPC_19).rebase (blkPl_19).base (hooksException H))
    blkLib_eq_19 checkBlockNoSvc0_19 (mid := s0.readReg64 (Reg.gpr 30#5)); intro _m_strip
  wp_steps
  refine SepWP.fold (sevenBytes_421_to_124_sp232 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_after_store_at_0_ret24 ret _ _ _ sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by wp_norm_lhs))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  try rw [hsp_sf_4]
  try rw [hsp_sf_3]
  try rw [hsp_sf_2]
  try rw [hsp_sf_1]
  try rw [hsp_sf]
  have hmod := otrFrom_model_ok ⟨ss, G, st, ret⟩ hsc hver hrem
  have hmod1 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).1 =
      .ok ⟨sc.ratchetKey, sc.chainKey, st.previousCounter, st.pqRatchetState,
        BitVec.ofNat 8 st.version.toNat, st.localIdentity, rem⟩ :=
    congrArg Prod.fst hmod
  have hmod2 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).2 = { st with pqRatchetState := [] } :=
    congrArg Prod.snd hmod
  have hnopanic := otrFrom_model_no_panic ⟨ss, G, st, ret⟩
  rw [hmod1] at hnopanic
  have hagree : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩ } := rfl
  have hagree' : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩, sender := some sg } :=
    agreeExceptPq_of_sender G ⟨0#64, 1#64⟩ sg hGs
  refine finish_otrFrom_placed ⟨ss, G, st, ret⟩ stB { G with pq := ⟨0#64, 1#64⟩ } ‹List AllocEvent› ‹FreeOnlyEvs _› _ _
    hmod1 hmod2 hnopanic hagree (by wp_done) ?_
  refine fold_entails (ret24_fold_srk ret sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine fold_entails (ret56_fold_priv ret sc.ratchetKey.privateKey.bytes hpriv_clamp _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · generalize pack8 (List.take 1 sc.ratchetKey.privateKey.bytes.toList) = b; clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · generalize pack8 (List.drop 31 sc.ratchetKey.privateKey.bytes.toList) = b; clear * -; bv_kernel
  refine fold_entails (ret88_fold_localIk ret st.localIdentity.publicKey.bytes.toList hlik_pk_len _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · have hhi : ∀ (v4 : BitVec 16) (v6 : BitVec 8),
        (v4.zeroExtend 64 ||| (v6.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32 =
          v4.zeroExtend 32 ||| (v6.zeroExtend 32 <<< 16) := by
      intro v4 v6; clear * -; bv_kernel
    rw [hhi]
    generalize CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.pack32
      (List.take 4 st.localIdentity.publicKey.bytes.toList) = v0
    generalize CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.pack16
      (List.take 2 (List.drop 4 st.localIdentity.publicKey.bytes.toList)) = v4
    generalize pack8 (List.take 1 (List.drop 6 st.localIdentity.publicKey.bytes.toList)) = v6
    clear * -; bv_kernel
  · have hhi : ∀ (v4 : BitVec 16) (v6 : BitVec 8),
        (v4.zeroExtend 64 ||| (v6.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32 =
          v4.zeroExtend 32 ||| (v6.zeroExtend 32 <<< 16) := by
      intro v4 v6; clear * -; bv_kernel
    rw [hhi]
    generalize CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.pack32
      (List.take 4 st.localIdentity.publicKey.bytes.toList) = v0
    generalize CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.pack16
      (List.take 2 (List.drop 4 st.localIdentity.publicKey.bytes.toList)) = v4
    generalize pack8 (List.take 1 (List.drop 6 st.localIdentity.publicKey.bytes.toList)) = v6
    clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine fold_entails (ret120_fold_remoteIk ret rem.publicKey.bytes.toList hrem_pk_len _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine fold_entails (ret152_fold_ck ret (keyToBytes32 sc.chainKey.key) hck_key_len _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine fold_entails (otrResultAt_ok_intro A.repAlloc ret G.pq sc st rem _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_) (by sep_focus) ?_
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  · clear * -; bv_kernel
  refine fold_entails (sevenBytes_124_to_421_sp232 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  refine fold_entails (memRegion56_fold_ok s0.sp _ _) (by sep_focus) ?_
  refine fold_entails (frame15_fold_16 s0.sp _ _ _) (by sep_focus) ?_
  refine fold_entails (frame33_fold s0.sp _ _ _ _ _) (by sep_focus) ?_
  refine fold_entails (frame128_fold_phaseB_64 s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine fold_entails (frame288_fold_phaseA s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine fold_entails (pq_empty_cells_intro A.repAlloc ss) (by sep_focus) ?_
  refine fold_entails (sessionStateAt_from_some_pq_empty_fold A.repAlloc ss G st sg sc hGs hsc hinv1 hdeser_srk hpriv_eq hpriv_clamp hsrk_len) (by sep_focus) ?_
  exact ent_of_eq (by sep_ac_rfl)

theorem otrFrom_case4_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A.repAlloc)))
    (hdropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec M A lim))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromCasePlacedSpec M A lim
        (fun x => ∃ sc rem, x.st.senderChain = some sc ∧
          ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = some rem)) :=
  otrFrom_case4_placed_ok_of_contracts
    (deserialize_vm_placed_ok H)
    hremIk hdropSpe

end LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case4Budget
