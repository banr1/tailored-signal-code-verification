/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.Neon
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.RecClone
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreDecodes
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.CanonPreservation
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# `InMemSessionStore::store_session::{closure#0}` (`0x08ee4`) on a Single-Entry Hit

Proves `storeSessionSingleHit_ok'` against `storeSessionSingleHitSpec A`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.SipHashBin
open CryptoVerification.E2E.InMem.HashbrownBin
open LoadSingle

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CanonSession
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


set_option maxHeartbeats 1600000 in
theorem storeSessionSingleHit_ok' (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName)
      (storeSessionSingleHitSpec A) := by
  have hStrClone := stringClone_ok_at_storeSessionClosure b hHooks
  have hClone := sessionClone_ok_at_storeSessionClosure b hHooks
  have hVecClone := vecVecCloneEmpty_ok_at_storeSessionClosure b hHooks
  have hHash := hashOneAddr36_ok_at_store b ext A
  have hBcmp := bcmp_ok_at_storeSessionClosure b hHooks
  have hMemcpy := memcpy_ok_at_storeSessionClosure b hHooks
  have hDealloc := dealloc_ok_at_storeSessionClosure b hHooks
  have hDrop := drop_session_structure_local1_ok_at_storeSessionClosure b hHooks
  simp only [storeSessionSingleHitSpec]
  have hfn : libsignalSessionCode.fnOff storeSessionClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") :=
    (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")) 912
  clear hfn
  dsimp only [RebasedProg, BitVec.ofNat_eq_ofNat] at hStrClone hClone hVecClone hHash hBcmp hMemcpy hDealloc hDrop ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr storeSessionClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  wpp_init x s0
  examples_hide_fetches
  obtain ⟨futPtr, sret, mp, k0, k1, k, peerG, oldRecG, oldSs,
    qAddrPtr, qG, recPtr, newRecG, newSs, newPrevCap, newPrevPtr⟩ := x
  dsimp only [StoreSessionSingleHitGhost.futPtr, StoreSessionSingleHitGhost.sret,
    StoreSessionSingleHitGhost.mp, StoreSessionSingleHitGhost.k0,
    StoreSessionSingleHitGhost.k1, StoreSessionSingleHitGhost.k,
    StoreSessionSingleHitGhost.peerG, StoreSessionSingleHitGhost.oldRecG,
    StoreSessionSingleHitGhost.oldSs, StoreSessionSingleHitGhost.qAddrPtr,
    StoreSessionSingleHitGhost.qG, StoreSessionSingleHitGhost.recPtr,
    StoreSessionSingleHitGhost.newRecG, StoreSessionSingleHitGhost.newSs,
    StoreSessionSingleHitGhost.newPrevCap, StoreSessionSingleHitGhost.newPrevPtr] at *
  have hk : k < 4 := by assumption
  have hpeer_len : peerG.name.bytes.length = 36 := by assumption
  have hq_bytes : qG.name.bytes = peerG.name.bytes := by assumption
  have hq_dev : qG.device = peerG.device := by assumption
  have hq_len : qG.name.bytes.length = 36 := hq_bytes ▸ hpeer_len
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
  wp_conv_pre => rw [table4SingleAt_eq]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro ctrl
  wp_conv_pre => rw [sret48_split_eq sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro c_sret0
  wp_conv_pre => rw [stackAt_store_eq s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat' (apply sepWP_exists_elim; intro _)
  refine sepWP_extract_pure (P := k < 4) (by sep_focus) fun _ => ?_
  refine sepWP_extract_pure (by sep_focus) ?_
  rintro ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩
  wp_conv_pre =>
    rw [protocolAddressAt_eq_vecGhostAt_parts A qG qAddrPtr,
        sessionRecordAt_some_any_prev_eq A recPtr newPrevCap newPrevPtr newRecG newSs,
        sessionAt_eq_head_tail A (recPtr + 24#64) newRecG newSs]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro bs336_src
  refine sepWP_extract_pure
    (P := bs336_src.length = 336 ∧ newRecG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline newRecG newSs.state (unpack64 newRecG.localIk.cap ++ bs336_src))
    (by sep_focus) fun ⟨hbs336_src, hcap_new, hinl_new⟩ => ?_
  have hcmn_new : (newRecG.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCap hcap_new
  refine step_stpSimd64_sp_pre (by wp_norm_lhs) (by wp_norm_lhs) (by wp_assumption)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_sep_access_fast) (by wp_sep_access_fast) fun _ => ?_
  wp_norm_state
  wp_steps
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) HashbrownBin.extHookStack (by decide)]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine wpp_call_stringClone qAddrPtr (s0.sp - 1264#64) (s0.sp - 1312#64) qG.name
    hStrClone (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp [Arm64.State.spAligned, arm64_norm, *])
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp [arm64_norm, *]) (by simp [arm64_norm, *]) (by sep_focus)
    fun sf_s hpc_s hrun_s hsp_s hcs_s htr_s => ?_
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
  obtain ⟨hcs_s19, hcs_s20, hcs_s21, hcs_s22, hcs_s23, hcs_s24, hcs_s25, hcs_s26, hcs_s27, hcs_s28, hcs_s29, hcs_svregs⟩ := hcs_s
  simp only [arm64_norm, *] at hcs_s19 hcs_s20 hcs_s21 hcs_s22 hcs_s23 hcs_s24 hcs_s25 hcs_s26 hcs_s27 hcs_s28 hcs_s29 hcs_svregs
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) HashbrownBin.extHookStack (by decide)).symm)
    (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sessionAt_pack_head_tail A (recPtr + 24#64) newRecG newSs hinl_new)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_vecGhostAt_parts A qG qAddrPtr).symm)
    (by sep_focus) ?_
  refine SepWP.fold (vecU8_and_dev_entails_protocolAddressAt A s0.sp qG.name.bytes peerG.device)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left]
  apply sepWP_exists_elim; intro clonedCap
  apply sepWP_exists_elim; intro clonedPtr
  let clonedG : AddrGhost := ⟨⟨clonedCap, clonedPtr, qG.name.bytes⟩, peerG.device⟩
  have hcloned_len : clonedG.name.bytes.length = 36 := hq_len
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) sessionCloneStack (by decide)]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine wpp_call_sessionClone (s0.sp - 528#64) (recPtr + 24#64) (s0.sp - 1312#64) newRecG newSs
    hClone (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp [Arm64.State.spAligned, arm64_norm, *])
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp [arm64_norm, *]) (by simp [arm64_norm, *]) (by sep_focus)
    fun sf_c hpc_c hrun_c hsp_c hcs_c htr_c => ?_
  apply SepWPp.of_sepWP_ret
  obtain ⟨hcs_c19, hcs_c20, hcs_c21, hcs_c22, hcs_c23, hcs_c24, hcs_c25, hcs_c26, hcs_c27, hcs_c28, hcs_c29, hcs_cvregs⟩ := hcs_c
  simp only [arm64_norm, *] at hcs_c19 hcs_c20 hcs_c21 hcs_c22 hcs_c23 hcs_c24 hcs_c25 hcs_c26 hcs_c27 hcs_c28 hcs_c29 hcs_cvregs
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) sessionCloneStack (by decide)).symm)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro clonedRecG
  refine sepWP_extract_pure (P := encSessionMem clonedRecG newSs = encSessionMem newRecG newSs)
    (by sep_focus) fun _ => ?_
  refine SepWP.fold (DeserializeGeneral.sessionAt_canon A (s0.sp - 528#64) clonedRecG newSs)
    (by sep_focus) ?_
  refine sepWP_extract_pure (P := CanonSession clonedRecG newSs)
    (by sep_focus) fun hcanon_cloned => ?_
  have h520 : s0.sp - 528#64 + 8#64 = s0.sp - 520#64 := by bv_omega
  wp_conv_pre => rw [sessionAt_eq_head_tail A (s0.sp - 528#64) clonedRecG newSs, h520]
  simp only [sepExists_sepConj_left]
  apply sepWP_exists_elim; intro bs336_new
  refine sepWP_extract_pure
    (P := bs336_new.length = 336 ∧ clonedRecG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline clonedRecG newSs.state (unpack64 clonedRecG.localIk.cap ++ bs336_new))
    (by sep_focus) fun ⟨hbs336_new, hcap_cloned, hinl_cloned⟩ => ?_
  wp_steps
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) 4096 (by decide)]
  refine SepWP.fold (Entails.of_eq (congrArg (memRegion (s0.sp - 864#64)) hbs336_new.symm))
    (by sep_focus) ?_
  wp_call hMemcpy (s0.sp - 864#64, s0.sp - 520#64, bs336_new)
  simp only [hsp_c] at *
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) 4096 (by decide)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (slot784_to_memRegion368 s0.sp clonedRecG.localIk.cap bs336_new hbs336_new)
    (by sep_focus) ?_
  wp_steps
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) vecVecCloneStack (by decide)]
  wp_call hVecClone ⟨s0.sp - 1232#64, newPrevPtr⟩
  simp only [‹sf.sp = s0.sp - 1312#64›] at *
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) vecVecCloneStack (by decide)).symm)
    (by sep_focus) ?_
  dsimp only [vecHeader]
  have h1224 : s0.sp - 1232#64 + 8#64 = s0.sp - 1224#64 := by bv_omega
  have h1216 : s0.sp - 1232#64 + 16#64 = s0.sp - 1216#64 := by bv_omega
  wp_conv_pre => rw [h1224, h1216]
  wp_steps
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) 4096 (by decide)]
  refine SepWP.fold (Entails.of_eq (congrArg (memRegion (s0.sp - 1200#64)) hbs336_new.symm))
    (by sep_focus) ?_
  wp_call hMemcpy (s0.sp - 1200#64, s0.sp - 864#64, bs336_new)
  simp only [‹sf_1.sp = s0.sp - 1312#64›] at *
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) 4096 (by decide)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (hbs336_new ▸ pointsToBytes_entails_memRegion (s0.sp - 864#64) bs336_new)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (slot80_full368_eq_bytes s0.sp clonedRecG.localIk.cap bs336_new))
    (by sep_focus) ?_
  obtain ⟨bs368_new, hdef368_new, hbs368_new⟩ :
      ∃ bs368_new,
        (unpack64 0#64 ++ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 clonedRecG.localIk.cap ++ bs336_new)) = bs368_new ∧
        bs368_new.length = 368 :=
    ⟨_, rfl, by simp [unpack64_length, hbs336_new]⟩
  wp_conv_pre => rw [hdef368_new]
  wp_steps
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) hashOneAddrStack (by decide)]
  wp_call hHash ⟨k0, k1, s0.sp - 1264#64, clonedG⟩
  simp only [‹sf_2.sp = s0.sp - 1312#64›] at *
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) hashOneAddrStack (by decide)).symm)
    (by sep_focus) ?_
  have hcloned_bytes : clonedG.name.bytes = peerG.name.bytes := hq_bytes
  have hcloned_dev : clonedG.device = peerG.device := rfl
  have h1256 : s0.sp - 1264#64 + 8#64 = s0.sp - 1256#64 := by bv_omega
  have h1248 : s0.sp - 1264#64 + 16#64 = s0.sp - 1248#64 := by bv_omega
  have h1240 : s0.sp - 1264#64 + 24#64 = s0.sp - 1240#64 := by bv_omega
  wp_conv_pre =>
    rw [protocolAddressAt_eq_of_len36 A clonedG (s0.sp - 1264#64) hcloned_len,
        h1256, h1248, h1240]
  wp_steps
  let pos := (hashAddrBv k0 k1 peerG.name.bytes peerG.device &&& 3#64).toNat
  have hpos_lt : pos < 4 :=
    probePos_3_toNat_lt (hashAddrBv k0 k1 peerG.name.bytes peerG.device)
  have hpos_bv : BitVec.ofNat 64 pos = hashAddrBv k0 k1 peerG.name.bytes peerG.device &&& 3#64 := by
    simp [pos]
  have hcbs_len : (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerG.name.bytes peerG.device))).length = 12 := by
    simp [singleCtrl4, mkCtrl4]
  have hcbs_split := pointsToBytes_ctrl12_split_at ctrl
    (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerG.name.bytes peerG.device))) hcbs_len pos hpos_lt
  rw [hpos_bv] at hcbs_split
  refine SepWP.fold (Entails.of_eq hcbs_split) (by sep_focus) ?_
  refine step_ldrSimd64 (wb := none) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_assumption)
    rfl (by simp [evalAddrMode, extendVal, arm64_norm, *]; rfl)
    (by wp_sep_access_fast) (by wp_norm_lhs) ?_
  refine SepWP.fold (Entails.of_eq hcbs_split.symm) (by sep_focus) ?_
  clear hcbs_split
  wp_steps
  rw [rawMatchTagMask_eq_findGroupIterMask]
  have hmask : ¬(findGroupIterMask
      (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerG.name.bytes peerG.device)))
      pos (h2Tag (hashAddrBv k0 k1 peerG.name.bytes peerG.device)) = 0#64) :=
    fun h0 => findGroupIterMask_singleCtrl4_eq_zero_imp_ne k0 k1 k hk
      peerG.name.bytes peerG.name.bytes peerG.device peerG.device h0 ⟨rfl, rfl⟩
  have hmask_eq := findGroupIterMask_singleCtrl4_ne_zero_eq k0 k1 k pos hk hpos_lt
    peerG.name.bytes peerG.name.bytes peerG.device peerG.device hmask
  have hprobe := eval_probeBucket_singleCtrl4' k pos hk hpos_lt
  have hmask_beq := laneBit_laneOfBucket4_beq_zero k pos hk hpos_lt
  rw [hpos_bv] at hprobe
  rw [hmask_eq]
  obtain ⟨hoff40, hoff48, hoff56, hoff64⟩ := bucket_rec_off_eqs ctrl k
  wp_conv_pre =>
    rw [arrayAt_single_split_400 ctrl k hk (sessionBucketEntryAt A peerG oldRecG oldSs)]
  dsimp only [sessionBucketEntryAt, sessionBucketValueOff]
  refine sepWP_extract_pure (P := CanonSession oldRecG oldSs) (by sep_focus) fun _ => ?_
  wp_conv_pre =>
    rw [protocolAddressAt_eq_of_len36 A peerG (bucketAddr ctrl 400 k) hpeer_len,
        sessionRecordAt_some_eq A (bucketAddr ctrl 400 k + 32#64) oldRecG oldSs,
        hoff40, hoff48, hoff56,
        sessionAt_eq_head_tail A (bucketAddr ctrl 400 k + 56#64) oldRecG oldSs,
        hoff64]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro bs336_old
  refine sepWP_extract_pure
    (P := bs336_old.length = 336 ∧ oldRecG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline oldRecG oldSs.state (unpack64 oldRecG.localIk.cap ++ bs336_old))
    (by sep_focus) fun ⟨hbs336_old, hcap_old, hinl_old⟩ => ?_
  have hcmn_old : (oldRecG.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCap hcap_old
  wp_steps
  rw [msub400_sub384_eq_bucketAddr_add16 ctrl k hk]
  wp_steps
  rw [msub400_sub392_eq_bucketAddr_add8 ctrl k hk]
  wp_steps
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) HashbrownBin.extHookStack (by decide)]
  wp_call hBcmp ⟨clonedG.name.ptr, peerG.name.ptr, clonedG.name.bytes, peerG.name.bytes⟩
  simp only [‹sf_3.sp = s0.sp - 1312#64›] at *
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) HashbrownBin.extHookStack (by decide)).symm)
    (by sep_focus) ?_
  have hbcmp0 : BitVec.truncate 32 (sf_4.readReg64 (Reg.gpr 0#5)) = 0#32 :=
    ‹BitVec.setWidth 32 (sf_4.readReg64 (Reg.gpr 0#5)) = 0#32 ↔ clonedG.name.bytes = peerG.name.bytes›.mpr hcloned_bytes
  wp_steps
  rw [msub400_sub376_eq_bucketAddr_add24 ctrl k hk]
  wp_steps
  rw [msub400_sub368_eq_bucketAddr_add32 ctrl k hk]
  wp_steps
  refine SepWP.fold (Entails.of_eq (bucket_full368_eq_bytes ctrl k oldRecG.localIk.cap bs336_old))
    (by sep_focus) ?_
  obtain ⟨bs368_old, hdef368_old, hbs368_old⟩ :
      ∃ bs368_old,
        (unpack64 0#64 ++ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 oldRecG.localIk.cap ++ bs336_old)) = bs368_old ∧
        bs368_old.length = 368 :=
    ⟨_, rfl, by simp [unpack64_length, hbs336_old]⟩
  wp_conv_pre => rw [hdef368_old, stackAt_store_sub_eq (s0.sp - 1312#64) 4096 (by decide)]
  refine SepWP.fold (Entails.of_eq (congrArg (memRegion (s0.sp - 528#64)) hbs368_old.symm))
    (by sep_focus) ?_
  wp_call hMemcpy (s0.sp - 528#64, bucketAddr ctrl 400 k + 32#64, bs368_old)
  simp only [‹sf_4.sp = s0.sp - 1312#64›] at *
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) 4096 (by decide)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (hbs368_old ▸ pointsToBytes_entails_memRegion (bucketAddr ctrl 400 k + 32#64) bs368_old)
    (by sep_focus) ?_
  wp_steps
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) 4096 (by decide)]
  refine SepWP.fold (Entails.of_eq (congrArg (memRegion (bucketAddr ctrl 400 k + 32#64)) hbs368_new.symm))
    (by sep_focus) ?_
  wp_call hMemcpy (bucketAddr ctrl 400 k + 32#64, s0.sp - 1232#64, bs368_new)
  simp only [‹sf_5.sp = s0.sp - 1312#64›] at *
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) 4096 (by decide)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (slot80_restore_regions s0.sp bs368_new hbs368_new)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left]
  apply sepWP_exists_elim; intro c104'
  refine SepWP.fold (addrClone_to_dealloc_parts A s0.sp clonedG hcloned_len)
    (by sep_focus) ?_
  refine sepWP_extract_pure (P := clonedG.name.cap ≠ 0#64) (by sep_focus) fun hcap_cloned_ne => ?_
  have hcap_cloned_beq : (clonedG.name.cap == 0#64) = false := beq_false_of_ne hcap_cloned_ne
  wp_steps
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) allocHookStack (by decide)]
  wp_call hDealloc (clonedG.name.ptr, clonedG.name.cap.toNat, 1)
  simp only [‹sf_6.sp = s0.sp - 1312#64›] at *
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) allocHookStack (by decide)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (slot48_restore_region24 s0.sp clonedG.name.cap clonedG.name.ptr 36#64)
    (by sep_focus) ?_
  wp_conv_pre => rw [← hdef368_old]
  refine SepWP.fold (Entails.of_eq (slot784_full368_eq_bytes s0.sp oldRecG.localIk.cap bs336_old).symm)
    (by sep_focus) ?_
  wp_steps
  have h496 : s0.sp - 504#64 + 8#64 = s0.sp - 496#64 := by bv_omega
  wp_conv_pre => rw [← h496]
  refine SepWP.fold (sessionAt_pack_head_tail A (s0.sp - 504#64) oldRecG oldSs hinl_old)
    (by sep_focus) ?_
  refine SepWP.fold (show sessionStateReprAt A (s0.sp - 504#64) oldRecG oldSs ⊢
      sessionStateAt A (s0.sp - 504#64) oldRecG oldSs.state from
    Entails.pure_left fun _ => Entails.refl _) (by sep_focus) ?_
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) dropSessionStructureLocal1Stack (by decide)]
  wp_call hDrop ⟨s0.sp - 504#64, oldRecG, oldSs.state⟩
  simp only [‹sf_7.sp = s0.sp - 1312#64›] at *
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) dropSessionStructureLocal1Stack (by decide)).symm)
    (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (slot784_dropped_restore_regions s0.sp) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A peerG (bucketAddr ctrl 400 k) hpeer_len).symm)
    (by sep_focus) ?_
  wp_conv_pre => rw [← hdef368_new]
  refine SepWP.fold (bucket_entry_of_full368_bytes A ctrl k peerG clonedRecG newSs hcanon_cloned bs336_new hinl_cloned)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (arrayAt_single_split_400 ctrl k hk (sessionBucketEntryAt A peerG clonedRecG newSs)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (table4SingleAt_of_parts A sessionBucketStride mp k0 k1 k hk
    peerG.name.bytes peerG.device (sessionBucketEntryAt A peerG clonedRecG newSs) ctrl
    ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
    (by sep_focus) ?_
  refine SepWP.fold (sessionRecordAt_some_any_prev_of_parts A recPtr newPrevCap newPrevPtr newRecG newSs)
    (by sep_focus) ?_
  refine SepWP.fold (pollUnitResultAt_of_parts sret)
    (by sep_focus) ?_
  refine SepWP.fold (stackAt_store_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  wp_done

end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
