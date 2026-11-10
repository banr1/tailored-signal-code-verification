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
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.Common
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadDecodes
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.Neon
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.RecClone
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.CanonPreservation
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.SipHashBin
open CryptoVerification.E2E.InMem.HashbrownBin
open Arm64 ProofLib

namespace LoadSingle

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


set_option maxHeartbeats 1600000 in
theorem loadSessionSingle_ok' (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr loadSessionClosureName)
      (loadSessionSingleSpec A) := by
  have hHash := hashOneAddr36_ok_at_load b ext A
  have hBcmp := bcmp_ok_at_loadSessionClosure b hHooks
  have hClone := sessionClone_ok_at_loadSessionClosure b hHooks
  have hVecClone := vecVecCloneEmpty_ok_at_loadSessionClosure b hHooks
  have hMemcpy := memcpy_ok_at_loadSessionClosure b hHooks
  have hMemcpyReg := memcpy_region_ok_at_loadSessionClosure b hHooks
  simp only [loadSessionSingleSpec]
  have hfn : libsignalSessionCode.fnOff loadSessionClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") :=
    (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")) 512
  clear hfn
  dsimp only [RebasedProg, BitVec.ofNat_eq_ofNat] at hHash hBcmp hClone hVecClone hMemcpy hMemcpyReg ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr loadSessionClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  wpp_init x s0
  examples_hide_fetches
  obtain ⟨futPtr, sret, mp, k0, k1, k, peerG, recG, ss, qAddrPtr, qG⟩ := x
  dsimp only [LoadSessionSingleGhost.futPtr, LoadSessionSingleGhost.sret,
    LoadSessionSingleGhost.mp, LoadSessionSingleGhost.k0, LoadSessionSingleGhost.k1,
    LoadSessionSingleGhost.k, LoadSessionSingleGhost.peerG, LoadSessionSingleGhost.recG,
    LoadSessionSingleGhost.ss, LoadSessionSingleGhost.qAddrPtr,
    LoadSessionSingleGhost.qG] at *
  by_cases hkey : qG.name.bytes = peerG.name.bytes ∧ qG.device = peerG.device
  · apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
    wp_conv_pre => rw [table4SingleAt_eq]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply sepWP_exists_elim; intro ctrl
    wp_conv_pre => rw [sret368_split_eq sret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply sepWP_exists_elim; intro c_sret0
    wp_conv_pre => rw [stackAt_load_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (apply sepWP_exists_elim; intro _)
    refine sepWP_extract_pure (P := k < 4) (by sep_focus) fun hk => ?_
    refine sepWP_extract_pure (by sep_focus) ?_
    rintro ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩
    refine step_stpSimd64_sp_pre (by wp_norm_lhs) (by wp_norm_lhs) (by wp_assumption)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_sep_access_fast) (by wp_sep_access_fast) fun _ => ?_
    wp_steps
    wp_conv_pre => rw [stackAt_load_sub_eq (s0.sp - 1200#64) hashOneAddrStack (by decide)]
    wp_call hHash ⟨k0, k1, qAddrPtr, qG⟩
    refine SepWP.fold (Entails.of_eq (stackAt_load_sub_eq (s0.sp - 1200#64) hashOneAddrStack (by decide)).symm)
      (by sep_focus) ?_
    wp_conv_pre => rw [protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)]
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
      rw [arrayAt_single_split_400 ctrl k hk (sessionBucketEntryAt A peerG recG ss)]
    dsimp only [sessionBucketEntryAt, sessionBucketValueOff]
    refine sepWP_extract_pure (P := CanonSession recG ss) (by sep_focus) fun hcanon => ?_
    wp_conv_pre =>
      rw [protocolAddressAt_eq_of_len36 A peerG (bucketAddr ctrl 400 k) (by assumption),
          sessionRecordAt_some_eq A (bucketAddr ctrl 400 k + 32#64) recG ss,
          hoff40, hoff48, hoff56,
          sessionAt_eq_head_tail A (bucketAddr ctrl 400 k + 56#64) recG ss,
          hoff64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply sepWP_exists_elim; intro bs336_rec
    refine sepWP_extract_pure
      (P := bs336_rec.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
        SessionInline recG ss.state (unpack64 recG.localIk.cap ++ bs336_rec))
      (by sep_focus) fun ⟨hbs336_rec, hcap_rec, hinl_rec⟩ => ?_
    have hcmn_rec : (recG.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCap hcap_rec
    wp_steps
    rw [msub400_sub384_eq_bucketAddr_add16 ctrl k hk]
    wp_steps
    rw [msub400_sub392_eq_bucketAddr_add8 ctrl k hk]
    wp_steps
    wp_conv_pre => rw [stackAt_load_sub_eq (s0.sp - 1200#64) HashbrownBin.extHookStack (by decide)]
    wp_call hBcmp ⟨qG.name.ptr, peerG.name.ptr, qG.name.bytes, peerG.name.bytes⟩
    simp only [‹sf.sp = s0.sp - 1200#64›] at *
    refine SepWP.fold (Entails.of_eq (stackAt_load_sub_eq (s0.sp - 1200#64) HashbrownBin.extHookStack (by decide)).symm)
      (by sep_focus) ?_
    have hbcmp0 : BitVec.truncate 32 (sf_1.readReg64 (Reg.gpr 0#5)) = 0#32 :=
      ‹BitVec.setWidth 32 (sf_1.readReg64 (Reg.gpr 0#5)) = 0#32 ↔ qG.name.bytes = peerG.name.bytes›.mpr hkey.1
    wp_steps
    rw [msub400_sub376_eq_bucketAddr_add24 ctrl k hk]
    wp_steps
    rw [msub400_sub344_eq_bucketAddr_add56 ctrl k hk]
    wp_steps
    rw [msub400_sub344_eq_bucketAddr_add56 ctrl k hk]
    wp_steps
    wp_conv_pre => rw [← hoff64]
    refine SepWP.fold (sessionAt_pack_head_tail A (bucketAddr ctrl 400 k + 56#64) recG ss hinl_rec)
      (by sep_focus) ?_
    wp_conv_pre => rw [stackAt_load_sub_eq (s0.sp - 1200#64) sessionCloneStack (by decide)]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine wpp_call_sessionClone (s0.sp - 824#64) (bucketAddr ctrl 400 k + 56#64) (s0.sp - 1200#64) recG ss
      hClone (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp [Arm64.State.spAligned, arm64_norm, *])
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp [arm64_norm, *]) (by simp [arm64_norm, *]) (by sep_focus)
      fun sf_c hpc_c hrun_c hsp_c hcs_c htr_c => ?_
    apply SepWPp.of_sepWP_ret
    obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcs_vregs⟩ := hcs_c
    simp only [arm64_norm, *] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hcs_vregs
    refine SepWP.fold (Entails.of_eq (stackAt_load_sub_eq (s0.sp - 1200#64) sessionCloneStack (by decide)).symm)
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply sepWP_exists_elim; intro G'
    refine sepWP_extract_pure (P := encSessionMem G' ss = encSessionMem recG ss) (by sep_focus) fun _ => ?_
    refine SepWP.fold (DeserializeGeneral.sessionAt_canon A (s0.sp - 824#64) G' ss) (by sep_focus) ?_
    refine sepWP_extract_pure (P := CanonSession G' ss) (by sep_focus) fun hcanon' => ?_
    have h816 : s0.sp - 824#64 + 8#64 = s0.sp - 816#64 := by bv_omega
    wp_conv_pre => rw [sessionAt_eq_head_tail A (s0.sp - 824#64) G' ss, h816]
    simp only [sepExists_sepConj_left]
    apply sepWP_exists_elim; intro bs336
    refine sepWP_extract_pure
      (P := bs336.length = 336 ∧ G'.localIk.cap.toNat < 2 ^ 63 ∧
        SessionInline G' ss.state (unpack64 G'.localIk.cap ++ bs336))
      (by sep_focus) fun ⟨hbs336, hcap', hinl'⟩ => ?_
    wp_steps
    wp_conv_pre => rw [stackAt_load_sub_eq (s0.sp - 1200#64) 4096 (by decide), ← hbs336]
    wp_call hMemcpy (s0.sp - 456#64, s0.sp - 816#64, bs336)
    simp only [hsp_c] at *
    refine SepWP.fold (Entails.of_eq (stackAt_load_sub_eq (s0.sp - 1200#64) 4096 (by decide)).symm)
      (by sep_focus) ?_
    refine SepWP.fold (slot376_to_vec_and_tail s0.sp G'.localIk.cap bs336 hbs336)
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply sepWP_exists_elim; intro c400
    wp_steps
    rw [msub400_sub360_eq_bucketAddr_add40 ctrl k hk]
    wp_steps
    rw [msub400_sub352_eq_bucketAddr_add48 ctrl k hk]
    wp_steps
    wp_conv_pre => rw [stackAt_load_sub_eq (s0.sp - 1200#64) vecVecCloneStack (by decide)]
    wp_call hVecClone ⟨s0.sp - 824#64, 8#64⟩
    simp only [‹sf_2.sp = s0.sp - 1200#64›] at *
    refine SepWP.fold (Entails.of_eq (stackAt_load_sub_eq (s0.sp - 1200#64) vecVecCloneStack (by decide)).symm)
      (by sep_focus) ?_
    dsimp only [vecHeader]
    have h808 : s0.sp - 824#64 + 16#64 = s0.sp - 808#64 := by bv_omega
    wp_conv_pre => rw [h816, h808]
    wp_steps
    wp_conv_pre => rw [stackAt_load_sub_eq (s0.sp - 1200#64) 4096 (by decide), ← hbs336]
    wp_call hMemcpy (s0.sp - 792#64, s0.sp - 456#64, bs336)
    simp only [‹sf_3.sp = s0.sp - 1200#64›] at *
    refine SepWP.fold (Entails.of_eq (stackAt_load_sub_eq (s0.sp - 1200#64) 4096 (by decide)).symm)
      (by sep_focus) ?_
    refine SepWP.fold (hbs336 ▸ pointsToBytes_entails_memRegion (s0.sp - 456#64) bs336)
      (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (slot376_tail360_eq_bytes s0.sp G'.localIk.cap bs336))
      (by sep_focus) ?_
    obtain ⟨bs360, hdef360, hbs360⟩ :
        ∃ bs360,
          (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 G'.localIk.cap ++ bs336) = bs360 ∧
          bs360.length = 360 :=
      ⟨_, rfl, by simp [unpack64_length, hbs336]⟩
    wp_conv_pre => rw [hdef360]
    wp_steps
    wp_conv_pre => rw [stackAt_load_sub_eq (s0.sp - 1200#64) 4096 (by decide)]
    refine SepWP.fold (Entails.of_eq (congrArg (memRegion (s0.sp - 1184#64)) hbs360.symm))
      (by sep_focus) ?_
    wp_call hMemcpy (s0.sp - 1184#64, s0.sp - 816#64, bs360)
    simp only [‹sf_4.sp = s0.sp - 1200#64›] at *
    refine SepWP.fold (Entails.of_eq (stackAt_load_sub_eq (s0.sp - 1200#64) 4096 (by decide)).symm)
      (by sep_focus) ?_
    refine SepWP.fold (slot376_restore_regions s0.sp bs360 hbs360)
      (by sep_focus) ?_
    wp_steps
    wp_conv_pre => rw [stackAt_load_sub_eq (s0.sp - 1200#64) 4096 (by decide)]
    refine SepWP.fold (Entails.of_eq (congrArg (memRegion (sret + 8#64)) hbs360.symm))
      (by sep_focus) ?_
    wp_call hMemcpy (sret + 8#64, s0.sp - 1184#64, bs360)
    simp only [‹sf_5.sp = s0.sp - 1200#64›] at *
    refine SepWP.fold (Entails.of_eq (stackAt_load_sub_eq (s0.sp - 1200#64) 4096 (by decide)).symm)
      (by sep_focus) ?_
    refine SepWP.fold (hbs360 ▸ pointsToBytes_entails_memRegion (s0.sp - 1184#64) bs360)
      (by sep_focus) ?_
    wp_steps
    refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A peerG (bucketAddr ctrl 400 k) (by assumption)).symm)
      (by sep_focus) ?_
    refine SepWP.fold (bucket_entry_of_parts A ctrl k peerG recG ss hcanon)
      (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (arrayAt_single_split_400 ctrl k hk (sessionBucketEntryAt A peerG recG ss)).symm)
      (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)).symm)
      (by sep_focus) ?_
    wp_conv_pre => rw [← hdef360]
    refine SepWP.fold (pollOptSessionRecordResultAt_some_of_parts A sret G' ss hcanon' bs336 ⟨hbs336, hcap', hinl'⟩)
      (by sep_focus) ?_
    refine SepWP.fold (table4SingleAt_of_parts A sessionBucketStride mp k0 k1 k hk
      peerG.name.bytes peerG.device (sessionBucketEntryAt A peerG recG ss) ctrl
      ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
      (by sep_focus) ?_
    refine SepWP.fold (stackAt_load_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by sep_focus) ?_
    simp only [hkey, and_self, ↓reduceIte]
    wp_done
  · apply SepWPp.of_sepWP_ret
    wp_conv_pre => rw [table4SingleAt_eq]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply sepWP_exists_elim; intro ctrl
    wp_conv_pre => rw [sret368_split_eq sret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply sepWP_exists_elim; intro c_sret0
    wp_conv_pre => rw [stackAt_load_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (apply sepWP_exists_elim; intro _)
    refine sepWP_extract_pure (P := k < 4) (by sep_focus) fun hk => ?_
    refine sepWP_extract_pure (by sep_focus) ?_
    rintro ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩
    refine step_stpSimd64_sp_pre (by wp_norm_lhs) (by wp_norm_lhs) (by wp_assumption)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_sep_access_fast) (by wp_sep_access_fast) fun _ => ?_
    wp_norm_state
    wp_steps
    wp_conv_pre => rw [stackAt_load_sub_eq (s0.sp - 1200#64) hashOneAddrStack (by decide)]
    wp_call hHash ⟨k0, k1, qAddrPtr, qG⟩
    refine SepWP.fold (Entails.of_eq (stackAt_load_sub_eq (s0.sp - 1200#64) hashOneAddrStack (by decide)).symm)
      (by sep_focus) ?_
    wp_conv_pre => rw [protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)]
    wp_steps
    let pos := (hashAddrBv k0 k1 qG.name.bytes qG.device &&& 3#64).toNat
    have hpos_lt : pos < 4 :=
      probePos_3_toNat_lt (hashAddrBv k0 k1 qG.name.bytes qG.device)
    have hpos_bv : BitVec.ofNat 64 pos = hashAddrBv k0 k1 qG.name.bytes qG.device &&& 3#64 := by
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
    wp_steps
    rw [rawMatchTagMask_eq_findGroupIterMask]
    wp_if hmask
    · wp_steps
      wp_if hemp
      · wp_steps
        wp_conv_pre => rw [memRegion_eq_exists_bytes (s0.sp - 1184#64) 360 (by decide)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply sepWP_exists_elim; intro bs_uninit
        refine sepWP_extract_pure (P := bs_uninit.length = 360) (by sep_focus) fun hbs_uninit => ?_
        wp_call hMemcpyReg (sret + 8#64, s0.sp - 1184#64, bs_uninit)
        simp only [‹sf.sp = s0.sp - 1200#64›] at *
        refine SepWP.fold (hbs_uninit ▸ pointsToBytes_entails_memRegion (sret + 8#64) bs_uninit)
          (by sep_focus) ?_
        refine SepWP.fold (hbs_uninit ▸ pointsToBytes_entails_memRegion (s0.sp - 1184#64) bs_uninit)
          (by sep_focus) ?_
        wp_steps
        simp only [hkey, ↓reduceIte]
        refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)).symm)
          (by sep_focus) ?_
        refine SepWP.fold (pollOptSessionRecordResultAt_none_of_parts A sret)
          (by sep_focus) ?_
        refine SepWP.fold (table4SingleAt_of_parts A sessionBucketStride mp k0 k1 k hk
          peerG.name.bytes peerG.device (sessionBucketEntryAt A peerG recG ss) ctrl
          ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
          (by sep_focus) ?_
        refine SepWP.fold (stackAt_load_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus) ?_
        wp_done
      · exfalso
        dsimp only [singleCtrl4] at hemp
        exact hemp (evalUmaxv_matchEmpty_mkCtrl4_getLsbD_zero _ _ _ _ pos hpos_lt)
    · have hmask_eq := findGroupIterMask_singleCtrl4_ne_zero_eq k0 k1 k pos hk hpos_lt
        peerG.name.bytes qG.name.bytes peerG.device qG.device hmask
      have hprobe := eval_probeBucket_singleCtrl4' k pos hk hpos_lt
      have hclear := eval_clearLowestBit_laneBit_sub k pos hk hpos_lt
      rw [hpos_bv] at hprobe
      rw [hmask_eq]
      wp_conv_pre =>
        rw [arrayAt_single_split_400 ctrl k hk (sessionBucketEntryAt A peerG recG ss)]
      dsimp only [sessionBucketEntryAt, sessionBucketValueOff]
      refine sepWP_extract_pure (P := CanonSession recG ss) (by sep_focus) fun hcanon => ?_
      wp_conv_pre =>
        rw [protocolAddressAt_eq_of_len36 A peerG (bucketAddr ctrl 400 k) (by assumption)]
      wp_steps
      rw [msub400_sub384_eq_bucketAddr_add16 ctrl k hk]
      wp_steps
      rw [msub400_sub392_eq_bucketAddr_add8 ctrl k hk]
      wp_steps
      wp_conv_pre => rw [stackAt_load_sub_eq (s0.sp - 1200#64) HashbrownBin.extHookStack (by decide)]
      wp_call hBcmp ⟨qG.name.ptr, peerG.name.ptr, qG.name.bytes, peerG.name.bytes⟩
      simp only [‹sf.sp = s0.sp - 1200#64›] at *
      refine SepWP.fold (Entails.of_eq (stackAt_load_sub_eq (s0.sp - 1200#64) HashbrownBin.extHookStack (by decide)).symm)
        (by sep_focus) ?_
      have hv9 : sf_1.readVReg128 9#5 =
          BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerG.name.bytes peerG.device))) pos) := by
        rw [readVReg128_of_vregs_eq ‹sf_1.vregs = _› 9#5]
        simp only [arm64_norm]
      wp_steps
      wp_if hbcmp
      · wp_steps
        wp_if hemp2
        · wp_steps
          wp_conv_pre => rw [memRegion_eq_exists_bytes (s0.sp - 1184#64) 360 (by decide)]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply sepWP_exists_elim; intro bs_uninit
          refine sepWP_extract_pure (P := bs_uninit.length = 360) (by sep_focus) fun hbs_uninit => ?_
          wp_call hMemcpyReg (sret + 8#64, s0.sp - 1184#64, bs_uninit)
          simp only [‹sf_1.sp = s0.sp - 1200#64›] at *
          refine SepWP.fold (hbs_uninit ▸ pointsToBytes_entails_memRegion (sret + 8#64) bs_uninit)
            (by sep_focus) ?_
          refine SepWP.fold (hbs_uninit ▸ pointsToBytes_entails_memRegion (s0.sp - 1184#64) bs_uninit)
            (by sep_focus) ?_
          wp_steps
          simp only [hkey, ↓reduceIte]
          refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A peerG (bucketAddr ctrl 400 k) (by assumption)).symm)
            (by sep_focus) ?_
          have hentry :
              (protocolAddressAt A peerG (bucketAddr ctrl 400 k) ∗
                sessionRecordAt A (bucketAddr ctrl 400 k + 32#64) ⟨0#64, 8#64, some recG⟩ ⟨some ss⟩) ⊢
              sessionBucketEntryAt A peerG recG ss (bucketAddr ctrl 400 k) := by
            dsimp only [sessionBucketEntryAt, sessionBucketValueOff]
            exact Entails.pure_right hcanon (Entails.refl _)
          refine SepWP.fold hentry (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (arrayAt_single_split_400 ctrl k hk (sessionBucketEntryAt A peerG recG ss)).symm)
            (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)).symm)
            (by sep_focus) ?_
          refine SepWP.fold (pollOptSessionRecordResultAt_none_of_parts A sret)
            (by sep_focus) ?_
          refine SepWP.fold (table4SingleAt_of_parts A sessionBucketStride mp k0 k1 k hk
            peerG.name.bytes peerG.device (sessionBucketEntryAt A peerG recG ss) ctrl
            ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
            (by sep_focus) ?_
          refine SepWP.fold (stackAt_load_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by sep_focus) ?_
          wp_done
        · exfalso
          dsimp only [singleCtrl4] at hemp2
          exact hemp2 (evalUmaxv_matchEmpty_mkCtrl4_getLsbD_zero _ _ _ _ pos hpos_lt)
      · wp_steps
        rw [msub400_sub376_eq_bucketAddr_add24 ctrl k hk]
        wp_steps
        wp_if hdev
        · exfalso
          have hname : qG.name.bytes = peerG.name.bytes := by
            have h0 : BitVec.setWidth 32 (sf_1.readReg64 (Reg.gpr 0#5)) = 0#32 := by
              have := congrArg (BitVec.setWidth 32) hbcmp
              simpa using this
            rwa [← ‹BitVec.setWidth 32 (sf_1.readReg64 (Reg.gpr 0#5)) = 0#32 ↔ qG.name.bytes = peerG.name.bytes›]
          have hdev_eq : qG.device = peerG.device := by
            have := congrArg (BitVec.setWidth 8) hdev
            simpa using this
          exact hkey ⟨hname, hdev_eq⟩
        · wp_steps
          wp_if hemp3
          · wp_steps
            wp_conv_pre => rw [memRegion_eq_exists_bytes (s0.sp - 1184#64) 360 (by decide)]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply sepWP_exists_elim; intro bs_uninit
            refine sepWP_extract_pure (P := bs_uninit.length = 360) (by sep_focus) fun hbs_uninit => ?_
            wp_call hMemcpyReg (sret + 8#64, s0.sp - 1184#64, bs_uninit)
            simp only [‹sf_1.sp = s0.sp - 1200#64›] at *
            refine SepWP.fold (hbs_uninit ▸ pointsToBytes_entails_memRegion (sret + 8#64) bs_uninit)
              (by sep_focus) ?_
            refine SepWP.fold (hbs_uninit ▸ pointsToBytes_entails_memRegion (s0.sp - 1184#64) bs_uninit)
              (by sep_focus) ?_
            wp_steps
            simp only [hkey, ↓reduceIte]
            refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A peerG (bucketAddr ctrl 400 k) (by assumption)).symm)
              (by sep_focus) ?_
            have hentry :
                (protocolAddressAt A peerG (bucketAddr ctrl 400 k) ∗
                  sessionRecordAt A (bucketAddr ctrl 400 k + 32#64) ⟨0#64, 8#64, some recG⟩ ⟨some ss⟩) ⊢
                sessionBucketEntryAt A peerG recG ss (bucketAddr ctrl 400 k) := by
              dsimp only [sessionBucketEntryAt, sessionBucketValueOff]
              exact Entails.pure_right hcanon (Entails.refl _)
            refine SepWP.fold hentry (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (arrayAt_single_split_400 ctrl k hk (sessionBucketEntryAt A peerG recG ss)).symm)
              (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)).symm)
              (by sep_focus) ?_
            refine SepWP.fold (pollOptSessionRecordResultAt_none_of_parts A sret)
              (by sep_focus) ?_
            refine SepWP.fold (table4SingleAt_of_parts A sessionBucketStride mp k0 k1 k hk
              peerG.name.bytes peerG.device (sessionBucketEntryAt A peerG recG ss) ctrl
              ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
              (by sep_focus) ?_
            refine SepWP.fold (stackAt_load_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by sep_focus) ?_
            wp_done
          · exfalso
            dsimp only [singleCtrl4] at hemp3
            exact hemp3 (evalUmaxv_matchEmpty_mkCtrl4_getLsbD_zero _ _ _ _ pos hpos_lt)

end LoadSingle

end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
