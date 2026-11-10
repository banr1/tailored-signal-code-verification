/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Arm64.Trusted.ISA.Eval
import all Init.Data.Range.Basic
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.Neon
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.RecClone
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreDecodes
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreEmptyHelpers
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.CanonPreservation
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

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
theorem storeSessionEmpty_ok' (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext)
    (hRehash :
      subroutine_ok (RebasedProg b ext)
        ((RebasedProg b ext).fnAddr storeSessionClosureName - bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore as libsignal_protocol::storage::traits::SignedPreKeyStore>::save_signed_pre_key::{closure#0}" + 324))
        (reserveRehashSessionEmptySpec A)) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName)
      (storeSessionEmptySpec A) := by
  have hStrClone := stringClone_ok_at_storeSessionClosure b hHooks
  have hClone := sessionClone_ok_at_storeSessionClosure b hHooks
  have hVecClone := vecVecCloneEmpty_ok_at_storeSessionClosure b hHooks
  have hHash := hashOneAddr36_ok_at_store b ext A
  have hMemcpy := memcpy_ok_at_storeSessionClosure b hHooks
  simp only [storeSessionEmptySpec]
  have hfn : libsignalSessionCode.fnOff storeSessionClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") :=
    (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")) 912
  clear hfn
  dsimp only [RebasedProg, BitVec.ofNat_eq_ofNat] at hStrClone hClone hVecClone hHash hMemcpy hRehash ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr storeSessionClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  wpp_init x s0
  examples_hide_fetches
  obtain ⟨futPtr, sret, base, mp, k0, k1, qAddrPtr, qG, recPtr, recG, ss, prevCap, prevPtr⟩ := x
  dsimp only [StoreSessionEmptyGhost.futPtr, StoreSessionEmptyGhost.sret,
    StoreSessionEmptyGhost.base, StoreSessionEmptyGhost.mp,
    StoreSessionEmptyGhost.k0, StoreSessionEmptyGhost.k1,
    StoreSessionEmptyGhost.qAddrPtr, StoreSessionEmptyGhost.qG,
    StoreSessionEmptyGhost.recPtr, StoreSessionEmptyGhost.recG,
    StoreSessionEmptyGhost.ss, StoreSessionEmptyGhost.prevCap,
    StoreSessionEmptyGhost.prevPtr] at *
  have hq_len : qG.name.bytes.length = 36 := by assumption
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
  wp_conv_pre => rw [emptyTableAt_eq base mp k0 k1]
  wp_conv_pre => rw [sret48_split_eq sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro c_sret0
  wp_conv_pre => rw [stackAt_store_eq s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat' (apply sepWP_exists_elim; intro _)
  wp_conv_pre =>
    rw [protocolAddressAt_eq_vecGhostAt_parts A qG qAddrPtr,
        sessionRecordAt_some_any_prev_eq A recPtr prevCap prevPtr recG ss,
        sessionAt_eq_head_tail A (recPtr + 24#64) recG ss]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro bs336_src
  refine sepWP_extract_pure
    (P := bs336_src.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG ss.state (unpack64 recG.localIk.cap ++ bs336_src))
    (by sep_focus) fun ⟨hbs336_src, hcap_rec, hinl_rec⟩ => ?_
  have hcmn_rec : (recG.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCap hcap_rec
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
  refine SepWP.fold (sessionAt_pack_head_tail A (recPtr + 24#64) recG ss hinl_rec)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_vecGhostAt_parts A qG qAddrPtr).symm)
    (by sep_focus) ?_
  refine SepWP.fold (vecU8_and_dev_entails_protocolAddressAt A s0.sp qG.name.bytes qG.device)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro clonedCap
  apply sepWP_exists_elim; intro clonedPtr
  let clonedG : AddrGhost := ⟨⟨clonedCap, clonedPtr, qG.name.bytes⟩, qG.device⟩
  have hcloned_len : clonedG.name.bytes.length = 36 := hq_len
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) sessionCloneStack (by decide)]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine wpp_call_sessionClone (s0.sp - 528#64) (recPtr + 24#64) (s0.sp - 1312#64) recG ss
    hClone (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp [Arm64.State.spAligned, arm64_norm, *])
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp [arm64_norm, *]) (by simp [arm64_norm, *]) (by sep_focus)
    fun sf_c hpc_c hrun_c hsp_c hcs_c htr_c => ?_
  rw [show entry - 33952#64 = entry + bv% (2 ^ 64 + (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>") - (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")) by bv_omega] at hRehash
  apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>") - (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")))
  obtain ⟨hcs_c19, hcs_c20, hcs_c21, hcs_c22, hcs_c23, hcs_c24, hcs_c25, hcs_c26, hcs_c27, hcs_c28, hcs_c29, hcs_cvregs⟩ := hcs_c
  simp only [arm64_norm, *] at hcs_c19 hcs_c20 hcs_c21 hcs_c22 hcs_c23 hcs_c24 hcs_c25 hcs_c26 hcs_c27 hcs_c28 hcs_c29 hcs_cvregs
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) sessionCloneStack (by decide)).symm)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro clonedRecG
  refine sepWP_extract_pure (P := encSessionMem clonedRecG ss = encSessionMem recG ss)
    (by sep_focus) fun _ => ?_
  refine SepWP.fold (DeserializeGeneral.sessionAt_canon A (s0.sp - 528#64) clonedRecG ss)
    (by sep_focus) ?_
  refine sepWP_extract_pure (P := CanonSession clonedRecG ss)
    (by sep_focus) fun hcanon_cloned => ?_
  have h520 : s0.sp - 528#64 + 8#64 = s0.sp - 520#64 := by bv_omega
  wp_conv_pre => rw [sessionAt_eq_head_tail A (s0.sp - 528#64) clonedRecG ss, h520]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro bs336_new
  refine sepWP_extract_pure
    (P := bs336_new.length = 336 ∧ clonedRecG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline clonedRecG ss.state (unpack64 clonedRecG.localIk.cap ++ bs336_new))
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
  wp_call hVecClone ⟨s0.sp - 1232#64, prevPtr⟩
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
  wp_steps
  refine SepWP.fold (Entails.of_eq (emptyTableAt_eq base mp k0 k1).symm)
    (by sep_focus) ?_
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) reserveRehashStack (by decide)]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine wpp_call_reserveRehash base mp (mp + 32#64) k0 k1 (s0.sp - 1312#64)
    hRehash (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp [Arm64.State.spAligned, arm64_norm, *])
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp [arm64_norm, *]) (by simp [arm64_norm, *]) (by sep_focus)
    fun sf_r hpc_r hrun_r hsp_r hcs_r hx0_r htr_r => ?_
  apply SepWPp.of_sepWP_ret
  obtain ⟨hcs_r19, hcs_r20, hcs_r21, hcs_r22, hcs_r23, hcs_r24, hcs_r25, hcs_r26, hcs_r27, hcs_r28, hcs_r29, hcs_rvregs⟩ := hcs_r
  simp only [arm64_norm, show clonedG.name.bytes = qG.name.bytes from rfl,
    show clonedG.device = qG.device from rfl, *] at hcs_r19 hcs_r20 hcs_r21 hcs_r22 hcs_r23 hcs_r24 hcs_r25 hcs_r26 hcs_r27 hcs_r28 hcs_r29 hcs_rvregs
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) reserveRehashStack (by decide)).symm)
    (by sep_focus) ?_
  wp_conv_pre => rw [table4EmptyAt_eq]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro ctrl
  refine sepWP_extract_pure (by sep_focus) ?_
  rintro ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, _, _, _⟩
  refine SepWP.fold (addrClone_to_4words A s0.sp clonedG hcloned_len) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro w_dev
  refine sepWP_extract_pure
    (P := w_dev.truncate 8 = clonedG.device ∧
      clonedG.name.bytes.length ≤ clonedG.name.cap.toNat ∧
      clonedG.name.cap.toNat < 2 ^ 63 ∧ clonedG.name.ptr ≠ 0)
    (by sep_focus) fun ⟨hw_dev, hcloned_inv⟩ => ?_
  wp_steps
  let hash := hashAddrBv k0 k1 qG.name.bytes qG.device
  let k := (hash &&& 3#64).toNat
  have hk : k < 4 := probePos_3_toNat_lt hash
  have hk_bv : BitVec.ofNat 64 k = hashAddrBv k0 k1 qG.name.bytes qG.device &&& 3#64 := by
    simp [k, hash]
  have hcbs_len : emptyCtrl4.length = 12 := by decide
  have hcbs_split := pointsToBytes_ctrl12_split_at ctrl emptyCtrl4 hcbs_len k hk
  rw [hk_bv] at hcbs_split
  refine SepWP.fold (Entails.of_eq hcbs_split) (by sep_focus) ?_
  refine step_ldrSimd64 (wb := none) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_assumption)
    rfl (by simp [evalAddrMode, extendVal, arm64_norm, *]; rfl)
    (by wp_sep_access_fast) (by wp_norm_lhs) ?_
  refine SepWP.fold (Entails.of_eq hcbs_split.symm) (by sep_focus) ?_
  clear hcbs_split
  wp_steps
  rw [rawMatchTagMask_eq_findGroupIterMask, findGroupIterMask_emptyCtrl4 k hk]
  simp only [beq_self_eq_true, ↓reduceIte]
  have hgrp := loadGroupAt_emptyCtrl4 k hk
  have hclz1 : (bv% (2 ^ 64 - 1)).reverse.clz = 0#64 := by decide +kernel
  have hclz2 : countLeadingZeros (reverseBits (bv% (2 ^ 64 - 1))) = 0 := by decide +kernel
  have humax :
      (Id.run do
        let mut __s := 0#128
        for i in [:8] do
          if __s.ult ((0xffffffffffffffff#128 >>> (i * 8)) &&& 255#128) = true then
            __s := (0xffffffffffffffff#128 >>> (i * 8)) &&& 255#128
          else
            pure ()
        pure __s) = 255#128 := by decide +kernel
  have hand3 : (hashAddrBv k0 k1 qG.name.bytes qG.device &&& 3#64 &&& 3#64) =
      hashAddrBv k0 k1 qG.name.bytes qG.device &&& 3#64 := by
    rw [BitVec.and_assoc]; rfl
  have hmir := sub8_and3_eq k hk
  have hbkt := msub400_sub400_eq_bucketAddr ctrl k hk
  have hbkt1 : ctrl + (0#64 - BitVec.ofNat 64 k * 400#64) - 400#64 = bucketAddr ctrl 400 k := by
    rw [← msub400_sub400_eq_bucketAddr ctrl k hk]; bv_omega
  have hbkt2 : ctrl + -(BitVec.ofNat 64 k * 400#64) - 400#64 = bucketAddr ctrl 400 k := by
    rw [← msub400_sub400_eq_bucketAddr ctrl k hk]; bv_omega
  rw [hk_bv] at hmir hbkt hbkt1 hbkt2
  wp_conv_pre =>
    rw [emptyCtrl4_split_k_and_k8 ctrl k hk,
        hk_bv,
        arrayAt_table4Empty_split_400 ctrl k hk]
  refine SepWP.fold (Entails.of_eq (slot784_split_for_insert s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat' (apply sepWP_exists_elim; intro _)
  wp_steps
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) 4096 (by decide)]
  refine SepWP.fold (Entails.of_eq (congrArg (memRegion (s0.sp - 496#64)) hbs368_new.symm))
    (by sep_focus) ?_
  wp_call hMemcpy (s0.sp - 496#64, s0.sp - 1232#64, bs368_new)
  simp only [hsp_r] at *
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) 4096 (by decide)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (slot80_restore_regions s0.sp bs368_new hbs368_new)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro c104'
  refine SepWP.fold
    (Entails.of_eq (slot784_full400_eq_bytes s0.sp clonedG.name.cap clonedG.name.ptr 36#64 w_dev bs368_new))
    (by sep_focus) ?_
  obtain ⟨bs400, hdef400, hbs400⟩ :
      ∃ bs400,
        (unpack64 clonedG.name.cap ++ unpack64 clonedG.name.ptr ++ unpack64 36#64 ++ unpack64 w_dev ++ bs368_new) = bs400 ∧
        bs400.length = 400 :=
    ⟨_, rfl, by simp [unpack64_length, hbs368_new]⟩
  wp_conv_pre => rw [hdef400]
  wp_steps
  wp_conv_pre => rw [stackAt_store_sub_eq (s0.sp - 1312#64) 4096 (by decide)]
  refine SepWP.fold (Entails.of_eq (congrArg (memRegion (bucketAddr ctrl 400 k)) hbs400.symm))
    (by sep_focus) ?_
  wp_call hMemcpy (bucketAddr ctrl 400 k, s0.sp - 528#64, bs400)
  simp only [‹sf_4.sp = s0.sp - 1312#64›] at *
  refine SepWP.fold (Entails.of_eq (stackAt_store_sub_eq (s0.sp - 1312#64) 4096 (by decide)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (slot784_restore_from_400 s0.sp bs400 hbs400)
    (by sep_focus) ?_
  refine SepWP.fold (slot48_4words_restore s0.sp clonedG.name.cap clonedG.name.ptr 36#64 w_dev)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro c72'
  wp_steps
  have htag1 : BitVec.zeroExtend 8 (hashAddrBv k0 k1 qG.name.bytes qG.device >>> 57) = h2Tag hash :=
    zeroExtend8_ushr57_eq_h2Tag hash
  have hctrl_write := singleCtrl4_of_write_k_and_k8 ctrl k hk (h2Tag hash)
  rw [hk_bv] at hctrl_write
  wp_conv_pre => rw [htag1, ← hdef400, ← hdef368_new]
  refine SepWP.fold (Entails.of_eq hctrl_write)
    (by sep_focus) ?_
  refine SepWP.fold
    (bucket_entry_of_full400_bytes A ctrl k clonedG w_dev hcloned_len hw_dev hcloned_inv
      clonedRecG ss hcanon_cloned bs336_new hinl_cloned)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (arrayAt_single_split_400 ctrl k hk (sessionBucketEntryAt A clonedG clonedRecG ss)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (table4SingleAt_of_parts A sessionBucketStride mp k0 k1 k hk
    qG.name.bytes qG.device (sessionBucketEntryAt A clonedG clonedRecG ss) ctrl
    ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, nofun,
      ctrlMirrorInv_singleCtrl4 k (h2Tag hash),
      fullBucketsInv_singleCtrl4 k hk (h2Tag hash) (h2Tag_msb hash)⟩)
    (by sep_focus) ?_
  refine SepWP.fold (sessionRecordAt_some_any_prev_of_parts A recPtr prevCap prevPtr recG ss)
    (by sep_focus) ?_
  refine SepWP.fold (pollUnitResultAt_of_parts sret)
    (by sep_focus) ?_
  refine SepWP.fold (stackAt_store_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  wp_done

end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
