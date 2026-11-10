/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStaleness
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTail
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyStale
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyBody
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyStale
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# CLI MessageEncrypt `WithStoresVT` (Part 5): `SegPreKey` prefix helpers on `trTrapProgAt`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.Cli.LibsignalPublicApi (encryptWithStoresName)

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section SegPreKeyPrefix

private theorem h45_poll_unackItems_pack_pollWithBaseKey_trap (sp : BitVec 64) (items : PendingPreKey)
    (ts : SystemTime) :
    (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 88 ∗
      memRegion (sp + 0x5d8#64) 0x298 ∗
      memRegion (sp + 0x870#64) 36 ∗
      memRegion (sp + 0x894#64) 0x21c ∗
      memRegion (sp + 0xab0#64) 4 ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0x2c ∗
      ((sp + 0xb00#64) ↦₆₄ ts.tvSec) ∗
      ((sp + 0xb08#64) ↦₃₂ ts.tvNsec) ∗
      memRegion (sp + 0xb0c#64) 4 ∗
      memRegion (sp + 0xb10#64) 0x70) ⊢
    Pf.SegPreKey.pollWithBaseKey_trap sp items ts := by
  unfold Pf.SegPreKey.pollWithBaseKey_trap
  rw [mr_cut_add sp 0x46a 0x116 0x534 (by decide),
      mr_cut_add sp 0x580 88 0x4dc (by decide),
      mr_cut_add sp 0x5d8 0x298 0x244 (by decide),
      mr_cut_add sp 0x870 36 0x220 (by decide),
      mr_cut_add sp 0x894 0x21c 4 (by decide)]
  simp only [sepConj_assoc]
  exact Entails.refl _

private theorem h45_pollWithBaseKey_dur_unpack_trap (sp : BitVec 64) (items : PendingPreKey)
    (ts : SystemTime) :
    Pf.SegPreKey.pollWithBaseKey_trap sp items ts =
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 24 ∗
      memRegion (sp + 0x598#64) 0x300 ∗
      memRegion (sp + 0x898#64) 8 ∗
      memRegion (sp + 0x8a0#64) 0x214 ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0x2c ∗
      ((sp + 0xb00#64) ↦₆₄ ts.tvSec) ∗
      ((sp + 0xb08#64) ↦₃₂ ts.tvNsec) ∗
      memRegion (sp + 0xb0c#64) 4 ∗
      memRegion (sp + 0xb10#64) 0x70 := by
  unfold Pf.SegPreKey.pollWithBaseKey_trap
  rw [mr_cut_add sp 0x46a 0x116 0x534 (by decide),
      mr_cut_add sp 0x580 24 0x51c (by decide),
      mr_cut_add sp 0x598 0x300 0x21c (by decide),
      mr_cut_add sp 0x898 8 0x214 (by decide)]
  simp only [sepConj_assoc]

private theorem h45_durationSinceBounded_b00_intro_trap (sp : BitVec 64) (tvSec : BitVec 64)
    (tvNsec : BitVec 32) (hns : tvNsec.toNat < 1000000000) :
    (((sp + 0xb00#64) ↦₆₄ tvSec) ∗ ((sp + 0xb08#64) ↦₃₂ tvNsec) ∗ memRegion (sp + 0xb0c#64) 4) ⊢
      (∃∗ tvSec : BitVec 64, ∃∗ tvNsec : BitVec 32,
        ⌜tvNsec.toNat < 1000000000⌝ ∗
        ((sp + 0xb00#64) ↦₆₄ tvSec) ∗ (((sp + 0xb00#64) + 8#64) ↦₃₂ tvNsec) ∗
        memRegion ((sp + 0xb00#64) + 12#64) 4) := by
  have h := CryptoVerification.SignalSession.Cli.Slots.durationSinceBounded_self_intro
    (sp + 0xb00#64) tvSec tvNsec hns
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_unackItems_to_dur_ok_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (hpk : sess.pendingPreKey = some items)
    (hkey : KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => ∃ prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen,
        Pf.SegPreKey.StalenessDurState_trap kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s') := by
  rcases hkey with ⟨hcur, hscope, hotr, hrem, hpc, hmeta, htr, hregs, hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hregs with ⟨hx0, hx8, hx20, hx22, hx23, hx25, hx26, hx27, hx28⟩
  have hmeta' := hmeta
  rcases hmeta' with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hfrozen, hsym, hvregs⟩
  rw [sp_sub_60_eq_add_b80 s0.sp] at hx29
  set sp := s0.sp - 0xbe0#64
  change s.pc = encEntry img + 836#64 at hpc
  apply Pf.SegPreKey.segExit_of_sepWPp_callInv_trap ⟨hfrozen, hsym⟩
    (target := (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 1732#64)
    (encSeam_mem_group hmem)
  dsimp only [takenSlots, encCommon]
  rw [poll_unackItems_regions sp, encSubStack_split_unack hsp]
  refine SepWPp.fold (takenRecord_sessionRecordAt_unpack A sp sess taken) (by sep_focus) ?_
  refine sepWPp_elim_ex fun prevCap => sepWPp_elim_ex fun prevPtr => sepWPp_elim_ex fun G => ?_
  have henc_fn := Pf.SegPreKey.encEntry_eq_fnAddr_trap (h45_envF hEnv)
  rw [henc_fn] at hpc
  have hunack := henc_fn ▸ Pf.SegPreKey.unack_ok_at_enc_trap (h45_envF hEnv)
  clear hEnv
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x344 0x4c
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x680 0x44
  dsimp only [trTrapProgAt] at hpc hunack henc_fn ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  apply Pf.SegPreKey.SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
  wp_step
  apply SepWP.done (by simp_all) (by simp_all)
  refine Pf.SegPreKey.SepWPp.call_frame hunack
    (x := (⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ : UnackCall))
    (ret_pc := entry + 840#64)
    (by simp_all) (by simp_all) hspAl rfl rfl ⟨by simp_all, by simp_all⟩
    (by dsimp [State.sp, State.setPC, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sf _ hm => by rw [sepConj_assoc] at hm; exact Pf.SegPreKey.onPanic_of_unack htr hcur hscope hotr hrem hpk hm)
    fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
  dsimp only [unackItemsSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  have hcs1' := calleeSavedPreserved_after_bl hcs1; clear hcs1
  rcases hcs1' with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
  rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
  rw [sp_after_bl] at hsp1
  rw [trace_after_bl] at htr1
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hspAl ⊢; rwa [hsp1]
  rw [hsp] at hsp1
  rw [htr] at htr1
  refine SepWPp.fold (unackOutAt_taken_some sp G.kyber sess items hpk) (by sep_focus) ?_
  refine sepWPp_elim_ex fun ts => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hts => ?_
  refine sepWPp_fold_ex1 (optU32At_unpack32 (sp + 0x580#64) items.preKeyId) (by sep_focus)
    fun pkVal hpkVal => ?_
  refine sepWPp_fold_ex1 (optU32At_unpack64 (sp + 0x588#64) (sess.pendingKyberPreKey.map (·.preKeyId)))
    (by sep_focus) fun kyIdVal hkyIdVal => ?_
  refine sepWPp_fold_ex5 (baseKeyShift_unpack_59c sp items.baseKey) (by sep_focus)
    fun bk0 bk1 bk2 bk3 bk4 hbk => ?_
  refine sepWPp_fold_ex2 (unackKyberSliceAt_unpack (sp + 0x5c0#64) G.kyber) (by sep_focus)
    fun kyPtr kyLen hkySlice => ?_
  refine SepWPp.fold (curScratch_unackItems_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun s48 => sepWPp_elim_ex fun s40 => sepWPp_elim_ex fun s38 =>
    sepWPp_elim_ex fun s34 => sepWPp_elim_ex fun s28 => sepWPp_elim_ex fun s24 =>
    sepWPp_elim_ex fun s18 => ?_
  refine SepWPp.fold (memRegion_36_unpack (sp + 0x870#64)) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w890 => sepWPp_elim_ex fun w888 => sepWPp_elim_ex fun w880 =>
    sepWPp_elim_ex fun w878 => sepWPp_elim_ex fun w870 => ?_
  refine SepWPp.fold (memRegion_36_unpack (sp + 0xab0#64)) (by sep_focus) ?_
  refine sepWPp_elim_ex fun wad0 => sepWPp_elim_ex fun wac8 => sepWPp_elim_ex fun wac0 =>
    sepWPp_elim_ex fun wab8 => sepWPp_elim_ex fun wab0 => ?_
  refine SepWPp.fold (memRegion_16_ts_unpack_b00 sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun wb08 => sepWPp_elim_ex fun wb00 => ?_
  apply Pf.SegPreKey.SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.fold (baseKeyShift_pack_ab0 sp items.baseKey bk0 bk1 bk2 bk3 bk4 hbk) (by sep_focus) ?_
  refine SepWP.fold (cells36_entails_memRegion_36_870 sp bk0 bk1 bk2 bk3 bk4) (by sep_focus) ?_
  refine SepWP.fold
    (unackOut_cells_entails_memRegion_88_580 sp _ pkVal _ ts.tvSec ts.tvNsec bk0 bk1 bk2 bk3 bk4 kyPtr kyLen items.signedPreKeyId)
    (by sep_focus) ?_
  refine SepWP.fold (h45_poll_unackItems_pack_pollWithBaseKey_trap sp items ts) (by sep_focus) ?_
  refine sepWP_fold_preKeyScratch sp kyLen _ items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey
    (by sep_focus) (by rfl) ?_
  refine SepWP.fold (encSubStack_pack_unack hsp (entry + 840#64) (entry + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv hmf
  dsimp only [Pf.SegPreKey.StalenessDurState_trap, sp] at hsp1 hx19_1 hx20_1 hx22_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
  refine ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen,
    hts, hpkVal, hkyIdVal, hkySlice, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
  · rw [henc_fn]; wp_norm_goal
  · refine ⟨by wp_norm_goal, by wp_norm_goal, hsp0Al,
      by unfold State.spAligned at hsp0Al ⊢; wp_norm_goal; exact hsp0Al,
      by rw [sp_sub_60_eq_add_b80 s0.sp]; wp_norm_goal,
      by wp_norm_goal, hinv.1, hinv.2, by wp_norm_goal⟩
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · cases items.preKeyId <;> wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · dsimp only [encCommon, encSpillsAtV] at hmf ⊢; arm64_sep_close

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_staleness_to_add_ok_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R0 : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hdur : Pf.SegPreKey.StalenessDurState_trap kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => ∃ expiry,
        Pf.SegPreKey.StalenessAddState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R0 s0 s') := by
  rcases hdur with ⟨hts, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx2, hx8, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hfrozen, hsym, hvregs⟩
  have hts_nsec : ts.tvNsec.toNat < 10 ^ 9 := (unixEpoch_checkedAddSecs_tvNsec hts).2
  set sp := s0.sp - 0xbe0#64
  change s.pc = encEntry img + 1732#64 at hpc
  apply Pf.SegPreKey.segExit_of_sepWPp_callInv_trap ⟨hfrozen, hsym⟩
    (target := (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 1788#64)
    (dur_mem_group hmem)
  dsimp only [encCommon]
  rw [h45_pollWithBaseKey_dur_unpack_trap sp items ts, encSubStack_split_ext hsp]
  refine SepWPp.fold (h45_durationSinceBounded_b00_intro_trap sp ts.tvSec ts.tvNsec hts_nsec) (by sep_focus) ?_
  have henc_fn := Pf.SegPreKey.encEntry_eq_fnAddr_trap (h45_envF hEnv)
  rw [henc_fn] at hpc
  have hdur_call := henc_fn ▸ Pf.SegPreKey.durationSince_ok_at_enc_trap (h45_envF hEnv)
  have hadd_call := henc_fn ▸ Pf.SegPreKey.timeAdd_ok_at_enc_trap (h45_envF hEnv)
  clear hEnv
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x6c4 0x38
  dsimp only [trTrapProgAt] at hpc hdur_call hadd_call henc_fn ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  apply Pf.SegPreKey.SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<std::time::SystemTime>::duration_since" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
  wp_step
  apply SepWP.done (by simp_all) (by simp_all)
  refine Pf.SegPreKey.SepWPp.call_frame hdur_call
    (x := (sp + 0xb00#64, sp + 0x580#64))
    (ret_pc := entry + 1736#64)
    (by simp_all) (by simp_all) hspAl rfl rfl
    ⟨by simp_all, by simp_all, by dsimp [State.setPC, State.writeReg64, State.readReg64, Reg.x2] at hx2 ⊢; rw [hx2]; decide⟩
    (by dsimp [State.sp, State.setPC, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ hm => by
      dsimp only [CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec, Spec.onPanic] at hm
      rw [sepConj_assoc] at hm
      exact (not_satisfies_false_sepConj hm).elim)
    fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
  dsimp only [CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
  have hcs1' := calleeSavedPreserved_after_bl hcs1; clear hcs1
  rcases hcs1' with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1; rw [hx23] at hx23_1
  rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
  have hx21_1' : (s1.readReg64 .x21).setWidth 32 = ts.tvNsec := by
    change (s1.readReg64 (.gpr 21#5)).setWidth 32 = ts.tvNsec; rw [hx21_1]; exact hx21
  have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
  rw [sp_after_bl] at hsp1
  rw [trace_after_bl] at htr1
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hspAl ⊢; rwa [hsp1]
  rw [hsp] at hsp1
  rw [htr] at htr1
  refine SepWPp.fold (dur_ret_24_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  refine SepWPp.fold (memRegion_8_898_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w898 => ?_
  apply Pf.SegPreKey.SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine Pf.SegPreKey.SepWPp.call_frame hadd_call
    (x := (ts, maxUnacknowledgedSessionAge))
    (ret_pc := entry + 1788#64)
    (by wp_norm_goal) (by wp_norm_goal)
    (by unfold State.spAligned at hsp1_al ⊢; rw [hsp1] at hsp1_al; wp_norm_goal)
    rfl rfl
    ⟨by wp_norm_goal, by wp_norm_goal, hts_nsec, by wp_norm_goal, by wp_norm_goal⟩
    (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sf _ hm => by
      rw [sepConj_assoc] at hm
      refine Pf.SegPreKey.onPanic_of_timeAdd (s := _) ?_ hcur hscope hotr hrem hpk hts hm
      wp_norm_goal)
    fun s2 hpc2 hstat2 hsp2 hcs2 => ?_
  dsimp only [timeAddSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hexp, htr2⟩ => ?_
  refine SepWPp.fold (stackAt_eq_sp hsp2) (by sep_focus) ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, arm64_norm]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2 hsp2 htr2
  rw [hx19_1] at hx19_2; rw [hx20_1] at hx20_2; rw [hx22_1] at hx22_2; rw [hx23_1] at hx23_2
  rw [hx25_1] at hx25_2; rw [hx26_1] at hx26_2; rw [hx27_1] at hx27_2; rw [hx28_1] at hx28_2; rw [hx29_1] at hx29_2; rw [hvregs_1] at hvregs_2
  have hx21_2' : (s2.readReg64 .x21).setWidth 32 = ts.tvNsec := by
    change (s2.readReg64 (.gpr 21#5)).setWidth 32 = ts.tvNsec; rw [hx21_2]; exact hx21_1'
  have hx24_2' : (s2.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    change (s2.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_2]; exact hx24_1'
  rw [hsp1] at hsp2
  rw [htr1] at htr2
  apply Pf.SegPreKey.SepWPp.of_sepWP_ret
  refine SepWP.fold (pollWithBaseKey_dur_pack sp items w580 w588 _) (by sep_focus) ?_
  have hsp2_pack :
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        stackAt s2.sp extHookStack) ⊢ stackAt sp encSubStack := by
    rw [hsp2, ← encSubStack_split_ext rfl]
    exact Entails.refl _
  refine SepWP.fold hsp2_pack (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv hmf
  dsimp only [Pf.SegPreKey.StalenessAddState, sp] at hsp2 hx19_2 hx20_2 hx22_2 hx25_2 hx26_2 hx28_2 hx29_2 hvregs_2 hmf ⊢
  refine ⟨⟨s2.readReg64 .x0, (s2.readReg64 .x1).setWidth 32⟩,
    hts, hexp, hpkVal, hkyIdVal, hkySlice, ?_, ?_, htr2, rfl, rfl,
    hx20_2, hx21_2', hx22_2, hx23_2, hx24_2', hx25_2, hx26_2, hx27_2, hx28_2,
    hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
  · rw [henc_fn]; exact hpc2
  · refine ⟨hstat2, hsp2, hsp0Al,
      by unfold State.spAligned at hsp0Al ⊢; rw [hsp2]; wp_norm_goal,
      hx29_2, hx19_2, hinv.1, hinv.2, hvregs_2⟩
  · dsimp only [encCommon] at hmf ⊢; arm64_sep_close

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_stale_ok_trap
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hlt : expiry.lt x.now = true)
    (hadd : Pf.SegPreKey.StalenessAddState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  let envF := h45_envF hEnv
  rcases hadd with ⟨hts, hexp, _hpkVal, _hkyIdVal, _hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, _hx23, _hx24, hx25, hx26, _hx27, hx28,
    _hptlen, _hrestlen, _hlocA, _hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hfrozen, hsym, hvregs⟩
  have ⟨hmod, hdraws⟩ := model_of_stale (C := C) (S := S) (x := x)
    hcur hotr hrem hpk hts hexp hlt
  set sp := s0.sp - 0xbe0#64
  apply Pf.SegPreKey.segExit_trans_trap
    (mid := fun sf =>
      ∃ cap ptr devWord,
        devWord.setWidth 8 = x.rem.device ∧
        sf.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
        Tails.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x (preKeyErrAnswers r) (encEntry img + 0x46c#64)
          (tailRegs cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length))
          (fun sp => dropRecordSlots A sp curScratch ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
            (some (pqCap, pqPtr, otr)) none
            (pollWith sp 0x9d0 [devWord, img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)), 15#64]) ∗
            (vecU8Body A cap ptr x.rem.name.bytes ∗
              ((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt")))
          R s0 sf)
  · change s.pc = encEntry img + 1788#64 at hpc
    apply Pf.SegPreKey.segExit_of_sepWPp_callInv_trap ⟨hfrozen, hsym⟩
      (target := (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 1132#64)
      (dur_mem_group hmem)
    have himg := hEnv.loads
    refine Pf.SegPreKey.rodata_message_encrypt_sepWPp himg hfrozen.roData ?_
    refine SepWPp.fold (takenRecord_sessionRecordAt_pack_exact A sp prevCap prevPtr G sess taken)
      (by sep_focus) ?_
    refine SepWPp.fold (pointsTo64_entails_memRegion (sp + 0x280#64) (sp + 0x128#64))
      (by sep_focus) ?_
    refine SepWPp.fold (cmSlotAt_none_pack A sp k) (by sep_focus) ?_
    refine SepWPp.fold
      (preKeyScratch_stale_weaken sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
      (by sep_focus) ?_
    refine SepWPp.fold (pollWithBaseKey_stale_weaken sp items) (by sep_focus) ?_
    dsimp only [encSpillsAt, encSpillsAtV, encCommon, protocolAddressAt, logOff]
    rw [poll_stale_split sp, encSubStack_split_ext hsp]
    refine SepWPp.fold (memRegion_16_unpack_598 sp) (by sep_focus) ?_
    refine sepWPp_elim_ex fun w5a0 => sepWPp_elim_ex fun w598 => ?_
    refine SepWPp.fold (memRegion_24_unpack_9d0 sp) (by sep_focus) ?_
    refine sepWPp_elim_ex fun w9e0 => sepWPp_elim_ex fun w9d8 => sepWPp_elim_ex fun w9d0 => ?_
    have henc_fn := Pf.SegPreKey.encEntry_eq_fnAddr_trap envF
    rw [henc_fn] at hpc
    have hclone_call := henc_fn ▸ Pf.SegPreKey.stringClone_ok_at_enc_trap envF
    have hentry_val : (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName =
        img.base + (bv% (ls_off% "libsignal_cli_ratchet::encrypt")) := by
      rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]
    messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x6fc 0x34
    messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x78c 0x44
    dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc hclone_call henc_fn hentry_val ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (trTrapExterns C abs))).fnAddr encryptWithStoresName = entry
    examples_hide_fetches
    have hlog := Pf.SegPreKey.adrp_0x718_logFilterAddr himg hentry_val
    have hlog_norm := Pf.SegPreKey.adrp_0x718_logFilterAddr_norm himg hentry_val
    have hadrp_op := Pf.SegPreKey.adrp_0x4a6a0_eq img.base entry
      (ProofLib.ObjectLoad.base_aligned_of_loads himg) hentry_val.symm
    clear hentry_val
    apply Pf.SegPreKey.SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine Pf.SegPreKey.SepWPp.call_frame hclone_call
      (x := (x.remA, sp + 1408#64, x.rem.name))
      (ret_pc := entry + 1948#64)
      (by wp_norm_goal) (by wp_norm_goal) hspAl
      rfl rfl ⟨by wp_norm_goal, by wp_norm_goal⟩
      (by dsimp only [State.sp, State.setPC, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun sf _ hm => by
        rw [sepConj_assoc] at hm
        refine Pf.SegPreKey.onPanic_of_alloc (s := _) ?_ hm
        change s0.trace <+: s.trace
        rw [htr]
        exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩)
      fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
    dsimp only [stringCloneSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htr1 => ?_
    refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm]
      at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
    rw [hx19] at hx19_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned at hspAl ⊢; rwa [hsp1]
    rw [hsp] at hsp1
    rw [htr] at htr1
    refine SepWPp.fold (vecU8_580_unpack A sp x.rem.name.bytes) (by sep_focus) ?_
    refine sepWPp_elim_ex fun ptr => sepWPp_elim_ex fun cap => ?_
    apply Pf.SegPreKey.SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.fold (curScratch_stale_pack sp) (by sep_focus) ?_
    refine SepWP.fold (pollWith_9d0_pack sp cap ptr _ _ _ _ _ _) (by sep_focus) ?_
    have hsp1_pack :
        (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          stackAt s1.sp extHookStack) ⊢ stackAt sp encSubStack := by
      rw [hsp1, ← encSubStack_split_ext rfl]
      exact Entails.refl _
    refine SepWP.fold hsp1_pack (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv1 hmf
    have hfinal :
        kit.storeFinal st0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = st0 := by
      rw [congrArg Prod.snd hmod]
      rfl
    have hidfinal :
        ikit.idFinal ist0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = ist0 := by
      rw [congrArg Prod.snd hmod]
      rfl
    dsimp only [Tails.EncTail, Tails.EncTailV, encStoreExtra, tailRegs, dropRecordSlots, otrSlotAt, encSpillsAt, encSpillsAtV, encCommon, protocolAddressAt, logOff, sp]
      at hsp1 hx19_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
    refine ⟨cap, ptr, (w598 &&& 0xffffffffffffff00#64) ||| BitVec.zeroExtend 64 x.rem.device,
      by ext i hi; simp, by wp_norm_goal, ?_, ?_, ?_,
      hstack, ?_⟩
    · rw [henc_fn]; wp_norm_goal
    · refine ⟨by wp_norm_goal, by wp_norm_goal, hsp0Al, hsp1_al,
        by rw [sp_sub_60_eq_add_b80 s0.sp]; wp_norm_goal,
        by wp_norm_goal, hinv1.1, hinv1.2, by wp_norm_goal⟩
    · refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · rw [hdraws, hfinal, hidfinal]
      arm64_sep_close
  · intro sf ⟨cap, ptr, devWord, hdev, htr_sf, htail⟩
    have hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r)
        (.error (.sessionNotFound x.rem.val "message_encrypt")) s0 sf := by
      refine ⟨⟨congrArg Prod.fst hmod, by rw [congrArg Prod.snd hmod]; exact ⟨hscope.2, trivial⟩,
        by rw [congrArg Prod.snd hmod]; trivial⟩, ?_⟩
      rw [congrArg Prod.snd hmod, htr_sf, ikit.traceOfWith_load]
      rfl
    have h15 : 15#64 = BitVec.ofNat 64 (utf8 "message_encrypt").length := by
      open ProofLib.ProgramReflection in rfl_kernel
    have hst : SpeStaged A x.ret (.sessionNotFound x.rem.val "message_encrypt")
        [cap, ptr, BitVec.ofNat 64 x.rem.name.bytes.length, devWord, img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)), 15#64]
        (vecU8Body A cap ptr x.rem.name.bytes ∗
          ((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt")) :=
      speStaged_sessionNotFound A x.ret x.rem.val "message_encrypt"
        cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length) devWord (img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) 15#64
        rfl hdev h15
    rw [← h45_segExit_kitF_trap]
    exact Tails.tailDropRecord_ok_trap envF x R s0 sf (preKeyErrAnswers r)
      (.sessionNotFound x.rem.val "message_encrypt")
      cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length) devWord (img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) 15#64
      (vecU8Body A cap ptr x.rem.name.bytes ∗
        ((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt"))
      curScratch (Or.inl rfl) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
      (some (pqCap, pqPtr, otr))
      ((h45_tailModel_kitF kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r)
        (.error (.sessionNotFound x.rem.val "message_encrypt")) s0 sf).mpr hm)
      hst
      ((h45_encTailV_kitF kit st0 ikit ist0 C ctl uuidTryParse S x (preKeyErrAnswers r) _ _ _ R s0 sf).mpr htail)

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_regId_kyber_ok_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hlt : expiry.lt x.now = false)
    (hadd : Pf.SegPreKey.StalenessAddState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (Pf.SegPreKey.PreKeyEncryptState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items R s0) := by
  rcases hadd with ⟨hts, hexp, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, hx23, hx24, hx25, hx26, _hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hfrozen, hsym, hvregs⟩
  have hky_bound := (hEnv.scopeIn r hscope sess hcur).2.2.2
  set sp := s0.sp - 0xbe0#64
  change s.pc = encEntry img + 1788#64 at hpc
  apply Pf.SegPreKey.segExit_of_sepWPp_callInv_trap ⟨hfrozen, hsym⟩
    (target := (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 2228#64)
    (dur_mem_group hmem)
  have himg := hEnv.loads
  refine SepWPp.fold (sessionAt_regId_unpack A sp G sess taken) (by sep_focus) ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hkyRel => ?_
  refine SepWPp.fold
    (preKeyScratch_regId_unpack sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
    (by sep_focus) ?_
  refine sepWPp_elim_ex fun w14 => ?_
  refine SepWPp.fold (pollWithBaseKey_regId_unpack sp items) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w590 => sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  dsimp only [encSpillsAt, encSpillsAtV, encCommon, nowAt, logOff]
  rw [encSubStack_split_kyber hsp]
  have henc_fn := Pf.SegPreKey.encEntry_eq_fnAddr_trap (h45_envF hEnv)
  rw [henc_fn] at hpc
  have hkyber_call := henc_fn ▸ Pf.SegPreKey.kyber_ok_at_enc_trap (h45_envF hEnv)
  have hentry_val : (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName =
      img.base + (bv% (ls_off% "libsignal_cli_ratchet::encrypt")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]
  clear hEnv
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x6fc 0x28
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x7d0 0x1c
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x880 0x34
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc hkyber_call henc_fn hentry_val ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  have hlog := Pf.SegPreKey.adrp_0x718_logFilterAddr himg hentry_val
  have hlog_norm := Pf.SegPreKey.adrp_0x718_logFilterAddr_norm himg hentry_val
  clear hentry_val
  cases hky : sess.pendingKyberPreKey with
  | none =>
    cases hGky : G.kyber with
    | some g =>
      rw [hGky, hky] at hkyRel
      exact False.elim hkyRel
    | none =>
      rw [hGky] at hkySlice
      dsimp only [unackKyberSliceProp] at hkySlice
      subst hkySlice
      apply Pf.SegPreKey.SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      wp_steps
      refine SepWP.fold (kyberArgAt_none_pack sp w580 w590) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine Pf.SegPreKey.SepWPp.call_frame hkyber_call
        (x := ⟨sp + 0x8a0#64, sp + 0x580#64, 0#64, none⟩)
        (ret_pc := entry + 2228#64)
        (by wp_norm_goal) (by wp_norm_goal)
        (by dsimp [State.spAligned, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; exact hspAl)
        rfl rfl ⟨by wp_norm_goal, by wp_norm_goal⟩
        (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun sf _ hm => by
          rw [sepConj_assoc] at hm
          refine Pf.SegPreKey.onPanic_of_alloc (s := _) ?_ hm
          change s0.trace <+: s.trace
          rw [htr]
          exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩)
        fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
      dsimp only [kyberMapSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr1 => ?_
      refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
      refine SepWPp.fold (kyberPost_unpack A (sp + 0x8a0#64) (sp + 0x580#64) 0#64 none) (by sep_focus) ?_
      refine sepWPp_elim_ex fun bp => ?_
      refine SepWPp.fold (kyberArgAt_none_to_memRegion sp) (by sep_focus) ?_
      rcases hcs1 with ⟨hx19_1, hx20_1, _hx21_1, hx22_1, _hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [wp_norm, arm64_norm]
        at hx19_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
      rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
      rw [hx25] at hx25_1; rw [hx26] at hx26_1
      rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
      have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
        change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
      have hsp1_al : s1.spAligned = true := by
        unfold State.spAligned at hspAl ⊢; rwa [hsp1]
      rw [hsp] at hsp1
      rw [htr] at htr1
      rw [← hGky]
      apply Pf.SegPreKey.SepWPp.of_sepWP_ret
      refine SepWP.fold (sessionAt_regId_pack A sp G sess taken) (by sep_focus) ?_
      refine SepWP.fold (takenRecord_sessionRecordAt_pack_exact A sp prevCap prevPtr G sess taken)
        (by sep_focus) ?_
      refine SepWP.fold (preKeyEncryptScratch_pack sp _ _ sess.localRegistrationId items.signedPreKeyId pkVal)
        (by sep_focus) ?_
      refine SepWP.fold (pollPreKeyEncrypt_pack A sp bp items sess.pendingKyberPreKey none (by simp [hky]))
        (by sep_focus) ?_
      have hsp1_pack :
          (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - (allocHookStack + 0x40)) ∗
            stackAt s1.sp (allocHookStack + 0x40)) ⊢ stackAt sp encSubStack := by
        rw [hsp1, ← encSubStack_split_kyber rfl]
        exact Entails.refl _
      refine SepWP.fold hsp1_pack (by sep_focus) ?_
      apply SepWP.done hpc1 hstat1
      intro hinv1 hmf
      dsimp only [Pf.SegPreKey.PreKeyEncryptState, Pf.SegPreKey.PreKeyEncryptState', preKeyEncryptScratch, pollPreKeyEncrypt, encMidMeta, encSpillsAt, encSpillsAtV, encCommon, nowAt, logOff, sp]
        at hsp1 hx19_1 hx20_1 hx22_1 hx24_1' hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
      refine ⟨prevCap, prevPtr, G, ts, expiry, pkVal, bp, hts, hexp, hlt, hpkVal,
        by rw [henc_fn]; exact hpc1,
        ⟨hstat1, hsp1, hsp0Al, hsp1_al, hx29_1, hx19_1, hinv1.1, hinv1.2, hvregs_1⟩,
        htr1, hx20_1, hx22_1, hx24_1', hx25_1, hx26_1, hx27_1, hx28_1,
        hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
      arm64_sep_close
  | some ky =>
    cases hGky : G.kyber with
    | none =>
      rw [hGky, hky] at hkyRel
      exact False.elim hkyRel
    | some g =>
      rw [hGky, hky] at hkyRel
      dsimp only [KyberRel] at hkyRel
      rcases hkyRel with ⟨hkyBytes, _⟩
      rw [hGky] at hkySlice
      dsimp only [unackKyberSliceProp] at hkySlice
      rcases hkySlice with ⟨rfl, rfl⟩
      have hkyId_eq : kyIdVal = ky.preKeyId := hkyIdVal ky.preKeyId (by simp [hky])
      subst hkyId_eq
      have hct_lt : ky.ciphertext.length < 2 ^ 32 := hky_bound ky hky
      rw [hkyBytes]
      refine SepWPp.fold (optTailVecAt_borrow A (sp + 0x250#64) g) (by sep_focus) ?_
      rw [sepConj_assoc, sepConj_assoc]
      refine SepWPp.pure_elim fun hptr => ?_
      rw [hkyBytes]
      dsimp only [Option.map, Option.isSome]
      have hptr_beq : (g.vec.ptr == 0#64) = false := _root_.beq_false_of_ne hptr
      apply Pf.SegPreKey.SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      wp_steps
      refine SepWP.fold (kyberArgAt_some_pack sp g.vec.ptr ky hptr hct_lt) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine Pf.SegPreKey.SepWPp.call_frame hkyber_call
        (x := ⟨sp + 0x8a0#64, sp + 0x580#64, g.vec.ptr,
          some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)⟩)
        (ret_pc := entry + 2228#64)
        (by wp_norm_goal) (by wp_norm_goal)
        (by dsimp [State.spAligned, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; exact hspAl)
        rfl rfl ⟨by wp_norm_goal, by wp_norm_goal⟩
        (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun sf _ hm => by
          rw [sepConj_assoc] at hm
          refine Pf.SegPreKey.onPanic_of_alloc (s := _) ?_ hm
          change s0.trace <+: s.trace
          rw [htr]
          exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩)
        fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
      dsimp only [kyberMapSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr1 => ?_
      refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
      refine SepWPp.fold
        (kyberPost_unpack A (sp + 0x8a0#64) (sp + 0x580#64) g.vec.ptr
          (some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)))
        (by sep_focus) ?_
      refine sepWPp_elim_ex fun bp => ?_
      refine SepWPp.fold (kyberArgAt_some_unpack sp g.vec.ptr ky) (by sep_focus) ?_
      rw [← hkyBytes]
      refine SepWPp.fold (optTailVecAt_unborrow A (sp + 0x250#64) g) (by sep_focus) ?_
      rw [hkyBytes, ← hGky]
      rcases hcs1 with ⟨hx19_1, hx20_1, _hx21_1, hx22_1, _hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [wp_norm, arm64_norm]
        at hx19_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
      rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
      rw [hx25] at hx25_1; rw [hx26] at hx26_1
      rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
      have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
        change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
      have hsp1_al : s1.spAligned = true := by
        unfold State.spAligned at hspAl ⊢; rwa [hsp1]
      rw [hsp] at hsp1
      rw [htr] at htr1
      apply Pf.SegPreKey.SepWPp.of_sepWP_ret
      refine SepWP.fold (sessionAt_regId_pack A sp G sess taken) (by sep_focus) ?_
      refine SepWP.fold (takenRecord_sessionRecordAt_pack_exact A sp prevCap prevPtr G sess taken)
        (by sep_focus) ?_
      refine SepWP.fold (preKeyEncryptScratch_pack sp _ _ sess.localRegistrationId items.signedPreKeyId pkVal)
        (by sep_focus) ?_
      refine SepWP.fold
        (pollPreKeyEncrypt_pack A sp bp items sess.pendingKyberPreKey
          (some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)) (by simp [hky]))
        (by sep_focus) ?_
      have hsp1_pack :
          (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - (allocHookStack + 0x40)) ∗
            stackAt s1.sp (allocHookStack + 0x40)) ⊢ stackAt sp encSubStack := by
        rw [hsp1, ← encSubStack_split_kyber rfl]
        exact Entails.refl _
      refine SepWP.fold hsp1_pack (by sep_focus) ?_
      apply SepWP.done hpc1 hstat1
      intro hinv1 hmf
      dsimp only [Pf.SegPreKey.PreKeyEncryptState, Pf.SegPreKey.PreKeyEncryptState', preKeyEncryptScratch, pollPreKeyEncrypt, encMidMeta, encSpillsAt, encSpillsAtV, encCommon, nowAt, logOff, sp]
        at hsp1 hx19_1 hx20_1 hx22_1 hx24_1' hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
      refine ⟨prevCap, prevPtr, G, ts, expiry, pkVal, bp, hts, hexp, hlt, hpkVal,
        by rw [henc_fn]; exact hpc1,
        ⟨hstat1, hsp1, hsp0Al, hsp1_al, hx29_1, hx19_1, hinv1.1, hinv1.2, hvregs_1⟩,
        htr1, hx20_1, hx22_1, hx24_1', hx25_1, hx26_1, hx27_1, hx28_1,
        hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
      arm64_sep_close

end SegPreKeyPrefix

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
