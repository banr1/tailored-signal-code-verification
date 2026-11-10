/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTail
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStaleness
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyStale
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyBody
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyStale
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `segPreKey` Registration IDs, Kyber Closure, and Segment Assembly

Proves `segPreKey_regId_kyber_ok` (and its trap-mode counterpart) across `+0x6fc..+0x8b4` when the
unacknowledged pre-key session is not stale, and composes the staleness, Kyber, and tail lemmas into
`segPreKey_ok_body` and `segPreKey_ok_body_trap`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Encrypt

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. E6b Registration IDs and Kyber Closure (`+0x6fc..+0x8b4`) -/

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_regId_kyber_ok_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
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
    (hadd : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessAddState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items R s0) := by
  rcases hadd with ⟨hts, hexp, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, hx23, hx24, hx25, hx26, _hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hfrozen, hsym, hvregs⟩
  have hky_bound := (env.scopeIn r hscope sess hcur).2.2.2
  set sp := s0.sp - 0xbe0#64
  change s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 1788#64 at hpc
  apply CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_sepWPp_callInv_trap ⟨hfrozen, hsym⟩
    (target := (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 2228#64)
    (dur_mem_group hmem)
  have himg := env.loads
  refine SepWPp.fold (sessionAt_regId_unpack A sp G sess taken) (by sep_focus) ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hkyRel => ?_
  refine SepWPp.fold
    (preKeyScratch_regId_unpack sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
    (by sep_focus) ?_
  refine sepWPp_elim_ex fun w14 => ?_
  refine SepWPp.fold (pollWithBaseKey_regId_unpack sp items) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w590 => sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  dsimp only [encSpillsAt, encSpillsAtV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon, nowAt, logOff]
  rw [encSubStack_split_kyber hsp]
  have henc_fn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr_trap env
  rw [henc_fn] at hpc
  have hkyber_call := henc_fn ▸ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.kyber_ok_at_enc_trap env
  have hentry_val : (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName =
      img.base + (bv% (ls_off% "libsignal_cli_ratchet::encrypt")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]
  clear env
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x6fc 0x28
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x7d0 0x1c
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x880 0x34
  dsimp only [trTrapProgAt] at hpc hkyber_call henc_fn hentry_val ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  have hlog := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.adrp_0x718_logFilterAddr himg hentry_val
  have hlog_norm := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.adrp_0x718_logFilterAddr_norm himg hentry_val
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
      apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      wp_steps
      refine SepWP.fold (kyberArgAt_none_pack sp w580 w590) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine SepWPp.call_frame hkyber_call
        (x := ⟨sp + 0x8a0#64, sp + 0x580#64, 0#64, none⟩)
        (ret_pc := entry + 2228#64)
        (by wp_norm_goal) (by wp_norm_goal)
        (by dsimp [State.spAligned, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; exact hspAl)
        rfl rfl ⟨by wp_norm_goal, by wp_norm_goal⟩
        (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun sf _ hm => by
          rw [sepConj_assoc] at hm
          refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_of_alloc (s := _) ?_ hm
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
      apply SepWPp.of_sepWP_ret
      refine SepWP.fold (sessionAt_regId_pack A sp G sess taken) (by sep_focus) ?_
      refine SepWP.fold (takenRecord_sessionRecordAt_pack_exact A sp prevCap prevPtr G sess taken)
        (by sep_focus) ?_
      refine SepWP.fold (preKeyEncryptScratch_pack sp kyLen _ sess.localRegistrationId items.signedPreKeyId pkVal)
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
      dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState', preKeyEncryptScratch, pollPreKeyEncrypt, encMidMeta, encSpillsAt, encSpillsAtV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon, nowAt, logOff, sp]
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
      apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      wp_steps
      refine SepWP.fold (kyberArgAt_some_pack sp g.vec.ptr ky hptr hct_lt) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine SepWPp.call_frame hkyber_call
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
          refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_of_alloc (s := _) ?_ hm
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
      apply SepWPp.of_sepWP_ret
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
      dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState', preKeyEncryptScratch, pollPreKeyEncrypt, encMidMeta, encSpillsAt, encSpillsAtV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon, nowAt, logOff, sp]
        at hsp1 hx19_1 hx20_1 hx22_1 hx24_1' hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
      refine ⟨prevCap, prevPtr, G, ts, expiry, pkVal, bp, hts, hexp, hlt, hpkVal,
        by rw [henc_fn]; exact hpc1,
        ⟨hstat1, hsp1, hsp0Al, hsp1_al, hx29_1, hx19_1, hinv1.1, hinv1.2, hvregs_1⟩,
        htr1, hx20_1, hx22_1, hx24_1', hx25_1, hx26_1, hx27_1, hx28_1,
        hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
      arm64_sep_close

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_regId_kyber_ok {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
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
    (hadd : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessAddState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items R s0) := by
  rcases hadd with ⟨hts, hexp, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, hx23, hx24, hx25, hx26, _hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hfrozen, hsym, hvregs⟩
  have hky_bound := (env.scopeIn r hscope sess hcur).2.2.2
  set sp := s0.sp - 0xbe0#64
  change s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 1788#64 at hpc
  apply CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_sepWPp_callInv ⟨hfrozen, hsym⟩
    (target := (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 2228#64)
    (dur_mem_group hmem)
  have himg := env.loads
  refine SepWPp.fold (sessionAt_regId_unpack A sp G sess taken) (by sep_focus) ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hkyRel => ?_
  refine SepWPp.fold
    (preKeyScratch_regId_unpack sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
    (by sep_focus) ?_
  refine sepWPp_elim_ex fun w14 => ?_
  refine SepWPp.fold (pollWithBaseKey_regId_unpack sp items) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w590 => sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  dsimp only [encSpillsAt, encSpillsAtV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon, nowAt, logOff]
  rw [encSubStack_split_kyber hsp]
  have henc_fn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr env
  rw [henc_fn] at hpc
  have hkyber_call := henc_fn ▸ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.kyber_ok_at_enc env
  have hentry_val : (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName =
      img.base + (bv% (ls_off% "libsignal_cli_ratchet::encrypt")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]
  clear env
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x6fc 0x28
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x7d0 0x1c
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x880 0x34
  dsimp only [tripleRatchetProgAt] at hpc hkyber_call henc_fn hentry_val ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  have hlog := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.adrp_0x718_logFilterAddr himg hentry_val
  have hlog_norm := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.adrp_0x718_logFilterAddr_norm himg hentry_val
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
      apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      wp_steps
      refine SepWP.fold (kyberArgAt_none_pack sp w580 w590) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine SepWPp.call_frame hkyber_call
        (x := ⟨sp + 0x8a0#64, sp + 0x580#64, 0#64, none⟩)
        (ret_pc := entry + 2228#64)
        (by wp_norm_goal) (by wp_norm_goal)
        (by dsimp [State.spAligned, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; exact hspAl)
        rfl rfl ⟨by wp_norm_goal, by wp_norm_goal⟩
        (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun sf _ hm => by
          rw [sepConj_assoc] at hm
          refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_of_alloc (s := _) ?_ hm
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
      apply SepWPp.of_sepWP_ret
      refine SepWP.fold (sessionAt_regId_pack A sp G sess taken) (by sep_focus) ?_
      refine SepWP.fold (takenRecord_sessionRecordAt_pack_exact A sp prevCap prevPtr G sess taken)
        (by sep_focus) ?_
      refine SepWP.fold (preKeyEncryptScratch_pack sp kyLen _ sess.localRegistrationId items.signedPreKeyId pkVal)
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
      dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState', preKeyEncryptScratch, pollPreKeyEncrypt, encMidMeta, encSpillsAt, encSpillsAtV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon, nowAt, logOff, sp]
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
      apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      wp_steps
      refine SepWP.fold (kyberArgAt_some_pack sp g.vec.ptr ky hptr hct_lt) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine SepWPp.call_frame hkyber_call
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
          refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_of_alloc (s := _) ?_ hm
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
      apply SepWPp.of_sepWP_ret
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
      dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState', preKeyEncryptScratch, pollPreKeyEncrypt, encMidMeta, encSpillsAt, encSpillsAtV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon, nowAt, logOff, sp]
        at hsp1 hx19_1 hx20_1 hx22_1 hx24_1' hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
      refine ⟨prevCap, prevPtr, G, ts, expiry, pkVal, bp, hts, hexp, hlt, hpkVal,
        by rw [henc_fn]; exact hpc1,
        ⟨hstat1, hsp1, hsp0Al, hsp1_al, hx29_1, hx19_1, hinv1.1, hinv1.2, hvregs_1⟩,
        htr1, hx20_1, hx22_1, hx24_1', hx25_1, hx26_1, hx27_1, hx28_1,
        hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
      arm64_sep_close

/-! ## 2. Top-Level `segPreKey_ok_body` Composition -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_ok_body_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpecV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs := by
  intro env x r sess otr taken pqCap pqPtr k R s0 s his hkey
  obtain ⟨items, hpk⟩ := Option.isSome_iff_exists.mp his
  have hcur := hkey.1
  have hscope := hkey.2.1
  have hfrom := hkey.2.2.1
  have hrem := hkey.2.2.2.1
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_trans_trap
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_unackItems_to_dur_ok_trap env x r sess otr taken pqCap pqPtr k items R s0 s hpk hkey) ?_
  rintro s1 ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen, hdur⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_trans_trap
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_staleness_to_add_ok_trap env x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R s0 s1
      hcur hscope hfrom hrem hpk hdur) ?_
  rintro s2 ⟨expiry, hadd⟩
  by_cases hlt : expiry.lt x.now = true
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_false_trap (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_stale_ok_trap env x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s2
      hcur hscope hfrom hrem hpk hlt hadd)
  · have hlt_f : expiry.lt x.now = false := Bool.eq_false_iff.mpr hlt
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_trans_trap
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_regId_kyber_ok_trap env x r sess otr taken pqCap pqPtr k items
        prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s2
        hcur hscope hlt_f hadd) ?_
    intro s3 he6c
    exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_tail_ok_trap env x r sess otr taken pqCap pqPtr k items R s0 s3
      hcur hscope hfrom hrem hpk he6c

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_ok_body {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs := by
  intro env x r sess otr taken pqCap pqPtr k R s0 s his hkey
  obtain ⟨items, hpk⟩ := Option.isSome_iff_exists.mp his
  have hcur := hkey.1
  have hscope := hkey.2.1
  have hfrom := hkey.2.2.1
  have hrem := hkey.2.2.2.1
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_trans
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_unackItems_to_dur_ok env x r sess otr taken pqCap pqPtr k items R s0 s hpk hkey) ?_
  rintro s1 ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen, hdur⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_trans
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_staleness_to_add_ok env x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R s0 s1
      hcur hscope hfrom hrem hpk hdur) ?_
  rintro s2 ⟨expiry, hadd⟩
  by_cases hlt : expiry.lt x.now = true
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_false (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_stale_ok env x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s2
      hcur hscope hfrom hrem hpk hlt hadd)
  · have hlt_f : expiry.lt x.now = false := Bool.eq_false_iff.mpr hlt
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_trans
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_regId_kyber_ok env x r sess otr taken pqCap pqPtr k items
        prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s2
        hcur hscope hlt_f hadd) ?_
    intro s3 he6c
    exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_tail_ok env x r sess otr taken pqCap pqPtr k items R s0 s3
      hcur hscope hfrom hrem hpk he6c

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
