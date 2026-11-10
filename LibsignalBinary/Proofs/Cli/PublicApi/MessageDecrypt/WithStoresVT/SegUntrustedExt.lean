/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegUntrusted
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.StoreCallSite
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAux
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Ext-Generic `SegUntrusted` (`+0x21b0 → +0x2294`)

Proves `segUntrustedVX_ok_ext` over `tripleRatchetProgAtExt img.base ext` for arbitrary `Extra` and
`Scope`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_decodes libsignalSessionCode_tree segUntrustedExtBinCli
  [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8624) →
    (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8636),
   (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8784) →
    (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8848)]

private theorem adrp_logFlag_21b0_eq_ext {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (he : entry = b + bv% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) :
    ((entry + 8624#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) -
        (page% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8624))) =
      b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) := by
  rw [he, BitVec.add_assoc, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]; rfl

set_option maxHeartbeats 800000 in
theorem segUntrusted_wp_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (hb : b &&& 0xfff#64 = 0#64)
    {s : State} {R : SepProp}
    {addrA e0 e1 e3 devWord : BitVec 64} {e2 : BitVec 32} {d0 : BitVec 8} {pad : List (BitVec 8)}
    {addr : AddrGhost}
    (hw4 : addr.device :: pad = unpack64 devWord)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x21b0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2294#64) s
      (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
        vecGhostAt A addr.name addrA ∗
        ((addrA + 0x18#64) ↦₈ addr.device) ∗
        memRegion (s.sp + 0x5f0#64) 24 ∗
        ((s.sp + 0x608#64) ↦₈ d0) ∗ ((s.sp + 0x609#64) ↦ₛ pad) ∗
        ((s.sp + 0x580#64) ↦₆₄ e0) ∗ ((s.sp + 0x588#64) ↦₆₄ e1) ∗
        ((s.sp + 0x590#64) ↦₃₂ e2) ∗ ((s.sp + 0x594#64) ↦₆₄ e3) ∗
        A.pool ∗ stackAt s.sp extHookStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
          ⌜sf.readReg64 .x28 = 0x800000000000000c#64 ∧
            sf.readReg64 .x20 = ((cap.extractLsb' 0 32) >>> 8#32).zeroExtend 64 ∧
            sf.readReg64 .x21 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
            sf.trace = s.trace⌝ ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
          vecGhostAt A addr.name addrA ∗
          ((addrA + 0x18#64) ↦₈ addr.device) ∗
          ((s.sp + 0x5f0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s.sp + 0x5f4#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((s.sp + 0x5f8#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x600#64) ↦₆₄ BitVec.ofNat 64 addr.name.bytes.length) ∗
          ((s.sp + 0x608#64) ↦₆₄ devWord) ∗
          ((s.sp + 0x580#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((s.sp + 0x584#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x58c#64) ↦₆₄ BitVec.ofNat 64 addr.name.bytes.length) ∗
          ((s.sp + 0x594#64) ↦₆₄ devWord) ∗
          CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr addr.name.bytes ∗
          A.pool ∗ stackAt s.sp extHookStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName =
      (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have hclone :
      subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName +
          bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
        (stringCloneSpec A) :=
    stringClone_ok_at_dec_ext hA
  have hadp_log :
      (((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 8624#64) &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) -
          (page% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8624))) =
      b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) :=
    adrp_logFlag_21b0_eq_ext hb (by rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn])
  code_fetches_range CryptoVerification.libsignalSessionCode segUntrustedExtBinCli b
    (Rust.withPanics ext) hfn (ls_off% "libsignal_cli_ratchet::decrypt_signal") 0x21b0 0x10
  code_fetches_range CryptoVerification.libsignalSessionCode segUntrustedExtBinCli b
    (Rust.withPanics ext) hfn (ls_off% "libsignal_cli_ratchet::decrypt_signal") 0x2250 0x44
  dsimp only [tripleRatchetProgAtExt] at hpc hclone hadp_log ⊢
  generalize (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName = entry at *
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - (ls_off% "libsignal_cli_ratchet::decrypt_signal")) % 2^64))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  messageDecrypt_call_panic hclone (addrA, s.sp + 1520#64, addr.name)
  apply SepWP.fold (vecU8_unpack_5f0 A s.sp addr.name.bytes) (by sep_focus)
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro (cap : BitVec 64)
  apply SepWP.exists_elim; intro (ptr : BitVec 64)
  wp_steps 5
  apply SepWP.fold
    (Entails.of_eq (repack_5f4_for_q0 s.sp cap ptr (BitVec.ofNat 64 addr.name.bytes.length)))
    (by sep_focus)
  wp_step
  apply SepWP.fold
    (Entails.of_eq (repack_5f4_for_q1 s.sp cap ptr (BitVec.ofNat 64 addr.name.bytes.length) addr.device pad devWord hw4))
    (by sep_focus)
  wp_steps 3
  apply SepWP.fold
    (Entails.of_eq (repack_588_for_q1 s.sp ptr (BitVec.ofNat 64 addr.name.bytes.length) e2))
    (by sep_focus)
  wp_steps 4
  apply SepWP.fold
    (Entails.of_eq (repack_580_after_q1 s.sp cap ptr))
    (by sep_focus)
  wp_done

private theorem model_of_trust_false_noScope (C : Crypto) (S : SpqrModel) (x : DecryptGhost)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8))
    (ses : Session (List (BitVec 8))) (k : IdentityKey)
    (hload : ans.loadSession = .ok (some rec))
    (hdec : decryptRecord C S uuidTryParse x rec = .ok (pt, rec'))
    (hcur : rec'.currentSession = some ses)
    (hik : ses.state.remoteIdentity = some k)
    (htrust : ans.isTrustedIdentity = .ok false) :
    (x.model C S uuidTryParse ans).1 = .error (.untrustedIdentity x.rem.val) ∧
    (x.model C S uuidTryParse ans).2 =
      [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .receiving] := by
  have h : x.model C S uuidTryParse ans =
      (.error (.untrustedIdentity x.rem.val),
        [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .receiving]) := by
    unfold DecryptGhost.model
    unfold decryptRecord at hdec
    rw [messageDecryptSignal_eq_flat]
    simp [decryptFlat, hload, hdec, hcur, hik, htrust]
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

attribute [local irreducible] protocolAddressAt vecGhostAt

private def wsUntrustedCommonRestExt (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) : SepProp :=
  wsUntrustedFixedRest A img kit ikit x s0 sp ∗ wsMsgCells x sp ∗
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
  vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x300#64) 0x280 ∗
  (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
  memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)

private def wsUntrustedFrameExt (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) (e4 : BitVec 64) : SepProp :=
  ((sp + 0x59c#64) ↦₆₄ e4) ∗
  memRegion (sp + 0x610#64) 16 ∗
  wsUntrustedCommonRestExt C A img kit ikit x ans s0 sp rec' pt k

private theorem trusted_entails_untrustedPre_ext (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) :
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)) ⊢
    ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 32,
    ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
      ⌜pad.length = 7⌝ ∗
      wsUntrustedPre A img x sp e0 e1 e3 e2 d0 pad ∗
      wsUntrustedFrameExt C A img kit ikit x ans s0 sp rec' pt k e4 := by
  rw [← sepConj_assoc, wsFixed_wsEnv_untrusted_split, memRegion_300_b00_split,
    memRegion_5a4_85c_split]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (sp + 0x580#64) 0x24 ∗ memRegion (sp + 0x5f0#64) 48) ∗
    (wsUntrustedFixedEnv A img x sp ∗
      wsUntrustedCommonRestExt C A img kit ikit x ans s0 sp rec' pt k) by
    unfold wsUntrustedCommonRestExt; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono
    (memRegion_36_untrusted_entails (sp + 0x580#64))
    (memRegion_48_untrusted_entails (sp + 0x5f0#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro (d0 : BitVec 8)
  apply Entails.sepExists_elim; intro (pad : List (BitVec 8))
  apply Entails.sepExists_elim; intro (e0 : BitVec 64)
  apply Entails.sepExists_elim; intro (e1 : BitVec 64)
  apply Entails.sepExists_elim; intro (e2 : BitVec 32)
  apply Entails.sepExists_elim; intro (e3 : BitVec 64)
  apply Entails.sepExists_elim; intro (e4 : BitVec 64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜pad.length = 7⌝ ∗
      (wsUntrustedPre A img x sp e0 e1 e3 e2 d0 pad ∗
        wsUntrustedFrameExt C A img kit ikit x ans s0 sp rec' pt k e4) by
    unfold wsUntrustedPre wsUntrustedFrameExt wsUntrustedFixedEnv
    ac_rfl)) ?_
  apply Entails.pure_left; intro hpad
  exact Entails.sepExists_right e0 (Entails.sepExists_right e1
    (Entails.sepExists_right e2 (Entails.sepExists_right e3
      (Entails.sepExists_right e4 (Entails.sepExists_right d0
        (Entails.sepExists_right pad (Entails.pure_right hpad (Entails.refl _))))))))

private theorem untrustedPost_entails_ext (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (pt : List (BitVec 8)) (k : IdentityKey)
    (x28 w20 w21 cap ptr devWord e4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : x.rem.device :: pad = unpack64 devWord)
    (hx28 : x28 = 0x800000000000000c#64) (hw1 : resWord1 w20 w21 = cap.extractLsb' 0 32) :
    wsUntrustedPostSpatial A img x sp cap ptr devWord ∗
      wsUntrustedFrameExt C A img kit ikit x ans s0 sp rec' pt k e4 ⊢
    ∃∗ G : SessionGhost,
      wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
      (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) (.error (.untrustedIdentity x.rem.val)) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) := by
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
    (((sp + 0x5f0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
      ((sp + 0x5f4#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((sp + 0x5f8#64) ↦₆₄ ptr) ∗
      ((sp + 0x600#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
      ((sp + 0x608#64) ↦₆₄ devWord) ∗
      memRegion (sp + 0x610#64) 16) ∗
    ((((sp + 0x580#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((sp + 0x584#64) ↦₆₄ ptr) ∗
      ((sp + 0x58c#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
      ((sp + 0x594#64) ↦₆₄ devWord) ∗
      ((sp + 0x59c#64) ↦₆₄ e4)) ∗
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr x.rem.name.bytes) ∗
    vecU8 A (sp + 0x290#64) pt ∗
    ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
    ((wsUntrustedFixedEnv A img x sp ∗ wsUntrustedFixedRest A img kit ikit x s0 sp) ∗
      wsMsgCells x sp ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗
      (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)) by
    unfold wsUntrustedPostSpatial wsUntrustedFrameExt wsUntrustedCommonRestExt wsUntrustedFixedEnv
    ac_rfl)) ?_
  rw [← wsFixed_wsEnv_untrusted_split]
  have h48 := cells_48_untrusted_entails_memRegion (sp + 0x5f0#64)
    (cap.extractLsb' 0 32) (cap.extractLsb' 32 32) ptr
    (BitVec.ofNat 64 x.rem.name.bytes.length) devWord
  have hst := stagedRes_untrusted_intro A x28 w20 w21 (sp + 0x580#64)
    cap ptr devWord e4 x.rem pad hpad hw4 hx28 hw1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48 hst
  have hrec := sessionRecordAt_some_entails_droppable A (sp + 0x120#64) rec' ses hcur
  have hpt : vecU8 A (sp + 0x290#64) pt ⊢ ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p :=
    Entails.sepExists_right pt (Entails.refl _)
  refine Entails.trans (sepConj_mono hrec (sepConj_mono h48
    (sepConj_mono hst (sepConj_mono hpt
      (sepConj_mono_left (key_entails_memRegion_32 (sp + 0x2a8#64) k)))))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [memRegion_5a4_85c_split]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 600000 in
attribute [local semireducible] SepWP in
theorem segUntrustedVX_ok_of_loads_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts4K img.base A ext)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hst : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans false R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV
        C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x true R s0) := by
  intro hL
  rcases hst with ⟨hpc, hmeta, hx26, hx19, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htrust, htrustRel, htr, hm⟩
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, _hfr, _hsym, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hpc' : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x21b0#64 := by
    rw [← entryOf_eq_tripleRatchetProgAtExt ext himg, hpc]; rfl
  rw [← hsp] at hx26 hx19 hx22 hm
  let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity
  let R' : SepProp := decStoreExtra kit ikit st0 ist1 s0 ∗ R
  have hm_pre : s.mem ⊨
      (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 32,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
          ⌜pad.length = 7⌝ ∗
          wsUntrustedPre A img x s.sp e0 e1 e3 e2 d0 pad ∗
          wsUntrustedFrameExt C A img kit ikit x ans s0 s.sp rec' pt k e4) ∗ R' := by
    refine Satisfies.mono (sepConj_mono_left
      (trusted_entails_untrustedPre_ext C A img kit ikit x ans s0 s.sp rec' pt k)) ?_
    simpa only [R', ist1, sepConj_assoc] using hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨e0, e1, e2, e3, e4, d0, pad, hm_pre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hpad, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨devWord, hw4⟩ := exists_unpack64_of_length_8 (bs := x.rem.device :: pad) (by simp [hpad])
  obtain ⟨sf, hsteps, hout⟩ :=
    segUntrusted_wp_ext hA hb
      (R := wsUntrustedFrameExt C A img kit ikit x ans s0 s.sp rec' pt k e4 ∗ R')
      hw4 hpc' hrun hsp_align
      (wsUntrustedFrameExt C A img kit ikit x ans s0 s.sp rec' pt k e4 ∗ R') hm_pre hL
  rcases hout with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1'
    rcases hm1' with ⟨cap, ptr, hm1'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1'
    rcases hm1' with ⟨⟨hx28_1, hx20_1, hx21_1, htr1⟩, hm1'⟩
    rw [← sepConj_assoc] at hm1'
    have hmeta1 := wsMeta_of_steps hmeta hsteps hrun1 hsp1 hx29_1 hx27_1 hvregs_1
    have hw1 : resWord1 (sf.readReg64 .x20) (sf.readReg64 .x21) = cap.extractLsb' 0 32 := by
      rw [hx20_1, hx21_1, resWord1_lsr8]
    have hm1_post := Satisfies.mono (sepConj_mono_left
      (untrustedPost_entails_ext C A img kit ikit x ans s0 s.sp rec' ses hcur pt k
        (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21)
        cap ptr devWord e4 pad hpad hw4 hx28_1 hw1)) hm1'
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm1_post
    rcases hm1_post with ⟨G, hm1_post⟩
    refine ⟨sf, hsteps, Or.inl ?_⟩
    have hmod := model_of_trust_false_noScope C S x ans rec rec' pt ses k
      hload hdec hcur hrem htrust
    refine ⟨?_, hmeta1, ?_, ?_, ans, some (G, ses.state), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpc1, ← entryOf_eq_tripleRatchetProgAtExt ext himg]; rfl
    · rw [hx26_1, hx26, hsp]
    · rw [hx28_1]; decide
    · rw [hmod.1]; exact nofun
    · intro p; rw [hmod.1]; exact nofun
    · intro r hr; rw [hload] at hr; cases hr; exact hscope
    · rw [hmod.2]; exact ⟨hload ▸ hscope.2, trivial⟩
    · rw [hmod.2]; exact ⟨htrustRel, trivial⟩
    · rw [htr1, htr, hmod.2]; simp
    · have hstf : kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2 = st0 := by
        rw [hmod.2]; rfl
      have histf : ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2 = ist1 := by
        rw [hmod.2]; rfl
      rw [hmod.1, hstf, histf]
      simpa only [R', ite_true, hsp, sepConj_assoc] using hm1_post
  · have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
      have hpan_m0 := hpan_post1 hm1
      rw [← sepConj_assoc] at hpan_m0
      have hpan_m1 := Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m0
      have hreord :
          (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R' ⊢
          (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
        dsimp only [R']
        rw [← sepConj_assoc, sepConj_assoc ⌜_⌝ anyHeap]
        exact sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))
      exact Satisfies.mono hreord hpan_m1
    exact ⟨sf, hsteps, Or.inr (panic_outcome_of_allocFailedInVX_ext ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem segUntrustedVX_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hst : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans false R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV
        C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x true R s0) :=
  segUntrustedVX_ok_of_loads_ext hyps.loads hyps.toDecHypsExt4K.alloc x ans R s0 s hst

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
