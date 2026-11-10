/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2b
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StoreEmpty
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OneKeyVtables
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccount
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP2
import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.Skeleton
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2a
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCut

/-!
# Responder Closure Stage P2 Substage 5 (`+0x36ac → +0x125c`)

Proves `stageP2_sub5_ok_trap` and `stageP2_sub5_ok`, composing `get_identity_key_pair`,
`IdentityKey::is_same_account`, and `initialize_bob_session` in
`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession

open CryptoVerification CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi

open CryptoVerification.LibsignalPublicApi.StoreSession

open CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

open CryptoVerification.E2E.InMem

open CryptoVerification.E2E.InMem.HashbrownModel

open CryptoVerification.E2E.InMem.HashbrownBin

open CryptoVerification.E2E.Pqxdh.WireEntries

attribute [local irreducible] protocolAddressAt

open CryptoVerification.E2E.InMem.SessionStoreImpl

open CryptoVerification.LibsignalSession

open CryptoVerification.E2E.Bin

open CryptoVerification.E2E.Pqxdh

open CryptoVerification.E2E.Pqxdh.Initiator

open CryptoVerification.E2E.Pqxdh.WireEntries

open CryptoVerification.E2E.Pqxdh.ResponderStore

open CryptoVerification.E2E.Pqxdh.ResponderCore

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## Substage P2.5 (`+0x36ac → +0x125c`) -/

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.stageP2_sub5_ok_trap {P : Primitives} {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (C : Crypto) (abs : String → Option (State → State))
    (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes) (opkPkBytes opkSkBytes : List (BitVec 8))
    (gMe gPeer : AddrGhost)
    (himg : Obj.Loads libsignalSessionImage img) (hbase : img.base = b) (hWF : StructuralPrims P)
    (hH : ResponderCore.PqxdhHookContracts P A img abs) (hP : PrimitivesMatchCrypto P C)
    (htrusted : inp.trustedPeer = true) (hreplay : inp.replayOk = true)
    (hopk_match : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome) (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hacc_none : Model.acceptKeys P inp = none)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (hneq : bytesToBv8 ikBPk ≠ bytesToBv8 inp.hdr.ikAPk ∨
      DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes) (s0 s : State)
    (coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idKpFutPtr kyberKpPubPtr kyberKpSecPtr ctBufPtr fp
     v_a8 v_b8 v_d0 u_b90 : BitVec 64)
    (opkId : BitVec 32) (b_4f1 b_b98 : BitVec 8) (hb : b &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x36ac#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace =
      s0.trace)
    (hx0 : s.readReg64 .x0 = idKpFutPtr) (hx1 : s.readReg64 .x1 = b + bv% (ls_reloc% 0x7b34 - 24))
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = coroPtr + 0x390#64)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x125c#64) s
      (A.live idKpFutPtr 16 8 ∗ inMemId16BoxAt idKpFutPtr idStorePtr 0#8 ∗
       futVtableAtP (b + bv% (ls_reloc% 0x7b34 - 24)) (b + 0x01fe4#64) 16#64 8#64 (b + 0x07b34#64) ∗
       ((idStorePtr + 0x30#64) ↦ₛ bytesToBv8 ikBPk) ∗
         ((idStorePtr + 0x50#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
       ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       cells (coroPtr + 0x4f8#64) 2 ∗ ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
       ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ memRegion (coroPtr + 0x658#64) 298 ∗
       memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
       ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       (kyberKpSecPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
       ((kyberKpSecPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗ (ctBufPtr ↦₈ 8#8) ∗
       ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
       ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
       memRegion (s.sp + 0x3c8#64) 7 ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ cells (s.sp + 0x560#64) 4 ∗
       cells (s.sp + 0x6a0#64) 4 ∗ cells (s.sp + 0x7e0#64) 4 ∗ cells (s.sp + 0x930#64) 8 ∗
       cells (s.sp + 0xa90#64) 8 ∗ ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗
       ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗
       stackAt s.sp stageP2bStack)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ v_a8' : BitVec 64, ∃∗ v_b8' : BitVec 64, ∃∗ v_d0' : BitVec 64,
          ∃∗ u_b90' : BitVec 64, ∃∗ b_b98' : BitVec 8,
            bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
              (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
            (match Model.acceptKeys P inp with
             | some drKey =>
               ∃∗ localIkBoxPtr : BitVec 64, ∃∗ remoteIkBoxPtr : BitVec 64,
                 ∃∗ rootKeyBoxPtr : BitVec 64,
               ∃∗ baseKeyBoxPtr : BitVec 64, ∃∗ ratchetPubBoxPtr : BitVec 64,
               ∃∗ ratchetPrivBoxPtr : BitVec 64, ∃∗ chainKeyBoxPtr : BitVec 64,
                 ∃∗ pad_f4 : BitVec 32,
               ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
                 ∃∗ c4 : BitVec 64,
               ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
                 ⌜localIkBoxPtr ≠ 0 ∧ remoteIkBoxPtr ≠ 0 ∧ rootKeyBoxPtr ≠ 0 ∧ baseKeyBoxPtr ≠ 0 ∧
                   ratchetPubBoxPtr ≠ 0 ∧ ratchetPrivBoxPtr ≠ 0 ∧ chainKeyBoxPtr ≠ 0⌝ ∗
                 (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
                 (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
                   A.live remoteIkBoxPtr 33 1 ∗
                 (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
                 (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
                   A.live baseKeyBoxPtr 33 1 ∗
                 (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
                   A.live ratchetPubBoxPtr 33 1 ∗
                 (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
                 (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
                 ((s.sp + 0x3e0#64) ↦ₛ bobSession344Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr
                   baseKeyBoxPtr
                   0#64 1#64 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
                   pad_f4 c0 c1 c2 c3 c4 d0 d1 d2)
             | none =>
               initBobErrAt (s.sp + 0x3e0#64) ∗ anyHeap) ∗
            futVtableAtP (b + bv% (ls_reloc% 0x7b34 - 24)) (b + 0x01fe4#64) 16#64 8#64 (b + 0x07b34#64) ∗
            ((idStorePtr + 0x30#64) ↦ₛ bytesToBv8 ikBPk) ∗
            ((idStorePtr + 0x50#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
            ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
            ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
              ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
            cells (coroPtr + 0x4f8#64) 2 ∗ ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
            ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
            ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
            opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
            memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
            ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
            ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
            protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
            ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
              ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((s.sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
            ((s.sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ v_d0') ∗ memRegion (s.sp + 0x3c8#64) 7 ∗
              cells (s.sp + 0x560#64) 4 ∗
            cells (s.sp + 0x6a0#64) 4 ∗ cells (s.sp + 0x7e0#64) 4 ∗ cells (s.sp + 0x930#64) 8 ∗
            cells (s.sp + 0xa90#64) 8 ∗ ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗
            ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗
            stackAt s.sp stageP2bStack) ∧ sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x21 = msgPtr + 0x90#64 ∧
        sf.readReg64 .x22 = s.sp + 0x370#64 ∧ sf.readReg64 .x23 = s.sp + 0x930#64 ∧
        sf.readReg64 .x24 = coroPtr + 0x398#64 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.sp + 0xa90#64 ∧
        sf.readReg64 .x29 = fp ∧ img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hA : AllocHooks A abs := hH.alloc
  have hikBPk_bv : (bytesToBv8 ikBPk).length = 32 := by rw [bytesToBv8_length]; exact hikBPk_len
  have hikBSk_bv : (bytesToBv8 inp.ikBSk).length = 32 := by rw [bytesToBv8_length]; exact hwell.1
  have hspkBPk_bv : (bytesToBv8 spkBPk).length = 32 := by rw [bytesToBv8_length]; exact hspkBPk_len
  have hspkBSk_bv : (bytesToBv8 inp.spkBSk).length = 32 :=
    by rw [bytesToBv8_length]; exact hwell.2.2.1
  have hikAPk_bv : (bytesToBv8 inp.hdr.ikAPk).length = 32 :=
    by rw [bytesToBv8_length]; exact hwell.2.2.2.2.2.2.2.1
  have hekAPk_bv : (bytesToBv8 inp.hdr.ekAPk).length = 32 :=
    by rw [bytesToBv8_length]; exact hwell.2.2.2.2.2.2.2.2.1
  obtain ⟨ik0, ik1, ik2, ik3, hikB0⟩ := exists_words4_of_len32 hikBPk_bv
  obtain ⟨ik4, ik5, ik6, ik7, hikB1⟩ := exists_words4_of_len32 hikBSk_bv
  obtain ⟨spk0, spk1, spk2, spk3, hspkPk⟩ := exists_words4_of_len32 hspkBPk_bv
  obtain ⟨spk4, spk5, spk6, spk7, hspkSk⟩ := exists_words4_of_len32 hspkBSk_bv
  obtain ⟨ikA0, ikA1, ikA2, ikA3, hikA⟩ := exists_words4_of_len32 hikAPk_bv
  obtain ⟨ekA0, ekA1, ekA2, ekA3, hekA⟩ := exists_words4_of_len32 hekAPk_bv
  obtain ⟨opk0, opk1, opk2, opk3, opk4, opk5, opk6, opk7, opk_b64, hopk⟩ :=
    exists_opkSlot65_words (opkPresentTag inp.opkBSk?) hopkPk_len hopkSk_len
  have hvt_eq : futVtableAtP (b + bv% (ls_reloc% 0x7b34 - 24)) (b + 0x01fe4#64) 16#64 8#64 (b + 0x07b34#64) =
      ((b + bv% (ls_reloc% 0x7b34 - 24) + 0x0#64) ↦₆₄ᵣ (b + 0x01fe4#64)) ∗ ((b + bv% (ls_reloc% 0x7b34 - 24) + 0x8#64) ↦₆₄ᵣ 16#64) ∗
      ((b + bv% (ls_reloc% 0x7b34 - 24) + 0x10#64) ↦₆₄ᵣ 8#64) ∗
      ((b + bv% (ls_reloc% 0x7b34 - 24) + 0x18#64) ↦₆₄ᵣ (b + 0x07b34#64)) := by
    unfold futVtableAtP; rw [show (b + bv% (ls_reloc% 0x7b34 - 24)) + 0x0#64 = b + bv% (ls_reloc% 0x7b34 - 24) by bv_omega]
  have hc4f8 : cells (coroPtr + 0x4f8#64) 2 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
        ((coroPtr + 0x4f8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x500#64) ↦₆₄ u1)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hvt_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hc4f8) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_4f8 => SepWPp.exists_elim fun u_500 => ?_
  have hstep1 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5a_wp_trap b C abs s coroPtr ctxPtr idKpFutPtr
    (b + bv% (ls_reloc% 0x7b34 - 24)) (b + 0x07b34#64) u_4f8 u_500
    hpc hrun hx0 hx1 hx19 hx27
  refine SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus) fun s1 hpc1 hrun1 hF1 hsym1 hregs1 =>
    ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx8_1, hx19_1, hx21_1, hx23_1, hx24_1, hx25_1,
    hx26_1, hx27_1, hx28_1, hx29_1, hx30_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hbox_eq : inMemId16BoxAt idKpFutPtr idStorePtr 0#8 =
      (idKpFutPtr ↦₆₄ idStorePtr) ∗ ((idKpFutPtr + 8#64) ↦₈ 0#8) ∗
        memRegion (idKpFutPtr + 9#64) 7 := rfl
  have hikStore_eq :
      ((idStorePtr + 0x30#64) ↦ₛ bytesToBv8 ikBPk) ∗
        ((idStorePtr + 0x50#64) ↦ₛ bytesToBv8 inp.ikBSk) =
      ((idStorePtr + 0x30#64) ↦₆₄ ik0) ∗ ((idStorePtr + 0x38#64) ↦₆₄ ik1) ∗
      ((idStorePtr + 0x40#64) ↦₆₄ ik2) ∗ ((idStorePtr + 0x48#64) ↦₆₄ ik3) ∗
      ((idStorePtr + 0x50#64) ↦₆₄ ik4) ∗ ((idStorePtr + 0x58#64) ↦₆₄ ik5) ∗
      ((idStorePtr + 0x60#64) ↦₆₄ ik6) ∗ ((idStorePtr + 0x68#64) ↦₆₄ ik7) := by
    rw [hikB0 (idStorePtr + 0x30#64), hikB1 (idStorePtr + 0x50#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hbox_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hikStore_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp3e0_344_split_65_279 s.sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion65_eq_byte_words8 (s.sp + 0x3e0#64))) (by
    sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
    SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
    SepWPp.exists_elim fun u4 => SepWPp.exists_elim fun u5 =>
    SepWPp.exists_elim fun u6 => SepWPp.exists_elim fun u7 => SepWPp.exists_elim fun b_sret0 => ?_
  have hpoll := getIdentityKeyPairPoll_ok_trap (b := b) (C := C) (abs := abs)
  refine SepWPp.call_frame_frozen_nopanic
    (x := ({ futPtr := idKpFutPtr, sret := s.sp + 0x3e0#64, self := idStorePtr,
             ik0 := ik0, ik1 := ik1, ik2 := ik2, ik3 := ik3,
             ik4 := ik4, ik5 := ik5, ik6 := ik6, ik7 := ik7,
             b_sret0 := b_sret0, u0 := u0, u1 := u1, u2 := u2, u3 := u3,
             u4 := u4, u5 := u5, u6 := u6, u7 := u7 } : GetIdentityKeyPairPollGhost))
    (φ := s1.readReg64 .x0 = idKpFutPtr ∧ s1.readReg64 .x8 = s.sp + 0x3e0#64)
    (T := (idKpFutPtr ↦₆₄ idStorePtr) ∗ ((idKpFutPtr + 8#64) ↦₈ 0#8) ∗
          ((idStorePtr + 0x30#64) ↦₆₄ ik0) ∗ ((idStorePtr + 0x38#64) ↦₆₄ ik1) ∗
          ((idStorePtr + 0x40#64) ↦₆₄ ik2) ∗ ((idStorePtr + 0x48#64) ↦₆₄ ik3) ∗
          ((idStorePtr + 0x50#64) ↦₆₄ ik4) ∗ ((idStorePtr + 0x58#64) ↦₆₄ ik5) ∗
          ((idStorePtr + 0x60#64) ↦₆₄ ik6) ∗ ((idStorePtr + 0x68#64) ↦₆₄ ik7) ∗
          ((s.sp + 0x3e0#64) ↦₈ b_sret0) ∗
          ((s.sp + 0x3e0#64 + 0x01#64) ↦₆₄ u0) ∗ ((s.sp + 0x3e0#64 + 0x09#64) ↦₆₄ u1) ∗
          ((s.sp + 0x3e0#64 + 0x11#64) ↦₆₄ u2) ∗ ((s.sp + 0x3e0#64 + 0x19#64) ↦₆₄ u3) ∗
          ((s.sp + 0x3e0#64 + 0x21#64) ↦₆₄ u4) ∗ ((s.sp + 0x3e0#64 + 0x29#64) ↦₆₄ u5) ∗
          ((s.sp + 0x3e0#64 + 0x31#64) ↦₆₄ u6) ∗ ((s.sp + 0x3e0#64 + 0x39#64) ↦₆₄ u7))
    hF1 hsym1 hpoll hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [getIdentityKeyPairPollSpec])
    ⟨hx0_1, hx8_1⟩
    (by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  dsimp only [getIdentityKeyPairPollSpec]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, _, hx23_cs2, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2,
    hx28_cs2, hx29_cs2, _⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = coroPtr + 0x390#64 := by rw [hx21_cs2, hx21_1, hx21]
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0x4f2#64 := by rw [hx23_cs2, hx23_1, hx23]
  have hx24_2 : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_cs2, hx24_1, hx24, hsp2]
  have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hx25_cs2.trans hx25_1
  have hx26_2 : s2.readReg64 .x26 = s.readReg64 .x26 := hx26_cs2.trans hx26_1
  have hx26_2' : s2.readReg64 .x26 = coroPtr + 0x398#64 := hx26_2.trans hx26
  have hx27_2 : s2.readReg64 .x27 = ctxPtr := hx27_cs2.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  have hx29_2 : s2.readReg64 .x29 = fp := by rw [hx29_cs2, hx29_1, hx29]
  refine SepWPp.weaken_frame (Entails.of_eq hikStore_eq.symm) (by sep_focus) ?_
  have hbox1 : (idKpFutPtr ↦₆₄ idStorePtr) ∗ ((idKpFutPtr + 8#64) ↦₈ 1#8) ∗
      memRegion (idKpFutPtr + 9#64) 7 ⊢ memRegion idKpFutPtr 16 :=
    inMemId16Box_entails_memRegion idKpFutPtr idStorePtr 1#8
  refine SepWPp.weaken_frame hbox1 (by sep_focus) ?_
  have hkp_sp : ((s.sp + 0x3e0#64 + 0x01#64) ↦₆₄ ik0) ∗ ((s.sp + 0x3e0#64 + 0x09#64) ↦₆₄ ik1) ∗
      ((s.sp + 0x3e0#64 + 0x11#64) ↦₆₄ ik2) ∗ ((s.sp + 0x3e0#64 + 0x19#64) ↦₆₄ ik3) ∗
      ((s.sp + 0x3e0#64 + 0x21#64) ↦₆₄ ik4) ∗ ((s.sp + 0x3e0#64 + 0x29#64) ↦₆₄ ik5) ∗
      ((s.sp + 0x3e0#64 + 0x31#64) ↦₆₄ ik6) ∗ ((s.sp + 0x3e0#64 + 0x39#64) ↦₆₄ ik7) =
      keyPair64UnalignedAt (s.sp + 0x3e1#64)
        (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
        (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8)
        (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8) (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56
          8)
        (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8) (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56
          8)
        (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8) (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56
          8)
        (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
        (ik7.extractLsb' 56 8) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words8_eq_keyPair64UnalignedAt (s.sp + 0x3e1#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
  refine SepWPp.weaken_frame (Entails.of_eq hkp_sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion7_eq_bytes7At (s.sp + 0x3c8#64))) (by
    sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun s6_b => SepWPp.exists_elim fun s5_b =>
    SepWPp.exists_elim fun s4_b => SepWPp.exists_elim fun s3_b =>
    SepWPp.exists_elim fun s2_b => SepWPp.exists_elim fun s1_b => SepWPp.exists_elim fun s0_b => ?_
  have hdrop_nz : b + 0x01fe4#64 ≠ 0#64 := by
    intro h; rw [show b = 0#64 - 0x01fe4#64 by rw [← h,
      BitVec.add_sub_cancel]] at hb; exact absurd hb (by decide)
  have hstep3 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5b_fp_wp_trap b C abs s2 coroPtr msgPtr ctxPtr idKpFutPtr
    (b + bv% (ls_reloc% 0x7b34 - 24)) (b + 0x01fe4#64) fp
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) (coroPtr + 0x390#64)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_a8 (coroPtr + 0x390#64) v_b8 ctxPtr v_d0 u_b90
    opkId
    (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
    (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) (ik7.extractLsb' 56 8)
    s0_b s1_b s2_b s3_b s4_b s5_b s6_b b_b98
    (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8) (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
    (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8) (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
    (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8) (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
    (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
    hdrop_nz hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx23_2 hx24_2 hx26_2' hx27_2 hx29_2
  rw [hsp2] at hstep3
  refine SepWPp.bind_sepWP_frame hF2 hsym2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hF3 hsym3 hregs3
    => ?_
  rcases hregs3 with ⟨hsp3, htr3, _, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3,
    hx26_3, hx27_3, hx28_3, hx29_3, hx30_3⟩
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hfutDrop := SessionStoreImpl.futDrop_ok_trap (b := b) (C := C) (abs := abs)
  refine SepWPp.call_frame_frozen_nopanic (x := ()) (T := emp)
    hF3 hsym3 hfutDrop hpc3 hrun3 hsp3_al hx30_3
    (by simp [LibsignalPublicApi.StoreSession.futDropSpec]) True.intro (by sep_focus)
    (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hF4 hsym4 => ?_)
  dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr4_3 => ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, hx20_cs4, hx21_cs4, hx22_cs4, hx23_cs4, hx24_cs4, hx25_cs4,
    hx26_cs4, hx27_cs4, hx28_cs4, hx29_cs4, _⟩
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx20_4 : s4.readReg64 .x20 = ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8 :=
    hx20_cs4.trans hx20_3
  have hx21_4 : s4.readReg64 .x21 = idKpFutPtr := hx21_cs4.trans hx21_3
  have hx22_4 : s4.readReg64 .x22 = 0#64 := hx22_cs4.trans hx22_3
  have hx23_4 : s4.readReg64 .x23 = ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8 :=
    hx23_cs4.trans hx23_3
  have hx24_4 : s4.readReg64 .x24 = b + bv% (ls_reloc% 0x7b34 - 24) := hx24_cs4.trans hx24_3
  have hx25_4 : s4.readReg64 .x25 = s.readReg64 .x25 := by rw [hx25_cs4, hx25_3, hx25_2]
  have hx26_4 : s4.readReg64 .x26 = s.readReg64 .x26 := by rw [hx26_cs4, hx26_3, ← hx26]
  have hx27_4 : s4.readReg64 .x27 = ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8 :=
    hx27_cs4.trans hx27_3
  have hx28_4 : s4.readReg64 .x28 = s.sp + 0xa90#64 := by rw [hx28_cs4, hx28_3, ← hsp2, hx28_2]
  have hx29_4 : s4.readReg64 .x29 = fp := by rw [hx29_cs4, hx29_3]
  refine SepWPp.weaken_frame (coro798_64_entails_unaligned coroPtr) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c0_798 => SepWPp.exists_elim fun c1_798 =>
    SepWPp.exists_elim fun c2_798 => SepWPp.exists_elim fun c3_798 =>
    SepWPp.exists_elim fun c4_798 => SepWPp.exists_elim fun c5_798 => SepWPp.exists_elim fun c6_798
      =>
    SepWPp.exists_elim fun cw0 => SepWPp.exists_elim fun cw1 =>
    SepWPp.exists_elim fun cw2 => SepWPp.exists_elim fun cw3 =>
    SepWPp.exists_elim fun cw4 => SepWPp.exists_elim fun cw5 =>
    SepWPp.exists_elim fun cw6 => SepWPp.exists_elim fun c63_798 => ?_
  have hstk_alloc := stackAt_sub_eq s.sp stageP2bStack allocHookStack (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hstep5 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c1_fp_wp_trap b C abs hA s4
    coroPtr msgPtr remoteAddrPtr localAddrPtr idKpFutPtr (b + bv% (ls_reloc% 0x7b34 - 24))
    fp (msgPtr + 0x90#64)
    (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8) (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
    (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8) (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
    (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8) (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
    (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
    cw0 cw1 cw2 cw3 cw4 cw5 opkId
    (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
    (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) (ik7.extractLsb' 56 8)
    c0_798 c1_798 c2_798 c3_798 c4_798 c5_798 c6_798
    hpc4 hrun4 hsp4_align hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx27_4 hx29_4
  rw [hsp4] at hstep5
  refine SepWPp.bind_sepWP_frame hF4 hsym4 hstep5 (by sep_focus) fun s5 hpc5 hrun5 hF5 hsym5 hregs5
    => ?_
  rcases hregs5 with ⟨hsp5, htr5, hx0_5, hx1_5, hx3_5, hx8_5, hx9_5, hx10_5, hx11_5,
    hx19_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, _, hx28_5, hx29_5⟩
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5]; exact hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (bytes7At_entails_memRegion7 (s.sp + 0x3c8#64)
      (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8))
    (by sep_focus) ?_
  have hkp39 : bytes7At (coroPtr + 0x798#64)
        (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
        (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) ∗
      ((coroPtr + 0x79f#64) ↦₆₄ (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)) ∗
      ((coroPtr + 0x7a7#64) ↦₆₄ (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)) ∗
      ((coroPtr + 0x7af#64) ↦₆₄ (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)) ∗
      ((coroPtr + 0x7b7#64) ↦₆₄ (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)) =
      ((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
      ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
        bytes7At (coroPtr + 0x7b8#64)
        (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8) (ik4.extractLsb' 24 8)
        (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      keyPair39_eq_words4_bytes7 (coroPtr + 0x798#64) ik0 ik1 ik2 ik3 ik4
  refine SepWPp.weaken_frame (Entails.of_eq hkp39) (by sep_focus) ?_
  have hopk_4b0 :
      ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗
      ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) =
      ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗
      ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗ ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗
      ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
      ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
      ((coroPtr + 0x4f0#64) ↦₈ opk_b64) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hopk (coroPtr + 0x4b0#64)
  refine SepWPp.weaken_frame (Entails.of_eq hopk_4b0) (by sep_focus) ?_
  have hc930 : cells (s.sp + 0x930#64) 8 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
       ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
        ((s.sp + 0x930#64) ↦₆₄ u0) ∗ ((s.sp + 0x938#64) ↦₆₄ u1) ∗
        ((s.sp + 0x940#64) ↦₆₄ u2) ∗ ((s.sp + 0x948#64) ↦₆₄ u3) ∗
        ((s.sp + 0x950#64) ↦₆₄ u4) ∗ ((s.sp + 0x958#64) ↦₆₄ u5) ∗
        ((s.sp + 0x960#64) ↦₆₄ u6) ∗ ((s.sp + 0x968#64) ↦₆₄ u7)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc930) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_930 => SepWPp.exists_elim fun u_938 =>
    SepWPp.exists_elim fun u_940 => SepWPp.exists_elim fun u_948 =>
    SepWPp.exists_elim fun u_950 => SepWPp.exists_elim fun u_958 =>
    SepWPp.exists_elim fun u_960 => SepWPp.exists_elim fun u_968 => ?_
  have hstep6 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c2_wp_trap b C abs s5 coroPtr msgPtr
    ik0 ik1 ik2 ik3
    (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8) cw6
    u_930 u_938 u_940 u_948
    (ik7.extractLsb' 56 8) c63_798 opk_b64
    hpc5 hrun5 hx8_5 hx9_5 hx10_5 hx11_5 hx19_5 (by rw [hsp5, hx23_5])
  rw [hsp5] at hstep6
  refine SepWPp.bind_sepWP_frame hF5 hsym5 hstep6 (by sep_focus) fun s6 hpc6 hrun6 hF6 hsym6 hregs6
    => ?_
  rcases hregs6 with ⟨hsp6, htr6, hx0_6, hx1_6, hx2_6, hx3_6, hx8_6, hx9_6, hx10_6,
    hx19_6, hx21_6, hx22_6, hx23_6, hx24_6, hx25_6, hx26_6, _, hx28_6, hx29_6⟩
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
  have hkp32hi : bytes7At (coroPtr + 0x7b8#64)
        (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8) (ik4.extractLsb' 24 8)
        (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) ∗
      ((coroPtr + 0x7bf#64) ↦₆₄ (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)) ∗
      ((coroPtr + 0x7c7#64) ↦₆₄ (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)) ∗
      ((coroPtr + 0x7cf#64) ↦₆₄ (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)) ∗
      ((coroPtr + 0x7d7#64) ↦₈ (ik7.extractLsb' 56 8)) =
      ((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
      ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x7d0#64) ↦₆₄ ik7) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      keyPair32Hi_eq_words4 (coroPtr + 0x7b8#64) ik4 ik5 ik6 ik7
  refine SepWPp.weaken_frame (Entails.of_eq hkp32hi) (by sep_focus) ?_
  have hspk_398 :
      ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
        ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) =
      ((coroPtr + 0x398#64) ↦₆₄ spk0) ∗ ((coroPtr + 0x3a0#64) ↦₆₄ spk1) ∗
      ((coroPtr + 0x3a8#64) ↦₆₄ spk2) ∗ ((coroPtr + 0x3b0#64) ↦₆₄ spk3) ∗
      ((coroPtr + 0x3b8#64) ↦₆₄ spk4) ∗ ((coroPtr + 0x3c0#64) ↦₆₄ spk5) ∗
      ((coroPtr + 0x3c8#64) ↦₆₄ spk6) ∗ ((coroPtr + 0x3d0#64) ↦₆₄ spk7) := by
    rw [hspkPk (coroPtr + 0x398#64), hspkSk (coroPtr + 0x3b8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hekA_msg : ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) =
      ((msgPtr + 0xa8#64) ↦₆₄ ekA0) ∗ ((msgPtr + 0xb0#64) ↦₆₄ ekA1) ∗
      ((msgPtr + 0xb8#64) ↦₆₄ ekA2) ∗ ((msgPtr + 0xc0#64) ↦₆₄ ekA3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hekA (msgPtr + 0xa8#64)
  have hikA_msg : ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) =
      ((msgPtr + 0xc8#64) ↦₆₄ ikA0) ∗ ((msgPtr + 0xd0#64) ↦₆₄ ikA1) ∗
      ((msgPtr + 0xd8#64) ↦₆₄ ikA2) ∗ ((msgPtr + 0xe0#64) ↦₆₄ ikA3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hikA (msgPtr + 0xc8#64)
  have hsp3e0_unfold : ((s.sp + 0x3e0#64) ↦₈ 0#8) ∗ keyPair64UnalignedAt (s.sp + 0x3e1#64)
        (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
        (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8)
        (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8) (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56
          8)
        (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8) (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56
          8)
        (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8) (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56
          8)
        (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
        (ik7.extractLsb' 56 8) ⊢
      memRegion (s.sp + 0x3e0#64) 65 := by
    rw [← hkp_sp]
    exact pointsTo8_words8_entails_memRegion65 (s.sp + 0x3e0#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 0#8
  refine SepWPp.weaken_frame hsp3e0_unfold (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hspk_398) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hekA_msg) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hikA_msg) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion65_eq_words8_byte (s.sp + 0x3e0#64))) (by
    sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_420 => SepWPp.exists_elim fun u_3e0 => SepWPp.exists_elim fun
    u_3e8 =>
    SepWPp.exists_elim fun u_3f0 => SepWPp.exists_elim fun u_3f8 =>
    SepWPp.exists_elim fun u_400 => SepWPp.exists_elim fun u_408 =>
    SepWPp.exists_elim fun u_410 => SepWPp.exists_elim fun u_418 => ?_
  have hca90 : cells (s.sp + 0xa90#64) 8 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
       ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
        ((s.sp + 0xa90#64) ↦₆₄ u0) ∗ ((s.sp + 0xa98#64) ↦₆₄ u1) ∗
        ((s.sp + 0xaa0#64) ↦₆₄ u2) ∗ ((s.sp + 0xaa8#64) ↦₆₄ u3) ∗
        ((s.sp + 0xab0#64) ↦₆₄ u4) ∗ ((s.sp + 0xab8#64) ↦₆₄ u5) ∗
        ((s.sp + 0xac0#64) ↦₆₄ u6) ∗ ((s.sp + 0xac8#64) ↦₆₄ u7)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hca90) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_a90 => SepWPp.exists_elim fun u_a98 =>
    SepWPp.exists_elim fun u_aa0 => SepWPp.exists_elim fun u_aa8 =>
    SepWPp.exists_elim fun u_ab0 => SepWPp.exists_elim fun u_ab8 =>
    SepWPp.exists_elim fun u_ac0 => SepWPp.exists_elim fun u_ac8 => ?_
  have hc560 : cells (s.sp + 0x560#64) 4 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((s.sp + 0x560#64) ↦₆₄ u0) ∗ ((s.sp + 0x568#64) ↦₆₄ u1) ∗
        ((s.sp + 0x570#64) ↦₆₄ u2) ∗ ((s.sp + 0x578#64) ↦₆₄ u3)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc560) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_560 => SepWPp.exists_elim fun u_568 =>
    SepWPp.exists_elim fun u_570 => SepWPp.exists_elim fun u_578 => ?_
  have hc6a0 : cells (s.sp + 0x6a0#64) 4 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((s.sp + 0x6a0#64) ↦₆₄ u0) ∗ ((s.sp + 0x6a8#64) ↦₆₄ u1) ∗
        ((s.sp + 0x6b0#64) ↦₆₄ u2) ∗ ((s.sp + 0x6b8#64) ↦₆₄ u3)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc6a0) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_6a0 => SepWPp.exists_elim fun u_6a8 =>
    SepWPp.exists_elim fun u_6b0 => SepWPp.exists_elim fun u_6b8 => ?_
  have hc7e0 : cells (s.sp + 0x7e0#64) 4 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((s.sp + 0x7e0#64) ↦₆₄ u0) ∗ ((s.sp + 0x7e8#64) ↦₆₄ u1) ∗
        ((s.sp + 0x7f0#64) ↦₆₄ u2) ∗ ((s.sp + 0x7f8#64) ↦₆₄ u3)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc7e0) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_7e0 => SepWPp.exists_elim fun u_7e8 =>
    SepWPp.exists_elim fun u_7f0 => SepWPp.exists_elim fun u_7f8 => ?_
  have hstep7 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c3_wp_trap b C abs s6 coroPtr msgPtr localAddrPtr remoteAddrPtr
    ik4 ik5 ik6 ik7
    spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
    kyberKpPubPtr 0x620#64 kyberKpSecPtr 0xc60#64
    ikA0 ikA1 ikA2 ikA3
    ekA0 ekA1 ekA2 ekA3
    u_950 u_958 u_960 u_968
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8 u_ac0 u_ac8
    u_3e0 u_3e8 u_3f0 u_3f8 u_400 u_408 u_410 u_418
    u_560 u_568 u_570 u_578
    u_6a0 u_6a8 u_6b0 u_6b8
    u_7e0 u_7e8 u_7f0 u_7f8
    opk_b64 u_420 b_4f1
    hpc6 hrun6 hsp6_align
    (hx0_6.trans hx0_5) (hx1_6.trans hx1_5) hx2_6 (hx3_6.trans hx3_5)
    hx8_6 hx9_6 hx10_6 hx19_6
    (by rw [hx22_6, hx22_5, hsp6]) (by rw [hx23_6, hsp6]) (hx24_6.trans hx24_5)
    (by rw [hx28_6, hx28_5, hx28_4, hsp6])
  rw [hsp6] at hstep7
  refine SepWPp.bind_sepWP_frame hF6 hsym6
    (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hstep7)
    (by sep_focus)
    fun s7 hpc7 hrun7 hF7 hsym7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7, htr7, hx0_7, hx1_7, hx2_7, hx3_7, hx19_7, hx21_7, hx22_7, hx23_7,
    hx24_7, hx25_7, hx26_7, _, hx28_7, hx29_7, hx30_7⟩
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7] using hsp_align
  let localIk : IdentityKey := ⟨⟨⟨bytesToBv8 ikBPk, hikBPk_bv⟩⟩⟩
  let remoteIk : IdentityKey := ⟨⟨⟨bytesToBv8 inp.hdr.ikAPk, hikAPk_bv⟩⟩⟩
  have hneq' : localIk ≠ remoteIk ∨ DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes :=
    hneq.imp (fun h => identityKey_ne_of_bytes_ne hikBPk_bv hikAPk_bv (fun h_eq => h (congrArg
      bytesToBv8 h_eq))) id
  have hlocIk_eq : ((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
      ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) =
      ((coroPtr + 0x798#64) ↦ₛ localIk.publicKey.bytes.toList) := by
    change _ = ((coroPtr + 0x798#64) ↦ₛ bytesToBv8 ikBPk)
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikB0 (coroPtr + 0x798#64)).symm
  have hremIk_eq : ((msgPtr + 0xc8#64) ↦₆₄ ikA0) ∗ ((msgPtr + 0xd0#64) ↦₆₄ ikA1) ∗
      ((msgPtr + 0xd8#64) ↦₆₄ ikA2) ∗ ((msgPtr + 0xe0#64) ↦₆₄ ikA3) =
      ((msgPtr + 0xc8#64) ↦ₛ remoteIk.publicKey.bytes.toList) :=
    hikA_msg.symm
  refine SepWPp.weaken_frame (Entails.of_eq hlocIk_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hremIk_eq) (by sep_focus) ?_
  have hstk_same := stackAt_sub_eq s.sp stageP2bStack isSameAccountDistinctStack (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hstk_same) (by sep_focus) ?_
  have hsame := isSameAccountEqDistinct_ok_trap b C A abs
  have hfn_same : (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64) =
      (trTrapProgAt b C abs).fnAddr Getters.isSameAccountName := by
    simp only [trTrapProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"),
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"), BitVec.add_assoc]
    rfl
  rw [hfn_same] at hpc7
  refine SepWPp.call_frame_frozen_nopanic
    (x := ({ localIkA := coroPtr + 0x798#64, localIk := localIk,
             locA := localAddrPtr, loc := gMe,
             remoteIkA := msgPtr + 0xc8#64, remoteIk := remoteIk,
             remA := remoteAddrPtr, rem := gPeer } : IsSameAccountDistinctGhost))
    (φ := s7.readReg64 .x0 = coroPtr + 0x798#64 ∧ s7.readReg64 .x1 = localAddrPtr ∧
          s7.readReg64 .x2 = msgPtr + 0xc8#64 ∧ s7.readReg64 .x3 = remoteAddrPtr ∧
          (localIk ≠ remoteIk ∨ DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes))
    (T := ((coroPtr + 0x798#64) ↦ₛ localIk.publicKey.bytes.toList) ∗
          protocolAddressAt A gMe localAddrPtr ∗
          ((msgPtr + 0xc8#64) ↦ₛ remoteIk.publicKey.bytes.toList) ∗
          protocolAddressAt A gPeer remoteAddrPtr ∗ stackAt s.sp isSameAccountDistinctStack)
    hF7 hsym7 hsame hpc7 hrun7 hsp7_al hx30_7
    (by dsimp only [isSameAccountDistinctSpec]; rw [hsp7])
    ⟨hx0_7, hx1_7, hx2_7, hx3_7, hneq'⟩ (by sep_focus)
    (hnext := fun s8 hpc8 hrun8 hsp8_7 _ hcs8 hF8 hsym8 => ?_)
  dsimp only [isSameAccountDistinctSpec]; rw [hsp7]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0_8_lo, htr8_7⟩ => ?_
  have hsp8 : s8.sp = s.sp := hsp8_7.trans hsp7
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, hx21_cs8, hx22_cs8, hx23_cs8, hx24_cs8, hx25_cs8, hx26_cs8, _,
    hx28_cs8, hx29_cs8, _⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx21_8 : s8.readReg64 .x21 = msgPtr + 0x90#64 := by rw [hx21_cs8, hx21_7, hx21_6, hx21_5]
  have hx22_8 : s8.readReg64 .x22 = s8.sp + 0x370#64 := by rw [hx22_cs8, hx22_7, hsp8]
  have hx23_8 : s8.readReg64 .x23 = s8.sp + 0x930#64 := by rw [hx23_cs8, hx23_7, hsp8]
  have hx24_8 : s8.readReg64 .x24 = coroPtr + 0x398#64 := hx24_cs8.trans hx24_7
  have hx25_8 : s8.readReg64 .x25 = s.readReg64 .x25 :=
    by rw [hx25_cs8, hx25_7, hx25_6, hx25_5, hx25_4]
  have hx26_8 : s8.readReg64 .x26 = s.readReg64 .x26 :=
    by rw [hx26_cs8, hx26_7, hx26_6, hx26_5, hx26_4]
  have hx28_8 : s8.readReg64 .x28 = s8.sp + 0xa90#64 := by rw [hx28_cs8, hx28_7, hsp8]
  have hx29_8 : s8.readReg64 .x29 = fp := by rw [hx29_cs8, hx29_7, hx29_6, hx29_5]
  refine SepWPp.weaken_frame (Entails.of_eq hstk_same.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hlocIk_eq.symm) (by sep_focus) ?_
  have h798_64 : ((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
      ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
      ((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
      ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x7d0#64) ↦₆₄ ik7) ⊢
      memRegion (coroPtr + 0x798#64) 64 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words8_entails_memRegion64 (coroPtr + 0x798#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
  refine SepWPp.weaken_frame h798_64 (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hspk_398.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hopk_4b0.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hekA_msg.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (coro658_298_eq coroPtr)) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c_781 => SepWPp.exists_elim fun c_780 => ?_
  have hc658 : cells (coroPtr + 0x658#64) 37 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c14 : BitVec 64, ∃∗ c15 : BitVec 64,
       ∃∗ c16 : BitVec 64, ∃∗ c17 : BitVec 64, ∃∗ c18 : BitVec 64, ∃∗ c19 : BitVec 64,
       ∃∗ c20 : BitVec 64, ∃∗ c21 : BitVec 64, ∃∗ c22 : BitVec 64, ∃∗ c23 : BitVec 64,
       ∃∗ c24 : BitVec 64, ∃∗ c25 : BitVec 64, ∃∗ c26 : BitVec 64, ∃∗ c27 : BitVec 64,
       ∃∗ c28 : BitVec 64, ∃∗ c29 : BitVec 64, ∃∗ c30 : BitVec 64, ∃∗ c31 : BitVec 64,
       ∃∗ c32 : BitVec 64, ∃∗ c33 : BitVec 64, ∃∗ c34 : BitVec 64, ∃∗ c35 : BitVec 64,
       ∃∗ c36 : BitVec 64,
        ((coroPtr + 0x658#64) ↦₆₄ c0) ∗ ((coroPtr + 0x660#64) ↦₆₄ c1) ∗
        ((coroPtr + 0x668#64) ↦₆₄ c2) ∗ ((coroPtr + 0x670#64) ↦₆₄ c3) ∗
        ((coroPtr + 0x678#64) ↦₆₄ c4) ∗ ((coroPtr + 0x680#64) ↦₆₄ c5) ∗
        ((coroPtr + 0x688#64) ↦₆₄ c6) ∗ ((coroPtr + 0x690#64) ↦₆₄ c7) ∗
        ((coroPtr + 0x698#64) ↦₆₄ c8) ∗ ((coroPtr + 0x6a0#64) ↦₆₄ c9) ∗
        ((coroPtr + 0x6a8#64) ↦₆₄ c10) ∗ ((coroPtr + 0x6b0#64) ↦₆₄ c11) ∗
        ((coroPtr + 0x6b8#64) ↦₆₄ c12) ∗ ((coroPtr + 0x6c0#64) ↦₆₄ c13) ∗
        ((coroPtr + 0x6c8#64) ↦₆₄ c14) ∗ ((coroPtr + 0x6d0#64) ↦₆₄ c15) ∗
        ((coroPtr + 0x6d8#64) ↦₆₄ c16) ∗ ((coroPtr + 0x6e0#64) ↦₆₄ c17) ∗
        ((coroPtr + 0x6e8#64) ↦₆₄ c18) ∗ ((coroPtr + 0x6f0#64) ↦₆₄ c19) ∗
        ((coroPtr + 0x6f8#64) ↦₆₄ c20) ∗ ((coroPtr + 0x700#64) ↦₆₄ c21) ∗
        ((coroPtr + 0x708#64) ↦₆₄ c22) ∗ ((coroPtr + 0x710#64) ↦₆₄ c23) ∗
        ((coroPtr + 0x718#64) ↦₆₄ c24) ∗ ((coroPtr + 0x720#64) ↦₆₄ c25) ∗
        ((coroPtr + 0x728#64) ↦₆₄ c26) ∗ ((coroPtr + 0x730#64) ↦₆₄ c27) ∗
        ((coroPtr + 0x738#64) ↦₆₄ c28) ∗ ((coroPtr + 0x740#64) ↦₆₄ c29) ∗
        ((coroPtr + 0x748#64) ↦₆₄ c30) ∗ ((coroPtr + 0x750#64) ↦₆₄ c31) ∗
        ((coroPtr + 0x758#64) ↦₆₄ c32) ∗ ((coroPtr + 0x760#64) ↦₆₄ c33) ∗
        ((coroPtr + 0x768#64) ↦₆₄ c34) ∗ ((coroPtr + 0x770#64) ↦₆₄ c35) ∗
        ((coroPtr + 0x778#64) ↦₆₄ c36)) := by
    simp (config := { maxSteps :=
      1000000 }) only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc658) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c_658 => SepWPp.exists_elim fun c_660 =>
    SepWPp.exists_elim fun c_668 => SepWPp.exists_elim fun c_670 =>
    SepWPp.exists_elim fun c_678 => SepWPp.exists_elim fun c_680 =>
    SepWPp.exists_elim fun c_688 => SepWPp.exists_elim fun c_690 =>
    SepWPp.exists_elim fun c_698 => SepWPp.exists_elim fun c_6a0 =>
    SepWPp.exists_elim fun c_6a8 => SepWPp.exists_elim fun c_6b0 =>
    SepWPp.exists_elim fun c_6b8 => SepWPp.exists_elim fun c_6c0 =>
    SepWPp.exists_elim fun c_6c8 => SepWPp.exists_elim fun c_6d0 =>
    SepWPp.exists_elim fun c_6d8 => SepWPp.exists_elim fun c_6e0 =>
    SepWPp.exists_elim fun c_6e8 => SepWPp.exists_elim fun c_6f0 =>
    SepWPp.exists_elim fun c_6f8 => SepWPp.exists_elim fun c_700 =>
    SepWPp.exists_elim fun c_708 => SepWPp.exists_elim fun c_710 =>
    SepWPp.exists_elim fun c_718 => SepWPp.exists_elim fun c_720 =>
    SepWPp.exists_elim fun c_728 => SepWPp.exists_elim fun c_730 =>
    SepWPp.exists_elim fun c_738 => SepWPp.exists_elim fun c_740 =>
    SepWPp.exists_elim fun c_748 => SepWPp.exists_elim fun c_750 =>
    SepWPp.exists_elim fun c_758 => SepWPp.exists_elim fun c_760 =>
    SepWPp.exists_elim fun c_768 => SepWPp.exists_elim fun c_770 => SepWPp.exists_elim fun c_778 =>
      ?_
  have hstep9 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5d_wp_trap b C abs s8 coroPtr (msgPtr + 0x90#64) (s8.readReg64 .x0)
    ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
    spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
    kyberKpPubPtr 0x620#64 kyberKpSecPtr 0xc60#64
    ikA0 ikA1 ikA2 ikA3
    ekA0 ekA1 ekA2 ekA3
    c_658 c_660 c_668 c_670 c_678 c_680 c_688 c_690
    c_698 c_6a0 c_6a8 c_6b0 c_6b8 c_6c0 c_6c8 c_6d0
    c_6d8 c_6e0 c_6e8 c_6f0
    c_6f8 c_700 c_708 c_710
    c_718 c_720 c_728 c_730 c_738
    c_740 c_748 c_750 c_758 c_760 c_768 c_770 c_778
    opk_b64 c_780 c_781
    hpc8 hrun8 hsp8_align rfl hx19_8 hx21_8 hx22_8 hx23_8 hx24_8 hx28_8
  rw [hsp8, setWidth8_eq_zero_of_setWidth32 hx0_8_lo] at hstep9
  refine SepWPp.bind_sepWP_frame hF8 hsym8
    (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hstep9)
    (by sep_focus)
    fun s9 hpc9 hrun9 hF9 hsym9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9, htr9, hx0_9, hx1_9, hx8_9, hx19_9, hx21_9, hx22_9, hx23_9, hx24_9,
    hx25_9, hx26_9, _, hx28_9, hx29_9, hx30_9⟩
  have hsp9_al : s9.spAligned = true := by simpa only [State.spAligned, hsp9] using hsp_align
  refine SepWPp.weaken_frame
    (words8_byte_entails_memRegion65 (s.sp + 0x3e0#64) opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
      opk_b64)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp3e0_344_split_65_279 s.sp).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words8_entails_cells8 (s.sp + 0x930#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words8_entails_cells8 (s.sp + 0xa90#64) spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words4_entails_cells4 (s.sp + 0x560#64) kyberKpPubPtr 0x620#64 kyberKpSecPtr 0xc60#64)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words4_entails_cells4 (s.sp + 0x6a0#64) ikA0 ikA1 ikA2 ikA3)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words4_entails_cells4 (s.sp + 0x7e0#64) ekA0 ekA1 ekA2 ekA3)
    (by sep_focus) ?_
  have hikB0_658 : ((coroPtr + 0x658#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x660#64) ↦₆₄ ik1) ∗
      ((coroPtr + 0x668#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x670#64) ↦₆₄ ik3) =
      ((coroPtr + 0x658#64) ↦ₛ bytesToBv8 ikBPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikB0 (coroPtr + 0x658#64)).symm
  have hikB1_678 : ((coroPtr + 0x678#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x680#64) ↦₆₄ ik5) ∗
      ((coroPtr + 0x688#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x690#64) ↦₆₄ ik7) =
      ((coroPtr + 0x678#64) ↦ₛ bytesToBv8 inp.ikBSk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikB1 (coroPtr + 0x678#64)).symm
  have hspkPk_698 : ((coroPtr + 0x698#64) ↦₆₄ spk0) ∗ ((coroPtr + 0x6a0#64) ↦₆₄ spk1) ∗
      ((coroPtr + 0x6a8#64) ↦₆₄ spk2) ∗ ((coroPtr + 0x6b0#64) ↦₆₄ spk3) =
      ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hspkPk (coroPtr + 0x698#64)).symm
  have hspkSk_6b8 : ((coroPtr + 0x6b8#64) ↦₆₄ spk4) ∗ ((coroPtr + 0x6c0#64) ↦₆₄ spk5) ∗
      ((coroPtr + 0x6c8#64) ↦₆₄ spk6) ∗ ((coroPtr + 0x6d0#64) ↦₆₄ spk7) =
      ((coroPtr + 0x6b8#64) ↦ₛ bytesToBv8 inp.spkBSk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hspkSk (coroPtr + 0x6b8#64)).symm
  have hikA_6d8 : ((coroPtr + 0x6d8#64) ↦₆₄ ikA0) ∗ ((coroPtr + 0x6e0#64) ↦₆₄ ikA1) ∗
      ((coroPtr + 0x6e8#64) ↦₆₄ ikA2) ∗ ((coroPtr + 0x6f0#64) ↦₆₄ ikA3) =
      ((coroPtr + 0x6d8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc] using (hikA (coroPtr + 0x6d8#64)).symm
  have hekA_6f8 : ((coroPtr + 0x6f8#64) ↦₆₄ ekA0) ∗ ((coroPtr + 0x700#64) ↦₆₄ ekA1) ∗
      ((coroPtr + 0x708#64) ↦₆₄ ekA2) ∗ ((coroPtr + 0x710#64) ↦₆₄ ekA3) =
      ((coroPtr + 0x6f8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc] using (hekA (coroPtr + 0x6f8#64)).symm
  have hopk_740 : ((coroPtr + 0x740#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x748#64) ↦₆₄ opk1) ∗
      ((coroPtr + 0x750#64) ↦₆₄ opk2) ∗ ((coroPtr + 0x758#64) ↦₆₄ opk3) ∗
      ((coroPtr + 0x760#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x768#64) ↦₆₄ opk5) ∗
      ((coroPtr + 0x770#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x778#64) ↦₆₄ opk7) ∗
      ((coroPtr + 0x780#64) ↦₈ opk_b64) =
      ((coroPtr + 0x740#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
      ((coroPtr + 0x761#64) ↦ₛ opkSkBytes) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc] using (hopk (coroPtr + 0x740#64)).symm
  refine SepWPp.weaken_frame (Entails.of_eq hikB0_658) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hikB1_678) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hspkPk_698) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hspkSk_6b8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hikA_6d8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hekA_6f8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hopk_740) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (opkSlot65_eq_optField (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes hopkSk_eq))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (bobParamsFieldsAt_intro coroPtr msgPtr kyberKpSecPtr ctBufPtr inp ikBPk spkBPk))
    (by sep_focus) ?_
  have hinitBob := initializeBobSession_err_ok_trap (C := C)
    himg hWF hH hP
  rw [hbase] at hinitBob
  have hfn_initBob : (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "libsignal_protocol::ratchet::initialize_bob_session" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64) =
      (trTrapProgAt b C abs).fnAddr initializeBobSessionSym := by
    simp only [trTrapProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"),
      (ls_lemma% fnOff "libsignal_protocol::ratchet::initialize_bob_session"), BitVec.add_assoc]
    rfl
  rw [hfn_initBob] at hpc9
  have hlog_eq : logFilterAddr img = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by unfold logFilterAddr; rw [hbase]
  have htr9_0 : s9.trace = s0.trace := by
    rw [htr9, htr8_7, htr7, htr6, htr5, htr4_3, htr3, htr2_1, htr1, htr]
  refine SepWPp.call_frame_inImage_oom
    (x := ({ inp := inp, ikBPk := ikBPk, spkBPk := spkBPk, sameAccountByte := 0#8,
             argPtr := coroPtr + 0x658#64, pqskPtr := kyberKpSecPtr,
             ctSlicePtr := msgPtr + 0x90#64, ctBufPtr := ctBufPtr,
             ratchetKeyPairPtr := coroPtr + 0x398#64, outPtr :=
               s.sp + 0x3e0#64 } : InitBobCallGhost))
    (T := bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
            (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ stackAt s.sp stageP2bStack ∗ A.pool)
    hF9 hsym9 htr9_0 hinitBob hpc9 hrun9 hsp9_al hx30_9
    (φ := s9.readReg64 .x0 = coroPtr + 0x658#64 ∧ s9.readReg64 .x1 = coroPtr + 0x398#64 ∧
          s9.readReg64 .x8 = s.sp + 0x3e0#64 ∧ inp.trustedPeer = true ∧ inp.replayOk = true ∧
          inp.hdr.opkId?.isSome = inp.opkBSk?.isSome ∧ WellSizedAcceptKeysInput inp ∧
            ikBPk.length = 32 ∧
          spkBPk.length = 32 ∧ Model.acceptKeys P inp = none)
    (by
      dsimp only [initializeBobSessionErrInnerSpec, stageP2bStack]; rw [hlog_eq, hsp9])
    ⟨hx0_9, hx1_9, hx8_9, htrusted, hreplay, hopk_match, hwell, hikBPk_len, hspkBPk_len, hacc_none⟩
    (by sep_focus) (by intro _; rfl) (by intro _ _; rfl)
    fun sf hpcf hrunf hspf_9 _ hcsf hFf hsymf => ?_
  dsimp only [initializeBobSessionErrInnerSpec, initializeBobSessionInnerSpec]
  rw [hlog_eq, hsp9]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htrf_9 => ?_
  rcases hcsf with ⟨hx19_csf, _, hx21_csf, hx22_csf, hx23_csf, hx24_csf, hx25_csf, hx26_csf, _,
    hx28_csf, hx29_csf, _⟩
  have h490_fold : ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
    ((coroPtr + 0x500#64) ↦₆₄ (b + bv% (ls_reloc% 0x7b34 - 24))) ⊢
      cells (coroPtr + 0x4f8#64) 2 := by
    rw [hc4f8]
    exact Entails.sepExists_right idKpFutPtr (Entails.sepExists_right (b + bv% (ls_reloc% 0x7b34 - 24)) (Entails.refl
      _))
  refine SepWPp.weaken_frame h490_fold (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hvt_eq.symm) (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ⟨?_, hspf_9.trans hsp9, htrf_9.trans htr9_0,
    hx19_csf.trans hx19_9,
    hx21_csf.trans hx21_9,
    hx22_csf.trans hx22_9,
    hx23_csf.trans hx23_9,
    hx24_csf.trans hx24_9,
    by rw [hx25_csf, hx25_9, hx25_8],
    by rw [hx26_csf, hx26_9, hx26_8],
    hx28_csf.trans hx28_9,
    by rw [hx29_csf, hx29_9, hx29_8],
    hFf, hsymf⟩
  refine Entails.sepExists_right (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)
    (Entails.sepExists_right (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)
      (Entails.sepExists_right (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
        (Entails.sepExists_right (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
          (Entails.sepExists_right (ik7.extractLsb' 56 8) ?_))))
  dsimp only [remoteIk, stageP2bStack]
  have hfp80 : fp - 128#64 = fp + 0xffffffffffffff80#64 := by bv_omega
  have hfp78 : fp - 120#64 = fp + 0xffffffffffffff88#64 := by bv_omega
  rw [hfp80, hfp78]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 8000000 in
/-- Stage P2 Substage 5 (`stageP2_sub5_ok`, `+0x36ac#64 -> +0x125c#64`): Composes `p2_seg5a_wp`, `getIdentityKeyPairPoll_ok`, `p2_seg5b_fp_wp`,
  `SessionStoreImpl.futDrop_ok`,
`p2_seg5c1_fp_wp`, `p2_seg5c2_wp`, `p2_seg5c3_wp`, `Glue.is_same_account_ok`,
`p2_seg5d_wp`, and `CryptoCallees.initializeBobSession_ok`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.stageP2_sub5_ok {P : Primitives} {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State))
    (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes) (opkPkBytes opkSkBytes : List (BitVec 8))
    (gMe gPeer : AddrGhost)
    (himg : Obj.Loads libsignalSessionImage img) (hbase : img.base = b) (hWF : StructuralPrims P)
    (hH : ResponderCore.PqxdhHookContracts P A img abs) (hP : PrimitivesMatchCrypto P C)
    (htrusted : inp.trustedPeer = true) (hreplay : inp.replayOk = true)
    (hopk_match : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome) (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hacc_none : Model.acceptKeys P inp = none)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (hneq : bytesToBv8 ikBPk ≠ bytesToBv8 inp.hdr.ikAPk ∨
      DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes) (s0 s : State)
    (coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idKpFutPtr kyberKpPubPtr kyberKpSecPtr ctBufPtr fp
     v_a8 v_b8 v_d0 u_b90 : BitVec 64)
    (opkId : BitVec 32) (b_4f1 b_b98 : BitVec 8) (hb : b &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x36ac#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace =
      s0.trace)
    (hx0 : s.readReg64 .x0 = idKpFutPtr) (hx1 : s.readReg64 .x1 = b + bv% (ls_reloc% 0x7b34 - 24))
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = coroPtr + 0x390#64)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x125c#64) s
      (A.live idKpFutPtr 16 8 ∗ inMemId16BoxAt idKpFutPtr idStorePtr 0#8 ∗
       futVtableAtP (b + bv% (ls_reloc% 0x7b34 - 24)) (b + 0x01fe4#64) 16#64 8#64 (b + 0x07b34#64) ∗
       ((idStorePtr + 0x30#64) ↦ₛ bytesToBv8 ikBPk) ∗
         ((idStorePtr + 0x50#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
       ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       cells (coroPtr + 0x4f8#64) 2 ∗ ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
       ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ memRegion (coroPtr + 0x658#64) 298 ∗
       memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
       ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       (kyberKpSecPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
       ((kyberKpSecPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗ (ctBufPtr ↦₈ 8#8) ∗
       ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
       ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
       memRegion (s.sp + 0x3c8#64) 7 ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ cells (s.sp + 0x560#64) 4 ∗
       cells (s.sp + 0x6a0#64) 4 ∗ cells (s.sp + 0x7e0#64) 4 ∗ cells (s.sp + 0x930#64) 8 ∗
       cells (s.sp + 0xa90#64) 8 ∗ ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗
       ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗
       stackAt s.sp stageP2bStack)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ v_a8' : BitVec 64, ∃∗ v_b8' : BitVec 64, ∃∗ v_d0' : BitVec 64,
          ∃∗ u_b90' : BitVec 64, ∃∗ b_b98' : BitVec 8,
            bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
              (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
            (match Model.acceptKeys P inp with
             | some drKey =>
               ∃∗ localIkBoxPtr : BitVec 64, ∃∗ remoteIkBoxPtr : BitVec 64,
                 ∃∗ rootKeyBoxPtr : BitVec 64,
               ∃∗ baseKeyBoxPtr : BitVec 64, ∃∗ ratchetPubBoxPtr : BitVec 64,
               ∃∗ ratchetPrivBoxPtr : BitVec 64, ∃∗ chainKeyBoxPtr : BitVec 64,
                 ∃∗ pad_f4 : BitVec 32,
               ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
                 ∃∗ c4 : BitVec 64,
               ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
                 ⌜localIkBoxPtr ≠ 0 ∧ remoteIkBoxPtr ≠ 0 ∧ rootKeyBoxPtr ≠ 0 ∧ baseKeyBoxPtr ≠ 0 ∧
                   ratchetPubBoxPtr ≠ 0 ∧ ratchetPrivBoxPtr ≠ 0 ∧ chainKeyBoxPtr ≠ 0⌝ ∗
                 (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
                 (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
                   A.live remoteIkBoxPtr 33 1 ∗
                 (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
                 (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
                   A.live baseKeyBoxPtr 33 1 ∗
                 (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
                   A.live ratchetPubBoxPtr 33 1 ∗
                 (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
                 (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
                 ((s.sp + 0x3e0#64) ↦ₛ bobSession344Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr
                   baseKeyBoxPtr
                   0#64 1#64 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
                   pad_f4 c0 c1 c2 c3 c4 d0 d1 d2)
             | none =>
               initBobErrAt (s.sp + 0x3e0#64) ∗ anyHeap) ∗
            futVtableAtP (b + bv% (ls_reloc% 0x7b34 - 24)) (b + 0x01fe4#64) 16#64 8#64 (b + 0x07b34#64) ∗
            ((idStorePtr + 0x30#64) ↦ₛ bytesToBv8 ikBPk) ∗
            ((idStorePtr + 0x50#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
            ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
            ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
              ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
            cells (coroPtr + 0x4f8#64) 2 ∗ ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
            ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
            ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
            opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
            memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
            ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
            ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
            protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
            ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
              ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((s.sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
            ((s.sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ v_d0') ∗ memRegion (s.sp + 0x3c8#64) 7 ∗
              cells (s.sp + 0x560#64) 4 ∗
            cells (s.sp + 0x6a0#64) 4 ∗ cells (s.sp + 0x7e0#64) 4 ∗ cells (s.sp + 0x930#64) 8 ∗
            cells (s.sp + 0xa90#64) 8 ∗ ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗
            ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗
            stackAt s.sp stageP2bStack) ∧ sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x21 = msgPtr + 0x90#64 ∧
        sf.readReg64 .x22 = s.sp + 0x370#64 ∧ sf.readReg64 .x23 = s.sp + 0x930#64 ∧
        sf.readReg64 .x24 = coroPtr + 0x398#64 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.sp + 0xa90#64 ∧
        sf.readReg64 .x29 = fp ∧ img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.stageP2_sub5_ok_trap
    img b C abs inp ikBPk spkBPk opkPkBytes opkSkBytes gMe gPeer himg hbase hWF hH hP
    htrusted hreplay hopk_match hwell hikBPk_len hspkBPk_len hacc_none hopkPk_len hopkSk_len
    hopkSk_eq hneq s0 s coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr idStorePtr idKpFutPtr
    kyberKpPubPtr kyberKpSecPtr ctBufPtr fp v_a8 v_b8 v_d0 u_b90 opkId b_4f1 b_b98 hb
    hF hsym hpc hrun hsp_align htr hx0 hx1 hx19 hx21 hx23 hx24 hx26 hx27 hx28 hx29)

end CryptoVerification.E2E.Pqxdh.ResponderClosure
