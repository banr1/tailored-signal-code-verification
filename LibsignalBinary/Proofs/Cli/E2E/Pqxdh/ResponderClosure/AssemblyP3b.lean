/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyBase
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.DecryptPqTrapBridge
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe

/-!
# Responder Closure Stage P3 Version-4 Call & Version-Mismatch Funnel

Proves `stageP3_tryDecrypt_v4_ok` (`+0x1bac → +0x1cd8`), `stageP3_ver_ne_ok` (`+0x1bac → x30`),
`stageP3_clone_and_tryDecrypt_v4_ok`, and `stageP3_clone_and_ver_ne_ok`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

namespace P3P4

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

open CryptoVerification.LibsignalTripleRatchet.RawByteMove

open CryptoVerification.LibsignalTripleRatchet.Record

open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps

open CryptoVerification.LibsignalTripleRatchet.ChainClone3

open CryptoVerification.LibsignalSession

open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Clone Aliases & `stageP3_tryDecrypt_v4_ok` (`+0x1bac → +0x1cd8`) -/

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub1_to_3_ok_trap := @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub1_ok_trap

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub1_to_3_ok := @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub1_ok

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_b_ok_trap := @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_ok_trap

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_b_ok := @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_ok

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.entryOf_tryDecryptPq_eq_trap {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (abs : String → Option (State → State)) : entryOf img
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = img.base + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) := by
  rw [entryOf_eq_tripleRatchetProgAt (C := C) (ctl := 0#64) (abs := abs) himg
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName]
  dsimp only [tripleRatchetProgAt]
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")]

set_option linter.unusedVariables false in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.entryOf_tryDecryptPq_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) : entryOf img
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = img.base + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.entryOf_tryDecryptPq_eq_trap himg C abs

set_option linter.unusedVariables false in
def _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost where
  pre x s := ⌜x.st.pqRatchetState = [] ∧ s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧
      s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧ (s.readReg64
      .x5).setWidth 8 = msgTypeByte x.msgType ∧ x.st.remoteIdentity ≠ some x.st.localIdentity ∧
      SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc
      x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗ memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest
      ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool
  post x s0 sf := ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗ (∃∗ G' :
    SessionGhost, ⌜x.G.AfterTryDecrypt (x.model C S uuidParse).1.toBool G'⌝ ∗ sessionStateAt A x.ss G'
    (x.model C S uuidParse).2) ∗ vecResultAt A x.ret (x.model C S uuidParse).1 ∗ protocolAddressAt A
    x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
    CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗ logOff img ∗
    stackAt s0.sp rootStack ∗ A.pool
  onPanic x s0 sf := ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.recvPanics x.st.pqRatchetState
      x.msg.pqRatchet ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptPq_ok_trap {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} {img : Obj.Image} (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) : subroutine_ok (trTrapProgAt img.base C abs) (img.base + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      ((CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpec C A ctl uuidTryParse S img).inImage img) := by
  have h := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.DecryptPqTrapBridge.tryDecryptPqEmpty_ok_trap
    (ctl := ctl) hH hempty himg
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOk_trap
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry at h
  rw [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.entryOf_tryDecryptPq_eq_trap himg C abs] at h
  refine Arm64.subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨
      (((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).restrictPre
        (·.st.pqRatchetState = [])).pre x s0) ∗ R := by
    dsimp only [Spec.restrictPre, CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpec, Spec.inImage] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨himg_pre, hpre⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hpq, hregs⟩, hm⟩
    refine ⟨hpq, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨himg_pre, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hregs, hm⟩
  exact (h.to_outcome x R s0 hpc hrun hpre' hsp).mono_outcome fun _ hout => hout

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptPq_ok {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} {img : Obj.Image} (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      ((CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpec C A ctl uuidTryParse S img).inImage img) :=
  subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptPq_ok_trap hH hempty himg)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_ok_trap {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18
    c0 remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v24 v28 v2c f248 f24c prevCounter : BitVec 32) (locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes rest : List (BitVec 8)) (sg' : SenderChainGhost) (sc : SenderChain) (st :
    SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc : AddrGhost) (msgG :
    SignalMessageGhost) (msg : SignalMessage) (hnew1 : newLocIdPtr ≠ 0#64) (hnew2 : newRemIdPtr ≠
    0#64) (hnew3 : newRootKeyPtr ≠ 0#64) (hnew4 : newAliceBasePtr ≠ 0#64) (hloc_len :
    locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33) (halice_len : aliceBaseBytes.length
    = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok st.localIdentity.publicKey) (hrem_eq
    : st.remoteIdentity = some remIk) (hrem_deser : PublicKey.deserialize remIdBytes = .ok
    remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some st.localIdentity) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hsc_inl :
    OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5)) (hF :
    img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc : s.pc = (trTrapProgAt img.base C
    abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) (hrun : s.status = .Running) (hsp_align :
    (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = 1#64) (hx22 : s.readReg64 .x22 =
    0xffffffffffffffff#64) (hx23 : s.readReg64 .x23 = newAliceBasePtr) (hx24 : s.readReg64 .x24 =
    33#64) (hx25 : s.readReg64 .x25 = 8#64) (hx26 : s.readReg64 .x26 = 0#64) (hx28 : s.readReg64
    .x28 = 32#64) : SepWPp (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s
      (memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
      ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp
      + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
      0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0)
      ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
      0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr)
      ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
      whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp +
      0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄
      sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄
      sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄
      sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄
      sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄
      sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
      sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ A.live newLocIdPtr 33
      1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
      A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗
      (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗ optSenderChainHeap A (some sg') (some sc) ∗
      protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A
      msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗
      stackAt s.sp rootStack ∗ A.pool)
      (fun s2 P_f => ∃ G' : SessionGhost, (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
          st).1 ≠ .error .panic ∧ (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr
          newAliceBasePtr
            locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt (pqxdhTryDecryptModel C S
            uuidTryParse rem loc msg rest st).1.toBool G' ∧ (P_f ⊢ sessionStateAt A (s.sp +
            0xa90#64) G'
              (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt A (s.sp +
              0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
              protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
              signalMessageAt A msgG whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base cur rest (decryptDraws C st
              msg.senderRatchetKey rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ ((s.sp +
              0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp +
              0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp +
              0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp + 0x38#64) ↦₆₄
              0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0) ∗
              ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
              0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄
              newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
              ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64)
              ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp
              + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64)
              ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄
              sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp +
              0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
              ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb'
              0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
              sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧ s2.sp = s.sp
              ∧ s2.trace = s0.trace ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab ∧ s2.readReg64
              .x19 = coroPtr ∧ s2.readReg64 .x24 = s.sp + 0x370#64 ∧ s2.readReg64 .x27 = s.readReg64
              .x27 ∧ s2.readReg64 .x29 = s.readReg64 .x29)
      (TryDecryptPanicProp C S uuidTryParse rem loc st msg rest s0) := by
  refine SepWPp.weaken_pre (sepConj_mono_left (memRegion_344_entails_spA90SlotsAt s.sp)) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun dv => ?_
  dsimp only [spA90SlotsAt]
  refine SepWPp.bind_sepWP_frame hF hsym
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg6_v4_wp_trap img.base C abs s coroPtr 33#64 newLocIdPtr 33#64 newRemIdPtr newRootKeyPtr
      v08 v10 v18 0xffffffffffffffff#64 0#64 c0 (sq0.extractLsb' 0 64) (sq0.extractLsb' 64 64)
      (sq1.extractLsb' 0 64) (sq1.extractLsb' 64 64) (sq2.extractLsb' 0 64) (sq2.extractLsb' 64 64)
      (sq3.extractLsb' 0 64) (sq3.extractLsb' 64 64) (sq4.extractLsb' 0 64) (sq4.extractLsb' 64 64)
      (sq5.extractLsb' 0 64) (sq5.extractLsb' 64 64) remAddrPtr locAddrPtr whisperMsgPtr dv.w_ca0
      dv.w_ca8 dv.w_cb0 dv.w_cb8 dv.w_cc0 dv.w_cc8 dv.w_cd0 dv.w_cd8 dv.w_ce0 dv.w_ce8 dv.w_cf0
      dv.w_cf8 dv.w_d00 dv.w_d08 dv.w_d10 dv.w_d18 dv.w_d20 dv.w_d28 dv.w_d30 (dv.q0.extractLsb' 0
      64) (dv.q0.extractLsb' 64 64) (dv.q1.extractLsb' 0 64) (dv.q1.extractLsb' 64 64)
      (dv.q2.extractLsb' 0 64) (dv.q2.extractLsb' 64 64) (dv.q3.extractLsb' 0 64) (dv.q3.extractLsb'
      64 64) (dv.q4.extractLsb' 0 64) (dv.q4.extractLsb' 64 64) (dv.q5.extractLsb' 0 64)
      (dv.q5.extractLsb' 64 64) dv.w_d98 dv.w_da0 dv.w_da8 dv.w_db8 dv.w_dc8 dv.w_dd0 dv.w_dd8 v24
      v28 v2c f248 f24c prevCounter dv.w_db0 dv.w_db4 dv.w_dc0 dv.w_de0 dv.w_de8 dv.w_dec dv.w_df0
      dv.w_df4 hpc hrun hsp_align hx19)
    (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1,
      hx19_1, hx24_1, hx27_1, hx29_1, hlr1⟩ => ?_
  have htr10 : s1.trace = s0.trace := htr1.trans htr
  have hsp_alm1 : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  rw [hx21, hx22, hx23, hx24, hx25, hx26, hx28]
  have hfold := clonedSlots_sp_a90_entails_sessionStateAt (A := A)
    s.sp newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr c0 sq0 sq1 sq2 sq3 sq4 sq5 locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes sg' sc prevCounter f248 f24c v18 0xffffffffffffffff#64
    v10 v08 0xffffffffffffffff#64 v2c ((s.readReg64 .x20).truncate 32) v28 v24 st remIk hnew1 hnew2
    hnew3 hnew4 hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser hroot_eq hrc hpq hsc
    hpend hver hprev hsc_inl
  refine SepWPp.weaken_pre
    (Entails.trans
      (Q := (((s.sp + 0xa90#64) ↦₆₄ 33#64) ∗ ((s.sp + 0xa98#64) ↦₆₄ newLocIdPtr) ∗ ((s.sp +
      0xaa0#64) ↦₆₄ 33#64) ∗
             ((s.sp + 0xaa8#64) ↦₆₄ 33#64) ∗ ((s.sp + 0xab0#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp +
             0xab8#64) ↦₆₄ 33#64) ∗ ((s.sp + 0xac0#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xac8#64) ↦₆₄
             newRootKeyPtr) ∗ ((s.sp + 0xad0#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xad8#64) ↦₆₄ 0#64) ∗ ((s.sp
             + 0xae0#64) ↦₆₄ 8#64) ∗ ((s.sp + 0xae8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0xaf0#64) ↦₆₄ 33#64) ∗
             ((s.sp + 0xaf8#64) ↦₆₄ newAliceBasePtr) ∗ ((s.sp + 0xb00#64) ↦₆₄ 33#64) ∗ ((s.sp +
             0xb08#64) ↦₆₄ 0#64) ∗ ((s.sp + 0xb10#64) ↦₆₄ 1#64) ∗ ((s.sp + 0xb18#64) ↦₆₄ 0#64) ∗
             ((s.sp + 0xb20#64) ↦₆₄ c0) ∗ ((s.sp + 0xb28#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp +
             0xb30#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0xb38#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
             ((s.sp + 0xb40#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0xb48#64) ↦₆₄ sq2.extractLsb'
             0 64) ∗ ((s.sp + 0xb50#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0xb58#64) ↦₆₄
             sq3.extractLsb' 0 64) ∗ ((s.sp + 0xb60#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp +
             0xb68#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 0xb70#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
             ((s.sp + 0xb78#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp + 0xb80#64) ↦₆₄ sq5.extractLsb'
             64 64) ∗ ((s.sp + 0xb88#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0xb90#64) ↦₆₄ v18) ∗
             ((s.sp + 0xb98#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0xba0#64) ↦₃₂ v2c) ∗ ((s.sp +
             0xba4#64) ↦₃₂ (s.readReg64 .x20).truncate 32) ∗ ((s.sp + 0xba8#64) ↦₆₄ v10) ∗ ((s.sp +
             0xbb0#64) ↦₃₂ v28) ∗ memRegion (s.sp + 0xbb4#64) 4 ∗ ((s.sp + 0xbb8#64) ↦₆₄
             0xffffffffffffffff#64) ∗ ((s.sp + 0xbc0#64) ↦₆₄ v08) ∗ ((s.sp + 0xbc8#64) ↦₆₄
             0xffffffffffffffff#64) ∗ ((s.sp + 0xbd0#64) ↦₃₂ v24) ∗ memRegion (s.sp + 0xbd4#64) 4 ∗
             ((s.sp + 0xbd8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xbdc#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0xbe0#64)
             ↦₃₂ f248) ∗ ((s.sp + 0xbe4#64) ↦₃₂ f24c) ∗ A.live newLocIdPtr 33 1 ∗ (newLocIdPtr ↦ₛ
             locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗ A.live
             newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗
             (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗ optSenderChainHeap A (some sg') (some sc)) ∗
             (protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
             signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base
             cur rest ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗
             ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
             ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗
             ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp + 0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp +
             0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
             ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp +
             0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32)
             ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp +
             0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr)
             ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp +
             0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
             ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb'
             0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄
             sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp +
             0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
             ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb'
             64 64)))
      (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hfold)) ?_
  have hseeds : SeedsLen32 st := by
    intro c hc; rw [hrc] at hc; cases hc
  have hrc_len : st.receiverChains.length < 2 ^ 32 := by simp [hrc]
  have hsp_root1 : rootStack ≤ s1.sp.toNat := by rw [hsp1]; exact hsp_root
  have hx5_byte : (s1.readReg64 .x5).setWidth 8 = msgTypeByte .preKey := by
    rw [hx5_1]; rfl
  refine SepWPp.call_inImage_frame hF1 hsym1 (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptPq_ok_trap (ctl := 0#64) hH hempty himg)
    (x := mkClonedTryDecryptGhost s.sp newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
      locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c st remAddrPtr rem locAddrPtr loc
      whisperMsgPtr msgG msg cur rest)
    hpc1 hrun1 hsp_alm1 hlr1
    rfl ⟨hpq, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_byte, hnot_self, hseeds, hrc_len, hsp_root1⟩
    (by dsimp only [mkClonedTryDecryptGhost]; rw [hsp1]; sep_focus) (fun _ _ => rfl) ?_ ?_
  · intro sf _ R hm
    dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpec, mkClonedTryDecryptGhost, TryDecryptGhost.model] at hm
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
    rcases hm with ⟨⟨hpan_or, hpref⟩, hm⟩
    have htr_pref : s0.trace <+: sf.trace := htr10 ▸ hpref
    have hpan_or0 :
        (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 = .error .panic ∨ S.recvPanics
        st.pqRatchetState msg.pqRatchet ∨ allocFailedIn s0 sf := by
      rcases hpan_or with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (by unfold allocFailedIn at h3 ⊢; rwa [← htr10]))
    rw [← sepConj_assoc] at hm
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpan_or0, htr_pref⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm⟩
  · intro s2 hpc2 hrun2 hsp2 _ hcs2 hF2 hsym2
    dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpec, mkClonedTryDecryptGhost, TryDecryptGhost.model]
    rw [hsp1, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hnpan, htr2⟩ => ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    refine SepWPp.exists_elim fun G' => ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hdec => ?_
    refine SepWPp.done hpc2 hrun2 ?_
    refine ⟨G', hnpan, hdec, Entails.of_eq (by ac_rfl),
      hsp2.trans hsp1, htr2.trans htr10, hF2, hsym2, (hcs2.1).trans hx19_1, (hcs2.2.2.2.2.2.1).trans
      hx24_1, (hcs2.2.2.2.2.2.2.2.2.1).trans hx27_1, (hcs2.2.2.2.2.2.2.2.2.2.2.1).trans hx29_1⟩

/-- Stage P3 Version-4 `try_decrypt_with_state` Bridge (`+0x1bac -> +0x1cd8`, `0x4cc78 ->
  0x4cda4`): Stores the cloned `SessionState` (`344` B) into `sp + 0xa90..0xbe8`, folds it into
`sessionStateAt A (s.sp + 0xa90#64) G₁ st`, checks `session_version = 4 == 4 = message_version`,
and invokes `try_decrypt_with_state::<PqxdhRng>` at `+0x1cd4`, returning to `+0x1cd8`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_ok {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18
    c0 remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v24 v28 v2c f248 f24c prevCounter : BitVec 32) (locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes rest : List (BitVec 8)) (sg' : SenderChainGhost) (sc : SenderChain) (st :
    SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc : AddrGhost) (msgG :
    SignalMessageGhost) (msg : SignalMessage) (hnew1 : newLocIdPtr ≠ 0#64) (hnew2 : newRemIdPtr ≠
    0#64) (hnew3 : newRootKeyPtr ≠ 0#64) (hnew4 : newAliceBasePtr ≠ 0#64) (hloc_len :
    locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33) (halice_len : aliceBaseBytes.length
    = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok st.localIdentity.publicKey) (hrem_eq
    : st.remoteIdentity = some remIk) (hrem_deser : PublicKey.deserialize remIdBytes = .ok
    remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some st.localIdentity) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hsc_inl :
    OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5)) (hF :
    img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc : s.pc = (tripleRatchetProgAt img.base C
    ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) (hrun : s.status = .Running) (hsp_align :
    (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = 1#64) (hx22 : s.readReg64 .x22 =
    0xffffffffffffffff#64) (hx23 : s.readReg64 .x23 = newAliceBasePtr) (hx24 : s.readReg64 .x24 =
    33#64) (hx25 : s.readReg64 .x25 = 8#64) (hx26 : s.readReg64 .x26 = 0#64) (hx28 : s.readReg64
    .x28 = 32#64) : SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s
      (memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
      ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp
      + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
      0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0)
      ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
      0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr)
      ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
      whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp +
      0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄
      sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄
      sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄
      sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄
      sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄
      sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
      sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ A.live newLocIdPtr 33
      1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
      A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗
      (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗ optSenderChainHeap A (some sg') (some sc) ∗
      protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A
      msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗
      stackAt s.sp rootStack ∗ A.pool)
      (fun s2 P_f => ∃ G' : SessionGhost, (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
          st).1 ≠ .error .panic ∧ (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr
          newAliceBasePtr
            locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt (pqxdhTryDecryptModel C S
            uuidTryParse rem loc msg rest st).1.toBool G' ∧ (P_f ⊢ sessionStateAt A (s.sp +
            0xa90#64) G'
              (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt A (s.sp +
              0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
              protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
              signalMessageAt A msgG whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base cur rest (decryptDraws C st
              msg.senderRatchetKey rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ ((s.sp +
              0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp +
              0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp +
              0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp + 0x38#64) ↦₆₄
              0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0) ∗
              ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
              0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄
              newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
              ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64)
              ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp
              + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64)
              ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄
              sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp +
              0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
              ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb'
              0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
              sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧ s2.sp = s.sp
              ∧ s2.trace = s0.trace ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab ∧ s2.readReg64
              .x19 = coroPtr ∧ s2.readReg64 .x24 = s.sp + 0x370#64 ∧ s2.readReg64 .x27 = s.readReg64
              .x27 ∧ s2.readReg64 .x29 = s.readReg64 .x29)
      (TryDecryptPanicProp C S uuidTryParse rem loc st msg rest s0) := by
  simp only [← trTrapProgAt_fnAddr_eq img.base C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_ok_trap
      img C S abs hH hempty himg s0 s coroPtr newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
      v08 v10 v18 c0 remAddrPtr locAddrPtr whisperMsgPtr cur sq0 sq1 sq2 sq3 sq4 sq5
      v24 v28 v2c f248 f24c prevCounter locIdBytes remIdBytes rootKeyBytes aliceBaseBytes rest
      sg' sc st remIk rem loc msgG msg hnew1 hnew2 hnew3 hnew4 hloc_len hrem_len halice_len
      hloc_deser hrem_eq hrem_deser hnot_self hroot_eq hrc hpq hsc hpend hver hprev hsc_inl
      hF hsym hpc hrun hsp_align hsp_root htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx28)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_nopanic_ok_trap {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18
    c0 remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v24 v28 v2c f248 f24c prevCounter : BitVec 32) (locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes rest : List (BitVec 8)) (sg' : SenderChainGhost) (sc : SenderChain) (st :
    SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc : AddrGhost) (msgG :
    SignalMessageGhost) (msg : SignalMessage) (hnpan1 : (pqxdhTryDecryptModel C S uuidTryParse rem
    loc msg rest st).1 ≠ .error .panic) (hnpan2 : ¬ S.recvPanics st.pqRatchetState msg.pqRatchet)
    (hnew1 : newLocIdPtr ≠ 0#64) (hnew2 : newRemIdPtr ≠ 0#64) (hnew3 : newRootKeyPtr ≠ 0#64) (hnew4
    : newAliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length =
    33) (halice_len : aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes =
    .ok st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity) (hroot_eq : rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains =
    []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey =
    false) (hver : st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hsc_inl :
    OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5)) (hF :
    img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc : s.pc = (trTrapProgAt img.base C
    abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) (hrun : s.status = .Running) (hsp_align :
    (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = 1#64) (hx22 : s.readReg64 .x22 =
    0xffffffffffffffff#64) (hx23 : s.readReg64 .x23 = newAliceBasePtr) (hx24 : s.readReg64 .x24 =
    33#64) (hx25 : s.readReg64 .x25 = 8#64) (hx26 : s.readReg64 .x26 = 0#64) (hx28 : s.readReg64
    .x28 = 32#64) : SepWPp (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s
      (memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
      ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp
      + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
      0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0)
      ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
      0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr)
      ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
      whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp +
      0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄
      sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄
      sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄
      sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄
      sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄
      sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
      sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ A.live newLocIdPtr 33
      1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
      A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗
      (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗ optSenderChainHeap A (some sg') (some sc) ∗
      protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A
      msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗
      stackAt s.sp rootStack ∗ A.pool)
      (fun s2 P_f => ∃ G' : SessionGhost, (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
          st).1 ≠ .error .panic ∧ (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr
          newAliceBasePtr
            locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt (pqxdhTryDecryptModel C S
            uuidTryParse rem loc msg rest st).1.toBool G' ∧ (P_f ⊢ sessionStateAt A (s.sp +
            0xa90#64) G'
              (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt A (s.sp +
              0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
              protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
              signalMessageAt A msgG whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base cur rest (decryptDraws C st
              msg.senderRatchetKey rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ ((s.sp +
              0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp +
              0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp +
              0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp + 0x38#64) ↦₆₄
              0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0) ∗
              ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
              0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄
              newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
              ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64)
              ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp
              + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64)
              ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄
              sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp +
              0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
              ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb'
              0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
              sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧ s2.sp = s.sp
              ∧ s2.trace = s0.trace ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab ∧ s2.readReg64
              .x19 = coroPtr ∧ s2.readReg64 .x24 = s.sp + 0x370#64 ∧ s2.readReg64 .x27 = s.readReg64
              .x27 ∧ s2.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := SepWPp.mono_panic (fun _ _ => tryDecryptPanicProp_imp_panicOomProp
      (_parse := uuidTryParse) hnpan1 hnpan2)
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_ok_trap img C S abs hH hempty himg s0 s coroPtr
      newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18 c0 remAddrPtr locAddrPtr
      whisperMsgPtr cur sq0 sq1 sq2 sq3 sq4 sq5 v24 v28 v2c f248 f24c prevCounter locIdBytes
      remIdBytes rootKeyBytes aliceBaseBytes rest sg' sc st remIk rem loc msgG msg hnew1 hnew2 hnew3
      hnew4 hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser hnot_self hroot_eq hrc hpq
      hsc hpend hver hprev hsc_inl hF hsym hpc hrun hsp_align hsp_root htr hx19 hx21 hx22 hx23 hx24
      hx25 hx26 hx28)

/-- Specialisation of `stageP3_tryDecrypt_v4_ok` to `PanicOomProp s0` when the pure model does not
panic and `S.recvPanics` is false. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_nopanic_ok {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18
    c0 remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v24 v28 v2c f248 f24c prevCounter : BitVec 32) (locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes rest : List (BitVec 8)) (sg' : SenderChainGhost) (sc : SenderChain) (st :
    SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc : AddrGhost) (msgG :
    SignalMessageGhost) (msg : SignalMessage) (hnpan1 : (pqxdhTryDecryptModel C S uuidTryParse rem
    loc msg rest st).1 ≠ .error .panic) (hnpan2 : ¬ S.recvPanics st.pqRatchetState msg.pqRatchet)
    (hnew1 : newLocIdPtr ≠ 0#64) (hnew2 : newRemIdPtr ≠ 0#64) (hnew3 : newRootKeyPtr ≠ 0#64) (hnew4
    : newAliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length =
    33) (halice_len : aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes =
    .ok st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity) (hroot_eq : rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains =
    []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey =
    false) (hver : st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hsc_inl :
    OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5)) (hF :
    img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc : s.pc = (tripleRatchetProgAt img.base C
    ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) (hrun : s.status = .Running) (hsp_align :
    (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = 1#64) (hx22 : s.readReg64 .x22 =
    0xffffffffffffffff#64) (hx23 : s.readReg64 .x23 = newAliceBasePtr) (hx24 : s.readReg64 .x24 =
    33#64) (hx25 : s.readReg64 .x25 = 8#64) (hx26 : s.readReg64 .x26 = 0#64) (hx28 : s.readReg64
    .x28 = 32#64) : SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s
      (memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
      ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp
      + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
      0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0)
      ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
      0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr)
      ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
      whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp +
      0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄
      sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄
      sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄
      sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄
      sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄
      sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
      sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ A.live newLocIdPtr 33
      1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
      A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗
      (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗ optSenderChainHeap A (some sg') (some sc) ∗
      protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A
      msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗
      stackAt s.sp rootStack ∗ A.pool)
      (fun s2 P_f => ∃ G' : SessionGhost, (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
          st).1 ≠ .error .panic ∧ (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr
          newAliceBasePtr
            locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt (pqxdhTryDecryptModel C S
            uuidTryParse rem loc msg rest st).1.toBool G' ∧ (P_f ⊢ sessionStateAt A (s.sp +
            0xa90#64) G'
              (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt A (s.sp +
              0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
              protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
              signalMessageAt A msgG whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base cur rest (decryptDraws C st
              msg.senderRatchetKey rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ ((s.sp +
              0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp +
              0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp +
              0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp + 0x38#64) ↦₆₄
              0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0) ∗
              ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
              0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄
              newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
              ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64)
              ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp
              + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64)
              ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄
              sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp +
              0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
              ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb'
              0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
              sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧ s2.sp = s.sp
              ∧ s2.trace = s0.trace ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab ∧ s2.readReg64
              .x19 = coroPtr ∧ s2.readReg64 .x24 = s.sp + 0x370#64 ∧ s2.readReg64 .x27 = s.readReg64
              .x27 ∧ s2.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq img.base C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_nopanic_ok_trap img C S abs hH hempty himg s0 s coroPtr
    newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18 c0 remAddrPtr locAddrPtr
    whisperMsgPtr cur sq0 sq1 sq2 sq3 sq4 sq5 v24 v28 v2c f248 f24c prevCounter locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes rest sg' sc st remIk rem loc msgG msg hnpan1 hnpan2
    hnew1 hnew2 hnew3 hnew4 hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser hnot_self
    hroot_eq hrc hpq hsc hpend hver hprev hsc_inl hF hsym hpc hrun hsp_align hsp_root htr hx19
    hx21 hx22 hx23 hx24 hx25 hx26 hx28)

/-! ## 2. Version-Mismatch Error Funnel (`stageP3_ver_ne_ok`, `+0x1bac → x30`) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_pqxdhLogClosure_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : (trTrapProgAt b C
    abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName = b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
  rw [trTrapProgAt, Program.fnAddr_rebase,
    show libsignalSessionCode.fnOff CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName = (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") from
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")]

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_pqxdhLogClosure_eq (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : (tripleRatchetProgAt b C ctl
    abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName = b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs]
  exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_pqxdhLogClosure_eq_trap b C abs

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_dropSessionStructure3_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : (trTrapProgAt b C
    abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name = b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) := by
  rw [trTrapProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_dropSessionStructure3_eq (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : (tripleRatchetProgAt b C ctl
    abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name = b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs]
  exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_dropSessionStructure3_eq_trap b C abs

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp.intro_rodata_decryptionFailed {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) {prog : Program} {ret : BitVec 64} {s : State} {P :
    SepProp} {Q Qp : State → SepProp → Prop} (hF : img.FrozenLoaded s) (h : SepWPp prog ret s
    (((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ 0x6974707972636564#64) ∗ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ
    0x656c696166206e6f#64) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm1 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.rodata_0x87358_intro himg hF hm
  have hm2 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.rodata_0x87350_intro himg hF hm1
  exact h R (Satisfies.of_eq hm2 (by ac_rfl)) hL

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ver_ne_ok_trap {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) (himg :
    Obj.Loads libsignalSessionImage img) (s0 s : State) (coroPtr newLocIdPtr newRemIdPtr
    newRootKeyPtr newAliceBasePtr v08 v10 v18 c0 u_c0 outPtr errsPtr0 prevStatesPtr : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (msgVer v24 v28 v2c f248 f24c prevCounter : BitVec 32)
    (b_2c0 : BitVec 8) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes : List (BitVec 8)) (sg' :
    SenderChainGhost) (sc : SenderChain) (G₀ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (remIk : IdentityKey) (hver_ne : msgVer ≠ 4#32) (herrs_nz : errsPtr0 ≠ 0#64) (hcap0 :
    G₀.localIk.cap ≠ 0xffffffffffffffff#64) (hnew1 : newLocIdPtr ≠ 0#64) (hnew2 : newRemIdPtr ≠
    0#64) (hnew3 : newRootKeyPtr ≠ 0#64) (hnew4 : newAliceBasePtr ≠ 0#64) (hloc_len :
    locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33) (halice_len : aliceBaseBytes.length
    = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok st.localIdentity.publicKey) (hrem_eq
    : st.remoteIdentity = some remIk) (hrem_deser : PublicKey.deserialize remIdBytes = .ok
    remIk.publicKey) (hroot_eq : rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains =
    []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey =
    false) (hver : st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hsc_inl :
    OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5)) (hF :
    img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc : s.pc = (trTrapProgAt img.base C
    abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) (hrun : s.status = .Running) (hsp_align :
    (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = 1#64) (hx22 : s.readReg64 .x22 = 0xffffffffffffffff#64) (hx23 :
    s.readReg64 .x23 = newAliceBasePtr) (hx24 : s.readReg64 .x24 = 33#64) (hx25 : s.readReg64 .x25 =
    8#64) (hx26 : s.readReg64 .x26 = 0#64) (hx28 : s.readReg64 .x28 = 32#64) : SepWPp
    (trTrapProgAt img.base C abs) (s0.readReg64 .x30) s
      (memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
       ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp
       + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
       0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0)
       ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
       0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr)
       ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp +
       0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp +
       0xd0#64) ↦₆₄ 33#64) ∗ memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr0) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x3e0#64)
       48 ∗ ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64
       64) ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb'
       64 64) ∗ ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄
       sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64)
       ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp +
       0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp
       + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ A.live newLocIdPtr 33 1 ∗ (newLocIdPtr ↦ₛ
       locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗ A.live newRootKeyPtr 32
       1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗ (newAliceBasePtr ↦ₛ
       aliceBaseBytes) ∗ optSenderChainHeap A (some sg') (some sc) ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64)
       ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ sessionStateAt A
       (coroPtr + 0xf8#64) G₀ st ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ decryptPrekeySavedRegsAt (s.sp
       + 0xcd0#64) s0 ∗ memRegion outPtr 48 ∗ logOff img ∗ stackAt s.sp growOneSpeStack ∗ A.pool)
      (fun sf P_f => (P_f ⊢ (outPtr ↦₆₄ 0x8000000000000018#64) ∗ memRegion (outPtr + 8#64) 40 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr +
          0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ logOff img ∗ decryptPrekeySavedRegsAt
          (s.sp + 0xcd0#64) s0 ∗ stackAt s.sp growOneSpeStack ∗ A.pool ∗ anyHeap) ∧ sf.sp = s.sp +
          0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧ img.FrozenLoaded sf ∧
          sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  refine SepWPp.weaken_pre (sepConj_mono_left (memRegion_344_entails_spA90SlotsAt s.sp)) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun dv => ?_
  dsimp only [spA90SlotsAt]
  refine SepWPp.weaken_frame (Entails.of_eq (sp3e0_48_ver_split_eq s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e5 => SepWPp.exists_elim fun e4 =>
    SepWPp.exists_elim fun e3 => SepWPp.exists_elim fun e2 =>
    SepWPp.exists_elim fun u3ec => SepWPp.exists_elim fun u3e8 => SepWPp.exists_elim fun u3e0 => ?_
  refine SepWPp.bind_sepWP_frame hF hsym
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg6_ver_ne_wp_trap img.base C abs s coroPtr 33#64 newLocIdPtr 33#64 newRemIdPtr
    newRootKeyPtr
      v08 v10 v18 0xffffffffffffffff#64 0#64 c0 (sq0.extractLsb' 0 64) (sq0.extractLsb' 64 64)
      (sq1.extractLsb' 0 64) (sq1.extractLsb' 64 64) (sq2.extractLsb' 0 64) (sq2.extractLsb' 64 64)
      (sq3.extractLsb' 0 64) (sq3.extractLsb' 64 64) (sq4.extractLsb' 0 64) (sq4.extractLsb' 64 64)
      (sq5.extractLsb' 0 64) (sq5.extractLsb' 64 64) u3e0 dv.w_ca0 dv.w_ca8 dv.w_cb0 dv.w_cb8
      dv.w_cc0 dv.w_cc8 dv.w_cd0 dv.w_cd8 dv.w_ce0 dv.w_ce8 dv.w_cf0 dv.w_cf8 dv.w_d00 dv.w_d08
      dv.w_d10 dv.w_d18 dv.w_d20 dv.w_d28 dv.w_d30 (dv.q0.extractLsb' 0 64) (dv.q0.extractLsb' 64
      64) (dv.q1.extractLsb' 0 64) (dv.q1.extractLsb' 64 64) (dv.q2.extractLsb' 0 64)
      (dv.q2.extractLsb' 64 64) (dv.q3.extractLsb' 0 64) (dv.q3.extractLsb' 64 64)
      (dv.q4.extractLsb' 0 64) (dv.q4.extractLsb' 64 64) (dv.q5.extractLsb' 0 64) (dv.q5.extractLsb'
      64 64) dv.w_d98 dv.w_da0 dv.w_da8 dv.w_db8 dv.w_dc8 dv.w_dd0 dv.w_dd8 msgVer v24 v28 v2c f248
      f24c prevCounter u3e8 dv.w_db0 dv.w_db4 dv.w_dc0 dv.w_de0 dv.w_de8 dv.w_dec dv.w_df0 dv.w_df4
      hb hver_ne hpc hrun hsp_align hx19)
    (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx19_1, hx24_1,
      hx27_1, hx29_1, hlr1⟩ => ?_
  rw [hx21, hx22, hx23, hx24, hx25, hx26, hx28]
  have hfold := clonedSlots_sp_a90_entails_sessionStateAt (A := A)
    s.sp newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr c0 sq0 sq1 sq2 sq3 sq4 sq5 locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes sg' sc prevCounter f248 f24c v18 0xffffffffffffffff#64
    v10 v08 0xffffffffffffffff#64 v2c ((s.readReg64 .x20).truncate 32) v28 v24 st remIk hnew1 hnew2
    hnew3 hnew4 hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser hroot_eq hrc hpq hsc
    hpend hver hprev hsc_inl
  refine SepWPp.weaken_frame hfold (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hpc1_log : s1.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName := by
    rw [hpc1, CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_pqxdhLogClosure_eq_trap]
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack pqxdhClosureStack)) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_frame_inImage_nopanic
    (x := ()) (φ := True) (T := logOff img ∗ stackAt s.sp pqxdhClosureStack) hF1 hsym1
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdh_log_closure_ok_trap himg) hpc1_log hrun1 hsp1_al hlr1
    (by dsimp only [pqxdhLogClosureSpec]; rw [hsp1, pure_true, emp_sepConj])
    trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hF2 hsym2 => ?_)
  dsimp only [pqxdhLogClosureSpec]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack pqxdhClosureStack).symm) (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
  have hx24_2 : s2.readReg64 .x24 = s.sp + 0x370#64 := hcs2.2.2.2.2.2.1.trans hx24_1
  have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
  refine SepWPp.bind_sepWP_frame hF2 hsym2
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_b_wp_trap img.base C abs s2 coroPtr hpc2 hrun2 hsp2_align hx19_2)
    (by rw [hsp2]; sep_focus)
    fun s3 hpc3 hrun3 hF3 hsym3 ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx27_3, hx29_3,
    hlr3⟩ => ?_
  have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
  have hsp3_al : s3.spAligned = true := by simpa [State.spAligned, hsp3] using hsp_align
  have htr3_0 : s3.trace = s0.trace := by rw [htr3_2, htr2_1, htr1, htr]
  have hpc3_grow : s3.pc = (trTrapProgAt img.base C abs).fnAddr growOneSpeName := by
    rw [hpc3, fnAddr_growOneSpe_eq_trap]
  have hx0_3' : s3.readReg64 .x0 = s.sp + 0x3c8#64 := by rw [hx0_3, hsp2]
  refine SepWPp.call_frame_frozen_oom
    (x := ((s.sp + 0x3c8#64, 0#64, errsPtr0, ([] : List (BitVec 8))) : GrowGhost)) (φ :=
    s3.readReg64 .x0 = s.sp + 0x3c8#64 ∧ ([] : List (BitVec 8)).length = (0#64).toNat * 48 ∧
    errsPtr0 ≠ 0 ∧ max (2 * (0#64).toNat) 4 * 48 + 8 ≤ 2 ^ 63)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr0) ∗ A.pool ∗ stackAt s.sp
    growOneSpeStack) hF3 hsym3 htr3_0 (FromRecordCallees.grow_one_spe_ok_trap hA) hpc3_grow hrun3 hsp3_al
    hlr3
    (by rw [growOneSpe_pre_zero_eq A s.sp errsPtr0 s3, hsp3])
    ⟨hx0_3', rfl, herrs_nz, by decide⟩
    (by rw [hsp2]; sep_focus) (hnext := fun s4 hpc4 hrun4 hsp4_3 hsp4_al hcs4 hF4 hsym4 => ?_)
  rw [growOneSpe_post_zero_eq A s.sp errsPtr0 s3 s4, hsp3, sepConj_assoc]
  refine SepWPp.pure_elim fun htr4_3 => ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun errsPtr => ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun herrsPtr_nz => ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hcs4.1.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = 0#64 := hcs4.2.2.1.trans hx21_3
  have hx24_4 : s4.readReg64 .x24 = s4.sp + 0x370#64 := by
    rw [hcs4.2.2.2.2.2.1, hx24_3, hx24_2, hsp4]
  have hx27_4 : s4.readReg64 .x27 = s.readReg64 .x27 := hcs4.2.2.2.2.2.2.2.2.1.trans (hx27_3.trans
    hx27_2)
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := hcs4.2.2.2.2.2.2.2.2.2.2.1.trans (hx29_3.trans
    hx29_2)
  refine SepWPp.weaken_frame (Entails.of_eq (pointsTo32_pair_sp3e8 s.sp msgVer u3ec)) (by sep_focus)
    ?_
  refine SepWPp.weaken_frame (Entails.of_eq (errs192_split_eq errsPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  refine SepWPp.bind_sepWP_frame hF4 hsym4
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_c_wp_trap img.base C abs s4 coroPtr errsPtr
      0x8000000000000006#64 (u3ec ++ msgVer) e2 e3 e4 e5 u_c0 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 hpc4
      hrun4 hsp4_align hx19_4 hx21_4 hx24_4)
    (by rw [hsp4]; sep_focus)
    fun s5 hpc5 hrun5 hF5 hsym5 ⟨hsp5_4, htr5_4, hx0_5, hx19_5, hx24_5, hx27_5, hx29_5, hlr5⟩ => ?_
  refine SepWPp.weaken_frame (errs48_fold_ver errsPtr e2 e3 e4 e5 msgVer u3ec) (by sep_focus) ?_
  have hsp5 : s5.sp = s.sp := hsp5_4.trans hsp4
  have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_align
  have hpc5_drop : s5.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name
    := by
    rw [hpc5, CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_dropSessionStructure3_eq_trap]
  have hx0_5' : s5.readReg64 .x0 = s.sp + 0xa90#64 := by rw [hx0_5, hsp4]
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack dropSessionStructureLocal2Stack))
    (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_frame_frozen_nopanic
    (x := (⟨s.sp + 0xa90#64, mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
      locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr
    newAliceBasePtr
              locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c) st ∗ A.pool ∗ stackAt s.sp
              dropSessionStructureLocal2Stack)
    hF5 hsym5 (CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.drop_session_structure3_ok_trap hA) hpc5_drop hrun5 hsp5_al hlr5
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp5])
    hx0_5' (by sep_focus)
    (hnext := fun s6 hpc6 hrun6 hsp6_5 hsp6_al hcs6 hF6 hsym6 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp5, sepConj_assoc]
  refine SepWPp.pure_elim fun htr6_5 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack dropSessionStructureLocal2Stack).symm)
    (by sep_focus) ?_
  have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
  have hx19_6 : s6.readReg64 .x19 = coroPtr := hcs6.1.trans hx19_5
  have hx29_6 : s6.readReg64 .x29 = s.readReg64 .x29 := hcs6.2.2.2.2.2.2.2.2.2.2.1.trans (hx29_5.trans
    hx29_4)
  refine SepWPp.weaken_frame
    (Entails.of_eq (sessionStateAt_expose_cap A (coroPtr + 0xf8#64) G₀ st)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (logOff_eq_5b810 img)) (by sep_focus) ?_
  refine SepWPp.bind_sepWP_frame hF6 hsym6
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_d_wp_trap img.base C abs s6 coroPtr outPtr (s4.readReg64 .x27)
      G₀.localIk.cap 0x8000000000000006#64 hb hcap0 hpc6 hrun6 hsp6_align hx19_6)
    (by rw [hsp6]; sep_focus)
    fun s7 hpc7 hrun7 hF7 hsym7 ⟨hsp7_6, htr7_6, hx0_7, hx1_7, hx19_7, hx24_7, hx25_7, hx26_7,
    hx27_7, hx29_7⟩ => ?_
  have hsp7 : s7.sp = s.sp := hsp7_6.trans hsp6
  have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hsp7]; exact hsp_align
  have htr7_0 : s7.trace = s0.trace := by rw [htr7_6, htr6_5, htr5_4, htr4_3, htr3_0]
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack allocHookStack)) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.bind_sepWPp_frame_dep
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_33b0_ok_trap img img.base C abs hA s0 s7 emp
      hF7 hsym7 hpc7 hrun7 hsp7_align htr7_0 hx0_7 hx1_7)
    (by rw [hsp7]; sep_focus)
    fun s8 hpc8 hrun8 ⟨hdf_nz, hsp8_7, htr8_7, hcs8, hF8, hsym8⟩ => ?_
  set dfPtr := s8.readReg64 .x0
  have hsp8 : s8.sp = s.sp := hsp8_7.trans hsp7
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8]; exact hsp_align
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hcs8.1.trans hx19_7
  have hx24_8 : s8.readReg64 .x24 = s.sp + 0x370#64 := by
    rw [hcs8.2.2.2.2.2.1, hx24_7, hsp6]
  have hx25_8 : s8.readReg64 .x25 = s.sp + 0x210#64 := by
    rw [hcs8.2.2.2.2.2.2.1, hx25_7, hsp6]
  have hx26_8 : s8.readReg64 .x26 = outPtr := hcs8.2.2.2.2.2.2.2.1.trans hx26_7
  have hx27_8 : s8.readReg64 .x27 = s.readReg64 .x27 := by
    rw [hcs8.2.2.2.2.2.2.2.2.1, hx27_7, hx27_4]
  have hx29_8 : s8.readReg64 .x29 = s.readReg64 .x29 := by
    rw [hcs8.2.2.2.2.2.2.2.2.2.2.1, hx29_7, hx29_6]
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion_17_split_eq dfPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_df10 => SepWPp.exists_elim fun u_df8 => SepWPp.exists_elim fun
    u_df0 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp270_48_split_eq s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_290 => SepWPp.exists_elim fun u_288 =>
    SepWPp.exists_elim fun u_280 => SepWPp.exists_elim fun u_278 => SepWPp.exists_elim fun u_270 =>
    ?_
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp.intro_rodata_decryptionFailed himg hF8 ?_
  refine SepWPp.bind_sepWP_frame hF8 hsym8
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_e_wp_trap img.base C abs s8 coroPtr dfPtr errsPtr
      0x6974707972636564#64 0x656c696166206e6f#64 u_df0 u_df8 u_270 u_278 u_280 u_288 u_df10 u_290
      hb hdf_nz hpc8 hrun8 hsp8_align rfl hx19_8)
    (by rw [hsp8]; sep_focus)
    fun s9 hpc9 hrun9 hF9 hsym9 ⟨hsp9_8, htr9_8, hx0_9, hx19_9, hx21_9, hx22_9, hx23_9, hx24_9,
      hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, hlr9⟩ => ?_
  have hsp9 : s9.sp = s.sp := hsp9_8.trans hsp8
  have hsp9_al : s9.spAligned = true := by simpa [State.spAligned, hsp9] using hsp_align
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack allocHookStack).symm)
    (by rw [hsp7]; sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack dropSpeStack)) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_frame_inImage_nopanic
    (x := (errsPtr, msgVer)) (T := (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂
          msgVer) ∗ memRegion (errsPtr + 12#64) 36 ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    hF9 hsym9 (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.drop_spe2_ver_ok_trap himg) hpc9 hrun9 hsp9_al hlr9
    (by dsimp only [dropSpeVerSpec]; rw [hsp9])
    hx0_9 (by sep_focus)
    (hnext := fun s10 hpc10 hrun10 hsp10_9 hsp10_al hcs10 hF10 hsym10 => ?_)
  dsimp only [dropSpeVerSpec]
  rw [hsp9, sepConj_assoc]
  refine SepWPp.pure_elim fun htr10_9 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack dropSpeStack).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (errs48_144_join errsPtr)) (by sep_focus) ?_
  have hsp10 : s10.sp = s.sp := hsp10_9.trans hsp9
  have hsp10_align : (s10.sp &&& 15#64 == 0#64) = true := by rw [hsp10]; exact hsp_align
  have hx19_10 : s10.readReg64 .x19 = coroPtr := hcs10.1.trans hx19_9
  have hx21_10 : s10.readReg64 .x21 = errsPtr := hcs10.2.2.1.trans hx21_9
  have hx22_10 : s10.readReg64 .x22 = errsPtr := hcs10.2.2.2.1.trans hx22_9
  have hx23_10 : s10.readReg64 .x23 = 1#64 := hcs10.2.2.2.2.1.trans hx23_9
  have hx24_10 : s10.readReg64 .x24 = s10.sp + 0x370#64 := by
    rw [hcs10.2.2.2.2.2.1, hx24_9, hx24_8, hsp10]
  have hx25_10 : s10.readReg64 .x25 = s10.sp + 0x210#64 := by
    rw [hcs10.2.2.2.2.2.2.1, hx25_9, hx25_8, hsp10]
  have hx26_10 : s10.readReg64 .x26 = outPtr := hcs10.2.2.2.2.2.2.2.1.trans (hx26_9.trans hx26_8)
  have hx27_10 : s10.readReg64 .x27 = s.readReg64 .x27 := hcs10.2.2.2.2.2.2.2.2.1.trans
    (hx27_9.trans hx27_8)
  have hx28_10 : s10.readReg64 .x28 = 0x8000000000000018#64 := hcs10.2.2.2.2.2.2.2.2.2.1.trans
    hx28_9
  have hx29_10 : s10.readReg64 .x29 = s.readReg64 .x29 := hcs10.2.2.2.2.2.2.2.2.2.2.1.trans
    (hx29_9.trans hx29_8)
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack allocHookStack)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (sp278_40_resplit s.sp 17#64 dfPtr 17#64 3#8) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun v_298 => SepWPp.exists_elim fun v_290 =>
    SepWPp.exists_elim fun v_28c => SepWPp.exists_elim fun v_284 =>
    SepWPp.exists_elim fun v_27c => SepWPp.exists_elim fun v_278 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus)
    ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun
    u_250 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_ver_f_split_eq s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 =>
    ?_
  refine SepWPp.bind_sepWP_frame hF10 hsym10
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_f_wp_trap img.base C abs hA s10 coroPtr errsPtr G₀.localIk.cap
      v_27c v_284 v_290 v_298 u_250 u_258 u_370 u_378 u_384 u_38c v_278 v_28c u_260 u_380 hcap0
      hpc10 hrun10 hsp10_align hx19_10 hx21_10 hx22_10 hx23_10 hx24_10 hx25_10 hx28_10)
    (by rw [hsp10]; sep_focus)
    fun s11 hpc11 hrun11 hF11 hsym11 ⟨hsp11_10, htr11_10, hx0_11, hx19_11, hx22_11, hx24_11,
      hx25_11, hx26_11, hx27_11, hx28_11, hx29_11, hlr11⟩ => ?_
  have hsp11 : s11.sp = s.sp := hsp11_10.trans hsp10
  have hsp11_al : s11.spAligned = true := by simpa [State.spAligned, hsp11] using hsp_align
  have hpc11_drop : s11.pc = (trTrapProgAt img.base C abs).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc11, CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_dropSessionStructure3_eq_trap]
  refine SepWPp.weaken_frame
    (Entails.of_eq (sessionStateAt_expose_cap A (coroPtr + 0xf8#64) G₀ st).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack allocHookStack).symm)
    (by rw [hsp10]; sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack dropSessionStructureLocal2Stack))
    (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_frame_frozen_nopanic
    (x := (⟨coroPtr + 0xf8#64, G₀, st⟩ : DropSessionStructureGhost)) (T := sessionStateAt A (coroPtr
    + 0xf8#64) G₀ st ∗ A.pool ∗ stackAt s.sp dropSessionStructureLocal2Stack) hF11 hsym11
    (CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.drop_session_structure3_ok_trap hA) hpc11_drop hrun11 hsp11_al hlr11
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp11])
    hx0_11 (by sep_focus)
    (hnext := fun s12 hpc12 hrun12 hsp12_11 hsp12_al hcs12 hF12 hsym12 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp11, sepConj_assoc]
  refine SepWPp.pure_elim fun htr12_11 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack dropSessionStructureLocal2Stack).symm)
    (by sep_focus) ?_
  have hsp12 : s12.sp = s.sp := hsp12_11.trans hsp11
  have hsp12_align : (s12.sp &&& 15#64 == 0#64) = true := by rw [hsp12]; exact hsp_align
  have hx19_12 : s12.readReg64 .x19 = coroPtr := hcs12.1.trans hx19_11
  have hx22_12 : s12.readReg64 .x22 = v_278.zeroExtend 64 := hcs12.2.2.2.1.trans hx22_11
  have hx25_12 : s12.readReg64 .x25 = s12.sp + 0x210#64 := by
    rw [hcs12.2.2.2.2.2.2.1, hx25_11, hsp10, hsp12]
  have hx26_12 : s12.readReg64 .x26 = outPtr := hcs12.2.2.2.2.2.2.2.1.trans (hx26_11.trans hx26_10)
  have hx28_12 : s12.readReg64 .x28 = 0x8000000000000018#64 := hcs12.2.2.2.2.2.2.2.2.2.1.trans
    hx28_11
  refine SepWPp.weaken_frame
    (sp370_36_ver_f_to_tail_b s.sp v_27c v_284 v_290 v_298 v_28c) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w_390 => SepWPp.exists_elim fun w_388 =>
    SepWPp.exists_elim fun w_380 => SepWPp.exists_elim fun w_378 => SepWPp.exists_elim fun w_370 =>
    ?_
  refine SepWPp.weaken_frame (Entails.of_eq (outPtr48_split_eq outPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ret2c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret08 => SepWPp.exists_elim fun
    u_ret0 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  have hstep13 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_tail_b_wp_trap img.base C abs s12 coroPtr outPtr
    0x8000000000000018#64 prevStatesPtr w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c
    u_ret24 (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64
    .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30) v_278 w_390 u_ret08 u_ret2c
    b_2c0 hpc12 hrun12 hsp12_align hx19_12 hx22_12 hx25_12 hx26_12 hx28_12
  rw [hsp12] at hstep13
  refine SepWPp.bind_sepWP_frame hF12 hsym12 hstep13 (by sep_focus)
    fun sf hpcf hrunf hFf hsymf ⟨hspf_s, htrf_12, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩ => ?_
  refine SepWPp.weaken_frame
    (outPtr48_err_fold outPtr 0x8000000000000018#64 w_370 w_378 w_380 w_388 v_278 w_390)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (logOff_eq_5b810 img).symm) (by sep_focus) ?_
  have htrf_0 : sf.trace = s0.trace := by
    rw [htrf_12, htr12_11, htr11_10, htr10_9, htr9_8, htr8_7, htr7_0]
  have hcs_f : ClosureCalleeSaved s0 sf := ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩
  refine SepWPp.done hpcf hrunf ⟨?_, hspf_s, htrf_0, hcs_f, hFf, hsymf⟩
  exact entails_anyHeap_10 (by sep_focus)

set_option maxHeartbeats 6400000 in
/-- Stage P3 Version-Mismatch Error Funnel (`+0x1bac -> s0.readReg64 .x30`): When `msgVer ≠ 4#32`, stores the cloned `SessionState` (`344` B) into `sp + 0xa90..0xbe8`,
constructs `SignalProtocolError::UnrecognizedMessageVersion(msgVer)` (`tag = 0x8000000000000006#64`)
at `sp + 0x3e0..0x410`, invokes `pqxdh_log_closure_ok`, grows the error `Vec` via
`grow_one_spe_ok` (`0x15c44`), drops the cloned `SessionState` via `drop_session_structure3_ok`, allocates `"decryption failed"` (`17` B) at `+0x33b0`, drops the error `Vec` elements
via `drop_spe2_ver_ok` and deallocates the `192`-byte buffer, drops the original Bob
`SessionState` at `coroPtr + 0xf8` via `drop_session_structure3_ok`, and returns
`Poll::Ready(Err(InvalidMessage(Whisper, "decryption failed")))` (`tag = 0x8000000000000018#64`)
at `outPtr` to `s0.readReg64 .x30`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ver_ne_ok {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State)) (hA : AllocHooks A abs) (himg :
    Obj.Loads libsignalSessionImage img) (s0 s : State) (coroPtr newLocIdPtr newRemIdPtr
    newRootKeyPtr newAliceBasePtr v08 v10 v18 c0 u_c0 outPtr errsPtr0 prevStatesPtr : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (msgVer v24 v28 v2c f248 f24c prevCounter : BitVec 32)
    (b_2c0 : BitVec 8) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes : List (BitVec 8)) (sg' :
    SenderChainGhost) (sc : SenderChain) (G₀ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (remIk : IdentityKey) (hver_ne : msgVer ≠ 4#32) (herrs_nz : errsPtr0 ≠ 0#64) (hcap0 :
    G₀.localIk.cap ≠ 0xffffffffffffffff#64) (hnew1 : newLocIdPtr ≠ 0#64) (hnew2 : newRemIdPtr ≠
    0#64) (hnew3 : newRootKeyPtr ≠ 0#64) (hnew4 : newAliceBasePtr ≠ 0#64) (hloc_len :
    locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33) (halice_len : aliceBaseBytes.length
    = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok st.localIdentity.publicKey) (hrem_eq
    : st.remoteIdentity = some remIk) (hrem_deser : PublicKey.deserialize remIdBytes = .ok
    remIk.publicKey) (hroot_eq : rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains =
    []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey =
    false) (hver : st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hsc_inl :
    OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5)) (hF :
    img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc : s.pc = (tripleRatchetProgAt img.base C
    ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) (hrun : s.status = .Running) (hsp_align :
    (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = 1#64) (hx22 : s.readReg64 .x22 = 0xffffffffffffffff#64) (hx23 :
    s.readReg64 .x23 = newAliceBasePtr) (hx24 : s.readReg64 .x24 = 33#64) (hx25 : s.readReg64 .x25 =
    8#64) (hx26 : s.readReg64 .x26 = 0#64) (hx28 : s.readReg64 .x28 = 32#64) : SepWPp
    (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s
      (memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
       ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp
       + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
       0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0)
       ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
       0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr)
       ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp +
       0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp +
       0xd0#64) ↦₆₄ 33#64) ∗ memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr0) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x3e0#64)
       48 ∗ ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64
       64) ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb'
       64 64) ∗ ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄
       sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64)
       ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp +
       0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp
       + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ A.live newLocIdPtr 33 1 ∗ (newLocIdPtr ↦ₛ
       locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗ A.live newRootKeyPtr 32
       1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗ (newAliceBasePtr ↦ₛ
       aliceBaseBytes) ∗ optSenderChainHeap A (some sg') (some sc) ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64)
       ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ sessionStateAt A
       (coroPtr + 0xf8#64) G₀ st ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ decryptPrekeySavedRegsAt (s.sp
       + 0xcd0#64) s0 ∗ memRegion outPtr 48 ∗ logOff img ∗ stackAt s.sp growOneSpeStack ∗ A.pool)
      (fun sf P_f => (P_f ⊢ (outPtr ↦₆₄ 0x8000000000000018#64) ∗ memRegion (outPtr + 8#64) 40 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr +
          0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ logOff img ∗ decryptPrekeySavedRegsAt
          (s.sp + 0xcd0#64) s0 ∗ stackAt s.sp growOneSpeStack ∗ A.pool ∗ anyHeap) ∧ sf.sp = s.sp +
          0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧ img.FrozenLoaded sf ∧
          sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq img.base C ctl abs] at hpc
  exact SepWPp_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ver_ne_ok_trap img C abs hA himg s0 s coroPtr newLocIdPtr newRemIdPtr
    newRootKeyPtr newAliceBasePtr v08 v10 v18 c0 u_c0 outPtr errsPtr0 prevStatesPtr sq0 sq1 sq2 sq3
    sq4 sq5 msgVer v24 v28 v2c f248 f24c prevCounter b_2c0 locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes sg' sc G₀ st remIk hver_ne herrs_nz hcap0 hnew1 hnew2 hnew3 hnew4 hloc_len
    hrem_len halice_len hloc_deser hrem_eq hrem_deser hroot_eq hrc hpq hsc hpend hver hprev hsc_inl
    hF hsym hpc hrun hsp_align htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx28)

/-! ## 3. Combined Clone + Version Dispatch (`+0x1778 → +0x1cd8` and `+0x1778 → x30`) -/

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_and_tryDecrypt_v4_ok_trap {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr v08 v10 v18
    remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938
    u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64) (v24 v28 v2c prevCounter f248
    f24c u_30 u_34 u_5c u_7c : BitVec 32) (sg : SenderChainGhost) (sc : SenderChain) (locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes rest : List (BitVec 8)) (st : SessionState (List (BitVec
    8))) (remIk : IdentityKey) (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg :
    SignalMessage) (hloc_nz : locIdPtr ≠ 0#64) (hrem_nz : remIdPtr ≠ 0#64) (hroot_nz : rootKeyPtr ≠
    0#64) (halice_nz : aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length = 33) (hrem_len :
    remIdBytes.length = 33) (hroot_len : rootKeyBytes.length = 32) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity) (hroot_eq : rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains =
    []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey =
    false) (hver : st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hnpan1 :
    (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic) (hnpan2 : ¬
    S.recvPanics st.pqRatchetState msg.pqRatchet) (hF : img.FrozenLoaded s) (hsym : s.symtab =
    img.symtab) (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64
    == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace) (hx19 :
    s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) : SepWPp
    (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s
      (stageP3ClonePre A s.sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
        u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
        u978 u980 u988 prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes
        rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr
        aliceBasePtr ∗ memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp +
        0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp +
        0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp
        + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x3a0#64) ↦₆₄
        remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A rem remAddrPtr ∗
        protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion
        (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗ memRegion (s.sp - BitVec.ofNat 64
        rootStack) (rootStack - chainCloneStack))
      (fun s2 P_f => ∃ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
          (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
          SessionGhost), newLocIdPtr ≠ 0#64 ∧ newRemIdPtr ≠ 0#64 ∧ newRootKeyPtr ≠ 0#64 ∧
          newAliceBasePtr ≠ 0#64 ∧ sg'.srk.bytes = sg.srk.bytes ∧ sg'.priv.bytes = sg.priv.bytes ∧
          OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) ∧
          (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic ∧
          (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
            locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt (pqxdhTryDecryptModel C S
            uuidTryParse rem loc msg rest st).1.toBool G' ∧ (P_f ⊢ sessionStateAt A (s.sp +
            0xa90#64) G' (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt
            A (s.sp + 0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
            sessionStateAt A (coroPtr + 0xf8#64)
              (mkClonedGhost locIdPtr remIdPtr rootKeyPtr aliceBasePtr
                locIdBytes remIdBytes aliceBaseBytes sg f248 f24c) st ∗ protocolAddressAt A rem
                remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG
                whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey
                rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ memRegion (s.sp + 0x3e0#64)
                104 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄
                v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64)
                ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
                0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp +
                0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂
                prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗
                ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x98#64)
                ↦₆₄ 32#64) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
                whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp +
                0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp +
                0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64)
                ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄
                sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp +
                0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64)
                ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄
                sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp +
                0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧ s2.sp = s.sp ∧ s2.trace = s0.trace ∧
                img.FrozenLoaded s2 ∧ s2.symtab = img.symtab ∧ s2.readReg64 .x19 = coroPtr ∧
                s2.readReg64 .x24 = s.sp + 0x370#64 ∧ s2.readReg64 .x27 = ctxPtr ∧ s2.readReg64 .x29
                = s.readReg64 .x29)
      (PanicOomProp s0) := by
  dsimp only [stageP3ClonePre]
  refine SepWPp.bind_oom_frame
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_ok_trap img img.base C abs hH.alloc s0 s coroPtr
      locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
      u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 prevCounter f248 f24c u_30 u_34
      u_5c u_7c sg sc locIdBytes remIdBytes rootKeyBytes aliceBaseBytes hloc_len hrem_len hroot_len
      halice_len hF hsym hpc hrun hsp_align htr hx19 hx27)
    (by sep_focus)
    fun s1 P_f1 hpc1 hrun1 ⟨newLocIdPtr, newRemIdPtr, newRootKeyPtr, newAliceBasePtr, sg', c0, sq0,
      sq1, sq2, sq3, sq4, sq5, hnew1, hnew2, hnew3, hnew4, hsrk', hpriv', hsc_inl, hent1, hsp1,
      htr1, hF1, hsym1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1,
      hx29_1⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hent1) ?_
  refine SepWPp.weaken_frame
    (bobCoroRest_fold_sessionStateAt coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr
      locIdBytes remIdBytes rootKeyBytes aliceBaseBytes sg sc prevCounter f248 f24c st remIk hloc_nz
      hrem_nz hroot_nz halice_nz hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser hroot_eq
      hrc hpq hsc hpend hver hprev)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_root_eq_chainClone s.sp).symm) (by sep_focus) ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  have hsp1_root : rootStack ≤ s1.sp.toNat := by rw [hsp1]; exact hsp_root
  have hdec := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_nopanic_ok_trap img C S abs hH hempty himg s0 s1 coroPtr
    newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18 c0 remAddrPtr locAddrPtr
    whisperMsgPtr cur sq0 sq1 sq2 sq3 sq4 sq5 v24 v28 v2c f248 f24c prevCounter locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes rest sg' sc st remIk rem loc msgG msg hnpan1 hnpan2 hnew1
    hnew2 hnew3 hnew4 hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser hnot_self hroot_eq
    hrc hpq hsc hpend hver hprev hsc_inl hF1 hsym1 hpc1 hrun1 hsp1_align hsp1_root htr1 hx19_1
    hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1
  rw [hsp1] at hdec
  refine SepWPp.bind_oom_frame hdec (by sep_focus)
    fun s2 P_f2 hpc2 hrun2 ⟨G', hnpan, hdec_rel, hent2, hsp2, htr2, hF2, hsym2, hx19_2, hx24_2,
    hx27_2, hx29_2⟩ => ?_
  refine SepWPp.done hpc2 hrun2 ⟨newLocIdPtr, newRemIdPtr, newRootKeyPtr, newAliceBasePtr, sg', c0,
    sq0, sq1, sq2, sq3, sq4, sq5, G', hnew1, hnew2, hnew3, hnew4, hsrk', hpriv', hsc_inl, hnpan,
    hdec_rel, ?_, hsp2, htr2, hF2, hsym2, hx19_2, hx24_2, hx27_2.trans hx27_1, hx29_2.trans hx29_1⟩
  exact Entails.trans (sepConj_mono_left hent2) (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 3200000 in
/-- Combined Stage P3 Clone + Version-4 `try_decrypt_with_state` (`+0x1778 -> +0x1cd8`): Composes `stageP3_clone_ok` (`+0x1778 -> +0x1bac`) and `stageP3_tryDecrypt_v4_nopanic_ok`
(`+0x1bac -> +0x1cd8`), folding the original Bob `SessionState` at `coroPtr + 0xf8`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_and_tryDecrypt_v4_ok {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr v08 v10 v18
    remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938
    u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64) (v24 v28 v2c prevCounter f248
    f24c u_30 u_34 u_5c u_7c : BitVec 32) (sg : SenderChainGhost) (sc : SenderChain) (locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes rest : List (BitVec 8)) (st : SessionState (List (BitVec
    8))) (remIk : IdentityKey) (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg :
    SignalMessage) (hloc_nz : locIdPtr ≠ 0#64) (hrem_nz : remIdPtr ≠ 0#64) (hroot_nz : rootKeyPtr ≠
    0#64) (halice_nz : aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length = 33) (hrem_len :
    remIdBytes.length = 33) (hroot_len : rootKeyBytes.length = 32) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity) (hroot_eq : rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains =
    []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey =
    false) (hver : st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hnpan1 :
    (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic) (hnpan2 : ¬
    S.recvPanics st.pqRatchetState msg.pqRatchet) (hF : img.FrozenLoaded s) (hsym : s.symtab =
    img.symtab) (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64
    == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace) (hx19 :
    s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) : SepWPp
    (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s
      (stageP3ClonePre A s.sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
        u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
        u978 u980 u988 prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes
        rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr
        aliceBasePtr ∗ memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp +
        0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp +
        0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp
        + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x3a0#64) ↦₆₄
        remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A rem remAddrPtr ∗
        protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion
        (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗ memRegion (s.sp - BitVec.ofNat 64
        rootStack) (rootStack - chainCloneStack))
      (fun s2 P_f => ∃ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
          (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
          SessionGhost), newLocIdPtr ≠ 0#64 ∧ newRemIdPtr ≠ 0#64 ∧ newRootKeyPtr ≠ 0#64 ∧
          newAliceBasePtr ≠ 0#64 ∧ sg'.srk.bytes = sg.srk.bytes ∧ sg'.priv.bytes = sg.priv.bytes ∧
          OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) ∧
          (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic ∧
          (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
            locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt (pqxdhTryDecryptModel C S
            uuidTryParse rem loc msg rest st).1.toBool G' ∧ (P_f ⊢ sessionStateAt A (s.sp +
            0xa90#64) G' (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt
            A (s.sp + 0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
            sessionStateAt A (coroPtr + 0xf8#64)
              (mkClonedGhost locIdPtr remIdPtr rootKeyPtr aliceBasePtr
                locIdBytes remIdBytes aliceBaseBytes sg f248 f24c) st ∗ protocolAddressAt A rem
                remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG
                whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey
                rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ memRegion (s.sp + 0x3e0#64)
                104 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄
                v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64)
                ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
                0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp +
                0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂
                prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗
                ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x98#64)
                ↦₆₄ 32#64) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
                whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp +
                0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp +
                0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64)
                ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄
                sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp +
                0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64)
                ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄
                sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp +
                0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧ s2.sp = s.sp ∧ s2.trace = s0.trace ∧
                img.FrozenLoaded s2 ∧ s2.symtab = img.symtab ∧ s2.readReg64 .x19 = coroPtr ∧
                s2.readReg64 .x24 = s.sp + 0x370#64 ∧ s2.readReg64 .x27 = ctxPtr ∧ s2.readReg64 .x29
                = s.readReg64 .x29)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq img.base C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_and_tryDecrypt_v4_ok_trap img C S abs hH hempty himg s0 s coroPtr
    locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr
    cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
    u978 u980 u988 v24 v28 v2c prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes rest st remIk rem loc msgG msg hloc_nz hrem_nz hroot_nz
    halice_nz hloc_len hrem_len hroot_len halice_len hloc_deser hrem_eq hrem_deser hnot_self
    hroot_eq hrc hpq hsc hpend hver hprev hnpan1 hnpan2 hF hsym hpc hrun hsp_align hsp_root htr
    hx19 hx27)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_and_ver_ne_ok_trap {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) (himg :
    Obj.Loads libsignalSessionImage img) (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr
    aliceBasePtr ctxPtr v08 v10 v18 outPtr errsPtr0 prevStatesPtr u_38 u_40 u_48 u_50 u_60 u_68 u_70
    u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64) (msgVer v24
    v28 v2c prevCounter f248 f24c u_30 u_34 u_5c u_7c : BitVec 32) (b_2c0 : BitVec 8) (sg :
    SenderChainGhost) (sc : SenderChain) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes : List
    (BitVec 8)) (st : SessionState (List (BitVec 8))) (remIk : IdentityKey) (hver_ne : msgVer ≠
    4#32) (herrs_nz : errsPtr0 ≠ 0#64) (hloc_nz : locIdPtr ≠ 0#64) (hrem_nz : remIdPtr ≠ 0#64)
    (hroot_nz : rootKeyPtr ≠ 0#64) (halice_nz : aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length =
    33) (hrem_len : remIdBytes.length = 33) (hroot_len : rootKeyBytes.length = 32) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hroot_eq : rootKeyBytes = keyToBytes32
    st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain
    = some sc) (hpend : st.pendingPreKey = false) (hver : st.sessionVersion = 4#32) (hprev :
    st.previousCounter = prevCounter) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc
    : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace =
    s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWPp (trTrapProgAt img.base C abs) (s0.readReg64 .x30) s
      (stageP3ClonePre A s.sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
        u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
        u978 u980 u988 prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes
        rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr
        aliceBasePtr ∗ memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp +
        0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp +
        0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64))
        ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ memRegion (s.sp +
        0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗ ((s.sp +
        0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr0) ∗ ((s.sp
        + 0x3d8#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄
        prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
        decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ memRegion outPtr 48 ∗ logOff img ∗ memRegion
        (s.sp - BitVec.ofNat 64 growOneSpeStack) (growOneSpeStack - chainCloneStack))
      (fun sf P_f => (P_f ⊢ (outPtr ↦₆₄ 0x8000000000000018#64) ∗ memRegion (outPtr + 8#64) 40 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr +
          0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ logOff img ∗ decryptPrekeySavedRegsAt
          (s.sp + 0xcd0#64) s0 ∗ stackAt s.sp growOneSpeStack ∗ A.pool ∗ anyHeap) ∧ sf.sp = s.sp +
          0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧ img.FrozenLoaded sf ∧
          sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  dsimp only [stageP3ClonePre]
  refine SepWPp.bind_oom_frame
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_ok_trap img img.base C abs hA s0 s coroPtr
      locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
      u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 prevCounter f248 f24c u_30 u_34
      u_5c u_7c sg sc locIdBytes remIdBytes rootKeyBytes aliceBaseBytes hloc_len hrem_len hroot_len
      halice_len hF hsym hpc hrun hsp_align htr hx19 hx27)
    (by sep_focus)
    fun s1 P_f1 hpc1 hrun1 ⟨newLocIdPtr, newRemIdPtr, newRootKeyPtr, newAliceBasePtr, sg', c0, sq0,
      sq1, sq2, sq3, sq4, sq5, hnew1, hnew2, hnew3, hnew4, _, _, hsc_inl, hent1, hsp1, htr1, hF1,
      hsym1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, _, hx28_1, _⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hent1) ?_
  refine SepWPp.weaken_frame
    (bobCoroRest_fold_sessionStateAt coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr
      locIdBytes remIdBytes rootKeyBytes aliceBaseBytes sg sc prevCounter f248 f24c st remIk hloc_nz
      hrem_nz hroot_nz halice_nz hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser hroot_eq
      hrc hpq hsc hpend hver hprev)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_sub_eq s.sp growOneSpeStack chainCloneStack).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (sp3e0_104_split_48 s.sp)) (by sep_focus) ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  have hver_ok := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ver_ne_ok_trap img C abs hA himg s0 s1 coroPtr
    newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18 c0 ctxPtr outPtr errsPtr0
    prevStatesPtr sq0 sq1 sq2 sq3 sq4 sq5 msgVer v24 v28 v2c f248 f24c prevCounter b_2c0 locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes sg' sc (mkClonedGhost locIdPtr remIdPtr rootKeyPtr
    aliceBasePtr
      locIdBytes remIdBytes aliceBaseBytes sg f248 f24c) st remIk
    hver_ne herrs_nz (by dsimp only [mkClonedGhost]; decide) hnew1 hnew2 hnew3 hnew4 hloc_len
    hrem_len halice_len
    hloc_deser hrem_eq hrem_deser hroot_eq hrc hpq hsc hpend hver hprev hsc_inl hF1 hsym1 hpc1 hrun1
    hsp1_align htr1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1
  rw [hsp1] at hver_ok
  refine SepWPp.bind_oom_frame hver_ok (by sep_focus)
    fun sf P_ff hpcf hrunf ⟨hentf, hspf, htrf, hcsf, hFf, hsymf⟩ => ?_
  refine SepWPp.done hpcf hrunf ⟨?_, hspf, htrf, hcsf, hFf, hsymf⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  simp only [sepConj_assoc]
  repeat apply sepConj_mono_right
  exact entails_anyHeap _

set_option maxHeartbeats 3200000 in
/-- Combined Stage P3 Clone + Version-Mismatch Error Funnel (`+0x1778 -> s0.readReg64 .x30`): Composes `stageP3_clone_ok` (`+0x1778 -> +0x1bac`) and `stageP3_ver_ne_ok` (`+0x1bac -> x30`)
when `msgVer ≠ 4#32`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_and_ver_ne_ok {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State)) (hA : AllocHooks A abs) (himg :
    Obj.Loads libsignalSessionImage img) (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr
    aliceBasePtr ctxPtr v08 v10 v18 outPtr errsPtr0 prevStatesPtr u_38 u_40 u_48 u_50 u_60 u_68 u_70
    u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64) (msgVer v24
    v28 v2c prevCounter f248 f24c u_30 u_34 u_5c u_7c : BitVec 32) (b_2c0 : BitVec 8) (sg :
    SenderChainGhost) (sc : SenderChain) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes : List
    (BitVec 8)) (st : SessionState (List (BitVec 8))) (remIk : IdentityKey) (hver_ne : msgVer ≠
    4#32) (herrs_nz : errsPtr0 ≠ 0#64) (hloc_nz : locIdPtr ≠ 0#64) (hrem_nz : remIdPtr ≠ 0#64)
    (hroot_nz : rootKeyPtr ≠ 0#64) (halice_nz : aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length =
    33) (hrem_len : remIdBytes.length = 33) (hroot_len : rootKeyBytes.length = 32) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hroot_eq : rootKeyBytes = keyToBytes32
    st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain
    = some sc) (hpend : st.pendingPreKey = false) (hver : st.sessionVersion = 4#32) (hprev :
    st.previousCounter = prevCounter) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc
    : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace =
    s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s
      (stageP3ClonePre A s.sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
        u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
        u978 u980 u988 prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes
        rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr
        aliceBasePtr ∗ memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp +
        0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp +
        0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64))
        ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ memRegion (s.sp +
        0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗ ((s.sp +
        0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr0) ∗ ((s.sp
        + 0x3d8#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄
        prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
        decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ memRegion outPtr 48 ∗ logOff img ∗ memRegion
        (s.sp - BitVec.ofNat 64 growOneSpeStack) (growOneSpeStack - chainCloneStack))
      (fun sf P_f => (P_f ⊢ (outPtr ↦₆₄ 0x8000000000000018#64) ∗ memRegion (outPtr + 8#64) 40 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr +
          0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ logOff img ∗ decryptPrekeySavedRegsAt
          (s.sp + 0xcd0#64) s0 ∗ stackAt s.sp growOneSpeStack ∗ A.pool ∗ anyHeap) ∧ sf.sp = s.sp +
          0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧ img.FrozenLoaded sf ∧
          sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq img.base C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_and_ver_ne_ok_trap img C abs hA himg s0 s coroPtr
    locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr v08 v10 v18 outPtr errsPtr0 prevStatesPtr
    u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
    u978 u980 u988 msgVer v24 v28 v2c prevCounter f248 f24c u_30 u_34 u_5c u_7c b_2c0 sg sc
    locIdBytes remIdBytes rootKeyBytes aliceBaseBytes st remIk hver_ne herrs_nz hloc_nz hrem_nz
    hroot_nz halice_nz hloc_len hrem_len hroot_len halice_len hloc_deser hrem_eq hrem_deser
    hroot_eq hrc hpq hsc hpend hver hprev hF hsym hpc hrun hsp_align htr hx19 hx27)

end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
