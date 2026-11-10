/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Trans
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5V1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub6V1

/-!
# Kit-Generic Stage P2 Fresh-Session Composition

Verifies Stage P2 (`+0x0868 → +0x1778` fresh Bob session initialization at SPQR V1, together with
all six store-error and PQXDH-rejection unwind exits to `s0.readReg64 .x30`) for
`message_decrypt_prekey::<Coins>::{closure#0}` against generic store kits.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (mkBobSenderChainGhost)
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_mono_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P₁ P₂ : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (h : SepWPp prog ret s P₂ Q Qp) :
    SepWPp prog ret s P₁ Q Qp :=
  fun R hm hL => h R (Arm64.Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem p2_arm5_err_payload_pull {A : RustAlloc} (img : Obj.Image) (s0 : State)
    (sp fp coroPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt
     v_330 v_388 errTag w2 w3 w4 w5 w6 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (S_spk S_kpk S_pk S_id : SepProp)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
      S_spk ∗ S_kpk ∗ S_pk ∗ S_id ∗
      p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt
        v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk (pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗ Frame) ⊢
    speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
      pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
      S_spk ∗ S_kpk ∗ S_pk ∗ S_id ∗
      p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt
        v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk Frame := by
  dsimp only [p2ErrFrameAt]
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- Verifies Stage P2 (`+0x0868 → +0x1778` fresh Bob session initialization, plus all six
store-error and PQXDH-rejection exits to `s0.readReg64 .x30`) parameterized by stack bound `stk`,
hook bundle, and panic postcondition `{Qp}`. -/
theorem stageP2_v1_kits_at {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : StageP2ClosureHooks A img.base ext)
    (hPure : StageP2PureCallees4K P A F img ext)
    {sameStk bobErrStk bobV1Stk : Nat}
    (hSameAcct :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.isSameAccountName)
        (isSameAccountDistinctAtSpec A uuidTryParse sameStk))
    (hInitBobErrOwned :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
        (initializeBobSessionErrOwnedAtSpec P A img bobErrStk))
    (hInitBobV1 : InitializeBobV1OkAtExt P A F img ext bobV1Stk)
    (hsame_le : sameStk ≤ bobV1Stk)
    (herr_le : bobErrStk ≤ bobV1Stk)
    (ikit : IdentityStoreSpec A img.base) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesOk img ikit skit)
    (hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (hspkVt : SignedPreKeyVtablesOk img spkKit)
    (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hkpkVt : KyberPreKeyVtablesOk img kpkKit)
    (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (pkKit : PreKeyStoreSpec A img.base)
    (hpkVt : PreKeyVtablesOk img pkKit)
    (hpkOk : PreKeyStoreKitOkImgE img pkKit ext)
    {v1CallStk : Nat}
    (hv1_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ v1CallStk)
    (hv1_bob : bobV1Stk ≤ v1CallStk)
    (stk : Nat) (hstk : v1CallStk ≤ stk)
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, ResponderClosure.PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hctBuf_nz : ctBufPtr ≠ 0#64)
    (hpqr_ne : sp - 576#64 ≠ 0#64)
    (hstk_lt : stk ≤ sp.toNat)
    (hikBSk_len : ikBSk.length = 32) (hikBPk_len : ikBPk.length = 32)
    (hikAPk_len : hdr.ikAPk.length = 32) (hekAPk_len : hdr.ekAPk.length = 32)
    (hkemCt_len : hdr.kemCt.length = 1568)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) s)
    (hid_spk : spkKit.idOk signedPreKeyId)
    (hspk_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) →
      spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
        spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hkpk_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopk_word : ∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → opkIdWord = id)
    (hid_pk : ∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → pkKit.getIdOk id)
    (hpk_wf : ∀ (id : BitVec 32) (r : PreKeyRecord), hdrOpkIdBv? hdr = some id →
      pkKit.getRel stPk id (.ok r) → pkKit.RecOk r →
      ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
        opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
        r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes)
    (hkp_sk : ∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.privateKey.bytes.toList = bytesToBv8 ikBSk)
    (hkp_pk : ∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk)
    (hneq : bytesToBv8 ikBPk ≠ bytesToBv8 hdr.ikAPk ∨
      DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running) (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kpkKit.kpk_vt) (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = pkKit.pk_vt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = ikit.id_vt) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) (hx29 : s.readReg64 .x29 = fp)
    (hErrSpk : ∀ (e : spkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt spkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
        kpkKit.storeAt kyberStorePtr stKpk ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (hErrKpk : ∀ (spkRec : SignedPreKeyRecord) (e : kpkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt kpkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (hErrPk : ∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
        (opkId : BitVec 32) (e : pkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      hdrOpkIdBv? hdr = some opkId → pkKit.getRel stPk opkId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ pkKit.getEvs opkId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt pkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (hErrKp : ∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (e : skit.KpErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      skit.kpRel stId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt skit.kpErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (hErrBob : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (errTag w2 w3 w4 w5 w6 : BitVec 64)
        (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      Model.acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = none →
      errTag ≠ 0xfffffffffffffffe#64 → errTag ≠ 0xfffffffffffffffd#64 →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
        pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (hErrRegId : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (drKey : DRKey) (e : skit.RegIdErr)
        (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      Model.acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey →
      skit.regIdRel stId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) ++ skit.regIdEvs (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt skit.regIdErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (hOk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (drKey : DRKey) (localRegId : BitVec 32)
        (G_bob : SessionGhost) (sf : State),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      (hspkPub_len : spkPubBytes.length = 32) → (hspkPriv_len : spkPrivBytes.length = 32) →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      Model.acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey →
      skit.regIdRel stId (.ok localRegId) →
      G_bob.pending = none →
      G_bob.kyber = none →
      G_bob.alice.bytes = bytesToBv8 (Model.encodeEC hdr.ekAPk) →
      G_bob.regIds = unpack32 remoteRegId ++ unpack32 localRegId →
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
        (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) sf →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1778#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) ++ skit.regIdEvs (.ok localRegId) →
      sf.readReg64 .x8 = coroPtr + 0xe0#64 →
      sf.readReg64 .x9 = 8#64 →
      sf.readReg64 .x10 = msgVerByte.zeroExtend 64 →
      sf.readReg64 .x11 = coroPtr + 0xf8#64 →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x20 = 0xfffffffffffffffe#64 →
      sf.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 →
      sf.readReg64 .x23 = (opkOptTag32 (hdrOpkIdBv? hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32) →
      sf.readReg64 .x24 = (opkOptTag32 (hdrOpkIdBv? hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32) →
      sf.readReg64 .x25 = sp + 0x210#64 →
      sf.readReg64 .x26 = v_330 →
      sf.readReg64 .x27 = sp + 0x370#64 →
      sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
        (p2OkPostAt A img spkKit kpkKit pkKit ikit s0
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
          G_bob
          (p2BobInitSessionV1 ikBPk (toU8 spkPubBytes)
            (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
              kyberPubBytes kyberPrivBytes opkSkBytes)
            drKey (initialStateValue F (p2BobSpqrParams drKey.pqrKey))
            hikBPk_len hikAPk_len
            (by simp [toU8, hspkPub_len])
            (by simp [mkP2AcceptKeysInput, toU8, clampBv8List_length hspkPriv_len]))
          hdr msgVerByte b_2c0 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk)
          stId gMe gPeer stk Frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP2PreAt A img spkKit kpkKit pkKit ikit s0
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
        hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        stSpk stKpk stPk stId gMe gPeer stk Frame)
      Q Qp := by
  have hstk_le64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hstk_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk :=
    Nat.le_trans hv1_p2 hstk
  have hstk_bob : bobV1Stk ≤ stk :=
    Nat.le_trans hv1_bob hstk
  have hstk_sub56 : stageP2Sub56Stack skit ≤ stk :=
    Nat.le_trans (p2_sub56_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2
  have hstk_alloc : allocHookStack ≤ stk :=
    Nat.le_trans (p2_allocHookStack_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2
  have hstk_drop : dropSessionStructureLocal2Stack ≤ stk :=
    Nat.le_trans (p2_dropSs3Stack_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2
  have hkem_pos : 0 < (bytesToBv8 hdr.kemCt).length := by
    simp [bytesToBv8, hkemCt_len]
  let baseKey : PublicKey := ⟨⟨bytesToBv8 hdr.ekAPk, by simpa [bytesToBv8] using hekAPk_len⟩⟩
  refine p2_mono_pre
    (p2_entry_to_sub1To4 img spkKit kpkKit pkKit ikit s0
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer stk Frame) ?_
  refine stageP2_sub1_to_4_kits_ext img ext himg hH hPure
    ikit skit hskitVt hskitOk spkKit hspkVt hspkOk kpkKit hkpkVt hkpkOk pkKit hpkVt hpkOk
    stk hstk_p2 hstk_le64 s0 s
    (p2Sub1To4Frame A ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
      v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame)
    Q hpan sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr ctBufPtr
    (coroPtr + 0x390#64) u_90 u_a8 u_b8 u_d0 u_488
    baseKey signedPreKeyId kyberPreKeyId opkIdWord (hdrOpkIdBv? hdr)
    stSpk stKpk stPk b_2c0 b_390 b_4b0 b_4f1 b_4f2
    hb hctBuf_nz hF hsym hfs
    hid_spk hspk_wf hid_kpk hkpk_wf hopk_word hid_pk hpk_wf
    hpc hrun hsp_eq hsp_align htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
    -- Arm 1: `get_signed_pre_key` error
    (fun e spkFutPtr sf P_f hrel hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
      hErrSpk e sf P_f hrel hpcf hrunf htrf hspf hcsf hvregsf hinvf
        (Entails.trans hent
          (p2_v1_arm1_entails img spkKit kpkKit pkKit ikit s0
            sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
            (coroPtr + 0x390#64) v_330 v_388 u_488 u_80 u_88 spkFutPtr
            b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr
            stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    -- Arm 2: `get_kyber_pre_key` error
    (fun spkRec spkPubBytes spkPrivBytes e kyberFutPtr sf P_f
        hspk_rel hspk_ok hpub_len hpriv_len _ _ hkpk_rel
        hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
      hErrKpk spkRec e sf P_f hspk_rel hspk_ok hkpk_rel hpcf hrunf htrf hspf hcsf hvregsf hinvf
        (Entails.trans hent
          (p2_v1_arm2_entails img spkKit kpkKit pkKit ikit s0
            sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
            (coroPtr + 0x390#64) v_330 v_388 u_488 u_80 u_88 kyberFutPtr
            b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr
            spkRec spkPubBytes spkPrivBytes hpub_len hpriv_len
            stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    -- Arm 3: `get_pre_key` error
    (fun spkRec spkPubBytes spkPrivBytes kpkRec _ _ opkId e pkBuf skBuf opkFutPtr v90 sf P_f
        hspk_rel hspk_ok hpub_len hpriv_len _ _ hkpk_rel hkpk_ok _ _ _ _ hopk_some hpk_rel
        hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
      hErrPk spkRec kpkRec opkId e sf P_f
        hspk_rel hspk_ok hkpk_rel hkpk_ok hopk_some hpk_rel
        hpcf hrunf htrf hspf hcsf hvregsf hinvf
        (Entails.trans hent
          (p2_v1_arm3_entails img spkKit kpkKit pkKit ikit s0
            sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
            (coroPtr + 0x390#64) v_330 v_388 u_80 u_88 pkBuf skBuf opkFutPtr v90
            b_4b0 msgVerByte opkId opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr
            spkRec kpkRec spkPubBytes spkPrivBytes hpub_len hpriv_len
            stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    -- Substages 1–4 Ok (`+0x36ac`) -> Substage 5 -> Substage 6
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes pkBuf skBuf idKpFutPtr v90 v_a8' v_b8' v_d0' s4
        hst_s4 hfs4 hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
        hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
        hopk_rel hopkPk_len hopkSk_len hopk_kb
        _ _ _ _
        hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4
        hx29_4 hvregs4 hF4 hsym4 => ?_)
  let inp := mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
    kyberPubBytes kyberPrivBytes opkSkBytes
  let spkBPk : SignalPqxdh.Bytes := toU8 spkPubBytes
  have hspkBPk_len : spkBPk.length = 32 := by simp [spkBPk, toU8, hspkPub_len]
  have hwell : WellSizedAcceptKeysInput inp :=
    wellSized_mkP2AcceptKeysInput hikBSk_len hikBPk_len hspkPub_len hspkPriv_len
      hkyberPub_len hkyberPriv_len hopkSk_len hikAPk_len hekAPk_len hkemCt_len
  have hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk :=
    fun _ h => opkOkSkBytes?_eq_of_some h
  have htr_s_s4 : s.trace <+: s4.trace := by
    rw [htr4, List.append_assoc, List.append_assoc]
    exact List.prefix_append _ _
  have htr0_4 : s0.trace <+: s4.trace := htr.trans htr_s_s4
  refine p2_mono_pre
    (p2_sub4_to_sub5 img spkKit kpkKit pkKit skit s0
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0'
      inp hdr spkBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkPkBytes opkSkBytes
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      msgVerByte b_2c0 b_390 b_4f2
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
      gMe gPeer stk Frame
      rfl (bytesToBv8_toU8 spkPubBytes)
      (mkP2AcceptKeysInput_spkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes)
      (mkP2AcceptKeysInput_pqspkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes)
      (opkOptTag8_eq_opkPresentTag (hdrOpkIdBv? hdr) opkSkBytes).symm
      hkyberPriv_len hkem_pos) ?_
  refine SepWPp.exists_elim fun u_b90 => SepWPp.exists_elim fun b_b98 => ?_
  refine stageP2_sub5_v1_kits_at img ext skit hH hskitOk hskitVt
    hSameAcct hInitBobErrOwned hInitBobV1 hsame_le herr_le
    inp spkBPk opkPkBytes opkSkBytes gMe gPeer stId s0 s4 Q hpan
    sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idKpFutPtr pkBuf skBuf ctBufPtr fp
    v_a8' v_b8' v_d0' u_b90 opkIdWord 1#8 b_b98 stk
    (p2Sub5Frame A img spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
      remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
      msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) Frame)
    hb rfl rfl (hdr_opkId?_isSome_eq_opkOkSkBytes? hdr opkSkBytes)
    hwell hspkBPk_len hopkPk_len hopkSk_len hopkSk_eq
    (fun kp hkp => hkp_sk kp hkp)
    (fun kp hkp => by rw [hkp_pk kp hkp]; exact hneq)
    hpqr_ne hstk_bob hstk_sub56 hstk_lt
    hF4 hsym4 hpc4 hrun4 hsp4 hsp_align htr0_4 hvregs4
    (fun s1 htr1 hst1 => p2_envOk_id hfs4 hst1 htr1)
    hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4 hx26_4 hx27_4 hx28_4 (hx29_4.trans hx29)
    -- Substage 5 Ok (`+0x125c`) -> Substage 6
    (fun kp drKey s5 v_a8'' v_b8'' v_d0'' u_b90' b_b98'
        hkp_rel hacc hst_s5 hpc5 hrun5 hsp5 htr5
        hx19_5 _ _ _ _ hx25_5 _ hx28_5 hx29_5 hvregs5 hF5 hsym5 => ?_)
    -- Arm 5: `initialize_bob_session` error (`acceptKeys = none`)
    (fun kp errTag w2 w3 w4 w5 w6 sf5 v_a8'' v_b8'' v_d0'' u_b90' b_b98'
        hkp_rel hacc_none herr_ne_ok herr_ne_pend _ hpc5 hrun5 hsp5 htr5
        hx19_5 _ _ _ _ hx25_5 _ hx28_5 _ hvregs5 hF5 hsym5 => by
      have hikBPk_eq : toU8 kp.identityKey.publicKey.bytes.toList = ikBPk := by
        rw [hkp_pk kp hkp_rel, p2_toU8_bytesToBv8]
      conv => arg 4; rw [hikBPk_eq]
      have harm5 := p2_mono_panic hpan
        (p2_v1_arm5_ok_hooks img ext spkKit kpkKit pkKit ikit hH s0 sf5 Q
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          pkBuf skBuf v_330 v_388 u_80 u_88 v90
          errTag w2 w3 w4 w5 w6 v_a8'' v_b8'' v_d0'' u_b90'
          inp ikBPk spkBPk kyberPubBytes opkPkBytes opkSkBytes
          opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          msgVerByte b_2c0 b_390 b_4f2 b_b98'
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
          gMe gPeer stk (pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗ Frame)
          hb hwell hikBPk_len hspkBPk_len hkyberPub_len hopkPk_len hopkSk_len hopkSk_eq
          herr_ne_ok herr_ne_pend hstk_alloc hstk_lt
          hF5 hsym5 hpc5 hrun5 hsp5 hsp_align hx19_5 (hx25_5.trans hx25_4) hx28_5 hvregs5
          (fun sf P_f _ hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
            hErrBob spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
              wOpk opkPkBytes opkSkBytes kp errTag w2 w3 w4 w5 w6 sf P_f
              hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
              hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
              hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc_none herr_ne_ok herr_ne_pend
              hpcf hrunf (by rw [htrf, htr5, htr4]) hspf hcsf hvregsf hinvf
              (Entails.trans hent
                (p2_arm5_err_payload_pull img s0 sp fp coroPtr outPtr msgPtr ctBufPtr
                  remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt
                  kyberStorePtr kpkKit.kpk_vt v_330 v_388 errTag w2 w3 w4 w5 w6
                  inp.hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
                  (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)))
                  (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)))
                  (pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk))
                  (ikit.identityAt idStorePtr stId)
                  gMe gPeer stk Frame))))
      dsimp only [p2Sub5Frame] at harm5 ⊢
      exact p2_sepWPp_weaken_eq harm5 (by sep_focus))
    -- Arm 4: `get_identity_key_pair` error
    (fun e s2 hkp_err _ hpc2 hrun2 hsp2 htr2
        hx19_2 hx21_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs2 hF2 hsym2 =>
      p2_mono_panic hpan
        (p2_v1_arm4_ok_hooks img ext spkKit kpkKit pkKit skit hH hskitOk s0 s2 Q
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90
          v_a8' v_b8' v_d0' u_b90
          inp spkBPk kyberPubBytes opkPkBytes opkSkBytes
          opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          msgVerByte b_2c0 b_390 b_4f2 b_b98
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
          e gMe gPeer stk Frame
          hb hwell hspkBPk_len hkyberPub_len hopkPk_len hopkSk_len hstk_alloc hstk_lt
          hF2 hsym2 hpc2 hrun2 hsp2 hsp_align
          hx19_2 hx21_2 hx23_2 hx24_2 (hx25_2.trans hx25_4) hx26_2 hx27_2 hx28_2 hx29_2 hvregs2
          (fun sf P_f _ hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
            hErrKp spkRec kpkRec wOpk e sf P_f
              hspk_rel hspk_ok hkpk_rel hkpk_ok hopk_rel hkp_err
              hpcf hrunf (by rw [htrf, htr2, htr4]) hspf hcsf hvregsf hinvf hent)))
  have hikBPk_eq : toU8 kp.identityKey.publicKey.bytes.toList = ikBPk := by
    rw [hkp_pk kp hkp_rel, p2_toU8_bytesToBv8]
  have hfs5 : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) s5 :=
    p2_fsAt_step_kp (.ok kp) hfs4 hst_s5 htr5
  have htr_s4_s5 : s4.trace <+: s5.trace := by
    rw [htr5]; exact List.prefix_append _ _
  have htr0_5 : s0.trace <+: s5.trace := htr0_4.trans htr_s4_s5
  have hx25_5' : s5.readReg64 .x25 = sp + 0x210#64 := hx25_5.trans hx25_4
  let pqBytes := initialStateValue F (p2BobSpqrParams drKey.pqrKey)
  conv => arg 4; rw [hikBPk_eq]
  refine p2_mono_pre
    (p2_sub5_to_sub6 img spkKit kpkKit pkKit ikit s0
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8'' v_b8'' v_d0'' u_b90'
      inp ikBPk spkBPk drKey pqBytes kyberPubBytes opkPkBytes opkSkBytes
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      msgVerByte b_2c0 b_390 b_4f2 b_b98'
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
      gMe gPeer stk Frame hkyberPub_len) ?_
  refine SepWPp.exists_elim fun localIkBoxPtr =>
    SepWPp.exists_elim fun remoteIkBoxPtr =>
    SepWPp.exists_elim fun rootKeyBoxPtr =>
    SepWPp.exists_elim fun baseKeyBoxPtr =>
    SepWPp.exists_elim fun ratchetPubBoxPtr =>
    SepWPp.exists_elim fun ratchetPrivBoxPtr =>
    SepWPp.exists_elim fun chainKeyBoxPtr =>
    SepWPp.exists_elim fun spqrCap =>
    SepWPp.exists_elim fun spqrBufPtr =>
    SepWPp.exists_elim fun pad_f4 =>
    SepWPp.exists_elim fun c0 =>
    SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 =>
    SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 =>
    SepWPp.exists_elim fun d0 =>
    SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 =>
    SepWPp.exists_elim fun u_650 =>
    SepWPp.exists_elim fun u_298 =>
    SepWPp.exists_elim fun u_2a0 =>
    SepWPp.exists_elim fun u_2a8 =>
    SepWPp.exists_elim fun u_3a0 =>
    SepWPp.exists_elim fun b_3ac =>
    SepWPp.exists_elim fun u_3b0 =>
    SepWPp.exists_elim fun u_3b8 =>
    SepWPp.exists_elim fun u_3c0 =>
    SepWPp.exists_elim fun u_3c8 =>
    SepWPp.exists_elim fun u_3d0 =>
    SepWPp.exists_elim fun u_3d8 => ?_
  refine SepWPp.pure_elim
    fun ⟨hloc_nz, hrem_nz, hroot_nz, halice_nz, hrat_pub, hrat_priv, hck_ptr⟩ => ?_
  have hspk_clamp : clampBv8List spkPrivBytes = bytesToBv8 inp.spkBSk :=
    (mkP2AcceptKeysInput_spkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes
      kyberPubBytes kyberPrivBytes opkSkBytes).symm
  refine stageP2_sub6_v1_kits_ext img ext skit hH hskitOk hskitVt hPure
    inp ikBPk spkBPk stId s0 s5 (s0.readReg64 .x30) Q hpan
    sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr outPtr
    idStorePtr pkBuf skBuf ctBufPtr
    localIkBoxPtr remoteIkBoxPtr v_330 v_388 u_650
    u_298 u_2a0 u_80 u_88 v90 v_a8'' v_b8'' v_d0''
    u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
    (p2BobSessMid280V1 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2)
    (p2BobSessMid280V1_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    remoteRegId (opkOptTag32 (hdrOpkIdBv? inp.hdr)) opkIdWord kyberPreKeyId signedPreKeyId u_2a8
    msgVerByte b_4f2 b_390 b_3ac stk
    (p2Sub6Frame A img spkKit kpkKit pkKit s0 sp fp coroPtr outPtr msgPtr
      remoteAddrPtr localAddrPtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
      localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      inp ikBPk spkBPk drKey pqBytes opkPkBytes opkSkBytes b_2c0
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) gMe gPeer Frame)
    hb hwell hctBuf_nz hstk_sub56 hstk_lt
    hF5 hsym5 hpc5 hrun5 hsp5 hsp_align htr0_5 hvregs5
    (fun s3 htr3 hst3 => p2_envOk_id hfs5 hst3 htr3) hx19_5
    -- Substage 6 Ok (`+0x1778`) -> Normal exit into Stage P3
    (fun localRegId regIdFutPtr sf hreg_rel hst_sf hpcf hrunf hspf htrf
        hx8f hx9f hx10f hx11f hx19f hx20f hx22f hx23f hx24f hx25f hx26f hx27f hx28f hx29f
        hvregsf hFf hsymf =>
      p2_mono_pre
        (p2_v1_ok_entails img spkKit kpkKit pkKit skit hWF s0
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          regIdFutPtr pkBuf skBuf v_330 v_388
          localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
          ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          c0 c1 c2 c3 c4 d0 d1 d2
          inp ikBPk spkBPk drKey spkPrivBytes pqBytes opkPkBytes opkSkBytes
          pad_f4 opkIdWord kyberPreKeyId remoteRegId localRegId signedPreKeyId
          msgVerByte b_2c0
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
          gMe gPeer stk Frame
          hacc hwell hikBPk_len hspkBPk_len hspkPriv_len hspk_clamp
          hopkPk_len hopkSk_len hopkSk_eq
          hloc_nz hrem_nz hroot_nz halice_nz hrat_pub hrat_priv hck_ptr)
        (hOk spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
          wOpk opkPkBytes opkSkBytes kp drKey localRegId
          (mkBobGhostV1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
            (bytesToBv8 (Model.encodeEC ikBPk)) (bytesToBv8 (Model.encodeEC inp.hdr.ikAPk))
            (bytesToBv8 (Model.encodeEC inp.hdr.ekAPk))
            (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              (bytesToBv8 (Model.encodeEC spkBPk)) (bytesToBv8 inp.spkBSk))
            remoteRegId localRegId)
          sf
          hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
          hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
          hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc hreg_rel
          rfl rfl rfl rfl
          (hst_s4.trans (hst_s5.trans hst_sf))
          (p2_fsAt_step_regId (.ok localRegId) hfs5 hst_sf htrf)
          hpcf hrunf hspf (by rw [htrf, htr5, htr4])
          hx8f hx9f hx10f hx11f hx19f hx20f hx22f hx23f hx24f
          (hx25f.trans hx25_5') hx26f hx27f (hx28f.trans hx28_5) (hx29f.trans hx29_5)
          hvregsf hFf hsymf))
    -- Arm 6: `get_local_registration_id` error (`+0x09f4 -> s0.readReg64 .x30`)
    (fun e regIdFutPtr s6 hreg_err _ hpc6 hrun6 hsp6 htr6
        hx19_6 hx21_6 hx23_6 hx25_6 hx26_6 _ hx28_6 _ hvregs6 hF6 hsym6 =>
      p2_mono_panic hpan
        (p2_v1_arm6_ok_hooks img ext spkKit kpkKit pkKit skit hWF hH hPure.dropSessionStructure3
          hskitOk s0 s6 Q
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          regIdFutPtr pkBuf skBuf v_330 v_388
          localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
          ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          c0 c1 c2 c3 c4 d0 d1 d2
          u_298 u_2a0 u_80 u_88 v90 v_a8'' v_b8'' v_d0''
          u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
          inp ikBPk spkBPk drKey spkPrivBytes pqBytes opkPkBytes opkSkBytes
          pad_f4 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId u_2a8
          msgVerByte b_2c0 b_390 b_4f2 b_3ac
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
          e gMe gPeer stk Frame
          hb hacc hwell hikBPk_len hspkBPk_len hspkPriv_len hspk_clamp
          hopkPk_len hopkSk_len hopkSk_eq
          hloc_nz hrem_nz hroot_nz halice_nz hrat_pub hrat_priv hck_ptr
          hstk_drop hstk_lt hF6 hsym6 hpc6 hrun6 hsp6 hsp_align
          hx19_6 hx21_6 hx23_6 (hx25_6.trans hx25_5') hx26_6 (hx28_6.trans hx28_5) hvregs6
          (fun sf P_f _ hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
            hErrRegId spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
              wOpk opkPkBytes opkSkBytes kp drKey e sf P_f
              hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
              hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
              hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc hreg_err
              hpcf hrunf (by rw [htrf, htr6, htr5, htr4]) hspf hcsf hvregsf hinvf hent)))

abbrev stageP2V1KitsAtProp (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (img : Obj.Image) (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A img.base} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (stk : Nat) : Prop :=
  ∀ (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (_hpan : ∀ sf Pf, ResponderClosure.PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (_hb : img.base &&& 0xfff#64 = 0#64) (_hctBuf_nz : ctBufPtr ≠ 0#64)
    (_hpqr_ne : sp - 576#64 ≠ 0#64) (_hstk_lt : stk ≤ sp.toNat)
    (_hikBSk_len : ikBSk.length = 32) (hikBPk_len : ikBPk.length = 32)
    (hikAPk_len : hdr.ikAPk.length = 32) (_hekAPk_len : hdr.ekAPk.length = 32)
    (_hkemCt_len : hdr.kemCt.length = 1568)
    (_hF : img.FrozenLoaded s) (_hsym : s.symtab = img.symtab)
    (_hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) s)
    (_hid_spk : spkKit.idOk signedPreKeyId)
    (_hspk_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) →
      spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
        spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (_hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (_hkpk_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (_hopk_word : ∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → opkIdWord = id)
    (_hid_pk : ∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → pkKit.getIdOk id)
    (_hpk_wf : ∀ (id : BitVec 32) (r : PreKeyRecord), hdrOpkIdBv? hdr = some id →
      pkKit.getRel stPk id (.ok r) → pkKit.RecOk r →
      ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
        opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
        r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes)
    (_hkp_sk : ∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.privateKey.bytes.toList = bytesToBv8 ikBSk)
    (_hkp_pk : ∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk)
    (_hneq : bytesToBv8 ikBPk ≠ bytesToBv8 hdr.ikAPk ∨
      DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes)
    (_hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (_hrun : s.status = .Running) (_hsp_eq : s.sp = sp)
    (_hsp_align : (sp &&& 15#64 == 0#64) = true)
    (_htr : s0.trace <+: s.trace) (_hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (_hx8 : s.readReg64 .x8 = kyberStorePtr) (_hx9 : s.readReg64 .x9 = msgPtr)
    (_hx10 : s.readReg64 .x10 = kpkKit.kpk_vt) (_hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (_hx12 : s.readReg64 .x12 = remoteAddrPtr) (_hx13 : s.readReg64 .x13 = pkKit.pk_vt)
    (_hx14 : s.readReg64 .x14 = localAddrPtr) (_hx15 : s.readReg64 .x15 = idStorePtr)
    (_hx16 : s.readReg64 .x16 = ikit.id_vt) (_hx19 : s.readReg64 .x19 = coroPtr)
    (_hx22 : s.readReg64 .x22 = spkStorePtr) (_hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (_hx24 : s.readReg64 .x24 = spkKit.spk_vt) (_hx29 : s.readReg64 .x29 = fp)
    (_hErrSpk : ∀ (e : spkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt spkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
        kpkKit.storeAt kyberStorePtr stKpk ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (_hErrKpk : ∀ (spkRec : SignedPreKeyRecord) (e : kpkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt kpkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (_hErrPk : ∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
        (opkId : BitVec 32) (e : pkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      hdrOpkIdBv? hdr = some opkId → pkKit.getRel stPk opkId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ pkKit.getEvs opkId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt pkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (_hErrKp : ∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (e : skit.KpErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      skit.kpRel stId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt skit.kpErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (_hErrBob : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (errTag w2 w3 w4 w5 w6 : BitVec 64)
        (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      Model.acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = none →
      errTag ≠ 0xfffffffffffffffe#64 → errTag ≠ 0xfffffffffffffffd#64 →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
        pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (_hErrRegId : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (drKey : DRKey) (e : skit.RegIdErr)
        (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      Model.acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey →
      skit.regIdRel stId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) ++ skit.regIdEvs (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt skit.regIdErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (_hOk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (drKey : DRKey) (localRegId : BitVec 32)
        (G_bob : SessionGhost) (sf : State),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      (hspkPub_len : spkPubBytes.length = 32) → (hspkPriv_len : spkPrivBytes.length = 32) →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      Model.acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey →
      skit.regIdRel stId (.ok localRegId) →
      G_bob.pending = none → G_bob.kyber = none →
      G_bob.alice.bytes = bytesToBv8 (Model.encodeEC hdr.ekAPk) →
      G_bob.regIds = unpack32 remoteRegId ++ unpack32 localRegId →
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
        (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) sf →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1778#64 →
      sf.status = .Running → sf.sp = sp →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) ++ skit.regIdEvs (.ok localRegId) →
      sf.readReg64 .x8 = coroPtr + 0xe0#64 → sf.readReg64 .x9 = 8#64 →
      sf.readReg64 .x10 = msgVerByte.zeroExtend 64 → sf.readReg64 .x11 = coroPtr + 0xf8#64 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x20 = 0xfffffffffffffffe#64 →
      sf.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 →
      sf.readReg64 .x23 = (opkOptTag32 (hdrOpkIdBv? hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32) →
      sf.readReg64 .x24 = (opkOptTag32 (hdrOpkIdBv? hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32) →
      sf.readReg64 .x25 = sp + 0x210#64 → sf.readReg64 .x26 = v_330 →
      sf.readReg64 .x27 = sp + 0x370#64 → sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
        (p2OkPostAt A img spkKit kpkKit pkKit ikit s0
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
          G_bob
          (p2BobInitSessionV1 ikBPk (toU8 spkPubBytes)
            (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
              kyberPubBytes kyberPrivBytes opkSkBytes)
            drKey (initialStateValue F (p2BobSpqrParams drKey.pqrKey))
            hikBPk_len hikAPk_len
            (by simp [toU8, hspkPub_len])
            (by simp [mkP2AcceptKeysInput, toU8, clampBv8List_length hspkPriv_len]))
          hdr msgVerByte b_2c0 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk)
          stId gMe gPeer stk Frame)
        Q Qp),
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP2PreAt A img spkKit kpkKit pkKit ikit s0
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
        hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        stSpk stKpk stPk stId gMe gPeer stk Frame)
      Q Qp

/-- Fresh-session Stage P2 (`+0x0868 → +0x1778` and error exits) under `AllocContracts`. -/
theorem stageP2_v1_kits {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hA : AllocContracts img.base A ext)
    (hPure : StageP2PureCallees P A F img ext)
    (hInitBobErrOwned :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
        (initializeBobSessionErrOwnedSpec P A img))
    (ikit : IdentityStoreSpec A img.base) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesOk img ikit skit)
    (hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (hspkVt : SignedPreKeyVtablesOk img spkKit)
    (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hkpkVt : KyberPreKeyVtablesOk img kpkKit)
    (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (pkKit : PreKeyStoreSpec A img.base)
    (hpkVt : PreKeyVtablesOk img pkKit)
    (hpkOk : PreKeyStoreKitOkImgE img pkKit ext)
    (stk : Nat) (hstk : stageP2V1CallStack spkKit kpkKit pkKit skit ≤ stk) :
    stageP2V1KitsAtProp P A F img ext skit spkKit kpkKit pkKit stk :=
  stageP2_v1_kits_at img ext himg hWF
    (StageP2ClosureHooks.of_allocContracts hA) hPure.to_4K
    (isSameAccountDistinctSpec_to_at hPure.isSameAccount)
    hInitBobErrOwned hPure.initializeBobV1
    p2_isSameAccount_le_bobV1 p2_stageP2bStack_le_bobV1
    ikit skit hskitVt hskitOk spkKit hspkVt hspkOk kpkKit hkpkVt hkpkOk pkKit hpkVt hpkOk
    (p2_callStack_le_v1CallStack spkKit kpkKit pkKit skit)
    (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit)
    stk hstk

/-- Fresh-session Stage P2 (`+0x0868 → +0x1778` and error exits) under 4K/`Ext`
`StageP2ClosureHooks`. -/
theorem stageP2_v1_kits_ext {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : StageP2ClosureHooks A img.base ext)
    (hPure : StageP2PureCallees4K P A F img ext)
    (hInitBobErrOwned :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
        (initializeBobSessionErrOwned4KSpec P A img))
    (ikit : IdentityStoreSpec A img.base) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesOk img ikit skit)
    (hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (hspkVt : SignedPreKeyVtablesOk img spkKit)
    (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hkpkVt : KyberPreKeyVtablesOk img kpkKit)
    (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (pkKit : PreKeyStoreSpec A img.base)
    (hpkVt : PreKeyVtablesOk img pkKit)
    (hpkOk : PreKeyStoreKitOkImgE img pkKit ext)
    (stk : Nat) (hstk : stageP2V1CallStack4K spkKit kpkKit pkKit skit ≤ stk) :
    stageP2V1KitsAtProp P A F img ext skit spkKit kpkKit pkKit stk :=
  stageP2_v1_kits_at img ext himg hWF hH hPure
    (isSameAccountDistinctSpecExt_to_at hPure.isSameAccount)
    hInitBobErrOwned hPure.initializeBobV1
    p2_isSameAccountExt_le_bobExt p2_bobErr4K_le_bobExt
    ikit skit hskitVt hskitOk spkKit hspkVt hspkOk kpkKit hkpkVt hkpkOk pkKit hpkVt hpkOk
    (Nat.le_trans (p2_callStack_le_4K spkKit kpkKit pkKit skit)
      (p2_callStack4K_le_v1CallStack4K spkKit kpkKit pkKit skit))
    (p2_bobStack4K_le_v1CallStack4K spkKit kpkKit pkKit skit)
    stk hstk

abbrev stageP2_v1_kits_4k := @stageP2_v1_kits_ext

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
