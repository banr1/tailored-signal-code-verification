/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Bridge
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5Defs

/-!
# Stage P2 Exit Arm Bridges

Spatial entailments into `p2ErrFrameAt` for Error Arms 1–3 (`p2_v1_arm1_entails`..`arm3`), full
`SepWPp` exit bridges for Error Arms 4–5 (`p2_v1_arm4_ok`, `p2_v1_arm5_ok`), and re-exports of Arm
6 and normal-exit bridges from `StageP2Arms2`.
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

theorem p2_sp3b0_8_40_eq_48 (sp : BitVec 64) :
    memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3b8#64) 40 =
      memRegion (sp + 0x3b0#64) 48 :=
  (ProofLib.memRegion_split' (b := sp + 0x3b0#64) (n := 8) (k := 40)
    (b' := sp + 0x3b8#64) rfl (by bv_omega) (by decide)).symm

/-- Frame held constant across `stageP2_sub1_to_4_kits` (`+0x0868 -> +0x36ac` and Arms 1–3). -/
def p2Sub1To4Frame (A : RustAlloc) {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
     v_330 v_388 u_80 u_88 : BitVec 64)
    (stId : ikit.IdState) (hdr : HandshakeHdr) (msgVerByte : BitVec 8)
    (remoteRegId : BitVec 32) (gMe gPeer : AddrGhost) (Frame : SepProp) : SepProp :=
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  memRegion (coroPtr + 0x298#64) 20 ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  memRegion (coroPtr + 0x508#64) 328 ∗
  memRegion (coroPtr + 0x650#64) 8 ∗
  memRegion (coroPtr + 0x658#64) 298 ∗
  memRegion (coroPtr + 0x788#64) 16 ∗
  memRegion (coroPtr + 0x798#64) 64 ∗
  ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
  ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
  ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 hdr.ikAPk) ∗
  ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
  (ctBufPtr ↦ₛ (8#8 :: bytesToBv8 hdr.kemCt)) ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  ((sp + 0x80#64) ↦₆₄ u_80) ∗
  ((sp + 0x88#64) ↦₆₄ u_88) ∗
  memRegion (sp + 0x3a0#64) 8 ∗
  memRegion (sp + 0x3ac#64) 1 ∗
  memRegion (sp + 0x3b8#64) 40 ∗
  cells (sp + 0x560#64) 4 ∗
  cells (sp + 0x6a0#64) 4 ∗
  cells (sp + 0x7e0#64) 4 ∗
  memRegion (sp + 0xad1#64) 223 ∗
  memRegion (fp + 0xffffffffffffff80#64) 9 ∗
  Frame

/-- Arm 1 (`get_signed_pre_key` error) spatial bridge into `p2ErrFrameAt`. -/
theorem p2_v1_arm1_entails {A : RustAlloc} (img : Obj.Image)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_b0 v_330 v_388 u_488 u_80 u_88 spkFutPtr : BitVec 64)
    (b_4b0 msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (hdr : HandshakeHdr)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (e : spkKit.GetErr) (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    speErrAt spkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
      kpkKit.storeAt kyberStorePtr stKpk ∗
      pkKit.storeAt preKeyStorePtr stPk ∗
      memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
      ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
      cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
      ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
      memRegion (coroPtr + 0x4b1#64) 64 ∗
      ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
      ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
      ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
      ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
      ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
      ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
      ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
      ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
      memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
      memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      logOff img ∗ A.pool ∗ stackAt sp stk ∗
      p2Sub1To4Frame A ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
        v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame ⊢
    speErrAt spkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
      kpkKit.storeAt kyberStorePtr stKpk ∗
      pkKit.storeAt preKeyStorePtr stPk ∗
      ikit.identityAt idStorePtr stId ∗
      p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
        v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk Frame := by
  dsimp only [p2Sub1To4Frame, p2ErrFrameAt, p2CoroScratchTailAt, p2MsgFieldsAt]
  refine p2_entails_frame_v1 (Entails.of_eq (p2_coro398_cells8_4_eq_96 coroPtr)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (pointsTo64_entails_memRegion (coroPtr + 0x488#64) u_488)
    (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro4b0_byte_64_entails_65 coroPtr b_4b0) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro4f8_words2_328_entails_344 coroPtr spkFutPtr (img.base + spkKit.getFutVtOff))
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 u_88 (spkKit.getErr.w5 e) (coroPtr + 0x398#64)
      (coroPtr + 0x4f2#64) (spkKit.getErr.w4 e) v_b0 (spkKit.getErr.w2 e) ctxPtr outPtr
      (spkKit.getErr.w3 e)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_8_40_eq_48 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err123_to_288 sp)) (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-- Arm 2 (`get_kyber_pre_key` error) spatial bridge into `p2ErrFrameAt`. -/
theorem p2_v1_arm2_entails {A : RustAlloc} (img : Obj.Image)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_b0 v_330 v_388 u_488 u_80 u_88 kyberFutPtr : BitVec 64)
    (b_4b0 msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (hdr : HandshakeHdr) (spkRec : SignedPreKeyRecord)
    (spkPubBytes spkPrivBytes : List (BitVec 8))
    (hpub : spkPubBytes.length = 32) (hpriv : spkPrivBytes.length = 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (e : kpkKit.GetErr) (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    speErrAt kpkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
      kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
      pkKit.storeAt preKeyStorePtr stPk ∗
      memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
      ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
      ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
      ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
      cells (coroPtr + 0x3d8#64) 4 ∗
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
      ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
      memRegion (coroPtr + 0x4b1#64) 64 ∗
      ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
      ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
      ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
      ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
      ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
      ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
      ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
      ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
      memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
      memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      logOff img ∗ A.pool ∗ stackAt sp stk ∗
      p2Sub1To4Frame A ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
        v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame ⊢
    speErrAt kpkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
      kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
      pkKit.storeAt preKeyStorePtr stPk ∗
      ikit.identityAt idStorePtr stId ∗
      p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
        v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk Frame := by
  dsimp only [p2Sub1To4Frame, p2ErrFrameAt, p2CoroScratchTailAt, p2MsgFieldsAt]
  refine p2_entails_frame_v1
    (p2_coro398_bytes_cells4_entails_96 coroPtr spkPubBytes (clampBv8List spkPrivBytes)
      hpub (clampBv8List_length hpriv)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (pointsTo64_entails_memRegion (coroPtr + 0x488#64) u_488)
    (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro4b0_byte_64_entails_65 coroPtr b_4b0) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro4f8_words2_328_entails_344 coroPtr kyberFutPtr (img.base + kpkKit.getFutVtOff))
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 u_88 (kpkKit.getErr.w5 e) (coroPtr + 0x398#64)
      (coroPtr + 0x4f2#64) (kpkKit.getErr.w4 e) v_b0 (kpkKit.getErr.w2 e) ctxPtr outPtr
      (kpkKit.getErr.w3 e)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_8_40_eq_48 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err123_to_288 sp)) (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-- Arm 3 (`get_pre_key` error) spatial bridge into `p2ErrFrameAt`. -/
theorem p2_v1_arm3_entails {A : RustAlloc} (img : Obj.Image)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_b0 v_330 v_388 u_80 u_88 pkBuf skBuf opkFutPtr v90 : BitVec 64)
    (b_4b0 msgVerByte : BitVec 8)
    (opkId opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (hdr : HandshakeHdr) (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
    (spkPubBytes spkPrivBytes : List (BitVec 8))
    (hpub : spkPubBytes.length = 32) (hpriv : spkPrivBytes.length = 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (e : pkKit.GetErr) (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    speErrAt pkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
      kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
      pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
      memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
      ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
      ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
      ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
      ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
      ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
      ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
      memRegion (coroPtr + 0x4b1#64) 64 ∗
      ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
      ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
      ((coroPtr + 0x500#64) ↦₆₄ (img.base + pkKit.getFutVtOff)) ∗
      ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
      ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
      ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ pkKit.getErr.w4 e) ∗
      ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ pkKit.getErr.w2 e) ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
      ((sp + 0xd0#64) ↦₆₄ pkKit.getErr.w3 e) ∗
      memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
      memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      logOff img ∗ A.pool ∗ stackAt sp stk ∗
      p2Sub1To4Frame A ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
        v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame ⊢
    speErrAt pkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
      kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
      pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
      ikit.identityAt idStorePtr stId ∗
      p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
        v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk Frame := by
  dsimp only [p2Sub1To4Frame, p2ErrFrameAt, p2CoroScratchTailAt, p2MsgFieldsAt]
  refine p2_entails_frame_v1
    (p2_coro398_bytes_words4_entails_96 coroPtr spkPubBytes (clampBv8List spkPrivBytes)
      pkBuf 0x620#64 skBuf 0xc60#64 hpub (clampBv8List_length hpriv)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (pointsTo64_entails_memRegion (coroPtr + 0x488#64) (msgPtr + 0x90#64))
    (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro4b0_byte_64_entails_65 coroPtr b_4b0) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro4f8_words2_328_entails_344 coroPtr opkFutPtr (img.base + pkKit.getFutVtOff))
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 u_88 v90 (coroPtr + 0x398#64)
      (coroPtr + 0x4f2#64) (pkKit.getErr.w4 e) v_b0 (pkKit.getErr.w2 e) ctxPtr outPtr
      (pkKit.getErr.w3 e)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_8_40_eq_48 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err123_to_288 sp)) (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem p2_head56_mid280V1_zero_eq_regIds (p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    p2BobSessHead56Bv8 p1 p2 ++
        (p2BobSessMid280V1 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
          unpack64 0#64) =
      p2BobSessRegIdsV1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 0#32 0#32 := by
  rw [← p2BobSession344Bv8V1_eq_head56_mid280V1, p2BobSession344Bv8V1_eq_regIds_zero]

/-- Frame held constant across `stageP2_sub5_v1_kits` (`+0x36ac -> +0x125c` and Arms 4–5). -/
def p2Sub5Frame (A : RustAlloc) (img : Obj.Image)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (s0 : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90 : BitVec 64)
    (kyberPubBytes : List (BitVec 8))
    (hdr : HandshakeHdr) (msgVerByte b_2c0 b_390 b_4f2 : BitVec 8)
    (kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState)
    (Frame : SepProp) : SepProp :=
  spkKit.storeAt spkStorePtr stSpk' ∗
  kpkKit.storeAt kyberStorePtr stKpk' ∗
  pkKit.storeAt preKeyStorePtr stPk' ∗
  (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
  A.live skBuf 3168 1 ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
  memRegion (coroPtr + 0x100#64) 336 ∗
  cells (coroPtr + 0x250#64) 6 ∗
  memRegion (coroPtr + 0x298#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ b_390) ∗
  ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
  ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
  ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
  ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
  memRegion (coroPtr + 0x508#64) 328 ∗
  memRegion (coroPtr + 0x650#64) 8 ∗
  memRegion (coroPtr + 0x788#64) 16 ∗
  ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
  ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗
  ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
  ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
  ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
  ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
  ((sp + 0x80#64) ↦₆₄ u_80) ∗
  ((sp + 0x88#64) ↦₆₄ u_88) ∗
  ((sp + 0x90#64) ↦₆₄ v90) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  memRegion (sp + 0x270#64) 9 ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3a0#64) 8 ∗
  memRegion (sp + 0x3ac#64) 1 ∗
  memRegion (sp + 0x3b0#64) 8 ∗
  memRegion (sp + 0x3b8#64) 8 ∗
  memRegion (sp + 0x3c0#64) 8 ∗
  memRegion (sp + 0x3cf#64) 1 ∗
  memRegion (sp + 0x3d0#64) 8 ∗
  memRegion (sp + 0x3d8#64) 8 ∗
  memRegion (sp + 0x538#64) 24 ∗
  memRegion (sp + 0xad0#64) 1 ∗
  memRegion (sp + 0xad1#64) 223 ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  memRegion outPtr 48 ∗
  Frame

theorem p2_stack_split_alloc (sp : BitVec 64) (stk : Nat)
    (h1 : allocHookStack ≤ stk) (h2 : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      stackAt sp allocHookStack ∗
      memRegion (sp - BitVec.ofNat 64 stk) (stk - allocHookStack) := by
  dsimp only [stackAt]
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 stk) (stk - allocHookStack) allocHookStack
    (by omega)
  have haddr : sp - BitVec.ofNat 64 stk + BitVec.ofNat 64 (stk - allocHookStack) =
      sp - BitVec.ofNat 64 allocHookStack := by bv_omega
  have hsum : stk - allocHookStack + allocHookStack = stk := Nat.sub_add_cancel h1
  rw [haddr, hsum] at hsplit
  rw [hsplit, sepConj_comm]

theorem p2_stack_split_dropSs3 (sp : BitVec 64) (stk : Nat)
    (h1 : dropSessionStructureLocal2Stack ≤ stk) (h2 : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      stackAt sp dropSessionStructureLocal2Stack ∗
      memRegion (sp - BitVec.ofNat 64 stk) (stk - dropSessionStructureLocal2Stack) := by
  dsimp only [stackAt]
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 stk)
    (stk - dropSessionStructureLocal2Stack) dropSessionStructureLocal2Stack (by omega)
  have haddr : sp - BitVec.ofNat 64 stk + BitVec.ofNat 64 (stk - dropSessionStructureLocal2Stack) =
      sp - BitVec.ofNat 64 dropSessionStructureLocal2Stack := by bv_omega
  have hsum : stk - dropSessionStructureLocal2Stack + dropSessionStructureLocal2Stack = stk :=
    Nat.sub_add_cancel h1
  rw [haddr, hsum] at hsplit
  rw [hsplit, sepConj_comm]

set_option maxHeartbeats 800000 in
/-- Arm 4 (`+0x07bc -> s0.readReg64 .x30`) full `SepWPp` exit bridge into `p2ErrFrameAt`
under `StageP2ClosureHooks`. -/
theorem p2_v1_arm4_ok_hooks {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base)
    {ikit : IdentityStoreSpec A img.base} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooks A img.base ext)
    (hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
    (s0 s2 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90
     v_a8 v_b8 v_d0 u_b90 : BitVec 64)
    (inp : AcceptKeysInput) (spkBPk : SignalPqxdh.Bytes)
    (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 b_b98 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (e : skit.KpErr) (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hwell : WellSizedAcceptKeysInput inp)
    (hspkBPk_len : spkBPk.length = 32)
    (hkyberPub_len : kyberPubBytes.length = 1568)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hstk_alloc : allocHookStack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hF : img.FrozenLoaded s2) (hsym : s2.symtab = img.symtab)
    (hpc : s2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x7bc#64)
    (hrun : s2.status = .Running) (hsp : s2.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s2.readReg64 .x19 = coroPtr)
    (hx21 : s2.readReg64 .x21 = coroPtr + 0x390#64)
    (hx23 : s2.readReg64 .x23 = coroPtr + 0x4f2#64)
    (hx24 : s2.readReg64 .x24 = sp + 0x370#64)
    (hx25 : s2.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s2.readReg64 .x26 = coroPtr + 0x398#64)
    (hx27 : s2.readReg64 .x27 = ctxPtr)
    (hx28 : s2.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s2.readReg64 .x29 = fp)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hCont : ∀ (sf : State) (P_f : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s2 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s2.trace → sf.sp = sp + 0xcd0#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      ImgCallInv img sf →
      (P_f ⊢
        speErrAt skit.kpErr outPtr e ∗
        spkKit.storeAt spkStorePtr stSpk' ∗
        kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 inp.hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2
      (kpPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       memRegion (sp + 0x428#64) 272 ∗
       A.live idKpFutPtr skit.kpBoxSize 8 ∗
       skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗
       ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + skit.kpFutVtOff)) ∗
       ((img.base + skit.kpFutVtOff) ↦₆₄ᵣ (img.base + skit.kpFutDropOff)) ∗
       ((img.base + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
       ((img.base + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
       ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
       ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       memRegion (coroPtr + 0x658#64) 298 ∗ memRegion (coroPtr + 0x798#64) 64 ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
       ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
       ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       (skBuf ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
       ((skBuf + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
       (ctBufPtr ↦₈ 8#8) ∗
       ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
       ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
       memRegion (sp + 0x3c8#64) 7 ∗
       cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
       cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ∗
       logOff img ∗ A.pool ∗ stackAt sp stk ∗
       p2Sub5Frame A img spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
         remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
         pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
          msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
          stSpk' stKpk' stPk' Frame)
      Q (ResponderClosure.PanicOomProp s0) := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hpqsk_len : (bytesToBv8 inp.pqspkBSk).length = 3168 := by
    simp [bytesToBv8, hwell.2.2.2.2.2.1]
  have hkem_len : 0 < (bytesToBv8 inp.hdr.kemCt).length := by
    simp [bytesToBv8, hwell.2.2.2.2.2.2.2.2.2]
  dsimp only [p2Sub5Frame]
  refine SepWPp.weaken_frame
    (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (p2_pqsk_split_rejoin skBuf (bytesToBv8 inp.pqspkBSk) (by omega)))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_pointsToBytes_entails_memRegion skBuf (bytesToBv8 inp.pqspkBSk) 3168 hpqsk_len)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_cells8_a90_to_cells6_2 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_stack_split_alloc sp stk hstk_alloc hstk64))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_eq coroPtr))
    (by sep_focus) ?_
  have hif0 : (if (0#64 : BitVec 64) = 0 then emp
      else A.live 8#64 ((0#64 : BitVec 64).toNat * 24) 8 ∗
           memRegion 8#64 ((0#64 : BitVec 64).toNat * 24)) = emp := by simp
  have harm4 := p2_arm4_err_hooks_ok (Qp := fun _ _ => False) hH hskitOk s0 s2
    sp coroPtr msgPtr ctxPtr outPtr 0#64 8#64
    idStorePtr idKpFutPtr pkBuf skBuf fp
    (coroPtr + 0x390#64) (coroPtr + 0x398#64) (coroPtr + 0x4f2#64)
    v_a8 (coroPtr + 0x390#64) v_b8 ctxPtr v_d0 u_b90
    opkIdWord b_2c0 b_390 b_4f2 b_b98 e
    hb (by decide) ⟨hF, hsym⟩ hsp hpc hrun (hsp ▸ hsp_align)
    hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs
  rw [hif0] at harm4
  refine p2_finish_err_arm_drop
    (Drop := ((img.base + skit.kpFutVtOff) ↦₆₄ᵣ (img.base + skit.kpFutDropOff)) ∗
             ((img.base + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
             ((img.base + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64))
    harm4 (by sep_focus) ?_
    (fun sf P_f hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hinvf⟩ =>
      hCont sf P_f hst hpcf hrunf htrf hspf hcsf hvregsf hinvf hent)
  dsimp only [p2ErrFrameAt, p2CoroScratchTailAt, p2MsgFieldsAt]
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_stack_split_alloc sp stk hstk_alloc hstk64).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3e0_arm4_to_368 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_48_split_8_40 sp).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err45_to_288 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 u_88 v90 (coroPtr + 0x398#64)
      (coroPtr + 0x4f2#64) (skit.kpErr.w4 e) (coroPtr + 0x390#64) (skit.kpErr.w2 e)
      ctxPtr outPtr (skit.kpErr.w3 e)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro398_bytes_words4_entails_96 coroPtr (bytesToBv8 spkBPk) (bytesToBv8 inp.spkBSk)
      pkBuf 0x620#64 skBuf 0xc60#64
      (by simp [bytesToBv8, hspkBPk_len]) (by simp [bytesToBv8, hwell.2.2.1]))
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (pointsTo64_entails_memRegion (coroPtr + 0x488#64) (msgPtr + 0x90#64)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro4b0_byte_bytes_entails_65 coroPtr (opkPresentTag inp.opkBSk?) opkPkBytes opkSkBytes
      hopkPk_len hopkSk_len) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro4f8_words2_328_entails_344 coroPtr idKpFutPtr (img.base + skit.kpFutVtOff))
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_ctBuf_split ctBufPtr (bytesToBv8 inp.hdr.kemCt) hkem_len).symm)
    (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev p2_v1_arm4_ok_ext := @p2_v1_arm4_ok_hooks
abbrev p2_v1_arm4_ok_4k := @p2_v1_arm4_ok_hooks

/-- Arm 4 (`+0x07bc -> s0.readReg64 .x30`) full `SepWPp` exit bridge into `p2ErrFrameAt`. -/
theorem p2_v1_arm4_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base)
    {ikit : IdentityStoreSpec A img.base} (skit : IdentitySelfStoreSpec ikit)
    (hA : AllocContracts img.base A ext) :
    IdentitySelfStoreKitOkI img ikit skit ext →
    ∀ (s0 s2 : State) (Q : State → SepProp → Prop)
      (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
       idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
       idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90
       v_a8 v_b8 v_d0 u_b90 : BitVec 64)
      (inp : AcceptKeysInput) (spkBPk : SignalPqxdh.Bytes)
      (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
      (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
      (msgVerByte b_2c0 b_390 b_4f2 b_b98 : BitVec 8)
      (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
      (e : skit.KpErr) (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp),
      img.base &&& 0xfff#64 = 0#64 →
      WellSizedAcceptKeysInput inp →
      spkBPk.length = 32 →
      kyberPubBytes.length = 1568 →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      allocHookStack ≤ stk → stk ≤ sp.toNat →
      img.FrozenLoaded s2 → s2.symtab = img.symtab →
      s2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x7bc#64 →
      s2.status = .Running → s2.sp = sp →
      (sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = coroPtr →
      s2.readReg64 .x21 = coroPtr + 0x390#64 →
      s2.readReg64 .x23 = coroPtr + 0x4f2#64 →
      s2.readReg64 .x24 = sp + 0x370#64 →
      s2.readReg64 .x25 = sp + 0x210#64 →
      s2.readReg64 .x26 = coroPtr + 0x398#64 →
      s2.readReg64 .x27 = ctxPtr →
      s2.readReg64 .x28 = sp + 0xa90#64 →
      s2.readReg64 .x29 = fp →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      (∀ (sf : State) (P_f : SepProp),
        Steps (tripleRatchetProgAtExt img.base ext) s2 sf →
        sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        sf.trace = s2.trace → sf.sp = sp + 0xcd0#64 →
        ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
        ImgCallInv img sf →
        (P_f ⊢
          speErrAt skit.kpErr outPtr e ∗
          spkKit.storeAt spkStorePtr stSpk' ∗
          kpkKit.storeAt kyberStorePtr stKpk' ∗
          pkKit.storeAt preKeyStorePtr stPk' ∗
          ikit.identityAt idStorePtr stId ∗
          p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
            v_330 v_388 inp.hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
            gMe gPeer stk Frame) →
        Q sf P_f) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2
        (kpPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
         memRegion (sp + 0x428#64) 272 ∗
         A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗
         ikit.identityAt idStorePtr stId ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (img.base + skit.kpFutVtOff)) ∗
         ((img.base + skit.kpFutVtOff) ↦₆₄ᵣ (img.base + skit.kpFutDropOff)) ∗
         ((img.base + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
         ((img.base + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
         memRegion (coroPtr + 0x658#64) 298 ∗ memRegion (coroPtr + 0x798#64) 64 ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
         ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         (skBuf ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
         ((skBuf + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
         (ctBufPtr ↦₈ 8#8) ∗
         ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
         ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
         protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
         ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
         ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
         ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
         memRegion (sp + 0x3c8#64) 7 ∗
         cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
         cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
         ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ∗
         logOff img ∗ A.pool ∗ stackAt sp stk ∗
         p2Sub5Frame A img spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
           remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
           pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
           msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
           stSpk' stKpk' stPk' Frame)
        Q (ResponderClosure.PanicOomProp s0) :=
  p2_v1_arm4_ok_hooks img ext spkKit kpkKit pkKit skit
    (StageP2ClosureHooks.of_allocContracts hA)

set_option maxHeartbeats 800000 in
/-- Arm 5 (`+0x125c -> s0.readReg64 .x30`) full `SepWPp` exit bridge into `p2ErrFrameAt`
under `StageP2ClosureHooks`. -/
theorem p2_v1_arm5_ok_hooks {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (hH : StageP2ClosureHooks A img.base ext)
    (s0 sf5 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90
     errTag w2 w3 w4 w5 w6 v_a8' v_b8' v_d0' u_b90' : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 b_b98' : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hkyberPub_len : kyberPubBytes.length = 1568)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (herr_ne_ok : errTag ≠ 0xfffffffffffffffe#64)
    (herr_ne_pend : errTag ≠ 0xfffffffffffffffd#64)
    (hstk_alloc : allocHookStack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hF : img.FrozenLoaded sf5) (hsym : sf5.symtab = img.symtab)
    (hpc : sf5.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x125c#64)
    (hrun : sf5.status = .Running) (hsp : sf5.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : sf5.readReg64 .x19 = coroPtr)
    (hx25 : sf5.readReg64 .x25 = sp + 0x210#64)
    (hx28 : sf5.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs sf5 = calleeSavedVRegs s0)
    (hCont : ∀ (sf : State) (P_f : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) sf5 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = sf5.trace → sf.sp = sp + 0xcd0#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      ImgCallInv img sf →
      (P_f ⊢
        speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
        spkKit.storeAt spkStorePtr stSpk' ∗
        kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 inp.hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf5
      (((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
       memRegion (sp + 0x418#64) 288 ∗
       bobParamsFieldsAt (coroPtr + 0x658#64) skBuf (msgPtr + 0x90#64) ctBufPtr
         (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
       ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       cells (coroPtr + 0x4f8#64) 2 ∗
       ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
       ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
       ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
       opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
       memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
       ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
       memRegion (sp + 0x3c8#64) 7 ∗ cells (sp + 0x560#64) 4 ∗
       cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
       cells (sp + 0xa90#64) 8 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗
       logOff img ∗ anyHeap ∗ A.pool ∗ stackAt sp stk ∗
       p2Sub5Frame A img spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
         remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
         pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
         msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
         stSpk' stKpk' stPk' Frame)
      Q (ResponderClosure.PanicOomProp s0) := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hkem_len : 0 < (bytesToBv8 inp.hdr.kemCt).length := by
    simp [bytesToBv8, hwell.2.2.2.2.2.2.2.2.2]
  refine p2_drop_frame_mid (Drop := anyHeap) (by sep_focus) ?_
  dsimp only [p2Sub5Frame]
  refine SepWPp.weaken_frame
    (p2_bobParamsFieldsAt_err_weaken coroPtr msgPtr skBuf ctBufPtr inp ikBPk spkBPk hwell)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_fp80_to_memRegion9 fp u_b90' b_b98') (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_cells8_a90_to_cells6_2 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_stack_split_alloc sp stk hstk_alloc hstk64))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_eq coroPtr))
    (by sep_focus) ?_
  have hif0 : (if (0#64 : BitVec 64) = 0 then emp
      else A.live 8#64 ((0#64 : BitVec 64).toNat * 24) 8 ∗
           memRegion 8#64 ((0#64 : BitVec 64).toNat * 24)) = emp := by simp
  have harm5 := p2_arm5_err_hooks_ok (Qp := fun _ _ => False) hH s0 sf5
    sp coroPtr outPtr 0#64 8#64 pkBuf skBuf
    errTag w2 w3 w4 w5 w6 u_88 v_a8' v_b8' v_d0'
    b_2c0 b_390 b_4f2 hb (by decide) herr_ne_pend herr_ne_ok
    ⟨hF, hsym⟩ hsp hpc hrun (hsp ▸ hsp_align)
    hx19 hx25 hx28 hvregs
  rw [hif0] at harm5
  refine p2_finish_err_arm_drop (Drop := emp) harm5 (by sep_focus) ?_
    (fun sf P_f hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hinvf⟩ =>
      hCont sf P_f hst hpcf hrunf htrf hspf hcsf hvregsf hinvf hent)
  rw [emp_sepConj]
  dsimp only [p2ErrFrameAt, p2CoroScratchTailAt, p2MsgFieldsAt]
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_stack_split_alloc sp stk hstk_alloc hstk64).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp3e0_arm5_to_368 sp errTag w2 w3 w4 w5 w6) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_48_split_8_40 sp).symm) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err45_to_288 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 errTag v90 (coroPtr + 0x398#64)
      (coroPtr + 0x4f2#64) w5 (coroPtr + 0x390#64) w3 ctxPtr outPtr w4) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro658_298_rejoin coroPtr msgPtr pkBuf skBuf inp ikBPk spkBPk opkPkBytes opkSkBytes
      hwell hikBPk_len hspkBPk_len hopkPk_len hopkSk_len hopkSk_eq) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro398_bytes_words4_entails_96 coroPtr (bytesToBv8 spkBPk) (bytesToBv8 inp.spkBSk)
      pkBuf 0x620#64 skBuf 0xc60#64
      (by simp [bytesToBv8, hspkBPk_len]) (by simp [bytesToBv8, hwell.2.2.1]))
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (pointsTo64_entails_memRegion (coroPtr + 0x488#64) (msgPtr + 0x90#64)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro4b0_byte_bytes_entails_65 coroPtr (opkPresentTag inp.opkBSk?) opkPkBytes opkSkBytes
      hopkPk_len hopkSk_len) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_coro4f8_2cells_328_eq_344 coroPtr)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_ctBuf_split ctBufPtr (bytesToBv8 inp.hdr.kemCt) hkem_len).symm)
    (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev p2_v1_arm5_ok_ext := @p2_v1_arm5_ok_hooks
abbrev p2_v1_arm5_ok_4k := @p2_v1_arm5_ok_hooks

/-- Arm 5 (`+0x125c -> s0.readReg64 .x30`) full `SepWPp` exit bridge into `p2ErrFrameAt`. -/
theorem p2_v1_arm5_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (hA : AllocContracts img.base A ext) :
    ∀ (s0 sf5 : State) (Q : State → SepProp → Prop)
      (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
       idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
       pkBuf skBuf v_330 v_388 u_80 u_88 v90
       errTag w2 w3 w4 w5 w6 v_a8' v_b8' v_d0' u_b90' : BitVec 64)
      (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
      (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
      (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
      (msgVerByte b_2c0 b_390 b_4f2 b_b98' : BitVec 8)
      (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
      (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp),
      img.base &&& 0xfff#64 = 0#64 →
      WellSizedAcceptKeysInput inp →
      ikBPk.length = 32 → spkBPk.length = 32 →
      kyberPubBytes.length = 1568 →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      (∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk) →
      errTag ≠ 0xfffffffffffffffe#64 →
      errTag ≠ 0xfffffffffffffffd#64 →
      allocHookStack ≤ stk → stk ≤ sp.toNat →
      img.FrozenLoaded sf5 → sf5.symtab = img.symtab →
      sf5.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x125c#64 →
      sf5.status = .Running → sf5.sp = sp →
      (sp &&& 15#64 == 0#64) = true →
      sf5.readReg64 .x19 = coroPtr →
      sf5.readReg64 .x25 = sp + 0x210#64 →
      sf5.readReg64 .x28 = sp + 0xa90#64 →
      calleeSavedVRegs sf5 = calleeSavedVRegs s0 →
      (∀ (sf : State) (P_f : SepProp),
        Steps (tripleRatchetProgAtExt img.base ext) sf5 sf →
        sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        sf.trace = sf5.trace → sf.sp = sp + 0xcd0#64 →
        ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
        ImgCallInv img sf →
        (P_f ⊢
          speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
          spkKit.storeAt spkStorePtr stSpk' ∗
          kpkKit.storeAt kyberStorePtr stKpk' ∗
          pkKit.storeAt preKeyStorePtr stPk' ∗
          ikit.identityAt idStorePtr stId ∗
          p2ErrFrameAt A img s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
            v_330 v_388 inp.hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
            gMe gPeer stk Frame) →
        Q sf P_f) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf5
        (((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
         speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
         memRegion (sp + 0x418#64) 288 ∗
         bobParamsFieldsAt (coroPtr + 0x658#64) skBuf (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
         ikit.identityAt idStorePtr stId ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         cells (coroPtr + 0x4f8#64) 2 ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
         opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
         memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
         ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
         ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
         ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
         memRegion (sp + 0x3c8#64) 7 ∗ cells (sp + 0x560#64) 4 ∗
         cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
         cells (sp + 0xa90#64) 8 ∗
         ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗
         logOff img ∗ anyHeap ∗ A.pool ∗ stackAt sp stk ∗
         p2Sub5Frame A img spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
           remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
           pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
           msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
           stSpk' stKpk' stPk' Frame)
        Q (ResponderClosure.PanicOomProp s0) :=
  p2_v1_arm5_ok_hooks img ext spkKit kpkKit pkKit ikit
    (StageP2ClosureHooks.of_allocContracts hA)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
