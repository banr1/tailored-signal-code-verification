/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Trans
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common -- shake: keep

/-!
# Inter-Substage Spatial Bridges for Over-Path Stage P2

Defines the populated-record Stage P2 entry precondition `stageP2OverPreAt` at `+0x0868` and proves
the spatial frame transitions between entry, Substages P2.1–P2.4, Substage P2.5, and Substage P2.6.
-/

@[expose] public section

set_option autoImplicit false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

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
open CryptoVerification.E2E.Pqxdh.Initiator hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)

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

/-! ## Entry Precondition and Inter-Substage Transitions -/

/-- Populated-record Stage P2 entry precondition at `+0x0868`, holding `prevSessionsEmptyAt` at
`coroPtr` and `sessionStateReprAt` at `coroPtr + 0xf8`. -/
def stageP2OverPreAt (A : RustAlloc) (img : Obj.Image)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp) : SepProp :=
  spkKit.storeAt spkStorePtr stSpk ∗
  kpkKit.storeAt kyberStorePtr stKpk ∗
  pkKit.storeAt preKeyStorePtr stPk ∗
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  prevSessionsEmptyAt A coroPtr g ∗
  sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
  cells (coroPtr + 0x250#64) 6 ∗
  memRegion (coroPtr + 0x298#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ b_390) ∗
  memRegion (coroPtr + 0x398#64) 96 ∗
  cells (coroPtr + 0x3f8#64) 6 ∗
  cells (coroPtr + 0x468#64) 4 ∗
  ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
  ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
  memRegion (coroPtr + 0x4b1#64) 64 ∗
  ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
  ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2MsgFieldsAt msgPtr ctBufPtr hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  ((sp + 0x80#64) ↦₆₄ u_80) ∗
  ((sp + 0x88#64) ↦₆₄ u_88) ∗
  ((sp + 0x90#64) ↦₆₄ u_90) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
  ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
  ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
  memRegion (sp + 0x270#64) 9 ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3a0#64) 8 ∗
  memRegion (sp + 0x3ac#64) 1 ∗
  memRegion (sp + 0x3b0#64) 48 ∗
  memRegion (sp + 0x3e0#64) 368 ∗
  cells (sp + 0x560#64) 4 ∗
  cells (sp + 0x6a0#64) 4 ∗
  cells (sp + 0x7e0#64) 4 ∗
  cells (sp + 0x930#64) 8 ∗
  memRegion (sp + 0xa90#64) 288 ∗
  memRegion (fp + 0xffffffffffffff80#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  memRegion outPtr 48 ∗
  logOff img ∗
  A.pool ∗
  stackAt sp stk ∗
  Frame

theorem p2_over_entry_to_sub1To4 {A : RustAlloc} (img : Obj.Image)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp) :
    stageP2OverPreAt A img spkKit kpkKit pkKit ikit s0
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame ⊢
    spkKit.storeAt spkStorePtr stSpk ∗
      kpkKit.storeAt kyberStorePtr stKpk ∗
      pkKit.storeAt preKeyStorePtr stPk ∗
      prevSessionsEmptyAt A coroPtr g ∗
      sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗ cells (coroPtr + 0x250#64) 6 ∗
      ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
      cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
      cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
      ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
      memRegion (coroPtr + 0x4b1#64) 64 ∗
      ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
      cells (coroPtr + 0x4f8#64) 2 ∗
      ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
      ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
      ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
      ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
      memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
      memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 65 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp stk ∗
      p2Sub1To4Frame A ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
        v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame := by
  dsimp only [stageP2OverPreAt, p2Sub1To4Frame, p2CoroScratchTailAt, p2MsgFieldsAt]
  rw [← p2_coro398_cells8_4_eq_96 coroPtr,
      ← p2_coro4f8_2cells_328_eq_344 coroPtr,
      ← p2_sp3b0_8_40_eq_48 sp,
      p2_memRegion_a90_288_split_65_223 sp]
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem p2_over_sub4_to_sub5 {A : RustAlloc} (img : Obj.Image)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base)
    {ikit : IdentityStoreSpec A img.base} (skit : IdentitySelfStoreSpec ikit)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0' : BitVec 64)
    (inp : AcceptKeysInput) (hdr : HandshakeHdr) (spkBPk : SignalPqxdh.Bytes)
    (spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp)
    (hhdr : inp.hdr = hdr)
    (hspk_pub : bytesToBv8 spkBPk = spkPubBytes)
    (hspk_priv : bytesToBv8 inp.spkBSk = clampBv8List spkPrivBytes)
    (hpq_priv : bytesToBv8 inp.pqspkBSk = kyberPrivBytes)
    (hopk_tag : opkPresentTag inp.opkBSk? = opkOptTag8 (hdrOpkIdBv? hdr))
    (hkyber_priv_len : kyberPrivBytes.length = 3168)
    (hkem_len : 0 < (bytesToBv8 hdr.kemCt).length) :
    spkKit.storeAt spkStorePtr stSpk' ∗
      kpkKit.storeAt kyberStorePtr stKpk' ∗
      pkKit.storeAt preKeyStorePtr stPk' ∗
      A.live idKpFutPtr skit.kpBoxSize 8 ∗ skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
      (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
      (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
      prevSessionsEmptyAt A coroPtr g ∗
      sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗ cells (coroPtr + 0x250#64) 6 ∗
      ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
      ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
      ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
      ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
      ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
      ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
      ((coroPtr + 0x4b0#64) ↦₈ opkOptTag8 (hdrOpkIdBv? hdr)) ∗
      ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
      ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
      cells (coroPtr + 0x4f8#64) 2 ∗
      ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
      ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
      ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8') ∗
      ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8') ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
      ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
      memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
      memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 65 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp stk ∗
      p2Sub1To4Frame A ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
        v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame ⊢
    ∃∗ u_b90 : BitVec 64, ∃∗ b_b98 : BitVec 8,
      A.live idKpFutPtr skit.kpBoxSize 8 ∗
      skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
      ikit.identityAt idStorePtr stId ∗
      ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
      ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
      ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
      ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
      ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
      ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
      ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
      cells (coroPtr + 0x4f8#64) 2 ∗
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
      ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
      memRegion (sp + 0x3c8#64) 7 ∗ memRegion (sp + 0x3e0#64) 344 ∗
      cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
      cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
      ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ∗
      logOff img ∗ A.pool ∗ stackAt sp stk ∗
      p2OverSub5Frame A img spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
        remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
        msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
        stSpk' stKpk' stPk' g recG sess Frame := by
  rw [← hopk_tag, ← hhdr, ← hspk_pub, ← hspk_priv, ← hpq_priv]
  dsimp only [p2Sub1To4Frame, p2OverSub5Frame]
  rw [p2_pointsToBytes_split_head skBuf (bytesToBv8 inp.pqspkBSk) (by rw [hpq_priv]; omega),
      p2_ctBuf_split ctBufPtr (bytesToBv8 inp.hdr.kemCt) (by rw [hhdr]; exact hkem_len),
      p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt,
      p2_sp3b8_40_split sp,
      p2_memRegion_3e0_split_344_24 sp,
      p2_memRegion_a90_65_eq_cells8_1 sp,
      p2_fp80_9_split fp]
  sep_norm
  refine Entails.sepExists_elim fun u_b90 => Entails.sepExists_elim fun b_b98 =>
    Entails.sepExists_right u_b90 (Entails.sepExists_right b_b98 ?_)
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 800000 in
theorem p2_over_sub5_to_sub6 {A : RustAlloc} (img : Obj.Image)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0' u_b90' : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes) (drKey : DRKey)
    (pqBytes kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 b_b98' : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp)
    (hkyberPub_len : kyberPubBytes.length = 1568) :
    (bobParamsFieldsAt (coroPtr + 0x658#64) skBuf (msgPtr + 0x90#64) ctBufPtr
       (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
     p2BobSessV1At A (sp + 0x3e0#64) inp ikBPk spkBPk drKey pqBytes ∗
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
     logOff img ∗ A.pool ∗ stackAt sp stk ∗
     p2OverSub5Frame A img spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
       remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
       pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
       msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
       stSpk' stKpk' stPk' g recG sess Frame) ⊢
    ∃∗ localIkBoxPtr : BitVec 64, ∃∗ remoteIkBoxPtr : BitVec 64, ∃∗ rootKeyBoxPtr : BitVec 64,
    ∃∗ baseKeyBoxPtr : BitVec 64, ∃∗ ratchetPubBoxPtr : BitVec 64,
    ∃∗ ratchetPrivBoxPtr : BitVec 64, ∃∗ chainKeyBoxPtr : BitVec 64,
    ∃∗ spqrCap : BitVec 64, ∃∗ spqrBufPtr : BitVec 64, ∃∗ pad_f4 : BitVec 32,
    ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
    ∃∗ c4 : BitVec 64, ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
    ∃∗ u_650 : BitVec 64, ∃∗ u_298 : BitVec 64, ∃∗ u_2a0 : BitVec 64, ∃∗ u_2a8 : BitVec 32,
    ∃∗ u_3a0 : BitVec 64, ∃∗ b_3ac : BitVec 8,
    ∃∗ u_3b0 : BitVec 64, ∃∗ u_3b8 : BitVec 64, ∃∗ u_3c0 : BitVec 64,
    ∃∗ u_3c8 : BitVec 64, ∃∗ u_3d0 : BitVec 64, ∃∗ u_3d8 : BitVec 64,
      ⌜localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧ baseKeyBoxPtr ≠ 0#64 ∧
        ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧ chainKeyBoxPtr ≠ 0#64⌝ ∗
      bobParamsFieldsAt (coroPtr + 0x658#64) skBuf (msgPtr + 0x90#64) ctBufPtr
        (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
      ((sp + 0x3e0#64) ↦ₛ (p2BobSessHead56Bv8 localIkBoxPtr remoteIkBoxPtr ++
        (p2BobSessMid280V1 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
           (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
           pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++ unpack64 0#64))) ∗
      memRegion (sp + 0xa90#64) 288 ∗
      memRegion (coroPtr + 0x4f8#64) 344 ∗
      ((coroPtr + 0x650#64) ↦₆₄ u_650) ∗
      memRegion (coroPtr + 0x788#64) 16 ∗
      ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
      ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
      ikit.identityAt idStorePtr stId ∗
      ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
      ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
      ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗
      ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
      ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
      ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
      prevSessionsEmptyAt A coroPtr g ∗
      sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
      ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
      ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
      ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
      cells (coroPtr + 0x250#64) 6 ∗
      ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
      ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
      ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
      ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
      ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
      ((coroPtr + 0x390#64) ↦₈ b_390) ∗
      ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
      ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? inp.hdr)) ∗
      ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
      ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
      ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗
      ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8') ∗
      ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8') ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
      ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
      ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
      ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
      ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
      ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
      A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
      A.live skBuf 3168 1 ∗
      logOff img ∗ A.pool ∗ stackAt sp stk ∗
      p2Sub6Frame A img spkKit kpkKit pkKit s0 sp fp coroPtr outPtr msgPtr
        remoteAddrPtr localAddrPtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
        localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
        ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        inp ikBPk spkBPk drKey pqBytes opkPkBytes opkSkBytes b_2c0
        stSpk' stKpk' stPk' gMe gPeer Frame := by
  dsimp only [p2BobSessV1At, p2OverSub5Frame, p2Sub6Frame, p2BobSessHeapAt]
  sep_norm
  refine Entails.sepExists_elim fun localIkBoxPtr =>
    Entails.sepExists_elim fun remoteIkBoxPtr =>
    Entails.sepExists_elim fun rootKeyBoxPtr =>
    Entails.sepExists_elim fun baseKeyBoxPtr =>
    Entails.sepExists_elim fun ratchetPubBoxPtr =>
    Entails.sepExists_elim fun ratchetPrivBoxPtr =>
    Entails.sepExists_elim fun chainKeyBoxPtr =>
    Entails.sepExists_elim fun spqrCap =>
    Entails.sepExists_elim fun spqrBufPtr =>
    Entails.sepExists_elim fun pad_f4 =>
    Entails.sepExists_elim fun c0 =>
    Entails.sepExists_elim fun c1 =>
    Entails.sepExists_elim fun c2 =>
    Entails.sepExists_elim fun c3 =>
    Entails.sepExists_elim fun c4 =>
    Entails.sepExists_elim fun d0 =>
    Entails.sepExists_elim fun d1 =>
    Entails.sepExists_elim fun d2 => ?_
  rw [p2BobSession344Bv8V1_eq_head56_mid280V1]
  refine p2_entails_frame_v1 (Entails.of_eq (p2_coro298_20_split coroPtr)) (by sep_focus) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun u_298 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun u_2a0 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun u_2a8 => ?_
  refine p2_entails_frame_v1 (Entails.of_eq (ProofLib.memRegion_eight (coroPtr + 0x650#64)))
    (by sep_focus) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun u_650 => ?_
  refine p2_entails_frame_v1 (Entails.of_eq (ProofLib.memRegion_eight (sp + 0x3a0#64)))
    (by sep_focus) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun u_3a0 => ?_
  refine p2_entails_frame_v1 (Entails.of_eq (ProofLib.memRegion_one (sp + 0x3ac#64)))
    (by sep_focus) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun b_3ac => ?_
  refine p2_entails_frame_v1 (Entails.of_eq (ProofLib.memRegion_eight (sp + 0x3b0#64)))
    (by sep_focus) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun u_3b0 => ?_
  refine p2_entails_frame_v1 (Entails.of_eq (ProofLib.memRegion_eight (sp + 0x3b8#64)))
    (by sep_focus) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun u_3b8 => ?_
  refine p2_entails_frame_v1 (Entails.of_eq (ProofLib.memRegion_eight (sp + 0x3c0#64)))
    (by sep_focus) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun u_3c0 => ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3c8_7_1_eq_exists64 sp)) (by sep_focus) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun u_3c8 => ?_
  refine p2_entails_frame_v1 (Entails.of_eq (ProofLib.memRegion_eight (sp + 0x3d0#64)))
    (by sep_focus) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun u_3d0 => ?_
  refine p2_entails_frame_v1 (Entails.of_eq (ProofLib.memRegion_eight (sp + 0x3d8#64)))
    (by sep_focus) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun u_3d8 => ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_cells8_1_223_eq_288 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_coro4f8_2cells_328_eq_344 coroPtr))
    (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_fp80_words_entails_9 fp u_b90' b_b98') (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len) (by sep_focus) ?_
  refine Entails.sepExists_right localIkBoxPtr
    (Entails.sepExists_right remoteIkBoxPtr
    (Entails.sepExists_right rootKeyBoxPtr
    (Entails.sepExists_right baseKeyBoxPtr
    (Entails.sepExists_right ratchetPubBoxPtr
    (Entails.sepExists_right ratchetPrivBoxPtr
    (Entails.sepExists_right chainKeyBoxPtr
    (Entails.sepExists_right spqrCap
    (Entails.sepExists_right spqrBufPtr
    (Entails.sepExists_right pad_f4
    (Entails.sepExists_right c0
    (Entails.sepExists_right c1
    (Entails.sepExists_right c2
    (Entails.sepExists_right c3
    (Entails.sepExists_right c4
    (Entails.sepExists_right d0
    (Entails.sepExists_right d1
    (Entails.sepExists_right d2
    (Entails.sepExists_right u_650
    (Entails.sepExists_right u_298
    (Entails.sepExists_right u_2a0
    (Entails.sepExists_right u_2a8
    (Entails.sepExists_right u_3a0
    (Entails.sepExists_right b_3ac
    (Entails.sepExists_right u_3b0
    (Entails.sepExists_right u_3b8
    (Entails.sepExists_right u_3c0
    (Entails.sepExists_right u_3c8
    (Entails.sepExists_right u_3d0
    (Entails.sepExists_right u_3d8 ?_)))))))))))))))))))))))))))))
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
