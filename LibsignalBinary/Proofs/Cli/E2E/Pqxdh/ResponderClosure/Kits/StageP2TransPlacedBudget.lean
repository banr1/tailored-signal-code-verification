/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2TransPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Stage P2 Precondition and Spatial Transitions

Budget-threaded `[LibsignalPlacement]` counterpart of `StageP2TransPlaced`, defining
`stageP2PreAtPlaced` at `A.atState lim st s` and proving the inter-substage framing transitions.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2TransPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement lsLogFilterAddr)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  IdentitySelfStoreSpec IdentityStoreSpec KyberPreKeyStoreSpec PreKeyStoreSpec SignedPreKeyStoreSpec
)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput DRKey HandshakeHdr bytesToBv8)
open CryptoVerification.E2E.Pqxdh.ResponderStore (clampBv8List)
open CryptoVerification.E2E.Pqxdh.ResponderCore (bobParamsFieldsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  decryptPrekeySavedRegsAt opkPresentTag opkUnusedFieldAt processPrekeyActive10At
  sessionRecordEmptyHeaderAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  hdrOpkIdBv? opkOptTag8 opkOptTag32 p2BobSessHead56Bv8 p2BobSessMid280V1 p2Sub1To4Frame
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (retagSignedPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (retagKyberPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (retagPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (retagIdentityStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (retagIdentitySelfStore)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget (
  p2BobSessV1At
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlacedBudget (
  p2Sub5FramePlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms2PlacedBudget (
  p2Sub6FramePlaced
)

/-- Budget-threaded `[LibsignalPlacement]` spatial precondition at `+0x0868` for fresh Bob session
initialization in Stage P2. -/
def stageP2PreAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP2PreAtPlaced
    (A.atState lim st s)
    (retagSignedPreKeyStore spkKit)
    (retagKyberPreKeyStore kpkKit)
    (retagPreKeyStore pkKit)
    (retagIdentityStore ikit)
    s0 sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
    hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
    stSpk stKpk stPk stId gMe gPeer stk Frame

theorem stageP2PreAtPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    stageP2PreAtPlaced A lim st s0 s spkKit kpkKit pkKit ikit
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer stk Frame =
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP2PreAtPlaced
      (A.atState lim st s)
      (retagSignedPreKeyStore spkKit)
      (retagKyberPreKeyStore kpkKit)
      (retagPreKeyStore pkKit)
      (retagIdentityStore ikit)
      s0 sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer stk Frame := rfl

theorem p2_entry_to_sub1To4_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    stageP2PreAtPlaced A lim st s0 s spkKit kpkKit pkKit ikit
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer stk Frame ⊢
    spkKit.storeAt spkStorePtr stSpk ∗
      kpkKit.storeAt kyberStorePtr stKpk ∗
      pkKit.storeAt preKeyStorePtr stPk ∗
      sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
      memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
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
      memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp stk ∗
      p2Sub1To4Frame A.repAlloc ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2_entry_to_sub1To4_placed
    (A := A.atState lim st s)
    (retagSignedPreKeyStore spkKit)
    (retagKyberPreKeyStore kpkKit)
    (retagPreKeyStore pkKit)
    (retagIdentityStore ikit)
    s0 sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
    hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
    stSpk stKpk stPk stId gMe gPeer stk Frame

theorem p2_sub4_to_sub5_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    {ikit : IdentityStoreSpec A.repAlloc b} (skit : IdentitySelfStoreSpec ikit)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0' : BitVec 64)
    (inp : AcceptKeysInput) (hdr : HandshakeHdr) (spkBPk : List UInt8)
    (spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
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
      sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
      memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
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
      memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp stk ∗
      p2Sub1To4Frame A.repAlloc ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame ⊢
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
      protocolAddressAt A.repAlloc gMe localAddrPtr ∗
      protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
      ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
      memRegion (sp + 0x3c8#64) 7 ∗ memRegion (sp + 0x3e0#64) 344 ∗
      cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
      cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
      ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp stk ∗
      p2Sub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
        remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
        msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
        stSpk' stKpk' stPk' Frame :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2_sub4_to_sub5_placed
    (A := A.atState lim st s)
    (retagSignedPreKeyStore spkKit)
    (retagKyberPreKeyStore kpkKit)
    (retagPreKeyStore pkKit)
    (retagIdentitySelfStore (A' := A.atState lim st s) skit)
    s0 sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0'
    inp hdr spkBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkPkBytes opkSkBytes
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
    msgVerByte b_2c0 b_390 b_4f2 stSpk' stKpk' stPk' stId gMe gPeer stk Frame
    hhdr hspk_pub hspk_priv hpq_priv hopk_tag hkyber_priv_len hkem_len

theorem p2_sub5_to_sub6_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0' u_b90' : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : List UInt8) (drKey : DRKey)
    (pqBytes kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 b_b98' : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
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
     protocolAddressAt A.repAlloc gMe localAddrPtr ∗
     protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
     ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
     ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
     ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
     memRegion (sp + 0x3c8#64) 7 ∗ cells (sp + 0x560#64) 4 ∗
     cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
     cells (sp + 0xa90#64) 8 ∗
     ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗
     (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp stk ∗
     p2Sub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
       remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
       pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
       msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
       stSpk' stKpk' stPk' Frame) ⊢
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
      sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
      memRegion (coroPtr + 0x100#64) 336 ∗
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
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp stk ∗
      p2Sub6FramePlaced A spkKit kpkKit pkKit s0 sp fp coroPtr outPtr msgPtr
        remoteAddrPtr localAddrPtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
        localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
        ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        inp ikBPk spkBPk drKey pqBytes opkPkBytes opkSkBytes b_2c0
        stSpk' stKpk' stPk' gMe gPeer Frame :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2_sub5_to_sub6_placed
    (A := A.atState lim st s)
    (retagSignedPreKeyStore spkKit)
    (retagKyberPreKeyStore kpkKit)
    (retagPreKeyStore pkKit)
    (retagIdentityStore ikit)
    s0 sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0' u_b90'
    inp ikBPk spkBPk drKey pqBytes kyberPubBytes opkPkBytes opkSkBytes
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
    msgVerByte b_2c0 b_390 b_4f2 b_b98'
    stSpk' stKpk' stPk' stId gMe gPeer stk Frame hkyberPub_len

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2TransPlacedBudget
