/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BridgePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsCPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget

/-!
# Budget-Threaded Relocatable Stage P2 Exit Arm Bridges

Proves `RustCliAllocBudget M` placed spatial entailments into `p2ErrFrameAtPlaced` for Error Arms
1–3 and `SepWPp` unwind bridges for Error Arms 4–5 on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  IdentitySelfStoreSpec IdentityStoreSpec KyberPreKeyStoreSpec LibsignalCodeRoLoaded
  PreKeyStoreSpec SignedPreKeyStoreSpec speErrAt speWordsAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf (kpPollOutAt)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord SignedPreKeyRecord)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput HandshakeHdr WellSizedAcceptKeysInput bytesToBv8
)
open CryptoVerification.E2E.Pqxdh.ResponderStore (clampBv8List)
open CryptoVerification.E2E.Pqxdh.ResponderCore (bobParamsFieldsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved decryptPrekeySavedRegsAt eq_of_sep_emp opkPresentTag opkUnusedFieldAt
  processPrekeyActive10At sessionRecordEmptyHeaderAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp (weaken_frame)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  hdrOpkIdBv? opkOptTag32 p2CoroScratchTailAt p2ErrFrameAt p2MsgFieldsAt p2Sub1To4Frame
  p2_a90_err45_to_288 p2_bobParamsFieldsAt_err_weaken p2_cells8_a90_to_cells6_2
  p2_coro398_bytes_words4_entails_96 p2_coro4b0_byte_bytes_entails_65
  p2_coro4f8_2cells_328_eq_344 p2_coro4f8_words2_328_entails_344 p2_coro658_298_rejoin
  p2_ctBuf_split p2_drop_frame_mid p2_entails_frame_v1 p2_fp80_to_memRegion9
  p2_pointsToBytes_entails_memRegion p2_pqsk_split_rejoin p2_processPrekeyActive10At_eq
  p2_sessionRecordEmptyHeaderAt_eq p2_sp3b0_48_split_8_40 p2_sp3e0_arm4_to_368
  p2_sp3e0_arm5_to_368 p2_sp80_11words_entails_88 p2_stack_split_alloc
  stageP1EntryPlaced stageP1ProgPlaced
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.SepWPp (mono_run)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (retagSignedPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (retagKyberPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (retagPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (retagIdentityStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (IdentitySelfStoreKitPlacedOkI)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BridgePlacedBudget (
  p2ErrFrameAtPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget (
  p2_bind_sepWPp_steps_frame_state
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsBPlacedBudget (
  p2Arm4ErrEvents p2_arm4_err_hooks_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsCPlacedBudget (
  p2Arm5ErrEvents p2_arm5_err_hooks_placed_ok
)

/-- Arm 1 (`get_signed_pre_key` error) budget-threaded placed spatial bridge into
`p2ErrFrameAtPlaced`. -/
theorem p2_v1_arm1_entails_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (s0 sf : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_b0 v_330 v_388 u_488 u_80 u_88 spkFutPtr : BitVec 64)
    (b_4b0 msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (hdr : HandshakeHdr)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
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
      ((coroPtr + 0x500#64) ↦₆₄ (0#64 + spkKit.getFutVtOff)) ∗
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
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st sf ∗ stackAt sp stk ∗
      p2Sub1To4Frame A.repAlloc ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame ⊢
    speErrAt spkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
      kpkKit.storeAt kyberStorePtr stKpk ∗
      pkKit.storeAt preKeyStorePtr stPk ∗
      ikit.identityAt idStorePtr stId ∗
      p2ErrFrameAtPlaced A lim st s0 sf sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
        v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk Frame :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2_v1_arm1_entails_placed
    (A := A.atState lim st sf)
    (retagSignedPreKeyStore spkKit)
    (retagKyberPreKeyStore kpkKit)
    (retagPreKeyStore pkKit)
    (retagIdentityStore ikit)
    s0 sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    v_b0 v_330 v_388 u_488 u_80 u_88 spkFutPtr
    b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr
    stSpk stKpk stPk stId e gMe gPeer stk Frame

/-- Arm 2 (`get_kyber_pre_key` error) budget-threaded placed spatial bridge into
`p2ErrFrameAtPlaced`. -/
theorem p2_v1_arm2_entails_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (s0 sf : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_b0 v_330 v_388 u_488 u_80 u_88 kyberFutPtr : BitVec 64)
    (b_4b0 msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (hdr : HandshakeHdr) (spkRec : SignedPreKeyRecord)
    (spkPubBytes spkPrivBytes : List (BitVec 8))
    (hpub : spkPubBytes.length = 32) (hpriv : spkPrivBytes.length = 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
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
      ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
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
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st sf ∗ stackAt sp stk ∗
      p2Sub1To4Frame A.repAlloc ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame ⊢
    speErrAt kpkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
      kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
      pkKit.storeAt preKeyStorePtr stPk ∗
      ikit.identityAt idStorePtr stId ∗
      p2ErrFrameAtPlaced A lim st s0 sf sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
        v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk Frame :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2_v1_arm2_entails_placed
    (A := A.atState lim st sf)
    (retagSignedPreKeyStore spkKit)
    (retagKyberPreKeyStore kpkKit)
    (retagPreKeyStore pkKit)
    (retagIdentityStore ikit)
    s0 sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    v_b0 v_330 v_388 u_488 u_80 u_88 kyberFutPtr
    b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr spkRec
    spkPubBytes spkPrivBytes hpub hpriv
    stSpk stKpk stPk stId e gMe gPeer stk Frame

/-- Arm 3 (`get_pre_key` error) budget-threaded placed spatial bridge into
`p2ErrFrameAtPlaced`. -/
theorem p2_v1_arm3_entails_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (s0 sf : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_b0 v_330 v_388 u_80 u_88 pkBuf skBuf opkFutPtr v90 : BitVec 64)
    (b_4b0 msgVerByte : BitVec 8)
    (opkId opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (hdr : HandshakeHdr) (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
    (spkPubBytes spkPrivBytes : List (BitVec 8))
    (hpub : spkPubBytes.length = 32) (hpriv : spkPrivBytes.length = 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
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
      ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
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
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st sf ∗ stackAt sp stk ∗
      p2Sub1To4Frame A.repAlloc ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame ⊢
    speErrAt pkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
      kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
      pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
      ikit.identityAt idStorePtr stId ∗
      p2ErrFrameAtPlaced A lim st s0 sf sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
        v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk Frame :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2_v1_arm3_entails_placed
    (A := A.atState lim st sf)
    (retagSignedPreKeyStore spkKit)
    (retagKyberPreKeyStore kpkKit)
    (retagPreKeyStore pkKit)
    (retagIdentityStore ikit)
    s0 sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    v_b0 v_330 v_388 u_80 u_88 pkBuf skBuf opkFutPtr v90
    b_4b0 msgVerByte opkId opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr spkRec kpkRec
    spkPubBytes spkPrivBytes hpub hpriv
    stSpk stKpk stPk stId e gMe gPeer stk Frame

/-- Frame held constant across `stageP2_sub5_v1_kits_placed` (`+0x36ac -> +0x125c` and Arms 4–5),
parameterized by `A : RustCliAllocBudget M`. -/
def p2Sub5FramePlaced {M : AllocCostModel} (A : RustCliAllocBudget M) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (s0 : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90 : BitVec 64)
    (kyberPubBytes : List (BitVec 8))
    (hdr : HandshakeHdr) (msgVerByte b_2c0 b_390 b_4f2 : BitVec 8)
    (kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState)
    (Frame : SepProp) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Sub5FramePlaced
    A.repAlloc spkKit kpkKit pkKit ikit s0
    sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes
    hdr msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
    stSpk' stKpk' stPk' Frame

theorem p2Sub5FramePlaced_eq_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (s0 : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90 : BitVec 64)
    (kyberPubBytes : List (BitVec 8))
    (hdr : HandshakeHdr) (msgVerByte b_2c0 b_390 b_4f2 : BitVec 8)
    (kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState) (stPk' : pkKit.PkState)
    (Frame : SepProp) :
    p2Sub5FramePlaced A spkKit kpkKit pkKit ikit s0
      sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes
      hdr msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
      stSpk' stKpk' stPk' Frame =
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Sub5FramePlaced
      (A.atState lim st s)
      (retagSignedPreKeyStore spkKit)
      (retagKyberPreKeyStore kpkKit)
      (retagPreKeyStore pkKit)
      (retagIdentityStore ikit)
      s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes
      hdr msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
      stSpk' stKpk' stPk' Frame := rfl

private theorem lsLogOff_eq_pl [LibsignalPlacement] :
    lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

private theorem protocolAddressAt_atState_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : AddrGhost) (p : BitVec 64) :
    protocolAddressAt (A.atState lim st s) g p = protocolAddressAt A.repAlloc g p := rfl

private theorem p2_finish_err_arm_drop_state {prog : Program} {ret : BitVec 64} {s : State}
    {P ArmPre Rest Drop : SepProp} {ArmOut Keep : State → SepProp}
    {Q Qp : State → SepProp → Prop} {Φ : State → Prop}
    (hArm : SepWPp prog ret s ArmPre
      (fun sf P_f => sf.trace = s.trace ∧ (P_f ⊢ ArmOut sf) ∧ Φ sf)
      (fun _ _ => False))
    (hP : P = ArmPre ∗ Rest)
    (hSplit : ∀ sf : State, ArmOut sf ∗ Rest ⊢ Drop ∗ Keep sf)
    (hQ : ∀ sf P_f,
      Steps prog s sf → sf.pc = ret → sf.status = .Running →
      sf.trace = s.trace → (P_f ⊢ Keep sf) → Φ sf → Q sf P_f) :
    SepWPp prog ret s P Q Qp := by
  have hArm_re := mono_run hArm fun sf P_f h =>
    let ⟨htrf, hentf, hΦ⟩ := h
    And.intro hentf (And.intro htrf hΦ)
  refine p2_bind_sepWPp_steps_frame_state hArm_re hP fun sf hst hpcf hrunf ⟨htrf, hΦ⟩ => ?_
  refine weaken_frame (hSplit sf) (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  refine p2_drop_frame_mid (Drop := Drop) rfl ?_
  exact SepWPp.done hpcf hrunf (hQ sf (Keep sf) hst hpcf hrunf htrf (Entails.refl _) hΦ)

set_option maxHeartbeats 800000 in
/-- Arm 4 (`+0x07bc -> s0.readReg64 .x30`) budget-threaded placed full `SepWPp` exit bridge into
`p2ErrFrameAtPlaced` under `StageP2ClosureHooksPlaced`. -/
theorem p2_v1_arm4_ok_hooks_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    {senv : IdentitySelfStoreBudgetEnv skit}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (s0 s2 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90
     v_a8 v_b8 v_d0 u_b90 : BitVec 64)
    (inp : AcceptKeysInput) (spkBPk : List UInt8)
    (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 b_b98 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (e : skit.KpErr) (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
    (hwell : WellSizedAcceptKeysInput inp)
    (hspkBPk_len : spkBPk.length = 32)
    (hkyberPub_len : kyberPubBytes.length = 1568)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hstk_alloc : allocHookStack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hCode : LibsignalCodeRoLoaded lsmpl s2.mem)
    (hpc : s2.pc = stageP1EntryPlaced + 0x7bc#64)
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
      Steps (stageP1ProgPlaced ext) s2 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s2.trace → sf.sp = sp + 0xcd0#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt skit.kpErr outPtr e ∗
        spkKit.storeAt spkStorePtr stSpk' ∗
        kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents (p2Arm4ErrEvents skit.kpBoxSize 0#64) st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 inp.hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s2
      (kpPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       memRegion (sp + 0x428#64) 272 ∗
       A.live idKpFutPtr skit.kpBoxSize 8 ∗
       skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗
       ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ∗
       ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
       ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
       ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
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
       protocolAddressAt A.repAlloc gMe localAddrPtr ∗
       protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
       memRegion (sp + 0x3c8#64) 7 ∗
       cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
       cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s2 ∗ stackAt sp stk ∗
       p2Sub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
         remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
         pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
         msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
         stSpk' stKpk' stPk' Frame)
      Q Qp := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hpqsk_len : (bytesToBv8 inp.pqspkBSk).length = 3168 := by
    simp [bytesToBv8, hwell.2.2.2.2.2.1]
  have hkem_len : 0 < (bytesToBv8 inp.hdr.kemCt).length := by
    simp [bytesToBv8, hwell.2.2.2.2.2.2.2.2.2]
  dsimp only [p2Sub5FramePlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Sub5FramePlaced,
    RustCliAllocBudget.repAlloc_live]
  refine weaken_frame
    (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len)
    (by sep_focus) ?_
  refine weaken_frame
    (Entails.of_eq (p2_pqsk_split_rejoin skBuf (bytesToBv8 inp.pqspkBSk) (by omega)))
    (by sep_focus) ?_
  refine weaken_frame
    (p2_pointsToBytes_entails_memRegion skBuf (bytesToBv8 inp.pqspkBSk) 3168 hpqsk_len)
    (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_cells8_a90_to_cells6_2 sp)) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_stack_split_alloc sp stk hstk_alloc hstk64))
    (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_eq coroPtr))
    (by sep_focus) ?_
  have hif0 : (if (0#64 : BitVec 64) = 0 then emp
      else A.live 8#64 ((0#64 : BitVec 64).toNat * 24) 8 ∗
           memRegion 8#64 ((0#64 : BitVec 64).toNat * 24)) = emp := by simp
  have harm4 := p2_arm4_err_hooks_placed_ok (st := st) (Qp := fun _ _ => False) hH hskitOk s0 s2
    sp coroPtr msgPtr ctxPtr outPtr 0#64 8#64
    idStorePtr idKpFutPtr pkBuf skBuf fp
    (coroPtr + 0x390#64) (coroPtr + 0x398#64) (coroPtr + 0x4f2#64)
    v_a8 (coroPtr + 0x390#64) v_b8 ctxPtr v_d0 u_b90
    opkIdWord b_2c0 b_390 b_4f2 b_b98 e
    (by decide) hCode hsp hpc hrun (hsp ▸ hsp_align)
    hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs
  rw [hif0, emp_sepConj] at harm4
  refine p2_finish_err_arm_drop_state
    (Drop := ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
             ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
             ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64))
    harm4 (by sep_focus) (fun sf => ?_)
    (fun sf P_f hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hinvf, _hlive⟩ =>
      hCont sf P_f hst hpcf hrunf htrf hspf hcsf hvregsf hinvf hent)
  dsimp only [p2ErrFrameAtPlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2ErrFrameAtPlaced,
    p2ErrFrameAt, p2CoroScratchTailAt, p2MsgFieldsAt]
  rw [protocolAddressAt_atState_eq, protocolAddressAt_atState_eq, lsLogOff_eq_pl]
  dsimp only [RustCliAllocBudget.atState]
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
    (p2_coro4f8_words2_328_entails_344 coroPtr idKpFutPtr (0#64 + skit.kpFutVtOff))
    (by sep_focus) ?_
  refine p2_entails_frame_v1
    (Entails.of_eq (p2_ctBuf_split ctBufPtr (bytesToBv8 inp.hdr.kemCt) hkem_len).symm)
    (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev p2_v1_arm4_ok_ext_placed := @p2_v1_arm4_ok_hooks_placed
abbrev p2_v1_arm4_ok_4k_placed := @p2_v1_arm4_ok_hooks_placed
abbrev p2_v1_arm4_ok_placed := @p2_v1_arm4_ok_hooks_placed

set_option maxHeartbeats 800000 in
/-- Arm 5 (`+0x125c -> s0.readReg64 .x30`) budget-threaded placed full `SepWPp` exit bridge into
`p2ErrFrameAtPlaced` under `StageP2ClosureHooksPlaced`. -/
theorem p2_v1_arm5_ok_hooks_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s0 sf5 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90
     errTag w2 w3 w4 w5 w6 v_a8' v_b8' v_d0' u_b90' : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : List UInt8)
    (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 b_b98' : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
    (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hkyberPub_len : kyberPubBytes.length = 1568)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (herr_ne_ok : errTag ≠ 0xfffffffffffffffe#64)
    (herr_ne_pend : errTag ≠ 0xfffffffffffffffd#64)
    (hstk_alloc : allocHookStack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hCode : LibsignalCodeRoLoaded lsmpl sf5.mem)
    (hpc : sf5.pc = stageP1EntryPlaced + 0x125c#64)
    (hrun : sf5.status = .Running) (hsp : sf5.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : sf5.readReg64 .x19 = coroPtr)
    (hx25 : sf5.readReg64 .x25 = sp + 0x210#64)
    (hx28 : sf5.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs sf5 = calleeSavedVRegs s0)
    (hCont : ∀ (sf : State) (P_f : SepProp),
      Steps (stageP1ProgPlaced ext) sf5 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = sf5.trace → sf.sp = sp + 0xcd0#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
        spkKit.storeAt spkStorePtr stSpk' ∗
        kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents (p2Arm5ErrEvents 0#64) st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 inp.hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf5
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
       protocolAddressAt A.repAlloc gMe localAddrPtr ∗
       protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
       memRegion (sp + 0x3c8#64) 7 ∗ cells (sp + 0x560#64) 4 ∗
       cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
       cells (sp + 0xa90#64) 8 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ anyHeap ∗ A.pool lim st sf5 ∗ stackAt sp stk ∗
       p2Sub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
         remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
         pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
         msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
         stSpk' stKpk' stPk' Frame)
      Q Qp := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hkem_len : 0 < (bytesToBv8 inp.hdr.kemCt).length := by
    simp [bytesToBv8, hwell.2.2.2.2.2.2.2.2.2]
  refine p2_drop_frame_mid (Drop := anyHeap) (by sep_focus) ?_
  dsimp only [p2Sub5FramePlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Sub5FramePlaced,
    RustCliAllocBudget.repAlloc_live]
  refine weaken_frame
    (p2_bobParamsFieldsAt_err_weaken coroPtr msgPtr skBuf ctBufPtr inp ikBPk spkBPk hwell)
    (by sep_focus) ?_
  refine weaken_frame
    (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len)
    (by sep_focus) ?_
  refine weaken_frame (p2_fp80_to_memRegion9 fp u_b90' b_b98') (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_cells8_a90_to_cells6_2 sp)) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_stack_split_alloc sp stk hstk_alloc hstk64))
    (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_eq coroPtr))
    (by sep_focus) ?_
  have hif0 : (if (0#64 : BitVec 64) = 0 then emp
      else A.live 8#64 ((0#64 : BitVec 64).toNat * 24) 8 ∗
           memRegion 8#64 ((0#64 : BitVec 64).toNat * 24)) = emp := by simp
  have harm5 := p2_arm5_err_hooks_placed_ok (st := st) (Qp := fun _ _ => False) hH s0 sf5
    sp coroPtr outPtr 0#64 8#64 pkBuf skBuf
    errTag w2 w3 w4 w5 w6 u_88 v_a8' v_b8' v_d0'
    b_2c0 b_390 b_4f2 (by decide) herr_ne_pend herr_ne_ok
    hCode hsp hpc hrun (hsp ▸ hsp_align)
    hx19 hx25 hx28 hvregs
  rw [hif0, emp_sepConj] at harm5
  refine p2_finish_err_arm_drop_state (Drop := emp) harm5 (by sep_focus) (fun sf => ?_)
    (fun sf P_f hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hinvf, _hlive⟩ =>
      hCont sf P_f hst hpcf hrunf htrf hspf hcsf hvregsf hinvf hent)
  rw [emp_sepConj]
  dsimp only [p2ErrFrameAtPlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2ErrFrameAtPlaced,
    p2ErrFrameAt, p2CoroScratchTailAt, p2MsgFieldsAt]
  rw [protocolAddressAt_atState_eq, protocolAddressAt_atState_eq, lsLogOff_eq_pl]
  dsimp only [RustCliAllocBudget.atState]
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

abbrev p2_v1_arm5_ok_ext_placed := @p2_v1_arm5_ok_hooks_placed
abbrev p2_v1_arm5_ok_4k_placed := @p2_v1_arm5_ok_hooks_placed
abbrev p2_v1_arm5_ok_placed := @p2_v1_arm5_ok_hooks_placed

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlacedBudget
