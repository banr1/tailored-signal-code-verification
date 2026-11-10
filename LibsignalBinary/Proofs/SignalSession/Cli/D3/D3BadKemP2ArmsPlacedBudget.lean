/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsAPlaced
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Trans

/-!
# Budget-Threaded Stage P2 Spatial Bridges and Error Arms on Bad-KEM

Budget-threaded `[LibsignalPlacement]` entry and Substage 4→5 spatial bridges, Error Arms 1–3
entailments into `p2BadKemErrFrameAtPlaced`, and Arm 5 error-payload unpacking.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost protocolAddressAt
)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionStateReprAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  IdentityStoreSpec KyberPreKeyStoreSpec PreKeyStoreSpec SignedPreKeyStoreSpec
  speErrAt speWordsAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf (IdentitySelfStoreSpec)
open CryptoVerification.RecordCodecs (
  KyberPreKeyRecord PreKeyRecord SignedPreKeyRecord
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput HandshakeHdr bytesToBv8
)
open CryptoVerification.E2E.Pqxdh.ResponderStore (
  clampBv8List clampBv8List_length
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  decryptPrekeySavedRegsAt opkPresentTag processPrekeyActive10At
  sessionRecordEmptyHeaderAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  hdrOpkIdBv? opkOptTag8 opkOptTag32 p2Sub5FramePlaced
  p2_a90_err123_to_288 p2_coro398_bytes_cells4_entails_96
  p2_coro398_bytes_words4_entails_96 p2_coro4b0_byte_64_entails_65
  p2_coro4f8_words2_328_entails_344 p2_entails_frame_v1 p2_fp80_9_split
  p2_memRegion_3e0_split_344_24 p2_memRegion_a90_65_eq_cells8_1
  p2_processPrekeyActive10At_eq p2_sp3b8_40_split p2_sp80_11words_entails_88
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (p2OverSub5FramePlaced)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.reduceNeg]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

private theorem eq_of_sep_emp {P Q : SepProp} (h : P = Q ∗ emp) : P = Q :=
  h.trans (sepConj_emp Q)

/-! ## 1. Entry Spatial Bridges on Bad-KEM (`[LibsignalPlacement]`) -/

theorem p2_badKem_entry_to_sub1To4_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (st : M.σ) (s0 s : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced A lim spkKit kpkKit pkKit ikit st s0 s
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr ctBytes msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer stk Frame ⊢
    spkKit.storeAt spkStorePtr stSpk ∗
      kpkKit.storeAt kyberStorePtr stKpk ∗
      pkKit.storeAt preKeyStorePtr stPk ∗
      sessionRecordEmptyHeaderAt (coroPtr + 224#64) ∗
      memRegion (coroPtr + 256#64) 336 ∗ cells (coroPtr + 592#64) 6 ∗
      ((coroPtr + 704#64) ↦₈ b_2c0) ∗ ((coroPtr + 912#64) ↦₈ b_390) ∗
      cells (coroPtr + 920#64) 8 ∗ cells (coroPtr + 984#64) 4 ∗
      cells (coroPtr + 1016#64) 6 ∗ cells (coroPtr + 1128#64) 4 ∗
      ((coroPtr + 1160#64) ↦₆₄ u_488) ∗ ((coroPtr + 1200#64) ↦₈ b_4b0) ∗
      memRegion (coroPtr + 1201#64) 64 ∗
      ((coroPtr + 1265#64) ↦₈ b_4f1) ∗ ((coroPtr + 1266#64) ↦₈ b_4f2) ∗
      cells (coroPtr + 1272#64) 2 ∗
      ((msgPtr + 120#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗ ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 160#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 168#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
      ((msgPtr + 236#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 240#64) ↦₈ 4#8) ∗
      ((sp + 144#64) ↦₆₄ u_90) ∗ ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗
      ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ u_a8) ∗
      ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗ ((sp + 184#64) ↦₆₄ u_b8) ∗
      ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 200#64) ↦₆₄ outPtr) ∗
      ((sp + 208#64) ↦₆₄ u_d0) ∗
      memRegion (sp + 624#64) 9 ∗ memRegion (sp + 880#64) 36 ∗
      memRegion (sp + 944#64) 8 ∗ memRegion (sp + 992#64) 368 ∗
      cells (sp + 2352#64) 8 ∗ memRegion (sp + 2704#64) 65 ∗
      decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
      memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim st s ∗ stackAt sp stk ∗
      D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame A ikit
        sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
        v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame := by
  dsimp only [D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced,
    D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame, p2CoroScratchTailAt, p2BadKemMsgFieldsAt]
  rw [← p2_coro398_cells8_4_eq_96 coroPtr,
      ← p2_coro4f8_2cells_328_eq_344 coroPtr,
      ← p2_sp3b0_8_40_eq_48 sp,
      p2_memRegion_a90_288_split_65_223 sp]
  exact Entails.of_eq (by sep_ac_rfl)

theorem p2_over_badKem_entry_to_sub1To4_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (st : M.σ) (s0 s : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp) :
    D3BadKemP2KitsPlacedBudget.stageP2OverBadKemPreAtPlaced A lim spkKit kpkKit pkKit ikit st s0 s
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr ctBytes msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame ⊢
    spkKit.storeAt spkStorePtr stSpk ∗
      kpkKit.storeAt kyberStorePtr stKpk ∗
      pkKit.storeAt preKeyStorePtr stPk ∗
      D3BadKemP2KitsPlacedBudget.prevSessionsEmptyAt A coroPtr g ∗
      sessionStateReprAt A.repAlloc (coroPtr + 248#64) recG sess ∗ cells (coroPtr + 592#64) 6 ∗
      ((coroPtr + 704#64) ↦₈ b_2c0) ∗ ((coroPtr + 912#64) ↦₈ b_390) ∗
      cells (coroPtr + 920#64) 8 ∗ cells (coroPtr + 984#64) 4 ∗
      cells (coroPtr + 1016#64) 6 ∗ cells (coroPtr + 1128#64) 4 ∗
      ((coroPtr + 1160#64) ↦₆₄ u_488) ∗ ((coroPtr + 1200#64) ↦₈ b_4b0) ∗
      memRegion (coroPtr + 1201#64) 64 ∗
      ((coroPtr + 1265#64) ↦₈ b_4f1) ∗ ((coroPtr + 1266#64) ↦₈ b_4f2) ∗
      cells (coroPtr + 1272#64) 2 ∗
      ((msgPtr + 120#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗ ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 160#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 168#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
      ((msgPtr + 236#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 240#64) ↦₈ 4#8) ∗
      ((sp + 144#64) ↦₆₄ u_90) ∗ ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗
      ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ u_a8) ∗
      ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗ ((sp + 184#64) ↦₆₄ u_b8) ∗
      ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 200#64) ↦₆₄ outPtr) ∗
      ((sp + 208#64) ↦₆₄ u_d0) ∗
      memRegion (sp + 624#64) 9 ∗ memRegion (sp + 880#64) 36 ∗
      memRegion (sp + 944#64) 8 ∗ memRegion (sp + 992#64) 368 ∗
      cells (sp + 2352#64) 8 ∗ memRegion (sp + 2704#64) 65 ∗
      decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
      memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim st s ∗ stackAt sp stk ∗
      D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame A ikit
        sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
        v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame := by
  dsimp only [D3BadKemP2KitsPlacedBudget.stageP2OverBadKemPreAtPlaced,
    D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame, p2CoroScratchTailAt, p2BadKemMsgFieldsAt]
  rw [← p2_coro398_cells8_4_eq_96 coroPtr,
      ← p2_coro4f8_2cells_328_eq_344 coroPtr,
      ← p2_sp3b0_8_40_eq_48 sp,
      p2_memRegion_a90_288_split_65_223 sp]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. Substage 4→5 Spatial Bridges on Bad-KEM (`[LibsignalPlacement]`) -/

theorem p2_badKem_sub4_to_sub5_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    {ikit : IdentityStoreSpec A.repAlloc b}
    (skit : IdentitySelfStoreSpec ikit)
    (st : M.σ) (s0 s : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0' : BitVec 64)
    (inp : AcceptKeysInput) (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (spkBPk : SignalPqxdh.Bytes)
    (spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
    (hhdr : inp.hdr = hdr) (hspk_pub : bytesToBv8 spkBPk = spkPubBytes)
    (hspk_priv : bytesToBv8 inp.spkBSk = clampBv8List spkPrivBytes)
    (hpq_priv : bytesToBv8 inp.pqspkBSk = kyberPrivBytes)
    (hopk_tag : opkPresentTag inp.opkBSk? = opkOptTag8 (hdrOpkIdBv? hdr))
    (hkyber_priv_len : kyberPrivBytes.length = 3168) :
    spkKit.storeAt spkStorePtr stSpk' ∗ kpkKit.storeAt kyberStorePtr stKpk' ∗
      pkKit.storeAt preKeyStorePtr stPk' ∗
      A.live idKpFutPtr skit.kpBoxSize 8 ∗ skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
      (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
      (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
      sessionRecordEmptyHeaderAt (coroPtr + 224#64) ∗
      memRegion (coroPtr + 256#64) 336 ∗ cells (coroPtr + 592#64) 6 ∗
      ((coroPtr + 704#64) ↦₈ b_2c0) ∗ ((coroPtr + 912#64) ↦₈ b_390) ∗
      ((coroPtr + 920#64) ↦ₛ spkPubBytes) ∗ ((coroPtr + 952#64) ↦ₛ clampBv8List spkPrivBytes) ∗
      ((coroPtr + 984#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 992#64) ↦₆₄ 1568#64) ∗
      ((coroPtr + 1000#64) ↦₆₄ skBuf) ∗ ((coroPtr + 1008#64) ↦₆₄ 3168#64) ∗
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
      ((coroPtr + 1160#64) ↦₆₄ (msgPtr + 144#64)) ∗
      ((coroPtr + 1200#64) ↦₈ opkOptTag8 (hdrOpkIdBv? hdr)) ∗
      ((coroPtr + 1201#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 1233#64) ↦ₛ opkSkBytes) ∗
      ((coroPtr + 1265#64) ↦₈ 1#8) ∗ ((coroPtr + 1266#64) ↦₈ b_4f2) ∗
      cells (coroPtr + 1272#64) 2 ∗
      ((msgPtr + 120#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗ ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 160#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 168#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
      ((msgPtr + 236#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 240#64) ↦₈ 4#8) ∗
      ((sp + 144#64) ↦₆₄ v90) ∗ ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗
      ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ v_a8') ∗
      ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗ ((sp + 184#64) ↦₆₄ v_b8') ∗
      ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 200#64) ↦₆₄ outPtr) ∗ ((sp + 208#64) ↦₆₄ v_d0') ∗
      memRegion (sp + 624#64) 9 ∗ memRegion (sp + 880#64) 36 ∗
      memRegion (sp + 944#64) 8 ∗ memRegion (sp + 992#64) 368 ∗
      cells (sp + 2352#64) 8 ∗ memRegion (sp + 2704#64) 65 ∗
      decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
      memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp stk ∗
      D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame A ikit
        sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
        v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame ⊢
    ∃∗ u_b90 : BitVec 64, ∃∗ b_b98 : BitVec 8,
      A.live idKpFutPtr skit.kpBoxSize 8 ∗ skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
      ikit.identityAt idStorePtr stId ∗
      ((coroPtr + 920#64) ↦ₛ bytesToBv8 spkBPk) ∗ ((coroPtr + 952#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
      ((coroPtr + 984#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 992#64) ↦₆₄ 1568#64) ∗
      ((coroPtr + 1000#64) ↦₆₄ skBuf) ∗ ((coroPtr + 1008#64) ↦₆₄ 3168#64) ∗
      ((coroPtr + 1128#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 1136#64) ↦₆₄ remoteAddrPtr) ∗
      ((coroPtr + 1144#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 1160#64) ↦₆₄ (msgPtr + 144#64)) ∗
      cells (coroPtr + 1272#64) 2 ∗ ((coroPtr + 1200#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
      ((coroPtr + 1201#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 1233#64) ↦ₛ opkSkBytes) ∗
      ((coroPtr + 1265#64) ↦₈ 1#8) ∗ memRegion (coroPtr + 1624#64) 298 ∗ memRegion (coroPtr + 1944#64) 64 ∗
      ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗ ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗
      ((msgPtr + 152#64) ↦₆₄ BitVec.ofNat 64 ctBytes.length) ∗
      ((msgPtr + 168#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((msgPtr + 200#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
      (skBuf ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
      ((skBuf + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗ (ctBufPtr ↦ₛ ctBytes) ∗
      protocolAddressAt A.repAlloc gMe localAddrPtr ∗ protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
      ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗
      ((sp + 168#64) ↦₆₄ v_a8') ∗ ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗
      ((sp + 184#64) ↦₆₄ v_b8') ∗ ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 208#64) ↦₆₄ v_d0') ∗
      memRegion (sp + 968#64) 7 ∗ memRegion (sp + 992#64) 344 ∗
      cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗ cells (sp + 2016#64) 4 ∗
      cells (sp + 2352#64) 8 ∗ cells (sp + 2704#64) 8 ∗
      ((fp + -128#64) ↦₆₄ u_b90) ∗ ((fp + -120#64) ↦₈ b_b98) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp stk ∗
      p2Sub5FramePlaced A.repAlloc spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
        remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
        msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
        stSpk' stKpk' stPk' Frame := by
  rw [← hopk_tag, ← hhdr, ← hspk_pub, ← hspk_priv, ← hpq_priv]
  dsimp only [D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame, p2Sub5FramePlaced,
    RustCliAllocBudget.repAlloc]
  simp only [BitVec.reduceNeg]
  rw [p2_pointsToBytes_split_head skBuf (bytesToBv8 inp.pqspkBSk) (by rw [hpq_priv]; omega),
      p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt,
      p2_sp3b8_40_split sp, p2_memRegion_3e0_split_344_24 sp,
      p2_memRegion_a90_65_eq_cells8_1 sp, p2_fp80_9_split fp]
  sep_norm
  refine Entails.sepExists_elim fun u_b90 => Entails.sepExists_elim fun b_b98 =>
    Entails.sepExists_right u_b90 (Entails.sepExists_right b_b98 ?_)
  exact Entails.of_eq (by sep_ac_rfl)

theorem p2_over_badKem_sub4_to_sub5_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    {ikit : IdentityStoreSpec A.repAlloc b}
    (skit : IdentitySelfStoreSpec ikit)
    (st : M.σ) (s0 s : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0' : BitVec 64)
    (inp : AcceptKeysInput) (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (spkBPk : SignalPqxdh.Bytes)
    (spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp)
    (hhdr : inp.hdr = hdr) (hspk_pub : bytesToBv8 spkBPk = spkPubBytes)
    (hspk_priv : bytesToBv8 inp.spkBSk = clampBv8List spkPrivBytes)
    (hpq_priv : bytesToBv8 inp.pqspkBSk = kyberPrivBytes)
    (hopk_tag : opkPresentTag inp.opkBSk? = opkOptTag8 (hdrOpkIdBv? hdr))
    (hkyber_priv_len : kyberPrivBytes.length = 3168) :
    spkKit.storeAt spkStorePtr stSpk' ∗ kpkKit.storeAt kyberStorePtr stKpk' ∗
      pkKit.storeAt preKeyStorePtr stPk' ∗
      A.live idKpFutPtr skit.kpBoxSize 8 ∗ skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
      (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
      (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
      D3BadKemP2KitsPlacedBudget.prevSessionsEmptyAt A coroPtr g ∗
      sessionStateReprAt A.repAlloc (coroPtr + 248#64) recG sess ∗ cells (coroPtr + 592#64) 6 ∗
      ((coroPtr + 704#64) ↦₈ b_2c0) ∗ ((coroPtr + 912#64) ↦₈ b_390) ∗
      ((coroPtr + 920#64) ↦ₛ spkPubBytes) ∗ ((coroPtr + 952#64) ↦ₛ clampBv8List spkPrivBytes) ∗
      ((coroPtr + 984#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 992#64) ↦₆₄ 1568#64) ∗
      ((coroPtr + 1000#64) ↦₆₄ skBuf) ∗ ((coroPtr + 1008#64) ↦₆₄ 3168#64) ∗
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
      ((coroPtr + 1160#64) ↦₆₄ (msgPtr + 144#64)) ∗
      ((coroPtr + 1200#64) ↦₈ opkOptTag8 (hdrOpkIdBv? hdr)) ∗
      ((coroPtr + 1201#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 1233#64) ↦ₛ opkSkBytes) ∗
      ((coroPtr + 1265#64) ↦₈ 1#8) ∗ ((coroPtr + 1266#64) ↦₈ b_4f2) ∗
      cells (coroPtr + 1272#64) 2 ∗
      ((msgPtr + 120#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗ ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 160#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 168#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
      ((msgPtr + 236#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 240#64) ↦₈ 4#8) ∗
      ((sp + 144#64) ↦₆₄ v90) ∗ ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗
      ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ v_a8') ∗
      ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗ ((sp + 184#64) ↦₆₄ v_b8') ∗
      ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 200#64) ↦₆₄ outPtr) ∗ ((sp + 208#64) ↦₆₄ v_d0') ∗
      memRegion (sp + 624#64) 9 ∗ memRegion (sp + 880#64) 36 ∗
      memRegion (sp + 944#64) 8 ∗ memRegion (sp + 992#64) 368 ∗
      cells (sp + 2352#64) 8 ∗ memRegion (sp + 2704#64) 65 ∗
      decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
      memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp stk ∗
      D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame A ikit
        sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
        v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame ⊢
    ∃∗ u_b90 : BitVec 64, ∃∗ b_b98 : BitVec 8,
      A.live idKpFutPtr skit.kpBoxSize 8 ∗ skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
      ikit.identityAt idStorePtr stId ∗
      ((coroPtr + 920#64) ↦ₛ bytesToBv8 spkBPk) ∗ ((coroPtr + 952#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
      ((coroPtr + 984#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 992#64) ↦₆₄ 1568#64) ∗
      ((coroPtr + 1000#64) ↦₆₄ skBuf) ∗ ((coroPtr + 1008#64) ↦₆₄ 3168#64) ∗
      ((coroPtr + 1128#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 1136#64) ↦₆₄ remoteAddrPtr) ∗
      ((coroPtr + 1144#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 1160#64) ↦₆₄ (msgPtr + 144#64)) ∗
      cells (coroPtr + 1272#64) 2 ∗ ((coroPtr + 1200#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
      ((coroPtr + 1201#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 1233#64) ↦ₛ opkSkBytes) ∗
      ((coroPtr + 1265#64) ↦₈ 1#8) ∗ memRegion (coroPtr + 1624#64) 298 ∗ memRegion (coroPtr + 1944#64) 64 ∗
      ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗ ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗
      ((msgPtr + 152#64) ↦₆₄ BitVec.ofNat 64 ctBytes.length) ∗
      ((msgPtr + 168#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((msgPtr + 200#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
      (skBuf ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
      ((skBuf + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗ (ctBufPtr ↦ₛ ctBytes) ∗
      protocolAddressAt A.repAlloc gMe localAddrPtr ∗ protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
      ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗
      ((sp + 168#64) ↦₆₄ v_a8') ∗ ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗
      ((sp + 184#64) ↦₆₄ v_b8') ∗ ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 208#64) ↦₆₄ v_d0') ∗
      memRegion (sp + 968#64) 7 ∗ memRegion (sp + 992#64) 344 ∗
      cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗ cells (sp + 2016#64) 4 ∗
      cells (sp + 2352#64) 8 ∗ cells (sp + 2704#64) 8 ∗
      ((fp + -128#64) ↦₆₄ u_b90) ∗ ((fp + -120#64) ↦₈ b_b98) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp stk ∗
      p2OverSub5FramePlaced A.repAlloc spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
        remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
        msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
        stSpk' stKpk' stPk' g recG sess Frame := by
  rw [← hopk_tag, ← hhdr, ← hspk_pub, ← hspk_priv, ← hpq_priv]
  dsimp only [D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame, p2OverSub5FramePlaced,
    D3BadKemP2KitsPlacedBudget.prevSessionsEmptyAt,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt,
    RustCliAllocBudget.repAlloc]
  simp only [BitVec.reduceNeg]
  rw [p2_pointsToBytes_split_head skBuf (bytesToBv8 inp.pqspkBSk) (by rw [hpq_priv]; omega),
      p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt,
      p2_sp3b8_40_split sp, p2_memRegion_3e0_split_344_24 sp,
      p2_memRegion_a90_65_eq_cells8_1 sp, p2_fp80_9_split fp]
  sep_norm
  refine Entails.sepExists_elim fun u_b90 => Entails.sepExists_elim fun b_b98 =>
    Entails.sepExists_right u_b90 (Entails.sepExists_right b_b98 ?_)
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Error Arms 1–3 Entailments and Arm 5 Payload Pull on Bad-KEM (`[LibsignalPlacement]`) -/

theorem p2_badKem_arm5_err_payload_pull_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 sf : State)
    (sp fp coroPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt
     v_330 v_388 errTag w2 w3 w4 w5 w6 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8)) (msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (S_spk S_kpk S_pk S_id : SepProp)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
      S_spk ∗ S_kpk ∗ S_pk ∗ S_id ∗
      D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim st s0 sf
        sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt
        v_330 v_388 hdr ctBytes msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk (pqxdhBadKemErrPayloadAt A.repAlloc errTag w2 w3 w4 ∗ Frame) ⊢
    speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
      pqxdhBadKemErrPayloadAt A.repAlloc errTag w2 w3 w4 ∗
      S_spk ∗ S_kpk ∗ S_pk ∗ S_id ∗
      D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim st s0 sf
        sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt
        v_330 v_388 hdr ctBytes msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk Frame := by
  dsimp only [D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced]
  exact Entails.of_eq (by sep_ac_rfl)

theorem p2_badKem_arm1_entails_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (st : M.σ) (s0 sf : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_b0 v_330 v_388 u_488 u_80 u_88 spkFutPtr : BitVec 64)
    (b_4b0 msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (e : spkKit.GetErr) (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    speErrAt spkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
      kpkKit.storeAt kyberStorePtr stKpk ∗ pkKit.storeAt preKeyStorePtr stPk ∗
      memRegion (coroPtr + 224#64) 368 ∗ cells (coroPtr + 592#64) 6 ∗
      ((coroPtr + 704#64) ↦₈ 1#8) ∗ ((coroPtr + 912#64) ↦₈ 1#8) ∗
      cells (coroPtr + 920#64) 8 ∗ cells (coroPtr + 984#64) 4 ∗
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
      ((coroPtr + 1160#64) ↦₆₄ u_488) ∗ ((coroPtr + 1200#64) ↦₈ b_4b0) ∗
      memRegion (coroPtr + 1201#64) 64 ∗
      ((coroPtr + 1265#64) ↦₈ 0#8) ∗ ((coroPtr + 1266#64) ↦₈ 1#8) ∗
      ((coroPtr + 1272#64) ↦₆₄ spkFutPtr) ∗ ((coroPtr + 1280#64) ↦₆₄ (b + spkKit.getFutVtOff)) ∗
      ((msgPtr + 120#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗ ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 160#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 168#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
      ((msgPtr + 236#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 240#64) ↦₈ 4#8) ∗
      ((sp + 144#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗
      ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ spkKit.getErr.w4 e) ∗
      ((sp + 176#64) ↦₆₄ v_b0) ∗ ((sp + 184#64) ↦₆₄ spkKit.getErr.w2 e) ∗
      ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 200#64) ↦₆₄ outPtr) ∗ ((sp + 208#64) ↦₆₄ spkKit.getErr.w3 e) ∗
      memRegion (sp + 624#64) 9 ∗ memRegion (sp + 880#64) 36 ∗
      memRegion (sp + 944#64) 8 ∗ memRegion (sp + 992#64) 368 ∗
      cells (sp + 2352#64) 8 ∗ cells (sp + 2704#64) 6 ∗ memRegion (sp + 2752#64) 17 ∗
      decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st sf ∗ stackAt sp stk ∗
      D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame A ikit
        sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
        v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame ⊢
    speErrAt spkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
      kpkKit.storeAt kyberStorePtr stKpk ∗ pkKit.storeAt preKeyStorePtr stPk ∗
      ikit.identityAt idStorePtr stId ∗
      D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim st s0 sf
        sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
        v_330 v_388 hdr ctBytes msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk Frame := by
  dsimp only [D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame,
    D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced,
    p2CoroScratchTailAt, p2BadKemMsgFieldsAt]
  refine p2_entails_frame_v1 (Entails.of_eq (p2_coro398_cells8_4_eq_96 coroPtr)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (pointsTo64_entails_memRegion (coroPtr + 1160#64) u_488) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro4b0_byte_64_entails_65 coroPtr b_4b0) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro4f8_words2_328_entails_344 coroPtr spkFutPtr (b + spkKit.getFutVtOff)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 u_88 (spkKit.getErr.w5 e) (coroPtr + 920#64)
      (coroPtr + 1266#64) (spkKit.getErr.w4 e) v_b0 (spkKit.getErr.w2 e) ctxPtr outPtr
      (spkKit.getErr.w3 e)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_8_40_eq_48 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err123_to_288 sp)) (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem p2_badKem_arm2_entails_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (st : M.σ) (s0 sf : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_b0 v_330 v_388 u_488 u_80 u_88 kyberFutPtr : BitVec 64)
    (b_4b0 msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8)) (spkRec : SignedPreKeyRecord)
    (spkPubBytes spkPrivBytes : List (BitVec 8))
    (hpub : spkPubBytes.length = 32) (hpriv : spkPrivBytes.length = 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (e : kpkKit.GetErr) (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    speErrAt kpkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
      kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
      pkKit.storeAt preKeyStorePtr stPk ∗
      memRegion (coroPtr + 224#64) 368 ∗ cells (coroPtr + 592#64) 6 ∗
      ((coroPtr + 704#64) ↦₈ 1#8) ∗ ((coroPtr + 912#64) ↦₈ 1#8) ∗
      ((coroPtr + 920#64) ↦ₛ spkPubBytes) ∗ ((coroPtr + 952#64) ↦ₛ clampBv8List spkPrivBytes) ∗
      cells (coroPtr + 984#64) 4 ∗
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
      ((coroPtr + 1160#64) ↦₆₄ u_488) ∗ ((coroPtr + 1200#64) ↦₈ b_4b0) ∗
      memRegion (coroPtr + 1201#64) 64 ∗
      ((coroPtr + 1265#64) ↦₈ 0#8) ∗ ((coroPtr + 1266#64) ↦₈ 1#8) ∗
      ((coroPtr + 1272#64) ↦₆₄ kyberFutPtr) ∗ ((coroPtr + 1280#64) ↦₆₄ (b + kpkKit.getFutVtOff)) ∗
      ((msgPtr + 120#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗ ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 160#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 168#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
      ((msgPtr + 236#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 240#64) ↦₈ 4#8) ∗
      ((sp + 144#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗
      ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
      ((sp + 176#64) ↦₆₄ v_b0) ∗ ((sp + 184#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
      ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 200#64) ↦₆₄ outPtr) ∗ ((sp + 208#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
      memRegion (sp + 624#64) 9 ∗ memRegion (sp + 880#64) 36 ∗
      memRegion (sp + 944#64) 8 ∗ memRegion (sp + 992#64) 368 ∗
      cells (sp + 2352#64) 8 ∗ cells (sp + 2704#64) 6 ∗ memRegion (sp + 2752#64) 17 ∗
      decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st sf ∗ stackAt sp stk ∗
      D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame A ikit
        sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
        v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame ⊢
    speErrAt kpkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
      kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
      pkKit.storeAt preKeyStorePtr stPk ∗ ikit.identityAt idStorePtr stId ∗
      D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim st s0 sf
        sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
        v_330 v_388 hdr ctBytes msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk Frame := by
  dsimp only [D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame,
    D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced,
    p2CoroScratchTailAt, p2BadKemMsgFieldsAt]
  refine p2_entails_frame_v1
    (p2_coro398_bytes_cells4_entails_96 coroPtr spkPubBytes (clampBv8List spkPrivBytes)
      hpub (clampBv8List_length hpriv)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (pointsTo64_entails_memRegion (coroPtr + 1160#64) u_488) (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro4b0_byte_64_entails_65 coroPtr b_4b0) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro4f8_words2_328_entails_344 coroPtr kyberFutPtr (b + kpkKit.getFutVtOff)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 u_88 (kpkKit.getErr.w5 e) (coroPtr + 920#64)
      (coroPtr + 1266#64) (kpkKit.getErr.w4 e) v_b0 (kpkKit.getErr.w2 e) ctxPtr outPtr
      (kpkKit.getErr.w3 e)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_8_40_eq_48 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err123_to_288 sp)) (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem p2_badKem_arm3_entails_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (st : M.σ) (s0 sf : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_b0 v_330 v_388 u_80 u_88 pkBuf skBuf opkFutPtr v90 : BitVec 64)
    (b_4b0 msgVerByte : BitVec 8)
    (opkId opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
    (spkPubBytes spkPrivBytes : List (BitVec 8))
    (hpub : spkPubBytes.length = 32) (hpriv : spkPrivBytes.length = 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (e : pkKit.GetErr) (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    speErrAt pkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
      kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
      pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
      memRegion (coroPtr + 224#64) 368 ∗ cells (coroPtr + 592#64) 6 ∗
      ((coroPtr + 704#64) ↦₈ 1#8) ∗ ((coroPtr + 912#64) ↦₈ 1#8) ∗
      ((coroPtr + 920#64) ↦ₛ spkPubBytes) ∗ ((coroPtr + 952#64) ↦ₛ clampBv8List spkPrivBytes) ∗
      ((coroPtr + 984#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 992#64) ↦₆₄ 1568#64) ∗
      ((coroPtr + 1000#64) ↦₆₄ skBuf) ∗ ((coroPtr + 1008#64) ↦₆₄ 3168#64) ∗
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
      ((coroPtr + 1160#64) ↦₆₄ (msgPtr + 144#64)) ∗ ((coroPtr + 1200#64) ↦₈ b_4b0) ∗
      memRegion (coroPtr + 1201#64) 64 ∗
      ((coroPtr + 1265#64) ↦₈ 0#8) ∗ ((coroPtr + 1266#64) ↦₈ 1#8) ∗
      ((coroPtr + 1272#64) ↦₆₄ opkFutPtr) ∗ ((coroPtr + 1280#64) ↦₆₄ (b + pkKit.getFutVtOff)) ∗
      ((msgPtr + 120#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗ ((msgPtr + 124#64) ↦₃₂ opkIdWord) ∗
      ((msgPtr + 144#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 160#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 168#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
      ((msgPtr + 236#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 240#64) ↦₈ 4#8) ∗
      ((sp + 144#64) ↦₆₄ v90) ∗ ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗
      ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ pkKit.getErr.w4 e) ∗
      ((sp + 176#64) ↦₆₄ v_b0) ∗ ((sp + 184#64) ↦₆₄ pkKit.getErr.w2 e) ∗
      ((sp + 192#64) ↦₆₄ ctxPtr) ∗ ((sp + 200#64) ↦₆₄ outPtr) ∗ ((sp + 208#64) ↦₆₄ pkKit.getErr.w3 e) ∗
      memRegion (sp + 624#64) 9 ∗ memRegion (sp + 880#64) 36 ∗
      memRegion (sp + 944#64) 8 ∗ memRegion (sp + 992#64) 368 ∗
      cells (sp + 2352#64) 8 ∗ cells (sp + 2704#64) 6 ∗ memRegion (sp + 2752#64) 17 ∗
      decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st sf ∗ stackAt sp stk ∗
      D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame A ikit
        sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
        v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame ⊢
    speErrAt pkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
      kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
      pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
      ikit.identityAt idStorePtr stId ∗
      D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim st s0 sf
        sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
        v_330 v_388 hdr ctBytes msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        gMe gPeer stk Frame := by
  dsimp only [D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame,
    D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced,
    p2CoroScratchTailAt, p2BadKemMsgFieldsAt]
  refine p2_entails_frame_v1
    (p2_coro398_bytes_words4_entails_96 coroPtr spkPubBytes (clampBv8List spkPrivBytes)
      pkBuf 1568#64 skBuf 3168#64 hpub (clampBv8List_length hpriv)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (pointsTo64_entails_memRegion (coroPtr + 1160#64) (msgPtr + 144#64))
    (by sep_focus) ?_
  refine p2_entails_frame_v1 (p2_coro4b0_byte_64_entails_65 coroPtr b_4b0) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_coro4f8_words2_328_entails_344 coroPtr opkFutPtr (b + pkKit.getFutVtOff)) (by sep_focus) ?_
  refine p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 u_88 v90 (coroPtr + 920#64)
      (coroPtr + 1266#64) (pkKit.getErr.w4 e) v_b0 (pkKit.getErr.w2 e) ctxPtr outPtr
      (pkKit.getErr.w3 e)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_8_40_eq_48 sp)) (by sep_focus) ?_
  refine p2_entails_frame_v1 (Entails.of_eq (p2_a90_err123_to_288 sp)) (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget
