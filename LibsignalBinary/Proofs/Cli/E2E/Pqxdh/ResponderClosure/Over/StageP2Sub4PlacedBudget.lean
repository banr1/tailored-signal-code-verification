/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4Placed
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget

/-!
# Budget-Threaded Placed Stage P2 Over-Path Normal-Exit Postcondition

Defines budget-threaded `[LibsignalPlacement]` forms of `prevArchived1AtPlaced` and
`p2OverOkPostAtPlaced` at `+0x1778`, together with `A.atState` bridge equalities.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4PlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (SessionState)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost protocolAddressAt sessionStateAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  IdentityStoreSpec KyberPreKeyStoreSpec PreKeyStoreSpec SignedPreKeyStoreSpec
)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.E2E.Pqxdh.Initiator (HandshakeHdr)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  decryptPrekeySavedRegsAt processPrekeyActive10At
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2 (
  clearPending clearPendingGhost
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  hdrOpkIdBv? opkOptTag32 p2CoroScratchTailAt p2MsgFieldsAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  prevArchived1At prevArchived1At_eq
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (retagSignedPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (retagKyberPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (retagPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (retagIdentityStore)

/-- Placed 1-element `previous_sessions` predicate at `coroPtr + 0xe0` over `A.repAlloc`. -/
noncomputable abbrev prevArchived1AtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (coroPtr : BitVec 64)
    (recG : SessionGhost) (sess : Session (List (BitVec 8))) : SepProp :=
  prevArchived1At A.repAlloc coroPtr recG sess

theorem prevArchived1At_placed_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (coroPtr : BitVec 64)
    (recG : SessionGhost) (sess : Session (List (BitVec 8))) :
    (∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
      ⌜prevCap' ≠ 0#64⌝ ∗
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2.prevVecAt
        A.repAlloc (coroPtr + 0xe0#64) prevCap' prevPtr'
        [encSessionMem (clearPendingGhost recG) (clearPending sess)]) =
    prevArchived1AtPlaced A coroPtr recG sess :=
  prevArchived1At_eq A.repAlloc coroPtr recG sess

theorem prevArchived1At_atState_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (coroPtr : BitVec 64) (recG : SessionGhost) (sess : Session (List (BitVec 8))) :
    prevArchived1At (A.atState lim st s) coroPtr recG sess =
      prevArchived1At A.repAlloc coroPtr recG sess :=
  rfl

/-- Budget-threaded placed Stage P2 Over-path normal-exit postcondition at `+0x1778`. -/
noncomputable def p2OverOkPostAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (b : BitVec 64)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (st : M.σ) (s0 sf : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388 : BitVec 64)
    (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (G_bob : SessionGhost) (st_bob : SessionState (List (BitVec 8)))
    (hdr : HandshakeHdr) (msgVerByte b_2c0 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  spkKit.storeAt spkStorePtr stSpk' ∗
  kpkKit.storeAt kyberStorePtr stKpk' ∗
  pkKit.storeAt preKeyStorePtr stPk' ∗
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  prevArchived1At A.repAlloc coroPtr recG sess ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G_bob st_bob ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x298#64) ↦₆₄ ((opkOptTag32 (hdrOpkIdBv? hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32))) ∗
  ((coroPtr + 0x2a0#64) ↦₆₄ ((kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64)) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
  memRegion (coroPtr + 0x398#64) 96 ∗
  processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
  memRegion (coroPtr + 0x488#64) 8 ∗
  memRegion (coroPtr + 0x4b0#64) 65 ∗
  ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
  ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2MsgFieldsAt msgPtr ctBufPtr hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A.repAlloc gMe localAddrPtr ∗
  protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
  ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
  ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((sp + 0x90#64) ↦₆₄ v_388) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
  ((sp + 0xa8#64) ↦₆₄ v_330) ∗
  ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗
  ((sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
  memRegion (sp + 0xbc#64) 4 ∗
  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
  memRegion (sp + 0x270#64) 9 ∗
  memRegion (sp + 0x370#64) 36 ∗
  ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
  ((sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
  ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
  ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
  ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
  ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x3e0#64) 368 ∗
  cells (sp + 0x560#64) 4 ∗
  cells (sp + 0x6a0#64) 4 ∗
  cells (sp + 0x7e0#64) 4 ∗
  cells (sp + 0x930#64) 8 ∗
  memRegion (sp + 0xa90#64) 288 ∗
  memRegion (fp + 0xffffffffffffff80#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  memRegion outPtr 48 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool lim st sf ∗
  stackAt sp stk ∗
  Frame

theorem p2OverOkPostAtPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (b : BitVec 64)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (st : M.σ) (s0 sf : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388 : BitVec 64)
    (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (G_bob : SessionGhost) (st_bob : SessionState (List (BitVec 8)))
    (hdr : HandshakeHdr) (msgVerByte b_2c0 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    p2OverOkPostAtPlaced A lim b spkKit kpkKit pkKit ikit st s0 sf
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
      recG sess G_bob st_bob hdr msgVerByte b_2c0
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk' stKpk' stPk' stId gMe gPeer stk Frame =
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2OverOkPostAtPlaced
      (A.atState lim st sf) b
      (retagSignedPreKeyStore spkKit)
      (retagKyberPreKeyStore kpkKit)
      (retagPreKeyStore pkKit)
      (retagIdentityStore ikit)
      s0
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
      recG sess G_bob st_bob hdr msgVerByte b_2c0
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk' stKpk' stPk' stId gMe gPeer stk Frame :=
  rfl

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4PlacedBudget
