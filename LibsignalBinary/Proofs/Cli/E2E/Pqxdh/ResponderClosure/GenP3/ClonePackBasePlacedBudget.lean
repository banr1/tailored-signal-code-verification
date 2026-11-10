/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTailPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePack
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackBase
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackBasePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Placed Segment 5 Packing Helpers

Budget-threaded (`RustCliAllocBudget M`) spatial frame `packRestFramePlacedBudget`, Stage P3
clone exit postconditions (`genP3PostPlacedBudget`), and `VmPreserved` pool-transport entailments
across `+0x1bac → +0x1cd4 / +0x1e04`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackBasePlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (PublicKey SessionState SignalMessage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (vecBuf vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost protocolAddressAt sessionStateAt signalMessageAt
)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  OptSenderChainInline bytes104OfW6Q optSenderChainHeap
)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (OptKybClone OptPendClone)
open CryptoVerification.SignalSession.Coins (coinsAtPlaced)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (GenP3J4Witness genP3SpillAll)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4 (
  packDstSlotsWrittenAt packRestFramePlaced packSrcSlotsAt packed_entails_genP3PostSpatialPlaced
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  genP3PostEqPlaced genP3PostNePlaced genP3PostPlaced genP3PostSpatialPlaced
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)

/-! ## 1. Budget-Threaded Segment 5 Frame & Stage-P3 Clone Postconditions -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` untouched spatial frame threaded across
    `pack_eq_placed_wp` / `pack_ne_placed_wp`. -/
def packRestFramePlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8))) (w : GenP3J4Witness)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
  A.pool lim stB s ∗
  stackAt sp chainCloneStack ∗
  memRegion (sp + 0x3e0#64) 104 ∗
  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
  ((sp + 0x98#64) ↦₆₄ 32#64) ∗
  protocolAddressAt A.repAlloc rem remAddrPtr ∗
  protocolAddressAt A.repAlloc loc locAddrPtr ∗
  signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
  memRegion (sp + 0x270#64) 48 ∗
  coinsAtPlaced cur rest ∗
  lsLogOff ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
  vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
  vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
  vecU8Buf A.repAlloc 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
  optSenderChainHeap A.repAlloc w.sender' st.senderChain ∗
  vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) (BitVec.ofNat 64 st.receiverChains.length)
    w.newRcPtr (w.chains'.zip st.receiverChains) ∗
  OptPendClone A.repAlloc recG.pending w.pendCap' w.pendPtr' ∗
  OptKybClone A.repAlloc recG.kyber w.kybCap' w.kybPtr' ∗
  vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.alice.bytes.length) w.newAlicePtr recG.alice.bytes ∗
  vecU8Buf A.repAlloc (BitVec.ofNat 64 st.pqRatchetState.length) w.newPqPtr st.pqRatchetState

theorem packRestFramePlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8))) (w : GenP3J4Witness)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) :
    packRestFramePlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      rest recG st w rem loc msgG msg s =
    packRestFramePlaced (A.atState lim stB s) sp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur rest recG st w rem loc msgG msg :=
  rfl

theorem packRestFramePlacedBudget_eq_of_vmPreserved [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8))) (w : GenP3J4Witness)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    {s₁ s₂ : State} (hvm : VmPreserved s₁ s₂) :
    packRestFramePlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      rest recG st w rem loc msgG msg s₂ =
    packRestFramePlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      rest recG st w rem loc msgG msg s₁ := by
  rw [packRestFramePlacedBudget_eq_atState, packRestFramePlacedBudget_eq_atState,
    A.atState_eq_of_vmPreserved lim stB hvm]

/-- Budget-threaded relocatable `[LibsignalPlacement]` `genP3PostSpatial`. -/
def genP3PostSpatialPlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
    (∃∗ G₁ : SessionGhost, ⌜CloneRel recG G₁⌝ ∗ sessionStateAt A.repAlloc (sp + 0xa90#64) G₁ st) ∗
    protocolAddressAt A.repAlloc rem remAddrPtr ∗
    protocolAddressAt A.repAlloc loc locAddrPtr ∗
    signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
    memRegion (sp + 0x270#64) 48 ∗
    coinsAtPlaced cur rest ∗
    lsLogOff ∗
    stackAt sp rootStack ∗
    A.pool lim stB s ∗
    memRegion (sp + 0x3e0#64) 104 ∗
    ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
    ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
    ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
    ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
    ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
    ((sp + 0x3ac#64) ↦₈ 3#8) ∗
    genP3SpillAll sp

theorem genP3PostSpatialPlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) :
    genP3PostSpatialPlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg s =
    genP3PostSpatialPlaced (A.atState lim stB s) sp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg :=
  rfl

theorem genP3PostSpatialPlacedBudget_eq_of_vmPreserved [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    {s₁ s₂ : State} (hvm : VmPreserved s₁ s₂) :
    genP3PostSpatialPlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg s₂ =
    genP3PostSpatialPlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg s₁ := by
  rw [genP3PostSpatialPlacedBudget_eq_atState, genP3PostSpatialPlacedBudget_eq_atState,
    A.atState_eq_of_vmPreserved lim stB hvm]

/-- Budget-threaded relocatable `[LibsignalPlacement]` `genP3PostEq` at
    `dpClosureEntryM3Placed + 0x1cd4#64`. -/
def genP3PostEqPlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ⌜s.sp = sp ∧ s.readReg64 .x0 = sp + 0x270#64 ∧ s.readReg64 .x1 = sp + 0xa90#64 ∧
    s.readReg64 .x2 = remAddrPtr ∧ s.readReg64 .x3 = locAddrPtr ∧ s.readReg64 .x4 = whisperMsgPtr ∧
    s.readReg64 .x5 = 3#64 ∧ s.readReg64 .x6 = 0#64 ∧ s.readReg64 .x19 = coroPtr ∧
    s.readReg64 .x24 = sp + 0x370#64 ∧ s.readReg64 .x27 = ctxPtr ∧ s.readReg64 .x29 = fp⌝ ∗
    genP3PostSpatialPlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg s

theorem genP3PostEqPlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) :
    genP3PostEqPlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg s =
    genP3PostEqPlaced (A.atState lim stB s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s :=
  rfl

/-- Budget-threaded relocatable `[LibsignalPlacement]` `genP3PostNe` at
    `dpClosureEntryM3Placed + 0x1e04#64`. -/
def genP3PostNePlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ⌜s.sp = sp ∧ s.readReg64 .x9 = msgVer.setWidth 64 ∧ s.readReg64 .x19 = coroPtr ∧
    s.readReg64 .x24 = sp + 0x370#64 ∧ s.readReg64 .x27 = ctxPtr ∧ s.readReg64 .x29 = fp⌝ ∗
    genP3PostSpatialPlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg s

theorem genP3PostNePlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) :
    genP3PostNePlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg s =
    genP3PostNePlaced (A.atState lim stB s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s :=
  rfl

/-- Budget-threaded relocatable `[LibsignalPlacement]` `genP3Post`. -/
def genP3PostPlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  if st.version = msgVer then
    genP3PostEqPlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg s
  else
    genP3PostNePlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg s

theorem genP3PostPlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) :
    genP3PostPlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg s =
    genP3PostPlaced (A.atState lim stB s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s :=
  rfl

/-! ## 2. Spatial Entailments Into `genP3PostSpatialPlacedBudget` -/

/-- Budget-threaded `[LibsignalPlacement]` counterpart of `packed_entails_genP3PostSpatialPlaced`
    at a single machine state `s`. -/
theorem packed_entails_genP3PostSpatialPlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (w : GenP3J4Witness) (w20 : BitVec 32)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State)
    (h_loc_deser : PublicKey.deserialize recG.localIk.bytes = .ok st.localIdentity.publicKey)
    (h_rem_deser : match st.remoteIdentity with
      | none => recG.remoteIk.bytes = []
      | some ik => PublicKey.deserialize recG.remoteIk.bytes = .ok ik.publicKey)
    (h_pend_some : recG.pending.isSome = st.pendingPreKey)
    (h_reg_len : recG.regIds.length = 8)
    (h_loc_len : recG.localIk.bytes.length = 33)
    (h_rem_len : st.remoteIdentity.isSome → recG.remoteIk.bytes.length = 33)
    (hreg_eq : recG.regIds = unpack32 w.regW0 ++ unpack32 w.regW1)
    (hchains_len : w.chains'.length = st.receiverChains.length)
    (hsc_inl : OptSenderChainInline w.sender' st.senderChain
      (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)) :
    ((packSrcSlotsAt sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
        packDstSlotsWrittenAt sp recG st w w20) ∗
      packRestFramePlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
        cur rest recG st w rem loc msgG msg s) ⊢
      genP3PostSpatialPlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
        cur msgVer rest recG st rem loc msgG msg s := by
  rw [packRestFramePlacedBudget_eq_atState, genP3PostSpatialPlacedBudget_eq_atState]
  exact packed_entails_genP3PostSpatialPlaced (A.atState lim stB s) sp coroPtr ctxPtr remAddrPtr
    locAddrPtr whisperMsgPtr cur msgVer rest recG st w w20 rem loc msgG msg
    h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len hreg_eq hchains_len hsc_inl

/-- `VmPreserved`-transported `[LibsignalPlacement]` spatial entailment across Segment 5's
    pure register/stack packing steps (`s → s1` with `VmPreserved s s1`). -/
theorem packed_entails_genP3PostSpatialPlacedBudget_of_vmPreserved [LibsignalPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (w : GenP3J4Witness) (w20 : BitVec 32)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    {s s1 : State} (hvm : VmPreserved s s1)
    (h_loc_deser : PublicKey.deserialize recG.localIk.bytes = .ok st.localIdentity.publicKey)
    (h_rem_deser : match st.remoteIdentity with
      | none => recG.remoteIk.bytes = []
      | some ik => PublicKey.deserialize recG.remoteIk.bytes = .ok ik.publicKey)
    (h_pend_some : recG.pending.isSome = st.pendingPreKey)
    (h_reg_len : recG.regIds.length = 8)
    (h_loc_len : recG.localIk.bytes.length = 33)
    (h_rem_len : st.remoteIdentity.isSome → recG.remoteIk.bytes.length = 33)
    (hreg_eq : recG.regIds = unpack32 w.regW0 ++ unpack32 w.regW1)
    (hchains_len : w.chains'.length = st.receiverChains.length)
    (hsc_inl : OptSenderChainInline w.sender' st.senderChain
      (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)) :
    ((packSrcSlotsAt sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
        packDstSlotsWrittenAt sp recG st w w20) ∗
      packRestFramePlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
        cur rest recG st w rem loc msgG msg s) ⊢
      genP3PostSpatialPlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
        cur msgVer rest recG st rem loc msgG msg s1 := by
  rw [genP3PostSpatialPlacedBudget_eq_of_vmPreserved A lim stB sp coroPtr ctxPtr remAddrPtr
    locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hvm]
  exact packed_entails_genP3PostSpatialPlacedBudget A lim stB sp coroPtr ctxPtr remAddrPtr
    locAddrPtr whisperMsgPtr cur msgVer rest recG st w w20 rem loc msgG msg s
    h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len hreg_eq hchains_len hsc_inl

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackBasePlacedBudget
