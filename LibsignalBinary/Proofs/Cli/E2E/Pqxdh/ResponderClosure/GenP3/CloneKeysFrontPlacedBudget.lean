/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Placed Segment 1: Keys & Sender Chain (Block `518`)

Deterministic allocation-event trace `cloneKeysFrontEvents` / `CloneKeysFrontEnv`, budget-threaded
junction predicates (`genP3PrePlacedBudget`, `genP3J1PlacedBudget`..`genP3J4PlacedBudget`), and
Segment 1 proofs (`cloneKeysFront_vregs_placed_ok`, `+0x1778 → +0x19b0`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (SenderChain SessionState SignalMessage)
open CryptoVerification (LibsignalPlacement lsMemcpySym lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (GenP3FrontSpill GenP3J1Witness GenP3J2Witness GenP3J3Witness GenP3J4Witness OptSenderChainCloneRel genP3ChainsSpillScratch genP3J1Placed genP3J2Placed genP3J3Placed genP3J4Placed genP3PendSpillScratch genP3SenderInlineWords genP3SpillAll genP3TailSpillScratch)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (dpClosureEntryM3Placed genP3CallFramePlaced genP3PrePlaced)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalSessionRepr (chainAt vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (OptSenderChainInline bytes104OfW6Q optSenderChainHeap)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (OptKybClone OptPendClone stackAt_chainClone_eq_alloc)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost SignalMessageGhost optSenderChainAt sessionStateAt)
open CryptoVerification.RustHeap (allocHookStack vecBuf vecU8At vecU8Buf)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
  allocMemcpyVmSpec fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
  subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
  subroutine_ok_sessionShimBudget_of_rustAllocShimVm
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  SenderChainClone3OkPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudgetAux (
  optSenderChainCloneEvents seg_locId_placed_budget_ok seg_remId_placed_budget_ok
  seg_rootKey_placed_budget_ok seg_senderChain_placed_budget_ok sepWPp_bind_frame_any
  sepWPp_done_any sepWPp_exists_elim_any sepWPp_pure_elim_any sepWPp_weaken_frame_any
  sepWPp_weaken_pre_any
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Deterministic `AllocEvent` Trace & Envelope for `CloneKeysFront` -/

/-- Exact allocator envelope for optional sender-chain clone (`optSenderChainCloneEvents`). -/
def OptSenderChainCloneEnv (scG : Option CryptoVerification.LibsignalTripleRatchetRepr.SenderChainGhost)
    (scM : Option SenderChain) (evs : List AllocEvent) : Prop :=
  evs = optSenderChainCloneEvents scG scM

/-- Deterministic `AllocEvent` sequence emitted by Segment 1 (`+0x1778 → +0x19b0`) of Stage P3
    `SessionState::clone`:
    1. `local_identity_public` (`len > 0` → `rustAllocEvents len 1`);
    2. `remote_identity_public` (`len = 0` → `[]`, else `rustAllocEvents len 1`);
    3. `root_key` (`rustAllocEvents 32 1`);
    4. `sender_chain` (`optSenderChainCloneEvents recG.sender st.senderChain`). -/
def cloneKeysFrontEvents (recG : SessionGhost) (st : SessionState (List (BitVec 8))) :
    List AllocEvent :=
  rustAllocEvents recG.localIk.bytes.length 1 ++
  (if recG.remoteIk.bytes.length = 0 then [] else rustAllocEvents recG.remoteIk.bytes.length 1) ++
  rustAllocEvents 32 1 ++
  optSenderChainCloneEvents recG.sender st.senderChain

/-- Exact allocation envelope for Segment 1 (`+0x1778 → +0x19b0`) of Stage P3 `SessionState::clone`. -/
def CloneKeysFrontEnv (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  evs = cloneKeysFrontEvents recG st

theorem cloneKeysFrontEnv_events (recG : SessionGhost) (st : SessionState (List (BitVec 8))) :
    CloneKeysFrontEnv recG st (cloneKeysFrontEvents recG st) := rfl

theorem fitsEvents_cloneKeysFront_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits)
    (stB : M.σ) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (h : FitsEnv M lim stB (CloneKeysFrontEnv recG st)) :
    FitsEvents M lim stB (cloneKeysFrontEvents recG st) :=
  h (cloneKeysFrontEvents recG st) rfl

/-! ## 2. Budget-Threaded Precondition & Junction Predicates (`genP3J1..J4PlacedBudget`) -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` `genP3Pre` at
    `dpClosureEntryM3Placed + 0x1778#64`. -/
def genP3PrePlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ⌜s.sp = sp ∧ s.readReg64 .x19 = coroPtr ∧ s.readReg64 .x27 = sp + 0x370#64 ∧ s.readReg64 .x29 = fp⌝ ∗
    sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
    A.pool lim stB s ∗
    stackAt sp chainCloneStack ∗
    memRegion (sp + 0x3e0#64) 104 ∗
    ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
    genP3CallFramePlaced A.repAlloc sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      rem loc msgG msg ∗
    genP3SpillAll sp

/-- Budget-threaded relocatable `[LibsignalPlacement]` Junction 1 predicate at `+0x19b0`. -/
def genP3J1PlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ∃∗ w : GenP3J1Witness,
    ⌜s.sp = sp ∧
      s.readReg64 .x19 = coroPtr ∧
      s.readReg64 .x23 = w.newLocIdPtr ∧
      s.readReg64 .x24 = BitVec.ofNat 64 recG.remoteIk.bytes.length ∧
      s.readReg64 .x25 = w.newRemIdPtr ∧
      s.readReg64 .x27 = sp + 0x370#64 ∧
      s.readReg64 .x29 = fp ∧
      OptSenderChainCloneRel recG.sender st.senderChain w.sender' ∧
      OptSenderChainInline w.sender' st.senderChain
        (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)⌝ ∗
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      A.pool lim stB s ∗
      stackAt sp chainCloneStack ∗
      memRegion (sp + 0x3e0#64) 104 ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFramePlaced A.repAlloc sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        rem loc msgG msg ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
      vecU8Buf A.repAlloc 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
      optSenderChainHeap A.repAlloc w.sender' st.senderChain ∗
      genP3PendSpillScratch sp ∗
      genP3TailSpillScratch sp ∗
      genP3ChainsSpillScratch sp ∗
      ((sp + 0x48#64) ↦₆₄ w.c0) ∗
      ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
      ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
      ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
      ((sp + 0x98#64) ↦₆₄ 32#64) ∗
      ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
      genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

/-- Budget-threaded relocatable `[LibsignalPlacement]` Junction 2 predicate at `+0x1a5c`. -/
def genP3J2PlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ∃∗ w : GenP3J2Witness,
    ⌜s.sp = sp ∧
      s.readReg64 .x19 = coroPtr ∧
      s.readReg64 .x23 = BitVec.ofNat 64 st.receiverChains.length ∧
      s.readReg64 .x25 = w.newRcPtr ∧
      s.readReg64 .x27 = sp + 0x370#64 ∧
      s.readReg64 .x28 = 32#64 ∧
      s.readReg64 .x29 = fp ∧
      w.chains'.length = st.receiverChains.length ∧
      OptSenderChainCloneRel recG.sender st.senderChain w.sender' ∧
      OptSenderChainInline w.sender' st.senderChain
        (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)⌝ ∗
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      A.pool lim stB s ∗
      stackAt sp chainCloneStack ∗
      memRegion (sp + 0x3e0#64) 104 ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFramePlaced A.repAlloc sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        rem loc msgG msg ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
      vecU8Buf A.repAlloc 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
      optSenderChainHeap A.repAlloc w.sender' st.senderChain ∗
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) (BitVec.ofNat 64 st.receiverChains.length)
        w.newRcPtr (w.chains'.zip st.receiverChains) ∗
      genP3PendSpillScratch sp ∗
      genP3TailSpillScratch sp ∗
      ((sp + 0x48#64) ↦₆₄ w.c0) ∗
      ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
      ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
      ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
      ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
      ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
      ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
      ((sp + 0x98#64) ↦₆₄ 32#64) ∗
      ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
      genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

/-- Budget-threaded relocatable `[LibsignalPlacement]` Junction 3 predicate at `+0x1b20`. -/
def genP3J3PlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ∃∗ w : GenP3J3Witness,
    ⌜s.sp = sp ∧
      s.readReg64 .x19 = coroPtr ∧
      s.readReg64 .x22 = w.pendCap' ∧
      s.readReg64 .x23 = BitVec.ofNat 64 st.receiverChains.length ∧
      s.readReg64 .x25 = w.newRcPtr ∧
      s.readReg64 .x26 = w.kybCap' ∧
      s.readReg64 .x27 = ctxPtr ∧
      s.readReg64 .x28 = 32#64 ∧
      s.readReg64 .x29 = fp ∧
      w.chains'.length = st.receiverChains.length ∧
      OptSenderChainCloneRel recG.sender st.senderChain w.sender' ∧
      OptSenderChainInline w.sender' st.senderChain
        (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)⌝ ∗
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      A.pool lim stB s ∗
      stackAt sp chainCloneStack ∗
      memRegion (sp + 0x3e0#64) 104 ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFramePlaced A.repAlloc sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        rem loc msgG msg ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
      vecU8Buf A.repAlloc 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
      optSenderChainHeap A.repAlloc w.sender' st.senderChain ∗
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) (BitVec.ofNat 64 st.receiverChains.length)
        w.newRcPtr (w.chains'.zip st.receiverChains) ∗
      OptPendClone A.repAlloc recG.pending w.pendCap' w.pendPtr' ∗
      OptKybClone A.repAlloc recG.kyber w.kybCap' w.kybPtr' ∗
      genP3TailSpillScratch sp ∗
      ((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗
      ((sp + 0x10#64) ↦₆₄ w.d10) ∗
      ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗
      ((sp + 0x24#64) ↦₃₂ w.w24) ∗
      ((sp + 0x28#64) ↦₃₂ w.w28) ∗
      ((sp + 0x2c#64) ↦₃₂ w.w2c) ∗
      ((sp + 0x48#64) ↦₆₄ w.c0) ∗
      ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
      ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
      ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
      ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
      ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
      ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
      ((sp + 0x98#64) ↦₆₄ 32#64) ∗
      ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
      genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

/-- Budget-threaded relocatable `[LibsignalPlacement]` Junction 4 predicate at `+0x1bac`. -/
def genP3J4PlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ∃∗ w : GenP3J4Witness,
    ⌜s.sp = sp ∧
      s.readReg64 .x19 = coroPtr ∧
      s.readReg64 .x21 = w.newPqPtr ∧
      s.readReg64 .x22 = w.pendCap' ∧
      s.readReg64 .x23 = w.newAlicePtr ∧
      s.readReg64 .x24 = BitVec.ofNat 64 recG.alice.bytes.length ∧
      s.readReg64 .x25 = w.newRcPtr ∧
      s.readReg64 .x26 = BitVec.ofNat 64 st.pqRatchetState.length ∧
      s.readReg64 .x27 = ctxPtr ∧
      s.readReg64 .x28 = 32#64 ∧
      s.readReg64 .x29 = fp ∧
      recG.regIds = unpack32 w.regW0 ++ unpack32 w.regW1 ∧
      w.chains'.length = st.receiverChains.length ∧
      OptSenderChainCloneRel recG.sender st.senderChain w.sender' ∧
      OptSenderChainInline w.sender' st.senderChain
        (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)⌝ ∗
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      A.pool lim stB s ∗
      stackAt sp chainCloneStack ∗
      memRegion (sp + 0x3e0#64) 104 ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFramePlaced A.repAlloc sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        rem loc msgG msg ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
      vecU8Buf A.repAlloc 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
      optSenderChainHeap A.repAlloc w.sender' st.senderChain ∗
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) (BitVec.ofNat 64 st.receiverChains.length)
        w.newRcPtr (w.chains'.zip st.receiverChains) ∗
      OptPendClone A.repAlloc recG.pending w.pendCap' w.pendPtr' ∗
      OptKybClone A.repAlloc recG.kyber w.kybCap' w.kybPtr' ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.alice.bytes.length) w.newAlicePtr recG.alice.bytes ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 st.pqRatchetState.length) w.newPqPtr st.pqRatchetState ∗
      ((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗
      ((sp + 0x10#64) ↦₆₄ w.d10) ∗
      ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗
      ((sp + 0x24#64) ↦₃₂ w.w24) ∗
      ((sp + 0x28#64) ↦₃₂ w.w28) ∗
      ((sp + 0x2c#64) ↦₃₂ w.w2c) ∗
      ((sp + 0x30#64) ↦₃₂ w.regW0) ∗
      ((sp + 0x34#64) ↦₃₂ w.regW1) ∗
      ((sp + 0x38#64) ↦₆₄ w.kybCap') ∗
      ((sp + 0x40#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
      ((sp + 0x48#64) ↦₆₄ w.c0) ∗
      ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
      ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
      ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
      ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
      ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
      ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
      ((sp + 0x98#64) ↦₆₄ 32#64) ∗
      ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
      genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

theorem genP3PrePlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) :
    genP3PrePlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg s =
    genP3PrePlaced (A.atState lim stB s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg s :=
  rfl

theorem genP3J1PlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) :
    genP3J1PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg s =
    genP3J1Placed (A.atState lim stB s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg s :=
  rfl

theorem genP3J2PlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) :
    genP3J2PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg s =
    genP3J2Placed (A.atState lim stB s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg s :=
  rfl

theorem genP3J3PlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) :
    genP3J3PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg s =
    genP3J3Placed (A.atState lim stB s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg s :=
  rfl

theorem genP3J4PlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) :
    genP3J4PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg s =
    genP3J4Placed (A.atState lim stB s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg s :=
  rfl

/-! ## 3. Public Top-Level Segment 1 Budget-Threaded Theorems -/

set_option maxHeartbeats 800000 in
theorem cloneKeysFront_vregs_placed_ok_stepEvents [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (hscc : SenderChainClone3OkPlaced A lim ext)
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (_hrc : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (_hsp_root : rootStack ≤ sp.toNat)
    (hfits : FitsEvents M lim stB (cloneKeysFrontEvents recG st))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1778#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext)
      (dpClosureEntryM3Placed + 0x19b0#64) s
      (genP3PrePlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3J1PlacedBudget A lim (M.stepEvents (cloneKeysFrontEvents recG st) stB)
          sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧
        LibsignalCodeRoLoaded lsmpl s1.mem ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp := by
  let evs1 := rustAllocEvents recG.localIk.bytes.length 1
  let evs2 := if recG.remoteIk.bytes.length = 0 then [] else rustAllocEvents recG.remoteIk.bytes.length 1
  let evs3 := rustAllocEvents 32 1
  let evs4 := optSenderChainCloneEvents recG.sender st.senderChain
  have hfits_all : FitsEvents M lim stB ((evs1 ++ evs2 ++ evs3) ++ evs4) := hfits
  rw [fitsEvents_append] at hfits_all
  rcases hfits_all with ⟨hfits123, hfits4_raw⟩
  rw [fitsEvents_append] at hfits123
  rcases hfits123 with ⟨hfits12, hfits3_raw⟩
  rw [fitsEvents_append] at hfits12
  rcases hfits12 with ⟨hfits1, hfits2⟩
  have hst12 : M.stepEvents (evs1 ++ evs2) stB = M.stepEvents evs2 (M.stepEvents evs1 stB) :=
    M.stepEvents_append evs1 evs2 stB
  have hst123 :
      M.stepEvents (evs1 ++ evs2 ++ evs3) stB =
        M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 stB)) := by
    rw [M.stepEvents_append (evs1 ++ evs2) evs3 stB, hst12]
  have hst1234 :
      M.stepEvents (cloneKeysFrontEvents recG st) stB =
        M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 stB))) := by
    change M.stepEvents ((evs1 ++ evs2 ++ evs3) ++ evs4) stB = _
    rw [M.stepEvents_append (evs1 ++ evs2 ++ evs3) evs4 stB, hst123]
  have hfits3 : FitsEvents M lim (M.stepEvents evs2 (M.stepEvents evs1 stB)) evs3 := by
    rwa [hst12] at hfits3_raw
  have hfits4 :
      FitsEvents M lim (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 stB))) evs4 := by
    rwa [hst123] at hfits4_raw
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  dsimp only [genP3PrePlacedBudget, genP3SpillAll]
  refine sepWPp_pure_elim_any fun ⟨hsp, hx19, hx27, hx29⟩ => ?_
  subst hsp
  rw [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.sessionStateAt_front_eq A.repAlloc coroPtr recG st]
  simp only [sepConj_assoc]
  refine sepWPp_pure_elim_any fun hss_pure => ?_
  have hloc_pos : 0 < recG.localIk.bytes.length := by
    have hloc33 : recG.localIk.bytes.length = 33 := hss_pure.2.2.2.2.2.1
    omega
  let F_rest : SepProp :=
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.frontSessionRestAt A.repAlloc coroPtr recG st ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFramePlaced A.repAlloc s.sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        rem loc msgG msg ∗
      genP3PendSpillScratch s.sp ∗
      genP3TailSpillScratch s.sp ∗
      genP3ChainsSpillScratch s.sp
  refine sepWPp_weaken_pre_any
    (P' := (∃∗ wf : GenP3FrontSpill,
      ((s.sp + 0x48#64) ↦₆₄ wf.u_48) ∗ ((s.sp + 0x50#64) ↦₆₄ wf.u_50) ∗
      ((s.sp + 0x5c#64) ↦₃₂ wf.u_5c) ∗ ((s.sp + 0x7c#64) ↦₃₂ wf.u_7c) ∗
      ((s.sp + 0x98#64) ↦₆₄ wf.u_98) ∗ ((s.sp + 0xd0#64) ↦₆₄ wf.u_d0) ∗
      ((s.sp + 0x930#64) ↦₆₄ wf.u930) ∗ ((s.sp + 0x938#64) ↦₆₄ wf.u938) ∗
      ((s.sp + 0x940#64) ↦₆₄ wf.u940) ∗ ((s.sp + 0x948#64) ↦₆₄ wf.u948) ∗
      ((s.sp + 0x950#64) ↦₆₄ wf.u950) ∗ ((s.sp + 0x958#64) ↦₆₄ wf.u958) ∗
      ((s.sp + 0x960#64) ↦₆₄ wf.u960) ∗ ((s.sp + 0x968#64) ↦₆₄ wf.u968) ∗
      ((s.sp + 0x970#64) ↦₆₄ wf.u970) ∗ ((s.sp + 0x978#64) ↦₆₄ wf.u978) ∗
      ((s.sp + 0x980#64) ↦₆₄ wf.u980) ∗ ((s.sp + 0x988#64) ↦₆₄ wf.u988)) ∗
      (vecGhostAt A.repAlloc recG.localIk (coroPtr + 0xf8#64) ∗
        vecGhostAt A.repAlloc recG.remoteIk (coroPtr + 0x110#64) ∗
        vecU8At A.repAlloc (coroPtr + 0x128#64) recG.root.cap recG.root.ptr (keyToBytes32 st.rootKey) ∗
        optSenderChainAt A.repAlloc (coroPtr + 0x188#64) recG.sender st.senderChain ∗
        ((coroPtr + 0x240#64) ↦₃₂ st.sessionVersion) ∗
        ((coroPtr + 0x244#64) ↦₃₂ st.previousCounter) ∗
        A.pool lim stB s ∗ stackAt s.sp chainCloneStack ∗ memRegion (s.sp + 0x3e0#64) 104 ∗ F_rest))
    (by dsimp only [F_rest]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  rw [sepExists_sepConj_left]
  refine sepWPp_exists_elim_any fun wf => ?_
  rw [stackAt_chainClone_eq_alloc s.sp]
  simp only [sepConj_assoc]
  refine sepWPp_bind_frame_any
    (seg_locId_placed_budget_ok (Qp := fun _ _ => False) ext hshim halloc hmemcpy s0 s coroPtr
      wf.u_d0 st.sessionVersion wf.u_7c recG.localIk hloc_pos hfits1 hcro hpc hrun hsp_align htr hx19)
    (by sep_focus)
    fun s1 _ hpc1 hrun1
      ⟨newLocIdPtr, hent1, hsp1, htr1, hcro1, hx19_1, hx23_1, hx27_1, hx29_1, hvregs1⟩ => ?_
  refine sepWPp_weaken_pre_any (sepConj_mono_left hent1) ?_
  simp only [sepConj_assoc]
  have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine sepWPp_bind_frame_any
    (seg_remId_placed_budget_ok (Qp := fun _ _ => False) ext hshim halloc hmemcpy s0 s1 coroPtr
      recG.remoteIk hfits2 hcro1 hpc1 hrun1 hsp1_al htr1 hx19_1)
    (by simp only [hsp1]; sep_focus)
    fun s2 _ hpc2 hrun2
      ⟨newRemIdPtr, hent2, hsp2, htr2, hcro2, hx19_2, hx22_2, hx23_2, hx24_2, hx25_2,
        hx27_2, hx29_2, hvregs2⟩ => ?_
  refine sepWPp_weaken_pre_any (sepConj_mono_left hent2) ?_
  simp only [sepConj_assoc]
  have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
  have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
  refine sepWPp_bind_frame_any
    (seg_rootKey_placed_budget_ok (Qp := fun _ _ => False) ext hshim halloc hmemcpy s0 s2 coroPtr
      recG.root.cap recG.root.ptr wf.u_50 wf.u_98 st.rootKey hfits3 hcro2 hpc2 hrun2 hsp2_al
      htr2 hx19_2)
    (by simp only [hsp1, hsp2']; sep_focus)
    fun s3 _ hpc3 hrun3
      ⟨newRootKeyPtr, hent3, hsp3, htr3, hcro3, hx19_3, hx22_3, hx23_3, hx24_3, hx25_3,
        hx27_3, hx29_3, hvregs3⟩ => ?_
  refine sepWPp_weaken_pre_any (sepConj_mono_left hent3) ?_
  simp only [sepConj_assoc]
  have hsp3' : s3.sp = s.sp := hsp3.trans hsp2'
  have hsp3_al : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3']; exact hsp_align
  have hx22_3' : s3.readReg64 .x22 = s3.sp + 0x930#64 := by
    rw [hx22_3, hx22_2, hsp1, hsp3']
  have hx27_3' : s3.readReg64 .x27 = s3.sp + 0x370#64 := by
    rw [hx27_3, hx27_2, hx27_1, hx27, hsp3']
  have hstack_fold :
      (memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ stackAt s2.sp allocHookStack) ⊢
        stackAt s.sp chainCloneStack := by
    rw [hsp2', ← stackAt_chainClone_eq_alloc s.sp]
    exact Entails.refl _
  refine sepWPp_weaken_frame_any hstack_fold (by sep_focus) ?_
  refine sepWPp_bind_frame_any
    (seg_senderChain_placed_budget_ok (Qp := fun _ _ => False) ext hscc s0 s3 coroPtr wf.u_48
      wf.u930 wf.u938 wf.u940 wf.u948 wf.u950 wf.u958
      wf.u960 wf.u968 wf.u970 wf.u978 wf.u980 wf.u988
      st.previousCounter wf.u_5c recG.sender st.senderChain
      hfits4 hcro3 hpc3 hrun3 hsp3_al htr3 hx19_3 hx22_3' hx27_3')
    (by simp only [hsp3']; sep_focus)
    fun s4 _ hpc4 hrun4
      ⟨sender', c0, sq0, sq1, sq2, sq3, sq4, sq5, hsc_rel, hsc_inl, hent4,
        hsp4, htr4, hcro4, hx19_4, hx23_4, hx24_4, hx25_4, hx27_4, hx29_4, hvregs4⟩ => ?_
  refine sepWPp_weaken_pre_any (sepConj_mono_left hent4) ?_
  refine sepWPp_done_any hpc4 hrun4
    ⟨?_, htr4, hcro4, hvregs4.trans (hvregs3.trans (hvregs2.trans hvregs1))⟩
  rw [hst1234]
  dsimp only [genP3J1PlacedBudget, F_rest]
  refine Entails.sepExists_right
    { newLocIdPtr := newLocIdPtr
      newRemIdPtr := newRemIdPtr
      newRootKeyPtr := newRootKeyPtr
      c0 := c0
      sender' := sender'
      sq0 := sq0, sq1 := sq1, sq2 := sq2, sq3 := sq3, sq4 := sq4, sq5 := sq5 } ?_
  refine Entails.pure_right
    ⟨hsp4.trans hsp3', hx19_4,
     hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_1)),
     hx24_4.trans (hx24_3.trans hx24_2),
     hx25_4.trans (hx25_3.trans hx25_2),
     by rw [hx27_4, hsp3'],
     hx29_4.trans (hx29_3.trans (hx29_2.trans (hx29_1.trans hx29))),
     hsc_rel, hsc_inl⟩ ?_
  rw [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.sessionStateAt_front_eq A.repAlloc coroPtr recG st]
  simp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp, hsp3', hsp2', hsp1, sepConj_assoc]
  exact Entails.pure_right hss_pure (Entails.of_eq (by sep_ac_rfl))

/-- Envelope-form (`FitsEnv M lim stB (CloneKeysFrontEnv recG st)`) counterpart of
    `cloneKeysFront_vregs_placed_ok_stepEvents`. -/
theorem cloneKeysFront_vregs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (hscc : SenderChainClone3OkPlaced A lim ext)
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ sp.toNat)
    (hfits : FitsEnv M lim stB (CloneKeysFrontEnv recG st))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1778#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext)
      (dpClosureEntryM3Placed + 0x19b0#64) s
      (genP3PrePlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        ∃ evs : List AllocEvent,
          CloneKeysFrontEnv recG st evs ∧
          (P_f ⊢ genP3J1PlacedBudget A lim (M.stepEvents evs stB)
            sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
            recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp := by
  have hstep :=
    cloneKeysFront_vregs_placed_ok_stepEvents (Qp := fun _ _ => False)
      ext hshim halloc hmemcpy hscc s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root
      (fitsEvents_cloneKeysFront_of_fitsEnv M lim stB recG st hfits)
      hcro hpc hrun htr
  refine sepWPp_bind_frame_any hstep (sepConj_emp _).symm fun s1 P_f hpc1 hrun1 ⟨hent1, htr1, hcro1, hv1⟩ => ?_
  rw [sepConj_emp]
  exact sepWPp_done_any hpc1 hrun1 ⟨cloneKeysFrontEvents recG st, rfl, hent1, htr1, hcro1, hv1⟩

/-- VM-hook entry variant accepting `rustAllocShimVmSpec` and `allocMemcpyVmSpec` directly. -/
theorem cloneKeysFront_vregs_vmHooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) allocMemcpyVmSpec)
    (hscc : SenderChainClone3OkPlaced A lim ext)
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ sp.toNat)
    (hfits : FitsEnv M lim stB (CloneKeysFrontEnv recG st))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1778#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext)
      (dpClosureEntryM3Placed + 0x19b0#64) s
      (genP3PrePlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        ∃ evs : List AllocEvent,
          CloneKeysFrontEnv recG st evs ∧
          (P_f ⊢ genP3J1PlacedBudget A lim (M.stepEvents evs stB)
            sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
            recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp :=
  cloneKeysFront_vregs_placed_ok ext
    (subroutine_ok_sessionShimBudget_of_rustAllocShimVm hshim)
    halloc
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm hmemcpy)
    hscc s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg hrc hsp_align hsp_root hfits hcro hpc hrun htr

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudget
