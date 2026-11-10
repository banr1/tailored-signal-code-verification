/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.EpilogueReassemblyXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.KyberBaseKeyPqStateXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.SessionCloneTailXPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget

/-!
# Budget-Threaded `SessionStructure::clone` Tail (`+592 ∨ +648` → `ret`, Block `80`)

Chains the budget-threaded proofs of fields 7–9 (`pending_kyber_pre_key`, `alice_base_key`,
`pq_ratchet_state`) and the epilogue from `+592 ∨ +648` to `ret` on Block `80`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.SessionCloneTailXPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl lsρ withLsCl lsMemcpySym
)
open CryptoVerification.RustHeap (vecU8At vecU8Buf vecBuf)
open CryptoVerification.LibsignalSessionRepr (VecGhost ChainGhost vecGhostAt chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SenderChainGhost optSenderChainAt optTailVecAt
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (chainCloneStackX)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (chunks96_6QAt optSenderChainHeap)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (DstVals)
open CryptoVerification.E2E.Record.Placed (blkPl_80 lsProg_80)
open CryptoVerification.E2E.Record.Serialization (SessionCloneGhost)
open CryptoVerification.E2E.Record.Serialization.SessionCloneAux (
  ScSpillVals ScOptPendClone ScOptKybClone
  scDstSlotsAt scDstSlotsWrittenAt scSpillSlotsAt scSavedRegsAt
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl sessionCloneStackX)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEvents fitsEvents_append
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  vecCloneEvents optTailCloneEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget (sc_transport_pool)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.EpilogueReassemblyXBudget (
  sc_epilogue_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.KyberBaseKeyPqStateXPlacedBudget (
  pqCloneEvents sc_pendingKyber_placed_x sc_aliceBaseKey_placed_x sc_pqRatchet_placed_x
)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-- Allocation events emitted by the tail (`s4 → ret`: fields 7, 8, and 9). -/
def scTailEvents (x : SessionCloneGhost) : List AllocEvent :=
  optTailCloneEvents x.G.kyber ++
  vecCloneEvents x.G.alice ++
  pqCloneEvents x.s.state.pqRatchetState

private theorem stackAt_chainClone_eq_alloc_x (sp : BitVec 64) :
    stackAt sp chainCloneStackX =
      memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗ stackAt sp extHookStack := by
  have h := stackAt_split_bottom sp extHookStack 208 (by decide)
  rwa [show extHookStack + 208 = chainCloneStackX by decide] at h

/-- Budget-threaded tail of `SessionStructure::clone` from `s4` (`+592 ∨ +648`) through `ret`
on `lsProg_80 H`. -/
theorem sc_tail_from_s4_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H)
    (hmemcpy : subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (withVmPreserved (sessionMemcpySpec extHookStack))))
    (x : SessionCloneGhost) (st4 : M.σ) (s0 s4 : State)
    {Q Qp : State → SepProp → Prop}
    (sv : ScSpillVals) (dv : DstVals) (w288 w28c : BitVec 32)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost)
    (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32)
    (hfits_tail : FitsEvents M lim st4 (scTailEvents x))
    (hpc4 : s4.pc = (blkPl_80).base + 592#64 ∨ s4.pc = (blkPl_80).base + 648#64)
    (hrun4 : s4.status = .Running)
    (hsp4_eq : s4.sp = s0.sp - 0x1d0#64)
    (hspA4 : s4.spAligned = true)
    (hx19_4' : s4.readReg64 .x19 = x.dst)
    (hx23_4 : (s4.readReg64 .x23).truncate 32 = w23')
    (hx24_4 : (s4.readReg64 .x24).truncate 32 = w24')
    (hx25_4 : s4.readReg64 .x25 = x.src)
    (hx26_4' : s4.readReg64 .x26 = chainsCap')
    (hx27_4' : s4.readReg64 .x27 = chainsPtr')
    (hx28_4 : s4.readReg64 .x28 = pendCap')
    (htr4 : s4.trace = s0.trace)
    (hvregs4_eq : s4.calleeSavedVRegs = s0.calleeSavedVRegs)
    (hdone : ∀ (s8 : State) (kybCap' kybPtr' : BitVec 64) (v28' : BitVec 32)
      (alice' : VecGhost) (pqCap' pqPtr' : BitVec 64) (v0c' : BitVec 32),
      s8.pc = s0.readReg64 .lr →
      s8.status = .Running →
      s8.sp = (s0.sp - 0x1d0#64) + 0x1d0#64 →
      CalleeSavedPreserved s0 s8 →
      s8.trace = s0.trace →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      pqCap' = BitVec.ofNat 64 x.s.state.pqRatchetState.length →
      let sp := s0.sp - 0x1d0#64
      SepWPp (lsProg_80 H) (s0.readReg64 .lr) s8
        (scDstSlotsWrittenAt x.dst localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
            pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w23' w24' v18' v2c'
            kybCap' kybPtr' v28' x.s.state.sessionVersion x.s.state.previousCounter w288 w28c ∗
          chunks96_6QAt (sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          scSpillSlotsAt sp v0c' kybPtr' v18' pendPtr' v28' v2c' alice'.ptr w28c
            kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
          scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
            (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
            (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
            (s0.readReg64 .x19) ∗
          ((vecGhostAt A.repAlloc x.G.localIk x.src ∗
            vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
            vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
            ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
            ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
            ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
            vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
            vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
            vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
            optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
            optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
            optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
            ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
            ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
            ((x.src + 0x150#64) ↦₃₂ w288) ∗
            ((x.src + 0x154#64) ↦₃₂ w28c)) ∗
          (vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
            vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
            vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
            vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
            vecU8Buf A.repAlloc alice'.cap alice'.ptr alice'.bytes ∗
            vecU8Buf A.repAlloc pqCap' pqPtr' x.s.state.pqRatchetState ∗
            optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
            ScOptPendClone A.repAlloc x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
            ScOptKybClone A.repAlloc x.G.kyber kybCap' kybPtr' v28') ∗
          A.pool lim (M.stepEvents (scTailEvents x) st4) s8 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
            stackAt sp chainCloneStackX ∗
            memRegion (sp + 0xf0#64) 8 ∗
            memRegion (sp + 0xf8#64) 104 ∗
            memRegion (sp + 0x160#64) 16)))
        Q Qp) :
    let sp := s0.sp - 0x1d0#64
    SepWPpLsCl lsmpl (lsProg_80 H) (s0.readReg64 .lr) s4
      (A.pool lim st4 s4 ∗
        optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
        ScOptPendClone A.repAlloc x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
        ((sp + 0x18#64) ↦₆₄ v18') ∗
        ((sp + 0x20#64) ↦₆₄ pendPtr') ∗
        ((sp + 0x2c#64) ↦₃₂ v2c') ∗
        stackAt sp extHookStack ∗
        (((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
          memRegion (sp + 0xf8#64) 104 ∗
          memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗
          vecGhostAt A.repAlloc x.G.localIk x.src ∗
          vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
          vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
          optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
          vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
          vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
          optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
          chunks96_6QAt (sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          ((sp + 0x48#64) ↦₆₄ scCap') ∗
          ((sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
          ((sp + 0x58#64) ↦₆₄ rootPtr') ∗
          ((sp + 0x60#64) ↦₆₄ 32#64) ∗
          ((sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗
          ((sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
          ((sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗
          ((sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
          ((sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
          ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
          ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
          ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
          memRegion sp 12 ∗ ((sp + 0x0c#64) ↦₃₂ sv.v0c) ∗
          ((sp + 0x10#64) ↦₆₄ sv.v10) ∗
          ((sp + 0x28#64) ↦₃₂ sv.v28) ∗
          ((sp + 0x30#64) ↦₆₄ sv.v30) ∗
          memRegion (sp + 0x38#64) 4 ∗ ((sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
          ((sp + 0x40#64) ↦₆₄ sv.v40) ∗
          memRegion (sp + 0x50#64) 4 ∗
          memRegion (sp + 0x80#64) 4 ∗
          ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
          vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
          vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
          optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
          ((x.src + 0x150#64) ↦₃₂ w288) ∗
          ((x.src + 0x154#64) ↦₃₂ w28c) ∗
          scDstSlotsAt x.dst dv ∗
          scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
            (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
            (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
            (s0.readReg64 .x19) ∗
          memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
          memRegion (sp + 0xf0#64) 8 ∗
          memRegion (sp + 0x160#64) 16))
      Q Qp := by
  dsimp only
  set sp := s0.sp - 0x1d0#64
  have hfits123 : FitsEvents M lim st4
      (optTailCloneEvents x.G.kyber ++ (vecCloneEvents x.G.alice ++ pqCloneEvents x.s.state.pqRatchetState)) := by
    simpa only [scTailEvents, List.append_assoc] using hfits_tail
  obtain ⟨hfits_kyb, hfits23⟩ := (fitsEvents_append M lim _ _ st4).mp hfits123
  obtain ⟨hfits_alice, hfits_pq⟩ := (fitsEvents_append M lim _ _ _).mp hfits23
  have hstep_tail : M.stepEvents (pqCloneEvents x.s.state.pqRatchetState)
      (M.stepEvents (vecCloneEvents x.G.alice) (M.stepEvents (optTailCloneEvents x.G.kyber) st4)) =
      M.stepEvents (scTailEvents x) st4 := by
    simp only [scTailEvents, M.stepEvents_append]
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool lim st4 s4 ∗
            optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
            ((s4.sp + 0x10#64) ↦₆₄ sv.v10) ∗
            ((s4.sp + 0x28#64) ↦₃₂ sv.v28) ∗
            ((s4.sp + 0x40#64) ↦₆₄ sv.v40) ∗
            stackAt s4.sp extHookStack ∗
            (optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
              ScOptPendClone A.repAlloc x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
              ((sp + 0x18#64) ↦₆₄ v18') ∗
              ((sp + 0x20#64) ↦₆₄ pendPtr') ∗
              ((sp + 0x2c#64) ↦₃₂ v2c') ∗
              ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
              memRegion (sp + 0xf8#64) 104 ∗
              memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗
              vecGhostAt A.repAlloc x.G.localIk x.src ∗
              vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
              chunks96_6QAt (sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
              ((sp + 0x48#64) ↦₆₄ scCap') ∗
              ((sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
              ((sp + 0x58#64) ↦₆₄ rootPtr') ∗
              ((sp + 0x60#64) ↦₆₄ 32#64) ∗
              ((sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗
              ((sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
              ((sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗
              ((sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              memRegion sp 12 ∗ ((sp + 0x0c#64) ↦₃₂ sv.v0c) ∗
              ((sp + 0x30#64) ↦₆₄ sv.v30) ∗
              memRegion (sp + 0x38#64) 4 ∗ ((sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
              memRegion (sp + 0x50#64) 4 ∗
              memRegion (sp + 0x80#64) 4 ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
              vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
              vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              ((x.src + 0x150#64) ↦₃₂ w288) ∗
              ((x.src + 0x154#64) ↦₃₂ w28c) ∗
              scDstSlotsAt x.dst dv ∗
              scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
                (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
                (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
                (s0.readReg64 .x19) ∗
              memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              memRegion (sp + 0xf0#64) 8 ∗
              memRegion (sp + 0x160#64) 16))
    (by rw [hsp4_eq]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine sc_pendingKyber_placed_x hA hmemcpy hfits_kyb hpc4 hrun4 hspA4 hx25_4 htr4
    fun s5 kybCap' kybPtr' v28'
      hpc5 hrun5 hsp5 hspA5 hx19_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hx29_5 htr5 hvregs5 => ?_
  have hsp5_eq : s5.sp = sp := hsp5.trans hsp4_eq
  have hx19_5' : s5.readReg64 .x19 = x.dst := hx19_5.trans hx19_4'
  have hx23_5' : (s5.readReg64 .x23).truncate 32 = w23' := by rw [hx23_5]; exact hx23_4
  have hx24_5' : (s5.readReg64 .x24).truncate 32 = w24' := by rw [hx24_5]; exact hx24_4
  have hx26_5' : s5.readReg64 .x26 = chainsCap' := hx26_5.trans hx26_4'
  have hx27_5' : s5.readReg64 .x27 = chainsPtr' := hx27_5.trans hx27_4'
  have hx28_5' : s5.readReg64 .x28 = pendCap' := hx28_5.trans hx28_4
  rw [hsp4_eq]
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool lim (M.stepEvents (optTailCloneEvents x.G.kyber) st4) s5 ∗
            vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
            ((x.src + 0x150#64) ↦₃₂ w288) ∗
            ((x.src + 0x154#64) ↦₃₂ w28c) ∗
            ((s5.sp + 0x30#64) ↦₆₄ sv.v30) ∗
            ((s5.sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
            stackAt s5.sp extHookStack ∗
            (optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
              ScOptKybClone A.repAlloc x.G.kyber kybCap' kybPtr' v28' ∗
              ((sp + 0x10#64) ↦₆₄ kybPtr') ∗
              ((sp + 0x28#64) ↦₃₂ v28') ∗
              ((sp + 0x40#64) ↦₆₄ kybCap') ∗
              optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
              ScOptPendClone A.repAlloc x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
              ((sp + 0x18#64) ↦₆₄ v18') ∗
              ((sp + 0x20#64) ↦₆₄ pendPtr') ∗
              ((sp + 0x2c#64) ↦₃₂ v2c') ∗
              ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
              memRegion (sp + 0xf8#64) 104 ∗
              memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗
              vecGhostAt A.repAlloc x.G.localIk x.src ∗
              vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
              chunks96_6QAt (sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
              ((sp + 0x48#64) ↦₆₄ scCap') ∗
              ((sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
              ((sp + 0x58#64) ↦₆₄ rootPtr') ∗
              ((sp + 0x60#64) ↦₆₄ 32#64) ∗
              ((sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗
              ((sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
              ((sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗
              ((sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              memRegion sp 12 ∗ ((sp + 0x0c#64) ↦₃₂ sv.v0c) ∗
              memRegion (sp + 0x38#64) 4 ∗
              memRegion (sp + 0x50#64) 4 ∗
              memRegion (sp + 0x80#64) 4 ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
              vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              scDstSlotsAt x.dst dv ∗
              scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
                (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
                (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
                (s0.readReg64 .x19) ∗
              memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              memRegion (sp + 0xf0#64) 8 ∗
              memRegion (sp + 0x160#64) 16))
    (by rw [hsp5_eq]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine sc_aliceBaseKey_placed_x hA hmemcpy hfits_alice hpc5 hrun5 hspA5 hx25_5 htr5
    fun s6 alice'
      hpc6 hrun6 hsp6 hspA6 hx19_6 hx20_6 hx21_6 hx23_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 hx29_6
      htr6 hvregs6 halice_bytes halice_cap => ?_
  have hsp6_eq : s6.sp = sp := hsp6.trans hsp5_eq
  have hx19_6' : s6.readReg64 .x19 = x.dst := hx19_6.trans hx19_5'
  have hx23_6' : (s6.readReg64 .x23).truncate 32 = w23' := by rw [hx23_6]; exact hx23_5'
  have hx24_6' : (s6.readReg64 .x24).truncate 32 = w24' := by rw [hx24_6]; exact hx24_5'
  have hx26_6' : s6.readReg64 .x26 = chainsCap' := hx26_6.trans hx26_5'
  have hx27_6' : s6.readReg64 .x27 = chainsPtr' := hx27_6.trans hx27_5'
  have hx28_6' : s6.readReg64 .x28 = pendCap' := hx28_6.trans hx28_5'
  rw [hsp5_eq]
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool lim (M.stepEvents (vecCloneEvents x.G.alice) (M.stepEvents (optTailCloneEvents x.G.kyber) st4)) s6 ∗
            vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
            ((s6.sp + 0x0c#64) ↦₃₂ sv.v0c) ∗
            stackAt s6.sp extHookStack ∗
            (vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
              vecU8Buf A.repAlloc alice'.cap alice'.ptr alice'.bytes ∗
              ((x.src + 0x150#64) ↦₃₂ w288) ∗
              ((x.src + 0x154#64) ↦₃₂ w28c) ∗
              ((sp + 0x30#64) ↦₆₄ alice'.ptr) ∗
              ((sp + 0x3c#64) ↦₃₂ w28c) ∗
              optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
              ScOptKybClone A.repAlloc x.G.kyber kybCap' kybPtr' v28' ∗
              ((sp + 0x10#64) ↦₆₄ kybPtr') ∗
              ((sp + 0x28#64) ↦₃₂ v28') ∗
              ((sp + 0x40#64) ↦₆₄ kybCap') ∗
              optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
              ScOptPendClone A.repAlloc x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
              ((sp + 0x18#64) ↦₆₄ v18') ∗
              ((sp + 0x20#64) ↦₆₄ pendPtr') ∗
              ((sp + 0x2c#64) ↦₃₂ v2c') ∗
              ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
              memRegion (sp + 0xf8#64) 104 ∗
              memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗
              vecGhostAt A.repAlloc x.G.localIk x.src ∗
              vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
              chunks96_6QAt (sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
              ((sp + 0x48#64) ↦₆₄ scCap') ∗
              ((sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
              ((sp + 0x58#64) ↦₆₄ rootPtr') ∗
              ((sp + 0x60#64) ↦₆₄ 32#64) ∗
              ((sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗
              ((sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
              ((sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗
              ((sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              memRegion sp 12 ∗
              memRegion (sp + 0x38#64) 4 ∗
              memRegion (sp + 0x50#64) 4 ∗
              memRegion (sp + 0x80#64) 4 ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
              scDstSlotsAt x.dst dv ∗
              scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
                (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
                (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
                (s0.readReg64 .x19) ∗
              memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              memRegion (sp + 0xf0#64) 8 ∗
              memRegion (sp + 0x160#64) 16))
    (by rw [hsp6_eq]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine sc_pqRatchet_placed_x hA hmemcpy hfits_pq hpc6 hrun6 hspA6 hx25_6 htr6
    fun s7 pqCap' pqPtr' v0c'
      hpc7 hrun7 hsp7 hspA7 hx19_7 hx20_7 hx21_7 hx22_7 hx23_7 hx24_7 hx25_7 hx26_7 hx27_7 hx28_7 hx29_7
      htr7 hvregs7 hpq_cap => ?_
  have hsp7_eq : s7.sp = sp := hsp7.trans hsp6_eq
  have hx19_7' : s7.readReg64 .x19 = x.dst := hx19_7.trans hx19_6'
  have hx20_7' : (s7.readReg64 .x20).truncate 32 = w288 := hx20_7.trans hx20_6
  have hx21_7' : s7.readReg64 .x21 = alice'.cap := hx21_7.trans hx21_6
  have hx23_7' : (s7.readReg64 .x23).truncate 32 = w23' := hx23_7.trans hx23_6'
  have hx24_7' : (s7.readReg64 .x24).truncate 32 = w24' := hx24_7.trans hx24_6'
  have hx26_7' : s7.readReg64 .x26 = chainsCap' := hx26_7.trans hx26_6'
  have hx27_7' : s7.readReg64 .x27 = chainsPtr' := hx27_7.trans hx27_6'
  have hx28_7' : s7.readReg64 .x28 = pendCap' := hx28_7.trans hx28_6'
  rw [hsp6_eq, hstep_tail]
  refine SepWPpLsCl.weaken_pre
    (P' := scDstSlotsAt x.dst dv ∗
            chunks96_6QAt (s7.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
            scSpillSlotsAt s7.sp v0c' kybPtr' v18' pendPtr' v28' v2c' alice'.ptr w28c
              kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
              localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
            scSavedRegsAt s7.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
              (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
              (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
              (s0.readReg64 .x19) ∗
            ((vecGhostAt A.repAlloc x.G.localIk x.src ∗
              vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
              ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
              vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
              optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              ((x.src + 0x150#64) ↦₃₂ w288) ∗
              ((x.src + 0x154#64) ↦₃₂ w28c)) ∗
            (vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
              vecU8Buf A.repAlloc alice'.cap alice'.ptr alice'.bytes ∗
              vecU8Buf A.repAlloc pqCap' pqPtr' x.s.state.pqRatchetState ∗
              optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
              ScOptPendClone A.repAlloc x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
              ScOptKybClone A.repAlloc x.G.kyber kybCap' kybPtr' v28') ∗
            A.pool lim (M.stepEvents (scTailEvents x) st4) s7 ∗
            (memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              stackAt sp chainCloneStackX ∗
              memRegion (sp + 0xf0#64) 8 ∗
              memRegion (sp + 0xf8#64) 104 ∗
              memRegion (sp + 0x160#64) 16)))
    (by
      rw [hsp7_eq, stackAt_chainClone_eq_alloc_x sp]
      unfold scSpillSlotsAt
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine sc_epilogue_placed_x dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice' pqCap' pqPtr'
    scCap' sq0 sq1 sq2 sq3 sq4 sq5 v0c' kybCap' kybPtr' pendCap' pendPtr' v18'
    w23' w24' v28' v2c' w288 w28c
    (s0.readReg64 .x29) (s0.readReg64 .x28) (s0.readReg64 .x27)
    (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) _
    hpc7 hrun7 hspA7 hx19_7' hx20_7' hx21_7' hx22_7 hx23_7' hx24_7' hx25_7 hx26_7' hx27_7' hx28_7' htr7
    fun s8 hvm8 hpc8 hrun8 hsp8 hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8 hx25_8 hx26_8 hx27_8 hx28_8 hx29_8 _hlr8 htr8 hvregs8 => ?_
  rw [hsp7_eq] at hsp8 ⊢
  refine SepWPp.weaken_pre
    (P' := A.pool lim (M.stepEvents (scTailEvents x) st4) s7 ∗
      (scDstSlotsWrittenAt x.dst localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w23' w24' v18' v2c'
          kybCap' kybPtr' v28' x.s.state.sessionVersion x.s.state.previousCounter w288 w28c ∗
        chunks96_6QAt (sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        scSpillSlotsAt sp v0c' kybPtr' v18' pendPtr' v28' v2c' alice'.ptr w28c
          kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
        scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
          (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
          (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
          (s0.readReg64 .x19) ∗
        (vecGhostAt A.repAlloc x.G.localIk x.src ∗
          vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
          vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
          ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
          ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
          ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
          vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
          vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
          optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
          optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
          optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
          ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
          ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
          ((x.src + 0x150#64) ↦₃₂ w288) ∗
          ((x.src + 0x154#64) ↦₃₂ w28c)) ∗
        (vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
          vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
          vecU8Buf A.repAlloc alice'.cap alice'.ptr alice'.bytes ∗
          vecU8Buf A.repAlloc pqCap' pqPtr' x.s.state.pqRatchetState ∗
          optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
          ScOptPendClone A.repAlloc x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
          ScOptKybClone A.repAlloc x.G.kyber kybCap' kybPtr' v28') ∗
        (memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
          stackAt sp chainCloneStackX ∗
          memRegion (sp + 0xf0#64) 8 ∗
          memRegion (sp + 0xf8#64) 104 ∗
          memRegion (sp + 0x160#64) 16)))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine sc_transport_pool hvm8 ?_
  refine SepWPp.weaken_pre ?_
    (hdone s8 kybCap' kybPtr' v28' alice' pqCap' pqPtr' v0c'
      hpc8 hrun8 hsp8
      ⟨hx19_8, hx20_8, hx21_8, hx22_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8, hx29_8,
        hvregs8.trans (hvregs7.trans (hvregs6.trans (hvregs5.trans hvregs4_eq)))⟩
      htr8 halice_bytes halice_cap hpq_cap)
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.SessionCloneTailXPlacedBudget
