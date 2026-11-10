/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.EpilogueReassemblyX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.KyberBaseKeyPqStateXPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ReceiverChainsPendingPreKeyX

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable `SessionStructure::clone` Tail (`+592 ∨ +648` → `ret`, Block `80`)

Chains fields 7–9 (`pending_kyber_pre_key`, `alice_base_key`, `pq_ratchet_state`) with the epilogue
from `+592 ∨ +648` to `ret` on Block `80` under `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization.SessionCloneAux

open Arm64 Arm64.Obj ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
  CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

section Placed

/-- Tail of `SessionStructure::clone` from `s4` (`+592 ∨ +648`) through `ret` on `lsProg_80 H`. -/
theorem sc_tail_from_s4_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (x : SessionCloneGhost) (R : SepProp) (s0 s4 : State)
    {Q : State → SepProp → Prop}
    (sv : ScSpillVals) (dv : DstVals) (w288 w28c : BitVec 32)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost)
    (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32)
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
          ((vecGhostAt A x.G.localIk x.src ∗
            vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
            vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
            ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
            ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
            ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
            vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
            vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
            vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
            optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
            optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
            optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
            ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
            ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
            ((x.src + 0x150#64) ↦₃₂ w288) ∗
            ((x.src + 0x154#64) ↦₃₂ w28c)) ∗
          (vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
            vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
            vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
            vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
            vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
            vecU8Buf A pqCap' pqPtr' x.s.state.pqRatchetState ∗
            optSenderChainHeap A sender' x.s.state.senderChain ∗
            ScOptPendClone A x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
            ScOptKybClone A x.G.kyber kybCap' kybPtr' v28') ∗
          A.pool ∗
          (memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
            stackAt sp chainCloneStackX ∗
            memRegion (sp + 0xf0#64) 8 ∗
            memRegion (sp + 0xf8#64) 104 ∗
            memRegion (sp + 0x160#64) 16)))
        Q (scPanicPostX A x R s0)) :
    let sp := s0.sp - 0x1d0#64
    SepWPpLsCl lsmpl (lsProg_80 H) (s0.readReg64 .lr) s4
      (A.pool ∗
        optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
        ScOptPendClone A x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
        ((sp + 0x18#64) ↦₆₄ v18') ∗
        ((sp + 0x20#64) ↦₆₄ pendPtr') ∗
        ((sp + 0x2c#64) ↦₃₂ v2c') ∗
        stackAt sp Stage1X.extHookStack ∗
        (((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
          vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
          memRegion (sp + 0xf8#64) 104 ∗
          memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗
          vecGhostAt A x.G.localIk x.src ∗
          vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
          vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
          optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
          optSenderChainHeap A sender' x.s.state.senderChain ∗
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
          vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
          vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
          optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
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
      Q (scPanicPostX A x R s0) := by
  dsimp only
  set sp := s0.sp - 0x1d0#64
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool ∗
            optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
            ((s4.sp + 0x10#64) ↦₆₄ sv.v10) ∗
            ((s4.sp + 0x28#64) ↦₃₂ sv.v28) ∗
            ((s4.sp + 0x40#64) ↦₆₄ sv.v40) ∗
            stackAt s4.sp Stage1X.extHookStack ∗
            (optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
              ScOptPendClone A x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
              ((sp + 0x18#64) ↦₆₄ v18') ∗
              ((sp + 0x20#64) ↦₆₄ pendPtr') ∗
              ((sp + 0x2c#64) ↦₃₂ v2c') ∗
              ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
              memRegion (sp + 0xf8#64) 104 ∗
              memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗
              vecGhostAt A x.G.localIk x.src ∗
              vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainHeap A sender' x.s.state.senderChain ∗
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
              vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
              vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
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
    (by rw [hsp4_eq]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_pendingKyber_placed_x hC hpc4 hrun4 hspA4 hx25_4 htr4
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
    (P' := A.pool ∗
            vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
            ((x.src + 0x150#64) ↦₃₂ w288) ∗
            ((x.src + 0x154#64) ↦₃₂ w28c) ∗
            ((s5.sp + 0x30#64) ↦₆₄ sv.v30) ∗
            ((s5.sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
            stackAt s5.sp Stage1X.extHookStack ∗
            (optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
              ScOptKybClone A x.G.kyber kybCap' kybPtr' v28' ∗
              ((sp + 0x10#64) ↦₆₄ kybPtr') ∗
              ((sp + 0x28#64) ↦₃₂ v28') ∗
              ((sp + 0x40#64) ↦₆₄ kybCap') ∗
              optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
              ScOptPendClone A x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
              ((sp + 0x18#64) ↦₆₄ v18') ∗
              ((sp + 0x20#64) ↦₆₄ pendPtr') ∗
              ((sp + 0x2c#64) ↦₃₂ v2c') ∗
              ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
              memRegion (sp + 0xf8#64) 104 ∗
              memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗
              vecGhostAt A x.G.localIk x.src ∗
              vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainHeap A sender' x.s.state.senderChain ∗
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
              vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              scDstSlotsAt x.dst dv ∗
              scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
                (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
                (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
                (s0.readReg64 .x19) ∗
              memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              memRegion (sp + 0xf0#64) 8 ∗
              memRegion (sp + 0x160#64) 16))
    (by rw [hsp5_eq]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_aliceBaseKey_placed_x hC hpc5 hrun5 hspA5 hx25_5 htr5
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
    (P' := A.pool ∗
            vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
            ((s6.sp + 0x0c#64) ↦₃₂ sv.v0c) ∗
            stackAt s6.sp Stage1X.extHookStack ∗
            (vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
              vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
              ((x.src + 0x150#64) ↦₃₂ w288) ∗
              ((x.src + 0x154#64) ↦₃₂ w28c) ∗
              ((sp + 0x30#64) ↦₆₄ alice'.ptr) ∗
              ((sp + 0x3c#64) ↦₃₂ w28c) ∗
              optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
              ScOptKybClone A x.G.kyber kybCap' kybPtr' v28' ∗
              ((sp + 0x10#64) ↦₆₄ kybPtr') ∗
              ((sp + 0x28#64) ↦₃₂ v28') ∗
              ((sp + 0x40#64) ↦₆₄ kybCap') ∗
              optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
              ScOptPendClone A x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
              ((sp + 0x18#64) ↦₆₄ v18') ∗
              ((sp + 0x20#64) ↦₆₄ pendPtr') ∗
              ((sp + 0x2c#64) ↦₃₂ v2c') ∗
              ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
              memRegion (sp + 0xf8#64) 104 ∗
              memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗
              vecGhostAt A x.G.localIk x.src ∗
              vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainHeap A sender' x.s.state.senderChain ∗
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
    (by rw [hsp6_eq]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_pqRatchet_placed_x hC hpc6 hrun6 hspA6 hx25_6 htr6
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
  rw [hsp6_eq]
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
            ((vecGhostAt A x.G.localIk x.src ∗
              vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
              ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
              vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
              optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              ((x.src + 0x150#64) ↦₃₂ w288) ∗
              ((x.src + 0x154#64) ↦₃₂ w28c)) ∗
            (vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
              vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
              vecU8Buf A pqCap' pqPtr' x.s.state.pqRatchetState ∗
              optSenderChainHeap A sender' x.s.state.senderChain ∗
              ScOptPendClone A x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
              ScOptKybClone A x.G.kyber kybCap' kybPtr' v28') ∗
            A.pool ∗
            (memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              stackAt sp chainCloneStackX ∗
              memRegion (sp + 0xf0#64) 8 ∗
              memRegion (sp + 0xf8#64) 104 ∗
              memRegion (sp + 0x160#64) 16)))
    (by
      rw [hsp7_eq, stackAt_chainClone_eq_alloc_x sp]
      unfold scSpillSlotsAt
      exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_epilogue_placed_x dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice' pqCap' pqPtr'
    scCap' sq0 sq1 sq2 sq3 sq4 sq5 v0c' kybCap' kybPtr' pendCap' pendPtr' v18'
    w23' w24' v28' v2c' w288 w28c
    (s0.readReg64 .x29) (s0.readReg64 .x28) (s0.readReg64 .x27)
    (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) _
    hpc7 hrun7 hspA7 hx19_7' hx20_7' hx21_7' hx22_7 hx23_7' hx24_7' hx25_7 hx26_7' hx27_7' hx28_7' htr7
    fun s8 hpc8 hrun8 hsp8 hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8 hx25_8 hx26_8 hx27_8 hx28_8 hx29_8 hlr8 htr8 hvregs8 => ?_
  rw [hsp7_eq] at hsp8 ⊢
  exact hdone s8 kybCap' kybPtr' v28' alice' pqCap' pqPtr' v0c'
    hpc8 hrun8 hsp8
    ⟨hx19_8, hx20_8, hx21_8, hx22_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8, hx29_8,
      hvregs8.trans (hvregs7.trans (hvregs6.trans (hvregs5.trans hvregs4_eq)))⟩
    htr8 halice_bytes halice_cap hpq_cap

end Placed

end CryptoVerification.E2E.Record.Serialization.SessionCloneAux
