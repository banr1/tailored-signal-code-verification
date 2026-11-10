/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseX
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEntryX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEntryXPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.EpilogueReassemblyX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.KyberBaseKeyPqStateX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.PrologueFields1To4X
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.PrologueFields1To4XPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ReceiverChainsPendingPreKeyX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ReceiverChainsPendingPreKeyXPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.SessionCloneTailXPlaced
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

@[expose] public section

set_option autoImplicit false

/-!
# `<SessionStructure as Clone>::clone` (`0x240f0`)

Assembles the prologue, fields 1–9, and epilogue to establish the top-level subroutine contract of
`<SessionStructure as Clone>::clone` (`0x240f0`, Block `80`) at `sessionCloneStackX` on `SP2Ext` and
under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Record.Serialization.SessionCloneAux
open Proofs.libsignal
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg
  updateCalleeSavedVRegs
  Arm64.State.calleeSavedVRegs_writeReg64_gpr
  Arm64.State.calleeSavedVRegs_writeReg32_gpr
  Arm64.State.calleeSavedVRegs_setPC
  Arm64.State.calleeSavedVRegs_setPState

theorem L1_SessionCloneX : True := trivial

/-- Extracts `rcs.length < 2 ^ 63` from `vecBuf` over 104-byte `Chain` elements. -/
theorem sc_vecBuf_chains_len_lt_x (A : RustAlloc) (cap ptr : BitVec 64)
    (gs : List ChainGhost) (rcs : List ReceiverChain)
    (hlen : gs.length = rcs.length) :
    vecBuf A 104 8 (chainAt A) cap ptr (gs.zip rcs) ⊢
      ⌜rcs.length < 2 ^ 63⌝ ∗ vecBuf A 104 8 (chainAt A) cap ptr (gs.zip rcs) := by
  cases rcs with
  | nil =>
    exact Entails.pure_right (by decide) (Entails.refl _)
  | cons rc rcs_tl =>
    cases gs with
    | nil => simp at hlen
    | cons g gs_tl =>
      have hexp := segClone_vecBuf_expose_arrayAt A (stride := 104) 8 (chainAt A) cap ptr
        ((g :: gs_tl).zip (rc :: rcs_tl)) emp
      have hreasm := segClone_vecBuf_reassemble_arrayAt A 104 8 (chainAt A) cap ptr
        ((g :: gs_tl).zip (rc :: rcs_tl))
      simp only [sepConj_emp] at hexp
      refine Entails.trans hexp ?_
      apply Entails.pure_left; intro hlt
      have hgs_tl : gs_tl.length = rcs_tl.length := by simpa using hlen
      have hzip : ((g :: gs_tl).zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
        simp [hgs_tl]
      rw [hzip] at hlt
      have hrc_lt : (rc :: rcs_tl).length < 2 ^ 63 := by
        simp only [List.length_cons] at hlt ⊢
        omega
      exact Entails.pure_right hrc_lt hreasm

theorem sc_sp_sub_add_0x1d0_x (sp0 : BitVec 64) :
    sp0 - 0x1d0#64 + 0x1d0#64 = sp0 := by bv_omega

theorem sc_initial_stack_dst_decomp_x (dst sp0 : BitVec 64) (P1 P2 : SepProp) :
    (memRegion dst 344 ∗ P1 ∗ P2 ∗ stackAt sp0 sessionCloneStackX) ⊢
      (∃∗ dv : DstVals, scDstSlotsAt dst dv) ∗
      P1 ∗ P2 ∗
      memRegion (sp0 - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
      stackAt (sp0 - 0x1d0#64) chainCloneStackX ∗
      (∃∗ sv : ScSpillVals,
        scSpillSlotsAt (sp0 - 0x1d0#64) sv.v0c sv.v10 sv.v18 sv.v20 sv.v28 sv.v2c sv.v30 sv.v3c
          sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 sv.v84 sv.v88) ∗
      (∃∗ bq0 : BitVec 128, ∃∗ bq1 : BitVec 128, ∃∗ bq2 : BitVec 128,
        ∃∗ bq3 : BitVec 128, ∃∗ bq4 : BitVec 128, ∃∗ bq5 : BitVec 128,
        chunks96_6QAt (sp0 - 0x1d0#64 + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5) ∗
      memRegion (sp0 - 0x1d0#64 + 0xf0#64) 8 ∗
      memRegion (sp0 - 0x1d0#64 + 0xf8#64) 104 ∗
      memRegion (sp0 - 0x1d0#64 + 0x160#64) 16 ∗
      (∃∗ rv : ScSavedVals,
        scSavedRegsAt (sp0 - 0x1d0#64) rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25
          rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19) := by
  rw [stackAt_sessionClone_eq_x sp0]
  dsimp only [chainCloneStackX]
  set sp := sp0 - 0x1d0#64
  rw [memRegion_96_eq_exists_chunks96_6QAt (sp + 0x90#64)]
  refine sepConj_mono (memRegion_344_entails_scDstSlotsAt dst) (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine sepConj_mono (memRegion_0x90_entails_scSpillSlotsAt sp) ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  exact memRegion_0x170_0x60_entails_scSavedRegsAt sp

theorem sc_post_entails_x (A : RustAlloc) (x : SessionCloneGhost) (s0 sf : State)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost)
    (alice' : VecGhost) (pqCap' pqPtr' : BitVec 64)
    (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v0c' : BitVec 32) (kybCap' kybPtr' pendCap' pendPtr' v18' : BitVec 64)
    (w23' w24' v28' v2c' w288 w28c : BitVec 32)
    (htr : sf.trace = s0.trace)
    (h_pend_rel : PendingRel x.G.pending x.s.pendingPreKey)
    (h_kyb_rel : KyberRel x.G.kyber x.s.pendingKyberPreKey)
    (h_alice_eq : x.G.alice.bytes = x.s.aliceBaseKey)
    (h_rem_reg : x.G.regIds.take 4 = leBytes 4 x.s.remoteRegistrationId.toNat)
    (h_loc_reg : (x.G.regIds.drop 4).take 4 = leBytes 4 x.s.localRegistrationId.toNat)
    (h_loc_deser : PublicKey.deserialize x.G.localIk.bytes = .ok x.s.state.localIdentity.publicKey)
    (h_rem_deser : match x.s.state.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (h_chains_len : x.G.chains.length = x.s.state.receiverChains.length)
    (h_pend_some : x.G.pending.isSome = x.s.state.pendingPreKey)
    (h_reg_len : x.G.regIds.length = 8)
    (h_loc_len : x.G.localIk.bytes.length = 33)
    (h_rem_len : x.s.state.remoteIdentity.isSome → x.G.remoteIk.bytes.length = 33)
    (h_reg_pts : ∀ a : BitVec 64, (a ↦ₛ x.G.regIds) = (a ↦₃₂ w288) ∗ ((a + 4#64) ↦₃₂ w28c))
    (hloc_bytes : localIk'.bytes = x.G.localIk.bytes)
    (hloc_cap : localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length)
    (hrem_bytes : remoteIk'.bytes = x.G.remoteIk.bytes)
    (hrem_cap : remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (hchains_len : chains'.length = x.s.state.receiverChains.length)
    (hchains_cap : chainsCap' = BitVec.ofNat 64 x.s.state.receiverChains.length)
    (hchains_enc : ((chains'.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) =
      ((x.G.chains.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)))
    (halice_bytes : alice'.bytes = x.G.alice.bytes)
    (halice_cap : alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length)
    (hpq_cap : pqCap' = BitVec.ofNat 64 x.s.state.pqRatchetState.length)
    (hsc_inl : OptSenderChainInline sender' x.s.state.senderChain
      (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5))
    (hsc_enc : encSenderFieldMem sender' x.s.state.senderChain =
      encSenderFieldMem x.G.sender x.s.state.senderChain) :
    let sp := s0.sp - 0x1d0#64
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
      (vecGhostAt A x.G.localIk x.src ∗
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
        memRegion (sp + 0x160#64) 16)) ⊢
      (sessionCloneSpecX A).post x s0 sf := by
  dsimp only [sessionCloneSpecX, chainCloneStackX]
  set sp := s0.sp - 0x1d0#64
  apply Entails.pure_right htr
  have hsrc :
      (vecGhostAt A x.G.localIk x.src ∗
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
        ((x.src + 0x154#64) ↦₃₂ w28c)) ⊢
      sessionStateReprAt A x.src x.G x.s := by
    refine Entails.trans ?_
      (sc_srcSessionAt_reassemble A x w288 w28c h_pend_rel h_kyb_rel h_alice_eq h_rem_reg h_loc_reg
        h_loc_deser h_rem_deser h_chains_len h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts)
    rw [sc_vecAt_0x48_chains_eq A x.src x.G.chainsCap x.G.chainsPtr x.G.chains
        x.s.state.receiverChains h_chains_len]
    exact Entails.of_eq (by ac_rfl)
  have hdst :=
    scDstSlotsWrittenAt_entails_sessionAt A x localIk' remoteIk' rootPtr'
      chainsCap' chainsPtr' chains' alice' pqCap' pqPtr' sender' scCap'
      sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w23' w24' v18' v2c'
      kybCap' kybPtr' v28' w288 w28c
      h_pend_rel h_kyb_rel h_alice_eq h_rem_reg h_loc_reg h_loc_deser h_rem_deser
      h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts hloc_bytes hloc_cap hrem_bytes hrem_cap
      hchains_len hchains_cap hchains_enc halice_bytes halice_cap hpq_cap hsc_inl hsc_enc
  have hstk :=
    sc_stack_reassemble_x s0.sp v0c' kybPtr' v18' pendPtr' v28' v2c' alice'.ptr w28c
      kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
      localIk'.ptr x.s.state.sessionVersion localIk'.cap
      sq0 sq1 sq2 sq3 sq4 sq5
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
      (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
      (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
      (s0.readReg64 .x19)
  dsimp only [chainCloneStackX] at hstk
  refine Entails.trans
    (Q := (vecGhostAt A x.G.localIk x.src ∗
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
          (scDstSlotsWrittenAt x.dst localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
            pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w23' w24' v18' v2c'
            kybCap' kybPtr' v28' x.s.state.sessionVersion x.s.state.previousCounter w288 w28c ∗
            vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
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
            stackAt sp (0xd0 + Stage1X.extHookStack) ∗
            scSpillSlotsAt sp v0c' kybPtr' v18' pendPtr' v28' v2c' alice'.ptr w28c
              kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
              localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
            chunks96_6QAt (sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
            memRegion (sp + 0xf0#64) 8 ∗
            memRegion (sp + 0xf8#64) 104 ∗
            memRegion (sp + 0x160#64) 16 ∗
            scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
              (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
              (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
              (s0.readReg64 .x19)))
    (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono hsrc (sepConj_mono hdst (sepConj_mono_right hstk))

set_option maxHeartbeats 1600000 in
theorem sessionClone_sepWPpIn_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (x : SessionCloneGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr sessionCloneName)
    (hrun : s0.status = .Running)
    (hs0_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.dst)
    (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 .lr) s0
      (memRegion x.dst 344 ∗
        sessionStateReprAt A x.src x.G x.s ∗
        A.pool ∗
        stackAt s0.sp sessionCloneStackX)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (sessionCloneSpecX A).post x s0 sf))
      (scPanicPostX A x R s0) := by
  have hcc : ChainCloneLocal1OkX img A ext := chain_clone_ok_x hC
  have hscc : SenderChainCloneLocal1OkX img A ext := senderChain_clone_ok_x hC
  refine SepWPpIn.weaken_pre
    (sc_initial_stack_dst_decomp_x x.dst s0.sp (sessionStateReprAt A x.src x.G x.s) A.pool) ?_
  set sp := s0.sp - 0x1d0#64
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPpIn.exists_elim fun rv =>
    SepWPpIn.exists_elim fun bq0 => SepWPpIn.exists_elim fun bq1 =>
    SepWPpIn.exists_elim fun bq2 => SepWPpIn.exists_elim fun bq3 =>
    SepWPpIn.exists_elim fun bq4 => SepWPpIn.exists_elim fun bq5 =>
    SepWPpIn.exists_elim fun sv => SepWPpIn.exists_elim fun dv => ?_
  unfold sessionStateReprAt
  rw [sc_sessionStateAt_eq A x.src x.G x.s.state]
  simp only [sepConj_assoc]
  refine sepWPpIn_pure_2nd fun ⟨h_pend_rel, h_kyb_rel, h_alice_eq, h_rem_reg, h_loc_reg⟩ => ?_
  refine sepWPpIn_pure_2nd fun ⟨h_loc_deser, h_rem_deser, h_chains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩ => ?_
  obtain ⟨w288, w28c, _, h_reg_pts⟩ := exists_unpack32_pair_of_length_8 h_reg_len
  have h154 : x.src + 0x150#64 + 4#64 = x.src + 0x154#64 := by bv_arith
  have h_reg_src : ((x.src + 0x150#64) ↦ₛ x.G.regIds) =
      ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) := by
    rw [h_reg_pts (x.src + 0x150#64), h154]
  rw [sc_vecAt_0x48_chains_eq A x.src x.G.chainsCap x.G.chainsPtr x.G.chains
      x.s.state.receiverChains h_chains_len, h_reg_src]
  refine SepWPpIn.weaken_pre
    (P' := vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
            scSavedRegsAt (s0.sp - 0x1d0#64) rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25
              rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗
            (A.pool ∗
              vecGhostAt A x.G.localIk x.src ∗
              vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              chunks96_6QAt (sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (sp + 0xf8#64) 104 ∗
              scSpillSlotsAt sp sv.v0c sv.v10 sv.v18 sv.v20 sv.v28 sv.v2c sv.v30 sv.v3c
                sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 sv.v84 sv.v88 ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
              ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
              vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
              optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              ((x.src + 0x150#64) ↦₃₂ w288) ∗
              ((x.src + 0x154#64) ↦₃₂ w28c) ∗
              scDstSlotsAt x.dst dv ∗
              stackAt sp chainCloneStackX ∗
              memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              memRegion (sp + 0xf0#64) 8 ∗
              memRegion (sp + 0x160#64) 16))
    (Entails.of_eq (by dsimp only [sp]; ac_rfl)) ?_
  refine SepWPpIn.weaken_pre
    (sepConj_mono_left (sc_vecBuf_chains_len_lt_x A x.G.chainsCap x.G.chainsPtr x.G.chains
      x.s.state.receiverChains h_chains_len)) ?_
  rw [sepConj_assoc]
  refine SepWPpIn.pure_elim fun hrc_lt => ?_
  refine SepWPpIn.weaken_pre
    (P' := scSavedRegsAt (s0.sp - 0x1d0#64) rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25
              rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗
            (A.pool ∗
              vecGhostAt A x.G.localIk x.src ∗
              vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              chunks96_6QAt (sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (sp + 0xf8#64) 104 ∗
              scSpillSlotsAt sp sv.v0c sv.v10 sv.v18 sv.v20 sv.v28 sv.v2c sv.v30 sv.v3c
                sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 sv.v84 sv.v88 ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
              ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
              vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
              optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              ((x.src + 0x150#64) ↦₃₂ w288) ∗
              ((x.src + 0x154#64) ↦₃₂ w28c) ∗
              scDstSlotsAt x.dst dv ∗
              stackAt sp chainCloneStackX ∗
              memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              memRegion (sp + 0xf0#64) 8 ∗
              memRegion (sp + 0x160#64) 16))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sc_prologue_x (rv := rv) hpc hrun hs0_align hx0 hx1
    fun s1 hpc1 hrun1 hsp1 hspA1 hx0_1 hx1_1 hx29_1 htr1 hvregs1 => ?_
  have hsp1_eq : s1.sp = sp := hsp1
  unfold scSpillSlotsAt
  refine SepWPpIn.weaken_pre
    (P' := A.pool ∗
            vecGhostAt A x.G.localIk x.src ∗
            vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
            vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
            optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
            chunks96_6QAt (s1.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            memRegion (s1.sp + 0xf8#64) 104 ∗
            ((s1.sp + 0x48#64) ↦₆₄ sv.v48) ∗
            ((s1.sp + 0x54#64) ↦₃₂ sv.v54) ∗
            ((s1.sp + 0x58#64) ↦₆₄ sv.v58) ∗
            ((s1.sp + 0x60#64) ↦₆₄ sv.v60) ∗
            ((s1.sp + 0x68#64) ↦₆₄ sv.v68) ∗
            ((s1.sp + 0x70#64) ↦₆₄ sv.v70) ∗
            ((s1.sp + 0x78#64) ↦₆₄ sv.v78) ∗
            ((s1.sp + 0x84#64) ↦₃₂ sv.v84) ∗
            ((s1.sp + 0x88#64) ↦₆₄ sv.v88) ∗
            ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
            ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
            ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
            stackAt s1.sp chainCloneStackX ∗
            (memRegion sp 12 ∗ ((sp + 0x0c#64) ↦₃₂ sv.v0c) ∗
              ((sp + 0x10#64) ↦₆₄ sv.v10) ∗ ((sp + 0x18#64) ↦₆₄ sv.v18) ∗ ((sp + 0x20#64) ↦₆₄ sv.v20) ∗
              ((sp + 0x28#64) ↦₃₂ sv.v28) ∗ ((sp + 0x2c#64) ↦₃₂ sv.v2c) ∗
              ((sp + 0x30#64) ↦₆₄ sv.v30) ∗
              memRegion (sp + 0x38#64) 4 ∗ ((sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
              ((sp + 0x40#64) ↦₆₄ sv.v40) ∗
              memRegion (sp + 0x50#64) 4 ∗
              memRegion (sp + 0x80#64) 4 ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
              ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
              vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
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
    (by rw [hsp1_eq]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_fields_1_to_4_x hC hscc hpc1 hrun1 hspA1 hx0_1 hx1_1 hx29_1 htr1 hvregs1 hrc_lt
    fun s2 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc2 hrun2 hsp2 hspA2 hx19_2 hx21_2 hx25_2 hx26_2 hx29_2 htr2 hvregs2
      hloc_bytes hloc_cap hrem_bytes hrem_cap hsc_inl hsc_enc => ?_
  have hsp2_eq : s2.sp = sp := hsp2.trans hsp1_eq
  rw [hsp1_eq] at hx21_2 hx29_2 ⊢
  refine SepWPpIn.weaken_pre
    (P' := A.pool ∗
            ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
            vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
            memRegion (s2.sp + 0xf8#64) 104 ∗
            stackAt s2.sp chainCloneStackX ∗
            (vecGhostAt A x.G.localIk x.src ∗
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
              ((sp + 0x10#64) ↦₆₄ sv.v10) ∗ ((sp + 0x18#64) ↦₆₄ sv.v18) ∗ ((sp + 0x20#64) ↦₆₄ sv.v20) ∗
              ((sp + 0x28#64) ↦₃₂ sv.v28) ∗ ((sp + 0x2c#64) ↦₃₂ sv.v2c) ∗
              ((sp + 0x30#64) ↦₆₄ sv.v30) ∗
              memRegion (sp + 0x38#64) 4 ∗ ((sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
              ((sp + 0x40#64) ↦₆₄ sv.v40) ∗
              memRegion (sp + 0x50#64) 4 ∗
              memRegion (sp + 0x80#64) 4 ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
              vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
              vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
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
    (by rw [hsp2_eq]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_receiverChains_x hC hcc x R s0 s2 (s0.readReg64 .lr) _ _
    hpc2 hrun2 hspA2 (by rw [hsp2_eq]; exact hx21_2) hx25_2 hx26_2
    (by rw [hsp2_eq]; exact hx29_2) htr2 h_chains_len
    fun s3 chainsCap' chainsPtr' chains' hchains_len hchains_cap hchains_enc
      hpc3 hrun3 hsp3 hspA3 hx19_3 hx21_3 hx25_3 hx26_3 hx27_3 hx29_3 htr3 hvregs3 => ?_
  have hsp3_eq : s3.sp = sp := hsp3.trans hsp2_eq
  have hx19_3' : s3.readReg64 .x19 = x.dst := hx19_3.trans hx19_2
  rw [hsp2_eq, stackAt_chainClone_eq_alloc_x sp]
  refine SepWPpIn.weaken_pre
    (P' := A.pool ∗
            optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
            ((s3.sp + 0x18#64) ↦₆₄ sv.v18) ∗
            ((s3.sp + 0x20#64) ↦₆₄ sv.v20) ∗
            ((s3.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗
            stackAt s3.sp Stage1X.extHookStack ∗
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
    (by rw [hsp3_eq]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_pendingPreKey_x hC hpc3 hrun3 hspA3 hx25_3 htr3
    fun s4 pendCap' pendPtr' v18' w23' w24' v2c'
      hpc4 hrun4 hsp4 hspA4 hx19_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 htr4 hvregs4 => ?_
  have hsp4_eq : s4.sp = sp := hsp4.trans hsp3_eq
  have hx19_4' : s4.readReg64 .x19 = x.dst := hx19_4.trans hx19_3'
  have hx26_4' : s4.readReg64 .x26 = chainsCap' := hx26_4.trans hx26_3
  have hx27_4' : s4.readReg64 .x27 = chainsPtr' := hx27_4.trans hx27_3
  rw [hsp3_eq]
  refine SepWPpIn.weaken_pre
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
  refine sc_pendingKyber_x hC hpc4 hrun4 hspA4 hx25_4 htr4
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
  refine SepWPpIn.weaken_pre
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
  refine sc_aliceBaseKey_x hC hpc5 hrun5 hspA5 hx25_5 htr5
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
  refine SepWPpIn.weaken_pre
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
  refine sc_pqRatchet_x hC hpc6 hrun6 hspA6 hx25_6 htr6
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
  refine SepWPpIn.weaken_pre
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
  refine sc_epilogue_x dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice' pqCap' pqPtr'
    scCap' sq0 sq1 sq2 sq3 sq4 sq5 v0c' kybCap' kybPtr' pendCap' pendPtr' v18'
    w23' w24' v28' v2c' w288 w28c
    (s0.readReg64 .x29) (s0.readReg64 .x28) (s0.readReg64 .x27)
    (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) _
    hpc7 hrun7 hspA7 hx19_7' hx20_7' hx21_7' hx22_7 hx23_7' hx24_7' hx25_7 hx26_7' hx27_7' hx28_7' htr7
    fun s8 hpc8 hrun8 hsp8 hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8 hx25_8 hx26_8 hx27_8 hx28_8 hx29_8 hlr8 htr8 hvregs8 => ?_
  have hsp8_eq : s8.sp = s0.sp := by
    rw [hsp8, hsp7_eq]
    exact sc_sp_sub_add_0x1d0_x s0.sp
  rw [hsp7_eq]
  apply SepWPpIn.done hpc8 hrun8
  refine ⟨hsp8_eq, ?_, ?_⟩
  · refine ⟨hx19_8, hx20_8, hx21_8, hx22_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8, hx29_8,
      hvregs8.trans (hvregs7.trans (hvregs6.trans (hvregs5.trans (hvregs4.trans (hvregs3.trans hvregs2)))))⟩
  · exact sc_post_entails_x A x s0 s8 localIk' remoteIk' rootPtr'
      chainsCap' chainsPtr' chains' alice' pqCap' pqPtr' sender' scCap'
      sq0 sq1 sq2 sq3 sq4 sq5 v0c' kybCap' kybPtr' pendCap' pendPtr' v18'
      w23' w24' v28' v2c' w288 w28c htr8
      h_pend_rel h_kyb_rel h_alice_eq h_rem_reg h_loc_reg h_loc_deser h_rem_deser
      h_chains_len h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts hloc_bytes hloc_cap hrem_bytes hrem_cap
      hchains_len hchains_cap hchains_enc halice_bytes halice_cap hpq_cap hsc_inl hsc_enc

theorem sepWPp_mono_x {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp Q' Qp' : State → SepProp → Prop}
    (hQ : ∀ sf P_f, Q sf P_f → Q' sf P_f) (hQp : ∀ sf P_f, Qp sf P_f → Qp' sf P_f)
    (h : SepWPp prog ret s P Q Qp) : SepWPp prog ret s P Q' Qp' := by
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨hoom, hmf⟩⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, P_f, hmf, hQ _ _ hq⟩⟩
  · exact ⟨sf, hst, Or.inr (Or.inl ⟨hpan, P_f, hmf, hQp _ _ hqp⟩)⟩
  · exact ⟨sf, hst, Or.inr (Or.inr ⟨hoom, hmf⟩)⟩

/-- `SessionStructure::clone` (`0x240f0`) meets `(sessionCloneSpecX A).inImage img` on `SP2Ext img.base ext`. -/
theorem sessionClone_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    SessionCloneOkX img A ext := by
  apply subroutine_ok_inImage_of_sepWPpIn
  intro x R s0 hpc hrun hpre hs0_align
  simp only [sessionCloneSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion x.dst 344 ∗ sessionStateReprAt A x.src x.G x.s ∗ A.pool ∗ stackAt s0.sp sessionCloneStackX, R, ?_, ?_⟩
  · refine Satisfies.mono ?_ hmem
    exact Entails.of_eq (by ac_rfl)
  · intro hF hsym
    refine sepWPp_mono_x ?_ (fun _ _ h => h)
      (sessionClone_sepWPpIn_x hC x R s0 hpc hrun hs0_align hx0 hx1 hF hsym)
    intro sf P_f ⟨hsp_f, hcc_f, hpost_f⟩
    exact ⟨fun hm => Satisfies.mono (sepConj_mono_left hpost_f) hm, hsp_f, hcc_f⟩

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `80`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem sessionClone_placed_sepWPpLsCl_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (x : SessionCloneGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (blkPl_80).base)
    (hrun : s0.status = .Running)
    (hs0_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.dst)
    (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPpLsCl lsmpl (lsProg_80 H) (s0.readReg64 .lr) s0
      (memRegion x.dst 344 ∗
        sessionStateReprAt A x.src x.G x.s ∗
        A.pool ∗
        stackAt s0.sp sessionCloneStackX)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (sessionCloneSpecX A).post x s0 sf))
      (scPanicPostX A x R s0) := by
  have hcc : ChainCloneLocal1PlacedOkX A H := chain_clone_placed_ok_x hC
  have hscc : SenderChainCloneLocal1PlacedOkX A H := senderChain_clone_placed_ok_x hC
  refine SepWPpLsCl.weaken_pre
    (sc_initial_stack_dst_decomp_x x.dst s0.sp (sessionStateReprAt A x.src x.G x.s) A.pool) ?_
  set sp := s0.sp - 0x1d0#64
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPpLsCl.exists_elim fun rv =>
    SepWPpLsCl.exists_elim fun bq0 => SepWPpLsCl.exists_elim fun bq1 =>
    SepWPpLsCl.exists_elim fun bq2 => SepWPpLsCl.exists_elim fun bq3 =>
    SepWPpLsCl.exists_elim fun bq4 => SepWPpLsCl.exists_elim fun bq5 =>
    SepWPpLsCl.exists_elim fun sv => SepWPpLsCl.exists_elim fun dv => ?_
  unfold sessionStateReprAt
  rw [sc_sessionStateAt_eq A x.src x.G x.s.state]
  simp only [sepConj_assoc]
  refine sepWPpLsCl_pure_2nd fun ⟨h_pend_rel, h_kyb_rel, h_alice_eq, h_rem_reg, h_loc_reg⟩ => ?_
  refine sepWPpLsCl_pure_2nd fun ⟨h_loc_deser, h_rem_deser, h_chains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩ => ?_
  obtain ⟨w288, w28c, _, h_reg_pts⟩ := exists_unpack32_pair_of_length_8 h_reg_len
  have h154 : x.src + 0x150#64 + 4#64 = x.src + 0x154#64 := by bv_arith
  have h_reg_src : ((x.src + 0x150#64) ↦ₛ x.G.regIds) =
      ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) := by
    rw [h_reg_pts (x.src + 0x150#64), h154]
  rw [sc_vecAt_0x48_chains_eq A x.src x.G.chainsCap x.G.chainsPtr x.G.chains
      x.s.state.receiverChains h_chains_len, h_reg_src]
  refine SepWPpLsCl.weaken_pre
    (P' := vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
            scSavedRegsAt (s0.sp - 0x1d0#64) rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25
              rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗
            (A.pool ∗
              vecGhostAt A x.G.localIk x.src ∗
              vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              chunks96_6QAt (sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (sp + 0xf8#64) 104 ∗
              scSpillSlotsAt sp sv.v0c sv.v10 sv.v18 sv.v20 sv.v28 sv.v2c sv.v30 sv.v3c
                sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 sv.v84 sv.v88 ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗ ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
              vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
              optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) ∗
              scDstSlotsAt x.dst dv ∗ stackAt sp chainCloneStackX ∗
              memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              memRegion (sp + 0xf0#64) 8 ∗ memRegion (sp + 0x160#64) 16))
    (Entails.of_eq (by dsimp only [sp]; ac_rfl)) ?_
  refine SepWPpLsCl.weaken_pre
    (sepConj_mono_left (sc_vecBuf_chains_len_lt_x A x.G.chainsCap x.G.chainsPtr x.G.chains
      x.s.state.receiverChains h_chains_len)) ?_
  rw [sepConj_assoc]
  refine SepWPpLsCl.pure_elim fun hrc_lt => ?_
  refine SepWPpLsCl.weaken_pre
    (P' := scSavedRegsAt (s0.sp - 0x1d0#64) rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25
              rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗
            (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              chunks96_6QAt (sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗ memRegion (sp + 0xf8#64) 104 ∗
              scSpillSlotsAt sp sv.v0c sv.v10 sv.v18 sv.v20 sv.v28 sv.v2c sv.v30 sv.v3c
                sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 sv.v84 sv.v88 ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗ ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
              vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
              optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) ∗
              scDstSlotsAt x.dst dv ∗ stackAt sp chainCloneStackX ∗
              memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              memRegion (sp + 0xf0#64) 8 ∗ memRegion (sp + 0x160#64) 16))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sc_prologue_placed_x (rv := rv) hpc hrun hs0_align hx0 hx1
    fun s1 hpc1 hrun1 hsp1 hspA1 hx0_1 hx1_1 hx29_1 htr1 hvregs1 => ?_
  have hsp1_eq : s1.sp = sp := hsp1
  unfold scSpillSlotsAt
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool ∗ vecGhostAt A x.G.localIk x.src ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
            vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
            optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
            chunks96_6QAt (s1.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            memRegion (s1.sp + 0xf8#64) 104 ∗
            ((s1.sp + 0x48#64) ↦₆₄ sv.v48) ∗ ((s1.sp + 0x54#64) ↦₃₂ sv.v54) ∗
            ((s1.sp + 0x58#64) ↦₆₄ sv.v58) ∗ ((s1.sp + 0x60#64) ↦₆₄ sv.v60) ∗
            ((s1.sp + 0x68#64) ↦₆₄ sv.v68) ∗ ((s1.sp + 0x70#64) ↦₆₄ sv.v70) ∗
            ((s1.sp + 0x78#64) ↦₆₄ sv.v78) ∗ ((s1.sp + 0x84#64) ↦₃₂ sv.v84) ∗
            ((s1.sp + 0x88#64) ↦₆₄ sv.v88) ∗
            ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
            ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
            ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
            stackAt s1.sp chainCloneStackX ∗
            (memRegion sp 12 ∗ ((sp + 0x0c#64) ↦₃₂ sv.v0c) ∗
              ((sp + 0x10#64) ↦₆₄ sv.v10) ∗ ((sp + 0x18#64) ↦₆₄ sv.v18) ∗ ((sp + 0x20#64) ↦₆₄ sv.v20) ∗
              ((sp + 0x28#64) ↦₃₂ sv.v28) ∗ ((sp + 0x2c#64) ↦₃₂ sv.v2c) ∗
              ((sp + 0x30#64) ↦₆₄ sv.v30) ∗ memRegion (sp + 0x38#64) 4 ∗ ((sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
              ((sp + 0x40#64) ↦₆₄ sv.v40) ∗ memRegion (sp + 0x50#64) 4 ∗ memRegion (sp + 0x80#64) 4 ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗ ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
              vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
              optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
              ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) ∗
              scDstSlotsAt x.dst dv ∗
              scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
                (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
                (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
                (s0.readReg64 .x19) ∗
              memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              memRegion (sp + 0xf0#64) 8 ∗ memRegion (sp + 0x160#64) 16))
    (by rw [hsp1_eq]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_fields_1_to_4_placed_x hC hscc hpc1 hrun1 hspA1 hx0_1 hx1_1 hx29_1 htr1 hvregs1 hrc_lt
    fun s2 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc2 hrun2 hsp2 hspA2 hx19_2 hx21_2 hx25_2 hx26_2 hx29_2 htr2 hvregs2
      hloc_bytes hloc_cap hrem_bytes hrem_cap hsc_inl hsc_enc => ?_
  have hsp2_eq : s2.sp = sp := hsp2.trans hsp1_eq
  rw [hsp1_eq] at hx21_2 hx29_2 ⊢
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool ∗ ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
            vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
            memRegion (s2.sp + 0xf8#64) 104 ∗ stackAt s2.sp chainCloneStackX ∗
            (vecGhostAt A x.G.localIk x.src ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainHeap A sender' x.s.state.senderChain ∗
              chunks96_6QAt (sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
              ((sp + 0x48#64) ↦₆₄ scCap') ∗ ((sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
              ((sp + 0x58#64) ↦₆₄ rootPtr') ∗ ((sp + 0x60#64) ↦₆₄ 32#64) ∗
              ((sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗ ((sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
              ((sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗ ((sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              memRegion sp 12 ∗ ((sp + 0x0c#64) ↦₃₂ sv.v0c) ∗
              ((sp + 0x10#64) ↦₆₄ sv.v10) ∗ ((sp + 0x18#64) ↦₆₄ sv.v18) ∗ ((sp + 0x20#64) ↦₆₄ sv.v20) ∗
              ((sp + 0x28#64) ↦₃₂ sv.v28) ∗ ((sp + 0x2c#64) ↦₃₂ sv.v2c) ∗ ((sp + 0x30#64) ↦₆₄ sv.v30) ∗
              memRegion (sp + 0x38#64) 4 ∗ ((sp + 0x3c#64) ↦₃₂ sv.v3c) ∗ ((sp + 0x40#64) ↦₆₄ sv.v40) ∗
              memRegion (sp + 0x50#64) 4 ∗ memRegion (sp + 0x80#64) 4 ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗ vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
              vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
              optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
              ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) ∗
              scDstSlotsAt x.dst dv ∗
              scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
                (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
                (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
                (s0.readReg64 .x19) ∗
              memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              memRegion (sp + 0xf0#64) 8 ∗ memRegion (sp + 0x160#64) 16))
    (by rw [hsp2_eq]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_receiverChains_placed_x hC hcc x R s0 s2 (s0.readReg64 .lr) _ _
    hpc2 hrun2 hspA2 (by rw [hsp2_eq]; exact hx21_2) hx25_2 hx26_2
    (by rw [hsp2_eq]; exact hx29_2) htr2 h_chains_len
    fun s3 chainsCap' chainsPtr' chains' hchains_len hchains_cap hchains_enc
      hpc3 hrun3 hsp3 hspA3 hx19_3 hx21_3 hx25_3 hx26_3 hx27_3 hx29_3 htr3 hvregs3 => ?_
  have hsp3_eq : s3.sp = sp := hsp3.trans hsp2_eq
  have hx19_3' : s3.readReg64 .x19 = x.dst := hx19_3.trans hx19_2
  rw [hsp2_eq, stackAt_chainClone_eq_alloc_x sp]
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool ∗ optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
            ((s3.sp + 0x18#64) ↦₆₄ sv.v18) ∗ ((s3.sp + 0x20#64) ↦₆₄ sv.v20) ∗
            ((s3.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗ stackAt s3.sp Stage1X.extHookStack ∗
            (((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
              memRegion (sp + 0xf8#64) 104 ∗ memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗
              vecGhostAt A x.G.localIk x.src ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainHeap A sender' x.s.state.senderChain ∗
              chunks96_6QAt (sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
              ((sp + 0x48#64) ↦₆₄ scCap') ∗ ((sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
              ((sp + 0x58#64) ↦₆₄ rootPtr') ∗ ((sp + 0x60#64) ↦₆₄ 32#64) ∗
              ((sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗ ((sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
              ((sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗ ((sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              memRegion sp 12 ∗ ((sp + 0x0c#64) ↦₃₂ sv.v0c) ∗ ((sp + 0x10#64) ↦₆₄ sv.v10) ∗
              ((sp + 0x28#64) ↦₃₂ sv.v28) ∗ ((sp + 0x30#64) ↦₆₄ sv.v30) ∗
              memRegion (sp + 0x38#64) 4 ∗ ((sp + 0x3c#64) ↦₃₂ sv.v3c) ∗ ((sp + 0x40#64) ↦₆₄ sv.v40) ∗
              memRegion (sp + 0x50#64) 4 ∗ memRegion (sp + 0x80#64) 4 ∗
              ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗ vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
              vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
              optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
              ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) ∗
              scDstSlotsAt x.dst dv ∗
              scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
                (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
                (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
                (s0.readReg64 .x19) ∗
              memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
              memRegion (sp + 0xf0#64) 8 ∗ memRegion (sp + 0x160#64) 16))
    (by rw [hsp3_eq]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_pendingPreKey_placed_x hC hpc3 hrun3 hspA3 hx25_3 htr3
    fun s4 pendCap' pendPtr' v18' w23' w24' v2c'
      hpc4 hrun4 hsp4 hspA4 hx19_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 htr4 hvregs4 => ?_
  have hsp4_eq : s4.sp = sp := hsp4.trans hsp3_eq
  have hx19_4' : s4.readReg64 .x19 = x.dst := hx19_4.trans hx19_3'
  have hx26_4' : s4.readReg64 .x26 = chainsCap' := hx26_4.trans hx26_3
  have hx27_4' : s4.readReg64 .x27 = chainsPtr' := hx27_4.trans hx27_3
  have hvregs4_eq : s4.calleeSavedVRegs = s0.calleeSavedVRegs :=
    hvregs4.trans (hvregs3.trans hvregs2)
  rw [hsp3_eq]
  refine sc_tail_from_s4_placed_x hC x R s0 s4 sv dv w288 w28c
    localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
    chainsCap' chainsPtr' chains' pendCap' pendPtr' v18' w23' w24' v2c'
    hpc4 hrun4 hsp4_eq hspA4 hx19_4' hx23_4 hx24_4 hx25_4 hx26_4' hx27_4' hx28_4 htr4 hvregs4_eq
    fun s8 kybCap' kybPtr' v28' alice' pqCap' pqPtr' v0c'
      hpc8 hrun8 hsp8 hcs8 htr8 halice_bytes halice_cap hpq_cap => ?_
  dsimp only
  have hsp8_eq : s8.sp = s0.sp := hsp8.trans (sc_sp_sub_add_0x1d0_x s0.sp)
  apply SepWPp.done hpc8 hrun8
  refine ⟨hsp8_eq, hcs8, ?_⟩
  exact sc_post_entails_x A x s0 s8 localIk' remoteIk' rootPtr'
    chainsCap' chainsPtr' chains' alice' pqCap' pqPtr' sender' scCap'
    sq0 sq1 sq2 sq3 sq4 sq5 v0c' kybCap' kybPtr' pendCap' pendPtr' v18'
    w23' w24' v28' v2c' w288 w28c htr8
    h_pend_rel h_kyb_rel h_alice_eq h_rem_reg h_loc_reg h_loc_deser h_rem_deser
    h_chains_len h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts hloc_bytes hloc_cap hrem_bytes hrem_cap
    hchains_len hchains_cap hchains_enc halice_bytes halice_cap hpq_cap hsc_inl hsc_enc

/-- Block `80` (`<SessionStructure as Clone>::clone`) meets
`withLsCodeLoaded lsmpl (sessionCloneSpecX A)` on `lsProg_80 H`. -/
theorem sessionClone_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) :
    SessionClonePlacedOkX A H := by
  apply subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
  intro x R s0 hpc hrun hpre hs0_align
  simp only [sessionCloneSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion x.dst 344 ∗ sessionStateReprAt A x.src x.G x.s ∗ A.pool ∗ stackAt s0.sp sessionCloneStackX, R, ?_, ?_⟩
  · refine Satisfies.mono ?_ hmem
    exact Entails.of_eq (by ac_rfl)
  · intro hcl
    refine sepWPp_mono_x ?_ (fun _ _ h => h)
      (sessionClone_placed_sepWPpLsCl_x hC x R s0 hpc hrun hs0_align hx0 hx1 hcl)
    intro sf P_f ⟨hsp_f, hcc_f, hpost_f⟩
    exact ⟨fun hm => Satisfies.mono (sepConj_mono_left hpost_f) hm, hsp_f, hcc_f⟩

theorem sessionClone_placed_ok_cl [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H) :
    subroutine_ok callerProg (lsmpl.base 80) (withLsCl lsmpl (sessionCloneSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (sessionClone_placed_ok_ext hC)

end Placed

end CryptoVerification.E2E.Record.Serialization
