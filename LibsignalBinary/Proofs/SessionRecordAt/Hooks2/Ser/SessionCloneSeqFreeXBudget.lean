/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneCkXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEntryXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.EpilogueReassemblyXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.KyberBaseKeyPqStateXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.PrologueFields1To4XPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ReceiverChainsPendingPreKeyXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.SessionCloneTailXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionClone
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import ProofLib.SepLogic.WPp

/-!
# Exact-Event (`SegCloneEnv`) `SessionStructure::clone` (Block `80`)

Verifies `<SessionStructure as Clone>::clone` (Block `80`) at `sessionCloneStackX` against the exact
deterministic event specification `sessionCloneSegSpecX M A lim` (`evs = segCloneEvents x.G x.s.state`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneSeqFreeXBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl lsρ
  lsMemcpySym withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (vecU8At vecU8Buf vecBuf)
open CryptoVerification.LibsignalSessionRepr (
  VecGhost ChainGhost vecGhostAt chainAt leBytes
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost SenderChainGhost optSenderChainAt optTailVecAt
)
open CryptoVerification.LibsignalPublicApiRepr (
  PendingRel KyberRel sessionStateReprAt
)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack sessionMemcpySpec ls_subroutine_ok_cl_of_callee
)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (chainCloneStackX)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  OptSenderChainInline bytes104OfW6Q chunks96_6QAt optSenderChainHeap
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  exists_unpack32_pair_of_length_8
)
open CryptoVerification.E2E.Record.Placed (blkPl_80 lsProg_80)
open CryptoVerification.E2E.Record.Serialization (
  SessionCloneGhost encSessionMem encSenderFieldMem encChainMem
  sc_vecBuf_chains_len_lt sc_initial_stack_dst_decomp_x
  sc_sp_sub_add_0x1d0 sepWPp_mono_x
)
open CryptoVerification.E2E.Record.Serialization.SessionCloneAux (
  ScOptPendClone ScOptKybClone
  scDstSlotsAt scDstSlotsWrittenAt scSpillSlotsAt scSavedRegsAt
  sc_sessionStateAt_eq sc_vecAt_0x48_chains_eq
  sc_srcSessionAt_reassemble scDstSlotsWrittenAt_entails_sessionAt
  sc_stack_reassemble_x
)
open Proofs.libsignal.Hooks2 (sessionCloneStackX)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits FitsEvents FitsEnv
  RustCliAllocBudget fitsEvents_append
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SegCloneEnv segCloneEvents optTailCloneEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  SepWPpLsCl subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget (
  ChainCloneLocal1PlacedOkX SenderChainCloneLocal1PlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseXBudget (
  sc_memcpy_placed_ok_at_x sepWPpLsCl_pure_2nd_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEntryXPlacedBudget (
  chain_clone_placed_ok_x senderChain_clone_placed_ok_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.PrologueFields1To4XPlacedBudget (
  scFields1To4Events sc_prologue_placed_x sc_fields_1_to_4_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ReceiverChainsPendingPreKeyXPlacedBudget (
  scReceiverChainsEvents sc_receiverChains_placed_x sc_pendingPreKey_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.SessionCloneTailXPlacedBudget (
  scTailEvents sc_tail_from_s4_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneXBudget (
  segCloneEvents_decomp_x
)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Exact `SegCloneEnv` specification and helpers -/

/-- Exact-event (`SegCloneEnv x.G x.s.state`) `sessionCloneSpec` at `sessionCloneStackX`. -/
def sessionCloneSegSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SessionCloneGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧
      FitsEnv M lim st (SegCloneEnv x.G x.s.state)⌝ ∗
      sessionStateReprAt A.repAlloc x.src x.G x.s ∗ memRegion x.dst 344 ∗
      A.pool lim st s ∗ stackAt s.sp sessionCloneStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SegCloneEnv x.G x.s.state evs⌝ ∗
      sessionStateReprAt A.repAlloc x.src x.G x.s ∗
      (∃∗ G' : SessionGhost, ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A.repAlloc x.dst G' x.s) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp sessionCloneStackX

abbrev SessionCloneSegPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_80 H) (blkPl_80).base
    (withLsCodeLoaded lsmpl (sessionCloneSegSpecX M A lim))

private theorem stackAt_chainClone_eq_alloc_x (sp : BitVec 64) :
    stackAt sp chainCloneStackX =
      memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗ stackAt sp extHookStack := by
  have h := stackAt_split_bottom sp extHookStack 208 (by decide)
  rwa [show extHookStack + 208 = chainCloneStackX by decide] at h

private theorem sc_memcpy_vm_ok_at_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (withVmPreserved (sessionMemcpySpec extHookStack))) := by
  simpa [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec,
    withVmPreserved] using sc_memcpy_placed_ok_at_x hC

/-! ## Postcondition reassembly -/

theorem sc_seg_post_entails_x {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : SessionCloneGhost) (st : M.σ) (s0 sf : State)
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
      (vecGhostAt A.repAlloc x.G.localIk x.src ∗
        vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
        vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
        ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
        ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
        ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
        vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.s.state.receiverChains) ∗
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
        vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr'
          (chains'.zip x.s.state.receiverChains) ∗
        vecU8Buf A.repAlloc alice'.cap alice'.ptr alice'.bytes ∗
        vecU8Buf A.repAlloc pqCap' pqPtr' x.s.state.pqRatchetState ∗
        optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
        ScOptPendClone A.repAlloc x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
        ScOptKybClone A.repAlloc x.G.kyber kybCap' kybPtr' v28') ∗
      A.pool lim (M.stepEvents (segCloneEvents x.G x.s.state) st) sf ∗
      (memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
        stackAt sp chainCloneStackX ∗
        memRegion (sp + 0xf0#64) 8 ∗
        memRegion (sp + 0xf8#64) 104 ∗
        memRegion (sp + 0x160#64) 16)) ⊢
      (sessionCloneSegSpecX M A lim).post (x, st) s0 sf := by
  dsimp only [sessionCloneSegSpecX, chainCloneStackX]
  set sp := s0.sp - 0x1d0#64
  apply Entails.sepExists_right (segCloneEvents x.G x.s.state)
  apply Entails.pure_right ⟨htr, rfl⟩
  have hsrc :
      (vecGhostAt A.repAlloc x.G.localIk x.src ∗
        vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
        vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
        ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
        ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
        ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
        vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.s.state.receiverChains) ∗
        vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
        vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
        optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
        optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
        optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
        ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        ((x.src + 0x150#64) ↦₃₂ w288) ∗
        ((x.src + 0x154#64) ↦₃₂ w28c)) ⊢
      sessionStateReprAt A.repAlloc x.src x.G x.s := by
    refine Entails.trans ?_
      (sc_srcSessionAt_reassemble A.repAlloc x w288 w28c h_pend_rel h_kyb_rel h_alice_eq h_rem_reg h_loc_reg
        h_loc_deser h_rem_deser h_chains_len h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts)
    rw [sc_vecAt_0x48_chains_eq A.repAlloc x.src x.G.chainsCap x.G.chainsPtr x.G.chains
        x.s.state.receiverChains h_chains_len]
    exact Entails.of_eq (by sep_ac_rfl)
  have hdst :=
    scDstSlotsWrittenAt_entails_sessionAt A.repAlloc x localIk' remoteIk' rootPtr'
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
  dsimp only at hstk
  refine Entails.trans
    (Q := (vecGhostAt A.repAlloc x.G.localIk x.src ∗
            vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
            vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
            ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
            ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
            ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
            vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.s.state.receiverChains) ∗
            vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
            vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
            optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
            optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
            optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
            ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
            ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
            ((x.src + 0x150#64) ↦₃₂ w288) ∗
            ((x.src + 0x154#64) ↦₃₂ w28c)) ∗
          (scDstSlotsWrittenAt x.dst localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
            pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w23' w24' v18' v2c'
            kybCap' kybPtr' v28' x.s.state.sessionVersion x.s.state.previousCounter w288 w28c ∗
            vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
            vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
            vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
            vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr'
              (chains'.zip x.s.state.receiverChains) ∗
            vecU8Buf A.repAlloc alice'.cap alice'.ptr alice'.bytes ∗
            vecU8Buf A.repAlloc pqCap' pqPtr' x.s.state.pqRatchetState ∗
            optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
            ScOptPendClone A.repAlloc x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
            ScOptKybClone A.repAlloc x.G.kyber kybCap' kybPtr' v28') ∗
          A.pool lim (M.stepEvents (segCloneEvents x.G x.s.state) st) sf ∗
          (memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
            stackAt sp (0xd0 + Proofs.libsignal.Stage1X.extHookStack) ∗
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
    (Entails.of_eq (by dsimp only [Proofs.libsignal.Stage1X.extHookStack]; sep_ac_rfl)) ?_
  exact sepConj_mono hsrc (sepConj_mono hdst (sepConj_mono_right hstk))

/-! ## Block `80` `SepWPpLsCl` and `subroutine_ok` proofs -/

set_option maxHeartbeats 1200000 in
theorem sessionClone_seg_placed_sepWPpLsCl_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (x : SessionCloneGhost) (st : M.σ) (s0 : State)
    {Qp : State → SepProp → Prop}
    (hfits_env : FitsEnv M lim st (SegCloneEnv x.G x.s.state))
    (hqp_false : ∀ sf F', sf.status = .Panicked → Qp sf (⌜False⌝ ∗ F'))
    (hpc : s0.pc = (blkPl_80).base)
    (hrun : s0.status = .Running)
    (hs0_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.dst)
    (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPpLsCl lsmpl (lsProg_80 H) (s0.readReg64 .lr) s0
      (memRegion x.dst 344 ∗
        sessionStateReprAt A.repAlloc x.src x.G x.s ∗
        A.pool lim st s0 ∗
        stackAt s0.sp sessionCloneStackX)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (sessionCloneSegSpecX M A lim).post (x, st) s0 sf))
      Qp := by
  have hcc : ChainCloneLocal1PlacedOkX M A lim H := chain_clone_placed_ok_x hC
  have hscc : SenderChainCloneLocal1PlacedOkX M A lim H := senderChain_clone_placed_ok_x hC
  have hmemcpy := sc_memcpy_vm_ok_at_x hC
  refine SepWPpLsCl.weaken_pre
    (sc_initial_stack_dst_decomp_x x.dst s0.sp
      (sessionStateReprAt A.repAlloc x.src x.G x.s) (A.pool lim st s0)) ?_
  set sp := s0.sp - 0x1d0#64
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPpLsCl.exists_elim fun rv =>
    SepWPpLsCl.exists_elim fun bq0 => SepWPpLsCl.exists_elim fun bq1 =>
    SepWPpLsCl.exists_elim fun bq2 => SepWPpLsCl.exists_elim fun bq3 =>
    SepWPpLsCl.exists_elim fun bq4 => SepWPpLsCl.exists_elim fun bq5 =>
    SepWPpLsCl.exists_elim fun sv => SepWPpLsCl.exists_elim fun dv => ?_
  unfold sessionStateReprAt
  rw [sc_sessionStateAt_eq A.repAlloc x.src x.G x.s.state]
  simp only [sepConj_assoc]
  refine sepWPpLsCl_pure_2nd_x fun ⟨h_pend_rel, h_kyb_rel, h_alice_eq, h_rem_reg, h_loc_reg⟩ => ?_
  refine sepWPpLsCl_pure_2nd_x fun ⟨h_loc_deser, h_rem_deser, h_chains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩ => ?_
  have hfits_seg : FitsEvents M lim st (segCloneEvents x.G x.s.state) :=
    hfits_env (segCloneEvents x.G x.s.state) rfl
  rw [segCloneEvents_decomp_x x] at hfits_seg
  obtain ⟨hfits_14, hfits_rem1⟩ := (fitsEvents_append M lim _ _ st).mp hfits_seg
  let st2 := M.stepEvents (scFields1To4Events x) st
  obtain ⟨hfits_rc, hfits_rem2⟩ := (fitsEvents_append M lim _ _ st2).mp hfits_rem1
  let st3 := M.stepEvents (scReceiverChainsEvents x) st2
  obtain ⟨hfits_pend, hfits_tail⟩ := (fitsEvents_append M lim _ _ st3).mp hfits_rem2
  let st4 := M.stepEvents (optTailCloneEvents x.G.pending) st3
  have hst_final :
      M.stepEvents (scTailEvents x) st4 = M.stepEvents (segCloneEvents x.G x.s.state) st := by
    dsimp only [st4, st3, st2]
    rw [← M.stepEvents_append, ← M.stepEvents_append, ← M.stepEvents_append,
        ← segCloneEvents_decomp_x x]
  obtain ⟨w288, w28c, _, h_reg_pts⟩ := exists_unpack32_pair_of_length_8 h_reg_len
  have h154 : x.src + 0x150#64 + 4#64 = x.src + 0x154#64 := by bv_arith
  have h_reg_src : ((x.src + 0x150#64) ↦ₛ x.G.regIds) =
      ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) := by
    rw [h_reg_pts (x.src + 0x150#64), h154]
  rw [sc_vecAt_0x48_chains_eq A.repAlloc x.src x.G.chainsCap x.G.chainsPtr x.G.chains
      x.s.state.receiverChains h_chains_len, h_reg_src]
  refine SepWPpLsCl.weaken_pre
    (P' := vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr
             (x.G.chains.zip x.s.state.receiverChains) ∗
           (A.pool lim st s0 ∗
             scSavedRegsAt sp rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25
               rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗
             scDstSlotsAt x.dst dv ∗
             vecGhostAt A.repAlloc x.G.localIk x.src ∗
             vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
             vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
             ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
             ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
             ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
             vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
             vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
             optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
             optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
             optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
             ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
             ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
             ((x.src + 0x150#64) ↦₃₂ w288) ∗
             ((x.src + 0x154#64) ↦₃₂ w28c) ∗
             memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
             stackAt sp chainCloneStackX ∗
             scSpillSlotsAt sp sv.v0c sv.v10 sv.v18 sv.v20 sv.v28 sv.v2c sv.v30 sv.v3c
               sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 sv.v84 sv.v88 ∗
             chunks96_6QAt (sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
             memRegion (sp + 0xf0#64) 8 ∗
             memRegion (sp + 0xf8#64) 104 ∗
             memRegion (sp + 0x160#64) 16))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWPpLsCl.weaken_pre
    (sepConj_mono_left (sc_vecBuf_chains_len_lt A.repAlloc x.G.chainsCap x.G.chainsPtr
      x.G.chains x.s.state.receiverChains h_chains_len)) ?_
  simp only [sepConj_assoc]
  refine SepWPpLsCl.pure_elim fun hrc_lt => ?_
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool lim st s0 ∗
           scSavedRegsAt (s0.sp - 0x1d0#64) rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25
             rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗
           (vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.s.state.receiverChains) ∗
            scDstSlotsAt x.dst dv ∗
            vecGhostAt A.repAlloc x.G.localIk x.src ∗
            vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
            vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
            ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗
            ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
            ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
            vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
            vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
            optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
            optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
            optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
            ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
            ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
            ((x.src + 0x150#64) ↦₃₂ w288) ∗
            ((x.src + 0x154#64) ↦₃₂ w28c) ∗
            memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
            stackAt sp chainCloneStackX ∗
            scSpillSlotsAt sp sv.v0c sv.v10 sv.v18 sv.v20 sv.v28 sv.v2c sv.v30 sv.v3c
              sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 sv.v84 sv.v88 ∗
            chunks96_6QAt (sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            memRegion (sp + 0xf0#64) 8 ∗
            memRegion (sp + 0xf8#64) 104 ∗
            memRegion (sp + 0x160#64) 16))
    (Entails.of_eq (by dsimp only [sp]; sep_ac_rfl)) ?_
  refine sc_prologue_placed_x hpc hrun hs0_align hx0 hx1
    fun s1 hpc1 hrun1 hsp1_eq hspA1 hx0_1 hx1_1 hx29_1 htr1 hvregs1 => ?_
  unfold scSpillSlotsAt
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool lim st s1 ∗
           vecGhostAt A.repAlloc x.G.localIk x.src ∗
           vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
           vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
           optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
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
            ((sp + 0x28#64) ↦₃₂ sv.v28) ∗ ((sp + 0x2c#64) ↦₃₂ sv.v2c) ∗ ((sp + 0x30#64) ↦₆₄ sv.v30) ∗
            memRegion (sp + 0x38#64) 4 ∗ ((sp + 0x3c#64) ↦₃₂ sv.v3c) ∗ ((sp + 0x40#64) ↦₆₄ sv.v40) ∗
            memRegion (sp + 0x50#64) 4 ∗ memRegion (sp + 0x80#64) 4 ∗
            ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗ ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
            vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.s.state.receiverChains) ∗
            vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
            vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
            optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
            optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
            ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) ∗
            scDstSlotsAt x.dst dv ∗
            scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
              (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
              (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
              (s0.readReg64 .x19) ∗
            memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
            memRegion (sp + 0xf0#64) 8 ∗ memRegion (sp + 0x160#64) 16))
    (by rw [hsp1_eq]; dsimp only [sp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine sc_fields_1_to_4_placed_x hC.alloc hmemcpy hscc hfits_14 hqp_false
    hpc1 hrun1 hspA1 hx0_1 hx1_1 hx29_1 htr1 hvregs1 hrc_lt
    fun s2 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc2 hrun2 hsp2 hspA2 hx19_2 hx21_2 hx25_2 hx26_2 hx29_2 htr2 hvregs2
      hloc_bytes hloc_cap hrem_bytes hrem_cap hsc_inl hsc_enc => ?_
  have hsp2_eq : s2.sp = sp := hsp2.trans hsp1_eq
  rw [hsp1_eq] at hx21_2 hx29_2 ⊢
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool lim st2 s2 ∗
           ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr
             (x.G.chains.zip x.s.state.receiverChains) ∗
           memRegion (s2.sp + 0xf8#64) 104 ∗ stackAt s2.sp chainCloneStackX ∗
           (vecGhostAt A.repAlloc x.G.localIk x.src ∗ vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
            vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
            optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
            vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
            vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
            vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
            optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
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
            ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗ vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
            vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
            optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
            optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
            ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) ∗
            scDstSlotsAt x.dst dv ∗
            scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
              (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
              (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
              (s0.readReg64 .x19) ∗
            memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
            memRegion (sp + 0xf0#64) 8 ∗ memRegion (sp + 0x160#64) 16))
    (by rw [hsp2_eq]; dsimp only [st2, sp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine sc_receiverChains_placed_x hC.alloc hcc hfits_rc hqp_false
    hpc2 hrun2 hspA2 (by rw [hsp2_eq]; exact hx21_2) hx25_2 hx26_2
    (by rw [hsp2_eq]; exact hx29_2) htr2 h_chains_len
    fun s3 chainsCap' chainsPtr' chains' hchains_len hchains_cap hchains_enc
      hpc3 hrun3 hsp3 hspA3 hx19_3 hx21_3 hx25_3 hx26_3 hx27_3 hx29_3 htr3 hvregs3 => ?_
  have hsp3_eq : s3.sp = sp := hsp3.trans hsp2_eq
  have hx19_3' : s3.readReg64 .x19 = x.dst := hx19_3.trans hx19_2
  rw [hsp2_eq, stackAt_chainClone_eq_alloc_x sp]
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool lim st3 s3 ∗ optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
           ((s3.sp + 0x18#64) ↦₆₄ sv.v18) ∗ ((s3.sp + 0x20#64) ↦₆₄ sv.v20) ∗
           ((s3.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗ stackAt s3.sp extHookStack ∗
           (((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
            vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.s.state.receiverChains) ∗
            vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr'
              (chains'.zip x.s.state.receiverChains) ∗
            memRegion (sp + 0xf8#64) 104 ∗ memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗
            vecGhostAt A.repAlloc x.G.localIk x.src ∗ vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
            vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
            optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
            vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
            vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
            vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
            optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
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
            ((x.src + 0x48#64) ↦₆₄ x.G.chainsCap) ∗ vecGhostAt A.repAlloc x.G.alice (x.src + 0x60#64) ∗
            vecU8At A.repAlloc (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
            optTailVecAt A.repAlloc 32 (x.src + 0x128#64) x.G.kyber ∗
            ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) ∗
            scDstSlotsAt x.dst dv ∗
            scSavedRegsAt sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
              (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24)
              (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20)
              (s0.readReg64 .x19) ∗
            memRegion (s0.sp - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
            memRegion (sp + 0xf0#64) 8 ∗ memRegion (sp + 0x160#64) 16))
    (by rw [hsp3_eq]; dsimp only [st3, sp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine sc_pendingPreKey_placed_x hC.alloc hmemcpy hfits_pend
    hpc3 hrun3 hspA3 hx25_3 htr3
    fun s4 pendCap' pendPtr' v18' w23' w24' v2c'
      hpc4 hrun4 hsp4 hspA4 hx19_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 htr4 hvregs4 => ?_
  have hsp4_eq : s4.sp = sp := hsp4.trans hsp3_eq
  have hx19_4' : s4.readReg64 .x19 = x.dst := hx19_4.trans hx19_3'
  have hx26_4' : s4.readReg64 .x26 = chainsCap' := hx26_4.trans hx26_3
  have hx27_4' : s4.readReg64 .x27 = chainsPtr' := hx27_4.trans hx27_3
  have hvregs4_eq : s4.calleeSavedVRegs = s0.calleeSavedVRegs :=
    hvregs4.trans (hvregs3.trans hvregs2)
  rw [hsp3_eq]
  refine sc_tail_from_s4_placed_x hC.alloc hmemcpy x st4 s0 s4 sv dv w288 w28c
    localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
    chainsCap' chainsPtr' chains' pendCap' pendPtr' v18' w23' w24' v2c' hfits_tail
    hpc4 hrun4 hsp4_eq hspA4 hx19_4' hx23_4 hx24_4 hx25_4 hx26_4' hx27_4' hx28_4 htr4 hvregs4_eq
    fun s8 kybCap' kybPtr' v28' alice' pqCap' pqPtr' v0c'
      hpc8 hrun8 hsp8 hcs8 htr8 halice_bytes halice_cap hpq_cap => ?_
  dsimp only
  rw [hst_final]
  have hsp8_eq : s8.sp = s0.sp := hsp8.trans (sc_sp_sub_add_0x1d0 s0.sp)
  apply SepWPp.done hpc8 hrun8
  refine ⟨hsp8_eq, hcs8, ?_⟩
  exact sc_seg_post_entails_x A lim x st s0 s8 localIk' remoteIk' rootPtr'
    chainsCap' chainsPtr' chains' alice' pqCap' pqPtr' sender' scCap'
    sq0 sq1 sq2 sq3 sq4 sq5 v0c' kybCap' kybPtr' pendCap' pendPtr' v18'
    w23' w24' v28' v2c' w288 w28c htr8
    h_pend_rel h_kyb_rel h_alice_eq h_rem_reg h_loc_reg h_loc_deser h_rem_deser
    h_chains_len h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts hloc_bytes hloc_cap hrem_bytes hrem_cap
    hchains_len hchains_cap hchains_enc halice_bytes halice_cap hpq_cap hsc_inl hsc_enc

/-- Block `80` (`<SessionStructure as Clone>::clone`) meets
`withLsCodeLoaded lsmpl (sessionCloneSegSpecX M A lim)` on `lsProg_80 H`. -/
theorem sessionClone_seg_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    SessionCloneSegPlacedOkX M A lim H := by
  apply subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
  intro ⟨x, st⟩ R s0 hpc hrun hpre hs0_align
  simp only [sessionCloneSegSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfits_env⟩, hmem⟩
  refine ⟨memRegion x.dst 344 ∗ sessionStateReprAt A.repAlloc x.src x.G x.s ∗
      A.pool lim st s0 ∗ stackAt s0.sp sessionCloneStackX, R, ?_, ?_⟩
  · refine Satisfies.mono ?_ hmem
    exact Entails.of_eq (by sep_ac_rfl)
  · intro hcl
    refine sepWPp_mono_x ?_ (fun _ _ h => h)
      (sessionClone_seg_placed_sepWPpLsCl_x hC x st s0
        (Qp := fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (sessionCloneSegSpecX M A lim).onPanic (x, st) s0 sf ∗ R))
        hfits_env
        (fun _ F' _ hm => by
          rw [sepConj_assoc] at hm
          exact (not_satisfies_false_sepConj hm).elim)
        hpc hrun hs0_align hx0 hx1 hcl)
    intro sf P_f ⟨hsp_f, hcc_f, hpost_f⟩
    exact ⟨fun hm => Satisfies.mono (sepConj_mono_left hpost_f) hm, hsp_f, hcc_f⟩

theorem sessionClone_seg_placed_ok_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 80) (withLsCl lsmpl (sessionCloneSegSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (sessionClone_seg_placed_ok_ext hC)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneSeqFreeXBudget
