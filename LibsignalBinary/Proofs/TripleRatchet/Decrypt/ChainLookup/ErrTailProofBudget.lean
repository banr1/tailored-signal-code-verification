/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
public import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessageBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSymBudget
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable `ErrTail` Contracts

Proves budget-threaded `[LibsignalPlacement]` `ErrTail` contracts (`errTail_all_steps_wp_placed`,
`errTail_placed_ok`, `errTail_placed_ok_x`) over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProofBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession
  (Crypto SessionState SignalProtocolError TripleRatchet)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc arrayAt)
open CryptoVerification.LibsignalSessionRepr (chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr
  (decryptDraws protocolAddressAt sessionStateAt signalMessageAt speFnAt speWord tapeAfter
   utf8 uuidTryParse vecResultAt)
open CryptoVerification.LibsignalTripleRatchet
  (SpqrModel TrGhost TryDecryptGhost decResultFnAt logOff trAt)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (dropChainStack lsRustDeallocSym)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (speBodyAt speTag tryDecryptCommonHeap tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
  (SepWP.bind_framed SepWP.bind_framed_lscl SepWP.mono_pre
   blkPC_131 blkPl_131 chains_recombine_entails decRel_afterTrFrom
   errTailPC_placed errTail_stack_recombine
   exists_words3_of_memRegion_24 exists_words5_of_errTailBody exists_words5_of_speBodyAt
   exists_words6_of_memRegion_48 retEpiloguePC_placed
   sepWP_to_reaches_pc_midMeta_placed stackAt_dropChainStack_sub
   stackAt_tryDecryptSubStack_sub trAt_expose_errTail
   tryDecryptDummyImg tryDecryptMidMeta_placed tryDecryptWPInv words5At)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
  (tryDecryptFnSpecPlaced tryDecryptSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
  (ErrTailStateX_placed ErrTailState_placed
   reaches_epilogue_to_outcome_seam_fn_placed reaches_epilogue_to_outcome_seam_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSymBudget
  (errTail_copy_spe_wp_placed errTail_dealloc_chains_freeOnly_wp_placed
   errTail_dealloc_pq_freeOnly_wp_placed errTail_drop_chains_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
  (chainAt_atState_fn invalidMessageStrAt_atState live_atState
   protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState
   speAt_atState vecResultAt_atState vecU8_atState)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem speFnAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (fnName : List (BitVec 8)) (a : BitVec 64) (e : SignalProtocolError) :
    speFnAt (A.atState lim st s) fnName a e = speFnAt A.repAlloc fnName a e := by
  cases e <;> simp only [speFnAt, speAt_atState, invalidMessageStrAt_atState, vecU8_atState]

private theorem decResultFnAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : BitVec 64) (res : Except SignalProtocolError (List (BitVec 8))) :
    decResultFnAt (A.atState lim st s) r res = decResultFnAt A.repAlloc r res := by
  cases res with
  | ok _ => simp only [decResultFnAt, vecU8_atState]
  | error e => exact speFnAt_atState A lim st s _ _ e

private theorem errTail_chains_re_entails {A : RustAlloc} {P_pool : SepProp}
    {sp : BitVec 64} {S_in S_out : Nat} {R_rem : SepProp}
    (hstack : stackAt sp S_in = stackAt sp S_out ∗ R_rem)
    {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {w0 w1 w2 w3 w4 ret tag : BitVec 64}
    (hcs_le : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat)
    (hcs_lt : trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63) :
    let cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
    (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ P_pool ∗ stackAt sp S_in) ∗
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
       ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
       ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
       words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
       (if trG.pq.cap = 0#64 then emp
        else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)))) ⊢
    ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
      (if trG.ratchet.chainsCap = 0#64 then emp
       else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
         memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
      P_pool ∗ stackAt sp S_out) ∗
     (R_rem ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
      ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
      ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
      ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
      words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
      (if trG.pq.cap = 0#64 then emp
       else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by
  dsimp only; set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  rw [hstack]
  have hcomm1 :
      (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ P_pool ∗ (stackAt sp S_out ∗ R_rem)) ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
         ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
         words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)))) =
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       (memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗
        (if trG.ratchet.chainsCap = 0#64 then emp
         else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
           memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104))) ∗
       (P_pool ∗ stackAt sp S_out ∗ R_rem ∗
        ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
        ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
        words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by sep_ac_rfl
  have hcomm2 :
      ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
        (if trG.ratchet.chainsCap = 0#64 then emp
         else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
           memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
        P_pool ∗ stackAt sp S_out) ∗
       (R_rem ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
        ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
        ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
        ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) =
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
       (P_pool ∗ stackAt sp S_out ∗ R_rem ∗
        ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
        ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
        words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by sep_ac_rfl
  rw [hcomm1, hcomm2]
  exact sepConj_mono_right (sepConj_mono_left (chains_recombine_entails hcs_le hcs_lt))

/-! ## Multi-Placed (`[LibsignalPlacement]`) Budget-Threaded `ErrTail` Contracts -/

theorem errTail_all_steps_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    {ret tag : BitVec 64} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {w0 w1 w2 w3 w4 r0 r1 r2 r3 r4 r5 t0 t1 t2 : BitVec 64} {s0 s : State}
    (hcs_le : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat)
    (hcs_lt : trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = errTailPC_placed)
    (hmeta : tryDecryptWPInv s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx26 : s.readReg64 .x26 = tag) :
    let sp := s0.sp - 1504#64
    let cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
    SepWP ((blkPC_131).rebase (blkPl_131).base H) retEpiloguePC_placed s
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
       ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
       ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
            ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
       (if trG.pq.cap = 0#64 then emp
        else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
       A.pool lim ast s ∗ stackAt sp dropChainStack)
      (fun sf P =>
        P = (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
             ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
             ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
             ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt sp dropChainStack) ∧
        tryDecryptWPInv s0 sf) := by
  dsimp only; let sp := s0.sp - 1504#64; set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hcopy := errTail_copy_spe_wp_placed (A := A) (lim := lim) (ast := ast) (H := H)
    (chainsPtr := trG.ratchet.chainsPtr) (chainsLen := BitVec.ofNat 64 cs.length)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2) hpc hmeta hx19 hx20 hx26
  refine SepWP.bind_framed_lscl
    (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
               ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
          stackAt sp dropChainStack) hcl hcopy ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s1 P1 ⟨hP1, hmeta1, hx20_1, hx21_1⟩ hpc1 hcl1; subst hP1
  have hcs_lt' : cs.length * 104 < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 104 hcs_le) hcs_lt
  have hdrop_cs := errTail_drop_chains_wp_placed (A := A) (lim := lim) (ast := ast) (H := H)
    hdealloc hcs_lt' hpc1 hmeta1 hcl1 hx20_1 hx21_1
  refine SepWP.bind_framed
    (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
               ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))
    hdrop_cs ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s2 P2 ⟨hP2, hmeta2, hx20_2⟩ hpc2; subst hP2
  refine SepWP.mono_pre
    (errTail_chains_re_entails (A := A.repAlloc)
      (P_pool := ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) s2)
      (stackAt_dropChainStack_sub sp) hcs_le hcs_lt) ?_
  have hdealloc_cs := errTail_dealloc_chains_freeOnly_wp_placed (A := A) (lim := lim) (ast := ast) (H := H)
    hdealloc hcs_lt hpc2 hmeta2 hx20_2
  refine SepWP.bind_framed
    (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.pq.cap = 0#64 then emp
           else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))
    hdealloc_cs ?_ ?_
  · dsimp only [sp]
  intro s3 P3 ⟨hP3, hmeta3⟩ hpc3; subst hP3
  have hdealloc_pq := errTail_dealloc_pq_freeOnly_wp_placed (A := A) (lim := lim) (ast := ast) (H := H)
    (pqCap := trG.pq.cap) (pqPtr := trG.pq.ptr) hdealloc hpc3 hmeta3
  refine SepWP.bind_framed
    (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
          words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4) hdealloc_pq ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro sf Pf ⟨hPf, hmeta_f⟩ hpcf; subst hPf
  refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
  rw [stackAt_dropChainStack_sub sp]; dsimp only [sp]; sep_ac_rfl

theorem errTail_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : TryDecryptGhost) (st_init st : M.σ)
    (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State)
    (he : e ≠ .panic)
    (hmod1 : (x.model C S uuidTryParse).1 = .error e)
    (hmod2 : (x.model C S uuidTryParse).2 = st1)
    (hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st FreeOnlyEvs)
    (herr : ErrTailState_placed A lim st ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv) (x, st_init) R s0 s := by
  rcases herr with ⟨hpc, hmeta, hx19, hx20, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta_placed.to_wpInv hmeta
  have hcl : LibsignalCodeLoaded lsmpl s.mem := hmeta.2.2.2.2.2.2.1
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  let A0 : RustAlloc := A.atState lim st s
  have hmem_tr :
      s.mem ⊨ trAt A0 (sp + 0x38#64) trG tr ∗
        (sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ speBodyAt A0 (utf8 "decrypt") (sp + 0x168#64) e ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp, A0]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ speBodyAt A.repAlloc (utf8 "decrypt") (sp + 0x168#64) e ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp, A0] at hmem1 ⊢
    rw [chainAt_atState_fn, live_atState, sessionStateAt_atState] at hmem1
    have hspe_eq : speBodyAt (A.atState lim st s) (utf8 "decrypt") (sp + 0x168#64) e =
        speBodyAt A.repAlloc (utf8 "decrypt") (sp + 0x168#64) e := by
      cases e <;> simp only [speBodyAt, invalidMessageStrAt_atState, vecU8_atState]
    rw [hspe_eq] at hmem1
    convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_speBodyAt he hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 = memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide, memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗ (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    rw [h140_split] at hmem3; dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp := errTail_all_steps_wp_placed (A := A) (lim := lim) (ast := st) (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2)
    hdealloc hcs_le hcs_lt hpc hmeta_wp hcl hx19 hx20 hx26
  unfold tryDecryptCommonHeap at hmem4
  dsimp only [A0] at hmem4
  rw [protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hpool_eq : (A.atState lim st s).pool = A.pool lim st s := rfl
  rw [hpool_eq] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool lim st s ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptDummyImg ∗ tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  apply reaches_epilogue_to_outcome_seam_placed x st_init st x.G.afterTrFrom R s0 s hnpan hG' hsb
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta_placed hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩; subst hPf
  have hm_ex :
      sf.mem ⊨
        (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
         ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ speTag e) ∗
         words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ stackAt sp dropChainStack ∗
         memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptDummyImg ∗ tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨evs_exit, hm_ex⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_ex
  rcases hm_ex with ⟨hevs_exit, hm_ex⟩
  refine ⟨evs_exit, hevs_exit, hmeta_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [sessionStateAt_atState, vecResultAt_atState,
      protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hpool_f : (A.atState lim (M.stepEvents evs_exit st) sf).pool =
      A.pool lim (M.stepEvents evs_exit st) sf := rfl
  rw [hpool_f]
  have hdec_ent :
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      vecResultAt A.repAlloc x.ret (x.model C S uuidTryParse).1 := by
    rw [hmod1]; exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptDummyImg ∗
          (stackAt sp dropChainStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗ A.pool lim (M.stepEvents evs_exit st) sf) ∗ R := by
    dsimp only [sp] at hm_ex ⊢; convert hm_ex using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono hdec_ent (sepConj_mono_left
      (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4)))) hmem_f_re

theorem errTail_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : TryDecryptGhost) (st_init st : M.σ)
    (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State)
    (he : e ≠ .panic)
    (hmod1 : (x.modelFn C decFn S uuidTryParse).1 = .error e)
    (hmod2 : (x.modelFn C decFn S uuidTryParse).2 = st1)
    (hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st FreeOnlyEvs)
    (herr : ErrTailStateX_placed A lim st ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptFnSpecPlaced C decFn A lim ctl uuidTryParse S tdEnv) (x, st_init) R s0 s := by
  rcases herr with ⟨hpc, hmeta, hx19, hx20, b, hb, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta_placed.to_wpInv hmeta
  have hcl : LibsignalCodeLoaded lsmpl s.mem := hmeta.2.2.2.2.2.2.1
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  set tag := if b then speTag e else speWord 20
  let A0 : RustAlloc := A.atState lim st s
  have hmem_tr :
      s.mem ⊨ trAt A0 (sp + 0x38#64) trG tr ∗
        (sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         (if b then speBodyAt A0 (utf8 "decrypt") (sp + 0x168#64) e else memRegion (sp + 0x168#64) 40) ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp, A0]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ (if b then speBodyAt A.repAlloc (utf8 "decrypt") (sp + 0x168#64) e else memRegion (sp + 0x168#64) 40) ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp, A0] at hmem1 ⊢
    rw [chainAt_atState_fn, live_atState, sessionStateAt_atState] at hmem1
    have hspe_eq : speBodyAt (A.atState lim st s) (utf8 "decrypt") (sp + 0x168#64) e =
        speBodyAt A.repAlloc (utf8 "decrypt") (sp + 0x168#64) e := by
      cases e <;> simp only [speBodyAt, invalidMessageStrAt_atState, vecU8_atState]
    rw [hspe_eq] at hmem1
    convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_errTailBody he hb hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 = memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide, memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗ (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    rw [h140_split] at hmem3; dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp := errTail_all_steps_wp_placed (A := A) (lim := lim) (ast := st) (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2)
    hdealloc hcs_le hcs_lt hpc hmeta_wp hcl hx19 hx20 hx26
  unfold tryDecryptCommonHeap at hmem4
  dsimp only [A0] at hmem4
  rw [protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hpool_eq : (A.atState lim st s).pool = A.pool lim st s := rfl
  rw [hpool_eq] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool lim st s ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptDummyImg ∗ tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.modelFn C decFn S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.modelFn C decFn S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  apply reaches_epilogue_to_outcome_seam_fn_placed x st_init st x.G.afterTrFrom R s0 s hnpan hG' hsb
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta_placed hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩; subst hPf
  have hm_ex :
      sf.mem ⊨
        (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
         ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ tag) ∗
         words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ stackAt sp dropChainStack ∗
         memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptDummyImg ∗ tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨evs_exit, hm_ex⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_ex
  rcases hm_ex with ⟨hevs_exit, hm_ex⟩
  refine ⟨evs_exit, hevs_exit, hmeta_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [sessionStateAt_atState, decResultFnAt_atState,
      protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hpool_f : (A.atState lim (M.stepEvents evs_exit st) sf).pool =
      A.pool lim (M.stepEvents evs_exit st) sf := rfl
  rw [hpool_f]
  have hdec_ent :
      ((x.ret ↦₆₄ tag) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      decResultFnAt A.repAlloc x.ret (x.modelFn C decFn S uuidTryParse).1 := by
    rw [hmod1]; exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ tag) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptDummyImg ∗
          (stackAt sp dropChainStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗ A.pool lim (M.stepEvents evs_exit st) sf) ∗ R := by
    dsimp only [sp] at hm_ex ⊢; convert hm_ex using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono hdec_ent (sepConj_mono_left
      (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4)))) hmem_f_re

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProofBudget
