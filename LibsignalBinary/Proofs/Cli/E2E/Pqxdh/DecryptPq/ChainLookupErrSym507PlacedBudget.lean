/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupErrSym507Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2PlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSym
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable `ErrTail` Symbolic Execution on Block `507`

Budget-threaded (`RustCliAllocBudget M`) symbolic execution and `VmPreserved` epilogue lemmas for
the `ErrTail` cleanup block of `try_decrypt_with_state::<signal_session_handshake::Coins>`
(Block `507`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupErrSym507PlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (Crypto ReceiverChain TripleRatchet)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement lsRustDeallocSym lsmpl
  ls_subroutine_ok_of_block sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.CliHandshake.Placed (blkPl_513)
open CryptoVerification.CliHandshake.TryDecPlaced (blkLib_eq_508 blkPC_508 blkPl_508)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost UuidParser decryptDraws protocolAddressAt sessionStateAt signalMessageAt vecResultAt
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TrGhost TryDecryptGhost rootStack withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack ls_hook_ok_rustDealloc)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  errDropChainLoopPC_at errTailPC_at retEpiloguePC_at tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (
  SepWP.bind_framed SepWP.bind_framed_lscl SepWP.mono_pre SepWP.rw_pre
  arrayAt_cons arrayAt_nil
  bv_ofNat_succ_beq_zero bv_ofNat_succ_sub_one bv_ofNat_succ_succ_bne_one
  chains_recombine_entails sepWP_to_reaches_pc
  sp_sub_1504_add_0x38 sp_sub_1504_add_0xe8 sp_sub_1504_add_0xf0
  stackAt_dropChainStack_sub tryDecryptMidMeta_placed tryDecryptStack_recombine
  tryDecryptWPInv words5At
)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs PoolPreserved
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2PlacedBudget (drop_chain_placed_ok)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  cliTryDecryptCommonHeapPlaced cliTryDecryptTightSpecPlaced
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Budget Pool Helpers and Pure Segment Lift -/

private theorem sepWP_blk507_vm [LibsignalPlacement] {H : String → Option (State → State)}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_508).rebase (blkPl_508).base (hooksException H))
        mid (s.setMem m_strip) Pre (fun sm' Pm =>
          ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            SepWP ((blkPC_508).rebase (blkPl_508).base H) target (sm'.setMem m_real) Pm post)) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) target s Pre post :=
  sepWP_seg_ls_vm
    (Q := (blkPC_508).rebase (blkPl_508).base (hooksException H))
    blkLib_eq_508 (mid := mid) (hseg := hseg)

private abbrev freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

private theorem freeOnlyPool_intro {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ freeOnlyPool A lim st s :=
  Entails.sepExists_right [] (Entails.pure_right FreeOnlyEvs.nil (Entails.refl _))

private theorem freeOnlyPool_keep {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents evs st) s ⊢ freeOnlyPool A lim st sm := by
  rw [← A.pool_of_vmPreserved hvm]
  exact Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))

private theorem freeOnlyPool_append {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs1 evs2 : List AllocEvent}
    (hevs1 : FreeOnlyEvs evs1) (hevs2 : FreeOnlyEvs evs2) {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s ⊢
      freeOnlyPool A lim st sm := by
  rw [← A.pool_of_vmPreserved hvm, ← M.stepEvents_append evs1 evs2 st]
  exact Entails.sepExists_right (evs1 ++ evs2)
    (Entails.pure_right (FreeOnlyEvs.append hevs1 hevs2) (Entails.refl _))

private theorem freeOnlyPool_congr_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s sm : State} (hvm : VmPreserved s sm) :
    freeOnlyPool A lim st s = freeOnlyPool A lim st sm := by
  unfold freeOnlyPool
  simp only [A.pool_of_vmPreserved hvm]

private theorem SepWP.unpack_freeOnlyPool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {target : BitVec 64} {s : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s) ∗ Frame := by
      try dsimp only [freeOnlyPool]
      sep_focus)
    (hk : ∀ evs : List AllocEvent, FreeOnlyEvs evs →
      SepWP prog target s (A.pool lim (M.stepEvents evs st) s ∗ Frame) post) :
    SepWP prog target s P post := by
  rw [hf]
  wp_pull_exists
  rename_i evs
  exact SepWP.pure_elim (hk evs)

private theorem SepWP.sync_pool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim st s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (A.pool lim st sm ∗ Frame) post) :
    SepWP prog target sm P post := by
  rw [hf, ← A.pool_of_vmPreserved hvm]
  exact hk

private theorem errTail_chains_re_entails {A : RustAlloc} {P_pool : SepProp}
    {sp : BitVec 64} {S_in S_out : Nat} {R_rem : SepProp}
    (hstack : stackAt sp S_in = stackAt sp S_out ∗ R_rem)
    {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {w0 w1 w2 w3 w4 ret tag : BitVec 64}
    (hcs_le : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat)
    (hcs_lt : trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63) :
    let cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
    (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ P_pool ∗ stackAt sp S_in) ∗
      (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
       ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
       ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
       words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
            ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
       (if trG.pq.cap = 0#64 then emp
        else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)))) ⊢
    ((((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
      (if trG.ratchet.chainsCap = 0#64 then emp
       else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
         memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
      P_pool ∗ stackAt sp S_out) ∗
     (R_rem ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
      ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
      ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
      ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
      words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
      (if trG.pq.cap = 0#64 then emp
       else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by
  dsimp only; set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  rw [hstack]
  have hcomm1 :
      (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ P_pool ∗ (stackAt sp S_out ∗ R_rem)) ∗
        (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
         ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
         words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)))) =
      (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       (memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗
        (if trG.ratchet.chainsCap = 0#64 then emp
         else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
           memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
             ((trG.ratchet.chainsCap.toNat - cs.length) * 104))) ∗
       (P_pool ∗ stackAt sp S_out ∗ R_rem ∗
        ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗
        ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗ ((sp + 336#64) ↦₆₄ w2) ∗
        words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by sep_ac_rfl
  have hcomm2 :
      ((((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
        (if trG.ratchet.chainsCap = 0#64 then emp
         else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
           memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
        P_pool ∗ stackAt sp S_out) ∗
       (R_rem ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
        ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
        ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
        ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) =
      (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
       (P_pool ∗ stackAt sp S_out ∗ R_rem ∗
        ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗
        ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗ ((sp + 336#64) ↦₆₄ w2) ∗
        words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by sep_ac_rfl
  rw [hcomm1, hcomm2]
  exact sepConj_mono_right (sepConj_mono_left (chains_recombine_entails hcs_le hcs_lt))

/-! ## `VmPreserved` Epilogue and Budget-Threaded `ErrTail` Steps -/

theorem tryDecrypt_epilogue_394_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (s0 s : State) (hpc : s.pc = retEpiloguePC_at (blkPl_508).base) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1504#64) (hs0_align : s0.spAligned = true)
    (_hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
        memRegion (s0.sp - 1504#64) 1408 ∗ tryDecryptSavedRegs s0.sp s0)
      (fun sf P_f => sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ VmPreserved s sf ∧
        CalleeSavedPreserved s0 sf ∧ (P_f ⊢ stackAt s0.sp rootStack)) := by
  simp only [State.spAligned] at hs0_align
  generalize s0.sp = sp0 at hsp hs0_align ⊢
  unfold tryDecryptSavedRegs
  dsimp only [retEpiloguePC_at] at hpc
  apply sepWP_blk507_vm (mid := s0.readReg64 .x30)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], hvm, ?_, ?_⟩
  · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, *]
  · exact tryDecryptStack_recombine sp0 s0

theorem errTail_copy_spe_507_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {ret tag chainsPtr chainsLen : BitVec 64}
    {w0 w1 w2 w3 w4 r0 r1 r2 r3 r4 r5 t0 t1 t2 : BitVec 64}
    {s0 s : State}
    (hpc : s.pc = errTailPC_at (blkPl_508).base)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx26 : s.readReg64 .x26 = tag) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_508).base + 820#64) s
      (((sp + 64#64) ↦₆₄ chainsPtr) ∗ ((sp + 72#64) ↦₆₄ chainsLen) ∗
       ((sp + 320#64) ↦₆₄ t0) ∗ ((sp + 328#64) ↦₆₄ t1) ∗ ((sp + 336#64) ↦₆₄ t2) ∗
       words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5 ∗ A.pool lim ast s)
      (fun sf P =>
        P = (((sp + 64#64) ↦₆₄ chainsPtr) ∗ ((sp + 72#64) ↦₆₄ chainsLen) ∗
             ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗ ((sp + 336#64) ↦₆₄ w2) ∗
             words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗ A.pool lim ast sf) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x20 = chainsPtr ∧ sf.readReg64 .x21 = chainsLen) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [errTailPC_at] at hpc
  unfold words5At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps_sync_pool ((blkPl_508).base + 820#64)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem errTail_drop_one_507_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {p chainsPtr rem : BitVec 64} (gc : ChainGhost × ReceiverChain) {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = errDropChainLoopPC_at (blkPl_508).base)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_508).base + 836#64) s
      (chainAt A.repAlloc gc p ∗ A.pool lim ast s ∗ stackAt sp dropChainStack)
      (fun sf P =>
        P = (memRegion p 104 ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt sp dropChainStack) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = p ∧ sf.readReg64 .x20 = chainsPtr ∧ sf.readReg64 .x21 = rem) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hdrop := ls_subroutine_ok_of_block (callerProg := (blkPC_508).rebase (blkPl_508).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (drop_chain_placed_ok hdealloc))
  rw [show blkPl_513.base = lsmpl.base 513 from rfl] at hdrop
  simp only [withLsCodeLoaded, dropChainSpec] at hdrop
  dsimp only [errDropChainLoopPC_at] at hpc
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 513)
  wp_steps
  refine SepWP.sync_pool (hk := ?_)
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_call
  rw [← hsp]
  wp_call hdrop (⟨p, gc⟩, ast)
  refine SepWP.focus_weaken (freeOnlyPool_keep A lim ast ‹FreeOnlyEvs _› (VmPreserved.refl sf))
    (by sep_focus) ?_
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  rw [hsp]; unfold freeOnlyPool; sep_ac_rfl

theorem errTail_drop_exit_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {chainsPtr : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_508).base + 836#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = 1#64) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 848#64) s emp
      (fun sf P => P = emp ∧ tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr ∧
        VmPreserved s sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]⟩

theorem errTail_drop_cont_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {p chainsPtr rem : BitVec 64} {s0 s : State}
    (hne : (rem != 1#64) = true)
    (hpc : s.pc = (blkPl_508).base + 836#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) (errDropChainLoopPC_at (blkPl_508).base) s emp
      (fun sf P =>
        P = emp ∧ tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = p + 104#64 ∧ sf.readReg64 .x20 = chainsPtr ∧
        sf.readReg64 .x21 = rem - 1#64 ∧ VmPreserved s sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [errDropChainLoopPC_at]
  wp_steps
  try rw [hne, if_pos rfl]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]⟩

theorem errTail_drop_loop_507_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    {chainsPtr : BitVec 64} {s0 : State}
    (rest : List (ChainGhost × ReceiverChain)) :
    ∀ {ast : M.σ} (gc : ChainGhost × ReceiverChain) (p : BitVec 64) (s : State),
      (rest.length + 1) * 104 < 2 ^ 63 →
      s.pc = errDropChainLoopPC_at (blkPl_508).base →
      tryDecryptWPInv s0 s →
      LibsignalCodeLoaded lsmpl s.mem →
      s.readReg64 .x19 = p →
      s.readReg64 .x20 = chainsPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 (rest.length + 1) →
      SepWP ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 848#64) s
        (arrayAt (chainAt A.repAlloc) 104 p (gc :: rest) ∗ A.pool lim ast s ∗
         stackAt (s0.sp - 1504#64) dropChainStack)
        (fun sf P =>
          P = (memRegion p ((rest.length + 1) * 104) ∗
               (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
               stackAt (s0.sp - 1504#64) dropChainStack) ∧
          tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr) := by
  induction rest with
  | nil =>
    intro ast gc p s hlt hpc hmeta hcl hx19 hx20 hx21
    rw [List.length_nil, Nat.zero_add] at hx21
    have hone := errTail_drop_one_507_wp_placed (ast := ast) (H := H) gc hdealloc hcl hpc hmeta hx19 hx20 hx21
    refine SepWP.bind_framed (F := emp) hone ?_ ?_
    · rw [arrayAt_cons, arrayAt_nil, sepConj_emp, sepConj_emp]
    intro s1 P1 ⟨hP1, hmeta1, _, hx20_1, hx21_1⟩ hpc1
    subst hP1
    have hexit := errTail_drop_exit_507_wp_placed (H := H) hpc1 hmeta1 hx20_1 hx21_1
    refine SepWP.bind_framed
      (F := memRegion p 104 ∗ freeOnlyPool A lim ast s1 ∗ stackAt (s0.sp - 1504#64) dropChainStack)
      hexit ?_ ?_
    · rw [emp_sepConj, sepConj_emp]
    intro sf Pf ⟨hPf, hmeta_f, hx20_f, hvm_f⟩ hpcf
    subst hPf
    rw [freeOnlyPool_congr_vm A lim ast hvm_f]
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    rw [emp_sepConj, List.length_nil, Nat.zero_add, Nat.one_mul]
  | cons gc' rest' ih =>
    intro ast gc p s hlt hpc hmeta hcl hx19 hx20 hx21
    rw [List.length_cons] at hlt hx21
    have hone := errTail_drop_one_507_wp_placed (ast := ast) (H := H) gc hdealloc hcl hpc hmeta hx19 hx20 hx21
    refine SepWP.bind_framed_lscl
      (F := arrayAt (chainAt A.repAlloc) 104 (p + 104#64) (gc' :: rest')) hcl hone ?_ ?_
    · rw [arrayAt_cons]; sep_ac_rfl
    intro s1 P1 ⟨hP1, hmeta1, hx19_1, hx20_1, hx21_1⟩ hpc1 hcl1
    subst hP1
    have hstep := errTail_drop_cont_507_wp_placed (H := H)
      (bv_ofNat_succ_succ_bne_one hlt) hpc1 hmeta1 hx19_1 hx20_1 hx21_1
    refine SepWP.bind_framed_lscl
      (F := (memRegion p 104 ∗ freeOnlyPool A lim ast s1 ∗ stackAt (s0.sp - 1504#64) dropChainStack) ∗
            arrayAt (chainAt A.repAlloc) 104 (p + 104#64) (gc' :: rest')) hcl1 hstep ?_ ?_
    · rw [emp_sepConj]
    intro s2 P2 ⟨hP2, hmeta2, hx19_2, hx20_2, hx21_2, hvm2⟩ hpc2 hcl2
    subst hP2
    rw [freeOnlyPool_congr_vm A lim ast hvm2]
    refine SepWP.unpack_freeOnlyPool (hk := fun evs1 hevs1 => ?_)
    have hx21_2' : s2.readReg64 .x21 = BitVec.ofNat 64 (rest'.length + 1) := by
      rw [hx21_2, bv_ofNat_succ_sub_one (rest'.length + 1)]
    have hlt' : (rest'.length + 1) * 104 < 2 ^ 63 :=
      Nat.lt_trans (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (by decide)) hlt
    have hih := ih (ast := M.stepEvents evs1 ast) gc' (p + 104#64) s2
      hlt' hpc2 hmeta2 hcl2 hx19_2 hx20_2 hx21_2'
    refine SepWP.bind_framed (F := memRegion p 104) hih ?_ ?_
    · sep_ac_rfl
    intro sf Pf ⟨hPf, hmeta_f, hx20_f⟩ hpcf
    subst hPf
    refine SepWP.unpack_freeOnlyPool (hk := fun evs2 hevs2 => ?_)
    refine SepWP.focus_weaken (freeOnlyPool_append A lim ast hevs1 hevs2 (VmPreserved.refl sf))
      (by sep_focus) ?_
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    have hcomb : memRegion p ((rest'.length + 1 + 1) * 104) =
        memRegion p 104 ∗ memRegion (p + 104#64) ((rest'.length + 1) * 104) := by
      rw [show (rest'.length + 1 + 1) * 104 = 104 + (rest'.length + 1) * 104 by omega]
      exact ProofLib.memRegion_split p 104 ((rest'.length + 1) * 104) (by omega)
    rw [List.length_cons, hcomb]; unfold freeOnlyPool; sep_ac_rfl

theorem errTail_drop_nil_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {chainsPtr : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_508).base + 820#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = 0#64) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 848#64) s emp
      (fun sf P => P = emp ∧ tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr ∧
        VmPreserved s sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]⟩

theorem errTail_drop_init_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {chainsPtr rem : BitVec 64} {s0 s : State}
    (hne : (rem == 0#64) = false)
    (hpc : s.pc = (blkPl_508).base + 820#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) (errDropChainLoopPC_at (blkPl_508).base) s emp
      (fun s1 P1 =>
        P1 = emp ∧ tryDecryptWPInv s0 s1 ∧
        s1.readReg64 .x19 = chainsPtr ∧ s1.readReg64 .x20 = chainsPtr ∧ s1.readReg64 .x21 = rem ∧
        VmPreserved s s1) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [errDropChainLoopPC_at]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]⟩

theorem errTail_drop_chains_507_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {chainsPtr : BitVec 64} {cs : List (ChainGhost × ReceiverChain)} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hlt : cs.length * 104 < 2 ^ 63)
    (hpc : s.pc = (blkPl_508).base + 820#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 cs.length) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 848#64) s
      (arrayAt (chainAt A.repAlloc) 104 chainsPtr cs ∗ A.pool lim ast s ∗
       stackAt (s0.sp - 1504#64) dropChainStack)
      (fun sf P =>
        P = (memRegion chainsPtr (cs.length * 104) ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt (s0.sp - 1504#64) dropChainStack) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr) := by
  cases cs with
  | nil =>
    rw [List.length_nil] at hx21
    have hstep := errTail_drop_nil_507_wp_placed (H := H) hpc hmeta hx20 hx21
    refine SepWP.bind_framed
      (F := A.pool lim ast s ∗ stackAt (s0.sp - 1504#64) dropChainStack) hstep ?_ ?_
    · rw [arrayAt_nil]
    intro sf Pf ⟨hPf, hmeta_f, hx20_f, hvm_f⟩ hpcf
    subst hPf
    rw [← A.pool_of_vmPreserved hvm_f]
    refine SepWP.focus_weaken (freeOnlyPool_intro A lim ast sf) (by sep_focus) ?_
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    rw [List.length_nil, Nat.zero_mul, memRegion_zero]; unfold freeOnlyPool; sep_ac_rfl
  | cons gc rest =>
    rw [List.length_cons] at hlt hx21 ⊢
    have hstep := errTail_drop_init_507_wp_placed (H := H)
      (bv_ofNat_succ_beq_zero hlt) hpc hmeta hx20 hx21
    refine SepWP.bind_framed_lscl
      (F := arrayAt (chainAt A.repAlloc) 104 chainsPtr (gc :: rest) ∗ A.pool lim ast s ∗
            stackAt (s0.sp - 1504#64) dropChainStack) hcl hstep ?_ ?_
    · rw [emp_sepConj]
    intro s1 P1 ⟨hP1, hmeta1, hx19_1, hx20_1, hx21_1, hvm1⟩ hpc1 hcl1
    subst hP1
    rw [emp_sepConj, ← A.pool_of_vmPreserved hvm1]
    exact errTail_drop_loop_507_wp_placed (A := A) (lim := lim) (H := H)
      (chainsPtr := chainsPtr) (s0 := s0)
      hdealloc rest (ast := ast) gc chainsPtr s1 hlt hpc1 hmeta1 hcl1 hx19_1 hx20_1 hx21_1

theorem errTail_dealloc_chains_507_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {chainsCap chainsPtr : BitVec 64} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hlt : chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = (blkPl_508).base + 848#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 876#64) s
      (((s0.sp - 1504#64 + 56#64) ↦₆₄ chainsCap) ∗
       (if chainsCap = 0#64 then emp
        else A.repAlloc.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          memRegion chainsPtr (chainsCap.toNat * 104)) ∗
       A.pool lim ast s ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 56#64) ↦₆₄ chainsCap) ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hdealloc_ok := ls_hook_ok_rustDealloc (prog := (blkPC_508).rebase (blkPl_508).base H) hdealloc
  simp only [rustCliDeallocBudgetSpec] at hdealloc_ok
  by_cases hcap : chainsCap = 0#64
  · subst hcap
    refine SepWP.rw_pre (by simp only [ite_true, emp_sepConj, ← hsp]; exact rfl) ?_
    wp_steps
    refine SepWP.sync_pool (hk := ?_)
    refine SepWP.focus_weaken (freeOnlyPool_intro A lim ast _) (by sep_focus) ?_
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp]; unfold freeOnlyPool; sep_ac_rfl
  · refine SepWP.rw_pre
      (by simp only [hcap, ite_false, ← hsp, RustCliAllocBudget.repAlloc_live]; exact rfl) ?_
    have hcap_beq : (chainsCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hmul : (chainsCap * 104#64).toNat = chainsCap.toNat * 104 := by
      rw [BitVec.toNat_mul, show (104#64 : BitVec 64).toNat = 104 from rfl,
          Nat.mod_eq_of_lt (by omega)]
    have hmul_bv : chainsCap * 104#64 = BitVec.ofNat 64 (chainsCap.toNat * 104) := by bv_omega
    wp_steps
    refine SepWP.sync_pool (hk := ?_)
    wp_call hdealloc_ok (chainsPtr, chainsCap.toNat * 104, 8, ast)
    refine SepWP.focus_weaken
      (freeOnlyPool_keep A lim ast (FreeOnlyEvs.singleton 8 (chainsCap.toNat * 104)) (VmPreserved.refl sf))
      (by sep_focus) ?_
    refine SepWP.done (by simp_all [AllocCallPreserved, arm64_norm])
      (by simp_all [AllocCallPreserved, arm64_norm]) ?_
    refine ⟨?_, ⟨by simp_all [AllocCallPreserved, arm64_norm],
      by simp_all [AllocCallPreserved, arm64_norm], hs0_align,
      by simp_all [AllocCallPreserved, arm64_norm],
      by simp_all [AllocCallPreserved, arm64_norm],
      by simp_all [AllocCallPreserved, arm64_norm]⟩⟩
    rw [hsp, sp_sub_1504_add_0x38]; unfold freeOnlyPool; sep_ac_rfl

theorem errTail_dealloc_chains_freeOnly_507_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {chainsCap chainsPtr : BitVec 64} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hlt : chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = (blkPl_508).base + 848#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 876#64) s
      (((s0.sp - 1504#64 + 56#64) ↦₆₄ chainsCap) ∗
       (if chainsCap = 0#64 then emp
        else A.repAlloc.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          memRegion chainsPtr (chainsCap.toNat * 104)) ∗
       (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) s) ∗
       stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 56#64) ↦₆₄ chainsCap) ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  refine SepWP.unpack_freeOnlyPool (hk := fun evs1 hevs1 => ?_)
  have h1 := errTail_dealloc_chains_507_wp_placed (ast := M.stepEvents evs1 ast) (H := H)
    hdealloc hlt hpc hmeta hx20
  refine SepWP.bind_framed (F := emp) h1 (by sep_ac_rfl) ?_
  intro sf Pf ⟨hPf, hmeta_f⟩ hpcf
  subst hPf
  refine SepWP.unpack_freeOnlyPool (hk := fun evs2 hevs2 => ?_)
  refine SepWP.focus_weaken (freeOnlyPool_append A lim ast hevs1 hevs2 (VmPreserved.refl sf))
    (by sep_focus) ?_
  refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
  unfold freeOnlyPool; sep_ac_rfl

theorem errTail_dealloc_pq_507_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {pqCap pqPtr : BitVec 64} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hpc : s.pc = (blkPl_508).base + 876#64)
    (hmeta : tryDecryptWPInv s0 s) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) (retEpiloguePC_at (blkPl_508).base) s
      (((s0.sp - 1504#64 + 232#64) ↦₆₄ pqCap) ∗
       ((s0.sp - 1504#64 + 240#64) ↦₆₄ pqPtr) ∗
       (if pqCap = 0#64 then emp
        else A.repAlloc.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) ∗
       A.pool lim ast s ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 232#64) ↦₆₄ pqCap) ∗
             ((s0.sp - 1504#64 + 240#64) ↦₆₄ pqPtr) ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hdealloc_ok := ls_hook_ok_rustDealloc (prog := (blkPC_508).rebase (blkPl_508).base H) hdealloc
  simp only [rustCliDeallocBudgetSpec] at hdealloc_ok
  dsimp only [retEpiloguePC_at]
  by_cases hcap : pqCap = 0#64
  · subst hcap
    refine SepWP.rw_pre (by simp only [ite_true, emp_sepConj, ← hsp]; exact rfl) ?_
    wp_steps
    refine SepWP.sync_pool (hk := ?_)
    refine SepWP.focus_weaken (freeOnlyPool_intro A lim ast _) (by sep_focus) ?_
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp]; unfold freeOnlyPool; sep_ac_rfl
  · refine SepWP.rw_pre
      (by simp only [hcap, ite_false, ← hsp, RustCliAllocBudget.repAlloc_live]; exact rfl) ?_
    have hcap_beq : (pqCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    wp_steps
    refine SepWP.sync_pool (hk := ?_)
    wp_call hdealloc_ok (pqPtr, pqCap.toNat, 1, ast)
    wp_steps
    refine SepWP.sync_pool (s := sf) (hk := ?_)
    refine SepWP.focus_weaken
      (freeOnlyPool_keep A lim ast (FreeOnlyEvs.singleton 1 pqCap.toNat) (VmPreserved.refl _))
      (by sep_focus) ?_
    refine SepWP.done (by simp_all [AllocCallPreserved, arm64_norm])
      (by simp_all [AllocCallPreserved, arm64_norm]) ?_
    refine ⟨?_, ⟨by simp_all [AllocCallPreserved, arm64_norm],
      by simp_all [AllocCallPreserved, arm64_norm], hs0_align,
      by simp_all [AllocCallPreserved, arm64_norm],
      by simp_all [AllocCallPreserved, arm64_norm],
      by simp_all [AllocCallPreserved, arm64_norm]⟩⟩
    rw [hsp, sp_sub_1504_add_0xe8, sp_sub_1504_add_0xf0]; unfold freeOnlyPool; sep_ac_rfl

theorem errTail_dealloc_pq_freeOnly_507_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {pqCap pqPtr : BitVec 64} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hpc : s.pc = (blkPl_508).base + 876#64)
    (hmeta : tryDecryptWPInv s0 s) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) (retEpiloguePC_at (blkPl_508).base) s
      (((s0.sp - 1504#64 + 232#64) ↦₆₄ pqCap) ∗
       ((s0.sp - 1504#64 + 240#64) ↦₆₄ pqPtr) ∗
       (if pqCap = 0#64 then emp
        else A.repAlloc.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) ∗
       (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) s) ∗
       stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 232#64) ↦₆₄ pqCap) ∗
             ((s0.sp - 1504#64 + 240#64) ↦₆₄ pqPtr) ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  refine SepWP.unpack_freeOnlyPool (hk := fun evs1 hevs1 => ?_)
  have h1 := errTail_dealloc_pq_507_wp_placed (ast := M.stepEvents evs1 ast) (H := H)
    (pqCap := pqCap) (pqPtr := pqPtr) hdealloc hpc hmeta
  refine SepWP.bind_framed (F := emp) h1 (by sep_ac_rfl) ?_
  intro sf Pf ⟨hPf, hmeta_f⟩ hpcf
  subst hPf
  refine SepWP.unpack_freeOnlyPool (hk := fun evs2 hevs2 => ?_)
  refine SepWP.focus_weaken (freeOnlyPool_append A lim ast hevs1 hevs2 (VmPreserved.refl sf))
    (by sep_focus) ?_
  refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
  unfold freeOnlyPool; sep_ac_rfl

/-! ## Combined `ErrTail` Symbolic Execution and Epilogue -/

theorem errTail_all_steps_507_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    {ret tag : BitVec 64} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {w0 w1 w2 w3 w4 r0 r1 r2 r3 r4 r5 t0 t1 t2 : BitVec 64} {s0 s : State}
    (hcs_le : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat)
    (hcs_lt : trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = errTailPC_at (blkPl_508).base)
    (hmeta : tryDecryptWPInv s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx26 : s.readReg64 .x26 = tag) :
    let sp := s0.sp - 1504#64
    let cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
    SepWP ((blkPC_508).rebase (blkPl_508).base H) (retEpiloguePC_at (blkPl_508).base) s
      (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
       ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ t0) ∗ ((sp + 328#64) ↦₆₄ t1) ∗
       ((sp + 336#64) ↦₆₄ t2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
            ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
       (if trG.pq.cap = 0#64 then emp
        else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
       A.pool lim ast s ∗ stackAt sp dropChainStack)
      (fun sf P =>
        P = (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
             ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
             ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
             ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt sp dropChainStack) ∧
        tryDecryptWPInv s0 sf) := by
  dsimp only; let sp := s0.sp - 1504#64; set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hcopy := errTail_copy_spe_507_wp_placed (A := A) (lim := lim) (ast := ast) (H := H)
    (chainsPtr := trG.ratchet.chainsPtr) (chainsLen := BitVec.ofNat 64 cs.length)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2) hpc hmeta hx19 hx20 hx26
  refine SepWP.bind_framed_lscl
    (F := ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
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
  have hdrop_cs := errTail_drop_chains_507_wp_placed (A := A) (lim := lim) (ast := ast) (H := H)
    hdealloc hcs_lt' hpc1 hmeta1 hcl1 hx20_1 hx21_1
  refine SepWP.bind_framed
    (F := ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
          ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
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
  have hdealloc_cs := errTail_dealloc_chains_freeOnly_507_wp_placed (A := A) (lim := lim) (ast := ast) (H := H)
    hdealloc hcs_lt hpc2 hmeta2 hx20_2
  refine SepWP.bind_framed
    (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
          ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.pq.cap = 0#64 then emp
           else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))
    hdealloc_cs ?_ ?_
  · dsimp only [sp]
  intro s3 P3 ⟨hP3, hmeta3⟩ hpc3; subst hP3
  have hdealloc_pq := errTail_dealloc_pq_freeOnly_507_wp_placed (A := A) (lim := lim) (ast := ast) (H := H)
    (pqCap := trG.pq.cap) (pqPtr := trG.pq.ptr) hdealloc hpc3 hmeta3
  refine SepWP.bind_framed
    (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗ ((sp + 336#64) ↦₆₄ w2) ∗
          words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4) hdealloc_pq ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro sf Pf ⟨hPf, hmeta_f⟩ hpcf; subst hPf
  refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
  rw [stackAt_dropChainStack_sub sp]; dsimp only [sp]; sep_ac_rfl

theorem reaches_epilogue_to_outcome_tight_seam_507_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {remEnv : List AllocEvent → Prop}
    (x : TryDecryptGhost) (st_init st : M.σ) (G' : SessionGhost) (R : SepProp) (s0 s : State)
    (hnpan : (x.model C S parse).1 ≠ .error .panic)
    (hG' : x.G.AfterTryDecrypt (x.model C S parse).1.toBool G')
    (hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st remEnv)
    (hreach : reaches_pc ((blkPC_508).rebase (blkPl_508).base H) (retEpiloguePC_at (blkPl_508).base) s
      (fun s1 => ∃ evs_exit : List AllocEvent, remEnv evs_exit ∧
        tryDecryptMidMeta_placed s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt (A.atState lim (M.stepEvents evs_exit st) s1)
            x.ss G' (x.model C S parse).2 ∗
          vecResultAt (A.atState lim (M.stepEvents evs_exit st) s1)
            x.ret (x.model C S parse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          cliTryDecryptCommonHeapPlaced A lim (M.stepEvents evs_exit st) ctl
            x (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 s1 ∗ R))) :
    reaches_outcome ((blkPC_508).rebase (blkPl_508).base H)
      (cliTryDecryptTightSpecPlaced C A lim ctl parse S tdEnv) (x, st_init) R s0 s := by
  have hcomb : reaches_pc ((blkPC_508).rebase (blkPl_508).base H) (s0.readReg64 .x30) s
      (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.mem ⊨ (cliTryDecryptTightSpecPlaced C A lim ctl parse S tdEnv).post
          (x, st_init) s0 sf ∗ R)) := by
    refine reaches_pc_seq hreach ?_
    rintro s1 hpc1 _ ⟨evs_exit, hexit,
      ⟨hrun1, hsp1, hs0_align, hsp_align1, _, htrace1, _, hvregs1⟩, hm1⟩
    obtain ⟨evs_total, hst_eq, htd_tot⟩ := hsb.finish hexit
    rw [hst_eq] at hm1
    set A1 : RustAlloc := A.atState lim (M.stepEvents evs_total st_init) s1
    unfold cliTryDecryptCommonHeapPlaced
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced at hm1
    have hm1_re : s1.mem ⊨
        (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
          memRegion (s0.sp - 1504#64) 1408 ∗ tryDecryptSavedRegs s0.sp s0) ∗
        (sessionStateAt A1 x.ss G' (x.model C S parse).2 ∗
         vecResultAt A1 x.ret (x.model C S parse).1 ∗
         protocolAddressAt A1 x.rem x.remA ∗ protocolAddressAt A1 x.loc x.locA ∗
         signalMessageAt A1 x.msgG x.msgA x.msg ∗
         cliTapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         lsLogOff ∗ A1.pool ∗ R) := by convert hm1 using 1; sep_ac_rfl
    refine reaches_pc_mono
      (sepWP_to_reaches_pc
        (tryDecrypt_epilogue_394_507_wp_placed s0 s1 hpc1 hrun1 hsp1 hs0_align hsp_align1 htrace1 hvregs1)
        hm1_re) ?_
    intro sf _ _ ⟨P_f, hm_sf, hsp_sf, htrace_sf, hvm_sf, hcc_sf, hP_f⟩
    refine ⟨hsp_sf, hcc_sf, ?_⟩
    have hm2 := Satisfies.mono (sepConj_mono_left hP_f) hm_sf
    have hA_eq : A.atState lim (M.stepEvents evs_total st_init) sf = A1 :=
      RustCliAllocBudget.atState_eq_of_vmPreserved A lim (M.stepEvents evs_total st_init) hvm_sf
    dsimp only [cliTryDecryptTightSpecPlaced, withLsCodeRoLoaded,
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget.tryDecryptPlacedTightSpec,
      LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs_total, ?_⟩
    rw [hA_eq]
    have hm3 : sf.mem ⊨
        sessionStateAt A1 x.ss G' (x.model C S parse).2 ∗
        (vecResultAt A1 x.ret (x.model C S parse).1 ∗
         protocolAddressAt A1 x.rem x.remA ∗ protocolAddressAt A1 x.loc x.locA ∗
         signalMessageAt A1 x.msgG x.msgA x.msg ∗
         cliTapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         lsLogOff ∗ stackAt s0.sp rootStack ∗ A1.pool ∗ R) := by
      convert hm2 using 1; sep_ac_rfl
    have hent :
        sessionStateAt A1 x.ss G' (x.model C S parse).2 ⊢
          ⌜tdEnv (tryDecryptEnvArgs x) evs_total⌝ ∗
          ⌜(x.model C S parse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
          (∃∗ G'' : SessionGhost,
            ⌜x.G.AfterTryDecrypt (x.model C S parse).1.toBool G''⌝ ∗
            sessionStateAt A1 x.ss G'' (x.model C S parse).2) :=
      Entails.pure_right htd_tot
        (Entails.pure_right ⟨hnpan, htrace_sf⟩
          (Entails.trans (Entails.pure_right hG' (Entails.refl _))
            (Entails.sepExists_intro
              (P := fun G'' => ⌜x.G.AfterTryDecrypt (x.model C S parse).1.toBool G''⌝ ∗
                sessionStateAt A1 x.ss G'' (x.model C S parse).2) G')))
    have hm4 := Satisfies.mono (sepConj_mono_left hent) hm3
    convert hm4 using 1; sep_ac_rfl
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, hsp_sf, hcc_sf, hpost_sf⟩ | ⟨_, hfalse⟩⟩ := hcomb hL
  · exact reaches_outcome_steps hsteps
      (reaches_outcome.of_outcome (Or.inl ⟨⟨hpc_sf, hsp_sf, hrun_sf⟩, ⟨hsp_sf, hcc_sf⟩, hpost_sf⟩))
  · exact hfalse.elim

theorem reaches_epilogue_to_outcome_tight_507_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (x : TryDecryptGhost) (st_init : M.σ) (evs_total : List AllocEvent)
    (G' : SessionGhost) (R : SepProp) (s0 s : State)
    (hnpan : (x.model C S parse).1 ≠ .error .panic)
    (hG' : x.G.AfterTryDecrypt (x.model C S parse).1.toBool G')
    (htd : tdEnv (tryDecryptEnvArgs x) evs_total)
    (hreach : reaches_pc ((blkPC_508).rebase (blkPl_508).base H) (retEpiloguePC_at (blkPl_508).base) s
      (fun s1 => tryDecryptMidMeta_placed s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt (A.atState lim (M.stepEvents evs_total st_init) s1)
            x.ss G' (x.model C S parse).2 ∗
          vecResultAt (A.atState lim (M.stepEvents evs_total st_init) s1)
            x.ret (x.model C S parse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          cliTryDecryptCommonHeapPlaced A lim (M.stepEvents evs_total st_init) ctl
            x (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 s1 ∗ R))) :
    reaches_outcome ((blkPC_508).rebase (blkPl_508).base H)
      (cliTryDecryptTightSpecPlaced C A lim ctl parse S tdEnv) (x, st_init) R s0 s := by
  have hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x))
      st_init (M.stepEvents evs_total st_init) (· = []) :=
    ⟨FitsEnv.nil, evs_total, rfl, by rintro _ rfl; simpa using htd⟩
  refine reaches_epilogue_to_outcome_tight_seam_507_placed x st_init
    (M.stepEvents evs_total st_init) G' R s0 s hnpan hG' hsb (reaches_pc_mono hreach ?_)
  intro s1 _ _ ⟨hmeta, hm1⟩
  exact ⟨[], rfl, hmeta, hm1⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupErrSym507PlacedBudget
