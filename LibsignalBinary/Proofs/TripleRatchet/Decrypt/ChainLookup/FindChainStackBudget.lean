/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.FindReceiverChainKeyBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainStack
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainSym
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
import ProofLib.RegChain

/-!
# Budget-Threaded `find_receiver_chain_key` Call Reachability (Block `130`)

Proves `findChain_bl_vm_wp_placed` and `findChain_call_findReceiverChainKey_reaches_placed`,
threading `A.atState lim st` and `VmPreserved` across the zero-allocation call to
`findReceiverChainKeyPlacedSpec A` at `+0x2a4`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainStackBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (RatchetState SessionState SignalMessage TripleRatchet)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded blkPC_25 blkPl_25
   ls_subroutine_ok_of_block lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSessionRepr (RatchetGhost msgTypeByte ratchetAt)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SignalMessageGhost protocolAddressAt sessionStateAt tapeAfter)
open CryptoVerification.LibsignalTripleRatchet
  (FindReceiverChainKeyGhost TrGhost TryDecryptGhost findReceiverChainKeyResultAt
   findReceiverChainKeyStack trAt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (tryDecryptCommonHeap tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
  (blkPC_131 blkPl_131 logOff_tryDecryptDummyImg memRegion_0x140_split_findReceiverChainKey
   reaches_pc_call_lscl reaches_pc_lsro_preserve reaches_pc_seq_lscl segFindChainPC_placed
   sepWP_to_reaches_pc signalMessageAt_eq_srk_rest signalMessageRestAt
   stackAt_tryDecryptSubStack_sub trAt_eq_ratchetAt_trRestAt trRestAt tryDecryptDummyImg
   tryDecryptMidMeta_placed tryDecryptWPInv)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.ChainKey.FindReceiverChainKeyBudget
  (findReceiverChainKeyPlacedAllocSpec findReceiverChainKeyPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
  (FindChainState_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget
  (sepWP_blk130_vm)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
  (chainAt_atState_fn optBoxU8At_atState protocolAddressAt_atState sessionStateAt_atState
   signalMessageAt_atState)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem ratchetAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (self : BitVec 64) (G : RatchetGhost) (rst : RatchetState) :
    ratchetAt (A.atState lim st s) self G rst = ratchetAt A.repAlloc self G rst := by
  unfold ratchetAt
  rw [chainAt_atState_fn]
  rfl

private theorem trAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (t : BitVec 64) (G : TrGhost) (tr : TripleRatchet (List (BitVec 8))) :
    trAt (A.atState lim st s) t G tr = trAt A.repAlloc t G tr := by
  unfold trAt
  rw [ratchetAt_atState]
  rfl

private theorem trRestAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (t : BitVec 64) (G : TrGhost) (tr : TripleRatchet (List (BitVec 8))) :
    trRestAt (A.atState lim st s) t G tr = trRestAt A.repAlloc t G tr :=
  rfl

private theorem signalMessageRestAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : SignalMessageGhost) (a : BitVec 64) (m : SignalMessage) :
    signalMessageRestAt (A.atState lim st s) g a m = signalMessageRestAt A.repAlloc g a m := by
  unfold signalMessageRestAt
  rw [optBoxU8At_atState]
  rfl

/-- `VmPreserved`-preserving counterpart of `findChain_bl_wp_placed` on Block `130` (`+676 -> lsmpl.base 25`). -/
theorem findChain_bl_vm_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 676#64) (hmeta : tryDecryptWPInv s0 s) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.base 25) s emp
      (fun s1 P1 =>
        P1 = emp ∧
        VmPreserved s s1 ∧
        tryDecryptWPInv s0 s1 ∧
        s1.readReg64 Reg.lr = (blkPl_131).base + 680#64 ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧
        s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x8 = s.readReg64 .x8 ∧
        CalleeSavedPreserved s s1) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  apply sepWP_blk130_vm (mid := lsmpl.base 25)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun _m_real _hnsp => ?_
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨rfl, _hnsp.toVmPreserved rfl,
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

/-- Budget-threaded relocatable `FindChainState_placed` -> `+680` reachability across the
`bl find_receiver_chain_key` call on Block `130` (zero allocator events; `st` unchanged). -/
theorem findChain_call_findReceiverChainKey_reaches_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ctl : BitVec 64} {H : String → Option (State → State)}
    (hfrck : subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedSpec A)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hS2 : FindChainState_placed A lim st ctl x trG tr st1 R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    reaches_pc prog ((blkPl_131).base + 680#64) s
      (fun s_ret =>
        tryDecryptMidMeta_placed s0 s_ret ∧
        s_ret.readReg64 .x19 = x.ret ∧
        s_ret.readReg64 .x20 = sp + 0x140#64 ∧
        s_ret.readReg64 .x21 = x.ss ∧
        s_ret.readReg64 .x22 = x.msgA ∧
        s_ret.readReg64 .x23 = sp + 0x500#64 ∧
        (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s_ret.readReg64 .x25 = sp + 0x190#64 ∧
        s_ret.readReg64 .x27 = sp + 0x38#64 ∧
        s_ret.readReg64 .x28 = sp + 0x2c0#64 ∧
        (s_ret.mem ⊨
          sessionStateAt (A.atState lim st s_ret) x.ss x.G.afterTrFrom st1 ∗
          trAt (A.atState lim st s_ret) (sp + 0x38#64) trG tr ∗
          memRegion x.ret 48 ∗ memRegion sp 0x20 ∗
          ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 0x140#64) 0x50 ∗
          findReceiverChainKeyResultAt (sp + 0x190#64)
            (tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey) ∗
          memRegion (sp + 0x1b8#64) 0x3c8 ∗
          tryDecryptCommonHeap (A.atState lim st s_ret) ctl tryDecryptDummyImg x 0 s0 ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  dsimp only [FindChainState_placed,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.FindChainState_placed] at hS2
  rcases hS2 with ⟨hpc, hmeta, hx0, hx1, hx8, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hmem⟩
  dsimp only [segFindChainPC_placed] at hpc
  have hwp_bl := findChain_bl_vm_wp_placed (H := H) hpc (tryDecryptMidMeta_placed.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt (A.atState lim st s) x.ss x.G.afterTrFrom st1 ∗
       trAt (A.atState lim st s) (sp + 0x38#64) trG tr ∗ memRegion x.ret 48 ∗ memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x440 ∗
       tryDecryptCommonHeap (A.atState lim st s) ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    rw [emp_sepConj]; exact hmem
  have hcl_s : LibsignalCodeLoaded lsmpl s.mem := hmeta.2.2.2.2.2.2.1
  refine reaches_pc_seq_lscl hcl_s (reaches_pc_lsro_preserve hro (sepWP_to_reaches_pc hwp_bl hmem_emp)) ?_
  intro s_call hpc_call _
    ⟨⟨P1, hm_call, ⟨hP1, hvm_bl, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c, hcs_c⟩⟩, hro_call⟩
    hcl_call
  subst hP1
  rw [emp_sepConj] at hm_call
  have hA_call : A.atState lim st s_call = A.atState lim st s :=
    A.atState_eq_of_vmPreserved lim st hvm_bl
  rw [← hA_call] at hm_call
  unfold tryDecryptCommonHeap at hm_call
  rw [trAt_eq_ratchetAt_trRestAt, signalMessageAt_eq_srk_rest,
      memRegion_0x140_split_findReceiverChainKey, logOff_tryDecryptDummyImg,
      stackAt_tryDecryptSubStack_sub s0.sp findReceiverChainKeyStack (by decide),
      sessionStateAt_atState, ratchetAt_atState, trRestAt_atState,
      protocolAddressAt_atState, protocolAddressAt_atState, signalMessageRestAt_atState] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  let fg : FindReceiverChainKeyGhost :=
    { self := sp + 0x38#64, G := trG.ratchet, st := tr.ratchet,
      theirA := x.msgA + 0x38#64, their := x.msg.senderRatchetKey, ret := sp + 0x190#64 }
  let F_call : SepProp :=
    sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ trRestAt A.repAlloc (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1b8#64) 0x3c8 ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
    protocolAddressAt A.repAlloc x.loc x.locA ∗ signalMessageRestAt A.repAlloc x.msgG x.msgA x.msg ∗
    tapeAfter ctl x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64) (tryDecryptSubStack - findReceiverChainKeyStack) ∗
    tryDecryptSavedRegs s0.sp s0 ∗ (A.atState lim st s_call).pool ∗ R
  have hfrck_blk := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H) hfrck
  have hpre_call : s_call.mem ⊨ (findReceiverChainKeyPlacedSpec A).pre fg s_call ∗ F_call := by
    dsimp only [findReceiverChainKeyPlacedSpec, findReceiverChainKeyPlacedAllocSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.findReceiverChainKeyPlacedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hro_call, hx0_c.trans hx0, hx1_c.trans hx1, hx8_c.trans hx8⟩, ?_⟩
    rw [hsp_call]
    dsimp only [fg, F_call, sp] at hm_call ⊢
    convert hm_call using 1; sep_ac_rfl
  refine reaches_pc_call_lscl hfrck_blk fg F_call hpc_call hwpInv_call.1 hlr_call hcl_call hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hcl_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  dsimp only [findReceiverChainKeyPlacedSpec, findReceiverChainKeyPlacedAllocSpec, withVmPreserved,
    CryptoVerification.LibsignalTripleRatchet.findReceiverChainKeyPlacedSpec] at hpost_ret
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨hvm_ret, hm_ret⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_ret
  rcases hm_ret with ⟨htr_ret, hm_ret⟩
  have hsp_ret' : s_ret.sp = s0.sp - 1504#64 := by reg_chain
  have halign_ret : s_ret.spAligned = true := by
    rw [State.spAligned, hsp_ret', ← hwpInv_call.2.1]; exact halign_call
  have hmeta_ret : tryDecryptMidMeta_placed s0 s_ret :=
    ⟨hrun_ret, hsp_ret', hwpInv_call.2.2.1, halign_ret, by reg_chain, by reg_chain,
     hcl_ret, by reg_chain⟩
  refine ⟨hmeta_ret, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
  have hpool_ret : (A.atState lim st s_call).pool = (A.atState lim st s_ret).pool :=
    (A.pool_transport lim st s_call s_ret hvm_ret).symm
  rw [hsp_call] at hm_ret
  unfold tryDecryptCommonHeap
  rw [trAt_eq_ratchetAt_trRestAt, signalMessageAt_eq_srk_rest, logOff_tryDecryptDummyImg,
      stackAt_tryDecryptSubStack_sub s0.sp findReceiverChainKeyStack (by decide),
      sessionStateAt_atState, ratchetAt_atState, trRestAt_atState,
      protocolAddressAt_atState, protocolAddressAt_atState, signalMessageRestAt_atState]
  dsimp only [fg, F_call, sp] at hm_ret ⊢
  rw [hpool_ret] at hm_ret
  convert hm_ret using 1; sep_ac_rfl

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainStackBudget
