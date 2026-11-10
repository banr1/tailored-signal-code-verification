/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvictBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep5
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitWp
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded DH Step Commit Sub-Segment 4 (`+0xaf0 → +0xb98`) & Step 4/5 Block WPs

Provides `VmPreserved`-carrying basic-block `SepWP` bundles (`DhCommitStep45BlockWp`) for blocks
`130` and `433`, stack-parametric `dropChainSpecWithStack` and `evictActiveWithStack`, and the
total-correctness receiver-chain eviction loop (`dhCommit_evict_loop_of_wp`, `dhCommit_step4_of_wp`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetStep4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ReceiverChain)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecBuf)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchet (sessionMemmoveSpec)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  DropChainGhost dropChainStack dropChainStackX
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_131 blkPC_434 blkPl_131 blkPl_434
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit (
  ChainArrayBytes add_assoc_const cells_12_to_memRegion_96
  chainAt_of_bytes chainBytes chainBytes_length chainHeap chainHeap_srk_cap_ne_zero
  chainHeaps elim_memRegion_104 elim_memRegion_96 evictList evictList_cons_of_ge_six
  evictList_of_le_five memmove_len_toNat optChainKeyPadLen optChainKeyTailBytes
  pack64 pointsToBytes_chainBytes_eq_13_cells saturating_sub_one_u32 sub_one_ofNat_succ
  vecBuf_chainAt_expose_for_remove0 vecBuf_chainAt_of_remove0
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts (
  ge_six_of_not_lt_six le_five_of_lt_six le_five_of_not_ge_six len_lt_of_cons_le
  memmove_bounds setMem_trace setPC_trace setPState_trace spAligned_of_sp_eq
  ult_five_eq_false_of_le_five ult_five_of_ge_six ult_six_eq_false_of_not_lt_six
  ult_six_of_lt_six writeReg32_trace writeReg64_trace
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvictBudget (
  evictActive evictActiveX
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropChainSpec dropChainSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)

/-! ## 1. `VmPreserved`-Carrying Basic-Block `SepWP` Predicates & Block `130` / `433` Instances -/

abbrev CommitStep4aLoVmWp (prog : Program) (entry : BitVec 64) : Prop :=
  ∀ (sp newLen : BitVec 64) (s : State),
    s.pc = entry + 0xaf0#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    BitVec.ult newLen 6#64 = true →
    SepWP prog (entry + 0xb98#64) s ((sp + 0x48#64) ↦₆₄ newLen)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = newLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x48#64) ↦₆₄ newLen)))

abbrev CommitStep4aGeVmWp (prog : Program) (entry : BitVec 64) : Prop :=
  ∀ (sp newLen : BitVec 64) (s : State),
    s.pc = entry + 0xaf0#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x25 = sp + 0x190#64 → BitVec.ult newLen 6#64 = false →
    SepWP prog (entry + 0xb04#64) s ((sp + 0x48#64) ↦₆₄ newLen)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = sp + 0x190#64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧
        sf.readReg64 .x28 = newLen ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x48#64) ↦₆₄ newLen)))

abbrev CommitStep4bPreMemmoveVmWp (prog : Program) (entry memmoveEntry : BitVec 64) : Prop :=
  ∀ (sp chainsPtr curLen : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
     s500 s508 s510 s518 s520 s528 s530 s538 s540 s548 s550 s558 : BitVec 64) (s : State),
    s.pc = entry + 0xb04#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x24 = sp + 0x190#64 →
    s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x27 = 0xffffffffffffff98#64 →
    s.readReg64 .x28 = curLen →
    SepWP prog memmoveEntry s
      (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ (chainsPtr ↦₆₄ c0) ∗ ((chainsPtr + 8#64) ↦₆₄ c1) ∗
       ((chainsPtr + 16#64) ↦₆₄ c2) ∗ ((chainsPtr + 24#64) ↦₆₄ c3) ∗ ((chainsPtr + 32#64) ↦₆₄ c4) ∗
       ((chainsPtr + 40#64) ↦₆₄ c5) ∗ ((chainsPtr + 48#64) ↦₆₄ c6) ∗ ((chainsPtr + 56#64) ↦₆₄ c7) ∗
       ((chainsPtr + 64#64) ↦₆₄ c8) ∗ ((chainsPtr + 72#64) ↦₆₄ c9) ∗ ((chainsPtr + 80#64) ↦₆₄ c10) ∗
       ((chainsPtr + 88#64) ↦₆₄ c11) ∗ ((chainsPtr + 96#64) ↦₆₄ c12) ∗
       ((sp + 0x500#64) ↦₆₄ s500) ∗ ((sp + 0x508#64) ↦₆₄ s508) ∗ ((sp + 0x510#64) ↦₆₄ s510) ∗
       ((sp + 0x518#64) ↦₆₄ s518) ∗ ((sp + 0x520#64) ↦₆₄ s520) ∗ ((sp + 0x528#64) ↦₆₄ s528) ∗
       ((sp + 0x530#64) ↦₆₄ s530) ∗ ((sp + 0x538#64) ↦₆₄ s538) ∗ ((sp + 0x540#64) ↦₆₄ s540) ∗
       ((sp + 0x548#64) ↦₆₄ s548) ∗ ((sp + 0x550#64) ↦₆₄ s550) ∗ ((sp + 0x558#64) ↦₆₄ s558))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = chainsPtr ∧ sf.readReg64 .x1 = chainsPtr + 104#64 ∧
        sf.readReg64 .x2 = 0xffffffffffffff98#64 + curLen * 104#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x24 = sp + 0x190#64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x26 = c0 ∧
        sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧ sf.readReg64 .x28 = curLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xb4c#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ (chainsPtr ↦₆₄ c0) ∗ ((chainsPtr + 8#64) ↦₆₄ c1) ∗
          ((chainsPtr + 16#64) ↦₆₄ c2) ∗ ((chainsPtr + 24#64) ↦₆₄ c3) ∗ ((chainsPtr + 32#64) ↦₆₄ c4) ∗
          ((chainsPtr + 40#64) ↦₆₄ c5) ∗ ((chainsPtr + 48#64) ↦₆₄ c6) ∗ ((chainsPtr + 56#64) ↦₆₄ c7) ∗
          ((chainsPtr + 64#64) ↦₆₄ c8) ∗ ((chainsPtr + 72#64) ↦₆₄ c9) ∗ ((chainsPtr + 80#64) ↦₆₄ c10) ∗
          ((chainsPtr + 88#64) ↦₆₄ c11) ∗ ((chainsPtr + 96#64) ↦₆₄ c12) ∗
          ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
          ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
          ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
          ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12)))

abbrev CommitStep4bPostMemmoveVmWp (prog : Program) (entry dropChainEntry : BitVec 64) : Prop :=
  ∀ (sp curLen : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
     s190 s198 s1a0 s1a8 s1b0 s1b8 s1c0 s1c8 s1d0 s1d8 s1e0 s1e8 s1f0 : BitVec 64) (s : State),
    s.pc = entry + 0xb4c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x24 = sp + 0x190#64 →
    s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x26 = c0 →
    s.readReg64 .x27 = 0xffffffffffffff98#64 → s.readReg64 .x28 = curLen →
    c0 + 1#64 ≠ 0#64 →
    SepWP prog dropChainEntry s
      (((sp + 0x48#64) ↦₆₄ curLen) ∗
       ((sp + 0x190#64) ↦₆₄ s190) ∗ ((sp + 0x198#64) ↦₆₄ s198) ∗ ((sp + 0x1a0#64) ↦₆₄ s1a0) ∗
       ((sp + 0x1a8#64) ↦₆₄ s1a8) ∗ ((sp + 0x1b0#64) ↦₆₄ s1b0) ∗ ((sp + 0x1b8#64) ↦₆₄ s1b8) ∗
       ((sp + 0x1c0#64) ↦₆₄ s1c0) ∗ ((sp + 0x1c8#64) ↦₆₄ s1c8) ∗ ((sp + 0x1d0#64) ↦₆₄ s1d0) ∗
       ((sp + 0x1d8#64) ↦₆₄ s1d8) ∗ ((sp + 0x1e0#64) ↦₆₄ s1e0) ∗ ((sp + 0x1e8#64) ↦₆₄ s1e8) ∗
       ((sp + 0x1f0#64) ↦₆₄ s1f0) ∗
       ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
       ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
       ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
       ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x190#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x24 = sp + 0x190#64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x26 = c0 ∧
        sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧ sf.readReg64 .x28 = curLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xb8c#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x48#64) ↦₆₄ (curLen - 1#64)) ∗
          ((sp + 0x190#64) ↦₆₄ c0) ∗ ((sp + 0x198#64) ↦₆₄ c1) ∗ ((sp + 0x1a0#64) ↦₆₄ c2) ∗
          ((sp + 0x1a8#64) ↦₆₄ c3) ∗ ((sp + 0x1b0#64) ↦₆₄ c4) ∗ ((sp + 0x1b8#64) ↦₆₄ c5) ∗
          ((sp + 0x1c0#64) ↦₆₄ c6) ∗ ((sp + 0x1c8#64) ↦₆₄ c7) ∗ ((sp + 0x1d0#64) ↦₆₄ c8) ∗
          ((sp + 0x1d8#64) ↦₆₄ c9) ∗ ((sp + 0x1e0#64) ↦₆₄ c10) ∗ ((sp + 0x1e8#64) ↦₆₄ c11) ∗
          ((sp + 0x1f0#64) ↦₆₄ c12) ∗
          ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
          ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
          ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
          ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12)))

abbrev CommitStep4cHiVmWp (prog : Program) (entry : BitVec 64) : Prop :=
  ∀ (sp nextLen : BitVec 64) (s : State),
    s.pc = entry + 0xb8c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    BitVec.ult 5#64 nextLen = true →
    SepWP prog (entry + 0xb04#64) s ((sp + 0x48#64) ↦₆₄ nextLen)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = nextLen ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x48#64) ↦₆₄ nextLen)))

abbrev CommitStep4cLeVmWp (prog : Program) (entry : BitVec 64) : Prop :=
  ∀ (sp nextLen : BitVec 64) (s : State),
    s.pc = entry + 0xb8c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    BitVec.ult 5#64 nextLen = false →
    SepWP prog (entry + 0xb98#64) s ((sp + 0x48#64) ↦₆₄ nextLen)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = nextLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x48#64) ↦₆₄ nextLen)))

abbrev CommitStep5VmWp (prog : Program) (entry : BitVec 64) : Prop :=
  ∀ (sp : BitVec 64) (sck16 rck16 msgW oldTag oldSck16 v2d0 : BitVec 32)
    (oldSpk0 oldSpk1 oldSpk2 oldSpk3 oldSk0 oldSk1 oldSk2 oldSk3
     oldSck0 oldSck1 oldSck2 oldSck3 spk0 spk1 spk2 spk3 sk0 sk1 sk2 sk3
     sck0 sck1 sck2 sck3 rck0 rck1 rck2 rck3 v2b0 v2b8 v2c0 v2c8
     v450 v458 v460 v468 v470 v478 v480 v488 v490 v498 : BitVec 64) (s : State),
    s.pc = entry + 0xb98#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x25 = sp + 0x190#64 →
    SepWP prog (entry + 0x3e4#64) s
      (((sp + 0x8#64) ↦₃₂ sck16) ∗ ((sp + 0x10#64) ↦₃₂ rck16) ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x50#64) ↦₃₂ oldTag) ∗ ((sp + 0x54#64) ↦₆₄ oldSpk0) ∗ ((sp + 0x5c#64) ↦₆₄ oldSpk1) ∗
       ((sp + 0x64#64) ↦₆₄ oldSpk2) ∗ ((sp + 0x6c#64) ↦₆₄ oldSpk3) ∗ ((sp + 0x74#64) ↦₆₄ oldSk0) ∗
       ((sp + 0x7c#64) ↦₆₄ oldSk1) ∗ ((sp + 0x84#64) ↦₆₄ oldSk2) ∗ ((sp + 0x8c#64) ↦₆₄ oldSk3) ∗
       ((sp + 0x94#64) ↦₆₄ oldSck0) ∗ ((sp + 0x9c#64) ↦₆₄ oldSck1) ∗ ((sp + 0xa4#64) ↦₃₂ oldSck16) ∗
       ((sp + 0xa8#64) ↦₆₄ oldSck2) ∗ ((sp + 0xb0#64) ↦₆₄ oldSck3) ∗ ((sp + 0x2b0#64) ↦₆₄ v2b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ v2b8) ∗ ((sp + 0x2c0#64) ↦₆₄ v2c0) ∗ ((sp + 0x2c8#64) ↦₆₄ v2c8) ∗
       ((sp + 0x2d0#64) ↦₃₂ v2d0) ∗ ((sp + 0x400#64) ↦₆₄ spk0) ∗ ((sp + 0x408#64) ↦₆₄ spk1) ∗
       ((sp + 0x410#64) ↦₆₄ spk2) ∗ ((sp + 0x418#64) ↦₆₄ spk3) ∗ ((sp + 0x420#64) ↦₆₄ sk0) ∗
       ((sp + 0x428#64) ↦₆₄ sk1) ∗ ((sp + 0x430#64) ↦₆₄ sk2) ∗ ((sp + 0x438#64) ↦₆₄ sk3) ∗
       ((sp + 0x450#64) ↦₆₄ v450) ∗ ((sp + 0x458#64) ↦₆₄ v458) ∗ ((sp + 0x460#64) ↦₆₄ v460) ∗
       ((sp + 0x468#64) ↦₆₄ v468) ∗ ((sp + 0x470#64) ↦₆₄ v470) ∗ ((sp + 0x478#64) ↦₆₄ v478) ∗
       ((sp + 0x480#64) ↦₆₄ v480) ∗ ((sp + 0x488#64) ↦₆₄ v488) ∗ ((sp + 0x490#64) ↦₆₄ v490) ∗
       ((sp + 0x498#64) ↦₆₄ v498) ∗ ((sp + 0x4c0#64) ↦₆₄ rck2) ∗ ((sp + 0x4c8#64) ↦₆₄ rck3) ∗
       ((sp + 0x4d0#64) ↦₆₄ rck0) ∗ ((sp + 0x4d8#64) ↦₆₄ rck1) ∗ ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
       ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = msgW.zeroExtend 64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = s.readReg64 .x30 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x8#64) ↦₃₂ sck16) ∗ ((sp + 0x10#64) ↦₃₂ rck16) ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗
          ((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦₆₄ spk0) ∗ ((sp + 0x5c#64) ↦₆₄ spk1) ∗
          ((sp + 0x64#64) ↦₆₄ spk2) ∗ ((sp + 0x6c#64) ↦₆₄ spk3) ∗ ((sp + 0x74#64) ↦₆₄ sk0) ∗
          ((sp + 0x7c#64) ↦₆₄ sk1) ∗ ((sp + 0x84#64) ↦₆₄ sk2) ∗ ((sp + 0x8c#64) ↦₆₄ sk3) ∗
          ((sp + 0x94#64) ↦₆₄ sck0) ∗ ((sp + 0x9c#64) ↦₆₄ sck1) ∗ ((sp + 0xa4#64) ↦₃₂ sck16) ∗
          ((sp + 0xa8#64) ↦₆₄ sck2) ∗ ((sp + 0xb0#64) ↦₆₄ sck3) ∗ ((sp + 0x2b0#64) ↦₆₄ rck2) ∗
          ((sp + 0x2b8#64) ↦₆₄ rck3) ∗ ((sp + 0x2c0#64) ↦₆₄ rck0) ∗ ((sp + 0x2c8#64) ↦₆₄ rck1) ∗
          ((sp + 0x2d0#64) ↦₃₂ rck16) ∗ ((sp + 0x400#64) ↦₆₄ spk0) ∗ ((sp + 0x408#64) ↦₆₄ spk1) ∗
          ((sp + 0x410#64) ↦₆₄ spk2) ∗ ((sp + 0x418#64) ↦₆₄ spk3) ∗ ((sp + 0x420#64) ↦₆₄ sk0) ∗
          ((sp + 0x428#64) ↦₆₄ sk1) ∗ ((sp + 0x430#64) ↦₆₄ sk2) ∗ ((sp + 0x438#64) ↦₆₄ sk3) ∗
          ((sp + 0x450#64) ↦₆₄ spk0) ∗ ((sp + 0x458#64) ↦₆₄ spk1) ∗ ((sp + 0x460#64) ↦₆₄ spk2) ∗
          ((sp + 0x468#64) ↦₆₄ spk3) ∗ ((sp + 0x470#64) ↦₆₄ sk0) ∗ ((sp + 0x478#64) ↦₆₄ sk1) ∗
          ((sp + 0x480#64) ↦₆₄ sk2) ∗ ((sp + 0x488#64) ↦₆₄ sk3) ∗ ((sp + 0x490#64) ↦₆₄ sck0) ∗
          ((sp + 0x498#64) ↦₆₄ sck1) ∗ ((sp + 0x4c0#64) ↦₆₄ rck2) ∗ ((sp + 0x4c8#64) ↦₆₄ rck3) ∗
          ((sp + 0x4d0#64) ↦₆₄ rck0) ∗ ((sp + 0x4d8#64) ↦₆₄ rck1) ∗ ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
          ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1)))

/-- Bundle of `VmPreserved`-carrying `SepWP` obligations for Steps 4 & 5 (`+0xaf0 → +0x3e4`). -/
structure DhCommitStep45BlockWp (prog : Program) (entry memmoveEntry dropChainEntry : BitVec 64) :
    Prop where
  step4a_lo : CommitStep4aLoVmWp prog entry
  step4a_ge : CommitStep4aGeVmWp prog entry
  step4b_pre_memmove : CommitStep4bPreMemmoveVmWp prog entry memmoveEntry
  step4b_post_memmove : CommitStep4bPostMemmoveVmWp prog entry dropChainEntry
  step4c_hi : CommitStep4cHiVmWp prog entry
  step4c_le : CommitStep4cLeVmWp prog entry
  step5 : CommitStep5VmWp prog entry

section BlockWpInstances

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "wp_reg" : tactic =>
  `(tactic| simp only [wp_norm,
    writeReg64_trace, writeReg32_trace, setPC_trace,
    setPState_trace, setMem_trace, State.trace_writeVReg128,
    *])

local macro "wp_done_vm_reg" hsp_al:ident : tactic =>
  `(tactic|
    by_vm_steps (
      wp_steps
      refine SepWP.done (by rfl) (by wp_reg) ?_
      refine And.intro (by wp_reg) ?_
      refine And.intro (by wp_reg)
        (And.intro (spAligned_of_sp_eq (by wp_reg) $hsp_al) ?_)
      repeat' (refine And.intro ?_ ?_ <;> [wp_reg; skip])
      try rw [← saturating_sub_one_u32 _]
      exact Entails.refl _))

set_option maxHeartbeats 1200000 in
theorem dhCommitStep45BlockWp_159 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitStep45BlockWp ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      (lsmpl.ρ "memmove") (lsmpl.base 142) where
  step4a_lo := by intro _ _ s hpc hrun hsp hsp_align hlo; wp_done_vm_reg hsp_align
  step4a_ge := by intro _ _ s hpc hrun hsp hsp_align hx25 hge; wp_done_vm_reg hsp_align
  step4b_pre_memmove := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx27 hx28
    wp_done_vm_reg hsp_align
  step4b_post_memmove := by
    intro _ _ c0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx26 hx27 hx28 hc0_ne
    have hbeq : (c0 + 1#64 == 0#64) = false := beq_false_of_ne hc0_ne
    wp_done_vm_reg hsp_align
  step4c_hi := by intro _ _ s hpc hrun hsp hsp_align hhi; wp_done_vm_reg hsp_align
  step4c_le := by intro _ _ s hpc hrun hsp hsp_align hle; wp_done_vm_reg hsp_align
  step5 := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx25
    wp_done_vm_reg hsp_align

set_option maxHeartbeats 1200000 in
theorem dhCommitStep45BlockWp_549 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitStep45BlockWp ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      (lsmpl.ρ "memmove") (lsmpl.base 445) where
  step4a_lo := by intro _ _ s hpc hrun hsp hsp_align hlo; wp_done_vm_reg hsp_align
  step4a_ge := by intro _ _ s hpc hrun hsp hsp_align hx25 hge; wp_done_vm_reg hsp_align
  step4b_pre_memmove := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx27 hx28
    wp_done_vm_reg hsp_align
  step4b_post_memmove := by
    intro _ _ c0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx26 hx27 hx28 hc0_ne
    have hbeq : (c0 + 1#64 == 0#64) = false := beq_false_of_ne hc0_ne
    wp_done_vm_reg hsp_align
  step4c_hi := by intro _ _ s hpc hrun hsp hsp_align hhi; wp_done_vm_reg hsp_align
  step4c_le := by intro _ _ s hpc hrun hsp hsp_align hle; wp_done_vm_reg hsp_align
  step5 := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx25
    wp_done_vm_reg hsp_align

end BlockWpInstances

/-! ## 2. Stack-Parametric `dropChainSpecWithStack`, `evictActiveWithStack`, & `Steps` Combinators -/

/-- Stack-parametric budget-threaded specification of `drop_glue<session_structure::Chain>`,
definitionally equal to `dropChainSpec` at `dropChainStack` and `dropChainSpecX` at
`dropChainStackX`. -/
def dropChainSpecWithStack [LibsignalPlacement] (stk : Nat) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DropChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      chainAt A.repAlloc x.gc x.a ∗ A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 104 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp stk

theorem dropChainSpecWithStack_eq_dropChainSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    dropChainSpecWithStack dropChainStack M A lim = dropChainSpec M A lim :=
  rfl

theorem dropChainSpecWithStack_eq_dropChainSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    dropChainSpecWithStack dropChainStackX M A lim = dropChainSpecX M A lim :=
  rfl

/-- Stack-parametric budget-threaded receiver-chain eviction loop invariant, definitionally equal
to `DhCommitEvictBudget.evictActive` at `dropChainStack` and `evictActiveX` at `dropChainStackX`. -/
def evictActiveWithStack {M : AllocCostModel} (stk : Nat) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) : SepProp :=
  ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
  ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
  vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
  memRegion (sp + 0x190#64) 104 ∗
  memRegion (sp + 0x500#64) 96 ∗
  A.pool lim st s ∗
  stackAt sp stk

theorem evictActiveWithStack_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) :
    evictActiveWithStack dropChainStack A lim st s sp chainsCap chainsPtr gcs =
      evictActive A lim st s sp chainsCap chainsPtr gcs :=
  rfl

theorem evictActiveWithStack_eq_x {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) :
    evictActiveWithStack dropChainStackX A lim st s sp chainsCap chainsPtr gcs =
      evictActiveX A lim st s sp chainsCap chainsPtr gcs :=
  rfl

theorem freeOnlyEvs_append {evs₁ evs₂ : List AllocEvent}
    (h1 : FreeOnlyEvs evs₁) (h2 : FreeOnlyEvs evs₂) :
    FreeOnlyEvs (evs₁ ++ evs₂) := by
  intro ev hev
  rcases List.mem_append.mp hev with hev1 | hev2
  · exact h1 ev hev1
  · exact h2 ev hev2

theorem steps_of_sepWP {prog : Program} {s : State}
    {target : BitVec 64} {Pre Rest : SepProp}
    {PostWP : State → SepProp → Prop} {Q : State → Prop}
    (hwp : SepWP prog target s Pre PostWP)
    (hmem : s.mem ⊨ Pre ∗ Rest)
    (hL : prog.CodeLoaded s.mem)
    (hcont : ∀ s1 P_out,
      s1.pc = target → s1.status = .Running →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ P_out ∗ Rest) →
      PostWP s1 P_out →
      ∃ sf, Steps prog s1 sf ∧ Q sf) :
    ∃ sf, Steps prog s sf ∧ Q sf := by
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_out, hm1, hpost1⟩ | ⟨_, hoom⟩⟩ := hwp.elim hmem hL
  · obtain ⟨sf, hsteps2, hQ⟩ :=
      hcont s1 P_out hpc1 hrun1 (hL.of_keepsFrozen hsteps1.keepsFrozen) hm1 hpost1
    exact ⟨sf, hsteps1.trans hsteps2, hQ⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem steps_of_call_no_panic {α : Type} {prog : Program} {s : State}
    {entry ret_pc : BitVec 64} {spec : Spec α} {arg : α} {Rest : SepProp}
    {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hpre : s.mem ⊨ spec.pre arg s ∗ Rest)
    (hL : prog.CodeLoaded s.mem)
    (hpan_false : ∀ sf, spec.onPanic arg s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl)
    (hcont : ∀ s1,
      s1.pc = ret_pc → s1.status = .Running →
      s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ Rest) →
      ∃ sf, Steps prog s1 sf ∧ Q sf) :
    ∃ sf, Steps prog s sf ∧ Q sf := by
  obtain ⟨s1, hsteps1, hout, -⟩ :=
    hcall.no_fault_before_outcome arg Rest s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpc1, hsp1, hrun1⟩, ⟨_, hcs1⟩, hpost1⟩ | ⟨_, hpost1⟩ | ⟨code, _, hpost1⟩ | ⟨_, hpost1⟩
  · rw [show Reg.lr = Reg.x30 from rfl, hlr] at hpc1
    have hsp_align1 : s1.spAligned = true := by
      unfold State.spAligned at hsp ⊢; rw [hsp1]; exact hsp
    obtain ⟨sf, hsteps2, hQ⟩ :=
      hcont s1 hpc1 hrun1 hsp1 hsp_align1 hcs1 (hL.of_keepsFrozen hsteps1.keepsFrozen) hpost1
    exact ⟨sf, hsteps1.trans hsteps2, hQ⟩
  · rw [hpan_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hoom_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1

/-! ## 3. Budget-Threaded Eviction Loop (`dhCommit_evict_one_of_wp`, `dhCommit_evict_loop_of_wp`, `dhCommit_step4_of_wp`) -/

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Single iteration of the receiver-chain eviction loop (`+0xb04 → +0xb8c`) for `gc₀ :: gcs`,
yielding `FreeOnlyEvs evs` with zero `FitsEnv` preconditions. -/
theorem dhCommit_evict_one_of_wp [LibsignalPlacement]
    {prog : Program} {entry memmoveEntry dropChainEntry : BitVec 64}
    {stk : Nat} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (hwp_pre : CommitStep4bPreMemmoveVmWp prog entry memmoveEntry)
    (hwp_post : CommitStep4bPostMemmoveVmWp prog entry dropChainEntry)
    (hMemmove : subroutine_ok prog memmoveEntry (sessionMemmoveBudgetSpec stk))
    (hDrop : subroutine_ok prog dropChainEntry (dropChainSpecWithStack stk M A lim))
    (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (gc₀ : ChainGhost × ReceiverChain) (gcs : List (ChainGhost × ReceiverChain))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hpc : s.pc = entry + 0xb04#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx23 : s.readReg64 .x23 = sp + 0x500#64) (hx24 : s.readReg64 .x24 = sp + 0x190#64)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64) (hx27 : s.readReg64 .x27 = 0xffffffffffffff98#64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (gc₀ :: gcs).length)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨ evictActiveWithStack stk A lim st s sp chainsCap chainsPtr (gc₀ :: gcs) ∗ (Frame ∗ R))
    (hlr_ls : LsRetAddr624 (entry + 0xb8c#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    ∃ sf, Steps prog s sf ∧ ∃ evs : List AllocEvent,
      FreeOnlyEvs evs ∧
      sf.pc = entry + 0xb8c#64 ∧ sf.status = .Running ∧ sf.sp = sp ∧ sf.spAligned = true ∧
      sf.trace = s0.trace ∧
      sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
      sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
      sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x24 = sp + 0x190#64 ∧
      sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧
      sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
      prog.CodeLoaded sf.mem ∧
      (sf.mem ⊨
        evictActiveWithStack stk A lim (M.stepEvents evs st) sf sp chainsCap chainsPtr gcs ∗
          (Frame ∗ R)) := by
  unfold evictActiveWithStack at hmem
  have hexp := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecBuf_chainAt_expose_for_remove0 A.repAlloc chainsCap chainsPtr gc₀ gcs)))))
    hmem
  have hexp_pull :
      s.mem ⊨
        (∃∗ pad₀ : List (BitVec 8), ∃∗ bs_rest : List (BitVec 8),
          ⌜pad₀.length = optChainKeyPadLen gc₀.2.chainKey ∧
            ChainArrayBytes gcs bs_rest ∧ bs_rest.length = gcs.length * 104 ∧
            gcs.length + 1 ≤ chainsCap.toNat ∧ chainsCap.toNat * 104 < 2 ^ 63 ∧
            chainsPtr ≠ 0 ∧ chainsCap ≠ 0⌝ ∗
          A.repAlloc.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          (chainsPtr ↦ₛ chainBytes gc₀ pad₀) ∗
          ((chainsPtr + 104#64) ↦ₛ bs_rest) ∗
          memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
            ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
          chainHeap A.repAlloc gc₀ ∗
          chainHeaps A.repAlloc gcs) ∗
        (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
         memRegion (sp + 0x190#64) 104 ∗
         memRegion (sp + 0x500#64) 96 ∗
         A.pool lim st s ∗
         stackAt sp stk ∗
         (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hexp
    sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hexp_pull
  rcases hexp_pull with ⟨pad₀, hexp_pull⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hexp_pull
  rcases hexp_pull with ⟨bs_rest, hexp_pull⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hexp_pull
  rcases hexp_pull with ⟨⟨hpad₀, hrest, hbs_len, hcap_le, hcap_lt, hptr, _hcap_ne⟩, hm0⟩
  have hsrk_pull :
      s.mem ⊨ chainHeap A.repAlloc gc₀ ∗
        (A.repAlloc.live chainsPtr (chainsCap.toNat * 104) 8 ∗
         (chainsPtr ↦ₛ chainBytes gc₀ pad₀) ∗
         ((chainsPtr + 104#64) ↦ₛ bs_rest) ∗
         memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
           ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
         chainHeaps A.repAlloc gcs ∗
         ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
         memRegion (sp + 0x190#64) 104 ∗
         memRegion (sp + 0x500#64) 96 ∗
         A.pool lim st s ∗
         stackAt sp stk ∗
         (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm0
    sep_ac_rfl
  have hsrk_ne_mem := Satisfies.mono (sepConj_mono_left (chainHeap_srk_cap_ne_zero A.repAlloc gc₀)) hsrk_pull
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsrk_ne_mem
  rcases hsrk_ne_mem with ⟨hc0_ne, hm1⟩
  have hm500_front :
      s.mem ⊨ memRegion (sp + 0x500#64) 96 ∗
        ((chainsPtr ↦ₛ chainBytes gc₀ pad₀) ∗
         ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
         memRegion (sp + 0x190#64) 104 ∗
         A.repAlloc.live chainsPtr (chainsCap.toNat * 104) 8 ∗
         ((chainsPtr + 104#64) ↦ₛ bs_rest) ∗
         memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
           ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
         chainHeap A.repAlloc gc₀ ∗
         chainHeaps A.repAlloc gcs ∗
         A.pool lim st s ∗
         stackAt sp stk ∗
         (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    sep_ac_rfl
  obtain ⟨s500, s508, s510, s518, s520, s528, s530, s538, s540, s548, s550, s558, hm2⟩ :=
    elim_memRegion_96 hm500_front
  set tail₀ := optChainKeyTailBytes gc₀.1.ck gc₀.2.chainKey pad₀
  set c0 := gc₀.1.srk.cap
  set c1 := gc₀.1.srk.ptr
  set c2 := BitVec.ofNat 64 gc₀.1.srk.bytes.length
  set c3 := gc₀.1.priv.cap
  set c4 := gc₀.1.priv.ptr
  set c5 := BitVec.ofNat 64 gc₀.1.priv.bytes.length
  set c6 := gc₀.1.mkCap
  set c7 := gc₀.1.mkPtr
  set c8 := BitVec.ofNat 64 (gc₀.1.keys.zip gc₀.2.messageKeys).length
  set c9 := pack64 (tail₀.take 8)
  set c10 := pack64 ((tail₀.drop 8).take 8)
  set c11 := pack64 ((tail₀.drop 16).take 8)
  set c12 := pack64 (tail₀.drop 24)
  have hcells_ptr : (chainsPtr ↦ₛ chainBytes gc₀ pad₀) =
      (chainsPtr ↦₆₄ c0) ∗ ((chainsPtr + 8#64) ↦₆₄ c1) ∗ ((chainsPtr + 16#64) ↦₆₄ c2) ∗
      ((chainsPtr + 24#64) ↦₆₄ c3) ∗ ((chainsPtr + 32#64) ↦₆₄ c4) ∗ ((chainsPtr + 40#64) ↦₆₄ c5) ∗
      ((chainsPtr + 48#64) ↦₆₄ c6) ∗ ((chainsPtr + 56#64) ↦₆₄ c7) ∗ ((chainsPtr + 64#64) ↦₆₄ c8) ∗
      ((chainsPtr + 72#64) ↦₆₄ c9) ∗ ((chainsPtr + 80#64) ↦₆₄ c10) ∗ ((chainsPtr + 88#64) ↦₆₄ c11) ∗
      ((chainsPtr + 96#64) ↦₆₄ c12) :=
    pointsToBytes_chainBytes_eq_13_cells chainsPtr gc₀ hpad₀
  have hm_pre_wp :
      s.mem ⊨
        (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         (chainsPtr ↦₆₄ c0) ∗ ((chainsPtr + 8#64) ↦₆₄ c1) ∗ ((chainsPtr + 16#64) ↦₆₄ c2) ∗
         ((chainsPtr + 24#64) ↦₆₄ c3) ∗ ((chainsPtr + 32#64) ↦₆₄ c4) ∗ ((chainsPtr + 40#64) ↦₆₄ c5) ∗
         ((chainsPtr + 48#64) ↦₆₄ c6) ∗ ((chainsPtr + 56#64) ↦₆₄ c7) ∗ ((chainsPtr + 64#64) ↦₆₄ c8) ∗
         ((chainsPtr + 72#64) ↦₆₄ c9) ∗ ((chainsPtr + 80#64) ↦₆₄ c10) ∗ ((chainsPtr + 88#64) ↦₆₄ c11) ∗
         ((chainsPtr + 96#64) ↦₆₄ c12) ∗
         ((sp + 0x500#64) ↦₆₄ s500) ∗ ((sp + 0x508#64) ↦₆₄ s508) ∗ ((sp + 0x510#64) ↦₆₄ s510) ∗
         ((sp + 0x518#64) ↦₆₄ s518) ∗ ((sp + 0x520#64) ↦₆₄ s520) ∗ ((sp + 0x528#64) ↦₆₄ s528) ∗
         ((sp + 0x530#64) ↦₆₄ s530) ∗ ((sp + 0x538#64) ↦₆₄ s538) ∗ ((sp + 0x540#64) ↦₆₄ s540) ∗
         ((sp + 0x548#64) ↦₆₄ s548) ∗ ((sp + 0x550#64) ↦₆₄ s550) ∗ ((sp + 0x558#64) ↦₆₄ s558)) ∗
        ((((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
          memRegion (sp + 0x190#64) 104 ∗
          A.repAlloc.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          ((chainsPtr + 104#64) ↦ₛ bs_rest) ∗
          memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
            ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
          chainHeap A.repAlloc gc₀ ∗
          chainHeaps A.repAlloc gcs ∗
          A.pool lim st s ∗
          stackAt sp stk ∗
          Frame) ∗ R) := by
    rw [hcells_ptr] at hm2
    have e1 := add_assoc_const sp 0x500#64 8#64 0x508#64
    have e2 := add_assoc_const sp 0x500#64 16#64 0x510#64
    have e3 := add_assoc_const sp 0x500#64 24#64 0x518#64
    have e4 := add_assoc_const sp 0x500#64 32#64 0x520#64
    have e5 := add_assoc_const sp 0x500#64 40#64 0x528#64
    have e6 := add_assoc_const sp 0x500#64 48#64 0x530#64
    have e7 := add_assoc_const sp 0x500#64 56#64 0x538#64
    have e8 := add_assoc_const sp 0x500#64 64#64 0x540#64
    have e9 := add_assoc_const sp 0x500#64 72#64 0x548#64
    have e10 := add_assoc_const sp 0x500#64 80#64 0x550#64
    have e11 := add_assoc_const sp 0x500#64 88#64 0x558#64
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at hm2
    refine Satisfies.mono (Entails.of_eq ?_) hm2
    sep_ac_rfl
  refine steps_of_sepWP
    (hwp_pre sp chainsPtr
      (BitVec.ofNat 64 (gc₀ :: gcs).length)
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
      s500 s508 s510 s518 s520 s528 s530 s538 s540 s548 s550 s558
      s hpc hrun hsp hsp_align hx23 hx24 hx25 hx27 hx28)
    hm_pre_wp hL ?_
  intro s1 P1 hpc1 hrun1 hL1 hm_s1 hpost1
  rcases hpost1 with ⟨hvm1, hsp1, hsp_align1, htr1, hx0_1, hx1_1, hx2_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
  have hm_s1' := Satisfies.mono (sepConj_mono_left hP1) hm_s1
  rw [← A.pool_transport lim st s s1 hvm1] at hm_s1'
  set b₀ := chainBytes gc₀ pad₀
  have hb₀_len : b₀.length = 104 := chainBytes_length gc₀ hpad₀
  have hcomb_bytes : (chainsPtr ↦ₛ (b₀ ++ bs_rest)) =
      (chainsPtr ↦ₛ b₀) ∗ ((chainsPtr + 104#64) ↦ₛ bs_rest) := by
    rw [pointsToBytes_append, hb₀_len]
  have hx2_toNat : (s1.readReg64 .x2).toNat = gcs.length * 104 := by
    rw [hx2_1, List.length_cons]
    exact memmove_len_toNat hlen_lt
  have hm_memmove :
      s1.mem ⊨
        (sessionMemmoveBudgetSpec stk).pre (chainsPtr, b₀ ++ bs_rest, 0, 104, gcs.length * 104) s1 ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
          memRegion (sp + 0x190#64) 104 ∗
          ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
          ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
          ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
          ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12) ∗
          A.repAlloc.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
            ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
          chainHeap A.repAlloc gc₀ ∗
          chainHeaps A.repAlloc gcs ∗
          A.pool lim st s1 ∗
          Frame) ∗ R) := by
    dsimp only [sessionMemmoveBudgetSpec, sessionMemmoveSpec, libcMemmoveSpec]
    have hpre_pure :
        s1.readReg64 .x0 = chainsPtr + BitVec.ofNat 64 0 ∧
        s1.readReg64 .x1 = chainsPtr + BitVec.ofNat 64 104 ∧
        (s1.readReg64 .x2).toNat = gcs.length * 104 ∧
        0 + gcs.length * 104 ≤ (b₀ ++ bs_rest).length ∧
        104 + gcs.length * 104 ≤ (b₀ ++ bs_rest).length := by
      rw [BitVec.add_zero, List.length_append, hb₀_len, hbs_len]
      have ⟨hb1, hb2⟩ := memmove_bounds (n := gcs.length)
      exact ⟨hx0_1, hx1_1, hx2_toNat, hb1, hb2⟩
    rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpre_pure, ?_⟩
    rw [hcomb_bytes, show b₀ = chainBytes gc₀ pad₀ from rfl, hcells_ptr]
    refine Satisfies.mono (Entails.of_eq ?_) hm_s1'
    sep_ac_rfl
  refine steps_of_call_no_panic hMemmove
    hpc1 hrun1 hsp_align1 hx30_1 hm_memmove hL1 (by intro _; rfl) (by intros; rfl) (by intro _; rfl) ?_
  intro s2 hpc2 hrun2 hsp2 hsp_align2 hcs2 hL2 hm_s2
  dsimp only [sessionMemmoveBudgetSpec, sessionMemmoveSpec] at hm_s2
  rw [hsp1, sepConj_assoc, satisfies_pure_sepConj] at hm_s2
  rcases hm_s2 with ⟨hvm2, hm_s2⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_s2
  rcases hm_s2 with ⟨⟨_hx0_2, htr2⟩, hm_s2⟩
  rw [← A.pool_transport lim st s1 s2 hvm2] at hm_s2
  have hvec_reasm :
      s2.mem ⊨
        memRegion (sp + 0x190#64) 104 ∗
        (((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
         ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
         ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
         ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
         ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12) ∗
         ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
         chainHeap A.repAlloc gc₀ ∗
         A.pool lim st s2 ∗
         stackAt sp stk ∗
         (Frame ∗ R)) := by
    have hpull_rem :
        s2.mem ⊨
          (A.repAlloc.live chainsPtr (chainsCap.toNat * 104) 8 ∗
           (chainsPtr ↦ₛ listMove (b₀ ++ bs_rest) 0 104 (gcs.length * 104)) ∗
           memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
             ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
           chainHeaps A.repAlloc gcs) ∗
          (memRegion (sp + 0x190#64) 104 ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
           ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
           ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
           ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
           ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12) ∗
           ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
           chainHeap A.repAlloc gc₀ ∗
           A.pool lim st s2 ∗
           stackAt sp stk ∗
           (Frame ∗ R)) := by
      refine Satisfies.mono (Entails.of_eq ?_) hm_s2
      sep_ac_rfl
    have hrem := Satisfies.mono
      (sepConj_mono_left (vecBuf_chainAt_of_remove0 A.repAlloc chainsCap chainsPtr hb₀_len hrest hcap_le hcap_lt hptr))
      hpull_rem
    refine Satisfies.mono (Entails.of_eq ?_) hrem
    sep_ac_rfl
  obtain ⟨s190, s198, s1a0, s1a8, s1b0, s1b8, s1c0, s1c8, s1d0, s1d8, s1e0, s1e8, s1f0, hm_s2_cells⟩ :=
    elim_memRegion_104 hvec_reasm
  have hm_post_mm_wp :
      s2.mem ⊨
        (((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
         ((sp + 0x190#64) ↦₆₄ s190) ∗ ((sp + 0x198#64) ↦₆₄ s198) ∗ ((sp + 0x1a0#64) ↦₆₄ s1a0) ∗
         ((sp + 0x1a8#64) ↦₆₄ s1a8) ∗ ((sp + 0x1b0#64) ↦₆₄ s1b0) ∗ ((sp + 0x1b8#64) ↦₆₄ s1b8) ∗
         ((sp + 0x1c0#64) ↦₆₄ s1c0) ∗ ((sp + 0x1c8#64) ↦₆₄ s1c8) ∗ ((sp + 0x1d0#64) ↦₆₄ s1d0) ∗
         ((sp + 0x1d8#64) ↦₆₄ s1d8) ∗ ((sp + 0x1e0#64) ↦₆₄ s1e0) ∗ ((sp + 0x1e8#64) ↦₆₄ s1e8) ∗
         ((sp + 0x1f0#64) ↦₆₄ s1f0) ∗
         ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
         ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
         ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
         ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12)) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
          chainHeap A.repAlloc gc₀ ∗
          A.pool lim st s2 ∗
          stackAt sp stk ∗
          Frame) ∗ R) := by
    have e1 := add_assoc_const sp 0x190#64 8#64 0x198#64
    have e2 := add_assoc_const sp 0x190#64 16#64 0x1a0#64
    have e3 := add_assoc_const sp 0x190#64 24#64 0x1a8#64
    have e4 := add_assoc_const sp 0x190#64 32#64 0x1b0#64
    have e5 := add_assoc_const sp 0x190#64 40#64 0x1b8#64
    have e6 := add_assoc_const sp 0x190#64 48#64 0x1c0#64
    have e7 := add_assoc_const sp 0x190#64 56#64 0x1c8#64
    have e8 := add_assoc_const sp 0x190#64 64#64 0x1d0#64
    have e9 := add_assoc_const sp 0x190#64 72#64 0x1d8#64
    have e10 := add_assoc_const sp 0x190#64 80#64 0x1e0#64
    have e11 := add_assoc_const sp 0x190#64 88#64 0x1e8#64
    have e12 := add_assoc_const sp 0x190#64 96#64 0x1f0#64
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12] at hm_s2_cells
    refine Satisfies.mono (Entails.of_eq ?_) hm_s2_cells
    sep_ac_rfl
  refine steps_of_sepWP
    (hwp_post sp
      (BitVec.ofNat 64 (gc₀ :: gcs).length)
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
      s190 s198 s1a0 s1a8 s1b0 s1b8 s1c0 s1c8 s1d0 s1d8 s1e0 s1e8 s1f0
      s2 hpc2 hrun2 (by reg_chain) hsp_align2
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
      hc0_ne)
    hm_post_mm_wp hL2 ?_
  intro s3 P3 hpc3 hrun3 hL3 hm_s3 hpost3
  rcases hpost3 with ⟨hvm3, hsp3, hsp_align3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, hx24_3, hx25_3, _hx26_3, hx27_3, _hx28_3, hx29_3, hx30_3, hvregs_3, hP3⟩
  have hm_s3' := Satisfies.mono (sepConj_mono_left hP3) hm_s3
  rw [← A.pool_transport lim st s2 s3 hvm3] at hm_s3'
  have hcells_190 : ((sp + 0x190#64) ↦ₛ chainBytes gc₀ pad₀) =
      ((sp + 0x190#64) ↦₆₄ c0) ∗ ((sp + 0x198#64) ↦₆₄ c1) ∗ ((sp + 0x1a0#64) ↦₆₄ c2) ∗
      ((sp + 0x1a8#64) ↦₆₄ c3) ∗ ((sp + 0x1b0#64) ↦₆₄ c4) ∗ ((sp + 0x1b8#64) ↦₆₄ c5) ∗
      ((sp + 0x1c0#64) ↦₆₄ c6) ∗ ((sp + 0x1c8#64) ↦₆₄ c7) ∗ ((sp + 0x1d0#64) ↦₆₄ c8) ∗
      ((sp + 0x1d8#64) ↦₆₄ c9) ∗ ((sp + 0x1e0#64) ↦₆₄ c10) ∗ ((sp + 0x1e8#64) ↦₆₄ c11) ∗
      ((sp + 0x1f0#64) ↦₆₄ c12) := by
    have h := pointsToBytes_chainBytes_eq_13_cells (sp + 0x190#64) gc₀ hpad₀
    have e1 := add_assoc_const sp 0x190#64 8#64 0x198#64
    have e2 := add_assoc_const sp 0x190#64 16#64 0x1a0#64
    have e3 := add_assoc_const sp 0x190#64 24#64 0x1a8#64
    have e4 := add_assoc_const sp 0x190#64 32#64 0x1b0#64
    have e5 := add_assoc_const sp 0x190#64 40#64 0x1b8#64
    have e6 := add_assoc_const sp 0x190#64 48#64 0x1c0#64
    have e7 := add_assoc_const sp 0x190#64 56#64 0x1c8#64
    have e8 := add_assoc_const sp 0x190#64 64#64 0x1d0#64
    have e9 := add_assoc_const sp 0x190#64 72#64 0x1d8#64
    have e10 := add_assoc_const sp 0x190#64 80#64 0x1e0#64
    have e11 := add_assoc_const sp 0x190#64 88#64 0x1e8#64
    have e12 := add_assoc_const sp 0x190#64 96#64 0x1f0#64
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12] at h
    exact h
  have h500_reg :
      (((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
       ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
       ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
       ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12)) ⊢
      memRegion (sp + 0x500#64) 96 := by
    have h := cells_12_to_memRegion_96 (sp + 0x500#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    have e1 := add_assoc_const sp 0x500#64 8#64 0x508#64
    have e2 := add_assoc_const sp 0x500#64 16#64 0x510#64
    have e3 := add_assoc_const sp 0x500#64 24#64 0x518#64
    have e4 := add_assoc_const sp 0x500#64 32#64 0x520#64
    have e5 := add_assoc_const sp 0x500#64 40#64 0x528#64
    have e6 := add_assoc_const sp 0x500#64 48#64 0x530#64
    have e7 := add_assoc_const sp 0x500#64 56#64 0x538#64
    have e8 := add_assoc_const sp 0x500#64 64#64 0x540#64
    have e9 := add_assoc_const sp 0x500#64 72#64 0x548#64
    have e10 := add_assoc_const sp 0x500#64 80#64 0x550#64
    have e11 := add_assoc_const sp 0x500#64 88#64 0x558#64
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at h
    exact h
  have hsub1 : BitVec.ofNat 64 (gc₀ :: gcs).length - 1#64 = BitVec.ofNat 64 gcs.length :=
    sub_one_ofNat_succ gcs.length
  have hm_drop :
      s3.mem ⊨
        (dropChainSpecWithStack stk M A lim).pre (⟨sp + 0x190#64, gc₀⟩, st) s3 ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
          memRegion (sp + 0x500#64) 96 ∗
          Frame) ∗ R) := by
    dsimp only [dropChainSpecWithStack]
    rw [hsp3, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_3, hx30_3 ▸ hlr_ls⟩, ?_⟩
    have hpull_drop :
        s3.mem ⊨
          ((((sp + 0x190#64) ↦₆₄ c0) ∗ ((sp + 0x198#64) ↦₆₄ c1) ∗ ((sp + 0x1a0#64) ↦₆₄ c2) ∗
            ((sp + 0x1a8#64) ↦₆₄ c3) ∗ ((sp + 0x1b0#64) ↦₆₄ c4) ∗ ((sp + 0x1b8#64) ↦₆₄ c5) ∗
            ((sp + 0x1c0#64) ↦₆₄ c6) ∗ ((sp + 0x1c8#64) ↦₆₄ c7) ∗ ((sp + 0x1d0#64) ↦₆₄ c8) ∗
            ((sp + 0x1d8#64) ↦₆₄ c9) ∗ ((sp + 0x1e0#64) ↦₆₄ c10) ∗ ((sp + 0x1e8#64) ↦₆₄ c11) ∗
            ((sp + 0x1f0#64) ↦₆₄ c12)) ∗ chainHeap A.repAlloc gc₀) ∗
          (((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
           ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
           ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
           ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12)) ∗
          (A.pool lim st s3 ∗ stackAt sp stk ∗
           ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
             ((sp + 0x48#64) ↦₆₄ (BitVec.ofNat 64 (gc₀ :: gcs).length - 1#64)) ∗
             vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
             Frame) ∗ R)) := by
      refine Satisfies.mono (Entails.of_eq ?_) hm_s3'
      sep_ac_rfl
    rw [← hcells_190, hsub1] at hpull_drop
    have hch := Satisfies.mono
      (sepConj_mono (chainAt_of_bytes A.repAlloc gc₀ (sp + 0x190#64) hpad₀)
        (sepConj_mono_left h500_reg))
      hpull_drop
    refine Satisfies.mono (Entails.of_eq ?_) hch
    sep_ac_rfl
  refine steps_of_call_no_panic hDrop
    hpc3 hrun3 hsp_align3 hx30_3 hm_drop hL3 (by intro _; rfl) (by intros; rfl) (by intro _; rfl) ?_
  intro s4 hpc4 hrun4 hsp4 hsp_align4 hcs4 hL4 hm_s4
  dsimp only [dropChainSpecWithStack] at hm_s4
  rw [hsp3, sepConj_assoc, satisfies_pure_sepConj] at hm_s4
  rcases hm_s4 with ⟨htr4, hm_s4⟩
  have hm_s4_pull :
      s4.mem ⊨
        (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s4) ∗
        (memRegion (sp + 0x190#64) 104 ∗ stackAt sp stk ∗
         ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
           memRegion (sp + 0x500#64) 96 ∗
           Frame) ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm_s4
    sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_s4_pull
  rcases hm_s4_pull with ⟨evs, hm_s4_pull⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_s4_pull
  rcases hm_s4_pull with ⟨hfree, hm_s4_pull⟩
  refine ⟨s4, Steps.refl s4, evs, hfree, hpc4, hrun4, by reg_chain, hsp_align4, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, hL4, ?_⟩
  unfold evictActiveWithStack
  refine Satisfies.mono (Entails.of_eq ?_) hm_s4_pull
  sep_ac_rfl

/-- Full receiver-chain eviction loop (`+0xb04 → +0xb98`) while `6 ≤ gcs.length`, accumulating
`FreeOnlyEvs evs` across iterations with zero `FitsEnv` preconditions. -/
theorem dhCommit_evict_loop_of_wp {prog : Program} {entry : BitVec 64}
    {stk : Nat} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (R Frame : SepProp) (s0 : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (hEvictOne : ∀ (s : State) (st : M.σ) (gc₀ : ChainGhost × ReceiverChain)
      (gcs : List (ChainGhost × ReceiverChain)),
      gcs.length < 2 ^ 32 →
      s.pc = entry + 0xb04#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.trace = s0.trace →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x24 = sp + 0x190#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x27 = 0xffffffffffffff98#64 →
      s.readReg64 .x28 = BitVec.ofNat 64 (gc₀ :: gcs).length →
      prog.CodeLoaded s.mem →
      (s.mem ⊨ evictActiveWithStack stk A lim st s sp chainsCap chainsPtr (gc₀ :: gcs) ∗ (Frame ∗ R)) →
      ∃ sf, Steps prog s sf ∧ ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧
        sf.pc = entry + 0xb8c#64 ∧ sf.status = .Running ∧ sf.sp = sp ∧ sf.spAligned = true ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x24 = sp + 0x190#64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          evictActiveWithStack stk A lim (M.stepEvents evs st) sf sp chainsCap chainsPtr gcs ∗
            (Frame ∗ R)))
    (hwp_4c_hi : CommitStep4cHiVmWp prog entry)
    (hwp_4c_le : CommitStep4cLeVmWp prog entry)
    (gcs : List (ChainGhost × ReceiverChain)) :
    ∀ (s : State) (st : M.σ),
      6 ≤ gcs.length → gcs.length ≤ 2 ^ 32 →
      s.pc = entry + 0xb04#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.trace = s0.trace →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x24 = sp + 0x190#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x27 = 0xffffffffffffff98#64 →
      s.readReg64 .x28 = BitVec.ofNat 64 gcs.length →
      prog.CodeLoaded s.mem →
      (s.mem ⊨ evictActiveWithStack stk A lim st s sp chainsCap chainsPtr gcs ∗ (Frame ∗ R)) →
      ∃ sf, Steps prog s sf ∧ ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧
        sf.pc = entry + 0xb98#64 ∧ sf.status = .Running ∧ sf.sp = sp ∧ sf.spAligned = true ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          evictActiveWithStack stk A lim (M.stepEvents evs st) sf sp chainsCap chainsPtr (evictList gcs) ∗
            (Frame ∗ R)) := by
  induction gcs with
  | nil =>
    intro _ _ hge
    nomatch hge
  | cons gc₀ gcs ih =>
    intro s st hge hle hpc hrun hsp hsp_align htrace hx23 hx24 hx25 hx27 hx28 hL hmem
    rw [evictList_cons_of_ge_six gc₀ gcs hge]
    have hlen_lt : gcs.length < 2 ^ 32 := len_lt_of_cons_le hle
    obtain ⟨s1, hsteps1, evs₁, hfree1, hpc1, hrun1, hsp1, hsp_align1, htr1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx29_1, hvregs_1, hL1, hm1⟩ :=
      hEvictOne s st gc₀ gcs hlen_lt hpc hrun hsp hsp_align htrace hx23 hx24 hx25 hx27 hx28 hL hmem
    set st1 := M.stepEvents evs₁ st
    have hm1_48 :
        s1.mem ⊨ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
          ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
            vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
            memRegion (sp + 0x190#64) 104 ∗
            memRegion (sp + 0x500#64) 96 ∗
            A.pool lim st1 s1 ∗
            stackAt sp stk ∗
            Frame) ∗ R) := by
      unfold evictActiveWithStack at hm1
      refine Satisfies.mono (Entails.of_eq ?_) hm1
      sep_ac_rfl
    suffices ∃ sf, Steps prog s1 sf ∧ ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧
        sf.pc = entry + 0xb98#64 ∧ sf.status = .Running ∧ sf.sp = sp ∧ sf.spAligned = true ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          evictActiveWithStack stk A lim (M.stepEvents evs st) sf sp chainsCap chainsPtr
            (evictList gcs) ∗ (Frame ∗ R)) by
      obtain ⟨sf, hsteps_tail, hpost_tail⟩ := this
      exact ⟨sf, hsteps1.trans hsteps_tail, hpost_tail⟩
    by_cases hge' : 6 ≤ gcs.length
    · have hhi : BitVec.ult 5#64 (BitVec.ofNat 64 gcs.length) = true :=
        ult_five_of_ge_six hge' hlen_lt
      refine steps_of_sepWP
        (hwp_4c_hi sp (BitVec.ofNat 64 gcs.length) s1 hpc1 hrun1 hsp1 hsp_align1 hhi)
        hm1_48 hL1 ?_
      intro s2 P2 hpc2 hrun2 hL2 hm2 hpost2
      rcases hpost2 with ⟨hvm2, hsp2, hsp_align2, htr2, hx19_2, hx20_2, hx21_2, hx22_2,
        hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2, hP2⟩
      have hm2_act :
          s2.mem ⊨ evictActiveWithStack stk A lim st1 s2 sp chainsCap chainsPtr gcs ∗ (Frame ∗ R) := by
        have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
        rw [← A.pool_transport lim st1 s1 s2 hvm2] at hm2'
        unfold evictActiveWithStack
        refine Satisfies.mono (Entails.of_eq ?_) hm2'
        sep_ac_rfl
      obtain ⟨sf, hsteps_ih, evs₂, hfree2, hpc_f, hrun_f, hsp_f, hsp_align_f, htr_f,
        hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx25_f, hx29_f, hvregs_f, hL_f, hm_f⟩ :=
        ih s2 st1 hge' (Nat.le_of_lt hlen_lt) hpc2 hrun2 hsp2 hsp_align2 (by reg_chain)
          (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) hx28_2 hL2 hm2_act
      refine ⟨sf, hsteps_ih, evs₁ ++ evs₂, freeOnlyEvs_append hfree1 hfree2,
        hpc_f, hrun_f, hsp_f, hsp_align_f, htr_f,
        by reg_chain, by reg_chain, by reg_chain, by reg_chain, hx23_f, hx25_f,
        by reg_chain, by reg_chain, hL_f, ?_⟩
      rw [M.stepEvents_append evs₁ evs₂ st]
      exact hm_f
    · have hle5 : gcs.length ≤ 5 := le_five_of_not_ge_six hge'
      have hle_bv : BitVec.ult 5#64 (BitVec.ofNat 64 gcs.length) = false :=
        ult_five_eq_false_of_le_five hle5
      refine steps_of_sepWP
        (hwp_4c_le sp (BitVec.ofNat 64 gcs.length) s1 hpc1 hrun1 hsp1 hsp_align1 hle_bv)
        hm1_48 hL1 ?_
      intro s2 P2 hpc2 hrun2 hL2 hm2 hpost2
      rcases hpost2 with ⟨hvm2, hsp2, hsp_align2, htr2, hx19_2, hx20_2, hx21_2, hx22_2,
        hx23_2, hx25_2, _hx27_2, _hx28_2, hx29_2, hvregs_2, hP2⟩
      rw [evictList_of_le_five gcs hle5]
      have hm2_act :
          s2.mem ⊨ evictActiveWithStack stk A lim st1 s2 sp chainsCap chainsPtr gcs ∗ (Frame ∗ R) := by
        have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
        rw [← A.pool_transport lim st1 s1 s2 hvm2] at hm2'
        unfold evictActiveWithStack
        refine Satisfies.mono (Entails.of_eq ?_) hm2'
        sep_ac_rfl
      exact ⟨s2, Steps.refl s2, evs₁, hfree1, hpc2, hrun2, hsp2, hsp_align2, by reg_chain,
        by reg_chain, by reg_chain, by reg_chain, by reg_chain,
        by reg_chain, by reg_chain, by reg_chain, by reg_chain, hL2, hm2_act⟩

/-- Step 4 (`+0xaf0 → +0xb98`): checks `gcs.length < 6` at `+0xaf0`, skipping or running
`dhCommit_evict_loop_of_wp` to produce `FreeOnlyEvs evs`. -/
theorem dhCommit_step4_of_wp {prog : Program} {entry : BitVec 64}
    {stk : Nat} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (hwp_4a_lo : CommitStep4aLoVmWp prog entry)
    (hwp_4a_ge : CommitStep4aGeVmWp prog entry)
    (hEvictOne : ∀ (s1 : State) (st1 : M.σ) (gc₀ : ChainGhost × ReceiverChain)
      (gcs : List (ChainGhost × ReceiverChain)),
      gcs.length < 2 ^ 32 →
      s1.pc = entry + 0xb04#64 → s1.status = .Running → s1.sp = sp → s1.spAligned = true →
      s1.trace = s0.trace →
      s1.readReg64 .x23 = sp + 0x500#64 → s1.readReg64 .x24 = sp + 0x190#64 →
      s1.readReg64 .x25 = sp + 0x190#64 → s1.readReg64 .x27 = 0xffffffffffffff98#64 →
      s1.readReg64 .x28 = BitVec.ofNat 64 (gc₀ :: gcs).length →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ evictActiveWithStack stk A lim st1 s1 sp chainsCap chainsPtr (gc₀ :: gcs) ∗ (Frame ∗ R)) →
      ∃ sf, Steps prog s1 sf ∧ ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧
        sf.pc = entry + 0xb8c#64 ∧ sf.status = .Running ∧ sf.sp = sp ∧ sf.spAligned = true ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s1.readReg64 .x19 ∧ sf.readReg64 .x20 = s1.readReg64 .x20 ∧
        sf.readReg64 .x21 = s1.readReg64 .x21 ∧ sf.readReg64 .x22 = s1.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x24 = sp + 0x190#64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧
        sf.readReg64 .x29 = s1.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s1 ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          evictActiveWithStack stk A lim (M.stepEvents evs st1) sf sp chainsCap chainsPtr gcs ∗
            (Frame ∗ R)))
    (hwp_4c_hi : CommitStep4cHiVmWp prog entry)
    (hwp_4c_le : CommitStep4cLeVmWp prog entry)
    (gcs : List (ChainGhost × ReceiverChain))
    (hle : gcs.length ≤ 2 ^ 32)
    (hpc : s.pc = entry + 0xaf0#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx23 : s.readReg64 .x23 = sp + 0x500#64) (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨ evictActiveWithStack stk A lim st s sp chainsCap chainsPtr gcs ∗ (Frame ∗ R)) :
    ∃ sf, Steps prog s sf ∧ ∃ evs : List AllocEvent,
      FreeOnlyEvs evs ∧
      sf.pc = entry + 0xb98#64 ∧ sf.status = .Running ∧ sf.sp = sp ∧ sf.spAligned = true ∧
      sf.trace = s0.trace ∧
      sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
      sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
      sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x25 = sp + 0x190#64 ∧
      sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
      prog.CodeLoaded sf.mem ∧
      (sf.mem ⊨
        evictActiveWithStack stk A lim (M.stepEvents evs st) sf sp chainsCap chainsPtr (evictList gcs) ∗
          (Frame ∗ R)) := by
  have hm_48 :
      s.mem ⊨ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
          memRegion (sp + 0x190#64) 104 ∗
          memRegion (sp + 0x500#64) 96 ∗
          A.pool lim st s ∗
          stackAt sp stk ∗
          Frame) ∗ R) := by
    unfold evictActiveWithStack at hmem
    refine Satisfies.mono (Entails.of_eq ?_) hmem
    sep_ac_rfl
  by_cases hlt6 : gcs.length < 6
  · have hlo : BitVec.ult (BitVec.ofNat 64 gcs.length) 6#64 = true :=
      ult_six_of_lt_six hlt6
    refine steps_of_sepWP
      (hwp_4a_lo sp (BitVec.ofNat 64 gcs.length) s hpc hrun hsp hsp_align hlo)
      hm_48 hL ?_
    intro s1 P1 hpc1 hrun1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hvm1, hsp1, hsp_align1, htr1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx25_1, _hx27_1, _hx28_1, hx29_1, hvregs_1, hP1⟩
    rw [evictList_of_le_five gcs (le_five_of_lt_six hlt6)]
    have hm1_act :
        s1.mem ⊨ evictActiveWithStack stk A lim (M.stepEvents [] st) s1 sp chainsCap chainsPtr gcs ∗
          (Frame ∗ R) := by
      have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
      rw [← A.pool_transport lim st s s1 hvm1] at hm1'
      dsimp only [AllocCostModel.stepEvents, List.foldl]
      unfold evictActiveWithStack
      refine Satisfies.mono (Entails.of_eq ?_) hm1'
      sep_ac_rfl
    exact ⟨s1, Steps.refl s1, [], FreeOnlyEvs.nil, hpc1, hrun1, hsp1, hsp_align1, htr1.trans htrace,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1.trans hx23, hx25_1.trans hx25, hx29_1, hvregs_1,
      hL1, hm1_act⟩
  · have hge6 : 6 ≤ gcs.length := ge_six_of_not_lt_six hlt6
    have hge_bv : BitVec.ult (BitVec.ofNat 64 gcs.length) 6#64 = false :=
      ult_six_eq_false_of_not_lt_six hlt6 hle
    refine steps_of_sepWP
      (hwp_4a_ge sp (BitVec.ofNat 64 gcs.length) s hpc hrun hsp hsp_align hx25 hge_bv)
      hm_48 hL ?_
    intro s1 P1 hpc1 hrun1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hvm1, hsp1, hsp_align1, htr1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1, hP1⟩
    have hm1_act :
        s1.mem ⊨ evictActiveWithStack stk A lim st s1 sp chainsCap chainsPtr gcs ∗ (Frame ∗ R) := by
      have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
      rw [← A.pool_transport lim st s s1 hvm1] at hm1'
      unfold evictActiveWithStack
      refine Satisfies.mono (Entails.of_eq ?_) hm1'
      sep_ac_rfl
    obtain ⟨sf, hsteps_loop, evs, hfree, hpc_f, hrun_f, hsp_f, hsp_align_f, htr_f,
      hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx25_f, hx29_f, hvregs_f, hL_f, hm_f⟩ :=
      dhCommit_evict_loop_of_wp A lim R Frame s0 sp chainsCap chainsPtr
        hEvictOne hwp_4c_hi hwp_4c_le gcs
        s1 st hge6 hle hpc1 hrun1 hsp1 hsp_align1 (htr1.trans htrace)
        (hx23_1.trans hx23) hx24_1 hx25_1 hx27_1 hx28_1 hL1 hm1_act
    exact ⟨sf, hsteps_loop, evs, hfree, hpc_f, hrun_f, hsp_f, hsp_align_f, htr_f,
      hx19_f.trans hx19_1, hx20_f.trans hx20_1, hx21_f.trans hx21_1, hx22_f.trans hx22_1,
      hx23_f, hx25_f, hx29_f.trans hx29_1, hvregs_f.trans hvregs_1, hL_f, hm_f⟩

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetStep4
