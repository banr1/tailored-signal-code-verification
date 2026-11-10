/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.FindReceiverChainKeyBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChain
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainStackBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainSym
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Segment S2 (`FindChain`) Proofs

Proves `VmPreserved`-strengthened post-call branch lemmas on block `130` (`+680 → +0x3e4 / +0x500 / +0x30c`)
and discharges `S2SeamPlaced` and `S2SeamXPlaced` (`findChain_placed_ok`, `findChain_placed_ok_x`,
and `blackBoxHook` specializations) over `RustCliAllocBudget M` with zero allocator events.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession
  (ChainKey SessionState SignalProtocolError TripleRatchet)
open CryptoVerification
  (LibsignalPlacement blkPC_25 blkPl_25 lsBlackBoxU8Sym lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSessionRepr (chainKeyBytes msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr
  (invalidSessionStructureStr sessionStateAt speWord strRefAt utf8)
open CryptoVerification.LibsignalTripleRatchet
  (TrGhost TryDecryptGhost findReceiverChainKeyResultAt trAt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (speBodyAt tryDecryptCommonHeap)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
  (SepWP.bind_framed SepWP.rw_pre blkPC_131 blkPl_131 chainKeyBytes_length
   errTailPC_placed exists_word32_of_memRegion_4 exists_word64_of_memRegion_8
   exists_words16_of_length_16 exists_words16_of_memRegion_16
   exists_words20_of_length_20 exists_words20_of_memRegion_20
   exists_words36_of_memRegion_36 findChain_err_speBody_entails
   findChain_err_stack_recombine_0x190 findChain_err_stack_recombine_sp38
   findChain_none_stack_recombine findChain_some_stack_recombine_left
   findChain_some_stack_recombine_right findReceiverChainKeyResultAt_error_eq
   reaches_pc_lsro_preserve realign_20_bytes segConsumeMsgKeyPC_placed
   segDhStepPC_placed sepWP_to_reaches_pc_with_midMeta_placed
   tryDecryptDummyImg tryDecryptEntry_placed tryDecryptMidMeta_placed tryDecryptWPInv)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.ChainKey.FindReceiverChainKeyBudget
  (findReceiverChainKeyPlacedSpec find_receiver_chain_key_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
  (S2SeamPlaced S2SeamXPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
  (ConsumeMsgKeyStatePlaced_of_placed ConsumeMsgKeyState_placed
   DhStepStatePlaced_of_placed DhStepState_placed
   ErrTailStatePlaced_of_placed ErrTailState_placed
   FindChainStatePlaced_to_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainStackBudget
  (findChain_call_findReceiverChainKey_reaches_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget
  (sepWP_blk130_vm)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `VmPreserved`-Strengthened Post-Call Block `130` Step Lemmas (`+680 -> target`) -/

theorem findChain_err_1a_vm_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 d0 : BitVec 64} {w1_lo w1_hi d1_lo d1_hi : BitVec 32} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 680#64) (hmeta : tryDecryptWPInv s0 s) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_131).base + 720#64) s
      (((sp + 0x190#64) ↦₃₂ 2#32) ∗ ((sp + 0x198#64) ↦₆₄ w0) ∗
       ((sp + 0x1a0#64) ↦₃₂ w1_lo) ∗ ((sp + 0x1a4#64) ↦₃₂ w1_hi) ∗
       ((sp + 0x2c0#64) ↦₆₄ d0) ∗ ((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗ ((sp + 0x2cc#64) ↦₃₂ d1_hi))
      (fun sf P =>
        P = (((sp + 0x190#64) ↦₃₂ 2#32) ∗ ((sp + 0x198#64) ↦₆₄ w0) ∗
             ((sp + 0x1a0#64) ↦₃₂ w1_lo) ∗ ((sp + 0x1a4#64) ↦₃₂ w1_hi) ∗
             ((sp + 0x2c0#64) ↦₆₄ w0) ∗ ((sp + 0x2c8#64) ↦₃₂ w1_lo) ∗ ((sp + 0x2cc#64) ↦₃₂ w1_hi)) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 720#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) ?_
  exact ⟨by ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem findChain_err_1b_vm_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 w1 b0 b1 s1 s2 : BitVec 64} {d8c d2d0 s0_w : BitVec 32} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 720#64) (hmeta : tryDecryptWPInv s0 s)
    (hx12 : s.readReg64 .x12 = (s0.sp - 1504#64) + 0x2c0#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_131).base + 756#64) s
      (((sp + 0x18c#64) ↦₃₂ d8c) ∗ ((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1) ∗
       ((sp + 0x2c0#64) ↦₆₄ w0) ∗ ((sp + 0x2c8#64) ↦₆₄ w1) ∗ ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
       ((sp + 0x340#64) ↦₃₂ s0_w) ∗ ((sp + 0x344#64) ↦₆₄ s1) ∗ ((sp + 0x34c#64) ↦₆₄ s2))
      (fun sf P =>
        P = (((sp + 0x18c#64) ↦₃₂ 24#32) ∗ ((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1) ∗
             ((sp + 0x2c0#64) ↦₆₄ w0) ∗ ((sp + 0x2c8#64) ↦₆₄ w1) ∗ ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
             ((sp + 0x340#64) ↦₃₂ d2d0) ∗ ((sp + 0x344#64) ↦₆₄ b0) ∗ ((sp + 0x34c#64) ↦₆₄ b1)) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x26 = speWord 20 ∧
        sf.readVReg128 1#5 = w1 ++ w0) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 756#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) ?_
  exact ⟨by ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm, speWord],
    by simp_all [wp_norm, arm64_norm]⟩

theorem findChain_err_1c_vm_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 w1 u0 u1 c0 c1 g0 g1 g2 g3 : BitVec 64} {u2 g4 : BitVec 32} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 756#64) (hmeta : tryDecryptWPInv s0 s)
    (hx12 : s.readReg64 .x12 = (s0.sp - 1504#64) + 0x2c0#64)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hq1 : s.readVReg128 1#5 = w1 ++ w0) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog errTailPC_placed s
      (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x170#64) ↦₆₄ g1) ∗ ((sp + 0x178#64) ↦₆₄ g2) ∗
       ((sp + 0x180#64) ↦₆₄ g3) ∗ ((sp + 0x188#64) ↦₃₂ g4) ∗ ((sp + 0x330#64) ↦₆₄ c0) ∗
       ((sp + 0x338#64) ↦₆₄ c1) ∗ ((sp + 0x340#64) ↦₆₄ u0) ∗ ((sp + 0x348#64) ↦₆₄ u1) ∗
       ((sp + 0x350#64) ↦₃₂ u2))
      (fun sf P =>
        P = (((sp + 0x168#64) ↦₆₄ w0) ∗ ((sp + 0x170#64) ↦₆₄ w1) ∗ ((sp + 0x178#64) ↦₆₄ u0) ∗
             ((sp + 0x180#64) ↦₆₄ u1) ∗ ((sp + 0x188#64) ↦₃₂ u2) ∗ ((sp + 0x330#64) ↦₆₄ w0) ∗
             ((sp + 0x338#64) ↦₆₄ w1) ∗ ((sp + 0x340#64) ↦₆₄ u0) ∗ ((sp + 0x348#64) ↦₆₄ u1) ∗
             ((sp + 0x350#64) ↦₃₂ u2)) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x26 = s.readReg64 .x26) := by
  dsimp only [errTailPC_placed, tryDecryptEntry_placed]
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 0x30c#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) ?_
  exact ⟨by simp_all [wp_norm, arm64_norm], hvm,
    ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], hs0_align,
      by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

theorem findChain_ok_branch_vm_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {tag : BitVec 32} {s0 s : State}
    (htag : (tag != 2#32) = true)
    (hpc : s.pc = (blkPl_131).base + 680#64) (hmeta : tryDecryptWPInv s0 s) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_131).base + 948#64) s
      ((sp + 0x190#64) ↦₃₂ tag)
      (fun sf P =>
        P = ((sp + 0x190#64) ↦₃₂ tag) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧
        (sf.readReg64 .x9).setWidth 32 = tag ∧
        CalleeSavedPreserved s sf) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 948#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], hs0_align,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, *]

theorem findChain_ok_none_vm_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 : BitVec 32} {w1 w2 w3 w4 d0 d1 : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 948#64) (hmeta : tryDecryptWPInv s0 s)
    (hx9 : (s.readReg64 .x9).setWidth 32 = 0#32)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog segDhStepPC_placed s
      (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4) ∗ ((sp + 0x380#64) ↦₆₄ d0) ∗
       ((sp + 0x388#64) ↦₆₄ d1))
      (fun sf P =>
        P = (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
             ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4) ∗ ((sp + 0x380#64) ↦₆₄ w3) ∗
             ((sp + 0x388#64) ↦₆₄ w4)) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        CalleeSavedPreserved s sf) := by
  dsimp only [segDhStepPC_placed, tryDecryptEntry_placed]
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 0x500#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, *]

theorem findChain_ok_some_vm_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 c0 : BitVec 32} {w1 w2 w3 w4 b0 b1 c1 c2 d0 d1 : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 948#64) (hmeta : tryDecryptWPInv s0 s)
    (hx9 : (s.readReg64 .x9).setWidth 32 = 1#32)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog segConsumeMsgKeyPC_placed s
      (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4) ∗ ((sp + 0x2b0#64) ↦₆₄ b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ b1) ∗ ((sp + 0x2c0#64) ↦₃₂ c0) ∗ ((sp + 0x2c4#64) ↦₆₄ c1) ∗
       ((sp + 0x2cc#64) ↦₆₄ c2) ∗ ((sp + 0x380#64) ↦₆₄ d0) ∗ ((sp + 0x388#64) ↦₆₄ d1))
      (fun sf P =>
        P = (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
             ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4) ∗ ((sp + 0x2b0#64) ↦₆₄ w3) ∗
             ((sp + 0x2b8#64) ↦₆₄ w4) ∗ ((sp + 0x2c0#64) ↦₃₂ w0) ∗ ((sp + 0x2c4#64) ↦₆₄ w1) ∗
             ((sp + 0x2cc#64) ↦₆₄ w2) ∗ ((sp + 0x380#64) ↦₆₄ w3) ∗ ((sp + 0x388#64) ↦₆₄ w4)) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        CalleeSavedPreserved s sf) := by
  dsimp only [segConsumeMsgKeyPC_placed, tryDecryptEntry_placed]
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 0x3e4#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, *]

theorem findChain_err_vm_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 w1 g0 g1 g2 g3 b0 b1 d0 c0 c1 s1 s2 : BitVec 64}
    {g4 d8c d1_lo d1_hi d2d0 s0_w : BitVec 32} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 680#64) (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog errTailPC_placed s
      (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x170#64) ↦₆₄ g1) ∗ ((sp + 0x178#64) ↦₆₄ g2) ∗
       ((sp + 0x180#64) ↦₆₄ g3) ∗ ((sp + 0x188#64) ↦₃₂ g4) ∗ ((sp + 0x18c#64) ↦₃₂ d8c) ∗
       ((sp + 0x190#64) ↦₃₂ 2#32) ∗ ((sp + 0x198#64) ↦₆₄ w0) ∗ ((sp + 0x1a0#64) ↦₆₄ w1) ∗
       ((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1) ∗ ((sp + 0x2c0#64) ↦₆₄ d0) ∗
       ((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗ ((sp + 0x2cc#64) ↦₃₂ d1_hi) ∗ ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
       ((sp + 0x330#64) ↦₆₄ c0) ∗ ((sp + 0x338#64) ↦₆₄ c1) ∗ ((sp + 0x340#64) ↦₃₂ s0_w) ∗
       ((sp + 0x344#64) ↦₆₄ s1) ∗ ((sp + 0x34c#64) ↦₆₄ s2))
      (fun sf P =>
        let u0 := b0.extractLsb' 0 32 ++ d2d0
        let u1 := b1.extractLsb' 0 32 ++ b0.extractLsb' 32 32
        let u2 := b1.extractLsb' 32 32
        P = (((sp + 0x168#64) ↦₆₄ w0) ∗ ((sp + 0x170#64) ↦₆₄ w1) ∗ ((sp + 0x178#64) ↦₆₄ u0) ∗
             ((sp + 0x180#64) ↦₆₄ u1) ∗ ((sp + 0x188#64) ↦₃₂ u2) ∗ ((sp + 0x18c#64) ↦₃₂ 24#32) ∗
             ((sp + 0x190#64) ↦₃₂ 2#32) ∗ ((sp + 0x198#64) ↦₆₄ w0) ∗ ((sp + 0x1a0#64) ↦₆₄ w1) ∗
             ((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1) ∗ ((sp + 0x2c0#64) ↦₆₄ w0) ∗
             ((sp + 0x2c8#64) ↦₆₄ w1) ∗ ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗ ((sp + 0x330#64) ↦₆₄ w0) ∗
             ((sp + 0x338#64) ↦₆₄ w1) ∗ ((sp + 0x340#64) ↦₆₄ u0) ∗ ((sp + 0x348#64) ↦₆₄ u1) ∗
             ((sp + 0x350#64) ↦₃₂ u2)) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x26 = speWord 20) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hsplit_1a0 :
      ((sp + 0x1a0#64) ↦₆₄ w1) =
        ((sp + 0x1a0#64) ↦₃₂ w1.extractLsb' 0 32) ∗ ((sp + 0x1a4#64) ↦₃₂ w1.extractLsb' 32 32) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo64_split32 (sp + 0x1a0#64) w1
  have hsplit_2c8 :
      ((sp + 0x2c8#64) ↦₆₄ w1) =
        ((sp + 0x2c8#64) ↦₃₂ w1.extractLsb' 0 32) ∗ ((sp + 0x2cc#64) ↦₃₂ w1.extractLsb' 32 32) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo64_split32 (sp + 0x2c8#64) w1
  have h1a := findChain_err_1a_vm_wp_placed (H := H)
    (w0 := w0) (w1_lo := w1.extractLsb' 0 32) (w1_hi := w1.extractLsb' 32 32)
    (d0 := d0) (d1_lo := d1_lo) (d1_hi := d1_hi) hpc hmeta
  refine SepWP.rw_pre (by rw [hsplit_1a0]) ?_
  refine SepWP.bind_framed
    (F := ((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x170#64) ↦₆₄ g1) ∗ ((sp + 0x178#64) ↦₆₄ g2) ∗
          ((sp + 0x180#64) ↦₆₄ g3) ∗ ((sp + 0x188#64) ↦₃₂ g4) ∗ ((sp + 0x18c#64) ↦₃₂ d8c) ∗
          ((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1) ∗ ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
          ((sp + 0x330#64) ↦₆₄ c0) ∗ ((sp + 0x338#64) ↦₆₄ c1) ∗ ((sp + 0x340#64) ↦₃₂ s0_w) ∗
          ((sp + 0x344#64) ↦₆₄ s1) ∗ ((sp + 0x34c#64) ↦₆₄ s2))
    h1a (by dsimp only [sp]; sep_ac_rfl) ?_
  intro s1a P1a ⟨hP1a, hvm1a, hmeta1a, hx12_1a, hx19_1a, hx20_1a, hx25_1a⟩ hpc1a
  subst hP1a
  have h1b := findChain_err_1b_vm_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (b0 := b0) (b1 := b1) (s1 := s1) (s2 := s2)
    (d8c := d8c) (d2d0 := d2d0) (s0_w := s0_w) hpc1a hmeta1a hx12_1a (hx25_1a.trans hx25)
  refine SepWP.bind_framed
    (F := ((sp + 0x190#64) ↦₃₂ 2#32) ∗ ((sp + 0x198#64) ↦₆₄ w0) ∗ ((sp + 0x1a0#64) ↦₆₄ w1) ∗
          ((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x170#64) ↦₆₄ g1) ∗ ((sp + 0x178#64) ↦₆₄ g2) ∗
          ((sp + 0x180#64) ↦₆₄ g3) ∗ ((sp + 0x188#64) ↦₃₂ g4) ∗ ((sp + 0x330#64) ↦₆₄ c0) ∗
          ((sp + 0x338#64) ↦₆₄ c1))
    h1b (by rw [hsplit_1a0, hsplit_2c8]; dsimp only [sp]; sep_ac_rfl) ?_
  intro s1b P1b ⟨hP1b, hvm1b, hmeta1b, hx12_1b, hx19_1b, hx20_1b, hx26_1b, hq1_1b⟩ hpc1b
  subst hP1b
  have hrealign :
      (((sp + 0x340#64) ↦₃₂ d2d0) ∗ ((sp + 0x344#64) ↦₆₄ b0) ∗ ((sp + 0x34c#64) ↦₆₄ b1)) =
      (((sp + 0x340#64) ↦₆₄ (b0.extractLsb' 0 32 ++ d2d0)) ∗
       ((sp + 0x348#64) ↦₆₄ (b1.extractLsb' 0 32 ++ b0.extractLsb' 32 32)) ∗
       ((sp + 0x350#64) ↦₃₂ b1.extractLsb' 32 32)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using realign_20_bytes (sp + 0x340#64) d2d0 b0 b1
  have h1c := findChain_err_1c_vm_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (u0 := b0.extractLsb' 0 32 ++ d2d0)
    (u1 := b1.extractLsb' 0 32 ++ b0.extractLsb' 32 32) (u2 := b1.extractLsb' 32 32)
    (c0 := c0) (c1 := c1) (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3) (g4 := g4)
    hpc1b hmeta1b hx12_1b (by reg_chain) hq1_1b
  refine SepWP.bind_framed
    (F := ((sp + 0x18c#64) ↦₃₂ 24#32) ∗ ((sp + 0x190#64) ↦₃₂ 2#32) ∗ ((sp + 0x198#64) ↦₆₄ w0) ∗
          ((sp + 0x1a0#64) ↦₆₄ w1) ∗ ((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1) ∗
          ((sp + 0x2c0#64) ↦₆₄ w0) ∗ ((sp + 0x2c8#64) ↦₆₄ w1) ∗ ((sp + 0x2d0#64) ↦₃₂ d2d0))
    h1c (by rw [← hrealign]; dsimp only [sp]; sep_ac_rfl) ?_
  intro sf Pf ⟨hPf, hvm1c, hmetaf, hx19_f, hx20_f, hx26_f⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1
    ⟨by dsimp only [sp]; sep_ac_rfl, hvm1a.trans (hvm1b.trans hvm1c), hmetaf, by reg_chain⟩

theorem findChain_ok_none_full_vm_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 : BitVec 32} {w1 w2 w3 w4 d0 d1 : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 680#64) (hmeta : tryDecryptWPInv s0 s)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog segDhStepPC_placed s
      (((sp + 0x190#64) ↦₃₂ 0#32) ∗ ((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗
       ((sp + 0x1a0#64) ↦₆₄ w2) ∗ ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4) ∗
       ((sp + 0x380#64) ↦₆₄ d0) ∗ ((sp + 0x388#64) ↦₆₄ d1))
      (fun sf P =>
        P = (((sp + 0x190#64) ↦₃₂ 0#32) ∗ ((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗
             ((sp + 0x1a0#64) ↦₆₄ w2) ∗ ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4) ∗
             ((sp + 0x380#64) ↦₆₄ w3) ∗ ((sp + 0x388#64) ↦₆₄ w4)) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        CalleeSavedPreserved s sf) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hbr := findChain_ok_branch_vm_wp_placed (H := H) (tag := 0#32) (by decide) hpc hmeta
  refine SepWP.bind_framed hbr (by sep_frame) ?_
  intro s1 P1 ⟨hP1, hvm1, hmeta1, hx9_1, hcs1⟩ hpc1
  subst hP1
  have hx25_1 : s1.readReg64 .x25 = sp + 0x190#64 := (hcs1.2.2.2.2.2.2.1).trans hx25
  have hx28_1 : s1.readReg64 .x28 = sp + 0x2c0#64 := (hcs1.2.2.2.2.2.2.2.2.2.1).trans hx28
  have hnone := findChain_ok_none_vm_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (d0 := d0) (d1 := d1)
    hpc1 hmeta1 hx9_1 hx25_1 hx28_1
  refine SepWP.bind_framed hnone (by sep_frame) ?_
  intro sf Pf ⟨hPf, hvm2, hmetaf, hx12_f, hcsf⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨?_, hvm1.trans hvm2, hmetaf, hx12_f, CalleeSavedPreserved.trans hcs1 hcsf⟩
  sep_ac_rfl

theorem findChain_ok_some_full_vm_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 c0 : BitVec 32} {w1 w2 w3 w4 b0 b1 c1 c2 d0 d1 : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 680#64) (hmeta : tryDecryptWPInv s0 s)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog segConsumeMsgKeyPC_placed s
      (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗
       ((sp + 0x1a0#64) ↦₆₄ w2) ∗ ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4) ∗
       ((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1) ∗ ((sp + 0x2c0#64) ↦₃₂ c0) ∗
       ((sp + 0x2c4#64) ↦₆₄ c1) ∗ ((sp + 0x2cc#64) ↦₆₄ c2) ∗ ((sp + 0x380#64) ↦₆₄ d0) ∗
       ((sp + 0x388#64) ↦₆₄ d1))
      (fun sf P =>
        P = (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗
             ((sp + 0x1a0#64) ↦₆₄ w2) ∗ ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4) ∗
             ((sp + 0x2b0#64) ↦₆₄ w3) ∗ ((sp + 0x2b8#64) ↦₆₄ w4) ∗ ((sp + 0x2c0#64) ↦₃₂ w0) ∗
             ((sp + 0x2c4#64) ↦₆₄ w1) ∗ ((sp + 0x2cc#64) ↦₆₄ w2) ∗ ((sp + 0x380#64) ↦₆₄ w3) ∗
             ((sp + 0x388#64) ↦₆₄ w4)) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        CalleeSavedPreserved s sf) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hbr := findChain_ok_branch_vm_wp_placed (H := H) (tag := 1#32) (by decide) hpc hmeta
  refine SepWP.bind_framed hbr (by sep_frame) ?_
  intro s1 P1 ⟨hP1, hvm1, hmeta1, hx9_1, hcs1⟩ hpc1
  subst hP1
  have hx25_1 : s1.readReg64 .x25 = sp + 0x190#64 := (hcs1.2.2.2.2.2.2.1).trans hx25
  have hx28_1 : s1.readReg64 .x28 = sp + 0x2c0#64 := (hcs1.2.2.2.2.2.2.2.2.2.1).trans hx28
  have hsome := findChain_ok_some_vm_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (b0 := b0) (b1 := b1) (c0 := c0) (c1 := c1) (c2 := c2) (d0 := d0) (d1 := d1)
    hpc1 hmeta1 hx9_1 hx25_1 hx28_1
  refine SepWP.bind_framed hsome (by sep_frame) ?_
  intro sf Pf ⟨hPf, hvm2, hmetaf, hx12_f, hcsf⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨?_, hvm1.trans hvm2, hmetaf, hx12_f, CalleeSavedPreserved.trans hcs1 hcsf⟩
  sep_ac_rfl

/-! ## 2. Budget-Threaded Post-Call Branch & `S2SeamPlaced` Theorems (Block `130`) -/

private theorem findChain_err_pre_extract_placed [LibsignalPlacement] {A0 : RustAlloc} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {R : SepProp} {s0 s : State}
    (hm : s.mem ⊨
      sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗
      trAt A0 ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x20 ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 0x190#64) (.error e) ∗
      memRegion ((s0.sp - 1504#64) + 0x1b8#64) 0x3c8 ∗
      tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R) :
    let sp := s0.sp - 1504#64
    let w1 := BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length
    ∃ (p g0 g1 g2 g3 b0 b1 d0 c0 c1 s1 s2 : BitVec 64)
      (g4 d8c d1_lo d1_hi d2d0 s0_w : BitVec 32),
      e = .invalidSessionStructure .missingReceiverChainKey ∧
      s.mem ⊨
        (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x170#64) ↦₆₄ g1) ∗ ((sp + 0x178#64) ↦₆₄ g2) ∗
         ((sp + 0x180#64) ↦₆₄ g3) ∗ ((sp + 0x188#64) ↦₃₂ g4) ∗ ((sp + 0x18c#64) ↦₃₂ d8c) ∗
         ((sp + 0x190#64) ↦₃₂ 2#32) ∗ ((sp + 0x198#64) ↦₆₄ p) ∗ ((sp + 0x1a0#64) ↦₆₄ w1) ∗
         ((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1) ∗ ((sp + 0x2c0#64) ↦₆₄ d0) ∗
         ((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗ ((sp + 0x2cc#64) ↦₃₂ d1_hi) ∗ ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
         ((sp + 0x330#64) ↦₆₄ c0) ∗ ((sp + 0x338#64) ↦₆₄ c1) ∗ ((sp + 0x340#64) ↦₃₂ s0_w) ∗
         ((sp + 0x344#64) ↦₆₄ s1) ∗ ((sp + 0x34c#64) ↦₆₄ s2)) ∗
        ((p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗ memRegion (sp + 0x194#64) 4 ∗
         memRegion (sp + 0x1a8#64) 16 ∗ memRegion (sp + 0x1b8#64) 0xf8 ∗
         memRegion (sp + 0x2d4#64) 0x5c ∗ memRegion (sp + 0x354#64) 0x22c ∗
         sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
         memRegion x.ret 48 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x140#64) 0x28 ∗
         tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hm_frck : s.mem ⊨ findReceiverChainKeyResultAt (sp + 0x190#64) (.error e) ∗
      ((memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ∗
       sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x1b8#64) 0x3c8 ∗
       tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨he, hm_err⟩ := findReceiverChainKeyResultAt_error_eq hm_frck
  subst he
  have hm_sp38 := Satisfies.mono
    (sepConj_mono_right (sepConj_mono_left (findChain_err_stack_recombine_sp38 sp x.locA x.remA x.msg.counter)))
    hm_err
  unfold strRefAt at hm_sp38
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm_sp38
  have hm_ex : s.mem ⊨
      (∃∗ p : BitVec 64,
        ((sp + 0x198#64) ↦₆₄ p) ∗
        ((sp + 0x1a0#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length) ∗
        (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey)) ∗
      (((sp + 0x190#64) ↦₃₂ 2#32) ∗ memRegion (sp + 0x194#64) 4 ∗ memRegion (sp + 0x1a8#64) 16 ∗
       sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0x3c8 ∗ tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm_sp38 using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨p, hm_p⟩
  rw [memRegion_split (sp + 0x140#64) 0x28 0x28 (by decide),
      show (sp + 0x140#64) + BitVec.ofNat 64 0x28 = sp + 0x168#64 by bv_omega,
      memRegion_split (sp + 0x168#64) 16 24 (by decide),
      show (sp + 0x168#64) + 16#64 = sp + 0x178#64 by bv_omega,
      memRegion_split (sp + 0x178#64) 16 8 (by decide),
      show (sp + 0x178#64) + 16#64 = sp + 0x188#64 by bv_omega,
      memRegion_split (sp + 0x188#64) 4 4 (by decide),
      show (sp + 0x188#64) + 4#64 = sp + 0x18c#64 by bv_omega,
      memRegion_split (sp + 0x1b8#64) 0xf8 0x2d0 (by decide),
      show (sp + 0x1b8#64) + BitVec.ofNat 64 0xf8 = sp + 0x2b0#64 by bv_omega,
      memRegion_split (sp + 0x2b0#64) 16 0x2c0 (by decide),
      show (sp + 0x2b0#64) + 16#64 = sp + 0x2c0#64 by bv_omega,
      memRegion_split (sp + 0x2c0#64) 8 0x2b8 (by decide),
      show (sp + 0x2c0#64) + 8#64 = sp + 0x2c8#64 by bv_omega,
      memRegion_split (sp + 0x2c8#64) 4 0x2b4 (by decide),
      show (sp + 0x2c8#64) + 4#64 = sp + 0x2cc#64 by bv_omega,
      memRegion_split (sp + 0x2cc#64) 4 0x2b0 (by decide),
      show (sp + 0x2cc#64) + 4#64 = sp + 0x2d0#64 by bv_omega,
      memRegion_split (sp + 0x2d0#64) 4 0x2ac (by decide),
      show (sp + 0x2d0#64) + 4#64 = sp + 0x2d4#64 by bv_omega,
      memRegion_split (sp + 0x2d4#64) 0x5c 0x250 (by decide),
      show (sp + 0x2d4#64) + BitVec.ofNat 64 0x5c = sp + 0x330#64 by bv_omega,
      memRegion_split (sp + 0x330#64) 16 0x240 (by decide),
      show (sp + 0x330#64) + 16#64 = sp + 0x340#64 by bv_omega,
      memRegion_split (sp + 0x340#64) 20 0x22c (by decide),
      show (sp + 0x340#64) + 20#64 = sp + 0x354#64 by bv_omega] at hm_p
  let w1 := BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length
  let F_err_base :=
    (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗
    ((sp + 0x190#64) ↦₃₂ 2#32) ∗ ((sp + 0x198#64) ↦₆₄ p) ∗ ((sp + 0x1a0#64) ↦₆₄ w1) ∗
    memRegion (sp + 0x194#64) 4 ∗ memRegion (sp + 0x1a8#64) 16 ∗
    memRegion (sp + 0x1b8#64) 0xf8 ∗ memRegion (sp + 0x2d4#64) 0x5c ∗
    memRegion (sp + 0x354#64) 0x22c ∗
    sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x140#64) 0x28 ∗
    tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R
  have hm1 : s.mem ⊨ memRegion (sp + 0x168#64) 16 ∗
      (memRegion (sp + 0x178#64) 16 ∗ memRegion (sp + 0x188#64) 4 ∗ memRegion (sp + 0x18c#64) 4 ∗
       memRegion (sp + 0x2b0#64) 16 ∗ memRegion (sp + 0x2c0#64) 8 ∗ memRegion (sp + 0x2c8#64) 4 ∗
       memRegion (sp + 0x2cc#64) 4 ∗ memRegion (sp + 0x2d0#64) 4 ∗ memRegion (sp + 0x330#64) 16 ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    dsimp only [F_err_base, w1]; convert hm_p using 1; sep_ac_rfl
  obtain ⟨g0, g1, hm2⟩ := exists_words16_of_memRegion_16 hm1
  have hm3 : s.mem ⊨ memRegion (sp + 0x178#64) 16 ∗
      ((((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x188#64) 4 ∗ memRegion (sp + 0x18c#64) 4 ∗ memRegion (sp + 0x2b0#64) 16 ∗
       memRegion (sp + 0x2c0#64) 8 ∗ memRegion (sp + 0x2c8#64) 4 ∗ memRegion (sp + 0x2cc#64) 4 ∗
       memRegion (sp + 0x2d0#64) 4 ∗ memRegion (sp + 0x330#64) 16 ∗ memRegion (sp + 0x340#64) 20 ∗
       F_err_base) := by convert hm2 using 1; sep_ac_rfl
  obtain ⟨g2, g3, hm4⟩ := exists_words16_of_memRegion_16 hm3
  have hm5 : s.mem ⊨ memRegion (sp + 0x188#64) 4 ∗
      ((((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x18c#64) 4 ∗ memRegion (sp + 0x2b0#64) 16 ∗ memRegion (sp + 0x2c0#64) 8 ∗
       memRegion (sp + 0x2c8#64) 4 ∗ memRegion (sp + 0x2cc#64) 4 ∗ memRegion (sp + 0x2d0#64) 4 ∗
       memRegion (sp + 0x330#64) 16 ∗ memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨g4, hm6⟩ := exists_word32_of_memRegion_4 hm5
  have hm7 : s.mem ⊨ memRegion (sp + 0x18c#64) 4 ∗
      (((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x2b0#64) 16 ∗ memRegion (sp + 0x2c0#64) 8 ∗ memRegion (sp + 0x2c8#64) 4 ∗
       memRegion (sp + 0x2cc#64) 4 ∗ memRegion (sp + 0x2d0#64) 4 ∗ memRegion (sp + 0x330#64) 16 ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by convert hm6 using 1; sep_ac_rfl
  obtain ⟨d8c, hm8⟩ := exists_word32_of_memRegion_4 hm7
  have hm9 : s.mem ⊨ memRegion (sp + 0x2b0#64) 16 ∗
      (((sp + 0x18c#64) ↦₃₂ d8c) ∗ ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x2c0#64) 8 ∗ memRegion (sp + 0x2c8#64) 4 ∗ memRegion (sp + 0x2cc#64) 4 ∗
       memRegion (sp + 0x2d0#64) 4 ∗ memRegion (sp + 0x330#64) 16 ∗ memRegion (sp + 0x340#64) 20 ∗
       F_err_base) := by convert hm8 using 1; sep_ac_rfl
  obtain ⟨b0, b1, hm10⟩ := exists_words16_of_memRegion_16 hm9
  have hm11 : s.mem ⊨ memRegion (sp + 0x2c0#64) 8 ∗
      ((((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b0#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗ ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x2c8#64) 4 ∗ memRegion (sp + 0x2cc#64) 4 ∗ memRegion (sp + 0x2d0#64) 4 ∗
       memRegion (sp + 0x330#64) 16 ∗ memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    convert hm10 using 1; sep_ac_rfl
  obtain ⟨d0, hm12⟩ := exists_word64_of_memRegion_8 hm11
  have hm13 : s.mem ⊨ memRegion (sp + 0x2c8#64) 4 ∗
      (((sp + 0x2c0#64) ↦₆₄ d0) ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b0#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗ ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x2cc#64) 4 ∗ memRegion (sp + 0x2d0#64) 4 ∗ memRegion (sp + 0x330#64) 16 ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by convert hm12 using 1; sep_ac_rfl
  obtain ⟨d1_lo, hm14⟩ := exists_word32_of_memRegion_4 hm13
  have hm15 : s.mem ⊨ memRegion (sp + 0x2cc#64) 4 ∗
      (((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗ ((sp + 0x2c0#64) ↦₆₄ d0) ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b0#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗ ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x2d0#64) 4 ∗ memRegion (sp + 0x330#64) 16 ∗ memRegion (sp + 0x340#64) 20 ∗
       F_err_base) := by convert hm14 using 1; sep_ac_rfl
  obtain ⟨d1_hi, hm16⟩ := exists_word32_of_memRegion_4 hm15
  have hm17 : s.mem ⊨ memRegion (sp + 0x2d0#64) 4 ∗
      (((sp + 0x2cc#64) ↦₃₂ d1_hi) ∗ ((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗ ((sp + 0x2c0#64) ↦₆₄ d0) ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b0#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗ ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x330#64) 16 ∗ memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    convert hm16 using 1; sep_ac_rfl
  obtain ⟨d2d0, hm18⟩ := exists_word32_of_memRegion_4 hm17
  have hm19 : s.mem ⊨ memRegion (sp + 0x330#64) 16 ∗
      (((sp + 0x2d0#64) ↦₃₂ d2d0) ∗ ((sp + 0x2cc#64) ↦₃₂ d1_hi) ∗ ((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗
       ((sp + 0x2c0#64) ↦₆₄ d0) ∗ (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b0#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗ ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by convert hm18 using 1; sep_ac_rfl
  obtain ⟨c0, c1, hm20⟩ := exists_words16_of_memRegion_16 hm19
  have hm21 : s.mem ⊨ memRegion (sp + 0x340#64) 20 ∗
      ((((sp + 0x330#64) ↦₆₄ c0) ∗ ((sp + 0x330#64 + 8#64) ↦₆₄ c1)) ∗
       ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗ ((sp + 0x2cc#64) ↦₃₂ d1_hi) ∗ ((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗
       ((sp + 0x2c0#64) ↦₆₄ d0) ∗ (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b0#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗ ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗ F_err_base) := by
    convert hm20 using 1; sep_ac_rfl
  obtain ⟨s0_w, s1, s2, hm22⟩ := exists_words20_of_memRegion_20 hm21
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm22
  refine ⟨p, g0, g1, g2, g3, b0, b1, d0, c0, c1, s1, s2, g4, d8c, d1_lo, d1_hi, d2d0, s0_w, rfl, ?_⟩
  dsimp only [F_err_base, w1, sp] at hm22 ⊢; convert hm22 using 1; sep_ac_rfl

theorem findChain_after_call_ok_none_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ctl : BitVec 64} {H : String → Option (State → State)}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 680#64)
    (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64)
    (hm : s.mem ⊨
      sessionStateAt (A.atState lim st s) x.ss x.G.afterTrFrom st1 ∗
      trAt (A.atState lim st s) ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x20 ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 0x190#64) (.ok none) ∗
      memRegion ((s0.sp - 1504#64) + 0x1b8#64) 0x3c8 ∗
      tryDecryptCommonHeap (A.atState lim st s) ctl tryDecryptDummyImg x 0 s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segDhStepPC_placed s
      (DhStepState_placed A lim st ctl x trG tr st1 R s0) := by
  let sp := s0.sp - 1504#64
  let A0 : RustAlloc := A.atState lim st s
  change s.mem ⊨
    sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    (((sp + 0x190#64) ↦₃₂ 0#32) ∗ memRegion (sp + 0x190#64 + 4#64) 36) ∗
    memRegion (sp + 0x1b8#64) 0x3c8 ∗ tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R at hm
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_omega,
      memRegion_split (sp + 0x1b8#64) 0x1c8 0x200 (by decide),
      show (sp + 0x1b8#64) + BitVec.ofNat 64 0x1c8 = sp + 0x380#64 by bv_omega,
      memRegion_split (sp + 0x380#64) 16 0x1f0 (by decide),
      show (sp + 0x380#64) + 16#64 = sp + 0x390#64 by bv_omega] at hm
  have hm1 : s.mem ⊨ memRegion (sp + 0x194#64) 36 ∗
      (memRegion (sp + 0x380#64) 16 ∗ ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0x1c8 ∗ memRegion (sp + 0x390#64) 0x1f0 ∗
       tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, hm2⟩ := exists_words36_of_memRegion_36 hm1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm2
  have hm3 : s.mem ⊨ memRegion (sp + 0x380#64) 16 ∗
      ((((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
        ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗ sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗
       trAt A0 (sp + 0x38#64) trG tr ∗ memRegion x.ret 48 ∗ memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x1b8#64) 0x1c8 ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨d0, d1, hm4⟩ := exists_words16_of_memRegion_16 hm3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm4
  let F_none :=
    sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1b8#64) 0x1c8 ∗ memRegion (sp + 0x390#64) 0x1f0 ∗
    tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 0x190#64) ↦₃₂ 0#32) ∗ ((sp + 0x194#64) ↦₃₂ w0) ∗
       ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4) ∗
       ((sp + 0x380#64) ↦₆₄ d0) ∗ ((sp + 0x388#64) ↦₆₄ d1)) ∗ F_none := by
    dsimp only [F_none]; convert hm4 using 1; sep_ac_rfl
  have hwp := findChain_ok_none_full_vm_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (d0 := d0) (d1 := d1)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx25 hx28
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨hPf, hvm_f, hwpInv_f, hx12_f, hcs⟩ hinv_f hmf
  subst hPf
  have hAf : A.atState lim st sf = A0 := A.atState_eq_of_vmPreserved lim st hvm_f
  dsimp only [DhStepState_placed,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.DhStepState_placed]
  rw [hAf]
  refine ⟨hpcf, hwpInv_f.to_midMeta_placed hinv_f, hx12_f,
    (hcs.1).trans hx19, (hcs.2.1).trans hx20, (hcs.2.2.1).trans hx21,
    (hcs.2.2.2.1).trans hx22, (hcs.2.2.2.2.1).trans hx23,
    by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hcs.2.2.2.2.2.1]; exact hx24,
    (hcs.2.2.2.2.2.2.1).trans hx25, (hcs.2.2.2.2.2.2.2.2.1).trans hx27,
    (hcs.2.2.2.2.2.2.2.2.2.1).trans hx28, ?_⟩
  have hmf_re : sf.mem ⊨
      (memRegion (sp + 0x140#64) 0x50 ∗ ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗
        ((sp + 0x1a0#64) ↦₆₄ w2) ∗ ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       memRegion (sp + 0x1b8#64) 0x1c8 ∗
       (((sp + 0x380#64) ↦₆₄ w3) ∗ ((sp + 0x388#64) ↦₆₄ w4)) ∗
       memRegion (sp + 0x390#64) 0x1f0) ∗
      (sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    dsimp only [F_none, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono (sepConj_mono_left (findChain_none_stack_recombine sp w0 w1 w2 w3 w4)) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

theorem findChain_after_call_ok_some_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ctl : BitVec 64} {H : String → Option (State → State)}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 680#64)
    (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64)
    (hm : s.mem ⊨
      sessionStateAt (A.atState lim st s) x.ss x.G.afterTrFrom st1 ∗
      trAt (A.atState lim st s) ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x20 ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 0x190#64) (.ok (some ck)) ∗
      memRegion ((s0.sp - 1504#64) + 0x1b8#64) 0x3c8 ∗
      tryDecryptCommonHeap (A.atState lim st s) ctl tryDecryptDummyImg x 0 s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segConsumeMsgKeyPC_placed s
      (ConsumeMsgKeyState_placed A lim st ctl x trG tr st1 ck 0 R s0) := by
  let sp := s0.sp - 1504#64
  let A0 : RustAlloc := A.atState lim st s
  have htake_len : ((chainKeyBytes ck).take 20).length = 20 := by
    rw [List.length_take_of_le (by rw [chainKeyBytes_length]; decide)]
  have hdrop_len : ((chainKeyBytes ck).drop 20).length = 16 := by
    rw [List.length_drop, chainKeyBytes_length]
  obtain ⟨w0, w1, w2, hw20⟩ := exists_words20_of_length_20 htake_len
  obtain ⟨w3, w4, hw16⟩ := exists_words16_of_length_16 hdrop_len
  have hck_split :
      ((sp + 0x190#64 + 4#64) ↦ₛ chainKeyBytes ck) =
        (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2)) ∗
        (((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) := by
    rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_omega,
        ← List.take_append_drop 20 (chainKeyBytes ck), pointsToBytes_append, htake_len,
        show (sp + 0x194#64) + BitVec.ofNat 64 20 = sp + 0x1a8#64 by bv_omega,
        hw20 (sp + 0x194#64), hw16 (sp + 0x1a8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  change s.mem ⊨
    sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x190#64 + 4#64) ↦ₛ chainKeyBytes ck)) ∗
    memRegion (sp + 0x1b8#64) 0x3c8 ∗ tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R at hm
  rw [hck_split,
      memRegion_split (sp + 0x1b8#64) 0xf8 0x2d0 (by decide),
      show (sp + 0x1b8#64) + BitVec.ofNat 64 0xf8 = sp + 0x2b0#64 by bv_omega,
      memRegion_split (sp + 0x2b0#64) 16 0x2c0 (by decide),
      show (sp + 0x2b0#64) + 16#64 = sp + 0x2c0#64 by bv_omega,
      memRegion_split (sp + 0x2c0#64) 20 0x2ac (by decide),
      show (sp + 0x2c0#64) + 20#64 = sp + 0x2d4#64 by bv_omega,
      memRegion_split (sp + 0x2d4#64) 0xac 0x200 (by decide),
      show (sp + 0x2d4#64) + BitVec.ofNat 64 0xac = sp + 0x380#64 by bv_omega,
      memRegion_split (sp + 0x380#64) 16 0x1f0 (by decide),
      show (sp + 0x380#64) + 16#64 = sp + 0x390#64 by bv_omega] at hm
  have hm1 : s.mem ⊨ memRegion (sp + 0x2b0#64) 16 ∗
      (memRegion (sp + 0x2c0#64) 20 ∗ memRegion (sp + 0x380#64) 16 ∗ ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2)) ∗
       (((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0xf8 ∗ memRegion (sp + 0x2d4#64) 0xac ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨b0, b1, hm2⟩ := exists_words16_of_memRegion_16 hm1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm2
  have hm3 : s.mem ⊨ memRegion (sp + 0x2c0#64) 20 ∗
      ((((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1)) ∗
       memRegion (sp + 0x380#64) 16 ∗ ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2)) ∗
       (((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0xf8 ∗ memRegion (sp + 0x2d4#64) 0xac ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨c0, c1, c2, hm4⟩ := exists_words20_of_memRegion_20 hm3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm4
  have hm5 : s.mem ⊨ memRegion (sp + 0x380#64) 16 ∗
      ((((sp + 0x2c0#64) ↦₃₂ c0) ∗ ((sp + 0x2c4#64) ↦₆₄ c1) ∗ ((sp + 0x2cc#64) ↦₆₄ c2)) ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1)) ∗
       ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2)) ∗
       (((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0xf8 ∗ memRegion (sp + 0x2d4#64) 0xac ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨d0, d1, hm6⟩ := exists_words16_of_memRegion_16 hm5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm6
  let F_some :=
    sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1b8#64) 0xf8 ∗ memRegion (sp + 0x2d4#64) 0xac ∗
    memRegion (sp + 0x390#64) 0x1f0 ∗ tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x194#64) ↦₃₂ w0) ∗
       ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4) ∗
       ((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1) ∗
       ((sp + 0x2c0#64) ↦₃₂ c0) ∗ ((sp + 0x2c4#64) ↦₆₄ c1) ∗
       ((sp + 0x2cc#64) ↦₆₄ c2) ∗ ((sp + 0x380#64) ↦₆₄ d0) ∗
       ((sp + 0x388#64) ↦₆₄ d1)) ∗ F_some := by
    dsimp only [F_some]; convert hm6 using 1; sep_ac_rfl
  have hwp := findChain_ok_some_full_vm_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (b0 := b0) (b1 := b1) (c0 := c0) (c1 := c1) (c2 := c2) (d0 := d0) (d1 := d1)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx25 hx28
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨hPf, hvm_f, hwpInv_f, hx12_f, hcs⟩ hinv_f hmf
  subst hPf
  have hAf : A.atState lim st sf = A0 := A.atState_eq_of_vmPreserved lim st hvm_f
  dsimp only [ConsumeMsgKeyState_placed,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.ConsumeMsgKeyState_placed]
  rw [hAf]
  refine ⟨hpcf, hwpInv_f.to_midMeta_placed hinv_f, hx12_f,
    (hcs.1).trans hx19, (hcs.2.1).trans hx20, (hcs.2.2.1).trans hx21,
    (hcs.2.2.2.1).trans hx22, (hcs.2.2.2.2.1).trans hx23,
    by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hcs.2.2.2.2.2.1]; exact hx24,
    (hcs.2.2.2.2.2.2.1).trans hx25, ?_⟩
  have h2b0 : (((sp + 0x2b0#64) ↦₆₄ w3) ∗ ((sp + 0x2b8#64) ↦₆₄ w4)) =
      ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes ck).drop 20) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using (hw16 (sp + 0x2b0#64)).symm
  have h2c0 : (((sp + 0x2c0#64) ↦₃₂ w0) ∗ ((sp + 0x2c4#64) ↦₆₄ w1) ∗ ((sp + 0x2cc#64) ↦₆₄ w2)) =
      ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes ck).take 20) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using (hw20 (sp + 0x2c0#64)).symm
  have hmf_re : sf.mem ⊨
      (memRegion (sp + 0x140#64) 0x50 ∗ ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
        ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       memRegion (sp + 0x1b8#64) 0xf8) ∗
      (memRegion (sp + 0x2d4#64) 0xac ∗
       (((sp + 0x380#64) ↦₆₄ w3) ∗ ((sp + 0x388#64) ↦₆₄ w4)) ∗
       memRegion (sp + 0x390#64) 0x1f0) ∗
      (((sp + 0x2b0#64) ↦₆₄ w3) ∗ ((sp + 0x2b8#64) ↦₆₄ w4)) ∗
      (((sp + 0x2c0#64) ↦₃₂ w0) ∗ ((sp + 0x2c4#64) ↦₆₄ w1) ∗ ((sp + 0x2cc#64) ↦₆₄ w2)) ∗
      (sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    dsimp only [F_some, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  rw [h2b0, h2c0] at hmf_re
  have hmf2 := Satisfies.mono
    (sepConj_mono (findChain_some_stack_recombine_left sp w0 w1 w2 w3 w4)
      (sepConj_mono_left (findChain_some_stack_recombine_right sp w3 w4))) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

theorem findChain_after_call_error_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ctl : BitVec 64} {H : String → Option (State → State)}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 680#64)
    (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hm : s.mem ⊨
      sessionStateAt (A.atState lim st s) x.ss x.G.afterTrFrom st1 ∗
      trAt (A.atState lim st s) ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x20 ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 0x190#64) (.error e) ∗
      memRegion ((s0.sp - 1504#64) + 0x1b8#64) 0x3c8 ∗
      tryDecryptCommonHeap (A.atState lim st s) ctl tryDecryptDummyImg x 0 s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) errTailPC_placed s
      (ErrTailState_placed A lim st ctl x trG tr st1 e 0 R s0) := by
  let sp := s0.sp - 1504#64
  let A0 : RustAlloc := A.atState lim st s
  let w1 := BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length
  obtain ⟨p, g0, g1, g2, g3, b0, b1, d0, c0, c1, s1, s2, g4, d8c, d1_lo, d1_hi, d2d0, s0_w, he, hm_pre⟩ :=
    findChain_err_pre_extract_placed (A0 := A0) hm
  subst he
  have hwp := findChain_err_vm_wp_placed (H := H)
    (w0 := p) (w1 := w1) (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3)
    (b0 := b0) (b1 := b1) (d0 := d0) (c0 := c0) (c1 := c1) (s1 := s1) (s2 := s2)
    (g4 := g4) (d8c := d8c) (d1_lo := d1_lo) (d1_hi := d1_hi) (d2d0 := d2d0) (s0_w := s0_w)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx20 hx25
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨hPf, hvm_f, hwpInv_f, hx19_f, hx20_f, hx26_f⟩ hinv_f hmf
  subst hPf
  have hAf : A.atState lim st sf = A0 := A.atState_eq_of_vmPreserved lim st hvm_f
  dsimp only [ErrTailState_placed,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.ErrTailState_placed]
  rw [hAf]
  refine ⟨hpcf, hwpInv_f.to_midMeta_placed hinv_f, hx19_f.trans hx19, hx20_f.trans hx20, hx26_f, ?_⟩
  let u0 := b0.extractLsb' 0 32 ++ d2d0
  let u1 := b1.extractLsb' 0 32 ++ b0.extractLsb' 32 32
  let u2 := b1.extractLsb' 32 32
  have hmf_re : sf.mem ⊨
      (((sp + 0x168#64) ↦₆₄ p) ∗ ((sp + 0x170#64) ↦₆₄ w1) ∗
       (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗ ((sp + 0x178#64) ↦₆₄ u0) ∗
       ((sp + 0x180#64) ↦₆₄ u1) ∗ ((sp + 0x188#64) ↦₃₂ u2) ∗ ((sp + 0x18c#64) ↦₃₂ 24#32)) ∗
      (((sp + 0x190#64) ↦₃₂ 2#32) ∗ memRegion (sp + 0x194#64) 4 ∗
       (((sp + 0x198#64) ↦₆₄ p) ∗ ((sp + 0x1a0#64) ↦₆₄ w1)) ∗
       memRegion (sp + 0x1a8#64) 16 ∗ memRegion (sp + 0x1b8#64) 0xf8 ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1)) ∗
       (((sp + 0x2c0#64) ↦₆₄ p) ∗ ((sp + 0x2c8#64) ↦₆₄ w1)) ∗
       ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗ memRegion (sp + 0x2d4#64) 0x5c ∗
       (((sp + 0x330#64) ↦₆₄ p) ∗ ((sp + 0x338#64) ↦₆₄ w1)) ∗
       (((sp + 0x340#64) ↦₆₄ u0) ∗ ((sp + 0x348#64) ↦₆₄ u1)) ∗
       ((sp + 0x350#64) ↦₃₂ u2) ∗ memRegion (sp + 0x354#64) 0x22c) ∗
      (sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ trAt A0 (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x140#64) 0x28 ∗
       tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    dsimp only [u0, u1, u2, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (findChain_err_speBody_entails A0 sp p u0 u1 u2)
      (sepConj_mono_left (findChain_err_stack_recombine_0x190 sp p w1 b0 b1 u0 u1 d2d0 u2))) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

/-- Budget-threaded relocatable `[LibsignalPlacement]` `S2` segment verification (`S2SeamPlaced`,
Block `130`), parameterized by the Block-`25` `findReceiverChainKeyPlacedSpec A` contract. -/
theorem findChain_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    (hfrck : subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedSpec A))) :
    S2SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base A lim ctl := by
  intro x st trG tr st1 R s0 s hs2P _hcode
  obtain ⟨hs2, hro⟩ := FindChainStatePlaced_to_placed hs2P
  have hcall := reaches_pc_lsro_preserve hro
    (findChain_call_findReceiverChainKey_reaches_placed hfrck x trG tr st1 R s0 s hs2 hro)
  cases hres : tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
  | ok optCk =>
    cases optCk with
    | some ck =>
      rw [hres] at hcall
      refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, _, hx28_ret, hm_ret⟩, hro_ret⟩ => ?_)
      refine reaches_pc_mono (reaches_pc_lsro_preserve hro_ret
        (findChain_after_call_ok_some_placed hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hx28_ret hm_ret)) ?_
      intro sf _ _ ⟨hS, hro_f⟩
      exact ConsumeMsgKeyStatePlaced_of_placed hS hro_f
    | none =>
      rw [hres] at hcall
      refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hx27_ret, hx28_ret, hm_ret⟩, hro_ret⟩ => ?_)
      refine reaches_pc_mono (reaches_pc_lsro_preserve hro_ret
        (findChain_after_call_ok_none_placed hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hx27_ret hx28_ret hm_ret)) ?_
      intro sf _ _ ⟨hS, hro_f⟩
      exact DhStepStatePlaced_of_placed hS hro_f
  | error e =>
    rw [hres] at hcall
    refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨⟨hmeta_ret, hx19_ret, hx20_ret, _, _, _, _, hx25_ret, _, _, hm_ret⟩, hro_ret⟩ => ?_)
    refine reaches_pc_mono (reaches_pc_lsro_preserve hro_ret
      (findChain_after_call_error_placed hpc_ret hmeta_ret hx19_ret hx20_ret hx25_ret hm_ret)) ?_
    intro sf _ _ ⟨hS, hro_f⟩
    exact ErrTailStatePlaced_of_placed hS hro_f

/-- `decFn`-parametric alias (`S2SeamXPlaced = @S2SeamPlaced`) of `findChain_placed_ok`. -/
theorem findChain_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    (hfrck : subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedSpec A))) :
    S2SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base A lim ctl :=
  findChain_placed_ok hfrck

/-- Unconditional hook-table specialization of `findChain_placed_ok` from `blackBoxHook`. -/
theorem findChain_placed_ok_of_bb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    S2SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base A lim ctl :=
  findChain_placed_ok (find_receiver_chain_key_placed_ok h_bb)

/-- Unconditional hook-table specialization of `findChain_placed_ok_x` from `blackBoxHook`. -/
theorem findChain_placed_ok_of_bb_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    S2SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base A lim ctl :=
  findChain_placed_ok_of_bb h_bb

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainBudget
