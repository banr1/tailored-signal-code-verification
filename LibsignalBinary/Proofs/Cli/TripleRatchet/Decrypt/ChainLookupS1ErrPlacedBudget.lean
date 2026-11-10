/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupErrSymPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS1ErrPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Segment `S1` and `ErrTail` on Block `433`

Proves the budget-threaded relocatable `S1` (`LoadRatchet`, pinned and unpinned) and `ErrTail`
seam contracts under `RustCliAllocBudget M` for `try_decrypt_with_state::<Coins>` (block `433`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS1ErrPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto Mut SessionState SignalProtocolError TripleRatchet)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded blkPC_57 blkPl_57
  lsLogFilterAddr lsRustDeallocSym lsmpl ls_subroutine_ok_of_block
)
open CryptoVerification.RustHeap (RustAlloc arrayAt)
open CryptoVerification.LibsignalSessionRepr (chainAt msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost UuidParser decryptDraws errTag invalidMessageStrAt
  protocolAddressAt sessionStateAt signalMessageAt speAt utf8 uuidTryParse vecResultAt
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TrFromGhost TrGhost TryDecryptGhost trAt trFromStack trResultAt
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet (withLsRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkLib_eq_434 blkPC_434 blkPl_434 retEpiloguePC_at segFindChainPC_at segLoadRatchetPC_at
  speBodyAt speTag tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (
  SepWP.bind_framed SepWP.rw_pre
  decRel_afterTrFrom errTail_stack_recombine
  exists_words3_of_memRegion_24 exists_words5_of_speBodyAt exists_words6_of_memRegion_48
  fromSessionState_error_imp
  loadRatchet_err_stack_recombine loadRatchet_ok_stack_recombine
  reaches_pc_call_lscl reaches_pc_lsro reaches_pc_seq_lscl
  sepWP_to_reaches_pc sepWP_to_reaches_pc_midMeta_placed sepWP_to_reaches_pc_with_midMeta_placed
  signalMessageAt_eq_counter_rest signalMessageNoCounterAt speAt_eq_speTag_speBodyAt
  stackAt_tryDecryptSubStack_sub trAt_eq_cap_body_heap trAt_expose_errTail
  trBodyAt trHeapAt trHeapAt_facts tryDecryptMidMeta_placed tryDecryptWPInv
  words4At words5At words8At words32At words32At_40_eq words32At_198_eq
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.ChainLookupFacts (
  elim_exists_words32_of_trBodyAt elim_s1_ok_stack_extract
)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup (
  tryDecryptMidMetaPlaced_of_placed tryDecryptMidMetaPlaced_to_placed
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
  VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget (
  chainAt_atState_fn invalidMessageStrAt_atState live_atState
  protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState
  vecResultAt_atState vecU8_atState
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget (
  signalMessageNoCounterAt_atState trAt_atState trResultAt_atState
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (s1InitCaps trGhostCaps)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget (
  trFromPlacedSpec trFromRawPlacedSpec
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  ErrTailStatePlaced ErrTailTightSeamPlaced FindChainStatePlaced LoadRatchetStatePlaced
  cliTryDecryptCommonHeapPlaced cliTryDecryptSpecPlaced cliTryDecryptTightSpecPlaced
  reaches_outcome_weaken_tight_placed
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupErrSymPlacedBudget (
  errTail_all_steps_433_wp_placed reaches_epilogue_to_outcome_tight_seam_433_placed
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Pure Segment `VmPreserved` Lift and `LoadRatchet` Symbolic Steps -/

private theorem sepWP_blk433_vm [LibsignalPlacement] {H : String → Option (State → State)}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_434).rebase (blkPl_434).base (hooksException H))
        mid (s.setMem m_strip) Pre (fun sm' Pm =>
          ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            SepWP ((blkPC_434).rebase (blkPl_434).base H) target (sm'.setMem m_real) Pm post)) :
    SepWP ((blkPC_434).rebase (blkPl_434).base H) target s Pre post :=
  sepWP_seg_ls_vm
    (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
    blkLib_eq_434 (mid := mid) (hseg := hseg)

theorem loadRatchet_bl_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {s0 s : State}
    (hpc : s.pc = segLoadRatchetPC_at (blkPl_434).base)
    (hmeta : tryDecryptWPInv s0 s) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 57) s emp
      (fun s1 P1 =>
        P1 = emp ∧
        VmPreserved s s1 ∧
        tryDecryptWPInv s0 s1 ∧
        s1.readReg64 Reg.lr = (blkPl_434).base + 484#64 ∧
        s1.readReg64 .x0 = s.readReg64 .x21 ∧
        (s1.readReg64 .x1).setWidth 32 = (s.readReg64 .x1).setWidth 32 ∧
        s1.readReg64 .x8 = sp + 400#64 ∧
        CalleeSavedPreserved s s1) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [segLoadRatchetPC_at] at hpc
  apply sepWP_blk433_vm (mid := lsmpl.base 57)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨rfl, hvm,
    ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], hs0_align,
      by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, *]

theorem loadRatchet_err_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {ret tag w0 w1 w2 w3 w4 t0 t1 t2 t3 t4 t5 r0 r1 r2 r3 r4 r5 : BitVec 64}
    {s0 s : State}
    (hpc : s.pc = (blkPl_434).base + 484#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64) :
    let prog := (blkPC_434).rebase (blkPl_434).base H
    let sp := s0.sp - 1504#64
    SepWP prog (retEpiloguePC_at (blkPl_434).base) s
      (((sp + 400#64) ↦₆₄ errTag) ∗
       ((sp + 408#64) ↦₆₄ tag) ∗
       words5At (sp + 416#64) w0 w1 w2 w3 w4 ∗
       ((sp + 1280#64) ↦₆₄ t0) ∗
       words5At (sp + 1288#64) t1 t2 t3 t4 t5 ∗
       (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5)
      (fun sf P =>
        P = (((sp + 400#64) ↦₆₄ errTag) ∗
             ((sp + 408#64) ↦₆₄ tag) ∗
             words5At (sp + 416#64) w0 w1 w2 w3 w4 ∗
             ((sp + 1280#64) ↦₆₄ tag) ∗
             words5At (sp + 1288#64) w0 w1 w2 w3 w4 ∗
             (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  apply sepWP_blk433_vm (mid := retEpiloguePC_at (blkPl_434).base)
  intro _m_strip
  dsimp only [retEpiloguePC_at]
  unfold words5At errTag
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  exact ⟨by sep_ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩⟩

theorem loadRatchet_ok_1a_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {cap locA g20 w0 w1 w2 w3 w4 w5 t0 t1 t2 t3 t4 t5 : BitVec 64} {s0 s : State}
    (hcap : cap + 1#64 ≠ 0#64) (hpc : s.pc = (blkPl_434).base + 484#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx25 : s.readReg64 .x25 = locA) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_434).rebase (blkPl_434).base H) ((blkPl_434).base + 528#64) s
      (((sp + 32#64) ↦₆₄ g20) ∗ ((sp + 400#64) ↦₆₄ cap) ∗ words4At (sp + 408#64) w0 w1 w2 w3 ∗
       ((sp + 440#64) ↦₆₄ w4) ∗ ((sp + 448#64) ↦₆₄ w5) ∗ words4At (sp + 1280#64) t0 t1 t2 t3 ∗
       ((sp + 1312#64) ↦₆₄ t4) ∗ ((sp + 1320#64) ↦₆₄ t5))
      (fun sf P =>
        P = (((sp + 32#64) ↦₆₄ locA) ∗ ((sp + 400#64) ↦₆₄ cap) ∗ words4At (sp + 408#64) w0 w1 w2 w3 ∗
             ((sp + 440#64) ↦₆₄ w4) ∗ ((sp + 448#64) ↦₆₄ w5) ∗ words4At (sp + 1280#64) w0 w1 w2 w3 ∗
             ((sp + 1312#64) ↦₆₄ w4) ∗ ((sp + 1320#64) ↦₆₄ w5)) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x8 = cap ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = sp + 400#64 ∧ sf.readReg64 .x27 = sp + 56#64) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  unfold words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_blk433_vm (mid := (blkPl_434).base + 528#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  exact ⟨by sep_ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

theorem loadRatchet_ok_1b_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {cap remA msgA d_cap w6 w7 w16 w17 w24 w25 w26 w27 w28 w29 w30 w31
     d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64}
    {s0 s : State} (hpc : s.pc = (blkPl_434).base + 528#64) (hmeta : tryDecryptWPInv s0 s)
    (hx8 : s.readReg64 .x8 = cap) (hx22 : s.readReg64 .x22 = msgA)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 56#64) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_434).rebase (blkPl_434).base H) ((blkPl_434).base + 588#64) s
      (((sp + 48#64) ↦₆₄ remA) ∗ ((sp + 56#64) ↦₆₄ d_cap) ∗ ((sp + 456#64) ↦₆₄ w6) ∗
       ((sp + 464#64) ↦₆₄ w7) ∗ ((sp + 536#64) ↦₆₄ w16) ∗ ((sp + 544#64) ↦₆₄ w17) ∗
       words8At (sp + 600#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
       words8At (sp + 256#64) d24 d25 d26 d27 d28 d29 d30 d31)
      (fun sf P =>
        P = (((sp + 48#64) ↦₆₄ remA) ∗ ((sp + 56#64) ↦₆₄ cap) ∗ ((sp + 456#64) ↦₆₄ w6) ∗
             ((sp + 464#64) ↦₆₄ w7) ∗ ((sp + 536#64) ↦₆₄ w16) ∗ ((sp + 544#64) ↦₆₄ w17) ∗
             words8At (sp + 600#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
             words8At (sp + 256#64) w24 w25 w26 w27 w28 w29 w30 w31) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = sp + 56#64 ∧ sf.readReg64 .x1 = msgA + 56#64 ∧
        sf.readReg64 .x8 = remA ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = sp + 704#64 ∧ sf.readVReg128 0#5 = w17 ++ w16 ∧ sf.readVReg128 2#5 = w7 ++ w6) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_blk433_vm (mid := (blkPl_434).base + 588#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  exact ⟨by sep_ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem loadRatchet_ok_1c_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w8 w9 w16 w17 w18 w19 w20 w21 w22 w23 d16 d17 d18 d19 d20 d21 d22 d23 : BitVec 64}
    {s0 s : State} (hpc : s.pc = (blkPl_434).base + 588#64) (hmeta : tryDecryptWPInv s0 s)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 56#64)
    (hq0 : s.readVReg128 0#5 = w17 ++ w16) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_434).rebase (blkPl_434).base H) ((blkPl_434).base + 620#64) s
      (((sp + 472#64) ↦₆₄ w8) ∗ ((sp + 480#64) ↦₆₄ w9) ∗ ((sp + 552#64) ↦₆₄ w18) ∗
       ((sp + 560#64) ↦₆₄ w19) ∗ words4At (sp + 568#64) w20 w21 w22 w23 ∗
       words8At (sp + 192#64) d16 d17 d18 d19 d20 d21 d22 d23)
      (fun sf P =>
        P = (((sp + 472#64) ↦₆₄ w8) ∗ ((sp + 480#64) ↦₆₄ w9) ∗ ((sp + 552#64) ↦₆₄ w18) ∗
             ((sp + 560#64) ↦₆₄ w19) ∗ words4At (sp + 568#64) w20 w21 w22 w23 ∗
             words8At (sp + 192#64) w16 w17 w18 w19 w20 w21 w22 w23) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 0#5 = w9 ++ w8 ∧ sf.readVReg128 2#5 = s.readVReg128 2#5) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_blk433_vm (mid := (blkPl_434).base + 620#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  exact ⟨by sep_ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem loadRatchet_ok_1d_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {remA msgA g2a0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64}
    {counter g28 : BitVec 32} {g2ac : BitVec 8} {s0 s : State}
    (hpc : s.pc = (blkPl_434).base + 620#64) (hmeta : tryDecryptWPInv s0 s)
    (hx8 : s.readReg64 .x8 = remA) (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hq0 : s.readVReg128 0#5 = w9 ++ w8) (hq2 : s.readVReg128 2#5 = w7 ++ w6) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_434).rebase (blkPl_434).base H) (segFindChainPC_at (blkPl_434).base) s
      (((sp + 40#64) ↦₃₂ g28) ∗ ((sp + 488#64) ↦₆₄ w10) ∗ ((sp + 496#64) ↦₆₄ w11) ∗
       words4At (sp + 504#64) w12 w13 w14 w15 ∗ ((sp + 672#64) ↦₆₄ g2a0) ∗ ((sp + 684#64) ↦₈ g2ac) ∗
       words4At (sp + 1280#64) w0 w1 w2 w3 ∗ ((sp + 1312#64) ↦₆₄ w4) ∗ ((sp + 1320#64) ↦₆₄ w5) ∗
       ((msgA + 104#64) ↦₃₂ counter) ∗ words8At (sp + 64#64) d0 d1 d2 d3 d4 d5 d6 d7 ∗
       words8At (sp + 128#64) d8 d9 d10 d11 d12 d13 d14 d15)
      (fun sf P =>
        P = (((sp + 40#64) ↦₃₂ counter) ∗ ((sp + 488#64) ↦₆₄ w10) ∗ ((sp + 496#64) ↦₆₄ w11) ∗
             words4At (sp + 504#64) w12 w13 w14 w15 ∗ ((sp + 672#64) ↦₆₄ remA) ∗
             ((sp + 684#64) ↦₈ (s.readReg64 .x26).setWidth 8) ∗ words4At (sp + 1280#64) w0 w1 w2 w3 ∗
             ((sp + 1312#64) ↦₆₄ w4) ∗ ((sp + 1320#64) ↦₆₄ w5) ∗ ((msgA + 104#64) ↦₃₂ counter) ∗
             words8At (sp + 64#64) w0 w1 w2 w3 w4 w5 w6 w7 ∗
             words8At (sp + 128#64) w8 w9 w10 w11 w12 w13 w14 w15) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x8 = sp + 400#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  apply sepWP_blk433_vm (mid := segFindChainPC_at (blkPl_434).base)
  intro _m_strip
  dsimp only [segFindChainPC_at]
  unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  exact ⟨by sep_ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem loadRatchet_ok_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {cap locA remA msgA g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
     w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
     d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
     d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64}
    {counter g28 : BitVec 32} {g2ac : BitVec 8} {s0 s : State}
    (hcap : cap + 1#64 ≠ 0#64) (hpc : s.pc = (blkPl_434).base + 484#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx25 : s.readReg64 .x25 = locA) :
    let prog := (blkPC_434).rebase (blkPl_434).base H
    let sp := s0.sp - 1504#64
    SepWP prog (segFindChainPC_at (blkPl_434).base) s
      (((sp + 32#64) ↦₆₄ g20) ∗ ((sp + 40#64) ↦₃₂ g28) ∗ ((sp + 48#64) ↦₆₄ remA) ∗
       ((sp + 56#64) ↦₆₄ d_cap) ∗
       words32At (sp + 64#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 400#64) ↦₆₄ cap) ∗
       words32At (sp + 408#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       ((sp + 672#64) ↦₆₄ g2a0) ∗ ((sp + 684#64) ↦₈ g2ac) ∗
       words4At (sp + 1280#64) t0 t1 t2 t3 ∗ ((sp + 1312#64) ↦₆₄ t4) ∗ ((sp + 1320#64) ↦₆₄ t5) ∗
       ((msgA + 104#64) ↦₃₂ counter))
      (fun sf P =>
        ∃ b2ac : BitVec 8,
          P = (((sp + 32#64) ↦₆₄ locA) ∗ ((sp + 40#64) ↦₃₂ counter) ∗ ((sp + 48#64) ↦₆₄ remA) ∗
               ((sp + 56#64) ↦₆₄ cap) ∗
               words32At (sp + 64#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
                 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
               ((sp + 400#64) ↦₆₄ cap) ∗
               words32At (sp + 408#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
                 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
               ((sp + 672#64) ↦₆₄ remA) ∗ ((sp + 684#64) ↦₈ b2ac) ∗
               words4At (sp + 1280#64) w0 w1 w2 w3 ∗ ((sp + 1312#64) ↦₆₄ w4) ∗ ((sp + 1320#64) ↦₆₄ w5) ∗
               ((msgA + 104#64) ↦₃₂ counter)) ∧
          VmPreserved s sf ∧
          tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = sp + 56#64 ∧ sf.readReg64 .x1 = msgA + 56#64 ∧
          sf.readReg64 .x8 = sp + 400#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = sp + 400#64 ∧
          sf.readReg64 .x27 = sp + 56#64 ∧ sf.readReg64 .x28 = sp + 704#64) := by
  dsimp only
  have h1a := loadRatchet_ok_1a_433_wp_placed (H := H)
    (cap := cap) (locA := locA) (g20 := g20)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    hcap hpc hmeta hx20 hx23 hx25
  refine SepWP.rw_pre (by rw [words32At_40_eq, words32At_198_eq]) ?_
  refine SepWP.bind_framed h1a (by sep_frame) ?_
  intro s1a P1a ⟨hP1a, hvm1a, hmeta1a, hx8_1a, hx19_1a, hx20_1a, hx21_1a, hx22_1a, hx23_1a, hx24_1a, hx25_1a, hx27_1a⟩ hpc1a
  subst hP1a
  have h1b := loadRatchet_ok_1b_433_wp_placed (H := H)
    (cap := cap) (remA := remA) (msgA := msgA) (d_cap := d_cap)
    (w6 := w6) (w7 := w7) (w16 := w16) (w17 := w17)
    (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27)
    (w28 := w28) (w29 := w29) (w30 := w30) (w31 := w31)
    (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27)
    (d28 := d28) (d29 := d29) (d30 := d30) (d31 := d31)
    hpc1a hmeta1a hx8_1a (hx22_1a.trans hx22) hx25_1a hx27_1a
  refine SepWP.bind_framed h1b (by sep_frame) ?_
  intro s1b P1b ⟨hP1b, hvm1b, hmeta1b, hx0_1b, hx1_1b, hx8_1b, hx19_1b, hx20_1b, hx21_1b, hx22_1b, hx23_1b, hx24_1b, hx25_1b, hx27_1b, hx28_1b, hq0_1b, hq2_1b⟩ hpc1b
  subst hP1b
  have h1c := loadRatchet_ok_1c_433_wp_placed (H := H)
    (w8 := w8) (w9 := w9) (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19)
    (w20 := w20) (w21 := w21) (w22 := w22) (w23 := w23)
    (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19)
    (d20 := d20) (d21 := d21) (d22 := d22) (d23 := d23)
    hpc1b hmeta1b (hx25_1b.trans hx25_1a) (hx27_1b.trans hx27_1a) hq0_1b
  refine SepWP.bind_framed h1c (by sep_frame) ?_
  intro s1c P1c ⟨hP1c, hvm1c, hmeta1c, hx0_1c, hx1_1c, hx8_1c, hx19_1c, hx20_1c, hx21_1c, hx22_1c, hx23_1c, hx24_1c, hx25_1c, hx27_1c, hx28_1c, hq0_1c, hq2_1c⟩ hpc1c
  subst hP1c
  have h1d := loadRatchet_ok_1d_433_wp_placed (H := H)
    (remA := remA) (msgA := msgA) (g2a0 := g2a0)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (w6 := w6) (w7 := w7) (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11)
    (w12 := w12) (w13 := w13) (w14 := w14) (w15 := w15)
    (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14) (d15 := d15)
    (counter := counter) (g28 := g28) (g2ac := g2ac)
    hpc1c hmeta1c (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
    hq0_1c (by reg_chain)
  refine SepWP.bind_framed h1d (by sep_frame) ?_
  intro sf Pf ⟨hPf, hvm1d, hmetaf, hx0_f, hx1_f, hx8_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx27_f, hx28_f⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨(s1c.readReg64 .x26).setWidth 8, ?_,
    hvm1a.trans (hvm1b.trans (hvm1c.trans hvm1d)), hmetaf, by reg_chain⟩
  rw [words32At_40_eq, words32At_198_eq]
  sep_ac_rfl

/-! ## Budget-Threaded `trFrom` Call and Post-Call `S1` Branches -/

theorem loadRatchet_call_trFrom_433_reaches_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {ctl : BitVec 64} {H : String → Option (State → State)}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec M A lim))
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State)
    (hS1 : LoadRatchetStatePlaced (blkPl_434).base A lim stB ctl x R s0 s) :
    let prog := (blkPC_434).rebase (blkPl_434).base H
    let sp := s0.sp - 1504#64
    let res := Mut.exec TripleRatchet.fromSessionState x.st
    reaches_pc prog ((blkPl_434).base + 484#64) s
      (fun s_ret =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          tryDecryptMidMeta_placed s0 s_ret ∧
          s_ret.readReg64 .x19 = x.ret ∧
          s_ret.readReg64 .x20 = sp + 320#64 ∧
          s_ret.readReg64 .x21 = x.ss ∧
          s_ret.readReg64 .x22 = x.msgA ∧
          s_ret.readReg64 .x23 = sp + 1280#64 ∧
          (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
          s_ret.readReg64 .x25 = x.locA ∧
          (s_ret.mem ⊨
            sessionStateAt A.repAlloc x.ss x.G.afterTrFrom res.2 ∗
            trResultAt A.repAlloc (sp + 400#64) x.G res.1 ∗
            memRegion x.ret 48 ∗
            memRegion sp 48 ∗
            ((sp + 48#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 56#64) 344 ∗
            memRegion (sp + 664#64) 744 ∗
            cliTryDecryptCommonHeapPlaced A lim (M.stepEvents evs stB) ctl x 0 s0 s_ret ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hS1 with ⟨hpc, hmeta_full, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx1, hmem⟩
  obtain ⟨hmeta, hro⟩ := tryDecryptMidMetaPlaced_to_placed hmeta_full
  have hwp_bl := loadRatchet_bl_433_wp_placed (H := H) hpc (tryDecryptMidMeta_placed.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt (A.atState lim stB s) x.ss x.G x.st ∗ memRegion x.ret 48 ∗ memRegion sp 48 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 1352 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
         (A.atState lim stB s) ctl x 0 s0 ∗ R) := by
    rw [emp_sepConj]; exact hmem
  refine reaches_pc_seq_lscl hmeta.2.2.2.2.2.2.1
    (reaches_pc_lsro hro (sepWP_to_reaches_pc hwp_bl hmem_emp)) ?_
  intro s_call hpc_call _
    ⟨⟨P1, hm_call, ⟨hP1, hvm_c, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c, hcs_c⟩⟩, hro_call⟩
    hcl_call
  subst hP1
  rw [emp_sepConj] at hm_call
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced at hm_call
  have h56_split :
      memRegion (sp + 56#64) 1352 =
      memRegion (sp + 56#64) 344 ∗ memRegion (sp + 400#64) 264 ∗ memRegion (sp + 664#64) 744 := by
    rw [show (1352 : Nat) = 344 + (264 + 744) by decide,
        memRegion_split (sp + 56#64) 344 (264 + 744) (by decide),
        show sp + 56#64 + 344#64 = sp + 400#64 by bv_omega,
        memRegion_split (sp + 400#64) 264 744 (by decide),
        show sp + 400#64 + 264#64 = sp + 664#64 by bv_omega]
  have hpool_eq : (A.atState lim stB s).pool = A.pool lim stB s_call :=
    congrArg (·.pool) (A.atState_eq_of_vmPreserved lim stB hvm_c).symm
  rw [h56_split, show lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) from rfl,
      stackAt_tryDecryptSubStack_sub s0.sp trFromStack (by decide),
      hpool_eq, sessionStateAt_atState, protocolAddressAt_atState,
      protocolAddressAt_atState, signalMessageAt_atState] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  let tg : TrFromGhost := { ss := x.ss, G := x.G, st := x.st, ret := sp + 400#64 }
  let F_call : SepProp :=
    memRegion x.ret 48 ∗ memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 56#64) 344 ∗ memRegion (sp + 664#64) 744 ∗
    protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
    signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ cliTapeAfter ctl x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64) (tryDecryptSubStack - trFromStack) ∗
    tryDecryptSavedRegs s0.sp s0 ∗ R
  have htrFrom_blk :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_434).rebase (blkPl_434).base H) htrFrom
  rw [show (blkPl_57).base = lsmpl.base 57 from rfl] at htrFrom_blk
  have hpre_call :
      s_call.mem ⊨ (withLsRoLoaded lsmpl (trFromRawPlacedSpec M A lim)).pre (tg, stB) s_call ∗ F_call := by
    dsimp only [withLsRoLoaded, trFromRawPlacedSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro_call, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c.trans hx21, hx1_c.trans hx1, hx8_c⟩, ?_⟩
    rw [hsp_call]; dsimp only [tg, F_call, sp] at hm_call ⊢; convert hm_call using 1; sep_ac_rfl
  refine reaches_pc_call_lscl htrFrom_blk (tg, stB) F_call hpc_call hwpInv_call.1 hlr_call hcl_call hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hcl_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  dsimp only [withLsRoLoaded, trFromRawPlacedSpec] at hpost_ret
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpost_ret
  rcases hpost_ret with ⟨evs, hpost_ret⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨⟨hevs, _hAfter, htr_ret⟩, hm_ret⟩
  have hsp_ret' : s_ret.sp = s0.sp - 1504#64 := by reg_chain
  have halign_ret : s_ret.spAligned = true := by
    rw [State.spAligned, hsp_ret', ← hwpInv_call.2.1]; exact halign_call
  have hmeta_ret : tryDecryptMidMeta_placed s0 s_ret :=
    ⟨hrun_ret, hsp_ret', hwpInv_call.2.2.1, halign_ret, by reg_chain, by reg_chain, hcl_ret, by reg_chain⟩
  refine ⟨evs, hevs, hmeta_ret, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, ?_⟩
  rw [hsp_call] at hm_ret
  unfold cliTryDecryptCommonHeapPlaced
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
  have hpool_ret : (A.atState lim (M.stepEvents evs stB) s_ret).pool =
      A.pool lim (M.stepEvents evs stB) s_ret := rfl
  rw [show lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) from rfl,
      stackAt_tryDecryptSubStack_sub s0.sp trFromStack (by decide),
      protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState, hpool_ret]
  dsimp only [tg, TrFromGhost.model, F_call, sp] at hm_ret ⊢
  convert hm_ret using 1; sep_ac_rfl

private theorem loadRatchet_err_pre_extract_433 {A : RustAlloc}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {F : SepProp} {s0 s : State} (hnpan : e ≠ .panic)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 400#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 48 ∗
      (((s0.sp - 1504#64) + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 664#64) 744 ∗ F) :
    let sp := s0.sp - 1504#64
    ∃ (w0 w1 w2 w3 w4 t0 t1 t2 t3 t4 t5 r0 r1 r2 r3 r4 r5 : BitVec 64) (H_spe : SepProp),
      (∀ q : BitVec 64, (q ↦₆₄ speTag e) ∗ words5At (q + 8#64) w0 w1 w2 w3 w4 ∗ H_spe ⊢
        speAt A (utf8 "decrypt") q e) ∧
      (s.mem ⊨
        (((sp + 400#64) ↦₆₄ errTag) ∗ ((sp + 408#64) ↦₆₄ speTag e) ∗
         words5At (sp + 416#64) w0 w1 w2 w3 w4 ∗ ((sp + 1280#64) ↦₆₄ t0) ∗
         words5At (sp + 1288#64) t1 t2 t3 t4 t5 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5) ∗
        (H_spe ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 48 ∗
         ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
         memRegion (sp + 456#64) 208 ∗ memRegion (sp + 664#64) 616 ∗
         memRegion (sp + 1328#64) 80 ∗ F)) := by
  let sp := s0.sp - 1504#64
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    (((sp + 400#64) ↦₆₄ errTag) ∗ speAt A (utf8 "decrypt") (sp + 400#64 + 8#64) e ∗
     memRegion (sp + 400#64 + 56#64) 208) ∗
    memRegion x.ret 48 ∗ memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 56#64) 344 ∗ memRegion (sp + 664#64) 744 ∗ F at hm
  rw [show sp + 400#64 + 8#64 = sp + 408#64 by bv_omega,
      show sp + 400#64 + 56#64 = sp + 456#64 by bv_omega,
      speAt_eq_speTag_speBodyAt hnpan,
      show sp + 408#64 + 8#64 = sp + 416#64 by bv_omega,
      show (744 : Nat) = 616 + 128 by decide,
      memRegion_split (sp + 664#64) 616 128 (by decide),
      show sp + 664#64 + 616#64 = sp + 1280#64 by bv_omega,
      show (128 : Nat) = 48 + 80 by decide,
      memRegion_split (sp + 1280#64) 48 80 (by decide),
      show sp + 1280#64 + 48#64 = sp + 1328#64 by bv_omega] at hm
  have hm1 : s.mem ⊨ speBodyAt A (utf8 "decrypt") (sp + 416#64) e ∗
      (memRegion (sp + 1280#64) 48 ∗ memRegion x.ret 48 ∗ ((sp + 400#64) ↦₆₄ errTag) ∗
       ((sp + 408#64) ↦₆₄ speTag e) ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 456#64) 208 ∗ memRegion (sp + 664#64) 616 ∗
       memRegion (sp + 1328#64) 80 ∗ F) := by convert hm using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hm2, hent_spe⟩ := exists_words5_of_speBodyAt hnpan hm1
  have hm3 : s.mem ⊨ memRegion (sp + 1280#64) 48 ∗
      (memRegion x.ret 48 ∗ words5At (sp + 416#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
       ((sp + 400#64) ↦₆₄ errTag) ∗ ((sp + 408#64) ↦₆₄ speTag e) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 56#64) 344 ∗ memRegion (sp + 456#64) 208 ∗
       memRegion (sp + 664#64) 616 ∗ memRegion (sp + 1328#64) 80 ∗ F) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, t3, t4, t5, hm4⟩ := exists_words6_of_memRegion_48 hm3
  rw [show sp + 1280#64 + 8#64 = sp + 1288#64 by bv_omega] at hm4
  have hm5 : s.mem ⊨ memRegion x.ret 48 ∗
      (((sp + 1280#64) ↦₆₄ t0) ∗ words5At (sp + 1288#64) t1 t2 t3 t4 t5 ∗
       words5At (sp + 416#64) w0 w1 w2 w3 w4 ∗ H_spe ∗ ((sp + 400#64) ↦₆₄ errTag) ∗
       ((sp + 408#64) ↦₆₄ speTag e) ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 456#64) 208 ∗ memRegion (sp + 664#64) 616 ∗
       memRegion (sp + 1328#64) 80 ∗ F) := by convert hm4 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hm6⟩ := exists_words6_of_memRegion_48 hm5
  refine ⟨w0, w1, w2, w3, w4, t0, t1, t2, t3, t4, t5, r0, r1, r2, r3, r4, r5, H_spe, hent_spe, ?_⟩
  dsimp only [sp] at hm6 ⊢; convert hm6 using 1; sep_ac_rfl

theorem loadRatchet_after_call_error_tight_433_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {remEnv : List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init st : M.σ} {evs : List AllocEvent}
    {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st remEnv)
    (hevs : remEnv evs)
    (herr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1))
    (hpc : s.pc = (blkPl_434).base + 484#64)
    (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hm : s.mem ⊨
      sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
      trResultAt A.repAlloc ((s0.sp - 1504#64) + 400#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 48 ∗
      (((s0.sp - 1504#64) + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 664#64) 744 ∗
      cliTryDecryptCommonHeapPlaced A lim (M.stepEvents evs st) ctl x 0 s0 s ∗ R) :
    reaches_outcome ((blkPC_434).rebase (blkPl_434).base H)
      (cliTryDecryptTightSpecPlaced C A lim ctl uuidTryParse S tdEnv) (x, st_init) R s0 s := by
  let sp := s0.sp - 1504#64
  obtain ⟨_, hnpan, hdraws, hmodel⟩ := fromSessionState_error_imp C S x e st1 herr
  have hmod1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
  have hmod2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
  have hnpan_mod : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; intro h; injection h with h'; exact hnpan h'
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  refine reaches_epilogue_to_outcome_tight_seam_433_placed x st_init st x.G.afterTrFrom R s0 s
    hnpan_mod hG' hsb ?_
  set st_ret := M.stepEvents evs st
  set A_s : RustAlloc := A.atState lim st_ret s
  have hm_as : s.mem ⊨
      sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗
      trResultAt A_s (sp + 400#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗ memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 56#64) 344 ∗ memRegion (sp + 664#64) 744 ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
         A_s ctl x 0 s0 ∗ R) := by
    dsimp only [A_s, sp]
    rw [sessionStateAt_atState, trResultAt_atState]
    simpa only [cliTryDecryptCommonHeapPlaced, sepConj_assoc] using hm
  obtain ⟨w0, w1, w2, w3, w4, t0, t1, t2, t3, t4, t5, r0, r1, r2, r3, r4, r5,
    H_spe, hent_spe, hm_pre⟩ := loadRatchet_err_pre_extract_433 hnpan hm_as
  have hwp := loadRatchet_err_433_wp_placed (H := H)
    (ret := x.ret) (tag := speTag e) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx19 hx20 hx23
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf _ ⟨hPf, hvm_f, hwpInv_f⟩ hinv_f hmf
  subst hPf
  refine ⟨evs, hevs, hwpInv_f.to_midMeta_placed hinv_f, ?_⟩
  have hA_eq : A.atState lim st_ret sf = A_s :=
    A.atState_eq_of_vmPreserved lim st_ret hvm_f
  unfold cliTryDecryptCommonHeapPlaced
  rw [hA_eq, hmod1, hmod2, hdraws]
  change sf.mem ⊨
    sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ speAt A_s (utf8 "decrypt") x.ret e ∗
    memRegion sp 1408 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
      A_s ctl x 0 s0 ∗ R
  have hmf_re : sf.mem ⊨
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
      (memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
       ((sp + 400#64) ↦₆₄ errTag) ∗ ((sp + 408#64) ↦₆₄ speTag e) ∗
       words5At (sp + 416#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 456#64) 208 ∗
       memRegion (sp + 664#64) 616 ∗ ((sp + 1280#64) ↦₆₄ speTag e) ∗
       words5At (sp + 1288#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 1328#64) 80) ∗
      (sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
         A_s ctl x 0 s0 ∗ R) := by
    dsimp only [sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (hent_spe x.ret)
      (sepConj_mono_left (loadRatchet_err_stack_recombine sp x.remA (speTag e) w0 w1 w2 w3 w4)))
    hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

theorem loadRatchet_after_call_error_433_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {remEnv : List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init st : M.σ} {evs : List AllocEvent}
    {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st remEnv)
    (hevs : remEnv evs)
    (herr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1))
    (hpc : s.pc = (blkPl_434).base + 484#64)
    (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hm : s.mem ⊨
      sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
      trResultAt A.repAlloc ((s0.sp - 1504#64) + 400#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 48 ∗
      (((s0.sp - 1504#64) + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 664#64) 744 ∗
      cliTryDecryptCommonHeapPlaced A lim (M.stepEvents evs st) ctl x 0 s0 s ∗ R) :
    reaches_outcome ((blkPC_434).rebase (blkPl_434).base H)
      (cliTryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv) (x, st_init) R s0 s :=
  reaches_outcome_weaken_tight_placed
    (loadRatchet_after_call_error_tight_433_placed hsb hevs herr hpc hmeta hx19 hx20 hx23 hm)

theorem loadRatchet_after_call_ok_433_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_434).base + 484#64) (hmeta : tryDecryptMidMeta_placed s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = x.locA)
    (hm : s.mem ⊨
      sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
      trResultAt A.repAlloc ((s0.sp - 1504#64) + 400#64) x.G (.ok tr) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 48 ∗
      (((s0.sp - 1504#64) + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 664#64) 744 ∗
      cliTryDecryptCommonHeapPlaced A lim st ctl x 0 s0 s ∗ R) :
    reaches_pc ((blkPC_434).rebase (blkPl_434).base H) (segFindChainPC_at (blkPl_434).base) s
      (fun s' => ∃ trG, trGhostCaps trG = s1InitCaps x.G ∧
        FindChainStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 R s0 s') := by
  let sp := s0.sp - 1504#64
  set A_s : RustAlloc := A.atState lim st s
  have hm_as : s.mem ⊨
      sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗
      trResultAt A_s (sp + 400#64) x.G (.ok tr) ∗
      memRegion x.ret 48 ∗ memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 56#64) 344 ∗ memRegion (sp + 664#64) 744 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
        A_s ctl x 0 s0 ∗ R := by
    dsimp only [A_s, sp]
    rw [sessionStateAt_atState, trResultAt_atState]
    exact hm
  change s.mem ⊨
    sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗
    (∃∗ senderPad : List (BitVec 8),
      trAt A_s (sp + 400#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
    memRegion x.ret 48 ∗ memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 56#64) 344 ∗ memRegion (sp + 664#64) 744 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
      A_s ctl x 0 s0 ∗ R at hm_as
  have hm_ex : s.mem ⊨
      (∃∗ senderPad : List (BitVec 8),
        trAt A_s (sp + 400#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
      (sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 48 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 664#64) 744 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
         A_s ctl x 0 s0 ∗ R) := by
    convert hm_as using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨senderPad, hm_tr⟩
  let trG : TrGhost := ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩
  change s.mem ⊨ trAt A_s (sp + 400#64) trG tr ∗
    (sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 48 ∗
     ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
     memRegion (sp + 664#64) 744 ∗
     CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
       A_s ctl x 0 s0 ∗ R) at hm_tr
  rw [trAt_eq_cap_body_heap, show sp + 400#64 + 8#64 = sp + 408#64 by bv_omega] at hm_tr
  have hm_heap : s.mem ⊨ trHeapAt A_s trG tr ∗
      (((sp + 400#64) ↦₆₄ trG.ratchet.chainsCap) ∗ trBodyAt (sp + 408#64) trG tr ∗
       sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 48 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 664#64) 744 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
         A_s ctl x 0 s0 ∗ R) := by
    convert hm_tr using 1; sep_ac_rfl
  obtain ⟨hpad, hcap⟩ := trHeapAt_facts hm_heap
  have hm_body : s.mem ⊨ trBodyAt (sp + 408#64) trG tr ∗
      (trHeapAt A_s trG tr ∗ ((sp + 400#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 48 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 664#64) 744 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
         A_s ctl x 0 s0 ∗ R) := by
    convert hm_heap using 1; sep_ac_rfl
  refine elim_exists_words32_of_trBodyAt hpad hm_body
    fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 H_tr hm_w hent_tr => ?_
  have hm_stk : s.mem ⊨
      (memRegion sp 48 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 664#64) 744) ∗
      (words32At (sp + 408#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       H_tr ∗ trHeapAt A_s trG tr ∗ ((sp + 400#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
         A_s ctl x 0 s0 ∗ R) := by
    convert hm_w using 1; sep_ac_rfl
  refine elim_s1_ok_stack_extract hm_stk
    fun g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
        d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 g28 g2ac hm_stk2 => ?_
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced at hm_stk2
  rw [signalMessageAt_eq_counter_rest] at hm_stk2
  let F_ok : SepProp :=
    H_tr ∗ trHeapAt A_s trG tr ∗ sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗
    memRegion sp 32 ∗ memRegion (sp + 44#64) 4 ∗ memRegion (sp + 320#64) 80 ∗
    memRegion (sp + 664#64) 8 ∗ memRegion (sp + 680#64) 4 ∗ memRegion (sp + 685#64) 595 ∗
    memRegion (sp + 1328#64) 80 ∗ protocolAddressAt A_s x.rem x.remA ∗ protocolAddressAt A_s x.loc x.locA ∗
    signalMessageNoCounterAt A_s x.msgG x.msgA x.msg ∗ cliTapeAfter ctl x.cur x.rest 0 ∗
    lsLogOff ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
    tryDecryptSavedRegs s0.sp s0 ∗ A_s.pool ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 32#64) ↦₆₄ g20) ∗ ((sp + 40#64) ↦₃₂ g28) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
       ((sp + 56#64) ↦₆₄ d_cap) ∗
       words32At (sp + 64#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 400#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       words32At (sp + 408#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       ((sp + 672#64) ↦₆₄ g2a0) ∗ ((sp + 684#64) ↦₈ g2ac) ∗
       words4At (sp + 1280#64) t0 t1 t2 t3 ∗ ((sp + 1312#64) ↦₆₄ t4) ∗ ((sp + 1320#64) ↦₆₄ t5) ∗
       ((x.msgA + 104#64) ↦₃₂ x.msg.counter)) ∗ F_ok := by
    dsimp only [F_ok, sp] at hm_stk2 ⊢; convert hm_stk2 using 1; sep_ac_rfl
  have hwp := loadRatchet_ok_433_wp_placed (H := H)
    (cap := trG.ratchet.chainsCap) (locA := x.locA) (remA := x.remA) (msgA := x.msgA)
    (g20 := g20) (d_cap := d_cap) (g2a0 := g2a0)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5) (w6 := w6) (w7 := w7)
    (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11) (w12 := w12) (w13 := w13) (w14 := w14) (w15 := w15)
    (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19) (w20 := w20) (w21 := w21) (w22 := w22) (w23 := w23)
    (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27) (w28 := w28) (w29 := w29) (w30 := w30) (w31 := w31)
    (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14) (d15 := d15)
    (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19) (d20 := d20) (d21 := d21) (d22 := d22) (d23 := d23)
    (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27) (d28 := d28) (d29 := d29) (d30 := d30) (d31 := d31)
    (counter := x.msg.counter) (g28 := g28) (g2ac := g2ac)
    hcap hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx20 hx22 hx23 hx25
  have hstep : reaches_pc ((blkPC_434).rebase (blkPl_434).base H) (segFindChainPC_at (blkPl_434).base) s
      (fun sf => LibsignalRoLoaded lsmpl sf.mem →
        trGhostCaps trG = s1InitCaps x.G ∧
        FindChainStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 R s0 sf) := by
    refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
    intro sf Pf hpcf ⟨b2ac, hPf, hvm_f, hwpInv_f, hx0_f, hx1_f, hx8_f,
      hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx27_f, hx28_f⟩ hcl_f hmf hro_f
    subst hPf
    have hcaps : trGhostCaps trG = s1InitCaps x.G := rfl
    have hA_eq : A.atState lim st sf = A_s := A.atState_eq_of_vmPreserved lim st hvm_f
    refine ⟨hcaps, ?_⟩
    unfold FindChainStatePlaced CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainStatePlaced
    rw [hA_eq]
    refine ⟨hpcf, tryDecryptMidMetaPlaced_of_placed (hwpInv_f.to_midMeta_placed hcl_f) hro_f,
      hx0_f, hx1_f, hx8_f,
      hx19_f.trans hx19, hx20_f.trans hx20, hx21_f.trans hx21, hx22_f.trans hx22, hx23_f.trans hx23,
      by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_f]; exact hx24,
      hx25_f, hx27_f, hx28_f, ?_⟩
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
    rw [trAt_eq_cap_body_heap, show sp + 56#64 + 8#64 = sp + 64#64 by bv_omega,
        signalMessageAt_eq_counter_rest]
    have hmf_re : sf.mem ⊨
        (words32At (sp + 64#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
           w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr) ∗
        (memRegion (sp + 320#64) 80 ∗ ((sp + 400#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         words32At (sp + 408#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
           w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
         memRegion (sp + 664#64) 8 ∗ ((sp + 672#64) ↦₆₄ x.remA) ∗ memRegion (sp + 680#64) 4 ∗
         ((sp + 684#64) ↦₈ b2ac) ∗ memRegion (sp + 685#64) 595 ∗
         words4At (sp + 1280#64) w0 w1 w2 w3 ∗ ((sp + 1312#64) ↦₆₄ w4) ∗ ((sp + 1320#64) ↦₆₄ w5) ∗
         memRegion (sp + 1328#64) 80) ∗
        (sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         trHeapAt A_s trG tr ∗ memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
         ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         protocolAddressAt A_s x.rem x.remA ∗ protocolAddressAt A_s x.loc x.locA ∗
         ((x.msgA + 104#64) ↦₃₂ x.msg.counter) ∗ signalMessageNoCounterAt A_s x.msgG x.msgA x.msg ∗
         cliTapeAfter ctl x.cur x.rest 0 ∗ lsLogOff ∗
         stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗ A_s.pool ∗ R) := by
      dsimp only [F_ok, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
    have hmf2 := Satisfies.mono
      (sepConj_mono (hent_tr (sp + 64#64))
        (sepConj_mono_left
          (loadRatchet_ok_stack_recombine sp trG.ratchet.chainsCap x.remA b2ac
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31))) hmf_re
    dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl
  exact reaches_pc_mono (reaches_pc_lsro hro hstep) (fun _ _ _ ⟨himpl, hro_f⟩ => ⟨trG, himpl hro_f⟩)

/-! ## Budget-Threaded `ErrTail` Seam Theorems -/

def ErrTailSeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (e : SignalProtocolError) (R : SepProp) (s0 s : State),
    e ≠ .panic →
    (x.model C S parse).1 = .error e →
    (x.model C S parse).2 = st1 →
    SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st FreeOnlyEvs →
    ErrTailStatePlaced entry A lim st ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome prog (cliTryDecryptSpecPlaced C A lim ctl parse S tdEnv)
      (x, st_init) R s0 s

theorem errTail_ok_tight_433_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : TryDecryptGhost) (st_init st : M.σ) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (e : SignalProtocolError) (R : SepProp) (s0 s : State)
    (he : e ≠ .panic)
    (hmod1 : (x.model C S parse).1 = .error e)
    (hmod2 : (x.model C S parse).2 = st1)
    (hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st FreeOnlyEvs)
    (herr : ErrTailStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s) :
    reaches_outcome ((blkPC_434).rebase (blkPl_434).base H)
      (cliTryDecryptTightSpecPlaced C A lim ctl parse S tdEnv) (x, st_init) R s0 s := by
  rcases herr with ⟨hpc, hmeta_full, hx19, hx20, hx26, hmem⟩
  obtain ⟨hmeta, _⟩ := tryDecryptMidMetaPlaced_to_placed hmeta_full
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta_placed.to_wpInv hmeta
  have hcl : LibsignalCodeLoaded lsmpl s.mem := hmeta.2.2.2.2.2.2.1
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  let A0 : RustAlloc := A.atState lim st s
  have hmem_tr :
      s.mem ⊨ trAt A0 (sp + 56#64) trG tr ∗
        (sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 56 ∗
         memRegion (sp + 320#64) 40 ∗ speBodyAt A0 (utf8 "decrypt") (sp + 360#64) e ∗
         memRegion (sp + 400#64) 1008 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
           A0 ctl x draws s0 ∗ R) := by
    dsimp only [sp, A0]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e ∗
        (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 80#64) 152 ∗
         ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 248#64) 72 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 56 ∗
         memRegion (sp + 320#64) 40 ∗ memRegion (sp + 400#64) 1008 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
           A0 ctl x draws s0 ∗ R) := by
    dsimp only [sp, A0] at hmem1 ⊢
    rw [chainAt_atState_fn, live_atState, sessionStateAt_atState] at hmem1
    have hspe_eq : speBodyAt (A.atState lim st s) (utf8 "decrypt") (sp + 360#64) e =
        speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e := by
      cases e <;> simp only [speBodyAt, invalidMessageStrAt_atState, vecU8_atState]
    rw [hspe_eq] at hmem1
    convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_speBodyAt he hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 80#64) 152 ∗
         ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 248#64) 72 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion sp 56 ∗ memRegion (sp + 320#64) 40 ∗
         memRegion (sp + 400#64) 1008 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
           A0 ctl x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h320_split :
      memRegion (sp + 320#64) 40 = memRegion (sp + 320#64) 24 ∗ memRegion (sp + 344#64) 16 := by
    rw [show (40 : Nat) = 24 + 16 by decide, memRegion_split (sp + 320#64) 24 16 (by decide),
        show (sp + 320#64) + 24#64 = sp + 344#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 320#64) 24 ∗
        (memRegion (sp + 344#64) 16 ∗ (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 80#64) 152 ∗
         ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 248#64) 72 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion sp 56 ∗ memRegion (sp + 400#64) 1008 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
           A0 ctl x draws s0 ∗ R) := by
    rw [h320_split] at hmem3; dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp := errTail_all_steps_433_wp_placed (A := A) (lim := lim) (ast := st) (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2)
    hdealloc hcs_le hcs_lt hpc hmeta_wp hcl hx19 hx20 hx26
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced at hmem4
  dsimp only [A0] at hmem4
  rw [protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hpool_eq : (A.atState lim st s).pool = A.pool lim st s := rfl
  rw [hpool_eq] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ t0) ∗ ((sp + 328#64) ↦₆₄ t1) ∗
         ((sp + 336#64) ↦₆₄ t2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool lim st s ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 56 ∗
         memRegion (sp + 80#64) 152 ∗ memRegion (sp + 248#64) 72 ∗ memRegion (sp + 344#64) 16 ∗
         memRegion (sp + 400#64) 1008 ∗ sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ cliTapeAfter ctl x.cur x.rest draws ∗
         lsLogOff ∗ tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.model C S parse).1 ≠ .error .panic := by
    rw [hmod1]; exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.model C S parse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  apply reaches_epilogue_to_outcome_tight_seam_433_placed x st_init st x.G.afterTrFrom R s0 s hnpan hG' hsb
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta_placed hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩; subst hPf
  have hm_ex :
      sf.mem ⊨
        (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
         ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ speTag e) ∗
         words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ stackAt sp dropChainStack ∗
         memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 56 ∗
         memRegion (sp + 80#64) 152 ∗ memRegion (sp + 248#64) 72 ∗ memRegion (sp + 344#64) 16 ∗
         memRegion (sp + 400#64) 1008 ∗ sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ cliTapeAfter ctl x.cur x.rest draws ∗
         lsLogOff ∗ tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨evs_exit, hm_ex⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_ex
  rcases hm_ex with ⟨hevs_exit, hm_ex⟩
  refine ⟨evs_exit, hevs_exit, hmeta_f, ?_⟩
  unfold cliTryDecryptCommonHeapPlaced
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
  rw [sessionStateAt_atState, vecResultAt_atState,
      protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hpool_f : (A.atState lim (M.stepEvents evs_exit st) sf).pool =
      A.pool lim (M.stepEvents evs_exit st) sf := rfl
  rw [hpool_f]
  have hdec_ent :
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      vecResultAt A.repAlloc x.ret (x.model C S parse).1 := by
    rw [hmod1]; exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 56 ∗ ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 80#64) 152 ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 248#64) 72 ∗
          ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗ ((sp + 336#64) ↦₆₄ w2) ∗
          memRegion (sp + 344#64) 16 ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 400#64) 1008) ∗
         (protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ cliTapeAfter ctl x.cur x.rest draws ∗
          lsLogOff ∗
          (stackAt sp dropChainStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗ A.pool lim (M.stepEvents evs_exit st) sf) ∗ R := by
    dsimp only [sp] at hm_ex ⊢; convert hm_ex using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono hdec_ent (sepConj_mono_left
      (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4)))) hmem_f_re

theorem errTail_ok_433_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : TryDecryptGhost) (st_init st : M.σ) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (e : SignalProtocolError) (R : SepProp) (s0 s : State)
    (he : e ≠ .panic)
    (hmod1 : (x.model C S parse).1 = .error e)
    (hmod2 : (x.model C S parse).2 = st1)
    (hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st FreeOnlyEvs)
    (herr : ErrTailStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s) :
    reaches_outcome ((blkPC_434).rebase (blkPl_434).base H)
      (cliTryDecryptSpecPlaced C A lim ctl parse S tdEnv) (x, st_init) R s0 s :=
  reaches_outcome_weaken_tight_placed
    (errTail_ok_tight_433_placed hdealloc x st_init st trG tr st1 e R s0 s he hmod1 hmod2 hsb herr)

theorem errTail_433_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    ErrTailTightSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl parse S tdEnv := by
  intro x st_init st trG tr st1 e R s0 s he hmod1 hmod2 hsb herr
  exact errTail_ok_tight_433_placed hdealloc x st_init st trG tr st1 e R s0 s he hmod1 hmod2 hsb herr

theorem errTail_433_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    ErrTailSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl parse S tdEnv := by
  intro x st_init st trG tr st1 e R s0 s he hmod1 hmod2 hsb herr
  exact errTail_ok_433_placed hdealloc x st_init st trG tr st1 e R s0 s he hmod1 hmod2 hsb herr

/-! ## Budget-Threaded Segment `S1` (`LoadRatchet`) Seam Contracts -/

def S1SeamGenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1ErrEnv : List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s1ErrEnv →
      reaches_outcome prog (cliTryDecryptSpecPlaced C A lim ctl parse S tdEnv)
        (x, st_init) R s0 s
    | (.ok tr, st1) =>
      FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧
        ∃ evs trG, s1OkEnv x evs ∧
          FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

def S1TightSeamGenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1ErrEnv : List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s1ErrEnv →
      reaches_outcome prog (cliTryDecryptTightSpecPlaced C A lim ctl parse S tdEnv)
        (x, st_init) R s0 s
    | (.ok tr, st1) =>
      FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧
        ∃ evs trG, s1OkEnv x evs ∧
          FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

def S1SeamPinnedGenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1ErrEnv : List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s1ErrEnv →
      reaches_outcome prog (cliTryDecryptSpecPlaced C A lim ctl parse S tdEnv)
        (x, st_init) R s0 s
    | (.ok tr, st1) =>
      FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧
        ∃ evs trG, s1OkEnv x evs ∧ trGhostCaps trG = s1InitCaps x.G ∧
          FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

def S1TightSeamPinnedGenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1ErrEnv : List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s1ErrEnv →
      reaches_outcome prog (cliTryDecryptTightSpecPlaced C A lim ctl parse S tdEnv)
        (x, st_init) R s0 s
    | (.ok tr, st1) =>
      FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧
        ∃ evs trG, s1OkEnv x evs ∧ trGhostCaps trG = s1InitCaps x.G ∧
          FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

abbrev S1SeamFreePlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1SeamGenPlaced prog entry C A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

abbrev S1TightSeamFreePlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1TightSeamGenPlaced prog entry C A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

abbrev S1SeamPinnedFreePlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1SeamPinnedGenPlaced prog entry C A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

abbrev S1TightSeamPinnedFreePlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1TightSeamPinnedGenPlaced prog entry C A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

theorem loadRatchet_tight_pinned_gen_433_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1ErrEnv : List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec M A lim))
    (hs1Err : ∀ evs, FreeOnlyEvs evs → s1ErrEnv evs)
    (hs1Ok : ∀ x evs, FreeOnlyEvs evs → s1OkEnv x evs) :
    S1TightSeamPinnedGenPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S tdEnv s1ErrEnv s1OkEnv := by
  intro x st_init st R s0 s hS1 hcode
  have hro : LibsignalRoLoaded lsmpl s.mem := hS1.2.1.2.2.2.2.2.2.1.2
  have hcall := loadRatchet_call_trFrom_433_reaches_placed htrFrom x R s0 s hS1
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    intro hsb
    obtain ⟨s_ret, hsteps_ret,
      ⟨hpc_ret, _, evs, hevs, hmeta_ret, hx19_ret, hx20_ret, _, _, hx23_ret, _, _, hm_ret⟩ |
      ⟨_, hoom⟩⟩ := hcall hcode
    · rw [hres] at hm_ret
      exact reaches_outcome_steps hsteps_ret
        (loadRatchet_after_call_error_tight_433_placed hsb (hs1Err evs hevs)
          hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)
    · exact hoom.elim
  | ok tr =>
    intro _hfits
    have hreach : reaches_pc ((blkPC_434).rebase (blkPl_434).base H) (segFindChainPC_at (blkPl_434).base) s
        (fun s' => ∃ evs trG, s1OkEnv x evs ∧ trGhostCaps trG = s1InitCaps x.G ∧
          FindChainStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s') := by
      refine reaches_pc_seq (reaches_pc_lsro hro hcall) ?_
      rintro s_ret hpc_ret _ ⟨⟨evs, hevs, hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret,
        hx23_ret, hx24_ret, hx25_ret, hm_ret⟩, hro_ret⟩
      rw [hres] at hm_ret
      refine reaches_pc_mono
        (loadRatchet_after_call_ok_433_placed hpc_ret hmeta_ret hro_ret hx19_ret hx20_ret hx21_ret
          hx22_ret hx23_ret hx24_ret hx25_ret hm_ret)
        fun _ _ _ ⟨trG, hcaps, hS2⟩ => ⟨evs, trG, hs1Ok x evs hevs, hcaps, hS2⟩
    obtain ⟨s', hsteps, ⟨_, _, evs, trG, hevs_ok, hcaps, hS2⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, evs, trG, hevs_ok, hcaps, hS2⟩
    · exact hoom.elim

theorem loadRatchet_pinned_gen_433_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1ErrEnv : List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec M A lim))
    (hs1Err : ∀ evs, FreeOnlyEvs evs → s1ErrEnv evs)
    (hs1Ok : ∀ x evs, FreeOnlyEvs evs → s1OkEnv x evs) :
    S1SeamPinnedGenPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S tdEnv s1ErrEnv s1OkEnv := by
  have h := loadRatchet_tight_pinned_gen_433_placed_ok (C := C) (ctl := ctl) (S := S)
    (tdEnv := tdEnv) htrFrom hs1Err hs1Ok
  intro x st_init st R s0 s hst hcode
  have h' := h x st_init st R s0 s hst hcode; revert h'
  rcases Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | tr, st1⟩
  · exact fun hfn hsb => reaches_outcome_weaken_tight_placed (hfn hsb)
  · exact id

theorem loadRatchet_gen_433_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1ErrEnv : List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec M A lim))
    (hs1Err : ∀ evs, FreeOnlyEvs evs → s1ErrEnv evs)
    (hs1Ok : ∀ x evs, FreeOnlyEvs evs → s1OkEnv x evs) :
    S1TightSeamGenPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S tdEnv s1ErrEnv s1OkEnv := by
  have h := loadRatchet_tight_pinned_gen_433_placed_ok (C := C) (ctl := ctl) (S := S)
    (tdEnv := tdEnv) htrFrom hs1Err hs1Ok
  intro x st_init st R s0 s hst hcode
  have h' := h x st_init st R s0 s hst hcode; revert h'
  rcases Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | tr, st1⟩
  · exact id
  · rintro hfn hfits; rcases hfn hfits with ⟨s', hsteps, evs, trG, hevs, _hcaps, hS2⟩
    exact ⟨s', hsteps, evs, trG, hevs, hS2⟩

theorem loadRatchet_gen_433_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1ErrEnv : List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec M A lim))
    (hs1Err : ∀ evs, FreeOnlyEvs evs → s1ErrEnv evs)
    (hs1Ok : ∀ x evs, FreeOnlyEvs evs → s1OkEnv x evs) :
    S1SeamGenPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S tdEnv s1ErrEnv s1OkEnv := by
  have h := loadRatchet_gen_433_placed_okT (C := C) (ctl := ctl) (S := S)
    (tdEnv := tdEnv) htrFrom hs1Err hs1Ok
  intro x st_init st R s0 s hst hcode
  have h' := h x st_init st R s0 s hst hcode; revert h'
  rcases Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | tr, st1⟩
  · exact fun hfn hsb => reaches_outcome_weaken_tight_placed (hfn hsb)
  · exact id

theorem loadRatchet_pinned_433_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec M A lim))
    (hs1Ok : ∀ x evs, FreeOnlyEvs evs → s1OkEnv x evs) :
    S1TightSeamPinnedFreePlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S tdEnv s1OkEnv :=
  loadRatchet_tight_pinned_gen_433_placed_ok htrFrom (fun _ h => h) hs1Ok

theorem loadRatchet_pinned_433_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec M A lim))
    (hs1Ok : ∀ x evs, FreeOnlyEvs evs → s1OkEnv x evs) :
    S1SeamPinnedFreePlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S tdEnv s1OkEnv :=
  loadRatchet_pinned_gen_433_placed_ok htrFrom (fun _ h => h) hs1Ok

theorem loadRatchet_433_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec M A lim))
    (hs1Ok : ∀ x evs, FreeOnlyEvs evs → s1OkEnv x evs) :
    S1TightSeamFreePlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S tdEnv s1OkEnv :=
  loadRatchet_gen_433_placed_okT htrFrom (fun _ h => h) hs1Ok

theorem loadRatchet_433_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec M A lim))
    (hs1Ok : ∀ x evs, FreeOnlyEvs evs → s1OkEnv x evs) :
    S1SeamFreePlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S tdEnv s1OkEnv :=
  loadRatchet_gen_433_placed_ok htrFrom (fun _ h => h) hs1Ok

end LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS1ErrPlacedBudget
