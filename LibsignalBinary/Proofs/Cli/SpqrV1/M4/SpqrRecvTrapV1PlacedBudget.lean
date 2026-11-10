/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvErrPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeys
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Segments 5 & 6 (`PqRecv` and `DeriveKeys`) on CLI Block `433`

Proves budget-threaded (`RustCliAllocBudget M`) `S6SeamPlaced` (`deriveKeys_433_placed_ok`) and
`S5WTSeamPlaced` (`pqRecv_433_placed_ok_WT` and seam instantiations) on CLI Block `433` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvTrapV1PlacedBudget

open scoped LibsignalBinary.Proofs.Placed.BudgetVmSteps
open scoped LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp (
  sessionStateAt_atState trAt_atState trRestAt_atState
  protocolAddressAt_atState signalMessageAt_atState signalMessageRestAt_atState
  vecU8At_atState spqrRecvKeyAt_atState spqrRecvResultAt_atState
  vecArg_at_atState
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (
  steps_of_sepWP_placed_state s5_out_add_np_evs
  spqrRecvRawSpecPlaced PqRecvEnv
  fitsEnv_recv_of_pqRecvEnv fitsEnv_fmt_of_pqRecvEnv_err pqRecvEnv_of_err_parts
  onPanic_of_spqrRecv_budget_placed
)

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalTripleRatchet.Decrypt
  CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (
  Crypto SignalProtocolError TripleRatchet SessionState MessageKeyGenerator
)
open CryptoVerification (
  LibsignalPlacement lsmpl lsρ lsRustDeallocSym
)
open CryptoVerification.RustHeap (vecU8 vecU8At vecHeader)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser uuidTryParse errTag protocolAddressAt sessionStateAt signalMessageAt
)
open CryptoVerification.LibsignalTripleRatchet (
  GenerateKeysGhost generateKeysStack
  mkgAt spqrRecvKeyAt spqrRecvResultAt messageKeysAt
  SendCall SpqrModel TrGhost trAt TryDecryptGhost VecArg
  LibsignalCodeRoLoaded withLsCodeRoLoaded logOff rootStack spqrRecvStack
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_434 blkPl_434 blkLib_eq_434 instIsLsBlockProg_434
  segPqRecvPC_at segDeriveKeysPC_at segVerifyMacPC_at
  tryDecryptMidMetaPlaced
  tryDecryptSubStack tryDecryptSavedRegs tryDecryptPlacedImg
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (
  extractLsb0_8_append56
  sp_fp_eq mr_cut mr_cut_add stackAt_sub
  pointsTo32_merge64
  optKeyAt_split optKeyAt_fold mkgAt_fold
  tryDecryptMidMetaCore steps_done_of_sepWP_midMeta_placed
  trRestAt trAt_split_pq signalMessageRestAt signalMessageAt_split_pq
  cap_add_one_ne_zero byte_ne_zero_cbz32 byte_ne_zero_cbz64_32
  spqrRecvRawSpec
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees (
  lsFormatInnerSym
)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots (trTrapExternsPlaced)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  VmPreserved FitsEnv FreeOnlyEvs rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (
  FormatInnerEnv formatInnerBudgetEnvSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (
  hooksException sepWP_seg_ls_vm
)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (
  GenerateKeysEnv freeOnlyEvs_of_generateKeysEnv
  generateKeysSpecWithStack generateKeysSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget (
  steps_call_out_placed_cro
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  tryDecryptOnPanic
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (
  s6FreeOnlyEnv s6FreeOnlyEnv_inhabited
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (
  lsLogOff_eq_logOff_placed
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvErrPlacedBudget (
  pqRecv_recv_err_true_433_placed pqRecv_recv_err_false_433_placed
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  ErrTailStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced VerifyMacStatePlaced
  S5WTSeamPlaced S6SeamPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (
  SpqrRecvBytesEnv SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv
  spqrRecvRawSpecPlacedT spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecPlacedT
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

/-! ## 1. Re-Exports (`s6FreeOnlyEnv`, `spqrRecvRawSpecT`, `PqRecvEnv`) -/

abbrev spqrRecvRawSpecT := @spqrRecvRawSpecPlacedT
abbrev spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecT :=
  @spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecPlacedT

/-! ## 2. Segment 6 (`DeriveKeys`) on CLI Block `433` -/

private theorem reaches_pc_of_vm_and_cro_call [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P R : SepProp} {P_mid : State → SepProp}
    {RegMid Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧
        (VmPreserved s sm → (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid sm ∗ R))))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      RegMid sm → SepWP prog target sm (P_mid sm)
        (fun sf P_f => LibsignalCodeRoLoaded lsmpl sf.mem → (sf.mem ⊨ P_f ∗ R) → Q sf)) :
    reaches_pc prog target s Q := by
  intro hL
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hvm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hvm hmm
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    rcases (h2 sm hpc hrun hclm hReg).elim hmm' (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpcf, hrunf, P_f, hmf, hq⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, hq (hclm.of_keepsFrozen hsteps'.keepsFrozen) hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem deriveKeys_433_placed_ok_withStack [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (H : String → Option (State → State))
    {genStack : Nat}
    (hstack_sub : ∀ sp : BitVec 64,
      stackAt sp tryDecryptSubStack =
        memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - genStack) ∗
          stackAt sp genStack)
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    (hs6Env : ∀ (x : GenerateKeysGhost) evs, GenerateKeysEnv x evs → s6Env x.g evs)
    (hgen : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 69)
      (withLsCodeRoLoaded lsmpl (generateKeysSpecWithStack M A lim C.F genStack))) :
    S6SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A lim ctl s6Env := by
  intro x st trG tr st1 mkg newPqrState pqrKey draws R s0 s hseed_len _hfit h6
  unfold DeriveKeysStatePlaced
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysStatePlaced at h6
  rcases h6 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25, hx27, hx28,
    seedCap, seedPtr, newPqrCap, newPqrPtr, msgW, hx8, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  unfold segDeriveKeysPC_at at hpc
  rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl] at hpc
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced at hmem
  rw [lsLogOff_eq_logOff_placed] at hmem
  simp only [sessionStateAt_atState, trAt_atState, RustCliAllocBudget.atState_live,
    vecU8At_atState, spqrRecvKeyAt_atState,
    protocolAddressAt_atState, signalMessageAt_atState,
    RustCliAllocBudget.atState_pool] at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx27 hx28 hx29 hsp29_eq hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  have hreach : reaches_pc ((blkPC_434).rebase (blkPl_434).base H)
      ((blkPl_434).base + 1596#64) s
      (fun sf => ∃ evs, s6Env mkg evs ∧
        (sf.sp = sp ∧ (s0.sp &&& 15#64 == 0#64) = true ∧ sf.spAligned = true ∧
          sf.readReg64 .fp = sp + 1408#64 ∧ sf.trace = s0.trace ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        VerifyMacStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
          x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0 sf) := by
    refine reaches_pc_of_vm_and_cro_call hmem (hcl := hcl)
      (mid := lsmpl.base 69)
      (RegMid := fun sm =>
        newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
        sm.readReg64 .x0 = sp + 400#64 ∧
        sm.readReg64 .x1 = sp + 864#64 ∧
        sm.readReg64 .x8 = sp + 1280#64 ∧
        sm.readReg64 .lr = (blkPl_434).base + 1596#64 ∧
        sm.readReg64 .x19 = x.ret ∧
        sm.readReg64 .x20 = sp + 320#64 ∧
        sm.readReg64 .x21 = x.ss ∧
        sm.readReg64 .x22 = x.msgA ∧
        sm.readReg64 .x23 = sp + 976#64 ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
        sm.readReg64 .x25 = sp + 400#64 ∧
        sm.readReg64 .x27 = sp + 56#64 ∧
        sm.readReg64 .x28 = sp + 1280#64 ∧
        sm.readReg64 .fp = sp + 1408#64 ∧
        sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      (P_mid := fun sm =>
        mkgAt A.repAlloc (sp + 400#64) mkg ∗
        spqrRecvKeyAt A.repAlloc (sp + 864#64) pqrKey ∗
        memRegion (sp + 1280#64) 84 ∗
        A.pool lim st sm ∗ stackAt sp tryDecryptSubStack ∗
        sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
        trAt A.repAlloc (sp + 56#64) trG tr ∗
        (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
          (newPqrPtr ↦ₛ newPqrState) ∗
          memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length)
            (newPqrCap.toNat - newPqrState.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 8 ∗
        ((sp + 8#64) ↦₆₄ newPqrCap) ∗
        memRegion (sp + 16#64) 12 ∗
        ((sp + 28#64) ↦₃₂ msgW) ∗
        ((sp + 32#64) ↦₆₄ x.locA) ∗
        ((sp + 40#64) ↦₆₄ newPqrPtr) ∗
        ((sp + 48#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 320#64) 80 ∗
        memRegion (sp + 440#64) 424 ∗
        memRegion (sp + 888#64) 216 ∗
        memRegion (sp + 1104#64) 176 ∗
        memRegion (sp + 1364#64) 44 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        cliTapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        tryDecryptSavedRegs s0.sp s0)
      ?_ ?_
    · by_vm_steps (
      wp_conv_pre =>
        simp only [sepConj_assoc]
        unfold vecU8At vecHeader
        rw [memRegion_split sp 8 8 (by decide),
          mr_cut_add sp 320 80 704 (by decide),
          mr_cut_add sp 400 8 696 (by decide),
          mr_cut_add sp 408 8 688 (by decide),
          mr_cut_add sp 416 8 680 (by decide),
          mr_cut_add sp 424 8 672 (by decide),
          mr_cut_add sp 432 8 664 (by decide),
          mr_cut_add sp 440 8 656 (by decide),
          mr_cut_add sp 448 8 648 (by decide),
          mr_cut_add sp 456 8 640 (by decide),
          mr_cut_add sp 464 8 632 (by decide),
          mr_cut_add sp 472 8 624 (by decide),
          mr_cut_add sp 480 8 616 (by decide),
          mr_cut_add sp 488 376 240 (by decide),
          mr_cut_add sp 864 8 232 (by decide),
          mr_cut_add sp 872 8 224 (by decide),
          mr_cut_add sp 880 8 216 (by decide),
          mr_cut_add sp 1116 4 160 (by decide),
          mr_cut_add sp 1120 8 152 (by decide),
          mr_cut_add sp 1128 8 144 (by decide),
          mr_cut_add sp 1136 8 136 (by decide),
          mr_cut_add sp 1144 8 128 (by decide),
          mr_cut_add sp 1152 8 120 (by decide),
          mr_cut_add sp 1160 8 112 (by decide)]
        simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
          memRegion_eight (sp + 8#64),
          memRegion_eight (sp + 400#64),
          memRegion_eight (sp + 408#64),
          memRegion_eight (sp + 416#64),
          memRegion_eight (sp + 424#64),
          memRegion_eight (sp + 432#64),
          memRegion_eight (sp + 440#64),
          memRegion_eight (sp + 448#64),
          memRegion_eight (sp + 456#64),
          memRegion_eight (sp + 464#64),
          memRegion_eight (sp + 472#64),
          memRegion_eight (sp + 480#64),
          memRegion_eight (sp + 864#64),
          memRegion_eight (sp + 872#64),
          memRegion_eight (sp + 880#64),
          memRegion_four (sp + 1116#64),
          memRegion_eight (sp + 1120#64),
          memRegion_eight (sp + 1128#64),
          memRegion_eight (sp + 1136#64),
          memRegion_eight (sp + 1144#64),
          memRegion_eight (sp + 1152#64),
          memRegion_eight (sp + 1160#64),
          CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.pointsTo64_split32 (sp + 400#64)]
      refine SepWP.focus_weaken (optKeyAt_split A.repAlloc (sp + 1304#64) pqrKey) (by sep_focus) ?_
      wp_pull_exists
      wp_focus_pure
      rintro ⟨hnp1, hnp2, hnp3⟩
      refine SepWP.focus_rw (pointsTo32_merge64 (sp + 1112#64) mkg.counter _) (by sep_focus) ?_
      wp_steps
      rw [show ((sp + 424#64) ↦₆₄ 32#64) = ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) by
        rw [hseed_len]]
      refine SepWP.focus_weaken (optKeyAt_fold A.repAlloc (sp + 864#64) _ _ _ pqrKey) (by sep_focus) ?_
      refine SepWP.focus_weaken (mkgAt_fold A.repAlloc (sp + 400#64) seedCap seedPtr _ _ mkg hseed)
        (by sep_focus) ?_
      have hm16 : memRegion (sp + 16#64) 12 = memRegion (sp + 16#64) 8 ∗ memRegion (sp + 24#64) 4 := by
        simpa using mr_cut_add sp 16 8 4 (by decide)
      have hm440 : memRegion (sp + 440#64) 424 =
          memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗ (memRegion (sp + 456#64) 8 ∗
          (memRegion (sp + 464#64) 8 ∗ (memRegion (sp + 472#64) 8 ∗ (memRegion (sp + 480#64) 8 ∗
          memRegion (sp + 488#64) 376))))) := by
        rw [mr_cut_add sp 440 8 416 (by decide),
          mr_cut_add sp 448 8 408 (by decide),
          mr_cut_add sp 456 8 400 (by decide),
          mr_cut_add sp 464 8 392 (by decide),
          mr_cut_add sp 472 8 384 (by decide),
          mr_cut_add sp 480 8 376 (by decide)]
      have hm1104 : memRegion (sp + 1104#64) 176 =
          memRegion (sp + 1104#64) 8 ∗ (memRegion (sp + 1112#64) 8 ∗ (memRegion (sp + 1120#64) 8 ∗
          (memRegion (sp + 1128#64) 8 ∗ (memRegion (sp + 1136#64) 8 ∗ (memRegion (sp + 1144#64) 8 ∗
          (memRegion (sp + 1152#64) 8 ∗ (memRegion (sp + 1160#64) 8 ∗ memRegion (sp + 1168#64) 112))))))) := by
        rw [mr_cut_add sp 1104 8 168 (by decide),
          mr_cut_add sp 1112 8 160 (by decide),
          mr_cut_add sp 1120 8 152 (by decide),
          mr_cut_add sp 1128 8 144 (by decide),
          mr_cut_add sp 1136 8 136 (by decide),
          mr_cut_add sp 1144 8 128 (by decide),
          mr_cut_add sp 1152 8 120 (by decide),
          mr_cut_add sp 1160 8 112 (by decide)]
      have hm1280 : memRegion (sp + 1280#64) 84 =
          memRegion (sp + 1280#64) 8 ∗ (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗
          (memRegion (sp + 1304#64) 8 ∗ (memRegion (sp + 1312#64) 8 ∗ (memRegion (sp + 1320#64) 8 ∗
          memRegion (sp + 1328#64) 36))))) := by
        rw [mr_cut_add sp 1280 8 76 (by decide),
          mr_cut_add sp 1288 8 68 (by decide),
          mr_cut_add sp 1296 8 60 (by decide),
          mr_cut_add sp 1304 8 52 (by decide),
          mr_cut_add sp 1312 8 44 (by decide),
          mr_cut_add sp 1320 8 36 (by decide)]
      have hm1328 : memRegion (sp + 1328#64) 80 =
          memRegion (sp + 1328#64) 36 ∗ memRegion (sp + 1364#64) 44 := by
        simpa using mr_cut_add sp 1328 36 44 (by decide)
      rw [hm16, hm440, hm1104, hm1280, hm1328]
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm hm_out
      rw [← A.pool_of_vmPreserved hvm] at hm_out
      refine ⟨⟨hnp1, hnp2, hnp3,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩, ?_⟩
      arm64_sep_close
      )
    · intro sm hpcm hrunm ⟨hcl_code, hcl_ro⟩ hReg
      rcases hReg with ⟨hnp1, hnp2, hnp3, hx0m, hx1m, hx8m, hlrm,
        hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
      rw [hstack_sub sp, show stackAt sp genStack = stackAt sm.sp genStack by rw [hspm]]
      wp_call hgen (⟨sp + 400#64, mkg, sp + 864#64, pqrKey, sp + 1280#64⟩, st)
      have hevs_gen : GenerateKeysEnv ⟨sp + 400#64, mkg, sp + 864#64, pqrKey, sp + 1280#64⟩ w := hpost
      have htrace_f : sf.trace = sm.trace := by assumption
      have hm320 : memRegion (sp + 320#64) 960 =
          memRegion (sp + 320#64) 80 ∗ (memRegion (sp + 400#64) 40 ∗
          (memRegion (sp + 440#64) 424 ∗ (memRegion (sp + 864#64) 24 ∗
          (memRegion (sp + 888#64) 216 ∗ memRegion (sp + 1104#64) 176)))) := by
        rw [mr_cut_add sp 320 80 880 (by decide),
          mr_cut_add sp 400 40 840 (by decide),
          mr_cut_add sp 440 424 416 (by decide),
          mr_cut_add sp 864 24 392 (by decide),
          mr_cut_add sp 888 216 176 (by decide)]
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_
      intro hcl_sf sf_mem
      have hsp_sf : sf.sp = sp := by simp only [wp_norm, arm64_norm, *]
      refine ⟨w, hs6Env ⟨sp + 400#64, mkg, sp + 864#64, pqrKey, sp + 1280#64⟩ w hevs_gen, ?_, ?_⟩
      · refine ⟨hsp_sf, hsp0_al',
          by simp only [State.spAligned, wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
      · unfold VerifyMacStatePlaced
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacStatePlaced
          segVerifyMacPC_at tryDecryptMidMetaPlaced
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
        rw [show (0x63c#64 : BitVec 64) = 1596#64 by rfl]
        refine ⟨by simp only [wp_norm, arm64_norm, *], ?_,
          by simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          newPqrCap, newPqrPtr, msgW, hmsgW, hnp1, hnp2, hnp3, ?_⟩
        · refine ⟨by simp only [wp_norm, arm64_norm, *],
            by rw [hsp_def]; exact hsp_sf,
            hsp0_al',
            by simp only [State.spAligned, wp_norm, arm64_norm, *],
            by change _ = s0.sp - 96#64; rw [hsp29_eq]; simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            hcl_sf,
            by simp only [wp_norm, arm64_norm, *]⟩
        · rw [lsLogOff_eq_logOff_placed,
            CryptoVerification.LibsignalTripleRatchet.Decrypt.logOff_tryDecryptPlacedImg]
          rw [hsp_def, sessionStateAt_atState, trAt_atState, RustCliAllocBudget.atState_live,
            protocolAddressAt_atState, signalMessageAt_atState,
            RustCliAllocBudget.atState_pool, hstack_sub sp,
            show BitVec.ofNat 64 tryDecryptSubStack = 260640#64 by rfl, hm320]
          rw [hspm] at sf_mem
          simp only [sepConj_assoc] at sf_mem ⊢
          arm64_sep_close
  intro hL
  rcases hreach hL with ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, evs, hevs, _hmeta_core, hvmac⟩ | ⟨hpan_sf, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc_sf, hrun_sf, evs, hevs, hvmac⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan_sf, hoom⟩⟩

/-- Envelope-parametric budget-threaded relocatable `[LibsignalPlacement]` Segment S6 on CLI
    Block `433` (`blkPC_434` / `blkPl_434`). -/
theorem deriveKeys_433_placed_ok_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (H : String → Option (State → State))
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    (hs6Env : ∀ (x : GenerateKeysGhost) evs, GenerateKeysEnv x evs → s6Env x.g evs)
    (hgen : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 69)
      (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F))) :
    S6SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A lim ctl s6Env :=
  deriveKeys_433_placed_ok_withStack C A lim ctl H
    (fun sp => stackAt_sub sp tryDecryptSubStack generateKeysStack) hs6Env hgen

/-- Default `s6FreeOnlyEnv` budget-threaded relocatable `[LibsignalPlacement]` Segment S6 on CLI
    Block `433` (`blkPC_434` / `blkPl_434`), mirroring `SpqrRecvTrapV1Placed.deriveKeys_433_placed_ok`. -/
theorem deriveKeys_433_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (H : String → Option (State → State))
    (hgen : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 69)
      (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F))) :
    S6SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A lim ctl s6FreeOnlyEnv :=
  deriveKeys_433_placed_ok_ofEnv C A lim ctl H
    (fun _ _ h => freeOnlyEvs_of_generateKeysEnv h) hgen

/-! ## 3. Segment 5 (`PqRecv`) Helpers & `pqRecv_433_placed_ok_WT` on CLI Block `433` -/

private theorem pqr_len_lt_placed {A : CryptoVerification.RustHeap.RustAlloc}
    {g : CryptoVerification.LibsignalTripleRatchetRepr.SignalMessageGhost} {a : BitVec 64}
    {m : CryptoGames.LibsignalSession.SignalMessage} {Q : SepProp} {mem : Memory}
    (h : mem ⊨ signalMessageRestAt A g a m ∗ Q) :
    m.pqRatchet.length < 2 ^ 40 := by
  unfold signalMessageRestAt at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.2.2.1

private theorem pqr_len_lt_of_pre_placed {P F R : SepProp}
    {A : CryptoVerification.RustHeap.RustAlloc}
    {g : CryptoVerification.LibsignalTripleRatchetRepr.SignalMessageGhost} {a : BitVec 64}
    {m : CryptoGames.LibsignalSession.SignalMessage} {mem : Memory}
    (h : mem ⊨ P ∗ ((signalMessageRestAt A g a m ∗ F) ∗ R)) :
    m.pqRatchet.length < 2 ^ 40 := by
  have h' : mem ⊨ signalMessageRestAt A g a m ∗ (F ∗ R ∗ P) := by
    have heq : P ∗ ((signalMessageRestAt A g a m ∗ F) ∗ R) =
        signalMessageRestAt A g a m ∗ (F ∗ R ∗ P) := by sep_ac_rfl
    exact heq ▸ h
  exact pqr_len_lt_placed h'

private theorem spqrRecvStack_le_placed {sp0 sp : BitVec 64}
    (hstack : rootStack ≤ sp0.toNat) (hsp : sp0 - 1504#64 = sp) :
    spqrRecvStack ≤ sp.toNat := by
  subst hsp
  have h1 : rootStack = 262144 := rfl
  have h2 : spqrRecvStack = 131072 := rfl
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat]
    omega
  · rw [BitVec.le_def]
    simp only [BitVec.toNat_ofNat]
    omega

private theorem pre_spqrRecvRawSpecPlacedT [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {S : SpqrModel}
    {RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {stArg msgArg : VecArg} {ret : BitVec 64} {stB : M.σ} {sm : State} {F R : SepProp}
    (h1 : stArg.bytes.length < 2 ^ 32)
    (h2 : msgArg.bytes.length < 2 ^ 40)
    (h3 : spqrRecvStack ≤ sm.sp.toNat)
    (h : sm.mem ⊨ (spqrRecvRawSpecPlaced A lim S RecvEnv).pre ((stArg, msgArg, ret), stB) sm ∗
      (F ∗ (tokenInitPlacedAt ∗ R))) :
    sm.mem ⊨ (spqrRecvRawSpecPlacedT A lim S RecvEnv).pre ((stArg, msgArg, ret), stB) sm ∗
      (F ∗ R) := by
  dsimp only [spqrRecvRawSpecPlacedT]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨h1, h2, h3⟩, ?_⟩
  have heq :
      (tokenInitPlacedAt ∗
        (spqrRecvRawSpecPlaced A lim S RecvEnv).pre ((stArg, msgArg, ret), stB) sm) ∗ (F ∗ R) =
      (spqrRecvRawSpecPlaced A lim S RecvEnv).pre ((stArg, msgArg, ret), stB) sm ∗
        (F ∗ (tokenInitPlacedAt ∗ R)) := by
    sep_ac_rfl
  exact heq ▸ h

private theorem post_spqrRecvRawSpecPlacedT [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {S : SpqrModel}
    {RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : VecArg × VecArg × BitVec 64} {stB : M.σ} {sm sf1 : State} {F R : SepProp}
    (h : sf1.mem ⊨ ((spqrRecvRawSpecPlacedT A lim S RecvEnv).post (x, stB) sm sf1 ∗ F) ∗ R) :
    sf1.mem ⊨ ((spqrRecvRawSpecPlaced A lim S RecvEnv).post (x, stB) sm sf1 ∗ F) ∗
      (tokenInitPlacedAt ∗ R) := by
  dsimp only [spqrRecvRawSpecPlacedT] at h
  have heq :
      ((tokenInitPlacedAt ∗ (spqrRecvRawSpecPlaced A lim S RecvEnv).post (x, stB) sm sf1) ∗ F) ∗ R =
      ((spqrRecvRawSpecPlaced A lim S RecvEnv).post (x, stB) sm sf1 ∗ F) ∗ (tokenInitPlacedAt ∗ R) := by
    sep_ac_rfl
  exact heq ▸ h

private theorem tryDecryptOnPanic_absorb {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {x : TryDecryptGhost} {F R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ tryDecryptOnPanic C parse S x s0 sf ∗ (F ∗ R)) :
    sf.mem ⊨ tryDecryptOnPanic C parse S x s0 sf ∗ R := by
  unfold tryDecryptOnPanic at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hp, hmem⟩
  refine ⟨hp, ?_⟩
  rw [← sepConj_assoc] at hmem
  exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem

set_option maxHeartbeats 800000 in
theorem pqRecv_433_placed_ok_WT [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel)
    (RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop := FormatInnerEnv)
    (H : String → Option (State → State))
    (hrecv_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvRawSpecPlacedT A lim S RecvEnv)))
    (hfmt_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    S5WTSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      tokenInitPlacedAt C A lim ctl uuidTryParse S (PqRecvEnv S RecvEnv fmtEnv) := by
  intro x st trG tr st1 mkg draws R s0 s hQ hstack hfits hpqr_eq h5 hL
  unfold PqRecvStatePlaced
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvStatePlaced at h5
  rcases h5 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25,
    seedCap, seedPtr, msgW, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hfits_recv := fitsEnv_recv_of_pqRecvEnv hfits
  unfold segPqRecvPC_at at hpc
  rw [show (0x5b8#64 : BitVec 64) = 1464#64 by rfl] at hpc
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  clear hsp29_eq
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced at hmem
  rw [lsLogOff_eq_logOff_placed] at hmem
  simp only [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState,
    signalMessageAt_atState, RustCliAllocBudget.atState_pool,
    RustCliAllocBudget.atState_live] at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx29 hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  generalize hR0_def : (tokenInitPlacedAt ∗ R) = R0 at hmem
  simp only [← sepConj_assoc] at hmem
  suffices ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (∃ evs, PqRecvEnv S RecvEnv fmtEnv x tr evs ∧
            DeriveKeysStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
              x trG tr st1 mkg newPqrState pqrKey draws (tokenInitPlacedAt ∗ R) s0 s' ∧
            S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R)
      | .error sd =>
        let e := if sd = true then .invalidState else .invalidMessage x.msgType .pqRatchet
        (∃ evs, PqRecvEnv S RecvEnv fmtEnv x tr evs ∧
            ErrTailStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
              x trG tr st1 e draws (tokenInitPlacedAt ∗ R) s0 s' ∧
            S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R) by
    subst hR0_def
    cases hrecv_eq : S.recv tr.pqrState x.msg.pqRatchet with
    | error sd =>
      rw [hrecv_eq] at this
      exact this
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      rw [hrecv_eq] at this
      exact this
  refine steps_of_sepWP_placed_state hmem hL hcl
    (mid := lsmpl.base 329)
    (RegMid := fun sm =>
      sm.readReg64 .x0 = sp + 232#64 ∧
      sm.readReg64 .x1 = x.msgA ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = (blkPl_434).base + 1488#64 ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 1280#64 ∧
      (sm.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid := fun sm =>
      sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
      trAt A.repAlloc (sp + 56#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 16 ∗
      ((sp + 16#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 24#64) 4 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ seedCap) ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 784 ∗
      ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 1116#64) 164 ∗
      memRegion (sp + 1280#64) 48 ∗
      memRegion (sp + 1328#64) 80 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      protocolAddressAt A.repAlloc x.loc x.locA ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      cliTapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool lim st sm) ?_ ?_
  · wp_steps_sync_pool (lsmpl.base 329)
    have hm1116 : memRegion (sp + 1116#64) 292 =
        memRegion (sp + 1116#64) 164 ∗
          (memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80) := by
      rw [mr_cut_add sp 1116 164 128 (by decide), mr_cut_add sp 1280 48 80 (by decide)]
    rw [hm1116]
    wp_done
  · intro sm hpcm hrunm hclm hLm hReg hmm
    rcases hReg with ⟨hx0m, hx1m, hx8m, hlrm, hx19m, hx20m, hx21m, hx22m, hx23m, hw24m,
      hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    let stArg : VecArg := ⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩
    let msgArg : VecArg := ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩
    have hpre_call0 : sm.mem ⊨
        (spqrRecvRawSpecPlaced A lim S RecvEnv).pre ((stArg, msgArg, sp + 1280#64), st) sm ∗
        ((signalMessageRestAt A.repAlloc x.msgG x.msgA x.msg ∗
          trRestAt A.repAlloc sp trG tr ∗
          sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
          (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
            (seedPtr ↦ₛ mkg.seed) ∗
            memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
              (seedCap.toNat - mkg.seed.length)) ∗
          memRegion x.ret 48 ∗
          memRegion sp 16 ∗
          ((sp + 16#64) ↦₆₄ seedPtr) ∗
          memRegion (sp + 24#64) 4 ∗
          ((sp + 28#64) ↦₃₂ msgW) ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₆₄ seedCap) ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 784 ∗
          ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
          memRegion (sp + 1116#64) 164 ∗
          memRegion (sp + 1328#64) 80 ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          cliTapeAfter ctl x.cur x.rest draws ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
            (tryDecryptSubStack - spqrRecvStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R0) := by
      dsimp only [spqrRecvRawSpecPlaced, spqrRecvRawSpec, stArg, msgArg]
      simp only [vecArg_at_atState, RustCliAllocBudget.atState_pool]
      dsimp only [VecArg.at]
      rw [hspm]
      rw [trAt_split_pq, signalMessageAt_split_pq,
        stackAt_sub sp tryDecryptSubStack spqrRecvStack] at hmm
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hfits_recv, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0m, hx1m, hx8m⟩, ?_⟩
      simp only [sepConj_assoc] at hmm ⊢
      arm64_sep_close
    have hpq_lt : msgArg.bytes.length < 2 ^ 40 := pqr_len_lt_of_pre_placed hpre_call0
    have hst_lt : stArg.bytes.length < 2 ^ 32 := by
      show tr.pqrState.length < 2 ^ 32
      rw [hpqr_eq]
      exact hQ
    have hsp_lt : spqrRecvStack ≤ sm.sp.toNat := by
      rw [hspm]
      exact spqrRecvStack_le_placed hstack hsp_def
    subst hR0_def
    have hpre_call := pre_spqrRecvRawSpecPlacedT hst_lt hpq_lt hsp_lt hpre_call0
    clear hpre_call0
    cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      refine steps_call_out_placed_cro ((stArg, msgArg, sp + 1280#64), st) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => Or.inr ⟨hpan,
          onPanic_of_spqrRecv_budget_placed (A := A) (lim := lim) (RecvEnv := RecvEnv)
            (st_v := stArg) (msg_v := msgArg)
            (ret := sp + 1280#64) (st_m := st) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1_raw
      have hpost1 := post_spqrRecvRawSpecPlacedT hpost1_raw
      clear hpost1_raw
      generalize hR'_def : (tokenInitPlacedAt ∗ R) = R' at hpost1
      dsimp only [spqrRecvRawSpecPlaced, spqrRecvRawSpec, stArg, msgArg] at hpost1
      simp only [vecArg_at_atState, spqrRecvResultAt_atState,
        RustCliAllocBudget.atState_pool] at hpost1
      dsimp only [VecArg.at] at hpost1
      rw [hspm] at hspf1 hpost1
      have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨evs1, hpost1⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hevs1, hpost1⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt] at hpost1
      unfold vecU8 at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨newPqrCap, newPqrPtr, hpost1⟩
      set st_r := M.stepEvents evs1 st
      have hpq_evs : PqRecvEnv S RecvEnv fmtEnv x tr evs1 := by
        unfold PqRecvEnv; rw [hrecv]; exact hevs1
      have hpost1' : sf1.mem ⊨
          vecU8At A.repAlloc (sp + 1280#64) newPqrCap newPqrPtr newPqrState ∗
          (spqrRecvKeyAt A.repAlloc (sp + 1304#64) pqrKey ∗
           trAt A.repAlloc (sp + 56#64) trG tr ∗
           signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
           sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
               (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 16 ∗
           ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗
           ((sp + 28#64) ↦₃₂ msgW) ∗
           ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗
           ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 784 ∗
           ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
           ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
           memRegion (sp + 1116#64) 164 ∗
           memRegion (sp + 1328#64) 80 ∗
           protocolAddressAt A.repAlloc x.rem x.remA ∗
           protocolAddressAt A.repAlloc x.loc x.locA ∗
           cliTapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool lim st_r sf1) ∗ R' := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 24#64 = sp + 1304#64 by rw [BitVec.add_assoc]; rfl] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      unfold vecU8At vecHeader at hpost1'
      simp only [sepConj_assoc] at hpost1'
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1'
      rcases hpost1' with ⟨⟨hnp1, hnp2, hnp3⟩, hpost1'⟩
      have hcap_not_m1 : (newPqrCap + 1#64 == 0#64) = false := cap_add_one_ne_zero hnp2
      simp only [← sepConj_assoc] at hpost1'
      refine s5_out_add_np_evs hnpF ?_
      suffices ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) sf1 s' ∧
          (DeriveKeysStatePlaced (blkPl_434).base A lim st_r ctl
              x trG tr st1 mkg newPqrState pqrKey draws R' s0 s' ∨
            (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R)) by
        subst hR'_def
        obtain ⟨s', hsteps, hok | hpan⟩ := this
        · exact ⟨s', hsteps, Or.inl ⟨evs1, hpq_evs, hok⟩⟩
        · exact ⟨s', hsteps, Or.inr hpan⟩
      unfold DeriveKeysStatePlaced
        CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysStatePlaced
      refine steps_done_of_sepWP_midMeta_placed (s0 := s0)
        (Rest := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64 ∧
          sf.readReg64 .x21 = x.ss ∧
          sf.readReg64 .x22 = x.msgA ∧
          sf.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64 ∧
          (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
          sf.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64 ∧
          sf.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64 ∧
          sf.readReg64 .x28 = (s0.sp - 1504#64) + 0x500#64 ∧
          ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
            sf.readReg64 .x8 = newPqrCap ∧
            msgW.setWidth 8 = msgTypeByte x.msgType ∧
            mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
            (sf.mem ⊨
              sessionStateAt (A.atState lim st_r sf) x.ss x.G.afterTrFrom st1 ∗
              trAt (A.atState lim st_r sf) ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
              (if seedCap = 0 then emp else (A.atState lim st_r sf).live seedPtr seedCap.toNat 1 ∗
                (seedPtr ↦ₛ mkg.seed) ∗
                memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                  (seedCap.toNat - mkg.seed.length)) ∗
              vecU8At (A.atState lim st_r sf) ((s0.sp - 1504#64) + 0x500#64)
                newPqrCap newPqrPtr newPqrState ∗
              spqrRecvKeyAt (A.atState lim st_r sf) ((s0.sp - 1504#64) + 0x518#64) pqrKey ∗
              memRegion x.ret 48 ∗
              memRegion (s0.sp - 1504#64) 0x10 ∗
              (((s0.sp - 1504#64) + 0x10#64) ↦₆₄ seedPtr) ∗
              memRegion ((s0.sp - 1504#64) + 0x18#64) 4 ∗
              (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
              (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
              (((s0.sp - 1504#64) + 0x28#64) ↦₆₄ seedCap) ∗
              (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
              memRegion ((s0.sp - 1504#64) + 0x140#64) 0x310 ∗
              (((s0.sp - 1504#64) + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
              (((s0.sp - 1504#64) + 0x458#64) ↦₃₂ mkg.counter) ∗
              memRegion ((s0.sp - 1504#64) + 0x45c#64) 0xa4 ∗
              memRegion ((s0.sp - 1504#64) + 0x530#64) 0x50 ∗
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
                (A.atState lim st_r sf) ctl x draws s0 ∗ R'))
        hpost1' hLf1 hclf1 ?_
      unfold segDeriveKeysPC_at tryDecryptMidMetaCore
        CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
      rw [lsLogOff_eq_logOff_placed]
      simp only [sessionStateAt_atState, trAt_atState, vecU8At_atState, spqrRecvKeyAt_atState,
        protocolAddressAt_atState, signalMessageAt_atState,
        RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
      rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]
      clear hsp29_eq
      rw [hsp_def]
      dsimp only [vecU8At, vecHeader]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps_sync_pool ((blkPl_434).base + 1500#64)
      wp_done
    | error sd =>
      refine steps_call_out_placed_cro ((stArg, msgArg, sp + 1280#64), st) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => Or.inr ⟨hpan,
          onPanic_of_spqrRecv_budget_placed (A := A) (lim := lim) (RecvEnv := RecvEnv)
            (st_v := stArg) (msg_v := msgArg)
            (ret := sp + 1280#64) (st_m := st) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1_raw
      have hpost1 := post_spqrRecvRawSpecPlacedT hpost1_raw
      clear hpost1_raw
      generalize hR'_def : (tokenInitPlacedAt ∗ R) = R' at hpost1
      dsimp only [spqrRecvRawSpecPlaced, spqrRecvRawSpec, stArg, msgArg] at hpost1
      simp only [vecArg_at_atState, spqrRecvResultAt_atState,
        RustCliAllocBudget.atState_pool] at hpost1
      dsimp only [VecArg.at] at hpost1
      rw [hspm] at hspf1 hpost1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨evs1, hpost1⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hevs1, hpost1⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt, errTag] at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨d, hpost1⟩
      simp only [sepConj_assoc] at hpost1
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hd_iff, hpost1⟩
      set st_r := M.stepEvents evs1 st
      have hfits_fmt := fitsEnv_fmt_of_pqRecvEnv_err hrecv hfits hevs1
      have hpost1' : sf1.mem ⊨
          (((sp + 1288#64) ↦₈ d) ∗
           memRegion (sp + 1289#64) 7 ∗
           ((sp + 1280#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
           memRegion (sp + 1296#64) 32 ∗
           trAt A.repAlloc (sp + 56#64) trG tr ∗
           signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
           sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
               (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 16 ∗
           ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗
           ((sp + 28#64) ↦₃₂ msgW) ∗
           ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗
           ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 784 ∗
           ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
           ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
           memRegion (sp + 1116#64) 164 ∗
           memRegion (sp + 1328#64) 80 ∗
           protocolAddressAt A.repAlloc x.rem x.remA ∗
           protocolAddressAt A.repAlloc x.loc x.locA ∗
           cliTapeAfter ctl x.cur x.rest draws ∗
           lsLogOff ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool lim st_r sf1) ∗ R' := by
        rw [lsLogOff_eq_logOff_placed]
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 8#64 = sp + 1288#64 by rw [BitVec.add_assoc]; rfl,
          show (sp + 1280#64) + 9#64 = sp + 1289#64 by rw [BitVec.add_assoc]; rfl,
          mr_cut sp 1289 7 32 39 1296#64] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      rw [show sp + 1289#64 = (sp + 1288#64) + 1#64 by rw [BitVec.add_assoc]; rfl] at hpost1'
      subst hR'_def
      cases sd with
      | true =>
        have hd0 : d = 0#8 := hd_iff.mpr rfl
        subst hd0
        refine s5_out_add_np_evs hnpF ?_
        obtain ⟨s', hsteps, (⟨evs2, evs3, hevs2, hevs3, hok⟩ | ⟨hpan, hm⟩)⟩ :=
          pqRecv_recv_err_true_433_placed C A lim st_r ctl S fmtEnv H x trG tr st1 mkg draws
            (tokenInitPlacedAt ∗ R) s0
            hfits_fmt hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def
            sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
            htrace1 hvregs_1 hclf1 hLf1 hpost1'
        · refine ⟨s', hsteps, Or.inl ⟨(evs1 ++ evs2) ++ evs3,
            pqRecvEnv_of_err_parts hrecv hevs1 hevs2 hevs3, ?_⟩⟩
          simpa only [M.stepEvents_append, ↓reduceIte, Bool.false_eq_true] using hok
        · exact ⟨s', hsteps, Or.inr ⟨hpan, tryDecryptOnPanic_absorb hm⟩⟩
      | false =>
        have hd_ne : d ≠ 0#8 := fun h => Bool.noConfusion (hd_iff.mp h)
        refine s5_out_add_np_evs hnpF ?_
        obtain ⟨s', hsteps, (⟨evs2, evs3, hevs2, hevs3, hok⟩ | ⟨hpan, hm⟩)⟩ :=
          pqRecv_recv_err_false_433_placed C A lim st_r ctl S fmtEnv H x trG tr st1 mkg draws
            (tokenInitPlacedAt ∗ R) s0
            hfits_fmt hmsgW hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def hd_ne
            sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
            htrace1 hvregs_1 hclf1 hLf1 hpost1'
        · refine ⟨s', hsteps, Or.inl ⟨(evs1 ++ evs2) ++ evs3,
            pqRecvEnv_of_err_parts hrecv hevs1 hevs2 hevs3, ?_⟩⟩
          simpa only [M.stepEvents_append, ↓reduceIte, Bool.false_eq_true] using hok
        · exact ⟨s', hsteps, Or.inr ⟨hpan, tryDecryptOnPanic_absorb hm⟩⟩

/-! ## 4. Seam Instantiations from `SpqrV1PlacedSeams{,OfEnv}` -/

/-- Envelope-parametric `S5WTSeamPlaced` on CLI Block `433` at
    `Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))` from `SpqrV1PlacedSeamsOfEnv`. -/
theorem pqRecv_433_placed_ok_WT_of_seams_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtEnv : List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (ctl : BitVec 64)
    (hfmt_call : subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ lsFormatInnerSym) (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hdealloc_call : subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    S5WTSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (blkPl_434).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) RecvBytesEnv fmtEnv) := by
  have _ := instIsLsBlockProg_434 (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
  exact pqRecv_433_placed_ok_WT W.C A lim ctl (spqrV1 W.C.F W.Q.K)
    RecvBytesEnv fmtEnv (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecPlacedT
      (hS.spqrRecv_trTrap_at_block (i := 434)))
    hfmt_call hdealloc_call

/-- Default `SpqrRecvBytesEnv` `S5WTSeamPlaced` on CLI Block `433` at
    `Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))` from `SpqrV1PlacedSeams`,
    mirroring `SpqrRecvTrapV1Placed.pqRecv_433_placed_ok_WT_of_seams`. -/
theorem pqRecv_433_placed_ok_WT_of_seams [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hS : SpqrV1PlacedSeams M A lim mmpl gh W) (ctl : BitVec 64)
    {fmtEnv : List AllocEvent → Prop}
    (hfmt_call : subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ lsFormatInnerSym) (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hdealloc_call : subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    S5WTSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (blkPl_434).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) SpqrRecvBytesEnv fmtEnv) :=
  pqRecv_433_placed_ok_WT_of_seams_ofEnv hS ctl hfmt_call hdealloc_call

/-- Envelope-parametric `S5WTSeamPlaced` on CLI Block `433` at `cliGhostExterns gh (cliExternsPlaced mmpl W)`
    from `SpqrV1PlacedSeamsOfEnv` (used by `DecryptFrontTrapPlacedBudget.pqRecv_433_cli`). -/
theorem pqRecv_433_placed_ok_WT_cli_of_seams_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtEnv : List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (ctl : BitVec 64)
    (hfmt_call : subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsFormatInnerSym) (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hdealloc_call : subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    S5WTSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_434).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) RecvBytesEnv fmtEnv) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns gh (cliExternsPlaced mmpl W))
  exact pqRecv_433_placed_ok_WT W.C A lim ctl (spqrV1 W.C.F W.Q.K)
    RecvBytesEnv fmtEnv (cliGhostExterns gh (cliExternsPlaced mmpl W))
    (hS.spqrRecv_rawSpecPlacedT_at_block (i := 434))
    hfmt_call hdealloc_call

/-- Default `SpqrRecvBytesEnv` `S5WTSeamPlaced` on CLI Block `433` at `cliGhostExterns gh (cliExternsPlaced mmpl W)`
    from `SpqrV1PlacedSeams`. -/
theorem pqRecv_433_placed_ok_WT_cli_of_seams [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hS : SpqrV1PlacedSeams M A lim mmpl gh W) (ctl : BitVec 64)
    {fmtEnv : List AllocEvent → Prop}
    (hfmt_call : subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsFormatInnerSym) (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hdealloc_call : subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    S5WTSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_434).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) SpqrRecvBytesEnv fmtEnv) :=
  pqRecv_433_placed_ok_WT_cli_of_seams_ofEnv hS ctl hfmt_call hdealloc_call

end LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvTrapV1PlacedBudget
