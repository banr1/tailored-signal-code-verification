/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Local and E2E Callees for `initiate`

Transfers the 18 local handshake, PQXDH, TripleRatchet, and SPQR callees onto `initProgPlaced mmpl gh W`
(`lsProg_521`) over `RustCliAllocBudget M` and `VmPreserved`, wrapped in `withLsCodeRoLoaded lsmpl`
and bundled into `InitLocalCalleesPlaced`. Includes `VmPreserved` block proofs for `spqr_chain_params`
(block `74`) and empty-archive `promote_state` (blocks `51` and `47`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkLib_eq_47 blkPC_40
   blkPC_47 blkPC_51 blkPC_59 blkPC_74 blkPC_252 blkPl_40 blkPl_47 blkPl_51 blkPl_59 blkPl_74
   blkPl_252 libsignalMutatedBlocks lsMemcpySym lsPubFromSecretSym lsRustNoAllocShimSym
   lsProg_31 lsProg_34 lsProg_40 lsProg_47 lsProg_59 lsProg_71 lsProg_74 lsProg_200
   ls_hook_ok_of_mem ls_subroutine_ok_of_block lsmpl lsρ sepWP_seq_lscl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.CliHandshake.Placed (lsProg_512 lsProg_523)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims)
open CryptoVerification.E2E.Pqxdh (spqrChainParamsSpec)
open CryptoVerification.E2E.Pqxdh.Initiator
  (lsProg_27 lsProg_30 lsProg_37 readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre structuralPrims_initiatorModelPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (ofSignalPqxdhPrimitives primitivesMatchCrypto_modelPrims)
open CryptoVerification.E2E.Pqxdh.ResponderStore
  (archiveCurrentStateInnerEmptySpec pointsTo64_memRegion_336_entails_344 promoteStateEmptySpec)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchet
  (HkdfPlacedHooks extHookStack framelessMemcpySpec noAllocShimSpec uuidTryParseCodeSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (KemPubSerializeGhost VerifySignatureGhost initProgPlaced stk_sub_ge_base
   transfer_withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget VmPreserved
   rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
  (PqxdhHkdfExpandMultiInfoPlacedOk PqxdhHkdfExtractPlacedOk handshakeKeysDerivePlacedBaseSpec
   handshakeKeysDerive_placed_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget
  (kemCiphertextSerializeSpec kemCiphertextSerialize_placed_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget
  (sessionStateNewPlacedSpec sessionStateNew_placed_ok withReceiverChainEmptyPlacedSpec
   withReceiverChain_empty_placed_ok withSenderChainNonePlacedSpec withSenderChain_none_placed_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesBudget
  (setKyberCiphertextNoneBudgetSpec setKyberCiphertext_none_placed_ok
   setUnackKyberPreKeyIdBudgetSpec setUnackKyberPreKeyId_placed_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
  (ct_eq_ro_placed_vm_ok_of_block expand_multi_info_placed_vm_ok
   pqxdhCalculateAgreementPlacedBaseSpec pqxdhCalculateAgreement_placed_ok_of_block)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxSat
  (expand_multi_info_placed_vm_ok_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountBudget
  (isSameAccountDistinctSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget
  (isSameAccountEqDistinct_placed_ok_at)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5PlacedBudget
  (drop_session_structure5_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2PlacedBudget
  (kemPubKeySerialize_local2_full_rocl_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlacedBudget
  (spqrInitialStateInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
  (promoteStateEmptyBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget
  (cliExternsPlaced_durationSinceEpochAlloc_budget_sat setUnackPreKeyMsgEpochInnerSpec
   setUnackPreKeyMsg_exact_stack_epoch_placed_at_block)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (derivePublicKeyBytesSpec noAllocShimBudgetSpec
   subroutine_ok_derivePublicKeyBytes_of_withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytesBudget
  (derive_public_key_bytes_placed_ok_of_contract)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
  (dropSessionStructureLocal2Spec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
  (createChain_placed_ok createChain_placed_ok_x expandMultiInfoBudgetSpec extractBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpec createChainSpecX)
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlacedBudget
  (spqrInitialStateInnerSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
  (promoteStateEmptyBudgetSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget
  (setUnackPreKeyMsgEpochInnerSpec)

/-! ## Budget-threaded and `VmPreserved` inner specifications -/

/-- Budget-threaded inner specification of `<kem::Key<Public>>::serialize [local#1]` (block `523`). -/
def kemPubSerializeInnerSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (KemPubSerializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.kpkPtr ∧ s.readReg64 .x1 = 1568#64 ∧ x.kpk.length = 1568 ∧
      FitsEvents M lim st (rustAllocEvents 1569 1)⌝ ∗
      (x.keyRef ↦₆₄ x.kpkPtr) ∗ ((x.keyRef + 8#64) ↦₆₄ 1568#64) ∗
      (x.kpkPtr ↦ₛ x.kpk) ∗ A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.readReg64 .x1 = 1569#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) 1569 1 ∗
      ((sf.readReg64 .x0) ↦ₛ (0x08#8 :: x.kpk)) ∗
      (x.keyRef ↦₆₄ x.kpkPtr) ∗ ((x.keyRef + 8#64) ↦₆₄ 1568#64) ∗
      (x.kpkPtr ↦ₛ x.kpk) ∗
      A.pool lim (M.stepEvents (rustAllocEvents 1569 1) st) sf ∗ stackAt s0.sp stk

/-- `VmPreserved`-strengthened inner specification of `<PublicKey>::verify_signature` (block `203`). -/
def verifySignatureInnerSpec (P : SignalPqxdh.Primitives) : Spec VerifySignatureGhost :=
  withVmPreserved (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.verifySignatureInnerSpec P)

/-- Budget-threaded inner specification of `<PrivateKey>::calculate_agreement` (block `207`). -/
abbrev pqxdhCalculateAgreementPlacedInnerSpec {M : AllocCostModel} (P : SignalPqxdh.Primitives)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × List UInt8 × BitVec 64 × List UInt8 × BitVec 64 × BitVec 64) × M.σ) :=
  pqxdhCalculateAgreementPlacedBaseSpec M (ofSignalPqxdhPrimitives P) A lim

/-- `VmPreserved`-strengthened contract for `spqr_chain_params` (block `74`). -/
def spqrChainParamsBudgetSpec : Spec (BitVec 32) :=
  withVmPreserved spqrChainParamsSpec

/-! ## `VmPreserved` block proofs for `spqr_chain_params` and `promote_state` -/

private theorem subroutine_ok_withVmPreserved_intro {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.mem ⊨ spec.pre x s0 ∗ R → s0.spAligned →
      SepWP prog (s0.readReg64 .x30) s0 (spec.pre x s0)
        (fun sf P_f => VmPreserved s0 sf ∧
          ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
           sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    subroutine_ok prog entry (withVmPreserved spec) := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hal => ⟨spec.pre x s0, R, hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hpre hal) fun sf P_f _ _ hpost => ?_
  rcases hpost with ⟨hvm, hq, hsp, hcs⟩
  refine ⟨fun hm => ?_, hsp, hcs⟩
  dsimp only [withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm, hq hm⟩

private theorem hookSat_noAllocShimBudget_of_withVmPreserved {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

/-- Relocatable `VmPreserved` verification of `spqr_chain_params` (block `74`). -/
theorem spqrChainParams_placed_vm_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_74).rebase (blkPl_74).base H) (blkPl_74).base
      spqrChainParamsBudgetSpec := by
  apply subroutine_ok_withVmPreserved_intro
  intro v R s0 hpc hrun hpre hsp_align
  dsimp only [spqrChainParamsSpec] at *
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨rfl, _⟩
  simp only [pure_true]
  by_vm_steps (wp_steps; wp_done)

/-- Relocatable `VmPreserved` verification of `<SessionRecord>::archive_current_state_inner` on an empty session (block `51`). -/
theorem archive_current_state_inner_empty_placed_vm_ok [LibsignalPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_51).rebase (blkPl_51).base H) (blkPl_51).base
      (withVmPreserved archiveCurrentStateInnerEmptySpec) := by
  apply subroutine_ok_withVmPreserved_intro
  intro recPtr R s0 hpc hrun hpre hsp_align
  dsimp only [archiveCurrentStateInnerEmptySpec] at *
  cells_unfold
  by_vm_steps (
    wp_pull_exists
    refine SepWP.pure_elim ?_
    rintro rfl
    wp_steps
    wp_done
  )

section PromoteStateVm

private theorem promote_state_memcpy_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hmemcpy : HookSat H lsMemcpySym (withVmPreserved framelessMemcpySpec)) :
    subroutine_ok ((blkPC_47).rebase (blkPl_47).base H) (lsρ lsMemcpySym)
      (withVmPreserved framelessMemcpySpec) :=
  ls_hook_ok_of_mem (prog := lsProg_47 H) hmemcpy

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl

private theorem cells_sub32_4_merge (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
    ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      cells (sp - 32#64) 4 := by
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) := by
    cells_unfold
  rw [hc4]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

/-- Relocatable `VmPreserved` verification of `<SessionRecord>::promote_state` on empty archived sessions (block `47`). -/
theorem promote_state_empty_placed_vm_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hmemcpy : HookSat H lsMemcpySym (withVmPreserved framelessMemcpySpec)) :
    subroutine_ok ((blkPC_47).rebase (blkPl_47).base H) (blkPl_47).base
      (withLsCodeLoaded lsmpl promoteStateEmptyBudgetSpec) := by
  have harch0 : subroutine_ok ((blkPC_51).rebase (blkPl_51).base H) (blkPl_51).base
      (withLsCodeLoaded lsmpl (withVmPreserved archiveCurrentStateInnerEmptySpec)) :=
    subroutine_ok_withLsCodeLoaded_of_plain (archive_current_state_inner_empty_placed_vm_ok H)
  have harch : subroutine_ok ((blkPC_47).rebase (blkPl_47).base H) (lsmpl.base 51)
      (withLsCodeLoaded lsmpl (withVmPreserved archiveCurrentStateInnerEmptySpec)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_47 H) harch0 (by decide) (by decide) (by decide)
  have hmc := promote_state_memcpy_ok H hmemcpy
  unfold promoteStateEmptyBudgetSpec
  unfold withLsCodeLoaded withVmPreserved at harch ⊢
  unfold withVmPreserved at hmc
  dsimp only [archiveCurrentStateInnerEmptySpec, framelessMemcpySpec, promoteStateEmptySpec]
    at harch hmc ⊢
  clear harch0
  wp_init x s0
  obtain ⟨recPtr, srcPtr, bs⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 (.gpr 0#5) = recPtr := by assumption
  have hx1 : s0.readReg64 (.gpr 1#5) = srcPtr := by assumption
  have hbs_len : bs.length = 344 := by assumption
  subst hx0 hx1
  have hc4 : cells (s0.sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((s0.sp - 32#64) ↦₆₄ v0) ∗ ((s0.sp - 24#64) ↦₆₄ v1) ∗
        ((s0.sp - 16#64) ↦₆₄ v2) ∗ ((s0.sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [hc4]
  simp only [sepExists_sepConj_right]
  wp_pull_exists
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 51)
  apply sepWP_seg_ls_vm (Q := (blkPC_47).rebase (blkPl_47).base (hooksException H))
    blkLib_eq_47 (mid := lsmpl.base 51)
  intro _m_s1
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_r1 hnsp1 => ?_
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl1 => ?_
  have hvm1 : VmPreserved s0 _ := hnsp1.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm1 hcl1 ⊢
  have hsp_sub : s0.sp - 32#64 - 64#64 = s0.sp - 96#64 := by bv_arith
  wp_call harch (s0.readReg64 (.gpr 0#5))
  have hvm_arch : VmPreserved s0 sf := hvm1.trans ‹_›
  apply sepWP_seg_ls_vm (Q := (blkPC_47).rebase (blkPl_47).base (hooksException H))
    blkLib_eq_47 (mid := lsρ lsMemcpySym)
  intro _m_s2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_r2 hnsp2 => ?_
  have hvm2 : VmPreserved sf _ := hnsp2.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm2 ⊢
  have hvm_pre_mc : VmPreserved s0 _ := hvm_arch.trans hvm2
  apply SepWP.replace_pre (by sep_focus)
    (pointsTo64_memRegion_336_entails_344 (s0.readReg64 (.gpr 0#5)) 0xffffffffffffffff#64)
  apply SepWP.replace_pre (by sep_focus)
    (cells_sub32_4_merge s0.sp _ _ _ _)
  rw [← hbs_len]
  wp_call hmc (s0.readReg64 (.gpr 0#5) + 0x18#64, s0.readReg64 (.gpr 1#5), bs)
  rw [hbs_len] at *
  have hvm_final : VmPreserved s0 sf_1 := hvm_pre_mc.trans ‹_›
  simp only [sepConj_assoc, *] at *
  wp_done

end PromoteStateVm

/-! ## External callee bundle (`SubsetA4InitCalleesPlaced`) -/

/-- Bundle of external `verify_signature`, `is_same_account`, `spqr::initial_state`, and HKDF leaf contracts for `initLocalCallees_placed_ok`. -/
structure SubsetA4InitCalleesPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitStateEnv : Params → List AllocEvent → Prop) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop where
  verifySignature : ∀ (X : UnreachedPqxdhPrimitives),
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims X ⟨W.C, W.Q⟩)))
  isSameAccount :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 17)
      (withLsCodeRoLoaded lsmpl (isSameAccountDistinctSpec A.repAlloc uuidTryParse))
  spqrInitialState :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A lim InitStateEnv W.C.F))
  pqxdhHkdfExtract : ∀ (X : UnreachedPqxdhPrimitives),
    PqxdhHkdfExtractPlacedOk (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      ((blkPC_59).rebase (blkPl_59).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
  pqxdhHkdfExpand : ∀ (X : UnreachedPqxdhPrimitives),
    PqxdhHkdfExpandMultiInfoPlacedOk (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      ((blkPC_59).rebase (blkPl_59).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
  hkdfExtract40 :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractBudgetSpec W.C.F))

/-! ## Callee transfer theorems onto `initProgPlaced` -/

private theorem transfer_tr_codeLoaded [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [IsLsBlockProg calleeProg j (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (initProgPlaced mmpl gh W) entry (withLsCodeRoLoaded lsmpl spec) := by
  have hcrl : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee
  exact transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hcrl (by decide) hj hj_unmut

private theorem transfer_tr_codeRoLoaded [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [IsLsBlockProg calleeProg j (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (initProgPlaced mmpl gh W) entry (withLsCodeRoLoaded lsmpl spec) := by
  have hcrl : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec) :=
    subroutine_ok_mono hcallee
      (fun _ _ _ hp => by
        obtain ⟨hc, hpre⟩ := extract_withLsCodeRoLoaded hp
        dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        exact ⟨⟨hc.1, hc.2⟩, hpre⟩)
      (fun _ _ _ _ hq => hq)
  exact transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hcrl (by decide) hj hj_unmut

private theorem transfer_plain_block [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [IsLsBlockProg calleeProg j (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry spec)
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (initProgPlaced mmpl gh W) entry (withLsCodeRoLoaded lsmpl spec) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hcallee)
    (by decide) hj hj_unmut

/-- `<kem::Key<Public>>::serialize [local#1]` (block `523`) on `initProgPlaced`. -/
theorem kemPublicKeySerialize_local2_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 523)
      (withLsCodeRoLoaded lsmpl (kemPubSerializeInnerSpec A lim stk)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  exact (kemPubKeySerialize_local2_full_rocl_ok (prog := initProgPlaced mmpl gh W) hh hstk).mono_outcome
    ((x.keyRef, x.kpkPtr, x.kpk), st) R s0 hpc hrun hpre hsp (fun _ hout => hout)

/-- `core::ptr::drop_glue::<SessionStructure> [local#4]` (block `512`) on `initProgPlaced`. -/
theorem dropSessionStructure_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
      (withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  transfer_tr_codeLoaded
    (calleeProg := lsProg_512 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (drop_session_structure5_placed_ok hh.rawDealloc)

/-- Discharges `isSameAccount` (block `17`) on `initProgPlaced` from a block-`252` `uuidTryParse` witness. -/
theorem isSameAccount_cli_placed_ok_of_uuidTryParse [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_252).base (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse)))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 17)
      (withLsCodeRoLoaded lsmpl (isSameAccountDistinctSpec A.repAlloc uuidTryParse)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (isSameAccountEqDistinct_placed_ok_at A.repAlloc (callerProg := initProgPlaced mmpl gh W)
      hh.blackBox huuid)

/-- `<PrivateKey>::calculate_agreement` (block `207`) on `initProgPlaced`. -/
theorem calculateAgreement_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (X : UnreachedPqxdhPrimitives) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl
        (pqxdhCalculateAgreementPlacedInnerSpec (modelPrims X ⟨W.C, W.Q⟩) A lim)) := by
  have h207 := pqxdhCalculateAgreement_placed_ok_of_block
    (callerProg := initProgPlaced mmpl gh W) (i := 521)
    (primitivesMatchCrypto_modelPrims X ⟨W.C, W.Q⟩)
    hh.dh hh.sharedDrop hh.blackBox
    (hookSat_noAllocShimBudget_of_withVmPreserved hh.shim)
    hh.rawAlloc hh.staticDrop (by decide)
  exact subroutine_ok_mono h207
    (fun _ _ _ hp => by
      obtain ⟨hc, hpre⟩ := extract_withLsCodeRoLoaded hp
      dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨⟨hc.1, hc.2⟩, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-- `<curve25519::PrivateKey>::derive_public_key_bytes` (block `200`) on `initProgPlaced`. -/
theorem derivePubKeyBytes_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 200)
      (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesSpec W.C.pubKey)) :=
  transfer_plain_block
    (calleeProg := lsProg_200 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (derive_public_key_bytes_placed_ok_of_contract
      (subroutine_ok_derivePublicKeyBytes_of_withVmPreserved
        (ls_hook_ok_of_mem (prog := lsProg_200 (cliGhostExterns gh (cliExternsPlaced mmpl W))) hh.pubFromSecret)))

/-- `<HandshakeKeys>::derive` (block `59`) on `initProgPlaced`. -/
theorem handshakeDerive_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitStateEnv : Params → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl
        (handshakeKeysDerivePlacedBaseSpec M
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim)) :=
  transfer_tr_codeRoLoaded
    (calleeProg := lsProg_59 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (handshakeKeysDerive_placed_ok
      (structuralPrims_initiatorModelPrims X ⟨W.C, W.Q⟩)
      (ha4.pqxdhHkdfExtract X) (ha4.pqxdhHkdfExpand X))

/-- `<kem::Ciphertext>::serialize` (block `71`) on `initProgPlaced`. -/
theorem kemCtSerialize_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 71)
      (withLsCodeRoLoaded lsmpl (kemCiphertextSerializeSpec M A lim)) :=
  transfer_plain_block
    (calleeProg := lsProg_71 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (kemCiphertextSerialize_placed_ok hh.shimVm hh.rawAlloc hh.allocMemcpyVm)

private theorem hookSat_of_keepsFs {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (h : HookSat H sym spec.keepsFs) :
    HookSat H sym spec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Arm64.Spec.keepsFs] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr hrest

/-- `<RootKey>::create_chain` (block `40`) at `createChainStack` on `initProgPlaced`. -/
theorem rootKeyCreateChain_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitStateEnv : Params → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpec M A lim W.C)) := by
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) := hh.hkdf
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat (hookSat_of_keepsFs hh.memsetRegionKeepsFs)
  have hct207 := ct_eq_ro_placed_vm_ok_of_block
    (callerProg := (CryptoVerification.blkPC_207).rebase
      (CryptoVerification.blkPl_207).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    hh.blackBox (by decide)
  have hexp53 : subroutine_ok
      (CryptoVerification.LibsignalTripleRatchet.lsProg_53 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoBudgetSpec W.C.F)) :=
    expand_multi_info_placed_vm_ok_sat W.C (cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hexp40 : subroutine_ok
      ((blkPC_40).rebase (blkPl_40).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoBudgetSpec W.C.F)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_40 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      hexp53 (by decide) (by decide) (by decide)
  exact transfer_tr_codeRoLoaded
    (calleeProg := lsProg_40 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (createChain_placed_ok hh.dh hh.sharedDrop hct207
      (hookSat_noAllocShimBudget_of_withVmPreserved hh.shim)
      hh.rawAlloc hh.staticDrop ha4.hkdfExtract40 hexp40 hh.rawDealloc)

/-- `<RootKey>::create_chain` (block `40`) at `createChainStackX` on `initProgPlaced`. -/
theorem rootKeyCreateChainX_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitStateEnv : Params → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim W.C)) := by
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) := hh.hkdf
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat (hookSat_of_keepsFs hh.memsetRegionKeepsFs)
  have hct207 := ct_eq_ro_placed_vm_ok_of_block
    (callerProg := (CryptoVerification.blkPC_207).rebase
      (CryptoVerification.blkPl_207).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    hh.blackBox (by decide)
  have hexp53 : subroutine_ok
      (CryptoVerification.LibsignalTripleRatchet.lsProg_53 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoBudgetSpec W.C.F)) :=
    expand_multi_info_placed_vm_ok_sat W.C (cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hexp40 : subroutine_ok
      ((blkPC_40).rebase (blkPl_40).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoBudgetSpec W.C.F)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_40 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      hexp53 (by decide) (by decide) (by decide)
  exact transfer_tr_codeRoLoaded
    (calleeProg := lsProg_40 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (createChain_placed_ok_x hh.dh hh.sharedDrop hct207
      (hookSat_noAllocShimBudget_of_withVmPreserved hh.shim)
      hh.rawAlloc hh.staticDrop ha4.hkdfExtract40 hexp40 hh.rawDealloc)

/-- `spqr_chain_params` (block `74`) on `initProgPlaced`. -/
theorem spqrChainParams_cli_placed_ok [LibsignalPlacement] (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 74)
      (withLsCodeRoLoaded lsmpl spqrChainParamsBudgetSpec) :=
  transfer_plain_block
    (calleeProg := lsProg_74 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (spqrChainParams_placed_vm_ok (cliGhostExterns gh (cliExternsPlaced mmpl W)))

/-- `<SessionState>::new` (block `37`) on `initProgPlaced`. -/
theorem sessionStateNew_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 37)
      (withLsCodeRoLoaded lsmpl (sessionStateNewPlacedSpec M A lim)) :=
  transfer_tr_codeLoaded
    (calleeProg := lsProg_37 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (sessionStateNew_placed_ok hh.shimVm hh.rawAlloc)

/-- `<SessionState>::with_receiver_chain` (block `30`) on `initProgPlaced`. -/
theorem withReceiverChain_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 30)
      (withLsCodeRoLoaded lsmpl (withReceiverChainEmptyPlacedSpec M A lim)) :=
  transfer_tr_codeLoaded
    (calleeProg := lsProg_30 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (withReceiverChain_empty_placed_ok hh.shimVm hh.rawAlloc hh.rawDealloc hh.allocMemcpyVm)

/-- `<SessionState>::with_sender_chain` (block `27`) on `initProgPlaced`. -/
theorem withSenderChain_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 27)
      (withLsCodeRoLoaded lsmpl (withSenderChainNonePlacedSpec M A lim)) :=
  transfer_tr_codeLoaded
    (calleeProg := lsProg_27 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (withSenderChain_none_placed_ok hh.shimVm hh.rawAlloc hh.rawDealloc hh.allocMemcpyVm)

/-- `<SessionState>::set_kyber_ciphertext` (block `31`) on `initProgPlaced`. -/
theorem setKyberCiphertext_cli_placed_ok [LibsignalPlacement] (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 31)
      (withLsCodeRoLoaded lsmpl setKyberCiphertextNoneBudgetSpec) :=
  transfer_plain_block
    (calleeProg := lsProg_31 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (setKyberCiphertext_none_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W)))

/-- `<SessionState>::set_unacknowledged_pre_key_message` at `UNIX_EPOCH` (block `33`) on `initProgPlaced`. -/
theorem setUnackPreKeyMsg_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 33)
      (withLsCodeRoLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A lim)) :=
  setUnackPreKeyMsg_exact_stack_epoch_placed_at_block (callerProg := initProgPlaced mmpl gh W) (i := 521)
    hh.sessionShim hh.rawAlloc hh.rawDealloc hh.sessionMemcpyRegion
    (CryptoVerification.SignalSession.Cli.Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_durationSinceEpochAlloc_budget_sat mmpl W)) (by decide)

/-- `<SessionState>::set_unacknowledged_kyber_pre_key_id` (block `34`) on `initProgPlaced`. -/
theorem setUnackKyberId_cli_placed_ok [LibsignalPlacement] (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 34)
      (withLsCodeRoLoaded lsmpl setUnackKyberPreKeyIdBudgetSpec) :=
  transfer_plain_block
    (calleeProg := lsProg_34 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (setUnackKyberPreKeyId_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W)))

/-- `<SessionRecord>::promote_state` (block `47`) on `initProgPlaced`. -/
theorem promoteState_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 47)
      (withLsCodeRoLoaded lsmpl promoteStateEmptyBudgetSpec) :=
  transfer_tr_codeLoaded
    (calleeProg := lsProg_47 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (promote_state_empty_placed_vm_ok (cliGhostExterns gh (cliExternsPlaced mmpl W)) hh.framelessMemcpy)

/-! ## Bundled budget-threaded local and E2E callees (`InitLocalCalleesPlaced`) -/

/-- Budget-threaded relocatable bundle of all 18 local, PQXDH, TripleRatchet, and SPQR callees on `initProgPlaced`. -/
structure InitLocalCalleesPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitStateEnv : Params → List AllocEvent → Prop)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (stk : Nat) : Prop where
  kemPubSerialize : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 523)
    (withLsCodeRoLoaded lsmpl (kemPubSerializeInnerSpec A lim (stk - cliInitiateFrame)))
  dropSessionStructure : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
    (withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec M A lim))
  verifySignature : ∀ (X : UnreachedPqxdhPrimitives),
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims X ⟨W.C, W.Q⟩)))
  isSameAccount : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 17)
    (withLsCodeRoLoaded lsmpl (isSameAccountDistinctSpec A.repAlloc uuidTryParse))
  calculateAgreement : ∀ (X : UnreachedPqxdhPrimitives),
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl
        (pqxdhCalculateAgreementPlacedInnerSpec (modelPrims X ⟨W.C, W.Q⟩) A lim))
  derivePubKeyBytes : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 200)
    (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesSpec W.C.pubKey))
  handshakeDerive : ∀ (X : UnreachedPqxdhPrimitives),
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl
        (handshakeKeysDerivePlacedBaseSpec M
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim))
  kemCtSerialize : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 71)
    (withLsCodeRoLoaded lsmpl (kemCiphertextSerializeSpec M A lim))
  rootKeyCreateChain : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 40)
    (withLsCodeRoLoaded lsmpl (createChainSpec M A lim W.C))
  rootKeyCreateChainX : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 40)
    (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim W.C))
  spqrChainParams : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 74)
    (withLsCodeRoLoaded lsmpl spqrChainParamsBudgetSpec)
  spqrInitialState : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 327)
    (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A lim InitStateEnv W.C.F))
  sessionStateNew : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 37)
    (withLsCodeRoLoaded lsmpl (sessionStateNewPlacedSpec M A lim))
  withReceiverChain : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 30)
    (withLsCodeRoLoaded lsmpl (withReceiverChainEmptyPlacedSpec M A lim))
  withSenderChain : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 27)
    (withLsCodeRoLoaded lsmpl (withSenderChainNonePlacedSpec M A lim))
  setKyberCiphertext : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 31)
    (withLsCodeRoLoaded lsmpl setKyberCiphertextNoneBudgetSpec)
  setUnackPreKeyMsg : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 33)
    (withLsCodeRoLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A lim))
  setUnackKyberId : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 34)
    (withLsCodeRoLoaded lsmpl setUnackKyberPreKeyIdBudgetSpec)
  promoteState : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 47)
    (withLsCodeRoLoaded lsmpl promoteStateEmptyBudgetSpec)

/-- Assembles budget-threaded `InitLocalCalleesPlaced` on `initProgPlaced`. -/
theorem initLocalCallees_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitStateEnv : Params → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk := by
  exact
    { kemPubSerialize := kemPublicKeySerialize_local2_placed_ok mmpl gh W hh (by
        have h1 := stk_sub_ge_base hstk
        have hext : extHookStack ≤ 65536 := by decide
        omega)
      dropSessionStructure := dropSessionStructure_cli_placed_ok mmpl gh W hh
      verifySignature := ha4.verifySignature
      isSameAccount := ha4.isSameAccount
      calculateAgreement := calculateAgreement_cli_placed_ok mmpl gh W hh
      derivePubKeyBytes := derivePubKeyBytes_cli_placed_ok mmpl gh W hh
      handshakeDerive := fun X => handshakeDerive_cli_placed_ok mmpl gh W X ha4
      kemCtSerialize := kemCtSerialize_cli_placed_ok mmpl gh W hh
      rootKeyCreateChain := rootKeyCreateChain_cli_placed_ok mmpl gh W hh ha4
      rootKeyCreateChainX := rootKeyCreateChainX_cli_placed_ok mmpl gh W hh ha4
      spqrChainParams := spqrChainParams_cli_placed_ok mmpl gh W
      spqrInitialState := ha4.spqrInitialState
      sessionStateNew := sessionStateNew_cli_placed_ok mmpl gh W hh
      withReceiverChain := withReceiverChain_cli_placed_ok mmpl gh W hh
      withSenderChain := withSenderChain_cli_placed_ok mmpl gh W hh
      setKyberCiphertext := setKyberCiphertext_cli_placed_ok mmpl gh W
      setUnackPreKeyMsg := setUnackPreKeyMsg_cli_placed_ok mmpl gh W hh
      setUnackKyberId := setUnackKyberId_cli_placed_ok mmpl gh W
      promoteState := promoteState_cli_placed_ok mmpl gh W hh }

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
