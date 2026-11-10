/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
meta import Lean -- shake: keep
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2Budget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2Placed
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import ProofLib.RegChain
import ProofLib.SepLogic.WP.Apply

/-!
# `HookSat` Sibling of `Initiate.LocalCalleesPlacedBudget` (`Initiate/LocalCalleesPlacedBudgetSat`)

Re-types all `RunHooksPlaced` theorems in
`LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget` over
`HooksPlacedBudget.RunHooksPlaced` (`hkdf : HkdfPlacedHooksExactSat W.C.F H`).
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudgetSat

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPC_40 blkPC_252
   blkPl_40 blkPl_252 libsignalMutatedBlocks lsRustNoAllocShimSym lsProg_40 lsProg_47
   lsProg_71 lsProg_200 ls_hook_ok_of_mem ls_hook_ok_ultra_of_mem ls_subroutine_ok_of_block lsmpl
   withLsCodeLoaded)
open CryptoVerification.CliHandshake.Placed (blkPC_523 blkPl_523 lsProg_512 lsProg_523)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims)
open CryptoVerification.E2E.Pqxdh.Initiator (lsProg_27 lsProg_30 lsProg_37)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (ofSignalPqxdhPrimitives primitivesMatchCrypto_modelPrims)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block
   subroutine_ok_withLsCodeRoLoaded_of_plain
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack memcpyName noAllocShimSpec uuidTryParseCodeSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (initProgPlaced stk_sub_ge_base transfer_withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.KemPubSerializeLocal2
  (kemPubSerFixedStk)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget
   RustLayoutOk VmPreserved rustAllocEvents subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomSpecWithStack subroutine_ok_rustCliAllocNoOom_withStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
  (handshakeKeysDerivePlacedBaseSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget
  (kemCiphertextSerializeSpec kemCiphertextSerialize_placed_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget
  (sessionStateNewPlacedSpec sessionStateNew_placed_ok withReceiverChainEmptyPlacedSpec
   withReceiverChain_empty_placed_ok withSenderChainNonePlacedSpec withSenderChain_none_placed_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesBudget
  (setKyberCiphertextNoneBudgetSpec setUnackKyberPreKeyIdBudgetSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
  (ct_eq_ro_placed_vm_ok_of_block pqxdhCalculateAgreement_placed_ok_of_block)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxSat
  (expand_multi_info_placed_vm_ok_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountBudget
  (isSameAccountDistinctSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget
  (isSameAccountEqDistinct_placed_ok_at)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5PlacedBudget
  (drop_session_structure5_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2Budget
  (kemPubSerializeFullAtStkSpec kemPubSerializeValAtStkSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced SubsetA4InitCalleesPlaced kemPubSerializeInnerSpec
   pqxdhCalculateAgreementPlacedInnerSpec promote_state_empty_placed_vm_ok
   spqrChainParamsBudgetSpec)
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
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
  (createChain_placed_ok createChain_placed_ok_x expandMultiInfoBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpec createChainSpecX)

/-! ## 1. Internal `RunHooksPlaced` Helper for Block `523` (`kem::Key<Public>::serialize [local#1]`) -/

section KemPubSerializeSat

private theorem stackAt_kemPubSerFixed_placed (sp : BitVec 64) :
    stackAt sp kemPubSerFixedStk =
      stackAt (sp - 48#64) extHookStack ∗ ProofLib.cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem memRegion_1569_split_placed (a : BitVec 64) :
    memRegion a 1569 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 1568 := by
  rw [show (1569 : Nat) = 1 + 1568 by decide,
    memRegion_split a 1 1568 (by decide), ProofLib.memRegion_one]

private theorem sp_sub_48_add_48_placed (sp : BitVec 64) : (sp - 48#64) + 48#64 = sp := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
local elab "erase_hkdf_norm" : command => Lean.Elab.Command.liftCoreM do
  for n in [``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase n `arm64_norm
erase_hkdf_norm
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit sp_sub_48_add_48_placed BitVec.toNat_zero

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1200000 in
private theorem kemPubKeySerialize_local2_fixed_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {W : CliHooks} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H) :
    subroutine_ok (lsProg_523 H) (blkPl_523).base
      (kemPubSerializeValAtStkSpec M A lim kemPubSerFixedStk) := by
  have hshim : subroutine_ok (lsProg_523 H) ((blkPl_523).ρ lsRustNoAllocShimSymCli)
      (withVmPreserved noAllocShimSpec) :=
    ls_hook_ok_ultra_of_mem hh.shim
  have halloc : subroutine_ok (lsProg_523 H) ((blkPl_523).ρ lsRustAllocSymCli)
      (rustCliAllocNoOomSpecWithStack M A lim false extHookStack) :=
    subroutine_ok_rustCliAllocNoOom_withStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_ultra_of_mem hh.rawAlloc))
  have hmemcpy : subroutine_ok (lsProg_523 H) ((blkPl_523).ρ memcpyName)
      sessionMemcpyRegionBudgetSpec :=
    ls_hook_ok_ultra_of_mem hh.sessionMemcpyRegion
  clear hh
  simp only [kemPubSerializeValAtStkSpec, stackAt_kemPubSerFixed_placed]
  cells_unfold
  dsimp only [lsProg_523] at hshim halloc hmemcpy ⊢
  wpp_init g s0
  obtain ⟨⟨boxPtr, pkBytes⟩, st⟩ := g
  dsimp only at *
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 1569 1 := ⟨by decide, hpow2, by decide⟩
  have hrlay : RustLayoutOk 1569 1 := ⟨hlay, by decide⟩
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool ((blkPl_523).ρ lsRustNoAllocShimSymCli)
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  have htr_sf : sf.trace = s0.trace := by reg_chain
  wp_steps_sync_pool ((blkPl_523).ρ lsRustAllocSymCli)
  wp_call halloc (1569, 1, st)
  have htr_sf1 : sf_1.trace = s0.trace :=
    (‹AllocCallPreserved _ sf_1›).2.1.trans htr_sf
  have _hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 Reg.x0 ≠ 0#64›
  simp only [memRegion_1569_split_placed, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists
  rename_i b0
  wp_steps_sync_pool ((blkPl_523).ρ memcpyName)
  wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, pkBytes)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [pointsToBytes_cons]
  wp_done

private theorem memRegion_bound_of_pointsTo64_placed {m : Memory} {b a v : BitVec 64} {n : Nat}
    {R : SepProp} (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

private theorem stackAt_sub_split_placed (sp : BitVec 64) {subStk topStk : Nat}
    (hle : subStk ≤ topStk) (hhi : topStk ≤ 2 ^ 64) :
    stackAt sp topStk =
      memRegion (sp - BitVec.ofNat 64 topStk) (topStk - subStk) ∗ stackAt sp subStk := by
  have heq : topStk = subStk + (topStk - subStk) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp subStk (topStk - subStk) (by omega), ← heq]

private theorem kemPubKeySerialize_local2_full_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {W : CliHooks} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H)
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_523 H) (lsmpl.base 523)
      (kemPubSerializeFullAtStkSpec M A lim stk) := by
  refine subroutine_ok.of_codeLoaded fun ((keyRef, kpkPtr, kpk), st) R s0 hpc hrun hpre hsp _hL => ?_
  have hle : kemPubSerFixedStk ≤ stk := by
    dsimp [kemPubSerFixedStk]; omega
  have hbound_mem : s0.mem ⊨ memRegion (s0.sp - BitVec.ofNat 64 stk) stk ∗
      ((keyRef ↦₆₄ kpkPtr) ∗
       (⌜s0.readReg64 .x0 = kpkPtr ∧ s0.readReg64 .x1 = 1568#64 ∧ kpk.length = 1568 ∧
          FitsEvents M lim st (rustAllocEvents 1569 1)⌝ ∗
        ((keyRef + 8#64) ↦₆₄ 1568#64) ∗ (kpkPtr ↦ₛ kpk) ∗ A.pool lim st s0 ∗ R)) := by
    dsimp only [kemPubSerializeFullAtStkSpec, stackAt] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  have hhi : stk ≤ 2 ^ 64 := memRegion_bound_of_pointsTo64_placed hbound_mem
  have hsplit := stackAt_sub_split_placed s0.sp hle hhi
  let F : SepProp :=
    (keyRef ↦₆₄ kpkPtr) ∗ ((keyRef + 8#64) ↦₆₄ 1568#64) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kemPubSerFixedStk)
  have hpre' : s0.mem ⊨ (kemPubSerializeValAtStkSpec M A lim kemPubSerFixedStk).pre
      ((kpkPtr, kpk), st) s0 ∗ (F ∗ R) := by
    dsimp only [kemPubSerializeFullAtStkSpec, kemPubSerializeValAtStkSpec, F] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine (kemPubKeySerialize_local2_fixed_placed_ok_sat hh).mono_outcome ((kpkPtr, kpk), st) (F ∗ R) s0
    hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_hpan, hpost⟩ | ⟨_code, _hex, hpost⟩ | ⟨_hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [kemPubSerializeFullAtStkSpec, kemPubSerializeValAtStkSpec, F] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · dsimp only [kemPubSerializeValAtStkSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact hpost.1.elim
  · exact (allowPanic_not_exited hpost).elim
  · dsimp only [kemPubSerializeValAtStkSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact hpost.1.elim

private theorem kemPubKeySerialize_local2_full_rocl_ok_sat [LibsignalPlacement]
    {prog : Program} {i : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {W : CliHooks} {H : LibsignalHooks}
    [IsLsBlockProg prog i H]
    (hh : RunHooksPlaced W A lim H)
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 523)
      (withLsCodeRoLoaded lsmpl (kemPubSerializeFullAtStkSpec M A lim stk)) := by
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeRoLoaded_of_plain
      (kemPubKeySerialize_local2_full_placed_ok_sat hh hstk)) hi
  exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsRoCl, withLsCodeRoLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

end KemPubSerializeSat

public section

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (SubsetA4InitCalleesPlaced InitLocalCalleesPlaced)

/-! ## 2. Local, Subset A4/A5, & `Run/Slots` Callee Transfer Theorems onto `initProgPlaced mmpl gh W` -/

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

/-- Local handshake callee #1: `<kem::Key<Public>>::serialize [local#1]` (Block `523`). -/
theorem kemPublicKeySerialize_local2_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 523)
      (withLsCodeRoLoaded lsmpl (kemPubSerializeInnerSpec A lim stk)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  exact (kemPubKeySerialize_local2_full_rocl_ok_sat (prog := initProgPlaced mmpl gh W) hh hstk).mono_outcome
    ((x.keyRef, x.kpkPtr, x.kpk), st) R s0 hpc hrun hpre hsp (fun _ hout => hout)

/-- Local handshake callee #2: `core::ptr::drop_glue::<SessionStructure> [local#4]` (Block `512`). -/
theorem dropSessionStructure_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
      (withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  transfer_tr_codeLoaded
    (calleeProg := lsProg_512 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (drop_session_structure5_placed_ok hh.rawDealloc)

/-- Row 3 helper: discharge `isSameAccount` (Block `17`) on `initProgPlaced mmpl gh W` from a Block-`252`
`uuidTryParse` witness via `RecvWireSameAccountPlacedBudget.isSameAccountEqDistinct_placed_ok_at`. -/
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

/-- Row 3b: `<PrivateKey>::calculate_agreement` (Block `207`), proved unconditionally from
`CryptoBridgePlacedBudget.pqxdhCalculateAgreement_placed_ok_of_block`. -/
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

/-- Row 4: `<curve25519::PrivateKey>::derive_public_key_bytes` (Block `200`). -/
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

/-- Row 5: `<HandshakeKeys>::derive` (Block `59`) from `handshakeKeysDerive_placed_ok`. -/
theorem handshakeDerive_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitStateEnv : Params → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl
        (handshakeKeysDerivePlacedBaseSpec M
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim)) :=
  LocalCalleesPlacedBudget.handshakeDerive_cli_placed_ok mmpl gh W X ha4

/-- Row 6: `<kem::Ciphertext>::serialize` (Block `71`). -/
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
    {spec : Spec α} (h : HookSat H sym spec.keepsFs) : HookSat H sym spec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · dsimp only [Spec.keepsFs] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hkf, hsym, Or.inl ⟨hret, hcc, hpost.2⟩⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

/-- Row 7: `<RootKey>::create_chain` (Block `40`) at `createChainStack`. -/
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

/-- Row 7b: `<RootKey>::create_chain` (Block `40`) at `createChainStackX`. -/
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

/-- Row 8: `spqr_chain_params` (Block `74`). -/
theorem spqrChainParams_cli_placed_ok [LibsignalPlacement] (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 74)
      (withLsCodeRoLoaded lsmpl spqrChainParamsBudgetSpec) :=
  LocalCalleesPlacedBudget.spqrChainParams_cli_placed_ok mmpl gh W

/-- Row 10: `<SessionState>::new` (Block `37`). -/
theorem sessionStateNew_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 37)
      (withLsCodeRoLoaded lsmpl (sessionStateNewPlacedSpec M A lim)) :=
  transfer_tr_codeLoaded
    (calleeProg := lsProg_37 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (sessionStateNew_placed_ok hh.shimVm hh.rawAlloc)

/-- Row 11: `<SessionState>::with_receiver_chain` (Block `30`). -/
theorem withReceiverChain_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 30)
      (withLsCodeRoLoaded lsmpl (withReceiverChainEmptyPlacedSpec M A lim)) :=
  transfer_tr_codeLoaded
    (calleeProg := lsProg_30 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (withReceiverChain_empty_placed_ok hh.shimVm hh.rawAlloc hh.rawDealloc hh.allocMemcpyVm)

/-- Row 12: `<SessionState>::with_sender_chain` (Block `27`). -/
theorem withSenderChain_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 27)
      (withLsCodeRoLoaded lsmpl (withSenderChainNonePlacedSpec M A lim)) :=
  transfer_tr_codeLoaded
    (calleeProg := lsProg_27 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (withSenderChain_none_placed_ok hh.shimVm hh.rawAlloc hh.rawDealloc hh.allocMemcpyVm)

/-- Row 13: `<SessionState>::set_kyber_ciphertext` (Block `31`). -/
theorem setKyberCiphertext_cli_placed_ok [LibsignalPlacement] (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 31)
      (withLsCodeRoLoaded lsmpl setKyberCiphertextNoneBudgetSpec) :=
  LocalCalleesPlacedBudget.setKyberCiphertext_cli_placed_ok mmpl gh W

/-- Row 14: `<SessionState>::set_unacknowledged_pre_key_message` (Block `33`) at `UNIX_EPOCH`,
proved unconditionally from `SetUnackEpochPlacedBudget.setUnackPreKeyMsg_exact_stack_epoch_placed_at_block`. -/
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

/-- Row 15: `<SessionState>::set_unacknowledged_kyber_pre_key_id` (Block `34`). -/
theorem setUnackKyberId_cli_placed_ok [LibsignalPlacement] (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 34)
      (withLsCodeRoLoaded lsmpl setUnackKyberPreKeyIdBudgetSpec) :=
  LocalCalleesPlacedBudget.setUnackKyberId_cli_placed_ok mmpl gh W

/-- Row 16: `<SessionRecord>::promote_state` (Block `47`). -/
theorem promoteState_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 47)
      (withLsCodeRoLoaded lsmpl promoteStateEmptyBudgetSpec) :=
  transfer_tr_codeLoaded
    (calleeProg := lsProg_47 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (promote_state_empty_placed_vm_ok (cliGhostExterns gh (cliExternsPlaced mmpl W)) hh.framelessMemcpy)

/-! ## 3. Bundled Budget Local & Pure E2E Callees on `initProgPlaced mmpl gh W` under `RunHooksPlaced` -/

/-- `RunHooksPlaced` sibling of `LocalCalleesPlacedBudget.initLocalCallees_placed_ok`. -/
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

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudgetSat
