/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlaced
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlaced

/-!
# Budget-Threaded Stage P2 Bad-KEM Callee & Store-Kit Bridges

Cross-block and `4K`-stack wrappers for budget-threaded `initialize_bob_session` Bad-KEM
contracts, together with budget-threaded Stage-P2 Bad-KEM spatial frames and `A.atState`
bridges.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement
  libsignalSessionLib ls_externAt?_blockProgram_eq_of_externs_eq
  lsLogFilterAddr lsMemcpySym lsProg_75 lsmpl
)
open CryptoVerification.RustHeap (vecAt)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded
  withLsCodeRoLoaded withLsFrozen
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost protocolAddressAt
)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionStateReprAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  IdentityStoreSpec KyberPreKeyStoreSpec PreKeyStoreSpec SignedPreKeyStoreSpec speWordsAt
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput HandshakeHdr Primitives StructuralPrims WellSizedAcceptKeysInput
  bytesToBv8 pqxdhEntryStack pqxdhEntryStackExt
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  PrimitivesMatchCrypto ls_subroutine_ok_withLsFrozen_of_block
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  decryptPrekeySavedRegsAt processPrekeyActive10At sessionRecordEmptyHeaderAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (p2_stackAt_split_of_le)
open CryptoVerification.SignalSession.Cli.RunProofs (pkVecTag?)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget (
  PqxdhPlacedHookContracts hookSat_framelessMemcpy_of_allocMemcpyVm
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (retagSignedPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (retagKyberPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (retagPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (retagIdentityStore)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  InitBobBadKemGhost bobParamsBadKemFieldsAt initBobBadKemErrOwnedAt
  p2BadKemMsgFieldsAt p2CoroScratchTailAt pqxdhBadKemErrPayloadAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget (
  AcceptBadKemEnv
  initializeBobSessionBadKemErrOwnedFrozenPlacedSpec
  initializeBobSessionBadKemErrOwnedInnerPlacedSpec
  initializeBobSessionBadKemErrOwnedPlacedSpec
  initializeBobSession_badKem_errOwned_frozen_placed_ok_of_accept
  initializeBobSession_badKem_errOwned_full_placed_ok
  initializeBobSession_badKem_errOwned_placed_ok_of_accept
  pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec
  pqxdhAcceptBadKemErrOwnedPlacedSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpySpec)

/-! ## 1. Re-exported & Cross-Block / `4K` `initialize_bob_session` Bad-KEM Contracts -/

export LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget (
  acceptBadKemEvents
  AcceptBadKemEnv
  fitsEnv_acceptBadKemEnv_iff
  pqxdhAcceptBadKemErrOwnedInnerPlacedSpec
  pqxdhAcceptBadKemErrOwnedPlacedSpec
  pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec
  pqxdhAccept_badKem_err_owned_placed_ok
  pqxdhAccept_badKem_err_owned_placed_ok_of_std
  pqxdhAccept_badKem_err_owned_placed_ok_of_block
  pqxdhAccept_badKem_err_owned_placed_ok_of_block_std
  pqxdhAccept_badKem_err_owned_full_placed_ok_of_block
  pqxdhAccept_badKem_err_owned_full_placed_ok_of_block_std
  initializeBobSessionBadKemErrOwnedInnerPlacedSpec
  initializeBobSessionBadKemErrOwnedPlacedSpec
  initializeBobSessionBadKemErrOwnedFrozenPlacedSpec
  initializeBobSession_badKem_errOwned_memInv_placed_ok_of_accept
  initializeBobSession_badKem_errOwned_placed_ok_of_accept
  initializeBobSession_badKem_errOwned_frozen_placed_ok_of_accept
  initializeBobSession_badKem_errOwned_full_placed_ok
  initializeBobSession_badKem_errOwned_full_placed_ok_std
)

theorem initializeBobSession_badKem_errOwned_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {H : LibsignalHooks} [hcaller : IsLsBlockProg callerProg i H]
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptBadKemErrOwnedPlacedSpec A lim AcceptErrEnv)) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwnedPlacedSpec A lim AcceptErrEnv) := by
  have hcallee := initializeBobSession_badKem_errOwned_placed_ok_of_accept h_accept
  have hcallee_prog : IsLsBlockProg (lsProg_75 H) 75 H := inferInstance
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcrl0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : (lsProg_75 H).CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸
      hcrl0.1 75 (by decide) (by decide) H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, (lsProg_75 H).externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : (lsProg_75 H).svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

theorem initializeBobSession_badKem_errOwned_frozen_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec A lim AcceptErrEnv)) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim AcceptErrEnv) :=
  ls_subroutine_ok_withLsFrozen_of_block
    (initializeBobSession_badKem_errOwned_frozen_placed_ok_of_accept h_accept)

/-- Closed `[LibsignalFullPlacement]` budget-threaded owned-error rejecting contract for
`initialize_bob_session` (Block `75`) on Bad-KEM lifted to any `callerProg` at `lsmpl.base 75`. -/
theorem initializeBobSession_badKem_errOwned_full_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim (AcceptBadKemEnv P)) :=
  ls_subroutine_ok_withLsFrozen_of_block
    (initializeBobSession_badKem_errOwned_full_placed_ok hWF hP hH h_memcpy)

theorem initializeBobSession_badKem_errOwned_full_placed_ok_of_block_std [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim (AcceptBadKemEnv P)) :=
  initializeBobSession_badKem_errOwned_full_placed_ok_of_block hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

/-- `4K`/`Ext` (`768 + pqxdhEntryStackExt`) stack variant of
`initializeBobSessionBadKemErrOwnedInnerPlacedSpec`. -/
def initializeBobSessionBadKemErrOwned4KInnerPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobBadKemGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧
      g.spkBPk.length = 32 ∧
      g.ctBytes.length < 2 ^ 63 ∧
      pkVecTag? 8#8 1568 g.ctBytes = none ∧
      FitsEnv M lim st (AcceptErrEnv g.inp)⌝ ∗
    bobParamsBadKemFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ctBytes g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + pqxdhEntryStackExt) ∗
    A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AcceptErrEnv g.inp evs⌝ ∗
      bobParamsBadKemFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
        g.inp g.ctBytes g.ikBPk g.spkBPk g.sameAccountByte ∗
      (initBobBadKemErrOwnedAt A.repAlloc g.outPtr ∗ anyHeap) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp (768 + pqxdhEntryStackExt) ∗
      A.pool lim (M.stepEvents evs st) sf

def initializeBobSessionBadKemErrOwned4KPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobBadKemGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (initializeBobSessionBadKemErrOwned4KInnerPlacedSpec A lim AcceptErrEnv)

abbrev initializeBobSessionBadKemErrOwnedExtPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobBadKemGhost × M.σ) :=
  initializeBobSessionBadKemErrOwned4KPlacedSpec A lim AcceptErrEnv

def initializeBobSessionBadKemErrOwned4KFrozenPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobBadKemGhost × M.σ) :=
  withLsFrozen lsmpl (initializeBobSessionBadKemErrOwned4KInnerPlacedSpec A lim AcceptErrEnv)

abbrev initializeBobSessionBadKemErrOwnedExtFrozenPlacedSpec [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobBadKemGhost × M.σ) :=
  initializeBobSessionBadKemErrOwned4KFrozenPlacedSpec A lim AcceptErrEnv

private theorem initializeBobSessionBadKemErrOwned_memInv_to_4K [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} {Φ : Memory → Prop}
    (h : subroutine_ok prog entry
      ({ initializeBobSessionBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv with
          pre := fun x s0 =>
            (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv).pre x s0 ∗
              ⌜Φ s0.mem⌝ })) :
    subroutine_ok prog entry
      ({ initializeBobSessionBadKemErrOwned4KInnerPlacedSpec A lim AcceptErrEnv with
          pre := fun x s0 =>
            (initializeBobSessionBadKemErrOwned4KInnerPlacedSpec A lim AcceptErrEnv).pre x s0 ∗
              ⌜Φ s0.mem⌝ }) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + pqxdhEntryStackExt))
      ((768 + pqxdhEntryStackExt) - (768 + pqxdhEntryStack))
  have hsplit := p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
    (768 + pqxdhEntryStack) (by decide) (by decide)
  have hpre' : s0.mem ⊨
      ((initializeBobSessionBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv).pre x s0 ∗
        ⌜Φ s0.mem⌝) ∗ (F_stk ∗ R) := by
    dsimp only [initializeBobSessionBadKemErrOwned4KInnerPlacedSpec,
      initializeBobSessionBadKemErrOwnedInnerPlacedSpec, F_stk] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.of_eq hpre (by sep_ac_rfl)
  refine h.mono_outcome x (F_stk ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hexit⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [initializeBobSessionBadKemErrOwnedInnerPlacedSpec,
      initializeBobSessionBadKemErrOwned4KInnerPlacedSpec, F_stk] at hpost ⊢
    simp only [sepExists_sepConj_left] at hpost ⊢
    refine Satisfies.mono (Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_) hpost
    rw [hsplit]
    exact Entails.of_eq (by sep_ac_rfl)
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hexit).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem initializeBobSessionBadKemErrOwnedPlacedSpec_to_4K [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (initializeBobSessionBadKemErrOwnedPlacedSpec A lim AcceptErrEnv)) :
    subroutine_ok prog entry
      (initializeBobSessionBadKemErrOwned4KPlacedSpec A lim AcceptErrEnv) :=
  initializeBobSessionBadKemErrOwned_memInv_to_4K (Φ := LibsignalCodeRoLoaded lsmpl) h

theorem initializeBobSessionBadKemErrOwnedFrozenPlacedSpec_to_4K [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim AcceptErrEnv)) :
    subroutine_ok prog entry
      (initializeBobSessionBadKemErrOwned4KFrozenPlacedSpec A lim AcceptErrEnv) :=
  initializeBobSessionBadKemErrOwned_memInv_to_4K (Φ := LibsignalFrozen lsmpl) h

/-- Closed `[LibsignalFullPlacement]` `4K` (`768 + pqxdhEntryStackExt`) contract for
`initialize_bob_session` (Block `75`) on Bad-KEM lifted to any `callerProg` at `lsmpl.base 75`. -/
theorem initializeBobSession_badKem_errOwned_4K_full_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwned4KFrozenPlacedSpec A lim (AcceptBadKemEnv P)) :=
  initializeBobSessionBadKemErrOwnedFrozenPlacedSpec_to_4K
    (initializeBobSession_badKem_errOwned_full_placed_ok_of_block hWF hP hH h_memcpy)

theorem initializeBobSession_badKem_errOwned_4K_full_placed_ok_of_block_std [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwned4KFrozenPlacedSpec A lim (AcceptBadKemEnv P)) :=
  initializeBobSessionBadKemErrOwnedFrozenPlacedSpec_to_4K
    (initializeBobSession_badKem_errOwned_full_placed_ok_of_block_std hWF hP hH h_memcpy)

/-! ## 2. Allocator-Independent Helpers & Spatial Lemmas -/

export LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  p2CoroScratchTailAt
  p2_pointsToBytes_entails_memRegion
  p2_pointsToBytes_split_head
  p2_pqsk_split_rejoin
  p2_coro398_cells8_4_eq_96
  p2_coro4f8_2cells_328_eq_344
  p2_sp3b0_8_40_eq_48
  p2_memRegion_a90_288_split_65_223
  opkOkSkBytes?
  mkP2AcceptKeysInput
  p2BadKemMsgFieldsAt
  bobParamsBadKemFieldsAt_intro
  p2_bobParamsBadKemFieldsAt_err_weaken
)

/-! ## 3. Budget-Threaded Stage P2 Bad-KEM Spatial Bundles & `A.atState` Bridges -/

/-- Empty `previous_sessions` `Vec<SessionStructure>` header at `coroPtr + 0xe0` over
`A.repAlloc`. -/
def prevSessionsEmptyAt {M : AllocCostModel} (A : RustCliAllocBudget M)
    (coroPtr : BitVec 64) (g : RecordGhost) : SepProp :=
  vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (coroPtr + 0xe0#64) g.prevCap g.prevPtr []

theorem prevSessionsEmptyAt_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (coroPtr : BitVec 64) (g : RecordGhost) :
    prevSessionsEmptyAt A coroPtr g =
      LibsignalBinary.Proofs.SignalSession.Cli.D3.prevSessionsEmptyAt A.repAlloc coroPtr g :=
  rfl

theorem prevSessionsEmptyAt_eq_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (coroPtr : BitVec 64) (g : RecordGhost) :
    prevSessionsEmptyAt A coroPtr g =
      LibsignalBinary.Proofs.SignalSession.Cli.D3.prevSessionsEmptyAt
        (A.atState lim st s) coroPtr g :=
  rfl

/-- Frame held constant across `stageP2_sub1_to_4_kits` and `Over.stageP2_over_sub1_to_4_kits`
when the Kyber ciphertext slice is `(ctBufPtr, ctBytes)`, indexed over `A.repAlloc`. -/
def p2BadKemSub1To4Frame {M : AllocCostModel} (A : RustCliAllocBudget M) {b : BitVec 64}
    (ikit : IdentityStoreSpec A.repAlloc b)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
     v_330 v_388 u_80 u_88 : BitVec 64)
    (stId : ikit.IdState) (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (msgVerByte : BitVec 8) (remoteRegId : BitVec 32)
    (gMe gPeer : AddrGhost) (Frame : SepProp) : SepProp :=
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 112#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 120#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 128#64) ↦₆₄ localAddrPtr) ∗
  memRegion (coroPtr + 664#64) 20 ∗
  ((coroPtr + 816#64) ↦₆₄ v_330) ∗
  ((coroPtr + 904#64) ↦₆₄ v_388) ∗
  memRegion (coroPtr + 1288#64) 328 ∗
  memRegion (coroPtr + 1616#64) 8 ∗
  memRegion (coroPtr + 1624#64) 298 ∗
  memRegion (coroPtr + 1928#64) 16 ∗
  memRegion (coroPtr + 1944#64) 64 ∗
  ((msgPtr + 112#64) ↦₈ msgVerByte) ∗
  ((msgPtr + 152#64) ↦₆₄ BitVec.ofNat 64 ctBytes.length) ∗
  ((msgPtr + 200#64) ↦ₛ bytesToBv8 hdr.ikAPk) ∗
  ((msgPtr + 232#64) ↦₃₂ remoteRegId) ∗
  (ctBufPtr ↦ₛ ctBytes) ∗
  protocolAddressAt A.repAlloc gMe localAddrPtr ∗
  protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
  ((sp + 128#64) ↦₆₄ u_80) ∗
  ((sp + 136#64) ↦₆₄ u_88) ∗
  memRegion (sp + 928#64) 8 ∗
  memRegion (sp + 940#64) 1 ∗
  memRegion (sp + 952#64) 40 ∗
  cells (sp + 1376#64) 4 ∗
  cells (sp + 1696#64) 4 ∗
  cells (sp + 2016#64) 4 ∗
  memRegion (sp + 2769#64) 223 ∗
  memRegion (fp + -128#64) 9 ∗
  Frame

theorem p2BadKemSub1To4Frame_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    {b : BitVec 64} (ikit : IdentityStoreSpec A.repAlloc b)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
     v_330 v_388 u_80 u_88 : BitVec 64)
    (stId : ikit.IdState) (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (msgVerByte : BitVec 8) (remoteRegId : BitVec 32)
    (gMe gPeer : AddrGhost) (Frame : SepProp) :
    p2BadKemSub1To4Frame A ikit
      sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
      v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame =
    LibsignalBinary.Proofs.SignalSession.Cli.D3.p2BadKemSub1To4Frame A.repAlloc ikit
      sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
      v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame :=
  rfl

theorem p2BadKemSub1To4Frame_eq_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {b : BitVec 64}
    (ikit : IdentityStoreSpec A.repAlloc b)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
     v_330 v_388 u_80 u_88 : BitVec 64)
    (stId : ikit.IdState) (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (msgVerByte : BitVec 8) (remoteRegId : BitVec 32)
    (gMe gPeer : AddrGhost) (Frame : SepProp) :
    p2BadKemSub1To4Frame A ikit
      sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
      v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame =
    LibsignalBinary.Proofs.SignalSession.Cli.D3.p2BadKemSub1To4Frame
      (A.atState lim st s) (retagIdentityStore ikit)
      sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
      v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame :=
  rfl

/-- Budget-threaded common coroutine, stack, message, address, and allocator spatial frame
delivered uniformly at `s0.readReg64 .x30` on all 5 Stage-P2 Bad-KEM error exits (Arms 1–5) under
`[LibsignalPlacement]`, carrying `A.pool lim st sf`. -/
def p2BadKemErrFrameAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 sf : State)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8)) (msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  ((coroPtr + 112#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 120#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 128#64) ↦₆₄ localAddrPtr) ∗
  memRegion (coroPtr + 224#64) 368 ∗
  cells (coroPtr + 592#64) 6 ∗
  memRegion (coroPtr + 664#64) 20 ∗
  ((coroPtr + 704#64) ↦₈ 1#8) ∗
  ((coroPtr + 816#64) ↦₆₄ v_330) ∗
  ((coroPtr + 904#64) ↦₆₄ v_388) ∗
  ((coroPtr + 912#64) ↦₈ 1#8) ∗
  memRegion (coroPtr + 920#64) 96 ∗
  processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt ∗
  memRegion (coroPtr + 1160#64) 8 ∗
  memRegion (coroPtr + 1200#64) 65 ∗
  ((coroPtr + 1265#64) ↦₈ 0#8) ∗
  ((coroPtr + 1266#64) ↦₈ 1#8) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2BadKemMsgFieldsAt msgPtr ctBufPtr hdr ctBytes msgVerByte
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A.repAlloc gMe localAddrPtr ∗
  protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
  memRegion (sp + 128#64) 88 ∗
  memRegion (sp + 624#64) 9 ∗
  memRegion (sp + 880#64) 36 ∗
  memRegion (sp + 928#64) 8 ∗
  memRegion (sp + 940#64) 1 ∗
  memRegion (sp + 944#64) 48 ∗
  memRegion (sp + 992#64) 368 ∗
  cells (sp + 1376#64) 4 ∗
  cells (sp + 1696#64) 4 ∗
  cells (sp + 2016#64) 4 ∗
  cells (sp + 2352#64) 8 ∗
  memRegion (sp + 2704#64) 288 ∗
  memRegion (fp + -128#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool lim st sf ∗
  stackAt sp stk ∗
  Frame

theorem p2BadKemErrFrameAtPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 sf : State)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8)) (msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    p2BadKemErrFrameAtPlaced A lim st s0 sf
      sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388
      hdr ctBytes msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      gMe gPeer stk Frame =
    LibsignalBinary.Proofs.SignalSession.Cli.D3.p2BadKemErrFrameAtPlaced
      (A.atState lim st sf) s0
      sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388
      hdr ctBytes msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      gMe gPeer stk Frame :=
  rfl

/-- Budget-threaded spatial precondition at `+2152` for `stageP2_pathA_badKem_kits_placed` (Path A)
under `[LibsignalPlacement]`, carrying `A.pool lim st s` and `A.repAlloc`-indexed store kits. -/
def stageP2BadKemPreAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (st : M.σ) (s0 s : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  spkKit.storeAt spkStorePtr stSpk ∗
  kpkKit.storeAt kyberStorePtr stKpk ∗
  pkKit.storeAt preKeyStorePtr stPk ∗
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 112#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 120#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 128#64) ↦₆₄ localAddrPtr) ∗
  sessionRecordEmptyHeaderAt (coroPtr + 224#64) ∗
  memRegion (coroPtr + 256#64) 336 ∗
  cells (coroPtr + 592#64) 6 ∗
  memRegion (coroPtr + 664#64) 20 ∗
  ((coroPtr + 704#64) ↦₈ b_2c0) ∗
  ((coroPtr + 816#64) ↦₆₄ v_330) ∗
  ((coroPtr + 904#64) ↦₆₄ v_388) ∗
  ((coroPtr + 912#64) ↦₈ b_390) ∗
  memRegion (coroPtr + 920#64) 96 ∗
  cells (coroPtr + 1016#64) 6 ∗
  cells (coroPtr + 1128#64) 4 ∗
  ((coroPtr + 1160#64) ↦₆₄ u_488) ∗
  ((coroPtr + 1200#64) ↦₈ b_4b0) ∗
  memRegion (coroPtr + 1201#64) 64 ∗
  ((coroPtr + 1265#64) ↦₈ b_4f1) ∗
  ((coroPtr + 1266#64) ↦₈ b_4f2) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2BadKemMsgFieldsAt msgPtr ctBufPtr hdr ctBytes msgVerByte
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A.repAlloc gMe localAddrPtr ∗
  protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
  ((sp + 128#64) ↦₆₄ u_80) ∗ ((sp + 136#64) ↦₆₄ u_88) ∗ ((sp + 144#64) ↦₆₄ u_90) ∗
  ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗
  ((sp + 168#64) ↦₆₄ u_a8) ∗ ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗
  ((sp + 184#64) ↦₆₄ u_b8) ∗ ((sp + 192#64) ↦₆₄ ctxPtr) ∗
  ((sp + 200#64) ↦₆₄ outPtr) ∗ ((sp + 208#64) ↦₆₄ u_d0) ∗
  memRegion (sp + 624#64) 9 ∗ memRegion (sp + 880#64) 36 ∗
  memRegion (sp + 928#64) 8 ∗ memRegion (sp + 940#64) 1 ∗
  memRegion (sp + 944#64) 48 ∗ memRegion (sp + 992#64) 368 ∗
  cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗
  cells (sp + 2016#64) 4 ∗ cells (sp + 2352#64) 8 ∗
  memRegion (sp + 2704#64) 288 ∗ memRegion (fp + -128#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
  memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool lim st s ∗ stackAt sp stk ∗ Frame

theorem stageP2BadKemPreAtPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (st : M.σ) (s0 s : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    stageP2BadKemPreAtPlaced A lim spkKit kpkKit pkKit ikit st s0 s
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr ctBytes msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer stk Frame =
    LibsignalBinary.Proofs.SignalSession.Cli.D3.stageP2BadKemPreAtPlaced
      (A.atState lim st s)
      (retagSignedPreKeyStore spkKit)
      (retagKyberPreKeyStore kpkKit)
      (retagPreKeyStore pkKit)
      (retagIdentityStore ikit)
      s0
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr ctBytes msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer stk Frame :=
  rfl

/-- Budget-threaded spatial precondition at `+2152` for `stageP2_over_badKem_kits_placed`
(Over-Path C) under `[LibsignalPlacement]`, carrying `A.pool lim st s` and `A.repAlloc`-indexed
store kits. -/
def stageP2OverBadKemPreAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (st : M.σ) (s0 s : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp) : SepProp :=
  spkKit.storeAt spkStorePtr stSpk ∗
  kpkKit.storeAt kyberStorePtr stKpk ∗
  pkKit.storeAt preKeyStorePtr stPk ∗
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 112#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 120#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 128#64) ↦₆₄ localAddrPtr) ∗
  prevSessionsEmptyAt A coroPtr g ∗
  sessionStateReprAt A.repAlloc (coroPtr + 248#64) recG sess ∗
  cells (coroPtr + 592#64) 6 ∗
  memRegion (coroPtr + 664#64) 20 ∗
  ((coroPtr + 704#64) ↦₈ b_2c0) ∗
  ((coroPtr + 816#64) ↦₆₄ v_330) ∗
  ((coroPtr + 904#64) ↦₆₄ v_388) ∗
  ((coroPtr + 912#64) ↦₈ b_390) ∗
  memRegion (coroPtr + 920#64) 96 ∗
  cells (coroPtr + 1016#64) 6 ∗
  cells (coroPtr + 1128#64) 4 ∗
  ((coroPtr + 1160#64) ↦₆₄ u_488) ∗
  ((coroPtr + 1200#64) ↦₈ b_4b0) ∗
  memRegion (coroPtr + 1201#64) 64 ∗
  ((coroPtr + 1265#64) ↦₈ b_4f1) ∗
  ((coroPtr + 1266#64) ↦₈ b_4f2) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2BadKemMsgFieldsAt msgPtr ctBufPtr hdr ctBytes msgVerByte
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A.repAlloc gMe localAddrPtr ∗
  protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
  ((sp + 128#64) ↦₆₄ u_80) ∗ ((sp + 136#64) ↦₆₄ u_88) ∗ ((sp + 144#64) ↦₆₄ u_90) ∗
  ((sp + 152#64) ↦₆₄ (coroPtr + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (coroPtr + 1266#64)) ∗
  ((sp + 168#64) ↦₆₄ u_a8) ∗ ((sp + 176#64) ↦₆₄ (coroPtr + 912#64)) ∗
  ((sp + 184#64) ↦₆₄ u_b8) ∗ ((sp + 192#64) ↦₆₄ ctxPtr) ∗
  ((sp + 200#64) ↦₆₄ outPtr) ∗ ((sp + 208#64) ↦₆₄ u_d0) ∗
  memRegion (sp + 624#64) 9 ∗ memRegion (sp + 880#64) 36 ∗
  memRegion (sp + 928#64) 8 ∗ memRegion (sp + 940#64) 1 ∗
  memRegion (sp + 944#64) 48 ∗ memRegion (sp + 992#64) 368 ∗
  cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗
  cells (sp + 2016#64) 4 ∗ cells (sp + 2352#64) 8 ∗
  memRegion (sp + 2704#64) 288 ∗ memRegion (fp + -128#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
  memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool lim st s ∗ stackAt sp stk ∗ Frame

theorem stageP2OverBadKemPreAtPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (ikit : IdentityStoreSpec A.repAlloc b)
    (st : M.σ) (s0 s : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8))
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp) :
    stageP2OverBadKemPreAtPlaced A lim spkKit kpkKit pkKit ikit st s0 s
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr ctBytes msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame =
    LibsignalBinary.Proofs.SignalSession.Cli.D3.stageP2OverBadKemPreAtPlaced
      (A.atState lim st s)
      (retagSignedPreKeyStore spkKit)
      (retagKyberPreKeyStore kpkKit)
      (retagPreKeyStore pkKit)
      (retagIdentityStore ikit)
      s0
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr ctBytes msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame :=
  rfl

/-- Unpack `initBobBadKemErrOwnedAt A.repAlloc (sp + 992#64)` into `speWordsAt`,
`pqxdhBadKemErrPayloadAt A.repAlloc`, and the trailing 288-byte `memRegion`. -/
theorem p2_initBobBadKemErrOwnedAt_unpack {M : AllocCostModel}
    (A : RustCliAllocBudget M) (sp : BitVec 64) :
    initBobBadKemErrOwnedAt A.repAlloc (sp + 992#64) ⊢
      ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        ⌜errTag ≠ -2#64 ∧ errTag ≠ -3#64⌝ ∗
        ((sp + 992#64) ↦₆₄ -1#64) ∗
        speWordsAt (sp + 1000#64) errTag w2 w3 w4 w5 w6 ∗
        pqxdhBadKemErrPayloadAt A.repAlloc errTag w2 w3 w4 ∗
        memRegion (sp + 1048#64) 288 :=
  LibsignalBinary.Proofs.SignalSession.Cli.D3.p2_initBobBadKemErrOwnedAt_unpack A.repAlloc sp

end LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget
