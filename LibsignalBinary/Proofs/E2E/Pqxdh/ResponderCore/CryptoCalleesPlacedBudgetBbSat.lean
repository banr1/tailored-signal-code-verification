/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqROSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `HookSat`-backed `black_box` Sibling of `CryptoCalleesPlacedBudget{,Sat}` (`CryptoCalleesPlacedBudgetBbSat`)

Stacks `blackBox : HookSat H lsBlackBoxU8Sym blackBoxSpecSat` on top of
`CryptoCalleesPlacedBudgetSat` (`hkdf : HkdfPlacedHooksBudgetSat C.F H` kept by type without
projecting `.memcpy`):
- `calculateAgreement_placed_ok{,_x}_unconditional_sat`
- `pqxdhCalculateAgreement_placed_ok_sat`, `pqxdhCalculateAgreement_placed_{ok,frozen_ok}_of_block_sat`
- `createChain_placed_ok{,_x}_{unconditional,of_block}_sat`
- `PqxdhPlacedHookContractsBbSat`, `PqxdhPlacedHookContractsSat.toBbSat`,
  `PqxdhPlacedHookContracts.toBbSat`, and all 8 bundle projections.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetBbSat

open Arm64 ProofLib SepProp BitVec
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.Ratchet (X25519Fn)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement
   blkPC_207 blkPC_40 blkPl_207 blkPl_40 lsBlackBoxU8Sym lsRustDeallocSym
   ls_subroutine_ok_of_block lsmpl withLsCodeLoaded)
open CryptoVerification.E2E (u8Vec)
open CryptoVerification.E2E.Pqxdh.Initiator
  (Bytes Primitives StructuralPrims bytesToBv8)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PrimitivesMatchCrypto calculateAgreementResultAt_entails_pqxdh
   lsDalekMontToEdSym lsDalekTorsionFreeSym lsKyberDecapsSym
   u8Vec_toList_of_length)
open CryptoVerification.LibsignalTripleRatchet
  (CalculateAgreementGhost LibsignalCodeRoLoaded calculateAgreement
   calculateAgreementResultAt calculateAgreementStack diffieHellmanSpec
   extract_withLsCodeRoLoaded keys_ls_hook_ok_of_mem
   keys_ls_subroutine_ok_of_block_cro withLsCodeRoLoaded zeroizeSecretSpec)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (lsDhSym lsRustAllocSym lsRustNoAllocShimSym lsSharedDropSym lsStaticDropSym)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomExternSpecWithStack subroutine_ok_rustCliAllocNoOom_externWithStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpecSat hookSat_blackBox_of_eq)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
  (PqxdhHkdfExpandMultiInfoPlacedOk PqxdhHkdfExtractPlacedOk
   handshakeKeysDerivePlacedBaseSpec handshakeKeysDerivePlacedVmSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (calculateAgreementEvents)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
  (PqxdhCalculateAgreementPlacedFrozenOk PqxdhCalculateAgreementPlacedOk
   calculateAgreementEvents_eq pqxdhCalculateAgreementPlacedBaseSpec
   pqxdhCalculateAgreement_placed_frozen_of_cro)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
  (expand_multi_info_placed_vm_ok_of_other_block_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
  (PqxdhPlacedHookContracts cryptoBoolRegStubBudgetSpec dalekMontToEdStubBudgetSpec
   kyberDecapsStubBudgetSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (PqxdhPlacedHookContractsSat extract_placed_vm_ok_of_other_block_sat
   handshakeKeysDerive_placed_ok_of_block_sat handshakeKeysDerive_placed_vm_ok_of_block_sat
   pqxdhHkdfExpandMultiInfo_placed_ok_sat pqxdhHkdfExtract_placed_ok_sat)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqROSat
  (ctEqSliceROMemBudgetSpec16 ctEqSliceROMemSpec16
   ct_eq_ro_mem_placed_vm_ok_16_withLsCodeLoaded_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudget
  (allocPlacedCallSpec calculateAgreement_placed_ok_of_hooks_gen ctEqPlacedCallSpec
   dhPlacedCallSpec shimPlacedCallSpec
   subroutine_ok_calculateAgreementSpecX_of_calculateAgreementSpec zeroizePlacedCallSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
  (createChain_placed_ok_of_contracts subroutine_ok_createChainSpecX_of_createChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
  (CalculateAgreementEnv calculateAgreementSpec calculateAgreementSpecWithStack
   calculateAgreementSpecX createChainSpec createChainSpecX)

private theorem dhPlacedCallAt_of_raw {pl : Obj.MultiPlacement} {X : X25519Fn}
    {subStack : Nat} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withVmPreserved (diffieHellmanSpec X))) :
    subroutine_ok prog entry (dhPlacedCallSpec pl X subStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨secA, sec, pubA, pub, ret, sp⟩ R s0 hpre
  dsimp only [dhPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hx8, hsp⟩, hpre⟩
  subst hsp
  refine ⟨(secA, sec, pubA, pub, ret), stackAt s0.sp subStack ∗ R, ?_, ?_⟩
  · dsimp only [withVmPreserved, diffieHellmanSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withVmPreserved, diffieHellmanSpec, dhPlacedCallSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    exact ⟨⟨htr, hvm⟩, by arm64_sep_close⟩

private theorem zeroizePlacedCallAt_of_raw {pl : Obj.MultiPlacement} {subStack : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withVmPreserved zeroizeSecretSpec)) :
    subroutine_ok prog entry (zeroizePlacedCallSpec pl subStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨a, sp⟩ R s0 hpre
  dsimp only [zeroizePlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hsp⟩, hpre⟩
  subst hsp
  refine ⟨a, stackAt s0.sp subStack ∗ R, ?_, ?_⟩
  · dsimp only [withVmPreserved, zeroizeSecretSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withVmPreserved, zeroizeSecretSpec, zeroizePlacedCallSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    exact ⟨⟨htr, hvm⟩, by arm64_sep_close⟩

private theorem shimPlacedCallAt_of_raw {pl : Obj.MultiPlacement} {subStack : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry noAllocShimBudgetSpec) :
    subroutine_ok prog entry (shimPlacedCallSpec pl subStack) := by
  refine subroutine_ok_map h ?_
  rintro sp R s0 hpre
  dsimp only [shimPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hsp⟩, hpre⟩
  refine ⟨(), stackAt sp subStack ∗ R, ?_, ?_⟩
  · change s0.mem ⊨ emp ∗ (stackAt sp subStack ∗ R)
    simpa only [emp_sepConj] using hpre
  · intro sf hpost
    change sf.mem ⊨ ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ (stackAt sp subStack ∗ R) at hpost
    dsimp only [shimPlacedCallSpec]
    rwa [sepConj_assoc]

private theorem allocPlacedCallAt_of_allocStack [LibsignalPlacement] {pl : Obj.MultiPlacement}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok prog entry (allocPlacedCallSpec pl M A lim allocHookStack) := by
  have hno : subroutine_ok prog entry
      (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget h)
  refine subroutine_ok_map hno ?_
  rintro ⟨size, align, st, sp⟩ R s0 hpre
  dsimp only [allocPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hlay, hal_le, hfits, hsp, hlr_ls⟩, hpre⟩
  subst hsp
  refine ⟨(size, align, st), R, ?_, ?_⟩
  · dsimp only [rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
      LibsignalBinary.Heap.RustLayoutOk]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, ⟨hlay, hal_le⟩, hfits, hlr_ls⟩, by convert hpre using 1⟩
  · intro sf hpost
    dsimp only [rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
      allocPlacedCallSpec] at hpost ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨htr, hne0, hmod⟩, hpost⟩
    exact ⟨⟨hne0, hmod, htr⟩, by convert hpost using 1; sep_ac_rfl⟩

private theorem stackAt_allocHookStack_eq_mem64 (sp : BitVec 64) :
    stackAt sp allocHookStack =
      memRegion (sp - 64#64) 64 ∗ stackAt (sp - 64#64) 4032 := by
  rw [sepConj_comm]
  simp only [stackAt, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 4096) (n := 4032) (k := 64)
    (b' := sp - 64#64) rfl (by bv_omega) (by decide)]
  have hsub : sp - 64#64 - BitVec.ofNat 64 4032 = sp - BitVec.ofNat 64 4096 := by bv_omega
  rw [hsub]

/-- Lift `withLsCodeLoaded pl ctEqSliceROMemBudgetSpec16` (`64` B) to
`AgreeBudget.ctEqPlacedCallSpec pl allocHookStack` (`4096` B). -/
theorem ctEqPlacedCallAt_of_mem16_withLsCodeLoaded {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl ctEqSliceROMemBudgetSpec16)) :
    subroutine_ok prog entry (ctEqPlacedCallSpec pl allocHookStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  dsimp only [ctEqPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfr, hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  refine ⟨(p1, k1, p2, k2, sp), stackAt (sp - 64#64) 4032 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeLoaded, ctEqSliceROMemBudgetSpec16, withVmPreserved, ctEqSliceROMemSpec16]
    rw [stackAt_allocHookStack_eq_mem64 sp] at hpre
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr.1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hsp, hk1, hk2⟩, by simpa only [sepConj_assoc] using hpre⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, ctEqSliceROMemBudgetSpec16, withVmPreserved, ctEqSliceROMemSpec16,
      ctEqPlacedCallSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, ⟨hres, htr⟩, hpost⟩
    refine ⟨⟨by rw [hres]; split <;> rfl, htr, hvm⟩, ?_⟩
    rw [stackAt_allocHookStack_eq_mem64 sp]
    simpa only [sepConj_assoc] using hpost

/-! ## 1. Budget-Threaded `<PrivateKey>::calculate_agreement` (Block `207`) under `blackBoxSpecSat` -/

/-- `HookSat` `black_box` sibling of `CryptoBridgePlacedBudget.calculateAgreement_placed_ok_unconditional`
(`CryptoBridgePlacedBudget.lean:117`). -/
theorem calculateAgreement_placed_ok_unconditional_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : X25519Fn} {H : LibsignalHooks}
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpec M A lim X)) := by
  have hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROMemBudgetSpec16) :=
    ls_subroutine_ok_of_block (ct_eq_ro_mem_placed_vm_ok_16_withLsCodeLoaded_sat h_bb)
  exact calculateAgreement_placed_ok_of_hooks_gen (subStack := allocHookStack) (by decide)
    (dhPlacedCallAt_of_raw (keys_ls_hook_ok_of_mem (i := 207) h_dh))
    (zeroizePlacedCallAt_of_raw (keys_ls_hook_ok_of_mem (i := 207) h_shdrop))
    (ctEqPlacedCallAt_of_mem16_withLsCodeLoaded hct)
    (shimPlacedCallAt_of_raw (keys_ls_hook_ok_of_mem (i := 207) h_shim))
    (allocPlacedCallAt_of_allocStack (keys_ls_hook_ok_of_mem (i := 207) h_alloc))
    (zeroizePlacedCallAt_of_raw (keys_ls_hook_ok_of_mem (i := 207) h_stdrop))

/-- `HookSat` `black_box` sibling of `CryptoBridgePlacedBudget.calculateAgreement_placed_ok_x_unconditional`
(`CryptoBridgePlacedBudget.lean:132`). -/
theorem calculateAgreement_placed_ok_x_unconditional_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : X25519Fn} {H : LibsignalHooks}
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpecX M A lim X)) :=
  subroutine_ok_calculateAgreementSpecX_of_calculateAgreementSpec
    (calculateAgreement_placed_ok_unconditional_sat h_dh h_shdrop h_bb h_shim h_alloc h_stdrop)

/-- `HookSat` `black_box` sibling of `CryptoBridgePlacedBudget.pqxdhCalculateAgreement_placed_ok`
(`CryptoBridgePlacedBudget.lean:233`). -/
theorem pqxdhCalculateAgreement_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {H : LibsignalHooks}
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)) :
    PqxdhCalculateAgreementPlacedOk M P A lim ((blkPC_207).rebase (blkPl_207).base H) := by
  unfold PqxdhCalculateAgreementPlacedOk
  have hraw :=
    calculateAgreement_placed_ok_unconditional_sat h_dh h_shdrop h_bb h_shim h_alloc h_stdrop
  refine subroutine_ok_map hraw ?_
  rintro ⟨⟨ourA, ourSk32, theirA, theirPk32, ret, sp⟩, st⟩ R s0 hpre
  obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [pqxdhCalculateAgreementPlacedBaseSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hsp_eq, hour, htheir, hfits⟩, hpre⟩
  let xg : CalculateAgreementGhost := ⟨ourA, ⟨u8Vec 32 ourSk32⟩, theirA, ⟨u8Vec 32 theirPk32⟩, ret⟩
  have hour_list : xg.our.bytes.toList = bytesToBv8 ourSk32 := u8Vec_toList_of_length hour
  have htheir_list : xg.their.bytes.toList = bytesToBv8 theirPk32 := u8Vec_toList_of_length htheir
  have hevs_eq :
      LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementEvents C.X xg =
        calculateAgreementEvents P ourSk32 theirPk32 :=
    calculateAgreementEvents_eq hP ourA ourSk32 theirA theirPk32 ret
  have hfits_env : FitsEnv M lim st (CalculateAgreementEnv C.X xg) := by
    intro evs hevs
    rw [CalculateAgreementEnv, hevs_eq] at hevs
    subst hevs
    exact hfits
  refine ⟨(xg, st), R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, calculateAgreementSpec, calculateAgreementSpecWithStack]
    rw [hour_list, htheir_list, hsp_eq]
    have hcomm :
        ((⌜s0.readReg64 .x0 = xg.ourA ∧ s0.readReg64 .x1 = xg.theirA ∧ s0.readReg64 .x8 = xg.ret ∧
            FitsEnv M lim st (CalculateAgreementEnv C.X xg)⌝ ∗
          (xg.ourA ↦ₛ bytesToBv8 ourSk32) ∗ (xg.theirA ↦ₛ bytesToBv8 theirPk32) ∗
          memRegion xg.ret 24 ∗ A.pool lim st s0 ∗ stackAt sp calculateAgreementStack) ∗
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = xg.ourA ∧ s0.readReg64 .x1 = xg.theirA ∧ s0.readReg64 .x8 = xg.ret ∧
              FitsEnv M lim st (CalculateAgreementEnv C.X xg)⌝ ∗
            ((xg.ourA ↦ₛ bytesToBv8 ourSk32) ∗ ((xg.theirA ↦ₛ bytesToBv8 theirPk32) ∗
              (memRegion xg.ret 24 ∗ (A.pool lim st s0 ∗
                (stackAt sp calculateAgreementStack ∗ R)))))) := by
      sep_ac_rfl
    rw [hcomm, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hfr, ⟨hx0, hx1, hx8, hfits_env⟩, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, calculateAgreementSpec, calculateAgreementSpecWithStack,
      pqxdhCalculateAgreementPlacedBaseSpec] at hpost ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [hour_list, htheir_list, hsp_eq] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨htr, hevs⟩, hpost⟩
    rw [CalculateAgreementEnv, hevs_eq] at hevs
    subst hevs
    refine ⟨htr, ?_⟩
    have hE := calculateAgreementResultAt_entails_pqxdh hP A.repAlloc ret ourSk32 theirPk32
    have hq1 : sf.mem ⊨
        calculateAgreementResultAt A.repAlloc ret (calculateAgreement C.X xg.their xg.our) ∗
          ((ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
            A.pool lim (M.stepEvents (calculateAgreementEvents P ourSk32 theirPk32) st) sf ∗
            stackAt sp calculateAgreementStack ∗ R) := by
      ac_nf at hpost ⊢
    have hq2 := Satisfies.mono (sepConj_mono_left hE) hq1
    ac_nf at hq2 ⊢

/-- `HookSat` `black_box` sibling of `CryptoBridgePlacedBudget.pqxdhCalculateAgreement_placed_ok_of_block`
(`CryptoBridgePlacedBudget.lean:307`). -/
theorem pqxdhCalculateAgreement_placed_ok_of_block_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M P A lim callerProg :=
  keys_ls_subroutine_ok_of_block_cro
    (pqxdhCalculateAgreement_placed_ok_sat hP h_dh h_shdrop h_bb h_shim h_alloc h_stdrop)
    hi (by decide) (by decide)

/-- `HookSat` `black_box` sibling of `CryptoBridgePlacedBudget.pqxdhCalculateAgreement_placed_frozen_ok_of_block`
(`CryptoBridgePlacedBudget.lean:356`). -/
theorem pqxdhCalculateAgreement_placed_frozen_ok_of_block_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_frozen_of_cro
    (pqxdhCalculateAgreement_placed_ok_of_block_sat hP h_dh h_shdrop h_bb h_shim h_alloc h_stdrop hi)

/-! ## 2. Budget-Threaded `<RootKey>::create_chain` (Block `40`) & `PqxdhPlacedHookContractsBbSat` -/

/-- `HookSat` `black_box` + `HkdfPlacedHooksBudgetSat` sibling of
`createChain_placed_ok_unconditional` (`CryptoCalleesPlacedBudget.lean:478`). -/
theorem createChain_placed_ok_unconditional_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooksBudgetSat C.F H]
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)) :=
  createChain_placed_ok_of_contracts
    (keys_ls_subroutine_ok_of_block_cro
      (calculateAgreement_placed_ok_unconditional_sat h_dh h_shdrop h_bb h_shim h_alloc h_stdrop))
    (extract_placed_vm_ok_of_other_block_sat C H)
    (expand_multi_info_placed_vm_ok_of_other_block_sat C H)
    (keys_ls_hook_ok_of_mem h_dealloc)

/-- `HookSat` `black_box` + `HkdfPlacedHooksBudgetSat` sibling of
`createChain_placed_ok_of_block` (`CryptoCalleesPlacedBudget.lean:499`). -/
theorem createChain_placed_ok_of_block_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksBudgetSat C.F H]
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)) :=
  keys_ls_subroutine_ok_of_block_cro
    (createChain_placed_ok_unconditional_sat h_dh h_shdrop h_bb h_shim h_alloc h_stdrop h_dealloc)
    hi (by decide) (by decide)

/-- `HookSat` `black_box` + `HkdfPlacedHooksBudgetSat` sibling of
`createChain_placed_ok_x_unconditional` (`CryptoCalleesPlacedBudget.lean:520`). -/
theorem createChain_placed_ok_x_unconditional_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooksBudgetSat C.F H]
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)) :=
  subroutine_ok_createChainSpecX_of_createChainSpec
    (createChain_placed_ok_unconditional_sat h_dh h_shdrop h_bb h_shim h_alloc h_stdrop h_dealloc)

/-- `HookSat` `black_box` + `HkdfPlacedHooksBudgetSat` sibling of
`createChain_placed_ok_x_of_block` (`CryptoCalleesPlacedBudget.lean:537`). -/
theorem createChain_placed_ok_x_of_block_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksBudgetSat C.F H]
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)) :=
  keys_ls_subroutine_ok_of_block_cro
    (createChain_placed_ok_x_unconditional_sat h_dh h_shdrop h_bb h_shim h_alloc h_stdrop h_dealloc)
    hi (by decide) (by decide)

/-- `HookSat`-backed `black_box` sibling stacked on `CryptoCalleesPlacedBudgetSat.PqxdhPlacedHookContractsSat`
(`hkdf : HkdfPlacedHooksBudgetSat C.F H` kept by type). -/
structure PqxdhPlacedHookContractsBbSat [LibsignalPlacement] (M : AllocCostModel) (P : Primitives)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  hkdf             : HkdfPlacedHooksBudgetSat C.F H
  dh               : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X))
  sharedDrop       : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec)
  staticDrop       : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)
  blackBox         : HookSat H lsBlackBoxU8Sym blackBoxSpecSat
  noAllocShim      : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec
  alloc            : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc          : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  kyberDecaps      : HookSat H lsKyberDecapsSym (kyberDecapsStubBudgetSpec P)
  dalekMontToEd    : HookSat H lsDalekMontToEdSym (dalekMontToEdStubBudgetSpec P)
  dalekTorsionFree : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubBudgetSpec P.isTorsionFree 160)

/-- Bridge from `CryptoCalleesPlacedBudgetSat.PqxdhPlacedHookContractsSat` to
`PqxdhPlacedHookContractsBbSat` (weakening only `blackBox` via `hookSat_blackBox_of_eq`, keeping
`hkdf` by type). -/
theorem PqxdhPlacedHookContractsSat.toBbSat [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : PqxdhPlacedHookContractsSat M P C A lim H) :
    PqxdhPlacedHookContractsBbSat M P C A lim H :=
  { hkdf             := h.hkdf
    dh               := h.dh
    sharedDrop       := h.sharedDrop
    staticDrop       := h.staticDrop
    blackBox         := hookSat_blackBox_of_eq h.blackBox
    noAllocShim      := h.noAllocShim
    alloc            := h.alloc
    dealloc          := h.dealloc
    kyberDecaps      := h.kyberDecaps
    dalekMontToEd    := h.dalekMontToEd
    dalekTorsionFree := h.dalekTorsionFree }

/-- Exact-to-`HookSat` bridge from budget `PqxdhPlacedHookContracts`
(`CryptoCalleesPlacedBudget.lean:577`) to `PqxdhPlacedHookContractsBbSat`. -/
theorem PqxdhPlacedHookContracts.toBbSat [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : PqxdhPlacedHookContracts M P C A lim H) :
    PqxdhPlacedHookContractsBbSat M P C A lim H :=
  PqxdhPlacedHookContractsSat.toBbSat
    (LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat.PqxdhPlacedHookContracts.toSat h)

theorem PqxdhPlacedHookContractsBbSat.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsBbSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_ok_of_block_sat hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

theorem PqxdhPlacedHookContractsBbSat.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsBbSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_frozen_ok_of_block_sat hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

theorem PqxdhPlacedHookContractsBbSat.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsBbSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have _ : HkdfPlacedHooksBudgetSat C.F H := hH.hkdf
  exact pqxdhHkdfExtract_placed_ok_sat hP hi

theorem PqxdhPlacedHookContractsBbSat.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsBbSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have _ : HkdfPlacedHooksBudgetSat C.F H := hH.hkdf
  exact pqxdhHkdfExpandMultiInfo_placed_ok_sat hP hi

theorem PqxdhPlacedHookContractsBbSat.handshakeKeysDerive_vm_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsBbSat M P C A lim H)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedVmSpec P)) := by
  have _ : HkdfPlacedHooksBudgetSat C.F H := hH.hkdf
  exact handshakeKeysDerive_placed_vm_ok_of_block_sat hWF hP hi

theorem PqxdhPlacedHookContractsBbSat.handshakeKeysDerive_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsBbSat M P C A lim H)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec M P A lim)) := by
  have _ : HkdfPlacedHooksBudgetSat C.F H := hH.hkdf
  exact handshakeKeysDerive_placed_ok_of_block_sat hWF hP hi

theorem PqxdhPlacedHookContractsBbSat.createChain_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsBbSat M P C A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)) := by
  have _ : HkdfPlacedHooksBudgetSat C.F H := hH.hkdf
  exact createChain_placed_ok_of_block_sat hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.dealloc hi

theorem PqxdhPlacedHookContractsBbSat.createChain_x_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsBbSat M P C A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)) := by
  have _ : HkdfPlacedHooksBudgetSat C.F H := hH.hkdf
  exact createChain_placed_ok_x_of_block_sat hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.dealloc hi

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetBbSat
