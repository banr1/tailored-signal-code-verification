/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.MacCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Mac.AddressesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddressesBudget
import ProofLib.SepLogic.WPFrozen

/-!
# Budget-Threaded Relocatable `<SignalMessage>::verify_mac_with_addresses` Composition

Composes the `[LibsignalPlacement]` `RustCliAllocBudget` proofs of `serialize_addresses`,
`compute_mac`, and `VerifyMacWithAddressesBudget` into `verifyMacWithAddresses_placed_ok`,
`verifyMacWithAddresses_placed_ok_x`, and `verifyMacWithAddresses_placed_cro_ok`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement
  blkPC_60 blkPC_61 blkPC_62 blkPl_60 blkPl_61 blkPl_62
  extract_withLsCodeLoaded libsignalMutatedBlocks libsignalSessionLib
  lsBlackBoxU8Sym ls_externAt?_blockProgram_eq_of_externs_eq lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (
  blackBoxSpec extHookStack keys_ls_subroutine_ok_of_block_cro
  lsMacCompress256Sym lsMacMemcpySym lsMacMemsetSym
  lsMacRustAllocSym lsMacRustDeallocSym lsMacRustNoAllocShimSym
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  publicKeySerializeSpec publicKeySerializeSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (blackBoxU8BudgetSpec withStack)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget (
  parseSidCodeBudgetSpec parseSidCodeStackBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.AddressesBudget (
  serialize_addresses_placed_ok serialize_addresses_placed_ok_of_rustAllocShimVm
  serialize_addresses_placed_ok_x serialize_addresses_placed_ok_x_of_rustAllocShimVm
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudget (
  computeMac_placed_cro_ok computeMac_placed_ok computeMac_placed_ok_x
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux (
  compress256BudgetSpec newFromSliceBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (
  verifyMacWithAddressesPlacedSpec verifyMacWithAddressesPlacedSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddressesBudget (
  verifyMacWithAddresses_placed_cro_ok_of_compute
  verifyMacWithAddresses_placed_ok_of_compute
  verifyMacWithAddresses_placed_ok_of_compute_x
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (noAllocShimBudgetSpec)

private theorem ls_subroutine_ok_lscl_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcl0 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

theorem verifyMacWithAddresses_placed_ok [LibsignalPlacement]
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec parse)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceBudgetSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (withVmPreserved blackBoxSpec))
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256BudgetSpec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpec M A lim C.F parse)) :=
  verifyMacWithAddresses_placed_ok_of_compute C M A lim parse H
    hdealloc hbb_raw
    (ls_subroutine_ok_lscl_of_block (serialize_addresses_placed_ok hparse hshim halloc))
    (ls_subroutine_ok_lscl_of_block
      (computeMac_placed_ok C M A lim H hnew hpk hmemcpy hcompress hdealloc hmemset))

theorem verifyMacWithAddresses_placed_ok_of_rustAllocShimVm [LibsignalPlacement]
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec parse)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceBudgetSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (withVmPreserved blackBoxSpec))
    (hshim : HookSat H lsMacRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256BudgetSpec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpec M A lim C.F parse)) :=
  verifyMacWithAddresses_placed_ok_of_compute C M A lim parse H
    hdealloc hbb_raw
    (ls_subroutine_ok_lscl_of_block
      (serialize_addresses_placed_ok_of_rustAllocShimVm hparse hshim halloc))
    (ls_subroutine_ok_lscl_of_block
      (computeMac_placed_ok C M A lim H hnew hpk hmemcpy hcompress hdealloc hmemset))

theorem verifyMacWithAddresses_placed_ok_x [LibsignalPlacement]
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackBudgetSpec extHookStack)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceBudgetSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecX M A lim)))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsρ lsBlackBoxU8Sym)
      (withStack blackBoxU8BudgetSpec extHookStack))
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256BudgetSpec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpecX M A lim C.F uuidTryParse)) :=
  verifyMacWithAddresses_placed_ok_of_compute_x C M A lim uuidTryParse H
    hdealloc hbb_raw
    (ls_subroutine_ok_lscl_of_block (serialize_addresses_placed_ok_x hparse hshim halloc))
    (ls_subroutine_ok_lscl_of_block
      (computeMac_placed_ok_x C M A lim H hnew hpk hmemcpy hcompress hdealloc hmemset))

theorem verifyMacWithAddresses_placed_ok_x_of_rustAllocShimVm [LibsignalPlacement]
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackBudgetSpec extHookStack)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceBudgetSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecX M A lim)))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsρ lsBlackBoxU8Sym)
      (withStack blackBoxU8BudgetSpec extHookStack))
    (hshim : HookSat H lsMacRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256BudgetSpec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpecX M A lim C.F uuidTryParse)) :=
  verifyMacWithAddresses_placed_ok_of_compute_x C M A lim uuidTryParse H
    hdealloc hbb_raw
    (ls_subroutine_ok_lscl_of_block
      (serialize_addresses_placed_ok_x_of_rustAllocShimVm hparse hshim halloc))
    (ls_subroutine_ok_lscl_of_block
      (computeMac_placed_ok_x C M A lim H hnew hpk hmemcpy hcompress hdealloc hmemset))

theorem verifyMacWithAddresses_placed_cro_ok [LibsignalPlacement]
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec parse)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (withVmPreserved blackBoxSpec))
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256BudgetSpec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec M A lim C.F parse)) :=
  verifyMacWithAddresses_placed_cro_ok_of_compute C M A lim parse H
    hdealloc hbb_raw
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_lscl_of_block (serialize_addresses_placed_ok hparse hshim halloc)))
    (keys_ls_subroutine_ok_of_block_cro
      (computeMac_placed_cro_ok C M A lim H hnew hpk hmemcpy hcompress hdealloc hmemset))

theorem verifyMacWithAddresses_placed_cro_ok_of_rustAllocShimVm [LibsignalPlacement]
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec parse)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (withVmPreserved blackBoxSpec))
    (hshim : HookSat H lsMacRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256BudgetSpec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec M A lim C.F parse)) :=
  verifyMacWithAddresses_placed_cro_ok_of_compute C M A lim parse H
    hdealloc hbb_raw
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_lscl_of_block
        (serialize_addresses_placed_ok_of_rustAllocShimVm hparse hshim halloc)))
    (keys_ls_subroutine_ok_of_block_cro
      (computeMac_placed_cro_ok C M A lim H hnew hpk hmemcpy hcompress hdealloc hmemset))

end LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyBudget
