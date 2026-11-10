/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Rodata
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget

/-!
# Budget-Threaded Relocatable Callee Helpers for `OTR::encrypt`

Provides `[LibsignalPlacement]` hook-to-`subroutine_ok` bridges over `RustCliAllocBudget M` for
`aes_256_cbc_encrypt`, `format_inner`, and `__rust_dealloc`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.RodataBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsRustDeallocSym lsρ
)
open CryptoVerification.LibsignalTripleRatchet (keys_ls_hook_ok_of_mem)
open CryptoVerification.LibsignalTripleRatchet.Encrypt (lsAesEncSym lsFormatInnerSym)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (
  aesEncBudgetSpec formatInnerBudgetEnvSpec formatInnerBudgetSpec
)

theorem aesEnc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {C : Crypto} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_aes : HookSat H lsAesEncSym (aesEncBudgetSpec C.E M A lim))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsAesEncSym) (aesEncBudgetSpec C.E M A lim) :=
  keys_ls_hook_ok_of_mem h_aes (by decide) hi hunmut

theorem formatInnerEnv_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : List AllocEvent → Prop} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim Env))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsFormatInnerSym) (formatInnerBudgetEnvSpec M A lim Env) :=
  keys_ls_hook_ok_of_mem h_fmt (by decide) hi hunmut

theorem formatInner_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetSpec M A lim))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsFormatInnerSym) (formatInnerBudgetSpec M A lim) :=
  keys_ls_hook_ok_of_mem h_fmt (by decide) hi hunmut

theorem dealloc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  keys_ls_hook_ok_of_mem h_dealloc (by decide) hi hunmut

end LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.RodataBudget
