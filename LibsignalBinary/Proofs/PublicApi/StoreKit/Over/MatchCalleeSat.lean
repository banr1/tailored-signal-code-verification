/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.SessionRecordCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchDefs -- proof-setup: allow-public-import
import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCalleeBudgetSat

/-!
# `HookSat`-Backed `StoreKit.Over.MatchCallee` Proofs (`MatchCalleeSat`)

Additive `HookSat H lsBlackBoxU8Sym blackBoxSpecSat` sibling of the `[LibsignalPlacement]` section
of `LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCallee`.

Derived directly from `MatchCalleeBudgetSat` by dropping `VmPreserved`, keeping every theorem
conclusion token-identical to `MatchCallee`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCalleeSat

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPC_50 blkPl_50 lsBlackBoxU8Sym lsmpl withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
  (promoteMatchingSessionKeyMissRawSpec promoteMatchingSessionLenMissRawSpec
   promoteMatchingSessionMissSpec promoteMatchingSessionRecordOverSpec)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (blackBoxSpecSat)

private theorem subroutine_ok_drop_vm_lscl {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {S : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (withVmPreserved S))) :
    subroutine_ok prog entry (withLsCodeLoaded pl S) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeLoaded, withVmPreserved] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

/-- `HookSat` `black_box` sibling of `Over.promote_matching_session_len_miss_raw_placed_ok`. -/
theorem promote_matching_session_len_miss_raw_placed_ok_sat [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl promoteMatchingSessionLenMissRawSpec) :=
  subroutine_ok_drop_vm_lscl
    (MatchCalleeBudgetSat.promote_matching_session_len_miss_raw_placed_ok_sat h_bb)

/-- `HookSat` `black_box` sibling of `Over.promote_matching_session_key_miss_raw_placed_ok`. -/
theorem promote_matching_session_key_miss_raw_placed_ok_sat [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl promoteMatchingSessionKeyMissRawSpec) :=
  subroutine_ok_drop_vm_lscl
    (MatchCalleeBudgetSat.promote_matching_session_key_miss_raw_placed_ok_sat h_bb)

/-- `HookSat` `black_box` sibling of `Over.promote_matching_session_record_over_placed_ok`. -/
theorem promote_matching_session_record_over_placed_ok_sat [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl (promoteMatchingSessionRecordOverSpec A)) :=
  subroutine_ok_drop_vm_lscl
    (MatchCalleeBudgetSat.promote_matching_session_record_over_placed_ok_sat (A := A) h_bb)

/-- `HookSat` `black_box` sibling of `Over.promote_matching_session_miss_placed_ok`. -/
theorem promote_matching_session_miss_placed_ok_sat [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl (promoteMatchingSessionMissSpec A)) :=
  subroutine_ok_drop_vm_lscl
    (MatchCalleeBudgetSat.promote_matching_session_miss_placed_ok_sat (A := A) h_bb)

end LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCalleeSat
