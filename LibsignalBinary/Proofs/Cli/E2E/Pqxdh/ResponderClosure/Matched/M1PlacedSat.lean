/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudgetSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `HookSat`-Backed `Matched/M1Placed` (`M1PlacedSat`)

Additive `HookSat H lsBlackBoxU8Sym blackBoxSpecSat` sibling of
`LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Placed` on Block `50`
(`<libsignal_protocol::state::session::SessionRecord>::promote_matching_session`), derived
directly from `M1PlacedBudgetSat` by forgetting the `VmPreserved` conjunct.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedSat

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks blkPC_50 blkPl_50 lsmpl
   IsLsBlockProg ls_subroutine_ok_of_block ls_subroutine_ok_cl_of_plain
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded withLsCl)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (lsBlackBoxU8Sym)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (blackBoxSpecSat)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudgetSat
  (promoteMatchingSessionRawSpec16 promoteMatchingSessionRawBudgetSpec16
   promoteMatchingSessionMatchSpec16 promoteMatchingSessionMatchBudgetSpec16)

private theorem drop_vmPreserved {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withVmPreserved spec)) :
    subroutine_ok prog entry spec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withVmPreserved] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

/-- `HookSat` `black_box` sibling of `M1Placed.promote_matching_session_raw_placed_ok`. -/
theorem promote_matching_session_raw_placed_ok_sat [LibsignalPlacement]
    {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H)
      (blkPl_50).base
      promoteMatchingSessionRawSpec16 :=
  drop_vmPreserved (M1PlacedBudgetSat.promote_matching_session_raw_placed_ok_sat h_bb)

/-- `HookSat` `black_box` sibling of `M1Placed.promote_matching_session_match_placed_ok`. -/
theorem promote_matching_session_match_placed_ok_sat [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H)
      (blkPl_50).base
      (promoteMatchingSessionMatchSpec16 A) :=
  drop_vmPreserved (M1PlacedBudgetSat.promote_matching_session_match_placed_ok_sat h_bb)

/-- Caller-lifted `withLsCodeLoaded` sibling of `M1Placed.promote_matching_session_match_placed_ok_at`. -/
theorem promote_matching_session_match_placed_ok_at_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 50)
      (withLsCodeLoaded lsmpl (promoteMatchingSessionMatchSpec16 A)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (entry := lsmpl.base 50)
    (subroutine_ok_withLsCodeLoaded_of_plain (promote_matching_session_match_placed_ok_sat h_bb)) hi

/-- Caller-lifted `withLsCl` sibling of `M1Placed.promote_matching_session_match_placed_cl_ok_at`. -/
theorem promote_matching_session_match_placed_cl_ok_at_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 50)
      (withLsCl lsmpl (promoteMatchingSessionMatchSpec16 A)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := callerProg) (entry := lsmpl.base 50)
    (promote_matching_session_match_placed_ok_sat h_bb) hi

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedSat
