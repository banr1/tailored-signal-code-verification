/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `FdsGe3Closed`-Threaded Relocatable `[LibsignalPlacement]` Handshake `try_decrypt_with_state::<Coins>`

Wraps the `blkPl_508` (`lsmpl.base 508`) budget-threaded `try_decrypt_with_state` contracts
with `withFdsGe3Closed` so `⌜FdsGe3Closed s.fs⌝` is preserved from `.pre` to `.post`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudgetFd

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.CliHandshake.TryDecPlaced (blkPC_508 blkPl_508)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TryDecryptGhost withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (SpqrHooksBudget TripleRatchetHooksBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget (
  tryDecryptPlacedOnPanicTight_weaken tryDecryptPlacedSpecP tryDecryptPlacedSpecQF_PTight
  tryDecryptPlacedSpecT tryDecryptPlacedSpecTP tryDecryptPlacedSpecTP_pre_of_tryDecryptPlacedSpecT
  tryDecryptPlacedSpecTPTight tryDecryptPlacedTightSpec
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  tryDecryptRawSpecTPTightAt tryDecryptSpecTPTightAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget (tryDecryptOnPanicTight)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. `withFdsGe3Closed`-Threaded `tryDecryptPlaced*Fd` Contracts -/

def tryDecryptPlacedSpecPFd [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withFdsGe3Closed (tryDecryptPlacedSpecP C A lim ctl uuidParse S tdEnv)

def tryDecryptPlacedSpecTPFd [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withFdsGe3Closed (tryDecryptPlacedSpecTP C A lim ctl uuidParse S tdEnv)

def tryDecryptPlacedSpecTPTightFd [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withFdsGe3Closed (tryDecryptPlacedSpecTPTight C A lim ctl uuidParse S tdEnv)

def tryDecryptPlacedSpecQF_PTightFd [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withFdsGe3Closed (tryDecryptPlacedSpecQF_PTight Q F C A lim ctl parse S tdEnv)

def tryDecryptPlacedTightSpecFd [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withFdsGe3Closed (tryDecryptPlacedTightSpec C A lim ctl parse S tdEnv)

def tryDecryptPlacedSpecTFd [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withFdsGe3Closed (tryDecryptPlacedSpecT C A lim ctl uuidParse S tdEnv)

abbrev tryDecryptRawSpecTPTightAtFd [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withFdsGe3Closed (tryDecryptRawSpecTPTightAt C A lim ctl uuidParse S tdEnv)

def tryDecryptSpecTPTightAtFd [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withFdsGe3Closed (tryDecryptSpecTPTightAt C A lim ctl uuidParse S tdEnv)

/-- Commute `withFdsGe3Closed` and `StoreKit.withLsCodeRoLoaded lsmpl` on `tryDecryptRawSpecTPTightAt`. -/
theorem subroutine_ok_withLsCodeRoLoaded_tryDecryptRawSpecTPTightAtFd_of_outer
    [LibsignalPlacement] {M : AllocCostModel} {P : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h : subroutine_ok P entry
      (withFdsGe3Closed
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (tryDecryptRawSpecTPTightAt C A lim ctl parse S tdEnv)))) :
    subroutine_ok P entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (tryDecryptRawSpecTPTightAtFd C A lim ctl parse S tdEnv)) := by
  refine subroutine_ok_mono h
    (fun xs R s0 hpre => ?_)
    (fun _ _ _ _ hpost => hpost)
  dsimp only [tryDecryptRawSpecTPTightAtFd, withFdsGe3Closed,
    CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpre ⊢
  refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hpre
  sep_ac_rfl

/-- Commute `withFdsGe3Closed` and `StoreKit.withLsRoCl lsmpl` on `tryDecryptRawSpecTPTightAt`. -/
theorem subroutine_ok_withLsRoCl_tryDecryptRawSpecTPTightAtFd_of_outer
    [LibsignalPlacement] {M : AllocCostModel} {P : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h : subroutine_ok P entry
      (withFdsGe3Closed (withLsRoCl lsmpl
        (tryDecryptRawSpecTPTightAt C A lim ctl parse S tdEnv)))) :
    subroutine_ok P entry
      (withLsRoCl lsmpl
        (tryDecryptRawSpecTPTightAtFd C A lim ctl parse S tdEnv)) := by
  refine subroutine_ok_mono h
    (fun xs R s0 hpre => ?_)
    (fun xs R s0 sf hpost => ?_)
  · dsimp only [tryDecryptRawSpecTPTightAtFd, withFdsGe3Closed, withLsRoCl] at hpre ⊢
    refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hpre
    sep_ac_rfl
  · dsimp only [tryDecryptRawSpecTPTightAtFd, withFdsGe3Closed, withLsRoCl] at hpost ⊢
    refine Eq.mp (congrArg (sf.mem ⊨ ·) ?_) hpost
    sep_ac_rfl

/-! ## 2. `FdsGe3Closed`-Threaded Placed Run Statement Abbreviations & Weakening Bridges -/

def TryDecryptPqV1RunStmtPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (K : MlKem) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooksBudget C M A lim (spqrV1 C.F K) abs →
    SpqrHooksBudget C M A lim K abs →
    subroutine_ok ((blkPC_508).rebase (blkPl_508).base abs)
      (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (tryDecryptPlacedSpecTFd C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv))

def TryDecryptPqV1RunStmtPPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (K : MlKem) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooksBudget C M A lim (spqrV1 C.F K) abs →
    SpqrHooksBudget C M A lim K abs →
    subroutine_ok ((blkPC_508).rebase (blkPl_508).base abs)
      (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (tryDecryptPlacedSpecTPFd C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv))

def TryDecryptPqV1RunStmtPTightPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (K : MlKem) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooksBudget C M A lim (spqrV1 C.F K) abs →
    SpqrHooksBudget C M A lim K abs →
    subroutine_ok ((blkPC_508).rebase (blkPl_508).base abs)
      (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (tryDecryptPlacedSpecTPTightFd C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv))

theorem tryDecryptPqV1_ok_P_placed_fd_of_PTight [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {K : MlKem} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {abs : String → Option (State → State)}
    (h : TryDecryptPqV1RunStmtPTightPlacedFd C A lim ctl K tdEnv abs) :
    TryDecryptPqV1RunStmtPPlacedFd C A lim ctl K tdEnv abs := by
  intro hH hQ
  refine subroutine_ok_mono (h hH hQ)
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => hq)
    (fun ⟨_, st⟩ _ _ _ hp => by
      dsimp only [withLsCodeLoaded, tryDecryptPlacedSpecTPTightFd, tryDecryptPlacedSpecTPFd,
        withFdsGe3Closed] at hp ⊢
      exact tryDecryptPlacedOnPanicTight_weaken (A := A) (lim := lim) (ctl := ctl)
        (tdEnv := tdEnv) (st := st) hp)

theorem tryDecryptPqV1_ok_placed_fd_of_P [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {K : MlKem} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {abs : String → Option (State → State)}
    (h : TryDecryptPqV1RunStmtPPlacedFd C A lim ctl K tdEnv abs) :
    TryDecryptPqV1RunStmtPlacedFd C A lim ctl K tdEnv abs := by
  intro hH hQ
  refine subroutine_ok_mono (h hH hQ)
    (fun ⟨x, st⟩ R s0 hpre => ?_)
    (fun _ _ _ _ hq => hq)
  dsimp only [withLsCodeLoaded] at hpre ⊢
  rw [sepConj_assoc] at hpre ⊢
  obtain ⟨hfds, hinner⟩ := extract_withFdsGe3Closed hpre
  dsimp only [tryDecryptPlacedSpecTPFd, withFdsGe3Closed]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfds, tryDecryptPlacedSpecTP_pre_of_tryDecryptPlacedSpecT hinner⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudgetFd
