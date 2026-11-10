/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit

/-!
# File-System and Descriptor Preservation for Budget-Threaded `MessageEncrypt` Callees

Strengthens `kyberMapSpec`, `preKeyMsgNewSpec`, and `cmDropSpec` with `Spec.keepsFs` (`sf.fs = s0.fs`)
and `withFdsGe3Closed`, along with `subroutine_ok` lifting lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudgetFd

open Arm64 ProofLib
open CryptoGames.LibsignalSessionApi (CiphertextMessage)
open CryptoVerification (LibsignalPlacement extract_withLsCodeLoaded lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (KyberMapCall PreKeyMsgNewCall)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
  (cmDropSpec kyberMapSpec preKeyMsgNewSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (subroutine_ok_withFdsGe3Closed_of_keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)

abbrev kyberMapSpecFs (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (KyberMapCall × M.σ) :=
  (kyberMapSpec M A lim).keepsFs

abbrev kyberMapSpecFd (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (KyberMapCall × M.σ) :=
  withFdsGe3Closed (kyberMapSpec M A lim)

abbrev preKeyMsgNewSpecFs [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (PreKeyMsgNewCall × M.σ) :=
  (preKeyMsgNewSpec M A lim).keepsFs

abbrev preKeyMsgNewSpecFd [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (PreKeyMsgNewCall × M.σ) :=
  withFdsGe3Closed (preKeyMsgNewSpec M A lim)

abbrev cmDropSpecFs [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × CiphertextMessage × M.σ) :=
  (cmDropSpec M A lim).keepsFs

abbrev cmDropSpecFd [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × CiphertextMessage × M.σ) :=
  withFdsGe3Closed (cmDropSpec M A lim)

theorem subroutine_ok_kyberMapSpecFd_of_keepsFs {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (kyberMapSpecFs M A lim)) :
    subroutine_ok prog entry (kyberMapSpecFd M A lim) :=
  subroutine_ok_withFdsGe3Closed_of_keepsFs h

theorem subroutine_ok_cmDropSpecFd_of_keepsFs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (cmDropSpecFs M A lim)) :
    subroutine_ok prog entry (cmDropSpecFd M A lim) :=
  subroutine_ok_withFdsGe3Closed_of_keepsFs h

theorem subroutine_ok_withLsCodeLoaded_withFdsGe3Closed_of_keepsFs {α : Type}
    {pl : Arm64.Obj.MultiPlacement} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec.keepsFs)) :
    subroutine_ok prog entry (withLsCodeLoaded pl (withFdsGe3Closed spec)) := by
  have h1 : subroutine_ok prog entry (withLsCodeLoaded pl spec).keepsFs :=
    subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)
  exact subroutine_ok_mono (subroutine_ok_withFdsGe3Closed_of_keepsFs h1)
    (fun _ _ _ hp => by
      dsimp only [withLsCodeLoaded, withFdsGe3Closed] at hp ⊢
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp)
    (fun _ _ _ _ hq => hq)

theorem subroutine_ok_preKeyMsgNewSpecFd_cl_of_keepsFs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl (preKeyMsgNewSpecFs M A lim))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (preKeyMsgNewSpecFd M A lim)) :=
  subroutine_ok_withLsCodeLoaded_withFdsGe3Closed_of_keepsFs h

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudgetFd
