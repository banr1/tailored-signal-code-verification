/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Stage 5 Pure Model and Panic Post Bridge (`[LibsignalPlacement]`)

Re-exports `Stage5Lemmas/ModelBridge.lean` and proves `initPanicPost_of_oom_placed`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

/-- Any OOM panic (`allocFailedIn s0 sf` with `anyHeap`) entails `InitPanicPostPlaced`. -/
theorem initPanicPost_of_oom_placed [LibsignalPlacement] {A : RustAlloc} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 sf : State} {Pf : SepProp}
    (hoom : allocFailedIn s0 sf) (hheap : Pf ⊢ anyHeap) :
    InitPanicPostPlaced A S x stk s0 sf Pf := by
  dsimp only [InitPanicPostPlaced, initSlotSpecPlaced,
    LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  rw [pure_sepConj_of_true (Or.inr hoom)]
  exact hheap

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
