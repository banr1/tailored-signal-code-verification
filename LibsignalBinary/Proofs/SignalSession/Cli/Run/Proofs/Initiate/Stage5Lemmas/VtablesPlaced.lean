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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.Vtables
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Stage 5 Vtable and File-System Frame Helpers (`[LibsignalPlacement]`)

Relocatable `[LibsignalPlacement]` `.data.rel.ro` vtable dispatch and size/alignment lemmas for
`get_local_registration_id`, `save_identity`, and `store_session`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

set_option maxRecDepth 200000

theorem idVt_regIdShim_rodata_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} {s : State} {P : SepProp}
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ cliIdentityVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 603) ∗ P) :=
  hStore.rodata_idVt_regIdSlot hinv.2 hP

theorem idRegIdFut_drop_rodata_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ idRegIdFutVtSym) ↦₆₄ᵣ lsmpl.base 547) ∗ P) :=
  StoreCalleesProofs.rodata_idRegIdFut_drop_placed hinv.2 hP

theorem idRegIdFut_size_rodata_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ idRegIdFutVtSym + 8#64) ↦₆₄ᵣ 16#64) ∗ P) :=
  StoreCalleesProofs.rodata_idRegIdFut_size_placed hinv.2 hP

theorem idRegIdFut_align_rodata_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ idRegIdFutVtSym + 16#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  StoreCalleesProofs.rodata_idRegIdFut_align_placed hinv.2 hP

theorem idRegIdFut_poll_rodata_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ idRegIdFutVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 568) ∗ P) :=
  StoreCalleesProofs.rodata_idRegIdFut_poll_placed hinv.2 hP

theorem idVt_saveShim_rodata_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} {s : State} {P : SepProp}
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ cliIdentityVtSym + 40#64) ↦₆₄ᵣ lsmpl.base 600) ∗ P) :=
  hStore.rodata_idVt_saveSlot hinv.2 hP

theorem idSaveFut_drop_rodata_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ idSaveFutVtSym) ↦₆₄ᵣ lsmpl.base 547) ∗ P) :=
  StoreCalleesProofs.rodata_idSaveFut_drop_placed hinv.2 hP

theorem idSaveFut_size_rodata_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ idSaveFutVtSym + 8#64) ↦₆₄ᵣ 32#64) ∗ P) :=
  StoreCalleesProofs.rodata_idSaveFut_size_placed hinv.2 hP

theorem idSaveFut_align_rodata_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ idSaveFutVtSym + 16#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  StoreCalleesProofs.rodata_idSaveFut_align_placed hinv.2 hP

theorem idSaveFut_poll_rodata_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ idSaveFutVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 565) ∗ P) :=
  StoreCalleesProofs.rodata_idSaveFut_poll_placed hinv.2 hP

theorem sessVt_storeShim_rodata_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} {s : State} {P : SepProp}
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ cliSessionVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 605) ∗ P) :=
  hStore.rodata_sessVt_storeSlot hinv.2 hP

theorem sessStoreFut_drop_rodata_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ sessStoreFutVtSym) ↦₆₄ᵣ lsmpl.base 547) ∗ P) :=
  StoreCalleesProofs.rodata_sessStoreFut_drop_placed hinv.2 hP

theorem sessStoreFut_size_rodata_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ sessStoreFutVtSym + 8#64) ↦₆₄ᵣ 32#64) ∗ P) :=
  StoreCalleesProofs.rodata_sessStoreFut_size_placed hinv.2 hP

theorem sessStoreFut_align_rodata_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ sessStoreFutVtSym + 16#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  StoreCalleesProofs.rodata_sessStoreFut_align_placed hinv.2 hP

theorem sessStoreFut_poll_rodata_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((lsρ sessStoreFutVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 570) ∗ P) :=
  StoreCalleesProofs.rodata_sessStoreFut_poll_placed hinv.2 hP

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
