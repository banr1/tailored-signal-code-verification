/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage 2 Shared Helpers

Provides `[LibsignalPlacement]` `InitPanicPostPlaced` combinators, panic and `StaticSecret::drop`
hook contracts, and `.rodata` vtable lemmas for Stage 2, while re-exporting pure normalization and
clamping lemmas from `Stage2Lemmas/Common`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-! ## `InitPanicPostPlaced` combinators -/

theorem initPanicPostPlaced_of_allocFailed [LibsignalPlacement] (A : RustAlloc) (S : RunSem)
    (x : InitGhost) (stk : Nat) {s0 s sf : State} (htr : s.trace = s0.trace) (F : SepProp) :
    InitPanicPostPlaced A S x stk s0 sf
      ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  dsimp only [InitPanicPostPlaced, initSlotSpecPlaced,
    LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hfail, _⟩ => ?_
  have hfail0 : allocFailedIn s0 sf := by simpa [allocFailedIn, htr] using hfail
  exact Entails.pure_right (Or.inr hfail0) (entails_anyHeap _)

theorem initPanicPostPlaced_of_panicked [LibsignalPlacement] (A : RustAlloc) (S : RunSem)
    (x : InitGhost) (stk : Nat) {s0 s : State} (hfail : allocFailedIn s0 s) (P : SepProp) :
    InitPanicPostPlaced A S x stk s0 (Rust.panicked s) P := by
  dsimp only [InitPanicPostPlaced, initSlotSpecPlaced,
    LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  have hfail' : allocFailedIn s0 (Rust.panicked s) := by
    simpa [Rust.panicked, allocFailedIn] using hfail
  exact Entails.pure_right (Or.inr hfail') (entails_anyHeap P)

/-! ## Panic extern and `StaticSecret::drop` hook contracts -/

abbrev lsRawVecHandleErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

theorem handleError_externAt_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    (initProgPlaced mmpl gh W).externAt? (lsρ lsRawVecHandleErrorSym) = some Rust.panicked := by
  dsimp only [initProgPlaced, lsProg_521]
  exact (ls_externAt?_of_mem (sym := lsRawVecHandleErrorSym)).trans hh.panic_raw

theorem staticSecretDrop_placed_ok [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsStaticSecretDropSym) zeroizeSecretSpec := by
  dsimp only [initProgPlaced, lsProg_521]
  exact ls_hook_ok_ultra_of_mem hh.staticDrop

/-! ## Vtable `.rodata` lemmas -/

theorem rodata_idVt_getKeyPairShim_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} {s : State} {P : SepProp}
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((lsρ cliIdentityVtSym + 0x18#64) ↦₆₄ᵣ lsmpl.base 602) ∗ P :=
  hStore.rodata_idVt_keyPairSlot hinv.2 hP

theorem rodata_idKeyPairFutDrop_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((lsρ idKeyPairFutVtSym) ↦₆₄ᵣ lsmpl.base 547) ∗ P :=
  StoreCalleesProofs.rodata_idKeyPairFut_drop_placed hinv.2 hP

theorem rodata_idKeyPairFutSize_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((lsρ idKeyPairFutVtSym + 8#64) ↦₆₄ᵣ 16#64) ∗ P :=
  StoreCalleesProofs.rodata_idKeyPairFut_size_placed hinv.2 hP

theorem rodata_idKeyPairFutAlign_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((lsρ idKeyPairFutVtSym + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P :=
  StoreCalleesProofs.rodata_idKeyPairFut_align_placed hinv.2 hP

theorem rodata_idKeyPairFutPoll_placed [LibsignalPlacement] {s : State} {P : SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((lsρ idKeyPairFutVtSym + 0x18#64) ↦₆₄ᵣ lsmpl.base 567) ∗ P :=
  StoreCalleesProofs.rodata_idKeyPairFut_poll_placed hinv.2 hP

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
