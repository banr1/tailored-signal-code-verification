/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.InitiateCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LscroKitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Pure
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Stage 4 Pure Algebra and Callee Transfer Lemmas (`[LibsignalPlacement]`)

Re-exports Stage 4 pure model lemmas and provides `initProgPlaced W` callee transfer wrappers and
`TraceFsSound (initProgPlaced W)`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

theorem lscro_sp_eq [LibsignalPlacement] {st : State}
    (_ : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl st.mem) (v : BitVec 64)
    (h : st.sp = v) : st.sp = v := h

theorem lscro_fs_eq [LibsignalPlacement] {st : State}
    (_ : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl st.mem) (s_ref : State)
    (h : st.fs = s_ref.fs) : st.fs = s_ref.fs := h

theorem lscro_reg_eq [LibsignalPlacement] {st : State}
    (_ : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl st.mem) (r : Reg)
    (v : BitVec 64) (h : st.readReg64 r = v) : st.readReg64 r = v := h

theorem dealloc_ok_at_init_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustDeallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A)) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hh.alloc.dealloc

theorem memcpy_ok_at_init_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl session2MemcpySpecX) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
    (hh.alloc.session_memcpy extHookStack (by decide) (by decide))

theorem staticDrop_ok_at_init_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsStaticSecretDropSym)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl zeroizeSecretSpec) := by
  dsimp only [initProgPlaced, lsProg_521]
  exact subroutine_ok_mono (ls_hook_ok_ultra_of_mem hh.staticDrop)
    (fun _ _ _ h => by
      dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at h
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at h
      exact h.2)
    (fun _ _ _ _ h => h)

theorem initProgPlaced_traceFsSound [LibsignalPlacement] (mmpl : MultiPlacement)
    (gh : CliGhostHooks) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) [h : InitTraceFsSound mmpl gh W] :
    TraceFsSound (initProgPlaced mmpl gh W) :=
  h.out

theorem coinsFill_stk_placed_le {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    cliCoinsFillStackPlaced ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have hext : extHookStack ≤ 65536 := by decide
  unfold cliCoinsFillStackPlaced
  omega

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
