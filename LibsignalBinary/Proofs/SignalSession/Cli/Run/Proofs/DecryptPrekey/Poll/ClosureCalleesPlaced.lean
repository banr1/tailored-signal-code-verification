/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs

/-!
# Relocatable `[LibsignalPlacement]` Pure and Crypto Callee Discharges for `cliDpPollName`

Relocatable `[LibsignalPlacement]` callee and filesystem discharges for `cliDpPollName`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  CliGhostHooks cliGhostExterns
)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. `ChainClone3`, `SenderChainClone3`, & `DropSessionStructure4` under `[LibsignalPlacement]` -/

theorem cliGhostExterns_sessionMemcpyRegion_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : Slots.CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W))
      CryptoVerification.lsMemcpySym sessionMemcpyRegionSpec := by
  obtain ⟨f, hf, _, _, _, hok, _, _, _, _⟩ := hG.memcpy
  exact ⟨f, LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.cliGhostExterns_memcpy_some
    g (cliExternsPlaced mmpl W) hf, hok⟩

private theorem noAllocShimSpec_eq_sessionShimSpec :
    CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec =
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec := rfl

private theorem framelessMemcpySpec_eq_sessionMemcpyRegionSpec :
    CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec := rfl

theorem cliChainClone3_placed_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    ChainClone3OkPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  chainClone3_placed_ok_of_hooks
    (noAllocShimSpec_eq_sessionShimSpec ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    (framelessMemcpySpec_eq_sessionMemcpyRegionSpec ▸ hh.codecHooks.memcpy)
    hh.codecHooks.panic_raw

theorem cliSenderChainClone3_placed_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    SenderChainClone3OkPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  senderChainClone3_placed_ok_of_hooks
    (noAllocShimSpec_eq_sessionShimSpec ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    (framelessMemcpySpec_eq_sessionMemcpyRegionSpec ▸ hh.codecHooks.memcpy)
    hh.codecHooks.panic_raw

theorem cliDropSessionStructure4_placed_ok_at [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Spec
          E2E.HooksE.A0)) :=
  drop_session_structure4_placed_ok_at hh.codecHooks.dealloc hi

theorem cliFsAt_of_files_eq_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    {envOk : FsFiles → Prop} {Q : Prop} {F0 : FsFiles} {s : State}
    (hh : RunHooksPlaced E2E.HooksE.A0 ext)
    (hQ : Q) (henv : envOk F0) (hf : s.fs.files = F0) :
    FsAt envOk Q prog s :=
  .inr ⟨hQ, hh.fs prog i, hf ▸ henv⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
