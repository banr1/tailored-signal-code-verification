/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.PqDecrypt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.SmDecrypt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerGluePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `signal_session_ratchet::decrypt_signal` Slot Contract

Proves the `[LibsignalPlacement]` and `[LibsignalFullPlacement]` slot contracts for
`signal_session_ratchet::decrypt_signal` (Block `463`) and re-exports PQXDH and Signal-Message
model agreement.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification

export Agree (decSigKey decSigDef)

abbrev cliDecryptSignalNeed_placed (B : RunBudgets) : Nat :=
  2 ^ 20 + B.readFile

/-- Relocatable `decSigSlotSpecPlaced` contract for `signal_session_ratchet::decrypt_signal`
(`lsmpl.base 463`) on any caller block `i < 619`. -/
theorem cliDecryptSignal_slot_placed [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (DecryptLemmas.decSessKitPlaced F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (DecryptLemmas.decIdKitPlaced F0 peer B))
    (hInner463 : DecryptLemmas.InnerDecryptPlacedOk mmpl gh W B)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (stk : Nat) (hstk : cliDecryptSignalNeed_placed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 463)
      (decSigSlotSpecPlaced E2E.HooksE.A0 S stk) :=
  DecryptLemmas.cliDecryptSignal_slot_of_inner_placed W B S Scope (hh.fs callerProg i) hinjK hsub
    (fun F peer me msg coins =>
      congrFun (congrFun (congrFun (congrFun (congrFun hS F) peer) me) msg) coins)
    hok hvt hivt (DecryptLemmas.w2_inner_placed_at_block mmpl gh W B hInner463 hi) stk hstk hstk64

theorem cliDecryptSignal_slotOk_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (DecryptLemmas.decSessKitPlaced F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (DecryptLemmas.decIdKitPlaced F0 peer B))
    (hInner463 : DecryptLemmas.InnerDecryptPlacedOk mmpl gh W B)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed_placed B) :
    (slotsOfPlaced E2E.HooksE.A0 S needs).decryptSignal.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463) :=
  fun stk h1 h2 =>
    cliDecryptSignal_slot_placed (i := 579) mmpl gh W B S Scope hh hvt hivt hInner463 hinjK hsub hS hok stk
      (hneed ▸ h1) h2

/-- Closed `[LibsignalFullPlacement]` `decSigSlotSpecFrozenPlaced` contract for
`signal_session_ratchet::decrypt_signal` on any caller block `i < 619`. -/
theorem cliDecryptSignal_slot_full_placed [LibsignalFullPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (DecryptLemmas.decSessKitPlaced F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (DecryptLemmas.decIdKitPlaced F0 peer B))
    (hInner463 : DecryptLemmas.InnerDecryptFrozenPlacedOk mmpl gh W B)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (stk : Nat) (hstk : cliDecryptSignalNeed_placed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok callerProg (lsmpl.base 463)
      (decSigSlotSpecFrozenPlaced E2E.HooksE.A0 S stk) :=
  DecryptLemmas.cliDecryptSignal_slot_of_inner_frozen_placed W B S Scope (hh.fs callerProg i) hinjK hsub
    (fun F peer me msg coins =>
      congrFun (congrFun (congrFun (congrFun (congrFun hS F) peer) me) msg) coins)
    hok hvt hivt (DecryptLemmas.w2_inner_full_placed_at_block mmpl gh W B hInner463) stk hstk hstk64

theorem cliDecryptSignal_slotOk_full_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (DecryptLemmas.decSessKitPlaced F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (DecryptLemmas.decIdKitPlaced F0 peer B))
    (hInner463 : DecryptLemmas.InnerDecryptFrozenPlacedOk mmpl gh W B)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed_placed B) :
    (slotsOfSigFrozenPlaced E2E.HooksE.A0 S needs).decryptSignal.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463) :=
  fun stk h1 h2 =>
    cliDecryptSignal_slot_full_placed (i := 579) mmpl gh W B S Scope hh hvt hivt hInner463 hinjK hsub hS hok stk
      (hneed ▸ h1) h2

theorem pqDecryptSignalAgrees_decSigDef_placed (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.decryptSignal = decSigDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversPq W Scope) :
    RunRefine.PqDecryptSignalAgrees S W :=
  Agree.pqDecryptSignalAgrees_decSigDef_aux S W Scope hS hinj hcov

theorem smDecryptSignalAgrees_decSigDef_placed (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.decryptSignal = decSigDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversSm W.C Scope) :
    RunRefine.SmDecryptSignalAgrees S W.C :=
  Agree.smDecryptSignalAgrees_decSigDef_aux S W Scope hS hinj hcov

end CryptoVerification.SignalSession.Cli.RunProofs
