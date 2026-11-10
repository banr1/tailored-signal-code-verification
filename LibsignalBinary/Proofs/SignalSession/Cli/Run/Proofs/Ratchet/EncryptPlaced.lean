/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.PqEncrypt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.SmEncrypt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `signal_session_ratchet::encrypt` Slot Contract

Proves the `[LibsignalPlacement]` slot contract for `signal_session_ratchet::encrypt` (Block `464`)
and re-exports PQXDH and Signal-Message model agreement.
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

export Agree (cliAnswers cliStep cliFinal encKey encDef RatchetScopeCoversPq RatchetScopeCoversSm)

abbrev cliEncryptNeed_placed (B : RunBudgets) : Nat :=
  2 ^ 20 + B.readFile

theorem pqEncryptAgrees_encDef_placed (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.encrypt = encDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversPq W Scope) :
    RunRefine.PqEncryptAgrees S W :=
  Agree.pqEncryptAgrees_encDef_aux S W Scope hS hinj hcov

theorem smEncryptAgrees_encDef_placed (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.encrypt = encDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversSm W.C Scope) :
    RunRefine.SmEncryptAgrees S W.C :=
  Agree.smEncryptAgrees_encDef_aux S W Scope hS hinj hcov

/-- Relocatable `encSlotSpecPlaced` contract for `signal_session_ratchet::encrypt`
(`lsmpl.base 464`) on any caller block `i < 619`. -/
theorem cliEncrypt_slot_placed [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hInner464 : EncryptLemmas.W1InnerPlacedOk mmpl gh W B Scope)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = encDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (stk : Nat) (hstk : cliEncryptNeed_placed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 464)
      (encSlotSpecPlaced E2E.HooksE.A0 S stk) := by
  have hFinal : ∀ F calls, cliFinal F calls = EncryptLemmas.w1CliFinal F calls := by
    intro F calls
    unfold cliFinal EncryptLemmas.w1CliFinal
    have hStep : cliStep F = EncryptLemmas.w1CliStep F := by
      funext g c; cases c <;> rfl
    rw [hStep]
  have hAns : ∀ F peer,
      cliAnswers Scope F peer (encKey Scope F peer) =
        EncryptLemmas.w1CliAnswers Scope F peer (EncryptLemmas.w1EncKey Scope F peer) := by
    intro F peer
    have hKey : encKey Scope F peer = EncryptLemmas.w1EncKey Scope F peer := by
      unfold encKey EncryptLemmas.w1EncKey
      rcases Slots.loadRec Scope F peer with _ | (_ | r) <;> rfl
    rw [hKey]
    unfold cliAnswers EncryptLemmas.w1CliAnswers
    rcases EncryptLemmas.w1EncKey Scope F peer with _ | _ <;> rfl
  have hDef : encDef ⟨W.C, W.Q⟩ Scope = EncryptLemmas.w1EncDef ⟨W.C, W.Q⟩ Scope := by
    funext F peer me ptext coins
    unfold encDef EncryptLemmas.w1EncDef
    rw [hAns F peer]
    generalize LibsignalSessionApi.messageEncrypt W.C protoSignalCodec
      (pqxdhSpqrModel ⟨W.C, W.Q⟩).spqr (serializeAddrVals (serviceIdParse uuidTryParse))
      (EncryptLemmas.w1CliAnswers Scope F peer (EncryptLemmas.w1EncKey Scope F peer))
      ptext peer me unixEpoch coins = rc
    rcases rc with ⟨err | m, calls⟩
    · cases err <;> rfl
    · simp only [hFinal F calls]
  exact EncryptLemmas.cliEncrypt_slot_placed mmpl gh W B S Scope (hh.fs callerProg i) hInner464 hinjK hsub
    (hS.trans hDef) hok stk hstk hstk64 hi

theorem cliEncrypt_slotOk_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hInner464 : EncryptLemmas.W1InnerPlacedOk mmpl gh W B Scope)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = encDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (hneed : needs.encrypt = cliEncryptNeed_placed B) :
    (slotsOfPlaced E2E.HooksE.A0 S needs).encrypt.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 464) :=
  fun stk h1 h2 =>
    cliEncrypt_slot_placed (i := 579) mmpl gh W B S Scope hh hInner464 hinjK hsub hS hok stk
      (hneed ▸ h1) h2

end CryptoVerification.SignalSession.Cli.RunProofs
