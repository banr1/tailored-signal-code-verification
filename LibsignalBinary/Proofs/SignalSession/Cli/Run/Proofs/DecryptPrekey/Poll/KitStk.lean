/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOk

/-!
# Poll Store Callback Stack Budgets

Defines the 22-field stack budget bundle `DpKitStk` and its CLI instantiation `cliKitStk B` for the
store shims and polls invoked by `message_decrypt_prekey::<Coins>::{closure#0}`, proving every call
fits inside `dpClosSubStack B`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.KitInst

/-- Stack budgets for all 22 store shim and poll entry points invoked by `decrypt_prekey`. -/
structure DpKitStk where
  sessLoadShim : Nat
  sessLoadPoll : Nat
  sessStoreShim : Nat
  sessStorePoll : Nat
  idTrustShim : Nat
  idTrustPoll : Nat
  idSaveShim : Nat
  idSavePoll : Nat
  kpShim : Nat
  kpPoll : Nat
  regIdShim : Nat
  regIdPoll : Nat
  pkGetShim : Nat
  pkGetPoll : Nat
  pkRemoveShim : Nat
  pkRemovePoll : Nat
  spkGetShim : Nat
  spkGetPoll : Nat
  kpkGetShim : Nat
  kpkGetPoll : Nat
  kpkMarkShim : Nat
  kpkMarkPoll : Nat

/-- Pointwise predicate over all 22 fields of `DpKitStk`. -/
def DpKitStk.All (P : Nat → Prop) (σ : DpKitStk) : Prop :=
  P σ.sessLoadShim ∧ P σ.sessLoadPoll ∧ P σ.sessStoreShim ∧ P σ.sessStorePoll ∧
  P σ.idTrustShim ∧ P σ.idTrustPoll ∧ P σ.idSaveShim ∧ P σ.idSavePoll ∧
  P σ.kpShim ∧ P σ.kpPoll ∧ P σ.regIdShim ∧ P σ.regIdPoll ∧
  P σ.pkGetShim ∧ P σ.pkGetPoll ∧ P σ.pkRemoveShim ∧ P σ.pkRemovePoll ∧
  P σ.spkGetShim ∧ P σ.spkGetPoll ∧
  P σ.kpkGetShim ∧ P σ.kpkGetPoll ∧ P σ.kpkMarkShim ∧ P σ.kpkMarkPoll

/-- Exact `hstk` left-hand sides of the 22 CLI store hops at `RunBudgets` `B`. -/
def cliKitStk (B : RunBudgets) : DpKitStk where
  sessLoadShim := SessKit.loadShimNeed
  sessLoadPoll := SessKit.loadPollNeed B.readFile
  sessStoreShim := SessKit.storeShimNeed
  sessStorePoll := SessKit.storePollNeedX
  idTrustShim := IdKit.trustShimNeed
  idTrustPoll := IdKit.trustPollNeed B.readFile
  idSaveShim := IdKit.saveShimNeed
  idSavePoll := IdKit.savePollNeed B.readFile
  kpShim := 0x20 + extHookStack
  kpPoll := 0xb0 + max (max B.dirGetNeed smallRootStack) extHookStack
  regIdShim := 0x20 + extHookStack
  regIdPoll := 0x70 + max B.dirGetNeed extHookStack
  pkGetShim := 0x20 + extHookStack
  pkGetPoll :=
    0x100 + max (max SessKit.decNeed B.dirGetNeed)
      (max smallRootStack (max Getters.dropSpeStackX extHookStack))
  pkRemoveShim := 0x20 + extHookStack
  pkRemovePoll := 0xc0 + max (max SessKit.decNeed B.dirGetNeed) (max SessKit.dirPutNeed extHookStack)
  spkGetShim := 0x20 + extHookStack
  spkGetPoll :=
    0x180 + max (max SessKit.decNeed B.dirGetNeed)
      (max smallRootStack (max Getters.dropSpeStackX extHookStack))
  kpkGetShim := 0x20 + extHookStack
  kpkGetPoll :=
    0x1b0 + max (max SessKit.decNeed B.dirGetNeed)
      (max smallRootStack extHookStack)
  kpkMarkShim := 0x30 + extHookStack
  kpkMarkPoll :=
    0xf0 + max (max SessKit.decNeed B.dirGetNeed) (max SessKit.dirPutNeed doReserveStackX)

theorem dirGetNeed_eta (B : RunBudgets) :
    RunBudgets.dirGetNeed ⟨B.readFile⟩ = B.dirGetNeed := rfl

/-- Available stack below the closure's 3280-byte (`0xcd0`) hardware frame when `dpPollNeed B`
(`1048576 + B.dirGetNeed`) is supplied at poll entry. -/
abbrev dpClosSubStack (B : RunBudgets) : Nat :=
  (1048576 - 3280) + B.dirGetNeed

/-- Every CLI store shim and poll budget fits with ample headroom inside `dpClosSubStack B`
(even after adding `allocHookStack = 4096` for box allocation/drop wrappers). -/
theorem cliKitStk_add_alloc_le_subStack (B : RunBudgets) :
    (cliKitStk B).All (fun n => n + CryptoVerification.RustHeap.allocHookStack ≤ dpClosSubStack B) := by
  dsimp only [DpKitStk.All, cliKitStk, dpClosSubStack,
    SessKit.loadShimNeed, SessKit.loadPollNeed, SessKit.storeShimNeed, SessKit.storePollNeedX,
    IdKit.trustShimNeed, IdKit.trustPollNeed, IdKit.saveShimNeed, IdKit.savePollNeed]
  rw [dirGetNeed_eta B]
  have hDec : SessKit.decNeed ≤ 50000 := by decide
  have hAddr : SessKit.addrTextNeed ≤ 60000 := by decide
  have hPut : SessKit.dirPutNeed ≤ 50000 := by decide
  have hPutS : IdKit.dirPutStrNeed ≤ 50000 := by decide
  have hExt : extHookStack = 16384 := rfl
  have hAlloc : CryptoVerification.RustHeap.allocHookStack = 4096 := rfl
  have hRes : doReserveStackX ≤ 50000 := by decide
  have hSmall : smallRootStack = 65536 := rfl
  have hDrop : Getters.dropSpeStackX = 32 + 16384 := rfl
  have hDeser : E2E.Record.recDeserializeStack ≤ 200000 := by decide
  have hSer : Proofs.libsignal.Hooks2.serializeStackX ≤ 200000 := by decide
  have hPubSer : publicKeySerializeStackX ≤ 65536 := by decide
  generalize SessKit.decNeed = cDec at hDec ⊢
  generalize SessKit.addrTextNeed = cAddr at hAddr ⊢
  generalize SessKit.dirPutNeed = cPut at hPut ⊢
  generalize IdKit.dirPutStrNeed = cPutS at hPutS ⊢
  generalize extHookStack = cExt at hExt ⊢
  generalize CryptoVerification.RustHeap.allocHookStack = cAlloc at hAlloc ⊢
  generalize doReserveStackX = cRes at hRes ⊢
  generalize smallRootStack = cSmall at hSmall ⊢
  generalize Getters.dropSpeStackX = cDrop at hDrop ⊢
  generalize E2E.Record.recDeserializeStack = cDeser at hDeser ⊢
  generalize Proofs.libsignal.Hooks2.serializeStackX = cSer at hSer ⊢
  generalize publicKeySerializeStackX = cPubSer at hPubSer ⊢
  generalize B.dirGetNeed = cGet
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    omega

theorem cliKitStk_le_subStack (B : RunBudgets) :
    (cliKitStk B).All (fun n => n ≤ dpClosSubStack B) := by
  have h := cliKitStk_add_alloc_le_subStack B
  dsimp only [DpKitStk.All] at h ⊢
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    omega

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
