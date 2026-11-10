/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Assembly
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs

/-!
# Top-Level `signal_session_handshake::initiate` Slot Contract and Agreement Theorems

Exports `cliInitiate_ok`, `cliInitiate_slotOk`, `initOk₀_pqInit`, `pqInitiateAgrees_initDef`, and
the extern-parameterized slot lifts `cliInitiate_ext_slotOk_of_ok` and `cliInitiate_slotOk_of_ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose

/-- At `cliExterns W`, when `S.initiate = initDef X ⟨W.C, W.Q⟩` and `S.initOk` implies `InitOk₀`,
`signal_session_handshake::initiate` satisfies `initSlotSpec A img S stk` for every stack budget
`cliInitiateNeed B ≤ stk ≤ 2 ^ 63`. -/
theorem cliInitiate_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr cliInitiateName)
      (initSlotSpec A img S stk) := by
  exact Initiate.cliInitiate_ok_proof W X B S himg hh hRead hS hok stk hstk hstk64

/-- Packages `cliInitiate_ok` into `(slotsOf A img S needs).initiate.Ok` when `needs.initiate = cliInitiateNeed B`. -/
theorem cliInitiate_slotOk {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) (needs : RunNeeds)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (hneed : needs.initiate = cliInitiateNeed B) :
    (slotsOf A img S needs).initiate.Ok img (cliExterns W) wrapInitiateName :=
  fun stk h1 h2 => cliInitiate_ok W X B S himg hh hRead hS hok stk (hneed ▸ h1) h2

/-! ## `S₀` domain validity and model agreement -/

/-- `InitOk₀` holds on `runFiles (pqInitInputs W st b t)` for any domain party `st` with `st.session = none`. -/
theorem initOk₀_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = none) :
    InitOk₀ W (runFiles (pqInitInputs W st b t)) (RunRefine.addrValE st.party.other)
      (RunRefine.addrValE st.party) := by
  exact InitS0.initOk₀_pqInit_proof W st b t hwf hs

/-- `PqInitiateAgrees S X W` holds whenever `S.initiate = initDef X W`. -/
theorem pqInitiateAgrees_initDef (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hS : S.initiate = initDef X W) : RunRefine.PqInitiateAgrees S X W := by
  exact InitS0.pqInitiateAgrees_initDef_proof S X W hS

/-! ## Extern-parameterized slot lifts -/

/-- Lifts a `subroutine_ok` proof on `Initiate.initProgExt img ext` across `cliInitiateNeed B ≤ stk ≤ 2 ^ 63` to `SlotSpec.Ok`. -/
theorem cliInitiate_ext_slotOk_of_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets) (S : RunSem) (needs : RunNeeds)
    (hInit : ∀ (stk : Nat), cliInitiateNeed B ≤ stk → stk ≤ 2 ^ 63 →
      subroutine_ok (Initiate.initProgExt img ext)
        ((Initiate.initProgExt img ext).fnAddr cliInitiateName)
        (initSlotSpec A img S stk))
    (hneed : needs.initiate = cliInitiateNeed B) :
    (slotsOf A img S needs).initiate.Ok img (cliExternsWith ext) wrapInitiateName :=
  fun stk h1 h2 => hInit stk (hneed ▸ h1) h2

/-- Specializes `cliInitiate_ext_slotOk_of_ok` to `cliExterns W` at `HooksE.A0` via `cliExterns_ok W`. -/
theorem cliInitiate_slotOk_of_ext
    (hExt : ∀ {img : Obj.Image} {P : PEParams} {A : RustAlloc}
      {ext : String → Option (State → State)} (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem),
      Obj.Loads libsignalSessionImage img →
      CliExternsOk P A ext →
      subroutine_ok (Initiate.initProgExt img ext) ((Initiate.initProgExt img ext).fnAddr Cli.readFileName)
        (readFileSpec cliIo.rd cliWrOk A img B.readFile) →
      S.initiate = initDef X P →
      (∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ P F peer me) →
      ∀ stk : Nat, cliInitiateNeed B ≤ stk → stk ≤ 2 ^ 63 →
        subroutine_ok (Initiate.initProgExt img ext) ((Initiate.initProgExt img ext).fnAddr cliInitiateName)
          (initSlotSpec A img S stk))
    {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (needs : RunNeeds)
    (himg : Obj.Loads libsignalSessionImage img)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk HooksE.A0 img B.readFile))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (hneed : needs.initiate = cliInitiateNeed B) :
    (slotsOf HooksE.A0 img S needs).initiate.Ok img (cliExterns W) wrapInitiateName :=
  cliInitiate_ext_slotOk_of_ok (ext := cliHookExterns W) B S needs
    (Initiate.cliInitiate_ok_of_ext @hExt W X B S himg hRead hS hok) hneed

end CryptoVerification.SignalSession.Cli.RunProofs
