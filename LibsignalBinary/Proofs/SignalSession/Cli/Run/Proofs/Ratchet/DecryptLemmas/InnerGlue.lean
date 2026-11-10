/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.Spec
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1Trap
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Drops
import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Drops.Chain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.DropLocal2Ext
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.TripleRatchet.Glue

/-!
# Inner Store-Kit Contract Instantiation for `decrypt_signal`

Instantiates `InnerDecryptOk` and its `CliExternsOk`-parametric counterpart `InnerDecryptOkCliExt`
for `signal_session_ratchet::decrypt_signal` by combining the public-API store-kit contract, the V1
SPQR record decryption contract, `DropSessionStructureLocal2OkExt`, and the `scopeKit` store
invariants.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs

theorem decCalleesTP_trap_cli {img : Obj.Image} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecCalleesTP_trap
      img W.C E2E.HooksE.A0 0#64 (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) (cliExterns W) (fun _ => True) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecCalleesTP_trap.of_uncond
    (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_vregs_ok_PTight_trap
      W.C E2E.HooksE.A0 0#64 W.Q.K (cliExterns W) img
      (Slots.cliExterns_tripleRatchetHooks W (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K))
      (Slots.cliExterns_spqrHooks W)
      himg)
    (CryptoVerification.LibsignalTripleRatchet.Glue.remoteIdentityKeyOk_ext
      img E2E.HooksE.A0 (trTrapExterns W.C (cliExterns W)) himg)
    (CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.drop_session_structure_local2_ok_ext
      (Slots.allocContracts_trTrap W img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_ok_ext
        (Slots.allocContracts_trTrap W img)))

/-- Instantiates `InnerDecryptOk` for `decrypt_signal` at `decSessKit`, `decIdKit`,
`StoresGhost.opened`, and `Slots.scopeKit`. -/
theorem innerDecryptOk {img : Obj.Image} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img) :
    InnerDecryptOk img W B := by
  intro F0 peer hok
  dsimp only [decSessKit, decIdKit]
  have hok_fn :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.cliDecryptSignalWithStores_okVTP_distinct_fs_cli
      W (img := img) (ctl := 0#64) (S := E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) (F0 := F0)
      (Scope := Slots.scopeKit) (Q := fun _ => True) (peer := peer)
      (st0 := StoresGhost.opened.sessions) (ist0 := StoresGhost.opened.identity)
      (readStk := B.readFile)
      (s1 := SessKit.loadShimNeed) (s2 := SessKit.loadPollNeed B.readFile)
      (s3 := SessKit.storeShimNeed) (s4 := SessKit.storePollNeedX)
      (is1 := IdKit.trustShimNeed) (is2 := IdKit.trustPollNeed B.readFile)
      (is3 := IdKit.saveShimNeed) (is4 := IdKit.savePollNeed B.readFile)
      himg
      (Slots.sessDeserialize_scopeKit_cli W himg)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (fun _ hr => Slots.scopeKit_recordInScopeP hr)
      (fun x rec pt rec' haddr hsc hdec =>
        Slots.cliDecModelRecOkAt_opened (Scope₀ := Slots.scopeIn) (fun _ h => h) hok x rec rec' pt haddr hsc hdec)
      (decCalleesTP_trap_cli W himg)
      (fun _ _ ses hsc hcur => ⟨Slots.scopeKit_pqrState_lt hsc.1 ses hcur, trivial⟩)
  rw [← CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC_eq_fnAddr_ext
    (cliExterns W) himg] at hok_fn
  exact hok_fn

/-! ## Parametric `CliExternsOk` instantiation -/

/-- Assembles `DecCalleesTPExt` on `tripleRatchetProgAtExt img.base (cliExternsWith ext)` from the
tight record-decryption region contract and `DropSessionStructureLocal2OkExt`. -/
theorem decCalleesTPExt_of_region_and_drop {img : Obj.Image} {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hreg : region_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight P.C A 0#64 uuidTryParse
        (E2E.pqxdhSpqrModel P) img).withVRegs)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
      img.base A (cliExternsWith ext)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecCalleesTPExt
      img P.C A 0#64 (E2E.pqxdhSpqrModel P) (cliExternsWith ext) (fun _ => True) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecCalleesTPExt.of_uncond
    hreg
    (CryptoVerification.LibsignalTripleRatchet.Glue.remoteIdentityKeyOk_ext
      img A (cliExternsWith ext) himg)
    hdrop

/-- Instantiates `InnerDecryptOkCliExt` from `CliExternsOk` and `DecCalleesTPExt`. -/
theorem innerDecryptOkCliExt_of_callees {img : Obj.Image} {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hCallees : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecCalleesTPExt
      img P.C A 0#64 (E2E.pqxdhSpqrModel P) (cliExternsWith ext) (fun _ => True))
    (hreadStk : extHookStack ≤ B.readFile := by decide) :
    InnerDecryptOkCliExt img P A ext B := by
  intro F0 peer hok
  dsimp only [decSessKitExt, decIdKitExt]
  have hok_fn :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.cliDecryptSignalWithStores_okVTP_distinct_fs_ext
      (P := P) (A := A) (ext := ext) (img := img) (ctl := 0#64) (S := E2E.pqxdhSpqrModel P) (F0 := F0)
      (Scope := Slots.scopeKit) (Q := fun _ => True) (peer := peer)
      (st0 := StoresGhost.opened.sessions) (ist0 := StoresGhost.opened.identity)
      (readStk := B.readFile)
      (s1 := SessKit.loadShimNeed) (s2 := SessKit.loadPollNeed B.readFile)
      (s3 := SessKit.storeShimNeed) (s4 := SessKit.storePollNeedX)
      (is1 := IdKit.trustShimNeed) (is2 := IdKit.trustPollNeed B.readFile)
      (is3 := IdKit.saveShimNeed) (is4 := IdKit.savePollNeed B.readFile)
      hOk himg
      (Slots.sessDeserialize_scopeKit_ext hOk himg)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (fun _ hr => Slots.scopeKit_recordInScopeP hr)
      (fun x rec pt rec' haddr hsc hdec =>
        Slots.cliDecModelRecOkAt_opened (Scope₀ := Slots.scopeIn) (fun _ h => h) hok
          x rec rec' pt haddr hsc hdec)
      hCallees
      (fun _ _ ses hsc hcur => ⟨Slots.scopeKit_pqrState_lt hsc.1 ses hcur, trivial⟩)
      hreadStk
  rw [← CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC_eq_fnAddr_ext
    (cliExternsWith ext) himg] at hok_fn
  exact hok_fn

theorem innerDecryptOkCliExt_of_region_and_drop {img : Obj.Image} {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hreg : region_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight P.C A 0#64 uuidTryParse
        (E2E.pqxdhSpqrModel P) img).withVRegs)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
      img.base A (cliExternsWith ext))
    (hreadStk : extHookStack ≤ B.readFile := by decide) :
    InnerDecryptOkCliExt img P A ext B :=
    innerDecryptOkCliExt_of_callees B hOk himg
      (decCalleesTPExt_of_region_and_drop himg hreg hdrop) hreadStk

theorem drop_session_structure_local2_ok_cliExternsWith {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (b : BitVec 64)
    (hOk : CliExternsOk P A ext) :
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
      b A (cliExternsWith ext) :=
  drop_session_structure_local2_ok_of_dealloc
    (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.AllocContracts4K.of_cliExternsOk b hOk).dealloc

theorem decCalleesTPExt_of_region {img : Obj.Image} {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hreg : region_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight P.C A 0#64 uuidTryParse
        (E2E.pqxdhSpqrModel P) img).withVRegs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecCalleesTPExt
      img P.C A 0#64 (E2E.pqxdhSpqrModel P) (cliExternsWith ext) (fun _ => True) :=
  decCalleesTPExt_of_region_and_drop himg hreg
    (drop_session_structure_local2_ok_cliExternsWith img.base hOk)

/-- Instantiates `InnerDecryptOkCliExt` from `CliExternsOk` and the tight V1 record-decryption
region contract, discharging `DropSessionStructureLocal2OkExt` and both store kits internally. -/
theorem innerDecryptOkCliExt_of_region {img : Obj.Image} {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hreg : region_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight P.C A 0#64 uuidTryParse
        (E2E.pqxdhSpqrModel P) img).withVRegs)
    (hreadStk : extHookStack ≤ B.readFile := by decide) :
    InnerDecryptOkCliExt img P A ext B :=
  innerDecryptOkCliExt_of_region_and_drop B hOk himg hreg
    (drop_session_structure_local2_ok_cliExternsWith img.base hOk) hreadStk

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas
