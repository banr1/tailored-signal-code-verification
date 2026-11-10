/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed CLI `SessionFiles` Store Specification

Relocatable `[LibsignalPlacement]` instantiation of `cliSessionStoreSpec` at base `0#64`.
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs

/-- Relocatable `SessionStoreSpec` for CLI `SessionFiles` at base `0#64`. -/
def cliSessionStoreSpecPlaced [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat) : SessionStoreSpec A 0#64 :=
  { cliSessionStoreSpec A 0#64 rd F0 pathOk Scope peer s1 s2 s3 s4 with
    ss_vt := lsρ cliSessionVtSym
    id_vt := lsρ cliIdentityVtSym
    loadShimOff := lsmpl.base 604
    storeShimOff := lsmpl.base 605
    loadFutVtOff := lsρ sessLoadFutVtSym
    storeFutVtOff := lsρ sessStoreFutVtSym
    loadPollOff := lsmpl.base 569
    storePollOff := lsmpl.base 570
    loadFutDropOff := lsDropOffPlaced
    storeFutDropOff := lsDropOffPlaced
    loadFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    storeFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

theorem cliSessionStoreSpecPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat} :
    (cliSessionStoreSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4).Quiet :=
  ⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩

theorem cliSessionStoreSpecPlaced_storeUpdate_inv [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {g : DirGhost} {rem : AddrVal}
    {rec : SessionRecord (List (BitVec 8))} {ans : Except Unit Unit}
    (hinv : CliSessInv rd F0 pathOk Scope peer g) (hrem : rem = peer.val)
    (hrec : (cliSessionStoreSpec A 0#64 rd F0 pathOk Scope peer s1 s2 s3 s4).RecOk rec) :
    CliSessInv rd F0 pathOk Scope peer
      ((cliSessionStoreSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4).storeUpdate g rem rec ans) :=
  cliSessionStoreSpec_storeUpdate_inv (A := A) (b := 0#64)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (ans := ans) hinv hrem hrec

theorem cliSessionStoreSpecPlaced_futDrop [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (lsProg_547 H) (lsmpl.base 547) futDropSpec :=
  futDrop_block_placed_ok H

end CryptoVerification.SignalSession.Cli.KitInst
