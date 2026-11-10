/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed CLI `IdentityFiles` Store Specification

Relocatable `[LibsignalPlacement]` instantiation of `cliIdentityStoreSpec` at base `0#64`.
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs

/-- Relocatable `IdentityStoreSpec` for CLI `IdentityFiles` at base `0#64`. -/
def cliIdentityStoreSpecPlaced [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (peer : AddrGhost) (s1 s2 s3 s4 : Nat) : IdentityStoreSpec A 0#64 :=
  { cliIdentityStoreSpec A 0#64 rd F0 pathOk peer s1 s2 s3 s4 with
    id_vt := lsρ cliIdentityVtSym
    trustShimOff := lsmpl.base 601
    trustFutVtOff := lsρ idTrustFutVtSym
    trustPollOff := lsmpl.base 566
    trustFutDropOff := lsDropOffPlaced
    saveShimOff := lsmpl.base 600
    saveFutVtOff := lsρ idSaveFutVtSym
    savePollOff := lsmpl.base 565
    saveFutDropOff := lsDropOffPlaced
    trustFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    saveFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

theorem cliIdentityStoreSpecPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat} :
    (cliIdentityStoreSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4).Quiet :=
  ⟨fun _ _ _ _ => NoFsEv.nil, fun _ _ _ => NoFsEv.nil⟩

theorem cliIdentityStoreSpecPlaced_saveUpdate_inv [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {g : IdGhost} {rem : AddrVal} {k : IdentityKey} {ans : Except Unit IdentityChange}
    (hinv : CliIdInv rd F0 pathOk peer g) (hrem : rem = peer.val) :
    CliIdInv rd F0 pathOk peer
      ((cliIdentityStoreSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4).saveUpdate g rem k ans) :=
  cliIdentityStoreSpec_saveUpdate_inv (A := A) (b := 0#64)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (k := k) (ans := ans) hinv hrem

theorem cliIdentityStoreSpecPlaced_saveUpdate_own [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {g : IdGhost} {rem : AddrVal} {k : IdentityKey} {ans : Except Unit IdentityChange} :
    ((cliIdentityStoreSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4).saveUpdate g rem k ans).own =
      g.own :=
  cliIdentityStoreSpec_saveUpdate_own (A := A) (b := 0#64) (rd := rd) (F0 := F0)
    (pathOk := pathOk) (peer := peer) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
    (g := g) (rem := rem) (k := k) (ans := ans)

theorem cliIdentityStoreSpecPlaced_futDrop [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (lsProg_547 H) (lsmpl.base 547) futDropSpec :=
  futDrop_block_placed_ok H

end CryptoVerification.SignalSession.Cli.KitInst
