/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced
public import LibsignalBinary.Proofs.RecordCodecs.SignedAssembly
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitStk
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` CLI PreKey, SignedPreKey, and KyberPreKey Store-Kit Specs

Instantiates `PreKeyStoreSpec A 0#64`, `SignedPreKeyStoreSpec A 0#64`, and
`KyberPreKeyStoreSpec A 0#64` with `lsρ cli*VtSym` vtable addresses.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## 1. Placed `PreKeyStoreSpec`, `SignedPreKeyStoreSpec`, and `KyberPreKeyStoreSpec` (`b := 0#64`) -/

/-- Relocatable `[LibsignalPlacement]` `PreKeyStoreSpec A 0#64` with `pk_vt := lsρ cliPreKeyVtSym`
and placed shim/future-vtable/poll/drop addresses. -/
def cliPreKeyStoreSpecPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32)
    (getShimStk getPollStk removeShimStk removePollStk : Nat) : PreKeyStoreSpec A 0#64 :=
  { cliPreKeyStoreSpec A 0#64 rd F0 pathOk pid
      getShimStk getPollStk removeShimStk removePollStk with
    pk_vt := lsρ cliPreKeyVtSym
    getShimOff := lsmpl.base 608
    getFutVtOff := lsρ pkGetFutVtSym
    getPollOff := lsmpl.base 573
    getFutDropOff := lsDropOffPlaced
    removeShimOff := lsmpl.base 610
    removeFutVtOff := lsρ pkRemoveFutVtSym
    removePollOff := lsmpl.base 575
    removeFutDropOff := lsDropOffPlaced
    getFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    removeFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

/-- Relocatable `[LibsignalPlacement]` `SignedPreKeyStoreSpec A 0#64` with `spk_vt := lsρ cliSignedPreKeyVtSym`
and placed shim/future-vtable/poll/drop addresses. -/
def cliSignedPreKeyStoreSpecPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (sid : BitVec 32)
    (getShimStk getPollStk : Nat) : SignedPreKeyStoreSpec A 0#64 :=
  { cliSignedPreKeyStoreSpec A 0#64 rd F0 pathOk sid getShimStk getPollStk with
    spk_vt := lsρ cliSignedPreKeyVtSym
    getShimOff := lsmpl.base 606
    getFutVtOff := lsρ spkGetFutVtSym
    getPollOff := lsmpl.base 571
    getFutDropOff := lsDropOffPlaced
    getFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

/-- Relocatable `[LibsignalPlacement]` `KyberPreKeyStoreSpec A 0#64` with `kpk_vt := lsρ cliKyberPreKeyVtSym`
and placed shim/future-vtable/poll/drop addresses. -/
def cliKyberPreKeyStoreSpecPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (kid ksid : BitVec 32) (kbk : PublicKey)
    (getShimStk getPollStk markShimStk markPollStk : Nat) : KyberPreKeyStoreSpec A 0#64 :=
  { cliKyberPreKeyStoreSpec A 0#64 rd F0 pathOk kid ksid kbk
      getShimStk getPollStk markShimStk markPollStk with
    kpk_vt := lsρ cliKyberPreKeyVtSym
    getShimOff := lsmpl.base 611
    getFutVtOff := lsρ kpkGetFutVtSym
    getPollOff := lsmpl.base 576
    getFutDropOff := lsDropOffPlaced
    markShimOff := lsmpl.base 613
    markFutVtOff := lsρ kpkMarkFutVtSym
    markPollOff := lsmpl.base 578
    markFutDropOff := lsDropOffPlaced
    getFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    markFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

theorem cliPreKeyStoreSpecPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (pid : BitVec 32) (s1 s2 s3 s4 : Nat) :
    (cliPreKeyStoreSpecPlaced A rd F0 pathOk pid s1 s2 s3 s4).Quiet :=
  cliPreKeyStoreSpec_quiet (A := A) (b := 0#64) rd F0 pathOk pid s1 s2 s3 s4

theorem cliSignedPreKeyStoreSpecPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (sid : BitVec 32) (s1 s2 : Nat) :
    (cliSignedPreKeyStoreSpecPlaced A rd F0 pathOk sid s1 s2).Quiet :=
  cliSignedPreKeyStoreSpec_quiet (A := A) (b := 0#64) rd F0 pathOk sid s1 s2

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
