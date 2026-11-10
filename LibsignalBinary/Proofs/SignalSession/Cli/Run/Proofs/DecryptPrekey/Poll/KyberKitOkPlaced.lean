/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.PreKeyKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KyberKitOk
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` CLI KyberPreKey Store-Kit Specification

Defines `cliKpkStoreSpecFullPlaced` (`b := 0#64` with `lsρ` / `lsmpl.base` offsets) and proves
quietness.
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
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.KitInst

/-- Relocatable `[LibsignalPlacement]` `cliKpkStoreSpecFull` over `cliKyberPreKeyStoreSpecPlaced`. -/
def cliKpkStoreSpecFullPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (kid ksid : BitVec 32) (kbk : PublicKey)
    (getShimStk getPollStk markShimStk markPollStk : Nat) : KyberPreKeyStoreSpec A 0#64 :=
  { cliKyberPreKeyStoreSpecPlaced A rd F0 pathOk kid ksid kbk
      getShimStk getPollStk markShimStk markPollStk with
    storeAt := cliKpkStoreAtFull A rd F0 pathOk kid ksid kbk }

theorem cliKpkStoreSpecFullPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (s1 s2 s3 s4 : Nat) :
    (cliKpkStoreSpecFullPlaced A rd F0 pathOk kid ksid kbk s1 s2 s3 s4).Quiet :=
  cliKpkStoreSpec_quiet (A := A) (b := 0#64) rd F0 pathOk kid ksid kbk
    (cliKpkGetSide A rd F0 pathOk kid) s1 s2 s3 s4 pkBoxAt_memRegion kpkMarkBoxAt_memRegion

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
