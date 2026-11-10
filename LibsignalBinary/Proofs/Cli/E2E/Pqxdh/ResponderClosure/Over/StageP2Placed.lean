/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub5Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Stage P2 Over-Path Call-Stack Monotonicity Lemmas

Lifts the Stage P2 Over-path call-stack inequalities between `stageP2OverPureAndErrStack`,
`stageP2OverCallStack`, and `stageP2OverV1CallStack` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2

theorem p2_over_pure_le_callStack_placed [LibsignalPlacement] {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverPureAndErrStack ≤ stageP2OverCallStack spkKit kpkKit pkKit skit :=
  p2_over_pure_le_callStack spkKit kpkKit pkKit skit

theorem p2_over_pure_le_v1CallStack_placed [LibsignalPlacement] {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverPureAndErrStack ≤ stageP2OverV1CallStack spkKit kpkKit pkKit skit :=
  p2_over_pure_le_v1CallStack spkKit kpkKit pkKit skit

theorem p2_over_callStack_le_v1CallStack_placed [LibsignalPlacement] {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverCallStack spkKit kpkKit pkKit skit ≤
      stageP2OverV1CallStack spkKit kpkKit pkKit skit :=
  p2_over_callStack_le_v1CallStack spkKit kpkKit pkKit skit

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
end
