/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf

/-!
# SPQR V1 Prenegotiated Receive Step Definitions

Defines `PrenegotiatedStep` and `recvAddEpochOpt` capturing the pre-negotiation transition and
optional epoch addition in `Top.recv`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open Symbolic.Swarm.TRREF.SpqrSemOf

/-- Relation capturing how `statePb` is obtained from `prenegotiatedStatePb` in `Top.recv`:
either `Ordering::Equal` (`statePb = prenegotiatedStatePb`) or `Ordering::Less` (`initInner` and
`chainFrom` from `prenegotiatedStatePb.versionNegotiation = some vn`). -/
inductive PrenegotiatedStep (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (prenegotiatedStatePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB) :
    PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB → Prop where
  | equal :
      PrenegotiatedStep F K mac prenegotiatedStatePb prenegotiatedStatePb
  | less (vn : VersionNegotiationPB) (v : Version) (dir : Direction)
      (inner' : Option (spqrDepsWithMac F K mac).V1StatePB) (chain' : Chain) :
      prenegotiatedStatePb.versionNegotiation = some vn →
      Direction.fromI32? vn.direction = some dir →
      initInner (spqrDepsWithMac F K mac) v dir vn.authKey = .ok inner' →
      chainFrom (spqrHkdfWith F) prenegotiatedStatePb.chain (some vn) = .ok chain' →
      PrenegotiatedStep F K mac prenegotiatedStatePb {
        inner := inner'
        versionNegotiation := none
        chain := some chain'.intoPb
      }

/-- Optional epoch addition in `Top.recv`. -/
def recvAddEpochOpt (hkdf : HkdfFn) (chain0 : Chain) (key : Option EpochSecret) :
    SpqrApiResult Chain :=
  match key with
  | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch hkdf epochSecret)
  | none => pure chain0

end Symbolic.Swarm.TRREF
