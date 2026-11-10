/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bundle
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.InitFiles

/-!
# Top-Level `S₀` Domain and Agreement Proofs for `initiate`

Proves `initOk₀_pqInit_proof` and `pqInitiateAgrees_initDef_proof` from `InitPaths`, `InitFiles`,
and `agree_pqInit`, discharging the `S₀` domain and model-agreement obligations exported by
`Initiate/Spec.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.InitS0

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

theorem initOk₀_pqInit_proof (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = none) :
    InitOk₀ W (runFiles (pqInitInputs W st b t)) (RunRefine.addrValE st.party.other)
      (RunRefine.addrValE st.party) :=
  ⟨InitS0.nameLt_party _, InitS0.textLt_party _, InitS0.sessPathOk_party _,
    InitS0.idPathOk_party _, InitS0.sessPathLt_party _, InitS0.idPathLt_party _,
    InitS0.keyPairLt_pqInit W st b t hwf, InitS0.idGet_pqInit W st b t,
    InitS0.noSession_pqInit W st b t hs, InitS0.distinctAcct_party st.party,
    InitS0.idPairDerived_pqInit W st b t⟩

theorem pqInitiateAgrees_initDef_proof (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hS : S.initiate = initDef X W) : RunRefine.PqInitiateAgrees S X W := by
  intro st b t bv hwf hs hbv
  rw [RunRefine.readBundleV_pqInit] at hbv
  injection hbv with hbv; subst hbv
  have hbe : bundleEOf? (RunRefine.bundleVE b) = some b := by
    rcases b with ⟨_regId, _opk, _spkId, _spkPub, spkSig, _kpkId, kpkPub, kpkSig, _idPub⟩
    simp only [bundleEOf?, RunRefine.bundleVE, spkSig.toList_length, kpkSig.toList_length,
      kpkPub.toList_length, ↓reduceDIte, InitS0.vec_eta, InitS0.opk_map_roundtrip]
  rw [hS]
  unfold initDef
  rw [hbe]
  dsimp only
  have hp : initParty (RunRefine.addrValE st.party.other) = st.party :=
    InitS0.initParty_eq st.party
  have hc : padCoins t.toList = t := InitS0.padCoins_vec_eq t _
  rw [hp, hc]
  exact InitS0.agree_pqInit X W st b t hwf hs

end CryptoVerification.SignalSession.Cli.RunProofs.InitS0
