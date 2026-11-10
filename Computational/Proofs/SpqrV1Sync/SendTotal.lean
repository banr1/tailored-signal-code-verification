/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalRefinesCDefs
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Assembly

/-!
# SPQR V1 Bounded Send Totality

Proves `Corr.SpqrSendCorrectQ` for `spqrV1SessionUniformCoins` with send budget `q < 2 ^ 32` under
`Encaps1Total`, packaging the invariant reduction from `SendTotal.Defs` and `SendTotal.Assembly`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoGames.LibsignalSession (ShaCompress)

theorem spqrV1SessionB_sendCorrectQ_of (F : ShaCompress) (K : MlKem) (h : TopStmts F K)
    (hK : Encaps1Total K) (q : ℕ) (hq : q < 2 ^ 32) :
    CryptoGames.LibsignalSM.Corr.SpqrSendCorrectQ (spqrV1SessionUniformCoins F K) q := by
  obtain ⟨Inv, hinit, hsend, hrecv, htot⟩ := sendCorrectQ_of F K h hK q hq
  exact ⟨Inv, ⟨hinit, hsend, hrecv⟩, htot⟩

/-- `SpqrSendCorrectQ` for `spqrV1SessionUniformCoins` with send budget `q < 2 ^ 32`, assuming
`Encaps1Total`. -/
theorem spqrV1SessionB_sendCorrectQ (F : ShaCompress) (K : MlKem) (hK : Encaps1Total K) (q : ℕ)
    (hq : q < 2 ^ 32) : CryptoGames.LibsignalSM.Corr.SpqrSendCorrectQ (spqrV1SessionUniformCoins F K) q :=
  spqrV1SessionB_sendCorrectQ_of F K (topStmts F K) hK q hq

end CryptoVerification.SpqrV1Sync.SendTotal
