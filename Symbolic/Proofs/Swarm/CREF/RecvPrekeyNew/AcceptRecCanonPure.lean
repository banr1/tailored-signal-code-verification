/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieNormPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptBinPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRecSizePure

/-!
# Record Canonicality of Bob's Post-Handshake Session

Proves `PureTRRecordCanon` for the serialized session record `sm.state` returned by an accepting
`session_recv_prekey` call.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.AcceptD

cref_open

open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.LibsignalTripleRatchet
open CryptoProofLib.Refinement
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (StateAndMessage)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open Symbolic.Swarm.CREF.CliPure (e5_senderClamp_of_decrypt e5l_clamp_fix recvPrekey_accept_canon)

/-- Bob's returned session record `sm.state` satisfies `PureTRRecordCanon` under `AcceptTieD` and
the length bound `sm.state.length < 2 ^ 32 - 2 ^ 20`. -/
theorem recCanon_of_acceptTieD {interpretation : ExternInterpretation}
    (hCrypto : ExternCryptoLawsHold interpretation)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {r₀ : DY.Libsignal.Composed.Refinement.ProtocolSetup}
    (p₀ : DY.Participant) {p : PreKeyFields} {d pt : HwBytes} {sm : StateAndMessage}
    (hbase : ((p.baseKey.take 33).drop 1).length = 32)
    (htie : AcceptTieD interpretation r p d pt sm)
    (hlen : sm.state.length < 2 ^ 32 - 2 ^ 20) :
    Symbolic.Swarm.CREF.TR.PureTRRecordCanon r₀ p₀ sm.state := by
  obtain ⟨st0, st', _expected, hrt, hinv, hsk, hdec⟩ := htie
  obtain ⟨_, f248, hscope, hbin, hstate⟩ := hrt
  have hk2 : (secretBytes r 2).length = 32 := by
    rw [(TR.secretBytes_eq r hwf.1).2.2.1]
    exact hwf.2.1 (10, 32) (by rw [TR.setupRandomsAt_eq r hwf.1]; cases r.withOpk <;> simp)
  have hcl0 : ∀ sc, st0.senderChain = some sc →
      CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes =
        sc.ratchetKey.privateKey.bytes := by
    intro sc hsc
    rw [hsk sc hsc]
    exact e5l_clamp_fix _ hk2
  obtain ⟨hcl', hrem_eq⟩ := e5_senderClamp_of_decrypt hcl0 hdec
  have hooo := spqrOoo_of_acceptDecrypt hCrypto hinv hdec
  obtain ⟨_, _, _, _, _, _, _, hrem0, _, _, _, _⟩ := hinv
  have halice : (p.baseKey.take 33).length = 33 := by
    have h := hbase
    simp only [List.length_drop] at h
    omega
  rw [hstate] at hlen ⊢
  exact recvPrekey_accept_canon r₀ p₀ hscope hbin (hrem_eq.trans hrem0)
    halice hcl' hooo hlen

end Symbolic.Swarm.CREF.CliPure.AcceptD
