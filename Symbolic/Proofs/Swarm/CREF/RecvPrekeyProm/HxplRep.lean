/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import VCVio.Prelude.Core

/-!
# Inner-Message `recvRepresentations` Witness for PreKey Wire Messages

Proves `parsePreKeyWire_inner_tryFrom` and deduces non-emptiness of `recvRepresentations` on
`pf.message` whenever `parsePreKeyWire b = some pf`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open DY.Literal
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoProofLib.Refinement (ExternInterpretation)

theorem parsePreKeyWire_inner_tryFrom {b : HwBytes} {pf : PreKeyFields}
    (hpf : parsePreKeyWire b = some pf) :
    SignalMessage.tryFrom protoSignalCodec pf.message = Except.ok pf.inner := by
  unfold parsePreKeyWire at hpf
  rcases b with _ | ⟨t, body⟩
  · cases hpf
  · dsimp only at hpf
    split_ifs at hpf
    unfold parsePreKey at hpf
    rcases body with _ | ⟨vb, rest⟩
    · cases hpf
    · dsimp only at hpf
      split_ifs at hpf
      rcases hdec : decodePreKey rest with _ | m
      · rw [hdec] at hpf; cases hpf
      · rw [hdec] at hpf; dsimp only at hpf
        rcases hbk : m.baseKey with _ | bk <;> rcases hik : m.identityKey with _ | ik <;>
          rcases hmsg : m.message with _ | msg <;> rcases hsid : m.signedPreKeyId with _ | sid
        all_goals rw [hbk, hik, hmsg, hsid] at hpf; dsimp only at hpf; try cases hpf
        split_ifs at hpf
        rcases htry : SignalMessage.tryFrom protoSignalCodec msg with _ | inner
        · rw [htry] at hpf; cases hpf
        · rw [htry] at hpf
          injection hpf with hpf_eq
          subst hpf_eq
          exact htry

/-- Non-emptiness of `recvRepresentations` on `pf.message` for any `parsePreKeyWire b = some pf`. -/
theorem prom_recvRepresentations_nonempty_of_parsePreKeyWire
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    {b : HwBytes} {pf : PreKeyFields}
    (hpf : parsePreKeyWire b = some pf) :
    ∃ t : DY.Bytes, t ∈ recvRepresentations interpretation r₀ S g ms pf.message :=
  TR.RecvRep.recvRepresentations_nonempty_of_tryFrom
    interpretation r₀ S g ms pf.message pf.inner (parsePreKeyWire_inner_tryFrom hpf)

end Symbolic.Swarm.CREF
