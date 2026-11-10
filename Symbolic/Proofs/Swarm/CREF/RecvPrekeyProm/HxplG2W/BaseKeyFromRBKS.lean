/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBadG2.Frame
public import Symbolic.Proofs.Swarm.CREF.BobRecBaseKey
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.CBadG2.StampsReachBob
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Session Base-Key Membership on Session Promotion

Proves `prom_baseKeyInSession_of_rbks`: under `BobRecordBaseKeyInSession` and
`EligibleForSessionPromotion`, the parsed wire base key matches an entry of `sessionBaseKeys` for
Bob's current snapshot after delivering two `Move.attackerSend` steps across a `CBadSigmaFrame`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)

theorem stampsLt_of_mem_sessionBaseKeys
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {ts stateIdx : Nat} {tr : ExecTrace}
    (hreach : tr.Reachable reachability) (hlen : tr.length ≤ ts)
    {ek : DY.Bytes} (hek : ek ∈ sessionBaseKeys tr stateIdx) :
    TR.FreshSigma.StampsLt interpretation S g ts ek := by
  rcases hat : (tr.at? stateIdx : Option Symbolic.Swarm.COMPOSED.CompTrace.TRStEntry) with _ | ⟨⟨p, st⟩⟩
  · unfold sessionBaseKeys DY.ExecTrace.getLocalStateAt at hek; rw [hat] at hek; cases hek
  · rw [sessionBaseKeys_eq_sbkOf hat] at hek
    obtain ⟨i, _, hfind⟩ := List.mem_filterMap.mp hek
    rcases hev : tr.getEventAt ComposedEvent i with _ | ⟨s', d⟩ <;> rw [hev] at hfind
    · cases hfind
    · dsimp only at hfind
      split_ifs at hfind with hs
      rcases hpq : tr.getEventAt PQXDH.PQXDHEvent d with _ | ev <;> rw [hpq] at hfind
      · cases hfind
      · cases ev <;> cases hfind
        rename_i b a ikB ikA spk pqpk opk ct keys
        exact g2b_bobDoneEk_stampsLt_of_reachable interpretation S g ts hreach hlen
          d b a ikB ikA spk pqpk opk ek ct keys hpq

/-- Ties `pf.baseKey.take 33` to `sessionBaseKeys` of `stateIdx₀` after two `Move.attackerSend`
steps from `BobRecordBaseKeyInSession` and `EligibleForSessionPromotion` across `CBadSigmaFrame`. -/
theorem prom_baseKeyInSession_of_rbks
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g g' : Ghost} {ms : List Move} {records : Participant → Option HwBytes}
    {rec b : HwBytes} {pf : PreKeyFields}
    {stateIdx₀ : Nat} {st₀ : DY.Libsignal.TripleRatchet.TRState}
    (hpm : EligibleForSessionPromotion rec b)
    (hpf : parsePreKeyWire b = some pf)
    (hlook : records r.bob = some rec)
    (hbks : BobRecordBaseKeyInSession interpretation r S g ms records)
    (hrun : ModelRun r ms)
    (hst : ((PersistentLocalState.getLocalState r.bob stateIdx₀ :
        Traceful DY.Libsignal.TripleRatchet.TRState).run (runTraceMoves r ms)).1 = some st₀)
    (hcur : DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) stateIdx₀ = true)
    (hfr : CBadSigmaFrame g g' (runTraceMoves r ms).length)
    (x y : DY.Bytes) :
    ∃ ek ∈ sessionBaseKeys (runTraceMoves r (ms ++ [Move.attackerSend x, Move.attackerSend y]))
        stateIdx₀,
      pf.baseKey.take 33 = ecKey (gamma interpretation S g' ek) := by
  obtain ⟨rr, p, hrr, -, hp, hab⟩ := hpm
  rw [hp] at hpf
  cases hpf
  have hlook' : records r.bob = some (recordBytes rr) := hrr ▸ hlook
  obtain ⟨ek, hek, heq⟩ := hbks rr hlook' stateIdx₀ st₀ hst hcur
  have hle : runTraceMoves r ms ≤ runTraceMoves r (ms ++ [Move.attackerSend x, Move.attackerSend y]) :=
    runTrace_le_append r ms _
  have hstamp := stampsLt_of_mem_sessionBaseKeys interpretation S g hrun.2.2.1.1 (Nat.le_refl _) hek
  have hga := cbadG2_gammaAgree_of_sigmaFrame interpretation S hfr
  refine ⟨ek, sessionBaseKeys_mono hle stateIdx₀ hek, ?_⟩
  rw [← hab, heq, cbadG2_gamma_eq hga hstamp]

end Symbolic.Swarm.CREF
