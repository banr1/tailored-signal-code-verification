/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.COMPOSED.CompRatchet
import Symbolic.Proofs.Swarm.CREF.CBadG2.StampsReach
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Session Identifier Timestamp Freshness for Initiator Start

Proves `trRecvSid_fresh_alice`: on a reachable trace `runTraceMoves r₀ ms` of length at most `L`,
no receiver `MessageKey` or `SkippedKeyStored` event carries a session identifier of the form
`concat (dhPk (mkRand L 32)) rk`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.FreshSigma (StampsLt MemoStampsLt)
open DY.Libsignal.TripleRatchet (SessionInfo)
open DY.Libsignal.TripleRatchet (TREvent)
open Symbolic.Swarm.COMPOSED.CompTrace (mkRand)
open Symbolic.Swarm.COMPOSED.CompRatchet (compSessionOriginInv_reachable)

section Unsealed
unseal DY.Bytes

theorem rfsi_not_stampsLt_rand (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (L : Nat) :
    ¬ StampsLt i S g L (mkRand L 32) := by
  intro h
  unfold StampsLt gamma' at h
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g)] at h
  dsimp only [concretizeRandom, node, MemoStampsLt] at h
  split at h
  · next hz => exact absurd hz (by decide)
  · exact Nat.lt_irrefl L (h _ _ _ ({ timestamp := L, size := 32 } : DY.Random.Random DY.Bytes)
      (List.mem_cons_self ..) (BytesView.view_pack _))

end Unsealed

theorem rfsi_not_stampsLt_aliceSid (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (L : Nat)
    (rk : DY.Bytes) :
    ¬ StampsLt i S g L (DY.Concat.concat (DY.DiffieHellman.dhPk (mkRand L 32)) rk) := by
  intro h
  have h1 := ((FreshSigma.stampsLt_concat_pack i S g L ⟨_, rk⟩).mp h).1
  exact rfsi_not_stampsLt_rand i S g L ((FreshSigma.stampsLt_dhPk_pack i S g L ⟨_⟩).mp h1)

/-- On a reachable trace, the session descriptor `s` of every receiver `MessageKey` and
`SkippedKeyStored` event has a logged `ComposedEvent.HandshakeSession s d`. -/
theorem trRecvEv_handshakeSession {tr : ExecTrace} (hreach : tr.Reachable reachability)
    {s : SessionInfo} :
    (∀ seed pqSalt n r pIdx i, tr.EventLoggedAt
        (TREvent.MessageKey s .receiver seed pqSalt n r pIdx) i →
        ∃ d, tr.EventLogged (ComposedEvent.HandshakeSession s d)) ∧
    (∀ pk n seed r srcIdx i, tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed r srcIdx) i →
        ∃ d, tr.EventLogged (ComposedEvent.HandshakeSession s d)) := by
  have horig := compSessionOriginInv_reachable hreach
  refine ⟨fun seed pqSalt n r pIdx i hev => ?_, fun pk n seed r srcIdx i hev => ?_⟩
  · obtain ⟨d, _, hd, _⟩ := horig.mkSession _ _ _ _ _ _ _ ⟨i, hev⟩
    exact ⟨d, hd⟩
  · obtain ⟨d, _, hd, _⟩ := (horig.skippedOK _ _ _ _ _ _ ⟨i, hev⟩).2
    exact ⟨d, hd⟩

theorem trRecvSid_fresh_of_no_handshakeSession {tr : ExecTrace}
    (hreach : tr.Reachable reachability) {s : SessionInfo}
    (hno : ∀ d, ¬ tr.EventLogged (ComposedEvent.HandshakeSession s d)) :
    (∀ seed pqSalt n r pIdx i, ¬ tr.EventLoggedAt
        (TREvent.MessageKey s .receiver seed pqSalt n r pIdx) i) ∧
    (∀ pk n seed r srcIdx i, ¬ tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed r srcIdx) i) :=
  ⟨fun seed pqSalt n r pIdx i hev =>
      let ⟨d, hd⟩ := (trRecvEv_handshakeSession hreach).1 seed pqSalt n r pIdx i hev
      hno d hd,
    fun pk n seed r srcIdx i hev =>
      let ⟨d, hd⟩ := (trRecvEv_handshakeSession hreach).2 pk n seed r srcIdx i hev
      hno d hd⟩

theorem rfsi_no_handshakeSession_of_not_stampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {tr : ExecTrace} (hreach : tr.Reachable reachability) {L : Nat} (hL : tr.length ≤ L)
    {s : SessionInfo} (hns : ¬ StampsLt i S g L s.sid) :
    ∀ d, ¬ tr.EventLogged (ComposedEvent.HandshakeSession s d) := fun d hev =>
  hns (g2s_inv_of_reachable i S g hreach L hL
    (FreshSigma.traceEntriesLt_of_reachable i S g L hreach hL) s d hev)

theorem trRecvSid_fresh_of_not_stampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {tr : ExecTrace} (hreach : tr.Reachable reachability) {L : Nat} (hL : tr.length ≤ L)
    {s : SessionInfo} (hns : ¬ StampsLt i S g L s.sid) :
    (∀ seed pqSalt n r pIdx i, ¬ tr.EventLoggedAt
        (TREvent.MessageKey s .receiver seed pqSalt n r pIdx) i) ∧
    (∀ pk n seed r srcIdx i, ¬ tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed r srcIdx) i) :=
  trRecvSid_fresh_of_no_handshakeSession hreach
    (rfsi_no_handshakeSession_of_not_stampsLt i S g hreach hL hns)

/-- On a reachable trace `runTraceMoves r₀ ms` of length at most `L`, no receiver `MessageKey`
or `SkippedKeyStored` event carries a session descriptor with `sid = concat (dhPk (mkRand L 32)) rk`. -/
theorem trRecvSid_fresh_alice (r₀ : ProtocolSetup) (ms : List Move)
    (hrun : (runTraceMoves r₀ ms).Reachable reachability)
    (L : Nat) (hL : (runTraceMoves r₀ ms).length ≤ L) (rk : DY.Bytes) (s : SessionInfo)
    (hs : s.sid = DY.Concat.concat (DY.DiffieHellman.dhPk (mkRand L 32)) rk) :
    (∀ seed pqSalt n r pIdx i, ¬ (runTraceMoves r₀ ms).EventLoggedAt
        (TREvent.MessageKey s .receiver seed pqSalt n r pIdx) i) ∧
    (∀ pk n seed r srcIdx i, ¬ (runTraceMoves r₀ ms).EventLoggedAt
        (TREvent.SkippedKeyStored s pk n seed r srcIdx) i) := by
  let S₀ : OpaqueSymbolSemantics := ⟨fun _ _ => [], fun _ _ _ => [], fun _ _ => [], fun _ _ => [], fun _ _ => [],
    fun _ _ => [], fun _ _ => [], fun _ => [], fun _ _ => [], fun _ => [],
    fun _ _ _ => []⟩
  let g₀ : Ghost := ⟨fun _ _ => [], fun _ => []⟩
  exact trRecvSid_fresh_of_not_stampsLt (fun _ _ => none) S₀ g₀ hrun hL
    (by rw [hs]; exact rfsi_not_stampsLt_aliceSid _ S₀ g₀ L rk)

end Symbolic.Swarm.CREF.TR
