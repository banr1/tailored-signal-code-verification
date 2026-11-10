/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.COMPOSED.CompSchedule
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Cross-Epoch Skipped-Key and Chain-Seed Disjointness

On any reachable composed trace, a skipped message-key seed logged in `TREvent.SkippedKeyStored`
and a chain seed derived from a receiver chain `c ∈ st.recv` of a stored `TRState` snapshot `st`
collide only when they belong to the same ratchet epoch and message counter.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

open DY
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain consumeMessageKey kdfCk chainKeyAt)
open DY.Libsignal.TripleRatchet (TRState TREvent)
open DY.Libsignal.TripleRatchet.Cheval (StateStoredAt)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open Symbolic.Swarm.COMPOSED.CompTermAlgebra (kdfCk_snd_inj chainKeyAt_add)
open Symbolic.Swarm.COMPOSED.CompTrace (TREntry)
open Symbolic.Swarm.COMPOSED.CompRatchet (chainKeyAt_root_inj consumeMessageKey_compSchedule
  compScheduleInv_reachable)

/-- On any reachable composed trace `tr`, if `st` is stored at `stateIdx`, `c ∈ st.recv`, and
`TREvent.SkippedKeyStored s pk ctr seed_s rIdx_s srcIdx` is logged at `skIdx`, then
`seed_s = (kdfCk (chainKeyAt c.chainKey j)).2` forces `rIdx_s = c.rIdx` and
`ctr.toNat = c.index.toNat + j`. -/
theorem rIdx_and_counter_eq_of_skippedSeed_eq_chainKeyAt
    {tr : ExecTrace} (hreach : tr.Reachable reachability)
    {p : Participant} {stateIdx skIdx rIdx_s srcIdx j : Nat}
    {st : TRState} {c : RecvChain} {s : SessionInfo}
    {pk seed_s : Bytes} {ctr : UInt32}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st)
    (hc : c ∈ st.recv)
    (hsk : (tr.at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored s pk ctr seed_s rIdx_s srcIdx⟩)
    (hseed : seed_s = (kdfCk (chainKeyAt c.chainKey j)).2) :
    rIdx_s = c.rIdx ∧ ctr.toNat = c.index.toNat + j := by
  have hInv := compScheduleInv_reachable hreach
  have hst_at : StateStoredAt p st stateIdx tr :=
    FreshSigma.at?_eq_some_of_getLocalState_some hst
  obtain ⟨_, _, _, ⟨_, ikm, dh₁, _, _, _, hrecv⟩, _⟩ := hInv.stateOK p st stateIdx hst_at
  obtain ⟨hc_pos, _, _, ck₀, hroot_c, hck_c⟩ := hrecv c hc
  obtain ⟨hs_pos, _, _, ikm_s, dh₁_s, ck₀_s, _, hroot_s, hseed_s⟩ :=
    hInv.eventOK (TREvent.SkippedKeyStored s pk ctr seed_s rIdx_s srcIdx)
      ⟨skIdx, by rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]⟩
  have hchain_eq :
      chainKeyAt ck₀_s ctr.toNat = chainKeyAt ck₀ (c.index.toNat + j) := by
    apply kdfCk_snd_inj
    rw [← hseed_s, hseed, hck_c, ← chainKeyAt_add]
  obtain ⟨hck₀_eq, hctr_eq⟩ :=
    chainKeyAt_root_inj hroot_s.isChainRoot hroot_c.isChainRoot hchain_eq
  subst hck₀_eq
  have hm_eq : rIdx_s - 1 = c.rIdx - 1 := (hroot_s.eq_iff hroot_c).1
  exact ⟨by omega, hctr_eq⟩

/-- On any reachable composed trace `tr`, if `st` is stored at `stateIdx`, `c ∈ st.recv`,
`consumeMessageKey c n = some (seed_c, c')`, and
`TREvent.SkippedKeyStored s pk ctr seed_s rIdx_s srcIdx` is logged at `skIdx`, then
`seed_s = seed_c` forces `rIdx_s = c.rIdx` and `ctr = n`. -/
theorem rIdx_and_counter_eq_of_skippedSeed_eq_consumeMessageKey
    {tr : ExecTrace} (hreach : tr.Reachable reachability)
    {p : Participant} {stateIdx skIdx rIdx_s srcIdx : Nat}
    {st : TRState} {c c' : RecvChain} {s : SessionInfo}
    {pk seed_c seed_s : Bytes} {n ctr : UInt32}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st)
    (hc : c ∈ st.recv)
    (hcons : consumeMessageKey c n = some (seed_c, c'))
    (hsk : (tr.at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored s pk ctr seed_s rIdx_s srcIdx⟩)
    (hseed : seed_s = seed_c) :
    rIdx_s = c.rIdx ∧ ctr = n := by
  have hInv := compScheduleInv_reachable hreach
  have hst_at : StateStoredAt p st stateIdx tr :=
    FreshSigma.at?_eq_some_of_getLocalState_some hst
  obtain ⟨_, _, _, ⟨_, ikm, dh₁, _, _, _, hrecv⟩, _⟩ := hInv.stateOK p st stateIdx hst_at
  obtain ⟨_, _, hidx_le, _, _, ck₀, hroot_c, hck_c, hseed_c, _⟩ :=
    consumeMessageKey_compSchedule (hrecv c hc) hcons
  have hadv : chainKeyAt c.chainKey (n.toNat - c.index.toNat) = chainKeyAt ck₀ n.toNat := by
    rw [hck_c, ← chainKeyAt_add]
    congr 1
    omega
  have hseed' : seed_s = (kdfCk (chainKeyAt c.chainKey (n.toNat - c.index.toNat))).2 := by
    rw [hseed, hseed_c, hadv]
  obtain ⟨hrIdx, hctr_nat⟩ :=
    rIdx_and_counter_eq_of_skippedSeed_eq_chainKeyAt hreach hst hc hsk hseed'
  have hctr_bv : ctr.toBitVec.toNat = n.toBitVec.toNat := by
    change ctr.toNat = n.toNat
    omega
  exact ⟨hrIdx, UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hctr_bv)⟩

/-- On `runTraceMoves r₀ ms`, any `SkippedKeyStored` seed equal to a `consumeMessageKey` seed from
`c ∈ st.recv` shares the same ratchet epoch (`rIdx_s = c.rIdx`). -/
def SkippedSeedNeChainSeed (r₀ : ProtocolSetup) (ms : List Move) : Prop :=
  ∀ p stateIdx st c n seed_c c' skIdx pk ctr seed_s rIdx_s srcIdx,
    ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms)).1 = some st →
    c ∈ st.recv → consumeMessageKey c n = some (seed_c, c') →
    ((runTraceMoves r₀ ms).at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) pk ctr seed_s rIdx_s srcIdx⟩ →
    seed_s = seed_c → rIdx_s = c.rIdx

/-- Every `ModelRun r₀ ms` satisfies `SkippedSeedNeChainSeed r₀ ms`. -/
theorem skippedSeed_ne_chainSeed {r₀ : ProtocolSetup} {ms : List Move}
    (hrun : ModelRun r₀ ms) : SkippedSeedNeChainSeed r₀ ms := by
  intro p stateIdx st c n seed_c c' skIdx pk ctr seed_s rIdx_s srcIdx hst hc hcons hsk hseed
  have hreach : (runTraceMoves r₀ ms).Reachable reachability := by
    have hall := hrun.2.2.1.2.2 ms.length
    rwa [List.take_length] at hall
  exact (rIdx_and_counter_eq_of_skippedSeed_eq_consumeMessageKey hreach hst hc hcons hsk hseed).1

end Symbolic.Swarm.CREF.TR
