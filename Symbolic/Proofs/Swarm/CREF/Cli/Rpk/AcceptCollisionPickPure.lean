/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBadReadableBridge
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.CBad
public import Symbolic.Proofs.Swarm.CREF.CBadG2.Frame
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# `AcceptCollision` Witness Selection and `CBadBridgeHyp` Transport

Provides `acceptCollision_pick` to extract a non-colliding accepted representation from
`¬ AcceptCollision`, along with `cBadBridgeHyp_of_acceptsBy` and `cBadG2_of_rawWitness`
to transport `CleanBy`, `recvRepresentations`, and `¬ RecvCollision` across `CBadSigmaFrame`
and attacker-known message extensions.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement

/-- Extracts an accepting representation `t_star ∈ recvRepresentations` with `¬ RecvCollision`
from `¬ AcceptCollision` and a single accepted representation `t_m`. -/
theorem acceptCollision_pick
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {ms : List Move} {τ₁ : List MachineEvent} {e : MachineEvent} {τ₂ : List MachineEvent}
    {b : HwBytes} {t_m : DY.Bytes}
    (hnoAC : ¬ AcceptCollision interpretation r S who ok g ms τ₁ e τ₂ b)
    (ht_m : t_m ∈ recvRepresentations interpretation r S g ms b)
    (hacc_m : ModelAcceptsTermAfterCoinSplit interpretation r S who ok g ms τ₁ e τ₂ t_m) :
    ∃ t_star ∈ recvRepresentations interpretation r S g ms b,
      ModelAcceptsTermAfterCoinSplit interpretation r S who ok g ms τ₁ e τ₂ t_star ∧
      ¬ RecvCollision interpretation r S g ms t_star := by
  refine Classical.byContradiction fun hno => hnoAC ⟨⟨t_m, ht_m, hacc_m⟩, fun t' ht' hacc' => ?_⟩
  exact Classical.byContradiction fun hnc => hno ⟨t', ht', hacc', hnc⟩

theorem not_recvCollision_append_map_attackerSend
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g₁ : Ghost}
    {ms : List Move} {t : DY.Bytes} (ext : List DY.Bytes)
    (hext : ∀ u ∈ ext, u.AttackerKnows (runTraceMoves r ms))
    (hnc : ¬ RecvCollision interpretation r S g₁ ms t) :
    ¬ RecvCollision interpretation r S g₁ (ms ++ ext.map .attackerSend) t := by
  induction ext generalizing ms with
  | nil => simpa using hnc
  | cons u rest ih =>
    have hcons : ms ++ (u :: rest).map Move.attackerSend =
        (ms ++ [.attackerSend u]) ++ rest.map Move.attackerSend := by
      simp [List.append_assoc]
    rw [hcons]
    have hu : u.AttackerKnows (runTraceMoves r ms) := hext u List.mem_cons_self
    have hnc₁ : ¬ RecvCollision interpretation r S g₁ (ms ++ [.attackerSend u]) t :=
      not_recvCollision_append_one_attackerSend_of_known hu hnc
    have hle := runTrace_le_append r ms [.attackerSend u]
    refine ih (fun v hv => ?_) hnc₁
    exact DY.Bytes.AttackerKnows_le v (runTraceMoves r ms) (runTraceMoves r (ms ++ [.attackerSend u]))
      hle (hext v (List.mem_cons_of_mem u hv))

theorem runMoves_map_attackerSend_snd (ext : List DY.Bytes) (tr : ExecTrace) :
    (runMoves (ext.map .attackerSend) tr).2 = [] := by
  induction ext generalizing tr with
  | nil => rfl
  | cons u rest ih =>
    simp [runMoves, vis_attackerSend_nil, ih]

theorem isReadMove_false_of_mem_map_attackerSend {ext : List DY.Bytes} {m' : Move}
    (hm' : m' ∈ ext.map .attackerSend) : isReadMove m' = false := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm'
  rfl

theorem rcvMoveTerm_of_decryptMsgIdx_some {tr : ExecTrace} {m : Move} {msgIdx : Nat} {t : DY.Bytes}
    (hm : m.decryptMsgIdx? = some msgIdx)
    (hget : tr.getMessageSentAt msgIdx = some t) :
    rcvMoveTerm tr m = some t := by
  unfold rcvMoveTerm; rw [hm]; exact hget

theorem take_k_succ_eq_of_mid_accept {mid : List MachineEvent} {pt pt' : HwBytes} {k : Nat}
    (hmid : mid = [] ∨ ∃ d, mid = [.rng d])
    (hk : (mid ++ [MachineEvent.accept pt])[k]? = some (MachineEvent.accept pt')) :
    (mid ++ [MachineEvent.accept pt]).take (k + 1) = mid ++ [MachineEvent.accept pt] := by
  rcases hmid with rfl | ⟨d, rfl⟩
  · rcases k with _ | k
    · rfl
    · simp at hk
  · rcases k with _ | _ | k
    · simp at hk
    · rfl
    · simp at hk

/-- Transports `CleanBy`, `recvRepresentations`, and `¬ RecvCollision` along the frame `g` to `g₁`
and across `ext.map .attackerSend` to construct `CBadBridgeHyp`. -/
theorem cBadBridgeHyp_of_acceptsBy
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {acc mid : List MachineEvent}
    {tag : BitVec 8} {body b pt : HwBytes} {t_star : DY.Bytes}
    (hc : CleanBy interpretation r S who ok g ms acc)
    (hmid : mid = [] ∨ ∃ d, mid = [.rng d])
    (hrb : RecvBody (.recv (tag :: body)) b)
    (ht_star : t_star ∈ recvRepresentations interpretation r S g ms b)
    (hacc_star : ModelAcceptsTermAfterCoinSplit interpretation r S who ok g ms acc
      (.recv (tag :: body)) (mid ++ [.accept pt]) t_star)
    (hnc_star : ¬ RecvCollision interpretation r S g ms t_star) :
    ∃ g₁,
      CBadSigmaFrame g g₁ (runTraceMoves r ms).length ∧
      CleanBy interpretation r S who ok g₁ ms acc ∧
      CBadBridgeHyp interpretation r S who ok g₁ ms acc (tag :: body) b (mid ++ [.accept pt]) := by
  obtain ⟨ext, m, msgIdx, k, _pt', g₁, hext_kn, hm_idx, haddr, hσ, hget, hk, _hrng, hExpl⟩ := hacc_star
  have hfr : CBadSigmaFrame g g₁ (runTraceMoves r ms).length :=
    ⟨fun ts hts len => congrFun (hσ ts hts) len, haddr⟩
  have hc₁ : CleanBy interpretation r S who ok g₁ ms acc :=
    cbadG2_cleanBy_transfer hfr hc
  have ht_star₁ : t_star ∈ recvRepresentations interpretation r S g₁ ms b :=
    cbadG2_recvRep_of_sigmaFrame hfr hc.matched ht_star
  have hnc_star₁ : ¬ RecvCollision interpretation r S g₁ ms t_star :=
    cbadG2_notRecvCollision_of_sigmaFrame hfr hc.matched ht_star.1 hnc_star
  have htake : (mid ++ [MachineEvent.accept pt]).take (k + 1) = mid ++ [MachineEvent.accept pt] :=
    take_k_succ_eq_of_mid_accept hmid hk
  rw [htake, List.append_assoc] at hExpl
  have hnc_pre : ¬ RecvCollision interpretation r S g₁ (ms ++ ext.map .attackerSend) t_star :=
    not_recvCollision_append_map_attackerSend ext hext_kn hnc_star₁
  have hrep_pre : t_star ∈ recvRepresentations interpretation r S g₁
      (ms ++ ext.map .attackerSend) b :=
    ⟨DY.Bytes.AttackerKnows_le t_star _ _ (runTrace_le_append r ms _) ht_star₁.1, ht_star₁.2⟩
  refine ⟨g₁, hfr, hc₁, ext.map .attackerSend, [], m, t_star,
    hExpl,
    runMoves_map_attackerSend_snd ext (runTraceMoves r ms),
    fun _ hm' => isReadMove_false_of_mem_map_attackerSend hm',
    fun _ hm' => False.elim (List.not_mem_nil hm'),
    rcvMoveTerm_of_decryptMsgIdx_some hm_idx hget,
    hrb, hrep_pre, hnc_pre⟩

theorem acceptsVia_of_rawWitness
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g g₁ : Ghost}
    {ms : List Move} {acc mid : List MachineEvent}
    {p : Participant} {stateIdx : Nat} {spqrMsgIdx : UInt32}
    {pqSalt t_m : DY.Bytes} {tag : BitVec 8} {body b pt : HwBytes} {m : Move}
    (hc : CleanBy interpretation r S who ok g ms acc)
    (hfr : CBadSigmaFrame g g₁ (runTraceMoves r ms).length)
    (ht_m : t_m ∈ recvRepresentations interpretation r S g ms b)
    (hpq_kn : pqSalt.AttackerKnows (runTraceMoves r ms))
    (hwho : who[(callStarts acc).length]? = some p)
    (hok : ok (callStarts acc).length = true)
    (hm : m = Move.decrypt p stateIdx ((runTraceMoves r ms).length + 1) (runTraceMoves r ms).length
            spqrMsgIdx (decide (tag ≠ wireWhisperTag)) ∨
          ∃ skIdx, m = Move.decryptSkipped p stateIdx ((runTraceMoves r ms).length + 1) skIdx
            (runTraceMoves r ms).length spqrMsgIdx (decide (tag ≠ wireWhisperTag)))
    (hmid : mid = [] ∨ ∃ d, mid = [.rng d])
    (hrb : (tag = wireWhisperTag ∧ b = body ∧
        parsePreKeyWire (wireWhisperTag :: body) = none) ∨
      (tag ≠ wireWhisperTag ∧ ∃ pf, parsePreKeyWire (tag :: body) = some pf ∧
        b = pf.message ∧
        (∃ ek ∈ bobDoneBaseKeys (runTraceMoves r ms),
          ecKey (gamma interpretation S g₁ ek) = pf.baseKey.take 33)))
    (hraw : RawDecryptMatched interpretation r S g₁
      (ms ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [m]))
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt]))) :
    ModelAcceptsTermAfterCoinSplit interpretation r S who ok g ms acc (.recv (tag :: body))
      (mid ++ [.accept pt]) t_m := by
  have hc₁ := cbadG2_cleanBy_transfer hfr hc
  have ht₁ : t_m ∈ recvRepresentations interpretation r S g₁ ms b :=
    cbadG2_recvRep_of_sigmaFrame hfr hc.matched ht_m
  have hExpl : ExplainsMoves interpretation r S who ok g₁
      (ms ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [m]))
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt])) :=
    explains_append_decrypt_step hc₁.explains ht₁ hwho hok hm hmid hrb hraw
  have hmap : [pqSalt, t_m].map Move.attackerSend = [.attackerSend pqSalt, .attackerSend t_m] :=
    rfl
  refine ⟨[pqSalt, t_m], m, (runTraceMoves r ms).length + 1, mid.length, pt, g₁, ?_, ?_, hfr.2,
    fun i hi => funext (hfr.1 i hi), ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hpq_kn
    · exact ht_m.1
  · rcases hm with rfl | ⟨skIdx, rfl⟩ <;> rfl
  · rw [hmap, runTrace_append_two_attackerSend]
    have hlen : (runTraceMoves r ms).length + 1 =
        ((runTraceMoves r ms).append (⟨pqSalt⟩ : DY.Network.ExecEntryT)).length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [hlen, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, DY.Trace.at?_append]
  · simp
  · rcases hmid with rfl | ⟨d, rfl⟩ <;> rfl
  · have htake : (mid ++ [MachineEvent.accept pt]).take (mid.length + 1) =
        mid ++ [MachineEvent.accept pt] := by simp
    rw [htake, hmap, List.append_assoc]
    exact hExpl

/-- Combines `acceptsVia_of_rawWitness`, `acceptCollision_pick`, and `cBadBridgeHyp_of_acceptsBy`
to derive `CBadBridgeHyp` from a raw decrypt witness and `¬ AcceptCollisionBy`. -/
theorem cBadG2_of_rawWitness
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g g₁ : Ghost}
    {ms : List Move} {acc mid : List MachineEvent}
    {p : Participant} {stateIdx : Nat} {spqrMsgIdx : UInt32}
    {pqSalt t_m : DY.Bytes} {tag : BitVec 8} {body b pt : HwBytes} {m : Move}
    (hc : CleanBy interpretation r S who ok g ms acc)
    (hnoAC : ¬ AcceptCollisionBy interpretation r S who ok g ms acc
      (.recv (tag :: body)) (mid ++ [.accept pt]) b)
    (hfr : CBadSigmaFrame g g₁ (runTraceMoves r ms).length)
    (ht_m : t_m ∈ recvRepresentations interpretation r S g ms b)
    (hpq_kn : pqSalt.AttackerKnows (runTraceMoves r ms))
    (hwho : who[(callStarts acc).length]? = some p)
    (hok : ok (callStarts acc).length = true)
    (hm : m = Move.decrypt p stateIdx ((runTraceMoves r ms).length + 1) (runTraceMoves r ms).length
            spqrMsgIdx (decide (tag ≠ wireWhisperTag)) ∨
          ∃ skIdx, m = Move.decryptSkipped p stateIdx ((runTraceMoves r ms).length + 1) skIdx
            (runTraceMoves r ms).length spqrMsgIdx (decide (tag ≠ wireWhisperTag)))
    (hmid : mid = [] ∨ ∃ d, mid = [.rng d])
    (hrb : (tag = wireWhisperTag ∧ b = body ∧
        parsePreKeyWire (wireWhisperTag :: body) = none) ∨
      (tag ≠ wireWhisperTag ∧ ∃ pf, parsePreKeyWire (tag :: body) = some pf ∧
        b = pf.message ∧
        (∃ ek ∈ bobDoneBaseKeys (runTraceMoves r ms),
          ecKey (gamma interpretation S g₁ ek) = pf.baseKey.take 33)))
    (hraw : RawDecryptMatched interpretation r S g₁
      (ms ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [m]))
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt]))) :
    ∃ g₁',
      CBadSigmaFrame g g₁' (runTraceMoves r ms).length ∧
      CleanBy interpretation r S who ok g₁' ms acc ∧
      CBadBridgeHyp interpretation r S who ok g₁' ms acc (tag :: body) b (mid ++ [.accept pt]) := by
  have hacc_m := acceptsVia_of_rawWitness hc hfr ht_m hpq_kn hwho hok hm hmid hrb hraw
  obtain ⟨t_star, ht_star, hacc_star, hnc_star⟩ := acceptCollision_pick hnoAC ht_m hacc_m
  have hrb_body : RecvBody (.recv (tag :: body)) b := by
    rcases hrb with ⟨h1, h2, _⟩ | ⟨_, pf, h2, h3, _⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨pf, h2, h3⟩
  exact cBadBridgeHyp_of_acceptsBy hc hmid hrb_body ht_star hacc_star hnc_star

end Symbolic.Swarm.CREF.CliPure
