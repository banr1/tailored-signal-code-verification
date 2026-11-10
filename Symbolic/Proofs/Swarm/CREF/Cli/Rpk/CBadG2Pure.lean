/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBad
public import Symbolic.Proofs.Swarm.CREF.CBadG2.Kem -- shake: keep
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.CBadG2.Frame
import Symbolic.Proofs.Swarm.CREF.CBadG2.MacGuess
import Symbolic.Proofs.Swarm.CREF.CBadG2.Skipped
import Symbolic.Proofs.Swarm.CREF.CBadG2.Stamps
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecordsBridgePure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.ReadFaithful
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
# `CBadSigmaFrame` Transfer for `CleanBy` and `RecvCollision`

Proves that `RecvCollision`, `recvRepresentations`, `preKeyRepresentations`, `MatchedPrefix`,
`ExplainsMoves`, and `CleanBy` transfer between `g` and `g₁` across a `CBadSigmaFrame` at the
trace length `(runTraceMoves r ms).length`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (parseTrSignalMsg)
open Symbolic.Swarm.CREF.TR.FreshSigma (StampsLt VisStampsLt TraceEntriesLt
  stampsLt_parseTrSignalMsg traceEntriesLt_of_reachable)

/-! ## `RecvCollision` Invariance and Transfer -/

/-- `RecvCollision` is invariant between `g₁` and `g` on any stamped message term `t`. -/
theorem cbadG2_recvCollision_iff {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g g₁ : Ghost} {ms : List Move} {n : Nat} {t : DY.Bytes}
    (hga : CBadGammaAgree interpretation S g g₁ n)
    (hst : CBadStamps interpretation r S g ms n) (ht : StampsLt interpretation S g n t) :
    RecvCollision interpretation r S g₁ ms t ↔ RecvCollision interpretation r S g ms t := by
  unfold RecvCollision
  cases hp : parseTrSignalMsg t with
  | none =>
    exact cbadG2_memoCollisionOn_iff hga hst.pre (fun u hu => List.mem_singleton.mp hu ▸ ht)
  | some msg =>
    dsimp only
    refine or_congr ?_ (cbadG2_ownSaltMacCollision_iff hga hst ht hp)
    rw [cbadG2_whisperTrials_eq hga hst ht hp]
    exact cbadG2_memoCollisionOn_iff hga hst.pre (hst.recvTerms t msg ht hp)

theorem cbadG2_recvCollision_transfer {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g g₁ : Ghost} {ms : List Move} {n : Nat} {t : DY.Bytes}
    (hga : CBadGammaAgree interpretation S g g₁ n)
    (hst : CBadStamps interpretation r S g ms n) (ht : StampsLt interpretation S g n t)
    (h : RecvCollision interpretation r S g₁ ms t) :
    RecvCollision interpretation r S g ms t :=
  (cbadG2_recvCollision_iff hga hst ht).mp h

/-! ## Representation, Prefix-Matching, and `CleanBy` Transfer -/

section Frame

variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g g₁ : Ghost}
  {ms : List Move} {n : Nat}

theorem cbadG2_recvRep_transfer (hga : CBadGammaAgree interpretation S g g₁ n)
    (hst : CBadStamps interpretation r S g ms n) {b : HwBytes} {t : DY.Bytes}
    (ht : t ∈ recvRepresentations interpretation r S g ms b) :
    t ∈ recvRepresentations interpretation r S g₁ ms b := by
  obtain ⟨hk, hb, hp, hf⟩ := ht
  have hts := hst.knows hk
  refine ⟨hk, (cbadG2_gamma_eq hga hts).trans hb, hp, fun msg hmsg => ?_⟩
  obtain ⟨hw, hm, hrk, hct, hpq⟩ := stampsLt_parseTrSignalMsg hts hmsg
  obtain ⟨h1, h2, h3, h4⟩ := hf msg hmsg
  refine ⟨(cbadG2_gamma_eq hga hw).trans h1, (cbadG2_gamma_eq hga hm).trans h2, h3,
    fun m hm' => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := h4 m hm'
  exact ⟨(cbadG2_gamma_eq hga hct).trans e1, (cbadG2_gamma_eq hga hrk).trans e2,
    (cbadG2_gamma_eq hga hpq).trans e3, e4, e5⟩

theorem cbadG2_bundleMatches_transfer {b : HwBytes} {terms : List DY.Bytes}
    (hγ : ∀ t ∈ terms, gamma interpretation S g₁ t = gamma interpretation S g t) :
    PreKeyBundleLayoutMatches interpretation S g₁ b terms ↔ PreKeyBundleLayoutMatches interpretation S g b terms := by
  match terms with
  | [spk, spkSig, pqpk, pqpkSig] =>
    simp only [PreKeyBundleLayoutMatches, BundleSignedKeysMatch, hγ spk (by simp), hγ spkSig (by simp),
      hγ pqpk (by simp), hγ pqpkSig (by simp)]
  | [spk, spkSig, pqpk, pqpkSig, opk] =>
    simp only [PreKeyBundleLayoutMatches, BundleSignedKeysMatch, hγ spk (by simp), hγ spkSig (by simp),
      hγ pqpk (by simp), hγ pqpkSig (by simp), hγ opk (by simp)]
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem cbadG2_sendMatches_transfer {initIds : Option BundlePreKeyIds} {b : HwBytes} {terms : List DY.Bytes}
    (hγ : ∀ t ∈ terms, gamma interpretation S g₁ t = gamma interpretation S g t) :
    SendMatches interpretation r S g₁ initIds b terms ↔ SendMatches interpretation r S g initIds b terms := by
  match terms with
  | [ek, ct, msg] =>
    simp only [SendMatches, hγ ek (by simp), hγ ct (by simp), hγ msg (by simp)]
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => rfl

theorem cbadG2_preKeyRecvMatches_transfer {b : HwBytes} {terms : List DY.Bytes}
    (hγ : ∀ t ∈ terms, gamma interpretation S g₁ t = gamma interpretation S g t) :
    PreKeyRecvMatches interpretation r S g₁ b terms ↔ PreKeyRecvMatches interpretation r S g b terms := by
  match terms with
  | [ek, ct, msg] =>
    simp only [PreKeyRecvMatches, hγ ek (by simp), hγ ct (by simp), hγ msg (by simp)]
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => rfl

theorem cbadG2_preKeyRecvOpkMatches_transfer {b : HwBytes} {terms : List DY.Bytes}
    (hγ : ∀ t ∈ terms, gamma interpretation S g₁ t = gamma interpretation S g t) :
    PreKeyRecvOpkMatches interpretation r S g₁ b terms ↔
      PreKeyRecvOpkMatches interpretation r S g b terms := by
  match terms with
  | [ek, ct, msg] =>
    exact and_congr_left fun _ => cbadG2_preKeyRecvMatches_transfer (b := b) hγ
  | [ek, ct, msg, _opk] =>
    exact and_congr_left fun _ => cbadG2_preKeyRecvMatches_transfer (b := b) (terms := [ek, ct, msg])
      (fun t ht => hγ t (by simp at ht; rcases ht with rfl | rfl | rfl <;> simp))
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem cbadG2_preKeyRep_transfer (hga : CBadGammaAgree interpretation S g g₁ n)
    (hst : CBadStamps interpretation r S g ms n) {b : HwBytes} {x : PreKeyRep}
    (hx : x ∈ preKeyRepresentations interpretation r S g ms b) :
    x ∈ preKeyRepresentations interpretation r S g₁ ms b := by
  obtain ⟨hek, hct, hmsg, hm, p, hp, hfi⟩ := hx
  have h1 := hst.knows hek
  have h2 := hst.knows hct
  have h3 := hst.knows hmsg
  refine ⟨hek, hct, hmsg, ?_, p, hp, ?_⟩
  · have hγ : ∀ t ∈ [x.ek, x.ct, x.msg],
        gamma interpretation S g₁ t = gamma interpretation S g t := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact cbadG2_gamma_eq hga h1
      · exact cbadG2_gamma_eq hga h2
      · exact cbadG2_gamma_eq hga h3
    exact (cbadG2_preKeyRecvMatches_transfer hγ).mpr hm
  · obtain ⟨msg, hpm, e1, e2, e8, e3, e4, e7, e5, e6⟩ := hfi
    obtain ⟨hw, hmac, hrk, hct', hpq⟩ := stampsLt_parseTrSignalMsg h3 hpm
    exact ⟨msg, hpm, (cbadG2_gamma_eq hga hw).trans e1, (cbadG2_gamma_eq hga hmac).trans e2,
      e8, (cbadG2_gamma_eq hga hct').trans e3, (cbadG2_gamma_eq hga hrk).trans e4,
      (cbadG2_gamma_eq hga hpq).trans e7, e5, e6⟩

theorem cbadG2_eventMatchesEntry_transfer (hga : CBadGammaAgree interpretation S g g₁ n)
    {e : MachineEvent} {v : VisEntry} (hv : VisStampsLt interpretation S g n v) :
    EventMatchesEntry interpretation r S g₁ e v ↔ EventMatchesEntry interpretation r S g e v := by
  have hγ : ∀ t ∈ v.terms, gamma interpretation S g₁ t = gamma interpretation S g t :=
    fun t ht => cbadG2_gamma_eq hga (hv.1 t ht)
  have hkeys := hv.2
  have hmap : v.terms.map (gamma interpretation S g₁) = v.terms.map (gamma interpretation S g) :=
    List.map_congr_left hγ
  unfold EventMatchesEntry; apply and_congr_right; intro _; dsimp only
  cases hl : v.layout with
  | single => rw [hmap]
  | whisper =>
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [hγ t (by simp [ht])]
  | bundle => exact cbadG2_bundleMatches_transfer hγ
  | preKeySend => exact exists_congr fun ids => cbadG2_sendMatches_transfer hγ
  | preKeyRecv => exact cbadG2_preKeyRecvOpkMatches_transfer hγ
  | preKeyInner eks =>
    rw [hl] at hkeys
    refine exists_congr fun t => exists_congr fun p => and_congr_right fun ht =>
      and_congr_right fun _ => ?_
    rw [hγ t (by simp [ht])]
    refine and_congr_left fun _ => exists_congr fun ek => and_congr_right fun hek => ?_
    rw [cbadG2_gamma_eq hga (hkeys ek hek)]
  | fresh _ => rfl
  | kyberCoin j =>
    apply and_congr_right; intro _
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [hγ t (by simp [ht])]
  | unconstrained => rfl
  | leakPq pq => cases pq <;> simp [hmap]
  | leakRecord =>
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [hγ t (by simp [ht])]

private theorem cbadG2_alice_ne_bob_of_modelRun {r : ProtocolSetup} {ms : List Move}
    (hmr : ModelRun r ms) : r.alice ≠ r.bob := by
  intro hEq
  have hlen : (setupRandoms r).length = if r.withOpk then 7 else 6 := hmr.1
  have h1 : (setupRandoms r).length = 1 := by
    unfold setupRandoms
    rw [Symbolic.Swarm.CREF.CliPure.setupTrace_eq_self r hEq]
    simp [newRandoms, newIndices, setupTr1, List.range', DY.Trace.at?,
      Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.at_eq_2,
      RndE, EvE, NetE, StE]
    rfl
  rw [h1] at hlen
  cases hOpk : r.withOpk <;> rw [hOpk] at hlen <;> exact absurd hlen (by decide)

theorem cbadG2_compat_transfer (hNe : r.alice ≠ r.bob) (hfr : CBadSigmaFrame g g₁ n)
    (hn : (runTraceMoves r ms).length ≤ n)
    (htr : TraceEntriesLt interpretation S g n (runTraceMoves r ms))
    (hc : GhostAndSemMatchSetup interpretation r S g) : GhostAndSemMatchSetup interpretation r S g₁ := by
  have hga := cbadG2_gammaAgree_of_sigmaFrame interpretation S hfr
  have hsetup_le : (setupTrace r).length ≤ n :=
    Nat.le_trans (DY.Trace.length_le _ _ (Refinement.setupTrace_le_runTrace r ms)) hn
  refine ⟨fun p hp => ?_, fun t ht => ?_, hc.2.2⟩
  · have hlt : p.1 < (setupTrace r).length := cbadG2_fst_lt_of_mem_setupRandomsAt hNe hp
    rw [hfr.1 p.1 (by omega) p.2]; exact hc.1 p hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · unfold ProtocolSetup.spkSigTerm
      rw [cbadG2_gamma_eq hga (cbadG2_stampsLt_setupPublic hn htr 5)]; exact hc.2.1 r.spkSigTerm (by simp)
    · unfold ProtocolSetup.pqpkPubTerm
      rw [cbadG2_gamma_eq hga (cbadG2_stampsLt_setupPublic hn htr 6)]; exact hc.2.1 r.pqpkPubTerm (by simp)
    · unfold ProtocolSetup.pqpkSigTerm
      rw [cbadG2_gamma_eq hga (cbadG2_stampsLt_setupPublic hn htr 7)]; exact hc.2.1 r.pqpkSigTerm (by simp)

theorem cbadG2_readFaithful_transfer {τ : List MachineEvent}
    (hga : CBadGammaAgree interpretation S g g₁ n) (hst : CBadStamps interpretation r S g ms n)
    (hrf : ReadFaithful interpretation r S g ms τ) :
    ReadFaithful interpretation r S g₁ ms τ :=
  readFaithful_iff.mpr fun ev hev hk =>
    ReadOKWith.mono (fun _ _ ht => cbadG2_recvRep_transfer hga hst ht)
      (fun _ _ hx => cbadG2_preKeyRep_transfer hga hst hx) (readFaithful_iff.mp hrf ev hev hk)

/-- Transfers `MatchedPrefix` from `g` to `g₁` across a `CBadSigmaFrame` at `n ≥ (runTraceMoves r ms).length`. -/
theorem cbadG2_matchedPrefix_transfer {who : List Participant} {τ : List MachineEvent}
    (hfr : CBadSigmaFrame g g₁ n) (hn : (runTraceMoves r ms).length ≤ n)
    (hmp : MatchedPrefix interpretation r S who g ms τ) :
    MatchedPrefix interpretation r S who g₁ ms τ := by
  have hrun : ModelRun r ms := hmp.2.1
  have htr := traceEntriesLt_of_reachable interpretation S g n hrun.2.2.1.1 hn
  have hga := cbadG2_gammaAgree_of_sigmaFrame interpretation S hfr
  have hst := cbadG2_stamps_of_matched hmp hn
  refine ⟨cbadG2_compat_transfer (cbadG2_alice_ne_bob_of_modelRun hrun) hfr hn htr hmp.1,
    hrun, hmp.2.2.1, ?_, cbadG2_readFaithful_transfer hga hst hmp.2.2.2.2.1, ?_⟩
  · intro i m promote b p hm hpp hcs hpw
    rw [hmp.2.2.2.1 i m promote b p hm hpp hcs hpw]
    refine exists_congr fun ek => and_congr_right fun hek => ?_
    rw [cbadG2_gamma_eq hga (cbadG2_stampsLt_bobDoneBaseKeys_take hmp hn i hek)]
  · have hfor := hmp.2.2.2.2.2
    rw [List.forall₂_iff_zip] at hfor ⊢
    refine ⟨hfor.1, fun {e v} hx => ?_⟩
    have hvs : VisStampsLt interpretation S g n v :=
      cbadG2_runVis_visStampsLt hrun hn (List.of_mem_zip hx).2
    exact (cbadG2_eventMatchesEntry_transfer hga hvs).mpr (hfor.2 hx)

theorem cbadG2_explains_transfer {who : List Participant} {ok : Nat → Bool} {τ : List MachineEvent}
    (hfr : CBadSigmaFrame g g₁ n) (hn : (runTraceMoves r ms).length ≤ n)
    (hf : ExplainsMoves interpretation r S who ok g ms τ) :
    ExplainsMoves interpretation r S who ok g₁ ms τ :=
  ⟨cbadG2_matchedPrefix_transfer hfr hn hf.1, hf.2⟩

theorem cbadG2_readCollision_transfer_back {τ : List MachineEvent}
    (hga : CBadGammaAgree interpretation S g g₁ n)
    (hst : ∀ i, CBadStamps interpretation r S g (ms.take i) n)
    (h : ReadCollision interpretation r S g₁ ms τ) :
    ReadCollision interpretation r S g ms τ := by
  obtain ⟨i, τ₁, e, τ₂, m, hτ, hm, hF, hacc, hRd⟩ := h
  have hst' := hst i
  refine ⟨i, τ₁, e, τ₂, m, hτ, hm, ?_, hacc, ?_⟩
  · rw [List.forall₂_iff_zip] at hF ⊢
    refine ⟨hF.1, fun {e' v} hx => ?_⟩
    exact (cbadG2_eventMatchesEntry_transfer hga (hst'.vis v (List.of_mem_zip hx).2)).mp (hF.2 hx)
  · cases m <;> simp only [MoveReadsCollidingMsg] at hRd ⊢
    case decrypt =>
      obtain ⟨b, t, hb, ht, hc⟩ := hRd
      exact ⟨b, t, hb, ht, cbadG2_recvCollision_transfer hga hst'
        (cbadG2_stampsLt_getMessageSentAt hst' ht) hc⟩
    case decryptSkipped =>
      obtain ⟨b, t, hb, ht, hc⟩ := hRd
      exact ⟨b, t, hb, ht, cbadG2_recvCollision_transfer hga hst'
        (cbadG2_stampsLt_getMessageSentAt hst' ht) hc⟩

/-- Transfers `CleanBy` from `g` to `g₁` across a `CBadSigmaFrame` at `(runTraceMoves r ms).length`. -/
theorem cbadG2_cleanBy_transfer {who : List Participant} {ok : Nat → Bool} {τ : List MachineEvent}
    (hfr : CBadSigmaFrame g g₁ (runTraceMoves r ms).length)
    (hc : CleanBy interpretation r S who ok g ms τ) :
    CleanBy interpretation r S who ok g₁ ms τ := by
  have hga := cbadG2_gammaAgree_of_sigmaFrame interpretation S hfr
  refine ⟨cbadG2_explains_transfer hfr (Nat.le_refl _) hc.explains, fun hd => ?_⟩
  exact hc.not_readCollision (cbadG2_readCollision_transfer_back hga
    (cbadG2_stamps_of_matched_take hc.matched (Nat.le_refl _)) hd)

/-- Transfers `recvRepresentations` membership from `g` to `g₁` across a `CBadSigmaFrame` at
`(runTraceMoves r ms).length`. -/
theorem cbadG2_recvRep_of_sigmaFrame {who : List Participant} {τ : List MachineEvent}
    (hfr : CBadSigmaFrame g g₁ (runTraceMoves r ms).length)
    (hmp : MatchedPrefix interpretation r S who g ms τ) {b : HwBytes} {t : DY.Bytes}
    (ht : t ∈ recvRepresentations interpretation r S g ms b) :
    t ∈ recvRepresentations interpretation r S g₁ ms b :=
  cbadG2_recvRep_transfer (cbadG2_gammaAgree_of_sigmaFrame interpretation S hfr)
    (cbadG2_stamps_of_matched hmp (Nat.le_refl _)) ht

/-- Transfers `¬ RecvCollision` for an attacker-known term `t` from `g` to `g₁` across a
`CBadSigmaFrame` at `(runTraceMoves r ms).length`. -/
theorem cbadG2_notRecvCollision_of_sigmaFrame {who : List Participant} {τ : List MachineEvent}
    (hfr : CBadSigmaFrame g g₁ (runTraceMoves r ms).length)
    (hmp : MatchedPrefix interpretation r S who g ms τ) {t : DY.Bytes}
    (hk : t.AttackerKnows (runTraceMoves r ms))
    (hnc : ¬ RecvCollision interpretation r S g ms t) :
    ¬ RecvCollision interpretation r S g₁ ms t := fun hc =>
  have hst := cbadG2_stamps_of_matched hmp (Nat.le_refl _)
  hnc (cbadG2_recvCollision_transfer (cbadG2_gammaAgree_of_sigmaFrame interpretation S hfr) hst
    (hst.knows hk) hc)

end Frame

end Symbolic.Swarm.CREF.CliPure
