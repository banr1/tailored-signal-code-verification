/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunExtractA
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVisC
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux

/-!
# Clean Prefix Explanation and Whisper Acceptance

Proves that the canonical clean schedule `(gClean r cls, ssClean cls cleanSpqrIdxs, visClean r cls)`
satisfies `Explains` on `trace0.take m` (`m ≤ 24`), and derives
`ModelAcceptsTermAfterAttackerSends` for all ten whisper receive calls `k = 5 + 2 * h` (`h < 10`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunExtract

open scoped DY.Libsignal.Composed
open DY (ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   gamma parsePreKeyWire setupTrace setupPublic runTrace runSteps stepView
   rngEntry kyberCoinEntries randTerm OutputsMatch ReadsFaithfully RunMatches
   MatchesEventsAt Explains runWrapped inputKind nextBundleIds)
open DY.Libsignal.Composed.Refinement.Cli (ModelAcceptsTermAfterAttackerSends)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikB spkB pqskB spkNonce pqNonce t5 bh1 kh1 o1)
open Symbolic.Swarm.CREF.TR (gamma_rand)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (trace0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (recvCallIndices cleanCallSteps cleanCallSteps_length ssClean cleanRecvTerm)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse (ev)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace (r_names_of_fit)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
  (trace0_take_succ ev3_pt_eq_ev2 whisper_wire_eq ev0_cmd_and_exit ev0_bundle_slices
   send_coins_ge_64 send_runWrapped_prekey send_runWrapped_whisper
   nextBundleIds_non_init active_recv_coins_ge_32)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (cleanSpqrIdxs setupTrace_eq_t4 m1Clean pt2Clean m2Clean
   trClean2 trClean3 mhClean3 s0_next_ok s1_next_ok s2_next_ok s3_next_ok)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
  (gClean gClean_sigma_31 gClean_sigma_32 gClean_sigma_38 gClean_sigma_39 gClean_sigma_45
   gClean_sigma_whisper_pt gClean_sigma_whisper_coins gClean_sigma_whisper_dhs
   gamma_dhPk_ratchetTs)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTrace
  (modelRunWF_ssClean ssClean_succ cleanPreKeyRep_eq)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunPrefix
  (hrSender hrReceiver hrStHSend hrStHRecv hr_send_party_cmd hr_recv_party_cmd
   hr_whisper_spec hr_mem_whisper ccs_get_send ccs_get_recv sendCallOf_whisper CleanPrefixData)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVis
  (visClean visClean_succ stepView_s0 stepView_s1 stepView_s2)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVisB
  (stepView_s3 cleanHalfRound_at)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVisC
  (ghostWF_visClean)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunExtractA
  (gamma_randTerm_pos cleanPreKeyRep_mem cleanRecvTerm_mem_whisper
   drawsMatch_ev0 drawsMatch_single32 drawsMatch_enc)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

/-- Step-by-step `RunMatches` chain threading `BundlePreKeyIds` with no invisible prefix steps,
used to build `MatchesEventsAt` by right-append (`snoc`). -/
private inductive CleanStepsMatch (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) :
    Option BundlePreKeyIds → Option BundlePreKeyIds → ExecTrace →
      List Step → List CliEvent → List VisEntry → Prop
  | nil (ids : Option BundlePreKeyIds) (tr : ExecTrace) :
      CleanStepsMatch r S g ids ids tr [] [] []
  | cons {ids mid outIds : Option BundlePreKeyIds} {tr : ExecTrace}
      {s : Step} {ss : List Step} {e : RunEvent} {evs : List CliEvent}
      {v vs : List VisEntry} :
      mid = nextBundleIds ids e →
      RunMatches evictedI0 r S g tr s e v ids →
      CleanStepsMatch r S g mid outIds (s.next tr) ss evs vs →
      CleanStepsMatch r S g ids outIds tr (s :: ss) (.run e :: evs) (v ++ vs)

private theorem CleanStepsMatch.snoc {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ids mid outIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    {s : Step} {e : RunEvent} {v : List VisEntry}
    (hm : CleanStepsMatch r S g ids mid tr ss evs vis)
    (hnext : outIds = nextBundleIds mid e)
    (hrm : RunMatches evictedI0 r S g (runSteps ss tr) s e v mid) :
    CleanStepsMatch r S g ids outIds tr (ss ++ [s]) (evs ++ [.run e]) (vis ++ v) := by
  induction hm with
  | nil =>
    rw [List.nil_append, List.nil_append, List.nil_append, ← List.append_nil v]
    exact CleanStepsMatch.cons hnext hrm (.nil outIds _)
  | cons hmid hrm0 hrest ih =>
    rw [List.cons_append, List.cons_append, List.append_assoc]
    exact CleanStepsMatch.cons hmid hrm0 (ih hnext hrm)

private theorem CleanStepsMatch.toMatchesEventsAt {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ids outIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hm : CleanStepsMatch r S g ids outIds tr ss evs vis) :
    MatchesEventsAt evictedI0 r S g ids tr ss evs vis := by
  induction hm with
  | nil => exact .nil (by simp)
  | cons hmid hrm hrest ih =>
    subst hmid
    exact .run1 (pre := []) (by simp) hrm ih

private def cleanInitIds (m : Nat) : Option BundlePreKeyIds :=
  if m = 0 then none else some (none, 7#32, 9#32)

private theorem runMatches_clean_0 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k : Nat} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls) :
    RunMatches evictedI0 r S (gClean r cls) (setupTrace r)
      (.aliceStart "alice" "bob" 4 6 bh1) (ev 0)
      (stepView (.aliceStart "alice" "bob" 4 6 bh1) (setupTrace r) (runWrapped (ev 0)))
      none := by
  obtain ⟨hp0, hcmd0, hex0, _⟩ := ev0_cmd_and_exit
  obtain ⟨hlen_in, hbyte4, _, hsl46, hsl79, hsl147, hsl1716, _⟩ := ev0_bundle_slices
  have hnames := r_names_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hnames.1, hnames.2]; decide
  rw [setupTrace_eq_t4 hfit]
  refine ⟨rfl, by rw [hp0]; rfl, by rw [hcmd0]; trivial, hnames.2.symm,
    (s0_next_ok).2, ⟨[], hex0⟩, rfl, ?_⟩
  refine ⟨⟨.recv, [dhPk spkB, DY.Signature.sign ikB spkNonce (DY.Libsignal.PQXDH.encodeEC (dhPk spkB)),
      kemPk pqskB, DY.Signature.sign ikB pqNonce (DY.Libsignal.PQXDH.encodeKEM (kemPk pqskB))],
      .bundle, none⟩,
    rngEntry (randTerm 22 32) ::
      (kyberCoinEntries (randTerm 23 32) ++
        [{ rngEntry (randTerm 24 32) with anchor := some 27 }]),
    [], ?_, ?_, drawsMatch_ev0 r S cls, ?_, trivial, fun _ _ => trivial⟩
  · rw [stepView_s0, List.append_nil]
  · refine ⟨by unfold inputKind; rw [hcmd0], ⟨hlen_in, ?_, ?_, ?_, ?_⟩, hbyte4⟩
    · rw [DY.Libsignal.PQXDH.Refinement.BundleBlob.spkPub, hsl46, gamma_dhPk_ratchetTs (S := S) (cls := cls) hfit (by decide)]; rfl
    · rw [DY.Libsignal.PQXDH.Refinement.BundleBlob.spkSig, hsl79, ← hfit.1.1.2.2.2.2.2.2.2.2.2.1,
          ← (show gamma _ _ _ (setupPublic r 5) = r.opaqueBytes (setupPublic r 5) from
            d.compatClean.2.1 r.spkSigTerm (by simp)),
          Symbolic.Swarm.CREF.b1_setupPublic_5 r hNe]; rfl
    · rw [DY.Libsignal.PQXDH.Refinement.BundleBlob.kpkPub, hsl147, ← hfit.1.1.2.2.2.2.2.2.2.2.2.2.1,
          ← (show gamma _ _ _ (setupPublic r 6) = r.opaqueBytes (setupPublic r 6) from
            d.compatClean.2.1 r.pqpkPubTerm (by simp)),
          Symbolic.Swarm.CREF.b1_setupPublic_6 r hNe]; rfl
    · rw [DY.Libsignal.PQXDH.Refinement.BundleBlob.kpkSig, hsl1716, ← hfit.1.1.2.2.2.2.2.2.2.2.2.2.2.1,
          ← (show gamma _ _ _ (setupPublic r 7) = r.opaqueBytes (setupPublic r 7) from
            d.compatClean.2.1 r.pqpkSigTerm (by simp)),
          Symbolic.Swarm.CREF.b1_setupPublic_7 r hNe]; rfl
  · unfold OutputsMatch; rw [hex0, hcmd0]; rfl

private theorem runMatches_clean_1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k : Nat} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls) :
    RunMatches evictedI0 r S (gClean r cls) (runTrace r (ssClean cls cleanSpqrIdxs 1))
      (.messageEncrypt "alice" 30 (cls 0) 33) (ev 1)
      (stepView (.messageEncrypt "alice" 30 (cls 0) 33)
        (runTrace r (ssClean cls cleanSpqrIdxs 1)) (runWrapped (ev 1)))
      (some (none, 7#32, 9#32)) := by
  have hrun1 : runTrace r (ssClean cls cleanSpqrIdxs 1) = t5 := by
    unfold runTrace; rw [setupTrace_eq_t4 hfit]; exact (s0_next_ok).1
  have hp1 : (ev 1).party = "alice" := by unfold ev; rfl
  have hcmd1 : (ev 1).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := by unfold ev; rfl
  rw [hrun1]
  refine ⟨rfl, by rw [hp1]; rfl, by rw [hcmd1]; trivial, trivial,
    (s1_next_ok cls).2, ⟨_, d.ev1_out⟩, rfl, ?_⟩
  refine ⟨⟨.pt, [randTerm 31 32], .single, none⟩,
    if cls 0 != 0 then [rngEntry (randTerm 32 (cls 0))] else [],
    [⟨.send, [o1.ek, o1.ct, m1Clean cls], .preKeySend, none⟩],
    by rw [send_runWrapped_prekey.1]; exact stepView_s1 cls, ?_,
    drawsMatch_enc r S cls (d.validCls 0 (by decide)) (send_coins_ge_64 (s := 0) (by decide))
      (gClean_sigma_32 r cls (cls 0)),
    ?_, trivial, fun _ _ => trivial⟩
  · refine ⟨by unfold inputKind; rw [hcmd1], ?_⟩
    simp only [List.map_cons, List.map_nil, gamma_randTerm_pos (by decide : 32 ≠ 0),
      gClean_sigma_31]
  · unfold OutputsMatch
    rw [d.ev1_out, hcmd1]
    exact ⟨_, rfl, rfl, none, 7#32, 9#32, rfl, rfl⟩

private theorem runMatches_clean_2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k : Nat} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls) :
    RunMatches evictedI0 r S (gClean r cls) (runTrace r (ssClean cls cleanSpqrIdxs 2))
      (.messageEncrypt "alice" 36 (cls 1) 40) (ev 2)
      (stepView (.messageEncrypt "alice" 36 (cls 1) 40)
        (runTrace r (ssClean cls cleanSpqrIdxs 2)) (runWrapped (ev 2)))
      (some (none, 7#32, 9#32)) := by
  have htake2 : ssClean cls cleanSpqrIdxs 2 =
      [Step.aliceStart "alice" "bob" 4 6 bh1,
       Step.messageEncrypt "alice" 30 (cls 0) 33] := rfl
  have hrun2 : runTrace r (ssClean cls cleanSpqrIdxs 2) = trClean2 cls := by
    unfold runTrace; rw [setupTrace_eq_t4 hfit, htake2]; dsimp only [runSteps]
    rw [(s0_next_ok).1, (s1_next_ok cls).1]
  have hp2 : (ev 2).party = "alice" := by unfold ev; rfl
  have hcmd2 : (ev 2).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := by unfold ev; rfl
  rw [hrun2]
  refine ⟨rfl, by rw [hp2]; rfl, by rw [hcmd2]; trivial, trivial,
    (s2_next_ok cls).2, ⟨_, d.ev2_out⟩, rfl, ?_⟩
  refine ⟨⟨.pt, [randTerm 38 32], .single, none⟩,
    if cls 1 != 0 then [rngEntry (randTerm 39 (cls 1))] else [],
    [⟨.send, [o1.ek, o1.ct, m2Clean cls], .preKeySend, none⟩],
    by rw [send_runWrapped_prekey.2]; exact stepView_s2 cls, ?_,
    drawsMatch_enc r S cls (d.validCls 1 (by decide)) (send_coins_ge_64 (s := 1) (by decide))
      (gClean_sigma_39 r cls (cls 1)),
    ?_, trivial, fun _ _ => trivial⟩
  · refine ⟨by unfold inputKind; rw [hcmd2], ?_⟩
    simp only [List.map_cons, List.map_nil, gamma_randTerm_pos (by decide : 32 ≠ 0),
      gClean_sigma_38]
  · unfold OutputsMatch
    rw [d.ev2_out, hcmd2]
    exact ⟨_, rfl, rfl, none, 7#32, 9#32, rfl, rfl⟩

private theorem runMatches_clean_3 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k : Nat} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls)
    (hex3 : Explains evictedI0 r S (gClean r cls) (ssClean cls cleanSpqrIdxs 3)
      (visClean r cls 3) (trace0.take 3)) :
    RunMatches evictedI0 r S (gClean r cls) (runTrace r (ssClean cls cleanSpqrIdxs 3))
      (.bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3)) (ev 3)
      (stepView (.bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3))
        (runTrace r (ssClean cls cleanSpqrIdxs 3)) (runWrapped (ev 3)))
      (some (none, 7#32, 9#32)) := by
  have htake3 : ssClean cls cleanSpqrIdxs 3 =
      [Step.aliceStart "alice" "bob" 4 6 bh1,
       Step.messageEncrypt "alice" 30 (cls 0) 33,
       Step.messageEncrypt "alice" 36 (cls 1) 40] := rfl
  have hrun3 : runTrace r (ssClean cls cleanSpqrIdxs 3) = trClean3 cls := by
    unfold runTrace; rw [setupTrace_eq_t4 hfit, htake3]; dsimp only [runSteps]
    rw [(s0_next_ok).1, (s1_next_ok cls).1, (s2_next_ok cls).1]
  have hp3 : (ev 3).party = "bob" := by unfold ev; rfl
  obtain ⟨peer3, hcmd3⟩ : ∃ peer, (ev 3).cmd = .recv peer := by unfold ev; exact ⟨_, rfl⟩
  obtain ⟨hrep3, hopk3⟩ := cleanPreKeyRep_mem hfit d
  rw [cleanPreKeyRep_eq hfit] at hrep3
  have hbks_nil : DY.Libsignal.Composed.Refinement.bobDoneBaseKeys
      (runTrace r (ssClean cls cleanSpqrIdxs 3)) = [] :=
    Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux.bobDoneBaseKeys_eq_nil_of_no_recv
      hfit.1.1.1 hex3 (by decide +kernel)
  refine ⟨rfl, by rw [hp3]; rfl, by rw [hcmd3]; trivial, (r_names_of_fit hfit).1.symm,
    by rw [hrun3]; exact (s3_next_ok cls).2, ⟨_, ev3_pt_eq_ev2⟩, rfl, ?_⟩
  refine ⟨⟨.recv, [o1.ek, o1.ct, m2Clean cls], .preKeyRecv, none⟩,
    [rngEntry (randTerm 45 32)],
    [⟨.accept, [pt2Clean], .single, some 47⟩],
    by rw [hrun3]; exact stepView_s3 cls (runWrapped (ev 3)),
    ⟨by unfold inputKind; rw [hcmd3], hrep3.2.2.2.1, hopk3⟩,
    drawsMatch_single32 r S cls (active_recv_coins_ge_32 (by decide) (by decide))
      (gClean_sigma_45 r cls 32),
    ?_, hrep3, ?_⟩
  · unfold OutputsMatch
    rw [ev3_pt_eq_ev2, hcmd3]
    refine ⟨_, rfl, rfl, ?_⟩
    simp only [List.map_cons, List.map_nil]
    unfold pt2Clean rnd
    rw [gamma_rand]
    simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte, gClean_sigma_38]
  · unfold DY.Libsignal.Composed.Refinement.PathFaithfulAt
    intro p _
    dsimp only
    rw [hbks_nil]
    rintro ⟨_, ⟨⟩, _⟩

private theorem runMatches_clean_whisper_send {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k h : Nat} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls)
    (hh : h < 10) (hlt : 4 + 2 * h < k) :
    RunMatches evictedI0 r S (gClean r cls)
      (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h)))
      (.messageEncrypt (hrSender h) (hrStHSend h) (cls (2 + h)) (55 + 14 * h + 2))
      (ev (4 + 2 * h))
      (stepView (.messageEncrypt (hrSender h) (hrStHSend h) (cls (2 + h)) (55 + 14 * h + 2))
        (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))) (runWrapped (ev (4 + 2 * h))))
      (some (none, 7#32, 9#32)) := by
  have w := Classical.choice (cleanHalfRound_at hfit d.validCls hh)
  obtain ⟨hp, peer, hcmd⟩ := hr_send_party_cmd hh
  have hwrap : runWrapped (ev (4 + 2 * h)) = false := by
    rw [← sendCallOf_whisper hh]; exact send_runWrapped_whisper (by omega) (by omega)
  have hex := d.whisper_out h hh hlt
  have hcoins : 64 ≤ (ev (4 + 2 * h)).coins.length := by
    rw [← sendCallOf_whisper hh]; exact send_coins_ge_64 (s := 2 + h) (by omega)
  refine ⟨rfl, by rw [hp]; rfl, by rw [hcmd]; trivial, trivial,
    w.ok_send, ⟨_, hex⟩, rfl, ?_⟩
  refine ⟨⟨.pt, [randTerm (55 + 14 * h) 32], .single, none⟩,
    if cls (2 + h) != 0 then [rngEntry (randTerm (55 + 14 * h + 1) (cls (2 + h)))] else [],
    [⟨.send, [cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h)], .whisper, none⟩],
    by rw [hwrap]; exact w.view_send, ?_,
    drawsMatch_enc r S cls (d.validCls (2 + h) (by omega)) hcoins
      (gClean_sigma_whisper_coins r cls hh),
    ?_, trivial, fun _ _ => trivial⟩
  · refine ⟨by unfold inputKind; rw [hcmd], ?_⟩
    simp only [List.map_cons, List.map_nil, gamma_randTerm_pos (by decide : 32 ≠ 0),
      gClean_sigma_whisper_pt r cls hh]
  · unfold OutputsMatch
    rw [hex, hcmd]
    exact ⟨_, rfl, rfl, _, rfl, rfl⟩

private theorem runMatches_clean_whisper_recv {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k h : Nat} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls)
    (hh : h < 10) (hlt : 4 + 2 * h < k) :
    RunMatches evictedI0 r S (gClean r cls)
      (runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h)))
      (.messageDecrypt (hrReceiver h) (hrStHRecv h) (55 + 14 * h + 6) (55 + 14 * h + 2) 1)
      (ev (5 + 2 * h))
      (stepView (.messageDecrypt (hrReceiver h) (hrStHRecv h)
          (55 + 14 * h + 6) (55 + 14 * h + 2) 1)
        (runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h))) (runWrapped (ev (5 + 2 * h))))
      (some (none, 7#32, 9#32)) := by
  have w := Classical.choice (cleanHalfRound_at hfit d.validCls hh)
  obtain ⟨hp, peer, hcmd⟩ := hr_recv_party_cmd hh
  have hmem_rep := cleanRecvTerm_mem_whisper hfit d hh hlt
  obtain ⟨hw_out, hw_exit⟩ := whisper_wire_eq (hr_mem_whisper hh) (by omega)
  rw [show 5 + 2 * h - 1 = 4 + 2 * h by omega] at hw_out hw_exit
  have hcomb := hw_out.symm.trans (d.whisper_out h hh hlt)
  injection hcomb with hpair
  have hin : (ev (5 + 2 * h)).input =
      wireWhisperTag :: gamma evictedI0 S (gClean r cls)
        (cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h)) :=
    (Prod.mk.inj hpair).2
  have hwrap : runWrapped (ev (5 + 2 * h)) = false := (hr_whisper_spec hh).1
  have hmem_rc : 5 + 2 * h ∈ recvCallIndices := by
    revert hh
    match h with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => intro _; decide
    | n + 10 => intro hh; omega
  have hcoins := active_recv_coins_ge_32 hmem_rc (by omega)
  refine ⟨rfl, by rw [hp]; rfl, by rw [hcmd]; trivial, trivial,
    w.ok_recv, ⟨_, hw_exit⟩, rfl, ?_⟩
  refine ⟨⟨.recv, [cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h)], .whisper, none⟩,
    [rngEntry (randTerm (55 + 14 * h + 7) 32)],
    [⟨.accept, [rnd (55 + 14 * h) 32], .single, none⟩],
    by rw [hwrap]; exact w.view_recv,
    ⟨by unfold inputKind; rw [hcmd], _, rfl, hin⟩,
    drawsMatch_single32 r S cls hcoins (gClean_sigma_whisper_dhs r cls hh),
    ?_, ?_, ?_⟩
  · unfold OutputsMatch
    rw [hw_exit, hcmd]
    refine ⟨_, rfl, rfl, ?_⟩
    simp only [List.map_cons, List.map_nil]
    unfold rnd
    rw [gamma_rand]
    simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte, gClean_sigma_whisper_pt r cls hh]
  · unfold ReadsFaithfully
    rw [hin]
    simpa [hin] using hmem_rep
  · intro p hp_pk
    rw [hin] at hp_pk
    have hne : wireWhisperTag ≠ DY.Libsignal.PQXDH.Refinement.wirePrekeyTag := by decide
    simp [parsePreKeyWire, hne] at hp_pk

private theorem cleanStepsMatch_upto {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k : Nat} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls) :
    ∀ m ≤ 24,
      (3 < m → 3 < k) →
      (∀ h < 10, 4 + 2 * h < m → 4 + 2 * h < k) →
      CleanStepsMatch r S (gClean r cls) none (cleanInitIds m) (setupTrace r)
        (ssClean cls cleanSpqrIdxs m) (trace0.take m) (visClean r cls m)
  | 0, _, _, _ => .nil none (setupTrace r)
  | j + 1, hle, hgt3, hwh => by
    have hj24 : j < 24 := by omega
    have hm_prev := cleanStepsMatch_upto hfit d j (by omega)
      (fun h => hgt3 (by omega)) (fun h hh hlt => hwh h hh (by omega))
    obtain ⟨s, hs⟩ : ∃ s, (cleanCallSteps cls cleanSpqrIdxs)[j]? = some s := by
      have hlen : j < (cleanCallSteps cls cleanSpqrIdxs).length := by
        rw [cleanCallSteps_length]
        exact hj24
      exact ⟨_, List.getElem?_eq_getElem hlen⟩
    rw [ssClean_succ hs, trace0_take_succ (by omega : j < 25), visClean_succ hj24 hs]
    by_cases hj0 : j = 0
    · subst hj0
      have hs0 : s = .aliceStart "alice" "bob" 4 6 bh1 := by
        injection hs with hs0; exact hs0.symm
      subst hs0
      exact hm_prev.snoc ev0_bundle_slices.2.2.1.symm (runMatches_clean_0 hfit d)
    · have hids_j : cleanInitIds j = some (none, 7#32, 9#32) := by unfold cleanInitIds; simp [hj0]
      have hids_succ : cleanInitIds (j + 1) = nextBundleIds (cleanInitIds j) (ev j) := by
        rw [hids_j, nextBundleIds_non_init (by omega) (by omega)]; rfl
      refine hm_prev.snoc hids_succ ?_
      rw [hids_j]
      change RunMatches evictedI0 r S (gClean r cls)
        (runTrace r (ssClean cls cleanSpqrIdxs j)) s (ev j) _ _
      by_cases hj1 : j = 1
      · subst hj1
        have hs1 : s = .messageEncrypt "alice" 30 (cls 0) 33 := by
          injection hs with hs1; exact hs1.symm
        subst hs1; exact runMatches_clean_1 hfit d
      · by_cases hj2 : j = 2
        · subst hj2
          have hs2 : s = .messageEncrypt "alice" 36 (cls 1) 40 := by
            injection hs with hs2; exact hs2.symm
          subst hs2; exact runMatches_clean_2 hfit d
        · by_cases hj3 : j = 3
          · subst hj3
            have hs3 : s = .bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3) := by
              injection hs with hs3; exact hs3.symm
            subst hs3
            have hex3 : Explains evictedI0 r S (gClean r cls) (ssClean cls cleanSpqrIdxs 3)
                (visClean r cls 3) (trace0.take 3) :=
              ⟨d.compatClean, ghostWF_visClean 3 (by decide) hfit d.validCls,
                modelRunWF_ssClean 3 hfit d.validCls, hm_prev.toMatchesEventsAt⟩
            exact runMatches_clean_3 hfit d hex3
          · by_cases hpar : (j - 4) % 2 = 0
            · obtain ⟨h, hh, rfl⟩ : ∃ h < 10, j = 4 + 2 * h := ⟨(j - 4) / 2, by omega, by omega⟩
              have hs_eq := hs.symm.trans (ccs_get_send cls hh)
              injection hs_eq with hs_eq; subst hs_eq
              exact runMatches_clean_whisper_send hfit d hh (hwh h hh (by omega))
            · obtain ⟨h, hh, rfl⟩ : ∃ h < 10, j = 5 + 2 * h := ⟨(j - 4) / 2, by omega, by omega⟩
              have hs_eq := hs.symm.trans (ccs_get_recv cls hh)
              injection hs_eq with hs_eq; subst hs_eq
              exact runMatches_clean_whisper_recv hfit d hh (hwh h hh (by omega))

theorem explains_ssClean_upto {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k m : Nat} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls)
    (hm24 : m ≤ 24)
    (hgt3 : 3 < m → 3 < k)
    (hwh : ∀ h < 10, 4 + 2 * h < m → 4 + 2 * h < k) :
    Explains evictedI0 r S (gClean r cls) (ssClean cls cleanSpqrIdxs m)
      (visClean r cls m) (trace0.take m) :=
  ⟨d.compatClean, ghostWF_visClean m hm24 hfit d.validCls,
    modelRunWF_ssClean m hfit d.validCls,
    (cleanStepsMatch_upto hfit d m hm24 hgt3 hwh).toMatchesEventsAt⟩

theorem explains_ssClean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k m : Nat} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls)
    (hk24 : k ≤ 24) (hmk : m ≤ k) :
    Explains evictedI0 r S (gClean r cls) (ssClean cls cleanSpqrIdxs m)
      (visClean r cls m) (trace0.take m) :=
  explains_ssClean_upto hfit d (Nat.le_trans hmk hk24)
    (fun h => Nat.lt_of_lt_of_le h hmk)
    (fun _ _ h => Nat.lt_of_lt_of_le h hmk)

theorem accepts_ssClean_whisper {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k h : Nat} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls)
    (hh : h < 10) (hk_eq : k = 5 + 2 * h) :
    ModelAcceptsTermAfterAttackerSends evictedI0 r S (gClean r cls)
      (ssClean cls cleanSpqrIdxs k) (trace0.take k) (ev k)
      (cleanRecvTerm r cls cleanSpqrIdxs k) := by
  subst hk_eq
  have w := Classical.choice (cleanHalfRound_at hfit d.validCls hh)
  refine ⟨[], .messageDecrypt (hrReceiver h) (hrStHRecv h) (55 + 14 * h + 6) (55 + 14 * h + 2) 1,
    55 + 14 * h + 6, gClean r cls, visClean r cls ((5 + 2 * h) + 1),
    by simp, rfl, rfl, fun _ _ => rfl, ?_, ?_⟩
  · simpa using w.msg_sent
  · rw [List.map_nil, List.append_nil, ← ssClean_succ (ccs_get_recv cls hh),
      ← trace0_take_succ (by omega : 5 + 2 * h < 25)]
    exact explains_ssClean_upto hfit d (by omega) (fun _ => by omega)
      (fun h' _ hlt => by omega)

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunExtract
