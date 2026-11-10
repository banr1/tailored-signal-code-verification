/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInvB

/-!
# Prefix Propagation to Call 24

Propagates `NoBobState` across Alice's initial calls `0..2`, establishes `BobActiveInv` on Call `3`
(`bobStart`), and steps `BobActiveInv` across the five ping-pong rounds in Calls `4..23`. By Call
`24`, `pk_A0` (`idx = 4`) has been dropped from Bob's 5-element `recv` list `[6, 8, 10, 12, 14]`
and Bob's active ratchet secret is `15`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfePrefix

open DY (ExecTrace)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   clamp setupTrace StepsWF runSteps RunRejected RunMatches MatchesEventsAt Explains GhostWF)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned evictedSecretIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (cliTrace ev trace_eq_evs ev_not_rejected ev_alice ev_bob_send ev_bob_recv
   WhisperInputSpec ev7_whisper ev11_whisper ev15_whisper ev19_whisper ev23_whisper
   ev7_coins_idx ev11_coins_idx ev15_coins_idx ev19_coins_idx ev23_coins_idx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (r_names_of_fit matchesEventsAt_run_peel noBobState_setupTrace
   noNewBobState_runSteps_network BobActiveInv noNewBobState_preserves_active)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv
  (alice_step_noBobState alice_step_active bob_call3_step)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInvB
  (bob_send_step bob_whisper_recv_step)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

theorem pingPong_round {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {recvIdxs : List (Fin 16)} {skIdx pkIdx skIdx' : Fin 16}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
    {e1 e2 e3 e4 : RunEvent} {evs : List CliEvent} {vis visAll : List VisEntry}
    (hgwf : GhostWF g visAll)
    (hinv : BobActiveInv S g recvIdxs skIdx tr)
    (hwf : StepsWF ss tr)
    (hm : MatchesEventsAt evictedI0 r S g initIds tr ss
      (.run e1 :: .run e2 :: .run e3 :: .run e4 :: evs) vis)
    (hsub : ∀ w ∈ vis, w ∈ visAll)
    (hnr1 : ¬ RunRejected e1) (hb1 : e1.party = "bob" ∧ ∃ peer, e1.cmd = .send peer)
    (hnr2 : ¬ RunRejected e2) (ha2 : e2.party = "alice")
    (hnr3 : ¬ RunRejected e3) (ha3 : e3.party = "alice")
    (hnr4 : ¬ RunRejected e4) (hb4 : e4.party = "bob" ∧ ∃ peer, e4.cmd = .recv peer)
    (hwh : WhisperInputSpec e4 pkIdx)
    (hcoins : evictedSecretIdx (clamp (e4.coins.take 32)) = some skIdx')
    (hnotMem : pkIdx ∉ recvIdxs) :
    ∃ initIds' tr' ss' vs,
      BobActiveInv S g ((recvIdxs ++ [pkIdx]).drop ((recvIdxs.length + 1) - 5)) skIdx' tr' ∧
      StepsWF ss' tr' ∧
      MatchesEventsAt evictedI0 r S g initIds' tr' ss' evs vs ∧
      (∀ w ∈ vs, w ∈ visAll) := by
  obtain ⟨pre1, s1, ss1, v1, vs1, hnet1, hpre1, hwf1, hrm1, _, hsub1, hm1⟩ :=
    matchesEventsAt_run_peel hnr1 hwf hm hsub
  have hinv1 := bob_send_step hinv hnet1 hpre1 hb1 hrm1
  obtain ⟨pre2, s2, ss2, v2, vs2, hnet2, _, hwf2, hrm2, _, hsub2, hm2⟩ :=
    matchesEventsAt_run_peel hnr2 hwf1 hm1 hsub1
  have hinv2 := alice_step_active hinv1 hnet2 ha2 hrm2
  obtain ⟨pre3, s3, ss3, v3, vs3, hnet3, _, hwf3, hrm3, _, hsub3, hm3⟩ :=
    matchesEventsAt_run_peel hnr3 hwf2 hm2 hsub2
  have hinv3 := alice_step_active hinv2 hnet3 ha3 hrm3
  obtain ⟨pre4, s4, ss4, v4, vs4, hnet4, hpre4, hwf4, hrm4, hv4, hsub4, hm4⟩ :=
    matchesEventsAt_run_peel hnr4 hwf3 hm3 hsub3
  have hinv4 := bob_whisper_recv_step hgwf hinv3 hnet4 hpre4 hb4 hwh hcoins hnotMem hrm4 hv4
  exact ⟨_, _, ss4, vs4, hinv4, hwf4, hm4, hsub4⟩

theorem prefix_to_call24 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hex : Explains evictedI0 r S g ss vis cliTrace) :
    ∃ tr₂₄ s₂₄ v₂₄ initIds₂₄,
      BobActiveInv S g
        [⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩]
        ⟨15, by decide⟩ tr₂₄ ∧
      s₂₄.PreCond tr₂₄ ∧
      RunMatches evictedI0 r S g tr₂₄ s₂₄ (ev 24) v₂₄ initIds₂₄ := by
  have halice_r : r.alice = "alice" := (r_names_of_fit hfit).1
  have hgwf : GhostWF g vis := hex.2.1
  have hwf0 : StepsWF ss (setupTrace r) := hex.2.2.1.2.2.1
  have hm0 : MatchesEventsAt evictedI0 r S g none (setupTrace r) ss cliTrace vis := hex.2.2.2
  rw [trace_eq_evs] at hm0
  have hnoBob0 := noBobState_setupTrace r
  obtain ⟨pre0, s0, ss0, _, vs0, hnet0, _, hwf1, hrm0, _, hsub0, hm1⟩ :=
    matchesEventsAt_run_peel (ev_not_rejected 0 (by decide)) hwf0 hm0 (fun _ h => h)
  have hnoBob1 := alice_step_noBobState hnoBob0 hnet0 (ev_alice 0 (by decide)) hrm0
  obtain ⟨pre1, s1, ss1, _, vs1, hnet1, _, hwf2, hrm1, _, hsub1, hm2⟩ :=
    matchesEventsAt_run_peel (ev_not_rejected 1 (by decide)) hwf1 hm1 hsub0
  have hnoBob2 := alice_step_noBobState hnoBob1 hnet1 (ev_alice 1 (by decide)) hrm1
  obtain ⟨pre2, s2, ss2, _, vs2, hnet2, _, hwf3, hrm2, _, hsub2, hm3⟩ :=
    matchesEventsAt_run_peel (ev_not_rejected 2 (by decide)) hwf2 hm2 hsub1
  have hnoBob3 := alice_step_noBobState hnoBob2 hnet2 (ev_alice 2 (by decide)) hrm2
  obtain ⟨pre3, s3, ss3, v3, vs3, hnet3, _, hwf4, hrm3, hv3, hsub3, hm4⟩ :=
    matchesEventsAt_run_peel (ev_not_rejected 3 (by decide)) hwf3 hm3 hsub2
  have hinv3 := bob_call3_step halice_r hgwf hnoBob3 hnet3 hrm3 hv3
  obtain ⟨_, tr7, ss7, vs7, hinv7, hwf7, hm7, hsub7⟩ :=
    pingPong_round hgwf hinv3 hwf4 hm4 hsub3
      (ev_not_rejected 4 (by decide)) (ev_bob_send 4 (by decide))
      (ev_not_rejected 5 (by decide)) (ev_alice 5 (by decide))
      (ev_not_rejected 6 (by decide)) (ev_alice 6 (by decide))
      (ev_not_rejected 7 (by decide)) (ev_bob_recv 7 (by decide))
      ev7_whisper ev7_coins_idx (by decide)
  change BobActiveInv S g [⟨4, by decide⟩, ⟨6, by decide⟩] ⟨7, by decide⟩ tr7 at hinv7
  obtain ⟨_, tr11, ss11, vs11, hinv11, hwf11, hm11, hsub11⟩ :=
    pingPong_round hgwf hinv7 hwf7 hm7 hsub7
      (ev_not_rejected 8 (by decide)) (ev_bob_send 8 (by decide))
      (ev_not_rejected 9 (by decide)) (ev_alice 9 (by decide))
      (ev_not_rejected 10 (by decide)) (ev_alice 10 (by decide))
      (ev_not_rejected 11 (by decide)) (ev_bob_recv 11 (by decide))
      ev11_whisper ev11_coins_idx (by decide)
  change BobActiveInv S g
    [⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩] ⟨9, by decide⟩ tr11 at hinv11
  obtain ⟨_, tr15, ss15, vs15, hinv15, hwf15, hm15, hsub15⟩ :=
    pingPong_round hgwf hinv11 hwf11 hm11 hsub11
      (ev_not_rejected 12 (by decide)) (ev_bob_send 12 (by decide))
      (ev_not_rejected 13 (by decide)) (ev_alice 13 (by decide))
      (ev_not_rejected 14 (by decide)) (ev_alice 14 (by decide))
      (ev_not_rejected 15 (by decide)) (ev_bob_recv 15 (by decide))
      ev15_whisper ev15_coins_idx (by decide)
  change BobActiveInv S g
    [⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩]
    ⟨11, by decide⟩ tr15 at hinv15
  obtain ⟨_, tr19, ss19, vs19, hinv19, hwf19, hm19, hsub19⟩ :=
    pingPong_round hgwf hinv15 hwf15 hm15 hsub15
      (ev_not_rejected 16 (by decide)) (ev_bob_send 16 (by decide))
      (ev_not_rejected 17 (by decide)) (ev_alice 17 (by decide))
      (ev_not_rejected 18 (by decide)) (ev_alice 18 (by decide))
      (ev_not_rejected 19 (by decide)) (ev_bob_recv 19 (by decide))
      ev19_whisper ev19_coins_idx (by decide)
  change BobActiveInv S g
    [⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩]
    ⟨13, by decide⟩ tr19 at hinv19
  obtain ⟨_, tr23, ss23, vs23, hinv23, hwf23, hm23, hsub23⟩ :=
    pingPong_round hgwf hinv19 hwf19 hm19 hsub19
      (ev_not_rejected 20 (by decide)) (ev_bob_send 20 (by decide))
      (ev_not_rejected 21 (by decide)) (ev_alice 21 (by decide))
      (ev_not_rejected 22 (by decide)) (ev_alice 22 (by decide))
      (ev_not_rejected 23 (by decide)) (ev_bob_recv 23 (by decide))
      ev23_whisper ev23_coins_idx (by decide)
  change BobActiveInv S g
    [⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩]
    ⟨15, by decide⟩ tr23 at hinv23
  obtain ⟨pre24, s24, _, v24, _, hnet24, hpre24, _, hrm24, _, _, _⟩ :=
    matchesEventsAt_run_peel (ev_not_rejected 24 (by decide)) hwf23 hm23 hsub23
  have hinv24 :=
    noNewBobState_preserves_active (noNewBobState_runSteps_network pre24 tr23 hnet24) hinv23
  exact ⟨runSteps pre24 tr23, s24, v24, _, hinv24, hpre24, hrm24⟩

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfePrefix
