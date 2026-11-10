/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunRound
public import Symbolic.Proofs.Tests.CliNonvacuity.Defs
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Clean Schedule Well-Formedness and Message Terms

Composes the initial handshake steps (`0..3`) with the five ping-pong whisper rounds (`4..23`) of
`cleanCallSteps cls cleanSpqrIdxs` to establish `ModelRunWF`, `AllRecvChainsHonest`, per-step
execution success, and closed-form equations for `cleanPreKeyRep` and `cleanRecvTerm`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTrace

open DY (ExecTrace Trace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.TripleRatchet (isCurrentSnapshot)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup Step runSteps runTrace StepsWF StepsStateFaithful ModelRunWF)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs (modelRunWF_of_append)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd aliceTr aliceTrOpt NetE)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (o1 bh1 kh1 t4 t5 t4_length t5_length t4_reach)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (runSteps_le runSteps_append)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ValidCoinLens cleanPingPongRound cleanCallSteps cleanCallSteps_length ssClean
   cleanMsgIdx cleanRecvTerm cleanPreKeyRep)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (cleanSpqrIdxs ratchetKeyTimestamps append_len le_append_of_le at?_mono at?_append_at
   setupTrace_eq_t4 setupRandoms_len_eq encTrGen encTrGen_le
   isCurrentSnapshot_self isCurrentSnapshot_non
   AllRecvChainsHonest allRecvChainsHonest_of_le
   pt1Clean coins1Clean m1Clean trClean2 trClean2_length
   pt2Clean coins2Clean m2Clean trClean3
   mhClean3 trClean4 trClean4_length s0_next_ok s1_next_ok s2_next_ok s3_next_ok)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunRound
  (inv_at_4 stepsWF_cons pingPongRound_wf)

/-- Decidable check that no step with `mustBeLatest = true` shares `(party, stateIdx)` with a later
step. -/
private def stateFaithfulBool (ss : List Step) : Bool :=
  (List.range ss.length).all fun i =>
    (List.range ss.length).all fun j =>
      !(decide (i < j)) ||
        match ss[i]?, ss[j]? with
        | some si, some sj =>
          match si.stateLoad?, sj.stateLoad? with
          | some (p1, k1, true), some (p2, k2, _) => !(p1 == p2 && k1 == k2)
          | _, _ => true
        | _, _ => true

private theorem cleanCallSteps_map_stateLoad (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) :
    (cleanCallSteps cls spqrIdxs).map Step.stateLoad? =
      (cleanCallSteps (fun _ => 0) (fun _ => 0)).map Step.stateLoad? := rfl

private theorem stateFaithful_cleanCallSteps (r : ProtocolSetup)
    (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) :
    StepsStateFaithful r (cleanCallSteps cls spqrIdxs) := by
  have hbool : stateFaithfulBool (cleanCallSteps (fun _ => 0) (fun _ => 0)) = true := by
    decide +kernel
  have hmap := cleanCallSteps_map_stateLoad cls spqrIdxs
  intro i j si sj p k b hij hsi hsj hli _ hlj
  have hjlt : j < 24 := by
    rw [← cleanCallSteps_length cls spqrIdxs]
    exact (List.getElem?_eq_some_iff.mp hsj).1
  have hilt : i < 24 := Nat.lt_trans hij hjlt
  have hi0 : ((cleanCallSteps (fun _ => 0) (fun _ => 0)).map Step.stateLoad?)[i]? =
      some (some (p, k, true)) := by
    rw [← hmap, List.getElem?_map, hsi, Option.map_some, hli]
  have hj0 : ((cleanCallSteps (fun _ => 0) (fun _ => 0)).map Step.stateLoad?)[j]? =
      some (some (p, k, b)) := by
    rw [← hmap, List.getElem?_map, hsj, Option.map_some, hlj]
  rw [List.getElem?_map] at hi0 hj0
  obtain ⟨si0, hsi0, hli0⟩ := Option.map_eq_some_iff.mp hi0
  obtain ⟨sj0, hsj0, hlj0⟩ := Option.map_eq_some_iff.mp hj0
  have hi := List.all_eq_true.mp hbool i
    (List.mem_range.mpr (by rw [cleanCallSteps_length]; exact hilt))
  have hj := List.all_eq_true.mp hi j
    (List.mem_range.mpr (by rw [cleanCallSteps_length]; exact hjlt))
  rw [hsi0, hsj0] at hj; dsimp only at hj; rw [hli0, hlj0] at hj
  simp [hij] at hj

/-- Jointly establishes `StepsWF`, `AllRecvChainsHonest`, per-step `.ok`, and sent-message
structure across all 24 steps of `cleanCallSteps cls cleanSpqrIdxs` from `t4`. -/
theorem stepsWF_and_honest_full {cls : Nat → Nat} (hv : ValidCoinLens cls) :
    StepsWF (cleanCallSteps cls cleanSpqrIdxs) t4 ∧
    AllRecvChainsHonest (runSteps (cleanCallSteps cls cleanSpqrIdxs) t4) ∧
    (∀ k < 24, ∀ s, (cleanCallSteps cls cleanSpqrIdxs)[k]? = some s →
      s.ok (runSteps (ssClean cls cleanSpqrIdxs k) t4) = true) ∧
    (∀ k ∈ [5, 7, 9, 11, 13, 15, 17, 19, 21, 23],
      ∃ mW tsM, tsM ∈ ratchetKeyTimestamps ∧
        (runSteps (ssClean cls cleanSpqrIdxs k) t4).getMessageSentAt (cleanMsgIdx k) = some mW ∧
        DY.Libsignal.TripleRatchet.parseTrSignalMsg mW ≠ none ∧
        (∀ sig, DY.Libsignal.TripleRatchet.parseTrSignalMsg mW = some sig →
          sig.ratchetKey = dhPk (rnd tsM 32))) := by
  have hcur_t5_30 : isCurrentSnapshot t5 30 = true := by
    dsimp only [t5, aliceTr, aliceTrOpt]
    exact isCurrentSnapshot_self _ _ _ (by simp only [append_len, t4_length])
  have hcur_tr2_36 : isCurrentSnapshot (trClean2 cls) 36 = true := by
    dsimp only [trClean2, encTrGen]
    exact isCurrentSnapshot_non _ rfl
      (isCurrentSnapshot_self _ _ _ (by simp only [append_len, t5_length]))
  obtain ⟨hn0, hok0⟩ := s0_next_ok
  obtain ⟨hn1, hok1⟩ := s1_next_ok cls
  obtain ⟨hn2, hok2⟩ := s2_next_ok cls
  obtain ⟨hn3, hok3⟩ := s3_next_ok cls
  obtain ⟨tr8, stB8, stA8, hrs0, hwf0, hokR0, hw5, hw7, _, hlen8, hl0_eq, hinv8⟩ :=
    pingPongRound_wf (rd := 0) (trClean4_length cls) (inv_at_4 cls)
      (hv 2 (by decide)) (hv 3 (by decide)) rfl rfl
      (by decide) (by decide)
  obtain ⟨tr12, stB12, stA12, hrs1, hwf1, hokR1, hw9, hw11, _, hlen12, hl1_eq, hinv12⟩ :=
    pingPongRound_wf (rd := 1) hlen8 hinv8
      (hv 4 (by decide)) (hv 5 (by decide)) rfl rfl
      (by rw [hl0_eq]; decide) (by rw [hl0_eq]; decide)
  obtain ⟨tr16, stB16, stA16, hrs2, hwf2, hokR2, hw13, hw15, _, hlen16, hl2_eq, hinv16⟩ :=
    pingPongRound_wf (rd := 2) hlen12 hinv12
      (hv 6 (by decide)) (hv 7 (by decide)) rfl rfl
      (by rw [hl1_eq, hl0_eq]; decide) (by rw [hl1_eq, hl0_eq]; decide)
  obtain ⟨tr20, stB20, stA20, hrs3, hwf3, hokR3, hw17, hw19, _, hlen20, hl3_eq, hinv20⟩ :=
    pingPongRound_wf (rd := 3) hlen16 hinv16
      (hv 8 (by decide)) (hv 9 (by decide)) rfl rfl
      (by rw [hl2_eq, hl1_eq, hl0_eq]; decide) (by rw [hl2_eq, hl1_eq, hl0_eq]; decide)
  obtain ⟨tr24, stB24, stA24, hrs4, hwf4, hokR4, hw21, hw23, _, _, _, hinv24⟩ :=
    pingPongRound_wf (rd := 4) hlen20 hinv20
      (hv 10 (by decide)) (hv 11 (by decide)) rfl rfl
      (by rw [hl3_eq, hl2_eq, hl1_eq, hl0_eq]; decide)
      (by rw [hl3_eq, hl2_eq, hl1_eq, hl0_eq]; decide)
  have hwf_append : ∀ {xs ys : List Step} {tr : ExecTrace},
      StepsWF xs tr → StepsWF ys (runSteps xs tr) → StepsWF (xs ++ ys) tr := by
    intro xs ys tr hx hy
    induction xs generalizing tr with
    | nil => exact hy
    | cons x xs' ih => exact ⟨hx.1, hx.2.1, ih hx.2.2 hy⟩
  have hwf0_3 : StepsWF [Step.aliceStart "alice" "bob" 4 6 bh1,
      Step.messageEncrypt "alice" 30 (cls 0) 33,
      Step.messageEncrypt "alice" 36 (cls 1) 40,
      Step.bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3)] t4 :=
    stepsWF_cons trivial trivial hn0
      (stepsWF_cons hcur_t5_30 ⟨hv 0 (by decide), Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [t5_length])⟩ hn1
      (stepsWF_cons hcur_tr2_36 ⟨hv 1 (by decide), Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [trClean2_length])⟩ hn2
      (stepsWF_cons trivial trivial hn3 trivial)))
  have hrun0_3 : runSteps [Step.aliceStart "alice" "bob" 4 6 bh1,
      Step.messageEncrypt "alice" 30 (cls 0) 33,
      Step.messageEncrypt "alice" 36 (cls 1) 40,
      Step.bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3)] t4 = trClean4 cls := by
    simp only [runSteps, hn0, hn1, hn2, hn3]
  let b0 := [Step.aliceStart "alice" "bob" 4 6 bh1,
      Step.messageEncrypt "alice" 30 (cls 0) 33,
      Step.messageEncrypt "alice" 36 (cls 1) 40,
      Step.bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3)]
  let r0s := (cleanPingPongRound cls cleanSpqrIdxs 0 43 54 55).1
  let l0 := (cleanPingPongRound cls cleanSpqrIdxs 0 43 54 55).2.2.2
  let a0 := (cleanPingPongRound cls cleanSpqrIdxs 0 43 54 55).2.1
  let b0' := (cleanPingPongRound cls cleanSpqrIdxs 0 43 54 55).2.2.1
  let r1s := (cleanPingPongRound cls cleanSpqrIdxs 1 a0 b0' l0).1
  let l1 := (cleanPingPongRound cls cleanSpqrIdxs 1 a0 b0' l0).2.2.2
  let a1 := (cleanPingPongRound cls cleanSpqrIdxs 1 a0 b0' l0).2.1
  let b1' := (cleanPingPongRound cls cleanSpqrIdxs 1 a0 b0' l0).2.2.1
  let r2s := (cleanPingPongRound cls cleanSpqrIdxs 2 a1 b1' l1).1
  let l2 := (cleanPingPongRound cls cleanSpqrIdxs 2 a1 b1' l1).2.2.2
  let a2 := (cleanPingPongRound cls cleanSpqrIdxs 2 a1 b1' l1).2.1
  let b2' := (cleanPingPongRound cls cleanSpqrIdxs 2 a1 b1' l1).2.2.1
  let r3s := (cleanPingPongRound cls cleanSpqrIdxs 3 a2 b2' l2).1
  let l3 := (cleanPingPongRound cls cleanSpqrIdxs 3 a2 b2' l2).2.2.2
  let a3 := (cleanPingPongRound cls cleanSpqrIdxs 3 a2 b2' l2).2.1
  let b3' := (cleanPingPongRound cls cleanSpqrIdxs 3 a2 b2' l2).2.2.1
  let r4s := (cleanPingPongRound cls cleanSpqrIdxs 4 a3 b3' l3).1
  have hccs : cleanCallSteps cls cleanSpqrIdxs = b0 ++ r0s ++ r1s ++ r2s ++ r3s ++ r4s := rfl
  have htake_r0 : ∀ i ≤ 4, (cleanCallSteps cls cleanSpqrIdxs).take (4 + i) = b0 ++ r0s.take i := by
    intro i hi; match i with | 0 | 1 | 2 | 3 | 4 => rfl | n + 5 => omega
  have htake_r1 : ∀ i ≤ 4, (cleanCallSteps cls cleanSpqrIdxs).take (8 + i) =
      b0 ++ r0s ++ r1s.take i := by
    intro i hi; match i with | 0 | 1 | 2 | 3 | 4 => rfl | n + 5 => omega
  have htake_r2 : ∀ i ≤ 4, (cleanCallSteps cls cleanSpqrIdxs).take (12 + i) =
      b0 ++ r0s ++ r1s ++ r2s.take i := by
    intro i hi; match i with | 0 | 1 | 2 | 3 | 4 => rfl | n + 5 => omega
  have htake_r3 : ∀ i ≤ 4, (cleanCallSteps cls cleanSpqrIdxs).take (16 + i) =
      b0 ++ r0s ++ r1s ++ r2s ++ r3s.take i := by
    intro i hi; match i with | 0 | 1 | 2 | 3 | 4 => rfl | n + 5 => omega
  have htake_r4 : ∀ i ≤ 4, (cleanCallSteps cls cleanSpqrIdxs).take (20 + i) =
      b0 ++ r0s ++ r1s ++ r2s ++ r3s ++ r4s.take i := by
    intro i hi; match i with | 0 | 1 | 2 | 3 | 4 => rfl | n + 5 => omega
  have hrun_p0 : runSteps b0 t4 = trClean4 cls := hrun0_3
  have hrun_p1 : runSteps (b0 ++ r0s) t4 = tr8 := by rw [runSteps_append, hrun_p0]; exact hrs0
  have hrun_p2 : runSteps (b0 ++ r0s ++ r1s) t4 = tr12 := by rw [runSteps_append, hrun_p1]; exact hrs1
  have hrun_p3 : runSteps (b0 ++ r0s ++ r1s ++ r2s) t4 = tr16 := by
    rw [runSteps_append, hrun_p2]; exact hrs2
  have hrun_p4 : runSteps (b0 ++ r0s ++ r1s ++ r2s ++ r3s) t4 = tr20 := by
    rw [runSteps_append, hrun_p3]; exact hrs3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hccs]
    exact hwf_append (hwf_append (hwf_append (hwf_append
      (hwf_append hwf0_3 (by rw [hrun_p0]; exact hwf0))
      (by rw [hrun_p1]; exact hwf1))
      (by rw [hrun_p2]; exact hwf2))
      (by rw [hrun_p3]; exact hwf3))
      (by rw [hrun_p4]; exact hwf4)
  · rw [hccs, runSteps_append, hrun_p4]
    exact hrs4 ▸ hinv24.honest_all
  · intro k hk24 s hs
    unfold ssClean
    by_cases hk4 : k < 4
    · match k with
      | 0 => have h0 : (cleanCallSteps cls cleanSpqrIdxs)[0]? = some (Step.aliceStart "alice" "bob" 4 6 bh1) := rfl
             rw [h0] at hs; injection hs with hs'; subst hs'; exact hok0
      | 1 => have h0 : (cleanCallSteps cls cleanSpqrIdxs)[1]? = some (Step.messageEncrypt "alice" 30 (cls 0) 33) := rfl
             have ht : (cleanCallSteps cls cleanSpqrIdxs).take 1 = [Step.aliceStart "alice" "bob" 4 6 bh1] := rfl
             rw [h0] at hs; injection hs with hs'; subst hs'; rw [ht]; simp only [runSteps, hn0]; exact hok1
      | 2 => have h0 : (cleanCallSteps cls cleanSpqrIdxs)[2]? = some (Step.messageEncrypt "alice" 36 (cls 1) 40) := rfl
             have ht : (cleanCallSteps cls cleanSpqrIdxs).take 2 = [Step.aliceStart "alice" "bob" 4 6 bh1, Step.messageEncrypt "alice" 30 (cls 0) 33] := rfl
             rw [h0] at hs; injection hs with hs'; subst hs'; rw [ht]; simp only [runSteps, hn0, hn1]; exact hok2
      | 3 => have h0 : (cleanCallSteps cls cleanSpqrIdxs)[3]? = some (Step.bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3)) := rfl
             have ht : (cleanCallSteps cls cleanSpqrIdxs).take 3 = [Step.aliceStart "alice" "bob" 4 6 bh1, Step.messageEncrypt "alice" 30 (cls 0) 33, Step.messageEncrypt "alice" 36 (cls 1) 40] := rfl
             rw [h0] at hs; injection hs with hs'; subst hs'; rw [ht]; simp only [runSteps, hn0, hn1, hn2]; exact hok3
      | n + 4 => omega
    · by_cases hk8 : k < 8
      · have hk_eq : k = 4 + (k - 4) := by omega
        have hi : k - 4 < 4 := by omega
        have hget : (cleanCallSteps cls cleanSpqrIdxs)[4 + (k - 4)]? = r0s[k - 4]? := by
          match h : k - 4 with | 0 | 1 | 2 | 3 => rfl | n + 4 => omega
        rw [hk_eq] at hs ⊢
        rw [htake_r0 (k - 4) (by omega), runSteps_append, hrun_p0]
        exact hokR0 (k - 4) hi s (hget ▸ hs)
      · by_cases hk12 : k < 12
        · have hk_eq : k = 8 + (k - 8) := by omega
          have hi : k - 8 < 4 := by omega
          have hget : (cleanCallSteps cls cleanSpqrIdxs)[8 + (k - 8)]? = r1s[k - 8]? := by
            match h : k - 8 with | 0 | 1 | 2 | 3 => rfl | n + 4 => omega
          rw [hk_eq] at hs ⊢
          rw [htake_r1 (k - 8) (by omega), runSteps_append, hrun_p1]
          exact hokR1 (k - 8) hi s (hget ▸ hs)
        · by_cases hk16 : k < 16
          · have hk_eq : k = 12 + (k - 12) := by omega
            have hi : k - 12 < 4 := by omega
            have hget : (cleanCallSteps cls cleanSpqrIdxs)[12 + (k - 12)]? = r2s[k - 12]? := by
              match h : k - 12 with | 0 | 1 | 2 | 3 => rfl | n + 4 => omega
            rw [hk_eq] at hs ⊢
            rw [htake_r2 (k - 12) (by omega), runSteps_append, hrun_p2]
            exact hokR2 (k - 12) hi s (hget ▸ hs)
          · by_cases hk20 : k < 20
            · have hk_eq : k = 16 + (k - 16) := by omega
              have hi : k - 16 < 4 := by omega
              have hget : (cleanCallSteps cls cleanSpqrIdxs)[16 + (k - 16)]? = r3s[k - 16]? := by
                match h : k - 16 with | 0 | 1 | 2 | 3 => rfl | n + 4 => omega
              rw [hk_eq] at hs ⊢
              rw [htake_r3 (k - 16) (by omega), runSteps_append, hrun_p3]
              exact hokR3 (k - 16) hi s (hget ▸ hs)
            · have hk_eq : k = 20 + (k - 20) := by omega
              have hi : k - 20 < 4 := by omega
              have hget : (cleanCallSteps cls cleanSpqrIdxs)[20 + (k - 20)]? = r4s[k - 20]? := by
                match h : k - 20 with | 0 | 1 | 2 | 3 => rfl | n + 4 => omega
              rw [hk_eq] at hs ⊢
              rw [htake_r4 (k - 20) (by omega), runSteps_append, hrun_p4]
              exact hokR4 (k - 20) hi s (hget ▸ hs)
  · intro k hk
    unfold ssClean
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [htake_r0 1 (by decide), runSteps_append, hrun_p0]; exact hw5
    · rw [htake_r0 3 (by decide), runSteps_append, hrun_p0]; exact hw7
    · rw [htake_r1 1 (by decide), runSteps_append, hrun_p1]; exact hw9
    · rw [htake_r1 3 (by decide), runSteps_append, hrun_p1]; exact hw11
    · rw [htake_r2 1 (by decide), runSteps_append, hrun_p2]; exact hw13
    · rw [htake_r2 3 (by decide), runSteps_append, hrun_p2]; exact hw15
    · rw [htake_r3 1 (by decide), runSteps_append, hrun_p3]; exact hw17
    · rw [htake_r3 3 (by decide), runSteps_append, hrun_p3]; exact hw19
    · rw [htake_r4 1 (by decide), runSteps_append, hrun_p4]; exact hw21
    · rw [htake_r4 3 (by decide), runSteps_append, hrun_p4]; exact hw23

theorem modelRunWF_cleanCallSteps {r : ProtocolSetup} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hv : ValidCoinLens cls) :
    ModelRunWF r (cleanCallSteps cls cleanSpqrIdxs) :=
  ⟨setupRandoms_len_eq hfit,
   setupTrace_eq_t4 hfit ▸ t4_reach,
   setupTrace_eq_t4 hfit ▸ (stepsWF_and_honest_full hv).1,
   stateFaithful_cleanCallSteps r cls cleanSpqrIdxs⟩

theorem modelRunWF_ssClean {r : ProtocolSetup} {cls : Nat → Nat} (k : Nat)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hv : ValidCoinLens cls) :
    ModelRunWF r (ssClean cls cleanSpqrIdxs k) := by
  have hfull := modelRunWF_cleanCallSteps hfit hv
  rw [← List.take_append_drop k (cleanCallSteps cls cleanSpqrIdxs)] at hfull
  exact modelRunWF_of_append hfull

theorem step_ok_ssClean {r : ProtocolSetup} {cls : Nat → Nat} {k : Nat} {s : Step}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hv : ValidCoinLens cls)
    (hk : k < 24)
    (hs : (cleanCallSteps cls cleanSpqrIdxs)[k]? = some s) :
    s.ok (runTrace r (ssClean cls cleanSpqrIdxs k)) = true := by
  unfold runTrace
  rw [setupTrace_eq_t4 hfit]
  exact (stepsWF_and_honest_full hv).2.2.1 k hk s hs

theorem ssClean_succ {cls : Nat → Nat} {spqrIdxs : Nat → UInt32} {k : Nat} {s : Step}
    (hs : (cleanCallSteps cls spqrIdxs)[k]? = some s) :
    ssClean cls spqrIdxs (k + 1) = ssClean cls spqrIdxs k ++ [s] := by
  unfold ssClean
  rw [List.take_add_one, hs, Option.toList_some]

theorem allRecvChainsHonest_ssClean {r : ProtocolSetup} {cls : Nat → Nat} (k : Nat)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hv : ValidCoinLens cls) :
    AllRecvChainsHonest (runTrace r (ssClean cls cleanSpqrIdxs k)) := by
  unfold runTrace
  rw [setupTrace_eq_t4 hfit]
  have hfull := (stepsWF_and_honest_full hv).2.1
  have hsplit := (List.take_append_drop k (cleanCallSteps cls cleanSpqrIdxs)).symm
  rw [hsplit, runSteps_append] at hfull
  exact allRecvChainsHonest_of_le (runSteps_le _ _) hfull

theorem cleanPreKeyRep_eq {r : ProtocolSetup} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    cleanPreKeyRep r cls cleanSpqrIdxs =
      { ek := o1.ek, ct := o1.ct, msg := m2Clean cls } := by
  have htake3 : ssClean cls cleanSpqrIdxs 3 =
      [Step.aliceStart "alice" "bob" 4 6 bh1,
       Step.messageEncrypt "alice" 30 (cls 0) 33,
       Step.messageEncrypt "alice" 36 (cls 1) 40] := rfl
  have hrun3 : runTrace r (ssClean cls cleanSpqrIdxs 3) = trClean3 cls := by
    unfold runTrace
    rw [setupTrace_eq_t4 hfit, htake3]
    dsimp only [runSteps]
    rw [(s0_next_ok).1, (s1_next_ok cls).1, (s2_next_ok cls).1]
  have h53 : t5 ≤ trClean3 cls :=
    Trace.le_trans _ _ _ (encTrGen_le _ _ _ _ _ _) (encTrGen_le _ _ _ _ _ _)
  have hek : (trClean3 cls).getMessageSentAt 25 = some o1.ek := by
    have hat : (trClean3 cls).at? 25 = some (NetE o1.ek) := by
      refine at?_mono h53 ?_; dsimp only [t5, aliceTr, aliceTrOpt, o1,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt]
      rw [t4_length]
      exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
        (le_append_of_le (Trace.append_le _ _) _) _) _) _)
        (at?_append_at _ _ (by simp only [append_len, t4_length]))
    rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat]
  have hct : (trClean3 cls).getMessageSentAt 26 = some o1.ct := by
    have hat : (trClean3 cls).at? 26 = some (NetE o1.ct) := by
      refine at?_mono h53 ?_; dsimp only [t5, aliceTr, aliceTrOpt, o1,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt]
      rw [t4_length]
      exact at?_mono (le_append_of_le (le_append_of_le
        (le_append_of_le (Trace.append_le _ _) _) _) _)
        (at?_append_at _ _ (by simp only [append_len, t4_length]))
    rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat]
  have hmsg : (trClean3 cls).getMessageSentAt 44 = some (m2Clean cls) := by
    have hat : (trClean3 cls).at? 44 = some (NetE (m2Clean cls)) := by
      dsimp only [trClean3, encTrGen, m2Clean]
      have hm : rnd (trClean2 cls).length 32 = pt2Clean := by rw [trClean2_length]; rfl
      have hc : rnd ((trClean2 cls).length + 1) (cls 1) = coins2Clean cls := by
        rw [trClean2_length]; rfl
      rw [hm, hc]
      exact at?_append_at _ _ (by simp only [append_len, trClean2_length])
    rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat]
  have hidx3 : cleanMsgIdx 3 = 44 := rfl
  unfold cleanPreKeyRep cleanRecvTerm
  rw [hidx3, hrun3, hek, hct, hmsg]
  rfl

theorem cleanRecvTerm_24_eq {r : ProtocolSetup} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    cleanRecvTerm r cls cleanSpqrIdxs 24 = m1Clean cls := by
  have htake2 : (cleanCallSteps cls cleanSpqrIdxs).take 2 =
      [Step.aliceStart "alice" "bob" 4 6 bh1,
       Step.messageEncrypt "alice" 30 (cls 0) 33] := rfl
  have h2_le_24 : trClean2 cls ≤ runTrace r (ssClean cls cleanSpqrIdxs 24) := by
    unfold runTrace ssClean
    rw [setupTrace_eq_t4 hfit, List.take_of_length_le (by rw [cleanCallSteps_length])]
    have hsplit := (List.take_append_drop 2 (cleanCallSteps cls cleanSpqrIdxs)).symm
    rw [hsplit, runSteps_append, htake2]
    dsimp only [runSteps]
    rw [(s0_next_ok).1, (s1_next_ok cls).1]
    exact runSteps_le _ _
  have hm1 : (trClean2 cls).at? 37 = some (NetE (m1Clean cls)) := by
    dsimp only [trClean2, encTrGen, m1Clean]
    have hm : rnd t5.length 32 = pt1Clean := by rw [t5_length]; rfl
    have hc : rnd (t5.length + 1) (cls 0) = coins1Clean cls := by rw [t5_length]; rfl
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, t5_length])
  have hat : (runTrace r (ssClean cls cleanSpqrIdxs 24)).at? 37 = some (NetE (m1Clean cls)) :=
    at?_mono h2_le_24 hm1
  have hidx24 : cleanMsgIdx 24 = 37 := rfl
  unfold cleanRecvTerm
  rw [hidx24, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat]
  rfl

theorem cleanRecvTerm_whisper_sent {r : ProtocolSetup} {cls : Nat → Nat} {k : Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hv : ValidCoinLens cls)
    (hk : k ∈ [5, 7, 9, 11, 13, 15, 17, 19, 21, 23]) :
    ∃ tsM ∈ ratchetKeyTimestamps,
      (runTrace r (ssClean cls cleanSpqrIdxs k)).getMessageSentAt (cleanMsgIdx k) =
        some (cleanRecvTerm r cls cleanSpqrIdxs k) ∧
      DY.Libsignal.TripleRatchet.parseTrSignalMsg (cleanRecvTerm r cls cleanSpqrIdxs k) ≠ none ∧
      (∀ sig, DY.Libsignal.TripleRatchet.parseTrSignalMsg (cleanRecvTerm r cls cleanSpqrIdxs k) =
        some sig → sig.ratchetKey = dhPk (rnd tsM 32)) := by
  obtain ⟨mW, tsM, hts, hsent, hparse, hrk⟩ := (stepsWF_and_honest_full hv).2.2.2 k hk
  have hsent' : (runTrace r (ssClean cls cleanSpqrIdxs k)).getMessageSentAt (cleanMsgIdx k) =
      some mW := by
    unfold runTrace; rw [setupTrace_eq_t4 hfit]; exact hsent
  have heq : cleanRecvTerm r cls cleanSpqrIdxs k = mW := by
    unfold cleanRecvTerm; rw [hsent']; rfl
  rw [heq]
  exact ⟨tsM, hts, hsent', hparse, hrk⟩

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTrace
