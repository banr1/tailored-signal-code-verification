/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunExtract
import Symbolic.DYBridge.DY.Bytes.Basic

/-!
# Clean Prefix Read and Reselection Collision Absence

Proves two collision-absence properties on the canonical clean schedule
`(gClean r cls, ssClean cls cleanSpqrIdxs, visClean r cls)`:
`not_readCollisionCli_ssClean` rules out `ReadCollisionCli` on any prefix `k ≤ 24` by pinning
earlier decryptions to whisper steps, and `not_reselectCollisionOn_ssClean` rules out
`ReselectCollisionOn` at `k ∈ whisperOrReplayIndices` via `AllRecvChainsHonest` and
`gamma_ratchetKeyTimestamps_inj`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunAccept

open scoped DY.Libsignal.Composed
open DY (ExecTrace Participant)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg findRecvChain)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
   setupTrace runTrace storedStates availableStates storedRatchetKeys honestSaltsOf
   runWrapped stepView MatchesEventsAt Explains RecvCollisionOn ReselectCollisionOn)
open DY.Libsignal.Composed.Refinement.Cli (ReadCollisionCli)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (StT rnd parse_encMsg)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (bh1 kh1 stA0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (trace0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ValidCoinLens whisperOrReplayIndices cleanCallSteps ssClean cleanMsgIdx cleanRecvTerm)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev trace_eq_evs ev_not_rejected)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
  (trace0_eq_cliTrace trace0_getElem?_eq_ev)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (cleanSpqrIdxs ratchetKeyTimestamps AllRecvChainsHonest m1Clean mhClean3)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
  (gClean gamma_ratchetKeyTimestamps_inj)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTrace
  (allRecvChainsHonest_ssClean cleanRecvTerm_24_eq cleanRecvTerm_whisper_sent)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunPrefix
  (hr_mem_whisper ccs_get_send ccs_get_recv CleanPrefixData)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVis
  (visOfSteps visClean)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunExtract
  (explains_ssClean)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

private theorem cleanCallSteps_step_props {cls : Nat → Nat} {j : Nat} {s : Step}
    (hj : j < 24) (hs : (cleanCallSteps cls cleanSpqrIdxs)[j]? = some s) :
    s.cls = .party ∧
    ∀ msgIdx, s.decryptMsgIdx? = some msgIdx →
      ∃ h < 10, j = 5 + 2 * h ∧ msgIdx = cleanMsgIdx j := by
  by_cases hj0 : j = 0
  · subst hj0
    have hs0 : s = .aliceStart "alice" "bob" 4 6 bh1 := by injection hs with h; exact h.symm
    subst hs0; exact ⟨rfl, fun _ h => by cases h⟩
  · by_cases hj1 : j = 1
    · subst hj1
      have hs1 : s = .messageEncrypt "alice" 30 (cls 0) 33 := by injection hs with h; exact h.symm
      subst hs1; exact ⟨rfl, fun _ h => by cases h⟩
    · by_cases hj2 : j = 2
      · subst hj2
        have hs2 : s = .messageEncrypt "alice" 36 (cls 1) 40 := by injection hs with h; exact h.symm
        subst hs2; exact ⟨rfl, fun _ h => by cases h⟩
      · by_cases hj3 : j = 3
        · subst hj3
          have hs3 : s = .bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3) := by
            injection hs with h; exact h.symm
          subst hs3; exact ⟨rfl, fun _ h => by cases h⟩
        · by_cases hpar : (j - 4) % 2 = 0
          · obtain ⟨h, hh, rfl⟩ : ∃ h < 10, j = 4 + 2 * h := ⟨(j - 4) / 2, by omega, by omega⟩
            rw [ccs_get_send cls hh] at hs; injection hs with hs; subst hs
            exact ⟨rfl, fun _ h => by cases h⟩
          · obtain ⟨h, hh, rfl⟩ : ∃ h < 10, j = 5 + 2 * h := ⟨(j - 4) / 2, by omega, by omega⟩
            rw [ccs_get_recv cls hh] at hs; injection hs with hs; subst hs
            refine ⟨rfl, fun msgIdx hdec => ?_⟩
            injection hdec with hdec; subst hdec
            refine ⟨h, hh, rfl, ?_⟩
            revert hh
            match h with
            | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => intro _; decide
            | n + 10 => intro hh; omega

private theorem cleanCallSteps_mem_cls_party {cls : Nat → Nat} {s : Step}
    (hmem : s ∈ cleanCallSteps cls cleanSpqrIdxs) : s.cls = .party := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
  have hj24 : j < 24 := by
    rwa [Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs.cleanCallSteps_length] at hj
  exact (cleanCallSteps_step_props hj24 (List.getElem?_eq_getElem hj)).1

private theorem matchesEventsAt_clean_pin {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} :
    ∀ (evsA : List CliEvent) (j₀ : Nat) (ids : Option DY.Libsignal.Composed.Refinement.BundlePreKeyIds)
      (tr : ExecTrace) (ss₁ : List Step) (vis₁ : List VisEntry),
      MatchesEventsAt evictedI0 r S g ids tr ss₁ evsA vis₁ →
      (∀ x ∈ ss₁, x.cls ≠ .invisible) →
      j₀ + evsA.length ≤ 25 →
      (∀ idx < evsA.length, evsA[idx]? = some (.run (ev (j₀ + idx)))) →
      ss₁.length = evsA.length ∧ vis₁ = visOfSteps tr j₀ ss₁
  | [], j₀, _, tr, ss₁, vis₁, hm, hni, _, _ => by
    cases hm with
    | nil hinv =>
      cases ss₁ with
      | nil => exact ⟨rfl, rfl⟩
      | cons x xs => exfalso; exact hni x List.mem_cons_self (hinv x List.mem_cons_self)
  | c :: evsRest, j₀, ids, tr, ss₁, vis₁, hm, hni, hle, hevs => by
    have hc0 := hevs 0 (by simp)
    rw [List.getElem?_cons_zero, Nat.add_zero, Option.some.injEq] at hc0
    subst hc0
    cases hm with
    | run1 hinv hrm hrest =>
      rename_i pre s ss' v vs
      cases pre with
      | cons x xs =>
        exfalso
        exact hni x (by simp) (hinv x List.mem_cons_self)
      | nil =>
        simp only [List.nil_append] at hni ⊢
        have hv_eq := hrm.2.2.2.2.2.2.1
        obtain ⟨hlen_rest, hvis_rest⟩ := matchesEventsAt_clean_pin evsRest (j₀ + 1)
          _ (s.next tr) ss' vs hrest
          (fun x hx => hni x (List.mem_cons_of_mem s hx))
          (by simp only [List.length_cons] at hle; omega)
          (fun idx hidx => by
            have h := hevs (idx + 1) (by simp only [List.length_cons]; omega)
            rwa [List.getElem?_cons_succ, show j₀ + (idx + 1) = j₀ + 1 + idx by omega] at h)
        simp only [List.length_cons, hlen_rest, visOfSteps, hv_eq, hvis_rest]
        exact ⟨trivial, rfl⟩
    | run0 _ hrej _ =>
      exfalso
      exact ev_not_rejected j₀ (by simp only [List.length_cons] at hle; omega) hrej

theorem not_readCollisionCli_ssClean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k : Nat} {cls : Nat → Nat}
    (hWhisper : ∀ (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g' : Ghost)
        (vis' : List VisEntry) (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) (k : Nat),
      evictedCompFitsPinned (evictedI0, evictedHooks0) r →
      ValidCoinLens cls →
      k ∈ whisperOrReplayIndices →
      Explains evictedI0 r S g' (ssClean cls spqrIdxs k) vis' (trace0.take k) →
      ¬ RecvCollisionOn evictedI0 r S g'
          (runTrace r (ssClean cls spqrIdxs k)) vis'
          (honestSaltsOf r (ssClean cls spqrIdxs k))
          (cleanRecvTerm r cls spqrIdxs k))
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls)
    (hk24 : k ≤ 24) :
    ¬ ReadCollisionCli evictedI0 r S (gClean r cls)
        (ssClean cls cleanSpqrIdxs k) (trace0.take k) := by
  rintro ⟨evsA, evJ, evsB, ss₁, ss₂, m, vis₁, msgIdx, _, _, t,
    hevs_eq, hss_eq, _, _, _, hme, hdec, hsent, hcoll⟩
  have htr0_len : trace0.length = 25 := by rw [trace0_eq_cliTrace, trace_eq_evs]; rfl
  have htake_len : (trace0.take k).length = k := by
    rw [List.length_take, htr0_len]; omega
  obtain ⟨j, hj_def⟩ : ∃ j, evsA.length = j := ⟨evsA.length, rfl⟩
  have hj_lt_k : j < k := by
    have := congrArg List.length hevs_eq
    rw [htake_len, List.length_append, List.length_cons, hj_def] at this
    omega
  have hevs_at : ∀ idx < evsA.length, evsA[idx]? = some (.run (ev (0 + idx))) := by
    intro idx hidx
    have h1 : (evsA ++ .run evJ :: evsB)[idx]? = evsA[idx]? := List.getElem?_append_left hidx
    rw [← hevs_eq, List.getElem?_take_of_lt (by omega)] at h1
    rw [Nat.zero_add]
    exact h1.symm.trans (trace0_getElem?_eq_ev (by omega))
  have hni : ∀ x ∈ ss₁, x.cls ≠ .invisible := by
    intro x hx
    have hx_sub : x ∈ ssClean cls cleanSpqrIdxs k := by
      rw [hss_eq]; exact List.mem_append_left _ hx
    have hx_all : x ∈ cleanCallSteps cls cleanSpqrIdxs := List.mem_of_mem_take hx_sub
    rw [cleanCallSteps_mem_cls_party hx_all]; decide
  obtain ⟨hss1_len, hvis1_eq⟩ := matchesEventsAt_clean_pin evsA 0 none (setupTrace r) ss₁ vis₁
    hme hni (by omega) hevs_at
  have hss1_len_j : ss₁.length = j := hss1_len.trans hj_def
  have hss1_eq : ss₁ = ssClean cls cleanSpqrIdxs j := by
    have htake_j := congrArg (List.take j) hss_eq
    rw [ssClean, List.take_take, Nat.min_eq_left (by omega), List.take_left' hss1_len_j] at htake_j
    exact htake_j.symm
  subst hss1_eq
  have hvis1_clean : vis₁ = visClean r cls j := hvis1_eq
  subst hvis1_clean
  have hm_at : (cleanCallSteps cls cleanSpqrIdxs)[j]? = some m := by
    have hat_j := congrArg (fun l => l[j]?) hss_eq
    rw [ssClean, List.getElem?_take_of_lt hj_lt_k,
      List.getElem?_append_right (Nat.le_of_eq hss1_len_j),
      hss1_len_j, Nat.sub_self, List.getElem?_cons_zero] at hat_j
    exact hat_j
  obtain ⟨h, hh, rfl, hmsg_eq⟩ :=
    (cleanCallSteps_step_props (by omega) hm_at).2 msgIdx hdec
  subst hmsg_eq
  have ht_eq : cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h) = t := by
    unfold cleanRecvTerm; rw [hsent]; rfl
  rw [← ht_eq] at hcoll
  exact hWhisper r S (gClean r cls) (visClean r cls (5 + 2 * h)) cls cleanSpqrIdxs (5 + 2 * h)
    hfit d.validCls (hr_mem_whisper hh) (explains_ssClean hfit d hk24 (by omega)) hcoll

private theorem at_of_mem_availableStates {r : ProtocolSetup} {tr : ExecTrace} {st : TRState}
    (hst : st ∈ availableStates r tr) :
    ∃ idx me, tr.at? idx = some (StT me st) := by
  unfold availableStates storedStates DY.ExecTrace.getLocalStateAt at hst
  obtain ⟨ls, hls_mem, rfl⟩ := List.mem_map.mp hst
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hls_mem
  rcases hat : (tr.at? i : Option (DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState TRState))) with _ | e
  · simp [hat] at hi
  · simp only [hat, Option.map_some, Option.some.injEq] at hi
    subst hi
    rcases e with ⟨⟨me, st₀⟩⟩
    exact ⟨i, me, hat⟩

private theorem ratchetKey_mem_of_stored {r : ProtocolSetup} {tr : ExecTrace}
    {msg : TRSignalMsg} {rk : DY.Bytes}
    (hhon : AllRecvChainsHonest tr)
    (hmem : rk ∈ storedRatchetKeys r tr msg) :
    ∃ ts ∈ ratchetKeyTimestamps, rk = dhPk (rnd ts 32) := by
  unfold storedRatchetKeys at hmem
  rcases List.mem_append.mp hmem with hleft | hright
  · obtain ⟨st, hst, hc_map⟩ := List.mem_flatMap.mp hleft
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc_map
    obtain ⟨idx, me, hat⟩ := at_of_mem_availableStates hst
    exact hhon idx me st hat c hc
  · obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hright
    split at hi <;> try cases hi
    split at hi <;> try cases hi
    rename_i hcond
    obtain ⟨st, hst, hfind⟩ := List.any_eq_true.mp hcond.1
    unfold findRecvChain at hfind
    obtain ⟨c, hc, hbeq⟩ := List.find?_isSome.mp hfind
    have hrk_eq : c.ratchetKey = rk := beq_iff_eq.mp hbeq
    obtain ⟨idx, me, hat⟩ := at_of_mem_availableStates hst
    obtain ⟨ts, hts, hc_eq⟩ := hhon idx me st hat c hc
    exact ⟨ts, hts, hrk_eq.symm.trans hc_eq⟩

theorem not_reselectCollisionOn_ssClean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat} {k : Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hv : ValidCoinLens cls)
    (hk : k ∈ whisperOrReplayIndices) :
    ¬ ReselectCollisionOn evictedI0 r S (gClean r cls)
        (runTrace r (ssClean cls cleanSpqrIdxs k)) (visClean r cls k)
        (honestSaltsOf r (ssClean cls cleanSpqrIdxs k))
        (cleanRecvTerm r cls cleanSpqrIdxs k) := by
  rintro ⟨msg, hparse, rk, hrk_mem, hgam, hne, _⟩
  obtain ⟨ts₁, hts₁, hrk₁⟩ :=
    ratchetKey_mem_of_stored (allRecvChainsHonest_ssClean k hfit hv) hrk_mem
  obtain ⟨ts₂, hts₂, hrk₂⟩ : ∃ ts₂ ∈ ratchetKeyTimestamps, msg.ratchetKey = dhPk (rnd ts₂ 32) := by
    by_cases hk24 : k = 24
    · subst hk24
      rw [cleanRecvTerm_24_eq hfit, m1Clean, parse_encMsg] at hparse
      injection hparse with hmsg; subst hmsg
      exact ⟨24, by decide, rfl⟩
    · have hk_wh : k ∈ [5, 7, 9, 11, 13, 15, 17, 19, 21, 23] := by
        simp only [whisperOrReplayIndices, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · exact absurd rfl hk24
      obtain ⟨tsM, htsM, _, _, hrkM⟩ := cleanRecvTerm_whisper_sent hfit hv hk_wh
      exact ⟨tsM, htsM, hrkM msg hparse⟩
  rw [hrk₁, hrk₂] at hgam
  have hts_eq := gamma_ratchetKeyTimestamps_inj hfit hts₁ hts₂ hgam
  subst hts_eq
  exact hne (hrk₁.trans hrk₂.symm)

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunAccept
