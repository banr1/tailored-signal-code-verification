/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVisB
import Symbolic.DYBridge.DY.Bytes.Basic

/-!
# Clean Schedule Ghost Well-Formedness

Proves `ghostWF_visClean`: `GhostWF (gClean r cls) (visClean r cls m)` holds for every prefix length
`m ≤ 24` of the clean schedule.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVisC

open scoped DY.Libsignal.Composed
open DY.Libsignal.TripleRatchet (parseTrSignalMsg)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup Ghost Step VisEntry runTrace stepView rngEntry kyberCoinEntries randTerm
   runWrapped GhostWF)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (parse_encMsg)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (t4 t5 bh1 kh1)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedHooks0 evictedCompFitsPinned evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ValidCoinLens recvCallIndices cleanCallSteps ssClean cleanCallSteps_length)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse (ev)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
  (ev0_coins_facts send_coins_ge_64 send_runWrapped_prekey send_runWrapped_whisper
   active_recv_coins_ge_32)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (cleanSpqrIdxs setupTrace_eq_t4 m1Clean trClean2 m2Clean trClean3 mhClean3
   s0_next_ok s1_next_ok s2_next_ok)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
  (pqAddrBytes gClean gClean_sigma_22 gClean_sigma_23 gClean_sigma_24
   gClean_sigma_32 gClean_sigma_39 gClean_sigma_45
   gClean_sigma_whisper_coins gClean_sigma_whisper_dhs
   gClean_addr_m1 gClean_addr_m2 gClean_addr_whisper)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunPrefix
  (hrTsSend hr_whisper_spec ccs_get_send ccs_get_recv sendCallOf_whisper)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVis
  (visOfSteps visClean visClean_succ stepView_s0 stepView_s1 stepView_s2)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVisB
  (stepView_s3 cleanHalfRound_at)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

/-- Per-step slice of `GhostWF` (excluding the trace-independent `addr` range condition): every
`.rng` draw matches its requested byte length under `g.σ`, and every `.send` entry carries the
expected SPQR wire address under `g.addr`. -/
private def VisStepWF (g : Ghost) (vs : List VisEntry) : Prop :=
  (∀ v ∈ vs, v.kind = .rng → ∀ ts n, n ≠ 0 → randTerm ts n ∈ v.terms → (g.σ ts n).length = n) ∧
  (∀ v ∈ vs, v.kind = .send →
    (v.layout = .preKeySend →
      ∀ ek ct msg pm, v.terms = [ek, ct, msg] → parseTrSignalMsg msg = some pm →
        g.addr pm.wire = pqAddrBytes) ∧
    (v.layout = .whisper →
      ∀ msg pm, v.terms = [msg] → parseTrSignalMsg msg = some pm →
        g.addr pm.wire = []))

private theorem visStepWF_append {g : Ghost} {xs ys : List VisEntry}
    (hx : VisStepWF g xs) (hy : VisStepWF g ys) : VisStepWF g (xs ++ ys) :=
  ⟨fun v hv => by rcases List.mem_append.mp hv with h | h; exacts [hx.1 v h, hy.1 v h],
   fun v hv => by rcases List.mem_append.mp hv with h | h; exacts [hx.2 v h, hy.2 v h]⟩

private theorem randTerm_inj {ts ts' n n' : Nat}
    (heq : randTerm ts n = randTerm ts' n') : ts = ts' ∧ n = n' := by
  have h := Symbolic.DYBridge.DY.BytesView.pack_inj.mp heq
  exact ⟨congrArg DY.Random.Random.timestamp h, congrArg DY.Random.Random.size h⟩

private theorem take_len_eq {α : Type} {xs : List α} {n : Nat} (h : n ≤ xs.length) :
    (xs.take n).length = n :=
  List.length_take_of_le h

private theorem no_rng_or_send_single {g : Ghost} (v₀ : VisEntry)
    (h1 : v₀.kind ≠ .rng) (h2 : v₀.kind ≠ .send) :
    VisStepWF g [v₀] :=
  ⟨fun v hv hk => by simp only [List.mem_singleton] at hv; subst hv; exact absurd hk h1,
   fun v hv hk => by simp only [List.mem_singleton] at hv; subst hv; exact absurd hk h2⟩

private theorem visStepWF_cleanStep {r : ProtocolSetup} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hv : ValidCoinLens cls) :
    ∀ k < 24, ∀ s, (cleanCallSteps cls cleanSpqrIdxs)[k]? = some s →
      VisStepWF (gClean r cls)
        (stepView s (runTrace r (ssClean cls cleanSpqrIdxs k)) (runWrapped (ev k))) := by
  intro k hk s hs
  by_cases hk0 : k = 0
  · subst hk0
    have hs0 : s = .aliceStart "alice" "bob" 4 6 bh1 := by
      injection hs with h; exact h.symm
    subst hs0
    have htr0 : runTrace r (ssClean cls cleanSpqrIdxs 0) = t4 := setupTrace_eq_t4 hfit
    rw [htr0, stepView_s0]
    have hc0 := ev0_coins_facts.1
    refine ⟨?_, ?_⟩
    · intro v hv hkind ts n _ hmem
      simp only [kyberCoinEntries, List.mem_cons, List.mem_append, List.mem_map,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | ⟨j, _, rfl⟩ | rfl
      · cases hkind
      · simp only [rngEntry, List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
        rw [gClean_sigma_22]
        simp only [DY.Libsignal.Composed.Refinement.slice, List.drop_zero]
        exact take_len_eq (by omega)
      · simp only [List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
        rw [gClean_sigma_23]; exact ev0_coins_facts.2.2.2.1
      · simp only [rngEntry, List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
        rw [gClean_sigma_24]
        dsimp only [DY.Libsignal.Composed.Refinement.slice]
        exact take_len_eq (by rw [List.length_drop, hc0])
    · intro v hv hkind
      simp only [kyberCoinEntries, List.mem_cons, List.mem_append, List.mem_map,
        List.not_mem_nil, or_false, rngEntry] at hv
      rcases hv with rfl | rfl | ⟨j, _, rfl⟩ | rfl <;> cases hkind
  · by_cases hk1 : k = 1
    · subst hk1
      have hs1 : s = .messageEncrypt "alice" 30 (cls 0) 33 := by
        injection hs with h; exact h.symm
      subst hs1
      have htr1 : runTrace r (ssClean cls cleanSpqrIdxs 1) = t5 := by
        unfold runTrace; rw [setupTrace_eq_t4 hfit]
        change (Step.aliceStart "alice" "bob" 4 6 bh1).next t4 = t5
        exact (s0_next_ok).1
      rw [htr1, send_runWrapped_prekey.1, stepView_s1]
      have hcl_cases := hv 0 (by decide)
      have hcoins1 : 64 ≤ (ev 1).coins.length := send_coins_ge_64 (s := 0) (by decide)
      refine visStepWF_append
        (no_rng_or_send_single ⟨.pt, [randTerm 31 32], .single, none⟩ (by decide) (by decide)) ?_
      refine visStepWF_append ?_ ?_
      · by_cases hcl0 : cls 0 = 0
        · simp [hcl0, VisStepWF]
        · have hne : (cls 0 != 0) = true := bne_iff_ne.mpr hcl0
          simp only [hne, ↓reduceIte]
          refine ⟨?_, fun v hv hk => by simp [rngEntry] at hv; subst hv; cases hk⟩
          intro v hv _ ts n _ hmem
          simp only [List.mem_singleton] at hv; subst hv
          simp only [rngEntry, List.mem_singleton] at hmem
          obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
          rw [gClean_sigma_32]
          exact take_len_eq (by rcases hcl_cases with h | h | h <;> omega)
      · refine ⟨(fun v hv hk => by simp at hv; subst hv; cases hk), ?_⟩
        intro v hv _
        simp only [List.mem_singleton] at hv; subst hv
        refine ⟨?_, fun hl => by cases hl⟩
        intro _ ek ct msg pm hterms hparse
        simp only [List.cons.injEq, and_true] at hterms
        rcases hterms with ⟨_, _, rfl⟩
        rw [m1Clean, parse_encMsg] at hparse
        injection hparse with hpm; subst hpm
        exact gClean_addr_m1 r cls
    · by_cases hk2 : k = 2
      · subst hk2
        have hs2 : s = .messageEncrypt "alice" 36 (cls 1) 40 := by
          injection hs with h; exact h.symm
        subst hs2
        have htr2 : runTrace r (ssClean cls cleanSpqrIdxs 2) = trClean2 cls := by
          unfold runTrace; rw [setupTrace_eq_t4 hfit]
          change (Step.messageEncrypt "alice" 30 (cls 0) 33).next
            ((Step.aliceStart "alice" "bob" 4 6 bh1).next t4) = trClean2 cls
          rw [(s0_next_ok).1, (s1_next_ok cls).1]
        rw [htr2, send_runWrapped_prekey.2, stepView_s2]
        have hcl_cases := hv 1 (by decide)
        have hcoins2 : 64 ≤ (ev 2).coins.length := send_coins_ge_64 (s := 1) (by decide)
        refine visStepWF_append
          (no_rng_or_send_single ⟨.pt, [randTerm 38 32], .single, none⟩ (by decide) (by decide)) ?_
        refine visStepWF_append ?_ ?_
        · by_cases hcl1 : cls 1 = 0
          · simp [hcl1, VisStepWF]
          · have hne : (cls 1 != 0) = true := bne_iff_ne.mpr hcl1
            simp only [hne, ↓reduceIte]
            refine ⟨?_, fun v hv hk => by simp [rngEntry] at hv; subst hv; cases hk⟩
            intro v hv _ ts n _ hmem
            simp only [List.mem_singleton] at hv; subst hv
            simp only [rngEntry, List.mem_singleton] at hmem
            obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
            rw [gClean_sigma_39]
            exact take_len_eq (by rcases hcl_cases with h | h | h <;> omega)
        · refine ⟨(fun v hv hk => by simp at hv; subst hv; cases hk), ?_⟩
          intro v hv _
          simp only [List.mem_singleton] at hv; subst hv
          refine ⟨?_, fun hl => by cases hl⟩
          intro _ ek ct msg pm hterms hparse
          simp only [List.cons.injEq, and_true] at hterms
          rcases hterms with ⟨_, _, rfl⟩
          rw [m2Clean, parse_encMsg] at hparse
          injection hparse with hpm; subst hpm
          exact gClean_addr_m2 r cls
      · by_cases hk3 : k = 3
        · subst hk3
          have hs3 : s = .bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3) := by
            injection hs with h; exact h.symm
          subst hs3
          have htr3 : runTrace r (ssClean cls cleanSpqrIdxs 3) = trClean3 cls := by
            unfold runTrace; rw [setupTrace_eq_t4 hfit]
            change (Step.messageEncrypt "alice" 36 (cls 1) 40).next
              ((Step.messageEncrypt "alice" 30 (cls 0) 33).next
                ((Step.aliceStart "alice" "bob" 4 6 bh1).next t4)) = trClean3 cls
            rw [(s0_next_ok).1, (s1_next_ok cls).1, (s2_next_ok cls).1]
          rw [htr3, stepView_s3]
          have hcoins3 := active_recv_coins_ge_32 (k := 3) (by decide) (by decide)
          refine ⟨?_, ?_⟩
          · intro v hv hkind ts n _ hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl
            · cases hkind
            · simp only [rngEntry, List.mem_singleton] at hmem
              obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
              rw [gClean_sigma_45]; exact take_len_eq (by omega)
            · cases hkind
          · intro v hv hkind
            simp only [List.mem_cons, List.not_mem_nil, or_false, rngEntry] at hv
            rcases hv with rfl | rfl | rfl <;> cases hkind
        · by_cases hpar : (k - 4) % 2 = 0
          · obtain ⟨h, hh, rfl⟩ : ∃ h < 10, k = 4 + 2 * h := ⟨(k - 4) / 2, by omega, by omega⟩
            obtain ⟨w⟩ := cleanHalfRound_at hfit hv hh
            rw [ccs_get_send cls hh] at hs; injection hs with hs; subst hs
            have hwrap_send : runWrapped (ev (4 + 2 * h)) = false := by
              rw [← sendCallOf_whisper hh]; exact send_runWrapped_whisper (by omega) (by omega)
            rw [hwrap_send, w.view_send]
            have hcl_cases := hv (2 + h) (by omega)
            have hcoinsS : 64 ≤ (ev (4 + 2 * h)).coins.length := by
              have h := send_coins_ge_64 (s := 2 + h) (by omega)
              rwa [sendCallOf_whisper hh] at h
            refine visStepWF_append
              (no_rng_or_send_single ⟨.pt, [randTerm (55 + 14 * h) 32], .single, none⟩
                (by intro h0; cases h0) (by intro h0; cases h0)) ?_
            refine visStepWF_append ?_ ?_
            · by_cases hclH : cls (2 + h) = 0
              · simp [hclH, VisStepWF]
              · have hne : (cls (2 + h) != 0) = true := bne_iff_ne.mpr hclH
                simp only [hne, ↓reduceIte]
                refine ⟨?_, fun v hv hk => by simp [rngEntry] at hv; subst hv; cases hk⟩
                intro v hv _ ts n _ hmem
                simp only [List.mem_singleton] at hv; subst hv
                simp only [rngEntry, List.mem_singleton] at hmem
                obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
                rw [gClean_sigma_whisper_coins r cls hh]
                exact take_len_eq (by rcases hcl_cases with hc | hc | hc <;> omega)
            · refine ⟨(fun v hv hk => by simp at hv; subst hv; cases hk), ?_⟩
              intro v hv _
              simp only [List.mem_singleton] at hv; subst hv
              refine ⟨(fun hl => by cases hl), ?_⟩
              intro _ msg pm hterms hparse
              simp only [List.cons.injEq, and_true] at hterms; subst hterms
              rw [w.term_eq, parse_encMsg] at hparse
              injection hparse with hpm; subst hpm
              have hts_ne24 : hrTsSend h ≠ 24 := by unfold hrTsSend; split <;> omega
              exact gClean_addr_whisper r cls w.inv.dhs_eq.1 hts_ne24
          · obtain ⟨h, hh, rfl⟩ : ∃ h < 10, k = 5 + 2 * h := ⟨(k - 4) / 2, by omega, by omega⟩
            obtain ⟨w⟩ := cleanHalfRound_at hfit hv hh
            rw [ccs_get_recv cls hh] at hs; injection hs with hs; subst hs
            rw [(hr_whisper_spec hh).1, w.view_recv]
            have hmem_recv : 5 + 2 * h ∈ recvCallIndices := by
              match h with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide | n + 10 => omega
            have hcoinsR := active_recv_coins_ge_32 hmem_recv (by omega)
            refine ⟨?_, ?_⟩
            · intro v hv hkind ts n _ hmem
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with rfl | rfl | rfl
              · cases hkind
              · simp only [rngEntry, List.mem_singleton] at hmem
                obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
                rw [gClean_sigma_whisper_dhs r cls hh]
                exact take_len_eq (by omega)
              · cases hkind
            · intro v hv hkind
              simp only [List.mem_cons, List.not_mem_nil, or_false, rngEntry] at hv
              rcases hv with rfl | rfl | rfl <;> cases hkind

theorem ghostWF_visClean {r : ProtocolSetup} {cls : Nat → Nat} (m : Nat)
    (hm : m ≤ 24)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hv : ValidCoinLens cls) :
    GhostWF (gClean r cls) (visClean r cls m) := by
  have hstep : ∀ k ≤ 24, VisStepWF (gClean r cls) (visClean r cls k) := by
    intro k hk
    induction k with
    | zero =>
      unfold visClean ssClean
      simp [visOfSteps, VisStepWF]
    | succ k ih =>
      have hk_lt : k < (cleanCallSteps cls cleanSpqrIdxs).length := by
        rw [cleanCallSteps_length]; omega
      have hs : (cleanCallSteps cls cleanSpqrIdxs)[k]? =
          some (cleanCallSteps cls cleanSpqrIdxs)[k] :=
        List.getElem?_eq_getElem hk_lt
      rw [visClean_succ (by omega) hs]
      exact visStepWF_append (ih (by omega)) (visStepWF_cleanStep hfit hv k (by omega) _ hs)
  have hwf_m := hstep m hm
  refine ⟨hwf_m.1, ?_, hwf_m.2⟩
  intro t
  unfold gClean pqAddrBytes
  dsimp only
  split <;> [exact Or.inr rfl; exact Or.inl rfl]

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVisC
