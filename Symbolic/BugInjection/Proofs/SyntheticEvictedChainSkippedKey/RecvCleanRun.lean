/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunAccept
import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux

/-!
# Clean Prefix Extraction and `.recv` Collision Reduction

Reduces `¬ NextEventCollides` for every `.recv` event in `EvictedChainSkippedKeyCli.trace` to the
two clean-prefix collision-absence obligations (`hBob3` at Call 3 and `hWhisper` at Calls `5..23`
and `24`). Given any outer explanation of `trace0.take k`, extracts a `.network`-free explanation
along `ssClean cls cleanSpqrIdxs k` and discharges the side conditions for Call 3 (prekey start),
Calls `5..23` (honest Whisper delivery), and Call 24 (replayed prekey wrapper refuted by `hnfe` and
`KnownBaseKeyOn`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRun

open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry PreKeyFields parsePreKeyWire
   runTrace honestSaltsOf Explains BobSessionStartCollidesOrImplicitRejectsOn RecvCollisionOn)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse (ev)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (trace0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ValidCoinLens whisperOrReplayIndices ssClean cleanPreKeyRep cleanRecvTerm)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement (KnownBaseKeyOn)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (not_preKeyStartCollidesOrRejects_of_clean not_nextEventCollides_accepted_recv
   not_nextEventCollides_accepted_whisper not_nextEventCollides_accepted_prekey)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux
  (noRecvEvent not_knownBaseKeyOn_of_no_recv)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev3_preKey_fields ev24_preKey_fields)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
  (trace0_take_25 trace0_take_succ split_recv_trace0
   mem_whisperOrReplayIndices_of_recv not_kyberMismatch_ev3)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (cleanSpqrIdxs)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost (gClean)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunPrefix
  (hr_whisper_spec extract_clean_prefix)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVis (visClean)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunExtractA
  (cleanPreKeyRep_mem cleanRecvTerm_mem_whisper cleanRecvTerm_mem_24)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunExtract
  (explains_ssClean accepts_ssClean_whisper)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunAccept
  (not_readCollisionCli_ssClean not_reselectCollisionOn_ssClean)

private theorem no_recv_trace0_take3 : (trace0.take 3).all noRecvEvent = true := by
  decide +kernel

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

private theorem cons_wirePrekeyTag_of_parse {b : DY.Libsignal.HwBytes} {p : PreKeyFields}
    (hp : parsePreKeyWire b = some p) :
    ∃ body, b = wirePrekeyTag :: body := by
  unfold parsePreKeyWire at hp
  split at hp
  · split at hp
    · rename_i tag body htag
      exact ⟨body, by rw [htag]⟩
    · cases hp
  · cases hp

/-- Proves `¬ NextEventCollides` for every `.recv` event in `trace0` from the clean-prefix prekey
(`k = 3`) and Whisper/replay (`k ∈ whisperOrReplayIndices`) collision-absence hypotheses. -/
theorem not_nextEventCollides_recv_of_memo
    (hBob3 : ∀ (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g' : Ghost) (vis' : List VisEntry)
        (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) (p : PreKeyFields),
      evictedCompFitsPinned (evictedI0, evictedHooks0) r →
      ValidCoinLens cls →
      Explains evictedI0 r S g' (ssClean cls spqrIdxs 3) vis' (trace0.take 3) →
      parsePreKeyWire (ev 3).input = some p →
      ¬ BobSessionStartCollidesOrImplicitRejectsOn evictedI0 r S g'
          (runTrace r (ssClean cls spqrIdxs 3)) vis'
          (honestSaltsOf r (ssClean cls spqrIdxs 3)) p
          (cleanPreKeyRep r cls spqrIdxs))
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
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry)
    (evs₁ : List CliEvent) (evCur : RunEvent) (evs₂ : List CliEvent)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hnfe : ∀ g' ss' vis', ¬ Explains evictedI0 r S g' ss' vis' trace0)
    (hsplit : trace0 = evs₁ ++ .run evCur :: evs₂)
    (hex : Explains evictedI0 r S g ss vis evs₁)
    (hrecv : ∃ peer, evCur.cmd = .recv peer) :
    ¬ NextEventCollides evictedI0 r S g ss vis evs₁ evCur := by
  obtain ⟨hk, hevs₁, hevCur⟩ := split_recv_trace0 hsplit hrecv
  rw [hevs₁] at hex ⊢
  rw [hevCur] at hrecv ⊢
  obtain ⟨peer, hcmd⟩ := hrecv
  obtain ⟨cls, d⟩ := extract_clean_prefix hfit hk hex
  by_cases hk3 : evs₁.length = 3
  · rw [hk3] at hex hcmd d ⊢
    obtain ⟨_, p3, hp3, _, _, _⟩ := ev3_preKey_fields
    obtain ⟨body3, hin3⟩ := cons_wirePrekeyTag_of_parse hp3
    have hNotKnown : ¬ KnownBaseKeyOn evictedI0 S g (runTrace r ss) p3 :=
      not_knownBaseKeyOn_of_no_recv hfit.1.1.1 hex no_recv_trace0_take3
    have hexClean3 := explains_ssClean hfit d (by decide) (Nat.le_refl 3)
    have hrep3 := (cleanPreKeyRep_mem hfit d).1
    have hNoBob3 := hBob3 r S (gClean r cls) (visClean r cls 3) cls cleanSpqrIdxs p3
      hfit d.validCls hexClean3 hp3
    have hNoKyber := not_kyberMismatch_ev3 hfit hp3
    rw [hin3] at hp3 hrep3
    exact not_nextEventCollides_accepted_prekey hcmd hin3 hp3 hNotKnown
      (not_preKeyStartCollidesOrRejects_of_clean hNoKyber hexClean3
        (not_readCollisionCli_ssClean hWhisper hfit d (by decide)) hrep3 hNoBob3)
  · have hk_wr := mem_whisperOrReplayIndices_of_recv hk hk3
    by_cases hk24 : evs₁.length = 24
    · rw [hk24] at hex hcmd d ⊢
      obtain ⟨_, p24, hp24, hbk24, _, _, _⟩ := ev24_preKey_fields
      obtain ⟨body24, hin24⟩ := cons_wirePrekeyTag_of_parse hp24
      have hKnown24 : KnownBaseKeyOn evictedI0 S g (runTrace r ss) p24 := by
        obtain ⟨ek, hek, hec⟩ := d.bob_done (by decide)
        exact ⟨ek, hek, hbk24.trans hec.symm⟩
      apply not_nextEventCollides_accepted_recv hcmd hin24
      · intro htag
        have hne : wirePrekeyTag ≠ wireWhisperTag := by decide
        exact absurd htag hne
      · intro p' hp'
        rw [← hin24, hp24] at hp'
        injection hp' with heq
        subst heq
        refine ⟨fun _ => ?_, fun hnkb => absurd hKnown24 hnkb⟩
        rintro ⟨_, hall⟩
        have hexClean24 := explains_ssClean hfit d (Nat.le_refl 24) (Nat.le_refl 24)
        have hNoRead24 := not_readCollisionCli_ssClean hWhisper hfit d (Nat.le_refl 24)
        have ht24 := cleanRecvTerm_mem_24 hfit d hp24
        rcases hall (gClean r cls) (ssClean cls cleanSpqrIdxs 24) (visClean r cls 24)
            hexClean24 hNoRead24 with hallColl | ⟨⟨tAcc, _, hAcc⟩, _⟩
        · rcases hallColl _ ht24 with hrc | hrs
          · exact hWhisper r S (gClean r cls) (visClean r cls 24) cls cleanSpqrIdxs 24
              hfit d.validCls (by decide) hexClean24 hrc
          · exact not_reselectCollisionOn_ssClean hfit d.validCls (by decide) hrs
        · obtain ⟨_, _, _, g₁, vis₁, _, _, _, _, _, hexFull⟩ := hAcc
          rw [← trace0_take_succ (by decide : 24 < 25), trace0_take_25] at hexFull
          exact hnfe g₁ _ vis₁ hexFull
    · obtain ⟨h, hh, hk_eq⟩ : ∃ h < 10, evs₁.length = 5 + 2 * h := by
        simp only [whisperOrReplayIndices, List.mem_cons, List.not_mem_nil, or_false] at hk_wr
        rcases hk_wr with h5 | h7 | h9 | h11 | h13 | h15 | h17 | h19 | h21 | h23 | h24
        · exact ⟨0, by decide, h5⟩
        · exact ⟨1, by decide, h7⟩
        · exact ⟨2, by decide, h9⟩
        · exact ⟨3, by decide, h11⟩
        · exact ⟨4, by decide, h13⟩
        · exact ⟨5, by decide, h15⟩
        · exact ⟨6, by decide, h17⟩
        · exact ⟨7, by decide, h19⟩
        · exact ⟨8, by decide, h21⟩
        · exact ⟨9, by decide, h23⟩
        · exact absurd h24 hk24
      rw [hk_eq] at hex hcmd hk_wr d ⊢
      obtain ⟨body, _, hin, _, _, _⟩ := (hr_whisper_spec hh).2.2
      have hdrop : (ev (5 + 2 * h)).input.drop 1 = body := by rw [hin]; rfl
      have hexClean := explains_ssClean hfit d (by omega) (Nat.le_refl (5 + 2 * h))
      have ht := cleanRecvTerm_mem_whisper hfit d hh (by omega)
      rw [hdrop] at ht
      exact not_nextEventCollides_accepted_whisper hcmd hin hexClean
        (not_readCollisionCli_ssClean hWhisper hfit d (by omega)) ht
        (accepts_ssClean_whisper hfit d hh rfl)
        (hWhisper r S (gClean r cls) (visClean r cls (5 + 2 * h)) cls cleanSpqrIdxs (5 + 2 * h)
          hfit d.validCls hk_wr hexClean)
        (not_reselectCollisionOn_ssClean hfit d.validCls hk_wr)

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRun
