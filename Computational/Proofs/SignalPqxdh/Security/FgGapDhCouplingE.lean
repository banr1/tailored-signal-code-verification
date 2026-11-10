/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingD
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
import VCVio.EvalDist.Monad.Basic

/-!
# Hop 4 (`G3 → G3.5`): Lazy Coupling and Session Partnering

Couples the lazy tagged `KeyInd` runs up to `lazyStop` and relates equal `drKeyReal.rootKey` tags
to `keyIndPartner` under session and key-store invariants.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk

namespace Proofs.SignalPqxdh.Security

theorem relCoupled_testSession_setLazyView {S : Setup}
    (lst5 lst6 : KeyIndLazyState S) (adv' : KeyIndAdvCutoffState S)
    (kReal kRand : Bytes) (mkResp : DRKey → KeyIndResponse)
    (hAg : LazyTagCacheAgree lst5 lst6)
    (hRo5Eq : ∀ k, ro5KeyInView adv' k = ro5KeyInView lst5.adv k)
    (hPairNew : testedPairInView adv' kReal kRand = true)
    (hPairMono : ∀ r d, testedPairInView lst5.adv r d = true → testedPairInView adv' r d = true)
    (hPairSplit : lazyStop adv' = false → ∀ r d, testedPairInView adv' r d = true →
      testedPairInView lst5.adv r d = true ∨ (r = kReal ∧ d = kRand)) :
    RelCoupled
      (fun y5 y6 =>
        (y5.1 = y6.1 ∧ LazyTagCacheAgree y5.2 y6.2) ∨
        (lazyStop y5.2.adv = true ∧ lazyStop y6.2.adv = true))
      (runLazyPost false false S (.evalRand kRand mkResp) (setLazyView adv' lst5))
      (runLazyPost false false S (.evalRo kReal mkResp) (setLazyView adv' lst6)) := by
  by_cases hStop : lazyStop adv' = true
  · refine RelCoupled.of_support _ _ (fun y5 hy5 y6 hy6 => Or.inr ⟨?_, ?_⟩)
    · rw [lazyStop_runLazyPost_false_false _ _ hy5]
      exact hStop
    · rw [lazyStop_runLazyPost_false_false _ _ hy6]
      exact hStop
  · have hStopF : lazyStop adv' = false := Bool.eq_false_iff.mpr hStop
    have hRealNotRo5' : ro5KeyInView adv' kReal = false := by
      cases h : ro5KeyInView adv' kReal
      · rfl
      · have hT := not_testedRealKeyInView_of_lazyStop_false_of_ro5KeyInView adv' kReal hStopF h
        have hT2 := testedRealKeyInView_of_testedPairInView adv' kReal kRand hPairNew
        rw [hT] at hT2; nomatch hT2
    have hRealNotRo5 : ro5KeyInView lst5.adv kReal = false := by
      rw [← hRo5Eq kReal]; exact hRealNotRo5'
    rcases hAg with ⟨_, hRo5None, hRo6None, hRoEq, hRandNone, hPairEq⟩
    have hLookEq : lookupCache lst5.randCache kRand =
        lookupCache lst6.adv.shCr.base.roCache kReal := by
      cases hTR : testedRealKeyInView lst5.adv kReal
      · have hTRand : testedRandKeyInView lst5.adv kRand = false := by
          cases hRd : testedRandKeyInView lst5.adv kRand
          · rfl
          · rcases exists_testedPairInView_of_testedRandKeyInView lst5.adv kRand hRd with ⟨r0, hr0⟩
            have hr0' := hPairMono r0 kRand hr0
            have hBeq := testedPair_beq_eq_of_lazyStop_false adv' r0 kRand kReal kRand hStopF hr0'
              hPairNew
            simp only [beq_self_eq_true, beq_iff_eq] at hBeq
            subst hBeq
            have hT0 := testedRealKeyInView_of_testedPairInView lst5.adv r0 kRand hr0
            rw [hTR] at hT0; nomatch hT0
        rw [hRandNone kRand hTRand, hRo6None kReal hRealNotRo5 hTR]
      · rcases exists_testedPairInView_of_testedRealKeyInView lst5.adv kReal hTR with ⟨d0, hd0⟩
        have hd0' := hPairMono kReal d0 hd0
        have hBeq := testedPair_beq_eq_of_lazyStop_false adv' kReal d0 kReal kRand hStopF hd0'
          hPairNew
        simp only [beq_self_eq_true] at hBeq
        have hd0Eq : d0 = kRand := beq_iff_eq.mp hBeq.symm
        subst hd0Eq
        exact hPairEq kReal d0 hd0
    unfold runLazyPost CacheLens.eval
    simp only [randLens, roLens, setLazyView, roCache_withAdvRoCache, bind_assoc, pure_bind]
    refine (relCoupled_evalCache_of_lookup_eq
      lst5.randCache lst6.adv.shCr.base.roCache kRand kReal hLookEq).bind ?_
    intro p1 p2 ⟨hDk, hEqNew, hRestRand, hRestRo⟩
    rcases p1 with ⟨dk1, rand5'⟩
    rcases p2 with ⟨dk2, ro6'⟩
    dsimp only at hDk hEqNew hRestRand hRestRo
    subst hDk
    have hTestRealMono : ∀ q, testedRealKeyInView adv' q = false → testedRealKeyInView lst5.adv q =
      false := by
      intro q hF
      cases h : testedRealKeyInView lst5.adv q
      · rfl
      · rcases exists_testedPairInView_of_testedRealKeyInView lst5.adv q h with ⟨d, hd⟩
        have hT := testedRealKeyInView_of_testedPairInView adv' q d (hPairMono q d hd)
        rw [hF] at hT; nomatch hT
    have hTestRandMono : ∀ q, testedRandKeyInView adv' q = false → testedRandKeyInView lst5.adv q =
      false := by
      intro q hF
      cases h : testedRandKeyInView lst5.adv q
      · rfl
      · rcases exists_testedPairInView_of_testedRandKeyInView lst5.adv q h with ⟨r, hr⟩
        have hT := testedRandKeyInView_of_testedPairInView adv' r q (hPairMono r q hr)
        rw [hF] at hT; nomatch hT
    refine RelCoupled.of_pure (Or.inl ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩)
    · intro q hF
      simp only [ro5KeyInView_withAdvRoCache, hRo5Eq q] at hF
      simp only [roCache_withAdvRoCache]
      exact hRo5None q hF
    · intro q hF hTF
      simp only [ro5KeyInView_withAdvRoCache, hRo5Eq q] at hF
      simp only [testedRealKeyInView_withAdvRoCache] at hTF
      simp only [roCache_withAdvRoCache]
      have hne : (kReal == q) = false := by
        cases h : kReal == q
        · rfl
        · have hEqQ : kReal = q := beq_iff_eq.mp h
          subst hEqQ
          have hT := testedRealKeyInView_of_testedPairInView adv' kReal kRand hPairNew
          rw [hTF] at hT; nomatch hT
      rw [hRestRo q hne]
      exact hRo6None q hF (hTestRealMono q hTF)
    · intro q hTF
      simp only [testedRealKeyInView_withAdvRoCache] at hTF
      simp only [roCache_withAdvRoCache]
      have hne : (kReal == q) = false := by
        cases h : kReal == q
        · rfl
        · have hEqQ : kReal = q := beq_iff_eq.mp h
          subst hEqQ
          have hT := testedRealKeyInView_of_testedPairInView adv' kReal kRand hPairNew
          rw [hTF] at hT; nomatch hT
      rw [hRestRo q hne]
      exact hRoEq q (hTestRealMono q hTF)
    · intro q hRF
      simp only [testedRandKeyInView_withAdvRoCache] at hRF
      have hne : (kRand == q) = false := by
        cases h : kRand == q
        · rfl
        · have hEqQ : kRand = q := beq_iff_eq.mp h
          subst hEqQ
          have hT := testedRandKeyInView_of_testedPairInView adv' kReal kRand hPairNew
          rw [hRF] at hT; nomatch hT
      rw [hRestRand q hne]
      exact hRandNone q (hTestRandMono q hRF)
    · intro r d hPT
      simp only [testedPairInView_withAdvRoCache] at hPT
      simp only [roCache_withAdvRoCache]
      have hBeq := testedPair_beq_eq_of_lazyStop_false adv' kReal kRand r d hStopF hPairNew hPT
      by_cases hR : (kReal == r) = true
      · have hD : (kRand == d) = true := hBeq.symm.trans hR
        have hrEq : kReal = r := beq_iff_eq.mp hR
        have hdEq : kRand = d := beq_iff_eq.mp hD
        subst hrEq; subst hdEq
        exact hEqNew
      · have hneR : (kReal == r) = false := Bool.eq_false_iff.mpr hR
        have hneD : (kRand == d) = false := hBeq.symm.trans hneR
        rw [hRestRand d hneD, hRestRo r hneR]
        rcases hPairSplit hStopF r d hPT with hOld | ⟨rfl, _⟩
        · exact hPairEq r d hOld
        · simp at hneR

/-- Monotone extension on `KeyIndAdvCutoffState S`: `advRoLog`, `sessions`, and `respSessions`
    only grow, and `tested`/`revealed` only flip from `false` to `true`, preserving `drKeyReal`,
    `drKeyRand`, `fresh`, `senderHonest`, and `sid`. -/
def ViewExtends {S : Setup} (adv adv' : KeyIndAdvCutoffState S) : Prop :=
  (∀ sec, adv.advRoLog.contains sec = true → adv'.advRoLog.contains sec = true) ∧
  (∀ s ∈ adv.shCr.base.sessions, ∃ s' ∈ adv'.shCr.base.sessions,
    s'.sid = s.sid ∧ s'.drKeyReal = s.drKeyReal ∧ s'.drKeyRand = s.drKeyRand ∧ s'.fresh = s.fresh ∧
    (s.tested = true → s'.tested = true) ∧ (s.revealed = true → s'.revealed = true)) ∧
  (∀ r ∈ adv.shCr.base.respSessions, ∃ r' ∈ adv'.shCr.base.respSessions,
    r'.sid = r.sid ∧ r'.drKeyReal = r.drKeyReal ∧ r'.drKeyRand = r.drKeyRand ∧ r'.senderHonest =
      r.senderHonest ∧
    (r.tested = true → r'.tested = true) ∧ (r.revealed = true → r'.revealed = true))

theorem ViewExtends.refl {S : Setup} (adv : KeyIndAdvCutoffState S) : ViewExtends adv adv :=
  ⟨fun _ h => h,
   fun s hs => ⟨s, hs, rfl, rfl, rfl, rfl, id, id⟩,
   fun r hr => ⟨r, hr, rfl, rfl, rfl, rfl, id, id⟩⟩

theorem ViewExtends.of_eq_lists {S : Setup} (adv adv' : KeyIndAdvCutoffState S)
    (hLog : adv'.advRoLog = adv.advRoLog)
    (hSess : adv'.shCr.base.sessions = adv.shCr.base.sessions)
    (hResp : adv'.shCr.base.respSessions = adv.shCr.base.respSessions) :
    ViewExtends adv adv' := by
  refine ⟨fun sec h => by rw [hLog]; exact h,
    fun s hs => ⟨s, by rw [hSess]; exact hs, rfl, rfl, rfl, rfl, id, id⟩,
    fun r hr => ⟨r, by rw [hResp]; exact hr, rfl, rfl, rfl, rfl, id, id⟩⟩

theorem ro5KeyInView_mono_of_viewExtends {S : Setup} {adv adv' : KeyIndAdvCutoffState S}
    (hExt : ViewExtends adv adv') (sec : Bytes)
    (h : ro5KeyInView adv sec = true) :
    ro5KeyInView adv' sec = true := by
  rcases hExt with ⟨hLog, hSess, hResp⟩
  unfold ro5KeyInView at h ⊢
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with (hL | ⟨s, hs, hFR, hKey⟩) | ⟨r, hr, hSR, hKey⟩
  · exact Or.inl (Or.inl (hLog sec hL))
  · rcases hSess s hs with ⟨s', hs', _, hReal, _, hFresh, _, hRev⟩
    refine Or.inl (Or.inr ⟨s', hs', ?_, by rw [hReal]; exact hKey⟩)
    rcases hFR with hNF | hR
    · left; rw [hFresh]; exact hNF
    · right; exact hRev hR
  · rcases hResp r hr with ⟨r', hr', _, hReal, _, hHon, _, hRev⟩
    refine Or.inr ⟨r', hr', ?_, by rw [hReal]; exact hKey⟩
    rcases hSR with hNH | hR
    · left; rw [hHon]; exact hNH
    · right; exact hRev hR

theorem testedPairInView_mono_of_viewExtends {S : Setup} {adv adv' : KeyIndAdvCutoffState S}
    (hExt : ViewExtends adv adv') (kReal kRand : Bytes)
    (h : testedPairInView adv kReal kRand = true) :
    testedPairInView adv' kReal kRand = true := by
  rcases hExt with ⟨_, hSess, hResp⟩
  unfold testedPairInView at h ⊢
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with ⟨s, hs, ⟨ht, hR⟩, hRd⟩ | ⟨r, hr, ⟨ht, hR⟩, hRd⟩
  · rcases hSess s hs with ⟨s', hs', _, hReal, hRand, _, hTest, _⟩
    exact Or.inl ⟨s', hs', ⟨hTest ht, by rw [hReal]; exact hR⟩, by rw [hRand]; exact hRd⟩
  · rcases hResp r hr with ⟨r', hr', _, hReal, hRand, _, hTest, _⟩
    exact Or.inr ⟨r', hr', ⟨hTest ht, by rw [hReal]; exact hR⟩, by rw [hRand]; exact hRd⟩

theorem lazyStop_mono_of_viewExtends {S : Setup} {adv adv' : KeyIndAdvCutoffState S}
    (hExt : ViewExtends adv adv')
    (h : lazyStop adv = true) :
    lazyStop adv' = true := by
  have hRo5 := ro5KeyInView_mono_of_viewExtends hExt
  rcases hExt with ⟨_, hSess, hResp⟩
  unfold lazyStop at h ⊢
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with ((⟨s, hs, ht, hR5⟩ | ⟨r, hr, ht, hR5⟩) | ⟨s1, hs1, ht1, hS2⟩) | ⟨r1, hr1, ht1, r2,
    hr2, ht2, hCond⟩
  · rcases hSess s hs with ⟨s', hs', _, hReal, _, _, hTest, _⟩
    exact Or.inl (Or.inl (Or.inl ⟨s', hs', hTest ht, by rw [hReal]; exact hRo5 _ hR5⟩))
  · rcases hResp r hr with ⟨r', hr', _, hReal, _, _, hTest, _⟩
    exact Or.inl (Or.inl (Or.inr ⟨r', hr', hTest ht, by rw [hReal]; exact hRo5 _ hR5⟩))
  · rcases hSess s1 hs1 with ⟨s1', hs1', hSid1, hReal1, hRand1, _, hTest1, _⟩
    refine Or.inl (Or.inr ⟨s1', hs1', hTest1 ht1, ?_⟩)
    rcases hS2 with ⟨s2, hs2, ht2, hCond⟩ | ⟨r2, hr2, ht2, hCond⟩
    · rcases hSess s2 hs2 with ⟨s2', hs2', hSid2, hReal2, hRand2, _, hTest2, _⟩
      exact Or.inl ⟨s2', hs2', hTest2 ht2,
        by rw [hSid1, hSid2, hReal1, hReal2, hRand1, hRand2]; exact hCond⟩
    · rcases hResp r2 hr2 with ⟨r2', hr2', _, hReal2, hRand2, _, hTest2, _⟩
      exact Or.inr ⟨r2', hr2', hTest2 ht2, by rw [hReal1, hReal2, hRand1, hRand2]; exact hCond⟩
  · rcases hResp r1 hr1 with ⟨r1', hr1', hSid1, hReal1, hRand1, _, hTest1, _⟩
    rcases hResp r2 hr2 with ⟨r2', hr2', hSid2, hReal2, hRand2, _, hTest2, _⟩
    exact Or.inr ⟨r1', hr1', hTest1 ht1, r2', hr2', hTest2 ht2,
      by rw [hSid1, hSid2, hReal1, hReal2, hRand1, hRand2]; exact hCond⟩

/-- Unified postcondition for every non-`testSession` query in `tagStepView`:
    simultaneously implies `ViewExtends adv adv'` (hence `lazyStop` monotonicity) and
    `RelCoupled` step preservation of `LazyTagCacheAgree` up to `lazyStop`. -/
def ValidNonTestTagStep {S : Setup} (adv : KeyIndAdvCutoffState S)
    (post : LazyPost) (adv' : KeyIndAdvCutoffState S) : Prop :=
  ViewExtends adv adv' ∧
  (∀ k, testedRealKeyInView adv' k = testedRealKeyInView adv k) ∧
  (∀ kRand, testedRandKeyInView adv' kRand = testedRandKeyInView adv kRand) ∧
  (∀ r d, testedPairInView adv' r d = testedPairInView adv r d) ∧
  ((∃ resp, post = .done resp) ∨
   (∃ freshResp unfreshResp secrets pid?, post = .handshake true freshResp unfreshResp secrets pid?)
     ∨
   (∃ sec mkResp, post = .evalRo sec mkResp ∧ ro5KeyInView adv' sec = true) ∨
   (∃ freshResp unfreshResp sec pid?, post = .handshake false freshResp unfreshResp sec pid? ∧
     ro5KeyInView adv' sec = true))

theorem runLazyPost_false_false_handshake_true {S : Setup}
    (freshResp : KeyIndResponse) (unfreshResp : DRKey → KeyIndResponse)
    (secrets : Bytes) (pid? : Option Bytes) (lst : KeyIndLazyState S) :
    runLazyPost false false S (.handshake true freshResp unfreshResp secrets pid?) lst =
      pure (freshResp, lst) := by
  cases pid? <;> rfl

theorem runLazyPost_false_false_handshake_false {S : Setup}
    (freshResp : KeyIndResponse) (unfreshResp : DRKey → KeyIndResponse)
    (secrets : Bytes) (pid? : Option Bytes) (lst : KeyIndLazyState S) :
    runLazyPost false false S (.handshake false freshResp unfreshResp secrets pid?) lst =
      runLazyPost false false S (.evalRo secrets unfreshResp) lst := by
  cases pid? <;> rfl

theorem relCoupled_runLazyPost_of_validNonTestTagStep {S : Setup}
    (lst5 lst6 : KeyIndLazyState S) (post : LazyPost) (adv' : KeyIndAdvCutoffState S)
    (hAg : LazyTagCacheAgree lst5 lst6)
    (hStep : ValidNonTestTagStep (getLazyView lst5) post adv') :
    RelCoupled
      (fun y5 y6 =>
        (y5.1 = y6.1 ∧ LazyTagCacheAgree y5.2 y6.2) ∨
        (lazyStop y5.2.adv = true ∧ lazyStop y6.2.adv = true))
      (runLazyPost false false S post (setLazyView adv' lst5))
      (runLazyPost false false S post (setLazyView adv' lst6)) := by
  rcases hStep with ⟨hExt, hTR, hTRd, hTP, hPost⟩
  have hRo5Mono : ∀ sec, ro5KeyInView lst5.adv sec = true → ro5KeyInView adv' sec = true :=
    fun sec h => ro5KeyInView_mono_of_viewExtends hExt sec h
  have hTR' : ∀ k, testedRealKeyInView adv' k = testedRealKeyInView lst5.adv k := hTR
  have hTRd' : ∀ kRand, testedRandKeyInView adv' kRand = testedRandKeyInView lst5.adv kRand := hTRd
  have hTP' : ∀ r d, testedPairInView adv' r d = testedPairInView lst5.adv r d := hTP
  rcases hPost with ⟨resp, rfl⟩ | ⟨freshResp, unfreshResp, secrets, pid?, rfl⟩ |
    ⟨sec, mkResp, rfl, hSecIn⟩ | ⟨freshResp, unfreshResp, sec, pid?, rfl, hSecIn⟩
  · exact RelCoupled.of_pure (Or.inl ⟨rfl,
      lazyTagCacheAgree_setLazyView_of_noCache lst5 lst6 adv' hAg hRo5Mono hTR' hTRd' hTP'⟩)
  · rw [runLazyPost_false_false_handshake_true, runLazyPost_false_false_handshake_true]
    exact RelCoupled.of_pure (Or.inl ⟨rfl,
      lazyTagCacheAgree_setLazyView_of_noCache lst5 lst6 adv' hAg hRo5Mono hTR' hTRd' hTP'⟩)
  · exact relCoupled_evalRo_setLazyView lst5 lst6 adv' sec mkResp hAg hSecIn hRo5Mono hTR' hTRd'
      hTP'
  · rw [runLazyPost_false_false_handshake_false, runLazyPost_false_false_handshake_false]
    exact relCoupled_evalRo_setLazyView lst5 lst6 adv' sec unfreshResp hAg hSecIn hRo5Mono hTR'
      hTRd' hTP'

theorem ValidNonTestTagStep.of_eq_lists {S : Setup}
    (adv adv' : KeyIndAdvCutoffState S) (resp : KeyIndResponse)
    (hLog : adv'.advRoLog = adv.advRoLog)
    (hSess : adv'.shCr.base.sessions = adv.shCr.base.sessions)
    (hResp : adv'.shCr.base.respSessions = adv.shCr.base.respSessions) :
    ValidNonTestTagStep adv (.done resp) adv' := by
  refine ⟨ViewExtends.of_eq_lists adv adv' hLog hSess hResp, ?_, ?_, ?_, Or.inl ⟨resp, rfl⟩⟩
  · intro k; unfold testedRealKeyInView; rw [hSess, hResp]
  · intro kRand; unfold testedRandKeyInView; rw [hSess, hResp]
  · intro r d; unfold testedPairInView; rw [hSess, hResp]

theorem ValidNonTestTagStep.refl_done {S : Setup}
    (adv : KeyIndAdvCutoffState S) (resp : KeyIndResponse) :
    ValidNonTestTagStep adv (.done resp) adv :=
  ValidNonTestTagStep.of_eq_lists adv adv resp rfl rfl rfl

theorem ValidNonTestTagStep.of_roQuery {S : Setup}
    (adv : KeyIndAdvCutoffState S) (sec : Bytes) :
    ValidNonTestTagStep adv (.evalRo sec KeyIndResponse.drKeyResp)
      { adv with advRoLog := sec :: adv.advRoLog } := by
  refine ⟨⟨?_, fun s hs => ⟨s, hs, rfl, rfl, rfl, rfl, id, id⟩,
    fun r hr => ⟨r, hr, rfl, rfl, rfl, rfl, id, id⟩⟩,
    fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
    Or.inr (Or.inr (Or.inl ⟨sec, KeyIndResponse.drKeyResp, rfl, ?_⟩))⟩
  · intro k hk; simp only [List.contains_cons, hk, Bool.or_true]
  · unfold ro5KeyInView; simp

theorem ValidNonTestTagStep.of_cons_session {S : Setup}
    (adv adv' : KeyIndAdvCutoffState S)
    (isHonest : Bool) (freshResp : KeyIndResponse)
    (unfreshResp : DRKey → KeyIndResponse) (secrets : Bytes) (pid? : Option Bytes)
    (e0 : KeyIndInitiatorEntry S)
    (hLog : adv'.advRoLog = adv.advRoLog)
    (hSess : adv'.shCr.base.sessions = e0 :: adv.shCr.base.sessions)
    (hResp : adv'.shCr.base.respSessions = adv.shCr.base.respSessions)
    (hTestF : e0.tested = false)
    (hKey : e0.drKeyReal.rootKey = secrets)
    (hHonFresh : isHonest = false → e0.fresh = false) :
    ValidNonTestTagStep adv (.handshake isHonest freshResp unfreshResp secrets pid?) adv' := by
  have hExt : ViewExtends adv adv' :=
    ⟨fun sec h => by rw [hLog]; exact h,
     fun s hs => ⟨s, by rw [hSess]; exact List.mem_cons_of_mem _ hs, rfl, rfl, rfl, rfl, id, id⟩,
     fun r hr => ⟨r, by rw [hResp]; exact hr, rfl, rfl, rfl, rfl, id, id⟩⟩
  refine ⟨hExt, ?_, ?_, ?_, ?_⟩
  · intro k; unfold testedRealKeyInView; rw [hSess, hResp]; simp [hTestF]
  · intro kRand; unfold testedRandKeyInView; rw [hSess, hResp]; simp [hTestF]
  · intro r d; unfold testedPairInView; rw [hSess, hResp]; simp [hTestF]
  · cases isHonest
    · refine Or.inr (Or.inr (Or.inr ⟨freshResp, unfreshResp, secrets, pid?, rfl, ?_⟩))
      have hFr : e0.fresh = false := hHonFresh rfl
      unfold ro5KeyInView
      rw [hSess]
      simp [hFr, hKey]
    · exact Or.inr (Or.inl ⟨freshResp, unfreshResp, secrets, pid?, rfl⟩)

theorem ValidNonTestTagStep.of_cons_respSession {S : Setup}
    (adv adv' : KeyIndAdvCutoffState S)
    (senderHonest : Bool) (freshResp : KeyIndResponse)
    (unfreshResp : DRKey → KeyIndResponse) (secrets : Bytes) (pid? : Option Bytes)
    (r0 : KeyIndRespEntry S)
    (hLog : adv'.advRoLog = adv.advRoLog)
    (hSess : adv'.shCr.base.sessions = adv.shCr.base.sessions)
    (hResp : adv'.shCr.base.respSessions = r0 :: adv.shCr.base.respSessions)
    (hTestF : r0.tested = false)
    (hKey : r0.drKeyReal.rootKey = secrets)
    (hHon : r0.senderHonest = senderHonest) :
    ValidNonTestTagStep adv (.handshake senderHonest freshResp unfreshResp secrets pid?) adv' := by
  have hExt : ViewExtends adv adv' :=
    ⟨fun sec h => by rw [hLog]; exact h,
     fun s hs => ⟨s, by rw [hSess]; exact hs, rfl, rfl, rfl, rfl, id, id⟩,
     fun r hr => ⟨r, by rw [hResp]; exact List.mem_cons_of_mem _ hr, rfl, rfl, rfl, rfl, id, id⟩⟩
  refine ⟨hExt, ?_, ?_, ?_, ?_⟩
  · intro k; unfold testedRealKeyInView; rw [hSess, hResp]; simp [hTestF]
  · intro kRand; unfold testedRandKeyInView; rw [hSess, hResp]; simp [hTestF]
  · intro r d; unfold testedPairInView; rw [hSess, hResp]; simp [hTestF]
  · cases senderHonest
    · refine Or.inr (Or.inr (Or.inr ⟨freshResp, unfreshResp, secrets, pid?, rfl, ?_⟩))
      unfold ro5KeyInView
      rw [hResp]
      simp [hHon, hKey]
    · exact Or.inr (Or.inl ⟨freshResp, unfreshResp, secrets, pid?, rfl⟩)

theorem ValidNonTestTagStep.of_revealSession {S : Setup}
    (adv : KeyIndAdvCutoffState S) (sid : SessionId S) (e : KeyIndInitiatorEntry S)
    (he : e ∈ adv.shCr.base.sessions) (hSid : (e.sid == sid) = true) :
    let sessions' := adv.shCr.base.sessions.map (fun s =>
      if s.sid == sid then { s with revealed := true } else s)
    let adv' := { adv with shCr :=
      { adv.shCr with base := { adv.shCr.base with sessions := sessions' } } }
    ValidNonTestTagStep adv (.evalRo e.drKeyReal.rootKey KeyIndResponse.drKeyResp) adv' := by
  intro sessions' adv'
  have hExt : ViewExtends adv adv' := by
    refine ⟨fun _ h => h, ?_, fun r hr => ⟨r, hr, rfl, rfl, rfl, rfl, id, id⟩⟩
    intro s hs
    refine ⟨if s.sid == sid then { s with revealed := true } else s,
      List.mem_map_of_mem hs, ?_⟩
    cases s.sid == sid <;> simp
  have hMapEq : ∀ (f : KeyIndInitiatorEntry S → Bool)
      (hf : ∀ s, f { s with revealed := true } = f s),
      sessions'.any f = adv.shCr.base.sessions.any f := by
    intro f hf
    dsimp only [sessions']
    rw [List.any_map]
    congr 1; funext s
    dsimp only [Function.comp_apply]
    cases s.sid == sid <;> simp [hf]
  refine ⟨hExt, ?_, ?_, ?_, Or.inr (Or.inr (Or.inl ⟨e.drKeyReal.rootKey, KeyIndResponse.drKeyResp,
    rfl, ?_⟩))⟩
  · intro k; unfold testedRealKeyInView; dsimp only [adv']
    rw [hMapEq _ (fun _ => rfl)]
  · intro kRand; unfold testedRandKeyInView; dsimp only [adv']
    rw [hMapEq _ (fun _ => rfl)]
  · intro r d; unfold testedPairInView; dsimp only [adv']
    rw [hMapEq _ (fun _ => rfl)]
  · unfold ro5KeyInView; dsimp only [adv']
    simp only [Bool.or_eq_true, List.any_eq_true]
    refine Or.inl (Or.inr ⟨if e.sid == sid then { e with revealed := true } else e,
      List.mem_map_of_mem he, ?_⟩)
    simp [hSid]

theorem ValidNonTestTagStep.of_revealRespSession {S : Setup}
    (adv : KeyIndAdvCutoffState S) (sid : SessionId S) (r : KeyIndRespEntry S)
    (hr : r ∈ adv.shCr.base.respSessions) (hSid : (r.sid == sid) = true) :
    let resp' := adv.shCr.base.respSessions.map (fun x =>
      if x.sid == sid then { x with revealed := true } else x)
    let adv' := { adv with shCr :=
      { adv.shCr with base := { adv.shCr.base with respSessions := resp' } } }
    ValidNonTestTagStep adv (.evalRo r.drKeyReal.rootKey KeyIndResponse.drKeyResp) adv' := by
  intro resp' adv'
  have hExt : ViewExtends adv adv' := by
    refine ⟨fun _ h => h, fun s hs => ⟨s, hs, rfl, rfl, rfl, rfl, id, id⟩, ?_⟩
    intro x hx
    refine ⟨if x.sid == sid then { x with revealed := true } else x,
      List.mem_map_of_mem hx, ?_⟩
    cases x.sid == sid <;> simp
  have hMapEq : ∀ (f : KeyIndRespEntry S → Bool)
      (hf : ∀ x, f { x with revealed := true } = f x),
      resp'.any f = adv.shCr.base.respSessions.any f := by
    intro f hf
    dsimp only [resp']
    rw [List.any_map]
    congr 1; funext x
    dsimp only [Function.comp_apply]
    cases x.sid == sid <;> simp [hf]
  refine ⟨hExt, ?_, ?_, ?_, Or.inr (Or.inr (Or.inl ⟨r.drKeyReal.rootKey, KeyIndResponse.drKeyResp,
    rfl, ?_⟩))⟩
  · intro k; unfold testedRealKeyInView; dsimp only [adv']
    rw [hMapEq _ (fun _ => rfl)]
  · intro kRand; unfold testedRandKeyInView; dsimp only [adv']
    rw [hMapEq _ (fun _ => rfl)]
  · intro r0 d; unfold testedPairInView; dsimp only [adv']
    rw [hMapEq _ (fun _ => rfl)]
  · unfold ro5KeyInView; dsimp only [adv']
    simp only [Bool.or_eq_true, List.any_eq_true]
    refine Or.inr ⟨if r.sid == sid then { r with revealed := true } else r,
      List.mem_map_of_mem hr, ?_⟩
    simp [hSid]

theorem isHonestUncorruptedPeer_isSome_eq_false_of_findHonestPrincipal_isSome_eq_false
    (P : Primitives) (principals : List (Nat × PrincipalEntry)) (ikB : Bytes)
    (h : (findHonestPrincipal P principals ikB).isSome = false) :
    (isHonestUncorruptedPeer P principals ikB).isSome = false := by
  unfold isHonestUncorruptedPeer
  cases hF : findHonestPrincipal P principals ikB with
  | none => rfl
  | some p => rw [hF] at h; nomatch h

theorem validNonTestTagStep_of_tagStepInitiate {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (adv : KeyIndAdvCutoffState S)
    {y : LazyPost × KeyIndAdvCutoffState S}
    (hy : y ∈ support (tagStepInitiate S P sid u bundle adv)) :
    ValidNonTestTagStep adv y.1 y.2 := by
  unfold tagStepInitiate at hy
  dsimp only at hy
  cases hPre : preCheckKeyInd S P sid u bundle adv.shCr.base with
  | none =>
    rw [hPre] at hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ValidNonTestTagStep.refl_done adv .noneResp
  | some uEntry =>
    rw [hPre] at hy
    simp only [MonadAttach.mem_support_bind] at hy
    rcases hy with ⟨ekASk, _, kemCoins, _, hy⟩
    by_cases hSig : (!checkBundleSigs P adv.shCr.base.principals bundle) = true
    · simp only [hSig, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ValidNonTestTagStep.refl_done adv .noneResp
    · simp only [hSig, Bool.false_eq_true, ↓reduceIte] at hy
      cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
      | none =>
        rw [hKem] at hy
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact ValidNonTestTagStep.of_eq_lists adv _ .noneResp rfl rfl rfl
      | some p =>
        rcases p with ⟨ss, kemCt⟩
        rw [hKem] at hy
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact ValidNonTestTagStep.of_cons_session adv _ _ _ _ _ _ _
          rfl rfl rfl rfl rfl
          (isHonestUncorruptedPeer_isSome_eq_false_of_findHonestPrincipal_isSome_eq_false
            P adv.shCr.base.principals bundle.ikB)

theorem validNonTestTagStep_of_tagStepAcceptOPK {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (adv : KeyIndAdvCutoffState S)
    {y : LazyPost × KeyIndAdvCutoffState S}
    (hy : y ∈ support (tagStepAcceptOPK S P k j o hdr adv)) :
    ValidNonTestTagStep adv y.1 y.2 := by
  unfold tagStepAcceptOPK at hy
  dsimp only at hy
  split_ifs at hy
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact ValidNonTestTagStep.refl_done adv .noneResp
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact ValidNonTestTagStep.refl_done adv .noneResp
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact ValidNonTestTagStep.refl_done adv .noneResp
  · rcases hK : adv.shCr.base.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
    · rw [hK] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact ValidNonTestTagStep.refl_done adv .noneResp
    · rw [hK] at hy; dsimp only at hy
      rcases hB : adv.shCr.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ |
        ⟨_, bEntry⟩
      · rw [hB] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
        exact ValidNonTestTagStep.refl_done adv .noneResp
      · rw [hB] at hy; dsimp only at hy
        rcases hO : adv.shCr.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
          with _ | ⟨_, oEntry⟩
        · rw [hO] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
          exact ValidNonTestTagStep.refl_done adv .noneResp
        · rw [hO] at hy; dsimp only at hy
          split_ifs at hy
          · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
            exact ValidNonTestTagStep.refl_done adv .noneResp
          · rcases hAcc : Model.acceptKeys P _ with _ | accOut
            · rw [hAcc] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
              exact ValidNonTestTagStep.refl_done adv .noneResp
            · rw [hAcc] at hy; dsimp only at hy
              rcases hDec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss
              · rw [hDec] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
                exact ValidNonTestTagStep.refl_done adv .noneResp
              · rw [hDec] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
                exact ValidNonTestTagStep.of_cons_respSession adv _ _ _ _ _ _ _
                  rfl rfl rfl rfl rfl rfl

theorem validNonTestTagStep_of_tagStepAcceptNoOPK {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
    (adv : KeyIndAdvCutoffState S)
    {y : LazyPost × KeyIndAdvCutoffState S}
    (hy : y ∈ support (tagStepAcceptNoOPK S P k j l hdr adv)) :
    ValidNonTestTagStep adv y.1 y.2 := by
  unfold tagStepAcceptNoOPK at hy
  dsimp only at hy
  split_ifs at hy
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact ValidNonTestTagStep.refl_done adv .noneResp
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact ValidNonTestTagStep.refl_done adv .noneResp
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact ValidNonTestTagStep.refl_done adv .noneResp
  · rcases hK : adv.shCr.base.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
    · rw [hK] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact ValidNonTestTagStep.refl_done adv .noneResp
    · rw [hK] at hy; dsimp only at hy
      rcases hB : adv.shCr.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ |
        ⟨_, bEntry⟩
      · rw [hB] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
        exact ValidNonTestTagStep.refl_done adv .noneResp
      · rw [hB] at hy; dsimp only at hy
        rcases hAcc : Model.acceptKeys P _ with _ | accOut
        · rw [hAcc] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
          exact ValidNonTestTagStep.refl_done adv .noneResp
        · rw [hAcc] at hy; dsimp only at hy
          rcases hDec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss
          · rw [hDec] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
            exact ValidNonTestTagStep.refl_done adv .noneResp
          · rw [hDec] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
            exact ValidNonTestTagStep.of_cons_respSession adv _ _ _ _ _ _ _
              rfl rfl rfl rfl rfl rfl

theorem validNonTestTagStep_of_tagStepRevealSessionKey {S : Setup}
    (sid : SessionId S) (adv : KeyIndAdvCutoffState S)
    {y : LazyPost × KeyIndAdvCutoffState S}
    (hy : y ∈ support (tagStepRevealSessionKey S sid adv)) :
    ValidNonTestTagStep adv y.1 y.2 := by
  unfold tagStepRevealSessionKey at hy
  dsimp only at hy
  cases hFindS : adv.shCr.base.sessions.find? (fun e => e.sid == sid) with
  | some e =>
    rw [hFindS] at hy
    by_cases hT : e.tested = true
    · simp only [hT, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact ValidNonTestTagStep.refl_done adv .noneResp
    · simp only [hT, Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ValidNonTestTagStep.of_revealSession adv sid e
        (List.mem_of_find?_eq_some hFindS)
        (List.find?_some (p := fun e : KeyIndInitiatorEntry S => e.sid == sid) hFindS)
  | none =>
    rw [hFindS] at hy
    cases hFindR : adv.shCr.base.respSessions.find? (fun r => r.sid == sid) with
    | none =>
      rw [hFindR] at hy
      simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact ValidNonTestTagStep.refl_done adv .noneResp
    | some r =>
      rw [hFindR] at hy
      by_cases hT : r.tested = true
      · simp only [hT, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy; subst hy
        exact ValidNonTestTagStep.refl_done adv .noneResp
      · simp only [hT, Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact ValidNonTestTagStep.of_revealRespSession adv sid r
          (List.mem_of_find?_eq_some hFindR)
          (List.find?_some (p := fun r : KeyIndRespEntry S => r.sid == sid) hFindR)

theorem eq_lists_of_pqxdhKeyIndImpl_simple {S : Setup} (P : Primitives)
    (q : KeyIndQuery S)
    (hSimple : (∃ u, q = .initPrin u) ∨ (∃ u, q = .corruptIK u) ∨
               (∃ u j o, q = .genOPK u j o) ∨ q = .revealDhSecrets ∨ (∃ sk, q = .registerKey sk) ∨
               (∃ u j, q = .revealSpkSk u j))
    (st : KeyIndState S)
    {y : KeyIndResponse × KeyIndState S}
    (hy : y ∈ support ((pqxdhKeyIndImpl true S P q).run st)) :
    y.2.sessions = st.sessions ∧ y.2.respSessions = st.respSessions := by
  let proj := fun s : KeyIndState S => (s.sessions, s.respSessions)
  have hp : PreservesAt proj st (pqxdhKeyIndImpl true S P q) := by
    rcases hSimple with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, j, o, rfl⟩ | rfl | ⟨sk, rfl⟩ | ⟨u, j, rfl⟩ <;>
    · unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | split)
  have hEq := hp y hy
  exact ⟨congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩

theorem validNonTestTagStep_of_genSPK {S : Setup} (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv)
    (adv : KeyIndAdvCutoffState S)
    {y : LazyPost × KeyIndAdvCutoffState S}
    (hy : y ∈ support (do
      let (r, adv') ← (pqxdhKeyIndAdvG3Impl S P (.genSPK u j)).run adv
      return (.done r, adv'))) :
    ValidNonTestTagStep adv y.1 y.2 := by
  have hRun : (pqxdhKeyIndAdvG3Impl S P (.genSPK u j)).run adv =
      (do
        let (r, base') ← (genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
          (fun st bs =>
            { st with spkBundles := bs }) KeyIndResponse.noneResp KeyIndResponse.bundleResp
          u j).run adv.shCr.base
        return (r, { adv with shCr := { adv.shCr with base := base' } })) := by
    simp [pqxdhKeyIndAdvG3Impl, liftKeyIndAdvShCr, pqxdhKeyIndShCrImpl,
      runKeyIndShCrGenSPK, runShCrGenSPKGeneric, liftShCrBase, StateT.run]; rfl
  rw [hRun] at hy
  simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hy
  rcases hy with ⟨⟨r, base'⟩, hBase, rfl⟩
  rcases mem_support_genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
    (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp KeyIndResponse.bundleResp
    u j adv.shCr.base (r, base') hBase with
    hEq | ⟨uEntry, spkSk, rSpk, pqspkPk, pqspkSk, rPq, hFresh, hEq⟩
  · cases hEq
    exact ValidNonTestTagStep.of_eq_lists adv _ _ rfl rfl rfl
  · cases hEq
    exact ValidNonTestTagStep.of_eq_lists adv _ _ rfl rfl rfl

theorem validNonTestTagStep_of_simple {S : Setup} (P : Primitives)
    (q : KeyIndQuery S)
    (hSimple : (∃ u, q = .initPrin u) ∨ (∃ u, q = .corruptIK u) ∨
               (∃ u j o, q = .genOPK u j o) ∨ q = .revealDhSecrets ∨ (∃ sk, q = .registerKey sk) ∨
               (∃ u j, q = .revealSpkSk u j))
    (adv : KeyIndAdvCutoffState S)
    {y : LazyPost × KeyIndAdvCutoffState S}
    (hy : y ∈ support (do
      let (r, adv') ← (pqxdhKeyIndAdvG3Impl S P q).run adv
      return (.done r, adv'))) :
    ValidNonTestTagStep adv y.1 y.2 := by
  have hRun : (pqxdhKeyIndAdvG3Impl S P q).run adv =
      (do
        let (r, base') ← (pqxdhKeyIndImpl true S P q).run adv.shCr.base
        return (r, { adv with shCr := { adv.shCr with base := base' } })) := by
    rcases hSimple with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, j, o, rfl⟩ | rfl | ⟨sk, rfl⟩ | ⟨u, j, rfl⟩ <;>
      (simp [pqxdhKeyIndAdvG3Impl, liftKeyIndAdvShCr, pqxdhKeyIndShCrImpl,
        liftKeyIndShCrBase, liftShCrBase, StateT.run]; rfl)
  rw [hRun] at hy
  simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hy
  rcases hy with ⟨⟨r, base'⟩, hBase, rfl⟩
  have ⟨hSess, hResp⟩ := eq_lists_of_pqxdhKeyIndImpl_simple P q hSimple adv.shCr.base hBase
  exact ValidNonTestTagStep.of_eq_lists adv _ r rfl hSess hResp

theorem validNonTestTagStep_of_tagStepView {S : Setup} (testReal : Bool) (P : Primitives)
    (q : KeyIndQuery S) (hNeTest : ∀ sid, q ≠ .testSession sid)
    (adv : KeyIndAdvCutoffState S)
    {y : LazyPost × KeyIndAdvCutoffState S}
    (hy : y ∈ support (tagStepView testReal S P q adv)) :
    ValidNonTestTagStep adv y.1 y.2 := by
  cases q with
  | testSession sid => exact False.elim (hNeTest sid rfl)
  | initiateOPK u i bundle =>
    dsimp only [tagStepView] at hy
    split_ifs at hy
    · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact ValidNonTestTagStep.refl_done adv .noneResp
    · exact validNonTestTagStep_of_tagStepInitiate P (.sendOPK u i) u bundle adv hy
  | initiateNoOPK u i bundle =>
    dsimp only [tagStepView] at hy
    split_ifs at hy
    · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact ValidNonTestTagStep.refl_done adv .noneResp
    · exact validNonTestTagStep_of_tagStepInitiate P (.sendNoOPK u i) u bundle adv hy
  | acceptOPK k j o hdr =>
    exact validNonTestTagStep_of_tagStepAcceptOPK P k j o hdr adv hy
  | acceptNoOPK k j l hdr =>
    exact validNonTestTagStep_of_tagStepAcceptNoOPK P k j l hdr adv hy
  | revealSessionKey sid =>
    exact validNonTestTagStep_of_tagStepRevealSessionKey sid adv hy
  | roQuery sec =>
    dsimp only [tagStepView] at hy
    simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact ValidNonTestTagStep.of_roQuery adv sec
  | initPrin u =>
    exact validNonTestTagStep_of_simple P (.initPrin u) (Or.inl ⟨u, rfl⟩) adv hy
  | corruptIK u =>
    exact validNonTestTagStep_of_simple P (.corruptIK u) (Or.inr (Or.inl ⟨u, rfl⟩)) adv hy
  | genSPK u j =>
    exact validNonTestTagStep_of_genSPK P u j adv hy
  | genOPK u j o =>
    exact validNonTestTagStep_of_simple P (.genOPK u j o) (Or.inr (Or.inr (Or.inl ⟨u, j, o, rfl⟩)))
      adv hy
  | revealDhSecrets =>
    exact validNonTestTagStep_of_simple P .revealDhSecrets (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      adv hy
  | registerKey sk =>
    exact validNonTestTagStep_of_simple P (.registerKey sk) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨sk, rfl⟩))))) adv hy
  | revealSpkSk u j =>
    exact validNonTestTagStep_of_simple P (.revealSpkSk u j) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨u, j, rfl⟩))))) adv hy

theorem viewExtends_of_tagStepTestSession {S : Setup} (testReal : Bool)
    (sid : SessionId S) (adv : KeyIndAdvCutoffState S)
    {y : LazyPost × KeyIndAdvCutoffState S}
    (hy : y ∈ support (tagStepTestSession testReal S sid adv)) :
    ViewExtends adv y.2 := by
  unfold tagStepTestSession at hy
  dsimp only at hy
  by_cases hFresh : (!isKeyIndSessionTestable adv.shCr.base sid) = true
  · simp only [hFresh, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact ViewExtends.refl adv
  · simp only [hFresh, Bool.false_eq_true, ↓reduceIte] at hy
    cases hFindS : adv.shCr.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      rw [hFindS] at hy
      cases testReal <;>
      · simp only [↓reduceIte, Bool.false_eq_true, support_pure, Set.mem_singleton_iff] at hy
        subst hy
        refine ⟨fun _ h => h, ?_, fun r hr => ⟨r, hr, rfl, rfl, rfl, rfl, id, id⟩⟩
        intro s hs
        refine ⟨if s.sid == sid then { s with tested := true } else s,
          List.mem_map_of_mem hs, ?_⟩
        cases s.sid == sid <;> simp
    | none =>
      rw [hFindS] at hy
      cases hFindR : adv.shCr.base.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        rw [hFindR] at hy
        simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
        exact ViewExtends.refl adv
      | some r =>
        rw [hFindR] at hy
        cases testReal <;>
        · simp only [↓reduceIte, Bool.false_eq_true, support_pure, Set.mem_singleton_iff] at hy
          subst hy
          refine ⟨fun _ h => h, fun s hs => ⟨s, hs, rfl, rfl, rfl, rfl, id, id⟩, ?_⟩
          intro x hx
          refine ⟨if x.sid == sid then { x with tested := true } else x,
            List.mem_map_of_mem hx, ?_⟩
          cases x.sid == sid <;> simp

theorem viewExtends_of_tagStepView {S : Setup} (testReal : Bool) (P : Primitives)
    (q : KeyIndQuery S) (adv : KeyIndAdvCutoffState S)
    {y : LazyPost × KeyIndAdvCutoffState S}
    (hy : y ∈ support (tagStepView testReal S P q adv)) :
    ViewExtends adv y.2 := by
  by_cases hTest : ∃ sid, q = .testSession sid
  · rcases hTest with ⟨sid, rfl⟩
    exact viewExtends_of_tagStepTestSession testReal sid adv hy
  · exact (validNonTestTagStep_of_tagStepView testReal P q
      (fun sid hEq => hTest ⟨sid, hEq⟩) adv hy).1

theorem lazyStop_mono_pqxdhKeyIndAdvTagImpl_false_false {S : Setup}
    (testReal : Bool) (P : Primitives) (q : KeyIndQuery S) (lst : KeyIndLazyState S)
    (hStop : lazyStop lst.adv = true)
    {y : KeyIndResponse × KeyIndLazyState S}
    (hy : y ∈ support ((pqxdhKeyIndAdvTagImpl false false testReal S P q).run lst)) :
    lazyStop y.2.adv = true := by
  dsimp only [pqxdhKeyIndAdvTagImpl, mkLazyKeyIndImpl, liftTagView, StateT.run_mk] at hy
  simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨⟨post, adv'⟩, hStep, hRun⟩
  rw [lazyStop_runLazyPost_false_false post (setLazyView adv' lst) hRun]
  have hExt := viewExtends_of_tagStepView testReal P q (getLazyView lst) hStep
  have hStopView : lazyStop (getLazyView lst) = true := by
    simpa [getLazyView] using hStop
  simpa [setLazyView] using lazyStop_mono_of_viewExtends hExt hStopView

theorem tagStepView_eq_of_ne_testSession {S : Setup} (P : Primitives)
    (q : KeyIndQuery S) (hNeTest : ∀ sid, q ≠ .testSession sid)
    (adv : KeyIndAdvCutoffState S) :
    tagStepView false S P q adv = tagStepView true S P q adv := by
  cases q with
  | testSession sid => exact False.elim (hNeTest sid rfl)
  | _ => rfl

theorem relCoupled_tagStepTestSession {S : Setup} (P : Primitives) (sid : SessionId S)
    (lst5 lst6 : KeyIndLazyState S) (hAg : LazyTagCacheAgree lst5 lst6) :
    RelCoupled
      (fun y5 y6 =>
        (y5.1 = y6.1 ∧ LazyTagCacheAgree y5.2 y6.2) ∨
        (lazyStop y5.2.adv = true ∧ lazyStop y6.2.adv = true))
      ((pqxdhKeyIndAdvTagImpl false false false S P (.testSession sid)).run lst5)
      ((pqxdhKeyIndAdvTagImpl false false true S P (.testSession sid)).run lst6) := by
  dsimp only [pqxdhKeyIndAdvTagImpl, mkLazyKeyIndImpl, liftTagView, tagStepView, StateT.run_mk]
  simp only [bind_assoc, pure_bind]
  rw [← hAg.1]
  set v := getLazyView lst5
  unfold tagStepTestSession
  dsimp only
  by_cases hFresh : (!isKeyIndSessionTestable v.shCr.base sid) = true
  · simp only [hFresh, ↓reduceIte, pure_bind, runLazyPost]
    refine RelCoupled.of_pure ?_
    exact Or.inl ⟨rfl, lazyTagCacheAgree_setLazyView_of_noCache lst5 lst6 v hAg
      (fun _ h => h) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)⟩
  · simp only [hFresh, Bool.false_eq_true, ↓reduceIte]
    cases hFindS : v.shCr.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      simp only [pure_bind]
      let sessions' := v.shCr.base.sessions.map (fun s =>
        if s.sid == sid then { s with tested := true } else s)
      let adv' : KeyIndAdvCutoffState S := { v with shCr := { v.shCr with base :=
        { v.shCr.base with sessions := sessions' } } }
      have heMem : e ∈ lst5.adv.shCr.base.sessions := List.mem_of_find?_eq_some hFindS
      have heSid : (e.sid == sid) = true :=
        List.find?_some (p := fun e : KeyIndInitiatorEntry S => e.sid == sid) hFindS
      have he'Mem : { e with tested := true } ∈ sessions' := by
        have h := List.mem_map_of_mem (f := fun s : KeyIndInitiatorEntry S =>
          if s.sid == sid then { s with tested := true } else s) heMem
        simp only [heSid, ↓reduceIte] at h
        exact h
      have hRo5Eq : ∀ k, ro5KeyInView adv' k = ro5KeyInView lst5.adv k := by
        intro k
        unfold ro5KeyInView
        dsimp only [adv', sessions', v, getLazyView, withAdvRoCache, withShCrRoCache,
          withBaseRoCache]
        rw [List.any_map]
        congr 2; congr 1; funext s
        dsimp only [Function.comp_apply]
        cases s.sid == sid <;> rfl
      have hPairNew : testedPairInView adv' e.drKeyReal.rootKey e.drKeyRand.rootKey = true := by
        unfold testedPairInView; dsimp only [adv']
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inl ⟨{ e with tested := true }, he'Mem, by simp⟩
      have hExt : ViewExtends lst5.adv adv' := by
        refine ⟨fun _ h => h, ?_, fun r hr => ⟨r, hr, rfl, rfl, rfl, rfl, id, id⟩⟩
        intro s hs
        refine ⟨if s.sid == sid then { s with tested := true } else s,
          List.mem_map_of_mem hs, ?_⟩
        cases s.sid == sid <;> simp
      have hPairMono : ∀ r d, testedPairInView lst5.adv r d = true → testedPairInView adv' r d =
        true :=
        testedPairInView_mono_of_viewExtends hExt
      have hPairSplit : lazyStop adv' = false → ∀ r d, testedPairInView adv' r d = true →
          testedPairInView lst5.adv r d = true ∨ (r = e.drKeyReal.rootKey ∧ d = e.drKeyRand.rootKey)
            := by
        intro hStopF r d hPT
        unfold testedPairInView at hPT; dsimp only [adv'] at hPT
        simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hPT
        rcases hPT with ⟨s', hs', ⟨ht', rfl⟩, rfl⟩ | ⟨r', hr', ⟨ht', rfl⟩, rfl⟩
        · rw [List.mem_map] at hs'
          rcases hs' with ⟨s, hs, hEqS⟩
          by_cases hSidS : (s.sid == sid) = true
          · simp only [hSidS, ↓reduceIte] at hEqS
            subst hEqS
            have hs'Mem : { s with tested := true } ∈ adv'.shCr.base.sessions := by
              have h := List.mem_map_of_mem (f := fun x : KeyIndInitiatorEntry S =>
                if x.sid == sid then { x with tested := true } else x) hs
              simp only [hSidS, ↓reduceIte] at h
              exact h
            have hSidEq : ({ s with tested := true } : KeyIndInitiatorEntry S).sid =
                ({ e with tested := true } : KeyIndInitiatorEntry S).sid :=
              (beq_iff_eq.mp hSidS).trans (beq_iff_eq.mp heSid).symm
            exact Or.inr (tested_same_sid_keys_eq_of_lazyStop_false_sessions adv'
              { s with tested := true } { e with tested := true } hStopF
              hs'Mem rfl he'Mem rfl hSidEq)
          · simp only [hSidS, Bool.false_eq_true, ↓reduceIte] at hEqS
            subst hEqS
            left
            unfold testedPairInView
            simp only [Bool.or_eq_true, List.any_eq_true]
            exact Or.inl ⟨s, hs, by simp [ht']⟩
        · left
          unfold testedPairInView
          simp only [Bool.or_eq_true, List.any_eq_true]
          exact Or.inr ⟨r', hr', by simp [ht']⟩
      exact relCoupled_testSession_setLazyView lst5 lst6 adv'
        e.drKeyReal.rootKey e.drKeyRand.rootKey KeyIndResponse.drKeyResp
        hAg hRo5Eq hPairNew hPairMono hPairSplit
    | none =>
      cases hFindR : v.shCr.base.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        simp only [pure_bind, runLazyPost]
        refine RelCoupled.of_pure ?_
        exact Or.inl ⟨rfl, lazyTagCacheAgree_setLazyView_of_noCache lst5 lst6 v hAg
          (fun _ h => h) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)⟩
      | some r =>
        simp only [pure_bind]
        let resp' := v.shCr.base.respSessions.map (fun x =>
          if x.sid == sid then { x with tested := true } else x)
        let adv' : KeyIndAdvCutoffState S := { v with shCr := { v.shCr with base :=
          { v.shCr.base with respSessions := resp' } } }
        have hrMem : r ∈ lst5.adv.shCr.base.respSessions := List.mem_of_find?_eq_some hFindR
        have hrSid : (r.sid == sid) = true :=
          List.find?_some (p := fun r : KeyIndRespEntry S => r.sid == sid) hFindR
        have hr'Mem : { r with tested := true } ∈ resp' := by
          have h := List.mem_map_of_mem (f := fun x : KeyIndRespEntry S =>
            if x.sid == sid then { x with tested := true } else x) hrMem
          simp only [hrSid, ↓reduceIte] at h
          exact h
        have hRo5Eq : ∀ k, ro5KeyInView adv' k = ro5KeyInView lst5.adv k := by
          intro k
          unfold ro5KeyInView
          dsimp only [adv', resp', v, getLazyView, withAdvRoCache, withShCrRoCache, withBaseRoCache]
          rw [List.any_map]
          congr 2; funext x
          dsimp only [Function.comp_apply]
          cases x.sid == sid <;> rfl
        have hPairNew : testedPairInView adv' r.drKeyReal.rootKey r.drKeyRand.rootKey = true := by
          unfold testedPairInView; dsimp only [adv']
          simp only [Bool.or_eq_true, List.any_eq_true]
          exact Or.inr ⟨{ r with tested := true }, hr'Mem, by simp⟩
        have hExt : ViewExtends lst5.adv adv' := by
          refine ⟨fun _ h => h, fun s hs => ⟨s, hs, rfl, rfl, rfl, rfl, id, id⟩, ?_⟩
          intro x hx
          refine ⟨if x.sid == sid then { x with tested := true } else x,
            List.mem_map_of_mem hx, ?_⟩
          cases x.sid == sid <;> simp
        have hPairMono : ∀ r0 d0, testedPairInView lst5.adv r0 d0 = true → testedPairInView adv' r0
          d0 = true :=
          testedPairInView_mono_of_viewExtends hExt
        have hPairSplit : lazyStop adv' = false → ∀ r0 d0, testedPairInView adv' r0 d0 = true →
            testedPairInView lst5.adv r0 d0 = true ∨ (r0 = r.drKeyReal.rootKey ∧ d0 =
              r.drKeyRand.rootKey) := by
          intro hStopF r0 d0 hPT
          unfold testedPairInView at hPT; dsimp only [adv'] at hPT
          simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hPT
          rcases hPT with ⟨s', hs', ⟨ht', rfl⟩, rfl⟩ | ⟨x', hx', ⟨ht', rfl⟩, rfl⟩
          · left
            unfold testedPairInView
            simp only [Bool.or_eq_true, List.any_eq_true]
            exact Or.inl ⟨s', hs', by simp [ht']⟩
          · rw [List.mem_map] at hx'
            rcases hx' with ⟨x, hx, hEqX⟩
            by_cases hSidX : (x.sid == sid) = true
            · simp only [hSidX, ↓reduceIte] at hEqX
              subst hEqX
              have hx'Mem : { x with tested := true } ∈ adv'.shCr.base.respSessions := by
                have h := List.mem_map_of_mem (f := fun y : KeyIndRespEntry S =>
                  if y.sid == sid then { y with tested := true } else y) hx
                simp only [hSidX, ↓reduceIte] at h
                exact h
              have hSidEq : ({ x with tested := true } : KeyIndRespEntry S).sid =
                  ({ r with tested := true } : KeyIndRespEntry S).sid :=
                (beq_iff_eq.mp hSidX).trans (beq_iff_eq.mp hrSid).symm
              exact Or.inr (tested_same_sid_keys_eq_of_lazyStop_false_respSessions adv'
                { x with tested := true } { r with tested := true } hStopF
                hx'Mem rfl hr'Mem rfl hSidEq)
            · simp only [hSidX, Bool.false_eq_true, ↓reduceIte] at hEqX
              subst hEqX
              left
              unfold testedPairInView
              simp only [Bool.or_eq_true, List.any_eq_true]
              exact Or.inr ⟨x, hx, by simp [ht']⟩
        exact relCoupled_testSession_setLazyView lst5 lst6 adv'
          r.drKeyReal.rootKey r.drKeyRand.rootKey KeyIndResponse.drKeyResp
          hAg hRo5Eq hPairNew hPairMono hPairSplit

theorem relCoupled_pqxdhKeyIndAdvTagImpl_false_false_step {S : Setup} (P : Primitives)
    (q : KeyIndQuery S) (lst5 lst6 : KeyIndLazyState S)
    (hAg : LazyTagCacheAgree lst5 lst6) :
    RelCoupled
      (fun y5 y6 =>
        (y5.1 = y6.1 ∧ LazyTagCacheAgree y5.2 y6.2) ∨
        (lazyStop y5.2.adv = true ∧ lazyStop y6.2.adv = true))
      ((pqxdhKeyIndAdvTagImpl false false false S P q).run lst5)
      ((pqxdhKeyIndAdvTagImpl false false true S P q).run lst6) := by
  by_cases hTest : ∃ sid, q = .testSession sid
  · rcases hTest with ⟨sid, rfl⟩
    exact relCoupled_tagStepTestSession P sid lst5 lst6 hAg
  · have hNeTest : ∀ sid, q ≠ .testSession sid := fun sid hEq => hTest ⟨sid, hEq⟩
    dsimp only [pqxdhKeyIndAdvTagImpl, mkLazyKeyIndImpl, liftTagView, StateT.run_mk]
    simp only [bind_assoc, pure_bind]
    rw [← hAg.1, ← tagStepView_eq_of_ne_testSession P q hNeTest (getLazyView lst5)]
    refine RelCoupled.bind_same (tagStepView false S P q (getLazyView lst5)) ?_
    rintro ⟨post, adv'⟩ hy
    have hStepView := validNonTestTagStep_of_tagStepView false P q hNeTest (getLazyView lst5) hy
    exact relCoupled_runLazyPost_of_validNonTestTagStep lst5 lst6 post adv' hAg hStepView

open Proofs.SignalPqxdh.Security.FgGapDh

theorem eq_of_isCanonical_of_pow8_eq (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    {pk1 pk2 : Bytes} (hc1 : P.isCanonical pk1 = true) (hc2 : P.isCanonical pk2 = true)
    (hpow : P.pow8 pk1 = P.pow8 pk2) :
    pk1 = pk2 :=
  hP.toWellFormedPrimitivesδ.canon_pow8_inj pk1 pk2 hc1 hc2 hpow

theorem x25519_comm_of_pow8_eq (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (a sk pk : Bytes) (hpow : P.pow8 pk = P.pow8 (P.x25519Base sk)) :
    P.x25519 a pk = P.x25519 sk (P.x25519Base a) := by
  rw [hP.x25519_pow8_congr a pk (P.x25519Base sk)
        (hP.pow8_base_len pk sk hpow) (hP.x25519Base_len sk) hpow,
      hP.toWellFormedPrimitivesδ.x25519_comm a sk]

theorem nodup_of_hasDuplicateBytes_eq_false :
    ∀ (L : List Bytes), hasDuplicateBytes L = false → L.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [hasDuplicateBytes, Bool.or_eq_false_iff] at h
    have hNotMem : x ∉ xs := fun hMem => by
      have hc : xs.contains x = true := List.contains_iff_mem.mpr hMem
      rw [h.1] at hc
      nomatch hc
    exact List.nodup_cons.mpr ⟨hNotMem, nodup_of_hasDuplicateBytes_eq_false xs h.2⟩

theorem eq_of_nodup_map {α β : Type} (f : α → β) {L : List α}
    (hNodup : (L.map f).Nodup) {a b : α} (ha : a ∈ L) (hb : b ∈ L) (hEq : f a = f b) :
    a = b := by
  induction L with
  | nil => nomatch ha
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hNodup
    rcases List.mem_cons.mp ha with rfl | ha' <;>
      rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exfalso; exact hNodup.1 (hEq ▸ List.mem_map_of_mem hb')
    · exfalso; exact hNodup.1 (hEq.symm ▸ List.mem_map_of_mem ha')
    · exact ih hNodup.2 ha' hb'

theorem nodup_spkBundles_of_hasEcPkCollisionKeyInd_false {S : Setup} (P : Primitives)
    (st : KeyIndState S) (hNoEc : hasEcPkCollisionKeyInd P st = false) :
    (st.spkBundles.map (fun (_, b) => P.pow8 b.spkPk)).Nodup := by
  have hNodup := nodup_of_hasDuplicateBytes_eq_false (allHonestEcPksKeyInd P st)
    (Bool.or_eq_false_iff.mp hNoEc).1
  unfold allHonestEcPksKeyInd HasKeyIndState.toKeyIndState instHasKeyIndStateKeyIndState at hNodup
  dsimp only at hNodup
  exact (((List.nodup_append.mp hNodup).1 |> List.nodup_append.mp).1 |> List.nodup_append.mp).2.1

theorem nodup_sessions_of_hasEcPkCollisionKeyInd_false {S : Setup} (P : Primitives)
    (st : KeyIndState S) (hNoEc : hasEcPkCollisionKeyInd P st = false) :
    (st.sessions.map (fun s => P.pow8 s.hdr.ekAPk)).Nodup := by
  have hNodup := nodup_of_hasDuplicateBytes_eq_false (allHonestEcPksKeyInd P st)
    (Bool.or_eq_false_iff.mp hNoEc).1
  unfold allHonestEcPksKeyInd HasKeyIndState.toKeyIndState instHasKeyIndStateKeyIndState at hNodup
  dsimp only at hNodup
  exact (List.nodup_append.mp hNodup).2.1

theorem nodup_spkBundles_of_hasKemPkCollisionKeyInd_false {S : Setup}
    (st : KeyIndState S) (hNoKem : hasKemPkCollisionKeyInd st = false) :
    (st.spkBundles.map (fun (_, b) => b.pqspkPk)).Nodup :=
  nodup_of_hasDuplicateBytes_eq_false (allHonestKemPksKeyInd st) hNoKem

theorem eq_kemCt_and_pqspkPk_of_hasBadKemShCrRecords_false {S : Setup} (P : Primitives)
    (initRecs : List (_root_.Proofs.SignalPqxdh.Security.InitKemRecord S))
    (recvRecs : List _root_.Proofs.SignalPqxdh.Security.RecvKemRecord)
    (hNoBad : hasBadKemShCrRecords S P initRecs recvRecs = false)
    {i : _root_.Proofs.SignalPqxdh.Security.InitKemRecord S}
    {r : _root_.Proofs.SignalPqxdh.Security.RecvKemRecord}
    (hi : i ∈ initRecs) (hiLt : i.sendIdx < S.N_send_tot)
    (hr : r ∈ recvRecs) (hrLt : r.bIdx < S.N_spk_tot)
    (hDec : P.kemDecaps r.pqspkSk r.kemCt = some r.kemSs)
    (hSs : r.kemSs = i.kemSs) :
    r.kemCt = i.kemCt ∧ i.pqspkPk = r.pqspkPk := by
  have hPos : 0 < S.N_send_tot := by omega
  let idx := r.bIdx * S.N_send_tot + i.sendIdx
  have hIdxLt : idx < S.N_spk_tot * S.N_send_tot := by
    dsimp [idx]
    calc r.bIdx * S.N_send_tot + i.sendIdx
        < r.bIdx * S.N_send_tot + S.N_send_tot := Nat.add_lt_add_left hiLt _
      _ = (r.bIdx + 1) * S.N_send_tot := by ring
      _ ≤ S.N_spk_tot * S.N_send_tot := Nat.mul_le_mul_right _ hrLt
  have hDiv : idx / S.N_send_tot = r.bIdx := by
    dsimp [idx]
    rw [Nat.mul_comm, Nat.mul_add_div hPos, Nat.div_eq_of_lt hiLt, Nat.add_zero]
  have hMod : idx % S.N_send_tot = i.sendIdx := by
    dsimp [idx]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hiLt]
  have hPairFalse : isKemShCrPair P i r = false := by
    by_contra hPairNe
    have hPairTrue : isKemShCrPair P i r = true := Bool.eq_true_of_not_eq_false hPairNe
    have hAtTrue : hasBadKemShCrRecordsAt S P idx initRecs recvRecs = true := by
      unfold hasBadKemShCrRecordsAt
      rw [hDiv, hMod, List.any_eq_true]
      refine ⟨i, hi, ?_⟩
      simp only [beq_self_eq_true, Bool.true_and, List.any_eq_true]
      exact ⟨r, hr, by simp [hPairTrue]⟩
    have hBadTrue : hasBadKemShCrRecords S P initRecs recvRecs = true := by
      unfold hasBadKemShCrRecords
      rw [List.any_eq_true]
      exact ⟨idx, List.mem_range.mpr hIdxLt, hAtTrue⟩
    rw [hNoBad] at hBadTrue
    nomatch hBadTrue
  unfold isKemShCrPair at hPairFalse
  rw [hSs] at hDec
  simp only [hDec, decide_true, Bool.true_and, decide_eq_false_iff_not, not_or] at hPairFalse
  exact ⟨Classical.not_not.mp hPairFalse.1, Classical.not_not.mp hPairFalse.2⟩

def respBundleIdx {S : Setup} : SessionId S → Option (Nat × Nat)
  | .recvOPK k j _   => some (k.val, j.val)
  | .recvNoOPK k j _ => some (k.val, j.val)
  | _                => none

/-- Structural invariant on an initiator session `s ∈ hst.base.sessions` in
    `pqxdhKeyIndAdvTagImpl`. -/
def ValidInitSession (S : Setup) (P : Primitives) (hst : KeyIndShCrState S)
    (s : KeyIndInitiatorEntry S) : Prop :=
  initSessionSlotIdx s.sid < S.N_send_tot ∧
  s.ekASk.length = 32 ∧
  s.hdr.ekAPk = P.x25519Base s.ekASk ∧
  s.fresh = s.honestPeer.isSome ∧
  (∀ v, s.honestPeer = some v →
    ∃ vEntry, (v, vEntry) ∈ hst.base.principals ∧ P.pow8 s.peerIkPk = P.pow8 vEntry.ikAPk) ∧
  (s.spkHonest = true →
    ∃ k j bEntry, ((k, j), bEntry) ∈ hst.base.spkBundles ∧ P.pow8 bEntry.spkPk = P.pow8 s.peerSpkPk)
      ∧
  (s.opkHonest = true →
    initSessionSlotIdx s.sid < S.N_send_opk_tot ∧
    ∃ k j o oEntry opkPk,
      ((k, j, o), oEntry) ∈ hst.base.opkEntries ∧
      s.peerOpkPk? = some opkPk ∧
      P.pow8 oEntry.opkPk = P.pow8 opkPk) ∧
  (s.pqspkHonest = true →
    ∃ k j kEntry bEntry,
      (k, kEntry) ∈ hst.base.principals ∧
      ((k, j), bEntry) ∈ hst.base.spkBundles ∧
      P.pow8 s.peerIkPk = P.pow8 kEntry.ikAPk ∧
      bEntry.pqspkPk = s.peerPqspkPk) ∧
  (∃ skB, skB.length = 32 ∧ P.pow8 s.peerIkPk = P.pow8 (P.x25519Base skB)) ∧
  (∃ skSpk, skSpk.length = 32 ∧ P.pow8 s.peerSpkPk = P.pow8 (P.x25519Base skSpk)) ∧
  (∀ opkPk, s.peerOpkPk? = some opkPk →
    ∃ skOpk, skOpk.length = 32 ∧ P.pow8 opkPk = P.pow8 (P.x25519Base skOpk)) ∧
  (∃ (u : ℕ) (uEntry : PrincipalEntry) (kemCoins ss : Bytes)
      (initRec : _root_.Proofs.SignalPqxdh.Security.InitKemRecord S),
    (u, uEntry) ∈ hst.base.principals ∧
    s.hdr.ikAPk = uEntry.ikAPk ∧
    P.kemEncaps s.peerPqspkPk kemCoins = some (ss, s.hdr.kemCt) ∧
    initRec ∈ hst.initKemRecs ∧
    initRec.sendIdx < hst.sendCount ∧
    initRec.sid = s.sid ∧
    initRec.pqspkPk = s.peerPqspkPk ∧
    initRec.kemCt = s.hdr.kemCt ∧
    initRec.kemSs = ss ∧
    s.drKeyReal.rootKey = buildSecrets
      (P.x25519 uEntry.secIKA0 s.peerSpkPk)
      (P.x25519 s.ekASk s.peerIkPk)
      (P.x25519 s.ekASk s.peerSpkPk)
      (s.peerOpkPk?.map (fun opkPk => P.x25519 s.ekASk opkPk))
      ss)

/-- Structural invariant on a responder session `r ∈ hst.base.respSessions` in
    `pqxdhKeyIndAdvTagImpl`. -/
def ValidRespSession (S : Setup) (P : Primitives) (hst : KeyIndShCrState S)
    (r : KeyIndRespEntry S) : Prop :=
  ∃ (k : Fin S.N_id) (j : Fin S.N_recv) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (ss : Bytes) (recEntry : _root_.Proofs.SignalPqxdh.Security.RecvKemRecord),
    respBundleIdx r.sid = some (k.val, j.val) ∧
    (k.val, kEntry) ∈ hst.base.principals ∧
    ((k.val, j.val), bEntry) ∈ hst.base.spkBundles ∧
    (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val, r.hdr.ekAPk) ∈ hst.base.seenKyberBaseKeys ∧
    r.respIkPk = kEntry.ikAPk ∧
    r.spkPk = bEntry.spkPk ∧
    r.pqspkPk = bEntry.pqspkPk ∧
    r.hdr.spkId = UInt32.ofNat j.val ∧
    r.hdr.pqspkId = UInt32.ofNat j.val ∧
    r.hdr.ikAPk.length = 32 ∧
    r.hdr.ekAPk.length = 32 ∧
    P.isCanonical r.hdr.ekAPk = true ∧
    (∃ skA, skA.length = 32 ∧ P.pow8 r.hdr.ikAPk = P.pow8 (P.x25519Base skA)) ∧
    P.kemDecaps bEntry.pqspkSk r.hdr.kemCt = some ss ∧
    recEntry ∈ hst.recvKemRecs ∧
    recEntry.bIdx = _root_.SignalPqxdh.Security.RoKem.spkBundleFlatIdx S k j ∧
    recEntry.pqspkPk = bEntry.pqspkPk ∧
    recEntry.pqspkSk = bEntry.pqspkSk ∧
    recEntry.kemCt = r.hdr.kemCt ∧
    recEntry.kemSs = ss ∧
    ((r.opkPk? = none ∧ r.hdr.opkId? = none ∧
      r.drKeyReal.rootKey = buildSecrets
        (P.x25519 bEntry.spkSk r.hdr.ikAPk)
        (P.x25519 kEntry.secIKA0 r.hdr.ekAPk)
        (P.x25519 bEntry.spkSk r.hdr.ekAPk)
        none ss) ∨
     (∃ (o : ℕ) (oEntry : OpkEntry),
      ((k.val, j.val, o), oEntry) ∈ hst.base.opkEntries ∧
      r.opkPk? = some oEntry.opkPk ∧
      r.hdr.opkId? = some (UInt32.ofNat o) ∧
      r.drKeyReal.rootKey = buildSecrets
        (P.x25519 bEntry.spkSk r.hdr.ikAPk)
        (P.x25519 kEntry.secIKA0 r.hdr.ekAPk)
        (P.x25519 bEntry.spkSk r.hdr.ekAPk)
        (some (P.x25519 oEntry.opkSk r.hdr.ekAPk)) ss))

/-- Key-generation well-formedness on `principals`, `spkBundles`, and `opkEntries`. -/
def ValidKeyStores (S : Setup) (P : Primitives) (st : KeyIndState S) : Prop :=
  ValidPrincipals S st.principals ∧
  ValidSpkBundles S st.spkBundles ∧
  ValidOpkEntries S st.opkEntries ∧
  (∀ kv ∈ st.principals, kv.2.secIKA0.length = 32 ∧ kv.2.ikAPk = P.x25519Base kv.2.secIKA0) ∧
  (∀ kv ∈ st.spkBundles,
    kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk ∧
    (∃ uEntry, (kv.1.1, uEntry) ∈ st.principals) ∧
    ∃ kpCoins, (P.kemKeyGen kpCoins).1 = kv.2.pqspkPk ∧ (P.kemKeyGen kpCoins).2 = kv.2.pqspkSk) ∧
  (∀ kv ∈ st.opkEntries, kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk) ∧
  (∀ kv ∈ st.advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)

theorem spkBundleFlatIdx_lt_tot (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv) :
    _root_.SignalPqxdh.Security.RoKem.spkBundleFlatIdx S k j < S.N_spk_tot := by
  unfold _root_.SignalPqxdh.Security.RoKem.spkBundleFlatIdx Setup.N_spk_tot
  calc k.val * S.N_recv + j.val
      < k.val * S.N_recv + S.N_recv := Nat.add_lt_add_left j.isLt _
    _ = (k.val + 1) * S.N_recv := by ring
    _ ≤ S.N_id * S.N_recv := Nat.mul_le_mul_right _ k.isLt

theorem drKeyReal_eq_init_resp_components {S : Setup} (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P)
    (hst : KeyIndShCrState S)
    (hNoBadKem : hasBadKemShCrRecords S P hst.initKemRecs hst.recvKemRecs = false)
    (hSendLe : hst.sendCount ≤ S.N_send_tot)
    {s : KeyIndInitiatorEntry S} {r : KeyIndRespEntry S}
    {uEntry : PrincipalEntry} {kemCoins ss_s : Bytes}
    {initRec : _root_.Proofs.SignalPqxdh.Security.InitKemRecord S}
    (hEnc : P.kemEncaps s.peerPqspkPk kemCoins = some (ss_s, s.hdr.kemCt))
    (hiMem : initRec ∈ hst.initKemRecs)
    (hiLt : initRec.sendIdx < hst.sendCount)
    (hiPq : initRec.pqspkPk = s.peerPqspkPk)
    (hiCt : initRec.kemCt = s.hdr.kemCt)
    (hiSs : initRec.kemSs = ss_s)
    (hsKey : s.drKeyReal.rootKey = buildSecrets
      (P.x25519 uEntry.secIKA0 s.peerSpkPk)
      (P.x25519 s.ekASk s.peerIkPk)
      (P.x25519 s.ekASk s.peerSpkPk)
      (s.peerOpkPk?.map (fun opkPk => P.x25519 s.ekASk opkPk))
      ss_s)
    {k : Fin S.N_id} {j : Fin S.N_recv} {kEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {ss_r : Bytes} {recEntry : _root_.Proofs.SignalPqxdh.Security.RecvKemRecord}
    {dh4_r? : Option Bytes}
    (h4_r : ∀ d, dh4_r? = some d → d.length = 32)
    (hrPq : r.pqspkPk = bEntry.pqspkPk)
    (hDec : P.kemDecaps bEntry.pqspkSk r.hdr.kemCt = some ss_r)
    (hrMem : recEntry ∈ hst.recvKemRecs)
    (hrBIdx : recEntry.bIdx = _root_.SignalPqxdh.Security.RoKem.spkBundleFlatIdx S k j)
    (hrRecPq : recEntry.pqspkPk = bEntry.pqspkPk)
    (hrRecSk : recEntry.pqspkSk = bEntry.pqspkSk)
    (hrRecCt : recEntry.kemCt = r.hdr.kemCt)
    (hrRecSs : recEntry.kemSs = ss_r)
    (hrKey : r.drKeyReal.rootKey = buildSecrets
      (P.x25519 bEntry.spkSk r.hdr.ikAPk)
      (P.x25519 kEntry.secIKA0 r.hdr.ekAPk)
      (P.x25519 bEntry.spkSk r.hdr.ekAPk)
      dh4_r? ss_r)
    (hKeyEq : s.drKeyReal.rootKey = r.drKeyReal.rootKey) :
    ss_s = ss_r ∧
    P.x25519 uEntry.secIKA0 s.peerSpkPk = P.x25519 bEntry.spkSk r.hdr.ikAPk ∧
    P.x25519 s.ekASk s.peerIkPk = P.x25519 kEntry.secIKA0 r.hdr.ekAPk ∧
    P.x25519 s.ekASk s.peerSpkPk = P.x25519 bEntry.spkSk r.hdr.ekAPk ∧
    s.peerOpkPk?.map (fun opkPk => P.x25519 s.ekASk opkPk) = dh4_r? ∧
    r.hdr.kemCt = s.hdr.kemCt ∧
    s.peerPqspkPk = r.pqspkPk := by
  have hw := hP.toWellFormedPrimitivesδ
  have hSsLen_s : ss_s.length = 32 := (hw.kemEncaps_len s.peerPqspkPk kemCoins ss_s s.hdr.kemCt
    hEnc).1
  have hSsLen_r : ss_r.length = 32 := hw.kemDecaps_len bEntry.pqspkSk r.hdr.kemCt ss_r hDec
  have h4_s : ∀ d, s.peerOpkPk?.map (fun opkPk => P.x25519 s.ekASk opkPk) = some d → d.length = 32
    := by
    intro d hd
    cases hOpk : s.peerOpkPk? with
    | none => rw [hOpk] at hd; nomatch hd
    | some opkPk =>
      rw [hOpk, Option.map_some, Option.some.injEq] at hd
      subst hd
      exact hw.x25519_len s.ekASk opkPk
  rw [hsKey, hrKey] at hKeyEq
  have hComponents := (buildSecrets_eq_iff_of_len32
    (hw.x25519_len _ _) (hw.x25519_len _ _) (hw.x25519_len _ _) h4_s hSsLen_s
    (hw.x25519_len _ _) (hw.x25519_len _ _) (hw.x25519_len _ _) h4_r hSsLen_r).mp hKeyEq
  rcases hComponents with ⟨hSsEq, hDh1, hDh2, hDh3, hDh4⟩
  have hrLt : recEntry.bIdx < S.N_spk_tot := by
    rw [hrBIdx]
    exact spkBundleFlatIdx_lt_tot S k j
  have hDecRec : P.kemDecaps recEntry.pqspkSk recEntry.kemCt = some recEntry.kemSs := by
    rw [hrRecSk, hrRecCt, hrRecSs, hDec]
  have hKem := eq_kemCt_and_pqspkPk_of_hasBadKemShCrRecords_false P
    hst.initKemRecs hst.recvKemRecs hNoBadKem
    hiMem (Nat.lt_of_lt_of_le hiLt hSendLe) hrMem hrLt hDecRec
    (by rw [hrRecSs, hiSs, hSsEq])
  rw [hrRecCt, hiCt] at hKem
  have hPqEq : s.peerPqspkPk = r.pqspkPk := by
    rw [← hiPq, hKem.2, hrRecPq, hrPq]
  exact ⟨hSsEq, hDh1, hDh2, hDh3, hDh4, hKem.1, hPqEq⟩

/-- Under `hasBadKemShCrRecords = false`, an initiator `s` and a responder `r` with `pow8`-equal
    SPKs and equal `drKeyReal.rootKey` satisfy `keyIndPartner P s r = true`. -/
theorem drKeyReal_eq_imp_keyIndPartner_of_pow8_spk_eq {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (hst : KeyIndShCrState S) (hKS : ValidKeyStores S P
      hst.base)
    (hNoBadKem : hasBadKemShCrRecords S P hst.initKemRecs hst.recvKemRecs = false)
    (hSendLe : hst.sendCount ≤ S.N_send_tot)
    {s : KeyIndInitiatorEntry S} {r : KeyIndRespEntry S}
    (hs : ValidInitSession S P hst s) (hr : ValidRespSession S P hst r)
    (hPowSpk : P.pow8 s.peerSpkPk = P.pow8 r.spkPk)
    (hKeyEq : s.drKeyReal.rootKey = r.drKeyReal.rootKey) :
    keyIndPartner P s r = true := by
  have hw := hP.toWellFormedPrimitivesδ
  rcases hKS with ⟨_, _, _, hPrins, hSpks, hOpks, _⟩
  rcases hs with ⟨_, hekLen, hekPk, _, _, _, _, _, ⟨skB, _, hSkBPow⟩, _, hOpkKosk,
    u, uEntry, kemCoins, ss_s, initRec, huMem, hsIkPk, hEnc, hiMem, hiLt, _, hiPq, hiCt, hiSs,
      hsKey⟩
  rcases hr with ⟨k, j, kEntry, bEntry, ss_r, recEntry, _, hkMem, hbMem, _,
    hrRespIk, hrSpk, hrPqspk, _, _, hrIkLen, hrEkLen, hrEkCanon, _, hDec,
    hrMem, hrBIdx, hrRecPq, hrRecSk, hrRecCt, hrRecSs, hrOpkCases⟩
  have huIk := hPrins (u, uEntry) huMem
  have hkIk := hPrins (k.val, kEntry) hkMem
  have hbSpk := hSpks ((k.val, j.val), bEntry) hbMem
  rcases hbSpk with ⟨hbSkLen, hbSpkPk, _, _⟩
  let dh4_r? : Option Bytes :=
    match hrOpkCases with
    | _ => r.opkPk?.map (fun opkPk => P.x25519 s.ekASk opkPk)
  have hSpkPowBase : P.pow8 s.peerSpkPk = P.pow8 (P.x25519Base bEntry.spkSk) := by
    rw [hPowSpk, hrSpk, hbSpkPk]
  have hMain :
      P.x25519 uEntry.secIKA0 s.peerSpkPk = P.x25519 bEntry.spkSk r.hdr.ikAPk ∧
      P.x25519 s.ekASk s.peerIkPk = P.x25519 kEntry.secIKA0 r.hdr.ekAPk ∧
      P.x25519 s.ekASk s.peerSpkPk = P.x25519 bEntry.spkSk r.hdr.ekAPk ∧
      r.hdr.kemCt = s.hdr.kemCt ∧
      s.peerPqspkPk = r.pqspkPk ∧
      (s.hdr.ekAPk = r.hdr.ekAPk → s.peerOpkPk?.map P.pow8 = r.opkPk?.map P.pow8) := by
    rcases hrOpkCases with ⟨hrOpkNone, _, hrKey⟩ | ⟨o, oEntry, hoMem, hrOpkSome, _, hrKey⟩
    · rcases drKeyReal_eq_init_resp_components P hP hst hNoBadKem hSendLe
        hEnc hiMem hiLt hiPq hiCt hiSs hsKey
        (fun d hd => by nomatch hd)
        hrPqspk hDec hrMem hrBIdx hrRecPq hrRecSk hrRecCt hrRecSs hrKey hKeyEq with
        ⟨_, hDh1, hDh2, hDh3, hDh4, hCtEq, hPqEq⟩
      refine ⟨hDh1, hDh2, hDh3, hCtEq, hPqEq, fun _ => ?_⟩
      rw [hrOpkNone]
      cases hsOpk : s.peerOpkPk? with
      | none => rfl
      | some _ => rw [hsOpk] at hDh4; nomatch hDh4
    · have hoOpk := hOpks ((k.val, j.val, o), oEntry) hoMem
      rcases drKeyReal_eq_init_resp_components P hP hst hNoBadKem hSendLe
        hEnc hiMem hiLt hiPq hiCt hiSs hsKey
        (fun d hd => by injection hd with hd'; subst hd'; exact hw.x25519_len _ _)
        hrPqspk hDec hrMem hrBIdx hrRecPq hrRecSk hrRecCt hrRecSs hrKey hKeyEq with
        ⟨_, hDh1, hDh2, hDh3, hDh4, hCtEq, hPqEq⟩
      refine ⟨hDh1, hDh2, hDh3, hCtEq, hPqEq, fun hEkEq => ?_⟩
      rw [hrOpkSome]
      cases hsOpk : s.peerOpkPk? with
      | none => rw [hsOpk] at hDh4; nomatch hDh4
      | some sOpkPk =>
        rw [hsOpk, Option.map_some, Option.some.injEq] at hDh4
        rcases hOpkKosk sOpkPk hsOpk with ⟨skOpk, _, hSkOpkPow⟩
        have hOpk1 : P.x25519 s.ekASk sOpkPk = P.x25519 s.ekASk (P.x25519Base skOpk) :=
          hP.x25519_pow8_congr s.ekASk sOpkPk (P.x25519Base skOpk)
            (hP.pow8_base_len sOpkPk skOpk hSkOpkPow) (hw.x25519Base_len skOpk) hSkOpkPow
        have hOpk2 : P.x25519 oEntry.opkSk r.hdr.ekAPk = P.x25519 s.ekASk (P.x25519Base
          oEntry.opkSk) := by
          rw [← hEkEq, hekPk, hw.x25519_comm oEntry.opkSk s.ekASk]
        rw [hOpk1, hOpk2] at hDh4
        have hPowOpkBase := hP.x25519_inj_pow8 s.ekASk (P.x25519Base skOpk) (P.x25519Base
          oEntry.opkSk)
          hekLen (hw.x25519Base_len skOpk) (hw.x25519Base_len oEntry.opkSk) hDh4
        simp only [Option.map_some, Option.some.injEq]
        rw [hSkOpkPow, hPowOpkBase, ← hoOpk.2]
  rcases hMain with ⟨hDh1, hDh2, hDh3, hCtEq, hPqEq, hOpkImp⟩
  have hEkEq : s.hdr.ekAPk = r.hdr.ekAPk := by
    rw [x25519_comm_of_pow8_eq P hP s.ekASk bEntry.spkSk s.peerSpkPk hSpkPowBase, ← hekPk] at hDh3
    have hPowEk := hP.x25519_inj_pow8 bEntry.spkSk s.hdr.ekAPk r.hdr.ekAPk
      hbSkLen (by rw [hekPk]; exact hw.x25519Base_len s.ekASk) hrEkLen hDh3
    exact eq_of_isCanonical_of_pow8_eq P hP (by rw [hekPk]; exact hw.canon_base s.ekASk) hrEkCanon
      hPowEk
  have hPowIkB : P.pow8 s.peerIkPk = P.pow8 r.respIkPk := by
    have h1 : P.x25519 s.ekASk s.peerIkPk = P.x25519 s.ekASk (P.x25519Base skB) :=
      hP.x25519_pow8_congr s.ekASk s.peerIkPk (P.x25519Base skB)
        (hP.pow8_base_len s.peerIkPk skB hSkBPow) (hw.x25519Base_len skB) hSkBPow
    have h2 : P.x25519 kEntry.secIKA0 r.hdr.ekAPk = P.x25519 s.ekASk (P.x25519Base kEntry.secIKA0)
      := by
      rw [← hEkEq, hekPk, hw.x25519_comm kEntry.secIKA0 s.ekASk]
    rw [h1, h2] at hDh2
    have hPowBase := hP.x25519_inj_pow8 s.ekASk (P.x25519Base skB) (P.x25519Base kEntry.secIKA0)
      hekLen (hw.x25519Base_len skB) (hw.x25519Base_len kEntry.secIKA0) hDh2
    rw [hSkBPow, hPowBase, ← hkIk.2, hrRespIk]
  have hPowIkA : P.pow8 s.hdr.ikAPk = P.pow8 r.hdr.ikAPk := by
    rw [x25519_comm_of_pow8_eq P hP uEntry.secIKA0 bEntry.spkSk s.peerSpkPk hSpkPowBase,
        ← huIk.2, ← hsIkPk] at hDh1
    exact hP.x25519_inj_pow8 bEntry.spkSk s.hdr.ikAPk r.hdr.ikAPk
      hbSkLen (by rw [hsIkPk, huIk.2]; exact hw.x25519Base_len uEntry.secIKA0) hrIkLen hDh1
  unfold keyIndPartner
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨hPowIkA, hPowIkB⟩, hPowSpk⟩, hOpkImp hEkEq⟩, hEkEq⟩, hPqEq⟩, hCtEq.symm⟩

theorem drKeyReal_eq_imp_keyIndPartner_of_pqspkHonest {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (hst : KeyIndShCrState S) (hKS : ValidKeyStores S P
      hst.base)
    (hNoBadKem : hasBadKemShCrRecords S P hst.initKemRecs hst.recvKemRecs = false)
    (hNoKemColl : hasKemPkCollisionKeyInd hst.base = false)
    (hSendLe : hst.sendCount ≤ S.N_send_tot)
    {s : KeyIndInitiatorEntry S} {r : KeyIndRespEntry S}
    (hs : ValidInitSession S P hst s) (hr : ValidRespSession S P hst r)
    (hPqHon : s.pqspkHonest = true)
    (hKeyEq : s.drKeyReal.rootKey = r.drKeyReal.rootKey) :
    keyIndPartner P s r = true := by
  have hw := hP.toWellFormedPrimitivesδ
  have hs0 := hs
  have hr0 := hr
  rcases hKS with ⟨hValPrins, _, _, hPrins, hSpks, _, _⟩
  rcases hs with ⟨_, hekLen, hekPk, _, _, _, _, hPqHonImp, _, ⟨skSpk, _, hSkSpkPow⟩, _,
    u, uEntry, kemCoins, ss_s, initRec, _, _, hEnc, hiMem, hiLt, _, hiPq, hiCt, hiSs, hsKey⟩
  rcases hr with ⟨k, j, kEntry, bEntry, ss_r, recEntry, _, hkMem, hbMem, _,
    _, hrSpk, hrPqspk, _, _, _, hrEkLen, hrEkCanon, _, hDec,
    hrMem, hrBIdx, hrRecPq, hrRecSk, hrRecCt, hrRecSs, hrOpkCases⟩
  have hkIk := hPrins (k.val, kEntry) hkMem
  have hbSpk := hSpks ((k.val, j.val), bEntry) hbMem
  rcases hbSpk with ⟨_, hbSpkPk, _, _⟩
  have hSub :
      P.x25519 s.ekASk s.peerIkPk = P.x25519 kEntry.secIKA0 r.hdr.ekAPk ∧
      P.x25519 s.ekASk s.peerSpkPk = P.x25519 bEntry.spkSk r.hdr.ekAPk ∧
      s.peerPqspkPk = r.pqspkPk := by
    rcases hrOpkCases with ⟨_, _, hrKey⟩ | ⟨_, _, _, _, _, hrKey⟩
    · rcases drKeyReal_eq_init_resp_components P hP hst hNoBadKem hSendLe
        hEnc hiMem hiLt hiPq hiCt hiSs hsKey (fun d hd => by nomatch hd)
        hrPqspk hDec hrMem hrBIdx hrRecPq hrRecSk hrRecCt hrRecSs hrKey hKeyEq with
        ⟨_, _, hDh2, hDh3, _, _, hPqEq⟩
      exact ⟨hDh2, hDh3, hPqEq⟩
    · rcases drKeyReal_eq_init_resp_components P hP hst hNoBadKem hSendLe
        hEnc hiMem hiLt hiPq hiCt hiSs hsKey
        (fun d hd => by injection hd with hd'; subst hd'; exact hw.x25519_len _ _)
        hrPqspk hDec hrMem hrBIdx hrRecPq hrRecSk hrRecCt hrRecSs hrKey hKeyEq with
        ⟨_, _, hDh2, hDh3, _, _, hPqEq⟩
      exact ⟨hDh2, hDh3, hPqEq⟩
  rcases hSub with ⟨hDh2, hDh3, hPqEq⟩
  rcases hPqHonImp hPqHon with ⟨k_s, j_s, k_s_Entry, b_s, hk_sMem, hb_sMem, hPowIk_s, hPq_s⟩
  have hNodupKem := nodup_spkBundles_of_hasKemPkCollisionKeyInd_false hst.base hNoKemColl
  have hBundleEq : ((k_s, j_s), b_s) = ((k.val, j.val), bEntry) :=
    eq_of_nodup_map (fun (_, b) => b.pqspkPk) hNodupKem hb_sMem hbMem
      (by dsimp only; rw [hPq_s, hPqEq, hrPqspk])
  have hKsEq : k_s = k.val := by injection hBundleEq with hPair _; injection hPair
  subst hKsEq
  have hPrinEq : (k.val, k_s_Entry) = (k.val, kEntry) :=
    eq_of_nodup_map Prod.fst hValPrins.2 hk_sMem hkMem rfl
  injection hPrinEq with _ hkEntryEq
  cases hkEntryEq
  have hPowIkBase : P.pow8 s.peerIkPk = P.pow8 (P.x25519Base kEntry.secIKA0) := by
    rw [hPowIk_s, hkIk.2]
  have hEkEq : s.hdr.ekAPk = r.hdr.ekAPk := by
    rw [x25519_comm_of_pow8_eq P hP s.ekASk kEntry.secIKA0 s.peerIkPk hPowIkBase, ← hekPk] at hDh2
    have hPowEk := hP.x25519_inj_pow8 kEntry.secIKA0 s.hdr.ekAPk r.hdr.ekAPk
      hkIk.1 (by rw [hekPk]; exact hw.x25519Base_len s.ekASk) hrEkLen hDh2
    exact eq_of_isCanonical_of_pow8_eq P hP (by rw [hekPk]; exact hw.canon_base s.ekASk) hrEkCanon
      hPowEk
  have hPowSpk : P.pow8 s.peerSpkPk = P.pow8 r.spkPk := by
    have h1 : P.x25519 s.ekASk s.peerSpkPk = P.x25519 s.ekASk (P.x25519Base skSpk) :=
      hP.x25519_pow8_congr s.ekASk s.peerSpkPk (P.x25519Base skSpk)
        (hP.pow8_base_len s.peerSpkPk skSpk hSkSpkPow) (hw.x25519Base_len skSpk) hSkSpkPow
    have h2 : P.x25519 bEntry.spkSk r.hdr.ekAPk = P.x25519 s.ekASk (P.x25519Base bEntry.spkSk) := by
      rw [← hEkEq, hekPk, hw.x25519_comm bEntry.spkSk s.ekASk]
    rw [h1, h2] at hDh3
    have hPowBase := hP.x25519_inj_pow8 s.ekASk (P.x25519Base skSpk) (P.x25519Base bEntry.spkSk)
      hekLen (hw.x25519Base_len skSpk) (hw.x25519Base_len bEntry.spkSk) hDh3
    rw [hSkSpkPow, hPowBase, ← hbSpkPk, hrSpk]
  exact drKeyReal_eq_imp_keyIndPartner_of_pow8_spk_eq P hP hst ⟨hValPrins, ‹_›, ‹_›, hPrins, hSpks,
    ‹_›, ‹_›⟩
    hNoBadKem hSendLe hs0 hr0 hPowSpk hKeyEq

theorem keyIndPartner_inj_left {S : Setup} (P : Primitives) (st : KeyIndState S)
    (hNoEc : hasEcPkCollisionKeyInd P st = false)
    {s1 s2 : KeyIndInitiatorEntry S} {r : KeyIndRespEntry S}
    (hs1 : s1 ∈ st.sessions) (hs2 : s2 ∈ st.sessions)
    (hP1 : keyIndPartner P s1 r = true) (hP2 : keyIndPartner P s2 r = true) :
    s1 = s2 := by
  unfold keyIndPartner at hP1 hP2
  simp only [Bool.and_eq_true, beq_iff_eq] at hP1 hP2
  have hEkEq : P.pow8 s1.hdr.ekAPk = P.pow8 s2.hdr.ekAPk := by
    rw [hP1.1.1.2, hP2.1.1.2]
  exact eq_of_nodup_map (fun s => P.pow8 s.hdr.ekAPk)
    (nodup_sessions_of_hasEcPkCollisionKeyInd_false P st hNoEc) hs1 hs2 hEkEq

theorem keyIndPartner_inj_right {S : Setup} (P : Primitives) (hst : KeyIndShCrState S)
    (hNoKem : hasKemPkCollisionKeyInd hst.base = false)
    (hNodupResp : (hst.base.respSessions.map (fun r => (respBundleIdx r.sid, r.hdr.ekAPk))).Nodup)
    {s : KeyIndInitiatorEntry S} {r1 r2 : KeyIndRespEntry S}
    (hr1Mem : r1 ∈ hst.base.respSessions) (hr2Mem : r2 ∈ hst.base.respSessions)
    (hr1 : ValidRespSession S P hst r1) (hr2 : ValidRespSession S P hst r2)
    (hP1 : keyIndPartner P s r1 = true) (hP2 : keyIndPartner P s r2 = true) :
    r1 = r2 := by
  unfold keyIndPartner at hP1 hP2
  simp only [Bool.and_eq_true, beq_iff_eq] at hP1 hP2
  rcases hr1 with ⟨k1, j1, _, b1, _, _, hIdx1, _, hb1Mem, _, _, _, hr1Pq, _⟩
  rcases hr2 with ⟨k2, j2, _, b2, _, _, hIdx2, _, hb2Mem, _, _, _, hr2Pq, _⟩
  have hNodupKem := nodup_spkBundles_of_hasKemPkCollisionKeyInd_false hst.base hNoKem
  have hBundleEq : ((k1.val, j1.val), b1) = ((k2.val, j2.val), b2) :=
    eq_of_nodup_map (fun (_, b) => b.pqspkPk) hNodupKem hb1Mem hb2Mem
      (by dsimp only; rw [← hr1Pq, ← hP1.1.2, hP2.1.2, hr2Pq])
  have hPairEq : (k1.val, j1.val) = (k2.val, j2.val) := by injection hBundleEq
  have hEkEq : r1.hdr.ekAPk = r2.hdr.ekAPk := by rw [← hP1.1.1.2, hP2.1.1.2]
  exact eq_of_nodup_map (fun r => (respBundleIdx r.sid, r.hdr.ekAPk)) hNodupResp hr1Mem hr2Mem
    (by simp [hIdx1, hIdx2, hPairEq, hEkEq])

theorem resp_drKeyReal_eq_imp_eq_of_pow8_spk_eq {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (hst : KeyIndShCrState S) (hKS : ValidKeyStores S P
      hst.base)
    (hNoEc : hasEcPkCollisionKeyInd P hst.base = false)
    (hNodupResp : (hst.base.respSessions.map (fun r => (respBundleIdx r.sid, r.hdr.ekAPk))).Nodup)
    {r1 r2 : KeyIndRespEntry S}
    (hr1Mem : r1 ∈ hst.base.respSessions) (hr2Mem : r2 ∈ hst.base.respSessions)
    (hr1 : ValidRespSession S P hst r1) (hr2 : ValidRespSession S P hst r2)
    (hPowSpk : P.pow8 r1.spkPk = P.pow8 r2.spkPk)
    (hKeyEq : r1.drKeyReal.rootKey = r2.drKeyReal.rootKey) :
    r1 = r2 := by
  have hw := hP.toWellFormedPrimitivesδ
  rcases hKS with ⟨_, _, _, _, hSpks, _, _⟩
  rcases hr1 with ⟨k1, j1, kEntry1, b1, ss1, _, hIdx1, _, hb1Mem, _, _, hr1Spk, _, _, _, _,
    hr1EkLen, hr1EkCanon, _, hDec1, _, _, _, _, _, _, hr1Opk⟩
  rcases hr2 with ⟨k2, j2, kEntry2, b2, ss2, _, hIdx2, _, hb2Mem, _, _, hr2Spk, _, _, _, _,
    hr2EkLen, hr2EkCanon, _, hDec2, _, _, _, _, _, _, hr2Opk⟩
  have hNodupSpk := nodup_spkBundles_of_hasEcPkCollisionKeyInd_false P hst.base hNoEc
  have hBundleEq : ((k1.val, j1.val), b1) = ((k2.val, j2.val), b2) :=
    eq_of_nodup_map (fun (_, b) => P.pow8 b.spkPk) hNodupSpk hb1Mem hb2Mem
      (by dsimp only; rw [← hr1Spk, hPowSpk, hr2Spk])
  have hPairEq : (k1.val, j1.val) = (k2.val, j2.val) := by injection hBundleEq
  have hbEq : b1 = b2 := by injection hBundleEq
  subst hbEq
  have hbSpkLen : b1.spkSk.length = 32 := (hSpks ((k1.val, j1.val), b1) hb1Mem).1
  have hSs1Len : ss1.length = 32 := hw.kemDecaps_len b1.pqspkSk r1.hdr.kemCt ss1 hDec1
  have hSs2Len : ss2.length = 32 := hw.kemDecaps_len b1.pqspkSk r2.hdr.kemCt ss2 hDec2
  have hDh3Eq : P.x25519 b1.spkSk r1.hdr.ekAPk = P.x25519 b1.spkSk r2.hdr.ekAPk := by
    rcases hr1Opk with ⟨_, _, hK1⟩ | ⟨_, _, _, _, _, hK1⟩ <;>
      rcases hr2Opk with ⟨_, _, hK2⟩ | ⟨_, _, _, _, _, hK2⟩ <;>
    · rw [hK1, hK2] at hKeyEq
      exact ((buildSecrets_eq_iff_of_len32
        (hw.x25519_len _ _) (hw.x25519_len _ _) (hw.x25519_len _ _)
        (fun d hd => by cases hd <;> exact hw.x25519_len _ _) hSs1Len
        (hw.x25519_len _ _) (hw.x25519_len _ _) (hw.x25519_len _ _)
        (fun d hd => by cases hd <;> exact hw.x25519_len _ _) hSs2Len).mp hKeyEq).2.2.2.1
  have hPowEk := hP.x25519_inj_pow8 b1.spkSk r1.hdr.ekAPk r2.hdr.ekAPk
    hbSpkLen hr1EkLen hr2EkLen hDh3Eq
  have hEkEq : r1.hdr.ekAPk = r2.hdr.ekAPk :=
    eq_of_isCanonical_of_pow8_eq P hP hr1EkCanon hr2EkCanon hPowEk
  exact eq_of_nodup_map (fun r => (respBundleIdx r.sid, r.hdr.ekAPk)) hNodupResp hr1Mem hr2Mem
    (by simp [hIdx1, hIdx2, hPairEq, hEkEq])

end Proofs.SignalPqxdh.Security
