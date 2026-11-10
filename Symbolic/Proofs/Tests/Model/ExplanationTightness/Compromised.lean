/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
public import Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon
import Init.Data.String.Defs
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Tests.Shared.ExplanationTightness.CompromisedTraces
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

@[expose] public section

set_option autoImplicit false

/-!
# Tightness of the `Compromised` Predicate

Proves necessity and redundancy results for each disjunct of `(mkTestTracePredicates tr).Compromised`
and its sub-predicates `HandshakeRootCompromised`, `HandshakeKeysAt`, `HandshakeWasCompromisedAt`,
and `honestDH` in `ForwardSecrecy` and `PostCompromiseSecurity`. Every top-level and nested
disjunct is necessary except `ExposedDHs` and `honestDH ∧ BrokenDH` inside `ForwardSecrecy` and the
`TREvent.HonestDH` event disjunct of `honestDH` inside `Compromised`. Also proves strictness of the
session-scoped `HandshakeRootCompromised` over the existential baseline on `Adversary.trAlias`
(`b6_tight_bob_strict`).
-/

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.Compromised

open Symbolic.Proofs.Tests.Shared.Composed.Adversary (isAnyTRExposure isBrokenDH mem_trEvIdx
  not_tr_logged trAlias trAlias_aliceDone trAlias_bobDone trAlias_compIK trAlias_compIK_carol
  trAlias_compromise_indices trAlias_keys trAlias_out trAlias_reach trAlias_trExposure_indices
  trEvIdx trIKA trIKA_reach trIKA_trExposure_indices trIKB_out)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (dhsA dhsB1 evIdx ikA ikB isCompromise
  mem_evIdx noCompromise_of_evIdx not_logged pqskB spkB stA0 stB2)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.CompromisedTraces (cBDH dhsBDH
  fsQuery_mono_compromised handshakeKeysAt_of_aliceSingleton honestDH_event_imp_stored mkB0 mkBDH
  mkHrcCk mkHrcRk not_dhs_excuses_msgKey not_fsQuery_of_no_compromised pcsQuery_mono_compromised
  stB2_cks_eq trBDH trBDH_exposedRK_eq trBDH_honestDHEv_eq trBDH_honestDH_dhsA trBDH_knows_mkBDH
  trBDH_msgKey trBDH_nonRk_indices trBDH_not_handshakeExcusedAt trBDH_reach trCK
  trCK_compromise_indices trCK_knows_mkA0 trCK_msgKey trCK_nonCks_indices trCK_reach trCKr
  trCKr_compromise_indices trCKr_knows_mkCKr trCKr_msgKey trCKr_nonCkr_indices trCKr_reach trHrcCk
  trHrcCk_aliceDone_at trHrcCk_aliceDone_indices trHrcCk_bobDone_indices trHrcCk_brokenDH_indices
  trHrcCk_knows_mkHrcCk trHrcCk_msgKey trHrcCk_reach trHrcCk_trExposure_indices trHrcRk
  trHrcRk_aliceDone_at trHrcRk_aliceDone_indices trHrcRk_bobDone_indices trHrcRk_brokenDH_indices
  trHrcRk_knows_mkHrcRk trHrcRk_msgKey trHrcRk_reach trHrcRk_trExposure_indices
  trIKA_aliceDone_indices trIKA_brokenDH_indices trIKA_knows_mkIKA trIKA_msgKey trMK
  trMK_compromise_indices trMK_knows_seedB0 trMK_msgKey trMK_nonMk_indices trMK_reach trRK
  trRK_compromise_indices trRK_exposedKey trRK_honestDH_dhsA trRK_honestDH_dhsB1 trRK_knows_mkB0
  trRK_msgKey trRK_reach)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (ExposedKey FSQueryP IsChainRoot
  PCSQueryP TREntry TestTracePredicates chainKeyAt_root_inj compromised_iff_exposedKey_of_evIdx
  createChain_snd_inj eq_of_rootDescends_pqxdhKdf_rk fsQuery_iff_test isChainRoot_createChain_snd
  isChainRoot_pqxdhKdf_ck isChainRoot_pqxdhKdf_rk kdfCk_snd_inj mkTestTracePredicates
  not_chainKeyAt_eq_of_root not_exposedKey_of_trEvIdx not_handshakeRootCompromised_of_noCompromise
  pcsQuery_iff_test pqxdhKdf_ck_ne_createChain_snd pqxdhKdf_ck_ne_kdfCk_snd pqxdhKdf_rk_ne_ck
  pqxdhKdf_rk_ne_kdfCk_snd rnd_inj_pair saltDepth saltDepth_le_of_rootDescends)
open DY DY.Libsignal DY.Libsignal.Composed

open DY
open DY.DiffieHellman
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys HandshakeKeysAt HandshakeWasCompromisedAt
  AliceHandshakeWasCompromised BobHandshakeWasCompromised pqxdhKdf)
open DY.Libsignal.TripleRatchet (TRState TREvent createChain kdfCk chainKeyAt
  DerivesMsgKey DerivesChain RootDescends)
open DY.Libsignal.TripleRatchet.Cheval (FSQuery PCSQuery StateStoredAt HandshakeRootCompromised
  CompromisedKey)

/-! ## Top-Level `Compromised` Disjuncts -/

section TopLevelDisjuncts

/-- The seven top-level disjuncts of `(mkTestTracePredicates tr).Compromised`. -/
inductive CompromisedKind where
  | rk
  | dhs
  | cks
  | ckr
  | mk
  | hrc
  | bdh
  deriving DecidableEq

def keepUnless (drop : Option CompromisedKind) (kind : CompromisedKind) (p : Prop) : Prop :=
  match drop with
  | none => p
  | some o => o ≠ kind ∧ p

/-- `mkTestTracePredicates tr` with the top-level `Compromised` disjunct `drop` omitted
(`drop = none` keeps every disjunct). -/
def tracePredicatesWithout (tr : ExecTrace) (drop : Option CompromisedKind) : TestTracePredicates :=
  let honestDH (d : Bytes) : Prop :=
    (∃ s i, tr.EventLogged (TREvent.HonestDH s d i)) ∨
    (∃ me st idx, StateStoredAt me st idx tr ∧ st.dhs = d)
  { mkTestTracePredicates tr with
    Compromised := fun k =>
      keepUnless drop .rk (∃ s i, tr.EventLogged (TREvent.ExposedRK s k i)) ∨
      keepUnless drop .dhs (∃ s i, tr.EventLogged (TREvent.ExposedDHs s k i)) ∨
      keepUnless drop .cks (∃ s ns i, tr.EventLogged (TREvent.ExposedCKs s k ns i)) ∨
      keepUnless drop .ckr (∃ s nr i, tr.EventLogged (TREvent.ExposedCKr s k nr i)) ∨
      keepUnless drop .mk (∃ s n i, tr.EventLogged (TREvent.ExposedMK s k n i)) ∨
      keepUnless drop .hrc (HandshakeRootCompromised tr k) ∨
      keepUnless drop .bdh (honestDH k ∧ tr.EventLogged PQXDHEvent.BrokenDH) }

def ForwardSecrecyWithout (drop : Option CompromisedKind) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → FSQueryP (tracePredicatesWithout tr drop)

def PostCompromiseSecurityWithout (drop : Option CompromisedKind) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → PCSQueryP (tracePredicatesWithout tr drop)

theorem tracePredicatesWithout_none (tr : ExecTrace) :
    tracePredicatesWithout tr none = mkTestTracePredicates tr := rfl

theorem forwardSecrecyWithout_none : ForwardSecrecyWithout none ↔ ForwardSecrecy := by
  simp only [ForwardSecrecyWithout, tracePredicatesWithout_none, ForwardSecrecy, fsQuery_iff_test]

theorem postCompromiseSecurityWithout_none :
    PostCompromiseSecurityWithout none ↔ PostCompromiseSecurity := by
  simp only [PostCompromiseSecurityWithout, tracePredicatesWithout_none, PostCompromiseSecurity,
    pcsQuery_iff_test]

private theorem compromisedWithout_imp_real {tr : ExecTrace} {o : CompromisedKind} {k : Bytes}
    (h : (tracePredicatesWithout tr (some o)).Compromised k) :
    (mkTestTracePredicates tr).Compromised k := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr h)))))

private theorem compromisedWithout_dhs_of_real_of_not_dhs {tr : ExecTrace} {k : Bytes}
    (hc : (mkTestTracePredicates tr).Compromised k)
    (hno : ∀ s i, ¬ tr.EventLogged (TREvent.ExposedDHs s k i)) :
    (tracePredicatesWithout tr (some .dhs)).Compromised k := by
  rcases hc with h | ⟨s, i, h⟩ | h | h | h | h | h
  · exact .inl ⟨by decide, h⟩
  · exact False.elim (hno s i h)
  · exact .inr (.inr (.inl ⟨by decide, h⟩))
  · exact .inr (.inr (.inr (.inl ⟨by decide, h⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨by decide, h⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨by decide, h⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨by decide, h⟩)))))

private theorem compromisedWithout_bdh_of_real_of_not_bdh {tr : ExecTrace} {k : Bytes}
    (hc : (mkTestTracePredicates tr).Compromised k)
    (hno : (mkTestTracePredicates tr).HonestDH k → ¬ tr.EventLogged PQXDHEvent.BrokenDH) :
    (tracePredicatesWithout tr (some .bdh)).Compromised k := by
  rcases hc with h | h | h | h | h | h | ⟨hhdh, hbrk⟩
  · exact .inl ⟨by decide, h⟩
  · exact .inr (.inl ⟨by decide, h⟩)
  · exact .inr (.inr (.inl ⟨by decide, h⟩))
  · exact .inr (.inr (.inr (.inl ⟨by decide, h⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨by decide, h⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨by decide, h⟩)))))
  · exact False.elim (hno hhdh hbrk)

private theorem predKnows_of_msgKey {tr : ExecTrace} {seed : Bytes}
    (hmk : (mkTestTracePredicates tr).MessageKey seed) (hk : seed.AttackerKnows tr) :
    (mkTestTracePredicates tr).AttackerKnows seed := by
  rcases hmk with ⟨pqSalt, hev⟩
  exact ⟨pqSalt, hev, .inl hk⟩

private theorem not_handshakeRootCompromised_of_evIdx {tr : ExecTrace} {k : Bytes}
    (hno : evIdx tr isCompromise = []) : ¬ HandshakeRootCompromised tr k :=
  not_handshakeRootCompromised_of_noCompromise (noCompromise_of_evIdx hno)

private theorem not_brokenDH_of_evIdx {tr : ExecTrace}
    (hno : evIdx tr isCompromise = []) : ¬ tr.EventLogged PQXDHEvent.BrokenDH :=
  (noCompromise_of_evIdx hno).2.2.2.2.1

@[simp] private theorem saltDepth_cBDH_chainKey : saltDepth cBDH.chainKey = 6 := by
  have h : cBDH.chainKey = (createChain stA0.rk (dhPk dhsA) dhsA).2 := rfl
  rw [h]; simp

private theorem not_pcsQuery_trBDH {P : TestTracePredicates}
    (hmk : P.MessageKey mkBDH) (hknow : P.AttackerKnows mkBDH)
    (hdh : P.HonestDH dhsA)
    (hcomp : ∀ k, P.Compromised k → k = stA0.rk ∨ k = dhsBDH) :
    ¬ PCSQueryP P := by
  intro hpcs
  have hstep : DerivesMsgKey (createChain stA0.rk (dhPk dhsA) dhsA).2 mkBDH := ⟨0, rfl⟩
  rcases hpcs mkBDH stA0.rk dhsA dhsA hmk hknow hdh hdh (.inl hstep) with
    hc | ⟨ck, ⟨steps, heq⟩, hc⟩ | ⟨rk, ck, hr, _, _, hc⟩ | ⟨_, hc | hc⟩
  · rcases hcomp mkBDH hc with h | h
    · have := congrArg saltDepth h; simp at this
    · have := congrArg saltDepth h; simp at this
  · have hroot : IsChainRoot (createChain stA0.rk (dhPk dhsA) dhsA).2 :=
      isChainRoot_createChain_snd _ _ _
    rcases hcomp ck hc with rfl | rfl
    · exact not_chainKeyAt_eq_of_root (n := 0) hroot (by simp) (kdfCk_snd_inj heq)
    · exact not_chainKeyAt_eq_of_root (n := 0) hroot (by simp) (kdfCk_snd_inj heq)
  · have hle := saltDepth_le_of_rootDescends hr
    rcases hcomp rk hc with rfl | rfl <;> simp at hle
  · rcases hcomp dhsA hc with h | h
    · have := congrArg saltDepth h; simp at this
    · have := (rnd_inj_pair h).1; omega
  · rcases hcomp dhsA hc with h | h
    · have := congrArg saltDepth h; simp at this
    · have := (rnd_inj_pair h).1; omega

/-- Dropping `ExposedRK` from `Compromised` refutes `ForwardSecrecy`: leaking a pre-ratchet root key
and the peer's ratchet DH secret exposes the next chain's message key. -/
theorem not_ForwardSecrecy_compromisedWithoutRK :
    ¬ ForwardSecrecyWithout (some .rk) := by
  intro hfs
  have hq := hfs trRK trRK_reach mkB0 trRK_msgKey (predKnows_of_msgKey trRK_msgKey trRK_knows_mkB0)
  have hcomp_dhs : ∀ k, (tracePredicatesWithout trRK (some .rk)).Compromised k →
      ∃ s i, trRK.EventLogged (TREvent.ExposedDHs s k i) := by
    intro k hc
    have hexp : ExposedKey trRK k :=
      (compromised_iff_exposedKey_of_evIdx trRK_compromise_indices).mp
        (compromisedWithout_imp_real hc)
    have hno_tr : ∀ {ev : TREvent}, isAnyTRExposure ev = true →
        ev ≠ .ExposedRK (stA0.sessionInfo "alice") stA0.rk stA0.rIdx →
        ev ≠ .ExposedDHs (stA0.sessionInfo "alice") stA0.dhs stA0.rIdx →
        ¬ trRK.EventLogged ev := by
      intro ev hexp_ev hne1 hne2 hlog
      dsimp only [trRK, Symbolic.Proofs.Tests.Shared.ExplanationTightness.CompromisedTraces.trRK1,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeDhsTr,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeRkTr] at hlog
      rcases Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_ev
          (Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_other rfl hlog) with hlog | heq
      · rcases Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_ev
            (Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_other rfl hlog) with hlog | heq
        · exact not_tr_logged
            Symbolic.Proofs.Tests.Shared.ExplanationTightness.CompromisedTraces.t10_trExposure_indices
            hexp_ev hlog
        · exact hne1 heq.symm
      · exact hne2 heq.symm
    rcases hc with ⟨hne, _⟩ | ⟨_, h⟩ | ⟨_, s, ns, i, h⟩ | ⟨_, s, nr, i, h⟩ | ⟨_, s, n, i, h⟩ |
        ⟨_, h⟩ | ⟨_, _, h⟩
    · exact False.elim (hne rfl)
    · exact h
    · exact False.elim (hno_tr rfl (by intro h'; cases h') (by intro h'; cases h') h)
    · exact False.elim (hno_tr rfl (by intro h'; cases h') (by intro h'; cases h') h)
    · exact False.elim (hno_tr rfl (by intro h'; cases h') (by intro h'; cases h') h)
    · exact False.elim (not_handshakeRootCompromised_of_evIdx trRK_compromise_indices h)
    · exact False.elim (not_brokenDH_of_evIdx trRK_compromise_indices h)
  rcases hq with hc | ⟨ck, hd, hc⟩ | ⟨rk, ck, hdc, hd, hc⟩
  · exact (not_dhs_excuses_msgKey (Knows := fun t => t.AttackerKnows trRK)
      trRK_reach trRK_msgKey (.inl (hcomp_dhs mkB0 hc))).1 rfl
  · exact (not_dhs_excuses_msgKey (Knows := fun t => t.AttackerKnows trRK)
      trRK_reach trRK_msgKey (.inl (hcomp_dhs ck hc))).2.1 hd
  · exact (not_dhs_excuses_msgKey (Knows := fun t => t.AttackerKnows trRK)
      trRK_reach trRK_msgKey (.inl (hcomp_dhs rk hc))).2.2 ck ⟨hdc, hd⟩

/-- Dropping `ExposedDHs` from `Compromised` refutes `PostCompromiseSecurity`: leaking a pre-heal
root key and a healing DH secret exposes the post-heal message key. -/
theorem not_PostCompromiseSecurity_compromisedWithoutDHs :
    ¬ PostCompromiseSecurityWithout (some .dhs) := by
  intro hpcs
  have hstep : DerivesMsgKey (createChain stA0.rk (dhPk dhsA) dhsB1).2 mkB0 := by
    refine ⟨0, ?_⟩
    show (kdfCk stB2.cks).2 = (kdfCk (chainKeyAt (createChain stA0.rk (dhPk dhsA) dhsB1).2 0)).2
    rw [stB2_cks_eq]; rfl
  have hcomp_rk : ∀ k, (tracePredicatesWithout trRK (some .dhs)).Compromised k → k = stA0.rk := by
    intro k hc
    have hexp : ExposedKey trRK k :=
      (compromised_iff_exposedKey_of_evIdx trRK_compromise_indices).mp
        (compromisedWithout_imp_real hc)
    rcases trRK_exposedKey hexp with rfl | rfl
    · rfl
    · exfalso
      have hpeel : ∀ {ev : TREvent}, isAnyTRExposure ev = true → trRK.EventLogged ev →
          ev = .ExposedRK (stA0.sessionInfo "alice") stA0.rk stA0.rIdx ∨
          ev = .ExposedDHs (stA0.sessionInfo "alice") stA0.dhs stA0.rIdx := by
        intro ev hexp_ev hlog
        dsimp only [trRK, Symbolic.Proofs.Tests.Shared.ExplanationTightness.CompromisedTraces.trRK1,
          Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeDhsTr,
          Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeRkTr] at hlog
        rcases Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_ev
            (Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_other rfl hlog) with hlog | heq
        · rcases Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_ev
              (Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_other rfl hlog) with hlog | heq
          · exact False.elim (not_tr_logged
              Symbolic.Proofs.Tests.Shared.ExplanationTightness.CompromisedTraces.t10_trExposure_indices
              hexp_ev hlog)
          · exact .inl heq.symm
        · exact .inr heq.symm
      rcases hc with ⟨_, s, i, j, hj⟩ | ⟨hne, _⟩ | ⟨_, s, ns, i, h⟩ | ⟨_, s, nr, i, h⟩ |
          ⟨_, s, n, i, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩
      · rcases hpeel rfl ⟨j, hj⟩ with heq | heq
        · injection heq with _ hk _
          have hsd := congrArg saltDepth hk; simp at hsd
        · cases heq
      · exact hne rfl
      · rcases hpeel rfl h with heq | heq <;> cases heq
      · rcases hpeel rfl h with heq | heq <;> cases heq
      · rcases hpeel rfl h with heq | heq <;> cases heq
      · exact not_handshakeRootCompromised_of_evIdx trRK_compromise_indices h
      · exact not_brokenDH_of_evIdx trRK_compromise_indices h
  rcases hpcs trRK trRK_reach mkB0 stA0.rk dhsB1 dhsA trRK_msgKey
      (predKnows_of_msgKey trRK_msgKey trRK_knows_mkB0)
      trRK_honestDH_dhsB1 trRK_honestDH_dhsA (.inl hstep) with
    hc | ⟨ck, ⟨steps, heq⟩, hc⟩ | ⟨rk, ck, hr, _, _, hc⟩ | ⟨_, hc | hc⟩
  · have := congrArg saltDepth (hcomp_rk mkB0 hc); simp at this
  · rw [hcomp_rk ck hc] at heq
    exact not_chainKeyAt_eq_of_root (n := 0) (isChainRoot_createChain_snd _ _ _)
      (by simp) (kdfCk_snd_inj heq)
  · rw [hcomp_rk rk hc] at hr
    have hle := saltDepth_le_of_rootDescends hr
    simp at hle
  · have := congrArg saltDepth (hcomp_rk dhsB1 hc); simp at this
  · have := congrArg saltDepth (hcomp_rk dhsA hc); simp at this

/-- On every reachable trace, dropping `ExposedDHs` from `Compromised` preserves `FSQueryP` because
no root key, chain key, or message-key seed in a `MessageKey` genealogy is a `rnd` DH secret. -/
theorem fsQuery_compromisedWithoutDHs_iff (tr : ExecTrace) (hR : tr.Reachable reachability) :
    FSQueryP (tracePredicatesWithout tr (some .dhs)) ↔ FSQueryP (mkTestTracePredicates tr) := by
  constructor
  · exact fsQuery_mono_compromised (fun _ => id) (fun _ => id)
      (fun _ => compromisedWithout_imp_real)
  · intro hfs mk hmk hknow
    rcases hfs mk hmk hknow with hc | ⟨ck, hd, hc⟩ | ⟨rk, ck, hdc, hd, hc⟩
    · exact .inl (compromisedWithout_dhs_of_real_of_not_dhs hc
        (fun s i he => (not_dhs_excuses_msgKey (Knows := fun t => t.AttackerKnows tr)
          hR hmk (.inl ⟨s, i, he⟩)).1 rfl))
    · exact .inr (.inl ⟨ck, hd, compromisedWithout_dhs_of_real_of_not_dhs hc
        (fun s i he => (not_dhs_excuses_msgKey (Knows := fun t => t.AttackerKnows tr)
          hR hmk (.inl ⟨s, i, he⟩)).2.1 hd)⟩)
    · exact .inr (.inr ⟨rk, ck, hdc, hd, compromisedWithout_dhs_of_real_of_not_dhs hc
        (fun s i he => (not_dhs_excuses_msgKey (Knows := fun t => t.AttackerKnows tr)
          hR hmk (.inl ⟨s, i, he⟩)).2.2 ck ⟨hdc, hd⟩)⟩)

theorem forwardSecrecy_compromisedWithoutDHs_of_real (h : ForwardSecrecy) :
    ForwardSecrecyWithout (some .dhs) :=
  fun tr hR => (fsQuery_compromisedWithoutDHs_iff tr hR).mpr ((fsQuery_iff_test tr _).mp (h tr hR))

/-- Dropping `ExposedCKs` from `Compromised` refutes `ForwardSecrecy`. -/
theorem not_ForwardSecrecy_compromisedWithoutCKs :
    ¬ ForwardSecrecyWithout (some .cks) := by
  intro hfs
  refine not_fsQuery_of_no_compromised (P := tracePredicatesWithout trCK (some .cks)) trCK_msgKey
    (predKnows_of_msgKey trCK_msgKey trCK_knows_mkA0) ?_ (hfs trCK trCK_reach)
  intro k hc
  rcases hc with ⟨_, s, i, h⟩ | ⟨_, s, i, h⟩ | ⟨hne, _⟩ | ⟨_, s, nr, i, h⟩ | ⟨_, s, n, i, h⟩ |
      ⟨_, h⟩ | ⟨_, _, h⟩
  · exact not_tr_logged trCK_nonCks_indices rfl h
  · exact not_tr_logged trCK_nonCks_indices rfl h
  · exact hne rfl
  · exact not_tr_logged trCK_nonCks_indices rfl h
  · exact not_tr_logged trCK_nonCks_indices rfl h
  · exact not_handshakeRootCompromised_of_evIdx trCK_compromise_indices h
  · exact not_brokenDH_of_evIdx trCK_compromise_indices h

/-- Dropping `ExposedCKr` from `Compromised` refutes `ForwardSecrecy`. -/
theorem not_ForwardSecrecy_compromisedWithoutCKr :
    ¬ ForwardSecrecyWithout (some .ckr) := by
  intro hfs
  refine not_fsQuery_of_no_compromised (P := tracePredicatesWithout trCKr (some .ckr)) trCKr_msgKey
    (predKnows_of_msgKey trCKr_msgKey trCKr_knows_mkCKr) ?_ (hfs trCKr trCKr_reach)
  intro k hc
  rcases hc with ⟨_, s, i, h⟩ | ⟨_, s, i, h⟩ | ⟨_, s, ns, i, h⟩ | ⟨hne, _⟩ | ⟨_, s, n, i, h⟩ |
      ⟨_, h⟩ | ⟨_, _, h⟩
  · exact not_tr_logged trCKr_nonCkr_indices rfl h
  · exact not_tr_logged trCKr_nonCkr_indices rfl h
  · exact not_tr_logged trCKr_nonCkr_indices rfl h
  · exact hne rfl
  · exact not_tr_logged trCKr_nonCkr_indices rfl h
  · exact not_handshakeRootCompromised_of_evIdx trCKr_compromise_indices h
  · exact not_brokenDH_of_evIdx trCKr_compromise_indices h

/-- Dropping `ExposedMK` from `Compromised` refutes `ForwardSecrecy`. -/
theorem not_ForwardSecrecy_compromisedWithoutMK :
    ¬ ForwardSecrecyWithout (some .mk) := by
  intro hfs
  refine not_fsQuery_of_no_compromised (P := tracePredicatesWithout trMK (some .mk)) trMK_msgKey
    (predKnows_of_msgKey trMK_msgKey trMK_knows_seedB0) ?_ (hfs trMK trMK_reach)
  intro k hc
  rcases hc with ⟨_, s, i, h⟩ | ⟨_, s, i, h⟩ | ⟨_, s, ns, i, h⟩ | ⟨_, s, nr, i, h⟩ | ⟨hne, _⟩ |
      ⟨_, h⟩ | ⟨_, _, h⟩
  · exact not_tr_logged trMK_nonMk_indices rfl h
  · exact not_tr_logged trMK_nonMk_indices rfl h
  · exact not_tr_logged trMK_nonMk_indices rfl h
  · exact not_tr_logged trMK_nonMk_indices rfl h
  · exact hne rfl
  · exact not_handshakeRootCompromised_of_evIdx trMK_compromise_indices h
  · exact not_brokenDH_of_evIdx trMK_compromise_indices h

/-- Dropping `HandshakeRootCompromised` from `Compromised` refutes `ForwardSecrecy`: after
`compromiseIK "bob"` and a forged prekey bundle, the attacker derives Alice's initial sending chain
and message-0 seed from `keys.rk`. -/
theorem not_ForwardSecrecy_compromisedWithoutHRC :
    ¬ ForwardSecrecyWithout (some .hrc) := by
  intro hfs
  refine not_fsQuery_of_no_compromised (P := tracePredicatesWithout trHrcRk (some .hrc))
    trHrcRk_msgKey (predKnows_of_msgKey trHrcRk_msgKey trHrcRk_knows_mkHrcRk) ?_
    (hfs trHrcRk trHrcRk_reach)
  intro k hc
  rcases hc with ⟨_, s, i, h⟩ | ⟨_, s, i, h⟩ | ⟨_, s, ns, i, h⟩ | ⟨_, s, nr, i, h⟩ |
      ⟨_, s, n, i, h⟩ | ⟨hne, _⟩ | ⟨_, _, h⟩
  · exact not_exposedKey_of_trEvIdx trHrcRk_trExposure_indices (.inl ⟨s, i, h⟩)
  · exact not_exposedKey_of_trEvIdx trHrcRk_trExposure_indices (.inr (.inl ⟨s, i, h⟩))
  · exact not_exposedKey_of_trEvIdx trHrcRk_trExposure_indices (.inr (.inr (.inl ⟨s, ns, i, h⟩)))
  · exact not_exposedKey_of_trEvIdx trHrcRk_trExposure_indices
      (.inr (.inr (.inr (.inl ⟨s, nr, i, h⟩))))
  · exact not_exposedKey_of_trEvIdx trHrcRk_trExposure_indices
      (.inr (.inr (.inr (.inr ⟨s, n, i, h⟩))))
  · exact hne rfl
  · exact not_logged trHrcRk_brokenDH_indices (e := PQXDHEvent.BrokenDH) rfl h

/-- Dropping `honestDH k ∧ tr.EventLogged PQXDHEvent.BrokenDH` from `Compromised` refutes
`PostCompromiseSecurity` when a pre-heal root key is exposed and `breakDH`/`invertDH` inverts the
healing ratchet key after the handshake. -/
theorem not_PostCompromiseSecurity_compromisedWithoutBDH :
    ¬ PostCompromiseSecurityWithout (some .bdh) := by
  intro hpcs
  refine not_pcsQuery_trBDH (P := tracePredicatesWithout trBDH (some .bdh)) trBDH_msgKey
    (predKnows_of_msgKey trBDH_msgKey trBDH_knows_mkBDH) trBDH_honestDH_dhsA ?_
    (hpcs trBDH trBDH_reach)
  intro k hc
  rcases hc with ⟨_, s, i, h⟩ | ⟨_, s, i, h⟩ | ⟨_, s, ns, i, h⟩ | ⟨_, s, nr, i, h⟩ |
      ⟨_, s, n, i, h⟩ | ⟨_, ⟨keys, j, hhk, hkb⟩, hall⟩ | ⟨hne, _⟩
  · exact .inl (trBDH_exposedRK_eq h)
  · exact False.elim (not_tr_logged trBDH_nonRk_indices rfl h)
  · exact False.elim (not_tr_logged trBDH_nonRk_indices rfl h)
  · exact False.elim (not_tr_logged trBDH_nonRk_indices rfl h)
  · exact False.elim (not_tr_logged trBDH_nonRk_indices rfl h)
  · exact False.elim (trBDH_not_handshakeExcusedAt (hall keys j hhk hkb))
  · exact False.elim (hne rfl)

/-- On every reachable trace, dropping `honestDH k ∧ tr.EventLogged PQXDHEvent.BrokenDH` from
`Compromised` preserves `FSQueryP` because honest DH secrets are `rnd` terms distinct from root
keys, chain keys, and message-key seeds. -/
theorem fsQuery_compromisedWithoutBDH_iff (tr : ExecTrace) (hR : tr.Reachable reachability) :
    FSQueryP (tracePredicatesWithout tr (some .bdh)) ↔ FSQueryP (mkTestTracePredicates tr) := by
  constructor
  · exact fsQuery_mono_compromised (fun _ => id) (fun _ => id)
      (fun _ => compromisedWithout_imp_real)
  · intro hfs mk hmk hknow
    rcases hfs mk hmk hknow with hc | ⟨ck, hd, hc⟩ | ⟨rk, ck, hdc, hd, hc⟩
    · exact .inl (compromisedWithout_bdh_of_real_of_not_bdh hc
        (fun hhdh _ => (not_dhs_excuses_msgKey (Knows := fun t => t.AttackerKnows tr)
          hR hmk (.inr hhdh)).1 rfl))
    · exact .inr (.inl ⟨ck, hd, compromisedWithout_bdh_of_real_of_not_bdh hc
        (fun hhdh _ => (not_dhs_excuses_msgKey (Knows := fun t => t.AttackerKnows tr)
          hR hmk (.inr hhdh)).2.1 hd)⟩)
    · exact .inr (.inr ⟨rk, ck, hdc, hd, compromisedWithout_bdh_of_real_of_not_bdh hc
        (fun hhdh _ => (not_dhs_excuses_msgKey (Knows := fun t => t.AttackerKnows tr)
          hR hmk (.inr hhdh)).2.2 ck ⟨hdc, hd⟩)⟩)

theorem forwardSecrecy_compromisedWithoutBDH_of_real (h : ForwardSecrecy) :
    ForwardSecrecyWithout (some .bdh) :=
  fun tr hR => (fsQuery_compromisedWithoutBDH_iff tr hR).mpr ((fsQuery_iff_test tr _).mp (h tr hR))

end TopLevelDisjuncts

/-! ## Sub-Disjuncts of `HandshakeRootCompromised` -/

section HandshakeRootCompromisedMutants

/-- `HandshakeRootCompromised` parameterized by handshake-key predicate `HK`, handshake-excuse
predicate `HE`, and key-block selector `KB`. -/
def HandshakeRootCompromisedWith
    (HK : ExecTrace → Nat → HandshakeKeys → Prop)
    (HE : ExecTrace → Nat → Prop)
    (KB : HandshakeKeys → Bytes → Prop)
    (tr : ExecTrace) (k : Bytes) : Prop :=
  (∃ keys j, HK tr j keys ∧ KB keys k) ∧
  (∀ keys j, HK tr j keys → KB keys k → HE tr j)

theorem handshakeRootCompromisedWith_real :
    HandshakeRootCompromisedWith HandshakeKeysAt HandshakeWasCompromisedAt
      (fun keys k => k = keys.rk ∨ k = keys.ck) = HandshakeRootCompromised := rfl

/-- `mkTestTracePredicates` with `HandshakeRootCompromised` replaced by `HRC`. -/
def tracePredicatesWithHRC (HRC : ExecTrace → Bytes → Prop) (tr : ExecTrace) : TestTracePredicates :=
  let honestDH (d : Bytes) : Prop :=
    (∃ s i, tr.EventLogged (TREvent.HonestDH s d i)) ∨
    (∃ me st idx, StateStoredAt me st idx tr ∧ st.dhs = d)
  { mkTestTracePredicates tr with
    Compromised := fun k =>
      (∃ s i, tr.EventLogged (TREvent.ExposedRK s k i)) ∨
      (∃ s i, tr.EventLogged (TREvent.ExposedDHs s k i)) ∨
      (∃ s ns i, tr.EventLogged (TREvent.ExposedCKs s k ns i)) ∨
      (∃ s nr i, tr.EventLogged (TREvent.ExposedCKr s k nr i)) ∨
      (∃ s n i, tr.EventLogged (TREvent.ExposedMK s k n i)) ∨
      HRC tr k ∨
      (honestDH k ∧ tr.EventLogged PQXDHEvent.BrokenDH) }

def ForwardSecrecyWithHRC (HRC : ExecTrace → Bytes → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → FSQueryP (tracePredicatesWithHRC HRC tr)

theorem tracePredicatesWithHRC_real (tr : ExecTrace) :
    tracePredicatesWithHRC HandshakeRootCompromised tr = mkTestTracePredicates tr := rfl

theorem forwardSecrecyWithHRC_real :
    ForwardSecrecyWithHRC HandshakeRootCompromised ↔ ForwardSecrecy := by
  simp only [ForwardSecrecyWithHRC, tracePredicatesWithHRC_real, ForwardSecrecy, fsQuery_iff_test]

def HandshakeRootCompromised_withoutRk (tr : ExecTrace) (k : Bytes) : Prop :=
  HandshakeRootCompromisedWith HandshakeKeysAt HandshakeWasCompromisedAt (fun keys k => k = keys.ck) tr k

def HandshakeRootCompromised_withoutCk (tr : ExecTrace) (k : Bytes) : Prop :=
  HandshakeRootCompromisedWith HandshakeKeysAt HandshakeWasCompromisedAt (fun keys k => k = keys.rk) tr k

/-- `HandshakeWasCompromisedAt` restricted to the `BobDone` disjunct. -/
def HandshakeExcusedAt_withoutAlice (tr : ExecTrace) (j : Nat) : Prop :=
  ∃ b a ikB ikA spk pqpk opk ek ct keys,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) j ∧
      BobHandshakeWasCompromised b a ikB ikA spk pqpk opk j tr

/-- `HandshakeWasCompromisedAt` restricted to the `AliceDone` disjunct. -/
def HandshakeExcusedAt_withoutBob (tr : ExecTrace) (j : Nat) : Prop :=
  ∃ a b ikA ikB spk pqpk opk ek ct keys,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) j ∧
      AliceHandshakeWasCompromised b ikB spk pqpk j tr

theorem handshakeExcusedAt_real (tr : ExecTrace) (j : Nat) :
    (HandshakeExcusedAt_withoutBob tr j ∨ HandshakeExcusedAt_withoutAlice tr j) =
      HandshakeWasCompromisedAt tr j := rfl

def HandshakeRootCompromised_withoutAliceExcuse (tr : ExecTrace) (k : Bytes) : Prop :=
  HandshakeRootCompromisedWith HandshakeKeysAt HandshakeExcusedAt_withoutAlice
    (fun keys k => k = keys.rk ∨ k = keys.ck) tr k

def HandshakeRootCompromised_withoutBobExcuse (tr : ExecTrace) (k : Bytes) : Prop :=
  HandshakeRootCompromisedWith HandshakeKeysAt HandshakeExcusedAt_withoutBob
    (fun keys k => k = keys.rk ∨ k = keys.ck) tr k

/-- `HandshakeKeysAt` restricted to the `BobDone` disjunct. -/
def HandshakeKeysAt_withoutAlice (tr : ExecTrace) (j : Nat) (keys : HandshakeKeys) : Prop :=
  ∃ b a ikB ikA spk pqpk opk ek ct,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) j

/-- `HandshakeKeysAt` restricted to the `AliceDone` disjunct. -/
def HandshakeKeysAt_withoutBob (tr : ExecTrace) (j : Nat) (keys : HandshakeKeys) : Prop :=
  ∃ a b ikA ikB spk pqpk opk ek ct,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) j

theorem handshakeKeysAt_real (tr : ExecTrace) (j : Nat) (keys : HandshakeKeys) :
    (HandshakeKeysAt_withoutBob tr j keys ∨ HandshakeKeysAt_withoutAlice tr j keys) ↔
      HandshakeKeysAt tr j keys := by
  constructor
  · rintro (⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, h⟩ |
        ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, h⟩)
    · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, h⟩⟩
    · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct, h⟩⟩
  · rintro ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, h⟩ | ⟨ek, ct, h⟩⟩
    · exact .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, h⟩
    · exact .inr ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, h⟩

def HandshakeRootCompromised_withoutAliceKeys (tr : ExecTrace) (k : Bytes) : Prop :=
  HandshakeRootCompromisedWith HandshakeKeysAt_withoutAlice HandshakeWasCompromisedAt
    (fun keys k => k = keys.rk ∨ k = keys.ck) tr k

def HandshakeRootCompromised_withoutBobKeys (tr : ExecTrace) (k : Bytes) : Prop :=
  HandshakeRootCompromisedWith HandshakeKeysAt_withoutBob HandshakeWasCompromisedAt
    (fun keys k => k = keys.rk ∨ k = keys.ck) tr k

abbrev ForwardSecrecy_hrcWithoutRk : Prop :=
  ForwardSecrecyWithHRC HandshakeRootCompromised_withoutRk

abbrev ForwardSecrecy_hrcWithoutCk : Prop :=
  ForwardSecrecyWithHRC HandshakeRootCompromised_withoutCk

abbrev ForwardSecrecy_hrcWithoutAliceExcuse : Prop :=
  ForwardSecrecyWithHRC HandshakeRootCompromised_withoutAliceExcuse

abbrev ForwardSecrecy_hrcWithoutBobExcuse : Prop :=
  ForwardSecrecyWithHRC HandshakeRootCompromised_withoutBobExcuse

abbrev ForwardSecrecy_hrcWithoutAliceKeys : Prop :=
  ForwardSecrecyWithHRC HandshakeRootCompromised_withoutAliceKeys

abbrev ForwardSecrecy_hrcWithoutBobKeys : Prop :=
  ForwardSecrecyWithHRC HandshakeRootCompromised_withoutBobKeys

private theorem compWithHRC_imp_hrc_of_no_tr_no_bdh {HRC : ExecTrace → Bytes → Prop}
    {tr : ExecTrace} {k : Bytes}
    (htr : trEvIdx tr isAnyTRExposure = [])
    (hbdh : evIdx tr isBrokenDH = [])
    (hc : (tracePredicatesWithHRC HRC tr).Compromised k) :
    HRC tr k := by
  rcases hc with ⟨s, i, h⟩ | ⟨s, i, h⟩ | ⟨s, ns, i, h⟩ | ⟨s, nr, i, h⟩ | ⟨s, n, i, h⟩ |
      h | ⟨_, h⟩
  · exact False.elim (not_exposedKey_of_trEvIdx htr (.inl ⟨s, i, h⟩))
  · exact False.elim (not_exposedKey_of_trEvIdx htr (.inr (.inl ⟨s, i, h⟩)))
  · exact False.elim (not_exposedKey_of_trEvIdx htr (.inr (.inr (.inl ⟨s, ns, i, h⟩))))
  · exact False.elim (not_exposedKey_of_trEvIdx htr (.inr (.inr (.inr (.inl ⟨s, nr, i, h⟩)))))
  · exact False.elim (not_exposedKey_of_trEvIdx htr (.inr (.inr (.inr (.inr ⟨s, n, i, h⟩)))))
  · exact h
  · exact False.elim (not_logged hbdh (e := PQXDHEvent.BrokenDH) rfl h)

/-- Dropping `k = keys.rk` in `HandshakeRootCompromised` refutes `ForwardSecrecy`: Alice's initial
sending chain derives from `keys.rk`, not `keys.ck`. -/
theorem not_ForwardSecrecy_hrcWithoutRk :
    ¬ ForwardSecrecy_hrcWithoutRk := by
  intro hfs
  have hq := hfs trHrcRk trHrcRk_reach mkHrcRk trHrcRk_msgKey
    (predKnows_of_msgKey trHrcRk_msgKey trHrcRk_knows_mkHrcRk)
  have hcomp_ck : ∀ k,
      (tracePredicatesWithHRC HandshakeRootCompromised_withoutRk trHrcRk).Compromised k →
      k = trIKB_out.keys.ck := by
    intro k hc
    rcases compWithHRC_imp_hrc_of_no_tr_no_bdh trHrcRk_trExposure_indices trHrcRk_brokenDH_indices
        hc with ⟨⟨keys, j, hhk, rfl⟩, _⟩
    have := (handshakeKeysAt_of_aliceSingleton trHrcRk_aliceDone_indices trHrcRk_bobDone_indices
      trHrcRk_aliceDone_at hhk).2
    rw [this]
  obtain ⟨ikm₀, hikm₀⟩ : ∃ ikm, trIKB_out.keys = pqxdhKdf ikm := ⟨_, rfl⟩
  have hck_eq : trIKB_out.keys.ck = (pqxdhKdf ikm₀).ck := congrArg HandshakeKeys.ck hikm₀
  have hrk_eq : trIKB_out.keys.rk = (pqxdhKdf ikm₀).rk := congrArg HandshakeKeys.rk hikm₀
  rcases hq with hc | ⟨ck, ⟨steps, heq⟩, hc⟩ | ⟨rk, ck, ⟨rk', pk, sk, hdesc, rfl⟩, ⟨steps, heq⟩, hc⟩
  · have h1 := hcomp_ck mkHrcRk hc
    rw [hck_eq] at h1
    exact pqxdhKdf_ck_ne_kdfCk_snd ikm₀ _ h1.symm
  · have h1 := hcomp_ck ck hc
    rw [h1, hck_eq] at heq
    have hroot_eq := (chainKeyAt_root_inj (n₁ := 0) (isChainRoot_createChain_snd _ _ _)
      (isChainRoot_pqxdhKdf_ck ikm₀) (kdfCk_snd_inj heq)).1
    exact pqxdhKdf_ck_ne_createChain_snd ikm₀ _ _ _ hroot_eq.symm
  · have h1 := hcomp_ck rk hc
    have hroot_eq := (chainKeyAt_root_inj (n₁ := 0) (isChainRoot_createChain_snd _ _ _)
      (isChainRoot_createChain_snd rk' pk sk) (kdfCk_snd_inj heq)).1
    have hrk' : trIKB_out.keys.rk = rk' := createChain_snd_inj hroot_eq
    rw [h1, hck_eq, ← hrk', hrk_eq] at hdesc
    have hck_rk := eq_of_rootDescends_pqxdhKdf_rk hdesc
    exact (pqxdhKdf_rk_ne_ck ikm₀ ikm₀) hck_rk.symm

/-- Dropping `k = keys.ck` in `HandshakeRootCompromised` refutes `ForwardSecrecy`: on a forged
bundle, Alice's initial receiving chain key is `keys.ck` directly without a DH ratchet step. -/
theorem not_ForwardSecrecy_hrcWithoutCk :
    ¬ ForwardSecrecy_hrcWithoutCk := by
  intro hfs
  have hq := hfs trHrcCk trHrcCk_reach mkHrcCk trHrcCk_msgKey
    (predKnows_of_msgKey trHrcCk_msgKey trHrcCk_knows_mkHrcCk)
  have hcomp_rk : ∀ k,
      (tracePredicatesWithHRC HandshakeRootCompromised_withoutCk trHrcCk).Compromised k →
      k = trIKB_out.keys.rk := by
    intro k hc
    rcases compWithHRC_imp_hrc_of_no_tr_no_bdh trHrcCk_trExposure_indices trHrcCk_brokenDH_indices
        hc with ⟨⟨keys, j, hhk, rfl⟩, _⟩
    have := (handshakeKeysAt_of_aliceSingleton trHrcCk_aliceDone_indices trHrcCk_bobDone_indices
      trHrcCk_aliceDone_at hhk).2
    rw [this]
  obtain ⟨ikm₀, hikm₀⟩ : ∃ ikm, trIKB_out.keys = pqxdhKdf ikm := ⟨_, rfl⟩
  have hck_eq : trIKB_out.keys.ck = (pqxdhKdf ikm₀).ck := congrArg HandshakeKeys.ck hikm₀
  have hrk_eq : trIKB_out.keys.rk = (pqxdhKdf ikm₀).rk := congrArg HandshakeKeys.rk hikm₀
  rcases hq with hc | ⟨ck, ⟨steps, heq⟩, hc⟩ | ⟨rk, ck, ⟨rk', pk, sk, _, rfl⟩, ⟨steps, heq⟩, hc⟩
  · have h1 := hcomp_rk mkHrcCk hc
    rw [hrk_eq] at h1
    exact pqxdhKdf_rk_ne_kdfCk_snd ikm₀ _ h1.symm
  · have h1 := hcomp_rk ck hc
    rw [h1, hrk_eq] at heq
    have hinj : (pqxdhKdf ikm₀).ck = chainKeyAt (pqxdhKdf ikm₀).rk steps := by
      rw [← hck_eq]; exact kdfCk_snd_inj heq
    have hroot_eq := (chainKeyAt_root_inj (n₁ := 0) (isChainRoot_pqxdhKdf_ck ikm₀)
      (isChainRoot_pqxdhKdf_rk ikm₀) hinj).1
    exact (pqxdhKdf_rk_ne_ck ikm₀ ikm₀) hroot_eq.symm
  · have hinj : (pqxdhKdf ikm₀).ck = chainKeyAt (createChain rk' pk sk).2 steps := by
      rw [← hck_eq]; exact kdfCk_snd_inj heq
    have hroot_eq := (chainKeyAt_root_inj (n₁ := 0) (isChainRoot_pqxdhKdf_ck ikm₀)
      (isChainRoot_createChain_snd rk' pk sk) hinj).1
    exact pqxdhKdf_ck_ne_createChain_snd ikm₀ rk' pk sk hroot_eq

/-- Dropping the `AliceDone` disjunct of `HandshakeWasCompromisedAt` inside
`HandshakeRootCompromised` refutes `ForwardSecrecy`. -/
theorem not_ForwardSecrecy_hrcWithoutAliceExcuse :
    ¬ ForwardSecrecy_hrcWithoutAliceExcuse := by
  intro hfs
  refine not_fsQuery_of_no_compromised
    (P := tracePredicatesWithHRC HandshakeRootCompromised_withoutAliceExcuse trHrcRk)
    trHrcRk_msgKey (predKnows_of_msgKey trHrcRk_msgKey trHrcRk_knows_mkHrcRk) ?_
    (hfs trHrcRk trHrcRk_reach)
  intro k hc
  rcases compWithHRC_imp_hrc_of_no_tr_no_bdh trHrcRk_trExposure_indices trHrcRk_brokenDH_indices
      hc with ⟨⟨keys, j, hhk, hkb⟩, hall⟩
  rcases hall keys j hhk hkb with ⟨_, _, _, _, _, _, _, _, _, _, hj, _⟩
  exact not_logged trHrcRk_bobDone_indices (e := PQXDHEvent.BobDone ..) rfl ⟨j, hj⟩

/-- Dropping the `BobDone` disjunct of `HandshakeWasCompromisedAt` inside `HandshakeRootCompromised`
refutes `ForwardSecrecy`. -/
theorem not_ForwardSecrecy_hrcWithoutBobExcuse :
    ¬ ForwardSecrecy_hrcWithoutBobExcuse := by
  intro hfs
  refine not_fsQuery_of_no_compromised
    (P := tracePredicatesWithHRC HandshakeRootCompromised_withoutBobExcuse trIKA)
    trIKA_msgKey (predKnows_of_msgKey trIKA_msgKey trIKA_knows_mkIKA) ?_
    (hfs trIKA trIKA_reach)
  intro k hc
  rcases compWithHRC_imp_hrc_of_no_tr_no_bdh trIKA_trExposure_indices trIKA_brokenDH_indices
      hc with ⟨⟨keys, j, hhk, hkb⟩, hall⟩
  rcases hall keys j hhk hkb with ⟨_, _, _, _, _, _, _, _, _, _, hj, _⟩
  exact not_logged trIKA_aliceDone_indices (e := PQXDHEvent.AliceDone ..) rfl ⟨j, hj⟩

/-- Dropping the `AliceDone` disjunct of `HandshakeKeysAt` inside `HandshakeRootCompromised` refutes
`ForwardSecrecy`. -/
theorem not_ForwardSecrecy_hrcWithoutAliceKeys :
    ¬ ForwardSecrecy_hrcWithoutAliceKeys := by
  intro hfs
  refine not_fsQuery_of_no_compromised
    (P := tracePredicatesWithHRC HandshakeRootCompromised_withoutAliceKeys trHrcRk)
    trHrcRk_msgKey (predKnows_of_msgKey trHrcRk_msgKey trHrcRk_knows_mkHrcRk) ?_
    (hfs trHrcRk trHrcRk_reach)
  intro k hc
  rcases compWithHRC_imp_hrc_of_no_tr_no_bdh trHrcRk_trExposure_indices trHrcRk_brokenDH_indices
      hc with ⟨⟨_, j, ⟨_, _, _, _, _, _, _, _, _, hj⟩, _⟩, _⟩
  exact not_logged trHrcRk_bobDone_indices (e := PQXDHEvent.BobDone ..) rfl ⟨j, hj⟩

/-- Dropping the `BobDone` disjunct of `HandshakeKeysAt` inside `HandshakeRootCompromised` refutes
`ForwardSecrecy`. -/
theorem not_ForwardSecrecy_hrcWithoutBobKeys :
    ¬ ForwardSecrecy_hrcWithoutBobKeys := by
  intro hfs
  refine not_fsQuery_of_no_compromised
    (P := tracePredicatesWithHRC HandshakeRootCompromised_withoutBobKeys trIKA)
    trIKA_msgKey (predKnows_of_msgKey trIKA_msgKey trIKA_knows_mkIKA) ?_
    (hfs trIKA trIKA_reach)
  intro k hc
  rcases compWithHRC_imp_hrc_of_no_tr_no_bdh trIKA_trExposure_indices trIKA_brokenDH_indices
      hc with ⟨⟨_, j, ⟨_, _, _, _, _, _, _, _, _, hj⟩, _⟩, _⟩
  exact not_logged trIKA_aliceDone_indices (e := PQXDHEvent.AliceDone ..) rfl ⟨j, hj⟩

end HandshakeRootCompromisedMutants

/-! ## Sub-Disjuncts of `honestDH` Inside `Compromised` -/

section BrokenDHHonestMutants

/-- `mkTestTracePredicates` with the `honestDH` predicate inside `Compromised`'s `BrokenDH` disjunct
replaced by `HDH tr` (leaving `TestTracePredicates.HonestDH` unchanged). -/
def tracePredicatesWithBDH (HDH : ExecTrace → Bytes → Prop) (tr : ExecTrace) : TestTracePredicates :=
  { mkTestTracePredicates tr with
    Compromised := fun k =>
      (∃ s i, tr.EventLogged (TREvent.ExposedRK s k i)) ∨
      (∃ s i, tr.EventLogged (TREvent.ExposedDHs s k i)) ∨
      (∃ s ns i, tr.EventLogged (TREvent.ExposedCKs s k ns i)) ∨
      (∃ s nr i, tr.EventLogged (TREvent.ExposedCKr s k nr i)) ∨
      (∃ s n i, tr.EventLogged (TREvent.ExposedMK s k n i)) ∨
      HandshakeRootCompromised tr k ∨
      (HDH tr k ∧ tr.EventLogged PQXDHEvent.BrokenDH) }

/-- The `TREvent.HonestDH` event disjunct of `honestDH`. -/
def HonestDHEventOnly (tr : ExecTrace) (d : Bytes) : Prop :=
  ∃ s i, tr.EventLogged (TREvent.HonestDH s d i)

/-- The stored-`TRState.dhs` disjunct of `honestDH`. -/
def HonestDHStoredOnly (tr : ExecTrace) (d : Bytes) : Prop :=
  ∃ me st idx, StateStoredAt me st idx tr ∧ st.dhs = d

theorem honestDH_real (tr : ExecTrace) (d : Bytes) :
    (HonestDHEventOnly tr d ∨ HonestDHStoredOnly tr d) = (mkTestTracePredicates tr).HonestDH d := rfl

theorem tracePredicatesWithBDH_real (tr : ExecTrace) :
    tracePredicatesWithBDH (fun tr d => HonestDHEventOnly tr d ∨ HonestDHStoredOnly tr d) tr =
      mkTestTracePredicates tr := rfl

def ForwardSecrecyWithBDH (HDH : ExecTrace → Bytes → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → FSQueryP (tracePredicatesWithBDH HDH tr)

def PostCompromiseSecurityWithBDH (HDH : ExecTrace → Bytes → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → PCSQueryP (tracePredicatesWithBDH HDH tr)

theorem forwardSecrecyWithBDH_real :
    ForwardSecrecyWithBDH (fun tr d => HonestDHEventOnly tr d ∨ HonestDHStoredOnly tr d) ↔
      ForwardSecrecy := by
  simp only [ForwardSecrecyWithBDH, tracePredicatesWithBDH_real, ForwardSecrecy, fsQuery_iff_test]

theorem postCompromiseSecurityWithBDH_real :
    PostCompromiseSecurityWithBDH (fun tr d => HonestDHEventOnly tr d ∨ HonestDHStoredOnly tr d) ↔
      PostCompromiseSecurity := by
  simp only [PostCompromiseSecurityWithBDH, tracePredicatesWithBDH_real, PostCompromiseSecurity,
    pcsQuery_iff_test]

/-- On every reachable trace, dropping the `TREvent.HonestDH` event disjunct of `honestDH` inside
`Compromised` preserves `Compromised`, because every transition logging `TREvent.HonestDH s d i`
also stores a `TRState` with `st.dhs = d`. -/
theorem compromised_bdhStoredOnly_iff (tr : ExecTrace) (hR : tr.Reachable reachability)
    (k : Bytes) :
    (tracePredicatesWithBDH HonestDHStoredOnly tr).Compromised k ↔
      (mkTestTracePredicates tr).Compromised k := by
  constructor
  · rintro (h | h | h | h | h | h | ⟨hst, hbrk⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr (.inl h))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨.inr hst, hbrk⟩)))))
  · rintro (h | h | h | h | h | h | ⟨⟨s, i, hev⟩ | hst, hbrk⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr (.inl h))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨honestDH_event_imp_stored hR hev, hbrk⟩)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨hst, hbrk⟩)))))

theorem fsQuery_bdhStoredOnly_iff (tr : ExecTrace) (hR : tr.Reachable reachability) :
    FSQueryP (tracePredicatesWithBDH HonestDHStoredOnly tr) ↔
      FSQueryP (mkTestTracePredicates tr) :=
  ⟨fsQuery_mono_compromised (fun _ => id) (fun _ => id)
    (fun k => (compromised_bdhStoredOnly_iff tr hR k).mp),
   fsQuery_mono_compromised (fun _ => id) (fun _ => id)
    (fun k => (compromised_bdhStoredOnly_iff tr hR k).mpr)⟩

theorem pcsQuery_bdhStoredOnly_iff (tr : ExecTrace) (hR : tr.Reachable reachability) :
    PCSQueryP (tracePredicatesWithBDH HonestDHStoredOnly tr) ↔
      PCSQueryP (mkTestTracePredicates tr) :=
  ⟨pcsQuery_mono_compromised (fun _ => id) (fun _ => id) (fun _ => id)
    (fun k => (compromised_bdhStoredOnly_iff tr hR k).mp),
   pcsQuery_mono_compromised (fun _ => id) (fun _ => id) (fun _ => id)
    (fun k => (compromised_bdhStoredOnly_iff tr hR k).mpr)⟩

theorem forwardSecrecy_bdhStoredOnly_of_real (h : ForwardSecrecy) :
    ForwardSecrecyWithBDH HonestDHStoredOnly :=
  fun tr hR => (fsQuery_bdhStoredOnly_iff tr hR).mpr ((fsQuery_iff_test tr _).mp (h tr hR))

theorem postCompromiseSecurity_bdhStoredOnly_of_real (h : PostCompromiseSecurity) :
    PostCompromiseSecurityWithBDH HonestDHStoredOnly :=
  fun tr hR => (pcsQuery_bdhStoredOnly_iff tr hR).mpr ((pcsQuery_iff_test tr _).mp (h tr hR))

/-- Dropping the stored-`TRState.dhs` disjunct of `honestDH` inside `Compromised`
(`HonestDHEventOnly`) refutes `PostCompromiseSecurity`: Alice's initial `dhsA` is stored in
`TRState.dhs` without logging `TREvent.HonestDH`. -/
theorem not_PostCompromiseSecurity_bdhEventOnly :
    ¬ PostCompromiseSecurityWithBDH HonestDHEventOnly := by
  intro hpcs
  refine not_pcsQuery_trBDH (P := tracePredicatesWithBDH HonestDHEventOnly trBDH) trBDH_msgKey
    (predKnows_of_msgKey trBDH_msgKey trBDH_knows_mkBDH) trBDH_honestDH_dhsA ?_
    (hpcs trBDH trBDH_reach)
  intro k hc
  rcases hc with ⟨s, i, h⟩ | ⟨s, i, h⟩ | ⟨s, ns, i, h⟩ | ⟨s, nr, i, h⟩ |
      ⟨s, n, i, h⟩ | ⟨⟨keys, j, hhk, hkb⟩, hall⟩ | ⟨⟨s, i, h⟩, _⟩
  · exact .inl (trBDH_exposedRK_eq h)
  · exact False.elim (not_tr_logged trBDH_nonRk_indices rfl h)
  · exact False.elim (not_tr_logged trBDH_nonRk_indices rfl h)
  · exact False.elim (not_tr_logged trBDH_nonRk_indices rfl h)
  · exact False.elim (not_tr_logged trBDH_nonRk_indices rfl h)
  · exact False.elim (trBDH_not_handshakeExcusedAt (hall keys j hhk hkb))
  · exact .inr (trBDH_honestDHEv_eq h)

end BrokenDHHonestMutants

/-! ## Strictness of Session-Scoped `HandshakeRootCompromised` -/

section B6TightBob

/-- Existential baseline predicate that excuses `k` whenever at least one handshake deriving `k` as
its initial root or chain key is excused. -/
def HandshakeRootCompromised_old_bob (tr : ExecTrace) (k : Bytes) : Prop :=
  ∃ keys j, HandshakeKeysAt tr j keys ∧ HandshakeWasCompromisedAt tr j ∧ (k = keys.rk ∨ k = keys.ck)

private theorem eventLoggedAt_unique_pqxdh {tr : ExecTrace} {e₁ e₂ : PQXDHEvent} {j : Nat}
    (h₁ : tr.EventLoggedAt e₁ j) (h₂ : tr.EventLoggedAt e₂ j) : e₁ = e₂ := by
  rw [Trace.EventLoggedAt_eq_getEventAt] at h₁ h₂
  exact Option.some.inj (h₁.symm.trans h₂)

private theorem trAlias_compromise_eq {e : PQXDHEvent} {j : Nat}
    (hj : trAlias.EventLoggedAt e j) (hp : isCompromise e = true) :
    e = .CompromisedIK "bob" (dhPk ikB) ∨ e = .CompromisedIK "carol" (dhPk ikB) := by
  have hm := mem_evIdx hj hp
  rw [trAlias_compromise_indices] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact .inl (eventLoggedAt_unique_pqxdh hj trAlias_compIK)
  · exact .inr (eventLoggedAt_unique_pqxdh hj trAlias_compIK_carol)

private theorem trAlias_aliceDone_excused : HandshakeWasCompromisedAt trAlias 31 :=
  .inl ⟨"alice", "carol", dhPk ikA, dhPk ikB, dhPk spkB, DY.PQKem.kemPk pqskB, none,
    trAlias_out.ek, trAlias_out.ct, trAlias_keys, trAlias_aliceDone,
    .inl ⟨25, trAlias_compIK_carol, .inl (by decide)⟩⟩

private theorem trAlias_bobDone_not_excused : ¬ HandshakeWasCompromisedAt trAlias 44 := by
  rintro (⟨a, b, ikA', ikB', spk, pqpk, opk, ek, ct, keys, h44, _⟩ |
      ⟨b, a, ikB', ikA', spk, pqpk, opk, ek, ct, keys, h44, hc⟩)
  · cases eventLoggedAt_unique_pqxdh h44 trAlias_bobDone
  · cases eventLoggedAt_unique_pqxdh h44 trAlias_bobDone
    rcases hc with (⟨j, hj, _⟩ | ⟨j, hj, _⟩ | ⟨j, hj, _⟩) | ⟨_, ⟨j, hj⟩, _⟩ | ⟨⟨j, hj⟩, _⟩
    · rcases trAlias_compromise_eq hj rfl with h | h <;>
        (injection h with hp _; exact absurd hp (by decide))
    all_goals rcases trAlias_compromise_eq hj rfl with h | h <;> cases h

private theorem trAlias_hrc_strict_witness :
    trAlias.Reachable reachability ∧
    (HandshakeRootCompromised_old_bob trAlias trAlias_keys.rk ∧
      ¬ HandshakeRootCompromised trAlias trAlias_keys.rk) ∧
    (HandshakeRootCompromised_old_bob trAlias trAlias_keys.ck ∧
      ¬ HandshakeRootCompromised trAlias trAlias_keys.ck) := by
  have hhk31 : HandshakeKeysAt trAlias 31 trAlias_keys :=
    ⟨_, _, _, _, _, _, _, .inl ⟨_, _, trAlias_aliceDone⟩⟩
  have hhk44 : HandshakeKeysAt trAlias 44 trAlias_keys :=
    ⟨_, _, _, _, _, _, _, .inr ⟨_, _, trAlias_bobDone⟩⟩
  refine ⟨trAlias_reach,
    ⟨⟨trAlias_keys, 31, hhk31, trAlias_aliceDone_excused, .inl rfl⟩,
      fun ⟨_, hall⟩ => trAlias_bobDone_not_excused (hall trAlias_keys 44 hhk44 (.inl rfl))⟩,
    ⟨⟨trAlias_keys, 31, hhk31, trAlias_aliceDone_excused, .inr rfl⟩,
      fun ⟨_, hall⟩ => trAlias_bobDone_not_excused (hall trAlias_keys 44 hhk44 (.inr rfl))⟩⟩

private theorem trAlias_compromised_strict_witness :
    ((tracePredicatesWithHRC HandshakeRootCompromised_old_bob trAlias).Compromised trAlias_keys.rk ∧
      ¬ CompromisedKey trAlias trAlias_keys.rk) ∧
    ((tracePredicatesWithHRC HandshakeRootCompromised_old_bob trAlias).Compromised trAlias_keys.ck ∧
      ¬ CompromisedKey trAlias trAlias_keys.ck) := by
  have hbdh : evIdx trAlias isBrokenDH = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro j hj
    simp only [evIdx, List.mem_filter, List.mem_range] at hj
    cases hge : trAlias.getEventAt PQXDHEvent j with
    | none => simp [hge] at hj
    | some e =>
      simp only [hge] at hj
      have hel : trAlias.EventLoggedAt e j := by
        rw [Trace.EventLoggedAt_eq_getEventAt]; exact hge
      have hp : isCompromise e = true := by
        cases e <;> simp [isBrokenDH, isCompromise] at hj ⊢
      rcases trAlias_compromise_eq hel hp with rfl | rfl <;> simp [isBrokenDH] at hj
  obtain ⟨_, ⟨hold_rk, hnew_rk⟩, ⟨hold_ck, hnew_ck⟩⟩ := trAlias_hrc_strict_witness
  refine ⟨⟨.inr (.inr (.inr (.inr (.inr (.inl hold_rk))))), fun hc => hnew_rk
      (compWithHRC_imp_hrc_of_no_tr_no_bdh trAlias_trExposure_indices hbdh hc)⟩,
    ⟨.inr (.inr (.inr (.inr (.inr (.inl hold_ck))))), fun hc => hnew_ck
      (compWithHRC_imp_hrc_of_no_tr_no_bdh trAlias_trExposure_indices hbdh hc)⟩⟩

/-- On `Adversary.trAlias`, Carol registers Bob's compromised identity key `ikB`, so Alice's
handshake with Carol logs an excused `AliceDone` deriving `trAlias_keys` whereas Bob's handshake
with Alice logs an unexcused `BobDone` with the same `trAlias_keys`; the existential baseline
excuses both `keys.rk` and `keys.ck`, whereas session-scoped `HandshakeRootCompromised` and
`CompromisedKey tr` excuse neither. -/
theorem b6_tight_bob_strict :
    ∃ (tr : ExecTrace) (keys : HandshakeKeys) (a b c : Participant)
      (ikA' ikB' spk pqpk ek ct : Bytes) (jCompB jA jB : Nat),
      tr.Reachable reachability ∧
      tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB') jCompB ∧ jCompB < jA ∧
      tr.EventLoggedAt (PQXDHEvent.AliceDone a c ikA' ikB' spk pqpk none ek ct keys) jA ∧
      HandshakeWasCompromisedAt tr jA ∧
      tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB' ikA' spk pqpk none ek ct keys) jB ∧
      ¬ HandshakeWasCompromisedAt tr jB ∧
      (HandshakeRootCompromised_old_bob tr keys.rk ∧ ¬ HandshakeRootCompromised tr keys.rk) ∧
      (HandshakeRootCompromised_old_bob tr keys.ck ∧ ¬ HandshakeRootCompromised tr keys.ck) ∧
      ((tracePredicatesWithHRC HandshakeRootCompromised_old_bob tr).Compromised keys.rk ∧
        ¬ CompromisedKey tr keys.rk) ∧
      ((tracePredicatesWithHRC HandshakeRootCompromised_old_bob tr).Compromised keys.ck ∧
        ¬ CompromisedKey tr keys.ck) := by
  obtain ⟨hreach, hhrc_rk, hhrc_ck⟩ := trAlias_hrc_strict_witness
  obtain ⟨hcomp_rk, hcomp_ck⟩ := trAlias_compromised_strict_witness
  exact ⟨trAlias, trAlias_keys, "alice", "bob", "carol", dhPk ikA, dhPk ikB, dhPk spkB,
    DY.PQKem.kemPk pqskB, trAlias_out.ek, trAlias_out.ct, 22, 31, 44, hreach,
    trAlias_compIK, by decide, trAlias_aliceDone, trAlias_aliceDone_excused,
    trAlias_bobDone, trAlias_bobDone_not_excused, hhrc_rk, hhrc_ck, hcomp_rk, hcomp_ck⟩

end B6TightBob

end Symbolic.Proofs.Tests.Model.ExplanationTightness.Compromised
