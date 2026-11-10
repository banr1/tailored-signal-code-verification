/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatement
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.CREF.Initiate.PostBridgePure
public import Symbolic.Proofs.Swarm.CREF.OpkRelC
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvIni
import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPureB
import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPureC
import Symbolic.Proofs.Swarm.CREF.Initiate.ModelPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec -- shake: keep
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# `session_initiate` Accepted-Branch Step and `CoinSplit` Slicing

Normalizes accepted `aliceStart` explanations to `shown = 35`, slices a 192-byte CLI `coins` buffer
into the 34 hardware RNG draws `initiateDrawsOfCoins`, proves `ini_ok_pure_step`, and defines
`InitiatePureOutcome`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.IniPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.IniSndPure Symbolic.Swarm.COMPOSED
cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed.Refinement.Cli (CoinSplit ExternContractsHoldCli)
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Symbolic.Swarm.CREF.TR.RecvDec
  (at?_append_of_lt at?_eq_none_of_le at?_append_non_entry logSkippedKeysTr getLocalState_snd)

theorem ini_aliceStart_eq_of_iniStep {interpretation : ExternInterpretation} {r : ProtocolSetup}
    (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move} {acc : List MachineEvent}
    {bundle : HwBytes} {ds : List HwBytes}
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc
      (.recv bundle :: ds.map MachineEvent.rng))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hstep_m : IniStep r.alice (.recv bundle :: ds.map MachineEvent.rng)
      (runMoves pre (runTraceMoves r ms₀)).1 m)
    (hvis_m : List.Forall₂ (EventMatchesEntry interpretation r S g)
      (.recv bundle :: ds.map MachineEvent.rng)
      (m.vis (runMoves pre (runTraceMoves r ms₀)).1))
    (hex : ExplainsMoves interpretation r S who ok g (ms₀ ++ (pre ++ m :: post))
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng)))
    (hok : ok (callStarts acc).length = true)
    (hds_lens : ds.map List.length = initiateFullDrawLengths) :
    ∃ (bh : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat),
      35 ≤ shown ∧ m = .aliceStart r.alice r.bob 4 6 bh shown := by
  let tr := (runMoves pre (runTraceMoves r ms₀)).1
  have hNe : r.alice ≠ r.bob := hwf.1
  have hds_len : ds.length = 34 := by
    have := congrArg List.length hds_lens; simpa [initiateFullDrawLengths] using this
  have hlen_vis : (m.vis tr).length = 35 := by
    have := (xpl_forall₂_length hvis_m).symm; simpa [hds_len] using this
  obtain ⟨v, hv, hvk, _⟩ := xpl_head_entry hvis_m (e := .recv bundle) rfl
  have hrk := xpl_recvHeadKind m tr hv hvk
  have hidx := ini_getElem?_append_middle ms₀ pre post m
  have htake := ini_take_append_middle ms₀ pre post m
  have hvis_pre : runVis r (ms₀ ++ pre) = runVis r ms₀ := by
    rw [runVis_append, ini_invisible_nil pre (runTraceMoves r ms₀) hpre, List.append_nil]
  have hcc : callCount (runVis r ((ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length))) =
      (callStarts acc).length := by
    rw [htake, hvis_pre]; exact callCount_eq_callStarts_length hB.pre.2.2.2.2.2
  cases m with
  | reject draws =>
    exfalso
    have hfalse := (hex.2 (ms₀.length + pre.length) (.reject draws) hidx).1 draws rfl
    rw [hcc, hok] at hfalse; cases hfalse
  | bobStart b a kh r' mh pq sp sh =>
    have := vis_length_le_three_of_bob_or_dec tr (.bobStart b a kh r' mh pq sp sh)
      (Or.inl ⟨b, a, kh, r', mh, pq, sp, sh, rfl⟩)
    omega
  | decrypt me si mi pq sp w =>
    have := vis_length_le_three_of_bob_or_dec tr (.decrypt me si mi pq sp w)
      (Or.inr (Or.inl ⟨me, si, mi, pq, sp, w, rfl⟩))
    omega
  | decryptSkipped me si mi k pq sp w =>
    have := vis_length_le_three_of_bob_or_dec tr (.decryptSkipped me si mi k pq sp w)
      (Or.inr (Or.inr ⟨me, si, mi, k, pq, sp, w, rfl⟩))
    omega
  | aliceStart a b idStateIdx regIdxB bh shown =>
    have ha : a = r.alice := by
      rcases hstep_m.1 with h | h
      · cases h
      · exact Option.some.inj h
    have hb : b = r.bob :=
      hB.run.2.2.2.2.2.1 (.aliceStart a b idStateIdx regIdxB bh shown) (by simp)
    subst ha hb
    have hexp : exposures tr ((Move.aliceStart r.alice r.bob idStateIdx regIdxB bh shown).next tr) = [] :=
      exposures_nil_of_not_leakKind rfl (fun hc => nomatch hc)
    have hlen_take : ((aliceVis tr ((Move.aliceStart r.alice r.bob idStateIdx regIdxB bh shown).next tr) bh).take shown).length = 35 := by
      have hv_eq := xpl_vis_eq (Move.aliceStart r.alice r.bob idStateIdx regIdxB bh shown) tr
      rw [hexp, List.append_nil] at hv_eq; dsimp only [xpl_ownVis] at hv_eq
      rw [← hv_eq]; exact hlen_vis
    have hshown : 35 ≤ shown := by rw [List.length_take] at hlen_take; omega
    have htr_eq : tr = runTraceMoves r (ms₀ ++ pre) := (TR.runTrace_append r ms₀ pre).symm
    have hnoSetup : ∀ m' ∈ ms₀ ++ pre, m'.isSetup = false := fun m' hm' =>
      hB.run.2.1 m' (by
        rcases List.mem_append.mp hm' with h1 | h2
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ (List.mem_append_left _ h2))
    let Inv : ExecTrace → Prop := fun tr' =>
      tr' = tr ∨
      ((∃ ikA, Symbolic.Swarm.COMPOSED.CompTrace.PQXDHStoredAt tr r.alice { kind := .identity, sk := ikA } idStateIdx) ∧
       (∃ ikB vkB honest, tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered r.bob ikB vkB honest) regIdxB))
    have hInv : Inv ((Move.aliceStart r.alice r.bob idStateIdx regIdxB bh shown).next tr) := by
      change Inv (((DY.Libsignal.Composed.aliceStart r.alice r.bob idStateIdx regIdxB bh >>= _).run tr).2.val)
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]; unfold DY.Libsignal.PQXDH.aliceHandshake
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd]
      apply Symbolic.Swarm.COMPOSED.CompTrace.bind_getKey_at r.alice idStateIdx .identity tr (Or.inl rfl); intro ikA hstA
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd]
      apply Symbolic.Swarm.COMPOSED.CompTrace.bind_lookupIdentity_at r.bob regIdxB tr (Or.inl rfl); intro ikB vkB honest hregB
      exact Or.inr ⟨⟨ikA, hstA⟩, ⟨ikB, vkB, honest, hregB⟩⟩
    rcases hInv with hnext_id | ⟨⟨ikA, hstA⟩, ⟨ikB, vkB, honest, hregB⟩⟩
    · rw [hnext_id, List.length_take] at hlen_take
      simp [aliceVis, aliceDraws, newRandoms, newIndices] at hlen_take
      omega
    · rw [htr_eq] at hstA hregB
      have hid4 : idStateIdx = 4 := iniP_alice_st_idx_eq_4 hNe hnoSetup hstA
      have hreg6 : regIdxB = 6 := iniP_bob_id_idx_eq_6 hNe hnoSetup
        ((Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hregB)
      subst hid4 hreg6; exact ⟨bh, shown, hshown, rfl⟩
  | _ => exact False.elim hrk

/-! ## Normalization from `shown` (`35 ≤ shown`) to `35` -/

private theorem ini_anchored_aliceStart_to_35 (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : PQXDH.BundleHandles) {shown : Nat} (hshown : 35 ≤ shown) (tr : ExecTrace)
    (ha : (Move.aliceStart a b idStateIdx regIdxB bh shown).LogsSessionCompletion tr) :
    (Move.aliceStart a b idStateIdx regIdxB bh 35).LogsSessionCompletion tr := by
  refine ⟨by omega, ?_⟩
  rw [← ini_aliceStart_vis_eq_35 a b idStateIdx regIdxB bh hshown]
  exact ha.2

private theorem ini_movesAnchored_aliceStart_to_35 (pre' post : List Move)
    (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : PQXDH.BundleHandles) {shown : Nat} (hshown : 35 ≤ shown) (tr : ExecTrace)
    (h : MovesAnchored (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post) tr) :
    MovesAnchored (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post) tr := by
  induction pre' generalizing tr with
  | nil => exact ⟨ini_anchored_aliceStart_to_35 a b idStateIdx regIdxB bh hshown tr h.1, h.2⟩
  | cons m pre' ih => exact ⟨h.1, ih (m.next tr) h.2⟩

private theorem ini_compromises_aliceStart_eq_35 (pre' post : List Move)
    (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : PQXDH.BundleHandles) (shown : Nat) (tr : ExecTrace) :
    compromisesCurrentFrom tr (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post) =
      compromisesCurrentFrom tr (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post) := by
  induction pre' generalizing tr with
  | nil => rfl
  | cons m pre' ih =>
    cases m <;> dsimp only [List.cons_append, compromisesCurrentFrom, Move.next, Move.act] <;> rw [ih]

private theorem ini_ownSalts_aliceStart_eq_35 (pre' post : List Move)
    (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : PQXDH.BundleHandles) (shown : Nat) (tr : ExecTrace) :
    ownSaltsFrom tr (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post) =
      ownSaltsFrom tr (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post) := by
  induction pre' generalizing tr with
  | nil => rfl
  | cons m pre' ih =>
    cases m <;> dsimp only [List.cons_append, ownSaltsFrom, Move.next, Move.act] <;> rw [ih]

private theorem ini_runMoves_take_aliceStart_eq_35 (pre' post : List Move)
    (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : PQXDH.BundleHandles) (shown k : Nat) (tr : ExecTrace) :
    (runMoves (List.take k (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post)) tr).1 =
      (runMoves (List.take k (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post)) tr).1 := by
  induction pre' generalizing tr k with
  | nil => cases k <;> rfl
  | cons m pre' ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k (m.next tr)

private theorem ini_peerFaithful_aliceStart_to_35 {r : ProtocolSetup} (pre' post : List Move)
    (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : PQXDH.BundleHandles) (shown : Nat)
    (hp : PeerFaithful r (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post)) :
    PeerFaithful r (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post) := by
  intro m hm
  rcases List.mem_append.mp hm with hm1 | hm2
  · exact hp m (List.mem_append_left _ hm1)
  · rcases List.mem_cons.mp hm2 with rfl | hm3
    · exact hp (.aliceStart a b idStateIdx regIdxB bh shown)
        (List.mem_append_right _ List.mem_cons_self)
    · exact hp m (List.mem_append_right _ (List.mem_cons_of_mem _ hm3))

private theorem ini_stateFaithful_aliceStart_to_35 {r : ProtocolSetup} (pre' post : List Move)
    (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : PQXDH.BundleHandles) (shown : Nat)
    (hs : StateFaithful r (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post)) :
    StateFaithful r (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post) := by
  have hget : ∀ (k : Nat) (m : Move) (p : Participant) (s : Nat) (b' : Bool),
      (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post)[k]? = some m →
      m.stateLoad? = some (p, s, b') →
      (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post)[k]? = some m := by
    intro k m p s b' hk hload
    by_cases hlt : k < pre'.length
    · rw [List.getElem?_append_left hlt] at hk ⊢; exact hk
    · have hge := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hge] at hk ⊢
      rcases hsub : k - pre'.length with _ | j
      · rw [hsub, List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk; cases hload
      · rw [hsub, List.getElem?_cons_succ] at hk
        rw [List.getElem?_cons_succ]; exact hk
  intro i j mi mj p k b' hij hi hj hli hoki hlj
  have hi' := hget i mi p k true hi hli
  have hj' := hget j mj p k b' hj hlj
  have htr_i : runTraceMoves r (List.take i (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post)) =
      runTraceMoves r (List.take i (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post)) := by
    rw [runTrace_eq_setup, runTrace_eq_setup]
    exact ini_runMoves_take_aliceStart_eq_35 pre' post a b idStateIdx regIdxB bh shown i (setupTrace r)
  exact hs i j mi mj p k b' hij hi' hj' hli (htr_i ▸ hoki) hlj

private theorem ini_modelRun_aliceStart_to_35 {r : ProtocolSetup} (pre' post : List Move)
    (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : PQXDH.BundleHandles) {shown : Nat} (hshown : 35 ≤ shown)
    (hrun : ModelRun r (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post)) :
    ModelRun r (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post) := by
  refine ⟨hrun.1, fun m hm => ?_, ?_⟩
  · rcases List.mem_append.mp hm with hm | hm
    · exact hrun.2.1 m (List.mem_append_left _ hm)
    · rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · exact hrun.2.1 m (List.mem_append_right _ (List.mem_cons_of_mem _ hm))
  · obtain ⟨⟨hreach, hanc, hpre_reach⟩, hcomp, hown, hpeer, hstate⟩ := hrun.2.2
    have htr_eq : runTraceMoves r (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post) =
        runTraceMoves r (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post) := by
      simpa using (ini_runTrace_aliceStart_eq_35 r [] pre' post a b idStateIdx regIdxB bh shown).symm
    refine ⟨⟨htr_eq ▸ hreach,
      ini_movesAnchored_aliceStart_to_35 pre' post a b idStateIdx regIdxB bh hshown (setupTrace r) hanc,
      fun k => ?_⟩,
      (ini_compromises_aliceStart_eq_35 pre' post a b idStateIdx regIdxB bh shown (setupTrace r)).symm.trans hcomp,
      (ini_ownSalts_aliceStart_eq_35 pre' post a b idStateIdx regIdxB bh shown (setupTrace r)).symm.trans hown,
      ini_peerFaithful_aliceStart_to_35 pre' post a b idStateIdx regIdxB bh shown hpeer,
      ini_stateFaithful_aliceStart_to_35 pre' post a b idStateIdx regIdxB bh shown hstate⟩
    have htk : runTraceMoves r (List.take k (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post)) =
        runTraceMoves r (List.take k (pre' ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post)) := by
      rw [runTrace_eq_setup, runTrace_eq_setup]
      exact (ini_runMoves_take_aliceStart_eq_35 pre' post a b idStateIdx regIdxB bh shown k (setupTrace r)).symm
    exact htk ▸ hpre_reach k

private theorem ini_matchedPrefix_mid_aliceStart_35 {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₀ pre post : List Move}
    {acc blk : List MachineEvent} {a b : Participant} {idStateIdx regIdxB : Nat}
    {bh : PQXDH.BundleHandles} {shown : Nat} (hshown : 35 ≤ shown)
    (hm_full : MatchedPrefix interpretation r S who g
      (ms₀ ++ (pre ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post)) (acc ++ blk))
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.aliceStart a b idStateIdx regIdxB bh 35).next (runMoves pre (runTraceMoves r ms₀)).1) post) :
    MatchedPrefix interpretation r S who g
      (ms₀ ++ pre ++ [.aliceStart a b idStateIdx regIdxB bh 35]) (acc ++ blk) := by
  let ms₁ := ms₀ ++ pre
  have hpost_vis : (runMoves post ((Move.aliceStart a b idStateIdx regIdxB bh shown).next (runTraceMoves r ms₁))).2 = [] := by
    rw [ini_aliceStart_next_eq_35, TR.runTrace_append]
    exact ini_invisible_nil post _ hpost
  have hm_assoc : MatchedPrefix interpretation r S who g
      ((ms₁ ++ [.aliceStart a b idStateIdx regIdxB bh shown]) ++ post) ((acc ++ blk) ++ []) := by
    simpa [ms₁, List.append_assoc] using hm_full
  have hlen_eq : (acc ++ blk).length = (runVis r (ms₁ ++ [.aliceStart a b idStateIdx regIdxB bh shown])).length := by
    have h1 := hm_full.2.2.2.2.2.length_eq
    have h2 : runVis r (ms₀ ++ (pre ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post)) =
        runVis r (ms₁ ++ [.aliceStart a b idStateIdx regIdxB bh shown]) := by
      rw [show ms₀ ++ (pre ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post) =
          (ms₁ ++ [.aliceStart a b idStateIdx regIdxB bh shown]) ++ post by simp [ms₁, List.append_assoc],
        runVis_append, TR.runTrace_snoc, hpost_vis, List.append_nil]
    rwa [h2] at h1
  have hm_shown : MatchedPrefix interpretation r S who g
      (ms₁ ++ [.aliceStart a b idStateIdx regIdxB bh shown]) (acc ++ blk) :=
    (matchedPrefix_prefix hlen_eq hm_assoc).1
  have hvis_eq : runVis r (ms₁ ++ [.aliceStart a b idStateIdx regIdxB bh 35]) =
      runVis r (ms₁ ++ [.aliceStart a b idStateIdx regIdxB bh shown]) := by
    rw [runVis_snoc, runVis_snoc, ini_aliceStart_vis_eq_35 a b idStateIdx regIdxB bh hshown]
  have htr_eq : runTraceMoves r (ms₁ ++ [Move.aliceStart a b idStateIdx regIdxB bh 35]) =
      runTraceMoves r (ms₁ ++ [Move.aliceStart a b idStateIdx regIdxB bh shown]) := by
    simpa using (ini_runTrace_aliceStart_eq_35 r ms₁ [] [] a b idStateIdx regIdxB bh shown).symm
  refine ⟨hm_shown.1,
    ini_modelRun_aliceStart_to_35 ms₁ [] a b idStateIdx regIdxB bh hshown hm_shown.2.1,
    ?_, ?_, ?_, ?_⟩
  · have hrf_pre : RoleFaithful r who ms₁ := roleFaithful_prefix hm_shown.2.2.1
    have hwho_a : who[callCount (runVis r ms₁)]? = some a := by
      have h := hm_shown.2.2.1 ms₁.length (.aliceStart a b idStateIdx regIdxB bh shown) a (by simp) rfl
      simpa using h
    exact roleFaithful_snoc_party hrf_pre rfl hwho_a
  · intro i m promote b' p hi hpath hcall hparse
    by_cases hlt : i < ms₁.length
    · have hi' : (ms₁ ++ [Move.aliceStart a b idStateIdx regIdxB bh shown])[i]? = some m := by
        rw [List.getElem?_append_left hlt] at hi ⊢; exact hi
      have htk1 : (ms₁ ++ [Move.aliceStart a b idStateIdx regIdxB bh 35]).take i = ms₁.take i :=
        List.take_append_of_le_length (Nat.le_of_lt hlt)
      have htk2 : (ms₁ ++ [Move.aliceStart a b idStateIdx regIdxB bh shown]).take i = ms₁.take i :=
        List.take_append_of_le_length (Nat.le_of_lt hlt)
      rw [htk1, ← htk2] at hcall ⊢
      exact hm_shown.2.2.2.1 i m promote b' p hi' hpath hcall hparse
    · have hge := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hge] at hi
      rcases hsub : i - ms₁.length with _ | k
      · rw [hsub, List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi; cases hpath
      · rw [hsub, List.getElem?_cons_succ, List.getElem?_nil] at hi; cases hi
  · change ReadFaithful interpretation r S g (ms₁ ++ [Move.aliceStart a b idStateIdx regIdxB bh 35]) (acc ++ blk)
    unfold ReadFaithful recvRepresentations preKeyRepresentations
    rw [hvis_eq, htr_eq]
    exact hm_shown.2.2.2.2.1
  · change List.Forall₂ (EventMatchesEntry interpretation r S g) (acc ++ blk)
      (runVis r (ms₁ ++ [Move.aliceStart a b idStateIdx regIdxB bh 35]))
    rw [hvis_eq]
    exact hm_shown.2.2.2.2.2

/-- Canonical 34-piece hardware RNG draw list extracted from a 192-byte CLI `coins` buffer. -/
def initiateDrawsOfCoins (coins : HwBytes) : List HwBytes :=
  [coins.take 32] ++ (List.range 32).map (fun i => (coins.drop (32 + 4 * i)).take 4) ++
    [(coins.drop 160).take 32]

private theorem take_append_take_drop :
    ∀ (m n : Nat) (bs : HwBytes), bs.take m ++ (bs.drop m).take n = bs.take (m + n)
  | 0, _, _ => by simp
  | _ + 1, _, [] => by simp
  | m + 1, n, b :: bs => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append, Nat.succ_add]
    exact congrArg (b :: ·) (take_append_take_drop m n bs)

private theorem flatten_four_byte_slices :
    ∀ (k : Nat) (bs : HwBytes),
      ((List.range k).map (fun i => (bs.drop (4 * i)).take 4)).flatten = bs.take (4 * k)
  | 0, bs => by simp
  | k + 1, bs => by
    rw [List.range_succ, List.map_append, List.flatten_append, flatten_four_byte_slices k bs]
    simp only [List.map_singleton, List.flatten_cons, List.flatten_nil, List.append_nil]
    simpa [Nat.mul_succ] using take_append_take_drop (4 * k) 4 bs

theorem initiateDrawsOfCoins_lengths {coins : HwBytes} (hlen : coins.length = 192) :
    (initiateDrawsOfCoins coins).map List.length = initiateFullDrawLengths := by
  unfold initiateDrawsOfCoins initiateFullDrawLengths
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def]
  have h0 : (coins.take 32).length = 32 := by simp [hlen]
  have h33 : ((coins.drop 160).take 32).length = 32 := by simp [hlen]
  have hmid : (List.range 32).map (fun i => ((coins.drop (32 + 4 * i)).take 4).length) =
      List.replicate 32 4 := by
    apply List.ext_getElem
    · simp
    · intro i hi1 _
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate,
        List.length_take, List.length_drop, hlen]
      have : i < 32 := by simpa using hi1
      omega
  rw [h0, hmid, h33]

theorem initiateDrawsOfCoins_nonempty {coins : HwBytes} (hlen : coins.length = 192) :
    ∀ p ∈ initiateDrawsOfCoins coins, p ≠ [] := by
  intro p hp hnil
  have hmem := List.mem_map_of_mem (f := List.length) hp
  rw [initiateDrawsOfCoins_lengths hlen, hnil] at hmem
  unfold initiateFullDrawLengths at hmem; simp at hmem

theorem initiateDrawsOfCoins_flatten {coins : HwBytes} (hlen : coins.length = 192) :
    (initiateDrawsOfCoins coins).flatten = coins := by
  unfold initiateDrawsOfCoins
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
  have hdrop : (List.range 32).map (fun i => (coins.drop (32 + 4 * i)).take 4) =
      (List.range 32).map (fun i => ((coins.drop 32).drop (4 * i)).take 4) := by
    apply List.map_congr_left; intro i _; rw [List.drop_drop, Nat.add_comm 32 (4 * i)]
  rw [hdrop, flatten_four_byte_slices 32 (coins.drop 32)]
  have hmid : (coins.drop 32).take (4 * 32) = (coins.drop 32).take 128 := rfl
  rw [hmid, take_append_take_drop 32 128 coins]
  change coins.take 160 ++ (coins.drop 160).take 32 = coins
  rw [take_append_take_drop 160 32 coins]
  change coins.take 192 = coins; rw [← hlen, List.take_length]

theorem coinSplit_append {a₁ b₁ a₂ b₂ : List MachineEvent}
    (h₁ : CoinSplit a₁ b₁) (h₂ : CoinSplit a₂ b₂) : CoinSplit (a₁ ++ a₂) (b₁ ++ b₂) := by
  induction h₁ with
  | nil => exact h₂
  | keep hne _ ih => exact .keep hne ih
  | split hne hpre _ ih => rw [List.cons_append, List.append_assoc]; exact .split hne hpre ih

theorem coinSplit_initiate_step (bundle coins : HwBytes) (ds : List HwBytes)
    (hne : ∀ p ∈ ds, p ≠ []) (hpre : ds.flatten <+: coins) :
    CoinSplit [.recv bundle, .rng coins] (.recv bundle :: ds.map MachineEvent.rng) :=
  .keep (fun _ h => by cases h) (by simpa using (CoinSplit.split hne hpre CoinSplit.nil))

theorem coinSplit_initiate_full {coins : HwBytes} (bundle : HwBytes) (hlen : coins.length = 192) :
    CoinSplit [.recv bundle, .rng coins]
      (.recv bundle :: (initiateDrawsOfCoins coins).map MachineEvent.rng) :=
  coinSplit_initiate_step bundle coins (initiateDrawsOfCoins coins)
    (initiateDrawsOfCoins_nonempty hlen) ⟨[], by rw [initiateDrawsOfCoins_flatten hlen, List.append_nil]⟩

/-! ## Accepted-branch step and outcome predicate -/

/-- Steps `Clean`, `PureCRel`, and `COpkRelC` across an accepted `session_initiate` call. -/
theorem ini_ok_pure_step (interpretation : ExternInterpretation)
    (hext : ExternContractsHoldCli interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    (S : OpaqueSymbolSemantics) (hSeq : S = compSemOf interpretation r)
    (who : List Participant) (ok : Nat → Bool)
    (records : Participant → Option HwBytes) (sent accepted : List HwBytes) (opkUsed : Bool)
    (acc : List MachineEvent) (bundle : HwBytes) (ds : List HwBytes) (recState : HwBytes)
    (hclean₀ : ∃ g₀ ms₀, Clean interpretation r S who ok g₀ ms₀ acc)
    (hrel : PureCRel interpretation r S who ok records sent accepted acc)
    (hopk : COpkRelC interpretation r S who ok opkUsed acc)
    (hwho_cs : who[(callStarts acc).length]? = some r.alice)
    (hhon : HonestBundle interpretation r bundle)
    (hbin : IniOkBin bundle ds)
    (hV1 : AliceInitiatedV1PostPure interpretation r bundle ds recState) :
    let records' := fun q => if q = r.alice then some recState else records q
    (callStarts (.recv bundle :: ds.map MachineEvent.rng)).length = 1 ∧
    (∃ g ms, MatchedPrefix interpretation r S who g ms
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng))) ∧
    (ok (callStarts acc).length = true →
      (∃ g ms, Clean interpretation r S who ok g ms
        (acc ++ (.recv bundle :: ds.map MachineEvent.rng))) ∧
      PureCRel interpretation r S who ok records' sent accepted
        (acc ++ (.recv bundle :: ds.map MachineEvent.rng)) ∧
      COpkRelC interpretation r S who ok opkUsed
        (acc ++ (.recv bundle :: ds.map MachineEvent.rng))) := by
  subst hSeq
  intro records'
  let S0 := compSemOf interpretation r
  have hcs_blk : (callStarts (.recv bundle :: ds.map MachineEvent.rng)).length = 1 := by
    rw [ini_callStarts_blk bundle ds]; rfl
  obtain ⟨g₀, ms₀, hc₀⟩ := hclean₀
  obtain ⟨ms_opk, bh₀, g₀', -, -, -, hm₀'⟩ :=
    ini_matchedPrefix_initOk interpretation hext r hwf who g₀ ms₀ acc bundle ds
      hc₀.matched hwho_cs hhon hbin
  refine ⟨hcs_blk, ⟨g₀', _, hm₀'⟩, fun hok_j => ?_⟩
  have hbka' : BobRecordBaseKeyInAccepted r records' accepted :=
    ini_ok_bka hwf recState hrel.bka
  have hbkn' : PureBobKyberNone r records' := by
    intro rr hrr
    dsimp only [records'] at hrr
    simp only [hwf.1.symm, ↓reduceIte] at hrr
    exact hrel.bkn rr hrr
  have hooo' : COooAll records' :=
    ini_ok_cOOO interpretation r bundle ds recState hV1 hrel.oooAll
  obtain ⟨ms_opk_cl, bh_cl, g_cl, -, -, -, hc_cl⟩ :=
    ini_clean_initOk interpretation hext r hwf who ok g₀ ms₀ acc bundle ds
      hc₀ hwho_cs hok_j hhon hbin
  have hhead : ∀ e ∈ (MachineEvent.recv bundle :: ds.map MachineEvent.rng).head?,
      eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; exact Or.inl rfl
  have hbi : IniBlockShape (.recv bundle :: ds.map MachineEvent.rng) := by
    refine ⟨⟨bundle, rfl⟩, fun e he => ?_⟩
    simp only [List.tail_cons, List.mem_map] at he; obtain ⟨d, _, rfl⟩ := he; rfl
  refine ⟨⟨g_cl, _, hc_cl⟩,
    ⟨hooo', TR.sendsFit_append hrel.sendsFit (ini_sendsFit bundle ds), hbka', hbkn',
      fun g ms hcl => ?_⟩,
    cOpkRelC_of_no_accept hopk (fun h => h) hhead ini_prefix_reachable
      (ini_no_accept_in_blk bundle ds)⟩
  obtain ⟨ms_p, δ, rfl, hpre_mp, hmatch⟩ :=
    matchedPrefix_split hcl.matched hhead (ini_prefix_reachable g ms hcl.matched)
  have hB : XplBlock interpretation r S0 who g ms_p δ acc (.recv bundle :: ds.map MachineEvent.rng) :=
    ⟨hpre_mp, hcl.matched.2.1, hmatch⟩
  have hcl_pre : Clean interpretation r S0 who ok g ms_p acc :=
    clean_prefix hpre_mp.2.2.2.2.2.length_eq hcl
  obtain ⟨hrelAt₀, hbks₀⟩ := hrel.clean g ms_p hcl_pre
  have hne : (MachineEvent.recv bundle :: ds.map MachineEvent.rng) ≠ [] := List.cons_ne_nil _ _
  have htail : ∀ e ∈ (MachineEvent.recv bundle :: ds.map MachineEvent.rng).tail,
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; simp only [List.tail_cons, List.mem_map] at he
    obtain ⟨d, _, rfl⟩ := he; simp [eventKind]
  obtain ⟨pre, m, post, rfl, hpre, ⟨hs, ha, hvis_m⟩, hpost⟩ := xpl_oneMove hB hhead hne htail
  have hdf : DeltaFaithful r.alice (runTraceMoves r ms_p) (pre ++ m :: post) :=
    ini_deltaFaithful_of_explains hB hcl.1 hwho_cs
  have hact_m : ActorIn r.alice m :=
    actorIn_of_vis_ne_nil hdf (vis_ne_nil_of_forall₂ hvis_m hne)
  have hstep_m : IniStep r.alice (.recv bundle :: ds.map MachineEvent.rng)
      (runMoves pre (runTraceMoves r ms_p)).1 m :=
    xplStep_ini hs ha hvis_m hbi hact_m
  obtain ⟨bh, shown, hshown, rfl⟩ :=
    ini_aliceStart_eq_of_iniStep hwf hB hpre hstep_m hvis_m hcl.1 hok_j hbin.lens
  have hm_mid35 : MatchedPrefix interpretation r S0 who g
      (ms_p ++ pre ++ [.aliceStart r.alice r.bob 4 6 bh 35])
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng)) :=
    ini_matchedPrefix_mid_aliceStart_35 hshown hcl.matched hpost
  have hrelAt35 := ini_ok_step_pureCRelAt interpretation hext r hwf
    records sent accepted acc bundle ds recState hhon hV1 hbin.lens bh hm_mid35 hpre hpost hrelAt₀
  have hrelAt := ini_pureCRelAt_aliceStart_of_35 (shown := shown) hrelAt35
  have hrec_bob : records' r.bob = records r.bob := by
    dsimp only [records']; simp [hwf.1.symm]
  exact ⟨hrelAt, bks_ini_ok hwf bh shown hpre hpost hrec_bob hbks₀⟩

end Symbolic.Swarm.CREF.CliPure.IniPure

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed.Refinement.Cli (CoinSplit ExternContractsHoldCli)
open Symbolic.Swarm.COMPOSED
export IniPure (initiateDrawsOfCoins initiateDrawsOfCoins_lengths initiateDrawsOfCoins_nonempty
  initiateDrawsOfCoins_flatten coinSplit_initiate_step coinSplit_initiate_full)

/-- Postcondition relating CLI `initiate` inputs `(bundle, coins)` to optional new session record
`outRec` and consumed RNG draws `ds`. -/
def InitiatePureOutcome (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (bundle coins : HwBytes) (outRec : Option HwBytes) (ds : List HwBytes) : Prop :=
  match outRec with
  | none =>
    (∀ p ∈ ds, p ≠ []) ∧ ds.flatten <+: coins
  | some recState =>
    coins.length = 192 ∧
    ds = initiateDrawsOfCoins coins ∧
    HonestBundle interpretation r bundle ∧
    IniOkBin bundle ds ∧
    AliceInitiatedV1PostPure interpretation r bundle ds recState

end Symbolic.Swarm.CREF.CliPure
